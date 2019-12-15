import pulp
from itertools import chain
from day14 import parse_recipes, puzzle_input

recipes = parse_recipes(puzzle_input)
chemicals = {c: pulp.LpVariable(c, cat=pulp.LpInteger) for c in recipes}
chemicals["ORE"] = pulp.LpVariable("ORE", cat=pulp.LpInteger)
reactions = {c: pulp.LpVariable(f"reaction_{c}", cat=pulp.LpInteger) for c in recipes}
quantities_required = {c: [] for c in recipes}
quantities_required["ORE"] = []

constraints = []
for var in chain(chemicals.values(), reactions.values()):
    constraints.append(var >= 0)

for out_chemical, (quantity, inputs) in recipes.items():
    constraints.append(chemicals[out_chemical] == quantity * reactions[out_chemical])
    for chemical, quantity in inputs:
        quantities_required[chemical].append(reactions[out_chemical] * quantity)
for chemical, required in quantities_required.items():
    if not required:
        continue
    constraints.append(chemicals[chemical] >= pulp.lpSum(required))


# part 1
print("Part 1:")
prob = pulp.LpProblem("Day141", pulp.LpMinimize)
for c in constraints:
    prob += c
prob += chemicals["ORE"]
prob += chemicals["FUEL"] == 1

prob.solve()
print(("Status:", pulp.LpStatus[prob.status]))
print(pulp.value(chemicals["ORE"]))


# part 2
print("Part 2:")
prob = pulp.LpProblem("Day142", pulp.LpMaximize)
for c in constraints:
    prob += c
prob += chemicals["FUEL"]
prob += chemicals["ORE"] == 1000000000000

prob.solve()
print(("Status:", pulp.LpStatus[prob.status]))
print(pulp.value(chemicals["FUEL"]))
