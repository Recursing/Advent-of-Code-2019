import cvxpy as cp
from itertools import chain
from day14 import parse_recipes, puzzle_input

recipes = parse_recipes(puzzle_input)
chemicals = {c: cp.Variable(integer=True) for c in recipes}
chemicals["ORE"] = cp.Variable(integer=True)
reactions = {c: cp.Variable(integer=True) for c in recipes}
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
    constraints.append(chemicals[chemical] >= cp.sum(required))

# Doesn't work for me, maybe with a different solver? Or I'm doing something wrong?

# part 1
print("Part 1:")
objective = cp.Minimize(chemicals["ORE"])
constraints.append(chemicals["FUEL"] >= 1)
prob = cp.Problem(objective, constraints)

print(prob.solve())
print(chemicals["ORE"].value)


# part 2
print("Part 2:")
objective = cp.Maximize(chemicals["FUEL"])
constraints.append(chemicals["ORE"] == 1000000000000)
prob = cp.Problem(objective, constraints)
print(prob.solve())
print(chemicals["FUEL"].value)
