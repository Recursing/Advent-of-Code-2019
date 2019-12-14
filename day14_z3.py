import z3
from itertools import chain
from day14 import parse_recipes, puzzle_input

recipes = parse_recipes(puzzle_input)
chemicals = {c: z3.Int(c) for c in recipes}
chemicals["ORE"] = z3.Int("ORE")
reactions = {c: z3.Int(f"reaction_{c}") for c in recipes}
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
    constraints.append(chemicals[chemical] >= z3.Sum(required))

# part 1
print("Part 1:")


def solution_below(max_ore):
    solver = z3.Solver()
    solver.add(constraints)
    solver.add(chemicals["FUEL"] == 1)
    solver.add(chemicals["ORE"] < max_ore)
    if solver.check() == z3.sat:
        return solver.model()[chemicals["ORE"]].as_long()
    return -1


upper = solution_below(2 ** 31)
if upper >= 0:
    print("Upper bound:", upper)
else:
    print("unsat")
    quit()


lower = 1
while upper - lower > 1:
    middle = (upper + lower) // 2
    new_lower = solution_below(middle)
    if new_lower > -1:
        upper = new_lower
    else:
        lower = middle
    print(f"{lower} - {upper}")

# part 2
print("Part 2:")


def solution_above(min_fuel):
    solver = z3.Solver()
    solver.add(constraints)
    solver.add(chemicals["ORE"] == 1000000000000)
    solver.add(chemicals["FUEL"] > min_fuel)
    if solver.check() == z3.sat:
        return solver.model()[chemicals["FUEL"]].as_long()
    return -1


lower = solution_above(1)
upper = 1000000000000
while upper - lower > 1:
    middle = (upper + lower) // 2
    new_lower = solution_above(middle)
    if new_lower > -1:
        lower = new_lower
    else:
        upper = middle
    print(f"{lower} - {upper}")
