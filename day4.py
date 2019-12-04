import z3

LOWER = 109165
UPPER = 576723
# Part 1
digits = [z3.Int(f"d_{i}") for i in range(6)]
s = z3.Solver()
for i, d in enumerate(digits):
    if i == 0:
        s.add(z3.And(d > 0, d <= 9))
    else:
        s.add(z3.And(d >= digits[i - 1], d <= 9))

s.add(z3.Or([a == b for a, b in zip(digits, digits[1:])]))

number = sum(10 ** i * d for i, d in enumerate(reversed(digits)))
s.add(z3.And(number > LOWER, number < UPPER))

solutions = set()
while s.check() == z3.sat:
    solution = s.model()
    number = sum(
        10 ** i * solution[d].as_long() for i, d in enumerate(reversed(digits))
    )
    solutions.add(number)
    s.add(z3.Or([variable() != solution[variable] for variable in solution]))

print(111111 in solutions)
print(223450 not in solutions)
print(123789 not in solutions)
print(len(solutions))

# Part 2
digits = [z3.Int(f"d_{i}") for i in range(6)]
s = z3.Solver()
for i, d in enumerate(digits):
    if i == 0:
        s.add(z3.And(d > 0, d <= 9))
    else:
        s.add(z3.And(d >= digits[i - 1], d <= 9))

chunks = zip(digits, digits[1:], digits[2:], digits[3:])

s.add(
    z3.Or(
        *[z3.And(a != b, b == c, c != d) for a, b, c, d in chunks],
        z3.And(digits[0] == digits[1], digits[1] != digits[2]),
        z3.And(digits[-1] == digits[-2], digits[-2] != digits[-3]),
    )
)


number = sum(10 ** i * d for i, d in enumerate(reversed(digits)))
s.add(z3.And(number > LOWER, number < UPPER))

solutions = set()
while s.check() == z3.sat:
    solution = s.model()
    number = sum(
        10 ** i * solution[d].as_long() for i, d in enumerate(reversed(digits))
    )
    solutions.add(number)
    s.add(z3.Or([variable() != solution[variable] for variable in solution]))

print(111111 not in solutions)
print(112233 in solutions)
print(123444 not in solutions)
print(111122 in solutions)
print(len(solutions))
