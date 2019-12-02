from operator import add, mul

ops = [..., add, mul]
puzzle_input = "1,0,0,3,1,1,2,3,1,3,4,3,1,5,0,3,2,1,10,19,1,6,19,23,1,10,23,27,2,27,13,31,1,31,6,35,2,6,35,39,1,39,5,43,1,6,43,47,2,6,47,51,1,51,5,55,2,55,9,59,1,6,59,63,1,9,63,67,1,67,10,71,2,9,71,75,1,6,75,79,1,5,79,83,2,83,10,87,1,87,5,91,1,91,9,95,1,6,95,99,2,99,10,103,1,103,5,107,2,107,6,111,1,111,5,115,1,9,115,119,2,119,10,123,1,6,123,127,2,13,127,131,1,131,6,135,1,135,10,139,1,13,139,143,1,143,13,147,1,5,147,151,1,151,2,155,1,155,5,0,99,2,0,14,0"

# part 1
mem = [int(n) for n in puzzle_input.split(",")]
mem[1], mem[2] = 12, 2
for i in range(0, len(mem), 4):
    if mem[i] == 99:
        break
    opcode, pos1, pos2, pos_res = mem[i : i + 4]
    mem[pos_res] = ops[opcode](mem[pos1], mem[pos2])

print(mem[0])

# part 2
import z3

mem = [int(n) for n in puzzle_input.split(",")]
z3_mem = z3.Array("memory", z3.IntSort(), z3.IntSort())
for i, v in enumerate(mem):
    z3_mem = z3.Store(z3_mem, i, v)
noun, verb = z3.Int("noun"), z3.Int("verb")
z3_mem = z3.Store(z3_mem, 1, noun)
z3_mem = z3.Store(z3_mem, 2, verb)
mem_len = len(mem)
s = z3.Solver()

terminated = False
for i in range(0, mem_len, 4):
    opcode = z3_mem[i]
    terminated = z3.Or(opcode == 99, terminated)
    if i + 3 >= mem_len:
        break
    pos1, pos2, pos_res = z3_mem[i + 1], z3_mem[i + 2], z3_mem[i + 3]
    valid = z3.And(
        pos1 >= 0,
        pos2 >= 0,
        pos_res >= 0,
        pos1 < mem_len,
        pos2 < mem_len,
        pos_res < mem_len,
    )
    s.add(z3.Or(terminated, valid))

    z3_mem = z3.If(
        terminated,
        z3_mem,
        z3.If(
            opcode == 1,
            z3.Store(z3_mem, pos_res, z3_mem[pos1] + z3_mem[pos2]),
            z3.Store(z3_mem, pos_res, z3_mem[pos1] * z3_mem[pos2]),
        ),
    )

print("Solving...")
print(19690720, "=", z3.simplify(z3_mem[0]))
s.add(z3_mem[0] == 19690720)
s.add(terminated)
if not s.check():
    print("Cannot solve :(")
else:
    m = s.model()
    print(m[noun], m[verb])
