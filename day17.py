from day9 import Processor
from day15 import Vec2, Direction
from itertools import product

with open("day17.txt") as input_file:
    puzzle_input = input_file.readline()

start_mem = list(map(int, puzzle_input.split(",")))
proc = Processor(start_mem)
proc_gen = proc.run()
world = "".join(map(chr, proc_gen)).splitlines()
padded_world = ["." + line + "." for line in world if line]
padded_width = len(padded_world[0])
padded_world = ["." * padded_width] + padded_world + ["." * padded_width]


def neighbours(row, col, array):
    deltas = (d.value for d in Direction)
    for dx, dy in deltas:
        yield array[row + dy][col + dx]


def parameter(row, col):
    return (row - 1) * (col - 1)


tot = 0
for row, line in enumerate(padded_world):
    for col, char in enumerate(line):
        if char == "#" and all(c == "#" for c in neighbours(row, col, padded_world)):
            tot += parameter(row, col)

print("Part 1: ", tot)
direction_char, coords = next(
    (char, (col, row))
    for row, line in enumerate(padded_world)
    for col, char in enumerate(line)
    if char not in ".#"
)
directions = {
    "^": (Direction.UP.value, "<", ">"),
    "v": (Direction.DOWN.value, ">", "<"),
    "<": (Direction.LEFT.value, "v", "^"),
    ">": (Direction.RIGHT.value, "^", "v"),
}
direction = directions[direction_char]
pos = Vec2(*coords)
dirs = []
while True:
    length = 0
    left, right = direction[1:]
    left_d = directions[left][0]
    right_d = directions[right][0]
    lpos = pos + left_d
    while padded_world[lpos.y][lpos.x] == "#":
        length += 1
        direction = directions[left]
        pos = lpos
        lpos = pos + left_d
    if length != 0:
        dirs.append(f"L,{length}")
        continue
    rpos = pos + directions[right][0]
    while padded_world[rpos.y][rpos.x] == "#":
        length += 1
        direction = directions[right]
        pos = rpos
        rpos = pos + directions[right][0]
    if length != 0:
        dirs.append(f"R,{length}")
    else:
        break

directions_str = ",".join(dirs) + ","
print(directions_str)

# much better regex solution from Stefano
# ^(.{1,21})\1*(.{1,21})(?:\1|\2)*(.{1,21})(?:\1|\2|\3)*$
for A_len, B_len, C_len in product(range(2, 21), repeat=3):
    A = directions_str[:A_len]
    str_without_A = directions_str.replace(A, "")
    B = str_without_A[:B_len]
    str_without_B = str_without_A.replace(B, "")
    C = str_without_B[:C_len]
    str_without_C = str_without_B.replace(C, "")
    if str_without_C == "":
        break

main_str = directions_str.replace(A, "A,").replace(B, "B,").replace(C, "C,")
print(f"Pattern: {main_str[:-1]}")
print(f"A: {A[:-1]} B: {B[:-1]} C: {C[:-1]}")

# part 2
assert start_mem[0] == 1
start_mem[0] = 2
proc = Processor(start_mem)
proc_gen = proc.run()


def consume_output(proc_gen):
    for output in proc_gen:
        if output == "input":
            break
        yield output


while True:
    output = "".join(map(chr, consume_output(proc_gen)))
    if ord(output[-1]) > 1000:
        print("Part 2:", ord(output[-1]))
        break
    print(output)
    inputs = list(map(ord, input()))
    if len(inputs) > 20:
        print("Too many inputs!")
        quit()
    for in_code in inputs:
        assert proc_gen.send(in_code) == "input"
    print(chr(proc_gen.send(10)), end="")
