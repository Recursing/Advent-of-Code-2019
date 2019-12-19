from day9 import Processor
from day15 import Vec2, Direction
from itertools import product

with open("day19.txt") as input_file:
    puzzle_input = input_file.readline()

start_mem = tuple(map(int, puzzle_input.split(",")))


def cell_value(x, y):
    proc = Processor(start_mem)
    proc_gen = proc.run()
    assert next(proc_gen) == "input"
    assert proc_gen.send(x) == "input"
    ret = proc_gen.send(y)
    assert ret in (0, 1)
    return ret


s = 0
ls = 0
points = []
for y in range(50):
    for x in range(50):
        ret = cell_value(x, y)
        if ret:
            points.append(Vec2(x, y))
        s += ret

print("Part 1:", s)

# Part2 asserts x > y and a narrow beam, no time to do it cleanly, fast enough
lower_left = max(points)


def move(point: Vec2, dir1: Vec2, dir2: Vec2) -> Vec2:
    if cell_value(*(point + dir1)):
        return point + dir1
    else:
        assert cell_value(*(point + dir2))
        return point + dir2


# upper right corner is 99 steps to the right of lower left corner

while True:
    lower_left = move(lower_left, Direction.DOWNRIGHT.value, Direction.RIGHT.value)
    upper_right = lower_left + Vec2(99, -99)
    if cell_value(*(upper_right)):
        print("Part 2:", lower_left.x * 10000 + upper_right.y)
        break
