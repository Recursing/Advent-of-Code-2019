from math import gcd
from itertools import product, groupby, zip_longest
from math import atan2, pi as PI

with open("day10.txt", "r") as input_file:
    grid = [l.strip() for l in input_file.readlines()]

WIDTH = len(grid[0])
HEIGHT = len(grid)
all_cells = list(product(range(HEIGHT), range(WIDTH)))


def score(py, px):
    hits = set()
    for y, x in all_cells:
        if grid[y][x] != "#":
            continue
        dy, dx = y - py, x - px
        cd = gcd(dy, dx)
        if cd == 0:
            assert dy == dx and dx == 0
        else:
            hits.add((dy // cd, dx // cd))
    return len(hits)


max_score, (py, px) = max(
    (score(py, px), (py, px)) for py, px in all_cells if grid[py][px] == "#"
)

print(max_score, (py, px))


def sorted_asteroids(py, px):
    coords = [
        (y - py, x - px)
        for y, x in all_cells
        if grid[y][x] == "#" and (py != y or px != x)
    ]

    def ratio(pos):
        dy, dx = pos
        real_angle = (atan2(dy, dx) + 2 * PI + PI / 2) % (2 * PI)
        angle = round(real_angle, 5)
        length = dx * dx + dy * dy
        return angle, length

    coords.sort(key=ratio)
    groups = groupby(coords, key=lambda a: ratio(a)[0])
    zipped = zip_longest(*[list(items) for key, items in groups])
    return [c for group in zipped for c in group if c]


dy, dx = sorted_asteroids(py, px)[199]
print(dx + px, dy + py)
