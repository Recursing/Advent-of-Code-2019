from itertools import combinations
from functools import reduce
from math import gcd
import re


class Vec:
    def __init__(self, x, y, z):
        self.x = x
        self.y = y
        self.z = z

    def add(self, other):
        self.x += other.x
        self.y += other.y
        self.z += other.z

    def sub(self, other):
        self.x -= other.x
        self.y -= other.y
        self.z -= other.z

    def __getitem__(self, index):
        return [self.x, self.y, self.z][index]


class Moon:
    def __init__(self, pos, vel):
        self.pos = pos
        self.vel = vel

    def energy(self) -> int:
        return sum(abs(c) for c in self.pos) * sum(abs(c) for c in self.vel)


puzzle_input = """<x=-4, y=-9, z=-3>
<x=-13, y=-11, z=0>
<x=-17, y=-7, z=15>
<x=-16, y=4, z=2>""".splitlines()


def parse_line(line: str) -> Vec:
    numbers = map(int, re.findall(r"-?\d+", line))
    return Vec(*numbers)


moons = [Moon(parse_line(line), Vec(0, 0, 0)) for line in puzzle_input]


def sign(n: int):
    if n > 0:
        return 1
    if n < 0:
        return -1
    return 0


def apply_gravity(moon_a, moon_b):
    pos_a, pos_b = moon_a.pos, moon_b.pos
    signs = Vec(*(sign(ca - cb) for ca, cb in zip(pos_a, pos_b)))
    moon_b.vel.add(signs)
    moon_a.vel.sub(signs)


def apply_velocity(moon):
    moon.pos.add(moon.vel)


def step(moons):
    for pair in combinations(moons, 2):
        apply_gravity(*pair)
    for moon in moons:
        apply_velocity(moon)


def coord_hash(moons, coord):
    return tuple(
        x for m in moons for x in (getattr(m.pos, coord), getattr(m.vel, coord))
    )


sets = {"x": set(), "y": set(), "z": set()}
first_hashes = {coord_name: coord_hash(moons, coord_name) for coord_name in sets}
for coord_name in sets:
    sets[coord_name].add(first_hashes[coord_name])

periods = {coord_name: 0 for coord_name in sets}

for step_number in range(1, 10000000):
    step(moons)
    for coord_name in sets:
        if periods[coord_name]:
            continue
        c_hash = coord_hash(moons, coord_name)
        if c_hash in sets[coord_name]:
            assert c_hash == first_hashes[coord_name]
            periods[coord_name] = step_number
        sets[coord_name].add(c_hash)
    if all(periods.values()):
        break


def lcm2(a, b):
    return a * b // gcd(a, b)


def lcm(*args):
    return reduce(lcm2, args)


print(periods)
print(lcm(*periods.values()))
