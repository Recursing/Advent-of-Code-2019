from day9 import Processor
from enum import Enum, auto
from collections import namedtuple
from typing import Dict
import sys

sys.setrecursionlimit(10000)

with open("day15.txt", "r") as input_file:
    puzzle_input = input_file.read()

init_mem = map(int, puzzle_input.split(","))
proc = Processor(init_mem)
proc_gen = proc.run()
assert next(proc_gen) == "input"


class Tile(Enum):
    WALL = auto()
    VISITED = auto()
    GOAL = auto()


class Vec2(namedtuple("Point", ["x", "y"])):
    def __add__(self, other):
        return Vec2(self.x + other.x, self.y + other.y)


class Direction(Enum):
    UP = Vec2(0, -1)
    DOWN = Vec2(0, 1)
    LEFT = Vec2(-1, 0)
    RIGHT = Vec2(1, 0)
    DOWNRIGHT = Vec2(1, 1)


directions = {
    Direction.UP: 1,
    Direction.DOWN: 2,
    Direction.LEFT: 3,
    Direction.RIGHT: 4,
}
opposite_code = {1: 2, 2: 1, 3: 4, 4: 3}
status_codes = {0: Tile.WALL, 1: Tile.VISITED, 2: Tile.GOAL}


# Part 1, recursive depth first search


def goal_distance_in_direction(pos: Vec2, d: Direction, maze: Dict[Vec2, Tile]) -> int:
    # -1 means unreachable
    dir_code = directions[d]
    neighbour = pos + d.value
    if neighbour in maze:
        return -1
    res = status_codes[proc_gen.send(dir_code)]
    assert next(proc_gen) == "input"
    maze[neighbour] = res
    if res == Tile.GOAL:
        return 1
    elif res == Tile.WALL:
        return -1
    neighbour_distance = goal_distance(neighbour, maze)
    if neighbour_distance < 0:
        back_code = opposite_code[dir_code]
        prev_tile = proc_gen.send(back_code)
        assert status_codes[prev_tile] == Tile.VISITED
        assert next(proc_gen) == "input"
        return -1
    else:
        return 1 + neighbour_distance


def goal_distance(pos: Vec2, maze: Dict[Vec2, Tile]) -> int:
    for d in directions:
        dir_res = goal_distance_in_direction(pos, d, maze)
        if dir_res >= 0:
            return dir_res
    return -1


# Part 2, recursive depth first search


def furthest_point_in_direction(pos: Vec2, d: Direction, maze: Dict[Vec2, Tile]) -> int:
    dir_code = directions[d]
    neighbour = pos + d.value
    if neighbour in maze:
        return 0
    res = status_codes[proc_gen.send(dir_code)]
    assert next(proc_gen) == "input"
    maze[neighbour] = res
    if res == Tile.WALL:
        return 0
    dir_result = furthest_point(neighbour, maze)
    back_code = opposite_code[dir_code]
    prev_tile = proc_gen.send(back_code)
    assert status_codes[prev_tile] in (Tile.VISITED, Tile.GOAL)
    assert next(proc_gen) == "input"
    return 1 + dir_result


def furthest_point(pos: Vec2, maze: Dict[Vec2, Tile]) -> int:
    return max(furthest_point_in_direction(pos, d, maze) for d in directions)


if __name__ == "__main__":
    start_pos = Vec2(0, 0)
    maze: Dict[Vec2, Tile] = {start_pos: Tile.VISITED}
    print(goal_distance(start_pos, maze))

    maze_items = list(maze.items())
    assert maze_items[-1][1] == Tile.GOAL
    oxygen_pos = maze_items[-1][0]

    # Keep only wall positions
    maze = {k: v for k, v in maze.items() if v == Tile.WALL}
    maze[oxygen_pos] = Tile.GOAL
    print(furthest_point(oxygen_pos, maze))
