from itertools import cycle, chain, repeat

with open("day16.txt", "r") as input_file:
    puzzle_input = tuple(int(c) for c in input_file.read())

# puzzle_input = [int(c) for c in "03036732577212944063491565474664"]
pattern = (0, 1, 0, -1)


def part1():
    # part 1
    last_phase = puzzle_input
    next_phase = list(puzzle_input)
    for phase_num in range(100):
        for i, _ in enumerate(last_phase):
            repetitions = i + 1
            s = cycle(chain(*(repeat(v, repetitions) for v in pattern)))
            next(s)
            next_phase[i] = abs(sum(a * b for a, b in zip(last_phase, s))) % 10

        # asserts for part 2
        assert next_phase[-1] == abs(last_phase[-1]) % 10
        for i in range(2, 200):
            assert next_phase[-i] == abs(last_phase[-i] + next_phase[-i + 1]) % 10
        last_phase = tuple(next_phase)

    return "".join(map(str, next_phase[:8]))


print("Part 1:", part1())


# part 2
# Wrong idea: number of +1 and -1 in periodic input
# count the number of times each number appears as +1 and -1, using modular stuff
# To have a map to apply to full input
# That was useless, true key idea, discard stuff in list of 0s, the rest appears only as 1
# So just ignore stuff before offset and gg


def part2():
    input_repetitions = 10000
    period = len(puzzle_input)
    total_length = input_repetitions * period
    skip = int("".join(map(str, puzzle_input[:7])))
    # assert most stuff is skipped
    assert total_length > skip > total_length / 2 + 10000

    repetitions_after_skip = (total_length - skip) // period

    # dumbest possible solution, 0.5s with pypy 25s with cpython
    last_phase = puzzle_input * (repetitions_after_skip + 1)
    next_phase = list(last_phase)
    for _phase_num in range(100):
        for i in range(2, len(next_phase)):
            next_phase[-i] = abs(next_phase[-i] + next_phase[-i + 1]) % 10

    s = "".join(map(str, next_phase))
    offset = skip % period
    return s[offset : offset + 8]


print("Part 2:", part2())
