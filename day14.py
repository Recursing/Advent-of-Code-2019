from math import ceil

with open("day14.txt", "r") as input_file:
    puzzle_input = [line.strip() for line in input_file.readlines()]


def parse_line(line: str):
    input_string, output_string = line.split(" => ")

    def parse_pair(pair_string: str):
        quantity, name = pair_string.split()
        return name, int(quantity)

    outputs = parse_pair(output_string)
    inputs = tuple(map(parse_pair, input_string.split(", ")))
    return (outputs, inputs)


def parse_recipes(input_lines):
    recipes = {}

    for line in input_lines:
        outputs, inputs = parse_line(line)
        assert outputs[0] not in recipes
        recipes[outputs[0]] = (outputs[1], inputs)

    return recipes


def simplify_element(chemical, quantity, shopping_cart, left_overs, recipes):
    recycled = min(left_overs[chemical], quantity)
    quantity -= recycled
    left_overs[chemical] -= recycled
    output_quantity, inputs = recipes[chemical]
    reaction_number = ceil(quantity / output_quantity)
    for required_chemical, required_quantity in inputs:
        shopping_cart[required_chemical] += required_quantity * reaction_number
    left_overs[chemical] += reaction_number * output_quantity - quantity


def simplify_cart(shopping_cart, left_overs, recipes):
    to_simplify = [(ch, q) for ch, q in shopping_cart.items() if q and ch != "ORE"]
    for ch, _ in to_simplify:
        shopping_cart[ch] = 0
    for chemical, quantity in to_simplify:
        simplify_element(chemical, quantity, shopping_cart, left_overs, recipes)


def solve(recipes, fuel_required=1):
    shopping_cart = {chemical: 0 for chemical in recipes}
    shopping_cart["ORE"] = 0
    left_overs = {chemical: 0 for chemical in recipes}
    shopping_cart["FUEL"] = fuel_required
    while any(
        quantity for chemical, quantity in shopping_cart.items() if chemical != "ORE"
    ):
        """print({k: v for k, v in shopping_cart.items() if v})
        print({k: v for k, v in left_overs.items() if v})
        print()"""
        simplify_cart(shopping_cart, left_overs, recipes)

    return shopping_cart["ORE"]


if __name__ == "__main__":
    # part 1
    recipes = parse_recipes(puzzle_input)
    print(solve(recipes, 1))

    # part 2
    TRILLION = 1000000000000

    def bisect(recipes, goal=TRILLION):
        lower, upper = 1, goal

        while upper - lower > 1:
            middle = (lower + upper) // 2
            ore = solve(recipes, middle)
            if ore > goal:
                upper = middle
            else:
                lower = middle
        return lower

    print(bisect(recipes, goal=TRILLION))


tests = {
    """10 ORE => 10 A
1 ORE => 1 B
7 A, 1 B => 1 C
7 A, 1 C => 1 D
7 A, 1 D => 1 E
7 A, 1 E => 1 FUEL""": 31,
    """9 ORE => 2 A
8 ORE => 3 B
7 ORE => 5 C
3 A, 4 B => 1 AB
5 B, 7 C => 1 BC
4 C, 1 A => 1 CA
2 AB, 3 BC, 4 CA => 1 FUEL""": 165,
    """157 ORE => 5 NZVS
165 ORE => 6 DCFZ
44 XJWVT, 5 KHKGT, 1 QDVJ, 29 NZVS, 9 GPVTF, 48 HKGWZ => 1 FUEL
12 HKGWZ, 1 GPVTF, 8 PSHF => 9 QDVJ
179 ORE => 7 PSHF
177 ORE => 5 HKGWZ
7 DCFZ, 7 PSHF => 2 XJWVT
165 ORE => 2 GPVTF
3 DCFZ, 7 NZVS, 5 HKGWZ, 10 PSHF => 8 KHKGT""": 13312,
    """2 VPVL, 7 FWMGM, 2 CXFTF, 11 MNCFX => 1 STKFG
17 NVRVD, 3 JNWZP => 8 VPVL
53 STKFG, 6 MNCFX, 46 VJHF, 81 HVMC, 68 CXFTF, 25 GNMV => 1 FUEL
22 VJHF, 37 MNCFX => 5 FWMGM
139 ORE => 4 NVRVD
144 ORE => 7 JNWZP
5 MNCFX, 7 RFSQX, 2 FWMGM, 2 VPVL, 19 CXFTF => 3 HVMC
5 VJHF, 7 MNCFX, 9 VPVL, 37 CXFTF => 6 GNMV
145 ORE => 6 MNCFX
1 NVRVD => 8 CXFTF
1 VJHF, 6 MNCFX => 4 RFSQX
176 ORE => 6 VJHF""": 180697,
    """171 ORE => 8 CNZTR
7 ZLQW, 3 BMBT, 9 XCVML, 26 XMNCP, 1 WPTQ, 2 MZWV, 1 RJRHP => 4 PLWSL
114 ORE => 4 BHXH
14 VRPVC => 6 BMBT
6 BHXH, 18 KTJDG, 12 WPTQ, 7 PLWSL, 31 FHTLT, 37 ZDVW => 1 FUEL
6 WPTQ, 2 BMBT, 8 ZLQW, 18 KTJDG, 1 XMNCP, 6 MZWV, 1 RJRHP => 6 FHTLT
15 XDBXC, 2 LTCX, 1 VRPVC => 6 ZLQW
13 WPTQ, 10 LTCX, 3 RJRHP, 14 XMNCP, 2 MZWV, 1 ZLQW => 1 ZDVW
5 BMBT => 4 WPTQ
189 ORE => 9 KTJDG
1 MZWV, 17 XDBXC, 3 XCVML => 2 XMNCP
12 VRPVC, 27 CNZTR => 2 XDBXC
15 KTJDG, 12 BHXH => 5 XCVML
3 BHXH, 2 VRPVC => 7 MZWV
121 ORE => 7 VRPVC
7 XCVML => 6 RJRHP
5 BHXH, 4 VRPVC => 5 LTCX""": 2210736,
}


def test():
    for test_input, test_output in tests.items():
        recipes = parse_recipes(test_input.splitlines())
        assert solve(recipes, 1) == test_output

    tests_2 = {13312: 82892753, 180697: 5586022, 2210736: 460664}
    for test1_output, test2_output in tests_2.items():
        test_input = next(
            t_input for t_input, t_output in tests.items() if t_output == test1_output
        )
        recipes = parse_recipes(test_input.splitlines())
        assert bisect(recipes, goal=TRILLION) == test2_output
    return True


if __name__ == "__main__":
    if test():
        print("Tests passed")
