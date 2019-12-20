class Processor:
    def __init__(self, start_mem, verbose=False):
        self.operations = {
            1: (self.add_to, 3),
            2: (self.mul_to, 3),
            3: (self.take_input, 1),
            4: (self.print_output, 1),
            5: (self.jump_if_true, 2),
            6: (self.jump_if_false, 2),
            7: (self.less_then, 3),
            8: (self.equals, 3),
            9: (self.adjust_relative_base, 1),
            99: (self.halt, 0),
        }
        self.mem = list(start_mem) + [0] * (100000)
        self.registers = {
            "ip": 0,
            "rb": 0,
            "running": True,
            "output": None,
            "input": None,
        }
        self.verbose = verbose

    def apply_mode(self, param, mode):
        if mode == 0:
            return self.mem[param]
        elif mode == 1:
            return param
        elif mode == 2:
            return self.mem[self.registers["rb"] + param]

    def apply_dest_mode(self, param, mode):
        assert mode in (0, 2)
        if mode == 0:
            return param
        return self.registers["rb"] + param

    def apply_modes(self, params, modes):
        return [self.apply_mode(param, mode) for param, mode in zip(params, modes)]

    def adjust_relative_base(self, val1, mode):
        val1 = self.apply_mode(val1, mode)
        self.registers["rb"] += val1

    def jump_if_true(self, parameter: int, location: int, *modes):
        parameter, location = self.apply_modes((parameter, location), modes)
        if parameter != 0:
            self.registers["ip"] = location

    def jump_if_false(self, parameter: int, location: int, *modes):
        parameter, location = self.apply_modes((parameter, location), modes)
        if parameter == 0:
            self.registers["ip"] = location

    def less_then(self, val1: int, val2: int, val3: int, *modes):
        val1, val2 = self.apply_modes((val1, val2), modes)
        val3 = self.apply_dest_mode(val3, modes[2])
        self.mem[val3] = int(val1 < val2)

    def equals(self, val1: int, val2: int, val3: int, *modes):
        val1, val2 = self.apply_modes((val1, val2), modes)
        val3 = self.apply_dest_mode(val3, modes[2])
        self.mem[val3] = int(val1 == val2)

    def add_to(self, val1: int, val2: int, dest: int, *modes):
        val1, val2 = self.apply_modes((val1, val2), modes)
        dest = self.apply_dest_mode(dest, modes[2])
        self.mem[dest] = val1 + val2

    def mul_to(self, val1: int, val2: int, dest: int, *modes):
        val1, val2 = self.apply_modes((val1, val2), modes)
        dest = self.apply_dest_mode(dest, modes[2])
        self.mem[dest] = val1 * val2

    def take_input(self, dest: int, mode: int):
        dest = self.apply_dest_mode(dest, mode)
        self.registers["input"] = dest

    def print_output(self, source: int, mode: int):
        source = self.apply_mode(source, mode)
        self.registers["output"] = source

    def halt(self):
        self.registers["running"] = False

    def run(self):
        while self.registers["running"]:
            ip = self.registers["ip"]
            if self.verbose:
                print(f"{ip} {self.mem[ip]}")
            mode, opcode = self.mem[ip] // 100, self.mem[ip] % 100
            op, arg_num = self.operations[opcode]
            modes = []
            for _ in range(5):
                modes.append(mode % 10)
                mode //= 10

            args = self.mem[ip + 1 : ip + arg_num + 1]
            self.registers["ip"] += arg_num + 1
            if self.verbose:
                print(f"{opcode} {args} {modes[:arg_num]}")
            op(*args, *modes[:arg_num])
            if self.registers["output"] is not None:
                yield self.registers["output"]
                self.registers["output"] = None
            if self.registers["input"] is not None:
                self.mem[self.registers["input"]] = yield "input"
                self.registers["input"] = None


if __name__ == "__main__":
    puzzle_input = """1102,34463338,34463338,63,1007,63,34463338,63,1005,63,53,1101,0,3,1000,109,988,209,12,9,1000,209,6,209,3,203,0,1008,1000,1,63,1005,63,65,1008,1000,2,63,1005,63,902,1008,1000,0,63,1005,63,58,4,25,104,0,99,4,0,104,0,99,4,17,104,0,99,0,0,1102,32,1,1019,1101,0,500,1023,1101,0,636,1025,1102,36,1,1010,1101,0,29,1013,1102,864,1,1029,1102,21,1,1000,1102,1,507,1022,1102,1,28,1011,1102,38,1,1008,1101,0,35,1004,1101,25,0,1018,1102,24,1,1005,1102,30,1,1009,1102,1,869,1028,1101,0,37,1007,1102,1,23,1017,1102,1,20,1015,1102,1,22,1003,1101,0,39,1001,1102,1,31,1012,1101,701,0,1026,1101,0,641,1024,1101,0,34,1016,1102,1,0,1020,1102,698,1,1027,1102,33,1,1002,1102,26,1,1006,1101,0,1,1021,1101,0,27,1014,109,12,21101,40,0,0,1008,1012,40,63,1005,63,203,4,187,1105,1,207,1001,64,1,64,1002,64,2,64,109,-11,1207,7,37,63,1005,63,223,1105,1,229,4,213,1001,64,1,64,1002,64,2,64,109,14,1206,5,247,4,235,1001,64,1,64,1105,1,247,1002,64,2,64,109,-2,1207,-4,31,63,1005,63,269,4,253,1001,64,1,64,1105,1,269,1002,64,2,64,109,-6,1208,-5,35,63,1005,63,289,1001,64,1,64,1106,0,291,4,275,1002,64,2,64,109,9,21108,41,39,-1,1005,1015,311,1001,64,1,64,1105,1,313,4,297,1002,64,2,64,109,-5,2101,0,-9,63,1008,63,33,63,1005,63,339,4,319,1001,64,1,64,1106,0,339,1002,64,2,64,1205,10,351,4,343,1106,0,355,1001,64,1,64,1002,64,2,64,109,-18,2108,35,9,63,1005,63,375,1001,64,1,64,1105,1,377,4,361,1002,64,2,64,109,18,1205,9,389,1105,1,395,4,383,1001,64,1,64,1002,64,2,64,109,7,21107,42,41,-8,1005,1010,415,1001,64,1,64,1106,0,417,4,401,1002,64,2,64,109,-12,2102,1,0,63,1008,63,29,63,1005,63,437,1106,0,443,4,423,1001,64,1,64,1002,64,2,64,109,3,1208,0,30,63,1005,63,461,4,449,1105,1,465,1001,64,1,64,1002,64,2,64,109,5,1202,-5,1,63,1008,63,31,63,1005,63,489,1001,64,1,64,1106,0,491,4,471,1002,64,2,64,109,15,2105,1,-6,1001,64,1,64,1106,0,509,4,497,1002,64,2,64,109,-10,1206,2,525,1001,64,1,64,1106,0,527,4,515,1002,64,2,64,109,-18,1202,0,1,63,1008,63,39,63,1005,63,553,4,533,1001,64,1,64,1106,0,553,1002,64,2,64,109,1,2107,21,1,63,1005,63,571,4,559,1105,1,575,1001,64,1,64,1002,64,2,64,109,7,2102,1,-8,63,1008,63,39,63,1005,63,601,4,581,1001,64,1,64,1105,1,601,1002,64,2,64,109,2,1201,-7,0,63,1008,63,35,63,1005,63,623,4,607,1106,0,627,1001,64,1,64,1002,64,2,64,109,20,2105,1,-7,4,633,1106,0,645,1001,64,1,64,1002,64,2,64,109,-16,21107,43,44,-4,1005,1011,663,4,651,1105,1,667,1001,64,1,64,1002,64,2,64,109,-11,2107,36,0,63,1005,63,687,1001,64,1,64,1106,0,689,4,673,1002,64,2,64,109,19,2106,0,4,1106,0,707,4,695,1001,64,1,64,1002,64,2,64,109,-14,21108,44,44,6,1005,1015,725,4,713,1105,1,729,1001,64,1,64,1002,64,2,64,109,1,1201,-6,0,63,1008,63,36,63,1005,63,749,1106,0,755,4,735,1001,64,1,64,1002,64,2,64,109,-1,21101,45,0,10,1008,1019,42,63,1005,63,775,1105,1,781,4,761,1001,64,1,64,1002,64,2,64,109,16,21102,46,1,-7,1008,1018,44,63,1005,63,801,1105,1,807,4,787,1001,64,1,64,1002,64,2,64,109,-3,21102,47,1,-4,1008,1018,47,63,1005,63,833,4,813,1001,64,1,64,1105,1,833,1002,64,2,64,109,-14,2108,38,0,63,1005,63,851,4,839,1105,1,855,1001,64,1,64,1002,64,2,64,109,17,2106,0,3,4,861,1106,0,873,1001,64,1,64,1002,64,2,64,109,-31,2101,0,10,63,1008,63,36,63,1005,63,897,1001,64,1,64,1106,0,899,4,879,4,64,99,21101,0,27,1,21101,0,913,0,1106,0,920,21201,1,53612,1,204,1,99,109,3,1207,-2,3,63,1005,63,962,21201,-2,-1,1,21102,940,1,0,1106,0,920,21202,1,1,-1,21201,-2,-3,1,21101,955,0,0,1106,0,920,22201,1,-1,-2,1105,1,966,21201,-2,0,-2,109,-3,2106,0,0"""
    init_mem = puzzle_input.split(",")
    amp = Processor(map(int, init_mem))
    amp_gen = amp.run()
    first_output = next(amp_gen)
    assert first_output == "input"
    print(amp_gen.send(1))

    amp = Processor(map(int, init_mem))
    amp_gen = amp.run()
    first_output = next(amp_gen)
    assert first_output == "input"
    print(amp_gen.send(2))
