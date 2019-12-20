from itertools import permutations, cycle


class Processor:
    def __init__(self, start_mem):
        self.operations = {
            1: (self.add_to, 3),
            2: (self.mul_to, 3),
            3: (self.take_input, 1),
            4: (self.print_output, 1),
            5: (self.jump_if_true, 2),
            6: (self.jump_if_false, 2),
            7: (self.less_then, 3),
            8: (self.equals, 3),
            99: (self.halt, 0),
        }
        self.mem = list(start_mem) + [0] * 100000
        self.registers = {"ip": 0, "running": True, "output": None, "input": None}

    def apply_modes(self, params, modes):
        return [[self.mem[param], param][mode] for param, mode in zip(params, modes)]

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
        self.mem[val3] = int(val1 < val2)

    def equals(self, val1: int, val2: int, val3: int, *modes):
        val1, val2 = self.apply_modes((val1, val2), modes)
        self.mem[val3] = int(val1 == val2)

    def add_to(self, val1: int, val2: int, dest: int, *modes):
        val1, val2 = self.apply_modes((val1, val2), modes)
        self.mem[dest] = val1 + val2

    def mul_to(self, val1: int, val2: int, dest: int, *modes):
        val1, val2 = self.apply_modes((val1, val2), modes)
        self.mem[dest] = val1 * val2

    def take_input(self, dest: int, mode: int):
        self.registers["input"] = dest

    def print_output(self, source: int, mode: int):
        if mode == 1:
            self.registers["output"] = source
        else:
            self.registers["output"] = self.mem[source]

    def halt(self):
        self.registers["running"] = False

    def run(self):
        while self.registers["running"]:
            ip = self.registers["ip"]
            mode, opcode = self.mem[ip] // 100, self.mem[ip] % 100
            op, arg_num = self.operations[opcode]
            modes = list(map(int, reversed(f"{mode:0>5}")))
            args = self.mem[ip + 1 : ip + arg_num + 1]
            self.registers["ip"] += arg_num + 1
            op(*args, *modes[:arg_num])
            if self.registers["output"]:
                yield self.registers["output"]
                self.registers["output"] = None
            if self.registers["input"]:
                self.mem[self.registers["input"]] = yield "input"
                self.registers["input"] = None


puzzle_input = """3,8,1001,8,10,8,105,1,0,0,21,38,63,72,81,106,187,268,349,430,99999,3,9,101,5,9,9,1002,9,3,9,101,3,9,9,4,9,99,3,9,102,3,9,9,101,4,9,9,1002,9,2,9,1001,9,2,9,1002,9,4,9,4,9,99,3,9,1001,9,3,9,4,9,99,3,9,102,5,9,9,4,9,99,3,9,102,4,9,9,1001,9,2,9,1002,9,5,9,1001,9,2,9,102,3,9,9,4,9,99,3,9,1001,9,2,9,4,9,3,9,1002,9,2,9,4,9,3,9,1002,9,2,9,4,9,3,9,101,2,9,9,4,9,3,9,102,2,9,9,4,9,3,9,101,2,9,9,4,9,3,9,1001,9,1,9,4,9,3,9,101,1,9,9,4,9,3,9,102,2,9,9,4,9,3,9,101,2,9,9,4,9,99,3,9,1001,9,2,9,4,9,3,9,1001,9,1,9,4,9,3,9,101,1,9,9,4,9,3,9,102,2,9,9,4,9,3,9,1002,9,2,9,4,9,3,9,1001,9,1,9,4,9,3,9,1001,9,1,9,4,9,3,9,101,2,9,9,4,9,3,9,101,1,9,9,4,9,3,9,1001,9,1,9,4,9,99,3,9,102,2,9,9,4,9,3,9,1001,9,2,9,4,9,3,9,1002,9,2,9,4,9,3,9,101,2,9,9,4,9,3,9,1001,9,1,9,4,9,3,9,1002,9,2,9,4,9,3,9,101,2,9,9,4,9,3,9,102,2,9,9,4,9,3,9,1002,9,2,9,4,9,3,9,101,2,9,9,4,9,99,3,9,1002,9,2,9,4,9,3,9,1002,9,2,9,4,9,3,9,1001,9,1,9,4,9,3,9,1001,9,1,9,4,9,3,9,101,2,9,9,4,9,3,9,101,1,9,9,4,9,3,9,101,1,9,9,4,9,3,9,1001,9,1,9,4,9,3,9,1002,9,2,9,4,9,3,9,1002,9,2,9,4,9,99,3,9,102,2,9,9,4,9,3,9,101,1,9,9,4,9,3,9,101,1,9,9,4,9,3,9,1002,9,2,9,4,9,3,9,101,1,9,9,4,9,3,9,102,2,9,9,4,9,3,9,1001,9,1,9,4,9,3,9,1001,9,1,9,4,9,3,9,102,2,9,9,4,9,3,9,101,2,9,9,4,9,99"""


def run_amp_once(amp, input_signal, phase):
    inputs = [input_signal, phase]
    gen = amp.run()
    for output in gen:
        while output == "input":
            try:
                output = gen.send(inputs.pop())
            except StopIteration:
                return -1
        return output


def get_first_signal(phases):
    last_value = 0
    amplifiers = [Processor(map(int, init_mem)) for _ in range(5)]
    for amp, phase in zip(amplifiers, phases):
        last_value = run_amp_once(amp, last_value, phase)
    return last_value


init_mem = puzzle_input.split(",")
phase_sequences = permutations(range(5))
print(max(get_first_signal(phases) for phases in phase_sequences))


def get_second_signal(phases):
    last_value = 0
    amplifiers = [Processor(map(int, init_mem)) for _ in range(5)]
    amp_gens = []
    for amp, phase in zip(amplifiers, phases):
        amp_gen = amp.run()
        assert next(amp_gen) == "input"
        first_output = amp_gen.send(phase)
        assert first_output == "input"
        amp_gens.append(amp_gen)

    ampE = amp_gens[-1]
    last_value, last_e = 0, 0
    for amp in cycle(amp_gens):
        try:
            last_output = amp.send(last_value)
            while last_output == "input":
                last_output = amp.send(last_value)
            assert last_output != "input"
            last_value = last_output
            if amp is ampE:
                last_e = last_value
        except StopIteration:
            return last_e

    return last_value


phase_sequences = permutations(range(5, 10))
print(max(get_second_signal(phases) for phases in phase_sequences))
