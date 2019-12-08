# Should have used numpy reshape ...
from collections import Counter

with open("day8.txt", "r") as input_file:
    digits = input_file.read().strip()

width = 25
height = 6
layer_size = width * height
layer_counts = []
layers = []
for layer_start in range(0, len(digits), layer_size):
    layer = digits[layer_start : layer_start + layer_size]
    layer_counts.append(Counter(layer))
    layers.append(layer)


def checksum(layer_count):
    return layer_count["1"] * layer_count["2"]


print(checksum(min(layer_counts, key=lambda x: x["0"])))


def color(p):
    for layer in layers:
        if layer[p] != "2":
            return layer[p] if layer[p] == "1" else " "
    return "·"


merged = [color(p) for p in range(layer_size)]
print("\n".join("".join(merged[r : r + width]) for r in range(0, layer_size, width)))
