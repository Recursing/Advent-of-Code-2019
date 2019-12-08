from collections import defaultdict, deque

with open("day6.txt", "r") as input_file:
    lines = input_file.readlines()

orbits = defaultdict(list)
for parent, child in (line.strip().split(")") for line in lines):
    orbits[parent].append(child)


def weight(node, level=0):
    return level + sum(weight(child, level + 1) for child in orbits[node])


print(weight("COM"))


# Got lazy for part2, bidirectional BFS would be faster
# (or dijkstra, depending on sparsity)
graph = defaultdict(list)
for parent, children in orbits.items():
    graph[parent].extend(children)
    for child in children:
        graph[child].append(parent)

start = graph["YOU"][0]
destination = graph["SAN"][0]

queue = deque([start])
distances = {start: 0}
while queue:
    current = queue.popleft()
    neighbours = graph[current]
    for n in neighbours:
        if n == destination:
            print(distances[current] + 1)
            queue = deque()
            break
        if n not in distances:
            queue.append(n)
            distances[n] = distances[current] + 1
