"""Optional independent check on the NetworkX atlas of all graphs of order at most seven."""
from collections import defaultdict

import networkx as nx


def upper_exception(degrees, leaves):
    core_size = sum(degree >= 3 for degree in degrees)
    seeds = (
        (leaves + 5, 4, 4, 4, 4, 3),
        (leaves + 6, 4, 4, 4, 4, 4, 2),
        (leaves + 6, 5, 5, 3, 3, 3, 3),
    )
    sporadic = {(5, 5, 5, 5, 5, 3, 2, 2), (4,) * 7, (6, 6, 6, 3, 3, 3, 3, 2)}
    return (
        core_size == 5
        or (core_size == 6 and degrees.count(3) == 3)
        or any(degrees == seed + (1,) * leaves for seed in seeds)
        or degrees in sporadic
    )


def main():
    has_planar_graph = defaultdict(bool)
    for graph in nx.graph_atlas_g():
        degrees = tuple(sorted((d for _, d in graph.degree()), reverse=True))
        if degrees and degrees[-1] > 0:
            has_planar_graph[degrees] |= nx.check_planarity(graph)[0]

    counts = [[0, 0], [0, 0]]
    for degrees, planar in has_planar_graph.items():
        leaves = degrees.count(1)
        level = sum(degrees) + 2 * leaves - 4 * len(degrees)
        if level <= -2:
            group = 0
            forbidden = degrees == (4, 4, 4, 4, 4, 2)
        elif level == 0:
            group = 1
            forbidden = upper_exception(degrees, leaves)
        else:
            continue
        if planar == forbidden:
            raise AssertionError(f"Classification mismatch for {degrees}")
        counts[group][0] += 1
        counts[group][1] += not planar
    print(f"NetworkX {nx.__version__}")
    print("Lower region (graphical, nonplanaric):", *counts[0])
    print("Upper equality (graphical, nonplanaric):", *counts[1])


if __name__ == "__main__":
    main()
