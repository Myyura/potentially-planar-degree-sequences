"""Search for planar realizations up to a given order and compare with the classification."""

from argparse import ArgumentParser
from collections import defaultdict
from itertools import combinations_with_replacement, product
from pathlib import Path
from runpy import run_path

import networkx as nx


def admits_planar_realization(degrees):
    order = len(degrees)
    neighbors = [set() for _ in degrees]
    remaining = list(degrees)

    def complete(vertex):
        while vertex < order and remaining[vertex] == 0:
            vertex += 1
        if vertex == order:
            graph = nx.from_dict_of_lists(dict(enumerate(neighbors)))
            return nx.check_planarity(graph)[0]

        # Future vertices with identical past neighborhoods and residual
        # degrees can be exchanged without changing any completion.
        groups = defaultdict(list)
        for other in range(vertex + 1, order):
            if remaining[other]:
                groups[remaining[other], frozenset(neighbors[other])].append(other)
        blocks = list(groups.values())
        demand = remaining[vertex]
        if demand > sum(map(len, blocks)):
            return False
        choices = [range(min(demand, len(block)) + 1) for block in blocks]
        for counts in product(*choices):
            if sum(counts) != demand:
                continue
            selected = [v for block, count in zip(blocks, counts) for v in block[:count]]
            for v in selected:
                neighbors[vertex].add(v)
                neighbors[v].add(vertex)
                remaining[v] -= 1
            if nx.is_graphical(remaining[vertex + 1 :], method="eg") and complete(vertex + 1):
                return True
            for v in selected:
                remaining[v] += 1
                neighbors[v].remove(vertex)
                neighbors[vertex].remove(v)
        return False

    return complete(0)


def main():
    parser = ArgumentParser(description=__doc__)
    parser.add_argument("--max-order", type=int, default=9, help="largest order to check (default: 9)")
    args = parser.parse_args()
    if args.max_order < 1:
        parser.error("--max-order must be positive")
    classification = Path(__file__).with_name("check_atlas.py")
    upper_exception = run_path(str(classification))["upper_exception"]
    counts = {"lower": [0, 0], "upper": [0, 0]}
    for order in range(2, args.max_order + 1):
        for entries in combinations_with_replacement(range(1, order), order):
            degrees = entries[::-1]
            leaves = degrees.count(1)
            offset = sum(degrees) + 2 * leaves - 4 * order
            if offset > 0 or not nx.is_graphical(degrees, method="eg"):
                continue
            # Compute the truth value before consulting the manuscript's list.
            planar = admits_planar_realization(degrees)
            level = "upper" if offset == 0 else "lower"
            exception = upper_exception(degrees, leaves) if offset == 0 else degrees == (4, 4, 4, 4, 4, 2)
            if planar == exception:
                raise AssertionError(f"Classification mismatch for {degrees}")
            counts[level][0 if planar else 1] += 1
    print(f"NetworkX {nx.__version__}")
    for level, (positive, negative) in counts.items():
        print(f"{level}: {positive} planaric, {negative} nonplanaric")


if __name__ == "__main__":
    main()
