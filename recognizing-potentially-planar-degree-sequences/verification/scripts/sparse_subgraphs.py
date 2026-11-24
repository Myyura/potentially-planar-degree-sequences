"""Check the two sparse layers for every positive graphic list of orders 2 through 10.

Every simple planar graph of order at least three extends on its own vertices
to a triangulation. The C++ helper enumerates its spanning subgraphs, allowing
disconnected graphs. A separate Havel–Hakimi test selects the graphic inputs.

From this directory, with Python 3, a C++17 compiler and plantri installed, run
    python3 sparse_subgraphs.py --plantri /path/to/plantri
The helper is compiled in a temporary directory. To reuse your own binary, run
    c++ -O3 -std=c++17 sparse_subgraphs.cpp -o /tmp/sparse_subgraphs
    python3 sparse_subgraphs.py --enumerator /tmp/sparse_subgraphs
Use --max-order 8 for a shorter run. At order at most 10 the expected totals
are 866 planar and 200 excluded on the upper layer, 901 planar and 1 excluded
on the lower layer.
"""
import argparse
from itertools import combinations_with_replacement
from pathlib import Path
import subprocess
from tempfile import TemporaryDirectory


TRIANGULATIONS = {4: 1, 5: 1, 6: 2, 7: 5, 8: 14, 9: 50, 10: 233}


def maximal_hosts(order, plantri):
    if order == 2:
        return "2 b,a\n"
    if order == 3:
        return "3 bc,ca,ab\n"
    hosts = subprocess.check_output([plantri, "-a", str(order)], text=True)
    if len(hosts.splitlines()) != TRIANGULATIONS[order]:
        raise ValueError(f"Unexpected number of triangulations at order {order}")
    return hosts


def is_graphic(degrees):
    row = list(degrees)
    while row and row[0]:
        demand = row.pop(0)
        if demand > len(row) or row[demand - 1] == 0:
            return False
        row[:demand] = [value - 1 for value in row[:demand]]
        row.sort(reverse=True)
    return True


def is_exception(degrees, leaves, delta):
    if delta == 2:
        return degrees == (4, 4, 4, 4, 4, 2)
    core = sum(value >= 3 for value in degrees)
    if core == 5 or (core == 6 and degrees.count(3) == 3):
        return True
    families = (
        (leaves + 5, 4, 4, 4, 4, 3),
        (leaves + 6, 4, 4, 4, 4, 4, 2),
        (leaves + 6, 5, 5, 3, 3, 3, 3),
    )
    sporadic = {(5, 5, 5, 5, 5, 3, 2, 2), (4,) * 7, (6, 6, 6, 3, 3, 3, 3, 2)}
    return degrees in sporadic or any(degrees == seed + (1,) * leaves for seed in families)


def check_order(order, hosts, enumerator):
    output = subprocess.check_output([enumerator], input=hosts, text=True)
    found = {int(key) for key in output.splitlines()}
    counts = [0] * 4
    for ascending in combinations_with_replacement(range(1, order), order):
        degrees = ascending[::-1]
        leaves = degrees.count(1)
        delta = 4 * order - 2 * leaves - sum(degrees)
        if delta not in (0, 2) or not is_graphic(degrees):
            continue
        histogram = sum(1 << (4 * value) for value in degrees)
        realized = histogram in found
        excluded = is_exception(degrees, leaves, delta)
        if realized == excluded:
            raise ValueError(f"Mismatch at delta={delta} for {degrees}: planar={realized}")
        found.discard(histogram)
        counts[delta + int(excluded)] += 1
    if found:
        raise ValueError(f"{len(found)} unmatched histograms at order {order}")
    return counts


def main():
    parser = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    parser.add_argument("--plantri", default="plantri", help="plantri executable")
    parser.add_argument("--enumerator", type=Path, help="precompiled C++ helper")
    parser.add_argument("--max-order", type=int, default=10, choices=range(2, 11))
    args = parser.parse_args()
    with TemporaryDirectory() as temp:
        if args.enumerator is None:
            enumerator = Path(temp) / "sparse_subgraphs"
            source = Path(__file__).with_suffix(".cpp")
            subprocess.run(["c++", "-O3", "-std=c++17", source, "-o", enumerator], check=True)
        else:
            enumerator = args.enumerator.resolve()
        totals = [0] * 4
        print("order  upper-planar upper-excluded lower-planar lower-excluded", flush=True)
        for order in range(2, args.max_order + 1):
            counts = check_order(order, maximal_hosts(order, args.plantri), enumerator)
            print(order, *counts, flush=True)
            totals = [a + b for a, b in zip(totals, counts)]
        print("total", *totals)
        if args.max_order == 10 and totals != [866, 200, 901, 1]:
            raise ValueError(f"Unexpected ten-vertex totals: {totals}")


if __name__ == "__main__":
    main()
