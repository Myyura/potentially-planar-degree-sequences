"""Find missing integer midpoints of sorted degree lists of sphere triangulations."""

import argparse
import subprocess
from collections import defaultdict
from itertools import combinations


def census(plantri, order):
    maps = subprocess.run([plantri, "-a", str(order)], capture_output=True,
                          text=True, check=True).stdout.splitlines()
    profiles = set()
    for line in maps:
        size, adjacency = line.split()
        degrees = tuple(sorted((len(row) for row in adjacency.split(",")), reverse=True))
        assert int(size) == len(degrees) == order and sum(degrees) == 6 * order - 12
        profiles.add(degrees)
    by_parity = defaultdict(list)
    for degrees in sorted(profiles):
        by_parity[tuple(d % 2 for d in degrees)].append(degrees)
    missing = []
    for group in by_parity.values():
        for left, right in combinations(group, 2):
            midpoint = tuple((x + y) // 2 for x, y in zip(left, right))
            if midpoint not in profiles:
                # The midpoint is already sorted. Check that it is graphic by
                # the Erdős–Gallai inequalities, as required in the proposition.
                assert sum(midpoint) == 6 * order - 12
                for k in range(1, order + 1):
                    bound = k * (k - 1) + sum(min(d, k) for d in midpoint[k:])
                    assert sum(midpoint[:k]) <= bound, midpoint
                missing.append((left, right, midpoint))
    return len(maps), len(profiles), missing


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--plantri", required=True, help="standard plantri executable")
    args = parser.parse_args()
    print("n  triangulations  degree_profiles  missing_pairs  missing_midpoints")
    for order in range(4, 14):
        count, size, missing = census(args.plantri, order)
        distinct = len({mid for _, _, mid in missing})
        print(order, count, size, len(missing), distinct)
        if order < 13:
            assert not missing
        else:
            example = ((12, 7, 7) + (5,) * 5 + (3,) * 5,
                       (12, 9) + (5,) * 6 + (3,) * 5,
                       (12, 8, 6) + (5,) * 5 + (3,) * 5)
            assert (count, size, len(missing), distinct) == (49566, 947, 5, 5)
            assert example in missing
            for left, right, midpoint in sorted(missing):
                print(left, right, midpoint)
