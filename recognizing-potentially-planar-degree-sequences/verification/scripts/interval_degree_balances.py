"""Test a degree multiset by the interval rule, or compare with the project atlas."""

import argparse
import json
from functools import lru_cache
from itertools import combinations_with_replacement
from pathlib import Path


def next_rows(row, degree):
    for start in range(len(row) + 1):
        before = row[:start]
        yield before + (degree,) + row[start:]
        for length in range(1, min(degree, len(row) - start) + 1):
            end = start + length
            if length >= 3 and row[end - 2] != 1:
                break
            left = (row[start] - 1,) if row[start] > 1 else ()
            right = (row[end - 1] - 1,) if length > 1 and row[end - 1] > 1 else ()
            new = (degree - length,) if degree > length else ()
            after = row[end:]
            yield before + left + new + right + after
            if length == 1 and left and new:
                yield before + new + left + after


def planaric(degrees):
    if any(d < 0 for d in degrees):
        return False
    remaining = tuple(sorted(d for d in degrees if d))
    n = len(remaining)
    if not n:
        return True
    total = sum(remaining)
    if max(remaining) >= n or total % 2 or (n >= 3 and total > 6 * n - 12):
        return False

    @lru_cache(None)
    def search(row, unused):
        if not unused:
            return not row
        active, future = len(row), len(unused)
        pending, supply = sum(row), sum(unused)
        if max(row, default=0) > future or unused[-1] >= active + future:
            return False
        if active and pending - active > 2 * (future - 1):
            return False
        if pending > sum(min(active, d) for d in unused):
            return False
        # The old vertices lie on a common disk boundary. Future edges join
        # no two old vertices. Completing the boundary gives this Euler bound.
        edges = (pending + supply) // 2
        if active >= 2 and edges > 3 * future + active - 3:
            return False
        if active < 2 and active + future >= 3 and edges > 3 * (active + future) - 6:
            return False
        for i, degree in enumerate(unused):
            if i and degree == unused[i - 1]:
                continue
            rest = unused[:i] + unused[i + 1:]
            for updated in next_rows(row, degree):
                if search(min(updated, updated[::-1]), rest):
                    return True
        return False

    result = search((), remaining)
    search.cache_clear()
    return result


def check_atlas():
    assert planaric(()), "the empty graph realizes the empty list"
    path = Path(__file__).resolve().parents[1] / "data" / "atlas_summary.json"
    records = json.loads(path.read_text())["degree_sequence_catalogue"]
    positives = {tuple(sorted(r["sequence"])) for r in records if r["planar_realizations"]}
    checked = 0
    for n in range(1, 8):
        for degrees in combinations_with_replacement(range(n), n):
            if planaric(degrees) != (degrees in positives):
                raise AssertionError(degrees)
            checked += 1
    print(f"{checked} degree multisets through seven vertices agree with the atlas.")


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("degrees", nargs="*", type=int)
    parser.add_argument("--atlas", action="store_true")
    args = parser.parse_args()
    if args.atlas:
        check_atlas()
    else:
        print(planaric(args.degrees))
