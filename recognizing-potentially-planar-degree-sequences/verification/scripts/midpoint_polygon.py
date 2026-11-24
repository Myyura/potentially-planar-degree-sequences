"""Count the three midpoint-example degree profiles on a cyclically labelled 12-gon."""

from collections import Counter
from functools import cache


@cache
def degree_vectors(vertices):
    """Degree vectors, in boundary order, counted once per rooted-edge triangulation."""
    if vertices == 2:
        return [(1, 1)]  # The edge is already present in a subpolygon.
    vectors = []
    for apex in range(1, vertices - 1):
        for left in degree_vectors(apex + 1):
            for right in degree_vectors(vertices - apex):
                # The base completes the root triangle. The halves meet only at the apex.
                vectors.append((left[0] + 1, *left[1:-1], left[-1] + right[0],
                                *right[1:-1], right[-1] + 1))
    return vectors


if __name__ == "__main__":
    counts = Counter(tuple(sorted(d)) for d in degree_vectors(12))
    targets = [(6, 6, *([4] * 5), *([2] * 5)),
               (8, *([4] * 6), *([2] * 5)),
               (7, 5, *([4] * 5), *([2] * 5))]
    observed = [counts[tuple(sorted(d))] for d in targets]
    assert sum(counts.values()) == 16796 and observed == [36, 12, 0]
    print("labelled triangulations:", sum(counts.values()), "profiles:", observed)
