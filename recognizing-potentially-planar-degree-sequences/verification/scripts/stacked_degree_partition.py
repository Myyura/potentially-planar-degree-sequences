"""Degree-multiset recursion for planar 3-trees, with an optional plantri audit."""

from collections import Counter
from functools import lru_cache
from itertools import combinations_with_replacement, product
import argparse
import subprocess


def split_three(degrees):
    """Ordered multiset partitions into three, without distinguishing equal items."""
    blocks = []
    for value, count in Counter(degrees).items():
        blocks.append([((value,) * i, (value,) * j, (value,) * (count - i - j))
                       for i in range(count + 1) for j in range(count - i + 1)])
    for choices in product(*blocks):
        yield tuple(tuple(v for row in choices for v in row[part]) for part in range(3))


@lru_cache(None)
def disk_profiles(degrees):
    """Each output triple counts the interior neighbors of three boundary vertices."""
    if not degrees:
        return frozenset({(0, 0, 0)})
    k = len(degrees)
    boundary_sum = 6 * k - sum(degrees)
    if degrees[0] < 3 or degrees[-1] > k + 2 or not 3 <= boundary_sum <= 3 * k:
        return frozenset()
    profiles = set()
    for center in set(degrees):
        index = degrees.index(center)
        rest = degrees[:index] + degrees[index + 1:]
        for ab, bc, ca in split_three(rest):
            for pa, pb, pc in product(disk_profiles(ab), disk_profiles(bc), disk_profiles(ca)):
                if pa[2] + pb[2] + pc[2] == center - 3:
                    profiles.add((1 + pa[0] + pc[1], 1 + pa[1] + pb[0], 1 + pb[1] + pc[0]))
    return frozenset(profiles)


def is_planar_three_tree(degrees):
    seq = tuple(sorted(degrees))
    n = len(seq)
    if n < 4 or seq[0] < 3 or seq[-1] >= n or sum(seq) != 6 * n - 12:
        return False
    highest = seq[-1]
    for x, y in combinations_with_replacement(sorted(set(seq[:-1])), 2):
        if x == y and seq[:-1].count(x) < 2:
            continue
        inner = list(seq[:-1])
        inner.remove(x)
        inner.remove(y)
        if (x - 2, y - 2, highest - 2) in disk_profiles(tuple(inner)):
            return True
    return False


def peels_to_tetrahedron(graph):
    graph = [set(row) for row in graph]
    remaining = set(range(len(graph)))
    while len(remaining) > 4:
        v = next((i for i in remaining if len(graph[i]) == 3), None)
        if v is None:
            return False
        a, b, c = graph[v]
        if b not in graph[a] or c not in graph[b] or a not in graph[c]:
            return False
        for w in graph[v]:
            graph[w].remove(v)
        remaining.remove(v)
    return all(len(graph[v]) == 3 for v in remaining)


def audit(executable, maximum):
    for n in range(4, maximum + 1):
        maps = subprocess.run([executable, '-a', str(n)], capture_output=True, text=True, check=True)
        observed = set()
        count = 0
        for line in maps.stdout.splitlines():
            _, table = line.split()
            graph = [[ord(c) - ord('a') for c in row] for row in table.split(',')]
            if peels_to_tetrahedron(graph):
                observed.add(tuple(sorted(map(len, graph))))
                count += 1
        candidates = [d for d in combinations_with_replacement(range(3, n), n) if sum(d) == 6 * n - 12]
        computed = {d for d in candidates if is_planar_three_tree(d)}
        assert computed == observed, (n, computed ^ observed)
        print(n, len(maps.stdout.splitlines()), count, len(candidates), len(computed))


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--plantri', help='path to standard plantri for independent audit')
    parser.add_argument('--maximum', type=int, default=10)
    parser.add_argument('degrees', nargs='*', type=int)
    args = parser.parse_args()
    if args.plantri:
        audit(args.plantri, args.maximum)
    else:
        print(is_planar_three_tree(args.degrees))
