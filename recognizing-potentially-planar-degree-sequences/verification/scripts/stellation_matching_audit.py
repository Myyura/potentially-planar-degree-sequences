"""Audit the marked-face layers in the prescribed-edge reduction on small spheres."""
from collections import Counter, defaultdict
from itertools import combinations, permutations


def triangle(a, b, c):
    return tuple(sorted((a, b, c)))


def geometry(faces):
    """Check a connected closed simplicial 2-manifold of Euler characteristic two."""
    neighbors = defaultdict(set)
    opposite = defaultdict(list)
    links = defaultdict(lambda: defaultdict(set))
    for a, b, c in faces:
        assert a < b < c
        for u, v, w in ((a, b, c), (b, c, a), (c, a, b)):
            edge = tuple(sorted((u, v)))
            opposite[edge].append(w)
            neighbors[u].add(v)
            neighbors[v].add(u)
            links[w][u].add(v)
            links[w][v].add(u)
    assert all(len(row) == 2 for row in opposite.values())
    assert len(neighbors) - len(opposite) + len(faces) == 2

    def reaches_all(adjacency):
        start = next(iter(adjacency))
        seen = {start}
        todo = [start]
        while todo:
            for v in adjacency[todo.pop()]:
                if v not in seen:
                    seen.add(v)
                    todo.append(v)
        return len(seen) == len(adjacency)

    assert reaches_all(neighbors)
    for link in links.values():
        assert all(len(row) == 2 for row in link.values()) and reaches_all(link)
    return neighbors, opposite


def stellate(faces, blanks=()):
    blanks = set(blanks)
    assert blanks <= faces
    result = set(blanks)
    centers = {}
    fresh = 1 + max(max(face) for face in faces)
    for face in sorted(faces - blanks):
        a, b, c = face
        centers[face] = fresh
        result.update((triangle(a, b, fresh), triangle(b, c, fresh), triangle(c, a, fresh)))
        fresh += 1
    return result, centers


def peel(current, expected, marked, latest, marker_pool, side_pool):
    """Identify the final generation by degree alone and check restored identities."""
    neighbors, _ = geometry(current)
    removed = {v for v, row in neighbors.items() if len(row) == 3}
    assert len(removed) == 2 * len(expected) - 4 - len(marked) // 3
    assert all(not (neighbors[v] & removed) for v in removed)
    old = set(neighbors) - removed
    assert old == set(expected)
    old_only = {f for f in current if not removed.intersection(f)}
    restored = old_only | {triangle(*neighbors[v]) for v in removed}
    old_neighbors, _ = geometry(restored)
    assert all(neighbors[v] - removed == old_neighbors[v] for v in old)
    for v in old:
        now = len(neighbors[v])
        assert (now + 1) // 2 == len(old_neighbors[v]) == expected[v]
        assert now == 2 * expected[v] - (v in marked)
    omissions = Counter(v for f in old_only for v in f)
    assert omissions == Counter(marked)
    assert all(len(set(f) & group) == 1 for f in old_only
               for group in (latest, marker_pool, side_pool))
    return restored, old_only, removed


def shell(size):
    # A bipyramid supplies size disjoint edges on its equatorial cycle.
    cycle = 2 * size
    original = set(range(cycle + 2))
    base = {triangle(i, (i + 1) % cycle, pole)
            for i in range(cycle) for pole in (cycle, cycle + 1)}
    left = tuple(range(0, cycle, 2))
    right = tuple(range(1, cycle, 2))
    first, _ = stellate(base)
    second, centers = stellate(first)
    marker = tuple(next(s for f, s in centers.items() if l in f and r in f)
                   for l, r in zip(left, right))
    neighbors, _ = geometry(second)
    assert len(set(marker)) == size
    assert all(neighbors[s] & original == {l, r}
               for s, l, r in zip(marker, left, right))
    assert all(not (neighbors[s] & set(marker)) for s in marker)
    third, stars = stellate(second)
    return third, set(stars.values()), marker, left, right


def identities(size):
    full = tuple(range(size))
    bits = (size - 1).bit_length()
    for bit in range(bits):
        for value in (0, 1):
            yield bit, value, tuple(i for i in full if ((i >> bit) & 1) == value)


def rounds(size):
    base, first_latest, marker, left, right = shell(size)
    subsets = list(identities(size))
    full = tuple(range(size))
    checks = max_vertices = 0
    # Every bit and side gets a trial after a full previous test on either side.
    for previous_side in (left, right):
        for side in (left, right):
            for bit, value, selected in subsets:
                current, latest = base, first_latest
                trail = []
                for ids, ends in ((full, previous_side), (selected, side)):
                    neighbors, opposite = geometry(current)
                    assert all(not (neighbors[v] & latest) for v in latest)
                    blanks = set()
                    chosen = set()
                    for i in ids:
                        edge = tuple(sorted((marker[i], ends[i])))
                        options = set(opposite[edge]) & latest
                        assert options
                        v = min(options)
                        assert v not in chosen
                        chosen.add(v)
                        blanks.add(triangle(*edge, v))
                    marked = chosen | {marker[i] for i in ids} | {ends[i] for i in ids}
                    assert len(marked) == 3 * len(ids)
                    next_map, placed = stellate(current, blanks)
                    trail.append((current, marked, latest, set(ends), blanks))
                    current, latest = next_map, set(placed.values())
                    max_vertices = max(max_vertices, 2 + len(current)//2)
                for prior, marked, old_latest, ends, blanks in reversed(trail):
                    old_neighbors, _ = geometry(prior)
                    expected = {v:len(row) for v, row in old_neighbors.items()}
                    restored, actual_blanks, _ = peel(
                        current, expected, marked, old_latest, set(marker), ends)
                    assert restored == prior and actual_blanks == blanks
                    current = restored
                    checks += 1
    return checks, max_vertices


def permutation_check(size):
    """The full tests give two permutations. Check the remaining labeled tests."""
    blocks = [(bit, value, set(sub)) for bit, value, sub in identities(size)]
    full = set(range(size))
    total = survivors = 0
    for perm in permutations(range(size)):
        assert {perm[i] for i in full} == full
        total += 1
        passed = all({perm[i] for i in sub} == sub for _, _, sub in blocks)
        survivors += passed
        assert passed == (perm == tuple(range(size)))
    # Left and right are independent permutations of the designated matching.
    return total * total, survivors * survivors


def crossed_edges():
    size = 6
    current, latest, marker, left, physical_right = shell(size)
    neighbors, opposite = geometry(current)
    # Swap physical edges zero and two, so both requested new edges are absent.
    requested = (physical_right[2], physical_right[1], physical_right[0], *physical_right[3:])
    assert not (requested[0] in neighbors[left[0]] or requested[2] in neighbors[left[2]])
    tests = [(None, None, tuple(range(size))), *identities(size)]
    outcomes = {}
    for bit, value, sub in tests:
        for label, group in (("L", left), ("R", requested)):
            permitted = set(group[i] for i in sub)
            options = {i:{v for v in permitted if v in neighbors[marker[i]]
                          and set(opposite[tuple(sorted((v, marker[i])))]) & latest}
                       for i in sub}
            # There is at most one relevant original neighbor on each side.
            assert all(len(candidates) <= 1 for candidates in options.values())
            usable = [next(iter(candidates)) for candidates in options.values() if candidates]
            outcomes[label, bit, value] = len(set(usable)) == len(sub)
    failed = {key for key, passed in outcomes.items() if not passed}
    assert failed == {("R", 1, 0), ("R", 1, 1)}
    return failed


if __name__ == "__main__":
    layers, largest = rounds(6)
    counts = {n:permutation_check(n) for n in (5,6,7)}
    print("actual two-layer face-table round trips:", layers, "largest vertices:", largest)
    print("full-test assignments and surviving both side codes:", counts)
    print("crossed nonedges fail exactly:", sorted(crossed_edges()))
