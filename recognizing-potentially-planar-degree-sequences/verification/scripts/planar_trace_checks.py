"""Independent small-input audit by labelled graphs, rotation orders and tree subsets."""

from argparse import ArgumentParser
from collections import Counter
from itertools import combinations, permutations, product
from math import prod


def graphs(degrees):
    """Choose the complete set of neighbours above each vertex exactly once."""
    def extend(i, residual, edges):
        if i == len(residual):
            yield edges
            return
        possible = [j for j in range(i + 1, len(residual)) if residual[j] > 0]
        for later in combinations(possible, residual[i]):
            remaining = residual.copy()
            for j in later:
                remaining[j] -= 1
            yield from extend(i + 1, remaining, edges + [(i, j) for j in later])

    yield from extend(0, list(degrees), [])


def tree_count(n, edges):
    """Count spanning trees by testing each n-1 edge set for cycles."""
    count = 0
    for candidate in combinations(edges, n - 1):
        parent = list(range(n))

        def root(v):
            while v != parent[v]:
                v = parent[v]
            return v

        for i, j in candidate:
            a = root(i)
            b = root(j)
            if a == b:
                break
            parent[a] = b
        else:
            count += 1
    return count


def rotation_faces(n, edges):
    """Enumerate cyclic orders and trace the orbits of the face permutation."""
    incident = [[] for _ in range(n)]
    for index, (i, j) in enumerate(edges):
        incident[i].append(2 * index)
        incident[j].append(2 * index + 1)

    # Each dart points outwards from its vertex. The mate of s is s xor 1.
    choices = []
    for row in incident:
        choices.append([
            tuple(zip((s ^ 1 for s in cycle), cycle[1:] + cycle[:1]))
            for rest in permutations(row[1:])
            for cycle in [(row[0],) + rest]
        ])

    darts = 2 * len(edges)
    by_faces = Counter()
    for orders in product(*choices):
        successor = [0] * darts
        for row in orders:
            for source, target in row:
                successor[source] = target
        used = bytearray(darts)
        faces = 0
        for start in range(darts):
            if not used[start]:
                faces += 1
                current = start
                while not used[current]:
                    used[current] = 1
                    current = successor[current]
        by_faces[faces] += 1
    return by_faces


def check(degrees):
    """Return connected graphs, planar cyclic orders, and marked-tree port weight."""
    if not degrees or min(degrees) < 1:
        raise ValueError("this audit expects a nonempty positive sequence")
    connected = spherical = 0
    face_weights = Counter()
    faces_needed = 2 - len(degrees) + sum(degrees) // 2
    markings = prod(degrees)
    for edges in graphs(degrees):
        trees = tree_count(len(degrees), edges)
        if not trees:
            continue
        connected += 1
        by_faces = rotation_faces(len(degrees), edges)
        spherical += by_faces[faces_needed]
        for faces, rotations in by_faces.items():
            face_weights[faces] += markings * trees * rotations
    return connected, spherical, face_weights[faces_needed], dict(sorted(face_weights.items()))


SMALL_CASES = (
    (1, 1),
    (2, 1, 1),
    (2, 2, 2),
    (2, 2, 2, 2),
    (3, 2, 2, 1),
    (3, 3, 1, 1),
    (3, 3, 2, 2),
    (3, 3, 3, 3),
)


# The literal trace formula on these cases is much larger. The independent
# graph and rotation calculation still takes only seconds.
LARGER_CASES = (
    (3, 3, 3, 3, 2),
    (4, 4, 4, 4, 2),
    (4, 4, 4, 4, 4, 2),
    (4, 4, 4, 4, 4, 4),
    (5, 5, 5, 3, 3, 3),
)


if __name__ == "__main__":
    parser = ArgumentParser(description=__doc__)
    parser.add_argument("degrees", nargs="*", type=int)
    parser.add_argument("--compare", action="store_true",
                        help="also evaluate the arithmetic formula on these cases")
    parser.add_argument("--face-one", action="store_true",
                        help="also compare the arithmetic face polynomial at one color")
    args = parser.parse_args()
    if args.degrees:
        cases = [tuple(args.degrees)]
    else:
        cases = SMALL_CASES if args.compare else SMALL_CASES + LARGER_CASES
    if args.compare:
        from planar_trace_arithmetic import spherical_weight

    if args.face_one:
        from planar_trace_arithmetic import face_value

    for degrees in cases:
        connected, rotations, count, by_faces = check(degrees)
        print(f"{degrees}  connected={connected}  sphere_rotations={rotations}  "
              f"tree_marked_port_weight={count}  by_faces={by_faces}", flush=True)
        if args.face_one:
            obtained = face_value(degrees, 1)
            if obtained != sum(by_faces.values()):
                raise AssertionError((degrees, sum(by_faces.values()), obtained))
        if args.compare:
            actual = spherical_weight(degrees)
            if actual != count:
                raise AssertionError((degrees, count, actual))
