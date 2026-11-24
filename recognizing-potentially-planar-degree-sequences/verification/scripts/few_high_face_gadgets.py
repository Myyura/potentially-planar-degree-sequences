"""Check the plane embeddings used in few-high-bounded-width.md (standard library)."""

import argparse
from collections import Counter, defaultdict


def require(ok, message):
    if not ok:
        raise ValueError(message)


def sphere(rot):
    """Check that each component's rotation system is an embedding on the sphere."""
    for v, row in rot.items():
        require(v not in row and len(row) == len(set(row)), "loop or duplicate neighbor")
        require(all(v in rot[w] for w in row), "asymmetric edge")

    unseen = set(rot)
    walks = []
    while unseen:
        comp = set()
        stack = [next(iter(unseen))]
        while stack:
            v = stack.pop()
            if v in unseen:
                unseen.remove(v)
                comp.add(v)
                stack.extend(rot[v])
        darts = {(v, w) for v in comp for w in rot[v]}
        edges = len(darts) // 2
        faces = []
        while darts:
            a, b = next(iter(darts))
            start = a, b
            face = []
            while (a, b) in darts:
                darts.remove((a, b))
                face.append(a)
                row = rot[b]
                a, b = b, row[(row.index(a) + 1) % len(row)]
            require((a, b) == start, "unclosed face")
            faces.append(face)
        if not faces:  # one isolated vertex
            faces = [list(comp)]
        require(len(comp) - edges + len(faces) == 2, "positive genus")
        walks.extend(faces)
    return walks


def rot_from_faces(faces):
    """Orient polygonal faces across their shared edges and recover the cyclic links."""
    incidence = defaultdict(list)
    for i, f in enumerate(faces):
        for a, b in zip(f, f[1:] + f[:1]):
            incidence[tuple(sorted((a, b)))].append((i, a < b))
    neighbors = [[] for _ in faces]
    for sides in incidence.values():
        require(len(sides) == 2, "wrong face incidence")
        (i, s), (j, t) = sides
        neighbors[i].append((j, s == t))
        neighbors[j].append((i, s == t))
    reverse = {0: False}
    stack = [0]
    while stack:
        i = stack.pop()
        for j, flip in neighbors[i]:
            value = reverse[i] ^ flip
            if j not in reverse:
                reverse[j] = value
                stack.append(j)
            require(reverse[j] == value, "nonorientable faces")
    succ = defaultdict(dict)
    for i, f in enumerate(faces):
        if reverse[i]:
            f = f[::-1]
        for j, v in enumerate(f):
            a, b = f[j - 1], f[(j + 1) % len(f)]
            require(a not in succ[v], "reused corner")
            succ[v][a] = b
    rot = {}
    for v, nxt in succ.items():
        first = next(iter(nxt))
        row = [first]
        while nxt[row[-1]] != first:
            row.append(nxt[row[-1]])
            require(len(row) <= len(nxt), "invalid link")
        require(len(row) == len(nxt), "disconnected link")
        rot[v] = row
    sphere(rot)
    return rot


def cone(disk, root):
    boundary_count = Counter()
    for f in disk:
        boundary_count.update(tuple(sorted(e)) for e in zip(f, f[1:] + f[:1]))
    caps = [[a, b, root] for (a, b), count in boundary_count.items() if count == 1]
    return rot_from_faces(disk + caps)


def library(d):
    if d == 1:
        return {0: [1], 1: [0]}
    if d == 2:
        return {i: [(i - 1) % 3, (i + 1) % 3] for i in range(3)}
    if d == 3:
        return cone([[0, 1, 2]], 3)
    if d == 4:
        return rot_from_faces([[i, (i + 1) % 4, pole] for pole in (4, 5) for i in range(4)])
    ring = range(5)
    faces = []
    for a in ring:
        b = (a + 1) % 5
        faces += [[a, b, 10], [a + 5, b + 5, 11], [a, b, b + 5], [a, a + 5, b + 5]]
    return rot_from_faces(faces)


def add_tip(rot, face, v, tip):
    """Put the tip immediately after the preceding neighbor in this occurrence's corner."""
    i = face.index(v)
    row = rot[v]
    slot = row.index(face[i - 1]) + 1 if row else 0
    row.insert(slot, tip)
    rot[tip] = [v]


def splice(rot, tip1, tip2, block):
    """Replace the two free tips by the terminals of a fresh edge-deleted block."""
    u, = rot[tip1]
    v, = rot[tip2]
    offset = max(rot) + 1
    for z, row in block.items():
        rot[offset + z] = [offset + y for y in row]
    a = offset + next(iter(block))
    b = rot[a][0]
    rot[u][rot[u].index(tip1)] = a
    rot[v][rot[v].index(tip2)] = b
    rot[a][rot[a].index(b)] = u
    rot[b][rot[b].index(a)] = v
    del rot[tip1], rot[tip2]


def place_pair(rot, face, u, v, block):
    x = max(rot) + 1
    add_tip(rot, face, u, x)
    # Recompute the corner to allow both ends on the same original vertex.
    new_face = next(f for f in sphere(rot) if x in f)
    add_tip(rot, new_face, v, x + 1)
    splice(rot, x, x + 1, block)


def check_group(target, size, block, d):
    root = size
    if target == 4:
        k = size // 2
        disk = [[i, i + 1, k + i + 1, k + i] for i in range(k - 1)]
        rot = cone(disk, root)
        pairs = [(0, k), (k - 1, size - 1)]
    else:
        rot = cone([[i, i + 1, i + 2] for i in range(size - 2)], root)
        for ear in (1, size - 2):
            rot[root].remove(ear)
            rot[ear].remove(root)
        pairs = [(v, v) for v in (0, 1, size - 2, size - 1, root)]
    for u, v in pairs:
        if u == v:
            face = next(f for f in sphere(rot) if u in f)
        else:
            face = next(f for f in sphere(rot) if set(f) == {root, u, v})
        place_pair(rot, face, u, v, block)
    sphere(rot)
    require(len(rot[root]) == size and all(len(rot[i]) == target for i in range(size)),
            "wrong root or old degree")
    require(len(rot) == size + 1 + len(block) * len(pairs), "wrong block consumption")
    require(all(len(row) == d for v, row in rot.items() if v > root), "wrong library degree")


def necklace(holes):
    """Triangular boundary components temporarily joined by bridges in their common face."""
    rot = {}
    bridges = []
    for i in range(holes):
        a = 3 * i
        rot.update({a: [a + 1, a + 2], a + 1: [a + 2, a], a + 2: [a, a + 1]})
        if i:
            b = a - 2
            rot[b].insert(rot[b].index(b - 1) + 1, a)
            rot[a].insert(rot[a].index(a + 2) + 1, b)
            bridges.append((b, a))
    return rot, bridges


def ring_key(face):
    return min(tuple(face[i:] + face[:i]) for i in range(len(face)))


def check_holes(ports, d, block):
    """Cap ports on a specified multiply connected face, preserving the protected faces."""
    rot, bridges = necklace(len(ports))
    walks = sphere(rot)
    outer = max(walks, key=len)
    protected = {ring_key(f) for f in walks if f is not outer}
    require(len(protected) == len(ports), "wrong hole embedding")
    requests = [3 * i + offset for i, group in enumerate(ports) for offset in group]
    require(len(requests) % 2 == 0, "odd total")
    # Discard the temporary bridges before computing the prescribed final degrees.
    wanted = {v: 2 + requests.count(v) for v in rot}
    tips = set()
    for v in requests:
        tip = max(rot) + 1
        add_tip(rot, outer, v, tip)
        tips.add(tip)
        outer = next(f for f in sphere(rot) if tip in f)
    ordered = [v for v in outer if v in tips]
    require(len(ordered) == len(requests), "missing tip on common face")
    for x, y in zip(ordered[::2], ordered[1::2]):
        splice(rot, x, y, block)
    sphere(rot)  # embed while the bridges are still present, then remove them
    for u, v in bridges:
        rot[u].remove(v)
        rot[v].remove(u)
    walks = sphere(rot)
    require(protected <= {ring_key(f) for f in walks}, "a protected face was opened")
    require(all(len(rot[v]) == degree for v, degree in wanted.items()), "wrong boundary degrees")
    require(all(len(row) == d for v, row in rot.items() if v not in wanted), "wrong filler degrees")
    require(len(rot) == len(wanted) + len(requests) // 2 * len(block), "wrong size")


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--max-size", type=int, default=22, help="largest single-root group")
    args = parser.parse_args()
    if args.max_size < 4:
        parser.error("--max-size must be at least four")
    # Includes same-vertex ports, odd totals on individual holes, and unused holes.
    cases = [((0,), (0,)), ((0, 0), (1, 1)), ((2,), (0, 1), (2,)),
             ((0,), (), (1,), (0, 0)), ((), ())]
    groups = hole_tests = 0
    for d in range(1, 6):
        block = library(d)
        sphere(block)
        require(all(len(row) == d for row in block.values()), "nonregular template")
        for target in (4, 5):
            for size in range(4, args.max_size + 1, 2 if target == 4 else 1):
                check_group(target, size, block, d)
                groups += 1
        for ports in cases:
            check_holes(ports, d, block)
            hole_tests += 1
    require(sphere({}) == [] and len(sphere({0: [], 1: [], 2: []})) == 3, "zero-degree inputs")
    print(f"{groups} single-root group embeddings, {hole_tests} multiple-boundary fillings, "
          "and empty/isolated cases passed.")


if __name__ == "__main__":
    main()
