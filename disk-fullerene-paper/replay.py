"""Reproduce the computational checks in "The Smallest Three-Connected Disk-Fullerenes with a Prescribed Boundary Length".

Run `python3 replay.py` to check the constructions for h = 12 through 100.
Run `python3 replay.py --plantri /path/to/plantri` with plantri 5.8 to
reproduce Table 1 as well. The Python code uses only the standard library.
"""

import argparse
from collections import Counter, defaultdict
from itertools import combinations
import subprocess


def cap(tag, x, y):
    """The seam is xy. Its end quotas are 2 at x and 3 at y."""
    boundary = [x, y] + [f"{tag}b{i}" for i in range(2, 6)]
    rim = [f"{tag}r{i}" for i in range(5)]
    faces = []
    for i in range(5):
        faces.append((f"{tag}c", rim[i - 1], rim[i]))
        shared = boundary[5 if i == 0 else i]
        faces.append((rim[i - 1], rim[i], shared))
    # The rim vertex r0 spans the two boundary edges b5-b0 and b0-b1.
    for i in range(6):
        faces.append((rim[i % 5], boundary[i], boundary[(i + 1) % 6]))
    return faces


def edge_counts(faces):
    return Counter(
        tuple(sorted(edge)) for face in faces for edge in combinations(face, 2)
    )


def triangulation(h):
    keep, drop = "x", "y"
    faces = cap("L", keep, drop)
    for i in range(h - 10):
        new = f"t{i}"
        faces.append((keep, drop, new))
        keep, drop = new, keep
    faces.extend(cap("R", drop, keep))
    boundary = [edge for edge, count in edge_counts(faces).items() if count == 1]
    faces.extend(("peak", a, b) for a, b in boundary)
    return faces


def connected(neighbors):
    reached = set()
    todo = [next(iter(neighbors))]
    while todo:
        v = todo.pop()
        if v not in reached:
            reached.add(v)
            todo.extend(neighbors[v] - reached)
    return len(reached) == len(neighbors)


def verify(h, faces):
    triangles = {frozenset(face) for face in faces}
    if len(triangles) != len(faces) or any(len(f) != 3 for f in triangles):
        raise ValueError(f"h={h}: repeated or degenerate triangle")
    edges = edge_counts(faces)
    if set(edges.values()) != {2}:
        raise ValueError(f"h={h}: edge without two incident faces")
    links = defaultdict(lambda: defaultdict(set))
    for a, b, c in faces:
        for v, u, w in [(a, b, c), (b, c, a), (c, a, b)]:
            links[v][u].add(w)
            links[v][w].add(u)
    for v, link in links.items():
        if any(len(row) != 2 for row in link.values()) or not connected(link):
            raise ValueError(f"h={h}: invalid vertex link at {v}")
    if not connected({v: set(link) for v, link in links.items()}):
        raise ValueError(f"h={h}: disconnected triangulation")
    if len(links) - len(edges) + len(faces) != 2:
        raise ValueError(f"h={h}: wrong Euler characteristic")
    degrees = Counter(len(link) for link in links.values())
    if len(links["peak"]) != h or degrees != {5: h + 6, 6: 6, h: 1}:
        raise ValueError(f"h={h}: unexpected degrees {degrees}")


def census(program):
    targets = {
        (5,) * (h + 6) + (6,) * s + (h,): (h, s)
        for h in range(11, 15)
        for s in range(7)
    }
    matches = Counter()
    # The target degree sequence has h + s + 7 vertices.
    expected_totals = (12, 23, 73, 192, 651, 2070, 7290, 25381, 91441, 329824)
    for order, expected in enumerate(expected_totals, start=18):
        total = 0
        with subprocess.Popen([program, "-am5", str(order)], stdout=subprocess.PIPE) as run:
            for line in run.stdout:
                n, rotation = line.split()
                degrees = tuple(sorted(map(len, rotation.split(b","))))
                if int(n) != order or len(degrees) != order:
                    raise ValueError(f"malformed plantri record at order {order}")
                total += 1
                if degrees in targets:
                    matches[targets[degrees]] += 1
            if run.wait() != 0:
                raise RuntimeError(f"plantri failed at order {order}")
        if total != expected:
            raise ValueError(f"order {order}: counted {total}, expected {expected}")
    print(f"Enumerated {sum(expected_totals):,} triangulations of orders 18 through 27.")
    for h in range(11, 15):
        print(f"h={h}, matches for s=0,...,6: {[matches[h, s] for s in range(7)]}")
    if matches != {(12, 6): 1, (13, 6): 1, (14, 6): 1}:
        raise ValueError("census differs from the reference counts")


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--plantri", metavar="PATH", help="also enumerate orders 18 to 27")
    args = parser.parse_args()
    for h in range(12, 101):
        verify(h, triangulation(h))
    print("Verified 89 triangulated spheres for h=12,...,100.")
    if args.plantri:
        census(args.plantri)
