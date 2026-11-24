"""3-PARTITION to explicit sphere-triangulation degrees, optionally compressed on output."""

import argparse
from collections import Counter
from itertools import combinations

from few_high_face_gadgets import rot_from_faces


def partition_source(weights, capacity):
    if (not weights or len(weights) % 3 or capacity <= 0
            or any(4*w <= capacity or 2*w >= capacity for w in weights)
            or sum(weights) != len(weights)//3 * capacity):
        raise ValueError("requires a 3-PARTITION input, with B/4 < w < B/2 and sum(w) = mB")
    bins = len(weights)//3
    count = 4*bins+3
    faces = set(combinations(range(4), 3))
    for v in range(4, count):
        faces.remove((v-3, v-2, v-1))
        faces.update((a, b, v) for a, b in combinations(range(v-3, v), 2))
    faces = sorted(faces)
    fixed = {(u, v) for u in range(count) for v in range(u+1, min(count, u+4))}
    q = [min(3, v) + min(3, count-1-v) for v in range(count)]
    roots = list(range(0, 4*bins, 4))
    binsides = []
    for root in roots:
        a, b = root + 1, root + 3
        assert (root, a, b) in faces
        q[root] += capacity+1
        q[a] += capacity+1
        q[b] += 1
        binsides.append((root, a, b))
    paths = []
    for size in weights:
        path = list(range(len(q), len(q)+size))
        paths.append(path)
        fixed.update(zip(path, path[1:]))
        q.extend([4]*size)
    caps = []
    for root in roots:
        caps.append(len(q))
        fixed.add((root, len(q)))
        q.append(3)
    assert max(Counter(v for edge in fixed for v in edge).values()) <= 7
    assert sum(q) == 6*len(q)-12
    return q, sorted(fixed), faces, binsides, paths, caps


def matching_groups(edges):
    """Greedy edge coloring; each group's endpoints are pairwise distinct."""
    groups = []
    used = []
    for i, (x, y) in enumerate(edges):
        for group, vertices in zip(groups, used):
            if x not in vertices and y not in vertices:
                group.append(i)
                vertices.update((x, y))
                break
        else:
            groups.append([i])
            used.append({x, y})
    return groups


def tests(groups):
    for group in groups:
        yield group, 0
        yield group, 1
        for bit in range((len(group)-1).bit_length()):
            for value in (0, 1):
                subset = [edge for j, edge in enumerate(group) if (j >> bit) & 1 == value]
                if subset:
                    yield subset, 0
                    yield subset, 1


def encode(q, edges):
    """Keep original and marker positions explicit; group all other equal degrees."""
    n = len(q)
    if n < 4 or sum(q) != 6*n-12 or min(q) < 3 or max(q) >= n:
        raise ValueError("invalid initial triangulation target")
    if len(set(edges)) != len(edges) or any(not 0 <= a < b < n for a, b in edges):
        raise ValueError("edges must be distinct ordered pairs a < b of vertex positions")
    required_degrees = Counter(v for edge in edges for v in edge)
    if len(edges) > 3*n-6 or any(degree > q[v] for v, degree in required_degrees.items()):
        return Counter({5: 3, 3: 3}), 0
    if not edges:
        return Counter(q), 0
    # The first three full rounds. Markers are distinct second-generation stars.
    n1 = 3*n-4
    n2 = 3*n1-4
    order = 3*n2-4
    original = [8*d for d in q]
    marker = [6]*len(edges)
    aux = Counter({12: 2*n-4, 6: 2*n1-4-len(marker), 3: 2*n2-4})
    rounds = 3
    for group, side in tests(matching_groups(edges)):
        size = len(group)
        chosen = {edges[i][side] for i in group}
        assert len(chosen) == size and aux[3] >= size
        original = [2*d - (v in chosen) for v, d in enumerate(original)]
        marker = [2*d for d in marker]
        for i in group:
            marker[i] -= 1
        aux = Counter({2*d: count for d, count in aux.items()})
        aux[6] -= size
        aux[5] += size
        aux[3] = 2*order-4-size
        order += aux[3]
        rounds += 1
    output = Counter(original) + Counter(marker) + aux
    assert output.total() == order and sum(d*k for d,k in output.items()) == 6*order-12
    assert min(output) >= 3 and max(output) < order
    return output, rounds


def positive_source_witness(weights, capacity, assignment):
    q, required_edges, faces, bins, paths, caps = partition_source(weights, capacity)
    assert sorted(j for group in assignment for j in group) == list(range(len(weights)))
    remaining = set(faces)
    for (r, a, c), group, cap in zip(bins, assignment, caps, strict=True):
        assert sum(weights[j] for j in group) == capacity
        prev = c
        for v in [vertex for j in group for vertex in paths[j]] + [cap]:
            remaining.remove(tuple(sorted((r, a, prev))))
            remaining.update(tuple(sorted(f)) for f in ((r, a, v), (a, prev, v), (prev, r, v)))
            prev = v
    graph = rot_from_faces(sorted(remaining))
    assert all(len(graph[v]) == d for v, d in enumerate(q))
    assert all(y in graph[x] for x, y in required_edges)
    return graph


def audit():
    for m in range(1, 9):
        for weights, capacity in (([4,5,6]*m, 15), ([7,8,9]*m, 24), ([6,6,6]*m, 18)):
            groups = [list(range(i, i+3)) for i in range(0, 3*m, 3)]
            positive_source_witness(weights, capacity, groups)
            q, required, *_ = partition_source(weights, capacity)
            output, rounds = encode(q, required)
            colors = matching_groups(required)
            assert len(colors) <= 13
            assert rounds <= 3+len(colors)*(2+4*(len(required)-1).bit_length())
            assert output.total() <= len(q)*3**rounds
    negative = [4, 4, 4, 6, 6, 6]
    assert not any(sum(triple) == 15 for triple in combinations(negative, 3))
    positive = [4,5,6]*2
    for weights in (negative, positive):
        q, required, *_ = partition_source(weights, 15)
        out, rounds = encode(q, required)
        print(weights, "source order",len(q), "specified edges", len(required),
              "rounds",rounds,"final order",out.total(),"distinct degrees",len(out))
    print("verified 24 positive source embeddings and the infeasible two-bin arithmetic example")


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--capacity", type=int)
    parser.add_argument("--expand", action="store_true", help="write every degree, including its repetitions")
    parser.add_argument("weights", type=int, nargs="*")
    args = parser.parse_args()
    if args.capacity is None:
        audit()
    else:
        q, required, *_ = partition_source(args.weights, args.capacity)
        output, _ = encode(q, required)
        for d, multiplicity in sorted(output.items()):
            if args.expand:
                for _ in range(multiplicity):
                    print(d)
            else:
                print(d, multiplicity)
