"""Finite arithmetic test for simple planar degree realizability.

spherical_weight counts connected spherical slot pairings with spanning-tree
multiplicity, after removing isolates. The signed histogram sums grow quickly.
The decision entry point uses trace splitting through seven positive entries.
Use --weight for signed histogram summation, or --verify for exact small evaluations. Only standard-library arithmetic is
used; no simple graph or embedding catalogue is required by this calculation.
"""

import argparse
from collections import Counter
from functools import cache, lru_cache
from itertools import combinations, combinations_with_replacement, permutations, product
from math import comb, factorial, gcd, prod


@cache
def local_histograms(degree, colors):
    """Coefficient table of tr((X-J)^degree); J is the all-one matrix."""
    zero = (0,) * (colors * colors)
    table = Counter()
    for initial in range(colors):
        layer = {(initial, zero): 1}
        for step in range(degree):
            next_layer = Counter()
            for (current, histogram), coefficient in layer.items():
                if not coefficient:
                    continue
                # Close the cyclic word on its last transition.
                targets = (initial,) if step + 1 == degree else range(colors)
                for target in targets:
                    next_layer[target, histogram] -= coefficient
                    index = current * colors + target
                    updated = list(histogram)
                    updated[index] += 1
                    next_layer[target, tuple(updated)] += coefficient
            layer = next_layer
        for (_, histogram), coefficient in layer.items():
            if coefficient:
                table[histogram] += coefficient
    return {key: value for key, value in table.items() if value}


@cache
def tree_terms(n):
    """The tree terms in the Laplacian cofactor, from Prüfer words."""
    pairs = tuple(combinations(range(n), 2))
    edge_index = {pair: index for index, pair in enumerate(pairs)}
    all_indices = set(range(len(pairs)))
    terms = []
    for word in product(range(n), repeat=n-2):
        counts = [1] * n
        for v in word:
            counts[v] += 1
        tree = []
        for v in word:
            leaf = counts.index(1)
            tree.append(edge_index[tuple(sorted((leaf, v)))])
            counts[leaf] -= 1
            counts[v] -= 1
        tree.append(edge_index[tuple(i for i, d in enumerate(counts) if d)])
        terms.append((tuple(tree), tuple(sorted(all_indices.difference(tree)))))
    return terms


@cache
def interpolation_row(degree, power):
    """Integer weights giving degree! times the requested coefficient."""
    weights = []
    for i in range(degree+1):
        polynomial = [1]
        for j in range(degree+1):
            if j != i:
                extended = [0] * (len(polynomial)+1)
                for k, coefficient in enumerate(polynomial):
                    extended[k] -= j*coefficient
                    extended[k+1] += coefficient
                polynomial = extended
        weights.append((-1)**(degree-i)*comb(degree, i)*polynomial[power])
    return tuple(weights)


def determinant(matrix):
    """Bareiss elimination. Rows of the integer input can be overwritten."""
    sign, previous = 1, 1
    n = len(matrix)
    for k in range(n-1):
        if not matrix[k][k]:
            swap = next((i for i in range(k+1,n) if matrix[i][k]), None)
            if swap is None:
                return 0
            matrix[k], matrix[swap] = matrix[swap], matrix[k]
            sign = -sign
        pivot = matrix[k][k]
        for i in range(k+1,n):
            for j in range(k+1,n):
                matrix[i][j] = (pivot*matrix[i][j]-matrix[i][k]*matrix[k][j])//previous
        previous = pivot
    return sign*matrix[-1][-1]


def scaled_tree_value(c, n, z):
    """Clear denominators of the weighted Laplacian at a nonnegative node."""
    factors = [1+z*x for x in c]
    scale = 1
    for a in factors:
        scale = scale//gcd(scale,a)*a
    laplacian = [[0]*(n-1) for _ in range(n-1)]
    for (i,j), x, a in zip(combinations(range(n),2), c, factors):
        weight = (scale//a)*z*x
        laplacian[i][i] += weight
        if j < n-1:
            laplacian[j][j] += weight
            laplacian[i][j] -= weight
            laplacian[j][i] -= weight
    return (prod(factors)*determinant(laplacian))//(scale**(n-1))


def tree_weighted_polynomial(c, n, m):
    """Evaluate [z^m] product(1+z c_e) times the weighted tree cofactor."""
    if m == len(c):
        return n**(n-2) * prod(c)
    if m == len(c)-1:
        # Each excluded edge belongs to 2/n of the Cayley trees.
        tree_count = n**(n-2) * (n-2) // n
        return tree_count * sum(prod(c[:i]) * prod(c[i+1:]) for i in range(len(c)))
    if sum(x > 0 for x in c) < m:
        return 0
    row = interpolation_row(len(c),m)
    return sum(weight*scaled_tree_value(c,n,z) for z,weight in enumerate(row))//factorial(len(c))


def face_value(degrees, colors):
    """Evaluate the face-color polynomial with its spanning-tree weight."""
    if colors == 0:
        return 0
    n = len(degrees)
    m = sum(degrees) // 2
    groups = sorted(Counter(degrees).items())
    tables = {d: local_histograms(d, colors) for d, _ in groups}
    histograms = sorted(set().union(*(table.keys() for table in tables.values())))
    indices = {h: i for i, h in enumerate(histograms)}
    transpose = [tuple(h[b*colors+a] for a in range(colors) for b in range(colors))
                 for h in histograms]
    compatibility = [[sum(x*y for x, y in zip(s, t)) for t in transpose]
                     for s in histograms]
    pairs = tuple(combinations(range(n), 2))

    def group_choices(d, multiplicity):
        # Symmetry of E_m(c) under vertex permutations of equal target degree.
        indexed = {indices[h]: weight for h, weight in tables[d].items()}
        for copies in combinations_with_replacement(indexed, multiplicity):
            weight = factorial(multiplicity)
            for i, times in Counter(copies).items():
                weight //= factorial(times)
                weight *= indexed[i]**times
            yield copies, weight

    def accumulate(group_number, selected, coefficient):
        if group_number == len(groups):
            c = [compatibility[selected[i]][selected[j]] for i, j in pairs]
            return coefficient * tree_weighted_polynomial(c, n, m)
        return sum(accumulate(group_number+1, selected+copies, coefficient*weight)
                   for copies, weight in group_choices(*groups[group_number]))

    return accumulate(0, (), 1)


def spherical_weight(degrees):
    """Connected, spanning-tree weighted spherical count on the positive terms.

    A nonempty input with no positive terms is assigned weight one.
    For positive disconnected forests the connected count may vanish.
    """
    if not degrees or any(d < 0 for d in degrees):
        return 0
    positive = tuple(d for d in degrees if d)
    n = len(positive)
    if not n:
        return 1
    total = sum(positive)
    m = total // 2
    if total % 2 or max(positive) >= n or m < n-1 or (n >= 3 and m > 3*n-6):
        return 0
    faces = m-n+2
    numerator = sum((-1)**(faces-j) * comb(faces,j) * face_value(positive,j)
                    for j in range(1,faces+1))
    value, remainder = divmod(numerator, factorial(faces))
    if value < 0 or remainder:
        raise ArithmeticError("invalid sphere-weight normalization")
    return value


def colored_tree_type(neighbors, degrees):
    """A complete unrooted-tree invariant with prescribed degree labels."""
    def rooted(v, parent):
        return degrees[v], tuple(sorted(rooted(u, v) for u in neighbors[v] if u != parent))
    return min(rooted(v, None) for v in range(len(neighbors)))


def tree_trace_weight(neighbors, degrees):
    """Evaluate the sphere coefficient for one tree term by trace splitting."""
    n = len(degrees)
    bit = [[0]*n for _ in range(n)]
    for edge, (i, j) in enumerate(combinations(range(n), 2)):
        if j not in neighbors[i]:
            bit[i][j] = bit[j][i] = 1 << edge

    def branch(v, parent):
        # Rotate the slot for the parent to the beginning of the trace.
        # Its d_v possible positions are accounted for in the final product.
        children = [u for u in neighbors[v] if u != parent]
        choices = [branch(u, v) for u in children]
        result = Counter()
        length = degrees[v]-1
        for positions in permutations(range(length), len(children)):
            for words in product(*(table.items() for table in choices)):
                parts = [(v,)] * length
                coefficient = 1
                for pos, (word, weight) in zip(positions, words):
                    parts[pos] = word
                    coefficient *= weight
                result[sum(parts, ())] += coefficient
        return result

    @lru_cache(maxsize=40000)
    def interval(word):
        # Squarefree coefficient table for noncrossing pairs on a trace.
        # A bit marks one consumed factor (1+D_ij).
        if not word:
            return {0: 1}
        result = Counter()
        for j in range(1, len(word), 2):
            mark = bit[word[0]][word[j]]
            if not mark:
                continue
            inside = interval(word[1:j])
            outside = interval(word[j+1:])
            for u, left in inside.items():
                if u & mark:
                    continue
                occupied = u | mark
                for v, right in outside.items():
                    if not (v & occupied):
                        result[v | occupied] += left * right
        return result

    first_child = neighbors[0][0]
    left = branch(0, first_child)
    right = branch(first_child, 0)
    value = sum(a*b*sum(interval(u+v).values())
                for u, a in left.items() for v, b in right.items())
    interval.cache_clear()
    return value * prod(degrees)


def split_trace_weight(degrees):
    """Equivalent top coefficient by marking the spanning-tree edges first.

    Contracting them joins traces until one cyclic word remains. Each subsequent
    edge contraction either splits a trace or joins two. Only splits attain
    the largest possible power of the color count. Pairing the first symbol
    with a later symbol separates the two intervals in the split trace.
    """
    if not degrees or any(d < 0 for d in degrees):
        return 0
    positive = tuple(d for d in degrees if d)
    n = len(positive)
    if not n:
        return 1
    total = sum(positive)
    m = total//2
    if total % 2 or max(positive) >= n or m < n-1 or (n >= 3 and m > 3*n-6):
        return 0
    pairs = tuple(combinations(range(n), 2))
    multiplicities = Counter()
    representatives = {}
    for tree, _ in tree_terms(n):
        neighbors = [[] for _ in range(n)]
        for i in tree:
            u, v = pairs[i]
            neighbors[u].append(v)
            neighbors[v].append(u)
        if any(len(row) > degree for row, degree in zip(neighbors, positive)):
            continue
        tree_type = colored_tree_type(neighbors, positive)
        multiplicities[tree_type] += 1
        representatives.setdefault(tree_type, neighbors)
    return sum(count*tree_trace_weight(representatives[key], positive)
               for key, count in multiplicities.items())


def realizable(degrees):
    if not degrees or any(d < 0 for d in degrees):
        return False
    positive = [d for d in degrees if d]
    if not positive:
        return True
    n = len(positive)
    total = sum(positive)
    if total % 2 or max(positive) >= n or (n >= 3 and total > 6*n-12):
        return False
    if total <= 2*n-2:
        return True
    evaluate = split_trace_weight if n <= 7 else spherical_weight
    return evaluate(positive) > 0


def check_triangle_grid():
    """Evaluate the all-integer matrix grid separately for d=(2,2,2)."""
    # Four times the Lagrange kernel on the three nodes 0,1,2.
    kernel = ((15, -16, 5), (-16, 24, -8), (5, -8, 3))
    for q in (1, 2):
        matrices = tuple(product(range(3), repeat=q*q))

        def trace_pair(x, y):
            return sum(x[a*q+b]*y[b*q+a] for a in range(q) for b in range(q))

        local = {}
        for v in matrices:
            weight = sum(trace_pair(u, u)*prod(kernel[a][b] for a,b in zip(u,v))
                         for u in matrices)
            if weight:
                local[v] = weight
        total = 0
        for x, y, z in product(local, repeat=3):
            a, b, c = trace_pair(x,y), trace_pair(y,z), trace_pair(z,x)
            cofactor = determinant([[1+a, 0, 0, a, -a],
                                    [0, 1+b, 0, 0, b],
                                    [0, 0, 1+c, c, 0],
                                    [-1, 0, -1, 0, 0],
                                    [1, -1, 0, 0, 0]])
            assert cofactor == a*b+b*c+c*a+3*a*b*c
            total += cofactor * local[x] * local[y] * local[z]
        assert total == 4**(3*q*q) * 24*q*q


def verify():
    check_triangle_grid()
    # Direct tree-cofactor expansion on a fixed, nonconstant set of weights.
    c = [1, 0, 2, 3, 1, 4, 2, 5, 0, 1]
    for m in range(4,11):
        direct = 0
        for tree, outside in tree_terms(5):
            base = prod(c[i] for i in tree)
            direct += base * sum(prod(c[i] for i in extra)
                                 for extra in combinations(outside,m-4))
        assert direct == tree_weighted_polynomial(c,5,m)
    # These counts can also be obtained from the graph and its planar rotations.
    cases = [((1,1),1), ((2,1,1),2), ((2,2,2),24), ((2,2,2,2),192),
             ((3,2,2,1),72), ((3,3,3,1),0), ((3,3,2,2),576), ((3,3,3,3),2592)]
    for degrees, expected in cases:
        actual = spherical_weight(degrees)
        if actual != expected or split_trace_weight(degrees) != expected:
            raise AssertionError((degrees, actual, expected))
        print(degrees, actual)
    for degrees, expected in (((4,4,4,4,4,2),0), ((5,5,5,3,3,3),0),
                              ((4,4,4,4,4,4),47185920)):
        value = split_trace_weight(degrees)
        if value != expected:
            raise AssertionError((degrees, value, expected))
        print(degrees, value, "(split trace)")
    for degrees, expected in (([], False), ([0], True), ([1,1,1,1], True),
                              ([2,1,0], False), ([4,4,4,4,4], False)):
        assert realizable(degrees) == expected


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--verify", action="store_true")
    parser.add_argument("--weight", action="store_true", help="compute the connected sphere weight")
    parser.add_argument("--split-trace", action="store_true", help="evaluate tree-weighted count by trace splitting")
    parser.add_argument("degrees", nargs="*", type=int)
    args = parser.parse_args()
    if args.verify:
        verify()
    elif args.split_trace:
        print(split_trace_weight(args.degrees))
    else:
        print((spherical_weight if args.weight else realizable)(args.degrees))
