"""Recognize a simple planar degree multiset by adding triangles along a small frontier.

All edges of a spanning triangulation are scanned. A chosen subset contributes to
the requested degrees. The state keeps closed edges only between live vertices.
The --width option restricts the search to that width; default is unconditional.
"""

from functools import cache
from itertools import combinations, product
from math import isqrt
import argparse
import json


def recognize(sequence, width=None):
    degrees = tuple(sorted(sequence, reverse=True))
    n = len(degrees)
    if any(d < 0 or d >= n for d in degrees) or sum(degrees) % 2:
        return False
    if n <= 3:
        return degrees in ((), (0,), (0, 0), (1, 1), (0, 0, 0),
                           (1, 1, 0), (2, 1, 1), (2, 2, 2))
    if sum(degrees) > 6 * n - 12:
        return False
    num_faces = 2 * n - 4
    # 48 > 3 sqrt(8)/(1-sqrt(2/3)). Integer ceiling is deliberately loose.
    if width is None:
        width = min(3 * n - 6, 48 * (1 + isqrt(num_faces)))
    values = tuple(sorted(set(degrees)))
    slots = {d: i for i, d in enumerate(values)}
    initial = tuple(degrees.count(d) for d in values)
    kept_budget = sum(degrees) // 2
    unused_budget = 3 * n - 6 - kept_budget

    @cache
    def visit(step, introduced, groups, closed, red_degrees, remaining):
        # groups partitions the open edges by edge-connected face component.
        live = dict(red_degrees)
        op = {p for group in groups for p in group}
        finished_sum = sum(degrees) - sum(d * count for d, count in zip(values, remaining))
        red_count = (sum(live.values()) + finished_sum) // 2
        blue_count = (3 * step + len(op)) // 2 - red_count
        used = op.union(closed)
        fresh_limit = min(n - introduced, 3)
        for fresh in range(fresh_limit + 1):
            for known in combinations(live, 3 - fresh):
                tri = known + tuple(range(introduced, introduced + fresh))
                sides = set(combinations(sorted(tri), 2))
                if sides.intersection(closed):
                    continue
                new_edges = sorted(sides - op)
                next_open = op.symmetric_difference(sides)
                if len(next_open) > width:
                    continue
                next_live = {v for p in next_open for v in p}
                # Every previously closed live-live edge must stay forbidden.
                next_closed = tuple(sorted(p for p in (used | sides) - next_open
                                           if p[0] in next_live and p[1] in next_live))
                a = len(next_live)
                edge_cap = a * (a - 1) // 2 if a < 3 else 3 * a - 6
                if len(next_open) + len(next_closed) > edge_cap:
                    continue
                touched = [g for g in groups if not sides.isdisjoint(g)]
                joined_open = set(new_edges)
                for group in touched:
                    joined_open.update(p for p in group if p not in sides)
                others = [g for g in groups if g not in touched]
                last = step + 1 == num_faces
                if not joined_open and (not last or others):
                    continue
                if last and (next_open or introduced + fresh != n):
                    continue
                if joined_open:
                    others.append(tuple(sorted(joined_open)))
                next_groups = tuple(sorted(others))
                for flags in product((0, 1), repeat=len(new_edges)):
                    added_red = sum(flags)
                    if red_count + added_red > kept_budget or (
                            blue_count + len(flags) - added_red > unused_budget):
                        continue
                    totals = live.copy()
                    for v in tri:
                        totals.setdefault(v, 0)
                    for (u, v), keep in zip(new_edges, flags):
                        totals[u] += keep
                        totals[v] += keep
                    rest = list(remaining)
                    for v in totals.keys() - next_live:
                        k = slots.get(totals[v])
                        if k is None or not rest[k]:
                            break
                        rest[k] -= 1
                    else:
                        if last:
                            if not any(rest):
                                return True
                            continue
                        # Every current degree needs a distinct, sufficiently
                        # large eventual target. Unintroduced vertices need 0.
                        # The largest targets suffice for this monotone test.
                        partial = sorted((totals[v] for v in next_live), reverse=True)
                        limits = (val for val, count in zip(reversed(values), reversed(rest))
                                  for _ in range(count))
                        if any(b > lim for b, lim in zip(partial, limits)):
                            continue
                        next_red = tuple(sorted((v, totals[v]) for v in next_live))
                        if visit(step + 1, introduced + fresh, next_groups, next_closed,
                                 next_red, tuple(rest)):
                            return True
        return False

    try:
        return visit(0, 0, (), (), (), initial)
    finally:
        visit.cache_clear()


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("degrees", type=int, nargs="*")
    parser.add_argument("--width", type=int)
    args = parser.parse_args()
    print(json.dumps(dict(degrees=args.degrees, width=args.width,
                          accepted=recognize(args.degrees, args.width))))
