"""Compare the face-frontier recognizer with all labelled graphs on at most 5 vertices."""
import argparse
from itertools import combinations, combinations_with_replacement
from pathlib import Path
import json

from face_frontier_recognition import recognize

OUT = Path(__file__).resolve().parents[1] / 'results/face_frontier_small_audit.json'


def run():
    counts = []
    for n in range(6):
        possible = set()
        edges = tuple(combinations(range(n), 2))
        for mask in range(1 << len(edges)):
            # Every proper subgraph of K5 is planar: K5-e is the triangular
            # bipyramid. K5 itself violates Euler's edge bound.
            if n == 5 and mask == (1 << len(edges)) - 1:
                continue
            degree = [0] * n
            for i, (a, b) in enumerate(edges):
                if mask >> i & 1:
                    degree[a] += 1
                    degree[b] += 1
            possible.add(tuple(sorted(degree)))
        inputs = 0
        for seq in combinations_with_replacement(range(n), n):
            assert recognize(seq) == (seq in possible), seq
            inputs += 1
        counts.append(dict(n=n, inputs=inputs, accepted=len(possible)))
    return dict(comparison=counts, total_inputs=sum(row['inputs'] for row in counts))


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--verify-only', action='store_true')
    args = parser.parse_args()
    result = run()
    if args.verify_only:
        assert json.loads(OUT.read_text()) == result
    else:
        OUT.write_text(json.dumps(result, indent=2) + '\n')
    print(json.dumps(result))
