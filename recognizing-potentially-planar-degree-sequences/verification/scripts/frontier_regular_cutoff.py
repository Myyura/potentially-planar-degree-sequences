"""Check the residual-row proofs for four- and five-regular planar degree lists."""


def canonical(row):
    return min(row, row[::-1])


def successors(row, degree):
    result = set()
    for start in range(len(row) + 1):
        longest = min(degree, len(row) - start)
        for size in range(longest + 1):
            stop = start + size
            if size >= 3 and any(value != 1 for value in row[start + 1:stop - 1]):
                continue
            fresh = degree - size
            if size == 0:
                replacements = [(fresh,)]
            elif size == 1:
                old = row[start] - 1
                replacements = [(old, fresh), (fresh, old)]
            else:
                replacements = [(row[start] - 1, fresh, row[stop - 1] - 1)]
            for replacement in replacements:
                alive = tuple(value for value in replacement if value)
                result.add(canonical(row[:start] + alive + row[stop:]))
    return result


def census(n, degree):
    """Exhaust all rows, merging reflection and using only proved lower bounds."""
    rows = {()}
    counts = [1]
    penultimate_pairs = None
    total_loss = 3 * n - n * degree // 2
    for seen in range(1, n + 1):
        remaining = n - seen
        next_rows = set()
        for row in rows:
            for nxt in successors(row, degree):
                demand = sum(nxt)
                if max(nxt, default=0) > remaining or demand > remaining * degree:
                    continue
                if nxt and demand - len(nxt) > 2 * (remaining - 1):
                    continue
                edges = (seen * degree - demand) // 2
                loss = 3 * seen - edges - len(nxt)
                future_loss = 3 * (remaining > 0) + (seen == 1)
                if loss + future_loss <= total_loss:
                    next_rows.add(nxt)
        rows = next_rows
        counts.append(len(rows))
        if remaining == 2:
            penultimate_pairs = sorted(rows)
    return counts, penultimate_pairs


def check_path(degree, path):
    tokens = path.split()
    rows = [tuple(map(int, token)) if token != "-" else () for token in tokens]
    for before, after in zip(rows, rows[1:]):
        assert canonical(after) in successors(canonical(before), degree), (before, after)


if __name__ == "__main__":
    for n, d in [(7, 4), (14, 5)]:
        counts, near = census(n, d)
        assert counts[-1] == 0
        print(n, d, counts, near)

    # Reversing a row between two displayed steps is harmless: reflect the
    # rest of the disk construction whenever the next representative is reversed.
    check_path(4, "- 4 33 222 1212 1111 -")
    check_path(4, "- 4 33 222 1212 1221 1212 1111 -")
    check_path(4, "- 4 33 222 2132 1122 11312 1212 1111 -")
    check_path(4, "1212 2112 1212")
    check_path(5, "- 5 44 333 2323 23132 132132 1321231 1312131 1221131 121121 11111 -")
    check_path(5, "- 5 44 333 2323 22313 224213 2233113 22232113 221322113 "
                  "2212312113 22113212113 2111231122 211122112 112112 11111 -")
    check_path(5, "211122112 211213112 211122112")
