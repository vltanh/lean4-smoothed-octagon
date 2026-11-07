#!/usr/bin/env python3
"""Exact cross-check of the five-template sign coverage theorem.

Run: python3 explorations/finite_window_cover.py
Dependencies: Python standard library only; tested with Python 3.13.5.
Inputs: all 2^5 binary sign strings, not words up to a chosen total length.
No random seeds, floating point, Lean, Lake, or CI are used.

The domain is a periodic +/- sign sequence avoiding '+-+'. Each graph
vertex is a length-four suffix; an edge is a length-five block. Removing
the five target edges leaves a DAG. Thus no periodic sign sequence avoids
both the established exclusion and all five templates. This is only the
combinatorial coverage claim. It proves none of the analytic local
improvement statements, and does not establish a switch bound by itself.
The independent hand proof is docs/BOUNDED_REDUCTION.md, Section 2.
"""
from itertools import product

TARGETS = {
    '+++++': '012012',
    '-----': '021021',
    '--+--': '021210',
    '+--++': '010201',
    '---++': '021012',
}


def labels(signs: str) -> str:
    """Cyclically relabel the first vertex as zero, then follow the signs."""
    result = [0]
    for sign in signs:
        if sign not in '+-':
            raise ValueError('Expected a binary switch sign.')
        result.append((result[-1] + (1 if sign == '+' else -1)) % 3)
    return ''.join(map(str, result))


def main() -> None:
    for signs, word in TARGETS.items():
        assert labels(signs) == word, (signs, word)
    all_blocks = [''.join(s) for s in product('+-', repeat=5)]
    allowed = [s for s in all_blocks if '+-+' not in s]
    assert len(all_blocks) == 32
    assert len(allowed) == 21
    remaining = [s for s in allowed if s not in TARGETS]
    vertices = sorted({s[:4] for s in allowed} | {s[1:] for s in allowed})
    successors = {v: [] for v in vertices}
    indegree = {v: 0 for v in vertices}
    for s in remaining:
        v, u = s[:4], s[1:]
        successors[v].append(u)
        indegree[u] += 1
    queue = sorted(v for v in vertices if indegree[v] == 0)
    order = []
    while queue:
        v = queue.pop(0)
        order.append(v)
        for u in sorted(successors[v]):
            indegree[u] -= 1
            if indegree[u] == 0:
                queue.append(u)
                queue.sort()
    assert len(order) == len(vertices), 'A surviving directed cycle invalidates coverage.'
    rank = {v: i for i, v in enumerate(order)}
    for s in remaining:
        assert rank[s[:4]] < rank[s[1:]], s
    print(f'Binary five-sign blocks: {len(all_blocks)}')
    print(f'Blocks avoiding the established +-+ exclusion: {len(allowed)}')
    print(f'Target edges removed: {len(TARGETS)}')
    print(f'Remaining edges: {len(remaining)}; vertices: {len(vertices)}')
    print('Topological order: ' + ' '.join(order))
    print('All remaining edges strictly increase rank: PASS')
    print('Only combinatorial coverage checked; all five analytic exclusions remain open.')


if __name__ == '__main__':
    main()
