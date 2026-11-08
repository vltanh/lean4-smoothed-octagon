#!/usr/bin/env python3
"""Copy the shared definitions of library modules into `Challenge.lean`, or check the copies.

Comparator requires every constant that a Challenge statement uses to be the same in the
Challenge and in the Solution's environment. When the statements need definitions too large to
restate inline, keep them in library modules between marker lines (the blocks below), and let this
script copy each block verbatim into `Challenge.lean`, which may not import the project.
The Solution imports the library, so both environments then contain the same definitions.

Run from the repository root:

    python3 scripts/sync_challenge_defs.py           # rewrite the blocks in the Challenge
    python3 scripts/sync_challenge_defs.py --check   # exit 1 if the copy differs (for CI)

Configure the blocks below for the project.
"""

import sys
from pathlib import Path

# ---- configuration -------------------------------------------------------------------------
# The Challenge file, and the shared blocks: the library module each is copied from, and the marker
# lines around it, in both files.
CHALLENGE = 'ReinhardtChallenge.lean'
BLOCKS = [
    ('.lake/packages/SmoothedPolygons/SmoothedPolygons/Defs.lean',
     '-- BEGIN SHARED DEFINITIONS\n', '-- END SHARED DEFINITIONS\n'),
    ('SmoothedOctagon/Defs.lean', '-- BEGIN SHARED OCTAGON\n', '-- END SHARED OCTAGON\n'),
]
# ---------------------------------------------------------------------------------------------

ROOT = Path(__file__).resolve().parent.parent


def block(text: str, name: str, begin: str, end: str) -> tuple[int, int]:
    """The span of the shared block in `text`, markers included."""
    i, j = text.find(begin), text.find(end)
    if i < 0 or j < i or text.count(begin) != 1 or text.count(end) != 1:
        sys.exit(f'{name}: expected exactly one pair of markers {begin.strip()!r}')
    return i, j + len(end)


def main() -> None:
    args = sys.argv[1:]
    if args and args[0] in ('-h', '--help') or any(a != '--check' for a in args):
        print(__doc__.strip())
        sys.exit(0 if args and args[0] in ('-h', '--help') else 2)
    check = '--check' in args
    chal_path = ROOT / CHALLENGE
    chal = chal_path.read_text()
    for defs_rel, begin, end in BLOCKS:
        defs = (ROOT / defs_rel).read_text()
        di, dj = block(defs, defs_rel, begin, end)
        ci, cj = block(chal, CHALLENGE, begin, end)
        shared = defs[di:dj]
        if check:
            if chal[ci:cj] != shared:
                sys.exit(f'{CHALLENGE}: the shared definitions differ from {defs_rel}; '
                         f'run python3 scripts/sync_challenge_defs.py')
            print(f'{CHALLENGE}: the shared definitions match {defs_rel}')
        else:
            chal = chal[:ci] + shared + chal[cj:]
            print(f'{CHALLENGE}: shared definitions copied from {defs_rel}')
    if not check:
        chal_path.write_text(chal)


if __name__ == '__main__':
    main()
