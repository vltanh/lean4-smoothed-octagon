#!/usr/bin/env python3
"""Write scripts/Audit.lean: one `import all` line per module of the project's libraries, then
the check. Run from the repository root after adding or removing modules:

    python3 scripts/gen_audit.py && lake env lean scripts/Audit.lean
"""
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
LIBS = ['SmoothedOctagon', 'Cited']
mods = []
for lib in LIBS:
    for f in sorted((ROOT / lib).rglob('*.lean')):
        mods.append('.'.join(f.relative_to(ROOT).with_suffix('').parts))
mods += ['SmoothedOctagon'] if (ROOT / 'SmoothedOctagon.lean').exists() else []
head = '''module

public meta import Lean.Elab.Command
'''
imports = ''.join(f'import all {m}\n' for m in sorted(set(mods)) + ['ReinhardtSolution'])
body = (ROOT / 'scripts' / 'Audit.lean.in').read_text()
(ROOT / 'scripts' / 'Audit.lean').write_text(head + imports + body)
print(f'scripts/Audit.lean: {len(set(mods)) + 1} modules')
