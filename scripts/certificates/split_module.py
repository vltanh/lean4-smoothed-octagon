#!/usr/bin/env python3
"""Split a generated certificate module into a chain of smaller modules.

usage: split_module.py FILE.lean PARTS

Lean keeps the elaboration data of every declaration of a file until the file is done, so a file of
many generated identities needs memory in proportion to its length (`FwdHand/CertLGa.lean` peaked
at 26 GB). Splitting it into a chain bounds the memory of each step.

FILE must have the layout of the generated certificates: `module`, imports, a module docstring,
`@[expose] public section`, `namespace SmoothedOctagon`, top-level declarations, `end SmoothedOctagon`.
Its declarations are cut, in order, into PARTS pieces of about equal size. Pieces 1, …, PARTS - 1
become `<Dir>/<Name>/Part<i>.lean`, each importing the previous one; the last piece stays in FILE,
under its own module name, so its importers are unchanged. `private` is dropped, since later pieces
refer to earlier declarations. Running the script again on an already split FILE is refused.
"""
import re
import sys
from pathlib import Path

DECL = re.compile(r'^(?:/--|(?:private )?(?:noncomputable )?(?:theorem|lemma|def) )', re.M)


def main():
    path, parts = Path(sys.argv[1]), int(sys.argv[2])
    text = path.read_text()
    if f'{path.stem}.Part' in text:
        sys.exit(f'{path} is already split')
    ns = text.index('namespace SmoothedOctagon\n') + len('namespace SmoothedOctagon\n')
    end = text.rindex('end SmoothedOctagon')
    header, body = text[:ns], text[ns:end]
    starts = [m.start() for m in DECL.finditer(body)]
    # A docstring belongs to the declaration that follows it.
    starts = [s for i, s in enumerate(starts)
              if not (i > 0 and body[starts[i - 1]:starts[i - 1] + 3] == '/--'
                      and '-/' in body[starts[i - 1]:s] and body[starts[i - 1]:s].rstrip().endswith('-/'))]
    decls = [body[s:e] for s, e in zip(starts, starts[1:] + [len(body)])]
    assert ''.join(decls).strip() == body.strip(), 'unexpected text between declarations'
    decls = [re.sub(r'^private ', '', d, flags=re.M) for d in decls]
    total, target = sum(map(len, decls)), sum(map(len, decls)) / parts
    pieces, cur, size = [], [], 0
    for d in decls:
        if cur and size + len(d) / 2 > target * (len(pieces) + 1) and len(pieces) < parts - 1:
            pieces.append(cur)
            cur = []
        cur.append(d)
        size += len(d)
    pieces.append(cur)

    module = '.'.join(path.with_suffix('').parts)
    imports = re.findall(r'^public import .*$', header, re.M)
    doc = re.search(r'/-!.*?-/', header, re.S).group(0)
    name = path.stem
    (path.parent / name).mkdir(exist_ok=True)
    prev = None
    for i, piece in enumerate(pieces, 1):
        last = i == len(pieces)
        imp = imports if prev is None else [f'public import {prev}']
        if last:
            note = (f'\n\nThe certificate is split into a chain of {len(pieces)} modules to bound the '
                    f'memory of each (`scripts/certificates/split_module.py`); this is the last, and '
                    f'`{name}/Part1` … `{name}/Part{len(pieces) - 1}` hold the earlier declarations.')
            pdoc = doc[:-2].rstrip() + note + '\n-/'
            out = path
        else:
            pdoc = (f'/-!\n# Generated certificate `{name}`, part {i} of {len(pieces)}\n\n'
                    f'Declarations {i} of the split of `{module}`; see that module for the '
                    f'statement.\n-/')
            out = path.parent / name / f'Part{i}.lean'
        out.write_text('module\n\n' + '\n'.join(imp) + '\n\n' + pdoc +
                       '\n\n@[expose] public section\n\nnamespace SmoothedOctagon\n\n' +
                       ''.join(piece).rstrip() + '\n\nend SmoothedOctagon\n')
        prev = f'{module}.Part{i}'
        print(f'{out}: {len(piece)} declarations, {sum(map(len, piece))} bytes')


if __name__ == '__main__':
    main()
