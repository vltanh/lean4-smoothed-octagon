"""Regenerate SmoothedOctagon/Interval/SmallerShort.lean with a two-level combination."""
import sys, pickle, re
import smaller
from certemit import lean_cert, lean_box, children_boxes, kids
OUT = sys.argv[1]; G = int(sys.argv[2])
toptree, units = pickle.load(open('/tmp/claude-1000/-home-vltanh-Documents-lean4-reinhardt-conjecture/23f01b18-e411-49a2-8c2c-64188fa6f57f/scratchpad/iv/final_state.pkl', 'rb'))
B0 = smaller.root_box()
def nholes(t):
    if t[0] == 'hole':
        return 1
    if t[0] in ('split', 'cut'):
        a, b = kids(t); return nholes(a) + nholes(b)
    return 0
def group_level(tree, B):
    groups = []
    def grp(t, B):
        if nholes(t) <= G or t[0] not in ('split', 'cut'):
            idx = []
            def ren(t):
                if t[0] == 'hole':
                    idx.append(t[1]); return ('hole', len(idx) - 1)
                if t[0] in ('split', 'cut'):
                    a, b = kids(t); l = ren(a); r = ren(b)
                    return ('split', t[1], l, r) if t[0] == 'split' else ('cut', t[1], t[2], l, r)
                return t
            t2 = ren(t); groups.append((B, t2, idx)); return ('hole', len(groups) - 1)
        BL, BR = children_boxes(t, B); a, b = kids(t)
        l = grp(a, BL); r = grp(b, BR)
        return ('split', t[1], l, r) if t[0] == 'split' else ('cut', t[1], t[2], l, r)
    return grp(tree, B), groups
def forall_term(names):
    return names[0] if len(names) == 1 else '⟨' + ', '.join(names) + '⟩'
old = open(OUT).read()
head = old[:old.index('namespace SmoothedOctagon.Interval')]
tail_i = old.index('theorem mem_of_le')
tail = old[tail_i:]
body = ['namespace SmoothedOctagon.Interval', '', 'namespace SS', '',
        f'/-- `B₀`, rounded outward. -/\nnoncomputable def rootBox : List Ival := {lean_box(B0)}', '']
names = [(f'p{k:04d}_box', f'p{k:04d}_ok') for k in range(len(units))]
tree = toptree; level = 0
while nholes(tree) > G:
    level += 1
    tree, groups = group_level(tree, B0)
    print('level', level, 'groups', len(groups), file=sys.stderr)
    new = []
    for gi, (B, t, idx) in enumerate(groups):
        pre = f'g{level}_{gi}'
        body.append(f'/-- Box of group {pre} ({len(idx)} entries). -/')
        body.append(f'noncomputable def {pre}_box : List Ival := {lean_box(B)}')
        body.append(f'/-- Entries of group {pre}. -/')
        body.append(f'noncomputable def {pre}_done : List (List Ival) := [' + ', '.join(names[k][0] for k in idx) + ']')
        body.append(f'/-- Subdivision of group {pre}. -/')
        body.append(f'noncomputable def {pre}_top : Cert := {lean_cert(t)}')
        body.append(f'theorem {pre}_ok : Excluded r_fs {pre}_box :=')
        body.append(f'  excluded_of_check_done (fs := r_fs) (done := {pre}_done) (c := {pre}_top) (by decide +kernel)')
        body.append('    ' + forall_term([names[k][1] for k in idx]))
        body.append('')
        new.append((f'{pre}_box', f'{pre}_ok'))
    names = new
idx = []
def ren(t):
    if t[0] == 'hole':
        idx.append(t[1]); return ('hole', len(idx) - 1)
    if t[0] in ('split', 'cut'):
        a, b = kids(t); l = ren(a); r = ren(b)
        return ('split', t[1], l, r) if t[0] == 'split' else ('cut', t[1], t[2], l, r)
    return t
root = ren(tree)
body.append('/-- The top-level boxes. -/')
body.append('noncomputable def rootDone : List (List Ival) := [' + ', '.join(names[k][0] for k in idx) + ']')
body.append(f'/-- The top of the subdivision. -/\nnoncomputable def rootTop : Cert := {lean_cert(root)}')
body.append('/-- All of `rootBox` is excluded. -/')
body.append('theorem root_excluded : Excluded r_fs rootBox :=')
body.append('  excluded_of_check_done (fs := r_fs) (done := rootDone) (c := rootTop) (by decide +kernel)')
body.append('    ' + forall_term([names[k][1] for k in idx]))
body.append('')
open(OUT, 'w').write(head + '\n'.join(body) + '\n' + tail)
