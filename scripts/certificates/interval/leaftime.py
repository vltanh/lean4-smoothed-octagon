"""Collect real leaves of given kinds from a run and emit a Lean timing file (full residual list)."""
import sys, pickle, random
import run, nonshort, expr, fx, certemit
res = pickle.load(open(sys.argv[1], 'rb'))
chart = int(sys.argv[2]); kinds = sys.argv[3].split(','); per = int(sys.argv[4])
prob = run.make(chart, False)
B0 = nonshort.root_box()
found = {k: [] for k in kinds}
def walk(c, B):
    if c[0] == 'split':
        j = c[1]; lo, hi = B[j]; m = (lo + hi) >> 1
        BL = list(B); BL[j] = (lo, m); BR = list(B); BR[j] = (m, hi)
        walk(c[2], BL); walk(c[3], BR)
        return
    if c[0] == 'R':
        key = 'R:' + prob.names[c[1]]
    elif len(c[1]) == 1:
        key = 'S:' + prob.names[c[1][0][0]]
    else:
        key = 'L'
    if key in found and len(found[key]) < 400:
        found[key].append((B, c))
for p, ok, c, st in res:
    if not ok: continue
    B = B0
    for bit in p:
        j = prob.split_axis(B); lo, hi = B[j]; m = (lo + hi) >> 1
        B = list(B); B[j] = (lo, m) if bit == 0 else (m, hi)
    walk(c, B)
g, gn = nonshort.build(chart, int(__import__('os').environ.get('BRANCH', '0')))
roots = [x.i for x in g]
text, defname = expr.emit_lean(roots, 'tt_', gn)
out = ['module', '', 'public import SmoothedOctagon.Interval.Check', '', '@[expose] public section', '',
       'namespace SmoothedOctagon.Interval.Timing', 'open SmoothedOctagon.Interval', '', text, '',
       'def fs : List IExpr := [' + ', '.join(defname[r] for r in roots) + ']', '', 'set_option profiler true']
random.seed(0)
for k in kinds:
    sel = random.sample(found[k], min(per, len(found[k])))
    print(k, len(found[k]), 'selected', len(sel), file=sys.stderr)
    # each leaf must pass
    for B, c in sel:
        assert certemit.pycheck(roots, B, c)
    items = ', '.join(f'({certemit.lean_box(B)}, {certemit.lean_cert(c)})' for B, c in sel)
    nm = k.replace(':', '_').replace('+', '_')
    out.append(f'def L_{nm} : List (List Ival × Cert) := [{items}]')
    out.append(f'theorem T_{nm} : (L_{nm}.all fun p => check fs [] p.1 p.2) = true := by decide +kernel')
out.append('end SmoothedOctagon.Interval.Timing')
print('\n'.join(out))
