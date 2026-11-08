import sys, nonshort, expr, fx
mode = sys.argv[1]   # R or S
nbox = int(sys.argv[2])
which = sys.argv[3]  # residual name
g, nm = nonshort.build(1)
roots = [x.i for x in g]
text, defname = expr.emit_lean(roots, 'ns1_', nm)
idx = nm.index(which)
lines = ['module', '', 'public import SmoothedOctagon.Interval.Check', '', '@[expose] public section', '',
         'namespace SmoothedOctagon.Interval.Test', '', 'open SmoothedOctagon.Interval', '', text, '',
         'def fs : List IExpr := [' + ', '.join(defname[r] for r in roots) + ']', '']
boxes = []
import random
random.seed(1)
cert_ok = []
for k in range(nbox):
    vals = [0.66 + 0.001*k, 1.40, 0.3, 0.5]
    w = 1e-4
    B = [(int(v*fx.U)-int(w*fx.U), int(v*fx.U)+int(w*fx.U)) for v in vals]
    if mode == 'R':
        r = expr.evalR(B, roots[idx], {})
        ok = r is not None and r[1] < 0
    else:
        s = expr.evalS(B, roots[idx], {})
        ok = s is not None and expr.slope_hi(B, s) < 0
    cert_ok.append(ok)
    boxes.append(B)
print('python verdicts', sum(cert_ok), 'of', nbox, file=sys.stderr)
def lb(B):
    return '[' + ', '.join(f'⟨{lo}, {hi}⟩' for lo, hi in B) + ']'
lines.append('def boxes : List (List Ival) := [' + ',\n  '.join(lb(B) for B in boxes) + ']')
leaf = f'.byR {idx}' if mode == 'R' else f'.byS [({idx}, 1)]'
lines.append(f'def leaf : Cert := {leaf}')
lines.append('theorem test : (boxes.all fun B => check fs B leaf) = true := by decide +kernel')
lines.append('end SmoothedOctagon.Interval.Test')
print('\n'.join(lines))
