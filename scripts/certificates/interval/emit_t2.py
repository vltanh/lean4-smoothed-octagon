import sys, nonshort, expr, fx
# args: mode(R/S) nbox residual-name
mode, nbox, which = sys.argv[1], int(sys.argv[2]), sys.argv[3]
g, nm = nonshort.build(1)
roots = [x.i for x in g]
text, defname = expr.emit_lean(roots, 'ns1_', nm)
lines = ['module', '', 'public import SmoothedOctagon.Interval.Check', '', '@[expose] public section', '',
         'namespace SmoothedOctagon.Interval.Test', '', 'open SmoothedOctagon.Interval', '', text, '']
boxes = []
for k in range(nbox):
    vals = [0.66 + 0.001*k, 1.40, 0.3, 0.5]
    w = 1e-4
    boxes.append([(int(v*fx.U)-int(w*fx.U), int(v*fx.U)+int(w*fx.U)) for v in vals])
def lb(B):
    return '[' + ', '.join(f'⟨{lo}, {hi}⟩' for lo, hi in B) + ']'
lines.append('def boxes : List (List Ival) := [' + ',\n  '.join(lb(B) for B in boxes) + ']')
if which.startswith('hpt'):
    # time hPt at z values
    lines.append('def zs : List ℕ := [' + ', '.join(str(int((0.3+0.001*k)*fx.U)) for k in range(nbox)) + ']')
    lines.append('theorem test : (zs.all fun z => (Ival.hPt z).elim false fun I => zle I.lo I.hi) = true := by decide +kernel')
else:
    if which in nm:
        e = defname[roots[nm.index(which)]]
    else:
        e = which
    if mode == 'R':
        lines.append(f'theorem test : (boxes.all fun B => ({e}.evalR B).elim false fun I => zle I.lo I.hi) = true := by decide +kernel')
    else:
        lines.append(f'theorem test : (boxes.all fun B => ({e}.evalS B).elim false fun s => zle (Slope.bound B s).lo (Slope.bound B s).hi && zle s.r.lo s.r.hi) = true := by decide +kernel')
lines.append('end SmoothedOctagon.Interval.Test')
print('\n'.join(lines))
