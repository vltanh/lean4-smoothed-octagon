from common import *
from gen import *
import pickle
C = pickle.load(open('unitC.pkl','rb'))
C0,C1,C2,C3 = [expand(c) for c in pickle.load(open('unitC.pkl','rb'))]
J = {0:C0, 1: 20*x*C1+3*C0, 2: 53*C0+20*x**2*C2, 3: 24*x**3*C3+12*x**2*C2-C0, 4: 40*x**3*C3+30*x**2*C2+7*C0, 5: 24*x**3*C3-C0}
R=Rational
pieces = [("a", R(3,25),R(9,35), lambda a,b: R(9,35)-x, lambda a,b: x+x**2),
          ("b", R(9,35),R(2,5), lambda a,b: Integer(0), lambda a,b: x+x**2),
          ("c", R(2,5),Integer(1), lambda a,b: Integer(0), lambda a,b: 1-x)]
hdr = """module

public import SmoothedOctagon.Exclusion.Mixed.Nonshort.Bernstein

/-!
# Case M2, reverse successor: sign certificates for the unit shape

Bernstein-form certificates (generated; every identity is checked by `ring`) for the six signs
`J₀ = C₀`, `J₁, …, J₄`, `J_*` of the unit shape, in the coordinates
`(x, s)`, `s = 1 - 2t - x`, after division by `x²`. The domain
`0 < t ≤ 13/35, 0 < x ≤ 1 - 2t, 1 < 2t + 2x + x²` is covered by the three pieces
`x ∈ [3/25, 9/35], s ∈ [9/35 - x, x + x²]`; `x ∈ [9/35, 2/5], s ∈ [0, x + x²]`;
`x ∈ [2/5, 1], s ∈ [0, 1 - x]`. On each piece the polynomial is written in Bernstein form of degree
three in `s` with polynomial coefficients in `x`, each positive by a univariate Bernstein bound.
Route: Bernstein certificates on three pieces.

## Main API

* `nsrUJr i x s` (`i = 0, …, 5`): the polynomials `J_i/x²` at `t = (1 - x - s)/2`.
* `nsrUJr_pos_a`, `_b`, `_c`: their positivity on the three pieces.
-/

@[expose] public section

namespace SmoothedOctagon
"""
out=[hdr]
names = {0:'nsrUJr0',1:'nsrUJr1',2:'nsrUJr2',3:'nsrUJr3',4:'nsrUJr4',5:'nsrUJr5'}
tot=0
for i in J:
    e = expand(cancel(J[i].subs(t,(1-x-s)/2)/x**2))
    out.append(f"/-- `J_{i}/x²` of the unit shape at `t = (1 - x - s)/2`. -/\nnoncomputable def {names[i]} (x s : ℝ) : ℝ :=\n  {lpoly(e,[x,s],['x','s'])}\n")
    for (tag,lo,hi,S0f,S1f) in pieces:
        pl = plan_biv(e, s, x, lo, hi, S0f, S1f)
        assert len(pl)==1
        code, nl = emit_biv_piece(f"{names[i]}_pos_{tag}", e, s, x, 's', 'x', pl[0], stmt=f"{names[i]} x s", unfold=names[i])
        tot+=nl
        out.append(code)
out.append("end SmoothedOctagon\n")
open('/home/vltanh/Documents/lean4-reinhardt-conjecture/SmoothedOctagon/Exclusion/Mixed/Nonshort/UnitShape/Signs.lean','w').write("\n".join(out))
print('leaves', tot)
