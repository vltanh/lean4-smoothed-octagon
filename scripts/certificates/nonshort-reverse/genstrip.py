from sympy import *
from gen import *
import pickle
t,x = symbols('t x')
C = [expand(c) for c in pickle.load(open('stripC.pkl','rb'))]
C0,C1,C2,C3 = C
J = {0:C0, 1: 20*x*C1+3*C0, 2: 53*C0+20*x**2*C2, 3: 24*x**3*C3+12*x**2*C2-C0, 4: 40*x**3*C3+30*x**2*C2+7*C0, 5: 24*x**3*C3-C0}
R=Rational
f = R(29,4)*t**2-2*t
S0 = expand(R(175,416)*(f+R(27,875)))
hdr = """module

public import SmoothedOctagon.Exclusion.Mixed.Hand.Bern

/-!
# Case M2 by hand: generated sign certificates for the reverse scale strip

On the scale face `k = 29t²/4` (`MIXED_NONSHORT_REVERSE_HAND_EXCLUSION` §§2-3), the cleared
cubic `P = C₀ + C₁y + C₂y² + C₃y³` (`nhSC0`, …, `nhSC3`) satisfies the same six signs as on the
unit shape (`MIXED_NONSHORT_UNIT_SHAPE_HAND_EXCLUSION` (7)) throughout the strip
`13/35 ≤ t ≤ 2/5`, `x ≤ 9/35`, `29t²/4 < 2t + 2x + x²`. Since `x ≥ 3/25` there, the chord bound
`2x + x² ≤ (416/175)x - 27/875` gives `x ≥ (175/416)(29t²/4 - 2t + 27/875)`, so the strip lies in
`t ∈ [13/35, 2/5]`, `x ∈ [(175/416)(29t²/4 - 2t + 27/875), 9/35]`. Bernstein certificates in `x`
with univariate Bernstein bounds in `t` (generated; every identity is checked by `ring`).
Route: in place of the coefficient monotonicity (4)-(6) and the comparison with the unit shape at
`t₀ = 13/35`.

## Main API

* `nhSC0`, …, `nhSC3`; `nhSJr i t x` (`= J_i/x²`); `nhSJr_pos i`.
-/

@[expose] public section

namespace SmoothedOctagon
"""
out=[hdr]
for i,c in enumerate(C):
    out.append(f"/-- The coefficient of `y^{i}` of the scale-face cubic `P_{{29t²/4}}`. -/\nnoncomputable def nhSC{i} (t x : ℝ) : ℝ :=\n  {lpoly(c,[t,x],['t','x'])}\n")
for i in J:
    e = expand(cancel(J[i]/x**2))
    out.append(f"/-- `J_{i}/x²` on the scale face. -/\nnoncomputable def nhSJr{i} (t x : ℝ) : ℝ :=\n  {lpoly(e,[t,x],['t','x'])}\n")
    pl = plan_biv(e, x, t, R(13,35), R(2,5), lambda a,b: S0.subs(t,a), lambda a,b: R(9,35))
    print(i, [(float(p[0]),float(p[1]),p[4]) for p in pl])
    for j,pc in enumerate(pl):
        code, nl = emit_biv_piece(f"nhSJr{i}_pos{j}", e, x, t, 'x', 't', pc, stmt=f"nhSJr{i} t x", unfold=f"nhSJr{i}")
        out.append(code)
out.append("end SmoothedOctagon\n")
open('/home/vltanh/Documents/lean4-reinhardt-conjecture/SmoothedOctagon/Exclusion/Mixed/Hand/CertStrip.lean','w').write("\n".join(out))
