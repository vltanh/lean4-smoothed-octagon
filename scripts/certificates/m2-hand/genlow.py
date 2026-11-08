from sympy import *
from gen import *
import pickle
t,x = symbols('t x')
res = pickle.load(open('lowQ.pkl','rb'))
def Jl(P):
    P0,P1,P2,P3,P4 = P
    return {0:P0, 1:P1+2*P0, 2:P2+48*P0, 3:P3+4*P2, 4:P3-P0, 5:P4-P0}
R=Rational
Tn = lambda xx: (-2*xx**3-xx**2+10*xx+12)/(3*(xx+2)**3)
hdr = """module

public import SmoothedOctagon.Exclusion.Mixed.Hand.Bern

/-!
# Case M2 by hand: generated sign certificates for the low-scale faces

The quartic `Q = P₀ + P₁y + ⋯ + P₄y⁴` of `MIXED_NONSHORT_LOW_SCALE_HAND_EXCLUSION` (7) on the unit
face `k = 1` (`nhLU0`, …, `nhLU4`) and on the high-ratio face `k = 2t + 1/2` (`nhLH0`, …,
`nhLH4`), and Bernstein certificates (generated; every identity is checked by `ring`) for the six
signs (9) `J₀ = P₀`, `J₁ = P₁ + 2P₀`, `J₂ = P₂ + 48P₀`, `J₃ = P₃ + 4P₂`, `J₄ = P₃ - P₀`,
`J₅ = P₄ - P₀`:

* unit face (`nhLUJ i`, `nhLUJ_dom i`): `1/2 < x ≤ 7/3`, `0 ≤ t ≤ 1/4`, `x ≥ 1 - 2t`,
  `3(x + 2)³t ≤ -2x³ - x² + 10x + 12` (i.e. `t ≤ T(x)`); for `x ≥ 1` the constraint `t ≤ T(x)` is
  used through `T(x) ≤ T(x_a)` on subintervals `[x_a, x_b]` (`nh_T_anti`);
* high-ratio face (`nhLHJ i`, `nhLHJ_dom i`): `1/4 ≤ t ≤ 7/20`, `1/2 ≤ x ≤ 1`.

Route: in place of the hand estimates of §§4-7 and of
`MIXED_NONSHORT_LOW_SCALE_HIGH_RATIO_DERIVATIVE`.
-/

@[expose] public section

namespace SmoothedOctagon

/-- `T` is decreasing: for `0 ≤ x_a ≤ x`, `N(x)(x_a + 2)³ ≤ N(x_a)(x + 2)³`,
`N(z) = -2z³ - z² + 10z + 12`. -/
theorem nh_T_anti {xa x t : ℝ} (ha : 0 ≤ xa) (hax : xa ≤ x) (ht : 0 ≤ t)
    (hT : 3 * (x + 2) ^ 3 * t ≤ -2 * x ^ 3 - x ^ 2 + 10 * x + 12) :
    3 * (xa + 2) ^ 3 * t ≤ -2 * xa ^ 3 - xa ^ 2 + 10 * xa + 12 := by
  have hx : 0 ≤ x := le_trans ha hax
  have hQ : 0 ≤ (x - xa) * (11 * xa ^ 2 * x ^ 2 + 34 * xa ^ 2 * x + 28 * xa ^ 2 + 34 * xa * x ^ 2
      + 100 * xa * x + 80 * xa + 28 * x ^ 2 + 80 * x + 64) := mul_nonneg (by linarith) (by positivity)
  have e : (-2 * xa ^ 3 - xa ^ 2 + 10 * xa + 12) * (x + 2) ^ 3 -
      (-2 * x ^ 3 - x ^ 2 + 10 * x + 12) * (xa + 2) ^ 3 =
      (x - xa) * (11 * xa ^ 2 * x ^ 2 + 34 * xa ^ 2 * x + 28 * xa ^ 2 + 34 * xa * x ^ 2
      + 100 * xa * x + 80 * xa + 28 * x ^ 2 + 80 * x + 64) := by ring
  have h1 : 3 * (x + 2) ^ 3 * t * (xa + 2) ^ 3 ≤ (-2 * x ^ 3 - x ^ 2 + 10 * x + 12) * (xa + 2) ^ 3 :=
    mul_le_mul_of_nonneg_right hT (by positivity)
  have h2 : 3 * (xa + 2) ^ 3 * t * (x + 2) ^ 3 ≤ (-2 * xa ^ 3 - xa ^ 2 + 10 * xa + 12) * (x + 2) ^ 3 := by
    nlinarith
  have hx3 : 0 < (x + 2) ^ 3 := by positivity
  nlinarith
"""
out=[hdr]
for face, tag in [('unit','U'),('kh','H')]:
    for j,pj in enumerate(res[face]):
        out.append(f"/-- The coefficient `P_{j}` of the low-scale quartic on the {'unit' if face=='unit' else 'high-ratio'} face. -/\nnoncomputable def nhL{tag}{j} (t x : ℝ) : ℝ :=\n  {lpoly(pj,[t,x],['t','x'])}\n")
for face, tag in [('unit','U'),('kh','H')]:
    J = Jl(res[face])
    for i in J:
        e = expand(J[i])
        nm = f"nhL{tag}J{i}"
        out.append(f"/-- The sign `J_{i}` on the {'unit' if face=='unit' else 'high-ratio'} face. -/\nnoncomputable def {nm} (t x : ℝ) : ℝ :=\n  {lpoly(e,[t,x],['t','x'])}\n")
        if face=='unit':
            p1 = plan_biv(e, t, x, R(1,2), Integer(1), lambda a,b: (1-x)/2, lambda a,b: R(1,4))
            p2 = plan_biv(e, t, x, Integer(1), R(7,3), lambda a,b: Integer(0), lambda a,b: Tn(a))
            pl = p1+p2
        else:
            pl = plan_biv(e, t, x, R(1,2), Integer(1), lambda a,b: R(1,4), lambda a,b: R(7,20))
        for pi,pc in enumerate(pl):
            code, nl = emit_biv_piece(f"{nm}_p{pi}", e, t, x, 't', 'x', pc, stmt=f"{nm} t x", unfold=nm)
            out.append(code)
        # domain theorem
        if face=='unit':
            lines = [f"/-- `J_{i} > 0` on the unit face. -/",
                     f"theorem {nm}_dom (t x : ℝ) (hx0 : 1 / 2 < x) (hx1 : x ≤ 7 / 3) (ht0 : 0 ≤ t) (ht1 : t ≤ 1 / 4)",
                     f"    (hxt : 1 - 2 * t ≤ x) (hT : 3 * (x + 2) ^ 3 * t ≤ -2 * x ^ 3 - x ^ 2 + 10 * x + 12) :",
                     f"    0 < {nm} t x := by"]
            for pi,pc in enumerate(pl):
                xa, xb = pc[0], pc[1]
                last = (pi == len(pl)-1)
                ind = "  "
                if pi == 0:
                    lines.append(f"  rcases le_total x 1 with hc0 | hc0")
                    lines.append(f"  · exact {nm}_p0 x t hx0.le hc0 (by linarith) ht1 (by linarith)")
                    continue
                cur = f"hc{pi-1}"
                body = []
                tau = Tn(xa)
                body.append(f"have hT' := nh_T_anti (xa := {lnum(F(xa))}) (by norm_num) {cur} ht0 hT")
                body.append(f"exact {nm}_p{pi} x t {cur} {'hx1' if last else 'hc'+str(pi)} ht0 (by norm_num at hT' ⊢; linarith) (by norm_num)")
                if last:
                    lines.extend(["  " + b for b in body])
                else:
                    lines.append(f"  rcases le_total x {lnum(F(xb))} with hc{pi} | hc{pi}")
                    lines.append("  · " + body[0])
                    lines.append("    " + body[1])
            out.append("\n".join(lines) + "\n")
        else:
            out.append(f"""/-- `J_{i} > 0` on the high-ratio face. -/
theorem {nm}_dom (t x : ℝ) (ht0 : 1 / 4 ≤ t) (ht1 : t ≤ 7 / 20) (hx0 : 1 / 2 ≤ x) (hx1 : x ≤ 1) :
    0 < {nm} t x :=
  {nm}_p0 x t hx0 hx1 ht0 ht1 (by norm_num)
""")
out.append("end SmoothedOctagon\n")
open('/home/vltanh/Documents/lean4-reinhardt-conjecture/SmoothedOctagon/Exclusion/Mixed/Hand/CertLow.lean','w').write("\n".join(out))
