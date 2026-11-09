from sympy import *
from gen import *
def lean_num_str(q):
    return lnum(F(q))
import pickle, time
t,x = symbols('t x')
C = [expand(c) for c in pickle.load(open('highT7C.pkl','rb'))]
R=Rational
hdr = """module

public import SmoothedOctagon.Exclusion.Mixed.Nonshort.Reverse.Bernstein

/-!
# Case M2, reverse successor: sign certificates for the high-ratio exclusion

On the face `k = 7t²`, the cleared cubic
`P = C₀ + C₁y + C₂y² + C₃y³` (`nsrTC0`, …, `nsrTC3`) has `C₀, C₁, C₃ > 0` on `2/5 ≤ t ≤ 1/2`, `1/7 ≤ x ≤ 1/3`, and on the four `x`-rows
`[1/7, 1/5]`, `[1/5, 3/10]`, `[3/10, 8/25]`, `[8/25, 1/3]` the bounds `C₁ > b`, `C₂ > -M`,
`C₃ > c` with `(b, M, c) = (9/10, 1, 20)`, `(3/2, 10, 26)`, `(17/10, 13, 38)`, `(3/2, 31/2, 41)`,
all with `4bc > M²`. Bernstein certificates (generated;
every identity is checked by `ring`). Route: in place of the coefficient monotonicity (10) and the
interval table of §4.

## Main API

* `nsrTC0`, …, `nsrTC3`; `nsrTC0_pos`; `nsrTCj_ri_pos` (`j = 1, 2, 3`, row `i = 0, …, 3`).
-/

@[expose] public section

namespace SmoothedOctagon
"""
out=[hdr]
for i,c in enumerate(C):
    out.append(f"/-- The coefficient of `y^{i}` of the cubic on the face `k = 7t²`. -/\nnoncomputable def nsrTC{i} (t x : ℝ) : ℝ :=\n  {lpoly(c,[t,x],['t','x'])}\n")
R=Rational
rows = [(R(1,7),R(1,5),R(9,10),1,20),(R(1,5),R(3,10),R(3,2),10,26),(R(3,10),R(8,25),R(17,10),13,38),(R(8,25),R(1,3),R(3,2),R(31,2),41)]
jobs = [('nsrTC0', C[0], R(1,7), R(1,3))]
for ri,(lo,hi,b,M,c) in enumerate(rows):
    jobs.append((f'nsrTC1_r{ri}', C[1]-b, lo, hi))
    jobs.append((f'nsrTC2_r{ri}', C[2]+M, lo, hi))
    jobs.append((f'nsrTC3_r{ri}', C[3]-c, lo, hi))
for name, e, lo, hi in jobs:
    t0=time.time()
    pl = plan_biv(e, t, x, lo, hi, lambda a,b: R(2,5), lambda a,b: R(1,2))
    print(name, [(float(p[0]),float(p[1]),p[4]) for p in pl], round(time.time()-t0,1))
    base = name.split('_')[0]
    stmt = f"{base} t x" if '_' not in name else None
    shift = e - C[int(base[-1])] if '_' in name else 0
    if '_' in name:
        stmt = f"{base} t x - ({lean_num_str(-shift)})"
    for pi,pc in enumerate(pl):
        code, nl = emit_biv_piece(f"{name}_p{pi}", e, t, x, 't', 'x', pc, stmt=stmt, unfold=base)
        out.append(code)
    lines=[f"theorem {name}_pos (t x : ℝ) (ht0 : 2 / 5 ≤ t) (ht1 : t ≤ 1 / 2) (hx0 : {lnum(F(lo))} ≤ x) (hx1 : x ≤ {lnum(F(hi))}) :",
           f"    0 < {stmt} := by"]
    cur = "hx0"
    for pi,pc in enumerate(pl):
        last = pi == len(pl)-1
        if last:
            lines.append(f"  exact {name}_p{pi} x t {cur} hx1 ht0 ht1 (by norm_num)")
        else:
            lines.append(f"  rcases le_total x {lnum(F(pc[1]))} with hc{pi} | hc{pi}")
            lines.append(f"  · exact {name}_p{pi} x t {cur} hc{pi} ht0 ht1 (by norm_num)")
            cur = f"hc{pi}"
    out.append("\n".join(lines)+"\n")
out.append("end SmoothedOctagon\n")
open('/home/vltanh/Documents/lean4-reinhardt-conjecture/SmoothedOctagon/Exclusion/Mixed/Nonshort/Reverse/HighRatio/Signs.lean','w').write("\n".join(out))
