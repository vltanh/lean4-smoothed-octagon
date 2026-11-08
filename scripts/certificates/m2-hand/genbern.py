def term(j, d):
    fs = [f"c{j}"]
    if j >= 1: fs.append("a" if j == 1 else f"a ^ {j}")
    if d-j >= 1: fs.append("b" if d-j == 1 else f"b ^ {d-j}")
    return " * ".join(fs)
out = ["""module

public import Mathlib.Basic.Real.Basic
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.Ring

/-!
# Case M2 by hand: positivity of Bernstein forms

`nh_bern_pos1`, …, `nh_bern_pos6`: for `a, b ≥ 0` with `a + b > 0` and positive coefficients
`c₀, …, c_d`, the Bernstein form `∑ c_j a^j b^(d-j)` is positive. Used by the generated polynomial
sign certificates of `Hand/Cert*`.
-/

@[expose] public section

namespace SmoothedOctagon
"""]
for d in range(1, 15):
    cs = " ".join(f"c{j}" for j in range(d+1))
    hs = " ".join(f"(h{j} : 0 < c{j})" for j in range(d+1))
    expr = " + ".join(term(j, d) for j in range(d+1))
    rest0 = " + ".join(term(j, d) for j in range(1, d+1))
    restd = " + ".join(term(j, d) for j in range(0, d))
    out.append(f"""theorem nh_bern_pos{d} {{a b : ℝ}} (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : 0 < a + b) {{{cs} : ℝ}}
    {hs} :
    0 < {expr} := by
  rcases lt_or_ge 0 a with h | h
  · have h' : 0 < {term(d, d)} := by positivity
    have h'' : 0 ≤ {restd} := by positivity
    linarith
  · have hb' : 0 < b := by linarith
    have h' : 0 < {term(0, d)} := by positivity
    have h'' : 0 ≤ {rest0} := by positivity
    linarith
""")
out.append("end SmoothedOctagon\n")
open('/home/vltanh/Documents/lean4-reinhardt-conjecture/SmoothedOctagon/Exclusion/Mixed/Hand/Bern.lean','w').write("\n".join(out))
