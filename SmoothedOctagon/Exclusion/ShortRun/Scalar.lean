module

public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Analysis.SpecialFunctions.Log.Deriv

/-!
# Case M1: the reverse-centre angle gap

`MIXED_GLOBAL_SHORT_RUN_ANGLE_EXCLUSION` (1), (3)-(19): the scalar part.

At a reverse centre of a mixed normal period, with `r = a/(a + p)`, `t = a/(a + n)`,
`ρ = a²/(a² + 4)`, `u = 8 d_-`, `v = 8 d_+`, `E = 16 e` and `γ² = det U`, the data satisfy
(`m1_CentreData`): `0 < r, t < 1/2`, `0 < ρ < r t`, `3/4 ≤ u ≤ U(r)`, `3/4 ≤ v ≤ U(t)`
(`U(s) = 1 - s + s²`), the stationarity
`E = 1 + r + t - ρ + log(ρ/(r t)) - (1 - u)/r - (1 - v)/t` and the Gram identity
`16 (1 - ρ)² γ² = 4uv - E²`.

## Main API

* `m1_CentreData`: the scalar data of a reverse centre.
* `m1_angle_gap`: under the competitive cap `γ² ≤ 97969/529200`, `E < (3/5) √(uv)`, i.e. the
  centre angle `φ = arccos(E/(2√(uv)))` has `cos φ < 3/10` (MGSRAE (1)).
* `m1_cos_two_pi_div_five`: `cos(2π/5) = (√5 - 1)/4 > 3/10`; `m1_arccos_gt`: `arccos c > 2π/5`
  for `c < 3/10`.
-/

@[expose] public section

namespace SmoothedOctagon

open Real

/-- **The scalar data of a reverse centre** (MGSRAE (3)-(6)). -/
structure m1_CentreData (γ2 r t ρ u v E : ℝ) : Prop where
  r_pos : 0 < r
  r_lt : r < 1 / 2
  t_pos : 0 < t
  t_lt : t < 1 / 2
  ρ_pos : 0 < ρ
  ρ_lt : ρ < r * t
  u_ge : 3 / 4 ≤ u
  u_le : u ≤ 1 - r + r ^ 2
  v_ge : 3 / 4 ≤ v
  v_le : v ≤ 1 - t + t ^ 2
  stat : E = 1 + r + t - ρ + Real.log (ρ / (r * t)) - (1 - u) / r - (1 - v) / t
  gram : 16 * (1 - ρ) ^ 2 * γ2 = 4 * u * v - E ^ 2

/-- **The reverse-centre angle gap** (MGSRAE (1)): under the competitive Casimir cap, the centre
angle has `cos φ = E/(2√(uv)) < 3/10`. -/
theorem m1_angle_gap {γ2 r t ρ u v E : ℝ} (h : m1_CentreData γ2 r t ρ u v E)
    (hcap : γ2 ≤ 97969 / 529200) : E < 3 / 5 * √(u * v) := by
  sorry

/-- `cos(2π/5) = (√5 - 1)/4`. -/
theorem m1_cos_two_pi_div_five : Real.cos (2 * π / 5) = (√5 - 1) / 4 := by
  have h := Real.cos_pi_div_five
  have e : 2 * π / 5 = 2 * (π / 5) := by ring
  rw [e, Real.cos_two_mul, h]
  have h5 : √5 ^ 2 = 5 := Real.sq_sqrt (by norm_num)
  ring_nf
  rw [h5]
  ring

theorem m1_three_tenths_lt_cos : 3 / 10 < Real.cos (2 * π / 5) := by
  rw [m1_cos_two_pi_div_five]
  have : (11 / 5 : ℝ) < √5 := by
    rw [show (11 / 5 : ℝ) = √((11 / 5) ^ 2) by rw [Real.sqrt_sq (by norm_num)]]
    exact Real.sqrt_lt_sqrt (by norm_num) (by norm_num)
  linarith

/-- `c < 3/10` gives `arccos c > 2π/5`. -/
theorem m1_arccos_gt {c : ℝ} (hc : c < 3 / 10) : 2 * π / 5 < Real.arccos c := by
  have hcos := m1_three_tenths_lt_cos
  have hpi := Real.pi_pos
  rcases le_or_gt c (-1) with h1 | h1
  · rw [Real.arccos_eq_pi.2 h1]; linarith
  · have hmem : Real.cos (2 * π / 5) ∈ Set.Icc (-1 : ℝ) 1 :=
      ⟨Real.neg_one_le_cos _, Real.cos_le_one _⟩
    have hc' : c ∈ Set.Icc (-1 : ℝ) 1 := ⟨h1.le, by linarith⟩
    have := Real.strictAntiOn_arccos hc' hmem (by linarith)
    rwa [Real.arccos_cos (by positivity) (by linarith)] at this

end SmoothedOctagon
