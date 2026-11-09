module

public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Analysis.SpecialFunctions.Log.Deriv
public import SmoothedOctagon.Exclusion.ShortRun.Gap.Core

/-!
# Case M1: the reverse-centre angle gap

At a reverse centre of a mixed normal period, with `r = a/(a + p)`, `t = a/(a + n)`,
`ρ = a²/(a² + 4)`, `u = 8 d_-`, `v = 8 d_+`, `E = 16 e` and `γ² = det U`, the data satisfy
(`m1_CentreData`): `0 < r, t < 1/2`, `0 < ρ < r t`, `3/4 ≤ u ≤ U(r)`, `3/4 ≤ v ≤ U(t)`
(`U(s) = 1 - s + s²`), the stationarity
`E = 1 + r + t - ρ + log(ρ/(r t)) - (1 - u)/r - (1 - v)/t` and the Gram identity
`16 (1 - ρ)² γ² = 4uv - E²`.

## Main API

* `m1_CentreData`: the scalar data of a reverse centre.
* `m1_angle_gap`: under the competitive cap `γ² ≤ 97969/529200`, `E < (3/5) √(uv)`, i.e. the
  centre angle `φ = arccos(E/(2√(uv)))` has `cos φ < 3/10`.
* `m1_cos_two_pi_div_five`: `cos(2π/5) = (√5 - 1)/4 > 3/10`; `m1_arccos_gt`: `arccos c > 2π/5`
  for `c < 3/10`.
-/

@[expose] public section

namespace SmoothedOctagon

open Real

/-- **The scalar data of a reverse centre**: the ranges of `r, t, ρ, u, v`, the stationarity
identity for `E` and the Gram identity for `γ²`. -/
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

/-- **The reverse-centre angle gap**: under the competitive Casimir cap, the centre angle has
`cos φ = E/(2√(uv)) < 3/10`.

Each factor is moved to its boundary `u = U(r')` at fixed `u` (`ag_phi_le`), the two factors are
merged at fixed `uv` by the superadditivity of `σ(x) = -x - log(1 - x)` in `x²`
(`ag_sigma_superadd`), and the remaining two-variable inequality is closed by tangent lines of
`log`, an S-procedure multiplier and concavity in `z = 4ρ/(1 - S)` (`ag_core`). -/
theorem m1_angle_gap {γ2 r t ρ u v E : ℝ} (h : m1_CentreData γ2 r t ρ u v E)
    (hcap : γ2 ≤ 97969 / 529200) : E < 3 / 5 * √(u * v) := by
  by_contra hlt
  rw [not_lt] at hlt
  obtain ⟨hs0, hs1, hs2, hrs, hφr⟩ := ag_phi_le h.r_pos h.r_lt h.u_ge h.u_le
  obtain ⟨hs'0, hs'1, hs'2, hts, hφt⟩ := ag_phi_le h.t_pos h.t_lt h.v_ge h.v_le
  set s := √(4 * u - 3) with hs
  set s' := √(4 * v - 3) with hs'
  have hr0 := h.r_pos
  have ht0 := h.t_pos
  have hρ0 := h.ρ_pos
  -- `E = 1 - ρ + log ρ + φ_u(r) + φ_v(t)`
  have hEdec : E = 1 - ρ + Real.log ρ + (r - Real.log r - (1 - u) / r) +
      (t - Real.log t - (1 - v) / t) := by
    rw [h.stat, Real.log_div hρ0.ne' (mul_pos hr0 ht0).ne', Real.log_mul hr0.ne' ht0.ne']; ring
  have huv : 9 / 16 ≤ u * v := by
    have := mul_le_mul h.u_ge h.v_ge (by norm_num) (by linarith [h.u_ge])
    linarith
  have hW : 3 / 4 ≤ √(u * v) := (Real.le_sqrt (by norm_num) (by linarith)).2 (by linarith)
  have hE45 : 9 / 20 ≤ E := by linarith
  have h1s : 0 < 1 - s := by linarith
  have h1s' : 0 < 1 - s' := by linarith
  have h4ρ : 4 * ρ < (1 - s) * (1 - s') := by
    have := mul_le_mul hrs hts (by linarith) h1s.le
    linarith [h.ρ_lt]
  have hlog4 : Real.log (4 * ρ) = 2 * Real.log 2 + Real.log ρ := by
    rw [Real.log_mul (by norm_num) hρ0.ne', show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
    push_cast; ring
  have hlogss : Real.log ((1 - s) * (1 - s')) = Real.log (1 - s) + Real.log (1 - s') :=
    Real.log_mul h1s.ne' h1s'.ne'
  have hlt4 : Real.log (4 * ρ) < Real.log ((1 - s) * (1 - s')) :=
    Real.log_lt_log (by positivity) h4ρ
  have hss : s + s' < 11 / 20 := by linarith
  -- merge the two factors: `S² = s² + s'² + s²s'²/3`, so `uv = 3(3 + S²)/16`
  set S := √(s ^ 2 + s' ^ 2 + s ^ 2 * s' ^ 2 / 3) with hSdef
  have hS0 : 0 ≤ S := Real.sqrt_nonneg _
  have hS2 : S ^ 2 = s ^ 2 + s' ^ 2 + s ^ 2 * s' ^ 2 / 3 := Real.sq_sqrt (by positivity)
  have hm0 : 0 ≤ s + s' - s * s' := by linarith [mul_nonneg hs'0 h1s.le]
  have hSm : S ≤ s + s' - s * s' := by
    rw [hSdef, Real.sqrt_le_left hm0]
    linarith [mul_nonneg (mul_nonneg hs0 hs'0) (by linarith : (0 : ℝ) ≤ 1 - s - s'),
      sq_nonneg (s * s')]
  have h1S : (1 - s) * (1 - s') ≤ 1 - S := by linarith
  have hS1 : S < 1 := by linarith [mul_pos h1s h1s']
  have hsup := ag_sigma_superadd hs0 hs'0 hS0 hS1 (by rw [hS2]; linarith [sq_nonneg (s * s')])
  have h1S0 : 0 < 1 - S := by linarith
  -- the reduced variable `z = 4ρ/(1 - S) ∈ (0, 1)`
  set z := 4 * ρ / (1 - S) with hzdef
  have hz0 : 0 < z := div_pos (by positivity) h1S0
  have hz1 : z ≤ 1 := by rw [hzdef, div_le_one h1S0]; linarith
  have hlogz : Real.log z = Real.log (4 * ρ) - Real.log (1 - S) :=
    Real.log_div (by positivity) h1S0.ne'
  have hρz : ρ = (1 - S) * z / 4 := by rw [hzdef]; field_simp
  have hEz : E ≤ (1 - S) * (1 - z / 4) + Real.log z := by
    have e : (1 - S) * (1 - z / 4) = 1 - S - ρ := by rw [hρz]; ring
    rw [e]; linarith
  have huvS : u * v = 3 * (3 + S ^ 2) / 16 := by rw [hS2, hs2, hs'2]; ring
  have hE0 : 0 < E := by linarith
  have hE2 : 9 / 25 * (3 * (3 + S ^ 2) / 16) ≤ E ^ 2 := by
    rw [← huvS]
    have hsq : √(u * v) ^ 2 = u * v := Real.sq_sqrt (by linarith)
    have := pow_le_pow_left₀ (by positivity : (0 : ℝ) ≤ 3 / 5 * √(u * v)) hlt 2
    rw [mul_pow, hsq] at this
    linarith
  have hcore := ag_core hS0 hz0 hz1 hEz hE0 hE2
  rw [← huvS, ← hρz] at hcore
  have hγ := mul_le_mul_of_nonneg_left hcap (by positivity : (0 : ℝ) ≤ 16 * (1 - ρ) ^ 2)
  linarith [h.gram]

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
