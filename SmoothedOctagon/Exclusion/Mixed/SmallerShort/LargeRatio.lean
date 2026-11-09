module

public import SmoothedOctagon.Exclusion.Mixed.SmallerShort.FaceValue
public import SmoothedOctagon.Exclusion.Mixed.SmallerShort.LargeRatio.FaceSigns

/-!
# Smaller-short window, large ratio: `x < 12/5`, `D > 0`, `E_L > 0`

This module proves `x < 12/5` (the large-ratio exclusion), then `D > 0` and `E_L > 0` (the positive
diagonal and pairing). Assuming `x ≥ 12/5`, the actual root gives `G*_τ ≥ 0` for the floor-weighted
envelope `G = R_τ + ½(w - 3/4)` (`ss_env_weighted` with `m = 1/2`); the scale moves
(`lgr_endpoint_alt`, `lgr_G_zero_neg`, `lgr_tau_two`) push it to a face `q = q_c ≤ 1/7` or
`q = 1/7 ≤ q_c`; the norm substitution (`lgr_uslope`, `ss_sec_le_ubar`, `lgr_ubar_le_uhat`) and the
three duration tests (`ss_dur_three`) reduce to the face signs `lgr_central_tau_two`,
`lgr_central_duration`, `lgr_outer_tests`.

## Main API

* Shape lemmas: `lgr_al_be` (`α/β < 3/4`), `lgr_DQ_le` (`D/Q ≤ 3(1 + x)²/(7x²)`),
  `lgr_face_alpha`, `lgr_ubar_le_uhat`, `lgr_D_pos`, `lgr_pairing`.
* Scale lemmas: `lgr_uslope`, `lgr_endpoint_alt`, `lgr_G_zero_neg`, `lgr_tau_two`.
* Face signs: `lgr_central_tau_two`, `lgr_central_duration`, `lgr_outer_tests`, proved in
  `SmallerShort/LargeRatio/FaceSigns`.
* The bound: `SmallerShortData.ratio_lt_twelve_fifths`, `M2Short.ratio_lt_twelve_fifths`.
-/

@[expose] public section

namespace SmoothedOctagon

open Set Real

/-! ### Shape lemmas -/

/-- **`α/β < 3/4`**: for `x ≥ 12/5`, `1 ≤ α < x ≤ β` with equal secants, `4α < 3β` (upper bound of
`Sec(α, β, x)` by its value at `α`; lower bound of `Sec(1, x, β)` from the Padé bound
`ss_log_le_pade3` on `V(x)`, `V - 3/4 ≥ (x - 1)²/(6(1 + x)(3x + 1))`). -/
theorem lgr_al_be {x al be : ℝ} (hx : 12 / 5 ≤ x) (hal : 1 ≤ al) (hax : al < x) (hxb : x ≤ be)
    (heq : m2Sec 1 x be = m2Sec al be x) : 4 * al < 3 * be := by
  by_contra hcon
  push Not at hcon
  have hx1 : 1 < x := by linarith
  have hx0 : 0 < x := by linarith
  have hal0 : 0 < al := by linarith
  have hbe0 : 0 < be := by linarith
  -- the second secant is at most `g_β(α) ≤ 3/4 + 1/196`
  have hup : m2Sec al be x ≤ ss_gB be al := ss_sec_le_left hal0 hax.le hxb
  have hup2 : ss_gB be al ≤ 3 / 4 + 1 / 196 := by
    unfold ss_gB
    have hp : 0 < (be + al) ^ 2 := by positivity
    rw [sub_le_iff_le_add, ← sub_le_iff_le_add', le_div_iff₀ hp]
    nlinarith [mul_nonneg (sub_nonneg.2 hcon) (by linarith : (0 : ℝ) ≤ 4 * be - 3 * al)]
  -- the first secant: `(β - 1)u = (x - 1)V + (β - x)Sec(x, x, β)`
  have hadd := ss_sec_add (A := 1) (B := x) (M := x) (P := be) one_pos hx0 hx0 hbe0
  have h34 := ss_sec_ge_34 hx0 hx0 hbe0
  -- `V - 3/4 ≥ (x - 1)²/(6(1 + x)(3x + 1))` from the Padé bound
  have hV : 3 / 4 + (x - 1) ^ 2 / (6 * (1 + x) * (3 * x + 1)) ≤ m2Sec 1 x x := by
    rw [m2Sec_of_ne (by linarith : (1 : ℝ) ≠ x)]
    have hz : 1 ≤ (x + x) / (1 + x) := by rw [le_div_iff₀ (by positivity)]; linarith
    have hlog := ss_log_le_pade3 hz
    have k := mul_le_mul_of_nonneg_left hlog (by positivity : (0 : ℝ) ≤ x / (x - 1))
    have e : x / (x - 1) * (((x + x) / (1 + x) - 1) * (((x + x) / (1 + x)) ^ 2 +
        10 * ((x + x) / (1 + x)) + 1) / (6 * ((x + x) / (1 + x)) * ((x + x) / (1 + x) + 1))) =
        (25 * x ^ 2 + 22 * x + 1) / (12 * (1 + x) * (3 * x + 1)) := by
      have : x - 1 ≠ 0 := by linarith
      field_simp
      ring
    have e2 : 1 + 1 ^ 2 * 0 + x ^ 2 / ((1 + x) * (x + x)) -
        (25 * x ^ 2 + 22 * x + 1) / (12 * (1 + x) * (3 * x + 1)) =
        3 / 4 + (x - 1) ^ 2 / (6 * (1 + x) * (3 * x + 1)) := by
      field_simp
      ring
    rw [e] at k
    linarith
  have hc : 0 < (x - 1) ^ 2 / (6 * (1 + x) * (3 * x + 1)) := by
    have : 0 < x - 1 := by linarith
    positivity
  -- combine
  have hlow : (be - 1) * (3 / 4) + (x - 1) * ((x - 1) ^ 2 / (6 * (1 + x) * (3 * x + 1))) ≤
      (be - 1) * m2Sec 1 x be := by
    rw [hadd]
    nlinarith [mul_le_mul_of_nonneg_left h34 (by linarith : (0 : ℝ) ≤ be - x),
      mul_le_mul_of_nonneg_left hV (by linarith : (0 : ℝ) ≤ x - 1)]
  have hu : (be - 1) * m2Sec 1 x be ≤ (be - 1) * (3 / 4 + 1 / 196) := by
    rw [heq]
    exact mul_le_mul_of_nonneg_left (hup.trans hup2) (by linarith)
  have hb : be - 1 < (4 * x - 3) / 3 := by linarith
  have key : (x - 1) * ((x - 1) ^ 2 / (6 * (1 + x) * (3 * x + 1))) * 196 < (4 * x - 3) / 3 := by
    linarith
  rw [← mul_div_assoc, div_mul_eq_mul_div, div_lt_iff₀ (by positivity)] at key
  nlinarith [sq_nonneg (x - 12 / 5), mul_nonneg (sub_nonneg.2 hx) (sq_nonneg (x - 12 / 5))]

/-- **The diagonal ratio**: for `x ≥ 12/5`, `1 ≤ α ≤ x ≤ β`, `4α ≤ 3β`:
`D ≤ (3(1 + x)²/(7x²))·α(α + β)`. -/
theorem lgr_DQ_le {x al be : ℝ} (hx : 12 / 5 ≤ x) (hal : 1 ≤ al) (hax : al ≤ x) (hxb : x ≤ be)
    (h43 : 4 * al ≤ 3 * be) : ssDg x be al ≤ 3 * (1 + x) ^ 2 / (7 * x ^ 2) * (al * (al + be)) := by
  have hx0 : 0 < x := by linarith
  rw [div_mul_eq_mul_div, le_div_iff₀ (by positivity)]
  unfold ssDg
  -- the β-slope of `7x²D - 3S²Q` is negative
  have hsl : al * (11 * x ^ 2 - 6 * x - 3) - 14 * x ^ 3 ≤ 0 := by
    nlinarith [mul_le_mul_of_nonneg_right hax (by nlinarith : (0 : ℝ) ≤ 11 * x ^ 2 - 6 * x - 3)]
  have hq : 0 < 8 * x ^ 2 - 14 * x - 7 := by nlinarith
  rcases le_total al (3 * x / 4) with h | h
  · -- reduce to `β = x`; convex in `α` on `[1, 3x/4]`
    have hc2 : 0 ≤ 4 * x ^ 2 - 6 * x - 3 := by nlinarith
    have h1 : -14 * x ^ 4 + 25 * x ^ 3 + 5 * x ^ 2 - 9 * x - 3 < 0 := by
      nlinarith [mul_nonneg (sub_nonneg.2 hx) (sq_nonneg x), sq_nonneg x]
    have hh : (3 * x / 4 - 1) * (al ^ 2 * (4 * x ^ 2 - 6 * x - 3) + al * (11 * x ^ 3 - 6 * x ^ 2
        - 3 * x)
        - 14 * x ^ 4 + 14 * x ^ 3 + 7 * x ^ 2) ≤ 0 := by
      nlinarith [mul_nonneg (mul_nonneg hc2 (mul_nonneg (sub_nonneg.2 hal) (sub_nonneg.2 h)))
        (by linarith : (0 : ℝ) ≤ 3 * x / 4 - 1),
        mul_nonneg (sub_nonneg.2 h) (neg_nonneg.2 h1.le),
        mul_nonneg (sub_nonneg.2 hal) (mul_nonneg (sq_nonneg x) hq.le)]
    have hh2 : al ^ 2 * (4 * x ^ 2 - 6 * x - 3) + al * (11 * x ^ 3 - 6 * x ^ 2 - 3 * x)
        - 14 * x ^ 4 + 14 * x ^ 3 + 7 * x ^ 2 ≤ 0 := by
      by_contra hc; push Not at hc
      nlinarith [mul_pos hc (by linarith : (0 : ℝ) < 3 * x / 4 - 1)]
    nlinarith [mul_nonneg (neg_nonneg.2 hsl) (sub_nonneg.2 hxb)]
  · -- reduce to `β = 4α/3`; convex in `α` on `[3x/4, x]`, zero at `α = x`
    have hc2 : 0 ≤ 56 * x ^ 2 / 3 - 14 * x - 7 := by nlinarith
    have hg : al ^ 2 * (56 * x ^ 2 / 3 - 14 * x - 7) - 56 * al * x ^ 3 / 3 + 14 * x ^ 3 +
        7 * x ^ 2 ≤ 0 := by
      nlinarith [mul_nonneg hc2 (mul_nonneg (sub_nonneg.2 h) (sub_nonneg.2 hax)),
        mul_nonneg (mul_nonneg hx0.le (sub_nonneg.2 hax)) hq.le]
    nlinarith [mul_nonneg (neg_nonneg.2 hsl) (by linarith : (0 : ℝ) ≤ be - 4 * al / 3)]

/-- **The face α-bounds**: for `x > 0`, `α ≥ 0`: `6α² ≤ x(x + 2) → α ≤ (5x + 4)/12`; and for
`x ≥ 12/5`: `x(x + 2) ≤ 6α² → (22x + 20)/55 ≤ α`. -/
theorem lgr_face_alpha {x al : ℝ} (hx : 0 < x) (hal : 0 ≤ al) :
    (6 * al ^ 2 ≤ x * (x + 2) → al ≤ (5 * x + 4) / 12) ∧
      (12 / 5 ≤ x → x * (x + 2) ≤ 6 * al ^ 2 → (22 * x + 20) / 55 ≤ al) := by
  constructor
  · intro h
    by_contra hc
    push Not at hc
    nlinarith [mul_lt_mul'' hc hc (by positivity) (by positivity), sq_nonneg (x - 4)]
  · intro hx2 h
    by_contra hc
    push Not at hc
    nlinarith [mul_le_mul hc.le hc.le hal (by positivity)]

/-- **`ū ≤ û` on the central face domain**: for `12/5 ≤ x ≤ 9`, `1 ≤ α ≤ (5x + 4)/12`,
`x ≤ β ≤ x + x(7x + 1)(α - 1)/(4x² + 11x + 1)`, `ū(x, β) ≤ û(x, β)` (`P_t(x) > 0`). -/
theorem lgr_ubar_le_uhat {x al be : ℝ} (hx : 12 / 5 ≤ x) (hx9 : x ≤ 9) (hal : 1 ≤ al)
    (hal' : al ≤ (5 * x + 4) / 12) (hxb : x ≤ be)
    (hb : be ≤ x + x * (7 * x + 1) * (al - 1) / (4 * x ^ 2 + 11 * x + 1)) :
    ssUbar x be ≤ ssUhat x be := by
  have hx0 : 0 < x := by linarith
  have hb1 : 0 < be - 1 := by linarith
  have hR : 0 < 4 * x ^ 2 + 11 * x + 1 := by positivity
  have e : ssUhat x be - ssUbar x be = (be - x) * (12 * x ^ 2 * (x - 1) ^ 2 -
      (be - x) ^ 2 * ((1 + x) * (35 * x + 13))) /
      (48 * x ^ 2 * ((1 + x) * (35 * x + 13)) * (be - 1)) := by
    unfold ssUhat ssUbar
    field_simp
    ring
  -- `β - x ≤ B₀ = x(7x + 1)(5x - 8)/(12R)`
  have hB : be - x ≤ x * (7 * x + 1) * (5 * x - 8) / (12 * (4 * x ^ 2 + 11 * x + 1)) := by
    have h1 : x * (7 * x + 1) * (al - 1) ≤ x * (7 * x + 1) * ((5 * x - 8) / 12) :=
      mul_le_mul_of_nonneg_left (by linarith) (by positivity)
    have h2 := div_le_div_of_nonneg_right h1 hR.le
    rw [show x * (7 * x + 1) * ((5 * x - 8) / 12) / (4 * x ^ 2 + 11 * x + 1) =
      x * (7 * x + 1) * (5 * x - 8) / (12 * (4 * x ^ 2 + 11 * x + 1)) by field_simp] at h2
    linarith
  -- `P_t(x) > 0`
  have hbr : 0 < x ^ 2 * (162918 - 15227 * x) - 335862 := by
    rcases le_total x 4 with h4 | h4
    · have h1 : (144 / 25 : ℝ) ≤ x ^ 2 := by
        have := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 12 / 5) hx 2; norm_num at this ⊢; linarith
      have := mul_le_mul h1 (by linarith : (102010 : ℝ) ≤ 162918 - 15227 * x) (by norm_num)
        (by positivity)
      linarith
    · have h1 : (16 : ℝ) ≤ x ^ 2 := by
        have := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 4) h4 2; norm_num at this ⊢; linarith
      have := mul_le_mul h1 (by linarith : (25875 : ℝ) ≤ 162918 - 15227 * x) (by norm_num)
        (by positivity)
      linarith
  have hPt : (7 * x + 1) ^ 2 * (5 * x - 8) ^ 2 * ((1 + x) * (35 * x + 13)) ≤
      1728 * (x - 1) ^ 2 * (4 * x ^ 2 + 11 * x + 1) ^ 2 := by
    have e1 : 1728 * (x - 1) ^ 2 * (4 * x ^ 2 + 11 * x + 1) ^ 2 -
        (7 * x + 1) ^ 2 * (5 * x - 8) ^ 2 * ((1 + x) * (35 * x + 13)) =
        x ^ 3 * (x ^ 2 * (162918 - 15227 * x) - 335862) + 30432 * x ^ 4 + 80667 * x ^ 2 +
          20880 * x + 896 := by ring
    have := mul_pos (pow_pos hx0 3) hbr
    have : 0 ≤ 30432 * x ^ 4 + 80667 * x ^ 2 + 20880 * x + 896 := by positivity
    linarith
  have hsq : (be - x) ^ 2 * ((1 + x) * (35 * x + 13)) ≤ 12 * x ^ 2 * (x - 1) ^ 2 := by
    have hB0 : 0 ≤ be - x := by linarith
    have h2 : (be - x) ^ 2 ≤ (x * (7 * x + 1) * (5 * x - 8) / (12 * (4 * x ^ 2 + 11 * x
        + 1))) ^ 2 :=
      pow_le_pow_left₀ hB0 hB 2
    have h3 : (x * (7 * x + 1) * (5 * x - 8) / (12 * (4 * x ^ 2 + 11 * x + 1))) ^ 2 *
        ((1 + x) * (35 * x + 13)) ≤ 12 * x ^ 2 * (x - 1) ^ 2 := by
      rw [div_pow, div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
      have := mul_le_mul_of_nonneg_left hPt (by positivity : (0 : ℝ) ≤ x ^ 2)
      linarith
    have := mul_le_mul_of_nonneg_right h2 (by positivity : (0 : ℝ) ≤ (1 + x) * (35 * x + 13))
    linarith
  have : 0 ≤ ssUhat x be - ssUbar x be := by
    rw [e]
    apply div_nonneg
    · exact mul_nonneg (by linarith) (by linarith)
    · positivity
  linarith

/-- **The positive diagonal** (from `D ≥ αD₀`): for `1 < x ≤ 12/5`, `1 ≤ α ≤ x ≤ β ≤ αx`,
`D ≥ D₀ = 2 + 4x - 2x² ≥ 2/25`. -/
theorem lgr_D_pos {x al be : ℝ} (hx : 1 < x) (hx2 : x ≤ 12 / 5) (hal : 1 ≤ al) (hax : al ≤ x)
    (hxb : x ≤ be) (hb : be ≤ al * x) :
    2 + 4 * x - 2 * x ^ 2 ≤ ssDg x be al ∧ 2 / 25 ≤ ssDg x be al := by
  exact ss_D_pos hx hx2 hal hax hb

/-- **The positive pairing sign** (affine in `ρ`): for `1 < x ≤ 12/5`, `0 ≤ ρ ≤ 1/(1 + x)²`,
`D ≥ 2 + 4x - 2x²`, `3/4 ≤ u ≤ u₀(x)`: `F₂ = E_* - 2ρDu = S(u - 1) + 1/S + ρ(2S - 1) - 2ρDu < 0`. -/
theorem lgr_pairing {x rho D u : ℝ} (hx : 1 < x) (hx2 : x ≤ 12 / 5) (hρ : 0 ≤ rho)
    (hρr : rho ≤ 1 / (1 + x) ^ 2) (hD : 2 + 4 * x - 2 * x ^ 2 ≤ D) (hu : 3 / 4 ≤ u)
    (hu0 : u ≤ ssU0 x) : ssE0 x u + rho * (2 * (1 + x) - 1) - 2 * rho * D * u < 0 := by
  have hS : 0 < 1 + x := by linarith
  have hD0 : 2 / 25 ≤ 2 + 4 * x - 2 * x ^ 2 := by nlinarith
  have hρS : rho * (1 + x) ^ 2 ≤ 1 := by
    rwa [le_div_iff₀ (by positivity)] at hρr
  -- replace `D` by `D₀` and `u` by `u₀`
  have h1 : -(2 * rho * D * u) ≤ -(2 * rho * (2 + 4 * x - 2 * x ^ 2) * u) := by
    have := mul_le_mul_of_nonneg_left hD (by positivity : (0 : ℝ) ≤ 2 * rho * u)
    nlinarith
  have hcoef : 0 ≤ (1 + x) - 2 * rho * (2 + 4 * x - 2 * x ^ 2) := by
    have h4 : 2 + 4 * x - 2 * x ^ 2 ≤ 4 := by nlinarith
    have : rho * (2 + 4 * x - 2 * x ^ 2) * (1 + x) ^ 2 ≤ 4 := by nlinarith
    nlinarith
  have h2 : u * ((1 + x) - 2 * rho * (2 + 4 * x - 2 * x ^ 2)) ≤
      ssU0 x * ((1 + x) - 2 * rho * (2 + 4 * x - 2 * x ^ 2)) :=
    mul_le_mul_of_nonneg_right hu0 hcoef
  -- the affine function of `ρ`
  have hM0 : -2 * (x - 1) * (1 + x) ^ 2 * (x + 5) < 0 := by
    have : 0 < (x - 1) * (1 + x) ^ 2 * (x + 5) := by
      have : 0 < x - 1 := by linarith
      positivity
    linarith
  have hM1 : 0 < x ^ 5 - 13 * x ^ 4 + 6 * x ^ 3 + 32 * x ^ 2 + 37 * x + 9 := by
    obtain ⟨y, rfl⟩ : ∃ y, x = 1 + y := ⟨x - 1, by ring⟩
    have hy : 0 < y := by linarith
    have hy2 : y ≤ 7 / 5 := by linarith
    nlinarith [mul_nonneg hy.le (sub_nonneg.2 hy2), mul_nonneg (mul_nonneg hy.le hy.le)
      (sub_nonneg.2 hy2), mul_nonneg (pow_nonneg hy.le 3) (sub_nonneg.2 hy2),
      mul_nonneg (pow_nonneg hy.le 4) (sub_nonneg.2 hy2)]
  have hM : (9 * (1 + x) ^ 2 + (x - 1) ^ 2) * ((1 + x) - 2 * rho * (2 + 4 * x - 2 * x ^ 2)) *
      (1 + x) - 12 * (1 + x) ^ 4 + 12 * (1 + x) ^ 2 + 12 * rho * (2 * (1 + x) - 1) * (1 + x) ^ 3
      < 0 := by
    have e : ((9 * (1 + x) ^ 2 + (x - 1) ^ 2) * ((1 + x) - 2 * rho * (2 + 4 * x - 2 * x ^ 2)) *
        (1 + x) - 12 * (1 + x) ^ 4 + 12 * (1 + x) ^ 2 + 12 * rho * (2 * (1 + x) - 1) *
        (1 + x) ^ 3) * (1 + x) = (1 - rho * (1 + x) ^ 2) * ((1 + x) * (-2 * (x - 1) *
        (1 + x) ^ 2 * (x + 5))) + rho * (1 + x) ^ 2 *
        (-2 * (x ^ 5 - 13 * x ^ 4 + 6 * x ^ 3 + 32 * x ^ 2 + 37 * x + 9)) := by ring
    have : ((9 * (1 + x) ^ 2 + (x - 1) ^ 2) * ((1 + x) - 2 * rho * (2 + 4 * x - 2 * x ^ 2)) *
        (1 + x) - 12 * (1 + x) ^ 4 + 12 * (1 + x) ^ 2 + 12 * rho * (2 * (1 + x) - 1) *
        (1 + x) ^ 3) * (1 + x) < 0 := by
      rw [e]
      have a1 : (1 - rho * (1 + x) ^ 2) * ((1 + x) * (-2 * (x - 1) * (1 + x) ^ 2 * (x + 5))) ≤ 0 :=
        mul_nonpos_of_nonneg_of_nonpos (by linarith) (by nlinarith)
      have a2 : rho * (1 + x) ^ 2 * (-2 * (x ^ 5 - 13 * x ^ 4 + 6 * x ^ 3 + 32 * x ^ 2 + 37 * x
          + 9)) ≤ 0 := mul_nonpos_of_nonneg_of_nonpos (by positivity) (by linarith)
      rcases eq_or_lt_of_le hρ with h0 | h0
      · subst h0; nlinarith
      · have : rho * (1 + x) ^ 2 * (-2 * (x ^ 5 - 13 * x ^ 4 + 6 * x ^ 3 + 32 * x ^ 2 + 37 * x
            + 9)) < 0 := mul_neg_of_pos_of_neg (by positivity) (by linarith)
        linarith
    exact neg_of_mul_neg_left this hS.le
  have hU0 : ssU0 x * ((1 + x) - 2 * rho * (2 + 4 * x - 2 * x ^ 2)) - (1 + x) + 1 / (1 + x) +
      rho * (2 * (1 + x) - 1) = ((9 * (1 + x) ^ 2 + (x - 1) ^ 2) *
      ((1 + x) - 2 * rho * (2 + 4 * x - 2 * x ^ 2)) * (1 + x) - 12 * (1 + x) ^ 4 +
      12 * (1 + x) ^ 2 + 12 * rho * (2 * (1 + x) - 1) * (1 + x) ^ 3) / (12 * (1 + x) ^ 3) := by
    unfold ssU0
    field_simp
    ring
  have hneg : ssU0 x * ((1 + x) - 2 * rho * (2 + 4 * x - 2 * x ^ 2)) - (1 + x) + 1 / (1 + x) +
      rho * (2 * (1 + x) - 1) < 0 := by
    rw [hU0]
    exact div_neg_of_neg_of_pos hM (by positivity)
  unfold ssE0
  nlinarith

/-! ### Scale lemmas -/

/-- Sign of the `u`-slope in scalar form. -/
private theorem lgr_slope_pos {S q ε Δ ri τ : ℝ} (hS : 17 / 5 ≤ S) (hS10 : S ≤ 10) (hε : 0 ≤ ε)
    (hε1 : ε ≤ 1) (hq : 0 < q) (hq7 : q ≤ 1 / 7) (hri : 2 < ri) (hτ : 2 ≤ τ)
    (hτd : 0 ≤ Δ → τ * (q * Δ) < 1) (hΔ : Δ ≤ 51 / 25) (hΔ2 : 7 / 2 ≤ S → Δ ≤ 2) :
    0 < (τ + 1 / 2) * (q * Δ) * (q * Δ - (1 - ε * q) * S) + ri + (1 - ε * q) * S -
      2 * (q * Δ) := by
  have hεq : ε * q ≤ q := mul_le_of_le_one_left hq.le hε1
  have hεq0 : 0 ≤ ε * q := mul_nonneg hε hq.le
  have hl0 : 0 < 1 - ε * q := by linarith
  have hl1 : 1 - ε * q ≤ 1 := by linarith
  rcases lt_or_ge Δ 0 with hD | hD
  · -- `d < 0`: every grouped term is positive
    have hd : q * Δ < 0 := mul_neg_of_pos_of_neg hq hD
    have e : (τ + 1 / 2) * (q * Δ) * (q * Δ - (1 - ε * q) * S) + ri + (1 - ε * q) * S -
        2 * (q * Δ) = ri - 2 * (q * Δ) + (τ + 1 / 2) * (q * Δ) ^ 2 +
        (1 - ε * q) * S * (1 - (τ + 1 / 2) * (q * Δ)) := by ring
    rw [e]
    have : 0 ≤ (1 - ε * q) * S * (1 - (τ + 1 / 2) * (q * Δ)) := by
      apply mul_nonneg (by positivity)
      nlinarith
    nlinarith [sq_nonneg (q * Δ)]
  · have h1 := hτd hD
    set d := q * Δ with hd
    have hd0 : 0 ≤ d := mul_nonneg hq.le hD
    -- `d (2 + λS/2) ≤ 2 < 1/r_A`
    have hbound : d * (2 + (1 - ε * q) * S / 2) ≤ 2 := by
      rcases le_total (7 / 2) S with h7 | h7
      · have := hΔ2 h7
        have hd2 : d ≤ 2 / 7 := by
          rw [hd]
          have := mul_le_mul_of_nonneg_left this hq.le
          have := mul_le_mul_of_nonneg_right hq7 (by linarith : (0 : ℝ) ≤ 2)
          linarith
        have : (1 - ε * q) * S ≤ 10 := by
          have := mul_le_mul_of_nonneg_right hl1 (by linarith : (0 : ℝ) ≤ S); linarith
        have := mul_le_mul hd2 (by linarith : 2 + (1 - ε * q) * S / 2 ≤ 7)
          (by linarith [mul_nonneg hl0.le (by linarith : (0 : ℝ) ≤ S)]) (by norm_num)
        linarith
      · have hd2 : d ≤ 51 / 175 := by
          rw [hd]
          have := mul_le_mul_of_nonneg_left hΔ hq.le
          have := mul_le_mul_of_nonneg_right hq7 (by linarith : (0 : ℝ) ≤ 51 / 25)
          linarith
        have : (1 - ε * q) * S ≤ 7 / 2 := by
          have := mul_le_mul_of_nonneg_right hl1 (by linarith : (0 : ℝ) ≤ S); linarith
        have := mul_le_mul hd2 (by linarith : 2 + (1 - ε * q) * S / 2 ≤ 15 / 4)
          (by linarith [mul_nonneg hl0.le (by linarith : (0 : ℝ) ≤ S)]) (by norm_num)
        linarith
    have e : (τ + 1 / 2) * d * (d - (1 - ε * q) * S) + ri + (1 - ε * q) * S - 2 * d =
        ri - 2 * d + (τ + 1 / 2) * d ^ 2 + (1 - ε * q) * S * (1 - (τ + 1 / 2) * d) := by ring
    rw [e]
    have h2 : (1 - ε * q) * S * (-(d / 2)) ≤ (1 - ε * q) * S * (1 - (τ + 1 / 2) * d) :=
      mul_le_mul_of_nonneg_left (by nlinarith) (by positivity)
    nlinarith [sq_nonneg d]

/-- **The incoming coefficient**: for `12/5 ≤ x ≤ 9`, `1 ≤ α ≤ x ≤ β`, `α < β`, `D < α(α + β)`,
`0 < q ≤ 1/7`, and either `2 ≤ τ ≤ T = r_A/q` or `τ = 2`, the floor-weighted face value is
nondecreasing in `u` (it is affine with slope `1/r_A + λS - 2d + (τ + ½)d(d - λS) > 0`). -/
theorem lgr_uslope {x be al q τ ℓ u u' : ℝ} (hx : 12 / 5 ≤ x) (hx9 : x ≤ 9) (hal : 1 ≤ al)
    (hax : al ≤ x) (hxb : x ≤ be) (hab : al < be) (hDQ : ssDg x be al < al * (al + be))
    (hq : 0 < q) (hq7 : q ≤ 1 / 7) (hτ : (2 ≤ τ ∧ τ * q ≤ ssRA al be) ∨ τ = 2) (huu : u ≤ u') :
    ssF x be al u q τ ℓ (1 / 2) ≤ ssF x be al u' q τ ℓ (1 / 2) := by
  have hal0 : 0 < al := by linarith
  have ha2 : 0 < al ^ 2 := by positivity
  have hε : 0 ≤ 1 - 1 / al ^ 2 := by
    rw [sub_nonneg, div_le_one ha2]; exact one_le_pow₀ hal
  have hε1 : 1 - 1 / al ^ 2 ≤ 1 := by
    have : 0 ≤ 1 / al ^ 2 := by positivity
    linarith
  have hri : 2 < 1 / ssRA al be := by
    unfold ssRA
    rw [one_div_div, lt_div_iff₀ hal0]; linarith
  -- `D/α² ≤ 2 + (1 + 2x - x²)/α²`
  have hDle : ssDg x be al ≤ 2 * al ^ 2 + (1 + 2 * x - x ^ 2) := by
    unfold ssDg
    nlinarith [mul_le_mul_of_nonneg_right hxb (by linarith : (0 : ℝ) ≤ x - al), sq_nonneg (x - al)]
  have hΔ : ssDg x be al / al ^ 2 ≤ 51 / 25 := by
    rw [div_le_iff₀ ha2]
    have : 1 + 2 * x - x ^ 2 ≤ 1 / 25 := by nlinarith
    nlinarith
  have hΔ2 : 7 / 2 ≤ 1 + x → ssDg x be al / al ^ 2 ≤ 2 := by
    intro h
    rw [div_le_iff₀ ha2]
    have : 1 + 2 * x - x ^ 2 ≤ 0 := by nlinarith
    linarith
  have hτ2 : 2 ≤ τ := by rcases hτ with h | h <;> [exact h.1; exact h.ge]
  have hτd : 0 ≤ ssDg x be al / al ^ 2 → τ * (q * (ssDg x be al / al ^ 2)) < 1 := by
    intro hD
    rcases hτ with ⟨_, h⟩ | h
    · have hQ : 0 < al * (al + be) := mul_pos hal0 (by linarith)
      have e : ssRA al be * (ssDg x be al / al ^ 2) = ssDg x be al / (al * (al + be)) := by
        unfold ssRA; field_simp
      have h1 : τ * q * (ssDg x be al / al ^ 2) ≤ ssRA al be * (ssDg x be al / al ^ 2) :=
        mul_le_mul_of_nonneg_right h hD
      have h2 : ssDg x be al / (al * (al + be)) < 1 := by rwa [div_lt_one hQ]
      linarith
    · subst h
      have := mul_le_mul_of_nonneg_left hΔ hq.le
      linarith
  have hpos := lgr_slope_pos (S := 1 + x) (by linarith) (by linarith) hε hε1 hq hq7 hri hτ2 hτd hΔ
    hΔ2
  have e := ss_F_u_sub x be al u u' q τ ℓ (1 / 2)
  linarith [mul_nonneg (sub_nonneg.2 huu) hpos.le]

private theorem lgr_P1a {S : ℝ} (hS : 5 ≤ S) (hS10 : S ≤ 10) :
    0 < -83 * S ^ 4 / 1800 + 497 * S ^ 3 / 900 - 863 * S ^ 2 / 1200 - 343 * S / 225 - 1 / 225 := by
  obtain ⟨t, rfl⟩ : ∃ t, S = t + 5 := ⟨S - 5, by ring⟩
  have ht : 0 ≤ t := by linarith
  have ht5 : 0 ≤ 5 - t := by linarith
  have e : -83 * (t + 5) ^ 4 / 1800 + 497 * (t + 5) ^ 3 / 900 - 863 * (t + 5) ^ 2 / 1200 -
      343 * (t + 5) / 225 - 1 / 225 =
      -83 * t ^ 4 / 1800 - 37 * t ^ 3 / 100 + 259 * t ^ 2 / 400 + 1929 * t / 200 + 5841 / 400 := by
    ring
  rw [e]
  have h3 : t ^ 3 ≤ 25 * t := by
    nlinarith [mul_nonneg ht (mul_nonneg ht5 (by linarith : (0:ℝ) ≤ t + 5))]
  have h4 : t ^ 4 ≤ 125 * t := by nlinarith [mul_nonneg (mul_nonneg ht ht) ht5]
  nlinarith [sq_nonneg (t - 4)]

private theorem lgr_P1b {S : ℝ} (hS : 5 ≤ S) (hS10 : S ≤ 10) :
    0 < -221 * S ^ 4 / 6400 + 1547 * S ^ 3 / 3200 - 14173 * S ^ 2 / 14400 - 2969 * S / 1800 -
      1 / 225 := by
  obtain ⟨t, rfl⟩ : ∃ t, S = t + 5 := ⟨S - 5, by ring⟩
  have ht : 0 ≤ t := by linarith
  have ht5 : 0 ≤ 5 - t := by linarith
  have e : -221 * (t + 5) ^ 4 / 6400 + 1547 * (t + 5) ^ 3 / 3200 - 14173 * (t + 5) ^ 2 / 14400 -
      2969 * (t + 5) / 1800 - 1 / 225 = -221 * t ^ 4 / 6400 - 663 * t ^ 3 / 3200 +
      7831 * t ^ 2 / 7200 + 216011 * t / 28800 + 345029 / 57600 := by ring
  rw [e]
  have h3 : t ^ 3 ≤ 25 * t := by
    nlinarith [mul_nonneg ht (mul_nonneg ht5 (by linarith : (0:ℝ) ≤ t + 5))]
  have h4 : t ^ 4 ≤ 125 * t := by nlinarith [mul_nonneg (mul_nonneg ht ht) ht5]
  nlinarith [sq_nonneg (t - 4)]

private theorem lgr_P0 {S u : ℝ} (hS : 5 ≤ S) (hS10 : S ≤ 10) (hu : 3 / 4 ≤ u)
    (hu' : u ≤ 13 / 16) :
    0 < -S ^ 4 * u ^ 2 / 16 + S ^ 4 * u / 8 - S ^ 4 / 16 - 2 * S ^ 3 * u ^ 2 + 2 * S ^ 3 * u -
      4 * S ^ 2 * u ^ 2 + 17 * S ^ 2 * u / 8 + S ^ 2 / 8 - 2 * S * u - 1 / 16 := by
  have hh1 : 0 ≤ S ^ 2 * (1 - u) - 1 - 59 / 80 * S := by nlinarith
  have hh2 : 0 ≤ 32 * u * S - (S ^ 2 * (1 - u) - 1) - 59 / 80 * S := by nlinarith
  have hg : 0 < 36 * u + 32 * u * (59 / 80) - 64 * u ^ 2 - (59 / 80) ^ 2 := by
    nlinarith [mul_nonneg (sub_nonneg.2 hu) (sub_nonneg.2 hu')]
  have h1 := mul_nonneg hh1 hh2
  have h2 := mul_pos (by positivity : (0 : ℝ) < S ^ 2) hg
  have e : 16 * (-S ^ 4 * u ^ 2 / 16 + S ^ 4 * u / 8 - S ^ 4 / 16 - 2 * S ^ 3 * u ^ 2 +
      2 * S ^ 3 * u - 4 * S ^ 2 * u ^ 2 + 17 * S ^ 2 * u / 8 + S ^ 2 / 8 - 2 * S * u - 1 / 16) =
      S ^ 2 * (36 * u + 32 * u * (59 / 80) - 64 * u ^ 2 - (59 / 80) ^ 2) +
      (S ^ 2 * (1 - u) - 1 - 59 / 80 * S) * (32 * u * S - (S ^ 2 * (1 - u) - 1) - 59 / 80 * S) := by
    ring
  linarith

/-- The completed-square numerator of the `A₂ < 0` slope bound, multiplied by `S²`, is positive on
`5 ≤ S ≤ 10`, `3/4 ≤ u ≤ 13/16`, `0 ≤ a ≤ 11/45` (concave in `a` and, at `a = 11/45`, in `u`). -/
private theorem lgr_P_pos {S u a : ℝ} (hS : 5 ≤ S) (hS10 : S ≤ 10) (hu : 3 / 4 ≤ u)
    (hu' : u ≤ 13 / 16) (ha0 : 0 ≤ a) (ha : a ≤ 11 / 45) :
    0 < -9*S^4*a^2*u^2/16 + 9*S^4*a^2*u/8 - 9*S^4*a^2/16 + 3*S^4*a*u^2/8 - 3*S^4*a/8 -
      S^4*u^2/16 + S^4*u/8 - S^4/16 - 9*S^3*a^2*u/8 + 9*S^3*a^2/8 + 3*S^3*a*u/8 + 3*S^3*a/8 -
      2*S^3*u^2 + 2*S^3*u + 9*S^2*a^2*u/8 - 27*S^2*a^2/16 - 3*S^2*a*u/4 - 4*S^2*u^2 +
      17*S^2*u/8 + S^2/8 + 9*S*a^2/8 - 3*S*a/8 - 2*S*u - 9*a^2/16 + 3*a/8 - 1/16 := by
  have h1 := lgr_P1a hS hS10
  have h2 := lgr_P1b hS hS10
  have h0 := lgr_P0 hS hS10 hu hu'
  set P1a := -83 * S ^ 4 / 1800 + 497 * S ^ 3 / 900 - 863 * S ^ 2 / 1200 - 343 * S / 225 - 1 / 225
  set P1b := -221 * S ^ 4 / 6400 + 1547 * S ^ 3 / 3200 - 14173 * S ^ 2 / 14400 - 2969 * S / 1800 -
      1 / 225
  set P0 := -S ^ 4 * u ^ 2 / 16 + S ^ 4 * u / 8 - S ^ 4 / 16 - 2 * S ^ 3 * u ^ 2 + 2 * S ^ 3 * u -
      4 * S ^ 2 * u ^ 2 + 17 * S ^ 2 * u / 8 + S ^ 2 / 8 - 2 * S * u - 1 / 16
  -- `P(a = 11/45)` is concave in `u`
  set P1 := (1 - 16 * (u - 3 / 4)) * P1a + 16 * (u - 3 / 4) * P1b +
    S ^ 2 * (S ^ 2 + 450 * S + 900) / 225 * ((u - 3 / 4) * (13 / 16 - u)) with hP1
  have hP1pos : 0 < P1 := by
    have k1 := mul_nonneg (by linarith : (0 : ℝ) ≤ 1 - 16 * (u - 3 / 4)) h1.le
    have k2 := mul_nonneg (by linarith : (0 : ℝ) ≤ 16 * (u - 3 / 4)) h2.le
    have k3 := mul_nonneg (by positivity : (0 : ℝ) ≤ S ^ 2 * (S ^ 2 + 450 * S + 900) / 225)
      (mul_nonneg (sub_nonneg.2 hu) (sub_nonneg.2 hu'))
    rcases le_total u (25 / 32) with hu2 | hu2
    · have := mul_pos (by linarith : (0 : ℝ) < 1 - 16 * (u - 3 / 4)) h1
      linarith
    · have := mul_pos (by linarith : (0 : ℝ) < 16 * (u - 3 / 4)) h2
      linarith
  have hk := mul_nonneg (mul_nonneg ha0 (sub_nonneg.2 ha))
    (sq_nonneg (S ^ 2 * u - S ^ 2 + S - 1))
  have e : -9*S^4*a^2*u^2/16 + 9*S^4*a^2*u/8 - 9*S^4*a^2/16 + 3*S^4*a*u^2/8 - 3*S^4*a/8 -
      S^4*u^2/16 + S^4*u/8 - S^4/16 - 9*S^3*a^2*u/8 + 9*S^3*a^2/8 + 3*S^3*a*u/8 + 3*S^3*a/8 -
      2*S^3*u^2 + 2*S^3*u + 9*S^2*a^2*u/8 - 27*S^2*a^2/16 - 3*S^2*a*u/4 - 4*S^2*u^2 +
      17*S^2*u/8 + S^2/8 + 9*S*a^2/8 - 3*S*a/8 - 2*S*u - 9*a^2/16 + 3*a/8 - 1/16 =
      (1 - 45 * a / 11) * P0 + 45 * a / 11 * P1 +
        9 / 16 * (a * (11 / 45 - a) * (S ^ 2 * u - S ^ 2 + S - 1) ^ 2) := by
    rw [hP1]; ring
  rw [e]
  have k0 := mul_nonneg (by linarith : (0 : ℝ) ≤ 1 - 45 * a / 11) h0.le
  have k1 := mul_nonneg (by linarith : (0 : ℝ) ≤ 45 * a / 11) hP1pos.le
  rcases le_total a (11 / 90) with ha2 | ha2
  · have := mul_pos (by linarith : (0 : ℝ) < 1 - 45 * a / 11) h0
    linarith
  · have := mul_pos (by linarith : (0 : ℝ) < 45 * a / 11) hP1pos
    linarith

/-- `16S²(K̄² - 3𝒜) < 0` for `17/5 ≤ S ≤ 5`, `0 ≤ z < 11/5`. -/
private theorem lgr_Kbar {S z : ℝ} (hS : 17 / 5 ≤ S) (hS5 : S ≤ 5) (hz0 : 0 ≤ z)
    (hz : z < 11 / 5) : S ^ 4 - 56 * S ^ 2 + 16 + 2 * (7 * S ^ 2 - 4) * z + z ^ 2 < 0 := by
  have h1 : 0 ≤ (25 - S ^ 2) * (S ^ 2 - 289 / 25) := mul_nonneg (by nlinarith) (by nlinarith)
  have h2 : 2 * (7 * S ^ 2 - 4) * z ≤ 2 * (7 * S ^ 2 - 4) * (11 / 5) :=
    mul_le_mul_of_nonneg_left hz.le (by nlinarith)
  have h3 : z ^ 2 ≤ 11 / 5 * z := by nlinarith
  nlinarith

/-- The completed-square numerator in polynomial form. -/
private theorem lgr_eP {S u a H : ℝ} (hS : S ≠ 0) (hH : H = S * (1 - u) - 1 / S) :
    S ^ 2 * (3 * u * (3 / 4 * ((1 - a) ^ 2 + (1 - a) * (S * a) + (S * a) ^ 2) + 1 +
      ((1 - a) * H + (2 * S - 1) * a) - (1 - a) - S * a / 2) -
      (3 / 4 * ((1 - a) * H + (2 * S - 1) * a) + 2 * u - H / 2) ^ 2) =
      -9*S^4*a^2*u^2/16 + 9*S^4*a^2*u/8 - 9*S^4*a^2/16 + 3*S^4*a*u^2/8 - 3*S^4*a/8 -
      S^4*u^2/16 + S^4*u/8 - S^4/16 - 9*S^3*a^2*u/8 + 9*S^3*a^2/8 + 3*S^3*a*u/8 + 3*S^3*a/8 -
      2*S^3*u^2 + 2*S^3*u + 9*S^2*a^2*u/8 - 27*S^2*a^2/16 - 3*S^2*a*u/4 - 4*S^2*u^2 +
      17*S^2*u/8 + S^2/8 + 9*S*a^2/8 - 3*S*a/8 - 2*S*u - 9*a^2/16 + 3*a/8 - 1/16 := by
  rw [hH]; field_simp; ring

/-- For `S ≤ 5` and `z < 11/5`, `A₂ ≥ 𝒜 - K̄²/3 > 0`. -/
private theorem lgr_A2_pos_small {S u a Δ H : ℝ} (hS : 17 / 5 ≤ S) (hS5 : S ≤ 5) (hu : 3 / 4 ≤ u)
    (ha0 : 0 < a) (ha1 : a ≤ 1) (hΔ : 0 < Δ) (hz' : (S - 2) ^ 2 * a < 11 / 5)
    (hHb : H ≤ S / 4 - 1 / S) :
    0 < (1 - a) ^ 2 + (1 - a) * (S * a) + (S * a) ^ 2 - Δ * ((1 - a) * H + (2 * S - 1) * a) +
      u * Δ ^ 2 := by
  have hS0 : 0 < S := by linarith
  have hz0 : 0 ≤ (S - 2) ^ 2 * a := by positivity
  set Am := (1 - a) ^ 2 + (1 - a) * (S * a) + (S * a) ^ 2 with hAm
  set Kb := (1 - a) * (S / 4 - 1 / S) + (2 * S - 1) * a with hKb
  have hKK : (1 - a) * H + (2 * S - 1) * a ≤ Kb := by
    rw [hKb]
    have := mul_le_mul_of_nonneg_left hHb (by linarith : (0 : ℝ) ≤ 1 - a)
    linarith
  have h1 : Am - Δ * Kb + 3 / 4 * Δ ^ 2 ≤ Am - Δ * ((1 - a) * H + (2 * S - 1) * a) + u * Δ ^ 2 := by
    have := mul_le_mul_of_nonneg_left hKK hΔ.le
    have : 3 / 4 * Δ ^ 2 ≤ u * Δ ^ 2 := mul_le_mul_of_nonneg_right hu (by positivity)
    linarith
  have h2 : Am - Kb ^ 2 / 3 ≤ Am - Δ * Kb + 3 / 4 * Δ ^ 2 := by
    nlinarith [sq_nonneg (Δ - 2 * Kb / 3)]
  have e : 16 * S ^ 2 * (Kb ^ 2 - 3 * Am) = S ^ 4 - 56 * S ^ 2 + 16 +
      2 * (7 * S ^ 2 - 4) * ((S - 2) ^ 2 * a) + ((S - 2) ^ 2 * a) ^ 2 := by
    rw [hKb, hAm]; field_simp; ring
  have h3 := lgr_Kbar hS hS5 hz0 hz'
  have h4 : Kb ^ 2 - 3 * Am < 0 := by
    by_contra h5
    push Not at h5
    have : 0 ≤ 16 * S ^ 2 * (Kb ^ 2 - 3 * Am) := mul_nonneg (by positivity) h5
    linarith
  linarith

/-- **Negative `A₂` gives a positive slope**: with `a = α⁻²`, `Δ = D/α²`, `E₀ = S(u - 1) + 1/S`, if
`A₂ < 0` then `(3/4)A₂ + 1 - A₃ - A₁/2 > 0`. The hypothesis `hz` is `D > 0 ⇒ (x - 1)² < (11/5)α²`.
The cap `z < 11/5` avoids `√2`; then `S > 5`, `a < 11/45`. -/
private theorem lgr_A2neg {S u a Δ : ℝ} (hS : 17 / 5 ≤ S) (hS10 : S ≤ 10) (hu : 3 / 4 ≤ u)
    (hu' : u ≤ 13 / 16) (ha0 : 0 < a) (ha1 : a ≤ 1) (hz : 0 < Δ → (S - 2) ^ 2 * a < 11 / 5)
    (hA2 : (1 - a) ^ 2 + (1 - a) * (S * a) + (S * a) ^ 2 + Δ ^ 2 * u +
      Δ * (1 - a) * (S * (u - 1) + 1 / S) - Δ * (2 * S - 1) * a < 0) :
    0 < 3 / 4 * ((1 - a) ^ 2 + (1 - a) * (S * a) + (S * a) ^ 2 + Δ ^ 2 * u +
      Δ * (1 - a) * (S * (u - 1) + 1 / S) - Δ * (2 * S - 1) * a) + 1 -
      (2 * Δ * u + (1 - a) * (S * (u - 1) + 1 / S) - (2 * S - 1) * a) -
      (2 * (1 - a) + S * a + Δ * (S * (u - 1) + 1 / S)) / 2 := by
  have hS0 : 0 < S := by linarith
  obtain ⟨H, hH⟩ : ∃ H, H = S * (1 - u) - 1 / S := ⟨_, rfl⟩
  have eE : S * (u - 1) + 1 / S = -H := by rw [hH]; ring
  rw [eE] at hA2 ⊢
  have hS1 : 1 / S ≤ 5 / 17 := by rw [div_le_iff₀ hS0]; linarith
  have hH0 : 0 < H := by rw [hH]; nlinarith
  have hHb : H ≤ S / 4 - 1 / S := by rw [hH]; nlinarith
  set Am := (1 - a) ^ 2 + (1 - a) * (S * a) + (S * a) ^ 2 with hAm
  have hAm0 : 0 < Am := by
    have : 0 ≤ (1 - a) ^ 2 + (1 - a) * (S * a) := by
      have : 0 ≤ 1 - a := by linarith
      positivity
    have : 0 < (S * a) ^ 2 := by positivity
    linarith
  set K := (1 - a) * H + (2 * S - 1) * a with hK
  have hK0 : 0 < K := by
    have : 0 ≤ (1 - a) * H := mul_nonneg (by linarith) hH0.le
    have : 0 < (2 * S - 1) * a := mul_pos (by linarith) ha0
    linarith
  have eA2 : (1 - a) ^ 2 + (1 - a) * (S * a) + (S * a) ^ 2 + Δ ^ 2 * u + Δ * (1 - a) * -H -
      Δ * (2 * S - 1) * a = Am - Δ * K + u * Δ ^ 2 := by rw [hAm, hK]; ring
  rw [eA2] at hA2 ⊢
  -- `A₂ < 0` forces `Δ > 0`
  have hΔ : 0 < Δ := by
    by_contra h
    push Not at h
    have : 0 ≤ -Δ * K := mul_nonneg (by linarith) hK0.le
    have : 0 ≤ u * Δ ^ 2 := by positivity
    linarith
  have hz' := hz hΔ
  have hz0 : 0 ≤ (S - 2) ^ 2 * a := by positivity
  -- and `S > 5`
  have hS5 : 5 < S := by
    by_contra h
    push Not at h
    have := lgr_A2_pos_small hS h hu ha0 ha1 hΔ hz' hHb
    rw [← hAm, ← hK] at this
    linarith
  have ha45 : a ≤ 11 / 45 := by
    have : 9 * a ≤ (S - 2) ^ 2 * a := mul_le_mul_of_nonneg_right (by nlinarith) ha0.le
    linarith
  -- completing the square in `Δ`
  set B := 3 / 4 * K + 2 * u - H / 2 with hB
  set C := 3 / 4 * Am + 1 + K - (1 - a) - S * a / 2 with hC
  have eG : 3 / 4 * (Am - Δ * K + u * Δ ^ 2) + 1 - (2 * Δ * u + (1 - a) * -H - (2 * S - 1) * a) -
      (2 * (1 - a) + S * a + Δ * -H) / 2 = 3 / 4 * u * Δ ^ 2 - B * Δ + C := by
    rw [hB, hC, hK]; ring
  rw [eG]
  have eP := lgr_eP (a := a) hS0.ne' hH
  rw [← hK, ← hAm] at eP
  rw [← hB, ← hC] at eP
  have hP := lgr_P_pos hS5.le hS10 hu hu' ha0.le ha45
  rw [← eP] at hP
  have hcs : 0 < 3 * u * C - B ^ 2 := by
    by_contra h
    push Not at h
    have : S ^ 2 * (3 * u * C - B ^ 2) ≤ 0 := mul_nonpos_of_nonneg_of_nonpos (by positivity) h
    linarith
  have e3 : 3 * u * (3 / 4 * u * Δ ^ 2 - B * Δ + C) = (3 * u / 2 * Δ - B) ^ 2 +
      (3 * u * C - B ^ 2) := by ring
  have : 0 < 3 * u * (3 / 4 * u * Δ ^ 2 - B * Δ + C) := by
    rw [e3]; positivity
  exact pos_of_mul_pos_right this (by linarith)

/-- `D > 0` forces `(x - 1)² < (11/5)α²` (with the rational cap `11/5`). -/
private theorem lgr_z_lt {x be al : ℝ} (hx : 12 / 5 ≤ x) (hal : 1 ≤ al) (hxb : x ≤ be)
    (hD : 0 < ssDg x be al) : (x - 1) ^ 2 < 11 / 5 * al ^ 2 := by
  by_contra h
  push Not at h
  have hal' : al ≤ 27 / 40 * (x - 1) := by
    by_contra h'
    push Not at h'
    nlinarith [mul_lt_mul'' h' h' (by nlinarith) (by linarith)]
  have hDle : ssDg x be al ≤ al ^ 2 + 2 * al * x + 1 + 2 * x - 2 * x ^ 2 := by
    unfold ssDg
    nlinarith [mul_le_mul_of_nonneg_right hxb (by linarith : (0 : ℝ) ≤ x - al)]
  nlinarith [mul_le_mul hal' hal' (by linarith) (by nlinarith),
    mul_le_mul_of_nonneg_right hal' (by linarith : (0 : ℝ) ≤ 2 * x)]

/-- **The endpoint alternative at fixed `p`**: on `12/5 ≤ x ≤ 9`, `1 ≤ α ≤ x ≤ β`,
`3/4 ≤ u ≤ 13/16`, `0 < p ≤ r_A`, `0 ≤ q_m ≤ p/2`, the floor-weighted scale polynomial `𝒢(q) = Φ(q)`
(`m = 1/2`) satisfies `𝒢(q) ≤ max{𝒢(0), 𝒢(q_m)}` on `[0, q_m]` (convex if `A₂ ≥ 0`; increasing,
slope `> 1/10`, if `A₂ < 0`).
With the cap `D > 0 ⇒ (x - 1)² < (11/5)α²` (no `√2`), `A₂ < 0` forces `S > 5`, `α⁻² ≤ 11/45`;
the slope bound is taken at `p = 1/2` (decreasing in `p`). -/
theorem lgr_endpoint_alt {x be al u p qm q : ℝ} (hx : 12 / 5 ≤ x) (hx9 : x ≤ 9) (hal : 1 ≤ al)
    (hax : al ≤ x) (hxb : x ≤ be) (hu : 3 / 4 ≤ u) (hu' : u ≤ 13 / 16) (hp : 0 < p)
    (hpr : p ≤ ssRA al be) (hqm : 0 ≤ qm) (hqmp : qm ≤ p / 2) (hq : 0 ≤ q) (hqq : q ≤ qm) :
    ssPhi x be al u p (1 / 2) q ≤
      max (ssPhi x be al u p (1 / 2) 0) (ssPhi x be al u p (1 / 2) qm) := by
  rcases le_or_gt 0 (ssA2 x be al u) with hA | hA
  · exact ss_phi_convex_max (by norm_num) hA hq hqq
  have hal0 : 0 < al := by linarith
  have ha2 : 0 < al ^ 2 := by positivity
  have hz : 0 < ssDg x be al / al ^ 2 → ((1 + x) - 2) ^ 2 * (1 / al ^ 2) < 11 / 5 := by
    intro hΔ
    have := lgr_z_lt hx hal hxb (by
      by_contra h; push Not at h
      have : ssDg x be al / al ^ 2 ≤ 0 := div_nonpos_of_nonpos_of_nonneg h ha2.le
      linarith)
    rw [show ((1 + x) - 2) ^ 2 * (1 / al ^ 2) = (x - 1) ^ 2 / al ^ 2 by ring, div_lt_iff₀ ha2]
    linarith
  have eA2 : ssA2 x be al u = (1 - 1 / al ^ 2) ^ 2 + (1 - 1 / al ^ 2) * ((1 + x) * (1 / al ^ 2)) +
      ((1 + x) * (1 / al ^ 2)) ^ 2 + (ssDg x be al / al ^ 2) ^ 2 * u +
      ssDg x be al / al ^ 2 * (1 - 1 / al ^ 2) * ((1 + x) * (u - 1) + 1 / (1 + x)) -
      ssDg x be al / al ^ 2 * (2 * (1 + x) - 1) * (1 / al ^ 2) := by
    unfold ssA2 ssE0; ring
  have hcore := lgr_A2neg (S := 1 + x) (u := u) (a := 1 / al ^ 2) (Δ := ssDg x be al / al ^ 2)
    (by linarith) (by linarith) hu hu' (by positivity)
    (by rw [div_le_one ha2]; exact one_le_pow₀ hal) hz (by rw [← eA2]; exact hA)
  rw [← eA2] at hcore
  have eG : 2 * (ssDg x be al / al ^ 2) * u + (1 - 1 / al ^ 2) * ((1 + x) * (u - 1) + 1 / (1 + x)) -
      (2 * (1 + x) - 1) * (1 / al ^ 2) = ssA3 x be al u := by unfold ssA3 ssE0; ring
  have eG1 : 2 * (1 - 1 / al ^ 2) + (1 + x) * (1 / al ^ 2) +
      ssDg x be al / al ^ 2 * ((1 + x) * (u - 1) + 1 / (1 + x)) = ssA1 x be al u := by
    unfold ssA1 ssE0; ring
  rw [eG, eG1] at hcore
  -- the bracket of `Φ(q_m) - Φ(q)` exceeds `(3/4)A₂ + 1 - A₃ - A₁/2`
  have hp2 : p ≤ 1 / 2 := by
    have : ssRA al be ≤ 1 / 2 := by
      unfold ssRA; rw [div_le_iff₀ (by linarith)]; linarith
    linarith
  have hbr : 3 / 4 * ssA2 x be al u + 1 - ssA3 x be al u - ssA1 x be al u / 2 ≤
      ssLp x be al u p - 1 / 2 * ssA1 x be al u + 1 / 2 * (q + qm) * ssA2 x be al u := by
    unfold ssLp
    have h1 : (1 / 2) * ssA2 x be al u * p ≤ (1 / 2) * (q + qm) * ssA2 x be al u := by
      nlinarith
    have h2 : 3 / 4 * ssA2 x be al u ≤ 3 / 2 * p * ssA2 x be al u := by nlinarith
    have h3 : 2 ≤ 1 / p := by rw [le_div_iff₀ hp]; linarith
    linarith
  have e : ssPhi x be al u p (1 / 2) qm - ssPhi x be al u p (1 / 2) q = (qm - q) *
      (ssLp x be al u p - 1 / 2 * ssA1 x be al u + 1 / 2 * (q + qm) * ssA2 x be al u) := by
    unfold ssPhi; ring
  have : 0 ≤ ssPhi x be al u p (1 / 2) qm - ssPhi x be al u p (1 / 2) q := by
    rw [e]; exact mul_nonneg (by linarith) (by linarith)
  exact le_max_of_le_right (by linarith)

/-- The value at `r_A = 3/7` is `-P(x)/(168x²(x + 1)(35x + 13))`. -/
private theorem lgr_N37 {x : ℝ} (hx : 12 / 5 ≤ x) :
    (4 * x ^ 2 - 6 * x - 3) / (7 * x ^ 2) * ((1 + x) * (ssVbar x - 1) + 1 / (1 + x)) +
      7 / 3 * (ssVbar x - 1) + 9 / 8 - 3 / 7 * (1 + (x - 1) / x ^ 2) < 0 := by
  have hx0 : 0 < x := by linarith
  have hP : 0 < 648 * x ^ 5 - 237 * x ^ 4 - 2290 * x ^ 3 - 305 * x ^ 2 + 450 * x - 90 := by
    obtain ⟨z, rfl⟩ : ∃ z, x = (z + 12) / 5 := ⟨5 * x - 12, by ring⟩
    have hz : 0 ≤ z := by linarith
    have e : 648 * ((z + 12) / 5) ^ 5 - 237 * ((z + 12) / 5) ^ 4 - 2290 * ((z + 12) / 5) ^ 3 -
        305 * ((z + 12) / 5) ^ 2 + 450 * ((z + 12) / 5) - 90 = (648 * z ^ 5 + 37695 * z ^ 4 +
        818990 * z ^ 3 + 8074475 * z ^ 2 + 33628170 * z + 35346726) / 3125 := by ring
    rw [e]; positivity
  have e : (4 * x ^ 2 - 6 * x - 3) / (7 * x ^ 2) * ((1 + x) * (ssVbar x - 1) + 1 / (1 + x)) +
      7 / 3 * (ssVbar x - 1) + 9 / 8 - 3 / 7 * (1 + (x - 1) / x ^ 2) =
      -(648 * x ^ 5 - 237 * x ^ 4 - 2290 * x ^ 3 - 305 * x ^ 2 + 450 * x - 90) /
        (168 * x ^ 2 * (x + 1) * (35 * x + 13)) := by
    unfold ssVbar; field_simp; ring
  rw [e]
  exact div_neg_of_neg_of_pos (by linarith) (by positivity)

/-- `(49/9)(1 - V̄) ≥ 1 + (x - 1)/x²` for `x ≥ 12/5`. -/
private theorem lgr_Nd {x : ℝ} (hx : 12 / 5 ≤ x) :
    1 + (x - 1) / x ^ 2 ≤ 49 / 9 * (1 - ssVbar x) := by
  have hx0 : 0 < x := by linarith
  have hN4 : 0 < 63 * x ^ 4 + 148 * x ^ 3 - 691 * x ^ 2 + 1260 * x + 468 := by
    obtain ⟨z, rfl⟩ : ∃ z, x = (z + 12) / 5 := ⟨5 * x - 12, by ring⟩
    have hz : 0 ≤ z := by linarith
    have e : 63 * ((z + 12) / 5) ^ 4 + 148 * ((z + 12) / 5) ^ 3 - 691 * ((z + 12) / 5) ^ 2 +
        1260 * ((z + 12) / 5) + 468 = (63 * z ^ 4 + 3764 * z ^ 3 + 63797 * z ^ 2 + 498036 * z +
        2279988) / 625 := by ring
    rw [e]; positivity
  have e : 49 / 9 * (1 - ssVbar x) - (1 + (x - 1) / x ^ 2) =
      (63 * x ^ 4 + 148 * x ^ 3 - 691 * x ^ 2 + 1260 * x + 468) /
        (36 * x ^ 2 * (x + 1) * (35 * x + 13)) := by
    unfold ssVbar; field_simp; ring
  have : 0 ≤ 49 / 9 * (1 - ssVbar x) - (1 + (x - 1) / x ^ 2) := by rw [e]; positivity
  linarith

/-- `M₀ = E₀ + (u - 1)/r_A + r_A + 1/8 < 0`. -/
private theorem lgr_M0_neg {x u r : ℝ} (hx : 12 / 5 ≤ x) (hu' : u ≤ 13 / 16) (hr0 : 0 < r)
    (hrA : r ≤ 3 / 7) : ssE0 x u + (u - 1) / r + r + 1 / 8 < 0 := by
  have hS : 0 < 1 + x := by linarith
  have hE0 : ssE0 x u ≤ -(3 / 16) * (1 + x) + 1 / (1 + x) := by
    unfold ssE0; nlinarith
  have hE0n : 1 / (1 + x) ≤ 5 / 17 := by rw [div_le_iff₀ hS]; linarith
  have h1 : (u - 1) / r ≤ -(3 / 16) / r := div_le_div_of_nonneg_right (by linarith) hr0.le
  have h2 : 7 / 16 ≤ 3 / 16 / r := by rw [le_div_iff₀ hr0]; linarith
  have h3 : -(3 / 16) / r = -(3 / 16 / r) := by ring
  linarith

/-- `M(r_A) = E₀(1 - D/Q) + (u - 1)/r_A + 9/8 - r_A - (x - 1)/Q < 0`; `Qi = 1/Q`, `k = D/Q`. -/
private theorem lgr_Mr_neg {x u r vb k Qi : ℝ} (hx : 12 / 5 ≤ x) (hu' : u ≤ 13 / 16)
    (huV : u ≤ vb) (hr0 : 0 < r) (hrA : r ≤ 3 / 7) (hrQ : r / x ^ 2 ≤ Qi)
    (hk : k ≤ 3 * (1 + x) ^ 2 / (7 * x ^ 2))
    (hN : (4 * x ^ 2 - 6 * x - 3) / (7 * x ^ 2) * ((1 + x) * (vb - 1) + 1 / (1 + x)) +
      7 / 3 * (vb - 1) + 9 / 8 - 3 / 7 * (1 + (x - 1) / x ^ 2) < 0)
    (hNd : 1 + (x - 1) / x ^ 2 ≤ 49 / 9 * (1 - vb)) :
    ssE0 x u * (1 - k) + (u - 1) / r + 9 / 8 - r - (x - 1) * Qi < 0 := by
  have hx0 : 0 < x := by linarith
  have hS : 0 < 1 + x := by linarith
  have hE0 : ssE0 x u ≤ -(3 / 16) * (1 + x) + 1 / (1 + x) := by
    unfold ssE0; nlinarith
  have hE0n : 1 / (1 + x) ≤ 5 / 17 := by rw [div_le_iff₀ hS]; linarith
  have hE0neg : ssE0 x u ≤ 0 := by linarith
  have hK0 : 0 < 1 + (x - 1) / x ^ 2 := by
    have : 0 ≤ (x - 1) / x ^ 2 := div_nonneg (by linarith) (by positivity)
    linarith
  have hc0 : 0 ≤ (4 * x ^ 2 - 6 * x - 3) / (7 * x ^ 2) := div_nonneg (by nlinarith) (by positivity)
  have hcDQ : (4 * x ^ 2 - 6 * x - 3) / (7 * x ^ 2) ≤ 1 - k := by
    have e : (4 * x ^ 2 - 6 * x - 3) / (7 * x ^ 2) = 1 - 3 * (1 + x) ^ 2 / (7 * x ^ 2) := by
      field_simp; ring
    linarith
  have h1 : ssE0 x u * (1 - k) ≤ (4 * x ^ 2 - 6 * x - 3) / (7 * x ^ 2) * ssE0 x u := by
    have := mul_le_mul_of_nonpos_left hcDQ hE0neg
    linarith
  have h2 : (4 * x ^ 2 - 6 * x - 3) / (7 * x ^ 2) * ssE0 x u ≤
      (4 * x ^ 2 - 6 * x - 3) / (7 * x ^ 2) * ((1 + x) * (vb - 1) + 1 / (1 + x)) := by
    apply mul_le_mul_of_nonneg_left _ hc0
    unfold ssE0
    have := mul_le_mul_of_nonneg_left huV hS.le
    linarith
  have h3 : (u - 1) / r ≤ (vb - 1) / r := div_le_div_of_nonneg_right (by linarith) hr0.le
  have h4 : r * (x - 1) / x ^ 2 ≤ (x - 1) * Qi := by
    have := mul_le_mul_of_nonneg_left hrQ (by linarith : (0 : ℝ) ≤ x - 1)
    calc r * (x - 1) / x ^ 2 = (x - 1) * (r / x ^ 2) := by ring
      _ ≤ _ := this
  -- `N(r) ≤ N(3/7)`
  have h5 : (vb - 1) / r - r * (1 + (x - 1) / x ^ 2) ≤
      7 / 3 * (vb - 1) - 3 / 7 * (1 + (x - 1) / x ^ 2) := by
    have e : 7 / 3 * (vb - 1) - 3 / 7 * (1 + (x - 1) / x ^ 2) -
        ((vb - 1) / r - r * (1 + (x - 1) / x ^ 2)) =
        (3 / 7 - r) * (7 / 3 * (1 - vb) / r - (1 + (x - 1) / x ^ 2)) := by field_simp; ring
    have : 1 + (x - 1) / x ^ 2 ≤ 7 / 3 * (1 - vb) / r := by
      rw [le_div_iff₀ hr0]
      have := mul_le_mul_of_nonneg_left hrA hK0.le
      linarith only [this, hNd]
    have hprod := mul_nonneg (by linarith : (0 : ℝ) ≤ 3 / 7 - r) (sub_nonneg.2 this)
    linarith only [e, hprod]
  have e : r * (1 + (x - 1) / x ^ 2) = r + r * (x - 1) / x ^ 2 := by ring
  linarith only [e, h1, h2, h3, h4, h5, hN]

/-- **The zero-scale endpoint is negative**: for `x ≥ 12/5`, `1 ≤ α ≤ x ≤ β`, `r_A ≤ 3/7`,
`D ≤ (3(1 + x)²/(7x²))·α(α + β)`, `3/4 ≤ u ≤ 13/16`, `u ≤ V̄(x)` and `0 < p ≤ r_A`:
`𝒢(0) = C(p) + 1/8 < 0`. -/
theorem lgr_G_zero_neg {x be al u p : ℝ} (hx : 12 / 5 ≤ x) (hal : 1 ≤ al) (hax : al ≤ x)
    (hxb : x ≤ be) (hrA : ssRA al be ≤ 3 / 7)
    (hDQ : ssDg x be al ≤ 3 * (1 + x) ^ 2 / (7 * x ^ 2) * (al * (al + be))) (hu : 3 / 4 ≤ u)
    (hu' : u ≤ 13 / 16) (huV : u ≤ ssVbar x) (hp : 0 < p) (hpr : p ≤ ssRA al be) :
    ssPhi x be al u p (1 / 2) 0 < 0 := by
  have hal0 : 0 < al := by linarith
  have hbe0 : 0 < be := by linarith
  have hQ : 0 < al * (al + be) := by positivity
  have e0 : ssPhi x be al u p (1 / 2) 0 = ssE0 x u + (u - 1) / ssRA al be + ssRA al be + 1 -
      p * ssA1 x be al u + log (p / ssRA al be) + 1 / 8 := by
    unfold ssPhi ssCp; ring
  rw [e0]
  have hrA1 := ss_rA_A1 (x := x) (u := u) hal0 hbe0
  have hr0 : 0 < ssRA al be := by unfold ssRA; positivity
  have hrQ : ssRA al be / x ^ 2 ≤ 1 / (al * (al + be)) := by
    have e : 1 / (al * (al + be)) = ssRA al be / al ^ 2 := by unfold ssRA; field_simp
    rw [e]
    exact div_le_div_of_nonneg_left hr0.le (by positivity) (pow_le_pow_left₀ hal0.le hax 2)
  have hk : ssDg x be al / (al * (al + be)) ≤ 3 * (1 + x) ^ 2 / (7 * x ^ 2) := by
    rw [div_le_iff₀ hQ]; exact hDQ
  have hM0 := lgr_M0_neg hx hu' hr0 hrA
  have hMr := lgr_Mr_neg hx hu' huV hr0 hrA hrQ hk (lgr_N37 hx) (lgr_Nd hx)
  generalize ssRA al be = r at *
  generalize ssA1 x be al u = A1 at *
  have hlog : log (p / r) ≤ p / r - 1 := Real.log_le_sub_one_of_pos (div_pos hp hr0)
  have hMr' : ssE0 x u + (u - 1) / r + r + 1 / 8 + 1 - r * A1 < 0 := by
    rw [hrA1]
    have e : (x - 1) / (al * (al + be)) = (x - 1) * (1 / (al * (al + be))) := by ring
    linarith only [hMr, e]
  -- the affine combination in `p`
  have hpr' : p / r ≤ 1 := by rw [div_le_one hr0]; exact hpr
  have hp0 : 0 < p / r := div_pos hp hr0
  have e2 : ssE0 x u + (u - 1) / r + r + 1 - p * A1 + (p / r - 1) + 1 / 8 =
      (1 - p / r) * (ssE0 x u + (u - 1) / r + r + 1 / 8) +
        p / r * (ssE0 x u + (u - 1) / r + r + 1 / 8 + 1 - r * A1) := by
    have hpr2 : p / r * r = p := div_mul_cancel₀ p hr0.ne'
    linear_combination A1 * hpr2
  have h1 : (1 - p / r) * (ssE0 x u + (u - 1) / r + r + 1 / 8) ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos (by linarith only [hpr']) hM0.le
  have h2 : p / r * (ssE0 x u + (u - 1) / r + r + 1 / 8 + 1 - r * A1) < 0 :=
    mul_neg_of_pos_of_neg hp0 hMr'
  linarith only [e2, hlog, h1, h2]

/-- `N₀(0) = 20u - (2u - 5H/2)² > 0`; for `H ≥ 2` the incoming floor supplies `u ≥ 77/100`,
`H ≤ 76/35`. -/
private theorem lgr_N00 {u H : ℝ} (hu : 3 / 4 ≤ u) (hu' : u ≤ 13 / 16) (hH0 : 0 ≤ H)
    (hH2 : 2 ≤ H → 77 / 100 ≤ u ∧ H ≤ 76 / 35) :
    0 < -25 * H ^ 2 / 4 + 10 * H * u - 4 * u ^ 2 + 20 * u := by
  have e : -25 * H ^ 2 / 4 + 10 * H * u - 4 * u ^ 2 + 20 * u = 20 * u - (2 * u
      - 5 * H / 2) ^ 2 := by
    ring
  rw [e]
  rcases le_total H 2 with h | h
  · nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ 2 * u - 5 * H / 2 + 7 / 2)
      (by linarith : (0 : ℝ) ≤ 13 / 8 - (2 * u - 5 * H / 2))]
  · obtain ⟨h1, h2⟩ := hH2 h
    nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ 2 * u - 5 * H / 2 + 38 / 7 - 2 * u)
      (by linarith : (0 : ℝ) ≤ 5 * H / 2 - 2 * u)]

/-- `N₀(1/7) > 0`. -/
private theorem lgr_N017 {u H : ℝ} (hu : 3 / 4 ≤ u) (hu' : u ≤ 13 / 16) (hH0 : 0 ≤ H)
    (hH : H ≤ 12 / 5) : 0 < -625 * H ^ 2 / 196 + 10 * H * u - 4 * u ^ 2 + 240 * u / 49 := by
  nlinarith [mul_nonneg hH0 (sub_nonneg.2 hH), mul_nonneg (sub_nonneg.2 hu) (sub_nonneg.2 hu'),
    mul_nonneg hH0 (sub_nonneg.2 hu)]

/-- `N₀(s) > 0` on `0 ≤ s ≤ 1/7` from the two endpoints. -/
private theorem lgr_N0s {s u H : ℝ} (hs : 0 ≤ s) (hs7 : s ≤ 1 / 7) (hu : 3 / 4 ≤ u)
    (h0 : 0 < -25 * H ^ 2 / 4 + 10 * H * u - 4 * u ^ 2 + 20 * u)
    (h7 : 0 < -625 * H ^ 2 / 196 + 10 * H * u - 4 * u ^ 2 + 240 * u / 49) :
    0 < -25 * H ^ 2 / 4 + 10 * H * u - 4 * u ^ 2 + 20 * u + s * (25 * H ^ 2 - 120 * u) +
      s ^ 2 * (100 * u - 25 * H ^ 2) := by
  have hss := mul_nonneg hs (sub_nonneg.2 hs7)
  rcases le_total (100 * u) (25 * H ^ 2) with hc | hc
  · -- concave: above the chord
    have e : -25 * H ^ 2 / 4 + 10 * H * u - 4 * u ^ 2 + 20 * u + s * (25 * H ^ 2 - 120 * u) +
        s ^ 2 * (100 * u - 25 * H ^ 2) = (1 - 7 * s) * (-25 * H ^ 2 / 4 + 10 * H * u - 4 * u ^ 2 +
        20 * u) + 7 * s * (-625 * H ^ 2 / 196 + 10 * H * u - 4 * u ^ 2 + 240 * u / 49) +
        (25 * H ^ 2 - 100 * u) * (s * (1 / 7 - s)) := by ring
    rw [e]
    have k1 := mul_nonneg (by linarith : (0 : ℝ) ≤ 1 - 7 * s) h0.le
    have k2 := mul_nonneg (by linarith : (0 : ℝ) ≤ 7 * s) h7.le
    have k3 := mul_nonneg (by linarith : (0 : ℝ) ≤ 25 * H ^ 2 - 100 * u) hss
    rcases le_total s (1 / 14) with hs2 | hs2
    · have := mul_pos (by linarith : (0 : ℝ) < 1 - 7 * s) h0; linarith
    · have := mul_pos (by linarith : (0 : ℝ) < 7 * s) h7; linarith
  · -- convex and decreasing on `[0, 1/7]`
    have e : -25 * H ^ 2 / 4 + 10 * H * u - 4 * u ^ 2 + 20 * u + s * (25 * H ^ 2 - 120 * u) +
        s ^ 2 * (100 * u - 25 * H ^ 2) = (-625 * H ^ 2 / 196 + 10 * H * u - 4 * u ^ 2 +
        240 * u / 49) + (1 / 7 - s) * ((120 * u - 25 * H ^ 2) - (s + 1 / 7) *
        (100 * u - 25 * H ^ 2)) := by ring
    rw [e]
    have : 0 ≤ (120 * u - 25 * H ^ 2) - (s + 1 / 7) * (100 * u - 25 * H ^ 2) := by
      have := mul_le_mul_of_nonneg_right (by linarith : s + 1 / 7 ≤ 2 / 7) (sub_nonneg.2 hc)
      linarith
    have := mul_nonneg (sub_nonneg.2 hs7) this
    linarith

/-- `S²N₁(1/7) > 0` (concave in `u`). -/
private theorem lgr_N117 {S u : ℝ} (hS : 17 / 5 ≤ S) (hu : 3 / 4 ≤ u) (hu' : u ≤ 13 / 16) :
    0 < -225 * S ^ 4 / 196 - 75 * S ^ 3 / 49 + 475 * S ^ 2 / 98 + 25 * S / 7 +
      u ^ 2 * (-25 * S ^ 4 / 4 - 10 * S ^ 3 - 4 * S ^ 2) +
      u * (725 * S ^ 4 / 98 + 45 * S ^ 3 / 7 + 65 * S ^ 2 / 14 - 10 * S) - 25 / 4 := by
  obtain ⟨t, rfl⟩ : ∃ t, S = t + 17 / 5 := ⟨S - 17 / 5, by ring⟩
  have ht : 0 ≤ t := by linarith
  have pa : 0 < 2775 * t ^ 4 / 3136 + 7605 * t ^ 3 / 784 + 68437 * t ^ 2 / 1568 +
      74933 * t / 784 + 1210099 / 15680 := by positivity
  have pb : 0 < 36975 * t ^ 4 / 50176 + 89225 * t ^ 3 / 12544 + 687889 * t ^ 2 / 25088 +
      640645 * t / 12544 + 39541839 / 1254400 := by positivity
  have hw := mul_nonneg (mul_nonneg (sub_nonneg.2 hu) (sub_nonneg.2 hu'))
    (by positivity : (0 : ℝ) ≤ (t + 17 / 5) ^ 2 * (5 * (t + 17 / 5) + 4) ^ 2 / 4)
  have e : -225 * (t + 17 / 5) ^ 4 / 196 - 75 * (t + 17 / 5) ^ 3 / 49 + 475 * (t
      + 17 / 5) ^ 2 / 98 +
      25 * (t + 17 / 5) / 7 + u ^ 2 * (-25 * (t + 17 / 5) ^ 4 / 4 - 10 * (t + 17 / 5) ^ 3 -
      4 * (t + 17 / 5) ^ 2) + u * (725 * (t + 17 / 5) ^ 4 / 98 + 45 * (t + 17 / 5) ^ 3 / 7 +
      65 * (t + 17 / 5) ^ 2 / 14 - 10 * (t + 17 / 5)) - 25 / 4 =
      (1 - 16 * (u - 3 / 4)) * (2775 * t ^ 4 / 3136 + 7605 * t ^ 3 / 784 +
        68437 * t ^ 2 / 1568 + 74933 * t / 784 + 1210099 / 15680) +
      16 * (u - 3 / 4) * (36975 * t ^ 4 / 50176 + 89225 * t ^ 3 / 12544 +
        687889 * t ^ 2 / 25088 + 640645 * t / 12544 + 39541839 / 1254400) +
      (u - 3 / 4) * (13 / 16 - u) * ((t + 17 / 5) ^ 2 * (5 * (t + 17 / 5) + 4) ^ 2 / 4) := by ring
  rw [e]
  have k1 := mul_nonneg (by linarith : (0 : ℝ) ≤ 1 - 16 * (u - 3 / 4)) pa.le
  have k2 := mul_nonneg (by linarith : (0 : ℝ) ≤ 16 * (u - 3 / 4)) pb.le
  rcases le_total u (25 / 32) with h | h
  · have := mul_pos (by linarith : (0 : ℝ) < 1 - 16 * (u - 3 / 4)) pa; linarith
  · have := mul_pos (by linarith : (0 : ℝ) < 16 * (u - 3 / 4)) pb; linarith

/-- `N₁(s) > 0` on `0 ≤ s ≤ 1/7`: concave in `s`, or convex with `N₁'(1/7) < 0`. -/
private theorem lgr_N1s {s S u H : ℝ} (hs : 0 ≤ s) (hs7 : s ≤ 1 / 7) (hS : 17 / 5 ≤ S)
    (hu : 3 / 4 ≤ u) (hu' : u ≤ 13 / 16) (hH : H = S * (1 - u) - 1 / S)
    (h0 : 0 < -25 * H ^ 2 / 4 + 10 * H * u - 4 * u ^ 2 + 20 * u) :
    0 < -25 * H ^ 2 / 4 + 10 * H * u - 4 * u ^ 2 + 20 * u + s * (50 * H * S - 25 * H -
      50 * S * u - 20 * u) + s ^ 2 * (100 * S ^ 2 * u - 100 * S ^ 2 + 100 * S - 25) := by
  have hS0 : 0 < S := by linarith
  have h7 := lgr_N117 hS hu hu'
  set N0 := -25 * H ^ 2 / 4 + 10 * H * u - 4 * u ^ 2 + 20 * u with hN0
  set L1 := 50 * H * S - 25 * H - 50 * S * u - 20 * u with hL1
  set Q1 := 100 * S ^ 2 * u - 100 * S ^ 2 + 100 * S - 25 with hQ1
  have e7 : S ^ 2 * (N0 + 1 / 7 * L1 + (1 / 7) ^ 2 * Q1) = -225 * S ^ 4 / 196 - 75 * S ^ 3 / 49 +
      475 * S ^ 2 / 98 + 25 * S / 7 + u ^ 2 * (-25 * S ^ 4 / 4 - 10 * S ^ 3 - 4 * S ^ 2) +
      u * (725 * S ^ 4 / 98 + 45 * S ^ 3 / 7 + 65 * S ^ 2 / 14 - 10 * S) - 25 / 4 := by
    rw [hN0, hL1, hQ1, hH]; field_simp; ring
  have hN7 : 0 < N0 + 1 / 7 * L1 + (1 / 7) ^ 2 * Q1 := by
    rw [← e7] at h7
    exact pos_of_mul_pos_right h7 (by positivity)
  have hss := mul_nonneg hs (sub_nonneg.2 hs7)
  rcases le_total Q1 0 with hc | hc
  · have e : N0 + s * L1 + s ^ 2 * Q1 = (1 - 7 * s) * N0 + 7 * s * (N0 + 1 / 7 * L1 +
        (1 / 7) ^ 2 * Q1) + (-Q1) * (s * (1 / 7 - s)) := by ring
    rw [e]
    have k1 := mul_nonneg (by linarith : (0 : ℝ) ≤ 1 - 7 * s) h0.le
    have k2 := mul_nonneg (by linarith : (0 : ℝ) ≤ 7 * s) hN7.le
    have k3 := mul_nonneg (by linarith : (0 : ℝ) ≤ -Q1) hss
    rcases le_total s (1 / 14) with hs2 | hs2
    · have := mul_pos (by linarith : (0 : ℝ) < 1 - 7 * s) h0; linarith
    · have := mul_pos (by linarith : (0 : ℝ) < 7 * s) hN7; linarith
  · -- convex: `S(L₁ + 2Q₁/7) < 0`
    have hW : S * (L1 + 2 / 7 * Q1) < 0 := by
      have e : 4 * S ^ 2 * (S * (L1 + 2 / 7 * Q1)) = -5 * S * (2 * S - 1) * (23 * S - 4) +
          (-5 * S * (30 * S ^ 2 + 35 * S + 28) / 7) * (4 * S ^ 2 * u - (2 * S - 1) ^ 2) := by
        rw [hL1, hQ1, hH]; field_simp; ring
      have hq : 0 ≤ 4 * S ^ 2 * u - (2 * S - 1) ^ 2 := by rw [hQ1] at hc; linarith
      have : 4 * S ^ 2 * (S * (L1 + 2 / 7 * Q1)) < 0 := by
        rw [e]
        have a1 : 0 < 5 * S * (2 * S - 1) * (23 * S - 4) := by
          have : 0 < 2 * S - 1 := by linarith
          have : 0 < 23 * S - 4 := by linarith
          positivity
        have a2 : 0 ≤ 5 * S * (30 * S ^ 2 + 35 * S + 28) / 7 * (4 * S ^ 2 * u - (2 * S - 1) ^ 2) :=
          mul_nonneg (by positivity) hq
        linarith
      by_contra h
      push Not at h
      have : 0 ≤ 4 * S ^ 2 * (S * (L1 + 2 / 7 * Q1)) := mul_nonneg (by positivity) h
      linarith
    have hW' : L1 + 2 / 7 * Q1 < 0 := by
      by_contra h
      push Not at h
      have := mul_nonneg hS0.le h
      linarith
    have e : N0 + s * L1 + s ^ 2 * Q1 = (N0 + 1 / 7 * L1 + (1 / 7) ^ 2 * Q1) +
        (1 / 7 - s) * (-(L1 + (s + 1 / 7) * Q1)) := by ring
    rw [e]
    have : 0 ≤ -(L1 + (s + 1 / 7) * Q1) := by
      have := mul_le_mul_of_nonneg_right (by linarith : s + 1 / 7 ≤ 2 / 7) hc
      linarith
    have := mul_nonneg (sub_nonneg.2 hs7) this
    linarith

/-- **The `τ = 2` slope**: with `a = α⁻²`, `Δ = D/α²`, `H = -E₀`, the incoming floor
`u ≥ 3/4 + (S - 2)²/(28S²)` and `0 ≤ σ ≤ 1/7`, `σG₂'(σ) = 1 - σ(5A₁/2 + 1 + A₃) + 5σ²A₂ > 0`. -/
private theorem lgr_Psi_pos {S u a Δ σ H : ℝ} (hS : 17 / 5 ≤ S) (hS10 : S ≤ 10)
    (hu' : u ≤ 13 / 16) (hf : 3 / 4 + (S - 2) ^ 2 / (28 * S ^ 2) ≤ u) (ha0 : 0 ≤ a)
    (ha1 : a ≤ 1) (hσ : 0 ≤ σ) (hσ7 : σ ≤ 1 / 7) (hH : H = S * (1 - u) - 1 / S) :
    0 < 1 - σ * (5 / 2 * (2 * (1 - a) + S * a + Δ * -H) + 1 +
      (2 * Δ * u + (1 - a) * -H - (2 * S - 1) * a)) +
      5 * σ ^ 2 * ((1 - a) ^ 2 + (1 - a) * (S * a) + (S * a) ^ 2 + Δ ^ 2 * u +
        Δ * (1 - a) * -H - Δ * (2 * S - 1) * a) := by
  have hS0 : 0 < S := by linarith
  have hu : 3 / 4 ≤ u := by
    have : 0 ≤ (S - 2) ^ 2 / (28 * S ^ 2) := by positivity
    linarith
  -- bounds on `H` from `u` and from the floor
  have hSH : S * H = S ^ 2 * (1 - u) - 1 := by rw [hH]; field_simp
  have hH0 : 0 ≤ H := by
    have : 0 ≤ S * H := by rw [hSH]; nlinarith
    exact nonneg_of_mul_nonneg_right (by linarith) hS0
  have hH24 : H ≤ 12 / 5 := by
    have : S * H ≤ S * (12 / 5) := by rw [hSH]; nlinarith
    exact le_of_mul_le_mul_left this hS0
  have hf' : 6 * S ^ 2 + 4 * S - 4 ≥ 28 * S ^ 2 * (1 - u) := by
    have := (div_le_iff₀ (by positivity : (0 : ℝ) < 28 * S ^ 2)).1
      (show (S - 2) ^ 2 / (28 * S ^ 2) ≤ u - 3 / 4 by linarith)
    nlinarith
  have hH2 : 2 ≤ H → 77 / 100 ≤ u ∧ H ≤ 76 / 35 := by
    intro h2
    constructor
    · have hS8 : 8 < S := by
        have : 2 * S ≤ S ^ 2 * (1 - u) - 1 := by rw [← hSH]; nlinarith
        nlinarith
      have : 9 / 448 ≤ (S - 2) ^ 2 / (28 * S ^ 2) := by
        rw [le_div_iff₀ (by positivity)]; nlinarith
      linarith
    · have : 35 * (S * H) ≤ 35 * ((6 * S ^ 2 + 4 * S - 32) / 28) := by rw [hSH]; linarith
      have : S * H ≤ S * (76 / 35) := by nlinarith
      exact le_of_mul_le_mul_left this hS0
  have h00 := lgr_N00 hu hu' hH0 hH2
  have h07 := lgr_N017 hu hu' hH0 hH24
  have hN0 := lgr_N0s hσ hσ7 hu h00 h07
  have hN1 := lgr_N1s hσ hσ7 hS hu hu' hH h00
  -- concavity in `a`
  have hf2 : 0 ≤ (2 * S - 1 - H) ^ 2 - 4 * u * (S ^ 2 - S + 1) := by
    have e : S ^ 2 * ((2 * S - 1 - H) ^ 2 - 4 * u * (S ^ 2 - S + 1)) =
        (S ^ 2 * u - S ^ 2 + S - 1) ^ 2 := by rw [hH]; field_simp; ring
    have : 0 ≤ S ^ 2 * ((2 * S - 1 - H) ^ 2 - 4 * u * (S ^ 2 - S + 1)) := by rw [e]; positivity
    exact nonneg_of_mul_nonneg_right this (by positivity)
  have e : 20 * u * (1 - σ * (5 / 2 * (2 * (1 - a) + S * a + Δ * -H) + 1 +
      (2 * Δ * u + (1 - a) * -H - (2 * S - 1) * a)) +
      5 * σ ^ 2 * ((1 - a) ^ 2 + (1 - a) * (S * a) + (S * a) ^ 2 + Δ ^ 2 * u +
        Δ * (1 - a) * -H - Δ * (2 * S - 1) * a)) =
      (1 - a) * (-25 * H ^ 2 / 4 + 10 * H * u - 4 * u ^ 2 + 20 * u + σ * (25 * H ^ 2 - 120 * u) +
        σ ^ 2 * (100 * u - 25 * H ^ 2)) +
      a * (-25 * H ^ 2 / 4 + 10 * H * u - 4 * u ^ 2 + 20 * u + σ * (50 * H * S - 25 * H -
        50 * S * u - 20 * u) + σ ^ 2 * (100 * S ^ 2 * u - 100 * S ^ 2 + 100 * S - 25)) +
      25 * σ ^ 2 * ((2 * S - 1 - H) ^ 2 - 4 * u * (S ^ 2 - S + 1)) * (a * (1 - a)) +
      (10 * u * Δ * σ - (2 * u - 5 * H / 2 + 5 * ((1 - a) * H + (2 * S - 1) * a) * σ)) ^ 2 := by
    ring
  have k3 : 0 ≤ 25 * σ ^ 2 * ((2 * S - 1 - H) ^ 2 - 4 * u * (S ^ 2 - S + 1)) * (a * (1 - a)) :=
    mul_nonneg (mul_nonneg (by positivity) hf2) (mul_nonneg ha0 (by linarith))
  have k4 := sq_nonneg (10 * u * Δ * σ - (2 * u - 5 * H / 2 + 5 * ((1 - a) * H +
    (2 * S - 1) * a) * σ))
  have k1 := mul_nonneg (by linarith : (0 : ℝ) ≤ 1 - a) hN0.le
  have k2 := mul_nonneg ha0 hN1.le
  have hpos : 0 < 20 * u * (1 - σ * (5 / 2 * (2 * (1 - a) + S * a + Δ * -H) + 1 +
      (2 * Δ * u + (1 - a) * -H - (2 * S - 1) * a)) +
      5 * σ ^ 2 * ((1 - a) ^ 2 + (1 - a) * (S * a) + (S * a) ^ 2 + Δ ^ 2 * u +
        Δ * (1 - a) * -H - Δ * (2 * S - 1) * a)) := by
    rw [e]
    rcases le_total a (1 / 2) with ha2 | ha2
    · have := mul_pos (by linarith : (0 : ℝ) < 1 - a) hN0; linarith
    · have := mul_pos (by linarith : (0 : ℝ) < a) hN1; linarith
  exact pos_of_mul_pos_right hpos (by linarith)

/-- **The `τ = 2` face can be pushed**: for `12/5 ≤ x ≤ 9`, `1 ≤ α ≤ x ≤ β`, the *actual*
`u = Sec(1, x, β) ≤ 13/16` (the uniform floor `ss_sec_gt_floor` is essential),
`G₂(q) = R*_2 + ½(w_* - 3/4)` is strictly increasing on `(0, 1/7]`.
The bound `log(q₂/q₁) ≥ 2(q₂ - q₁)/(q₂ + q₁)` (`ss_log_ge_pade`) reduces the increment to
`σG₂'(σ) > 0` at the midpoint `σ`, with no derivative; the two quadratics in `σ` (`α⁻² = 0, 1`) are
handled by a convex/concave case split. -/
theorem lgr_tau_two {x be al u q₁ q₂ : ℝ} (hx : 12 / 5 ≤ x) (hx9 : x ≤ 9) (hal : 1 ≤ al)
    (hax : al ≤ x) (hxb : x ≤ be) (hu : u = m2Sec 1 x be) (hu' : u ≤ 13 / 16) (hq₁ : 0 < q₁)
    (hq : q₁ < q₂) (hq₂ : q₂ ≤ 1 / 7) :
    ssF x be al u q₁ 2 (log (2 * q₁ / ssRA al be)) (1 / 2) <
      ssF x be al u q₂ 2 (log (2 * q₂ / ssRA al be)) (1 / 2) := by
  have hx1 : 1 < x := by linarith
  have hal0 : 0 < al := by linarith
  have ha2 : 0 < al ^ 2 := by positivity
  have hr0 : 0 < ssRA al be := by unfold ssRA; exact div_pos hal0 (by linarith)
  have hq2 : 0 < q₂ := by linarith
  -- the incoming floor
  have hfl := ss_sec_gt_floor hx1 hx9 hxb
  rw [← hu] at hfl
  have hf : 3 / 4 + ((1 + x) - 2) ^ 2 / (28 * (1 + x) ^ 2) ≤ u := by
    unfold ssUf at hfl
    have e : ((1 + x) - 2) ^ 2 / (28 * (1 + x) ^ 2) = (x - 1) ^ 2 / (28 * (x + 1) ^ 2) := by ring
    rw [e]; linarith
  -- the slope at the midpoint
  have hΨ := lgr_Psi_pos (S := 1 + x) (u := u) (a := 1 / al ^ 2) (Δ := ssDg x be al / al ^ 2)
    (σ := (q₁ + q₂) / 2) (H := -ssE0 x u) (by linarith) (by linarith) hu' hf (by positivity)
    (by rw [div_le_one ha2]; exact one_le_pow₀ hal) (by linarith) (by linarith)
    (by unfold ssE0; ring)
  have eA : 1 - (q₁ + q₂) / 2 * (5 / 2 * ssA1 x be al u + 1 + ssA3 x be al u) +
      5 * ((q₁ + q₂) / 2) ^ 2 * ssA2 x be al u = 1 - (q₁ + q₂) / 2 * (5 / 2 * (2 * (1
          - 1 / al ^ 2) +
      (1 + x) * (1 / al ^ 2) + ssDg x be al / al ^ 2 * - -ssE0 x u) + 1 +
      (2 * (ssDg x be al / al ^ 2) * u + (1 - 1 / al ^ 2) * - -ssE0 x u -
        (2 * (1 + x) - 1) * (1 / al ^ 2))) +
      5 * ((q₁ + q₂) / 2) ^ 2 * ((1 - 1 / al ^ 2) ^ 2 + (1 - 1 / al ^ 2) * ((1
          + x) * (1 / al ^ 2)) +
        ((1 + x) * (1 / al ^ 2)) ^ 2 + (ssDg x be al / al ^ 2) ^ 2 * u +
        ssDg x be al / al ^ 2 * (1 - 1 / al ^ 2) * - -ssE0 x u -
        ssDg x be al / al ^ 2 * (2 * (1 + x) - 1) * (1 / al ^ 2)) := by
    unfold ssA1 ssA2 ssA3; ring
  rw [← eA] at hΨ
  -- the increment
  have e : ssF x be al u q₂ 2 (log (2 * q₂ / ssRA al be)) (1 / 2) -
      ssF x be al u q₁ 2 (log (2 * q₁ / ssRA al be)) (1 / 2) =
      (q₂ - q₁) * (-(5 / 2) * ssA1 x be al u + 5 / 2 * (q₁ + q₂) * ssA2 x be al u - 1 -
        ssA3 x be al u) + (log (2 * q₂ / ssRA al be) - log (2 * q₁ / ssRA al be)) := by
    unfold ssF ssWs ssELs; ring
  have hlog : 2 * (q₂ - q₁) / (q₂ + q₁) ≤ log (2 * q₂ / ssRA al be)
      - log (2 * q₁ / ssRA al be) := by
    rw [← Real.log_div (by positivity) (by positivity)]
    have ez : 2 * q₂ / ssRA al be / (2 * q₁ / ssRA al be) = q₂ / q₁ := by field_simp
    rw [ez]
    have h1 : 1 ≤ q₂ / q₁ := by rw [le_div_iff₀ hq₁]; linarith
    have h2 := ss_log_ge_pade h1
    have ez2 : 2 * (q₂ / q₁ - 1) / (q₂ / q₁ + 1) = 2 * (q₂ - q₁) / (q₂ + q₁) := by
      field_simp
    linarith
  -- `(q₂ - q₁)·Ψ(σ)/σ > 0`
  have key : 0 < (q₂ - q₁) * (-(5 / 2) * ssA1 x be al u + 5 / 2 * (q₁ + q₂) * ssA2 x be al u - 1 -
      ssA3 x be al u) + 2 * (q₂ - q₁) / (q₂ + q₁) := by
    have e2 : (q₂ - q₁) * (-(5 / 2) * ssA1 x be al u + 5 / 2 * (q₁ + q₂) * ssA2 x be al u - 1 -
        ssA3 x be al u) + 2 * (q₂ - q₁) / (q₂ + q₁) = (q₂ - q₁) * (2 / (q₁ + q₂)) *
        (1 - (q₁ + q₂) / 2 * (5 / 2 * ssA1 x be al u + 1 + ssA3 x be al u) +
          5 * ((q₁ + q₂) / 2) ^ 2 * ssA2 x be al u) := by
      field_simp; ring
    rw [e2]
    exact mul_pos (mul_pos (by linarith) (by positivity)) hΨ
  linarith

/-! ### Face signs -/

/-- **The central face, `τ = 2` test**: on `Dom_c` (`12/5 ≤ x ≤ 9`, `1 ≤ α ≤ (5x + 4)/12`,
`x ≤ β ≤ x + x(7x + 1)(α - 1)/(4x² + 11x + 1)`), at `q = q_c`, `u = û(x, β)`, `T = r_A/q_c`:
`F(2, 5/(2T) - 11/9) < 0` for the floor-weighted face value. Proved in `SmallerShort/LargeRatio/CentralFace*` (beta
convexity, the lower face and four upper faces). -/
theorem lgr_central_tau_two {x al be : ℝ} (hx : 12 / 5 ≤ x) (hx9 : x ≤ 9) (hal : 1 ≤ al)
    (hal' : al ≤ (5 * x + 4) / 12) (hxb : x ≤ be)
    (hb : be ≤ x + x * (7 * x + 1) * (al - 1) / (4 * x ^ 2 + 11 * x + 1)) :
    ssF x be al (ssUhat x be) (ssQc x al) 2
      (5 / (2 * (ssRA al be / ssQc x al)) - 11 / 9) (1 / 2) < 0 := by
  apply lgr_central_tau_two_proof <;> assumption

/-- **The central face, `τ = T` and `τ = 8T/9` tests**: on `Dom_c`, at `q = q_c`, `u = û`,
`T = r_A/q_c`: `F(T, 0) < 0` and `F(8T/9, -1/9) < 0` (no condition `cT ≥ 2`). Proved in
`SmallerShort/LargeRatio/CentralFace*` (beta convexity, the lower face and four upper faces). -/
theorem lgr_central_duration {x al be : ℝ} (hx : 12 / 5 ≤ x) (hx9 : x ≤ 9) (hal : 1 ≤ al)
    (hal' : al ≤ (5 * x + 4) / 12) (hxb : x ≤ be)
    (hb : be ≤ x + x * (7 * x + 1) * (al - 1) / (4 * x ^ 2 + 11 * x + 1)) :
    ssF x be al (ssUhat x be) (ssQc x al) (ssRA al be / ssQc x al) 0 (1 / 2) < 0 ∧
      ssF x be al (ssUhat x be) (ssQc x al) (8 * (ssRA al be / ssQc x al) / 9) (-1 / 9) (1 / 2) <
        0 := by
  apply lgr_central_duration_proof <;> assumption

/-- **The outer face, three tests**: on `Dom_o` (`12/5 ≤ x ≤ 9`, `(22x + 20)/55 ≤ α ≤ x`,
`x + 4x(α - 1)/(5x + 4) ≤ β ≤ x + x(7x + 1)(α - 1)/(4x² + 11x + 1)`), at `q = 1/7`, `u = ū(x, β)`,
`T = 7r_A`: `F(T, 0) < 0`, `F(8T/9, -1/9) < 0`, `F(2, 5/(2T) - 11/9) < 0`. Proved in
`SmallerShort/LargeRatio/OuterFace*` (the cubic comparison on the large shapes, beta convexity and five faces on the
strip). -/
theorem lgr_outer_tests {x al be : ℝ} (hx : 12 / 5 ≤ x) (hx9 : x ≤ 9)
    (hal : (22 * x + 20) / 55 ≤ al) (hax : al ≤ x)
    (hb : x + 4 * x * (al - 1) / (5 * x + 4) ≤ be)
    (hb' : be ≤ x + x * (7 * x + 1) * (al - 1) / (4 * x ^ 2 + 11 * x + 1)) :
    ssF x be al (ssUbar x be) (1 / 7) (7 * ssRA al be) 0 (1 / 2) < 0 ∧
      ssF x be al (ssUbar x be) (1 / 7) (8 * (7 * ssRA al be) / 9) (-1 / 9) (1 / 2) < 0 ∧
      ssF x be al (ssUbar x be) (1 / 7) 2 (5 / (2 * (7 * ssRA al be)) - 11 / 9) (1 / 2) < 0 := by
  apply lgr_outer_tests_proof <;> assumption

/-! ### The large-ratio bound -/

/-- One face of the large-ratio bound: the floor-weighted value at a face scale `q_f ≤ 1/7` with a duration
`τ ∈ [2, T]` (or `τ = 2`), after raising `u` to a ceiling `u_c`, is bounded by the largest of the
three duration tests. -/
private theorem lgr_face_step {x be al u uc qf τs T : ℝ} (hx : 12 / 5 ≤ x) (hx9 : x ≤ 9)
    (hal : 1 ≤ al) (hax : al ≤ x) (hxb : x ≤ be) (hab : al < be)
    (hDQ : ssDg x be al < al * (al + be)) (hq : 0 < qf) (hq7 : qf ≤ 1 / 7) (hτs : 2 ≤ τs)
    (hcase : τs * qf ≤ ssRA al be ∨ τs = 2) (huc : u ≤ uc)
    (h0 : 0 ≤ ssF x be al u qf τs (log (τs * qf / ssRA al be)) (1 / 2))
    (hT : T = ssRA al be / qf) :
    0 ≤ max (ssF x be al uc qf 2 (5 / (2 * T) - 11 / 9) (1 / 2))
      (max (ssF x be al uc qf (8 * T / 9) (-1 / 9) (1 / 2)) (ssF x be al uc qf T 0 (1 / 2))) := by
  have hr0 : 0 < ssRA al be := by unfold ssRA; exact div_pos (by linarith) (by linarith)
  have hτ' : (2 ≤ τs ∧ τs * qf ≤ ssRA al be) ∨ τs = 2 := by
    rcases hcase with h | h
    · exact Or.inl ⟨hτs, h⟩
    · exact Or.inr h
  have h1 : 0 ≤ ssF x be al uc qf τs (log (τs * qf / ssRA al be)) (1 / 2) :=
    h0.trans (lgr_uslope hx hx9 hal hax hxb hab hDQ hq hq7 hτ' huc)
  rcases hcase with h | h
  · have e : τs * qf / ssRA al be = τs / T := by rw [hT]; field_simp
    rw [e] at h1
    have hτT : τs ≤ T := by rw [hT, le_div_iff₀ hq]; exact h
    exact h1.trans (ss_F_dur hτs hτT)
  · subst h
    have hl : log (2 * qf / ssRA al be) ≤ 5 / (2 * T) - 11 / 9 := by
      have := ss_log_le_tangent (div_pos (mul_pos two_pos hq) hr0)
      have e : 5 * (2 * qf / ssRA al be) / 4 = 5 / (2 * T) := by rw [hT]; field_simp; ring
      linarith
    exact (h1.trans (ss_F_ell_mono hl)).trans (le_max_left _ _)

namespace SmallerShortData

variable (H : SmallerShortData)

/-- **The large-ratio exclusion**: `x ≥ 12/5` is impossible. -/
private theorem lgr_large (hx : 12 / 5 ≤ H.x) : False := by
  have hx1 := H.one_lt_x
  have hx0 : 0 < H.x := by linarith
  have hx9 := H.x_le_nine
  have hal := H.one_le_al
  have hax := H.al_lt_x
  have hxb := H.x_le_be
  have hab : H.al < H.be := by linarith
  have hal0 : 0 < H.al := by linarith
  have hbe0 : 0 < H.be := by linarith
  have hQ : 0 < H.al * (H.al + H.be) := by positivity
  -- shape: `α/β < 3/4`, `D/Q < 1`
  have h43 := lgr_al_be hx hal hax hxb (H.u_eq.symm.trans H.u_eq')
  have hrA : ssRA H.al H.be < 3 / 7 := by
    unfold ssRA; rw [div_lt_iff₀ (by linarith)]; linarith
  have hDQ := lgr_DQ_le hx hal hax.le hxb h43.le
  have hDQ' : ssDg H.x H.be H.al < H.al * (H.al + H.be) := by
    have : 3 * (1 + H.x) ^ 2 / (7 * H.x ^ 2) < 1 := by
      rw [div_lt_one (by positivity)]; nlinarith
    nlinarith
  -- incoming norm
  have hu34 := H.u_ge_34
  have hu1316 := H.ss_u_le_1316
  have huV : H.u ≤ ssVbar H.x := H.u_le_V.trans (ss_V_le_Vbar hx1)
  -- scale
  have hq0 := H.ss_q_pos
  have hq7 := H.q_lt_seventh
  have hqc := H.q_le_qc
  have hτ2 := H.two_lt_τ
  have hτT : H.τ * H.q < ssRA H.al H.be := H.τ_lt
  have h2q := H.ss_two_q
  have hr0 := H.ss_rA_pos
  -- the comparison chain: `0 ≤ Φ(q)` at `p = τq`
  have hB : ∀ s ∈ Icc (H.rho * (1 + H.x)) H.t, 0 < 1 + (H.τ + 1 / 2) *
      (ssLam H.al H.rho * s - ssLam H.al H.rho * H.rho * ssDg H.x H.be H.al) := by
    intro s hs
    have hτT' : H.τ * ssQ H.al H.rho < ssRA H.al H.be := H.τ_lt
    have h2q' : 2 * ssQ H.al H.rho < ssRA H.al H.be := h2q
    exact ss_B_pos_weighted (by linarith) hal hax.le hxb H.rho_pos hs.1 (by linarith)
      h2q'.le (by nlinarith)
  have hphi := H.ss_root_phi (by norm_num : (0 : ℝ) ≤ 1 / 2) hB
  set p := H.τ * H.q with hp
  have hp0 : 0 < p := by positivity
  have hpr : p ≤ ssRA H.al H.be := hτT.le
  have hq2 : H.q ≤ p / 2 := by rw [hp]; nlinarith
  have hqc0 : 0 < ssQc H.x H.al := by unfold ssQc; positivity
  set qh := min (ssQc H.x H.al) (1 / 7) with hqh
  have hqh0 : 0 < qh := lt_min hqc0 (by norm_num)
  have hqh7 : qh ≤ 1 / 7 := min_le_right _ _
  -- the endpoint alternative and the zero-scale endpoint
  have halt := lgr_endpoint_alt (qm := min qh (p / 2)) hx hx9 hal hax.le hxb hu34 hu1316 hp0 hpr
    (le_min hqh0.le (by linarith)) (min_le_right _ _) hq0.le
    (le_min (le_min hqc hq7.le) hq2)
  have hz := lgr_G_zero_neg hx hal hax.le hxb hrA.le hDQ hu34 hu1316 huV hp0 hpr
  have hm : 0 ≤ ssPhi H.x H.be H.al H.u p (1 / 2) (min qh (p / 2)) := by
    rcases le_total (ssPhi H.x H.be H.al H.u p (1 / 2) 0)
      (ssPhi H.x H.be H.al H.u p (1 / 2) (min qh (p / 2))) with h | h
    · rw [max_eq_right h] at halt; linarith
    · rw [max_eq_left h] at halt; linarith
  -- a nonnegative value on the face `q = q̂`
  have hface : ∃ τs, 2 ≤ τs ∧ (τs * qh ≤ ssRA H.al H.be ∨ τs = 2) ∧
      0 ≤ ssF H.x H.be H.al H.u qh τs (log (τs * qh / ssRA H.al H.be)) (1 / 2) := by
    rcases le_total qh (p / 2) with h | h
    · rw [min_eq_left h] at hm
      refine ⟨p / qh, by rw [le_div_iff₀ hqh0]; linarith, Or.inl ?_, ?_⟩
      · rw [div_mul_cancel₀ _ hqh0.ne']; exact hpr
      · rw [div_mul_cancel₀ _ hqh0.ne', ss_phi_eq hp0 hqh0]; exact hm
    · rw [min_eq_right h] at hm
      refine ⟨2, le_refl _, Or.inr rfl, ?_⟩
      rw [← ss_phi_eq hp0 (by positivity : (0 : ℝ) < p / 2)] at hm
      have e1 : p / (p / 2) = 2 := by field_simp
      have e2 : p / ssRA H.al H.be = 2 * (p / 2) / ssRA H.al H.be := by ring
      rw [e1, e2] at hm
      rcases eq_or_lt_of_le h with h' | h'
      · rw [← h']; exact hm
      · exact (hm.trans (lgr_tau_two hx hx9 hal hax.le hxb H.u_eq hu1316 (by positivity) h'
          hqh7).le)
  obtain ⟨τs, hτs, hcase, h0⟩ := hface
  rcases le_or_gt (ssQc H.x H.al) (1 / 7) with hc | hc
  · -- the central face `q = q_c ≤ 1/7`
    rw [hqh, min_eq_left hc] at hcase h0
    have h6 := (ss_qc_le_iff hx0).1 hc
    have hal' := (lgr_face_alpha hx0 hal0.le).1 h6
    have hb := H.ss_strip_up
    have huc : H.u ≤ ssUhat H.x H.be := by
      rw [H.u_eq]
      exact (ss_sec_le_ubar hx1 hxb).trans (lgr_ubar_le_uhat hx hx9 hal hal' hxb hb)
    have hmax := lgr_face_step hx hx9 hal hax.le hxb hab hDQ' hqc0 hc hτs hcase huc h0 rfl
    have hc2 := lgr_central_tau_two hx hx9 hal hal' hxb hb
    have hcd := lgr_central_duration hx hx9 hal hal' hxb hb
    have := max_lt hc2 (max_lt hcd.2 hcd.1)
    linarith
  · -- the outer face `q = 1/7 < q_c`
    rw [hqh, min_eq_right hc.le] at hcase h0
    have h6 : H.x * (H.x + 2) ≤ 6 * H.al ^ 2 := by
      by_contra h'
      push Not at h'
      exact absurd ((ss_qc_le_iff hx0).2 h'.le) (not_le.2 hc)
    have hal' := (lgr_face_alpha hx0 hal0.le).2 hx h6
    have huc : H.u ≤ ssUbar H.x H.be := by rw [H.u_eq]; exact ss_sec_le_ubar hx1 hxb
    have hmax := lgr_face_step (T := 7 * ssRA H.al H.be) hx hx9 hal hax.le hxb hab hDQ'
      (by norm_num) (le_refl _) hτs hcase huc h0 (by field_simp)
    have ho := lgr_outer_tests hx hx9 hal' hax.le H.ss_strip_54 H.ss_strip_up
    have := max_lt ho.2.2 (max_lt ho.2.1 ho.1)
    linarith

/-- **The large-ratio bound**: `x < 12/5`, `D > 0`, `E_L > 0`.
Proof: if `x ≥ 12/5`: `root_zero`, `w_ge` and `ss_env_weighted` (`m = 1/2`, factor positivity
`ss_B_pos_weighted`) give `0 ≤ G*_τ(q)`; `lgr_al_be`, `lgr_DQ_le` give `r_A < 3/7`, `D/Q < 1`; `ss_phi_eq`,
`q_le_qc`, `q_lt_seventh`, `lgr_endpoint_alt`, `lgr_G_zero_neg` (with `u_le_V`, `ss_V_le_Vbar`),
`lgr_tau_two` move to a face; `lgr_uslope` with `ss_sec_le_ubar`, `lgr_ubar_le_uhat`; `ss_dur_three`;
`lgr_face_alpha`, `strong_order`, `upper_order_54` place the shape in `Dom_c`/`Dom_o`; contradiction
with `lgr_central_tau_two`, `lgr_central_duration`, `lgr_outer_tests`. Then `lgr_D_pos` (with
`be_le_al_x`) and `EL_eq`, `ss_E_le_env`, `lgr_pairing` (with `ss_V_le_U0`, `u_le_V`) give
`D > 0`, `E_L = λ(2ρDu - E) > 0`. -/
theorem ratio_lt_twelve_fifths : H.x < 12 / 5 ∧ 0 < ssDg H.x H.be H.al ∧ 0 < H.EL := by
  have hx1 := H.one_lt_x
  have hxlt : H.x < 12 / 5 := by
    by_contra h
    push Not at h
    exact H.lgr_large h
  have hD := lgr_D_pos hx1 hxlt.le H.one_le_al H.al_lt_x.le H.x_le_be H.be_le_al_x
  refine ⟨hxlt, by linarith [hD.2], ?_⟩
  -- `E_L = λ(2ρDu - E) > 0`
  have hS : 0 < 1 + H.x := by linarith
  have ht0 : H.rho * (1 + H.x) ≤ H.t := by
    have h := H.rho_lt_rt
    rw [one_div_mul_eq_div, lt_div_iff₀ hS] at h
    linarith
  have hE := ss_E_le_env (u := H.u) hx1 H.rho_pos ht0 H.t_le_r H.v_le
  have hρr : H.rho ≤ 1 / (1 + H.x) ^ 2 := by
    have h1 := H.rho_lt_rt
    have h2 := H.t_le_r
    have : 1 / (1 + H.x) * H.t ≤ 1 / (1 + H.x) * (1 / (1 + H.x)) :=
      mul_le_mul_of_nonneg_left h2 (by positivity)
    rw [one_div_mul_one_div, ← sq] at this
    linarith
  have hu0 : H.u ≤ ssU0 H.x := H.u_le_V.trans (ss_V_le_U0 hx1)
  have hpair := lgr_pairing hx1 hxlt.le H.rho_pos.le hρr hD.1 H.u_ge_34 hu0
  have hlam : 0 < ssLam H.al H.rho := by
    unfold ssLam
    have : 0 ≤ H.rho * (H.al ^ 2 - 1) := mul_nonneg H.rho_pos.le (by nlinarith [H.one_le_al])
    positivity
  rw [← H.E_eq] at hE
  rw [H.EL_eq]
  unfold ssEL
  rw [← H.E_eq]
  have : H.E < 2 * H.rho * ssDg H.x H.be H.al * H.u := by linarith
  have e : 2 * (ssLam H.al H.rho * H.rho * ssDg H.x H.be H.al) * H.u - ssLam H.al H.rho * H.E =
      ssLam H.al H.rho * (2 * H.rho * ssDg H.x H.be H.al * H.u - H.E) := by ring
  rw [e]
  exact mul_pos hlam (by linarith)

end SmallerShortData

/-- **The large-ratio bound for the actual window**: `C/a < 12/5`, `D > 0`, `E_L > 0`. -/
theorem M2Short.ratio_lt_twelve_fifths (D : M2Short) :
    D.C / D.a < 12 / 5 ∧ 0 < ssDg (D.C / D.a) (D.B / D.a) (D.A / D.a) ∧ 0 < D.EL := by
  have h := D.toData.ratio_lt_twelve_fifths
  rw [D.toData_x, D.toData_be, D.toData_al, D.toData_EL] at h
  exact h

end SmoothedOctagon
