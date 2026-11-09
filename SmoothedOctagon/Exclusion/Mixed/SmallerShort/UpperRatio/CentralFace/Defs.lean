module

public import SmoothedOctagon.Exclusion.Mixed.SmallerShort.UpperRatio.Reductions

/-!
# Smaller-short window, upper ratio: the central face, definitions and duration tangent

The central sharp-ratio face (`q = q_c = α²/K`, `K = x(x + 2) + α²`), with `a = α`, `b = β`:
`w = (M + D²u - DE)/K²`, `E_L = (2Du - E)/K`, `k = aB/K`, `B = a + b`, `M = S²(S² - S + 1)`,
`E = S³(u - 1) + 3S - 1`, `S = 1 + x`, `R = (u - 1)B/a + a/B + 1 - a²/K - E_L`. The two
duration-tangent tests at a tangent point `t ≥ 2` are `urcF0`, `urcF1`.

## Main API

* `urcK`, `urcw`, `urcEL`, `urck`, `urcR`, `urcF0`, `urcF1`, `urcbp` (`b_+(x, a)`).
* `urc_face`: the face value `ssF` at `q = q_c` in terms of `w`, `R`, `k`.
* `urc_tangent`: `G_τ ≤ max(F₀(t), F₁(t))` for `2 ≤ τ ≤ 1/k`, `t ≥ 2`.
* `urc_strip`: the central strip lies in `x ≤ β ≤ b_+(x, a)`, and `a ≤ 4/3`.
-/

@[expose] public section

namespace SmoothedOctagon

open Real Set

/-- `K = x(x + 2) + a²`. -/
noncomputable def urcK (x a : ℝ) : ℝ := x * (x + 2) + a ^ 2

/-- The central outgoing norm `w = (M + D²u - DE)/K²`. -/
noncomputable def urcw (x a b u : ℝ) : ℝ :=
  ((1 + x) ^ 2 * ((1 + x) ^ 2 - (1 + x) + 1) + ssDg x b a ^ 2 * u -
    ssDg x b a * ((1 + x) ^ 3 * (u - 1) + 3 * (1 + x) - 1)) / urcK x a ^ 2

/-- The central pairing `E_L = (2Du - E)/K`. -/
noncomputable def urcEL (x a b u : ℝ) : ℝ :=
  (2 * ssDg x b a * u - ((1 + x) ^ 3 * (u - 1) + 3 * (1 + x) - 1)) / urcK x a

/-- `k = q_c/r_A = aB/K`. -/
noncomputable def urck (x a b : ℝ) : ℝ := a * (a + b) / urcK x a

/-- `R = (u - 1)B/a + a/B + 1 - a²/K - E_L`. -/
noncomputable def urcR (x a b u : ℝ) : ℝ :=
  (u - 1) * (a + b) / a + a / (a + b) + 1 - a ^ 2 / urcK x a - urcEL x a b u

/-- The first duration-tangent test `F₀(t) = R + (4 - 7k/2)h + 4/t - 2/t² - 3/2 + log(tk)`,
`h = w - 3/4` (the bound at `τ = 2`). -/
noncomputable def urcF0 (t x a b u : ℝ) : ℝ :=
  urcR x a b u + (4 - 7 * urck x a b / 2) * (urcw x a b u - 3 / 4) + 4 / t - 2 / t ^ 2 - 3 / 2 +
    log (t * urck x a b)

/-- The second duration-tangent test
`F₁(t) = R + (T + 1/4)h + T((t - 1)/t² - 1/4) + 2/t - 1 + log(tk)`, `T = 1/k` (the bound at
`τ = 1/k`). -/
noncomputable def urcF1 (t x a b u : ℝ) : ℝ :=
  urcR x a b u + (1 / urck x a b + 1 / 4) * (urcw x a b u - 3 / 4) +
    1 / urck x a b * ((t - 1) / t ^ 2 - 1 / 4) + 2 / t - 1 + log (t * urck x a b)

/-- The enclosing upper beta face `b_+(x, a) = x + (24x + 51)(a - 1)/128`. -/
noncomputable def urcbp (x a : ℝ) : ℝ := x + (24 * x + 51) * (a - 1) / 128

/-- **The central face value**: at `q = q_c` the face value `ssF` is
`(w - 1)τ + 1/τ + R + log(τk) + (2 - 7τk/4)(w - 3/4)`. -/
theorem urc_face {x a b u τ : ℝ} (ha : 0 < a) (hB : 0 < a + b) (hx : 0 < x) :
    ssF x b a u (ssQc x a) τ (log (τ * ssQc x a / ssRA a b))
        (2 - 7 * τ * ssQc x a / (4 * ssRA a b)) =
      (urcw x a b u - 1) * τ + 1 / τ + urcR x a b u + log (τ * urck x a b) +
        (2 - 7 * τ * urck x a b / 4) * (urcw x a b u - 3 / 4) := by
  have hK : 0 < urcK x a := by unfold urcK; positivity
  have hk : ssQc x a / ssRA a b = urck x a b := by
    unfold ssQc ssRA urck urcK; field_simp
  have hW : ssWs x b a u (ssQc x a) = urcw x a b u := by
    unfold ssWs ssA1 ssA2 ssQc urcw urcK
    unfold urcK at hK
    generalize ssDg x b a = D
    unfold ssE0
    field_simp
    ring
  have hE : ssELs x b a u (ssQc x a) = urcEL x a b u := by
    unfold ssELs ssA3 ssQc urcEL urcK
    unfold urcK at hK
    generalize ssDg x b a = D
    unfold ssE0
    field_simp
    ring
  rw [ur_hsF_face, hk, hW, hE]
  unfold urcR ssRA ssQc
  have : (u - 1) / (a / (a + b)) = (u - 1) * (a + b) / a := by field_simp
  rw [this]
  have : a ^ 2 / (x * (x + 2) + a ^ 2) = a ^ 2 / urcK x a := rfl
  rw [this]

/-- **Concavity of `log τ + 1/τ` on `[2, ∞)`**: its tangent at `t ≥ 2` lies above it. -/
theorem urc_log_tangent {t τ : ℝ} (ht : 2 ≤ t) (h2 : 2 ≤ τ) :
    log τ + 1 / τ ≤ log t + 2 / t - 1 + τ * (t - 1) / t ^ 2 := by
  have ht0 : 0 < t := by linarith
  -- `g(s) = [tangent at t](s) - log s - 1/s`, `g' = (s - t)(ts - s - t)/(s²t²)`
  have hd : ∀ s : ℝ, 0 < s → HasDerivAt (fun s => log t + 2 / t - 1 + s * (t - 1) / t ^ 2 -
      (log s + 1 / s)) ((t - 1) / t ^ 2 - (1 / s - 1 / s ^ 2)) s := by
    intro s hs
    have h1 := (Real.hasDerivAt_log hs.ne').add (hasDerivAt_inv hs.ne')
    have h2 := ((hasDerivAt_id s).mul_const ((t - 1) / t ^ 2)).const_add (log t + 2 / t - 1)
    convert h2.sub h1 using 1
    · funext y; simp [one_div]; ring
    · simp; ring
  have hsign : ∀ s : ℝ, 2 ≤ s → (t - 1) / t ^ 2 - (1 / s - 1 / s ^ 2) =
      (s - t) * (t * s - s - t) / (s ^ 2 * t ^ 2) := fun s hs => by
    have : s ≠ 0 := by linarith
    field_simp; ring
  have g0 : log t + 2 / t - 1 + t * (t - 1) / t ^ 2 - (log t + 1 / t) = 0 := by
    field_simp; ring
  rcases le_total t τ with h | h
  · have := ss_le_of_deriv h (fun s hs => hd s (by linarith [hs.1])) (fun s hs => by
      rw [hsign s (by linarith [hs.1])]
      apply div_nonneg _ (by positivity)
      apply mul_nonneg (by linarith [hs.1])
      nlinarith [hs.1])
    linarith
  · have := ss_le_of_deriv (f := fun s => -(log t + 2 / t - 1 + s * (t - 1) / t ^ 2 -
      (log s + 1 / s))) (f' := fun s => -((t - 1) / t ^ 2 - (1 / s - 1 / s ^ 2))) h
      (fun s hs => (hd s (by linarith [hs.1])).neg) (fun s hs => by
        rw [hsign s (by linarith [hs.1])]
        have : (s - t) * (t * s - s - t) / (s ^ 2 * t ^ 2) ≤ 0 := by
          apply div_nonpos_of_nonpos_of_nonneg _ (by positivity)
          apply mul_nonpos_of_nonpos_of_nonneg (by linarith [hs.2])
          nlinarith [hs.1]
        linarith)
    linarith

/-- **The duration tangent**: `log τ + 1/τ` is concave on
`[2, ∞)`, so for `t ≥ 2` and `2 ≤ τ ≤ 1/k`, `G_τ ≤ max(F₀(t), F₁(t))`. -/
theorem urc_tangent {W R k t τ : ℝ} (hk : 0 < k) (ht : 2 ≤ t) (h2 : 2 ≤ τ) (hτ : τ * k ≤ 1) :
    (W - 1) * τ + 1 / τ + R + log (τ * k) + (2 - 7 * τ * k / 4) * (W - 3 / 4) ≤
      max (R + (4 - 7 * k / 2) * (W - 3 / 4) + 4 / t - 2 / t ^ 2 - 3 / 2 + log (t * k))
        (R + (1 / k + 1 / 4) * (W - 3 / 4) + 1 / k * ((t - 1) / t ^ 2 - 1 / 4) + 2 / t - 1 +
          log (t * k)) := by
  have hτ0 : 0 < τ := by linarith
  have ht0 : 0 < t := by linarith
  -- the tangent: `log τ + 1/τ ≤ log t + 2/t - 1 + τ(t - 1)/t²`
  have htan : log τ + 1 / τ ≤ log t + 2 / t - 1 + τ * (t - 1) / t ^ 2 :=
    urc_log_tangent ht h2
  have hlogk : log (τ * k) = log τ + log k := log_mul hτ0.ne' hk.ne'
  have hlogt : log (t * k) = log t + log k := log_mul ht0.ne' hk.ne'
  rw [hlogk, hlogt]
  set h := W - 3 / 4 with hh
  have hT : τ ≤ 1 / k := by rw [le_div_iff₀ hk]; linarith
  -- affine upper bound in `τ`
  have aff : (W - 1) * τ + 1 / τ + R + (log τ + log k) + (2 - 7 * τ * k / 4) * h ≤
      R + log k + log t + 2 / t - 1 + 2 * h + τ * (h - 1 / 4 + (t - 1) / t ^ 2 - 7 * k * h / 4) := by
    have e : (W - 1) * τ + 1 / τ + R + (log τ + log k) + (2 - 7 * τ * k / 4) * h -
        (R + log k + log t + 2 / t - 1 + 2 * h + τ * (h - 1 / 4 + (t - 1) / t ^ 2 - 7 * k * h / 4)) =
        (log τ + 1 / τ) - (log t + 2 / t - 1 + τ * (t - 1) / t ^ 2) := by rw [hh]; ring
    linarith
  rcases le_total 0 (h - 1 / 4 + (t - 1) / t ^ 2 - 7 * k * h / 4) with hs | hs
  · refine le_trans aff (le_trans ?_ (le_max_right _ _))
    have := mul_le_mul_of_nonneg_right hT hs
    have e : R + log k + log t + 2 / t - 1 + 2 * h + 1 / k * (h - 1 / 4 + (t - 1) / t ^ 2 -
        7 * k * h / 4) = R + (1 / k + 1 / 4) * h + 1 / k * ((t - 1) / t ^ 2 - 1 / 4) + 2 / t - 1 +
        (log t + log k) := by field_simp; ring
    linarith
  · refine le_trans aff (le_trans ?_ (le_max_left _ _))
    have := mul_le_mul_of_nonpos_right h2 hs
    have e : R + log k + log t + 2 / t - 1 + 2 * h + 2 * (h - 1 / 4 + (t - 1) / t ^ 2 -
        7 * k * h / 4) = R + (4 - 7 * k / 2) * h + 4 / t - 2 / t ^ 2 - 3 / 2 + (log t + log k) := by
      field_simp; ring
    linarith

/-- **The central strip**: `1 ≤ a ≤ 4/3` and
`x ≤ β ≤ b_+(x, a)`. -/
theorem urc_strip {x al be : ℝ} (hx : 13 / 6 ≤ x) (hx2 : x ≤ 12 / 5) (hal : 1 ≤ al)
    (hqc : 6 * al ^ 2 ≤ x * (x + 2)) (hb : x + 8 * x * (al - 1) / (9 * x + 8) ≤ be)
    (hb' : be ≤ x + x * (7 * x + 1) * (al - 1) / (4 * x ^ 2 + 11 * x + 1)) :
    al ≤ 4 / 3 ∧ x ≤ be ∧ be ≤ urcbp x al := by
  have hal' : al ≤ 4 / 3 := by
    nlinarith [sq_nonneg (al - 4 / 3), mul_nonneg (sub_nonneg.2 hx) (sub_nonneg.2 hx2)]
  refine ⟨hal', ?_, ?_⟩
  · have : 0 ≤ 8 * x * (al - 1) / (9 * x + 8) := by
      apply div_nonneg _ (by linarith); nlinarith
    linarith
  · unfold urcbp
    have h1 : x * (7 * x + 1) * (al - 1) / (4 * x ^ 2 + 11 * x + 1) ≤ (24 * x + 51) * (al - 1) / 128 := by
      rw [div_le_div_iff₀ (by positivity) (by norm_num)]
      have hq : 0 ≤ (24 * x + 51) * (4 * x ^ 2 + 11 * x + 1) - 128 * x * (7 * x + 1) := by
        nlinarith [mul_nonneg (sub_nonneg.2 hx) (sub_nonneg.2 hx2), sq_nonneg (x - 9 / 4),
          mul_nonneg (mul_nonneg (sub_nonneg.2 hx) (sub_nonneg.2 hx)) (sub_nonneg.2 hx)]
      nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ al - 1) hq]
    linarith

end SmoothedOctagon
