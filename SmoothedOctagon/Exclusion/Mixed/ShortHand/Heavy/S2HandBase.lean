module

public import SmoothedOctagon.Exclusion.Mixed.ShortHand.S2Defs

/-!
# S2 hand signs: shared reductions

Shared scalar steps for the hand proofs of the three S2 face signs (`hs2_central_sign`,
`hs2_outer_sign_small`, `hs2_outer_sign_large`), following `archive/lighter-proofs/`
`SHORT_RATIO_CENTRAL_COMPLETE.md` and `SHORT_RATIO_OUTER_COMPLETE.md`.

## Main API

* `hl2_strip_c`: the strip coordinate `β = x + c(α - 1)`, `5/8 ≤ c ≤ 7/8`
  (`SHORT_RATIO_OUTER_COMPLETE` (7)).
* `hl2_hsF_face`: the face value `hsF` with `ℓ = log(τq/r_A)`, `m = 2 - 7τq/(4r_A)` is
  `G(τ) = (w - 1)τ + 1/τ + c + log(τk) + (2 - 7τk/4)(w - 3/4)`, `k = q/r_A`.
* `hl2_tau_outer`: for `2 ≤ τ ≤ 1/k`, `G(τ) ≤ max(G(2), G(2) + (1/k - 2)A)`,
  `A = (1 - 7k/4)(w - 3/4)` (`SHORT_RATIO_OUTER_COMPLETE` (5)).
* `hl2_le_max_of_deriv2`: a function with nonnegative second derivative on `[a, b]` is at most
  the larger endpoint value (the convexity step of the notes).
* Logarithm bounds: `hl2_log_le_quad` (`log y ≤ (y - 1) - (y - 1)²/2`, `0 < y ≤ 1`),
  `hl2_log_le_cubic` (`log y ≤ (y - 1) - (y - 1)²/2 + (y - 1)³/3`, `y > 0`).
-/

@[expose] public section

namespace SmoothedOctagon

open Real Set

/-- The strip coordinate: `β = x + c(α - 1)` with `5/8 ≤ c ≤ 7/8` (`SHORT_RATIO_OUTER_COMPLETE`
(7)). -/
theorem hl2_strip_c {x al be : ℝ} (hx : 13 / 6 ≤ x) (hx2 : x ≤ 12 / 5) (hal : 1 < al)
    (hb : x + 8 * x * (al - 1) / (9 * x + 8) ≤ be)
    (hb' : be ≤ x + x * (7 * x + 1) * (al - 1) / (4 * x ^ 2 + 11 * x + 1)) :
    ∃ c : ℝ, 5 / 8 ≤ c ∧ c ≤ 7 / 8 ∧ be = x + c * (al - 1) := by
  have ha : 0 < al - 1 := by linarith
  refine ⟨(be - x) / (al - 1), ?_, ?_, ?_⟩
  · rw [le_div_iff₀ ha]
    have h1 : 5 / 8 * (al - 1) ≤ 8 * x * (al - 1) / (9 * x + 8) := by
      rw [le_div_iff₀ (by linarith)]
      nlinarith
    linarith
  · rw [div_le_iff₀ ha]
    have h1 : x * (7 * x + 1) * (al - 1) / (4 * x ^ 2 + 11 * x + 1) ≤ 7 / 8 * (al - 1) := by
      rw [div_le_iff₀ (by positivity)]
      have hq : 0 ≤ 7 * (4 * x ^ 2 + 11 * x + 1) - 8 * x * (7 * x + 1) := by
        nlinarith [mul_nonneg (sub_nonneg.2 hx) (sub_nonneg.2 hx2)]
      nlinarith [mul_nonneg ha.le hq]
    linarith
  · field_simp
    ring

/-- **The face value.** `hsF` with `ℓ = log(τq/r_A)` and `m = 2 - 7τq/(4r_A)` in terms of
`k = q/r_A`. -/
theorem hl2_hsF_face (x be al u q τ : ℝ) :
    hsF x be al u q τ (log (τ * q / hsRA al be)) (2 - 7 * τ * q / (4 * hsRA al be)) =
      (hsWs x be al u q - 1) * τ + 1 / τ +
        ((u - 1) / hsRA al be + hsRA al be + 1 - q - hsELs x be al u q) +
        log (τ * (q / hsRA al be)) +
          (2 - 7 * τ * (q / hsRA al be) / 4) * (hsWs x be al u q - 3 / 4) := by
  unfold hsF
  rw [mul_div_assoc τ q]
  have : 7 * τ * q / (4 * hsRA al be) = 7 * τ * (q / hsRA al be) / 4 := by
    rw [mul_div_assoc, mul_div_assoc, div_mul_eq_div_div]
    ring
  rw [this]
  ring

/-- **Duration elimination, outer form** (`SHORT_RATIO_OUTER_COMPLETE` (5)): for `2 ≤ τ ≤ 1/k`,
`G(τ) ≤ max(G(2), G(2) + (1/k - 2)A)`, `A = (1 - 7k/4)(w - 3/4)`. -/
theorem hl2_tau_outer {W c k τ : ℝ} (hk : 0 < k) (h2 : 2 ≤ τ) (hτ : τ * k ≤ 1) :
    (W - 1) * τ + 1 / τ + c + log (τ * k) + (2 - 7 * τ * k / 4) * (W - 3 / 4) ≤
      max ((W - 1) * 2 + 1 / 2 + c + log (2 * k) + (2 - 7 * 2 * k / 4) * (W - 3 / 4))
        ((W - 1) * 2 + 1 / 2 + c + log (2 * k) + (2 - 7 * 2 * k / 4) * (W - 3 / 4) +
          (1 / k - 2) * ((1 - 7 * k / 4) * (W - 3 / 4))) := by
  have hτ0 : 0 < τ := by linarith
  have hlog : log (τ * k) = log (2 * k) + log (τ / 2) := by
    rw [← log_mul (by positivity) (by positivity)]
    congr 1
    field_simp
  have hhalf := ss_log_le_half (z := τ / 2) (by linarith)
  have e1 : (τ / 2 - (τ / 2)⁻¹) / 2 = τ / 4 - 1 / τ := by field_simp; try ring
  rw [e1] at hhalf
  have hτk : τ ≤ 1 / k := by rw [le_div_iff₀ hk]; linarith
  set A := (1 - 7 * k / 4) * (W - 3 / 4) with hA
  have key : (W - 1) * τ + 1 / τ + c + log (τ * k) + (2 - 7 * τ * k / 4) * (W - 3 / 4) ≤
      (W - 1) * 2 + 1 / 2 + c + log (2 * k) + (2 - 7 * 2 * k / 4) * (W - 3 / 4) + (τ - 2) * A := by
    rw [hlog, hA]
    nlinarith [hhalf]
  rcases le_total 0 A with hA0 | hA0
  · refine le_trans key (le_trans ?_ (le_max_right _ _))
    have : (τ - 2) * A ≤ (1 / k - 2) * A := mul_le_mul_of_nonneg_right (by linarith) hA0
    linarith
  · refine le_trans key (le_trans ?_ (le_max_left _ _))
    have : (τ - 2) * A ≤ 0 := mul_nonpos_of_nonneg_of_nonpos (by linarith) hA0
    linarith

/-- **Convexity bound**: a function whose derivative has a nonnegative derivative on `[a, b]` is
bounded on `[a, b]` by the larger of its two endpoint values. -/
theorem hl2_le_max_of_deriv2 {f f' f'' : ℝ → ℝ} {a b r : ℝ} (har : a ≤ r) (hrb : r ≤ b)
    (hf : ∀ s ∈ Icc a b, HasDerivAt f (f' s) s) (hf' : ∀ s ∈ Icc a b, HasDerivAt f' (f'' s) s)
    (h2 : ∀ s ∈ Icc a b, 0 ≤ f'' s) : f r ≤ max (f a) (f b) := by
  have hmono : ∀ s t, a ≤ s → s ≤ t → t ≤ b → f' s ≤ f' t := fun s t hs hst ht =>
    ss_le_of_deriv hst (fun z hz => hf' z ⟨hs.trans hz.1, hz.2.trans ht⟩)
      (fun z hz => h2 z ⟨hs.trans hz.1.le, hz.2.le.trans ht⟩)
  rcases le_total 0 (f' r) with h0 | h0
  · have : f r ≤ f b := ss_le_of_deriv hrb (fun z hz => hf z ⟨har.trans hz.1, hz.2⟩)
      (fun z hz => h0.trans (hmono r z har hz.1.le hz.2.le))
    exact this.trans (le_max_right _ _)
  · have : -f a ≤ -f r := ss_le_of_deriv (f := fun s => -f s) (f' := fun s => -f' s) har
      (fun z hz => (hf z ⟨hz.1, hz.2.trans hrb⟩).neg)
      (fun z hz => by have := hmono z r hz.1.le hz.2.le hrb; linarith)
    have : f r ≤ f a := by linarith
    exact this.trans (le_max_left _ _)

/-- `log y ≤ (y - 1) - (y - 1)²/2` for `0 < y ≤ 1` (`SHORT_RATIO_OUTER_OTHER_TERMINALS` (3); the
difference has derivative `-(y - 1)²/y ≤ 0`). -/
theorem hl2_log_le_quad {y : ℝ} (hy : 0 < y) (hy1 : y ≤ 1) :
    log y ≤ (y - 1) - (y - 1) ^ 2 / 2 := by
  have h := ss_le_of_deriv (f := fun s : ℝ => log s - ((s - 1) - (s - 1) ^ 2 / 2))
    (f' := fun s => (s - 1) ^ 2 / s) hy1 (fun s hs => ?_) (fun s hs => by
      have : 0 < s := by linarith [hs.1]
      positivity)
  · simp only [log_one, sub_self, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow,
      zero_div] at h
    linarith
  have hs0 : 0 < s := by linarith [hs.1]
  have hp : HasDerivAt (fun s : ℝ => (s - 1) - (s - 1) ^ 2 / 2) (1 - (s - 1)) s := by
    have h1 := (hasDerivAt_id' s).sub_const 1
    have := h1.sub ((h1.pow 2).div_const 2)
    convert this using 1
    simp
  convert (Real.hasDerivAt_log hs0.ne').sub hp using 1
  field_simp
  ring

/-- `log y ≤ (y - 1) - (y - 1)²/2 + (y - 1)³/3` for `y > 0` (`SHORT_RATIO_OUTER_TERMINAL_AF` (20);
the difference has derivative `(y - 1)³/y`). -/
theorem hl2_log_le_cubic {y : ℝ} (hy : 0 < y) :
    log y ≤ (y - 1) - (y - 1) ^ 2 / 2 + (y - 1) ^ 3 / 3 := by
  have hd : ∀ s : ℝ, 0 < s → HasDerivAt
      (fun s : ℝ => (s - 1) - (s - 1) ^ 2 / 2 + (s - 1) ^ 3 / 3 - log s) ((s - 1) ^ 3 / s) s := by
    intro s hs
    have h1 := (hasDerivAt_id' s).sub_const 1
    have hp := (h1.sub ((h1.pow 2).div_const 2)).add ((h1.pow 3).div_const 3)
    convert hp.sub (Real.hasDerivAt_log hs.ne') using 1
    field_simp
    ring
  rcases le_total 1 y with h | h
  · have := ss_le_of_deriv (f := fun s : ℝ => (s - 1) - (s - 1) ^ 2 / 2 + (s - 1) ^ 3 / 3 - log s)
      (f' := fun s => (s - 1) ^ 3 / s) h (fun s hs => hd s (by linarith [hs.1]))
      (fun s hs => by have : 0 < s - 1 := by linarith [hs.1]
                      have : 0 < s := by linarith [hs.1]
                      positivity)
    simp only [sub_self, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, zero_div,
      add_zero, log_one] at this
    linarith
  · have := ss_le_of_deriv
      (f := fun s : ℝ => -((s - 1) - (s - 1) ^ 2 / 2 + (s - 1) ^ 3 / 3 - log s))
      (f' := fun s => -((s - 1) ^ 3 / s)) h (fun s hs => (hd s (by linarith [hs.1])).neg)
      (fun s hs => by
        have h1 : 0 < s := by linarith [hs.1]
        have h2 : (s - 1) ^ 3 ≤ 0 := by
          have : s - 1 ≤ 0 := by linarith [hs.2]
          nlinarith [sq_nonneg (s - 1)]
        have : (s - 1) ^ 3 / s ≤ 0 := div_nonpos_of_nonpos_of_nonneg h2 h1.le
        linarith)
    simp only [sub_self, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, zero_div,
      add_zero, log_one, neg_zero] at this
    linarith

end SmoothedOctagon
