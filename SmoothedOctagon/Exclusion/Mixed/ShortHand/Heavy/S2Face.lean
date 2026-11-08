module

public import SmoothedOctagon.Exclusion.Mixed.ShortHand.S2Defs

/-!
# S2 heavy face signs: shared reductions

Shared scalar steps for the three heavy S2 face signs (`hs2_central_sign`, `hs2_outer_sign_small`,
`hs2_outer_sign_large`; `CENTRAL_RATIO_HAND_SIGN`, `OUTER_RATIO_HAND_SIGN`, inventory HS-S2 R23-R24).

* `hh2_hsF_face`: the face value `hsF` with `ℓ = log(τq/r_A)`, `m = 2 - 7τq/(4r_A)` is
  `G(τ) = (w - 1)τ + 1/τ + c + log(τk) + (2 - 7τk/4)(w - 3/4)` with `k = q/r_A`.
* Duration elimination (`CENTRAL_RATIO_HAND_SIGN` (9)-(11), `OUTER_RATIO_HAND_SIGN` (5)): with
  `A = (1 - 7k/4)(w - 3/4)` and `2 ≤ τ ≤ 1/k`,
  `hh2_tau_outer`: `G(τ) ≤ max(G(2), G(2) + (1/k - 2)A)`;
  `hh2_tau_central`: `G(τ) ≤ max(G(2), G(2) + (8A² + A/18)/k)` (the cubic loss).
* Logarithm: `hh2_log_taylor3` (`log(1 + t) ≤ t - t²/2 + t³/3`, `t > -1`),
  `hh2_log_le_bound` (`log y ≤ -296/1029 + t - t²/2 + t³/3`, `t = 4y/3 - 1`, the cubic Taylor
  majorant at `3/4` with `log(4/3) ≥ 296/1029`), `hh2_log_le_cubic_loss` (`log z ≤ (z - 1/z)/2 -
  (z - 1)³/(6z²)`, `z ≥ 1`).
* The outer face (`q = 1/7`) transport formulas `hh2_Ws_outer`, `hh2_ELs_outer` and the central
  face (`q = q_c`) formulas `hh2_Ws_central`, `hh2_ELs_central`.

Route: the logarithm is bounded by its cubic Taylor polynomial at `3/4` (the notes use
`2 artanh` partial sums); the bound is polynomial in `k`, which keeps the cleared numerators small.
-/

set_option linter.unusedSimpArgs false

@[expose] public section

namespace SmoothedOctagon

open Real Set

/-! ### Logarithm bounds -/

/-- `log (1 + t) ≤ t - t²/2 + t³/3` for `t > -1` (derivative of the difference `t³/(1 + t)`). -/
theorem hh2_log_taylor3 {t : ℝ} (ht : -1 < t) : log (1 + t) ≤ t - t ^ 2 / 2 + t ^ 3 / 3 := by
  have hd : ∀ s : ℝ, -1 < s →
      HasDerivAt (fun s : ℝ => s - s ^ 2 / 2 + s ^ 3 / 3 - log (1 + s)) (s ^ 3 / (1 + s)) s := by
    intro s hs
    have h1 : (1 + s) ≠ 0 := by linarith
    have hl : HasDerivAt (fun s : ℝ => log (1 + s)) (1 / (1 + s)) s := by
      have := ((hasDerivAt_id s).const_add 1).log (by simpa using h1)
      simpa using this
    have hp : HasDerivAt (fun s : ℝ => s - s ^ 2 / 2 + s ^ 3 / 3) (1 - s + s ^ 2) s := by
      have := ((hasDerivAt_id' s).sub (((hasDerivAt_id' s).mul (hasDerivAt_id' s)).div_const 2)).add
        ((((hasDerivAt_id' s).mul (hasDerivAt_id' s)).mul (hasDerivAt_id' s)).div_const 3)
      convert this using 1
      · funext t; simp only [Pi.mul_apply, Pi.add_apply, Pi.sub_apply, Pi.pow_apply]; ring1
      · simp only [Pi.mul_apply, Pi.add_apply, Pi.sub_apply, Pi.pow_apply]; ring1
    convert hp.sub hl using 1
    field_simp
    ring
  rcases le_total 0 t with h | h
  · have := ss_le_of_deriv (f := fun s : ℝ => s - s ^ 2 / 2 + s ^ 3 / 3 - log (1 + s))
      (f' := fun s => s ^ 3 / (1 + s)) h (fun s hs => hd s (by linarith [hs.1]))
      (fun s hs => by have := hs.1; positivity)
    simp only [add_zero, log_one] at this
    norm_num at this
    linarith
  · have := ss_le_of_deriv (f := fun s : ℝ => -(s - s ^ 2 / 2 + s ^ 3 / 3 - log (1 + s)))
      (f' := fun s => -(s ^ 3 / (1 + s))) h (fun s hs => (hd s (by linarith [hs.1])).neg)
      (fun s hs => by
        have h1 : 0 < 1 + s := by linarith [hs.1]
        have h2 : s ^ 3 ≤ 0 := by
          have : s ≤ 0 := hs.2.le
          nlinarith [sq_nonneg s]
        have : s ^ 3 / (1 + s) ≤ 0 := div_nonpos_of_nonpos_of_nonneg h2 h1.le
        linarith)
    simp only [add_zero, log_one] at this
    norm_num at this
    linarith

/-- `log (4/3) ≥ 296/1029` (two terms of `2 artanh (1/7)`, `ss_log_ge_cubic`). -/
theorem hh2_log_four_thirds : (296 / 1029 : ℝ) ≤ log (4 / 3) := by
  have := ss_log_ge_cubic (z := (4 / 3 : ℝ)) (by norm_num)
  norm_num at this ⊢
  linarith

/-- **The log majorant** `log y ≤ -296/1029 + t - t²/2 + t³/3`, `t = 4y/3 - 1`, for `y > 0`. -/
theorem hh2_log_le_bound {y : ℝ} (hy : 0 < y) :
    log y ≤ -296 / 1029 + (4 * y / 3 - 1) - (4 * y / 3 - 1) ^ 2 / 2 + (4 * y / 3 - 1) ^ 3 / 3 := by
  have h1 := hh2_log_taylor3 (t := 4 * y / 3 - 1) (by linarith)
  have h2 := hh2_log_four_thirds
  have e : log y = log (1 + (4 * y / 3 - 1)) - log (4 / 3) := by
    rw [← log_div (ne_of_gt (by linarith)) (by norm_num)]
    congr 1
    ring
  rw [e]
  linarith

/-- `log z ≤ (z - 1/z)/2 - (z - 1)³/(6z²)` for `z ≥ 1` (derivative of the difference
`(z - 1)³/(3z³)`). -/
theorem hh2_log_le_cubic_loss {z : ℝ} (hz : 1 ≤ z) :
    log z ≤ (z - 1 / z) / 2 - (z - 1) ^ 3 / (6 * z ^ 2) := by
  have := ss_le_of_deriv
    (f := fun s : ℝ => (s - 1 / s) / 2 - (s - 1) ^ 3 / (6 * s ^ 2) - log s)
    (f' := fun s => (s - 1) ^ 3 / (3 * s ^ 3)) hz (fun s hs => ?_) (fun s hs => by
      have : 1 < s := hs.1
      have : 0 < s - 1 := by linarith
      positivity)
  · have h1 : ((1 : ℝ) - 1 / 1) / 2 - (1 - 1) ^ 3 / (6 * 1 ^ 2) - log 1 = 0 := by norm_num
    linarith
  have hs0 : 0 < s := by linarith [hs.1]
  have h1 : HasDerivAt (fun s : ℝ => (s - 1 / s) / 2) ((1 + 1 / s ^ 2) / 2) s := by
    have hi : HasDerivAt (fun s : ℝ => 1 / s) (-(1 / s ^ 2)) s := by
      have := (hasDerivAt_inv hs0.ne')
      convert this using 1
      · funext t; rw [one_div]
      · rw [one_div]
    have := ((hasDerivAt_id' s).sub hi).div_const 2
    convert this using 1
    ring
  have h2 : HasDerivAt (fun s : ℝ => (s - 1) ^ 3 / (6 * s ^ 2))
      ((3 * (s - 1) ^ 2 * (6 * s ^ 2) - (s - 1) ^ 3 * (12 * s)) / (6 * s ^ 2) ^ 2) s := by
    have hn : HasDerivAt (fun s : ℝ => (s - 1) ^ 3) (3 * (s - 1) ^ 2) s := by
      have h' := (hasDerivAt_id' s).sub_const 1
      have := (h'.mul h').mul h'
      convert this using 1
      · funext t; simp only [Pi.mul_apply, Pi.add_apply, Pi.sub_apply, Pi.pow_apply]; ring1
      · simp only [Pi.mul_apply, Pi.add_apply, Pi.sub_apply, Pi.pow_apply]; ring1
    have hd : HasDerivAt (fun s : ℝ => 6 * s ^ 2) (12 * s) s := by
      have := ((hasDerivAt_id' s).mul (hasDerivAt_id' s)).const_mul 6
      convert this using 1
      · funext t; simp only [Pi.mul_apply, Pi.add_apply, Pi.sub_apply, Pi.pow_apply]; ring1
      · ring1
    exact hn.div hd (by positivity)
  convert (h1.sub h2).sub (Real.hasDerivAt_log hs0.ne') using 1
  field_simp
  ring

/-! ### The face value and duration elimination -/

/-- **The face value.** `hsF` with `ℓ = log(τq/r_A)` and `m = 2 - 7τq/(4r_A)` in terms of
`k = q/r_A`. -/
theorem hh2_hsF_face (x be al u q τ : ℝ) :
    hsF x be al u q τ (log (τ * q / hsRA al be)) (2 - 7 * τ * q / (4 * hsRA al be)) =
      (hsWs x be al u q - 1) * τ + 1 / τ +
        ((u - 1) / hsRA al be + hsRA al be + 1 - q - hsELs x be al u q) +
        log (τ * (q / hsRA al be)) + (2 - 7 * τ * (q / hsRA al be) / 4) * (hsWs x be al u q - 3 / 4) := by
  unfold hsF
  rw [mul_div_assoc τ q]
  have : 7 * τ * q / (4 * hsRA al be) = 7 * τ * (q / hsRA al be) / 4 := by
    rw [mul_div_assoc, mul_div_assoc, div_mul_eq_div_div]
    ring
  rw [this]
  ring

/-- **Duration elimination, outer form** (`OUTER_RATIO_HAND_SIGN` (5)): for `2 ≤ τ ≤ 1/k`,
`G(τ) ≤ max(G(2), G(2) + (1/k - 2)A)`, `A = (1 - 7k/4)(w - 3/4)`. -/
theorem hh2_tau_outer {W c k τ : ℝ} (hk : 0 < k) (h2 : 2 ≤ τ) (hτ : τ * k ≤ 1) :
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

/-- `Aσ - σ³/12 ≤ 8A² + A/18` for `A, σ ≥ 0` (`CENTRAL_RATIO_HAND_SIGN` (11); equality at
`A = 1/144`, `σ = 1/6`). -/
theorem hh2_cubic_loss_poly {A σ : ℝ} (hA : 0 ≤ A) (hσ : 0 ≤ σ) :
    A * σ - σ ^ 3 / 12 ≤ 8 * A ^ 2 + A / 18 := by
  rcases le_total σ (1 / 18) with h | h
  · nlinarith [mul_nonneg hA (sub_nonneg.2 h), pow_nonneg hσ 3]
  · nlinarith [sq_nonneg (A - (σ - 1 / 18) / 16), mul_nonneg (sq_nonneg (σ - 1 / 6))
      (by linarith : (0 : ℝ) ≤ 8 * σ - 1 / 3)]

/-- **Duration elimination, central form** (`CENTRAL_RATIO_HAND_SIGN` (9)-(11)): for
`2 ≤ τ ≤ 1/k`, `G(τ) ≤ max(G(2), G(2) + (8A² + A/18)/k)`, `A = (1 - 7k/4)(w - 3/4)`. -/
theorem hh2_tau_central {W c k τ : ℝ} (hk : 0 < k) (h2 : 2 ≤ τ) (hτ : τ * k ≤ 1) :
    (W - 1) * τ + 1 / τ + c + log (τ * k) + (2 - 7 * τ * k / 4) * (W - 3 / 4) ≤
      max ((W - 1) * 2 + 1 / 2 + c + log (2 * k) + (2 - 7 * 2 * k / 4) * (W - 3 / 4))
        ((W - 1) * 2 + 1 / 2 + c + log (2 * k) + (2 - 7 * 2 * k / 4) * (W - 3 / 4) +
          (8 * ((1 - 7 * k / 4) * (W - 3 / 4)) ^ 2 + (1 - 7 * k / 4) * (W - 3 / 4) / 18) / k) := by
  have hτ0 : 0 < τ := by linarith
  have hlog : log (τ * k) = log (2 * k) + log (τ / 2) := by
    rw [← log_mul (by positivity) (by positivity)]
    congr 1
    field_simp
  have hcl := hh2_log_le_cubic_loss (z := τ / 2) (by linarith)
  have e1 : (τ / 2 - 1 / (τ / 2)) / 2 - (τ / 2 - 1) ^ 3 / (6 * (τ / 2) ^ 2) =
      τ / 4 - 1 / τ - (τ - 2) ^ 3 / (12 * τ ^ 2) := by field_simp; try ring
  rw [e1] at hcl
  set A := (1 - 7 * k / 4) * (W - 3 / 4) with hA
  set σ := k * (τ - 2) with hσ
  have hσ0 : 0 ≤ σ := by rw [hσ]; nlinarith
  -- the cubic loss with `τ ≤ 1/k`
  have hloss : k ^ 2 * (τ - 2) ^ 3 / 12 ≤ (τ - 2) ^ 3 / (12 * τ ^ 2) := by
    rw [div_le_div_iff₀ (by norm_num) (by positivity)]
    have h3 : 0 ≤ (τ - 2) ^ 3 := pow_nonneg (by linarith) 3
    have : (τ * k) ^ 2 ≤ 1 := by nlinarith
    nlinarith [mul_le_mul_of_nonneg_left this h3]
  have key : (W - 1) * τ + 1 / τ + c + log (τ * k) + (2 - 7 * τ * k / 4) * (W - 3 / 4) ≤
      (W - 1) * 2 + 1 / 2 + c + log (2 * k) + (2 - 7 * 2 * k / 4) * (W - 3 / 4) +
        (A * σ - σ ^ 3 / 12) / k := by
    have e2 : (A * σ - σ ^ 3 / 12) / k = (τ - 2) * A - k ^ 2 * (τ - 2) ^ 3 / 12 := by
      rw [hσ]; field_simp
    rw [e2, hlog, hA]
    nlinarith [hcl, hloss]
  rcases le_total 0 A with hA0 | hA0
  · refine le_trans key (le_trans ?_ (le_max_right _ _))
    have := hh2_cubic_loss_poly hA0 hσ0
    have : (A * σ - σ ^ 3 / 12) / k ≤ (8 * A ^ 2 + A / 18) / k :=
      div_le_div_of_nonneg_right this hk.le
    linarith
  · refine le_trans key (le_trans ?_ (le_max_left _ _))
    have : A * σ - σ ^ 3 / 12 ≤ 0 := by nlinarith [pow_nonneg hσ0 3, mul_nonpos_of_nonpos_of_nonneg hA0 hσ0]
    have : (A * σ - σ ^ 3 / 12) / k ≤ 0 := div_nonpos_of_nonpos_of_nonneg this hk.le
    linarith

/-! ### Transport formulas on the two faces -/

/-- The outer face `q = 1/7`: `w_* = (M² - MS + S² + D²u - DN)/(49α⁴)`, `M = 6α² + 1`,
`N = M(S(u - 1) + 1/S) + 2S - 1` (`OUTER_RATIO_HAND_SIGN` (3)). -/
theorem hh2_Ws_outer (x be al u : ℝ) (ha : al ≠ 0) (hS : 1 + x ≠ 0) :
    hsWs x be al u (1 / 7) =
      ((6 * al ^ 2 + 1) ^ 2 - (6 * al ^ 2 + 1) * (1 + x) + (1 + x) ^ 2 + hsDg x be al ^ 2 * u -
        hsDg x be al * ((6 * al ^ 2 + 1) * ((1 + x) * (u - 1) + 1 / (1 + x)) + 2 * (1 + x) - 1)) /
        (49 * al ^ 4) := by
  unfold hsWs hsA1 hsA2 hsE0
  field_simp
  ring

/-- The outer face `q = 1/7`: `E_{L,*} = (2Du - N)/(7α²)`. -/
theorem hh2_ELs_outer (x be al u : ℝ) (ha : al ≠ 0) (hS : 1 + x ≠ 0) :
    hsELs x be al u (1 / 7) =
      (2 * hsDg x be al * u - ((6 * al ^ 2 + 1) * ((1 + x) * (u - 1) + 1 / (1 + x)) + 2 * (1 + x) - 1)) /
        (7 * al ^ 2) := by
  unfold hsELs hsA3 hsE0
  field_simp
  ring

/-- The central face `q = q_c`: `w_* = (S²(S² - S + 1) + D²u - DE)/K²`, `K = x(x + 2) + α²`,
`E = S³(u - 1) + 3S - 1` (`CENTRAL_RATIO_HAND_SIGN` (3)). -/
theorem hh2_Ws_central (x be al u : ℝ) (ha : al ≠ 0) (hS : 1 + x ≠ 0)
    (hK : x * (x + 2) + al ^ 2 ≠ 0) :
    hsWs x be al u (hsQc x al) =
      ((1 + x) ^ 2 * ((1 + x) ^ 2 - (1 + x) + 1) + hsDg x be al ^ 2 * u -
        hsDg x be al * ((1 + x) ^ 3 * (u - 1) + 3 * (1 + x) - 1)) / (x * (x + 2) + al ^ 2) ^ 2 := by
  unfold hsWs hsA1 hsA2 hsE0 hsQc
  field_simp
  ring

/-- The central face `q = q_c`: `E_{L,*} = (2Du - E)/K`. -/
theorem hh2_ELs_central (x be al u : ℝ) (ha : al ≠ 0) (hS : 1 + x ≠ 0)
    (hK : x * (x + 2) + al ^ 2 ≠ 0) :
    hsELs x be al u (hsQc x al) =
      (2 * hsDg x be al * u - ((1 + x) ^ 3 * (u - 1) + 3 * (1 + x) - 1)) / (x * (x + 2) + al ^ 2) := by
  unfold hsELs hsA3 hsE0 hsQc
  field_simp
  ring

/-- Sign transfer from a cleared numerator: `E·d = -P`, `d > 0`, `P > 0` give `E < 0`. -/
theorem hh2_neg_of_mul {E d P : ℝ} (hd : 0 < d) (hP : 0 < P) (h : E * d = -P) : E < 0 := by
  by_contra hE
  have : 0 ≤ E * d := mul_nonneg (not_lt.mp hE) hd.le
  linarith

end SmoothedOctagon
