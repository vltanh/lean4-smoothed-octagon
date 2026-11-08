module

public import SmoothedOctagon.Exclusion.Mixed.ShortHand.Heavy.S2HandCenTermPoly

/-!
# S2 hand signs: the central terminal signs

`archive/lighter-proofs/SHORT_RATIO_CENTRAL_TERMINALS.md`: at the terminal curve `x = 13/6`,
`β = b_+(13/6, a) = (309a + 523)/384`, `1 ≤ a ≤ 4/3`, with the original incoming norm
`u = hsUC(13/6, β)` and the tangent point `t = max(2, 20/3 - 4a)` of
`SHORT_RATIO_CENTRAL_COMPLETE` (6), both duration-tangent tests `F₀`, `F₁` are negative.

The logarithm is raised to the quadratic `Q` of (8) (`log(4/5) ≤ -488/2187` from two terms of
`2 artanh(1/9)`; the difference `log y - [Q(y) + 488/2187 + log(4/5)]` has derivative
`(y - 4/5)(y - 5/4)/y`, so `log y ≤ Q(y)` on `0 < y ≤ 5/4`, which contains `y = tk` by (6)-(7)).
The resulting rational functions of `a` are written exactly as `N/(c·Den)` with `Den > 0`, and the
numerators `N` are negative by `S2HandCenTermPoly`.

Route: the notes' affine norm chords (5) (with the `u`-monotonicity of the tests) and the
eighth-order Taylor polynomials with the power-series tail bound (9)-(22) are replaced by keeping
the exact incoming norm, clearing denominators exactly (`R`, `h`, `k` first, each verified by
`field_simp; ring`), and signing the four numerators (degree 13, 11, 9, 7) by the termwise rule
with absorption in a shifted variable (one split, at `a = 9/8`, for `N_{L0}`; square completion
for `N_{L1}`). Only strict negativity is proved, not the margin `-1/6000` of (2).

## Main API

* `hl2ctQ`, `hl2ct_log_le`: the quadratic logarithm bound.
* `hl2ct_u`, `hl2ct_k`, `hl2ct_R`, `hl2ct_h`: the components on the terminal curve.
* `hl2ct_fL0`, `hl2ct_fL1`, `hl2ct_fH0`, `hl2ct_fH1`: the cleared forms of the four tests.
* `hl2c_term`: the four terminal signs.
-/

@[expose] public section

namespace SmoothedOctagon

open Real

/-- The cleared numerator of `R` at the terminal curve: `R = N_R/(1330790400·a·G·B̃·K̃)`,
`G = 309a + 139`, `B̃ = 693a + 523`, `K̃ = 36a² + 325`. -/
noncomputable def hl2ctNR (a : ℝ) : ℝ :=
  -39109139958167316 * a ^ 5 - 43612691456899836 * a ^ 4 + 111598587182138247 * a ^ 3 +
    80391565724393691 * a ^ 2 - 8865552867585271 * a - 9408573805872475

/-- The cleared numerator of `h = w - 3/4` at the terminal curve:
`h = N_h/(10646323200·GK̃²)`. -/
noncomputable def hl2ctNh (a : ℝ) : ℝ :=
  18583422609446676 * a ^ 5 - 3987170728505064 * a ^ 4 - 77678538804803259 * a ^ 3 -
    32529602748928311 * a ^ 2 + 81426588498399963 * a + 36098659585101035

/-- `b_+(13/6, a) = (309a + 523)/384` (`SHORT_RATIO_CENTRAL_TERMINALS` (1)). -/
theorem hl2ct_b (a : ℝ) : hl2cbp (13 / 6) a = (309 * a + 523) / 384 := by
  unfold hl2cbp; ring

/-- The incoming ceiling on the terminal curve (`SHORT_RATIO_CENTRAL_TERMINALS` (3):
`u_g = 2401/3200 + 225659/(54150(309a + 139))`). -/
theorem hl2ct_u {a : ℝ} (ha : 0 < a) : hsUC (13 / 6) ((309 * a + 523) / 384) =
    7 * (114783921 * a + 53697359) / (3465600 * (309 * a + 139)) := by
  unfold hsUC
  have h1 : (309 * a + 139) ≠ 0 := by positivity
  have h2 : (309 * a + 523) / 384 - 1 = (309 * a + 139) / 384 := by ring
  rw [h2]
  field_simp
  ring

/-- `k = aB/K = 3a(693a + 523)/(32(36a² + 325))` on the terminal curve. -/
theorem hl2ct_k {a : ℝ} (ha : 0 < a) : hl2ck (13 / 6) a ((309 * a + 523) / 384) =
    3 * a * (693 * a + 523) / (32 * (36 * a ^ 2 + 325)) := by
  unfold hl2ck hl2cK
  have : 36 * a ^ 2 + 325 ≠ 0 := by positivity
  field_simp
  ring

/-- `R` on the terminal curve with the original incoming norm. -/
theorem hl2ct_R {a : ℝ} (ha : 0 < a) :
    hl2cR (13 / 6) a ((309 * a + 523) / 384)
        (7 * (114783921 * a + 53697359) / (3465600 * (309 * a + 139))) =
      hl2ctNR a / (1330790400 * (a * (309 * a + 139) * (693 * a + 523) * (36 * a ^ 2 + 325))) := by
  have hK : hl2cK (13 / 6) a = (36 * a ^ 2 + 325) / 36 := by unfold hl2cK; ring
  have hB : a + (309 * a + 523) / 384 = (693 * a + 523) / 384 := by ring
  have hD : hsDg (13 / 6) ((309 * a + 523) / 384) a = (3006 * a ^ 2 - 879 * a - 655) / 1152 := by
    unfold hsDg; ring
  unfold hl2cR hl2cEL
  rw [hK, hB, hD]
  have h1 : (309 * a + 139) ≠ 0 := by positivity
  have h2 : (693 * a + 523) ≠ 0 := by positivity
  have h3 : 36 * a ^ 2 + 325 ≠ 0 := by positivity
  unfold hl2ctNR
  field_simp
  ring

/-- `h = w - 3/4` on the terminal curve with the original incoming norm. -/
theorem hl2ct_h {a : ℝ} (ha : 0 < a) :
    hl2cw (13 / 6) a ((309 * a + 523) / 384)
        (7 * (114783921 * a + 53697359) / (3465600 * (309 * a + 139))) - 3 / 4 =
      hl2ctNh a / (10646323200 * ((309 * a + 139) * (36 * a ^ 2 + 325) ^ 2)) := by
  have hK : hl2cK (13 / 6) a = (36 * a ^ 2 + 325) / 36 := by unfold hl2cK; ring
  have hD : hsDg (13 / 6) ((309 * a + 523) / 384) a = (3006 * a ^ 2 - 879 * a - 655) / 1152 := by
    unfold hsDg; ring
  unfold hl2cw
  rw [hK, hD]
  have h1 : (309 * a + 139) ≠ 0 := by positivity
  have h3 : 36 * a ^ 2 + 325 ≠ 0 := by positivity
  unfold hl2ctNh
  field_simp
  ring


/-- The quadratic logarithm majorant `Q(y) = -488/2187 + 5/4(y - 4/5) - (y - 4/5)²/2`
(`SHORT_RATIO_CENTRAL_TERMINALS` (8)). -/
noncomputable def hl2ctQ (y : ℝ) : ℝ :=
  -(488 / 2187) + 5 / 4 * (y - 4 / 5) - (y - 4 / 5) ^ 2 / 2

/-- The first test on the lower interval (`t = 20/3 - 4a`), with `log` replaced by `Q`, is
`N_{L0}/(c·Den)`. -/
theorem hl2ct_fL0 {a t : ℝ} (ha : 0 < a) (ht0 : 0 < t) (ht : t = 20 / 3 - 4 * a) :
    hl2ctNR a / (1330790400 * (a * (309 * a + 139) * (693 * a + 523) * (36 * a ^ 2 + 325))) +
        (4 - 7 * (3 * a * (693 * a + 523) / (32 * (36 * a ^ 2 + 325))) / 2) *
          (hl2ctNh a / (10646323200 * ((309 * a + 139) * (36 * a ^ 2 + 325) ^ 2))) +
        4 / t - 2 / t ^ 2 - 3 / 2 +
        hl2ctQ (t * (3 * a * (693 * a + 523) / (32 * (36 * a ^ 2 + 325)))) =
      hl2ctNL0 a / (93134035353600 * (a * (693 * a + 523) * (36 * a ^ 2 + 325) ^ 3 * t ^ 2 *
        (309 * a + 139))) := by
  have h1 : (309 * a + 139) ≠ 0 := by positivity
  have h2 : (693 * a + 523) ≠ 0 := by positivity
  have h3 : 36 * a ^ 2 + 325 ≠ 0 := by positivity
  have h4 : t ≠ 0 := ht0.ne'
  unfold hl2ctQ hl2ctNR hl2ctNh hl2ctNL0
  field_simp
  subst ht
  ring

/-- The second test on the lower interval, with `log` replaced by `Q`. -/
theorem hl2ct_fL1 {a t : ℝ} (ha : 0 < a) (ht0 : 0 < t) (ht : t = 20 / 3 - 4 * a) :
    hl2ctNR a / (1330790400 * (a * (309 * a + 139) * (693 * a + 523) * (36 * a ^ 2 + 325))) +
        (1 / (3 * a * (693 * a + 523) / (32 * (36 * a ^ 2 + 325))) + 1 / 4) *
          (hl2ctNh a / (10646323200 * ((309 * a + 139) * (36 * a ^ 2 + 325) ^ 2))) +
        1 / (3 * a * (693 * a + 523) / (32 * (36 * a ^ 2 + 325))) * ((t - 1) / t ^ 2 - 1 / 4) +
        2 / t - 1 + hl2ctQ (t * (3 * a * (693 * a + 523) / (32 * (36 * a ^ 2 + 325)))) =
      hl2ctNL1 a / (5820877209600 * (a * (693 * a + 523) * (36 * a ^ 2 + 325) ^ 2 * t ^ 2 *
        (309 * a + 139))) := by
  have h1 : (309 * a + 139) ≠ 0 := by positivity
  have h2 : (693 * a + 523) ≠ 0 := by positivity
  have h3 : 36 * a ^ 2 + 325 ≠ 0 := by positivity
  have h4 : t ≠ 0 := ht0.ne'
  unfold hl2ctQ hl2ctNR hl2ctNh hl2ctNL1
  field_simp
  subst ht
  ring

/-- The first test on the upper interval (`t = 2`), with `log` replaced by `Q`. -/
theorem hl2ct_fH0 {a t : ℝ} (ha : 0 < a) (ht : t = 2) :
    hl2ctNR a / (1330790400 * (a * (309 * a + 139) * (693 * a + 523) * (36 * a ^ 2 + 325))) +
        (4 - 7 * (3 * a * (693 * a + 523) / (32 * (36 * a ^ 2 + 325))) / 2) *
          (hl2ctNh a / (10646323200 * ((309 * a + 139) * (36 * a ^ 2 + 325) ^ 2))) +
        4 / t - 2 / t ^ 2 - 3 / 2 +
        hl2ctQ (t * (3 * a * (693 * a + 523) / (32 * (36 * a ^ 2 + 325)))) =
      hl2ctNH0 a / (165571618406400 * (a * (693 * a + 523) * (36 * a ^ 2 + 325) ^ 3 *
        (309 * a + 139))) := by
  have h1 : (309 * a + 139) ≠ 0 := by positivity
  have h2 : (693 * a + 523) ≠ 0 := by positivity
  have h3 : 36 * a ^ 2 + 325 ≠ 0 := by positivity
  subst ht
  unfold hl2ctQ hl2ctNR hl2ctNh hl2ctNH0
  field_simp
  ring

/-- The second test on the upper interval, with `log` replaced by `Q`. -/
theorem hl2ct_fH1 {a t : ℝ} (ha : 0 < a) (ht : t = 2) :
    hl2ctNR a / (1330790400 * (a * (309 * a + 139) * (693 * a + 523) * (36 * a ^ 2 + 325))) +
        (1 / (3 * a * (693 * a + 523) / (32 * (36 * a ^ 2 + 325))) + 1 / 4) *
          (hl2ctNh a / (10646323200 * ((309 * a + 139) * (36 * a ^ 2 + 325) ^ 2))) +
        1 / (3 * a * (693 * a + 523) / (32 * (36 * a ^ 2 + 325))) * ((t - 1) / t ^ 2 - 1 / 4) +
        2 / t - 1 + hl2ctQ (t * (3 * a * (693 * a + 523) / (32 * (36 * a ^ 2 + 325)))) =
      hl2ctNH1 a / (10348226150400 * (a * (693 * a + 523) * (36 * a ^ 2 + 325) ^ 2 *
        (309 * a + 139))) := by
  have h1 : (309 * a + 139) ≠ 0 := by positivity
  have h2 : (693 * a + 523) ≠ 0 := by positivity
  have h3 : 36 * a ^ 2 + 325 ≠ 0 := by positivity
  subst ht
  unfold hl2ctQ hl2ctNR hl2ctNh hl2ctNH1
  field_simp
  ring

/-- `log(4/5) ≤ -488/2187`: two terms of `2 artanh(1/9) = log(5/4)`. -/
theorem hl2ct_log45 : log (4 / 5) ≤ -(488 / 2187) := by
  have h := ss_log_ge_cubic (z := 5 / 4) (by norm_num)
  have e : log (4 / 5) = -log (5 / 4) := by
    rw [show (4 / 5 : ℝ) = (5 / 4)⁻¹ by norm_num, log_inv]
  norm_num at h
  linarith

/-- `log y ≤ Q(y)` for `0 < y ≤ 5/4` (`SHORT_RATIO_CENTRAL_TERMINALS` (8)): the difference
`g(y) = log y - 5/4(y - 4/5) + (y - 4/5)²/2` has `g' = (y - 4/5)(y - 5/4)/y`, so it is largest at
`y = 4/5`. -/
theorem hl2ct_log_le {y : ℝ} (hy : 0 < y) (hy1 : y ≤ 5 / 4) : log y ≤ hl2ctQ y := by
  have hd : ∀ s : ℝ, 0 < s → HasDerivAt
      (fun s : ℝ => log s - (5 / 4 * (s - 4 / 5) - (s - 4 / 5) ^ 2 / 2))
      ((s - 4 / 5) * (s - 5 / 4) / s) s := by
    intro s hs
    have h1 := (hasDerivAt_id' s).sub_const (4 / 5)
    have hp := (h1.const_mul (5 / 4)).sub ((h1.pow 2).div_const 2)
    convert (Real.hasDerivAt_log hs.ne').sub hp using 1
    field_simp
    ring
  have key : log y - (5 / 4 * (y - 4 / 5) - (y - 4 / 5) ^ 2 / 2) ≤ log (4 / 5) := by
    rcases le_total y (4 / 5) with h | h
    · have := ss_le_of_deriv (f := fun s : ℝ => log s - (5 / 4 * (s - 4 / 5) - (s - 4 / 5) ^ 2 / 2))
        (f' := fun s => (s - 4 / 5) * (s - 5 / 4) / s) h (fun s hs => hd s (by linarith [hs.1]))
        (fun s hs => by
          have h0 : 0 < s := by linarith [hs.1]
          apply div_nonneg _ h0.le
          nlinarith [hs.2])
      norm_num at this
      linarith
    · have := ss_le_of_deriv
        (f := fun s : ℝ => -(log s - (5 / 4 * (s - 4 / 5) - (s - 4 / 5) ^ 2 / 2)))
        (f' := fun s => -((s - 4 / 5) * (s - 5 / 4) / s)) h
        (fun s hs => (hd s (by linarith [hs.1])).neg)
        (fun s hs => by
          have h0 : 0 < s := by linarith [hs.1]
          have : (s - 4 / 5) * (s - 5 / 4) / s ≤ 0 :=
            div_nonpos_of_nonpos_of_nonneg (by nlinarith [hs.1, hs.2]) h0.le
          linarith)
      norm_num at this
      linarith
  have := hl2ct_log45
  unfold hl2ctQ
  linarith

/-- `0 < tk ≤ 5/4` at the tangent point `t = max(2, 20/3 - 4a)`. -/
theorem hl2ct_y {a : ℝ} (ha : 1 ≤ a) (ha2 : a ≤ 4 / 3) :
    0 < max 2 (20 / 3 - 4 * a) * (3 * a * (693 * a + 523) / (32 * (36 * a ^ 2 + 325))) ∧
      max 2 (20 / 3 - 4 * a) * (3 * a * (693 * a + 523) / (32 * (36 * a ^ 2 + 325))) ≤ 5 / 4 := by
  have ha0 : 0 < a := by linarith
  have ht : 0 < max 2 (20 / 3 - 4 * a) := lt_of_lt_of_le two_pos (le_max_left _ _)
  refine ⟨mul_pos ht (by positivity), ?_⟩
  rw [← mul_div_assoc, div_le_iff₀ (by positivity)]
  have hc := sub_nonneg.2 ha
  rcases le_total a (7 / 6) with h | h
  · rw [max_eq_right (by linarith)]
    nlinarith [mul_nonneg hc hc, mul_nonneg (mul_nonneg hc hc) hc]
  · rw [max_eq_left (by linarith)]
    nlinarith [mul_nonneg (sub_nonneg.2 ha2) ha0.le]

/-- **The four terminal signs** (`SHORT_RATIO_CENTRAL_TERMINALS` (2), strict negativity): at
`x = 13/6`, `β = b_+(13/6, a)`, the original incoming norm and the tangent point
`t = max(2, 20/3 - 4a)`, both duration-tangent tests are negative for `1 ≤ a ≤ 4/3`. -/
theorem hl2c_term {a : ℝ} (ha : 1 ≤ a) (ha2 : a ≤ 4 / 3) :
    hl2cF0 (max 2 (20 / 3 - 4 * a)) (13 / 6) a (hl2cbp (13 / 6) a)
        (hsUC (13 / 6) (hl2cbp (13 / 6) a)) < 0 ∧
      hl2cF1 (max 2 (20 / 3 - 4 * a)) (13 / 6) a (hl2cbp (13 / 6) a)
        (hsUC (13 / 6) (hl2cbp (13 / 6) a)) < 0 := by
  have ha0 : 0 < a := by linarith
  have hB : 0 < a * (693 * a + 523) := by positivity
  have hG : 0 < 309 * a + 139 := by linarith
  have hK : 0 < 36 * a ^ 2 + 325 := by positivity
  have ht0 : 0 < max 2 (20 / 3 - 4 * a) := lt_of_lt_of_le two_pos (le_max_left _ _)
  obtain ⟨hy0, hy1⟩ := hl2ct_y ha ha2
  have hlog := hl2ct_log_le hy0 hy1
  unfold hl2cF0 hl2cF1
  rw [hl2ct_b, hl2ct_u ha0, hl2ct_R ha0, hl2ct_h ha0, hl2ct_k ha0]
  rcases le_total a (7 / 6) with h | h
  · have ht : max 2 (20 / 3 - 4 * a) = 20 / 3 - 4 * a := max_eq_right (by linarith)
    have e0 := hl2ct_fL0 ha0 ht0 ht
    have e1 := hl2ct_fL1 ha0 ht0 ht
    have d0 := div_neg_of_neg_of_pos (hl2ct_NL0_neg ha h)
      (mul_pos (by norm_num : (0 : ℝ) < 93134035353600)
        (mul_pos (mul_pos (mul_pos hB (pow_pos hK 3)) (pow_pos ht0 2)) hG))
    have d1 := div_neg_of_neg_of_pos (hl2ct_NL1_neg ha h)
      (mul_pos (by norm_num : (0 : ℝ) < 5820877209600)
        (mul_pos (mul_pos (mul_pos hB (pow_pos hK 2)) (pow_pos ht0 2)) hG))
    constructor <;> linarith
  · have ht : max 2 (20 / 3 - 4 * a) = 2 := max_eq_left (by linarith)
    have e0 := hl2ct_fH0 ha0 ht
    have e1 := hl2ct_fH1 ha0 ht
    have d0 := div_neg_of_neg_of_pos (hl2ct_NH0_neg h ha2)
      (mul_pos (by norm_num : (0 : ℝ) < 165571618406400) (mul_pos (mul_pos hB (pow_pos hK 3)) hG))
    have d1 := div_neg_of_neg_of_pos (hl2ct_NH1_neg h ha2)
      (mul_pos (by norm_num : (0 : ℝ) < 10348226150400) (mul_pos (mul_pos hB (pow_pos hK 2)) hG))
    constructor <;> linarith

end SmoothedOctagon
