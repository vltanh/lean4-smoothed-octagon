module

public import SmoothedOctagon.Exclusion.Mixed.ShortHand.Heavy.S2HandCenBetaCoef
public import SmoothedOctagon.Exclusion.Mixed.ShortHand.Heavy.S2HandCenBetaEdge

/-!
# S2 hand signs: the central beta monotonicity

`archive/lighter-proofs/SHORT_RATIO_CENTRAL_BETA.md`: on `x ≤ b ≤ x + 7(a - 1)/8` (which contains
`x ≤ b ≤ b_+(x, a)`) both duration-tangent tests `F₀`, `F₁` increase in `b`, the incoming ceiling
`u = u_C(x, b)` moving with `b`.

In the partial-fraction forms (`S2HandCenBetaDefs`) the second derivatives are
`G_bb = 6p₃B + 2p₂ + 2a/B³ + 2p_c/(b - 1)³ - 1/B²` and
`H_bb = c₂/2 + 2A₁/B³ + 2P_c/(b - 1)³ - 1/B²` (§3 (9), (12)). With `p₃ ≤ 0`, `p_c > 0`,
`6p₃B_max + 2p₂ > 1/10` and `B³ - 27a²(b - a) = (b - 2a)²(b + 7a)`, `G_bb > 1/10 - 1/27 > 0`
(§3 (11)); with `A₁ > 9/2`, `P_c > -2J`, `0 < J < 1/50`, `B ≤ 161/40`, `b - 1 ≥ 7/6`,
`H_bb ≥ 3/40 - (2/25)(6/7)³ > 0` (§3 (13), with the slightly weaker rational `3/40`). So both first
derivatives are smallest at `b = x`, where they are positive (`S2HandCenBetaEdge`). Finally
`(F₀)_b = G_b` and `(F₁)_b = H_b - Kφ/(aB²) ≥ H_b` with `φ = (t - 1)/t² - 1/4 ≤ 0` (§6 (23)).

Route: the base-face step uses the exact derivatives at `b = x` (`S2HandCenBetaEdge`) instead of
the lower comparison and factored numerators of §4-§5.

## Main API

* `hl2cb_G2`, `hl2cb_H2`: the second derivatives are nonnegative.
* `hl2cb_mono`: monotonicity from a lower derivative that increases from a nonnegative value.
* `hl2c_beta`: both tests increase in `b` on `x ≤ b ≤ b_+(x, a)`.
-/

@[expose] public section

namespace SmoothedOctagon

open Real Set

/-- `B³ ≥ 27(b - a)` for `1 ≤ a ≤ b` (`B³ - 27a²(b - a) = (b - 2a)²(b + 7a)`). -/
theorem hl2cb_cube {a s : ℝ} (ha : 1 ≤ a) (hs : a ≤ s) : 27 * (s - a) ≤ (a + s) ^ 3 := by
  have e : (a + s) ^ 3 - 27 * a ^ 2 * (s - a) = (s - 2 * a) ^ 2 * (s + 7 * a) := by ring
  have h1 : 0 ≤ (s - 2 * a) ^ 2 * (s + 7 * a) := mul_nonneg (sq_nonneg _) (by linarith)
  have h2 : 27 * (s - a) ≤ 27 * a ^ 2 * (s - a) := by
    have : 1 ≤ a ^ 2 := by nlinarith
    nlinarith
  linarith

/-- **`G_bb > 0`** (`SHORT_RATIO_CENTRAL_BETA` (9)-(11)). -/
theorem hl2cb_G2 {x a s : ℝ} (hx : 13 / 6 ≤ x) (hx2 : x ≤ 12 / 5) (ha : 1 ≤ a) (ha2 : a ≤ 4 / 3)
    (hs : x ≤ s) (hs' : s ≤ x + 7 * (a - 1) / 8) :
    0 ≤ 6 * hl2cbp3 x a * (a + s) + 2 * hl2cbp2 x a + 2 * a / (a + s) ^ 3 +
      2 * hl2cbpc x a / (s - 1) ^ 3 - 1 / (a + s) ^ 2 := by
  have hK := hl2cb_K_pos (a := a) (by linarith : (0 : ℝ) < x)
  have hB : 0 < a + s := by linarith
  have hs1 : 0 < s - 1 := by linarith
  have hpc := hl2cb_pc_pos hx hx2 ha ha2
  have hcurv := hl2cb_curv hx hx2 ha ha2
  have hp3 : hl2cbp3 x a ≤ 0 := by
    unfold hl2cbp3 hl2cbl hl2cbc2
    have : 0 ≤ 7 * a / (2 * hl2cK x a) * (2401 / 3200 * hl2cbd x a ^ 2 / hl2cK x a ^ 2) := by
      apply mul_nonneg <;> positivity
    linarith
  have h1 : 6 * hl2cbp3 x a * (a + x + 7 * (a - 1) / 8) ≤ 6 * hl2cbp3 x a * (a + s) :=
    mul_le_mul_of_nonpos_left (by linarith) (by linarith)
  have h2 : 0 ≤ 2 * hl2cbpc x a / (s - 1) ^ 3 := by positivity
  have h3 : -(1 / 27) ≤ 2 * a / (a + s) ^ 3 - 1 / (a + s) ^ 2 := by
    have e : 2 * a / (a + s) ^ 3 - 1 / (a + s) ^ 2 = -((s - a) / (a + s) ^ 3) := by
      field_simp
      ring
    rw [e, neg_le_neg_iff, div_le_iff₀ (by positivity)]
    have := hl2cb_cube ha (by linarith : a ≤ s)
    linarith
  linarith

/-- `(9 - B)/B³ ≥ 3/40` for `0 < B ≤ 161/40`. -/
theorem hl2cb_nine {B : ℝ} (hB : 0 < B) (hB' : B ≤ 161 / 40) : 3 / 40 ≤ (9 - B) / B ^ 3 := by
  rw [le_div_iff₀ (by positivity)]
  have : B ^ 3 ≤ (161 / 40) ^ 3 := pow_le_pow_left₀ hB.le hB' 3
  nlinarith

/-- **`H_bb > 0`** (`SHORT_RATIO_CENTRAL_BETA` (12)-(13)). -/
theorem hl2cb_H2 {x a s : ℝ} (hx : 13 / 6 ≤ x) (hx2 : x ≤ 12 / 5) (ha : 1 ≤ a) (ha2 : a ≤ 4 / 3)
    (hs : x ≤ s) (hs' : s ≤ x + 7 * (a - 1) / 8) :
    0 ≤ 6 * 0 * (a + s) + 2 * (hl2cbc2 x a / 4) + 2 * hl2cbA1 x a / (a + s) ^ 3 +
      2 * hl2cbPc x a / (s - 1) ^ 3 - 1 / (a + s) ^ 2 := by
  have hK := hl2cb_K_pos (a := a) (by linarith : (0 : ℝ) < x)
  have hB : 0 < a + s := by linarith
  have hs1 : 7 / 6 ≤ s - 1 := by linarith
  have hA := hl2cb_A1 hx hx2 ha ha2
  have hP := hl2cb_Pc hx hx2 ha ha2
  have hJ := hl2cb_J_pos hx hx2
  have hJ' := hl2cb_J_lt hx hx2
  have hc2 : 0 ≤ hl2cbc2 x a := by unfold hl2cbc2; positivity
  have h1 : 3 / 40 ≤ 2 * hl2cbA1 x a / (a + s) ^ 3 - 1 / (a + s) ^ 2 := by
    have e : 2 * hl2cbA1 x a / (a + s) ^ 3 - 1 / (a + s) ^ 2 =
        (2 * hl2cbA1 x a - (a + s)) / (a + s) ^ 3 := by
      field_simp
    rw [e]
    refine le_trans (hl2cb_nine hB (by linarith)) ?_
    apply div_le_div_of_nonneg_right (by linarith) (by positivity)
  have h2 : -(432 / 8575) ≤ 2 * hl2cbPc x a / (s - 1) ^ 3 := by
    have hc : (7 / 6) ^ 3 ≤ (s - 1) ^ 3 := pow_le_pow_left₀ (by norm_num) hs1 3
    have hc0 : 0 < (s - 1) ^ 3 := by positivity
    rw [le_div_iff₀ hc0]
    nlinarith
  linarith

/-- **Monotonicity from an increasing lower derivative**: if `g ≤ f'` on `[lo, hi]`, `g' ≥ 0` there
and `g(lo) ≥ 0`, then `f` increases on `[lo, hi]`. -/
theorem hl2cb_mono {f f' g g' : ℝ → ℝ} {lo hi b b' : ℝ} (hlo : lo ≤ b) (hbb : b ≤ b')
    (hhi : b' ≤ hi) (hf : ∀ s ∈ Icc lo hi, HasDerivAt f (f' s) s)
    (hge : ∀ s ∈ Icc lo hi, g s ≤ f' s) (hg : ∀ s ∈ Icc lo hi, HasDerivAt g (g' s) s)
    (hg2 : ∀ s ∈ Icc lo hi, 0 ≤ g' s) (h0 : 0 ≤ g lo) : f b ≤ f b' := by
  refine ss_le_of_deriv hbb (fun z hz => hf z ⟨hlo.trans hz.1, hz.2.trans hhi⟩) (fun z hz => ?_)
  have hz : z ∈ Icc lo hi := ⟨hlo.trans hz.1.le, hz.2.le.trans hhi⟩
  have : g lo ≤ g z := ss_le_of_deriv hz.1 (fun w hw => hg w ⟨hw.1, hw.2.trans hz.2⟩)
    (fun w hw => hg2 w ⟨hw.1.le, hw.2.le.trans hz.2⟩)
  linarith [hge z hz]

/-- **The central beta monotonicity** (`SHORT_RATIO_CENTRAL_BETA` §6): both duration-tangent tests
increase in `b` on `x ≤ b ≤ b_+(x, a)`, the incoming ceiling moving with `b`. -/
theorem hl2c_beta {t x a b b' : ℝ} (hx : 13 / 6 ≤ x) (hx2 : x ≤ 12 / 5) (ha : 1 ≤ a)
    (ha2 : a ≤ 4 / 3) (ht : 2 ≤ t) (hb : x ≤ b) (hbb : b ≤ b') (hb' : b' ≤ hl2cbp x a) :
    hl2cF0 t x a b (hsUC x b) ≤ hl2cF0 t x a b' (hsUC x b') ∧
      hl2cF1 t x a b (hsUC x b) ≤ hl2cF1 t x a b' (hsUC x b') := by
  have ht0 : 0 < t := by linarith
  have hx0 : 0 < x := by linarith
  have ha0 : 0 < a := by linarith
  have hK := hl2cb_K_pos (a := a) hx0
  have hhi : b' ≤ x + 7 * (a - 1) / 8 := by
    have : hl2cbp x a ≤ x + 7 * (a - 1) / 8 := by
      unfold hl2cbp
      have : (24 * x + 51) * (a - 1) ≤ 112 * (a - 1) :=
        mul_le_mul_of_nonneg_right (by linarith) (by linarith)
      linarith
    linarith
  have hS : ∀ s ∈ Icc x (x + 7 * (a - 1) / 8), 0 < a + s ∧ s - 1 ≠ 0 := fun s hs =>
    ⟨by linarith [hs.1], by linarith [hs.1]⟩
  have hb1 : 1 < b := by linarith
  have hb1' : 1 < b' := by linarith
  constructor
  · rw [hl2cb_F0_pf ht0 hx0 ha0 hb1, hl2cb_F0_pf ht0 hx0 ha0 hb1']
    have := hl2cb_mono (g := hl2cbG1 x a) hb hbb hhi
      (fun s hs => hl2cb_hd (α3 := hl2cbp3 x a) (α2 := hl2cbp2 x a) (α1 := hl2cbp1 x a) (β := a)
        (γ := hl2cbpc x a) (hS s hs).1 (hS s hs).2)
      (fun s _ => le_refl _)
      (fun s hs => hl2cb_hd2 (α3 := hl2cbp3 x a) (α2 := hl2cbp2 x a) (α1 := hl2cbp1 x a) (β := a)
        (γ := hl2cbpc x a) (hS s hs).1 (hS s hs).2)
      (fun s hs => hl2cb_G2 hx hx2 ha ha2 hs.1 hs.2) (hl2cb_G1_base hx hx2 ha ha2).le
    linarith
  · rw [hl2cb_F1_pf ht0 hx0 ha0 hb1, hl2cb_F1_pf ht0 hx0 ha0 hb1']
    have hφ : hl2cK x a * ((t - 1) / t ^ 2 - 1 / 4) / a ≤ 0 := by
      have e : (t - 1) / t ^ 2 - 1 / 4 = -((t - 2) ^ 2 / (4 * t ^ 2)) := by
        field_simp
        ring
      rw [e]
      have : 0 ≤ (t - 2) ^ 2 / (4 * t ^ 2) := by positivity
      apply div_nonpos_of_nonpos_of_nonneg _ ha0.le
      nlinarith
    have := hl2cb_mono (g := hl2cbH1 x a) hb hbb hhi
      (fun s hs => hl2cb_hd (α3 := 0) (α2 := hl2cbc2 x a / 4) (α1 := hl2cbq1 x a)
        (β := hl2cbA1 x a + hl2cK x a * ((t - 1) / t ^ 2 - 1 / 4) / a)
        (γ := hl2cbPc x a) (hS s hs).1 (hS s hs).2)
      (fun s hs => by
        unfold hl2cbH1
        have hB := (hS s hs).1
        have : hl2cK x a * ((t - 1) / t ^ 2 - 1 / 4) / a / (a + s) ^ 2 ≤ 0 :=
          div_nonpos_of_nonpos_of_nonneg hφ (by positivity)
        rw [add_div] at *
        linarith)
      (fun s hs => hl2cb_hd2 (α3 := 0) (α2 := hl2cbc2 x a / 4) (α1 := hl2cbq1 x a)
        (β := hl2cbA1 x a) (γ := hl2cbPc x a) (hS s hs).1 (hS s hs).2)
      (fun s hs => hl2cb_H2 hx hx2 ha ha2 hs.1 hs.2) (hl2cb_H1_base hx hx2 ha ha2).le
    simp only [zero_mul, zero_add] at this
    linarith

end SmoothedOctagon
