module

public import SmoothedOctagon.Exclusion.Mixed.CentralScale

/-!
# The scale of a reverse centre

Lowering the incident norms and raising the neighbour ratios gives one Gram
quotient. Its derivative has a positive square remainder after the reciprocal
midpoint comparison for the logarithm.
-/

@[expose] public section
namespace SmoothedOctagon
open Real Set

local syntax "analytic_deriv" : tactic
macro_rules
| `(tactic| analytic_deriv) => `(tactic|
  first
  | assumption
  | exact hasDerivAt_id' _
  | exact hasDerivAt_const _ _
  | apply HasDerivAt.add <;> analytic_deriv
  | apply HasDerivAt.sub <;> analytic_deriv
  | apply HasDerivAt.pow <;> analytic_deriv
  | apply HasDerivAt.mul <;> analytic_deriv
  | apply HasDerivAt.div <;> first | analytic_deriv | positivity | assumption
  | apply HasDerivAt.neg <;> analytic_deriv
  | apply HasDerivAt.log <;> first | analytic_deriv | positivity | assumption)



private theorem ssScale_le_of_deriv {f f' : ℝ → ℝ} {lo hi : ℝ} (hlh : lo ≤ hi)
    (hd : ∀ x ∈ Icc lo hi, HasDerivAt f (f' x) x)
    (hn : ∀ x ∈ Icc lo hi, 0 ≤ f' x) : f lo ≤ f hi := by
  have hm := monotoneOn_of_hasDerivWithinAt_nonneg (convex_Icc lo hi)
    (fun x hx => (hd x hx).continuousAt.continuousWithinAt)
    (fun x hx => (hd x (interior_subset hx)).hasDerivWithinAt)
    (fun x hx => hn x (interior_subset hx))
  exact hm ⟨le_rfl, hlh⟩ ⟨hlh, le_rfl⟩ hlh

private theorem ssScale_log_upper {z : ℝ} (hz : 0 < z) (hz1 : z ≤ 1) :
    Real.log z ≤ 2 * (z - 1) / (z + 1) := by
  have h := ssScale_le_of_deriv (f := fun s => Real.log s - 2 * (s - 1) / (s + 1))
    (f' := fun s => (s - 1) ^ 2 / (s * (s + 1) ^ 2)) hz1 (fun s hs => ?_) (fun s hs => ?_)
  · norm_num at h
    linarith only [h]
  · have hs0 : 0 < s := lt_of_lt_of_le hz hs.1
    have hs1 : 0 < s + 1 := by linarith
    apply HasDerivAt.congr_deriv
    · analytic_deriv
    · norm_num [npowRec]; field_simp; ring
  · have hs0 : 0 < s := lt_of_lt_of_le hz hs.1
    positivity

/-- The symmetric centre pairing at the incident norm floors and ratio ceilings. -/
noncomputable def ss_reversePairing (rho : ℝ) : ℝ := 1 - rho + Real.log (4 * rho)
/-- The symmetric reverse-centre Gram quotient at both norm floors. -/
noncomputable def ss_reverseGram (rho : ℝ) : ℝ := (9 / 4 - ss_reversePairing rho ^ 2) / (16 * (1 - rho) ^ 2)

private theorem ss_reversePairing_pos {rho : ℝ} (hlo : 1 / 7 ≤ rho) (hhi : rho < 1 / 4) : 0 < ss_reversePairing rho := by
  have hr : 0 < rho := by linarith
  have hlog := Real.one_sub_inv_le_log_of_pos (show 0 < 4 * rho by positivity)
  have hrec : (4 * rho)⁻¹ ≤ 7 / 4 := by
    have h : 1 / (4 * rho) ≤ 7 / 4 := by
      rw [div_le_iff₀ (by positivity)]
      nlinarith only [hlo]
    simpa only [one_div] using h
  unfold ss_reversePairing
  linarith only [hlog, hrec, hhi]

private theorem ssScale_gram_deriv {rho : ℝ} (hr : 0 < rho) (hb : 0 < 1 - rho) :
    HasDerivAt ss_reverseGram
      ((9 / 4 - ss_reversePairing rho ^ 2 - ss_reversePairing rho * (1 - rho) ^ 2 / rho) / (8 * (1 - rho) ^ 3)) rho := by
  unfold ss_reverseGram ss_reversePairing
  apply HasDerivAt.congr_deriv
  · analytic_deriv
  · norm_num [npowRec]; field_simp; ring

private theorem ssScale_gram_numerator_nonneg {rho : ℝ} (hlo : 1 / 7 ≤ rho) (hhi : rho < 1 / 4) :
    0 ≤ 9 / 4 - ss_reversePairing rho ^ 2 - ss_reversePairing rho * (1 - rho) ^ 2 / rho := by
  have hr : 0 < rho := by linarith
  have hD : 0 < 4 * rho + 1 := by positivity
  let H := 1 - rho + 2 * (4 * rho - 1) / (4 * rho + 1)
  have hB := ss_reversePairing_pos hlo hhi
  have hBH : ss_reversePairing rho ≤ H := by
    have hl := ssScale_log_upper (show 0 < 4 * rho by positivity) (show 4 * rho ≤ 1 by linarith)
    dsimp [ss_reversePairing, H]
    linarith only [hl]
  have hH : 0 ≤ H := hB.le.trans hBH
  have hs : ss_reversePairing rho ^ 2 ≤ H ^ 2 := by gcongr
  have hp : ss_reversePairing rho * (1 - rho) ^ 2 / rho ≤ H * (1 - rho) ^ 2 / rho := by gcongr
  have he : 9 / 4 - H ^ 2 - H * (1 - rho) ^ 2 / rho =
      (4 * rho - 1) ^ 2 * (4 * rho ^ 2 + rho + 4) / (4 * rho * (4 * rho + 1) ^ 2) := by
    dsimp [H]
    field_simp
    ring
  have hn : 0 ≤ 9 / 4 - H ^ 2 - H * (1 - rho) ^ 2 / rho := by rw [he]; positivity
  linarith only [hs, hp, hn]

/-- The symmetric Gram quotient increases on the entire reverse-centre scale range. -/
theorem ss_reverseGram_mono {rho : ℝ} (hlo : 1 / 7 ≤ rho) (hhi : rho < 1 / 4) :
    ss_reverseGram (1 / 7) ≤ ss_reverseGram rho := by
  refine ssScale_le_of_deriv hlo (fun x hx => ssScale_gram_deriv
    (by linarith [hx.1]) (by linarith [hx.2])) (fun x hx => ?_)
  have hb : 0 < 1 - x := by linarith [hx.2]
  exact div_nonneg (ssScale_gram_numerator_nonneg hx.1 (hx.2.trans_lt hhi)) (by positivity)

private theorem ssScale_gram_seventh : 9193 / 50000 < ss_reverseGram (1 / 7) := by
  have hlog : 33 / 59 < Real.log (7 / 4) := by
    have h := nsr_log_one_add_jensen (x := 3 / 4) (by norm_num)
    norm_num at h ⊢
    exact h
  have hB := ss_reversePairing_pos (rho := 1 / 7) (by norm_num) (by norm_num)
  have he : ss_reversePairing (1 / 7) = 6 / 7 - Real.log (7 / 4) := by
    unfold ss_reversePairing
    rw [show (4 : ℝ) * (1 / 7) = (7 / 4)⁻¹ by norm_num, Real.log_inv]
    ring
  have hBbound : ss_reversePairing (1 / 7) ≤ 6 / 7 - 33 / 59 := by rw [he]; linarith only [hlog]
  have hsq := pow_le_pow_left₀ hB.le hBbound 2
  unfold ss_reverseGram
  rw [lt_div_iff₀ (by norm_num)]
  nlinarith only [hsq]

/-- **`ρ < 1/7` at a reverse centre** (the scalar core of `nsr_a_sq`): if
`0 < r, t < 1/2`, `0 < ρ < rt`, `3/4 ≤ u ≤ U(r)`, `3/4 ≤ v ≤ U(t)`,
`E = 1 + r + t - ρ + log(ρ/(rt)) - (1 - u)/r - (1 - v)/t` and `(4uv - E²)/(16(1 - ρ)²) <
9193/50000`, then `ρ < 1/7`. -/
theorem ss_rev_centre_scale {r t ρ u v E : ℝ} (hr : 0 < r) (hr2 : r < 1 / 2) (ht : 0 < t)
    (ht2 : t < 1 / 2) (hρ : 0 < ρ) (hρrt : ρ < r * t) (hu : 3 / 4 ≤ u)
    (hur : u ≤ m2U r) (hv : 3 / 4 ≤ v) (hvt : v ≤ m2U t)
    (hE : E = 1 + r + t - ρ + log (ρ / (r * t)) - (1 - u) / r - (1 - v) / t)
    (hΓ : (4 * u * v - E ^ 2) / (16 * (1 - ρ) ^ 2) < 9193 / 50000) : ρ < 1 / 7 := by
  have hρ14 : ρ < 1 / 4 := by
    have hrt := mul_lt_mul'' hr2 ht2 hr.le ht.le
    linarith only [hρrt, hrt]
  by_contra hcon
  push Not at hcon
  unfold m2U at hur hvt
  -- the diagonal bound `E < -1 + 2r + 2t - rt`
  have hEb : E < -1 + 2 * r + 2 * t - r * t := by
    have hℓ1 : -ρ + log (ρ / (r * t)) < -(r * t) := by
      set y := ρ / (r * t) with hy
      have hy0 : 0 < y := by positivity
      have hl := Real.log_le_sub_one_of_pos hy0
      have hy1 : y < 1 := (div_lt_one (by positivity)).2 hρrt
      have hrt1 : r * t < 1 := by
        have := mul_lt_mul'' hr2 ht2 hr.le ht.le; linarith only [this]
      have e : ρ = y * (r * t) := by rw [hy]; field_simp
      have e2 : (1 - y) * (1 - r * t) = 1 - r * t - y + ρ := by rw [e]; ring
      have : 0 < (1 - y) * (1 - r * t) :=
        mul_pos (by linarith only [hy1]) (by linarith only [hrt1])
      linarith only [hl, e2, this]
    have hur' : 1 - r ≤ (1 - u) / r := by
      rw [le_div_iff₀ hr]; linarith only [hur, show (1 - r) * r = r - r ^ 2 by ring]
    have hvt' : 1 - t ≤ (1 - v) / t := by
      rw [le_div_iff₀ ht]; linarith only [hvt, show (1 - t) * t = t - t ^ 2 by ring]
    rw [hE]
    linarith only [hℓ1, hur', hvt']
  -- lower the norms to `3/4`
  set E0 := 1 + r + t - ρ + Real.log (ρ / (r * t)) - 1 / 4 * r⁻¹ - 1 / 4 * t⁻¹ with hE0
  have hEE0 : E = E0 + (u - 3 / 4) / r + (v - 3 / 4) / t := by
    rw [hE, hE0]; field_simp; ring
  have hEr : E ≤ 2 * (3 / 4) * r := by
    have : (2 - r) * (t - 1 / 2) < 0 := mul_neg_of_pos_of_neg (by linarith only [hr2])
      (by linarith only [ht2])
    linarith only [hEb, this,
      show (2 - r) * (t - 1 / 2) = -1 + 2 * r + 2 * t - r * t - 3 / 2 * r by ring]
  have hEt : E ≤ 2 * (3 / 4) * t := by
    have : (2 - t) * (r - 1 / 2) < 0 := mul_neg_of_pos_of_neg (by linarith only [ht2])
      (by linarith only [hr2])
    linarith only [hEb, this,
      show (2 - t) * (r - 1 / 2) = -1 + 2 * r + 2 * t - r * t - 3 / 2 * t by ring]
  have hlow := nsr_lower_norms hr ht hu hv hEr hEt hEE0
  have hE0pos : 0 < E0 := by
    have := nsr_E0_lower hr ht hr2 ht2 hρ hρrt hρ14
    have h8 : 1 / (8 * ρ) ≤ 7 / 8 := by rw [div_le_iff₀ (by positivity)]; linarith only [hcon]
    linarith only [this, h8, hcon, hE0]
  -- raise the ratios to `1/2`
  have hE0B : E0 ≤ 1 - ρ + Real.log (4 * ρ) := by
    have h1 := nsr_phi34_mono hr hr2.le
    have h2 := nsr_phi34_mono ht ht2.le
    have hφ : (1 / 2 : ℝ) - 1 / 4 * (1 / 2)⁻¹ - Real.log (1 / 2) = Real.log 2 := by
      rw [one_div, Real.log_inv]; norm_num
    rw [hφ] at h1 h2
    have e1 : E0 = 1 - ρ + Real.log ρ + (r - 1 / 4 * r⁻¹ - Real.log r) +
        (t - 1 / 4 * t⁻¹ - Real.log t) := by
      rw [hE0, Real.log_div hρ.ne' (by positivity), Real.log_mul hr.ne' ht.ne']; ring
    have e2 : Real.log (4 * ρ) = 2 * Real.log 2 + Real.log ρ := by
      rw [Real.log_mul (by norm_num) hρ.ne', show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
      push_cast; ring
    rw [e1, e2]; linarith only [h1, h2]
  have hE0sq : E0 ^ 2 ≤ ss_reversePairing ρ ^ 2 := by
    exact pow_le_pow_left₀ hE0pos.le hE0B 2
  have hden : 0 < 16 * (1 - ρ) ^ 2 := by
    have h : 0 < 1 - ρ := by linarith only [hρ14]
    positivity
  have hGram : ss_reverseGram ρ ≤ (4 * u * v - E ^ 2) / (16 * (1 - ρ) ^ 2) := by
    unfold ss_reverseGram
    apply div_le_div_of_nonneg_right _ hden.le
    linarith only [hlow, hE0sq]
  have hstrict := lt_of_lt_of_le ssScale_gram_seventh (ss_reverseGram_mono hcon hρ14)
  exact (not_lt_of_ge (lt_of_lt_of_le hstrict hGram).le hΓ).elim

end SmoothedOctagon
