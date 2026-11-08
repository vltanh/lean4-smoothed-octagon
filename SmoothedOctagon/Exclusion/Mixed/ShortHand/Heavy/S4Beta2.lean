module

public import SmoothedOctagon.Exclusion.Mixed.ShortHand.Heavy.S4Beta

/-!
# Heavy leaf `hs4_floor_box`: the `β`-step at fixed `u` and the `u`-step

See `S4Beta` for the route. Main API: `hh46_s4_phi_bstep`, `hh46_s4_psi_bstep`,
`hh46_s4_phi_ustep`, `hh46_s4_psi_ustep`, `hh46_s4_beta_mono`.
-/

@[expose] public section

namespace SmoothedOctagon

open Real

/-- Elementary sign facts on the box. -/
theorem hh46_s4_signs {x al b u : ℝ} (hx : 2 ≤ x) (hx2 : x ≤ 13 / 6) (hal : 1 ≤ al)
    (hal2 : al ≤ 22 / 19) (hb : x ≤ b) (hb2 : b ≤ 20 / 19 * x) (_hu : 757 / 1000 ≤ u)
    (hu2 : u ≤ 19 / 25) :
    1 ≤ hsDg x b al ∧ hsDg x b al ≤ hsDg x x al ∧ 127 / 100 ≤ hsDg x x al ∧
      hh46S4P x u ≤ 38 / 25 ∧ 2 * al * (al + b) ≤ x * (x + 2) + al ^ 2 := by
  unfold hsDg hh46S4P
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · have h1 : 2 * b * (al - x) ≥ 2 * (20 / 19 * x) * (al - x) := by nlinarith
    have h2 : al ^ 2 + 1 + 2 * x + 2 * (20 / 19 * x) * (al - x) ≥ 2 + 2 * x - 40 / 19 * x * (x - 1) := by
      nlinarith
    nlinarith [mul_nonneg (by linarith : (0:ℝ) ≤ x - 2) (by linarith : (0:ℝ) ≤ 13 / 6 - x)]
  · nlinarith
  · nlinarith [mul_nonneg (by linarith : (0:ℝ) ≤ x - 2) (by linarith : (0:ℝ) ≤ 13 / 6 - x)]
  · have h1 : (1 + x) ^ 3 * (u - 1) ≤ (1 + x) ^ 3 * (19 / 25 - 1) := by
      apply mul_le_mul_of_nonneg_left (by linarith); positivity
    have h2 : 12.5 * x + 2 ≤ (1 + x) ^ 3 := by
      have : 0 ≤ (x - 2) * (x ^ 2 + 5 * x + 1 / 2) := mul_nonneg (by linarith) (by positivity)
      nlinarith
    nlinarith
  · nlinarith

theorem hh46_s4_dg_sub {x al b1 b2 : ℝ} :
    hsDg x b2 al - hsDg x b1 al = -2 * (x - al) * (b2 - b1) := by
  unfold hsDg; ring

theorem hh46_s4_wc_sub {x al b1 b2 u : ℝ} (hS : x * (x + 2) + al ^ 2 ≠ 0) :
    hh46S4Wc x b2 al u - hh46S4Wc x b1 al u = (hsDg x b2 al - hsDg x b1 al) *
      ((hsDg x b1 al + hsDg x b2 al) * u - hh46S4P x u) / (x * (x + 2) + al ^ 2) ^ 2 := by
  unfold hh46S4Wc
  field_simp
  ring

/-- The rational part of the `Φ` bracket, `2w_c + Rest`. -/
theorem hh46_s4_phi_split {x al b u : ℝ} :
    hh46S4PhiC x b al u = hh46S4G x u - (2 * hh46S4Wc x b al u - 1 / 2 + hh46S4Rest x b al u +
      log (2 * al * (al + b) / (x * (x + 2) + al ^ 2))) / 7 := rfl

theorem hh46_s4_psi_phi {x al b u : ℝ} :
    hh46S4PsiC x b al u = hh46S4PhiC x b al u -
      ((x * (x + 2) + al ^ 2) / (al * (al + b)) - 2) * (hh46S4Wc x b al u - 3 / 4) / 7 := by
  unfold hh46S4PsiC hh46S4PhiC; ring

/-- The fixed-`u` divided difference of the rational part of the `Φ` bracket. -/
theorem hh46_s4_rest_sub {x al b1 b2 u : ℝ} (hS : x * (x + 2) + al ^ 2 ≠ 0) (hal : al ≠ 0)
    (hA1 : al + b1 ≠ 0) (hA2 : al + b2 ≠ 0) :
    (2 * hh46S4Wc x b2 al u + hh46S4Rest x b2 al u) - (2 * hh46S4Wc x b1 al u + hh46S4Rest x b1 al u) =
      (b2 - b1) * (4 * (x - al) * (u * (x * (x + 2) + al ^ 2) - (hsDg x b1 al + hsDg x b2 al) * u +
        hh46S4P x u) / (x * (x + 2) + al ^ 2) ^ 2 - (1 - u) / al - al / ((al + b1) * (al + b2))) := by
  unfold hh46S4Wc hh46S4Rest hh46S4EL hsDg
  field_simp
  ring

/-- `log(A₂/A₁) ≥ (β₂ - β₁)/A₂`. -/
theorem hh46_s4_log_sub {x al b1 b2 : ℝ} (hx : 0 < x) (hal : 0 < al) (hb1 : 0 < b1) (h12 : b1 ≤ b2) :
    (b2 - b1) / (al + b2) ≤ log (2 * al * (al + b2) / (x * (x + 2) + al ^ 2)) -
      log (2 * al * (al + b1) / (x * (x + 2) + al ^ 2)) := by
  have hS : 0 < x * (x + 2) + al ^ 2 := by positivity
  have hA1 : 0 < al + b1 := by linarith
  have hA2 : 0 < al + b2 := by linarith
  rw [← log_div (by positivity) (by positivity)]
  have e : 2 * al * (al + b2) / (x * (x + 2) + al ^ 2) / (2 * al * (al + b1) / (x * (x + 2) + al ^ 2)) =
      (al + b2) / (al + b1) := by
    field_simp
  rw [e]
  have := one_sub_inv_le_log_of_pos (x := (al + b2) / (al + b1)) (by positivity)
  have e2 : 1 - ((al + b2) / (al + b1))⁻¹ = (b2 - b1) / (al + b2) := by
    field_simp; ring
  linarith

/-- The quotient of the fixed-`u` step is at least `k_Φ`. -/
theorem hh46_s4_quot_ge {x al b1 b2 u : ℝ} (hx : 2 ≤ x) (hx2 : x ≤ 13 / 6) (hal : 1 ≤ al)
    (hal2 : al ≤ 22 / 19) (hb1 : x ≤ b1) (h12 : b1 ≤ b2) (hb2 : b2 ≤ 20 / 19 * x)
    (hu : 757 / 1000 ≤ u) (hu2 : u ≤ 19 / 25) :
    hh46S4kPhi x al u ≤ 4 * (x - al) * (u * (x * (x + 2) + al ^ 2) - (hsDg x b1 al + hsDg x b2 al) * u +
        hh46S4P x u) / (x * (x + 2) + al ^ 2) ^ 2 - (1 - u) / al - al / ((al + b1) * (al + b2)) +
      1 / (al + b2) := by
  obtain ⟨-, hD1, -, -, -⟩ := hh46_s4_signs hx hx2 hal hal2 hb1 (by linarith) hu hu2
  obtain ⟨-, hD2, -, -, -⟩ := hh46_s4_signs hx hx2 hal hal2 (by linarith : x ≤ b2) hb2 hu hu2
  have hS : 0 < x * (x + 2) + al ^ 2 := by positivity
  have hA1 : 0 < al + b1 := by linarith
  have hA2 : 0 < al + b2 := by linarith
  have h1 : 4 * (x - al) * (u * (x * (x + 2) + al ^ 2) - 2 * hsDg x x al * u + hh46S4P x u) /
      (x * (x + 2) + al ^ 2) ^ 2 ≤ 4 * (x - al) * (u * (x * (x + 2) + al ^ 2) -
        (hsDg x b1 al + hsDg x b2 al) * u + hh46S4P x u) / (x * (x + 2) + al ^ 2) ^ 2 := by
    apply div_le_div_of_nonneg_right _ (by positivity)
    apply mul_le_mul_of_nonneg_left _ (by linarith)
    nlinarith
  have h2 : x / ((al + x) * (al + 20 / 19 * x)) ≤ b1 / ((al + b1) * (al + b2)) := by
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    have k1 : x * (al + b1) ≤ b1 * (al + x) := by nlinarith
    have k2 : al + b2 ≤ al + 20 / 19 * x := by linarith
    have hb0 : 0 ≤ b1 * (al + x) := by
      have : 0 ≤ b1 := by linarith
      positivity
    have := mul_le_mul k1 k2 (by linarith) hb0
    nlinarith
  have e : -(al / ((al + b1) * (al + b2))) + 1 / (al + b2) = b1 / ((al + b1) * (al + b2)) := by
    field_simp; ring
  unfold hh46S4kPhi
  linarith

/-- **The fixed-`u` `β`-step for `Φ`**. -/
theorem hh46_s4_phi_bstep {x al b1 b2 u : ℝ} (hx : 2 ≤ x) (hx2 : x ≤ 13 / 6) (hal : 1 ≤ al)
    (hal2 : al ≤ 22 / 19) (hb1 : x ≤ b1) (h12 : b1 ≤ b2) (hb2 : b2 ≤ 20 / 19 * x)
    (hu : 757 / 1000 ≤ u) (hu2 : u ≤ 19 / 25) :
    (b2 - b1) / 105 ≤ hh46S4PhiC x b1 al u - hh46S4PhiC x b2 al u := by
  have hS : 0 < x * (x + 2) + al ^ 2 := by positivity
  have hA1 : 0 < al + b1 := by linarith
  have hA2 : 0 < al + b2 := by linarith
  have hid := hh46_s4_rest_sub (x := x) (al := al) (b1 := b1) (b2 := b2) (u := u) hS.ne'
    (by linarith) hA1.ne' hA2.ne'
  have hlog := hh46_s4_log_sub (x := x) (al := al) (b1 := b1) (b2 := b2) (by linarith) (by linarith)
    (by linarith) h12
  have hq := hh46_s4_quot_ge hx hx2 hal hal2 hb1 h12 hb2 hu hu2
  have hk := hh46_s4_kPhi_ge hx hx2 hal hal2 hu hu2
  rw [hh46_s4_phi_split, hh46_s4_phi_split]
  have h0 : 0 ≤ b2 - b1 := by linarith
  have hprod := mul_le_mul_of_nonneg_left (hk.trans hq) h0
  have e1 : (b2 - b1) * (1 / (al + b2)) = (b2 - b1) / (al + b2) := by ring
  nlinarith

/-- **The fixed-`u` `β`-step for `Ψ`**. -/
theorem hh46_s4_psi_bstep {x al b1 b2 u : ℝ} (hx : 2 ≤ x) (hx2 : x ≤ 13 / 6) (hal : 1 ≤ al)
    (hal2 : al ≤ 22 / 19) (hb1 : x ≤ b1) (h12 : b1 ≤ b2) (hb2 : b2 ≤ 20 / 19 * x)
    (hu : 757 / 1000 ≤ u) (hu2 : u ≤ 19 / 25) :
    (b2 - b1) / 105 ≤ hh46S4PsiC x b1 al u - hh46S4PsiC x b2 al u := by
  have hS : 0 < x * (x + 2) + al ^ 2 := by positivity
  have hal0 : 0 < al := by linarith
  have hA1 : 0 < al + b1 := by linarith
  have hA2 : 0 < al + b2 := by linarith
  have h0 : 0 ≤ b2 - b1 := by linarith
  obtain ⟨hD1lo, hD1, hD0, hP, hT1⟩ := hh46_s4_signs hx hx2 hal hal2 hb1 (by linarith) hu hu2
  obtain ⟨hD2lo, hD2, -, -, -⟩ := hh46_s4_signs hx hx2 hal hal2 (by linarith : x ≤ b2) hb2 hu hu2
  have hid := hh46_s4_rest_sub (x := x) (al := al) (b1 := b1) (b2 := b2) (u := u) hS.ne'
    hal0.ne' hA1.ne' hA2.ne'
  have hlog := hh46_s4_log_sub (x := x) (al := al) (b1 := b1) (b2 := b2) (by linarith) (by linarith)
    (by linarith) h12
  have hq := hh46_s4_quot_ge hx hx2 hal hal2 hb1 h12 hb2 hu hu2
  -- the `T` and `w_c` increments
  set T1 := (x * (x + 2) + al ^ 2) / (al * (al + b1)) with hT1d
  set T2 := (x * (x + 2) + al ^ 2) / (al * (al + b2)) with hT2d
  set T0 := (x * (x + 2) + al ^ 2) / (al * (al + x)) with hT0d
  set X12 := (hsDg x b1 al + hsDg x b2 al) * u - hh46S4P x u with hX12d
  set X0 := 2 * hsDg x x al * u - hh46S4P x u with hX0d
  have eT : T2 - T1 = -(x * (x + 2) + al ^ 2) * (b2 - b1) / (al * (al + b1) * (al + b2)) := by
    rw [hT1d, hT2d]; field_simp; ring
  have eW : hh46S4Wc x b2 al u - hh46S4Wc x b1 al u =
      -(2 * (x - al) * (b2 - b1) * X12) / (x * (x + 2) + al ^ 2) ^ 2 := by
    rw [hh46_s4_wc_sub hS.ne', hh46_s4_dg_sub, hX12d]; ring
  have hT1ge : 2 ≤ T1 := by
    rw [hT1d, le_div_iff₀ (by positivity)]; linarith only [hT1]
  have hT10 : T1 ≤ T0 := by
    rw [hT1d, hT0d]
    apply div_le_div_of_nonneg_left hS.le (by positivity)
    exact mul_le_mul_of_nonneg_left (by linarith) hal0.le
  have hu0 : 0 ≤ u := by linarith
  have hX0 : 0 ≤ X0 := by
    rw [hX0d]
    have := mul_le_mul_of_nonneg_left hD0 (by norm_num : (0:ℝ) ≤ 2 * (757 / 1000))
    have := mul_le_mul_of_nonneg_left (hD0.trans (le_refl _)) (by linarith : (0:ℝ) ≤ 2 * (u - 757 / 1000))
    nlinarith only [this, hD0, hP, hu, mul_le_mul_of_nonneg_right hD0 hu0]
  have hX120 : X12 ≤ X0 := by
    rw [hX12d, hX0d]
    have := mul_le_mul_of_nonneg_right (add_le_add hD1 hD2) hu0
    linarith
  -- the `T`-term
  have hTE : (T1 - 2) * X12 ≤ (T0 - 2) * X0 := by
    rcases le_total 0 X12 with h | h
    · have := mul_le_mul (by linarith : T1 - 2 ≤ T0 - 2) hX120 h (by linarith)
      linarith
    · have : (T1 - 2) * X12 ≤ 0 := mul_nonpos_of_nonneg_of_nonpos (by linarith) h
      have : 0 ≤ (T0 - 2) * X0 := mul_nonneg (by linarith) hX0
      linarith
  have hTEterm : -(2 * (x - al) * (b2 - b1) * ((T0 - 2) * X0)) / (x * (x + 2) + al ^ 2) ^ 2 ≤
      (T1 - 2) * (hh46S4Wc x b2 al u - hh46S4Wc x b1 al u) := by
    rw [eW]
    have hc : 0 ≤ 2 * (x - al) * (b2 - b1) := by
      have : 0 ≤ x - al := by linarith
      positivity
    have := mul_le_mul_of_nonneg_left hTE hc
    rw [show (T1 - 2) * (-(2 * (x - al) * (b2 - b1) * X12) / (x * (x + 2) + al ^ 2) ^ 2) =
      -(2 * (x - al) * (b2 - b1) * ((T1 - 2) * X12)) / (x * (x + 2) + al ^ 2) ^ 2 by ring]
    apply div_le_div_of_nonneg_right _ (by positivity)
    linarith
  have htE : hh46S4tE x al u = 2 * (T0 - 2) * (x - al) * X0 / (x * (x + 2) + al ^ 2) ^ 2 := by
    unfold hh46S4tE; rw [hT0d, hX0d]
  -- the `w_c`-term, by cases on the sign of `w_c(β₂) - 3/4`
  have hWc : hh46S4Wc x b2 al u ≤ hh46S4Wc x x al u := by
    have := hh46_s4_wc_sub (x := x) (al := al) (b1 := b2) (b2 := x) (u := u) hS.ne'
    rw [hh46_s4_dg_sub] at this
    have hpos : 0 ≤ -2 * (x - al) * (x - b2) * ((hsDg x b2 al + hsDg x x al) * u - hh46S4P x u) /
        (x * (x + 2) + al ^ 2) ^ 2 := by
      apply div_nonneg _ (by positivity)
      have h1 : 0 ≤ -2 * (x - al) * (x - b2) := by
        have := mul_nonneg (by linarith : (0:ℝ) ≤ x - al) (by linarith : (0:ℝ) ≤ b2 - x)
        linarith only [this, show -2 * (x - al) * (x - b2) = 2 * ((x - al) * (b2 - x)) by ring]
      have h2 : 0 ≤ (hsDg x b2 al + hsDg x x al) * u - hh46S4P x u := by
        have := mul_le_mul_of_nonneg_right (add_le_add hD2lo hD0) hu0
        nlinarith only [this, hP, hu]
      exact mul_nonneg h1 h2
    linarith
  have hA12 : (al + x) ^ 2 ≤ (al + b1) * (al + b2) := by
    have := mul_le_mul (by linarith : al + x ≤ al + b1) (by linarith : al + x ≤ al + b2)
      (by linarith) (by linarith)
    linarith only [this, show (al + x) ^ 2 = (al + x) * (al + x) by ring]
  set Q := 4 * (x - al) * (u * (x * (x + 2) + al ^ 2) - (hsDg x b1 al + hsDg x b2 al) * u +
      hh46S4P x u) / (x * (x + 2) + al ^ 2) ^ 2 - (1 - u) / al - al / ((al + b1) * (al + b2)) +
      1 / (al + b2) with hQd
  set W0 := (x * (x + 2) + al ^ 2) * (hh46S4Wc x x al u - 3 / 4) / (al * (al + x) ^ 2) with hW0d
  set tE := 2 * (T0 - 2) * (x - al) * X0 / (x * (x + 2) + al ^ 2) ^ 2 with htEd
  have hc : -((b2 - b1) * tE) ≤ (T1 - 2) * (hh46S4Wc x b2 al u - hh46S4Wc x b1 al u) := by
    have e : -((b2 - b1) * tE) = -(2 * (x - al) * (b2 - b1) * ((T0 - 2) * X0)) /
        (x * (x + 2) + al ^ 2) ^ 2 := by rw [htEd]; ring
    rw [e]; exact hTEterm
  have key : (b2 - b1) / 105 * 7 ≤ (b2 - b1) * Q + (T2 - T1) * (hh46S4Wc x b2 al u - 3 / 4) +
      (T1 - 2) * (hh46S4Wc x b2 al u - hh46S4Wc x b1 al u) := by
    rcases le_total (3 / 4) (hh46S4Wc x b2 al u) with hw | hw
    · have hk := hh46_s4_kI_ge hx hx2 hal hal2 hu hu2
      unfold hh46S4kI at hk
      rw [htE] at hk
      have hQ' : 1 / 15 + W0 + tE ≤ Q := by linarith only [hk, hq]
      have ha := mul_le_mul_of_nonneg_left hQ' h0
      have hb : (b2 - b1) * (1 / 15 + W0 + tE) = (b2 - b1) / 15 + (b2 - b1) * W0 + (b2 - b1) * tE := by
        ring
      have hd : -((b2 - b1) * W0) ≤ (T2 - T1) * (hh46S4Wc x b2 al u - 3 / 4) := by
        rw [eT]
        have e1 : -(x * (x + 2) + al ^ 2) * (b2 - b1) / (al * (al + b1) * (al + b2)) *
            (hh46S4Wc x b2 al u - 3 / 4) = -((b2 - b1) * ((x * (x + 2) + al ^ 2) *
              (hh46S4Wc x b2 al u - 3 / 4) / (al * ((al + b1) * (al + b2))))) := by ring
        rw [e1, neg_le_neg_iff]
        apply mul_le_mul_of_nonneg_left _ h0
        rw [hW0d]
        have n1 : 0 ≤ (x * (x + 2) + al ^ 2) * (hh46S4Wc x x al u - 3 / 4) :=
          mul_nonneg hS.le (by linarith only [hw, hWc])
        have n2 : (x * (x + 2) + al ^ 2) * (hh46S4Wc x b2 al u - 3 / 4) ≤
            (x * (x + 2) + al ^ 2) * (hh46S4Wc x x al u - 3 / 4) :=
          mul_le_mul_of_nonneg_left (by linarith only [hWc]) hS.le
        exact div_le_div₀ n1 n2 (by positivity) (mul_le_mul_of_nonneg_left hA12 hal0.le)
      linarith only [ha, hb, hc, hd]
    · have hk := hh46_s4_kII_ge hx hx2 hal hal2 hu hu2
      unfold hh46S4kII at hk
      rw [htE] at hk
      have hQ' : 1 / 15 + tE ≤ Q := by linarith only [hk, hq]
      have ha := mul_le_mul_of_nonneg_left hQ' h0
      have hb : (b2 - b1) * (1 / 15 + tE) = (b2 - b1) / 15 + (b2 - b1) * tE := by ring
      have hd : 0 ≤ (T2 - T1) * (hh46S4Wc x b2 al u - 3 / 4) := by
        rw [eT]
        apply mul_nonneg_of_nonpos_of_nonpos _ (by linarith only [hw])
        apply div_nonpos_of_nonpos_of_nonneg _ (by positivity)
        exact mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.2 hS.le) h0
      linarith only [ha, hb, hc, hd]
  have hsplit : hh46S4PsiC x b1 al u - hh46S4PsiC x b2 al u =
      ((2 * hh46S4Wc x b2 al u + hh46S4Rest x b2 al u) - (2 * hh46S4Wc x b1 al u + hh46S4Rest x b1 al u) +
        (log (2 * al * (al + b2) / (x * (x + 2) + al ^ 2)) - log (2 * al * (al + b1) / (x * (x + 2) + al ^ 2))) +
        ((T2 - T1) * (hh46S4Wc x b2 al u - 3 / 4) + (T1 - 2) * (hh46S4Wc x b2 al u - hh46S4Wc x b1 al u))) / 7 := by
    rw [hh46_s4_psi_phi, hh46_s4_psi_phi, hh46_s4_phi_split, hh46_s4_phi_split, hT1d, hT2d]
    ring
  rw [hsplit, hid]
  have e1 : (b2 - b1) * Q = (b2 - b1) * (4 * (x - al) * (u * (x * (x + 2) + al ^ 2) -
      (hsDg x b1 al + hsDg x b2 al) * u + hh46S4P x u) / (x * (x + 2) + al ^ 2) ^ 2 - (1 - u) / al -
      al / ((al + b1) * (al + b2))) + (b2 - b1) / (al + b2) := by rw [hQd]; ring
  linarith only [key, e1, hlog]

/-- `∂_u Φ` at the midpoint `m` (exact: `Φ` is quadratic in `u`). -/
noncomputable def hh46S4MPhi (x b al m : ℝ) : ℝ :=
  (4 * (1 + x) ^ 2 * ((1 + x) ^ 2 - (1 + x) + 1) - 2 * hh46S4P x m * (1 + x) ^ 3) /
      (16 * x ^ 2 * (x + 2) ^ 2) -
    (2 * hsDg x b al * (hsDg x b al - (1 + x) ^ 3) / (x * (x + 2) + al ^ 2) ^ 2 + (al + b) / al -
      (2 * hsDg x b al - (1 + x) ^ 3) / (x * (x + 2) + al ^ 2)) / 7

/-- `∂_u Ψ` at the midpoint `m`. -/
noncomputable def hh46S4MPsi (x b al m : ℝ) : ℝ :=
  (4 * (1 + x) ^ 2 * ((1 + x) ^ 2 - (1 + x) + 1) - 2 * hh46S4P x m * (1 + x) ^ 3) /
      (16 * x ^ 2 * (x + 2) ^ 2) -
    ((x * (x + 2) + al ^ 2) / (al * (al + b)) * (hsDg x b al * (hsDg x b al - (1 + x) ^ 3)) /
        (x * (x + 2) + al ^ 2) ^ 2 + (al + b) / al -
      (2 * hsDg x b al - (1 + x) ^ 3) / (x * (x + 2) + al ^ 2)) / 7

theorem hh46_s4_phi_usub {x al b u1 u2 : ℝ} (hx : 0 < x) (hal : 0 < al) (hb : 0 < b) :
    hh46S4PhiC x b al u1 - hh46S4PhiC x b al u2 = (u1 - u2) * hh46S4MPhi x b al ((u1 + u2) / 2) := by
  have hS : x * (x + 2) + al ^ 2 ≠ 0 := by positivity
  have hx2 : x + 2 ≠ 0 := by positivity
  unfold hh46S4PhiC hh46S4MPhi hh46S4G hh46S4Wc hh46S4Rest hh46S4EL hh46S4P
  field_simp
  ring

theorem hh46_s4_psi_usub {x al b u1 u2 : ℝ} (hx : 0 < x) (hal : 0 < al) (hb : 0 < b) :
    hh46S4PsiC x b al u1 - hh46S4PsiC x b al u2 = (u1 - u2) * hh46S4MPsi x b al ((u1 + u2) / 2) := by
  have hS : x * (x + 2) + al ^ 2 ≠ 0 := by positivity
  have hx2 : x + 2 ≠ 0 := by positivity
  have hA : al + b ≠ 0 := by positivity
  unfold hh46S4PsiC hh46S4MPsi hh46S4G hh46S4Wc hh46S4Rest hh46S4EL hh46S4P
  field_simp
  ring

/-- `∂_u Φ ≥ L_u ≥ -13/20` along `x ≤ β ≤ 20x/19`. -/
theorem hh46_s4_MPhi_ge {x al b m : ℝ} (hx : 2 ≤ x) (hx2 : x ≤ 13 / 6) (hal : 1 ≤ al)
    (hal2 : al ≤ 22 / 19) (hb : x ≤ b) (hb2 : b ≤ 20 / 19 * x) (hm : 757 / 1000 ≤ m)
    (hm2 : m ≤ 19 / 25) : -(13 / 20) ≤ hh46S4MPhi x b al m := by
  have hL := hh46_s4_Lu_ge hx hx2 hal hal2 hm hm2
  obtain ⟨hDlo, hD, -, -, -⟩ := hh46_s4_signs hx hx2 hal hal2 hb hb2 hm hm2
  obtain ⟨hDmlo, hDm, -, -, -⟩ := hh46_s4_signs hx hx2 hal hal2 (by linarith : x ≤ 20 / 19 * x)
    le_rfl hm hm2
  have hS : 0 < x * (x + 2) + al ^ 2 := by positivity
  have hal0 : 0 < al := by linarith
  have hD03 : hsDg x x al ≤ 3 := by unfold hsDg; nlinarith
  have hS3 : 27 ≤ (1 + x) ^ 3 := by nlinarith [sq_nonneg (1 + x)]
  have hsub := hh46_s4_dg_sub (x := x) (al := al) (b1 := b) (b2 := 20 / 19 * x)
  set D := hsDg x b al with hDd
  set Dm := hsDg x (20 / 19 * x) al with hDmd
  have hg : 2 * D * (D - (1 + x) ^ 3) / (x * (x + 2) + al ^ 2) ^ 2 - 2 * D / (x * (x + 2) + al ^ 2) ≤
      2 * Dm * (Dm - (1 + x) ^ 3) / (x * (x + 2) + al ^ 2) ^ 2 - 2 * Dm / (x * (x + 2) + al ^ 2) := by
    have e : (2 * D * (D - (1 + x) ^ 3) / (x * (x + 2) + al ^ 2) ^ 2 - 2 * D / (x * (x + 2) + al ^ 2)) -
        (2 * Dm * (Dm - (1 + x) ^ 3) / (x * (x + 2) + al ^ 2) ^ 2 - 2 * Dm / (x * (x + 2) + al ^ 2)) =
        (D - Dm) * (2 * (D + Dm - (1 + x) ^ 3 - (x * (x + 2) + al ^ 2))) / (x * (x + 2) + al ^ 2) ^ 2 := by
      field_simp; ring
    have h1 : 0 ≤ D - Dm := by
      rw [show D - Dm = -(Dm - D) by ring, hsub]
      have := mul_nonneg (by linarith : (0:ℝ) ≤ x - al) (by linarith : (0:ℝ) ≤ 20 / 19 * x - b)
      nlinarith only [this]
    have h2 : 2 * (D + Dm - (1 + x) ^ 3 - (x * (x + 2) + al ^ 2)) ≤ 0 := by
      linarith only [hD, hDm, hD03, hS3, hS]
    have : (D - Dm) * (2 * (D + Dm - (1 + x) ^ 3 - (x * (x + 2) + al ^ 2))) / (x * (x + 2) + al ^ 2) ^ 2 ≤ 0 :=
      div_nonpos_of_nonpos_of_nonneg (mul_nonpos_of_nonneg_of_nonpos h1 h2) (by positivity)
    linarith only [e, this]
  have hab : (al + b) / al ≤ (al + 20 / 19 * x) / al :=
    div_le_div_of_nonneg_right (by linarith) hal0.le
  have e1 : hh46S4MPhi x b al m = (4 * (1 + x) ^ 2 * ((1 + x) ^ 2 - (1 + x) + 1) - 2 * hh46S4P x m * (1 + x) ^ 3) /
      (16 * x ^ 2 * (x + 2) ^ 2) - ((2 * D * (D - (1 + x) ^ 3) / (x * (x + 2) + al ^ 2) ^ 2 -
        2 * D / (x * (x + 2) + al ^ 2)) + (al + b) / al + (1 + x) ^ 3 / (x * (x + 2) + al ^ 2)) / 7 := by
    unfold hh46S4MPhi; rw [← hDd]; ring
  have e2 : hh46S4Lu x al m = (4 * (1 + x) ^ 2 * ((1 + x) ^ 2 - (1 + x) + 1) - 2 * hh46S4P x m * (1 + x) ^ 3) /
      (16 * x ^ 2 * (x + 2) ^ 2) - ((2 * Dm * (Dm - (1 + x) ^ 3) / (x * (x + 2) + al ^ 2) ^ 2 -
        2 * Dm / (x * (x + 2) + al ^ 2)) + (al + 20 / 19 * x) / al + (1 + x) ^ 3 / (x * (x + 2) + al ^ 2)) / 7 := by
    unfold hh46S4Lu; rw [← hDmd]; ring
  linarith only [hL, e1, e2, hg, hab]

theorem hh46_s4_MPsi_ge {x al b m : ℝ} (hx : 2 ≤ x) (hx2 : x ≤ 13 / 6) (hal : 1 ≤ al)
    (hal2 : al ≤ 22 / 19) (hb : x ≤ b) (hb2 : b ≤ 20 / 19 * x) (hm : 757 / 1000 ≤ m)
    (hm2 : m ≤ 19 / 25) : -(13 / 20) ≤ hh46S4MPsi x b al m := by
  have h := hh46_s4_MPhi_ge hx hx2 hal hal2 hb hb2 hm hm2
  obtain ⟨hDlo, hD, -, -, hT⟩ := hh46_s4_signs hx hx2 hal hal2 hb hb2 hm hm2
  have hS : 0 < x * (x + 2) + al ^ 2 := by positivity
  have hal0 : 0 < al := by linarith
  have hD03 : hsDg x x al ≤ 3 := by unfold hsDg; nlinarith
  have hS3 : 27 ≤ (1 + x) ^ 3 := by nlinarith [sq_nonneg (1 + x)]
  set D := hsDg x b al with hDd
  have hT2 : 2 ≤ (x * (x + 2) + al ^ 2) / (al * (al + b)) := by
    have : 0 < al * (al + b) := mul_pos hal0 (by linarith)
    rw [le_div_iff₀ this]; linarith only [hT]
  have hDD : D * (D - (1 + x) ^ 3) ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos (by linarith) (by linarith)
  have hk : (x * (x + 2) + al ^ 2) / (al * (al + b)) * (D * (D - (1 + x) ^ 3)) ≤ 2 * (D * (D - (1 + x) ^ 3)) := by
    nlinarith only [hT2, hDD]
  have e : hh46S4MPsi x b al m - hh46S4MPhi x b al m =
      (2 * (D * (D - (1 + x) ^ 3)) - (x * (x + 2) + al ^ 2) / (al * (al + b)) * (D * (D - (1 + x) ^ 3))) /
        (x * (x + 2) + al ^ 2) ^ 2 / 7 := by
    unfold hh46S4MPsi hh46S4MPhi; rw [← hDd]; ring
  have : 0 ≤ (2 * (D * (D - (1 + x) ^ 3)) - (x * (x + 2) + al ^ 2) / (al * (al + b)) * (D * (D - (1 + x) ^ 3))) /
      (x * (x + 2) + al ^ 2) ^ 2 / 7 := by
    apply div_nonneg _ (by norm_num)
    exact div_nonneg (by linarith only [hk]) (by positivity)
  linarith only [h, e, this]

/-- **Monotonicity in `β`** (with `u = ū(x, β)`). -/
theorem hh46_s4_beta_mono {x al b1 b2 : ℝ} (hx : 2 ≤ x) (hx2 : x ≤ 13 / 6) (hal : 1 ≤ al)
    (hal2 : al ≤ 22 / 19) (hb1 : x ≤ b1) (h12 : b1 ≤ b2) (hb2 : b2 ≤ 20 / 19 * x) :
    hh46S4PhiC x b2 al (hsUbar x b2) ≤ hh46S4PhiC x b1 al (hsUbar x b1) ∧
      hh46S4PsiC x b2 al (hsUbar x b2) ≤ hh46S4PsiC x b1 al (hsUbar x b1) := by
  obtain ⟨hu1, hu1'⟩ := hh46_s4_ubar_bounds hx hx2 hb1 (by linarith)
  obtain ⟨hu2, hu2'⟩ := hh46_s4_ubar_bounds hx hx2 (by linarith : x ≤ b2) hb2
  obtain ⟨hl0, hl1⟩ := hh46_s4_ubar_lip hx hx2 hb1 h12 hb2
  set u1 := hsUbar x b1
  set u2 := hsUbar x b2
  have hx0 : 0 < x := by linarith
  have hal0 : 0 < al := by linarith
  have hb10 : 0 < b1 := by linarith
  have hm : 757 / 1000 ≤ (u1 + u2) / 2 := by linarith
  have hm2 : (u1 + u2) / 2 ≤ 19 / 25 := by linarith
  have h0 : 0 ≤ u1 - u2 := hl0
  constructor
  · have hb := hh46_s4_phi_bstep hx hx2 hal hal2 hb1 h12 hb2 hu2 hu2'
    have hu := hh46_s4_phi_usub (b := b1) (u1 := u1) (u2 := u2) hx0 hal0 hb10
    have hM := hh46_s4_MPhi_ge hx hx2 hal hal2 hb1 (by linarith) hm hm2
    have := mul_le_mul_of_nonneg_left hM h0
    linarith only [hb, hu, this, hl1, h12]
  · have hb := hh46_s4_psi_bstep hx hx2 hal hal2 hb1 h12 hb2 hu2 hu2'
    have hu := hh46_s4_psi_usub (b := b1) (u1 := u1) (u2 := u2) hx0 hal0 hb10
    have hM := hh46_s4_MPsi_ge hx hx2 hal hal2 hb1 (by linarith) hm hm2
    have := mul_le_mul_of_nonneg_left hM h0
    linarith only [hb, hu, this, hl1, h12]

end SmoothedOctagon
