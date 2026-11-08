module

public import SmoothedOctagon.Exclusion.Mixed.ShortHand.Heavy.S2HandTermPoly

/-!
# S2 hand signs: the lower-shape terminal curve

On `3/4 ≤ r ≤ 49/60` the component bounds (on `F`, `q`, `V`, `A_n`, `L_n`, `Q_n` and
`1/Z + log(2Z/7)`) give `R_n'' < 0`; `R_n'(84/103) > 0` then makes `R_n` increasing in `r` up to
`84/103`, and the two terminal values use the cubic logarithm bound
`log y ≤ (y - 1) - (y - 1)²/2 + (y - 1)³/3`: `R_{63/25}(84/103) < -1/5000`,
`R_{49/20}(42/53) < -1/1000`. The scalar values are computed exactly.

## Main API

* `hl2Rl`, `hl2Rh`: `R_n` for `n = 49/20`, `63/25`.
* `hl2_Rl_le`, `hl2_Rh_le`: the two terminal signs along the curve.
-/

@[expose] public section

namespace SmoothedOctagon

open Real Set

/-! ### Elementary component bounds -/

theorem hl2_KJ_pos {r : ℝ} (h0 : 3 / 4 ≤ r) (h1 : r ≤ 49 / 60) :
    0 < hl2Kc r ∧ 0 < hl2Jc r := by
  unfold hl2Kc hl2Jc; constructor <;> nlinarith

theorem hl2_q_bounds {r : ℝ} (h0 : 3 / 4 ≤ r) (h1 : r ≤ 49 / 60) :
    11 / 30 < hl2qc r ∧ hl2qc r < 5 / 12 ∧ -(5 / 7) < hl2qcd r ∧ hl2qcd r < 0 ∧
      0 < hl2qcdd r ∧ hl2qcdd r < 1 / 5 := by
  have hg : 0 < 84 + 11 * r := by linarith
  have hg2 : (369 / 4) ^ 2 ≤ (84 + 11 * r) ^ 2 := pow_le_pow_left₀ (by norm_num) (by linarith) 2
  have hg3 : (369 / 4) ^ 3 ≤ (84 + 11 * r) ^ 3 := pow_le_pow_left₀ (by norm_num) (by linarith) 3
  unfold hl2qc hl2qcd hl2qcdd
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [lt_div_iff₀ hg]; linarith
  · rw [div_lt_iff₀ hg]; linarith
  · rw [lt_div_iff₀ (by positivity)]; nlinarith
  · exact div_neg_of_neg_of_pos (by norm_num) (by positivity)
  · positivity
  · rw [div_lt_iff₀ (by positivity)]; nlinarith

theorem hl2_F_bounds {r : ℝ} (h0 : 3 / 4 ≤ r) (h1 : r ≤ 49 / 60) :
    0 < hl2Fc r ∧ hl2Fc r < 11 / 400 ∧ 7 / 500 < hl2Fcd r ∧ hl2Fcd r < 1 / 50 ∧
      hl2Fcdd r < 1 / 12 := by
  have hK := (hl2_KJ_pos h0 h1).1
  have k0 := hl2_bK0 h0 h1
  have k1 := hl2_bK1 h0 h1
  have k2 := hl2_bK2 h0 h1
  have k3 := hl2_bK3 h0 h1
  unfold hl2Kc at hK
  unfold hl2Fc hl2Fcd hl2Fcdd hl2Kc
  refine ⟨div_pos (by nlinarith) hK, ?_, ?_, ?_, ?_⟩
  · rw [div_lt_iff₀ hK]; nlinarith
  · rw [lt_div_iff₀ (by positivity)]; nlinarith
  · rw [div_lt_iff₀ (by positivity)]; nlinarith
  · rw [div_lt_iff₀ (by positivity)]; nlinarith

theorem hl2_V_bounds {r : ℝ} (h0 : 3 / 4 ≤ r) (h1 : r ≤ 49 / 60) :
    0 < hl2Vc r ∧ hl2Vc r < 11 / 1000 ∧ -(1 / 30) < hl2Vcd r ∧ hl2Vcd r < 1 / 30 ∧
      hl2Vcdd r < 11 / 100 := by
  obtain ⟨q1, q2, q3, q4, q5, q6⟩ := hl2_q_bounds h0 h1
  obtain ⟨f1, f2, f3, f4, f5⟩ := hl2_F_bounds h0 h1
  have hq2 : 1877 / 180 < 85 * hl2qc r ^ 2 - 1 := by nlinarith
  have hq2' : 85 * hl2qc r ^ 2 - 1 < 1981 / 144 := by nlinarith
  unfold hl2Vc hl2Vcd hl2Vcdd
  generalize hl2qc r = q at *
  generalize hl2qcd r = q' at *
  generalize hl2qcdd r = q'' at *
  generalize hl2Fc r = F at *
  generalize hl2Fcd r = F' at *
  generalize hl2Fcdd r = F'' at *
  refine ⟨by nlinarith, by nlinarith, ?_, ?_, ?_⟩
  · have h1 : 7 / 500 * (1877 / 180) ≤ F' * (85 * q ^ 2 - 1) := by nlinarith
    have h2 : -(11 / 400 * (5 / 12) * (5 / 7)) ≤ F * q * q' := by
      have : 0 ≤ F * q := by nlinarith
      have : F * q ≤ 11 / 400 * (5 / 12) := by nlinarith
      nlinarith
    nlinarith
  · have h1 : F' * (85 * q ^ 2 - 1) ≤ 1 / 50 * (1981 / 144) := by nlinarith
    have h2 : F * q * q' ≤ 0 := by
      have : 0 ≤ F * q := by nlinarith
      nlinarith
    nlinarith
  · have h1 : F'' * (85 * q ^ 2 - 1) ≤ 1 / 12 * (1981 / 144) := by nlinarith
    have h2 : F' * q * q' ≤ 0 := by
      have : 0 ≤ F' * q := by nlinarith
      nlinarith
    have h3 : F * (q' ^ 2 + q * q'') ≤ 11 / 400 * (25 / 49 + 5 / 12 * (1 / 5)) := by
      have : q' ^ 2 ≤ 25 / 49 := by nlinarith
      have : q * q'' ≤ 5 / 12 * (1 / 5) := by nlinarith
      have : 0 ≤ q' ^ 2 + q * q'' := by nlinarith
      nlinarith
    nlinarith

/-- `[1/Z + log(2Z/7)]'' < 7/20` (the cleared sign `T`, `hl2_bT`). -/
theorem hl2_ZL_bound {r : ℝ} (h0 : 3 / 4 ≤ r) (h1 : r ≤ 49 / 60) :
    hl2Zidd r + hl2Lgdd r < 7 / 20 := by
  have hJ := (hl2_KJ_pos h0 h1).2
  have hT := hl2_bT h0 h1
  have hr : 0 < r := by linarith
  unfold hl2Jc at hJ
  have e : hl2Zidd r + hl2Lgdd r = (1152 * (-r * (-2218) * hl2Jc r - 2 * (3645 - 2218 * r) *
      (hl2Jc r - r * (3645 - 2218 * r))) * r ^ 2 + (((-2218) * hl2Jc r - (3645 - 2218 * r) ^ 2) *
      hl2Jc r * r ^ 2 + hl2Jc r ^ 3)) / (r ^ 2 * hl2Jc r ^ 3) := by
    unfold hl2Zidd hl2Lgdd
    have : hl2Jc r ≠ 0 := by unfold hl2Jc; positivity
    field_simp
    ring
  rw [e, div_lt_iff₀ (by unfold hl2Jc; positivity)]
  unfold hl2Jc
  linarith

/-! ### Concavity of `R_n` -/

/-- `R_n'' < 0` from the component bounds `0 < A_n < 5`, `-17 < A_n' < 0`, `A_n'' < 53`,
`L_n'' < -1`, `Q_n'' < -17/10` and the bounds on `V`, `V'`, `V''` and `[1/Z + log(2Z/7)]''`. -/
theorem hl2_Rcdd_neg {CA CL q0 q1 r : ℝ} {As Ls Qs As1 Ls1 Qs1 As2 Ls2 Qs2 : ℝ → ℝ}
    (h0 : 3 / 4 ≤ r) (h1 : r ≤ 49 / 60) (hCA : 0 < CA) (hCL : 0 < CL) (hg : 0 < q0 * r + q1)
    (hA : 0 < As r) (hA5 : 0 < 5 * CA * r ^ 2 - As r)
    (hA1 : 0 < 17 * CA * r ^ 3 + (r * As1 r - 2 * As r)) (hA1' : 0 < -(r * As1 r - 2 * As r))
    (hA2 : 0 < 53 * CA * r ^ 4 - (r ^ 2 * As2 r - 4 * r * As1 r + 6 * As r))
    (hL2 : 0 < -(CL * r ^ 4) - (r ^ 2 * Ls2 r - 4 * r * Ls1 r + 6 * Ls r))
    (hQ2 : 0 < -(17 / 10) * (q0 * r + q1) ^ 3 - (Qs2 r * (q0 * r + q1) ^ 2 -
      2 * q0 * Qs1 r * (q0 * r + q1) + 2 * q0 ^ 2 * Qs r)) :
    hl2Rcdd CA CL q0 q1 As Ls Qs As1 Ls1 Qs1 As2 Ls2 Qs2 r < 0 := by
  have hr : 0 < r := by linarith
  obtain ⟨v0, v1, v2, v3, v4⟩ := hl2_V_bounds h0 h1
  have hZL := hl2_ZL_bound h0 h1
  -- the five component quantities
  set A := As r / (CA * r ^ 2) with hAdef
  set A' := (As1 r * (CA * r ^ 2) - As r * (2 * CA * r)) / (CA * r ^ 2) ^ 2 with hA'def
  set A'' := ((As2 r * (CA * r ^ 2) - As r * (2 * CA)) * (CA * r ^ 2) -
    2 * (2 * CA * r) * (As1 r * (CA * r ^ 2) - As r * (2 * CA * r))) / (CA * r ^ 2) ^ 3
    with hA''def
  set L'' := ((Ls2 r * (CL * r ^ 2) - Ls r * (2 * CL)) * (CL * r ^ 2) -
    2 * (2 * CL * r) * (Ls1 r * (CL * r ^ 2) - Ls r * (2 * CL * r))) / (CL * r ^ 2) ^ 3
    with hL''def
  set Q'' := ((Qs2 r * (q0 * r + q1) - Qs r * 0) * (q0 * r + q1) -
    2 * q0 * (Qs1 r * (q0 * r + q1) - Qs r * q0)) / (q0 * r + q1) ^ 3 with hQ''def
  have eA' : A' = (r * As1 r - 2 * As r) / (CA * r ^ 3) := by rw [hA'def]; field_simp
  have eA'' : A'' = (r ^ 2 * As2 r - 4 * r * As1 r + 6 * As r) / (CA * r ^ 4) := by
    rw [hA''def]; field_simp; ring
  have eL'' : L'' = (r ^ 2 * Ls2 r - 4 * r * Ls1 r + 6 * Ls r) / (CL * r ^ 4) := by
    rw [hL''def]; field_simp; ring
  have eQ'' : Q'' = (Qs2 r * (q0 * r + q1) ^ 2 - 2 * q0 * Qs1 r * (q0 * r + q1) +
      2 * q0 ^ 2 * Qs r) / (q0 * r + q1) ^ 3 := by rw [hQ''def]; field_simp; ring
  have bA : 0 < A := by rw [hAdef]; positivity
  have bA5 : A < 5 := by rw [hAdef, div_lt_iff₀ (by positivity)]; linarith
  have bA1 : -17 < A' := by rw [eA', lt_div_iff₀ (by positivity)]; linarith
  have bA1' : A' < 0 := by rw [eA']; exact div_neg_of_neg_of_pos (by linarith) (by positivity)
  have bA2 : A'' < 53 := by rw [eA'', div_lt_iff₀ (by positivity)]; linarith
  have bL2 : L'' < -1 := by rw [eL'', div_lt_iff₀ (by positivity)]; linarith
  have bQ2 : Q'' < -(17 / 10) := by rw [eQ'', div_lt_iff₀ (by positivity)]; linarith
  have p1 : hl2Vcdd r * A ≤ 11 / 100 * 5 := by
    have := mul_le_mul_of_nonneg_right v4.le bA.le
    linarith
  have p2 : hl2Vcd r * A' < 17 / 30 := by
    have := mul_pos (by linarith : 0 < hl2Vcd r + 1 / 30) (by linarith : 0 < -A')
    linarith
  have p3 : hl2Vc r * A'' ≤ 11 / 1000 * 53 := by
    have := mul_le_mul_of_nonneg_left bA2.le v0.le
    linarith
  unfold hl2Rcdd
  rw [← hAdef, ← hA'def, ← hA''def, ← hL''def, ← hQ''def]
  linarith

/-! ### The two instances -/

/-- `R_{49/20}` (`n₋`). -/
noncomputable def hl2Rl (r : ℝ) : ℝ :=
  hl2Rc 60197437440 80263249920 887040 6773760 hl2Asl hl2Lsl hl2Qsl r

/-- `R_{63/25}` (`n₊`). -/
noncomputable def hl2Rh (r : ℝ) : ℝ :=
  hl2Rc 8360755200 11147673600 123200 940800 hl2Ash hl2Lsh hl2Qsh r

/-- **Monotonicity**: if `R'' < 0` on `[3/4, 84/103]` and
`R'(84/103) > 0`, then `R(r) ≤ R(r_e)` for `3/4 ≤ r ≤ r_e ≤ 84/103`. -/
theorem hl2_R_mono {R R1 R2 : ℝ → ℝ} {r re : ℝ} (h0 : 3 / 4 ≤ r) (hre : r ≤ re)
    (he : re ≤ 84 / 103) (hd : ∀ s ∈ Icc (3 / 4 : ℝ) (84 / 103), HasDerivAt R (R1 s) s)
    (hd1 : ∀ s ∈ Icc (3 / 4 : ℝ) (84 / 103), HasDerivAt R1 (R2 s) s)
    (h2 : ∀ s ∈ Icc (3 / 4 : ℝ) (84 / 103), R2 s < 0) (h1 : 0 < R1 (84 / 103)) : R r ≤ R re := by
  apply ss_le_of_deriv hre (fun z hz => hd z ⟨h0.trans hz.1, hz.2.trans he⟩)
  intro z hz
  have hz0 : 3 / 4 ≤ z := h0.trans hz.1.le
  have hz1 : z ≤ 84 / 103 := hz.2.le.trans he
  have : -R1 z ≤ -R1 (84 / 103) := ss_le_of_deriv (f := fun s => -R1 s) (f' := fun s => -R2 s) hz1
    (fun y hy => (hd1 y ⟨hz0.trans hy.1, hy.2⟩).neg)
    (fun y hy => by have := h2 y ⟨hz0.trans hy.1.le, hy.2.le⟩; linarith)
  linarith

theorem hl2_hd_Rl {r : ℝ} (h0 : 3 / 4 ≤ r) (h1 : r ≤ 49 / 60) :
    HasDerivAt hl2Rl (hl2Rcd 60197437440 80263249920 887040 6773760 hl2Asl hl2Lsl hl2Qsl hl2Asl1
      hl2Lsl1 hl2Qsl1 r) r :=
  hl2_hd_Rc (by linarith) (by norm_num) (by norm_num) (by linarith) (hl2_KJ_pos h0 h1).1.ne'
    (hl2_KJ_pos h0 h1).2 (hl2_hd_Asl r) (hl2_hd_Lsl r) (hl2_hd_Qsl r)

theorem hl2_hd_Rh {r : ℝ} (h0 : 3 / 4 ≤ r) (h1 : r ≤ 49 / 60) :
    HasDerivAt hl2Rh (hl2Rcd 8360755200 11147673600 123200 940800 hl2Ash hl2Lsh hl2Qsh hl2Ash1
      hl2Lsh1 hl2Qsh1 r) r :=
  hl2_hd_Rc (by linarith) (by norm_num) (by norm_num) (by linarith) (hl2_KJ_pos h0 h1).1.ne'
    (hl2_KJ_pos h0 h1).2 (hl2_hd_Ash r) (hl2_hd_Lsh r) (hl2_hd_Qsh r)

theorem hl2_hd_Rld {r : ℝ} (h0 : 3 / 4 ≤ r) (h1 : r ≤ 49 / 60) :
    HasDerivAt (hl2Rcd 60197437440 80263249920 887040 6773760 hl2Asl hl2Lsl hl2Qsl hl2Asl1 hl2Lsl1
      hl2Qsl1) (hl2Rcdd 60197437440 80263249920 887040 6773760 hl2Asl hl2Lsl hl2Qsl hl2Asl1 hl2Lsl1
      hl2Qsl1 hl2Asl2 hl2Lsl2 hl2Qsl2 r) r :=
  hl2_hd_Rcd (by linarith) (by norm_num) (by norm_num) (by linarith) (hl2_KJ_pos h0 h1).1.ne'
    (hl2_KJ_pos h0 h1).2 (hl2_hd_Asl r) (hl2_hd_Lsl r) (hl2_hd_Qsl r) (hl2_hd_Asl1 r)
    (hl2_hd_Lsl1 r) (hl2_hd_Qsl1 r)

theorem hl2_hd_Rhd {r : ℝ} (h0 : 3 / 4 ≤ r) (h1 : r ≤ 49 / 60) :
    HasDerivAt (hl2Rcd 8360755200 11147673600 123200 940800 hl2Ash hl2Lsh hl2Qsh hl2Ash1 hl2Lsh1
      hl2Qsh1) (hl2Rcdd 8360755200 11147673600 123200 940800 hl2Ash hl2Lsh hl2Qsh hl2Ash1 hl2Lsh1
      hl2Qsh1 hl2Ash2 hl2Lsh2 hl2Qsh2 r) r :=
  hl2_hd_Rcd (by linarith) (by norm_num) (by norm_num) (by linarith) (hl2_KJ_pos h0 h1).1.ne'
    (hl2_KJ_pos h0 h1).2 (hl2_hd_Ash r) (hl2_hd_Lsh r) (hl2_hd_Qsh r) (hl2_hd_Ash1 r)
    (hl2_hd_Lsh1 r) (hl2_hd_Qsh1 r)

/-- `R_{49/20}'(84/103) > 0` (exact value). -/
theorem hl2_Rld_r0 : 0 < hl2Rcd 60197437440 80263249920 887040 6773760 hl2Asl hl2Lsl hl2Qsl
    hl2Asl1 hl2Lsl1 hl2Qsl1 (84 / 103) := by
  norm_num [hl2Rcd, hl2Asl, hl2Lsl, hl2Qsl, hl2Asl1, hl2Lsl1, hl2Qsl1, hl2Vc, hl2Vcd, hl2Fc,
    hl2Fcd, hl2Kc, hl2qc, hl2qcd, hl2Zid, hl2Jc, hl2Lgd]

/-- `R_{63/25}'(84/103) > 0` (exact value). -/
theorem hl2_Rhd_r0 : 0 < hl2Rcd 8360755200 11147673600 123200 940800 hl2Ash hl2Lsh hl2Qsh
    hl2Ash1 hl2Lsh1 hl2Qsh1 (84 / 103) := by
  norm_num [hl2Rcd, hl2Ash, hl2Lsh, hl2Qsh, hl2Ash1, hl2Lsh1, hl2Qsh1, hl2Vc, hl2Vcd, hl2Fc,
    hl2Fcd, hl2Kc, hl2qc, hl2qcd, hl2Zid, hl2Jc, hl2Lgd]

/-- The cubic logarithm bound at a curve point. -/
theorem hl2_Lg_le {r : ℝ} (hr : 0 < r) (hJ : 0 < hl2Jc r) :
    hl2Lg r ≤ (2 * (hl2Jc r / (1152 * r)) / 7 - 1) - (2 * (hl2Jc r / (1152 * r)) / 7 - 1) ^ 2 / 2 +
      (2 * (hl2Jc r / (1152 * r)) / 7 - 1) ^ 3 / 3 :=
  hl2_log_le_cubic (by positivity)

/-- `R_{63/25}(84/103) < -1/5000` (exact value with the cubic logarithm bound). -/
theorem hl2_Rh_r0 : hl2Rh (84 / 103) < -1 / 5000 := by
  have h := hl2_Lg_le (r := 84 / 103) (by norm_num) (by norm_num [hl2Jc])
  unfold hl2Rh hl2Rc
  norm_num [hl2Ash, hl2Lsh, hl2Qsh, hl2Vc, hl2Fc, hl2Kc, hl2qc, hl2Zi, hl2Jc] at h ⊢
  linarith

/-- `R_{49/20}(42/53) < -1/1000` (exact value with the cubic logarithm bound). -/
theorem hl2_Rl_r1 : hl2Rl (42 / 53) < -1 / 1000 := by
  have h := hl2_Lg_le (r := 42 / 53) (by norm_num) (by norm_num [hl2Jc])
  unfold hl2Rl hl2Rc
  norm_num [hl2Asl, hl2Lsl, hl2Qsl, hl2Vc, hl2Fc, hl2Kc, hl2qc, hl2Zi, hl2Jc] at h ⊢
  linarith

/-- `R_{63/25} < -1/5000` on `3/4 ≤ r ≤ 84/103` (used for `x ≤ 9/4`). -/
theorem hl2_Rh_le {r : ℝ} (h0 : 3 / 4 ≤ r) (h1 : r ≤ 84 / 103) : hl2Rh r < -1 / 5000 := by
  refine lt_of_le_of_lt (hl2_R_mono h0 h1 le_rfl (fun s hs => hl2_hd_Rh hs.1 (by linarith [hs.2]))
    (fun s hs => hl2_hd_Rhd hs.1 (by linarith [hs.2])) (fun s hs => ?_) hl2_Rhd_r0) hl2_Rh_r0
  have hs0 := hs.1
  have hs1 : s ≤ 49 / 60 := by linarith [hs.2]
  exact hl2_Rcdd_neg hs0 hs1 (by norm_num) (by norm_num) (by linarith) (hl2_bAh_pos hs0 hs1)
    (hl2_bAh_lt5 hs0 hs1) (hl2_bAdh_gt hs0 hs1) (hl2_bAdh_neg hs0 hs1) (hl2_bAddh_lt hs0 hs1)
    (hl2_bLddh hs0 hs1) (hl2_bQddh hs0 hs1)

/-- `R_{49/20} < -1/1000` on `3/4 ≤ r ≤ 42/53` (used for `x ≥ 9/4`). -/
theorem hl2_Rl_le {r : ℝ} (h0 : 3 / 4 ≤ r) (h1 : r ≤ 42 / 53) : hl2Rl r < -1 / 1000 := by
  refine lt_of_le_of_lt (hl2_R_mono h0 h1 (by norm_num)
    (fun s hs => hl2_hd_Rl hs.1 (by linarith [hs.2]))
    (fun s hs => hl2_hd_Rld hs.1 (by linarith [hs.2])) (fun s hs => ?_) hl2_Rld_r0) hl2_Rl_r1
  have hs0 := hs.1
  have hs1 : s ≤ 49 / 60 := by linarith [hs.2]
  exact hl2_Rcdd_neg hs0 hs1 (by norm_num) (by norm_num) (by linarith) (hl2_bAl_pos hs0 hs1)
    (hl2_bAl_lt5 hs0 hs1) (hl2_bAdl_gt hs0 hs1) (hl2_bAdl_neg hs0 hs1) (hl2_bAddl_lt hs0 hs1)
    (hl2_bLddl hs0 hs1) (hl2_bQddl hs0 hs1)

end SmoothedOctagon
