module

public import SmoothedOctagon.Terminal.Cycle
public import SmoothedPolygons.Ch7.SmoothedPolygonDisk

/-!
# Terminal comparison: identification with the smoothed octagon

Tools for the equality case of the terminal comparison.

* `Term.isIntegralCurve_conj`: conjugating a Carathéodory solution by constant matrices.
* `Term.isIntegralCurve_congr_ae`: changing the right-hand side on a null set.
* `Term.eq_of_margin_eq`: a traceless matrix is determined by its margins.
* `Term.margin_conj_pow`, `Term.Rpow_inv`: relabeling by `R^r`.
* `Term.octActive`, `Term.octThird`: the octagon's switch margins.
* `Term.octagon_identification`: a normal period with four forward pieces, all factors `√2` and the
  octagon's initial margins is the smoothed octagon after relabeling by `R^r`, with `T = t_f`
  (uniqueness `polygon_trajectory_unique` after conjugation and a null-set change of control).
-/

@[expose] public section

namespace SmoothedOctagon

namespace Term

open SmoothedPolygons Set MeasureTheory

theorem conj_apply (Ci M C : Mat2) (i j : Fin 2) :
    (Ci * M * C) i j = Ci i 0 * C 0 j * M 0 0 + Ci i 0 * C 1 j * M 0 1 +
      Ci i 1 * C 0 j * M 1 0 + Ci i 1 * C 1 j * M 1 1 := by
  simp [Matrix.mul_apply, Fin.sum_univ_two]; ring

/-- Conjugating a Carathéodory solution by constant matrices. -/
theorem isIntegralCurve_conj {f v : ℝ → Mat2} {T : ℝ} (hI : IsIntegralCurve f v T)
    (Ci C : Mat2) : IsIntegralCurve (fun t ↦ Ci * f t * C) (fun t ↦ Ci * v t * C) T := by
  intro i j
  have hint : ∀ a b, IntervalIntegrable (fun s ↦ v s a b) volume 0 T := fun a b ↦ (hI a b).1
  have hsum : IntervalIntegrable (fun s ↦ Ci i 0 * C 0 j * v s 0 0 + Ci i 0 * C 1 j * v s 0 1 +
      Ci i 1 * C 0 j * v s 1 0 + Ci i 1 * C 1 j * v s 1 1) volume 0 T :=
    ((((hint 0 0).const_mul _).add ((hint 0 1).const_mul _)).add
      ((hint 1 0).const_mul _)).add ((hint 1 1).const_mul _)
  refine ⟨by simpa only [conj_apply] using hsum, fun t ht ↦ ?_⟩
  have hint' : ∀ a b, IntervalIntegrable (fun s ↦ v s a b) volume 0 t := fun a b ↦
    (hint a b).mono_set (by
      rw [uIcc_of_le ht.1, uIcc_of_le (ht.1.trans ht.2)]
      exact Icc_subset_Icc_right ht.2)
  simp only [conj_apply]
  rw [(hI 0 0).2 t ht, (hI 0 1).2 t ht, (hI 1 0).2 t ht, (hI 1 1).2 t ht,
    intervalIntegral.integral_add (((hint' 0 0).const_mul _).add ((hint' 0 1).const_mul _) |>.add
      ((hint' 1 0).const_mul _)) ((hint' 1 1).const_mul _),
    intervalIntegral.integral_add (((hint' 0 0).const_mul _).add ((hint' 0 1).const_mul _))
      ((hint' 1 0).const_mul _),
    intervalIntegral.integral_add ((hint' 0 0).const_mul _) ((hint' 0 1).const_mul _)]
  simp only [intervalIntegral.integral_const_mul]
  ring

/-- Changing the right-hand side of a Carathéodory solution on a null set. -/
theorem isIntegralCurve_congr_ae {f v w : ℝ → Mat2} {T : ℝ} (hI : IsIntegralCurve f v T)
    (hT : 0 ≤ T) (h : ∀ᵐ t, t ∈ Ioo 0 T → v t = w t) : IsIntegralCurve f w T := by
  intro i j
  obtain ⟨hint, heq⟩ := hI i j
  have hae : ∀ t, 0 ≤ t → ∀ᵐ s, s ∈ Set.uIoc 0 t → t ≤ T → v s i j = w s i j := by
    intro t ht0
    filter_upwards [(countable_singleton T).ae_notMem volume, h] with s hs hsv hsI htT
    rw [uIoc_of_le ht0] at hsI
    rw [hsv ⟨hsI.1, lt_of_le_of_ne (hsI.2.trans htT) hs⟩]
  refine ⟨hint.congr_ae ?_, fun t ht ↦ ?_⟩
  · rw [Filter.EventuallyEq, ae_restrict_iff' measurableSet_uIoc]
    filter_upwards [hae T hT] with s hs hsI using hs hsI le_rfl
  · rw [heq t ht]
    congr 1
    refine intervalIntegral.integral_congr_ae ?_
    filter_upwards [hae t ht.1] with s hs hsI using hs hsI ht.2

/-- A traceless matrix is determined by its three margins. -/
theorem eq_of_margin_eq {X Y : Mat2} (hX : X.trace = 0) (hY : Y.trace = 0)
    (h : ∀ j, margin j X = margin j Y) : X = Y := by
  have h3 : (0 : ℝ) < √3 := by positivity
  have h0 := h 0; have h1 := h 1; have h2 := h 2
  rw [margin_zero_apply, margin_zero_apply] at h0
  rw [margin_one_apply, margin_one_apply] at h1
  rw [margin_two_apply, margin_two_apply] at h2
  rw [Matrix.trace_fin_two] at hX hY
  have e10 : X 1 0 = Y 1 0 := by
    have e : 2 * X 1 0 / √3 + 2 * X 1 0 / √3 = 2 * Y 1 0 / √3 + 2 * Y 1 0 / √3 := by linarith
    field_simp at e; linarith
  have e00 : X 0 0 = Y 0 0 := by linarith
  have e11 : X 1 1 = Y 1 1 := by linarith
  have e01 : X 0 1 = Y 0 1 := by
    rw [e10] at h0
    have : √3 * X 0 1 = √3 * Y 0 1 := by linarith
    exact mul_left_cancel₀ h3.ne' this
  ext a b; fin_cases a <;> fin_cases b <;> assumption

/-- The active margin `2/√(2√2 - 1)` of the smoothed octagon's pieces. -/
noncomputable def octActive : ℝ := 2 / √(2 * √2 - 1)

/-- The third margin `2(√2 - 1)/√(2√2 - 1)` of the smoothed octagon's switch states. -/
noncomputable def octThird : ℝ := 2 * (√2 - 1) / √(2 * √2 - 1)

private lemma tm_f0 : ∀ L : Fin 3, (0 : Fin 3) - (2 - L) = L + 1 := by decide
private lemma tm_f1 : ∀ L : Fin 3, (1 : Fin 3) - (2 - L) = L + 2 := by decide
private lemma tm_f2 : ∀ L : Fin 3, (2 : Fin 3) - (2 - L) = L := by decide

private lemma tm_s2 : √2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)

private lemma tm_N0_pos : 0 < 2 * √2 - 1 := by
  have : (1 : ℝ) < √2 := by rw [Real.lt_sqrt (by norm_num)]; norm_num
  linarith

private lemma tm_octActive_pos : 0 < octActive := by
  have := tm_N0_pos; unfold octActive; positivity

private lemma tm_octThird_eq : octThird = (√2 - 1) * octActive := by
  unfold octThird octActive; ring

/-- `R^r` conjugation shifts margins: `p_j(R^{-n} X R^n) = p_{j - n}(X)`. -/
theorem margin_conj_pow (n : ℕ) (X : Mat2) (j : Fin 3) :
    margin j (R⁻¹ ^ n * X * R ^ n) = margin (j - n • (1 : Fin 3)) X := by
  induction n generalizing j with
  | zero => simp
  | succ n ih =>
    rw [pow_succ', pow_succ, show R⁻¹ * R⁻¹ ^ n * X * (R ^ n * R) =
      R⁻¹ * (R⁻¹ ^ n * X * R ^ n) * R by simp only [Matrix.mul_assoc], margin_Rinv_conj, ih,
      succ_nsmul]
    congr 1; abel

theorem Rpow_inv (n : ℕ) : (R ^ n)⁻¹ = R⁻¹ ^ n :=
  Matrix.inv_eq_left_inv (poly_Rinvpow_mul_Rpow n)

/-- **Identification with the smoothed octagon** (`SMALL_PERIOD_COST_EQUALITY_AUDIT` §4): a normal
period with four forward pieces, all factors `√2` and the octagon's initial margins is, after the
relabeling `C = R^r`, the smoothed octagon's trajectory on `[0, t_f]`, and `T = t_f`. -/
theorem octagon_identification (P : NormalPeriod) (hN : P.N = 4) (hq : ∀ k, P.factor k = √2)
    (hfwd : ∀ k, P.rep.label (k + 1) = P.rep.label k + 1)
    (h0 : margin (P.rep.label 0) (P.X 0) = octActive)
    (h1 : margin (P.rep.label 0 + 1) (P.X 0) = octThird)
    (h2 : margin (P.rep.label 0 + 2) (P.X 0) = octActive) :
    P.T = tf 1 ∧ ∃ r : ℕ, ∀ t ∈ Icc 0 P.T,
      (R ^ r)⁻¹ * P.g t * R ^ r = smoothedPolygonG 1 t ∧
        (R ^ r)⁻¹ * P.X t * R ^ r = smoothedPolygonX 1 t := by
  have hs2 := tm_s2
  have hN0 := tm_N0_pos
  have hα := tm_octActive_pos
  have hβ := tm_octThird_eq
  have h2pos : (0 : ℝ) < √2 := by positivity
  have hN' : (P.N : ℤ) = 4 := by exact_mod_cast hN
  -- the margins at the switches
  have pat : ∀ k : ℕ, k ≤ 4 → margin (P.rep.label k) (P.X (P.rep.τ k)) = octActive ∧
      margin (P.rep.label k + 1) (P.X (P.rep.τ k)) = octThird ∧
      margin (P.rep.label k + 2) (P.X (P.rep.τ k)) = octActive := by
    intro k
    induction k with
    | zero => intro _; simpa [P.rep.τ_zero] using ⟨h0, h1, h2⟩
    | succ k ih =>
      intro hk
      obtain ⟨a0, a1, a2⟩ := ih (by omega)
      have hk0 : (0 : ℤ) ≤ k := by positivity
      have hkN : (k : ℤ) < P.N := by rw [hN']; exact_mod_cast hk
      obtain ⟨p0, p1, p2⟩ := P.piece_margin hk0 hkN
      rw [P.activeMargin_eq hk0 hkN, a0, a1, hq] at p1
      rw [P.activeMargin_eq hk0 hkN, a0, show P.rep.label k - 1 = P.rep.label k + 2 by abel_nf; rfl,
        a2, hq] at p2
      rw [P.activeMargin_eq hk0 hkN, a0] at p0
      push_cast
      rw [hfwd]
      refine ⟨?_, ?_, ?_⟩
      · rw [p1, hβ]; field_simp; nlinarith
      · rw [show P.rep.label k + 1 + 1 = P.rep.label k + 2 by abel, p2, hβ]
        field_simp; nlinarith
      · rw [show P.rep.label k + 1 + 2 = P.rep.label k by abel_nf, p0]
  -- the durations: every piece lasts `t_sw`
  have htsw : tsw 1 = Real.log 2 / (2 * √(2 * √2 - 1)) := by
    rw [example7_5_smoothedOctagon.2.2.2.1, poly_sqrt8]
  have hdur : ∀ k : ℕ, k < 4 → P.rep.τ (k + 1) - P.rep.τ k = tsw 1 := by
    intro k hk
    have hk0 : (0 : ℤ) ≤ k := by positivity
    have hkN : (k : ℤ) < P.N := by rw [hN']; exact_mod_cast hk
    have hl := P.log_factor k
    rw [hq, P.activeMargin_eq hk0 hkN, (pat k hk.le).1, Real.log_sqrt (by norm_num)] at hl
    rw [htsw]
    unfold octActive at hl
    have hsq : 0 < √(2 * √2 - 1) := Real.sqrt_pos.2 hN0
    field_simp at hl ⊢
    linarith
  have hτ : ∀ k : ℕ, k ≤ 4 → P.rep.τ k = k * tsw 1 := by
    intro k
    induction k with
    | zero => intro _; simp [P.rep.τ_zero]
    | succ k ih =>
      intro hk
      have := hdur k (by omega)
      push_cast at this ⊢
      rw [ih (by omega)] at this
      linarith
  have hT : P.T = tf 1 := by
    rw [← P.rep.τ_N, show ((P.rep.N : ℕ) : ℤ) = ((4 : ℕ) : ℤ) by exact_mod_cast hN, hτ 4 le_rfl,
      tf]
    norm_num
  -- the relabeling
  obtain ⟨L, hL⟩ : ∃ L, L = P.rep.label 0 := ⟨_, rfl⟩
  obtain ⟨r, hr⟩ : ∃ r : ℕ, r = ((2 : Fin 3) - L).val := ⟨_, rfl⟩
  have hr1 : r • (1 : Fin 3) = 2 - L := by
    rw [hr]; generalize (2 : Fin 3) - L = x; fin_cases x <;> rfl
  have hlab : ∀ k : ℕ, (P.rep.label k).val = (L.val + k) % 3 := by
    intro k
    induction k with
    | zero =>
      simp only [Nat.cast_zero, ← hL, add_zero]; exact (Nat.mod_eq_of_lt L.isLt).symm
    | succ k ih =>
      push_cast
      rw [hfwd, Fin.val_add, ih]
      simp only [Fin.val_one]
      omega
  have hidx : ∀ k : ℕ, (⟨((P.rep.label k).val + r) % 3, Nat.mod_lt _ (by norm_num)⟩ : Fin 3) =
      poly_idx k := by
    intro k
    have hLlt := L.isLt
    apply Fin.ext
    simp only [poly_idx, hlab, hr, Fin.sub_def]
    simp only [Fin.val_two]
    omega
  have hC : R ^ r * R⁻¹ ^ r = 1 := poly_Rpow_mul_Rinvpow r
  set g' : ℝ → Mat2 := fun t ↦ R⁻¹ ^ r * P.g t * R ^ r with hg'
  set X' : ℝ → Mat2 := fun t ↦ R⁻¹ ^ r * P.X t * R ^ r with hX'
  have hτpos : 0 < tsw 1 := by
    rw [tsw_eq_switchTime]
    exact poly_switchTime_pos (poly_y₀_mem le_rfl).1 (poly_y₀_mem le_rfl).2
  -- the control agrees almost everywhere with the octagon's control
  have hae : ∀ᵐ t, t ∈ Ioo 0 (tf 1) →
      R⁻¹ ^ r * (controlP (P.u t) (P.X t) * P.X t - P.X t * controlP (P.u t) (P.X t)) * R ^ r =
        controlP (polygonControl 1 t) (X' t) * X' t - X' t * controlP (polygonControl 1 t) (X' t) := by
    have hpieces : ∀ᵐ t, ∀ k : Fin 4, t ∈ Ioo (P.rep.τ (k : ℕ)) (P.rep.τ ((k : ℕ) + 1)) →
        P.u t = vertex (P.rep.label (k : ℕ)) := by
      rw [ae_all_iff]
      intro k
      have := P.ae_eq_vertex (k := (k : ℕ)) (by positivity) (by rw [hN']; exact_mod_cast k.isLt)
      simpa using this
    have hnull : ∀ᵐ t, t ∉ range fun n : ℕ ↦ (n : ℝ) * tsw 1 :=
      (countable_range _).ae_notMem volume
    filter_upwards [hpieces, hnull] with t ht htn htI
    obtain ⟨hk1, hk2⟩ := poly_floor_mem hτpos htI.1.le
    set k := ⌊t / tsw 1⌋₊ with hk
    have hk1' : (k : ℝ) * tsw 1 < t := lt_of_le_of_ne hk1 fun h ↦ htn ⟨k, h⟩
    have hk4 : k < 4 := by
      have : t < 4 * tsw 1 := by
        have := htI.2; rw [tf] at this; norm_num at this; linarith
      by_contra hcon
      have : (4 : ℝ) * tsw 1 ≤ k * tsw 1 := by
        apply mul_le_mul_of_nonneg_right _ hτpos.le; exact_mod_cast not_lt.1 hcon
      linarith
    have hu := ht ⟨k, hk4⟩ (by
      simp only
      have e := hτ (k + 1) (by omega)
      push_cast at e
      rw [hτ k hk4.le, e]
      exact ⟨hk1', hk2⟩)
    simp only at hu
    rw [hu, polygonControl_eq, poly_polygonControlAt_eq, ← hk, poly_conj_bracket hC,
      poly_controlP_conj hC (poly_conj_pow_vertex r _), hidx]
  -- the conjugated trajectory is a state trajectory with the octagon's control
  have hst : IsStateTrajectory (tf 1) (polygonControl 1) g' X' := by
    obtain ⟨-, -, -, hdetst, hgI, hXI⟩ := P.isStateTrajectory
    rw [hT] at hdetst hgI hXI
    refine ⟨hT ▸ P.T_pos, by rw [polygonControl_eq]; exact poly_measurable_polygonControlAt _,
      fun t _ ↦ by rw [polygonControl_eq, poly_polygonControlAt_eq]; exact poly_vertex_mem _,
      fun t ht ↦ ⟨by simp only [hg']; rw [poly_det_conj hC, (hdetst t ht).1],
        poly_isStarState_conj_pow r (hdetst t ht).2⟩, ?_, ?_⟩
    · have h := isIntegralCurve_conj hgI (R⁻¹ ^ r) (R ^ r)
      refine poly_isIntegralCurve_congr h (hT ▸ P.T_pos.le) fun t _ ↦ ?_
      simp only [hg', hX']
      rw [poly_conj_mul hC]
    · exact isIntegralCurve_congr_ae (isIntegralCurve_conj hXI (R⁻¹ ^ r) (R ^ r))
        (hT ▸ P.T_pos.le) hae
  have hg0 : g' 0 = 1 := by
    simp only [hg', P.g_zero, Matrix.mul_one, poly_Rinvpow_mul_Rpow]
  have hX0 : X' 0 = Φ 0 (y₀ 1) := by
    have hst0 := P.isStarState ⟨le_rfl, P.T_pos.le⟩
    have hy : 0 < y₀ 1 := poly_y0_pos (poly_y₀_mem le_rfl).1
    have h3 : (0 : ℝ) < √3 := by positivity
    have hy3 : 3 * y₀ 1 ^ 2 = 2 * √2 - 1 := by rw [poly_three_y₀_one_sq, poly_sqrt8]
    have hsq : √(2 * √2 - 1) = √3 * y₀ 1 := by
      rw [← hy3, show 3 * y₀ 1 ^ 2 = (√3 * y₀ 1) ^ 2 by
        rw [mul_pow, Real.sq_sqrt (by norm_num)], Real.sqrt_sq (by positivity)]
    have hs3 : √3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
    refine eq_of_margin_eq (by simp only [hX']; rw [poly_trace_conj hC, hst0.1])
      (by simp [Φ, Matrix.trace_fin_two]) fun j ↦ ?_
    simp only [hX']
    rw [margin_conj_pow r (P.X 0) j, hr1]
    rcases (show j = 0 ∨ j = 1 ∨ j = 2 by fin_cases j <;> simp) with rfl | rfl | rfl
    · rw [tm_f0 L, hL, h1, margin_zero_apply,
        octThird, hsq]
      simp [Φ]
      field_simp
      nlinarith [hy3]
    · rw [tm_f1 L, hL, h2, margin_one_apply,
        octActive, hsq]
      simp [Φ]
      field_simp
    · rw [tm_f2 L, hL, h0, margin_two_apply, octActive, hsq]
      simp [Φ]
      field_simp
  have huniq := polygon_trajectory_unique 1 le_rfl g' X' hst hg0 hX0
  have hred : ∀ t ∈ Icc 0 (tf 1), oct_red (6 * tf 1) t = t := by
    intro t ht
    have htf : 0 < tf 1 := hT ▸ P.T_pos
    simp only [oct_red]
    rw [Int.floor_eq_zero_iff.2 ⟨div_nonneg ht.1 (by linarith), (div_lt_one (by linarith)).2
      (by linarith [ht.2])⟩]
    simp
  refine ⟨hT, r, fun t ht ↦ ?_⟩
  rw [hT] at ht
  rw [Rpow_inv, smoothedPolygonG, smoothedPolygonX, hred t ht]
  exact huniq t ht


end Term

end SmoothedOctagon
