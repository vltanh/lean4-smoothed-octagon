module

public import SmoothedOctagon.Exclusion.Mixed.Defect.Angle
public import SmoothedOctagon.Exclusion.Mixed.Defect.Algebra

/-!
# Case M2, smaller-short window: the frames of a normal period in rotated triangular coordinates

The costate, the state and the frame increments of a normal period at a switch, read in the
triangular coordinates `Y ↦ C Y C⁻¹` (`Term.triC`) rotated to the label `i` of the piece
(`df_W i = R^i C`, `df_Wi i = C⁻¹ R^{-i}`, `R = Term.triR`): there a traceless matrix is
`triY` of its margins in the order `i, i + 1, i - 1`, the tangent factors of the labels `i`, `i + 1`
are `triFactor 0`, `triFactor 1`, `J` is `df_Jt = triY (2/√3, 2/√3, 2/√3)`, and the multiplier
`𝒰 = -(1/√12) X Λ₁ X` at the switch `k` is the frame `Mloc k` of the costate cycle.

## Main API

* `df_zc_prod`: `4 z(B M) conj z(B) = (tr M + tr(J Λ̂ M)) + i (tr(Λ̂ M) - tr(J M))` for
  `det B = 1`, `Λ̂ = -B⁻¹ J B`.
* `df_Jt`; `df_W`, `df_Wi`, `df_W_conj_*`, `df_trace_conj`, `df_rot_*`: the rotated triangular
  coordinates.
* `NormalPeriod.df_U` (`df_U_trace`), `df_mu`, `df_Mloc`, `df_Λ`: the multiplier at a switch
  `0 ≤ k < N`.
* `NormalPeriod.df_m_eq`, `df_piece_frame`: switch margins and frame increments.
-/

@[expose] public section

namespace SmoothedOctagon

open SmoothedPolygons Real Set Reduction

/-- `J` in triangular coordinates: `triY (2/√3, 2/√3, 2/√3)`. -/
noncomputable def df_Jt : Mat2 := triY fun _ ↦ 2 / √3

/-- **The endpoint product**: for `det B = 1` and
`Λ̂ = -B⁻¹ J B`, `4 z(BM) conj z(B) = (tr M + tr(J Λ̂ M)) + i (tr(Λ̂ M) - tr(J M))`. -/
theorem df_zc_prod {Bm M : Mat2} (hB : Bm.det = 1) :
    4 * (clr_zc (Bm * M) * (starRingEnd ℂ) (clr_zc Bm)).re =
        M.trace + (J * (-(Bm.adjugate * J * Bm)) * M).trace ∧
    4 * (clr_zc (Bm * M) * (starRingEnd ℂ) (clr_zc Bm)).im =
        ((-(Bm.adjugate * J * Bm)) * M).trace - (J * M).trace := by
  rw [Matrix.det_fin_two] at hB
  simp only [Complex.mul_re, Complex.mul_im, Complex.conj_re, Complex.conj_im, clr_zc_re,
    clr_zc_im, Matrix.trace_fin_two, Matrix.mul_apply, Fin.sum_univ_two, Matrix.adjugate_fin_two,
    Matrix.neg_apply, J, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.empty_val', Matrix.cons_val_fin_one]
  constructor
  · linear_combination (M 0 0 + M 1 1) * hB
  · linear_combination (M 1 0 - M 0 1) * hB

/-! ### Rotated triangular coordinates -/

/-- `R^i C`. -/
noncomputable def df_W (i : Fin 3) : Mat2 := elRp i * Term.triC

/-- `C⁻¹ R^{-i}`. -/
noncomputable def df_Wi (i : Fin 3) : Mat2 := Term.triCinv * elRm i

theorem df_Wi_W (i : Fin 3) : df_Wi i * df_W i = 1 := by
  rw [df_Wi, df_W, Matrix.mul_assoc, ← Matrix.mul_assoc (elRm i), elRm_mul_elRp, Matrix.one_mul,
    Term.triCinv_mul_triC]

theorem df_W_Wi (i : Fin 3) : df_W i * df_Wi i = 1 := by
  rw [df_Wi, df_W, Matrix.mul_assoc, ← Matrix.mul_assoc Term.triC, Term.triC_mul_triCinv,
    Matrix.one_mul, elRp_mul_elRm]

theorem df_W_conj_mul (i : Fin 3) (X Y : Mat2) :
    df_W i * (X * Y) * df_Wi i = (df_W i * X * df_Wi i) * (df_W i * Y * df_Wi i) := by
  have h := df_Wi_W i
  calc df_W i * (X * Y) * df_Wi i = df_W i * X * (df_Wi i * df_W i) * Y * df_Wi i := by
        rw [h]; simp only [Matrix.mul_one, Matrix.mul_assoc]
    _ = _ := by simp only [Matrix.mul_assoc]

theorem df_W_conj_neg (i : Fin 3) (X : Mat2) :
    df_W i * (-X) * df_Wi i = -(df_W i * X * df_Wi i) := by
  simp only [Matrix.mul_neg, Matrix.neg_mul]

theorem df_W_conj_smul (i : Fin 3) (c : ℝ) (X : Mat2) :
    df_W i * (c • X) * df_Wi i = c • (df_W i * X * df_Wi i) := by
  simp only [Matrix.mul_smul, Matrix.smul_mul]

theorem df_trace_conj (i : Fin 3) (X : Mat2) : (df_W i * X * df_Wi i).trace = X.trace := by
  rw [Matrix.trace_mul_comm, ← Matrix.mul_assoc, df_Wi_W, Matrix.one_mul]

theorem df_rot_triY (i : Fin 3) (p : Fin 3 → ℝ) :
    elRp i * triY p * elRm i = triY (fun j ↦ p (j + i)) := by
  fin_cases i <;> ext a b <;> fin_cases a <;> fin_cases b <;>
    simp [elRp, elRm, pow_succ, Term.triR, Term.triRinv, triY, Matrix.mul_apply,
      Fin.sum_univ_two] <;> ring_nf

theorem df_rot_fac0 (i : Fin 3) (q : ℝ) :
    elRp i * Term.triFactor i q * elRm i = Term.triFactor 0 q := by
  fin_cases i <;> ext a b <;> fin_cases a <;> fin_cases b <;>
    simp [elRp, elRm, pow_succ, Term.triR, Term.triRinv, Term.triFactor, Matrix.mul_apply,
      Fin.sum_univ_two]

theorem df_rot_fac1 (i : Fin 3) (q : ℝ) :
    elRp i * Term.triFactor (i + 1) q * elRm i = Term.triFactor 1 q := by
  fin_cases i <;> ext a b <;> fin_cases a <;> fin_cases b <;>
    simp [elRp, elRm, pow_succ, Term.triR, Term.triRinv, Term.triFactor, Matrix.mul_apply,
      Fin.sum_univ_two] <;> ring

/-- A traceless matrix in rotated triangular coordinates is `triY` of its rotated margins. -/
theorem df_W_conj_traceless (i : Fin 3) {Y : Mat2} (h : Y.trace = 0) :
    df_W i * Y * df_Wi i = triY (fun j ↦ margin (j + i) Y) := by
  rw [df_W, df_Wi, show elRp i * Term.triC * Y * (Term.triCinv * elRm i) =
    elRp i * (Term.triC * Y * Term.triCinv) * elRm i by simp only [Matrix.mul_assoc],
    ← el_triY_margin h, df_rot_triY]

theorem df_W_conj_J (i : Fin 3) : df_W i * J * df_Wi i = df_Jt := by
  have hJ : J.trace = 0 := by simp [J, Matrix.trace_fin_two]
  rw [df_W_conj_traceless i hJ, df_Jt]
  congr 1; funext j; exact NormalPeriod.el_margin_J _

theorem df_W_conj_tangent0 (i : Fin 3) {q : ℝ} (hq : q ≠ 0) :
    df_W i * tangentFactor i q * df_Wi i = Term.triFactor 0 q := by
  rw [df_W, df_Wi, show elRp i * Term.triC * tangentFactor i q * (Term.triCinv * elRm i) =
    elRp i * (Term.triC * tangentFactor i q * Term.triCinv) * elRm i by
      simp only [Matrix.mul_assoc], Term.triC_conj_tangentFactor i hq, df_rot_fac0]

theorem df_W_conj_tangent1 (i : Fin 3) {q : ℝ} (hq : q ≠ 0) :
    df_W i * tangentFactor (i + 1) q * df_Wi i = Term.triFactor 1 q := by
  rw [df_W, df_Wi, show elRp i * Term.triC * tangentFactor (i + 1) q * (Term.triCinv * elRm i) =
    elRp i * (Term.triC * tangentFactor (i + 1) q * Term.triCinv) * elRm i by
      simp only [Matrix.mul_assoc], Term.triC_conj_tangentFactor _ hq, df_rot_fac1]

/-! ### The multiplier, the switch margins and the frame increments of a normal period -/

namespace NormalPeriod

variable (P : NormalPeriod)

private lemma df_s3pos : (0 : ℝ) < √3 := by positivity
private lemma df_s3 : √3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)

/-- The local normal multiplier `𝒰(t) = -(1/√12) X(t) Λ₁(t) X(t)`. -/
noncomputable def df_U (t : ℝ) : Mat2 := -(1 / √12) • (P.X t * P.Λ₁ t * P.X t)

theorem df_U_trace {t : ℝ} (ht : t ∈ Icc 0 P.T) : (P.df_U t).trace = 0 := by
  have hX := P.isStarState ht
  have hΛ := (P.extremal.2.2.2.2.2.2.2.1 t ht).1
  rw [df_U, Matrix.trace_smul, cst_mul_mul_self hX.1 hX.2.1 hΛ, Matrix.trace_add,
    Matrix.trace_smul, hX.1, hΛ]
  simp

/-- `Λ₁ = -√12 X 𝒰 X`. -/
theorem df_Λ {t : ℝ} (ht : t ∈ Icc 0 P.T) :
    P.Λ₁ t = -√12 • (P.X t * P.df_U t * P.X t) := by
  have hX := P.isStarState ht
  have hXX := mul_self_eq_neg_one _ hX.1 hX.2.1
  have h12 : (0 : ℝ) < √12 := by positivity
  rw [df_U, Matrix.mul_smul, Matrix.smul_mul, smul_smul]
  have e : P.X t * (P.X t * P.Λ₁ t * P.X t) * P.X t = P.Λ₁ t := by
    rw [show P.X t * (P.X t * P.Λ₁ t * P.X t) * P.X t =
      (P.X t * P.X t) * P.Λ₁ t * (P.X t * P.X t) by simp only [Matrix.mul_assoc], hXX]
    simp
  rw [e, show -√12 * -(1 / √12) = (1 : ℝ) by field_simp, one_smul]

/-- The switch margins of the costate cycle at a switch `0 ≤ k < N` are those of `X(τ_k)`. -/
theorem df_m_eq {k : ℤ} (hk0 : 0 ≤ k) (hkN : k < P.N) (j : Fin 3) :
    P.costateCycle.m k j = margin j (P.X (P.rep.τ k)) := by
  have hmod : k % P.N = k := Int.emod_eq_of_lt hk0 hkN
  have hcs : P.cutShift k = 0 := by simp [cutShift, hmod]
  rw [costateCycle_m, termMargin_eq_cut, hcs, sub_zero, hmod]

/-- **The multiplier at a switch** (`mu_zero` at the switch `0 ≤ k < N`): `μ_k = p(𝒰(τ_k))`. -/
theorem df_mu {k : ℤ} (hk0 : 0 ≤ k) (hkN : k < P.N) (j : Fin 3) :
    P.costateCycle.mu k j = margin j (P.df_U (P.rep.τ k)) := by
  have hT : P.rep.τ k ∈ Icc 0 P.T := ⟨P.rep.τ_nonneg hk0, P.rep.τ_le_T hkN.le⟩
  have hX := P.isStarState hT
  have hmod : k % P.N = k := Int.emod_eq_of_lt hk0 hkN
  have hcs : P.cutShift k = 0 := by simp [cutShift, hmod]
  have hm : ∀ l, P.costateCycle.m k l = margin l (P.X (P.rep.τ k)) := P.df_m_eq hk0 hkN
  have hα : P.costateCycle.α k j =
      margin j (costateA (P.Λ₁ (P.rep.τ k)) (P.X (P.rep.τ k))) := by
    show P.cutAlpha k j = _
    simp only [cutAlpha, hcs, sub_zero, hmod, costateAlpha]
  have hXJX := cst_mul_mul_self hX.1 hX.2.1 cst_trace_J
  have hA : costateA (P.Λ₁ (P.rep.τ k)) (P.X (P.rep.τ k)) =
      P.X (P.rep.τ k) * P.Λ₁ (P.rep.τ k) * P.X (P.rep.τ k) +
        (3 / 2 : ℝ) • (P.X (P.rep.τ k) * J * P.X (P.rep.τ k)) := by
    simp only [costateA, costateL, Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul,
      Matrix.smul_mul]
  have hsum := sum_margin (P.X (P.rep.τ k))
  have h3 := df_s3pos
  have h12 : √12 = 2 * √3 := by
    rw [show (12 : ℝ) = 2 ^ 2 * 3 by norm_num, Real.sqrt_mul (by norm_num),
      Real.sqrt_sq (by norm_num)]
  simp only [CostateCycle.mu, hα, hm, df_U, cst_margin_smul]
  rw [hA, hXJX]
  simp only [cst_margin_add, cst_margin_smul, el_margin_J]
  have ht : traceForm J (P.X (P.rep.τ k)) =
      -(margin 0 (P.X (P.rep.τ k)) + margin 1 (P.X (P.rep.τ k)) +
        margin 2 (P.X (P.rep.τ k))) / √3 := by
    rw [hsum]; field_simp
  rw [ht, h12]
  field_simp
  ring_nf
  simp only [df_s3]
  ring_nf

/-- **The frame `Mloc k` is the multiplier in rotated triangular coordinates.** -/
theorem df_Mloc {k : ℤ} (hk0 : 0 ≤ k) (hkN : k < P.N) :
    P.costateCycle.Mloc k =
      df_W (P.rep.label k) * P.df_U (P.rep.τ k) * df_Wi (P.rep.label k) := by
  have hT : P.rep.τ k ∈ Icc 0 P.T := ⟨P.rep.τ_nonneg hk0, P.rep.τ_le_T hkN.le⟩
  rw [df_W_conj_traceless _ (P.df_U_trace hT), CostateCycle.Mloc]
  congr 1; funext j
  rw [P.df_mu hk0 hkN, costateCycle_lab]

/-- **The frame increment of piece `k`**, `0 ≤ k < N`:
`g(τ_k)⁻¹ g(τ_{k+1}) = -X(τ_k) T_{i_k}(q_k) X(τ_{k+1})`. -/
theorem df_piece_frame {k : ℤ} (hk0 : 0 ≤ k) (hkN : k < P.N) :
    (P.g (P.rep.τ k))⁻¹ * P.g (P.rep.τ (k + 1)) =
      -(P.X (P.rep.τ k) * tangentFactor (P.rep.label k) (P.factor k) *
        P.X (P.rep.τ (k + 1))) := by
  obtain ⟨h0, h01, h1⟩ := P.rep.piece_subset hk0 hkN
  have hT1 : P.rep.τ (k + 1) ∈ Icc 0 P.T := ⟨h0.trans h01, h1⟩
  have hT0 : P.rep.τ k ∈ Icc 0 P.T := ⟨h0, h01.trans h1⟩
  have hX1 := P.isStarState hT1
  have hXX := mul_self_eq_neg_one _ hX1.1 hX1.2.1
  have hdg : (P.g (P.rep.τ k)).det = 1 := (P.isStateTrajectory.2.2.2.1 _ hT0).1
  have hinv : (P.g (P.rep.τ k))⁻¹ * P.g (P.rep.τ k) = 1 :=
    Matrix.nonsing_inv_mul _ (by rw [hdg]; exact isUnit_one)
  have ht := P.piece_tangent hk0 hkN
  have e : P.g (P.rep.τ (k + 1)) =
      -(P.g (P.rep.τ k) * P.X (P.rep.τ k) * tangentFactor (P.rep.label k) (P.factor k) *
        P.X (P.rep.τ (k + 1))) := by
    have := congrArg (· * P.X (P.rep.τ (k + 1))) ht
    simp only [Matrix.mul_assoc, hXX] at this
    rw [← Matrix.mul_assoc, Matrix.mul_neg, Matrix.mul_one] at this
    rw [← neg_neg (P.g (P.rep.τ (k + 1))), this]
    simp only [Matrix.mul_assoc]
  rw [e, Matrix.mul_neg]
  simp only [← Matrix.mul_assoc, hinv, Matrix.one_mul]

end NormalPeriod

end SmoothedOctagon
