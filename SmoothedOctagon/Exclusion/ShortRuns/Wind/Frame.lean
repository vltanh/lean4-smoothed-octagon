module

public import SmoothedOctagon.Exclusion.ShortRun.Wind.Kappa

/-!
# The switch vectors in the physical frame

The algebraic switch vectors of a normal period, `y_{c-1} = P_c (incoming)`,
`y_c = P_c (outgoing)` (`CostateCycle.pre`, triangular coordinates), are, up to a common sign and
positive factors, `K V(τ_c) b` with the fixed matrix `K = R^{i_0} C (-X(0))` (`wd_K`), the physical
tangent frame `V = g X` at the switch time, and explicit base vectors `b` depending only on the
label of the piece (`wd_pre_phys`, `wd_bin`, `wd_bout`). With a factor `Q` of the costate metric
`S = Qᵀ Q` (`det Q < 0`), the angle `arccos(e_c/√(d_{c-1} d_c))` at a reverse centre is the
continuous angle increment `π/3 + κ(b_out) - κ(b_in)` of the canonical angle `κ` of
`Wind/Kappa.lean` (`wd_centre`).

Along a vertex piece the base vectors are eigenvectors of the tangent factor
(`wd_eig_self`, `wd_eig_pred`), so `κ` is constant along the piece (`wd_track_piece`,
`wd_track_range`); at the seam it jumps by the exact `π/3` of the frame (`wd_seam`).

## Main API

* `wd_bin`, `wd_bout`, `wd_bout_eq_R`, `wd_arg_bout_bin`, `wd_det_bin_bout`, `wd_bout_chain`,
  `wd_bout_seam`, `wd_IsEig`, `wd_eig_self`, `wd_eig_pred`.
* `wd_prod_pre`, `wd_K`, `wd_det_K`, `wd_pre_phys`.
* `wd_arccos_eq_arg`, `wd_centre`.
* `wd_good`, `wd_track_piece`, `wd_track_range`, `wd_seam`.
-/

@[expose] public section

namespace SmoothedOctagon

open Complex Set PlaneCurve SmoothedPolygons
open scoped Matrix

private lemma wd_s3 : √3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
private lemma wd_s3pos : (0 : ℝ) < √3 := by positivity

/-! ### Base vectors -/

/-- The incoming base vector of a reverse centre with label `L` (physical coordinates). -/
noncomputable def wd_bin (L : Fin 3) : Fin 2 → ℝ :=
  ![![-(1 / (2 * √3)), -(1 / 2)], ![-(1 / √3), 0], ![-(1 / (2 * √3)), 1 / 2]] L

/-- The outgoing base vector of a reverse centre with label `L` (physical coordinates). -/
noncomputable def wd_bout (L : Fin 3) : Fin 2 → ℝ :=
  ![![1 / (2 * √3), -(1 / 2)], ![-(1 / (2 * √3)), -(1 / 2)], ![-(1 / √3), 0]] L

theorem wd_triCinv_in (L : Fin 3) : Term.triCinv *ᵥ (elRm L *ᵥ ![-1, 0]) = wd_bin L := by
  have h := wd_s3pos
  fin_cases L <;> ext i <;> fin_cases i <;>
    simp [wd_bin, elRm, Term.triCinv, Term.triRinv, pow_succ, Matrix.mulVec, dotProduct,
      Fin.sum_univ_two, Matrix.mul_apply] <;> field_simp <;> ring

theorem wd_triCinv_out (L : Fin 3) : Term.triCinv *ᵥ (elRm L *ᵥ ![0, 1]) = wd_bout L := by
  have h := wd_s3pos
  fin_cases L <;> ext i <;> fin_cases i <;>
    simp [wd_bout, elRm, Term.triCinv, Term.triRinv, pow_succ, Matrix.mulVec, dotProduct,
      Fin.sum_univ_two, Matrix.mul_apply] <;> field_simp <;> ring

/-- The rotation `R` multiplies by `e^{iπ/3}`. -/
theorem wd_toC_R (v : Fin 2 → ℝ) :
    sc_toC (R *ᵥ v) = (1 / 2 + (√3 / 2 : ℝ) * I) * sc_toC v := by
  apply Complex.ext <;> simp [R, sc_toC, Matrix.mulVec, dotProduct, Fin.sum_univ_two] <;> ring

theorem wd_toC_Rinv (v : Fin 2 → ℝ) :
    sc_toC (R⁻¹ *ᵥ v) = (1 / 2 - (√3 / 2 : ℝ) * I) * sc_toC v := by
  rw [poly_R_inv]
  apply Complex.ext <;> simp [sc_toC, Matrix.mulVec, dotProduct, Fin.sum_univ_two] <;> ring

theorem wd_rot_mul : (1 / 2 + (√3 / 2 : ℝ) * I) * (1 / 2 - (√3 / 2 : ℝ) * I) = 1 := by
  have h : ((√3 / 2 : ℝ) : ℂ) ^ 2 = 3 / 4 := by
    rw [← ofReal_pow, div_pow, wd_s3]; push_cast; ring
  linear_combination h - ((√3 / 2 : ℝ) : ℂ) ^ 2 * Complex.I_sq

theorem wd_rot_ne : (1 / 2 + (√3 / 2 : ℝ) * I) ≠ 0 := by
  intro h; have := congrArg Complex.re h; simp at this

theorem wd_scb_zc_R : Reduction.scb_zc R = 1 / 2 + (√3 / 2 : ℝ) * I := by
  apply Complex.ext <;> simp [Reduction.scb_zc, R]

theorem wd_scb_zc_one : Reduction.scb_zc 1 = 1 := by
  apply Complex.ext <;> simp [Reduction.scb_zc]

theorem wd_bout_eq_R (L : Fin 3) : wd_bout L = R *ᵥ wd_bin L := by
  have h := wd_s3pos
  have h3 := wd_s3
  fin_cases L <;> ext i <;> fin_cases i <;>
    simp [wd_bin, wd_bout, R, Matrix.mulVec, dotProduct, Fin.sum_univ_two] <;> field_simp <;>
    nlinarith [h3]

theorem wd_bin_ne (L : Fin 3) : wd_bin L ≠ 0 := by
  have h := wd_s3pos
  intro h0
  have h1 := congrFun h0 0
  fin_cases L <;> simp [wd_bin] at h1

theorem wd_bout_ne (L : Fin 3) : wd_bout L ≠ 0 := by
  rw [wd_bout_eq_R]
  exact wd_mulVec_ne (by rw [poly_det_R]; norm_num) (wd_bin_ne L)

theorem wd_arg_bout_bin (L : Fin 3) :
    arg (sc_toC (wd_bout L) / sc_toC (wd_bin L)) = Real.pi / 3 := by
  rw [wd_bout_eq_R, wd_toC_R, mul_div_assoc, div_self (wd_toC_ne (wd_bin_ne L)), mul_one]
  have e : (1 / 2 + (√3 / 2 : ℝ) * I : ℂ) =
      Complex.cos ((Real.pi / 3 : ℝ) : ℂ) + Complex.sin ((Real.pi / 3 : ℝ) : ℂ) * I := by
    rw [← Complex.ofReal_cos, ← Complex.ofReal_sin, Real.cos_pi_div_three,
      Real.sin_pi_div_three]
    push_cast; ring
  rw [e, arg_cos_add_sin_mul_I ⟨by linarith [Real.pi_pos], by linarith [Real.pi_pos]⟩]

theorem wd_det_bin_bout (L : Fin 3) : elDet (wd_bin L) (wd_bout L) ≠ 0 := by
  have h := wd_s3pos
  have h3 := wd_s3
  fin_cases L <;> simp [elDet, wd_bin, wd_bout] <;> field_simp <;> nlinarith

theorem wd_bout_chain (L : Fin 3) : wd_bout L = wd_bin (L - 1) ∨ wd_bout L = -wd_bin (L - 1) := by
  fin_cases L
  · right; ext i; fin_cases i <;> simp [wd_bin, wd_bout]
  · left; ext i; fin_cases i <;> simp [wd_bin, wd_bout]
  · left; ext i; fin_cases i <;> simp [wd_bin, wd_bout]

theorem wd_bout_seam (L : Fin 3) :
    R *ᵥ wd_bout (L + 1) = wd_bout L ∨ R *ᵥ wd_bout (L + 1) = -wd_bout L := by
  have h := wd_s3pos
  have h3 := wd_s3
  fin_cases L
  · left; ext i; fin_cases i <;>
      simp [wd_bout, R, Matrix.mulVec, dotProduct, Fin.sum_univ_two] <;> field_simp <;> nlinarith
  · left; ext i; fin_cases i <;>
      simp [wd_bout, R, Matrix.mulVec, dotProduct, Fin.sum_univ_two] <;> field_simp
  · right; ext i; fin_cases i <;>
      simp [wd_bout, R, Matrix.mulVec, dotProduct, Fin.sum_univ_two] <;> field_simp <;> nlinarith

/-- `v` is an eigenvector with positive eigenvalue of every tangent factor `T_i(w)`, `w > 0`. -/
def wd_IsEig (i : Fin 3) (v : Fin 2 → ℝ) : Prop :=
  ∀ w : ℝ, 0 < w → ∃ c : ℝ, 0 < c ∧ tangentFactor i w *ᵥ v = c • v

theorem wd_eig_self (L : Fin 3) : wd_IsEig L (wd_bout L) := by
  intro w hw
  have h := wd_s3pos
  have h3 := wd_s3
  have hw0 := hw.ne'
  refine ⟨w⁻¹, inv_pos.2 hw, ?_⟩
  fin_cases L
  · change tangentFactor 0 w *ᵥ wd_bout 0 = w⁻¹ • wd_bout 0
    rw [tangentFactor_zero_eq hw0]
    ext i; fin_cases i <;> simp [wd_bout, Matrix.mulVec, dotProduct, Fin.sum_univ_two] <;>
      field_simp <;> ring_nf
  · change tangentFactor 1 w *ᵥ wd_bout 1 = w⁻¹ • wd_bout 1
    rw [tangentFactor_one_eq hw0]
    ext i; fin_cases i <;> simp [wd_bout, Matrix.mulVec, dotProduct, Fin.sum_univ_two] <;>
      field_simp <;> ring_nf
  · change tangentFactor 2 w *ᵥ wd_bout 2 = w⁻¹ • wd_bout 2
    rw [tangentFactor_two_eq hw0]
    ext i; fin_cases i <;> simp [wd_bout, Matrix.mulVec, dotProduct, Fin.sum_univ_two]

theorem wd_eig_pred (L : Fin 3) : wd_IsEig (L - 1) (wd_bout L) := by
  intro w hw
  have h := wd_s3pos
  have h3 := wd_s3
  have hw0 := hw.ne'
  refine ⟨w, hw, ?_⟩
  fin_cases L
  · change tangentFactor 2 w *ᵥ wd_bout 0 = w • wd_bout 0
    rw [tangentFactor_two_eq hw0]
    ext i; fin_cases i <;> simp [wd_bout, Matrix.mulVec, dotProduct, Fin.sum_univ_two] <;>
      field_simp <;> ring_nf
  · change tangentFactor 0 w *ᵥ wd_bout 1 = w • wd_bout 1
    rw [tangentFactor_zero_eq hw0]
    ext i; fin_cases i <;> simp [wd_bout, Matrix.mulVec, dotProduct, Fin.sum_univ_two] <;>
      field_simp <;> ring_nf
  · change tangentFactor 1 w *ᵥ wd_bout 2 = w • wd_bout 2
    rw [tangentFactor_one_eq hw0]
    ext i; fin_cases i <;> simp [wd_bout, Matrix.mulVec, dotProduct, Fin.sum_univ_two]

/-! ### The prefix frames in the physical frame -/

/-- `∏_{j<n} T_{i_j}(q_j) = ± R^{-i_0} P_n R^{i_n}` (triangular coordinates). -/
theorem wd_prod_pre {N : ℕ} (C : CostateCycle N) (n : ℕ) : ∃ s : ℝ, (s = 1 ∨ s = -1) ∧
    ((List.range n).map fun j : ℕ ↦ Term.triFactor (C.lab j) (C.q j)).prod =
      s • (elRm (C.lab 0) * C.pre n * elRp (C.lab n)) := by
  have hpm : ∀ s : ℝ, (s = 1 ∨ s = -1) → ∀ s' : ℝ, (s' = 1 ∨ s' = -1) →
      (s * s' = 1 ∨ s * s' = -1) := by
    rintro s (rfl | rfl) s' (rfl | rfl) <;> norm_num
  have hstep : ∀ n : ℕ, ∃ s : ℝ, (s = 1 ∨ s = -1) ∧
      C.pre n * Term.triFactor 0 (C.q n) * elRp (C.lab n) =
        s • (C.pre (n + 1) * elRp (C.lab ((n + 1 : ℕ) : ℤ))) := by
    intro n
    simp only [CostateCycle.pre, CostateCycle.Amat, Nat.cast_succ]
    rcases C.lab_cases n with h | h
    · simp only [h, ↓reduceIte]
      rcases elRp_fwd (C.lab n) with h' | h'
      · exact ⟨1, Or.inl rfl, by rw [h', one_smul]; try simp only [Matrix.mul_assoc]⟩
      · exact ⟨-1, Or.inr rfl, by rw [h', neg_smul, one_smul]; try simp only [Matrix.mul_assoc,
          Matrix.mul_neg]⟩
    · have hne : ¬ (C.lab n - 1 = C.lab n + 1) := by
        generalize C.lab n = i; revert i; decide
      simp only [h, hne, ↓reduceIte]
      rcases elRp_rev (C.lab n) with h' | h'
      · exact ⟨1, Or.inl rfl, by rw [h', one_smul]; try simp only [Matrix.mul_assoc]⟩
      · exact ⟨-1, Or.inr rfl, by rw [h', neg_smul, one_smul]; try simp only [Matrix.mul_assoc,
          Matrix.mul_neg]⟩
  induction n with
  | zero => exact ⟨1, Or.inl rfl, by simp [CostateCycle.pre, elRm_mul_elRp]⟩
  | succ n ih =>
    obtain ⟨s, hs, hF⟩ := ih
    obtain ⟨s', hs', hP⟩ := hstep n
    refine ⟨s * s', hpm s hs s' hs', ?_⟩
    rw [List.prod_range_succ, hF, triFactor_eq_conj]
    have e : elRm (C.lab 0) * C.pre n * elRp (C.lab n) *
        (elRm (C.lab n) * Term.triFactor 0 (C.q n) * elRp (C.lab n)) =
        elRm (C.lab 0) * (C.pre n * Term.triFactor 0 (C.q n) * elRp (C.lab n)) := by
      simp only [Matrix.mul_assoc]
      rw [← Matrix.mul_assoc (elRp (C.lab n)), elRp_mul_elRm, Matrix.one_mul]
    rw [Matrix.smul_mul, e, hP, Matrix.mul_smul, smul_smul]
    try simp only [Matrix.mul_assoc]

/-- The fixed matrix `K = R^{i_0} C (-X(0))` (triangular rotation, change of coordinates and the
initial state). -/
noncomputable def wd_K (P : NormalPeriod) : Mat2 :=
  elRp (P.rep.label 0) * Term.triC * -P.X 0

theorem wd_det_elRp (i : Fin 3) : (elRp i).det = 1 := by
  fin_cases i <;> simp [elRp, pow_succ, Term.triR, Matrix.det_fin_two]

theorem wd_det_K (P : NormalPeriod) : (wd_K P).det = -(2 * √3) := by
  have hX := P.isStarState (t := 0) ⟨le_rfl, P.T_pos.le⟩
  rw [wd_K, Matrix.det_mul, Matrix.det_mul, wd_det_elRp, Matrix.det_neg, hX.2.1]
  simp [Term.triC, Matrix.det_fin_two]; ring

/-- **The prefix frame in the physical frame**: `P_n = ± K V(τ_n) C⁻¹ R^{-i_n}`. -/
theorem wd_pre_phys (P : NormalPeriod) {n : ℕ} (hn : n ≤ P.N) : ∃ s : ℝ, (s = 1 ∨ s = -1) ∧
    P.costateCycle.pre n = s • (wd_K P * (P.g (P.rep.τ n) * P.X (P.rep.τ n)) *
      (Term.triCinv * elRm (P.rep.label n))) := by
  set C := P.costateCycle
  obtain ⟨s, hs, hk⟩ := wd_prod_pre C n
  have hX0 := P.isStarState (t := 0) ⟨le_rfl, P.T_pos.le⟩
  have hXX := mul_self_eq_neg_one (P.X 0) hX0.1 hX0.2.1
  -- the triangular product is the conjugated tangent product
  have hprod : ((List.range n).map fun j : ℕ ↦ Term.triFactor (C.lab j) (C.q j)).prod =
      Term.triC * P.tangentProduct n * Term.triCinv := by
    rw [NormalPeriod.tangentProduct, ← Term.prod_conj_triC]
    congr 1
    refine List.map_congr_left fun j _ ↦ ?_
    rw [Term.triC_conj_tangentFactor _ (P.factor_pos j).ne']
    rfl
  have htp : P.tangentProduct n = -P.X 0 * (P.g (P.rep.τ n) * P.X (P.rep.τ n)) := by
    rw [P.tangent_τ n hn, ← Matrix.mul_assoc, Matrix.neg_mul, hXX, neg_neg, Matrix.one_mul]
  refine ⟨s, hs, ?_⟩
  have hss : s * s = 1 := by rcases hs with rfl | rfl <;> norm_num
  have key : elRp (C.lab 0) * (Term.triC * P.tangentProduct n * Term.triCinv) *
      elRm (C.lab n) = s • C.pre n := by
    rw [← hprod, hk, Matrix.mul_smul, Matrix.smul_mul]
    congr 1
    simp only [← Matrix.mul_assoc]
    rw [elRp_mul_elRm, Matrix.one_mul, Matrix.mul_assoc, elRp_mul_elRm, Matrix.mul_one]
  have : C.pre n = s • (elRp (C.lab 0) * (Term.triC * P.tangentProduct n * Term.triCinv) *
      elRm (C.lab n)) := by
    rw [key, smul_smul, hss, one_smul]
  rw [this, htp, wd_K]
  congr 1
  simp only [Matrix.mul_assoc, Matrix.neg_mul, Matrix.mul_neg]
  rfl

/-! ### The angle at a reverse centre -/

/-- The costate angle as a principal argument: if `S = Qᵀ Q` with `det Q < 0` and
`det(a, b) < 0`, then `arccos(aᵀSb/√(aᵀSa · bᵀSb)) = arg(Q b / Q a)`. -/
theorem wd_arccos_eq_arg {S Q : Mat2} (hQ : Q.det < 0)
    (hS : ∀ x y, elQ S x y = (Q *ᵥ x) 0 * (Q *ᵥ y) 0 + (Q *ᵥ x) 1 * (Q *ᵥ y) 1)
    {a b : Fin 2 → ℝ} (hab : elDet a b < 0) :
    Real.arccos (elQ S a b / √(elQ S a a * elQ S b b)) =
      arg (sc_toC (Q *ᵥ b) / sc_toC (Q *ᵥ a)) := by
  have hdet : 0 < elDet (Q *ᵥ a) (Q *ᵥ b) := by rw [elDet_mulVec]; nlinarith
  have ha : a ≠ 0 := by rintro rfl; simp [elDet] at hab
  have hz := wd_toC_mulVec_ne hQ.ne ha
  have hb : b ≠ 0 := by rintro rfl; simp [elDet] at hab
  have hw := wd_toC_mulVec_ne hQ.ne hb
  set z := sc_toC (Q *ᵥ a)
  set w := sc_toC (Q *ᵥ b)
  have hζ : w / z ≠ 0 := div_ne_zero hw hz
  have him : 0 ≤ (w / z).im := by
    rw [Complex.div_im]
    have hn : 0 < Complex.normSq z := Complex.normSq_pos.2 hz
    have e : w.im * z.re / Complex.normSq z - w.re * z.im / Complex.normSq z =
        elDet (Q *ᵥ a) (Q *ᵥ b) / Complex.normSq z := by
      simp only [w, z, sc_toC_re, sc_toC_im, elDet]; ring
    rw [e]; exact (div_pos hdet hn).le
  have harg0 : 0 ≤ arg (w / z) := arg_nonneg_iff.2 him
  rw [← Real.arccos_cos harg0 (arg_le_pi _), cos_arg hζ]
  congr 1
  have hnz : ‖z‖ ^ 2 = elQ S a a := by
    rw [hS, ← Complex.normSq_eq_norm_sq, Complex.normSq_apply]; simp [z]
  have hnw : ‖w‖ ^ 2 = elQ S b b := by
    rw [hS, ← Complex.normSq_eq_norm_sq, Complex.normSq_apply]; simp [w]
  have hzn : 0 < ‖z‖ := norm_pos_iff.2 hz
  have hwn : 0 < ‖w‖ := norm_pos_iff.2 hw
  rw [← hnz, ← hnw, show ‖z‖ ^ 2 * ‖w‖ ^ 2 = (‖z‖ * ‖w‖) ^ 2 by ring,
    Real.sqrt_sq (by positivity), norm_div, Complex.div_re, hS]
  rw [← Complex.normSq_eq_norm_sq] at hnz
  have hns : Complex.normSq z = ‖z‖ ^ 2 := Complex.normSq_eq_norm_sq z
  rw [hns]
  simp only [w, z, sc_toC_re, sc_toC_im]
  field_simp

/-- The costate frame data along the period: `det L > 0`, the frame, the state, and an angle
`Φ(t)` of `z(g(t))`. -/
theorem wd_good (P : NormalPeriod) {Φ : ℝ → ℝ}
    (hΦ : ∀ t ∈ Icc 0 P.T, wd_IsAng (Φ t) (Reduction.scb_zc (P.g t))) {L : Mat2}
    (hL : 0 < L.det) {t : ℝ} (ht : t ∈ Icc 0 P.T) : wd_Good L (P.g t) (P.X t) (Φ t) :=
  ⟨hL, (P.isStateTrajectory.2.2.2.1 t ht).1, (P.isStateTrajectory.2.2.2.1 t ht).2, hΦ t ht⟩

theorem wd_τ_mem (P : NormalPeriod) {n : ℕ} (hn : n ≤ P.N) : P.rep.τ n ∈ Icc 0 P.T :=
  ⟨P.rep.τ_nonneg (by positivity), P.rep.τ_le_T (by exact_mod_cast hn)⟩

/-- **The angle at a reverse centre** `c`: with `S = Qᵀ Q` (`det Q < 0`) and
`κ = wd_kap (Q K) (g(τ_c)) (X(τ_c)) (Φ(τ_c))`,
`arccos(e_c/√(d_{c-1} d_c)) = π/3 + κ(b_out) - κ(b_in)`. -/
theorem wd_centre (P : NormalPeriod) {Φ : ℝ → ℝ}
    (hΦ : ∀ t ∈ Icc 0 P.T, wd_IsAng (Φ t) (Reduction.scb_zc (P.g t))) {Q : Mat2}
    (hQ : Q.det < 0)
    (hS : ∀ x y, elQ (P.costateCycle.Sloc 0) x y =
      (Q *ᵥ x) 0 * (Q *ᵥ y) 0 + (Q *ᵥ x) 1 * (Q *ᵥ y) 1)
    {c : ℕ} (hcN : c < P.N) (hin : P.rep.label c = P.rep.label (c - 1) - 1)
    (hout : P.rep.label (c + 1) = P.rep.label c - 1) :
    Real.arccos (P.costateCycle.cre c /
        √(P.costateCycle.swd (c - 1) * P.costateCycle.swd c)) =
      Real.pi / 3 + wd_kap (Q * wd_K P) (P.g (P.rep.τ c)) (P.X (P.rep.τ c)) (Φ (P.rep.τ c))
          (wd_bout (P.rep.label c)) -
        wd_kap (Q * wd_K P) (P.g (P.rep.τ c)) (P.X (P.rep.τ c)) (Φ (P.rep.τ c))
          (wd_bin (P.rep.label c)) := by
  set C := P.costateCycle with hC
  have hin' : C.lab c = C.lab (c - 1) - 1 := hin
  have hout' : C.lab ((c : ℤ) + 1) = C.lab c - 1 := hout
  obtain ⟨hcre, hdet⟩ := C.cross_mm hin' hout'
  have hsin := C.Sloc_in c
  have hsout := C.Sloc_out c
  set a := C.pre c *ᵥ C.inc c with ha
  set b := C.pre c *ᵥ C.outv c with hb
  have e1 : C.cre c = elQ (C.Sloc 0) a b := by rw [← hcre, ha, hb, C.elQ_pre]
  have e2 : C.swd (c - 1) = elQ (C.Sloc 0) a a := by rw [← hsin, ha, C.elQ_pre]
  have e3 : C.swd c = elQ (C.Sloc 0) b b := by rw [← hsout, hb, C.elQ_pre]
  have hab : elDet a b < 0 := by
    rw [ha, hb, C.elDet_pre, hdet]
    have : 0 < C.act c ^ 2 + 4 := by positivity
    have : 0 < 1 / (C.act c ^ 2 + 4) := by positivity
    linarith
  rw [e1, e2, e3, wd_arccos_eq_arg hQ hS hab]
  -- the switch vectors in the physical frame
  obtain ⟨s, hs, hpre⟩ := wd_pre_phys P hcN.le
  set V := P.g (P.rep.τ c) * P.X (P.rep.τ c) with hV
  have hss : s ≠ 0 := by rcases hs with rfl | rfl <;> norm_num
  have hsw1 := C.sw_pos (c - 1)
  have hsw2 := C.sw_pos c
  have hq := C.q_pos c
  have hinc : C.inc c = (1 / C.sw (c - 1)) • ![-1, 0] := by
    rw [C.inc_rev hin']; ext i; fin_cases i <;> simp
  have houtv : C.outv c = (1 / (C.q c * C.sw c)) • ![0, 1] := by
    rw [C.outv_rev hout']; ext i; fin_cases i <;> simp
  have hlab : C.lab (c : ℤ) = P.rep.label c := rfl
  have hQa : Q *ᵥ a = (s * (1 / C.sw (c - 1))) • ((Q * wd_K P) *ᵥ (P.g (P.rep.τ c) *ᵥ
      (P.X (P.rep.τ c) *ᵥ wd_bin (P.rep.label c)))) := by
    rw [ha, hpre, hinc, Matrix.smul_mulVec, Matrix.mulVec_smul, Matrix.mulVec_smul,
      Matrix.mulVec_smul, smul_smul, ← wd_triCinv_in]
    simp only [Matrix.mulVec_mulVec, Matrix.mul_assoc, hV]
  have hQb : Q *ᵥ b = (s * (1 / (C.q c * C.sw c))) • ((Q * wd_K P) *ᵥ (P.g (P.rep.τ c) *ᵥ
      (P.X (P.rep.τ c) *ᵥ wd_bout (P.rep.label c)))) := by
    rw [hb, hpre, houtv, Matrix.smul_mulVec, Matrix.mulVec_smul, Matrix.mulVec_smul,
      Matrix.mulVec_smul, smul_smul, ← wd_triCinv_out]
    simp only [Matrix.mulVec_mulVec, Matrix.mul_assoc, hV]
  have hdetL : 0 < (Q * wd_K P).det := by
    rw [Matrix.det_mul, wd_det_K]; have := wd_s3pos; nlinarith
  have hG := wd_good P hΦ hdetL (wd_τ_mem P hcN.le)
  have hMin := wd_toC_ne (wd_mulVec_ne hdetL.ne' (hG.gXne (wd_bin_ne (P.rep.label c))))
  rw [hQa, hQb, sc_toC_smul, sc_toC_smul]
  have hpos : 0 < (s * (1 / (C.q c * C.sw c))) / (s * (1 / C.sw (c - 1))) := by
    have : (s * (1 / (C.q c * C.sw c))) / (s * (1 / C.sw (c - 1))) =
        C.sw (c - 1) / (C.q c * C.sw c) := by field_simp
    rw [this]; positivity
  rw [show ((s * (1 / (C.q c * C.sw c)) : ℝ) : ℂ) * sc_toC ((Q * wd_K P) *ᵥ (P.g (P.rep.τ c) *ᵥ
      (P.X (P.rep.τ c) *ᵥ wd_bout (P.rep.label c)))) /
      (((s * (1 / C.sw (c - 1)) : ℝ) : ℂ) * sc_toC ((Q * wd_K P) *ᵥ (P.g (P.rep.τ c) *ᵥ
      (P.X (P.rep.τ c) *ᵥ wd_bin (P.rep.label c))))) =
      (((s * (1 / (C.q c * C.sw c))) / (s * (1 / C.sw (c - 1))) : ℝ) : ℂ) *
        (sc_toC ((Q * wd_K P) *ᵥ (P.g (P.rep.τ c) *ᵥ (P.X (P.rep.τ c) *ᵥ
          wd_bout (P.rep.label c)))) /
        sc_toC ((Q * wd_K P) *ᵥ (P.g (P.rep.τ c) *ᵥ (P.X (P.rep.τ c) *ᵥ
          wd_bin (P.rep.label c))))) by
    have : ((s * (1 / C.sw (c - 1)) : ℝ) : ℂ) ≠ 0 := by
      exact_mod_cast mul_ne_zero hss (one_div_pos.2 hsw1).ne'
    push_cast
    field_simp]
  rw [arg_real_mul _ hpos, wd_kap_seg hG (wd_det_bin_bout _), wd_arg_bout_bin]

/-! ### Tracking along the pieces and the seam -/

/-- Along a piece whose tangent factor has `ω` as an eigenvector, `κ(ω)` is constant. -/
theorem wd_track_piece (P : NormalPeriod) {Φ : ℝ → ℝ} (hΦc : ContinuousOn Φ (Icc 0 P.T))
    (hΦ : ∀ t ∈ Icc 0 P.T, wd_IsAng (Φ t) (Reduction.scb_zc (P.g t))) {L : Mat2}
    (hL : 0 < L.det) {ω : Fin 2 → ℝ} (hω : ω ≠ 0) {n : ℕ} (hn : n < P.N)
    (heig : wd_IsEig (P.rep.label n) ω) :
    wd_kap L (P.g (P.rep.τ (n + 1 : ℕ))) (P.X (P.rep.τ (n + 1 : ℕ))) (Φ (P.rep.τ (n + 1 : ℕ))) ω =
      wd_kap L (P.g (P.rep.τ n)) (P.X (P.rep.τ n)) (Φ (P.rep.τ n)) ω := by
  have hn0 : (0 : ℤ) ≤ n := by positivity
  have hnN : (n : ℤ) < P.N := by exact_mod_cast hn
  obtain ⟨h0, h01, h1⟩ := P.rep.piece_subset hn0 hnN
  have hsub : Icc (P.rep.τ n) (P.rep.τ ((n : ℤ) + 1)) ⊆ Icc 0 P.T := Icc_subset_Icc h0 h1
  have hgc := (Reduction.scb_continuousOn_frame P.isStateTrajectory).mono hsub
  have hXc := (Reduction.scb_continuousOn_state P.isStateTrajectory).mono hsub
  push_cast
  refine wd_kap_track h01 hgc hXc (hΦc.mono hsub) (fun t ht ↦ wd_good P hΦ hL (hsub ht)) hω
    fun t ht ↦ ?_
  have hpe := (vertexPiece_eq P.isStateTrajectory h0 h01 h1 (P.ae_eq_vertex hn0 hnN) t ht).2.2
  obtain ⟨c, hc, hcv⟩ := heig _ (Real.exp_pos _)
  refine ⟨c, hc, ?_⟩
  rw [Matrix.mulVec_mulVec, hpe, ← Matrix.mulVec_mulVec, hcv, Matrix.mulVec_smul,
    Matrix.mulVec_mulVec]

/-- Tracking over a range of pieces. -/
theorem wd_track_range (P : NormalPeriod) {Φ : ℝ → ℝ} (hΦc : ContinuousOn Φ (Icc 0 P.T))
    (hΦ : ∀ t ∈ Icc 0 P.T, wd_IsAng (Φ t) (Reduction.scb_zc (P.g t))) {L : Mat2}
    (hL : 0 < L.det) {ω : Fin 2 → ℝ} (hω : ω ≠ 0) {a b : ℕ} (hab : a ≤ b) (hbN : b ≤ P.N)
    (heig : ∀ n : ℕ, a ≤ n → n < b → wd_IsEig (P.rep.label n) ω) :
    wd_kap L (P.g (P.rep.τ b)) (P.X (P.rep.τ b)) (Φ (P.rep.τ b)) ω =
      wd_kap L (P.g (P.rep.τ a)) (P.X (P.rep.τ a)) (Φ (P.rep.τ a)) ω := by
  induction b, hab using Nat.le_induction with
  | base => rfl
  | succ b hab ih =>
    rw [wd_track_piece P hΦc hΦ hL hω (by omega) (heig b hab (by omega)),
      ih (by omega) fun n h1 h2 ↦ heig n h1 (by omega)]

/-- **The seam**: `κ_T(ω) = κ_0(R ω) + π/3`. -/
theorem wd_seam (P : NormalPeriod) {Φ : ℝ → ℝ} (hΦT : Φ P.T - Φ 0 = Real.pi / 3)
    (hΦ : ∀ t ∈ Icc 0 P.T, wd_IsAng (Φ t) (Reduction.scb_zc (P.g t))) {L : Mat2}
    (hL : 0 < L.det) {ω : Fin 2 → ℝ} (hω : ω ≠ 0) :
    wd_kap L (P.g P.T) (P.X P.T) (Φ P.T) ω =
      wd_kap L (P.g 0) (P.X 0) (Φ 0) (R *ᵥ ω) + Real.pi / 3 := by
  have hT := P.T_pos
  have hG := wd_good P hΦ hL ⟨hT.le, le_rfl⟩
  have hXne := hG.Xne hω
  rw [P.g_T, P.g_zero] at *
  rw [P.X_T] at hXne ⊢
  have hRω : R *ᵥ ω ≠ 0 := wd_mulVec_ne (by rw [poly_det_R]; norm_num) hω
  have hX0 := P.isStarState (t := 0) ⟨le_rfl, hT.le⟩
  have hX0Rω : P.X 0 *ᵥ (R *ᵥ ω) ≠ 0 := wd_mulVec_ne (by rw [hX0.2.1]; norm_num) hRω
  have e1 : (R⁻¹ * P.X 0 * R) *ᵥ ω = R⁻¹ *ᵥ (P.X 0 *ᵥ (R *ᵥ ω)) := by
    simp only [Matrix.mulVec_mulVec, Matrix.mul_assoc]
  have e2 : R *ᵥ ((R⁻¹ * P.X 0 * R) *ᵥ ω) = P.X 0 *ᵥ (R *ᵥ ω) := by
    rw [e1, Matrix.mulVec_mulVec, poly_R_mul_inv, Matrix.one_mulVec]
  have hgT : arg (sc_toC (R *ᵥ ((R⁻¹ * P.X 0 * R) *ᵥ ω)) /
      (Reduction.scb_zc R * sc_toC ((R⁻¹ * P.X 0 * R) *ᵥ ω))) = 0 := by
    rw [wd_toC_R, wd_scb_zc_R, div_self (mul_ne_zero wd_rot_ne (wd_toC_ne hXne)), arg_one]
  unfold wd_kap
  rw [hgT, e2, Matrix.one_mulVec, wd_scb_zc_one, one_mul,
    div_self (wd_toC_ne hX0Rω), arg_one, e1, wd_toC_Rinv, wd_toC_R ω]
  have hω' := wd_toC_ne hω
  have h1 : (1 / 2 - (√3 / 2 : ℝ) * I) * sc_toC (P.X 0 *ᵥ (R *ᵥ ω)) / sc_toC ω =
      sc_toC (P.X 0 *ᵥ (R *ᵥ ω)) / ((1 / 2 + (√3 / 2 : ℝ) * I) * sc_toC ω) := by
    rw [div_eq_div_iff hω' (mul_ne_zero wd_rot_ne hω')]
    linear_combination (sc_toC (P.X 0 *ᵥ (R *ᵥ ω)) * sc_toC ω) * wd_rot_mul
  rw [h1]
  linarith

end SmoothedOctagon
