module

public import SmoothedOctagon.ArcLength
public import Mathlib.Analysis.Calculus.MeanValue
public import Mathlib.Logic.Function.Iterate
public import SmoothedPolygons.Ch2.Boundary
public import SmoothedPolygons.Ch3.AreaFormula
public import SmoothedPolygons.Ch3.StateDynamics

/-!
# A constructed determinant-one clock for a balanced contact frame

Two adjacent contacts define a global `C¹` matrix frame of determinant one. Its
logarithmic derivative has positive determinant by the balanced star inequalities.
Integrating the positive periodic speed `sqrt (det X)` therefore gives a global
increasing clock. In its inverse parameter the logarithmic derivative is a star
state of determinant one, and upstream Proposition 3.1.9 gives its global Lipschitz
regularity. The frame differential equation is proved by the chain rule.

This constructs the change of parameter assumed in that upstream proposition. It
also proves that a positive contact successor with the sixfold period relation is
conjugated to translation by one sixth of the new full period. Constructing the
actual successor, the measurable control, terminal conditions, and control
optimality belong to separate results. Source draft only; compilation and kernel
validation have not been run.
-/

@[expose] public section

namespace SmoothedOctagon

open MeasureTheory Real Set Filter Matrix SmoothedPolygons
open scoped Topology

/-- The global frame sending the standard adjacent contacts to `σ₀(t), σ₁(t)`. -/
noncomputable def contactFrame (σ : ZMod 6 → ℝ → Fin 2 → ℝ) (t : ℝ) : Mat2 :=
  Matrix.of fun i j ↦ (![σ 0 t i, (2 * σ 1 t i - σ 0 t i) / √3] : Fin 2 → ℝ) j

lemma contactFrame_zero_contact (σ : ZMod 6 → ℝ → Fin 2 → ℝ) (t : ℝ) :
    contactFrame σ t *ᵥ sixthRoot 0 = σ 0 t := by
  rw [rein_sixthRoot_zero]
  ext i
  simp [contactFrame, Matrix.mulVec, dotProduct, Fin.sum_univ_two]

lemma contactFrame_one_contact (σ : ZMod 6 → ℝ → Fin 2 → ℝ) (t : ℝ) :
    contactFrame σ t *ᵥ sixthRoot 1 = σ 1 t := by
  rw [rein_sixthRoot_one]
  ext i
  have h3 : (√3 : ℝ) ≠ 0 := by positivity
  simp only [contactFrame, Matrix.of_apply, Matrix.mulVec, dotProduct, Fin.sum_univ_two,
    Matrix.cons_val_zero, Matrix.cons_val_one]
  field_simp [h3]
  ring

/-- The two contact equations determine the frame uniquely. -/
lemma contactFrame_unique {σ : ZMod 6 → ℝ → Fin 2 → ℝ} (t : ℝ) {A : Mat2}
    (h0 : A *ᵥ sixthRoot 0 = σ 0 t) (h1 : A *ᵥ sixthRoot 1 = σ 1 t) :
    A = contactFrame σ t := by
  have h3 : (√3 : ℝ) ≠ 0 := by positivity
  rw [rein_sixthRoot_zero] at h0
  rw [rein_sixthRoot_one] at h1
  ext i j
  have e0 := congrFun h0 i
  have e1 := congrFun h1 i
  simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_two,
    Matrix.cons_val_zero, Matrix.cons_val_one, mul_one, mul_zero, add_zero] at e0 e1
  fin_cases j
  · simpa only [contactFrame, Matrix.of_apply, Matrix.cons_val_zero] using e0
  · simp only [contactFrame, Matrix.of_apply, Matrix.cons_val_one, Matrix.cons_val_zero]
    rw [eq_div_iff h3]
    nlinarith [e0, e1]

/-- The multi-point identities propagate the two defining equations to all six contacts. -/
theorem contactFrame_action {σ : ZMod 6 → ℝ → Fin 2 → ℝ}
    (hmp : ∀ t, IsMultiPoint fun j ↦ σ j t) (t : ℝ) (j : ZMod 6) :
    σ j t = contactFrame σ t *ᵥ sixthRoot j := by
  refine bdy_seq_eq (bdy_mp_succ (hmp t)) (fun k ↦ ?_)
    (contactFrame_zero_contact σ t).symm (contactFrame_one_contact σ t).symm j
  rw [bdy_mp_succ bdy_isMultiPoint_sixthRoot, Matrix.mulVec_add]

/-- Normalized contact determinants give a determinant-one frame. -/
theorem contactFrame_det {σ : ZMod 6 → ℝ → Fin 2 → ℝ}
    (hmp : ∀ t, IsMultiPoint fun j ↦ σ j t) (t : ℝ) :
    (contactFrame σ t).det = 1 := by
  have h := ((hmp t) 0).2.2
  have hs := (bdy_isMultiPoint_sixthRoot 0).2.2
  simp only [zero_add] at h hs
  rw [contactFrame_action hmp t 0, contactFrame_action hmp t 1,
    oct_det2_mulVec, hs] at h
  apply mul_right_cancel₀ (by positivity : (√3 : ℝ) / 2 ≠ 0)
  simpa only [one_mul] using h

/-- Circle representation supplies the identity initial frame. -/
theorem contactFrame_initial {σ : ZMod 6 → ℝ → Fin 2 → ℝ}
    (hcirc : IsCircleRepresentation σ) : contactFrame σ 0 = 1 := by
  symm
  apply contactFrame_unique 0
  · rw [Matrix.one_mulVec, hcirc 0]
  · rw [Matrix.one_mulVec, hcirc 1]

theorem contactFrame_contDiff {σ : ZMod 6 → ℝ → Fin 2 → ℝ}
    (hC : ∀ j, ContDiff ℝ 1 (σ j)) (i j : Fin 2) :
    ContDiff ℝ 1 (fun t ↦ contactFrame σ t i j) := by
  have h0 : ContDiff ℝ 1 (fun t ↦ σ 0 t i) := contDiff_pi.1 (hC 0) i
  have h1 : ContDiff ℝ 1 (fun t ↦ σ 1 t i) := contDiff_pi.1 (hC 1) i
  fin_cases j
  · simpa only [contactFrame, Matrix.of_apply, Matrix.cons_val_zero] using h0
  · have htwo : ContDiff ℝ 1 (fun _ : ℝ ↦ (2 : ℝ)) := contDiff_const
    simpa only [contactFrame, Matrix.of_apply, Matrix.cons_val_one, Matrix.cons_val_zero] using
      ((htwo.mul h1).sub h0).div_const (√3 : ℝ)

theorem contactFrame_hasDerivAt {σ : ZMod 6 → ℝ → Fin 2 → ℝ}
    (hC : ∀ j, ContDiff ℝ 1 (σ j)) (t : ℝ) :
    HasDerivAtEntrywise (contactFrame σ) (derivEntrywise (contactFrame σ) t) t := by
  intro i j
  exact ((contDiff_one_iff_deriv.mp (contactFrame_contDiff hC i j)).1 t).hasDerivAt

theorem contactFrame_periodic {σ : ZMod 6 → ℝ → Fin 2 → ℝ} {T : ℝ}
    (hperiod : ∀ j, Function.Periodic (σ j) T) :
    Function.Periodic (contactFrame σ) T := by
  intro t
  ext i j
  simp only [contactFrame, Matrix.of_apply, hperiod 0 t, hperiod 1 t]

/-- A successor of contact configurations acts on the frame by right multiplication by `R`.
This is an algebraic transport statement; existence of a successor map is not assumed elsewhere. -/
theorem contactFrame_shift_of_contacts {σ : ZMod 6 → ℝ → Fin 2 → ℝ}
    (hmp : ∀ t, IsMultiPoint fun j ↦ σ j t) {φ : ℝ → ℝ}
    (hshift : ∀ j t, σ j (φ t) = σ (j + 1) t) (t : ℝ) :
    contactFrame σ (φ t) = contactFrame σ t * R := by
  have h (j : ZMod 6) : (contactFrame σ t * R) *ᵥ sixthRoot j = σ j (φ t) := by
    rw [← Matrix.mulVec_mulVec, oct_R_mulVec_sixthRoot,
      ← contactFrame_action hmp t (j + 1), hshift j t]
  exact (contactFrame_unique (φ t) (h 0) (h 1)).symm

/-- The global logarithmic derivative before changing time. -/
noncomputable def contactLogDerivative (σ : ZMod 6 → ℝ → Fin 2 → ℝ) (t : ℝ) : Mat2 :=
  (contactFrame σ t)⁻¹ * derivEntrywise (contactFrame σ) t

/-- The contact frame solves its logarithmic-derivative equation globally. -/
theorem contactFrame_dynamics {K : Set (Fin 2 → ℝ)}
    {σ : ZMod 6 → ℝ → Fin 2 → ℝ} {tf : ℝ} (hbal : IsBalancedPair K σ tf) (t : ℝ) :
    HasDerivAtEntrywise (contactFrame σ)
      (contactFrame σ t * contactLogDerivative σ t) t := by
  have hunit : IsUnit (contactFrame σ t).det := by
    rw [contactFrame_det hbal.2.2.2.1 t]
    exact isUnit_one
  rw [contactLogDerivative, ← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hunit,
    Matrix.one_mul]
  exact contactFrame_hasDerivAt (fun j ↦ (hbal.2.1 j).1) t

/-- The balanced star conditions give positive star functions and positive raw determinant. -/
theorem contactLogDerivative_properties {K : Set (Fin 2 → ℝ)}
    {σ : ZMod 6 → ℝ → Fin 2 → ℝ} {tf : ℝ} (hbal : IsBalancedPair K σ tf) (t : ℝ) :
    (contactLogDerivative σ t).trace = 0 ∧
      0 < ρ₀ (contactLogDerivative σ t) ∧ 0 < ρ₁ (contactLogDerivative σ t) ∧
      0 < ρ₂ (contactLogDerivative σ t) ∧ 0 < (contactLogDerivative σ t).det := by
  have hp := corollary3_1_6 K σ tf hbal (contactFrame σ)
    (contactFrame_action hbal.2.2.2.1) t
  refine ⟨?_, hp.1, hp.2.1, hp.2.2.1, hp.2.2.2.2.2.2.2⟩
  exact oct_trace_eq_zero (s := univ) (by simp) (contactFrame_dynamics hbal t)
    (fun u _ ↦ contactFrame_det hbal.2.2.2.1 u)

theorem continuous_contactLogDerivative {K : Set (Fin 2 → ℝ)}
    {σ : ZMod 6 → ℝ → Fin 2 → ℝ} {tf : ℝ} (hbal : IsBalancedPair K σ tf) :
    Continuous (contactLogDerivative σ) := by
  have hC : ∀ j, ContDiff ℝ 1 (σ j) := fun j ↦ (hbal.2.1 j).1
  have hinv : Continuous fun t ↦ (contactFrame σ t)⁻¹ := by
    apply continuous_iff_continuousAt.mpr
    intro t
    apply ((contactFrame_hasDerivAt hC t).inv ?_).continuousAt
    rw [contactFrame_det hbal.2.2.2.1 t]
    exact isUnit_one
  have hd : Continuous (derivEntrywise (contactFrame σ)) := by
    apply Matrix.continuous_iff_entrywise.mpr
    intro i j
    exact (contactFrame_contDiff hC i j).continuous_deriv le_rfl
  exact hinv.matrix_mul hd

theorem contactLogDerivative_periodic {σ : ZMod 6 → ℝ → Fin 2 → ℝ} {T : ℝ}
    (hperiod : ∀ j, Function.Periodic (σ j) T) :
    Function.Periodic (contactLogDerivative σ) T := by
  have hgper := contactFrame_periodic hperiod
  intro t
  simp only [contactLogDerivative, hgper t]
  congr 1
  ext i j
  simp only [derivEntrywise, Matrix.of_apply]
  rw [← deriv_comp_add_const]
  simp only [hgper]

/-- Because the contact frame has determinant one, its logarithmic derivative and
its ordinary entrywise derivative have the same determinant. -/
theorem contactLogDerivative_det {σ : ZMod 6 → ℝ → Fin 2 → ℝ}
    (hmp : ∀ t, IsMultiPoint fun j ↦ σ j t) (t : ℝ) :
    (contactLogDerivative σ t).det = (derivEntrywise (contactFrame σ) t).det := by
  simp only [contactLogDerivative, Matrix.det_mul, Matrix.det_nonsing_inv,
    contactFrame_det hmp t, Ring.inverse_one, inv_one, one_mul]

/-- Speed of the determinant-one time parameter: `ds/dt = sqrt (det X(t))`. -/
noncomputable def determinantSpeed (σ : ZMod 6 → ℝ → Fin 2 → ℝ) (t : ℝ) : ℝ :=
  √((contactLogDerivative σ t).det)

theorem determinantSpeed_pos {K : Set (Fin 2 → ℝ)}
    {σ : ZMod 6 → ℝ → Fin 2 → ℝ} {tf : ℝ} (hbal : IsBalancedPair K σ tf) (t : ℝ) :
    0 < determinantSpeed σ t :=
  Real.sqrt_pos.2 (contactLogDerivative_properties hbal t).2.2.2.2

theorem determinantSpeed_sq {K : Set (Fin 2 → ℝ)}
    {σ : ZMod 6 → ℝ → Fin 2 → ℝ} {tf : ℝ} (hbal : IsBalancedPair K σ tf) (t : ℝ) :
    determinantSpeed σ t ^ 2 = (contactLogDerivative σ t).det :=
  Real.sq_sqrt (contactLogDerivative_properties hbal t).2.2.2.2.le

theorem continuous_determinantSpeed {K : Set (Fin 2 → ℝ)}
    {σ : ZMod 6 → ℝ → Fin 2 → ℝ} {tf : ℝ} (hbal : IsBalancedPair K σ tf) :
    Continuous (determinantSpeed σ) := by
  have hc := Matrix.continuous_iff_entrywise.mp (continuous_contactLogDerivative hbal)
  have hdet : Continuous fun t ↦ (contactLogDerivative σ t).det := by
    simp only [Matrix.det_fin_two]
    exact ((hc 0 0).mul (hc 1 1)).sub ((hc 0 1).mul (hc 1 0))
  exact Real.continuous_sqrt.comp hdet

theorem determinantSpeed_periodic {σ : ZMod 6 → ℝ → Fin 2 → ℝ} {T : ℝ}
    (hperiod : ∀ j, Function.Periodic (σ j) T) :
    Function.Periodic (determinantSpeed σ) T := by
  intro t
  simp only [determinantSpeed, contactLogDerivative_periodic hperiod t]

/-- The determinant clock is invariant under a positive regular successor of the
contact configuration. This is the differential identity used to obtain a constant
cyclic time shift after integrating the clock. -/
theorem determinantSpeed_contact_shift {K : Set (Fin 2 → ℝ)}
    {σ : ZMod 6 → ℝ → Fin 2 → ℝ} {tf : ℝ} (hbal : IsBalancedPair K σ tf)
    {φ : ℝ → ℝ} (hφ : ContDiff ℝ 1 φ) (hφpos : ∀ t, 0 < deriv φ t)
    (hshift : ∀ j t, σ j (φ t) = σ (j + 1) t) (t : ℝ) :
    determinantSpeed σ (φ t) * deriv φ t = determinantSpeed σ t := by
  have hC : ∀ j, ContDiff ℝ 1 (σ j) := fun j ↦ (hbal.2.1 j).1
  have hmp := hbal.2.2.2.1
  have hfun : (fun u ↦ contactFrame σ (φ u)) = fun u ↦ contactFrame σ u * R :=
    funext (contactFrame_shift_of_contacts hmp hshift)
  have hcomp := (contactFrame_hasDerivAt hC (φ t)).scomp
    (((contDiff_one_iff_deriv.mp hφ).1 t).hasDerivAt)
  rw [hfun] at hcomp
  have hright := (contactFrame_hasDerivAt hC t).mul_const R
  have hmatrix := hcomp.unique hright
  have hR : R.det = 1 := by
    simp [R, Matrix.det_fin_two]
    ring_nf
    norm_num
  have hdet := congrArg Matrix.det hmatrix
  rw [Matrix.det_smul, Fintype.card_fin, Matrix.det_mul, hR, mul_one,
    ← contactLogDerivative_det hmp (φ t), ← contactLogDerivative_det hmp t] at hdet
  apply (sq_eq_sq₀
    (mul_pos (determinantSpeed_pos hbal (φ t)) (hφpos t)).le
    (determinantSpeed_pos hbal t).le).mp
  rw [mul_pow, determinantSpeed_sq hbal (φ t), determinantSpeed_sq hbal t]
  exact (mul_comm _ _).trans hdet

/-- A positive scalar normalizes the determinant without changing any star sign. -/
lemma inv_sqrt_smul_isStarState {X : Mat2} (htr : X.trace = 0)
    (h0 : 0 < ρ₀ X) (h1 : 0 < ρ₁ X) (h2 : 0 < ρ₂ X) (hdet : 0 < X.det) :
    IsStarState ((√X.det)⁻¹ • X) := by
  have hs : 0 < (√X.det)⁻¹ := inv_pos.2 (Real.sqrt_pos.2 hdet)
  have hsq : (√X.det) ^ 2 = X.det := Real.sq_sqrt hdet.le
  have hne : (√X.det : ℝ) ≠ 0 := (Real.sqrt_pos.2 hdet).ne'
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [Matrix.trace_smul, htr, smul_zero]
  · rw [Matrix.det_smul, Fintype.card_fin]
    have hcancel : ((√X.det)⁻¹) ^ 2 * (√X.det) ^ 2 = 1 := by
      rw [← mul_pow, inv_mul_cancel₀ hne, one_pow]
    simpa only [hsq] using hcancel
  · have hscale : ρ₀ ((√X.det)⁻¹ • X) = (√X.det)⁻¹ * ρ₀ X := by
      simp only [ρ₀, Matrix.smul_apply, smul_eq_mul]
      ring
    rw [hscale]
    exact mul_pos hs h0
  · have hscale : ρ₁ ((√X.det)⁻¹ • X) = (√X.det)⁻¹ * ρ₁ X := by
      simp only [ρ₁, Matrix.smul_apply, smul_eq_mul]
      ring
    rw [hscale]
    exact mul_pos hs h1
  · have hscale : ρ₂ ((√X.det)⁻¹ • X) = (√X.det)⁻¹ * ρ₂ X := by
      simp only [ρ₂, Matrix.smul_apply, smul_eq_mul]
      ring
    rw [hscale]
    exact mul_pos hs h2

/-- The logarithmic state after a scalar change of time. -/
noncomputable def normalizedContactState (σ : ZMod 6 → ℝ → Fin 2 → ℝ)
    (a : ℝ → ℝ) (t : ℝ) : Mat2 :=
  deriv a t • contactLogDerivative σ (a t)

/-- Construct the determinant-one clock from a balanced pair. All frame, speed,
normalization, and Lipschitz hypotheses are discharged from the balanced geometry. -/
theorem balanced_exists_determinant_clock {K : Set (Fin 2 → ℝ)}
    {σ : ZMod 6 → ℝ → Fin 2 → ℝ} {tf : ℝ} (hbal : IsBalancedPair K σ tf) :
    ∃ P : ℝ, 0 < P ∧ ∃ a : ℝ ≃o ℝ,
      a 0 = 0 ∧ ContDiff ℝ 1 (fun t ↦ a t) ∧
      (∀ t, HasDerivAt (fun u ↦ a u) (determinantSpeed σ (a t))⁻¹ t) ∧
      (∀ t, 0 < deriv (fun u ↦ a u) t) ∧
      (∀ t, a (t + P) = a t + 6 * tf) ∧
      (∀ t, IsStarState (normalizedContactState σ a t)) ∧
      LipschitzOnEntrywise (normalizedContactState σ a) univ ∧
      (∀ t, HasDerivAtEntrywise (fun u ↦ contactFrame σ (a u))
        (contactFrame σ (a t) * normalizedContactState σ a t) t) := by
  have htf : 0 < tf := hbal.2.2.2.2.2.2.1
  have hperiod : ∀ j, Function.Periodic (σ j) (6 * tf) := hbal.2.2.2.2.2.2.2.1
  obtain ⟨hP, a, ha0, haC1, haD, haper⟩ :=
    exists_inverse_integral_reparam (continuous_determinantSpeed hbal)
      (determinantSpeed_pos hbal) (by positivity : 0 < 6 * tf)
      (determinantSpeed_periodic hperiod)
  have hapos : ∀ t, 0 < deriv (fun u ↦ a u) t := by
    intro t
    rw [(haD t).deriv]
    exact inv_pos.2 (determinantSpeed_pos hbal (a t))
  have hstar : ∀ t, IsStarState (normalizedContactState σ a t) := by
    intro t
    obtain ⟨htr, h0, h1, h2, hdet⟩ := contactLogDerivative_properties hbal (a t)
    simpa only [normalizedContactState, (haD t).deriv, determinantSpeed] using
      inv_sqrt_smul_isStarState htr h0 h1 h2 hdet
  have hcanon : ∀ t, HasDerivAt (fun u ↦ a u) (deriv (fun u ↦ a u) t) t :=
    fun t ↦ (haD t).differentiableAt.hasDerivAt
  have hLip : LipschitzOnEntrywise (normalizedContactState σ a) univ :=
    proposition3_1_9 K σ tf hbal (contactFrame σ) (contactFrame_action hbal.2.2.2.1)
      a (deriv (fun u ↦ a u)) hcanon hapos (fun t ↦ (hstar t).2.1)
  refine ⟨∫ u in (0 : ℝ)..(6 * tf), determinantSpeed σ u, hP, a,
    ha0, haC1, haD, hapos, haper, hstar, hLip, ?_⟩
  intro t
  simpa only [normalizedContactState, Matrix.mul_smul] using
    (contactFrame_dynamics hbal (a t)).scomp (hcanon t)

/-- The constructed determinant clock sends a positive cyclic contact successor to
translation by one sixth of its full period. The successor and its sixfold relation
are explicit hypotheses here; `ContactLift` supplies them for actual worst disks. -/
theorem determinantClock_conjugates_successor {K : Set (Fin 2 → ℝ)}
    {σ : ZMod 6 → ℝ → Fin 2 → ℝ} {tf : ℝ} (hbal : IsBalancedPair K σ tf)
    {P : ℝ} (a : ℝ ≃o ℝ)
    (haD : ∀ t, HasDerivAt (fun u ↦ a u) (determinantSpeed σ (a t))⁻¹ t)
    (haper : ∀ t, a (t + P) = a t + 6 * tf)
    {φ : ℝ → ℝ} (hφ : ContDiff ℝ 1 φ) (hφpos : ∀ t, 0 < deriv φ t)
    (hshift : ∀ j t, σ j (φ t) = σ (j + 1) t)
    (hφsix : ∀ t, φ^[6] t = t + 6 * tf) :
    ∀ t, φ (a t) = a (t + P / 6) := by
  have hbD : ∀ u, HasDerivAt (fun v ↦ a.symm v) (determinantSpeed σ u) u := by
    intro u
    have hne : (determinantSpeed σ (a (a.symm u)))⁻¹ ≠ 0 :=
      inv_ne_zero (determinantSpeed_pos hbal (a (a.symm u))).ne'
    have h := HasDerivAt.of_local_left_inverse a.symm.continuous.continuousAt
      (haD (a.symm u)) hne (Filter.Eventually.of_forall fun v ↦ a.apply_symm_apply v)
    simpa only [a.apply_symm_apply, inv_inv] using h
  let F : ℝ → ℝ := fun t ↦ a.symm (φ (a t))
  have hFD : ∀ t, HasDerivAt F 1 t := by
    intro t
    have hchain := (hbD (φ (a t))).comp t
      ((((contDiff_one_iff_deriv.mp hφ).1 (a t)).hasDerivAt).comp t (haD t))
    have hs : determinantSpeed σ (φ (a t)) *
        (deriv φ (a t) * (determinantSpeed σ (a t))⁻¹) = 1 := by
      rw [← mul_assoc, determinantSpeed_contact_shift hbal hφ hφpos hshift (a t),
        mul_inv_cancel₀ (determinantSpeed_pos hbal (a t)).ne']
    simpa only [hs] using hchain
  have hdiff : ∀ t, HasDerivAt (fun u ↦ F u - u) 0 t := by
    intro t
    simpa only [sub_self] using (hFD t).sub (hasDerivAt_id t)
  have hF : ∀ t, F t = t + F 0 := by
    intro t
    have hconst := is_const_of_deriv_eq_zero
      (fun u ↦ (hdiff u).differentiableAt) (fun u ↦ (hdiff u).deriv) t 0
    dsimp only at hconst
    linarith
  have hφa : ∀ t, φ (a t) = a (t + F 0) := by
    intro t
    have h := congrArg (fun u : ℝ ↦ a u) (hF t)
    simpa only [F, a.apply_symm_apply] using h
  have hiter : ∀ (n : ℕ) (t : ℝ), φ^[n] (a t) = a (t + (n : ℝ) * F 0) := by
    intro n
    induction n with
    | zero =>
        intro t
        simp only [Function.iterate_zero_apply, Nat.cast_zero, zero_mul, add_zero]
    | succ n ih =>
        intro t
        rw [Function.iterate_succ_apply', ih, hφa]
        congr 1
        push_cast
        ring
  have hcycle : a (6 * F 0) = a P := by
    calc
      a (6 * F 0) = φ^[6] (a 0) := by simpa using (hiter 6 0).symm
      _ = a 0 + 6 * tf := hφsix (a 0)
      _ = a P := by simpa only [zero_add] using (haper 0).symm
  have hc : F 0 = P / 6 := by
    have h := a.injective hcycle
    linarith
  intro t
  simpa only [hc] using hφa t

end SmoothedOctagon
