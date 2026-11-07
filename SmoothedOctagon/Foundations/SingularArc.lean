module

public import SmoothedOctagon.Foundations.AdmissibleRegularity
public import SmoothedOctagon.Foundations.CircleExclusion
public import SmoothedOctagon.Foundations.SingularLocus
public import SmoothedPolygons.Ch6.Hamiltonian
public import Mathlib.MeasureTheory.Measure.OpenPos

/-!
# Rigidity of an interval with zero reduced costate

For an actual integral-form Pontryagin extremal, vanishing of the reduced
costate on a nonempty open interval forces the circle state on that interval.
The Hamiltonian and reduced-costate equation initially give information only
almost everywhere. Continuity upgrades the resulting first-costate identity
to every point before its classical differential equation is used.

The interval and the vanishing hypothesis remain explicit. No existence of a
Pontryagin lift, exclusion of proper singular subarcs in a minimizer, or global cost
lower bound is asserted. In particular, a nonunique maximizing edge is not
identified with the full control-independent singular case.

Source draft only: compilation and kernel validation have not been run.
-/

@[expose] public section

namespace SmoothedOctagon

open MeasureTheory Set Filter Real Matrix SmoothedPolygons
open scoped Topology

/-! ## Algebra at a stationary reduced costate -/

/-- A traceless matrix commuting with a determinant-one traceless matrix and
perpendicular to it in the trace form must vanish. -/
theorem commuting_perpendicular_eq_zero {X A : Mat2}
    (hXtr : X.trace = 0) (hXdet : X.det = 1) (hAtr : A.trace = 0)
    (hcomm : A * X - X * A = 0) (hperp : traceForm A X = 0) : A = 0 := by
  have hXne : X ≠ 0 := by
    intro hzero
    simp [hzero] at hXdet
  obtain ⟨c, hc⟩ := orb_centralizer X A hXtr hXne hAtr hcomm
  have hXX : traceForm X X = -2 := by
    rw [lemma3_4_1.1 X hXtr, hXdet]
    norm_num
  have hscale : traceForm (c • X) X = c * traceForm X X := by
    simp only [traceForm, Matrix.smul_mul, Matrix.trace_smul, smul_eq_mul]
  rw [hc, hscale, hXX] at hperp
  have hc0 : c = 0 := by linarith
  rw [hc, hc0, zero_smul]

/-- The zero reduced-costate derivative and zero Hamiltonian determine the
first costate. This is the algebraic content used from Lemma 8.2.2. -/
theorem costate_eq_cost_of_zero_reduced_derivative {L X : Mat2} {lam : ℝ}
    (hXtr : X.trace = 0) (hXdet : X.det = 1) (hLtr : L.trace = 0)
    (hcomm : (-L + (3 / 2 * lam) • J) * X -
      X * (-L + (3 / 2 * lam) • J) = 0)
    (hH : traceForm (L - (3 / 2 * lam) • J) X = 0) :
    L = (3 / 2 * lam) • J := by
  let A : Mat2 := L - (3 / 2 * lam) • J
  have hJtr : J.trace = 0 := by simp [J, Matrix.trace_fin_two]
  have hAtr : A.trace = 0 := by
    simp only [A, Matrix.trace_sub, Matrix.trace_smul, hLtr, hJtr,
      smul_eq_mul, mul_zero, sub_zero]
  have hnegative : (-L + (3 / 2 * lam) • J) * X -
      X * (-L + (3 / 2 * lam) • J) = -(A * X - X * A) := by
    simp only [A, Matrix.add_mul, Matrix.neg_mul, Matrix.mul_add, Matrix.mul_neg,
      Matrix.sub_mul, Matrix.mul_sub]
    abel
  rw [hnegative, neg_eq_zero] at hcomm
  exact sub_eq_zero.mp (commuting_perpendicular_eq_zero hXtr hXdet hAtr hcomm hH)

/-- In the star component, the only determinant-one traceless matrix commuting
with the rotation generator is the positively oriented circle state `J`. -/
theorem starState_eq_J_of_commutator_zero {X : Mat2} (hX : IsStarState X)
    (hcomm : J * X - X * J = 0) : X = J := by
  have h00 := congrArg (fun M : Mat2 ↦ M 0 0) hcomm
  have h01 := congrArg (fun M : Mat2 ↦ M 0 1) hcomm
  simp only [J, Matrix.sub_apply, Matrix.mul_apply, Fin.sum_univ_two, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, zero_mul, neg_one_mul,
    mul_zero, mul_one, mul_neg_one, zero_add, add_zero, Matrix.zero_apply] at h00 h01
  have htr := hX.1
  rw [Matrix.trace_fin_two] at htr
  have ha : X 0 0 = 0 := by linarith
  have hd : X 1 1 = 0 := by linarith
  have hb : X 0 1 = -X 1 0 := by linarith
  have hdet := hX.2.1
  rw [Matrix.det_fin_two, ha, hd, hb] at hdet
  have hρ := hX.2.2.1
  simp only [ρ₀, ha, mul_zero, add_zero] at hρ
  have hc : 0 < X 1 0 :=
    (div_pos_iff_of_pos_right (by positivity : (0 : ℝ) < √3)).1 hρ
  have hfactor : (X 1 0 - 1) * (X 1 0 + 1) = 0 := by nlinarith [hdet]
  have hc1 : X 1 0 = 1 :=
    sub_eq_zero.mp ((mul_eq_zero.mp hfactor).resolve_right (by linarith))
  ext i j
  fin_cases i <;> fin_cases j <;> simp [J, ha, hd, hb, hc1]

/-- The stationary circle state determines the control uniquely in the simplex.
The scalar trace denominator is explicitly `-2/3`. -/
theorem circle_control_unique {u : Fin 3 → ℝ} (hu : u ∈ controlSimplex)
    (hcomm : controlP u J * J - J * controlP u J = 0) :
    u = fun _ ↦ (1 / 3 : ℝ) := by
  have hden : traceForm (controlMatrix u) J = -(2 / 3 : ℝ) := by
    simp only [traceForm, controlMatrix, J, Matrix.trace_fin_two, Matrix.mul_apply,
      Fin.sum_univ_two, Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
      mul_zero, mul_one, mul_neg_one, zero_add, add_zero]
    linarith [hu.2]
  have hP : controlP u J = (-3 / 2 : ℝ) • controlMatrix u := by
    rw [controlP, hden]
    norm_num
  have hscale : (-3 / 2 : ℝ) • (controlMatrix u * J - J * controlMatrix u) = 0 := by
    simpa only [hP, Matrix.smul_mul, Matrix.mul_smul, smul_sub] using hcomm
  have hZ : controlMatrix u * J - J * controlMatrix u = 0 :=
    (smul_eq_zero.mp hscale).resolve_left (by norm_num)
  have h00 := congrArg (fun M : Mat2 ↦ M 0 0) hZ
  have h01 := congrArg (fun M : Mat2 ↦ M 0 1) hZ
  simp only [controlMatrix, J, Matrix.sub_apply, Matrix.mul_apply, Fin.sum_univ_two,
    Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one, zero_mul,
    neg_one_mul, mul_zero, mul_one, mul_neg_one, zero_add, add_zero,
    Matrix.zero_apply] at h00 h01
  have h3 : (√3 : ℝ) ≠ 0 := by positivity
  field_simp [h3] at h01
  funext i
  fin_cases i <;> simp only [Fin.reduceFinMk] <;> linarith [hu.2]

/-! ## The actual integral extremal on an explicit subinterval -/

/-- The first costate is fixed throughout any open interval on which the reduced
costate vanishes. No pointwise reduced-costate ODE is assumed: the proof first
uses its integral equation and the Hamiltonian almost everywhere, then continuity. -/
theorem pontryagin_costate_eq_on_zero_reducedCostate
    {T a b lam : ℝ} {u : ℝ → Fin 3 → ℝ} {g X Λ₁ ΛR : ℝ → Mat2}
    (h : IsPontryaginExtremal T u g X Λ₁ ΛR lam)
    (hsub : Ioo a b ⊆ Ioo 0 T) (hzero : ∀ t ∈ Ioo a b, ΛR t = 0) :
    ∀ t ∈ Ioo a b, Λ₁ t = (3 / 2 * lam) • J := by
  obtain ⟨htraj, _, _, _, _, _, _, hcostates, hL₁I, hLRI, hmax⟩ := h
  have hae : ∀ᵐ t, t ∈ Ioo a b → Λ₁ t = (3 / 2 * lam) • J := by
    filter_upwards [integralCurve_ae_hasDerivAt htraj.1.le hLRI, hmax] with t hd hH ht
    have htT := hsub ht
    have htcc : t ∈ Icc 0 T := Ioo_subset_Icc_self htT
    have hRderiv : HasDerivAtEntrywise ΛR 0 t :=
      (hasDerivAtEntrywise_const (0 : Mat2) t).congr_of_eventuallyEq
        (Filter.eventually_of_mem (Ioo_mem_nhds ht.1 ht.2) fun s hs ↦ hzero s hs)
    have hcomm : (-Λ₁ t + (3 / 2 * lam) • J) * X t -
        X t * (-Λ₁ t + (3 / 2 * lam) • J) = 0 := by
      have hz := (hd htT).unique hRderiv
      simpa only [hzero t ht, Matrix.mul_zero, Matrix.zero_mul, sub_self,
        traceForm, Matrix.trace_zero, zero_smul, sub_zero, zero_add] using hz
    have hH0 : traceForm (Λ₁ t - (3 / 2 * lam) • J) (X t) = 0 := by
      simpa only [hamiltonian, hzero t ht, traceForm, Matrix.zero_mul,
        Matrix.trace_zero, zero_div, sub_zero] using (hH htT).1
    have hstar := (htraj.2.2.2.1 t htcc).2
    exact costate_eq_cost_of_zero_reduced_derivative hstar.1 hstar.2.1
      (hcostates t htcc).1 hcomm hH0
  have hcont : ContinuousOn Λ₁ (Ioo a b) :=
    (Matrix.continuousOn_of_eq_add_integral hL₁I).mono
      (fun _ ht ↦ Ioo_subset_Icc_self (hsub ht))
  exact Measure.eqOn_open_of_ae_eq
    ((ae_restrict_iff' measurableSet_Ioo).mpr hae) isOpen_Ioo hcont continuousOn_const

/-- Actual singular-interval rigidity (the state and control content of
Theorem 8.2.3). The interval is nonempty and lies inside the original trajectory.
The control is determined only almost everywhere, as appropriate for integral
solutions with measurable controls. -/
theorem pontryagin_zero_reducedCostate_rigidity
    {T a b lam : ℝ} {u : ℝ → Fin 3 → ℝ} {g X Λ₁ ΛR : ℝ → Mat2}
    (h : IsPontryaginExtremal T u g X Λ₁ ΛR lam)
    (hab : a < b) (hsub : Ioo a b ⊆ Ioo 0 T)
    (hzero : ∀ t ∈ Ioo a b, ΛR t = 0) :
    lam < 0 ∧
      (∀ t ∈ Ioo a b, Λ₁ t = (3 / 2 * lam) • J ∧ X t = J) ∧
      (∀ᵐ t, t ∈ Ioo a b → u t = fun _ ↦ (1 / 3 : ℝ)) ∧
      (∀ t ∈ Ioo a b, HasDerivAtEntrywise g (g t * J) t) := by
  have hL₁eq := pontryagin_costate_eq_on_zero_reducedCostate h hsub hzero
  obtain ⟨htraj, _, _, _, _, _, hlam, hcostates, hL₁I, _, _⟩ := h
  have hlamne : lam ≠ 0 := by
    intro h0
    obtain ⟨s, hs⟩ := exists_between hab
    have hsI : s ∈ Ioo a b := hs
    have hnontriv := (hcostates s (Ioo_subset_Icc_self (hsub hsI))).2.2.2
    rcases hnontriv with hnontriv | hnontriv | hnontriv
    · exact hnontriv h0
    · exact hnontriv (by simpa only [h0, mul_zero, zero_smul] using hL₁eq s hsI)
    · exact hnontriv (hzero s hsI)
  have hlamlt : lam < 0 := lt_of_le_of_ne hlam hlamne
  have hcne : (3 / 2 * lam : ℝ) ≠ 0 := mul_ne_zero (by norm_num) hlamne
  have hL₁c : ContinuousOn Λ₁ (Icc 0 T) := Matrix.continuousOn_of_eq_add_integral hL₁I
  have hXc := (stateTrajectory_continuous htraj).2
  have hvelocity : ContinuousOn (fun t ↦ Λ₁ t * X t - X t * Λ₁ t) (Icc 0 T) :=
    (hL₁c.mul hXc).sub (hXc.mul hL₁c)
  have hXeq : ∀ t ∈ Ioo a b, X t = J := by
    intro t ht
    have htT := hsub ht
    have hL₁D : HasDerivAtEntrywise Λ₁ (Λ₁ t * X t - X t * Λ₁ t) t :=
      Matrix.hasDerivAtEntrywise_of_eq_add_integral hL₁I htT
        (hvelocity.continuousAt (Icc_mem_nhds htT.1 htT.2))
    have hconstant : HasDerivAtEntrywise Λ₁ 0 t :=
      (hasDerivAtEntrywise_const ((3 / 2 * lam) • J) t).congr_of_eventuallyEq
        (Filter.eventually_of_mem (Ioo_mem_nhds ht.1 ht.2) fun s hs ↦ hL₁eq s hs)
    have hscale : (3 / 2 * lam) • (J * X t - X t * J) = 0 := by
      simpa only [hL₁eq t ht, Matrix.smul_mul, Matrix.mul_smul, smul_sub] using
        hL₁D.unique hconstant
    have hcomm : J * X t - X t * J = 0 :=
      (smul_eq_zero.mp hscale).resolve_left hcne
    exact starState_eq_J_of_commutator_zero
      (htraj.2.2.2.1 t (Ioo_subset_Icc_self htT)).2 hcomm
  have hcontrol : ∀ᵐ t, t ∈ Ioo a b → u t = fun _ ↦ (1 / 3 : ℝ) := by
    filter_upwards [stateTrajectory_state_ae_hasDerivAt htraj] with t hd ht
    have htT := hsub ht
    have hconstant : HasDerivAtEntrywise X 0 t :=
      (hasDerivAtEntrywise_const J t).congr_of_eventuallyEq
        (Filter.eventually_of_mem (Ioo_mem_nhds ht.1 ht.2) fun s hs ↦ hXeq s hs)
    have hcomm := (hd htT).unique hconstant
    rw [hXeq t ht] at hcomm
    exact circle_control_unique (htraj.2.2.1 t (Ioo_subset_Icc_self htT)) hcomm
  refine ⟨hlamlt, fun t ht ↦ ⟨hL₁eq t ht, hXeq t ht⟩, hcontrol, ?_⟩
  intro t ht
  have hd := stateTrajectory_frame_hasDerivAt htraj t (hsub ht)
  rwa [hXeq t ht] at hd

/-- The same local rigidity follows from full control independence of the
Hamiltonian. This assumption is stronger than having a nonunique maximizing edge. -/
theorem pontryagin_controlIndependent_interval_rigidity
    {T a b lam : ℝ} {u : ℝ → Fin 3 → ℝ} {g X Λ₁ ΛR : ℝ → Mat2}
    (h : IsPontryaginExtremal T u g X Λ₁ ΛR lam)
    (hab : a < b) (hsub : Ioo a b ⊆ Ioo 0 T)
    (hconstant : ∀ t ∈ Ioo a b, ∀ v ∈ controlSimplex, ∀ w ∈ controlSimplex,
      hamiltonian lam (Λ₁ t) (ΛR t) (X t) v =
        hamiltonian lam (Λ₁ t) (ΛR t) (X t) w) :
    lam < 0 ∧
      (∀ t ∈ Ioo a b, Λ₁ t = (3 / 2 * lam) • J ∧ X t = J) ∧
      (∀ᵐ t, t ∈ Ioo a b → u t = fun _ ↦ (1 / 3 : ℝ)) ∧
      (∀ t ∈ Ioo a b, HasDerivAtEntrywise g (g t * J) t) := by
  apply pontryagin_zero_reducedCostate_rigidity h hab hsub
  obtain ⟨htraj, _, _, _, _, _, _, hcostates, _, _, _⟩ := h
  intro t ht
  have htcc : t ∈ Icc 0 T := Ioo_subset_Icc_self (hsub ht)
  have hdata := hcostates t htcc
  exact (hamiltonian_constant_on_simplex_iff_reducedCostate_eq_zero lam (Λ₁ t)
    (htraj.2.2.2.1 t htcc).2 hdata.2.1 hdata.2.2.1).mp (hconstant t ht)

/-- A full control minimizer with an actual Pontryagin lift cannot have zero
reduced costate throughout its whole time interval. Proper subintervals and
isolated singular contacts are not excluded by this statement. -/
theorem controlMinimizer_reducedCostate_not_identically_zero
    {T lam : ℝ} {u : ℝ → Fin 3 → ℝ} {g X Λ₁ ΛR : ℝ → Mat2}
    (hmin : IsReinhardtMinimizer T u g X)
    (hext : IsPontryaginExtremal T u g X Λ₁ ΛR lam) :
    ¬ (∀ t ∈ Ioo 0 T, ΛR t = 0) := by
  intro hzero
  have hrigid := pontryagin_zero_reducedCostate_rigidity hext hmin.1.1.1
    (Subset.rfl : Ioo 0 T ⊆ Ioo 0 T) hzero
  exact controlMinimizer_not_circle hmin (fun t ht ↦ (hrigid.2.1 t ht).2)

end SmoothedOctagon
