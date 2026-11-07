module

public import SmoothedOctagon.Foundations.AdmissibleRealization
public import SmoothedOctagon.Foundations.BalancedTargets
public import SmoothedPolygons.Ch4.TerminalTime

/-!
# Cost bounds and the exact remaining control comparison

Every integral state trajectory has cost at least three times its terminal time.
An actual worst disk's constructed realization has cost at most the concrete
octagon's area, hence strictly below `π` and terminal time below `π / 3`. This
uses geometric minimality and does not assume control minimality.

For the reverse comparison, costs at least `π` already have the octagon as a
geometric competitor. The named comparison proposition is therefore
equivalent to its restriction to costs below `π`. The conditional minimizer and
target-transfer results retain that comparison as an explicit input in this module;
`ReverseComparison` supplies it from the constructed extension and geometry.

Source draft only: compilation and kernel validation have not been run.
-/

@[expose] public section

namespace SmoothedOctagon

open MeasureTheory Real Set Matrix SmoothedPolygons

/-- The determinant-one star condition bounds the cost density from below.
The identity `(c-b)^2 - 4 = (b+c)^2 + 4a^2` gives the bound directly. -/
theorem star_costDensity_ge_three {X : Mat2} (hX : IsStarState X) :
    3 ≤ -(3 / 2) * traceForm J X := by
  have hnegative := poly_traceForm_J_neg hX
  have htr := hX.1
  have hdet := hX.2.1
  rw [Matrix.trace_fin_two] at htr
  have hd : X 1 1 = -X 0 0 := by linarith
  rw [Matrix.det_fin_two, hd] at hdet
  have hJX : traceForm J X = X 0 1 - X 1 0 := by
    simp [traceForm, J, Matrix.trace_fin_two, Matrix.vecMul, dotProduct,
      Fin.sum_univ_two]
    ring
  rw [hJX] at hnegative ⊢
  have hsquare : 4 ≤ (X 1 0 - X 0 1) ^ 2 := by
    nlinarith [sq_nonneg (X 0 0), sq_nonneg (X 0 1 + X 1 0)]
  have htwo : 2 ≤ X 1 0 - X 0 1 := by nlinarith
  linarith

/-- The lower cost bound uses the integral trajectory definition itself, without
assuming smooth controls, global extensions, or a minimizing trajectory. -/
theorem stateTrajectory_cost_ge_three_mul {T : ℝ} {u : ℝ → Fin 3 → ℝ}
    {g X : ℝ → Mat2} (hst : IsStateTrajectory T u g X) :
    3 * T ≤ reinhardtCost T X := by
  obtain ⟨hT, _, _, hstar, _, hXI⟩ := hst
  have hXc : ContinuousOn X (Icc 0 T) := Matrix.continuousOn_of_eq_add_integral hXI
  have hJc : ContinuousOn (fun t ↦ traceForm J (X t)) (Icc 0 T) :=
    (continuous_const.matrix_mul continuous_id).matrix_trace.comp_continuousOn hXc
  have hbound : ∀ t ∈ Icc 0 T, 3 ≤ -(3 / 2) * traceForm J (X t) :=
    fun t ht ↦ star_costDensity_ge_three (hstar t ht).2
  have h := intervalIntegral.integral_mono_on (μ := volume) hT.le
    intervalIntegrable_const
    ((hJc.intervalIntegrable_of_Icc hT.le).const_mul (-(3 / 2))) hbound
  rw [intervalIntegral.integral_const, intervalIntegral.integral_const_mul] at h
  simpa [reinhardtCost, smul_eq_mul, mul_comm] using h

/-- Every actual state trajectory has strictly positive cost. -/
theorem stateTrajectory_cost_pos {T : ℝ} {u : ℝ → Fin 3 → ℝ}
    {g X : ℝ → Mat2} (hst : IsStateTrajectory T u g X) :
    0 < reinhardtCost T X :=
  (mul_pos (by norm_num) hst.1).trans_le (stateTrajectory_cost_ge_three_mul hst)

/-- The low-cost regime automatically bounds the terminal time. -/
theorem stateTrajectory_terminalTime_lt_pi_div_three {T : ℝ}
    {u : ℝ → Fin 3 → ℝ} {g X : ℝ → Mat2} (hst : IsStateTrajectory T u g X)
    (hcost : reinhardtCost T X < π) : T < π / 3 := by
  have h := stateTrajectory_cost_ge_three_mul hst
  linarith

/-- The concrete octagon, with its existing geometric area theorem, has area
strictly below `π`. The strict bound is inherited from the pinned candidate proof. -/
theorem octagon_area_lt_pi : volume.real octagon < π := by
  obtain ⟨hst, hg0, hX0⟩ := smoothedPolygon_isStateTrajectory 1 le_rfl
  obtain ⟨_, hval, hlt, _⟩ :=
    example7_5_smoothedOctagon.2.2.2.2 _ _ hst hg0 hX0
  have hnonneg : 0 ≤ reinhardtCost (tf 1) (smoothedPolygonX 1) := by
    rw [hval]
    exact oct_octagon_value_nonneg
  change (volume (smoothedPolygonDisk 1)).toReal < π
  rw [smoothedPolygonDisk_volume 1 le_rfl, ENNReal.toReal_ofReal hnonneg]
  exact hlt

/-- Geometric minimality already supplies the cost upper bound. It is unnecessary
to assume optimality against arbitrary admissible controls for this conclusion. -/
theorem worstDisk_realization_cost_le_octagon {K : Set (Fin 2 → ℝ)}
    (hK : IsWorstDisk K) {σ : ZMod 6 → ℝ → Fin 2 → ℝ} {T : ℝ}
    (hbal : IsBalancedPair K σ T) (hcirc : IsCircleRepresentation σ)
    {X : ℝ → Mat2} (hcost : reinhardtCost T X = volume.real K) :
    reinhardtCost T X ≤ volume.real octagon := by
  have hmin := isBalancedCircleMinimizer_of_isWorstDisk hK hbal hcirc
  have harea := hmin.2 octagon (smoothedPolygonCurve 1) (tf 1)
    octagon_isBalancedPair octagon_isCircleRepresentation
  rw [hcost]
  exact ENNReal.toReal_mono octagon_isCCSDisk.2.1.measure_lt_top.ne harea

/-- The actual geometric worst representative has a low-cost admissible
realization with the bounded terminal time required by the control analysis. -/
theorem exists_worstDisk_lowCost_realization :
    ∃ (K : Set (Fin 2 → ℝ)) (T : ℝ) (σ : ZMod 6 → ℝ → Fin 2 → ℝ)
      (g X : ℝ → Mat2),
      IsWorstDisk K ∧ IsBalancedPair K σ T ∧ IsCircleRepresentation σ ∧
      IsReinhardtAdmissible T (boundaryControl X) g X ∧
      reinhardtCost T X = volume.real K ∧
      greatestPackingDensity K = reinhardtCost T X / √12 ∧
      reinhardtCost T X ≤ volume.real octagon ∧
      reinhardtCost T X < π ∧ T < π / 3 := by
  obtain ⟨K, T, σ, g, X, hK, hbal, hcirc, hadm, hcost, hdensity⟩ :=
    exists_worstDisk_admissible_realization
  have hle := worstDisk_realization_cost_le_octagon hK hbal hcirc hcost
  have hlt := hle.trans_lt octagon_area_lt_pi
  exact ⟨K, T, σ, g, X, hK, hbal, hcirc, hadm, hcost, hdensity, hle, hlt,
    stateTrajectory_terminalTime_lt_pi_div_three hadm.1 hlt⟩

/-- The reverse-comparison interface, over the full upstream admissible class.
It allows a different geometric competitor with area no greater than the cost. -/
def AdmissibleBalancedComparison : Prop :=
  ∀ (T : ℝ) (u : ℝ → Fin 3 → ℝ) (g X : ℝ → Mat2),
    IsReinhardtAdmissible T u g X →
      ∃ (K : Set (Fin 2 → ℝ)) (σ : ZMod 6 → ℝ → Fin 2 → ℝ) (tf : ℝ),
        IsBalancedPair K σ tf ∧ IsCircleRepresentation σ ∧
        volume.real K ≤ reinhardtCost T X

/-- Only the low-cost part of the reverse comparison needs reconstruction.
The reconstruction proving it is supplied in `ReverseComparison`. -/
def LowCostBalancedComparison : Prop :=
  ∀ (T : ℝ) (u : ℝ → Fin 3 → ℝ) (g X : ℝ → Mat2),
    IsReinhardtAdmissible T u g X → reinhardtCost T X < π →
      ∃ (K : Set (Fin 2 → ℝ)) (σ : ZMod 6 → ℝ → Fin 2 → ℝ) (tf : ℝ),
        IsBalancedPair K σ tf ∧ IsCircleRepresentation σ ∧
        volume.real K ≤ reinhardtCost T X

/-- At cost at least `π`, the existing octagon is already a strictly cheaper
balanced circle competitor. No boundary reconstruction is needed in this case. -/
theorem highCost_balanced_competitor {T : ℝ} {X : ℝ → Mat2}
    (hcost : π ≤ reinhardtCost T X) :
    ∃ (K : Set (Fin 2 → ℝ)) (σ : ZMod 6 → ℝ → Fin 2 → ℝ) (tf : ℝ),
      IsBalancedPair K σ tf ∧ IsCircleRepresentation σ ∧
      volume.real K ≤ reinhardtCost T X :=
  ⟨octagon, smoothedPolygonCurve 1, tf 1, octagon_isBalancedPair,
    octagon_isCircleRepresentation, octagon_area_lt_pi.le.trans hcost⟩

/-- Exact reduction of the reverse comparison to the low-cost regime. -/
theorem admissibleBalancedComparison_iff_lowCost :
    AdmissibleBalancedComparison ↔ LowCostBalancedComparison := by
  constructor
  · intro h T u g X hadm _
    exact h T u g X hadm
  · intro h T u g X hadm
    rcases lt_or_ge (reinhardtCost T X) π with hlt | hge
    · exact h T u g X hadm hlt
    · exact highCost_balanced_competitor hge

/-- Once the explicit reverse comparison is proved, the forward realization of
an actual geometric worst disk is a minimizer of the full control problem. -/
theorem controlMinimizer_of_worstDisk_realization
    (hcomparison : AdmissibleBalancedComparison) {K : Set (Fin 2 → ℝ)}
    (hK : IsWorstDisk K) {σ : ZMod 6 → ℝ → Fin 2 → ℝ} {T : ℝ}
    (hbal : IsBalancedPair K σ T) (hcirc : IsCircleRepresentation σ)
    {u : ℝ → Fin 3 → ℝ} {g X : ℝ → Mat2}
    (hadm : IsReinhardtAdmissible T u g X)
    (hcost : reinhardtCost T X = volume.real K) : IsReinhardtMinimizer T u g X := by
  refine ⟨hadm, ?_⟩
  intro T' u' g' X' hadm'
  obtain ⟨K', σ', tf', hbal', hcirc', hbound⟩ := hcomparison T' u' g' X' hadm'
  have hmin := isBalancedCircleMinimizer_of_isWorstDisk hK hbal hcirc
  have harea : volume.real K ≤ volume.real K' :=
    ENNReal.toReal_mono hbal'.1.2.1.measure_lt_top.ne
      (hmin.2 K' σ' tf' hbal' hcirc')
  rw [hcost]
  exact harea.trans hbound

/-- The global inequality remaining in the low-cost control problem. This
proposition does not restrict switching words or assume a finite classification. -/
def LowCostControlLowerBound : Prop :=
  ∀ (T : ℝ) (u : ℝ → Fin 3 → ℝ) (g X : ℝ → Mat2),
    IsReinhardtAdmissible T u g X → reinhardtCost T X < π →
      volume.real octagon ≤ reinhardtCost T X

/-- A universal low-cost control inequality suffices for the original conjecture
already from the constructed forward realization, without the reverse comparison. -/
theorem reinhardtConjecture_of_lowCostControlLowerBound (hbound : LowCostControlLowerBound) :
    ReinhardtConjecture := by
  obtain ⟨K, T, σ, g, X, hK, hbal, hcirc, hadm, hcost, hdensity, _, hlt, _⟩ :=
    exists_worstDisk_lowCost_realization
  apply reinhardtConjecture_of_worst_disk hK
  rw [← octagon_density, greatestPackingDensity_of_isBalancedPair octagon_isBalancedPair,
    hdensity]
  exact (div_le_div_iff_of_pos_right (by positivity : 0 < √12)).mpr
    (hbound T (boundaryControl X) g X hadm hlt)

/-- Under the named reverse-comparison obligation, the low-cost control
inequality is equivalent to geometric global minimality. Neither open input is
discharged by this conditional equivalence. -/
theorem reinhardtConjecture_iff_lowCostControlLowerBound
    (hcomparison : LowCostBalancedComparison) :
    ReinhardtConjecture ↔ LowCostControlLowerBound := by
  constructor
  · intro h T u g X hadm hlt
    obtain ⟨K, σ, tf, hbal, hcirc, hcost⟩ := hcomparison T u g X hadm hlt
    have harea := reinhardtConjecture_iff_balancedAreaLowerBound.mp h K σ tf hbal hcirc
    exact (ENNReal.toReal_mono hbal.1.2.1.measure_lt_top.ne harea).trans hcost
  · exact reinhardtConjecture_of_lowCostControlLowerBound

end SmoothedOctagon
