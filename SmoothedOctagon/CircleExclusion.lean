module

public import SmoothedOctagon.ReverseComparison

/-!
# Excluding a circular state on the entire minimizing interval

An actual integral-admissible trajectory whose state is `J` throughout `(0,T)`
has cost at least `π`. The proof uses the constructed global cyclic extension,
the unit angular speed of its reflected first row on that interval, and the
primary-winding theorem for costs below `π`. No regularity of the original
trajectory outside `[0,T]` is assumed.

Every full control minimizer has cost strictly below `π`, by comparison with
the already constructed low-cost admissible competitor. Consequently its
state differs from `J` somewhere in `(0,T)`. This excludes only an entirely
circular trajectory; it says nothing about proper circular subarcs.

Source draft only: Lean compilation and kernel validation have not been run.
-/

@[expose] public section

namespace SmoothedOctagon

open MeasureTheory Real Set Matrix PlaneCurve SmoothedPolygons

/-- Equality to the circle state only on the open interval already determines
the cost. Endpoint values do not affect the integral. -/
theorem reinhardtCost_eq_three_mul_of_circle {T : ℝ} {X : ℝ → Mat2}
    (hT : 0 ≤ T) (hcircle : ∀ t ∈ Ioo 0 T, X t = J) :
    reinhardtCost T X = 3 * T := by
  have hi : (∫ t in (0 : ℝ)..T, traceForm J (X t)) =
      ∫ _ in (0 : ℝ)..T, (-2 : ℝ) := by
    apply intervalIntegral.integral_congr_Ioo_of_le hT
    intro t ht
    simp only [hcircle t ht]
    norm_num [traceForm, J, Matrix.trace_fin_two, Matrix.mul_apply, Fin.sum_univ_two]
  unfold reinhardtCost
  rw [hi, intervalIntegral.integral_const]
  simp only [sub_zero, smul_eq_mul]
  ring

/-- A circle state gives unit angular speed to the reflected first row. -/
theorem reflectedFirstRow_angularSpeed_eq_one {g X : ℝ → Mat2}
    (hdet : ∀ t, (g t).det = 1)
    (hg : ∀ t, HasDerivAtEntrywise g (g t * X t) t)
    (hstar : ∀ t, IsStarState (X t)) {t : ℝ} (hJ : X t = J) :
    (sc_logDeriv (reflectedFirstRow g) t).im = 1 := by
  have hz := reflectedFirstRow_ne_zero hdet t
  have hn : Complex.normSq (sc_toC (reflectedFirstRow g t)) ≠ 0 :=
    (Complex.normSq_pos.mpr (fun h ↦ hz (sc_toC_eq_zero.mp h))).ne'
  have hnum : starRowQuadratic J (reflectedFirstRow g t) =
      Complex.normSq (sc_toC (reflectedFirstRow g t)) := by
    simp [starRowQuadratic, J, Complex.normSq_apply, sc_toC_re, sc_toC_im, pow_two]
  rw [sc_logDeriv_im, reflectedFirstRow_cross hg hstar t, hJ, hnum, div_self hn]

/-- If the state is circular throughout `(0,T)`, its continuous reflected-row
angle lift has advanced by exactly `T`. This does not use an endpoint angle. -/
theorem reflectedFirstRow_angle_eq_terminalTime_of_circle {g X : ℝ → Mat2} {T : ℝ}
    (hT : 0 ≤ T) (hgc : ∀ i j, ContDiff ℝ 1 (fun t ↦ g t i j))
    (hdet : ∀ t, (g t).det = 1)
    (hg : ∀ t, HasDerivAtEntrywise g (g t * X t) t)
    (hstar : ∀ t, IsStarState (X t))
    (hcircle : ∀ t ∈ Ioo 0 T, X t = J) :
    sc_angle (reflectedFirstRow g) T = T := by
  have hγ := reflectedFirstRow_contDiff hgc
  have hne := reflectedFirstRow_ne_zero hdet
  have hc := Complex.continuous_im.comp (continuous_logDeriv_of_contDiff hγ hne)
  have hangle : (∫ t in (0 : ℝ)..T, (sc_logDeriv (reflectedFirstRow g) t).im) =
      sc_angle (reflectedFirstRow g) T := by
    have hi := intervalIntegral.integral_eq_sub_of_hasDerivAt
      (fun t _ ↦ hasDerivAt_angle_of_contDiff hγ hne t)
      (hc.intervalIntegrable 0 T)
    simpa only [sc_angle_zero, sub_zero] using hi
  have hconstant : (∫ t in (0 : ℝ)..T, (sc_logDeriv (reflectedFirstRow g) t).im) =
      ∫ _ in (0 : ℝ)..T, (1 : ℝ) :=
    intervalIntegral.integral_congr_Ioo_of_le hT
      (fun t ht ↦ reflectedFirstRow_angularSpeed_eq_one hdet hg hstar (hcircle t ht))
  rw [hangle, intervalIntegral.integral_const] at hconstant
  simpa only [sub_zero, smul_eq_mul, mul_one] using hconstant

/-- No actual admissible trajectory of cost below `π` is circular on its
entire open interval. The input trajectories need only satisfy the upstream
integral equations with an arbitrary measurable simplex control. -/
theorem lowCost_admissible_not_circle {T : ℝ} {u : ℝ → Fin 3 → ℝ}
    {g X : ℝ → Mat2} (hadm : IsReinhardtAdmissible T u g X)
    (hcost : reinhardtCost T X < π) :
    ¬ (∀ t ∈ Ioo 0 T, X t = J) := by
  intro hcircle
  have hT : 0 < T := hadm.1.1
  obtain ⟨G, Y, hagree, hGC, hYC, _, hdet, hstar, hD, hG0,
      _, _, _, _, hcosteq⟩ := exists_cyclic_extension_of_isReinhardtAdmissible hadm
  have hGT : G T = R :=
    (hagree T ⟨hT.le, le_rfl⟩).1.trans hadm.2.2.1
  have hYJ : ∀ t ∈ Ioo 0 T, Y t = J := by
    intro t ht
    exact (hagree t (Ioo_subset_Icc_self ht)).2.trans (hcircle t ht)
  have hlow : reinhardtCost T Y < π := by rw [hcosteq]; exact hcost
  have hprimary := lowCost_reflectedFirstRow_angle hT hGC hdet hYC
    hD hstar hG0 hGT hlow
  have htime := reflectedFirstRow_angle_eq_terminalTime_of_circle hT.le hGC hdet
    hD hstar hYJ
  have hcirclecost := reinhardtCost_eq_three_mul_of_circle hT.le hcircle
  linarith

/-- Every actual admissible entirely circular trajectory costs at least `π`.
Extra turns, if present, cannot give a cheaper circular trajectory. -/
theorem admissible_circle_cost_ge_pi {T : ℝ} {u : ℝ → Fin 3 → ℝ}
    {g X : ℝ → Mat2} (hadm : IsReinhardtAdmissible T u g X)
    (hcircle : ∀ t ∈ Ioo 0 T, X t = J) : π ≤ reinhardtCost T X := by
  by_contra h
  exact lowCost_admissible_not_circle hadm (lt_of_not_ge h) hcircle

/-- Minimality against the constructed low-cost admissible competitor supplies
the strict bound for every full control minimizer. -/
theorem controlMinimizer_cost_lt_pi {T : ℝ} {u : ℝ → Fin 3 → ℝ}
    {g X : ℝ → Mat2} (hmin : IsReinhardtMinimizer T u g X) :
    reinhardtCost T X < π := by
  obtain ⟨K, S, σ, G, Y, _, _, _, hadm, _, _, _, hlt, _⟩ :=
    exists_worstDisk_lowCost_realization
  exact (hmin.2 S (boundaryControl Y) G Y hadm).trans_lt hlt

/-- An entirely circular trajectory cannot be a full control minimizer.
This statement does not exclude a circle state on a proper subinterval. -/
theorem controlMinimizer_not_circle {T : ℝ} {u : ℝ → Fin 3 → ℝ}
    {g X : ℝ → Mat2} (hmin : IsReinhardtMinimizer T u g X) :
    ¬ (∀ t ∈ Ioo 0 T, X t = J) :=
  lowCost_admissible_not_circle hmin.1 (controlMinimizer_cost_lt_pi hmin)

/-- Every full control minimizer has an interior state different from `J`. -/
theorem controlMinimizer_exists_non_circle_state {T : ℝ} {u : ℝ → Fin 3 → ℝ}
    {g X : ℝ → Mat2} (hmin : IsReinhardtMinimizer T u g X) :
    ∃ t ∈ Ioo 0 T, X t ≠ J := by
  classical
  by_contra h
  apply controlMinimizer_not_circle hmin
  intro t ht
  by_contra hne
  exact h ⟨t, ht, hne⟩

end SmoothedOctagon
