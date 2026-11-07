module

public import SmoothedOctagon.Period.Twist
public import SmoothedOctagon.Equality.Frontier
public import SmoothedOctagon.LowerBound

/-!
# The equality case

`GLOBAL_COST_EQUALITY_ASSEMBLY` §6 and `MINIMIZER_WINDOW_AUDIT` §6.

* A worst disk is a linear image of the smoothed octagon. Normalize the worst disk, realize it by
  its own boundary trajectory (a global control minimizer by the reverse comparison), rebase and
  relabel it to the octagon's trajectory by the terminal equality, and transport the six contact
  arcs back: `K = e⁻¹ G(s) C (K_oct)`.

The converse (every invertible linear image of the octagon has density `δ_oct`) is in
`Equality/Converse.lean`.

## Helpers

* `eq_worstDisk_minimizer_realization`: a worst disk has a normalized linear image realized by a
  global control minimizer `(T, g, X)` that keeps the link `σ_j(t) = g(t) s_j*` and the cyclic shift
  `σ_j(t + T) = σ_{j+1}(t)` on all of `ℝ`.
* `eq_frame_twist_of_contact`: the link and the cyclic shift force `g(t + T) = g(t) R` on `ℝ`.
* `eq_R_pow_mulVec_sixthRoot`: `Rⁿ s_j* = s_{j+n}*`.
-/

@[expose] public section

namespace SmoothedOctagon

open SmoothedPolygons MeasureTheory Set Matrix

/-- **The realization of a worst disk, with its contact link.** Every worst disk `K` has a
normalized linear image `eK`, a balanced circle representation `σ` of `eK`, and a global control
minimizer `(T, boundaryControl X, g, X)` with `σ_j(t) = g(t) s_j*` and `σ_j(t + T) = σ_{j+1}(t)` for
every `t`, and `δ(K) = C(T, X)/√12`. -/
theorem eq_worstDisk_minimizer_realization {K : Set (Fin 2 → ℝ)} (hK : IsWorstDisk K) :
    ∃ (e : (Fin 2 → ℝ) ≃L[ℝ] (Fin 2 → ℝ)) (T : ℝ) (σ : ZMod 6 → ℝ → Fin 2 → ℝ)
      (g X : ℝ → Mat2),
      IsWorstDisk (e '' K) ∧ IsBalancedPair (e '' K) σ T ∧ IsCircleRepresentation σ ∧
      (∀ j t, σ j t = g t *ᵥ sixthRoot j) ∧ (∀ j t, σ j (t + T) = σ (j + 1) t) ∧
      IsReinhardtMinimizer T (boundaryControl X) g X ∧
      greatestPackingDensity K = reinhardtCost T X / √12 := by
  obtain ⟨e, -, T, σ, g, X, -, hK', -, hbal, hcirc, hframe, hshift, hadm, hcost, hdens⟩ :=
    worstDisk_admissible_realization hK
  exact ⟨e, T, σ, g, X, hK', hbal, hcirc, hframe, hshift,
    controlMinimizer_of_worstDisk_realization admissibleBalancedComparison hK' hbal hcirc hadm
      hcost, hdens⟩

/-- A matrix is determined by its values on `s₀*` and `s₁*`. -/
private theorem mat_eq_of_mulVec_sixthRoot {M N : Mat2}
    (h0 : M *ᵥ sixthRoot 0 = N *ᵥ sixthRoot 0) (h1 : M *ᵥ sixthRoot 1 = N *ᵥ sixthRoot 1) :
    M = N := by
  rw [algA_sixthRoot_zero] at h0
  rw [algA_sixthRoot_one] at h1
  have h3 : (0 : ℝ) < √3 := by positivity
  ext i j
  have e0 := congrFun h0 i
  have e1 := congrFun h1 i
  simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_two, Matrix.cons_val_zero,
    Matrix.cons_val_one, mul_one, mul_zero, add_zero] at e0 e1
  fin_cases j
  · exact e0
  · have : M i 1 * (√3 / 2) = N i 1 * (√3 / 2) := by linear_combination e1 - e0 / 2
    simpa [h3.ne'] using this

/-- **The frame twist from the contact link.** If `σ_j(t) = g(t) s_j*` and `σ_j(t + T) = σ_{j+1}(t)`
for every `t`, then `g(t + T) = g(t) R` for every `t`. -/
theorem eq_frame_twist_of_contact {σ : ZMod 6 → ℝ → Fin 2 → ℝ} {g : ℝ → Mat2} {T : ℝ}
    (hframe : ∀ j t, σ j t = g t *ᵥ sixthRoot j) (hshift : ∀ j t, σ j (t + T) = σ (j + 1) t)
    (t : ℝ) : g (t + T) = g t * R := by
  have key : ∀ j, g (t + T) *ᵥ sixthRoot j = (g t * R) *ᵥ sixthRoot j := by
    intro j
    rw [← hframe, hshift, hframe, ← Matrix.mulVec_mulVec, oct_R_mulVec_sixthRoot]
  exact mat_eq_of_mulVec_sixthRoot (key 0) (key 1)

/-- `Rⁿ s_j* = s_{j+n}*`. -/
theorem eq_R_pow_mulVec_sixthRoot (n : ℕ) (j : ZMod 6) :
    R ^ n *ᵥ sixthRoot j = sixthRoot (j + n) := by
  induction n generalizing j with
  | zero => simp
  | succ n ih =>
    rw [pow_succ, ← Matrix.mulVec_mulVec, oct_R_mulVec_sixthRoot, ih]
    push_cast
    ring_nf

/-- **Rigidity.** Every worst disk is an invertible linear image of the smoothed octagon. -/
theorem worstDisk_eq_linear_image (h502 : Cited.HalesVajjha.Theorem5_0_2)
    (hcov : Certificates.IntervalCovers) : AffineRigidity := by
  intro K hK
  /- The realization of `K` by its own boundary trajectory. -/
  obtain ⟨e, T, σ, g, X, hK', hbal, -, hframe, hshift, hmin, hdens⟩ :=
    eq_worstDisk_minimizer_realization hK
  obtain ⟨hKccs, -, -, -, -, -, hT, hper, -, himage⟩ := hbal
  have hgT : ∀ t, g (t + T) = g t * R := eq_frame_twist_of_contact hframe hshift
  /- Its cost is `A_oct`, by the sharp lower bound. -/
  have hcost : reinhardtCost T X = octagonCost := by
    have h1 : greatestPackingDensity K = octagonDensity := by
      rw [hK.2, ← (reinhardtConjecture h502 hcov).2, octagon_density]
    rw [h1] at hdens
    rw [octagonCost, hdens]
    field_simp
  /- The finite normal representation and the terminal equality. -/
  obtain ⟨P, s, hPT, hs0, hsT, hPg, hPcost, -, hPK⟩ := finiteNormalRepresentation h502 hmin
  have hPc : P.cost = octagonCost := hPcost.trans hcost
  obtain ⟨hPtf, r, hr⟩ := terminal_equality P (period_le_five hcov P hPc.le hPK) hPc
  have hTtf : T = tf 1 := hPT.symm.trans hPtf
  /- The frame of `eK`, rebased at `s` and relabeled by `R^r`, is the octagon's frame. -/
  have hgs : IsUnit (g s).det := by
    rw [(hmin.1.1.2.2.2.1 s ⟨hs0, hsT.le⟩).1]
    exact isUnit_one
  set M : Mat2 := g s * R ^ r with hM
  have hbase : ∀ t ∈ Ico 0 T, g (s + t) = M * smoothedPolygonG 1 t * (R ^ r)⁻¹ := by
    intro t ht
    have h1 := (hPg t (Ico_subset_Icc_self ht)).1
    rw [rebaseFrame_eq_of_twist hgT] at h1
    have h2 := (hr t (by rw [hPT]; exact Ico_subset_Icc_self ht)).1
    rw [h1] at h2
    rw [← h2, hM]
    simp only [Matrix.mul_assoc]
    rw [R_pow_mul_inv, Matrix.mul_one, ← Matrix.mul_assoc (R ^ r), R_pow_mul_inv,
      Matrix.one_mul, ← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hgs, Matrix.one_mul]
  have hall : (fun t ↦ g (s + t)) = fun t ↦ M * smoothedPolygonG 1 t * (R ^ r)⁻¹ := by
    refine eq_of_eqOn_Ico_of_twist hT (fun t ↦ ?_) (fun t ↦ ?_) hbase
    · rw [← add_assoc, hgT]
    · rw [hTtf, oct_G_add_tf le_rfl]
      simp only [Matrix.mul_assoc, (commute_R_pow_inv r).eq]
  /- The contact arcs of `eK` are the images of the octagon's arcs. -/
  have hroot : (R ^ r)⁻¹ *ᵥ sixthRoot 0 = sixthRoot (-(r : ZMod 6)) := by
    have h := eq_R_pow_mulVec_sixthRoot r (-(r : ZMod 6))
    rw [neg_add_cancel] at h
    rw [← h, Matrix.mulVec_mulVec, R_pow_inv_mul, Matrix.one_mulVec]
  have hcurve : ∀ t, σ 0 (s + t) = M *ᵥ smoothedPolygonCurve 1 (-(r : ZMod 6)) t := by
    intro t
    have h : g (s + t) = M * smoothedPolygonG 1 t * (R ^ r)⁻¹ := congrFun hall t
    rw [hframe, h, smoothedPolygonCurve, ← hroot, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec,
      Matrix.mul_assoc]
  /- The linear map `x ↦ M x`. -/
  have hdetM : IsUnit M.det := by
    rw [hM, Matrix.det_mul, det_R_pow, mul_one]
    exact hgs
  let L : (Fin 2 → ℝ) ≃ₗ[ℝ] (Fin 2 → ℝ) :=
    Matrix.toLinearEquiv' M (M.invertibleOfIsUnitDet hdetM)
  have hL : ∀ x, L x = M *ᵥ x := fun x ↦ by
    rw [← LinearEquiv.coe_coe, Matrix.toLinearEquiv'_apply, Matrix.toLin'_apply]
  let Lc : (Fin 2 → ℝ) ≃L[ℝ] (Fin 2 → ℝ) := L.toContinuousLinearEquiv
  have hLc : ∀ x, Lc x = M *ᵥ x := hL
  /- The frontiers agree. -/
  obtain ⟨-, -, -, -, -, -, hTo, hpero, -, himageo⟩ := octagon_isBalancedPair
  have hfrK : frontier (e '' K) = range (σ 0) := by
    rw [← himage 0, oct_image_Ico (by positivity) (fun t ↦ hper 0 t)]
  have hfro : frontier octagon = range (smoothedPolygonCurve 1 (-(r : ZMod 6))) := by
    rw [← himageo, oct_image_Ico (by positivity) (fun t ↦ hpero _ t)]
  have hfr : frontier (e '' K) = frontier (Lc '' octagon) := by
    have hfrL : frontier (Lc '' octagon) = Lc '' frontier octagon :=
      (Lc.toHomeomorph.image_frontier octagon).symm
    rw [hfrL, hfrK, hfro]
    ext x
    simp only [mem_range, mem_image]
    constructor
    · rintro ⟨t, rfl⟩
      refine ⟨_, ⟨t - s, rfl⟩, ?_⟩
      rw [hLc, ← hcurve, add_sub_cancel]
    · rintro ⟨_, ⟨t, rfl⟩, rfl⟩
      exact ⟨s + t, by rw [hcurve, hLc]⟩
  /- Hence `eK = M (K_oct)` and `K = e⁻¹ M (K_oct)`. -/
  have hdisk : e '' K = Lc '' octagon :=
    eq_disk_eq_of_frontier_eq hKccs (bdy_isCCSDisk_image Lc octagon_isCCSDisk) hfr
  refine ⟨L.trans e.symm.toLinearEquiv, ?_⟩
  change K = (e.symm ∘ Lc) '' octagon
  rw [image_comp]
  rw [← hdisk, e.symm_image_image]

end SmoothedOctagon
