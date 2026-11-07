module

public import SmoothedOctagon.Reduction.Defs
public import SmoothedOctagon.Foundations.ReverseComparison

/-!
# The compact domain along a global minimizer

COMPACT_DOMAIN_SOURCE_AUDIT (main theorem and §§1, 4) and GLOBAL_MINIMIZER_COMPACTNESS (3)
(inventory A2, §2.2, `CDSA:Main`, `CDSA:§1`, `CDSA:§4`, `GMC:(3)`). The state of every global
minimizer stays in the compact domain `𝔥**` of Hales–Vajjha, Definition 5.0.1: realize the
minimizer as a balanced disk, keeping the link `σ_j(t) = g(t) s_j*` and the cyclic shift, and apply
Hales–Vajjha, Theorem 5.0.2 (the hypothesis `Cited.HalesVajjha.Theorem5_0_2`) in the
contrapositive: the disk's area is the minimizer's cost, at most `A_oct`. Route: the notes'
repaired proof of Theorem 5.0.2 (sector reduction, `CDSA:§§2-3`) is not needed here, since
Theorem 5.0.2 is a hypothesis.

Main API:

* `cost_le_octagonCost`: a global minimizer costs at most `A_oct`.
* `volume_real_smoothedPolygonDisk_one`, `octagonCost_lt_pi`: the octagon's area is `A_oct < π`.
* `exists_linked_balanced_realization`: a low-cost admissible trajectory is the boundary
  trajectory of a balanced disk in circle representation, with `σ_j(t) = g(t) s_j*` on `[0, T]` and
  `σ_j(t + T) = σ_{j+1}(t)`, whose area is the cost.
* `inCompactDomain_of_isReinhardtMinimizer`: the state of a global minimizer stays in `𝔥**`.
* `margin_eq_two_mul_ρ`, `two_div_fifteen_le_margin`: on traceless states `p₀ = 2ρ₂`,
  `p₁ = 2ρ₁`, `p₂ = 2ρ₀`; on `𝔥**` every margin is at least `2/15` (`CDSA:§1`).
* `frobSq_lt_of_inCompactDomain`: on `𝔥**`, `‖X‖_F² < 81` (`GMC:(3)`, `‖X‖_F < √(2869/36) < 9`).
-/

@[expose] public section

namespace SmoothedOctagon.Reduction

open SmoothedPolygons MeasureTheory Set Matrix Real

/-- A global minimizer is competitive with the smoothed octagon: its cost is at most `A_oct`
(the same proof as `cost_le_octagonCost_of_isReinhardtMinimizer` in `LowerBound.lean`, which
imports this module's consumer). -/
theorem cost_le_octagonCost {T : ℝ} {u : ℝ → Fin 3 → ℝ} {g X : ℝ → Mat2}
    (hmin : IsReinhardtMinimizer T u g X) : reinhardtCost T X ≤ octagonCost := by
  have h := controlMinimizer_density_eq_minimax hmin
  have h12 : (0 : ℝ) < √12 := by positivity
  rw [div_eq_iff h12.ne'] at h
  rw [h, octagonCost, mul_comm]
  exact mul_le_mul_of_nonneg_left minimaxDensity_le_octagonDensity h12.le

/-- The area of the smoothed octagon `smoothedPolygonDisk 1` is `A_oct`. -/
theorem volume_real_smoothedPolygonDisk_one :
    volume.real (smoothedPolygonDisk 1) = octagonCost := by
  have h := smoothedOctagon_volume.2
  have h12 : (0 : ℝ) < √12 := by positivity
  rw [div_eq_iff h12.ne'] at h
  rw [measureReal_def, h, octagonCost, octagonDensity, mul_comm]

/-- `A_oct < π`. -/
theorem octagonCost_lt_pi : octagonCost < π := by
  have h := octagon_area_lt_pi
  rwa [octagon, volume_real_smoothedPolygonDisk_one] at h

/-- **Balanced realization with the frame link** (the correspondence of ADMISSIBLE_REALIZATION
and REVERSE_COMPARISON, as `lowCost_admissible_balanced_realization`, keeping the link and the
shift). A low-cost admissible trajectory is the boundary trajectory `σ_j(t) = g(t) s_j*` of a
balanced disk in circle representation, with `σ_j(t + T) = σ_{j+1}(t)`, whose area is its cost. -/
theorem exists_linked_balanced_realization {T : ℝ} {u : ℝ → Fin 3 → ℝ} {g X : ℝ → Mat2}
    (hadm : IsReinhardtAdmissible T u g X) (hcost : reinhardtCost T X < π) :
    ∃ (K : Set (Fin 2 → ℝ)) (σ : ZMod 6 → ℝ → Fin 2 → ℝ),
      IsBalancedPair K σ T ∧ IsCircleRepresentation σ ∧
      (∀ j, ∀ t ∈ Icc 0 T, σ j t = g t *ᵥ sixthRoot j) ∧ (∀ j t, σ j (t + T) = σ (j + 1) t) ∧
      volume.real K = reinhardtCost T X := by
  obtain ⟨G, Y, hagree, hGC, hYC, hYLip, hdet, hstar, hD, hG0,
      hGshift, -, -, hcurv, hcosteq⟩ :=
    exists_cyclic_extension_of_isReinhardtAdmissible hadm
  have hκ : ∀ j, ∀ᵐ t, 0 ≤ det2 (deriv (frameContact G j) t)
      (deriv (deriv (frameContact G j)) t) := by
    intro j
    filter_upwards [hcurv] with t ht
    exact ht j
  have hlow : reinhardtCost T Y < π := by rw [hcosteq]; exact hcost
  obtain ⟨hbal, hcirc⟩ := lowCost_cyclicFrame_isBalancedPair hadm.1.1 hGC hdet hYC
    hD hstar hYLip hG0 hGshift hκ hlow
  have harea : reinhardtCost T Y = volume.real (cyclicFrameDisk G T) :=
    cost_eq_area_of_balanced_cyclic hbal G Y (fun j t _ ↦ rfl)
      (fun t _ ↦ hD t) (frameContact_shift hGshift)
  refine ⟨cyclicFrameDisk G T, frameContact G, hbal, hcirc, fun j t ht ↦ ?_,
    frameContact_shift hGshift, harea.symm.trans hcosteq⟩
  simp only [frameContact, (hagree t ht).1]

/-- **The compact domain** (COMPACT_DOMAIN_SOURCE_AUDIT, main theorem, from Hales–Vajjha,
Theorem 5.0.2). The state of every global minimizer stays in `𝔥**` at every time of `[0, T]`. -/
theorem inCompactDomain_of_isReinhardtMinimizer (h502 : Cited.HalesVajjha.Theorem5_0_2)
    {T : ℝ} {u : ℝ → Fin 3 → ℝ} {g X : ℝ → Mat2} (hmin : IsReinhardtMinimizer T u g X) :
    ∀ t ∈ Icc 0 T, Cited.HalesVajjha.InCompactDomain (X t) := by
  by_contra h
  push Not at h
  have hcost := cost_le_octagonCost hmin
  obtain ⟨K, σ, hbal, hcirc, hlink, hshift, harea⟩ :=
    exists_linked_balanced_realization hmin.1 (hcost.trans_lt octagonCost_lt_pi)
  have hlt := h502 K σ T u g X hbal hcirc hlink hshift hmin.1.1 h
  rw [volume_real_smoothedPolygonDisk_one, harea] at hlt
  linarith

/-- **Margin dictionary** (COMPACT_DOMAIN_SOURCE_AUDIT §1): on traceless matrices
`p₀ = 2ρ₂`, `p₁ = 2ρ₁`, `p₂ = 2ρ₀`, i.e. `p_i = 2ρ_{2-i}`. -/
theorem margin_eq_two_mul_ρ {X : Mat2} (hX : X.trace = 0) :
    margin 0 X = 2 * ρ₂ X ∧ margin 1 X = 2 * ρ₁ X ∧ margin 2 X = 2 * ρ₀ X := by
  have h11 : X 1 1 = -X 0 0 := by rw [Matrix.trace_fin_two] at hX; linarith
  have h3 : √3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  have h3' : √3 ≠ 0 := by positivity
  refine ⟨?_, ?_, ?_⟩ <;>
  simp [margin, traceForm, controlMatrix, vertex, Matrix.trace_fin_two,
    Fin.sum_univ_two, ρ₀, ρ₁, ρ₂, h11, Matrix.vecMul, dotProduct] <;> field_simp <;> ring_nf <;>
    simp [h3] <;> ring

/-- **Margins on `𝔥**`** (COMPACT_DOMAIN_SOURCE_AUDIT §1, inventory A2 §1.3): every margin, active
or not, of a state in `𝔥**` is at least `2/15`. -/
theorem two_div_fifteen_le_margin {X : Mat2} (hX : Cited.HalesVajjha.InCompactDomain X)
    (i : Fin 3) : 2 / 15 ≤ margin i X := by
  obtain ⟨x, y, rfl, hmem⟩ := hX
  obtain ⟨-, -, -, -, h0, h1, h2⟩ := hmem
  have htr : (Φ x y).trace = 0 := by
    rw [Matrix.trace_fin_two]; simp only [Φ, Matrix.of_apply, Matrix.cons_val',
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.empty_val', Matrix.cons_val_fin_one]
    ring
  obtain ⟨e0, e1, e2⟩ := margin_eq_two_mul_ρ htr
  fin_cases i
  · simp only [Fin.zero_eta, Fin.isValue]; rw [e0]; linarith
  · simp only [Fin.mk_one, Fin.isValue]; rw [e1]; linarith
  · simp only [Fin.reduceFinMk, Fin.isValue]; rw [e2]; linarith

/-- The cusp computation of GLOBAL_MINIMIZER_COMPACTNESS (3): with `a = 1/√3 - |x|`, the star
condition gives `a/√3 < y²`, and then `y ≤ 1/5` would put `(x, y)` inside a cusp disk. -/
private lemma cusp_aux {q a y : ℝ} (hq2 : q ^ 2 = 1 / 3) (hq : 0 < q) (ha : 0 < a) (hy : 0 < y)
    (hy5 : y ≤ 1 / 5) (h1 : a * q < y ^ 2) (hc : 8 / 27 * y ≤ a ^ 2 + y ^ 2) : False := by
  have h2 : a < 3 * q * y ^ 2 := by
    have h := mul_lt_mul_of_pos_right h1 (by positivity : (0 : ℝ) < 3 * q)
    have e : a * q * (3 * q) = a := by
      rw [mul_assoc, show q * (3 * q) = 3 * q ^ 2 by ring, hq2]; ring
    rw [e] at h; linarith
  have h3 : a ^ 2 < 3 * y ^ 4 := by
    have h := mul_lt_mul'' h2 h2 ha.le ha.le
    have e : 3 * q * y ^ 2 * (3 * q * y ^ 2) = 3 * y ^ 4 := by
      rw [show 3 * q * y ^ 2 * (3 * q * y ^ 2) = 9 * q ^ 2 * y ^ 4 by ring, hq2]; ring
    rw [e] at h; nlinarith
  have hy3 : y ^ 3 ≤ 1 / 125 := by
    have := pow_le_pow_left₀ hy.le hy5 3
    norm_num at this ⊢; linarith
  have : 8 / 27 * y < 3 * y ^ 4 + y ^ 2 := by linarith
  have h4 : 8 / 27 < 3 * y ^ 3 + y := by
    have e : 3 * y ^ 4 + y ^ 2 = y * (3 * y ^ 3 + y) := by ring
    rw [e, mul_comm] at this
    exact lt_of_mul_lt_mul_left this hy.le
  linarith

/-- **State bound on `𝔥**`** (GLOBAL_MINIMIZER_COMPACTNESS (3), inventory A2 §1.3): a state in
`𝔥**` has `‖X‖_F² < 81`. (On `𝔥**`, `y > 1/5` by the two cusp disks, `|x/y| < 5/√3`,
`(x² + y²)/y < 37/6`, so `‖X‖_F² < 2869/36`.) -/
theorem frobSq_lt_of_inCompactDomain {X : Mat2} (hX : Cited.HalesVajjha.InCompactDomain X) :
    frobSq X < 81 := by
  obtain ⟨x, y, rfl, hmem⟩ := hX
  obtain ⟨⟨hy, hx1, hx2, hr⟩, hy9, hc1, hc2, -, -, -⟩ := hmem
  simp only at hy hx1 hx2 hr hy9 hc1 hc2
  have hq2 : (1 / √3) ^ 2 = 1 / 3 := by
    rw [div_pow, Real.sq_sqrt (by norm_num)]; norm_num
  have hq : 0 < 1 / √3 := by positivity
  generalize 1 / √3 = q at hq2 hq hx1 hx2 hc1 hc2
  have hx2' : x ^ 2 < 1 / 3 := by nlinarith
  -- `y > 1/5`, by the two cusp disks
  have hy5 : 1 / 5 < y := by
    by_contra hle
    push Not at hle
    rcases le_total 0 x with hx0 | hx0
    · have ha : 0 < q - x := by linarith
      have h1 : (q - x) * q < y ^ 2 := by nlinarith [mul_nonneg hx0 ha.le]
      exact cusp_aux hq2 hq ha hy hle h1 (by nlinarith)
    · have ha : 0 < q + x := by linarith
      have h1 : (q + x) * q < y ^ 2 := by nlinarith [mul_nonneg (neg_nonneg.2 hx0) ha.le]
      exact cusp_aux hq2 hq ha hy hle h1 (by nlinarith)
  have hfrob : frobSq (Φ x y) = (2 * x ^ 2 + (x ^ 2 + y ^ 2) ^ 2 + 1) / y ^ 2 := by
    simp only [frobSq, Φ, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.empty_val', Matrix.cons_val_fin_one]
    field_simp
    ring
  rw [hfrob, div_lt_iff₀ (by positivity)]
  have hs1 : 1 / 25 < y ^ 2 := by nlinarith
  have hs2 : y ^ 2 ≤ 81 / 4 := by nlinarith
  have hxy : (x ^ 2 + y ^ 2) ^ 2 ≤ (1 / 3 + y ^ 2) ^ 2 := by
    have : x ^ 2 + y ^ 2 ≤ 1 / 3 + y ^ 2 := by linarith
    exact pow_le_pow_left₀ (by positivity) this 2
  nlinarith [mul_nonneg (sub_pos.2 hs1).le (sub_nonneg.2 hs2)]

end SmoothedOctagon.Reduction
