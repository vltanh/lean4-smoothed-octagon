module

public import SmoothedOctagon.Reduction.Defs
public import SmoothedOctagon.Foundations.ReverseComparison
public import SmoothedPolygons.Ch5.Theorem502

/-!
# The compact domain along a global minimizer

COMPACT_DOMAIN_SOURCE_AUDIT (main theorem and §§1, 4) and GLOBAL_MINIMIZER_COMPACTNESS (3)
(inventory A2, §2.2, `CDSA:Main`, `CDSA:§1`, `CDSA:§4`, `GMC:(3)`). The state of every global
minimizer stays in the compact domain `𝔥**` of Hales–Vajjha, Definition 5.0.1. This module is the
bridge to Hales–Vajjha's Theorem 5.0.2, proved in `SmoothedPolygons` as
`SmoothedPolygons.theorem5_0_2` (`Ch5/Theorem502.lean`): extend the minimizer cyclically to a
global trajectory `(G, Y)` of the same cost (`exists_cyclic_extension_of_isReinhardtAdmissible`),
whose frame contacts `σ_j(t) = G(t) s_j*` bound a balanced disk at every time
(`lowCost_cyclicFrame_isBalancedPair`), with `Y = G⁻¹G'` and `Y = Φ ∘ z`, `z` in `𝔥*`, everywhere;
then apply Theorem 5.0.2 in the contrapositive: leaving `𝔥**` would make the cost exceed `A_oct`.
Route: the notes' repaired proof of Theorem 5.0.2 (sector reduction, `CDSA:§§2-3`) is replaced by
the one in `SmoothedPolygons`.

Main API:

* `cost_le_octagonCost`: a global minimizer costs at most `A_oct`.
* `volume_real_smoothedPolygonDisk_one`, `octagonCost_lt_pi`: the octagon's area is `A_oct < π`.
* `compactDomain_eq_truncatedStarDomain`: `𝔥**` written with the star functions
  (`Cited.HalesVajjha.compactDomain`) is `SmoothedPolygons.truncatedStarDomain`.
* `exists_mem_starDomain_eq_Φ`: a star state is `Φ(z)` with `z ∈ 𝔥*`.
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

/-! ### `𝔥**` in the two vocabularies -/

private lemma ρ₀_Φ (x y : ℝ) : ρ₀ (Φ x y) = (x + 1 / √3) / y := by
  have h3 : √3 ≠ 0 := by positivity
  simp only [ρ₀, Φ, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.empty_val', Matrix.cons_val_fin_one]
  rcases eq_or_ne y 0 with rfl | hy
  · simp
  field_simp
  ring

private lemma ρ₁_Φ (x y : ℝ) : ρ₁ (Φ x y) = (1 / √3 - x) / y := by
  have h3 : √3 ≠ 0 := by positivity
  simp only [ρ₁, Φ, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.empty_val', Matrix.cons_val_fin_one]
  rcases eq_or_ne y 0 with rfl | hy
  · simp
  field_simp

private lemma ρ₂_Φ (x y : ℝ) : ρ₂ (Φ x y) = √3 / 2 * (x ^ 2 + y ^ 2 - 1 / 3) / y := by
  have h3 : √3 ≠ 0 := by positivity
  have h3sq : √3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  simp only [ρ₂, Φ, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.empty_val', Matrix.cons_val_fin_one]
  rcases eq_or_ne y 0 with rfl | hy
  · simp
  field_simp
  ring_nf
  rw [h3sq]
  ring

/-- **`𝔥**` in the two vocabularies** (Definition 5.0.1). `Cited.HalesVajjha.compactDomain` (the
cusp disks `8y/27 ≤ (x ∓ 1/√3)² + y²` and the star functions `ρⱼ(Φ(z)) ≥ 1/15`) is
`truncatedStarDomain` of `SmoothedPolygons` (the horoballs and the edge half-planes, in the explicit
form `truncatedStarDomain_eq`): `ρ₀(Φ(z)) = (x + 1/√3)/y`, `ρ₁(Φ(z)) = (1/√3 - x)/y` and
`ρ₂(Φ(z)) = (√3/2)(x² + y² - 1/3)/y`. -/
theorem compactDomain_eq_truncatedStarDomain :
    Cited.HalesVajjha.compactDomain = truncatedStarDomain := by
  rw [truncatedStarDomain_eq]
  ext ⟨x, y⟩
  simp only [Cited.HalesVajjha.compactDomain, mem_ofPred_eq, ρ₀_Φ, ρ₁_Φ, ρ₂_Φ]
  have h3sq : √3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  have e : 2 * y / (15 * √3) = 2 / 3 * √3 * (1 / 15 * y) := by
    field_simp
    rw [h3sq]
  have e2 : 2 / 3 * √3 * (√3 / 2 * (x ^ 2 + y ^ 2 - 1 / 3)) = x ^ 2 + y ^ 2 - 1 / 3 := by
    have : 2 / 3 * √3 * (√3 / 2 * (x ^ 2 + y ^ 2 - 1 / 3)) =
        √3 ^ 2 / 3 * (x ^ 2 + y ^ 2 - 1 / 3) := by ring
    rw [this, h3sq]
    ring
  have hpos : (0 : ℝ) < 2 / 3 * √3 := by positivity
  constructor
  · rintro ⟨hz, h1, h2, h3, h4, h5, h6⟩
    have hy : 0 < y := hz.1
    rw [le_div_iff₀ hy] at h4 h5 h6
    refine ⟨hz, h1, by nlinarith, by nlinarith, by linarith, ?_, by linarith⟩
    have := mul_le_mul_of_nonneg_left h6 hpos.le
    rw [e2] at this
    rw [e]
    linarith
  · rintro ⟨hz, h1, h2, h3, h4, h5, h6⟩
    have hy : 0 < y := hz.1
    refine ⟨hz, h1, by nlinarith, by nlinarith, ?_, ?_, ?_⟩ <;> rw [le_div_iff₀ hy]
    · linarith
    · linarith
    · rw [e] at h5
      have h7 : 2 / 3 * √3 * (1 / 15 * y) ≤ 2 / 3 * √3 * (√3 / 2 * (x ^ 2 + y ^ 2 - 1 / 3)) := by
        rw [e2]; linarith
      exact le_of_mul_le_mul_left h7 hpos

/-- A star state is `Φ(z)` for some `z ∈ 𝔥*` (Lemmas 4.1.1, 4.2.1 and Theorem 4.4.1). -/
theorem exists_mem_starDomain_eq_Φ {X : Mat2} (hX : IsStarState X) :
    ∃ z ∈ starDomain, X = Φ z.1 z.2 := by
  have hmem : X ∈ adjointOrbit J := by
    rw [← lemma4_1_1]
    exact ⟨hX.1, hX.2.1, poly_traceForm_J_neg hX⟩
  obtain ⟨z, -, hz⟩ := lemma4_2_1.surjOn hmem
  have hX' : X = Φ z.re z.im := by rw [← hz, ΦH]
  exact ⟨(z.re, z.im), (theorem4_4_1 _ _ z.im_pos).1 (hX' ▸ hX), hX'⟩

/-! ### The compact domain from Theorem 5.0.2 -/

/-- **The compact domain** (COMPACT_DOMAIN_SOURCE_AUDIT, main theorem, from Hales–Vajjha,
Theorem 5.0.2, `SmoothedPolygons.theorem5_0_2`). The state of every global minimizer stays in `𝔥**`
at every time of `[0, T]`.

Proof: the cyclic extension `(G, Y)` of the minimizer
(`exists_cyclic_extension_of_isReinhardtAdmissible`) agrees with `(g, X)` on `[0, T]`, has the
same cost, `G' = GY` and `Y` a star state at every time, and `G(t + T) = G(t) R`; its frame
contacts `σ_j = G s_j*` bound a balanced disk (`lowCost_cyclicFrame_isBalancedPair`, the cost being
at most `A_oct < π`). These are the global hypotheses of `theorem5_0_2` (`Y = G⁻¹G'` since
`det G = 1`, and `Y = Φ ∘ z` with `z` in `𝔥*` by `exists_mem_starDomain_eq_Φ`), which then puts
the cost strictly above `A_oct` if `X(t₀) = Y(t₀)` leaves `𝔥** = truncatedStarDomain`. -/
theorem inCompactDomain_of_isReinhardtMinimizer {T : ℝ} {u : ℝ → Fin 3 → ℝ} {g X : ℝ → Mat2}
    (hmin : IsReinhardtMinimizer T u g X) :
    ∀ t ∈ Icc 0 T, Cited.HalesVajjha.InCompactDomain (X t) := by
  intro t₀ ht₀
  by_contra hout
  have hcost := cost_le_octagonCost hmin
  -- the global cyclic extension `(G, Y)` of the minimizer, and its balanced disk
  obtain ⟨G, Y, hagree, hGC, hYC, hYLip, hdet, hstar, hD, hG0,
      hGshift, -, -, hcurv, hcosteq⟩ :=
    exists_cyclic_extension_of_isReinhardtAdmissible hmin.1
  have hκ : ∀ j, ∀ᵐ t, 0 ≤ det2 (deriv (frameContact G j) t)
      (deriv (deriv (frameContact G j)) t) := by
    intro j
    filter_upwards [hcurv] with t ht
    exact ht j
  have hlow : reinhardtCost T Y < π := by
    rw [hcosteq]; exact hcost.trans_lt octagonCost_lt_pi
  obtain ⟨hbal, -⟩ := lowCost_cyclicFrame_isBalancedPair hmin.1.1.1 hGC hdet hYC
    hD hstar hYLip hG0 hGshift hκ hlow
  -- `Y = G⁻¹G'` and `Y = Φ ∘ z` with `z` in `𝔥*`, at every time
  have hY : ∀ t, Y t = (G t)⁻¹ * derivEntrywise G t := by
    intro t
    rw [(hD t).derivEntrywise, ← Matrix.mul_assoc,
      Matrix.nonsing_inv_mul _ (by rw [hdet t]; exact isUnit_one), Matrix.one_mul]
  choose z hzD hzΦ using fun t ↦ exists_mem_starDomain_eq_Φ (hstar t)
  -- the state leaves `𝔥**` at `t₀`
  have hz₀ : z t₀ ∉ truncatedStarDomain := by
    intro hmem
    refine hout ⟨(z t₀).1, (z t₀).2, ?_, compactDomain_eq_truncatedStarDomain ▸ hmem⟩
    rw [← (hagree t₀ ht₀).2, hzΦ t₀]
  -- Theorem 5.0.2: then the cost exceeds the area `A_oct` of the smoothed octagon
  have hlt := (theorem5_0_2 hbal (fun j t ↦ rfl) (frameContact_shift hGshift) hY
    (fun t ↦ ⟨hzD t, hzΦ t⟩) hz₀).1
  rw [volume_real_smoothedPolygonDisk_one, hcosteq] at hlt
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
