module

public import SmoothedOctagon.Reduction.Defs
public import SmoothedOctagon.Reduction.Edge.Minimizer

/-!
# The edge bound (E4)

On a subinterval of `[0, T]` where one coordinate `u_j` of the control of a global minimizer
vanishes a.e., the control is a.e. a concatenation of at most four vertex pieces.

Main API:

* `edgeBound_of_isReinhardtMinimizer`: every global minimizer has property (E4) (`EdgeBound`).

The proof is split over `SmoothedOctagon/Reduction/Edge/`: `Calculus` (absolutely continuous
calculus, gluing of integral curves, uniqueness for `g' = gY`), `System` (the edge system and its
regularity), `BangBang` (the maximum principle's conclusions give at most four bang pieces),
`Splice` (reconstruction of edge competitors and the splice), `Minimizer` (the edge segment of a
global minimizer is a strong local minimizer of the edge problem).
-/

@[expose] public section

namespace SmoothedOctagon.Reduction

open SmoothedPolygons MeasureTheory Set Filter Edge

private lemma edge_relabelControl_injective : Function.Injective relabelControl := by
  intro v w h
  funext i
  have := congrFun h (i - 2)
  simpa [relabelControl] using this

/-- **The edge bound on the edge `u₀ = 0`.** -/
theorem edge_edgeBound_zero {T : ℝ} {u : ℝ → Fin 3 → ℝ} {g X : ℝ → Mat2}
    (hmin : IsReinhardtMinimizer T u g X) {t₀ t₁ : ℝ} (h0 : 0 ≤ t₀) (h01 : t₀ < t₁)
    (h1 : t₁ ≤ T) (hu0 : ∀ᵐ t, t ∈ Ioo t₀ t₁ → u t 0 = 0) :
    ∃ n ≤ 4, IsPiecewiseVertex u t₀ t₁ n := by
  have hSLM := edge_isStrongLocalMinimizer hmin h0 h01 h1 hu0
  have hTe : 0 < t₁ - t₀ := by linarith
  obtain ⟨ν, p, -, hlip, hN, hA, hM, hZ, -⟩ :=
    External.pontryagin_maximum_principle edge_isOpen_edgeDomain isCompact_Icc edge_isC1On_edgeField
      edge_isC1On_edgeCost hSLM
      (G := fun w : (ℝ × ℝ × ℝ) × (ℝ × ℝ × ℝ) ↦ w - (edge_refQ X t₀ 0, edge_refQ X t₀ (t₁ - t₀)))
      (contDiffAt_id.sub contDiffAt_const)
      (by rw [fderiv_sub_const, fderiv_fun_id]; exact Function.surjective_id)
      (sub_self _) (Eventually.of_forall fun _ hz ↦ sub_eq_zero.1 hz)
  obtain ⟨n, hn, τ, b, hτ0, hτn, hτlt, hτmem, hb, hae⟩ :=
    edge_bangBang hTe hSLM.2.1 hlip hN hA hM hZ
  refine ⟨n, hn, fun k ↦ t₀ + τ k, fun k ↦ if b k = 1 then 1 else 2, by simp [hτ0],
    by simp [hτn], fun k hk ↦ by simp [hτlt k hk], fun k hk ↦ ?_⟩
  have hshift := (measurePreserving_add_right volume (-t₀)).quasiMeasurePreserving.ae (hae k hk)
  filter_upwards [hshift, hu0] with t ht ht0 hmem
  have hs : t + -t₀ ∈ Ioo (τ k) (τ (k + 1)) := ⟨by linarith [hmem.1], by linarith [hmem.2]⟩
  have htI : t ∈ Ioo t₀ t₁ := ⟨by linarith [hmem.1, (hτmem k hk.le).1],
    by linarith [hmem.2, (hτmem (k + 1) hk).2]⟩
  have hv := ht hs
  simp only [edge_refV, show t₀ + (t + -t₀) = t by ring] at hv
  have h0' := ht0 htI
  have hsum := (hmin.1.1.2.2.1 t ⟨by linarith [htI.1], by linarith [htI.2]⟩).2
  funext j
  rcases hb k hk with hbk | hbk
  · have hne : b k ≠ 1 := by rw [hbk]; norm_num
    simp only [hne, ite_false]
    fin_cases j <;> simp [vertex] <;> linarith
  · simp only [hbk, ite_true]
    fin_cases j <;> simp [vertex] <;> linarith

/-- **The edge bound (E4)**. Let `(T, u, g, X)` be a global minimizer and `0 ≤ t₀ < t₁ ≤ T` with
`u_j = 0` a.e. on `(t₀, t₁)` for one `j`. Then on `[t₀, t₁]` the control is a.e. a concatenation of
at most four constant vertex pieces (with labels other than `j`).

Proof outline: rotate `j` to `0` (conjugation by `R^j`). On the edge the star state
`X = [[a, b], [c, -a]]` is determined by `(a, c)` and the frame by `x = a/c` and `s = ∫ c`. With
state `(a, c, s) = (X₀₀, X₁₀, ∫ X₁₀)` and control `v = u₁`, the segment is an admissible pair of the
edge system in physical time (`Edge/System.lean`) with the same cost; no time change is needed for
the segment or for competitors. By splicing (global minimality, competitors with any terminal time)
the segment minimizes the edge cost among edge pairs with the same end states and end frames and
free time (`Edge/Splice.lean`, `Edge/Minimizer.lean`). The free-time
`External.pontryagin_maximum_principle` then applies; its `H = 0` condition gives the nontriviality
used below (the fixed-time `theorem12_3` alone admits the multiplier `ν = 0`, `p = (c, 0, 0)`). The
switching function is `σ = p(a, c, 0)` with `σ' = -c (2 p_s + 3ν(1 + x²))`, `x = a/c` strictly
increasing, obtained from the adjoint equation, the homogeneity of the field in `(a, c)` and
`H = 0`; `v = 1` where `σ > 0` and `v = 0` where `σ < 0`. A nonzero quadratic in `x` has at most two
zeros, so `σ` has at most three (Rolle), and if `ν = p_s = 0` then `σ` is a nonzero constant: at
most four bang pieces (`Edge/BangBang.lean`). -/
theorem edgeBound_of_isReinhardtMinimizer {T : ℝ} {u : ℝ → Fin 3 → ℝ} {g X : ℝ → Mat2}
    (hmin : IsReinhardtMinimizer T u g X) : EdgeBound T u := by
  intro t₀ t₁ h0 h01 h1 j hj
  have hmin' : IsReinhardtMinimizer T (fun t ↦ relabelControl^[2 * j.val] (u t))
      (fun t ↦ (R ^ (2 * j.val))⁻¹ * g t * R ^ (2 * j.val))
      (fun t ↦ (R ^ (2 * j.val))⁻¹ * X t * R ^ (2 * j.val)) := by
    refine ⟨isReinhardtAdmissible_relabel hmin.1 _, fun T' u' g' X' h' ↦ ?_⟩
    rw [reinhardtCost_relabel]
    exact hmin.2 T' u' g' X' h'
  have hj0 : (0 : Fin 3) - Fin.ofNat 3 (2 * j.val) = j := by
    fin_cases j <;> decide
  have hj' : ∀ᵐ t, t ∈ Ioo t₀ t₁ → relabelControl^[2 * j.val] (u t) 0 = 0 := by
    filter_upwards [hj] with t ht hmem
    rw [relabelControl_iterate_apply, hj0]
    exact ht hmem
  obtain ⟨n, hn, τ, l, hτ0, hτn, hτlt, hl⟩ := edge_edgeBound_zero hmin' h0 h01 h1 hj'
  refine ⟨n, hn, τ, fun k ↦ l k - Fin.ofNat 3 (2 * j.val), hτ0, hτn, hτlt, fun k hk ↦ ?_⟩
  filter_upwards [hl k hk] with t ht hmem
  apply edge_relabelControl_injective.iterate (2 * j.val)
  rw [ht hmem, relabelControl_iterate_vertex, sub_add_cancel]

end SmoothedOctagon.Reduction
