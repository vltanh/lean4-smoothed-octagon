module

public import SmoothedOctagon.Period.Twist
public import SmoothedOctagon.Period.VertexFlow
public import Cited.HalesVajjha.CompactDomain

/-!
# The reflection of `𝔰𝔩₂` and the reversal of time

The reflection `S = reflS = diag(-1, 1)` acts on
`𝔰𝔩₂` by `X ↦ -S X S` (`extr_rev`) and on controls by exchanging the components `1` and `2`
(`extr_reflControl`, `(σ v)_j = v_{-j}`), so that `Z_{σ v} = -S Z_v S`. This map fixes `J`, preserves
the trace form, the determinant and the Hamiltonian, reverses the Lie bracket, maps the margin `p_i`
to `p_{-i}`, the star functions `ρ₀, ρ₁, ρ₂` to `ρ₁, ρ₀, ρ₂`, `Φ(x, y)` to `Φ(-x, y)` and `𝔥**` to
itself. Together with the reversal of time `t ↦ T - t` it is a symmetry of the Pontryagin system.

## Main API

* `extr_rev`, `extr_rev_apply`, `extr_rev_add`, `extr_rev_sub`, `extr_rev_neg`, `extr_rev_smul`,
  `extr_rev_combo`, `extr_rev_J`,
  `extr_rev_bracket` (`[S'A, S'B] = -S'[A, B]`), `extr_traceForm_rev`, `extr_trace_rev`, `extr_det_rev`.
* `extr_reflControl`, `extr_reflControl_reflControl`, `extr_reflControl_mem`, `measurable_wx_reflControl`,
  `extr_reflControl_vertex` (`σ e_i = e_{-i}`), `extr_controlMatrix_refl`, `extr_controlP_refl`,
  `extr_hamiltonian_refl`.
* `extr_margin_rev` (`p_{-i}(S'X) = p_i(X)`), `extr_isStarState_rev`, `extr_rev_Φ`,
  `extr_inCompactDomain_rev`.
* `extr_reflS_mul_self`, `extr_reflS_Rinv_reflS` (`S R⁻¹ S = R`), `extr_rev_twist`
  (`R⁻¹ S'(R⁻¹ X R) R = S' X`), `extr_det_reflS_Rinv`.
* `extr_isIntegralCurve_rev` (time reversal of a Carathéodory solution),
  `extr_isIntegralCurve_wx_rev`, `extr_ae_rev` (pull-back of an a.e. property by `t ↦ T - t`).
-/

@[expose] public section

namespace SmoothedOctagon

open SmoothedPolygons MeasureTheory Set

/-! ### The reflection on matrices -/

/-- The reflection `X ↦ -S X S` of `𝔰𝔩₂`, `S = diag(-1, 1)`. -/
noncomputable def extr_rev (A : Mat2) : Mat2 := -(reflS * A * reflS)

theorem extr_rev_apply (A : Mat2) : extr_rev A = !![-A 0 0, A 0 1; A 1 0, -A 1 1] := by
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [extr_rev, reflS, Matrix.mul_apply, Fin.sum_univ_two, Matrix.vecMul, dotProduct]

theorem extr_rev_eq_mul (A : Mat2) : extr_rev A = -reflS * A * reflS := by
  rw [extr_rev, Matrix.neg_mul, Matrix.neg_mul]

theorem extr_rev_add (A B : Mat2) : extr_rev (A + B) = extr_rev A + extr_rev B := by
  simp only [extr_rev, Matrix.mul_add, Matrix.add_mul, neg_add]

theorem extr_rev_neg (A : Mat2) : extr_rev (-A) = -extr_rev A := by
  simp only [extr_rev, Matrix.mul_neg, Matrix.neg_mul]

theorem extr_rev_sub (A B : Mat2) : extr_rev (A - B) = extr_rev A - extr_rev B := by
  rw [sub_eq_add_neg, extr_rev_add, extr_rev_neg, ← sub_eq_add_neg]

theorem extr_rev_smul (c : ℝ) (A : Mat2) : extr_rev (c • A) = c • extr_rev A := by
  simp only [extr_rev, Matrix.mul_smul, Matrix.smul_mul, smul_neg]

/-- The reflection of a combination `A - k B + C`, with reversed sign. -/
theorem extr_rev_combo (A B C : Mat2) (k : ℝ) :
    -extr_rev (A - k • B + C) = -extr_rev A - k • -extr_rev B + -extr_rev C := by
  rw [extr_rev_add, extr_rev_sub, extr_rev_smul, smul_neg]
  abel

theorem extr_rev_J : extr_rev J = J := by
  rw [extr_rev_apply]; ext i j; fin_cases i <;> fin_cases j <;> simp [J]

theorem extr_rev_rev (A : Mat2) : extr_rev (extr_rev A) = A := by
  rw [extr_rev_apply, extr_rev_apply]; ext i j; fin_cases i <;> fin_cases j <;> simp

/-- The reflection reverses the Lie bracket. -/
theorem extr_rev_bracket (A B : Mat2) :
    extr_rev A * extr_rev B - extr_rev B * extr_rev A = -extr_rev (A * B - B * A) := by
  rw [extr_rev_apply, extr_rev_apply, extr_rev_apply]
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two] <;> try ring

theorem extr_traceForm_rev (A B : Mat2) : traceForm (extr_rev A) (extr_rev B) = traceForm A B := by
  rw [extr_rev_apply, extr_rev_apply, traceForm, traceForm]
  simp [Matrix.trace_fin_two, Matrix.mul_apply, Fin.sum_univ_two]

theorem extr_trace_rev (A : Mat2) : (extr_rev A).trace = -A.trace := by
  rw [extr_rev_apply]; simp [Matrix.trace_fin_two]; try ring

theorem extr_det_rev (A : Mat2) : (extr_rev A).det = A.det := by
  rw [extr_rev_apply, Matrix.det_fin_two_of, Matrix.det_fin_two]; ring

/-! ### The reflection on controls -/

/-- The reflection of a control: `(σ v)_j = v_{-j}`, exchanging the components `1` and `2`. -/
def extr_reflControl (v : Fin 3 → ℝ) : Fin 3 → ℝ := fun j ↦ v (-j)

@[simp] theorem extr_reflControl_zero (v : Fin 3 → ℝ) : extr_reflControl v 0 = v 0 := rfl

@[simp] theorem extr_reflControl_one (v : Fin 3 → ℝ) : extr_reflControl v 1 = v 2 := rfl

@[simp] theorem extr_reflControl_two (v : Fin 3 → ℝ) : extr_reflControl v 2 = v 1 := rfl

theorem extr_reflControl_reflControl (v : Fin 3 → ℝ) : extr_reflControl (extr_reflControl v) = v := by
  funext j; simp [extr_reflControl]

theorem extr_reflControl_mem {v : Fin 3 → ℝ} (hv : v ∈ controlSimplex) :
    extr_reflControl v ∈ controlSimplex := by
  refine ⟨fun i ↦ hv.1 _, ?_⟩
  simp only [extr_reflControl_zero, extr_reflControl_one, extr_reflControl_two]
  linarith [hv.2]

theorem measurable_wx_reflControl : Measurable extr_reflControl :=
  Measurable.of_eval fun j ↦ measurable_pi_apply (-j)

theorem extr_reflControl_vertex (i : Fin 3) : extr_reflControl (vertex i) = vertex (-i) := by
  funext j
  simp only [extr_reflControl, vertex, Pi.single_apply, neg_eq_iff_eq_neg]

/-- `Z_{σ v} = -S Z_v S`. -/
theorem extr_controlMatrix_refl (v : Fin 3 → ℝ) :
    controlMatrix (extr_reflControl v) = extr_rev (controlMatrix v) := by
  rw [extr_rev_apply]
  ext i j; fin_cases i <;> fin_cases j <;> simp [controlMatrix] <;> ring

theorem extr_controlP_refl (v : Fin 3 → ℝ) (X : Mat2) :
    controlP (extr_reflControl v) (extr_rev X) = extr_rev (controlP v X) := by
  rw [controlP, controlP, extr_controlMatrix_refl, extr_traceForm_rev, extr_rev_smul]

/-- The reflection preserves the Hamiltonian. -/
theorem extr_hamiltonian_refl (lam : ℝ) (Λ₁ ΛR X : Mat2) (v : Fin 3 → ℝ) :
    hamiltonian lam (extr_rev Λ₁) (extr_rev ΛR) (extr_rev X) (extr_reflControl v) =
      hamiltonian lam Λ₁ ΛR X v := by
  have e : extr_rev Λ₁ - (3 / 2 * lam) • J = extr_rev (Λ₁ - (3 / 2 * lam) • J) := by
    rw [extr_rev_sub, extr_rev_smul, extr_rev_J]
  rw [hamiltonian, hamiltonian, extr_controlMatrix_refl, extr_traceForm_rev, extr_traceForm_rev, e,
    extr_traceForm_rev]

/-! ### Margins, star states and `𝔥**` -/

/-- The reflection maps the margin `p_i` to `p_{-i}`. -/
theorem extr_margin_rev (i : Fin 3) (X : Mat2) : margin (-i) (extr_rev X) = margin i X := by
  rw [margin, margin, ← extr_reflControl_vertex, extr_controlMatrix_refl, extr_traceForm_rev]

theorem extr_ρ_rev (X : Mat2) :
    ρ₀ (extr_rev X) = ρ₁ X ∧ ρ₁ (extr_rev X) = ρ₀ X ∧ ρ₂ (extr_rev X) = ρ₂ X := by
  rw [extr_rev_apply]
  refine ⟨?_, ?_, ?_⟩ <;> simp [ρ₀, ρ₁, ρ₂, sub_eq_add_neg]

theorem extr_isStarState_rev {X : Mat2} (hX : IsStarState X) : IsStarState (extr_rev X) := by
  obtain ⟨htr, hdet, h0, h1, h2⟩ := hX
  obtain ⟨e0, e1, e2⟩ := extr_ρ_rev X
  refine ⟨by rw [extr_trace_rev, htr, neg_zero], by rw [extr_det_rev, hdet], ?_, ?_, ?_⟩
  · rw [e0]; exact h1
  · rw [e1]; exact h0
  · rw [e2]; exact h2

theorem extr_rev_Φ (x y : ℝ) : extr_rev (Φ x y) = Φ (-x) y := by
  rw [extr_rev_apply]; ext i j; fin_cases i <;> fin_cases j <;> simp [Φ] <;> ring

/-- `𝔥**` is symmetric under the reflection. -/
theorem extr_inCompactDomain_rev {X : Mat2} (hX : Cited.HalesVajjha.InCompactDomain X) :
    Cited.HalesVajjha.InCompactDomain (extr_rev X) := by
  obtain ⟨x, y, rfl, hmem⟩ := hX
  obtain ⟨⟨hy, hx1, hx2, hxy⟩, hy9, hd1, hd2, h0, h1, h2⟩ := hmem
  obtain ⟨e0, e1, e2⟩ := extr_ρ_rev (Φ x y)
  rw [extr_rev_Φ] at e0 e1 e2
  refine ⟨-x, y, extr_rev_Φ x y, ⟨hy, ?_, ?_, ?_⟩, hy9, ?_, ?_, ?_, ?_, ?_⟩ <;> simp only at *
  · linarith
  · linarith
  · rw [neg_sq]; exact hxy
  · rw [show (-x - 1 / √3) ^ 2 = (x + 1 / √3) ^ 2 by ring]; exact hd2
  · rw [show (-x + 1 / √3) ^ 2 = (x - 1 / √3) ^ 2 by ring]; exact hd1
  · rw [e0]; exact h1
  · rw [e1]; exact h0
  · rw [e2]; exact h2

/-! ### The reflection and the rotation `R` -/

theorem extr_reflS_mul_self : reflS * reflS = 1 := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [reflS]

/-- `S R⁻¹ S = R`: the reflection conjugates the rotation to its inverse. -/
theorem extr_reflS_Rinv_reflS : reflS * R⁻¹ * reflS = R := by
  rw [poly_R_inv]
  ext i j; fin_cases i <;> fin_cases j <;> simp [reflS, R, Matrix.mul_apply, Fin.sum_univ_two]

/-- `R S R = S`. -/
theorem extr_R_reflS_R : R * reflS * R = reflS := by
  have h3 : √3 * √3 = 3 := Real.mul_self_sqrt (by norm_num)
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [reflS, R, Matrix.mul_apply, Fin.sum_univ_two] <;> nlinarith

/-- `R⁻¹ S R⁻¹ = S`. -/
theorem extr_Rinv_reflS_Rinv : R⁻¹ * reflS * R⁻¹ = reflS := by
  have h3 : √3 * √3 = 3 := Real.mul_self_sqrt (by norm_num)
  rw [poly_R_inv]
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [reflS, Matrix.mul_apply, Fin.sum_univ_two] <;> nlinarith

/-- The twisted endpoint condition is preserved: `R⁻¹ S'(R⁻¹ X R) R = S' X`. -/
theorem extr_rev_twist (X : Mat2) : R⁻¹ * extr_rev (R⁻¹ * X * R) * R = extr_rev X := by
  rw [extr_rev, extr_rev, Matrix.mul_neg, Matrix.neg_mul]
  congr 1
  calc R⁻¹ * (reflS * (R⁻¹ * X * R) * reflS) * R
      = (R⁻¹ * reflS * R⁻¹) * X * (R * reflS * R) := by simp only [Matrix.mul_assoc]
    _ = reflS * X * reflS := by rw [extr_Rinv_reflS_Rinv, extr_R_reflS_R]

theorem extr_det_reflS_Rinv : (reflS * R⁻¹).det = -1 := by
  have h3 : √3 * √3 = 3 := Real.mul_self_sqrt (by norm_num)
  rw [poly_R_inv, Matrix.det_mul]
  simp [reflS, Matrix.det_fin_two_of]
  nlinarith

/-! ### Reversal of time -/

/-- **Time reversal of a Carathéodory solution**: if `f' = v` on `[0, T]`, then
`(f(T - ·))' = -v(T - ·)` on `[0, T]`. -/
theorem extr_isIntegralCurve_rev {f v : ℝ → Mat2} {T : ℝ} (hT : 0 ≤ T) (h : IsIntegralCurve f v T) :
    IsIntegralCurve (fun t ↦ f (T - t)) (fun t ↦ -v (T - t)) T := by
  intro i j
  obtain ⟨hint, heq⟩ := h i j
  have hsub : ∀ a b, 0 ≤ a → a ≤ b → b ≤ T →
      IntervalIntegrable (fun x ↦ v x i j) volume a b := fun a b ha hab hb ↦
    hint.mono_set (by
      rw [uIcc_of_le hab, uIcc_of_le (ha.trans (hab.trans hb))]
      exact Icc_subset_Icc ha hb)
  refine ⟨?_, fun t ht ↦ ?_⟩
  · have := (hint.comp_sub_left T).symm.neg
    simp only [sub_zero, sub_self] at this
    convert this using 1
    funext x
    simp
  · simp only [Matrix.neg_apply, sub_zero]
    rw [intervalIntegral.integral_neg, intervalIntegral.integral_comp_sub_left (fun x ↦ v x i j) T,
      sub_zero, heq (T - t) ⟨by linarith [ht.2], by linarith [ht.1]⟩, heq T ⟨hT, le_rfl⟩,
      ← intervalIntegral.integral_add_adjacent_intervals
        (hsub 0 (T - t) le_rfl (by linarith [ht.2]) (by linarith [ht.1]))
        (hsub (T - t) T (by linarith [ht.2]) (by linarith [ht.1]) le_rfl)]
    ring

/-- Time reversal followed by the reflection: if `f' = v`, then
`(S' f(T - ·))' = -S' v(T - ·)`. -/
theorem extr_isIntegralCurve_wx_rev {f v : ℝ → Mat2} {T : ℝ} (hT : 0 ≤ T)
    (h : IsIntegralCurve f v T) :
    IsIntegralCurve (fun t ↦ extr_rev (f (T - t))) (fun t ↦ -extr_rev (v (T - t))) T := by
  refine isIntegralCurve_congr (isIntegralCurve_mul_mul (extr_isIntegralCurve_rev hT h) (-reflS)
    reflS) (fun t ↦ ?_) (fun t ↦ ?_)
  · rw [extr_rev_eq_mul]
  · rw [extr_rev_eq_mul, Matrix.mul_neg, Matrix.neg_mul]

/-- Pull-back of an almost-everywhere property by the reversal `t ↦ T - t`. -/
theorem extr_ae_rev {p : ℝ → Prop} (T : ℝ) (h : ∀ᵐ s, p s) : ∀ᵐ t, p (T - t) :=
  (Measure.measurePreserving_sub_left volume T).quasiMeasurePreserving.ae h

end SmoothedOctagon
