module

public import SmoothedOctagon.Reduction.Defs
public import SmoothedOctagon.Reduction.CompactDomain

/-!
# Matrix algebra for the singular clearance

Pointwise facts about `2 × 2` matrices used by the singular clearance and the projective bounds
(`Reduction/SingularClearance.lean`).

Main API:

* `clr_frobSq_nonneg`, `clr_frobSq_pos`: `‖M‖_F² ≥ 0`, and `> 0` for `M ≠ 0`.
* `clr_traceForm_sq_le`: `tr(AB)² ≤ ‖A‖_F² ‖B‖_F²` (Cauchy–Schwarz).
* `clr_frobSq_mul_le`: `‖AB‖_F² ≤ ‖A‖_F² ‖B‖_F²`.
* `clr_frobSq_adjugate`: `‖adj A‖_F = ‖A‖_F`.
* `clr_frobSq_add_smul_J_le`: `‖M + cJ‖_F² ≤ 2‖M‖_F² + 4c²`.
* `clr_rho`, `clr_rhoR`: `ρ(Y) = -tr(JY)/2` and the spatial `ρ_R = ρ(h Y adj h)`;
  `clr_rho_pos` (`ρ > 0` on star states), `clr_rhoR_pos` (`ρ_R > 0` for `det h = 1`),
  `clr_frobSq_conj` (`‖h Y adj h‖_F² = 4ρ_R² - 2`).
* `clr_traceForm_eq`: `tr(AB)` entry by entry; `clr_margin_eq`, `clr_sigma_eq`: the margins
  `p_i = -√3 tr(Z_i X)` and `σ_i = √3 tr(W Z_i)` of traceless matrices, entry by entry;
  `clr_hamiltonian_vertex`: `H_i = tr(AX) + σ_i / p_i` with `A = Λ₁ - (3/2)λJ`.
* `clr_vertex_scalar`: the exact equilibrium inequality and scaled pairing bounds.
* `clr_vertex_bounds`: a bound in terms of any positive lower bound for the pairwise margins.
* `clr_equilibrium_compact`: on every compact set of star states, `‖W‖_F ≤ C (-tr(AX))`.
* `clr_compact_costate_bound`: the corresponding uniform squared bound by `‖A‖_F²`.
-/

@[expose] public section

namespace SmoothedOctagon.Reduction

open SmoothedPolygons Matrix

/-! ### Frobenius norms -/

theorem clr_frobSq_nonneg (M : Mat2) : 0 ≤ frobSq M := by
  unfold frobSq; positivity

theorem clr_frobSq_pos {M : Mat2} (h : M ≠ 0) : 0 < frobSq M := by
  rcases (clr_frobSq_nonneg M).lt_or_eq with h' | h'
  · exact h'
  · exfalso
    apply h
    unfold frobSq at h'
    have e0 := sq_nonneg (M 0 0)
    have e1 := sq_nonneg (M 0 1)
    have e2 := sq_nonneg (M 1 0)
    have e3 := sq_nonneg (M 1 1)
    have h0 : M 0 0 = 0 := pow_eq_zero_iff (n := 2) (by norm_num) |>.mp (by linarith)
    have h1 : M 0 1 = 0 := pow_eq_zero_iff (n := 2) (by norm_num) |>.mp (by linarith)
    have h2 : M 1 0 = 0 := pow_eq_zero_iff (n := 2) (by norm_num) |>.mp (by linarith)
    have h3 : M 1 1 = 0 := pow_eq_zero_iff (n := 2) (by norm_num) |>.mp (by linarith)
    ext i j
    fin_cases i <;> fin_cases j <;> simp [h0, h1, h2, h3]

theorem clr_traceForm_eq (A B : Mat2) :
    traceForm A B = A 0 0 * B 0 0 + A 0 1 * B 1 0 + A 1 0 * B 0 1 + A 1 1 * B 1 1 := by
  simp [traceForm, Matrix.trace_fin_two, Matrix.mul_apply, Fin.sum_univ_two]
  ring

/-- Cauchy–Schwarz for the trace form. -/
theorem clr_traceForm_sq_le (A B : Mat2) : traceForm A B ^ 2 ≤ frobSq A * frobSq B := by
  rw [clr_traceForm_eq]
  unfold frobSq
  nlinarith [sq_nonneg (A 0 0 * B 1 0 - A 0 1 * B 0 0), sq_nonneg (A 0 0 * B 0 1 - A 1 0 * B 0 0),
    sq_nonneg (A 0 0 * B 1 1 - A 1 1 * B 0 0), sq_nonneg (A 0 1 * B 0 1 - A 1 0 * B 1 0),
    sq_nonneg (A 0 1 * B 1 1 - A 1 1 * B 1 0), sq_nonneg (A 1 0 * B 1 1 - A 1 1 * B 0 1)]

/-- Submultiplicativity of the Frobenius norm. -/
theorem clr_frobSq_mul_le (A B : Mat2) : frobSq (A * B) ≤ frobSq A * frobSq B := by
  unfold frobSq
  simp only [Matrix.mul_apply, Fin.sum_univ_two]
  nlinarith [sq_nonneg (A 0 0 * B 1 0 - A 0 1 * B 0 0), sq_nonneg (A 0 0 * B 1 1 - A 0 1 * B 0 1),
    sq_nonneg (A 1 0 * B 1 0 - A 1 1 * B 0 0), sq_nonneg (A 1 0 * B 1 1 - A 1 1 * B 0 1),
    sq_nonneg (A 0 0 * A 1 1), sq_nonneg (A 0 1 * A 1 0), sq_nonneg (B 0 0 * B 1 1),
    sq_nonneg (B 0 1 * B 1 0), sq_nonneg (A 0 0 * B 0 0), sq_nonneg (A 1 1 * B 1 1)]

theorem clr_frobSq_adjugate (A : Mat2) : frobSq A.adjugate = frobSq A := by
  rw [Matrix.adjugate_fin_two]
  simp [frobSq]
  ring

theorem clr_frobSq_add_smul_J_le (M : Mat2) (c : ℝ) :
    frobSq (M + c • J) ≤ 2 * frobSq M + 4 * c ^ 2 := by
  simp [frobSq, J]
  nlinarith [sq_nonneg (M 0 1 + c), sq_nonneg (M 1 0 - c)]

/-! ### The scalars `ρ` and `ρ_R` -/

/-- `ρ(Y) = -tr(JY)/2`; the cost density is `3ρ`. -/
noncomputable def clr_rho (Y : Mat2) : ℝ := -(1 / 2) * traceForm J Y

/-- The spatial scalar `ρ_R = ρ(h Y h⁻¹)`, written with the adjugate, which is the inverse when
`det h = 1`. -/
noncomputable def clr_rhoR (h Y : Mat2) : ℝ := clr_rho (h * Y * h.adjugate)

theorem clr_rho_eq (Y : Mat2) : clr_rho Y = (Y 1 0 - Y 0 1) / 2 := by
  rw [clr_rho, clr_traceForm_eq]
  simp [J]
  ring

theorem clr_rhoR_eq (h Y : Mat2) :
    2 * clr_rhoR h Y = (Y 0 0 - Y 1 1) * (h 0 0 * h 0 1 + h 1 0 * h 1 1) -
        Y 0 1 * (h 0 0 ^ 2 + h 1 0 ^ 2) + Y 1 0 * (h 0 1 ^ 2 + h 1 1 ^ 2) := by
  rw [clr_rhoR, clr_rho_eq, Matrix.adjugate_fin_two]
  simp [Matrix.mul_apply, Fin.sum_univ_two]
  ring

private theorem clr_star_entries {Y : Mat2} (hY : IsStarState Y) :
    Y 1 1 = -Y 0 0 ∧ -Y 0 0 ^ 2 - Y 0 1 * Y 1 0 = 1 ∧ 0 < Y 1 0 ∧ 3 * Y 0 1 + Y 1 0 < 0 := by
  obtain ⟨htr, hdet, h0, h1, h2⟩ := hY
  have e11 : Y 1 1 = -Y 0 0 := by rw [Matrix.trace_fin_two] at htr; linarith
  have hs : (0 : ℝ) < √3 := by positivity
  refine ⟨e11, ?_, ?_, ?_⟩
  · rw [Matrix.det_fin_two, e11] at hdet; linarith
  · have h01 := add_pos h0 h1
    simp only [ρ₀, ρ₁] at h01
    rw [← add_div] at h01
    have := (div_pos_iff_of_pos_right hs).mp h01
    linarith
  · simp only [ρ₂] at h2
    have := (div_pos_iff_of_pos_right (by positivity : (0 : ℝ) < 2 * √3)).mp h2
    linarith

/-- `ρ > 0` on star states. -/
theorem clr_rho_pos {Y : Mat2} (hY : IsStarState Y) : 0 < clr_rho Y := by
  obtain ⟨-, -, h10, h01⟩ := clr_star_entries hY
  rw [clr_rho_eq]
  linarith

/-- `ρ_R > 0`: `-J h Y h⁻¹ = h⁻ᵀ (-JY) h⁻¹` is positive definite. -/
theorem clr_rhoR_pos {h Y : Mat2} (hh : h.det = 1) (hY : IsStarState Y) : 0 < clr_rhoR h Y := by
  obtain ⟨e11, hdY, h10, -⟩ := clr_star_entries hY
  have key := clr_rhoR_eq h Y
  rw [e11] at key
  rw [Matrix.det_fin_two] at hh
  have hsum : Y 1 0 * (2 * clr_rhoR h Y) = (Y 1 0 * h 1 1 + Y 0 0 * h 1 0) ^ 2 +
      (Y 1 0 * h 0 1 + Y 0 0 * h 0 0) ^ 2 + h 1 0 ^ 2 + h 0 0 ^ 2 := by
    rw [key]
    linear_combination (h 1 0 ^ 2 + h 0 0 ^ 2) * hdY
  have hpos : 0 < h 1 0 ^ 2 + h 0 0 ^ 2 := by
    rcases eq_or_ne (h 0 0) 0 with h0 | h0
    · have : h 1 0 ≠ 0 := by
        intro h1; rw [h0, h1] at hh; simp at hh
      positivity
    · positivity
  have : 0 < Y 1 0 * (2 * clr_rhoR h Y) := by
    rw [hsum]; nlinarith [sq_nonneg (Y 1 0 * h 1 1 + Y 0 0 * h 1 0),
      sq_nonneg (Y 1 0 * h 0 1 + Y 0 0 * h 0 0)]
  have := (pos_iff_pos_of_mul_pos this).mp h10
  linarith

/-- `‖h Y h⁻¹‖_F² = 4ρ_R² - 2` for `det h = 1` and `Y` traceless with `det Y = 1`. -/
theorem clr_frobSq_conj {h Y : Mat2} (hh : h.det = 1) (hY : IsStarState Y) :
    frobSq (h * Y * h.adjugate) = 4 * clr_rhoR h Y ^ 2 - 2 := by
  obtain ⟨e11, hdY, -, -⟩ := clr_star_entries hY
  have key := clr_rhoR_eq h Y
  rw [e11] at key
  rw [Matrix.det_fin_two] at hh
  have e : 4 * clr_rhoR h Y ^ 2 = (2 * clr_rhoR h Y) ^ 2 := by ring
  rw [e, key, Matrix.adjugate_fin_two]
  simp only [frobSq, Matrix.mul_apply, Fin.sum_univ_two, Matrix.of_apply, Matrix.cons_val',
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.empty_val', Matrix.cons_val_fin_one, e11]
  linear_combination (-2 * (h 0 0 * h 1 1 - h 0 1 * h 1 0 + 1)) * hh * 1 +
    (-2) * (h 0 0 * h 1 1 - h 0 1 * h 1 0) ^ 2 * hdY

/-! ### The equilibrium control and the vertex Hamiltonians -/

/-- The margins of a traceless state, entry by entry. -/
theorem clr_margin_eq {X : Mat2} (hX : X.trace = 0) :
    margin 0 X = -√3 * X 0 1 - √3 / 3 * X 1 0 ∧ margin 1 X = -2 * X 0 0 + 2 * √3 / 3 * X 1 0 ∧
      margin 2 X = 2 * X 0 0 + 2 * √3 / 3 * X 1 0 := by
  have h11 : X 1 1 = -X 0 0 := by rw [Matrix.trace_fin_two] at hX; linarith
  have hs : √3 ≠ 0 := by positivity
  refine ⟨?_, ?_, ?_⟩ <;>
  · rw [margin, clr_traceForm_eq]
    simp [controlMatrix, vertex, h11]
    field_simp
    ring

/-- The scaled vertex pairings `σ_i = √3 tr(W Z_i)` of a traceless `W`, entry by entry. -/
theorem clr_sigma_eq {W : Mat2} (hW : W.trace = 0) :
    √3 * traceForm W (controlMatrix (vertex 0)) = √3 * W 0 1 + √3 / 3 * W 1 0 ∧
      √3 * traceForm W (controlMatrix (vertex 1)) = 2 * W 0 0 - 2 * √3 / 3 * W 1 0 ∧
      √3 * traceForm W (controlMatrix (vertex 2)) = -2 * W 0 0 - 2 * √3 / 3 * W 1 0 := by
  have h11 : W 1 1 = -W 0 0 := by rw [Matrix.trace_fin_two] at hW; linarith
  have hs : √3 ≠ 0 := by positivity
  refine ⟨?_, ?_, ?_⟩ <;>
  · rw [clr_traceForm_eq]
    simp [controlMatrix, vertex, h11]
    field_simp
    try ring

/-- The vertex Hamiltonian `H_i = tr(AX) + σ_i / p_i`. -/
theorem clr_hamiltonian_vertex (lam : ℝ) (Λ₁ W X : Mat2) (i : Fin 3) :
    hamiltonian lam Λ₁ W X (vertex i) = traceForm (Λ₁ - (3 / 2 * lam) • J) X +
      √3 * traceForm W (controlMatrix (vertex i)) / margin i X := by
  have hs : √3 ≠ 0 := by positivity
  have e : traceForm X (controlMatrix (vertex i)) = -margin i X / √3 := by
    rw [margin, traceForm, Matrix.trace_mul_comm]
    field_simp
    rfl
  rw [hamiltonian, e, div_div_eq_mul_div, div_neg, sub_neg_eq_add]
  ring

/-- The equilibrium weights sum to one. Their zero weighted pairing gives `α ≤ 0`
and bounds each scaled pairing by `-8α`, without a choice of margin constant. -/
theorem clr_vertex_scalar {p₀ p₁ p₂ σ₀ σ₁ σ₂ α : ℝ} (h₀ : 0 < p₀) (h₁ : 0 < p₁) (h₂ : 0 < p₂)
    (hsum : p₀ * p₁ + p₁ * p₂ + p₂ * p₀ = 4)
    (heq : (p₁ + p₂) * σ₀ + (p₀ + p₂) * σ₁ + (p₀ + p₁) * σ₂ = 0)
    (hH₀ : α + σ₀ / p₀ ≤ 0) (hH₁ : α + σ₁ / p₁ ≤ 0) (hH₂ : α + σ₂ / p₂ ≤ 0) :
    α ≤ 0 ∧ |(p₁ + p₂) * σ₀| ≤ -8 * α ∧
      |(p₀ + p₂) * σ₁| ≤ -8 * α ∧ |(p₀ + p₁) * σ₂| ≤ -8 * α := by
  -- `σ_i ≤ m p_i` with `m = -α`
  have k₀ : σ₀ ≤ -α * p₀ := by
    have := mul_le_mul_of_nonneg_right hH₀ h₀.le
    rw [add_mul, div_mul_cancel₀ _ h₀.ne'] at this; linarith
  have k₁ : σ₁ ≤ -α * p₁ := by
    have := mul_le_mul_of_nonneg_right hH₁ h₁.le
    rw [add_mul, div_mul_cancel₀ _ h₁.ne'] at this; linarith
  have k₂ : σ₂ ≤ -α * p₂ := by
    have := mul_le_mul_of_nonneg_right hH₂ h₂.le
    rw [add_mul, div_mul_cancel₀ _ h₂.ne'] at this; linarith
  have l₀ := mul_le_mul_of_nonneg_left k₀ (by positivity : (0 : ℝ) ≤ p₁ + p₂)
  have l₁ := mul_le_mul_of_nonneg_left k₁ (by positivity : (0 : ℝ) ≤ p₀ + p₂)
  have l₂ := mul_le_mul_of_nonneg_left k₂ (by positivity : (0 : ℝ) ≤ p₀ + p₁)
  have hα : α ≤ 0 := by nlinarith
  have p01 : 0 ≤ p₀ * p₁ := by positivity
  have p12 : 0 ≤ p₁ * p₂ := by positivity
  have p20 : 0 ≤ p₂ * p₀ := by positivity
  refine ⟨hα, ?_, ?_, ?_⟩ <;> rw [abs_le] <;> constructor <;>
    nlinarith [mul_nonneg (neg_nonneg.mpr hα) p01,
      mul_nonneg (neg_nonneg.mpr hα) p12, mul_nonneg (neg_nonneg.mpr hα) p20]

/-- All three margins of a star state are positive. -/
theorem clr_margin_pos {X : Mat2} (hX : IsStarState X) : ∀ i, 0 < margin i X := by
  have hXtr := hX.1
  obtain ⟨e0, e1, e2⟩ := margin_eq_two_mul_ρ hXtr
  obtain ⟨-, -, r0, r1, r2⟩ := hX
  intro i; fin_cases i
  · simp only [Fin.zero_eta, Fin.isValue]; rw [e0]; linarith
  · simp only [Fin.mk_one, Fin.isValue]; rw [e1]; linarith
  · simp only [Fin.reduceFinMk, Fin.isValue]; rw [e2]; linarith

/-- The equilibrium inequality and its quantitative bound for any positive
lower bound `δ` of the pairwise margins. -/
theorem clr_vertex_bounds {lam : ℝ} {Λ₁ W X : Mat2} (hX : IsStarState X) (hW : W.trace = 0)
    (hWX : traceForm W X = 0) (hH : ∀ i, hamiltonian lam Λ₁ W X (vertex i) ≤ 0) :
    traceForm (Λ₁ - (3 / 2 * lam) • J) X ≤ 0 ∧
      (∀ δ : ℝ, 0 < δ → δ ≤ margin 1 X + margin 2 X →
        δ ≤ margin 0 X + margin 2 X → δ ≤ margin 0 X + margin 1 X →
        frobSq W ≤ 3 * (8 / δ) ^ 2 * traceForm (Λ₁ - (3 / 2 * lam) • J) X ^ 2) := by
  have e11 : X 1 1 = -X 0 0 := by
    have ht := hX.1
    rw [Matrix.trace_fin_two] at ht
    linarith
  have hdet : -X 0 0 ^ 2 - X 0 1 * X 1 0 = 1 := by
    have hd := hX.2.1
    rw [Matrix.det_fin_two, e11] at hd
    nlinarith
  have hXtr : X.trace = 0 := hX.1
  obtain ⟨m0, m1, m2⟩ := clr_margin_eq hXtr
  obtain ⟨s0, s1, s2⟩ := clr_sigma_eq hW
  have hpos := clr_margin_pos hX
  have hW11 : W 1 1 = -W 0 0 := by rw [Matrix.trace_fin_two] at hW; linarith
  have h3 : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  have hsum : margin 0 X * margin 1 X + margin 1 X * margin 2 X + margin 2 X * margin 0 X = 4 := by
    rw [m0, m1, m2]
    linear_combination (-4 * X 0 1 * X 1 0 / 3) * h3 + 4 * hdet
  have hWX' := hWX
  rw [clr_traceForm_eq, hW11, e11] at hWX'
  have heq : (margin 1 X + margin 2 X) * (√3 * traceForm W (controlMatrix (vertex 0))) +
      (margin 0 X + margin 2 X) * (√3 * traceForm W (controlMatrix (vertex 1))) +
      (margin 0 X + margin 1 X) * (√3 * traceForm W (controlMatrix (vertex 2))) = 0 := by
    rw [m0, m1, m2, s0, s1, s2]
    linear_combination (4 * W 0 1 * X 1 0 / 3 + 4 * W 1 0 * X 0 1 / 3) * h3 + 4 * hWX'
  have hH' : ∀ i, traceForm (Λ₁ - (3 / 2 * lam) • J) X +
      √3 * traceForm W (controlMatrix (vertex i)) / margin i X ≤ 0 := fun i ↦ by
    rw [← clr_hamiltonian_vertex]; exact hH i
  obtain ⟨hα, hσ⟩ := clr_vertex_scalar (hpos 0) (hpos 1) (hpos 2) hsum heq (hH' 0) (hH' 1)
    (hH' 2)
  obtain ⟨b0, b1, b2⟩ := hσ
  refine ⟨hα, fun δ hδ hp0 hp1 hp2 ↦ ?_⟩
  have bound {σ p : ℝ} (hp : δ ≤ p) (hb : |p * σ| ≤ -8 *
      traceForm (Λ₁ - (3 / 2 * lam) • J) X) :
      σ ^ 2 ≤ (8 / δ) ^ 2 * traceForm (Λ₁ - (3 / 2 * lam) • J) X ^ 2 := by
    have habs : δ * |σ| ≤ -8 * traceForm (Λ₁ - (3 / 2 * lam) • J) X := by
      calc δ * |σ| ≤ p * |σ| := mul_le_mul_of_nonneg_right hp (abs_nonneg σ)
        _ = |p * σ| := by rw [abs_mul, abs_of_pos (hδ.trans_le hp)]
        _ ≤ _ := hb
    have hlin : |σ| ≤ (8 / δ) * (-traceForm (Λ₁ - (3 / 2 * lam) • J) X) := by
      calc |σ| ≤ (-8 * traceForm (Λ₁ - (3 / 2 * lam) • J) X) / δ :=
          (le_div_iff₀ hδ).mpr (by nlinarith only [habs])
        _ = _ := by ring
    have hs := pow_le_pow_left₀ (abs_nonneg σ) hlin 2
    simpa only [sq_abs, mul_pow, neg_sq] using hs
  have bs0 := bound hp0 b0
  have bs1 := bound hp1 b1
  have bs2 := bound hp2 b2
  have hfro : frobSq W ≤ (√3 * traceForm W (controlMatrix (vertex 0))) ^ 2 +
      (√3 * traceForm W (controlMatrix (vertex 1))) ^ 2 +
      (√3 * traceForm W (controlMatrix (vertex 2))) ^ 2 := by
    rw [s0, s1, s2]
    unfold frobSq
    rw [hW11]
    have he : (√3 * W 0 1 + √3 / 3 * W 1 0) ^ 2 +
        (2 * W 0 0 - 2 * √3 / 3 * W 1 0) ^ 2 +
        (-2 * W 0 0 - 2 * √3 / 3 * W 1 0) ^ 2 -
        (W 0 0 ^ 2 + W 0 1 ^ 2 + W 1 0 ^ 2 + (-W 0 0) ^ 2) =
        6 * W 0 0 ^ 2 + (W 0 1 + W 1 0) ^ 2 + W 0 1 ^ 2 + W 1 0 ^ 2 := by
      linear_combination (W 0 1 ^ 2 + 2 / 3 * W 0 1 * W 1 0 + W 1 0 ^ 2) * h3
    nlinarith only [he, sq_nonneg (W 0 1 + W 1 0), sq_nonneg (W 0 1),
      sq_nonneg (W 1 0), sq_nonneg (W 0 0)]
  nlinarith only [hfro, bs0, bs1, bs2]

/-- The pairwise margins have a common positive minimum on a compact set of star states. -/
theorem clr_compact_margin_gap {K : Set Mat2} (hK : IsCompact K)
    (hstar : ∀ X ∈ K, IsStarState X) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ X ∈ K, δ ≤ margin 1 X + margin 2 X ∧
      δ ≤ margin 0 X + margin 2 X ∧ δ ≤ margin 0 X + margin 1 X := by
  rcases K.eq_empty_or_nonempty with rfl | hne
  · exact ⟨1, by norm_num, by simp⟩
  have hm : ∀ i : Fin 3, Continuous (fun X : Mat2 ↦ margin i X) := by
    intro i
    unfold margin traceForm
    fun_prop
  let f : Mat2 → ℝ := fun X ↦ min (margin 1 X + margin 2 X)
    (min (margin 0 X + margin 2 X) (margin 0 X + margin 1 X))
  have hf : Continuous f := ((hm 1).add (hm 2)).min
    (((hm 0).add (hm 2)).min ((hm 0).add (hm 1)))
  obtain ⟨X₀, hX₀, hmin⟩ := hK.exists_isMinOn hne hf.continuousOn
  refine ⟨f X₀, ?_, ?_⟩
  · have hp := clr_margin_pos (hstar X₀ hX₀)
    exact lt_min (add_pos (hp 1) (hp 2))
      (lt_min (add_pos (hp 0) (hp 2)) (add_pos (hp 0) (hp 1)))
  · intro X hX
    have h := hmin hX
    exact ⟨h.trans (min_le_left _ _),
      h.trans ((min_le_right _ _).trans (min_le_left _ _)),
      h.trans ((min_le_right _ _).trans (min_le_right _ _))⟩

/-- The equilibrium costate bound is uniform on each compact set of star states. -/
theorem clr_equilibrium_compact {K : Set Mat2} (hK : IsCompact K)
    (hstar : ∀ X ∈ K, IsStarState X) :
    ∃ C : ℝ, 0 < C ∧ ∀ (lam : ℝ) (Λ₁ W X : Mat2), X ∈ K → W.trace = 0 →
      traceForm W X = 0 → (∀ i, hamiltonian lam Λ₁ W X (vertex i) ≤ 0) →
      √(frobSq W) ≤ C * (-traceForm (Λ₁ - (3 / 2 * lam) • J) X) := by
  obtain ⟨δ, hδ, hp⟩ := clr_compact_margin_gap hK hstar
  refine ⟨√3 * (8 / δ), by positivity, ?_⟩
  intro lam Λ₁ W X hX hW hWX hH
  obtain ⟨ha, hb⟩ := clr_vertex_bounds (hstar X hX) hW hWX hH
  obtain ⟨hp0, hp1, hp2⟩ := hp X hX
  have hbound := hb δ hδ hp0 hp1 hp2
  have he : 3 * (8 / δ) ^ 2 * traceForm (Λ₁ - (3 / 2 * lam) • J) X ^ 2 =
      (√3 * (8 / δ) * (-traceForm (Λ₁ - (3 / 2 * lam) • J) X)) ^ 2 := by
    rw [mul_pow, mul_pow, neg_sq, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3)]
  rw [he] at hbound
  have hs := Real.sqrt_le_sqrt hbound
  rw [Real.sqrt_sq (mul_nonneg (by positivity) (neg_nonneg.mpr ha))] at hs
  exact hs

/-- On a compact star set, the reduced costate is bounded by the shifted costate,
with a constant depending only on the set. -/
theorem clr_compact_costate_bound {K : Set Mat2} (hK : IsCompact K)
    (hstar : ∀ X ∈ K, IsStarState X) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ (lam : ℝ) (Λ₁ W X : Mat2), X ∈ K → W.trace = 0 →
      traceForm W X = 0 → (∀ i, hamiltonian lam Λ₁ W X (vertex i) ≤ 0) →
      frobSq W ≤ D * frobSq (Λ₁ - (3 / 2 * lam) • J) := by
  obtain ⟨C, hC, hbound⟩ := clr_equilibrium_compact hK hstar
  have hf : Continuous (fun X : Mat2 ↦ frobSq X) := by unfold frobSq; fun_prop
  obtain ⟨B, hB⟩ := hK.exists_bound_of_continuousOn hf.continuousOn
  refine ⟨C ^ 2 * max B 0, by positivity, ?_⟩
  intro lam Λ₁ W X hX hW hWX hH
  have heq := hbound lam Λ₁ W X hX hW hWX hH
  have hsq := pow_le_pow_left₀ (Real.sqrt_nonneg _) heq 2
  rw [Real.sq_sqrt (clr_frobSq_nonneg _), mul_pow, neg_sq] at hsq
  have hXbound : frobSq X ≤ max B 0 := by
    have hb := hB X hX
    rw [Real.norm_eq_abs, abs_of_nonneg (clr_frobSq_nonneg X)] at hb
    exact hb.trans (le_max_left _ _)
  have hcs := clr_traceForm_sq_le (Λ₁ - (3 / 2 * lam) • J) X
  have hA := clr_frobSq_nonneg (Λ₁ - (3 / 2 * lam) • J)
  calc frobSq W ≤ C ^ 2 * traceForm (Λ₁ - (3 / 2 * lam) • J) X ^ 2 := hsq
    _ ≤ C ^ 2 * (frobSq (Λ₁ - (3 / 2 * lam) • J) * frobSq X) :=
      mul_le_mul_of_nonneg_left hcs (sq_nonneg C)
    _ ≤ C ^ 2 * (frobSq (Λ₁ - (3 / 2 * lam) • J) * max B 0) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hXbound hA) (sq_nonneg C)
    _ = _ := by ring

end SmoothedOctagon.Reduction
