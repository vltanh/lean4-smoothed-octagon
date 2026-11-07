module

public import SmoothedOctagon.Reduction.Normal.Word
public import SmoothedOctagon.Period.Defs
public import SmoothedPolygons.Ch7.DiscreteK

/-!
# The coordinates of an abnormal costate and their transport along vertex pieces

For a state `X` and a costate `(Λ₁, Λ_R)` with cost multiplier `λ = 0` put `a = -XΛ₁X` and
`b = Λ_R + 2Λ₁ + ⟨Λ₁, X⟩X`, and use the coordinates `μ_j(M) = ⟨M, S_j⟩`, `S_j = √3 Z_{e_j}`, so
that the margins are `p_j = -μ_j(X)`. Then the vertex Hamiltonians are
`H_j p_j = 2 μ_j(a) + μ_j(b)` (`gn_hamiltonian_mul_margin`), `⟨b, X⟩ = ⟨Λ_R, X⟩ = 0`, and
`(a, b) = 0` only if `(Λ₁, Λ_R) = 0`.

On a vertex piece with label `i` the state, `a` and `b` satisfy `f' = κ [P, f]` with the constant
`P = -S_i / p_i` and `κ = 1, 2, 1` (for `b` this uses that the active Hamiltonian vanishes); then
their coordinates are transported by the one-arc map `gnL i` of `Normal/Word.lean`
(`gnMu_flow`), because `[S_i, S_{i+1}] = 2 (S_i + S_{i+1})` gives
`(μ_i + μ_{i±1})' = ±2κ/p_i (μ_i + μ_{i±1})`. This is the right-trivialized adjoint transport of
GLOBAL_NORMALITY §1 (`(a, b)` are the conserved covector `(α, β)` read in the moving frame), written
in the coordinates of the margin map.

## Main API

* `gnS`, `gnMu`, `gnA`, `gnB`; `gnS_zero`, `gnS_one`, `gnS_two`, `gnMu_eq`,
  `gn_margin_eq_neg_gnMu`, `gnMu_zero_apply`, `gnMu_one_apply`, `gnMu_two_apply`, linearity
  (`gnMu_add`, `gnMu_sub`, `gnMu_smul`, `gnMu_neg`), `gnS_bracket`.
* Pointwise: `gn_mul_mul_self` (`XΛX = ⟨Λ, X⟩X + Λ`), `gn_mul_self` (`X² = -1`),
  `gn_hamiltonian_mul_margin`, `gn_perp_eq` (`∑_{j ≠ l} μ_j(b) p_l(X) = 4 ⟨b, X⟩`),
  `gn_traceForm_gnB`, `gn_eq_zero_of_gnMu`, `gnA_trace`, `gnB_trace`, `gn_eq_zero_of_gnA`,
  `gnB_zero_left`; the twist `gnMu_Rinv_conj` (`μ_j(R⁻¹MR) = μ_{j-1}(M)`), `gnA_conj`, `gnB_conj`.
* Derivatives: `gnA_deriv_eq` (`a' = 2[P, a]`), `gnB_deriv_eq` (`b' = [P, b]`).
* Transport: `gn_exp_of_deriv` (`g' = r g` gives `g(s₁) = e^{r (s₁ - s₀)} g(s₀)`),
  `gnMu_bracket`, `gnMu_bracket_self`, `gnMu_bracket_add_one`, `gnMu_bracket_add_two`, `gnMu_flow`.
-/

@[expose] public section

namespace SmoothedOctagon.Reduction

open SmoothedPolygons Set

private lemma gn_s3 : √3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
private lemma gn_s3pos : (0 : ℝ) < √3 := by positivity
private lemma gn_s3c : √3 ^ 3 = 3 * √3 := by rw [pow_succ, gn_s3]
private lemma gn_s3q : √3 ^ 4 = 9 := by
  rw [show (4 : ℕ) = 2 * 2 from rfl, pow_mul, gn_s3]; norm_num

/-- Normalize a polynomial identity in `√3`, using `√3² = 3`. -/
local macro "gn_ring" : tactic =>
  `(tactic| ((try ring_nf); (try simp only [gn_s3, gn_s3c, gn_s3q]); (try ring_nf)))

/-! ### Coordinates -/

/-- `S_j = √3 Z_{e_j}`. -/
noncomputable def gnS (j : Fin 3) : Mat2 := √3 • controlMatrix (vertex j)

/-- The coordinate `μ_j(M) = ⟨M, S_j⟩ = √3 ⟨M, Z_{e_j}⟩`; the margins are `p_j = -μ_j(X)`. -/
noncomputable def gnMu (j : Fin 3) (M : Mat2) : ℝ := traceForm M (gnS j)

/-- `a = -XΛ₁X`. -/
def gnA (Λ₁ X : Mat2) : Mat2 := -(X * Λ₁ * X)

/-- `b = Λ_R + 2Λ₁ + ⟨Λ₁, X⟩X`. -/
noncomputable def gnB (Λ₁ ΛR X : Mat2) : Mat2 := ΛR + (2 : ℝ) • Λ₁ + traceForm Λ₁ X • X

theorem gnS_zero : gnS 0 = !![0, √3 / 3; √3, 0] := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [gnS, controlMatrix, vertex]; ring

theorem gnS_one : gnS 1 = !![1, -(2 * √3 / 3); 0, -1] := by
  have h := gn_s3pos
  ext i j; fin_cases i <;> fin_cases j <;> simp [gnS, controlMatrix, vertex] <;> field_simp

theorem gnS_two : gnS 2 = !![-1, -(2 * √3 / 3); 0, 1] := by
  have h := gn_s3pos
  ext i j; fin_cases i <;> fin_cases j <;> simp [gnS, controlMatrix, vertex] <;> field_simp

theorem gnMu_eq (j : Fin 3) (M : Mat2) :
    gnMu j M = √3 * traceForm M (controlMatrix (vertex j)) := by
  simp [gnMu, gnS, traceForm, Matrix.trace_smul]

theorem gn_margin_eq_neg_gnMu (j : Fin 3) (X : Mat2) : margin j X = -gnMu j X := by
  rw [margin, gnMu_eq, traceForm, traceForm, Matrix.trace_mul_comm]; ring

theorem gnMu_zero_apply (M : Mat2) : gnMu 0 M = √3 * M 0 1 + √3 / 3 * M 1 0 := by
  rw [gnMu, gnS_zero, traceForm, Matrix.eta_fin_two M]
  simp [Matrix.trace_fin_two]; ring

theorem gnMu_one_apply (M : Mat2) : gnMu 1 M = M 0 0 - 2 * √3 / 3 * M 1 0 - M 1 1 := by
  rw [gnMu, gnS_one, traceForm, Matrix.eta_fin_two M]
  simp [Matrix.trace_fin_two]; ring

theorem gnMu_two_apply (M : Mat2) : gnMu 2 M = -M 0 0 - 2 * √3 / 3 * M 1 0 + M 1 1 := by
  rw [gnMu, gnS_two, traceForm, Matrix.eta_fin_two M]
  simp [Matrix.trace_fin_two]; ring

theorem gnMu_add (j : Fin 3) (M N : Mat2) : gnMu j (M + N) = gnMu j M + gnMu j N := by
  simp [gnMu, traceForm, Matrix.add_mul, Matrix.trace_add]

theorem gnMu_sub (j : Fin 3) (M N : Mat2) : gnMu j (M - N) = gnMu j M - gnMu j N := by
  simp [gnMu, traceForm, Matrix.sub_mul, Matrix.trace_sub]

theorem gnMu_smul (j : Fin 3) (c : ℝ) (M : Mat2) : gnMu j (c • M) = c * gnMu j M := by
  simp [gnMu, traceForm, Matrix.trace_smul]

theorem gnMu_neg (j : Fin 3) (M : Mat2) : gnMu j (-M) = -gnMu j M := by
  simp [gnMu, traceForm, Matrix.trace_neg]

/-- `[S_i, S_{i+1}] = 2 (S_i + S_{i+1})`. -/
theorem gnS_bracket (i : Fin 3) :
    gnS i * gnS (i + 1) - gnS (i + 1) * gnS i = (2 : ℝ) • (gnS i + gnS (i + 1)) := by
  have h := gn_s3pos
  fin_cases i
  · simp only [Fin.zero_eta, zero_add, gnS_zero, gnS_one]
    ext a b; fin_cases a <;> fin_cases b <;> simp <;> gn_ring
  · simp only [Fin.mk_one, show (1 : Fin 3) + 1 = 2 from rfl, gnS_one, gnS_two]
    ext a b; fin_cases a <;> fin_cases b <;> (simp; try gn_ring)
  · simp only [show (⟨2, by norm_num⟩ : Fin 3) = 2 from rfl, show (2 : Fin 3) + 1 = 0 from rfl,
      gnS_two, gnS_zero]
    ext a b; fin_cases a <;> fin_cases b <;> simp <;> gn_ring

/-! ### Pointwise identities -/

private lemma gn_eta {M : Mat2} (h : M.trace = 0) : M = !![M 0 0, M 0 1; M 1 0, -M 0 0] :=
  algA_eta_of_trace_eq_zero M h

private lemma gn_det_entries {X : Mat2} (hX : X.trace = 0) (hdet : X.det = 1) :
    -(X 0 0 * X 0 0) - X 0 1 * X 1 0 = 1 := by
  rw [Matrix.det_fin_two] at hdet
  rw [Matrix.trace_fin_two] at hX
  have : X 1 1 = -X 0 0 := by linarith
  rw [this] at hdet; linarith

/-- `X Λ X = ⟨Λ, X⟩ X + Λ` for traceless `Λ` and a traceless `X` of determinant one. -/
theorem gn_mul_mul_self {X Λ : Mat2} (hX : X.trace = 0) (hdet : X.det = 1) (hΛ : Λ.trace = 0) :
    X * Λ * X = traceForm Λ X • X + Λ := by
  have hd := gn_det_entries hX hdet
  rw [gn_eta hX, gn_eta hΛ]
  ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, traceForm, Matrix.trace_fin_two]
  · linear_combination Λ 0 0 * hd
  · linear_combination Λ 0 1 * hd
  · linear_combination Λ 1 0 * hd
  · linear_combination -Λ 0 0 * hd

/-- `X² = -I` for a traceless `X` of determinant one. -/
theorem gn_mul_self {X : Mat2} (hX : X.trace = 0) (hdet : X.det = 1) : X * X = -1 := by
  have hd := gn_det_entries hX hdet
  rw [gn_eta hX]
  ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply] <;> linarith

/-- **The vertex Hamiltonians in coordinates** (with `λ = 0`): `H_j p_j = 2 μ_j(a) + μ_j(b)`. -/
theorem gn_hamiltonian_mul_margin (j : Fin 3) {Λ₁ ΛR X : Mat2} (hX : X.trace = 0)
    (hdet : X.det = 1) (hΛ : Λ₁.trace = 0) (hm : margin j X ≠ 0) :
    hamiltonian 0 Λ₁ ΛR X (vertex j) * margin j X =
      2 * gnMu j (gnA Λ₁ X) + gnMu j (gnB Λ₁ ΛR X) := by
  have hXZ : traceForm X (controlMatrix (vertex j)) ≠ 0 := by
    intro h; apply hm
    rw [margin, traceForm, Matrix.trace_mul_comm, ← traceForm, h, mul_zero]
  have hA : gnMu j (gnA Λ₁ X) = -(traceForm Λ₁ X * gnMu j X + gnMu j Λ₁) := by
    rw [gnA, gnMu_neg, gn_mul_mul_self hX hdet hΛ, gnMu_add, gnMu_smul]
  have hB : gnMu j (gnB Λ₁ ΛR X) = gnMu j ΛR + 2 * gnMu j Λ₁ + traceForm Λ₁ X * gnMu j X := by
    rw [gnB, gnMu_add, gnMu_add, gnMu_smul, gnMu_smul]
  rw [hA, hB, gn_margin_eq_neg_gnMu, hamiltonian]
  simp only [gnMu_eq, mul_zero, zero_smul, sub_zero]
  field_simp
  ring

/-- `∑_{j ≠ l} μ_j(b) p_l(X) = 4 ⟨b, X⟩` for traceless `b`, `X`. -/
theorem gn_perp_eq {b X : Mat2} (hb : b.trace = 0) (hX : X.trace = 0) :
    gnMu 0 b * (margin 1 X + margin 2 X) + gnMu 1 b * (margin 0 X + margin 2 X) +
      gnMu 2 b * (margin 0 X + margin 1 X) = 4 * traceForm b X := by
  rw [Matrix.trace_fin_two] at hb hX
  have hb' : b 1 1 = -b 0 0 := by linarith
  have hX' : X 1 1 = -X 0 0 := by linarith
  simp only [gn_margin_eq_neg_gnMu, gnMu_zero_apply, gnMu_one_apply, gnMu_two_apply, traceForm,
    Matrix.trace_fin_two, Matrix.mul_apply, Fin.sum_univ_two, hb', hX']
  gn_ring

/-- `⟨b, X⟩ = ⟨Λ_R, X⟩` when `⟨X, X⟩ = -2`. -/
theorem gn_traceForm_gnB {Λ₁ ΛR X : Mat2} (hXX : traceForm X X = -2) :
    traceForm (gnB Λ₁ ΛR X) X = traceForm ΛR X := by
  have e : traceForm (gnB Λ₁ ΛR X) X =
      traceForm ΛR X + 2 * traceForm Λ₁ X + traceForm Λ₁ X * traceForm X X := by
    simp only [gnB, traceForm, Matrix.add_mul, Matrix.smul_mul, Matrix.trace_add,
      Matrix.trace_smul, smul_eq_mul]
  rw [e, hXX]; ring

/-- A traceless matrix with vanishing coordinates is zero. -/
theorem gn_eq_zero_of_gnMu {M : Mat2} (hM : M.trace = 0) (h : ∀ j, gnMu j M = 0) : M = 0 := by
  have h0 := h 0; have h1 := h 1; have h2 := h 2
  rw [gnMu_zero_apply] at h0
  rw [gnMu_one_apply] at h1
  rw [gnMu_two_apply] at h2
  rw [Matrix.trace_fin_two] at hM
  have hs := gn_s3pos
  have e10 : M 1 0 = 0 := by
    have : 4 * √3 / 3 * M 1 0 = 0 := by linarith
    rcases mul_eq_zero.1 this with h | h
    · exact absurd h (by positivity)
    · exact h
  have e00 : M 0 0 = 0 := by rw [e10] at h1; linarith
  have e11 : M 1 1 = 0 := by linarith
  have e01 : M 0 1 = 0 := by
    rw [e10, mul_zero, add_zero] at h0
    rcases mul_eq_zero.1 h0 with h | h
    · exact absurd h hs.ne'
    · exact h
  ext i j; fin_cases i <;> fin_cases j <;> simp [e00, e01, e10, e11]

theorem gnA_trace {Λ X : Mat2} (hXX : X * X = -1) (hΛ : Λ.trace = 0) : (gnA Λ X).trace = 0 := by
  rw [gnA, Matrix.trace_neg, Matrix.trace_mul_comm (X * Λ) X, ← Matrix.mul_assoc, hXX]
  simp [hΛ]

theorem gnB_trace {Λ₁ ΛR X : Mat2} (hX : X.trace = 0) (hΛ : Λ₁.trace = 0)
    (hR : ΛR.trace = 0) : (gnB Λ₁ ΛR X).trace = 0 := by
  simp [gnB, Matrix.trace_add, Matrix.trace_smul, hX, hΛ, hR]

theorem gn_eq_zero_of_gnA {Λ X : Mat2} (hXX : X * X = -1) (h : gnA Λ X = 0) : Λ = 0 := by
  have e : X * (X * Λ * X) * X = Λ := by
    rw [show X * (X * Λ * X) * X = (X * X) * Λ * (X * X) by simp only [Matrix.mul_assoc], hXX]
    simp
  have h' : X * Λ * X = 0 := by rw [gnA, neg_eq_zero] at h; exact h
  rw [← e, h']; simp

theorem gnB_zero_left (ΛR X : Mat2) : gnB 0 ΛR X = ΛR := by simp [gnB, traceForm]

/-- The twist relabels the coordinates: `μ_j(R⁻¹ M R) = μ_{j-1}(M)`. -/
theorem gnMu_Rinv_conj (j : Fin 3) (M : Mat2) : gnMu j (R⁻¹ * M * R) = gnMu (j - 1) M := by
  have h := poly_Rinv_conj_vertex (j - 1)
  rw [sub_add_cancel] at h
  rw [gnMu_eq, gnMu_eq, ← h, poly_traceForm_conj poly_R_mul_inv]

theorem gnA_conj (Λ X : Mat2) : gnA (R⁻¹ * Λ * R) (R⁻¹ * X * R) = R⁻¹ * gnA Λ X * R := by
  have hRR : R * R⁻¹ = 1 := poly_R_mul_inv
  calc gnA (R⁻¹ * Λ * R) (R⁻¹ * X * R)
      = -(R⁻¹ * X * (R * R⁻¹) * Λ * (R * R⁻¹) * X * R) := by simp only [gnA, Matrix.mul_assoc]
    _ = R⁻¹ * gnA Λ X * R := by
      rw [hRR]; simp only [gnA, Matrix.mul_one, Matrix.mul_neg, Matrix.neg_mul, Matrix.mul_assoc]

theorem gnB_conj (Λ₁ ΛR X : Mat2) :
    gnB (R⁻¹ * Λ₁ * R) (R⁻¹ * ΛR * R) (R⁻¹ * X * R) = R⁻¹ * gnB Λ₁ ΛR X * R := by
  simp only [gnB, poly_traceForm_conj poly_R_mul_inv, Matrix.mul_add, Matrix.add_mul,
    Matrix.mul_smul, Matrix.smul_mul]

/-! ### Derivative identities -/

/-- `a' = 2 [P, a]` along `X' = [P, X]`, `Λ₁' = [Λ₁, X]`, when `X² = -1` and `PX + XP = 1`. -/
theorem gnA_deriv_eq {X L P : Mat2} (hXX : X * X = -1) (hPX : P * X + X * P = 1) :
    -(((P * X - X * P) * L + X * (L * X - X * L)) * X + X * L * (P * X - X * P)) =
      (2 : ℝ) • (P * gnA L X - gnA L X * P) := by
  have key : -(((P * X - X * P) * L + X * (L * X - X * L)) * X + X * L * (P * X - X * P)) -
      (2 : ℝ) • (P * gnA L X - gnA L X * P) =
        (P * X + X * P - 1) * L * X - X * L * (P * X + X * P - 1) - X * L * (X * X + 1) +
          (X * X + 1) * L * X := by
    simp only [gnA, two_smul]; noncomm_ring
  rw [hPX, hXX] at key
  simp only [sub_self, Matrix.mul_zero, Matrix.zero_mul, neg_add_cancel, add_zero] at key
  exact sub_eq_zero.1 key

/-- `b' = [P, b]` along the abnormal costate equations, when the active Hamiltonian
`⟨Λ₁, X⟩ - ⟨Λ_R, P⟩` vanishes, `det X = 1` and `⟨P, X⟩ = 1`. -/
theorem gnB_deriv_eq {X L R P X' L' R' : Mat2} (hX : X.trace = 0) (hL : L.trace = 0)
    (hR : R.trace = 0) (hP : P.trace = 0) (hdet : X.det = 1) (hPX : traceForm P X = 1)
    (hH : traceForm L X - traceForm R P = 0) (hX' : X' = P * X - X * P)
    (hL' : L' = L * X - X * L)
    (hR' : R' = (P * R - R * P) - traceForm R P • (P * X - X * P) +
      ((-L + (3 / 2 * (0 : ℝ)) • J) * X - X * (-L + (3 / 2 * (0 : ℝ)) • J))) :
    R' + (2 : ℝ) • L' + (traceForm L X • X' + (L' * X + L * X').trace • X) =
      P * gnB L R X - gnB L R X * P := by
  have hd := gn_det_entries hX hdet
  subst hX' hL' hR'
  rw [traceForm, Matrix.trace_fin_two] at hPX
  simp only [traceForm, Matrix.trace_fin_two] at hH
  rw [Matrix.trace_fin_two] at hX hL hR hP
  have eX : X 1 1 = -X 0 0 := by linarith
  have eL : L 1 1 = -L 0 0 := by linarith
  have eR : R 1 1 = -R 0 0 := by linarith
  have eP : P 1 1 = -P 0 0 := by linarith
  simp only [Matrix.mul_apply, Fin.sum_univ_two, eX, eL, eR, eP] at hPX hH
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [gnB, traceForm, Matrix.mul_apply, Fin.sum_univ_two, Matrix.trace_fin_two, eX, eL, eR,
      eP]
  · linear_combination (2 * (-L 0 1 * P 1 0 + L 1 0 * P 0 1)) * hd +
      (-L 0 1 * X 1 0 + L 1 0 * X 0 1) * hPX + (P 0 1 * X 1 0 - P 1 0 * X 0 1) * hH
  · linear_combination (4 * (-L 0 0 * P 0 1 + L 0 1 * P 0 0)) * hd +
      (2 * (-L 0 0 * X 0 1 + L 0 1 * X 0 0)) * hPX + (2 * P 0 0 * X 0 1 - 2 * P 0 1 * X 0 0) * hH
  · linear_combination (-4 * (-L 0 0 * P 1 0 + L 1 0 * P 0 0)) * hd +
      (-2 * (-L 0 0 * X 1 0 + L 1 0 * X 0 0)) * hPX + (2 * P 1 0 * X 0 0 - 2 * P 0 0 * X 1 0) * hH
  · linear_combination (-2 * (-L 0 1 * P 1 0 + L 1 0 * P 0 1)) * hd +
      (L 0 1 * X 1 0 - L 1 0 * X 0 1) * hPX + (-(P 0 1 * X 1 0 - P 1 0 * X 0 1)) * hH

/-! ### Transport along a vertex piece -/

/-- `g' = r g` on `[s₀, s₁]` gives `g(s₁) = e^{r (s₁ - s₀)} g(s₀)`. -/
theorem gn_exp_of_deriv {g : ℝ → ℝ} {r s₀ s₁ : ℝ} (h01 : s₀ ≤ s₁)
    (hg : ∀ t ∈ Icc s₀ s₁, HasDerivWithinAt g (r * g t) (Icc s₀ s₁) t) :
    g s₁ = Real.exp (r * (s₁ - s₀)) * g s₀ := by
  set ψ : ℝ → ℝ := fun t ↦ Real.exp (-(r * (t - s₀))) * g t with hψ
  have hd : ∀ t ∈ Icc s₀ s₁, HasDerivWithinAt ψ 0 (Icc s₀ s₁) t := by
    intro t ht
    have he : HasDerivAt (fun t ↦ Real.exp (-(r * (t - s₀))))
        (Real.exp (-(r * (t - s₀))) * -(r * 1)) t :=
      (((hasDerivAt_id' t).sub_const s₀).const_mul r).neg.exp
    have := he.hasDerivWithinAt.mul (hg t ht)
    convert this using 1; ring
  have hc := constant_of_has_deriv_right_zero (f := ψ) (fun t ht ↦ (hd t ht).continuousWithinAt)
    (fun t ht ↦ (hd t (Ico_subset_Icc_self ht)).mono_of_mem_nhdsWithin
      (Filter.mem_of_superset (Icc_mem_nhdsGE ht.2) (Icc_subset_Icc_left ht.1)))
    s₁ ⟨h01, le_rfl⟩
  simp only [hψ, sub_self, mul_zero, neg_zero, Real.exp_zero, one_mul] at hc
  rw [← hc, ← mul_assoc, ← Real.exp_add]; simp

/-- `μ_j([A, M]) = ⟨M, [S_j, A]⟩`. -/
theorem gnMu_bracket (j : Fin 3) (A M : Mat2) :
    gnMu j (A * M - M * A) = traceForm M (gnS j * A - A * gnS j) := by
  simp only [gnMu, traceForm, Matrix.sub_mul, Matrix.mul_sub, Matrix.trace_sub, Matrix.mul_assoc]
  rw [Matrix.trace_mul_comm A (M * gnS j), Matrix.mul_assoc]

theorem gnMu_bracket_self (i : Fin 3) (M : Mat2) : gnMu i (gnS i * M - M * gnS i) = 0 := by
  rw [gnMu_bracket, sub_self, traceForm, Matrix.mul_zero, Matrix.trace_zero]

theorem gnMu_bracket_add_one (i : Fin 3) (M : Mat2) :
    gnMu (i + 1) (gnS i * M - M * gnS i) = -2 * (gnMu i M + gnMu (i + 1) M) := by
  rw [gnMu_bracket, show gnS (i + 1) * gnS i - gnS i * gnS (i + 1) =
    -(gnS i * gnS (i + 1) - gnS (i + 1) * gnS i) by abel, gnS_bracket]
  simp only [gnMu, traceForm, Matrix.mul_neg, Matrix.mul_smul, Matrix.mul_add, Matrix.trace_neg,
    Matrix.trace_smul, Matrix.trace_add, smul_eq_mul]
  ring

private lemma gn_add_two_add_one (i : Fin 3) : i + 2 + 1 = i := by revert i; decide

theorem gnMu_bracket_add_two (i : Fin 3) (M : Mat2) :
    gnMu (i + 2) (gnS i * M - M * gnS i) = 2 * (gnMu i M + gnMu (i + 2) M) := by
  have h := gnS_bracket (i + 2)
  rw [gn_add_two_add_one] at h
  rw [gnMu_bracket, h]
  simp only [gnMu, traceForm, Matrix.mul_smul, Matrix.mul_add, Matrix.trace_smul,
    Matrix.trace_add, smul_eq_mul]
  ring

/-- **Transport of the coordinates along a vertex piece.** If `f' = κ [c S_i, f]` on
`[s₀, s₁]`, then `μ(f(s₁)) = L_i(q) μ(f(s₀))` with `q = e^{-2κc (s₁ - s₀)}`. -/
theorem gnMu_flow {f : ℝ → Mat2} {s₀ s₁ κ c : ℝ} (i : Fin 3) (h01 : s₀ ≤ s₁)
    (hf : ∀ t ∈ Icc s₀ s₁, Matrix.HasDerivWithinAtEntrywise f
      (κ • ((c • gnS i) * f t - f t * (c • gnS i))) (Icc s₀ s₁) t) :
    (fun j ↦ gnMu j (f s₁)) =
      gnL i (Real.exp (-2 * κ * c * (s₁ - s₀))) (fun j ↦ gnMu j (f s₀)) := by
  have hμ : ∀ j, ∀ t ∈ Icc s₀ s₁, HasDerivWithinAt (fun t ↦ gnMu j (f t))
      (κ * c * gnMu j (gnS i * f t - f t * gnS i)) (Icc s₀ s₁) t := by
    intro j t ht
    have := ((hf t ht).mul_const (gnS j)).trace
    convert this using 1
    · rfl
    · rw [gnMu, traceForm, Matrix.smul_mul, Matrix.trace_smul, Matrix.smul_mul, Matrix.mul_smul,
        ← smul_sub, Matrix.smul_mul, Matrix.trace_smul, smul_eq_mul, smul_eq_mul]
      ring
  have h0 := gn_exp_of_deriv (g := fun t ↦ gnMu i (f t)) (r := 0) h01 fun t ht ↦ by
    have := hμ i t ht
    rw [gnMu_bracket_self, mul_zero] at this
    simpa using this
  have h1 := gn_exp_of_deriv (g := fun t ↦ gnMu i (f t) + gnMu (i + 1) (f t))
    (r := -2 * κ * c) h01 fun t ht ↦ by
    have := (hμ i t ht).add (hμ (i + 1) t ht)
    rw [gnMu_bracket_self, gnMu_bracket_add_one] at this
    convert this using 1; ring
  have h2 := gn_exp_of_deriv (g := fun t ↦ gnMu i (f t) + gnMu (i + 2) (f t))
    (r := 2 * κ * c) h01 fun t ht ↦ by
    have := (hμ i t ht).add (hμ (i + 2) t ht)
    rw [gnMu_bracket_self, gnMu_bracket_add_two] at this
    convert this using 1; ring
  simp only [zero_mul, Real.exp_zero, one_mul] at h0
  funext j
  rcases gn_fin3_cases i j with rfl | rfl | rfl
  · rw [gnL_self]; exact h0
  · rw [gnL_add_one]; beta_reduce at h0 h1 ⊢; linarith
  · rw [gnL_add_two]
    beta_reduce at h0 h2 ⊢
    have e : Real.exp (2 * κ * c * (s₁ - s₀)) = (Real.exp (-2 * κ * c * (s₁ - s₀)))⁻¹ := by
      rw [← Real.exp_neg]; ring_nf
    rw [e] at h2
    rw [div_eq_mul_inv]
    linarith

end SmoothedOctagon.Reduction
