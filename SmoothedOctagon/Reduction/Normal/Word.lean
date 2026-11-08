module

public import SmoothedOctagon.Reduction.Defs

/-!
# Abnormal vertex sequences: the word argument for normality

This module is pure real algebra. It isolates what an abnormal (`λ = 0`) Pontryagin lift of a
finite vertex trajectory leaves at the switching times, written in the coordinates
`μ_j(M) = √3 ⟨M, Z_{e_j}⟩` of `𝔰𝔩₂(ℝ)`, and proves that such data cannot close up under the twist.

For a vertex piece with label `i` and factor `q = exp(2 t / p_i) > 1`, the linear map
`gnL i q` fixes the `i`-th coordinate and sends `v_{i+1} ↦ (v_i + v_{i+1}) q - v_i`,
`v_{i-1} ↦ (v_i + v_{i-1}) / q - v_i` (the one-arc margin map). Along an abnormal lift the margins
`m = (p₀, p₁, p₂)` and the coordinates `β = μ(b)` of `b = Λ_R + 2Λ₁ + ⟨Λ₁, X⟩X` move by `gnL i q`,
and the coordinates `α = μ(a)` of `a = -XΛ₁X` move by `gnL i q²`; the vertex Hamiltonians are
`H_j = (2α_j + β_j)/p_j`, and `⟨b, X⟩ = 0` reads `∑_{j ≠ l} β_j m_l = 0`
(`Normal/Bridge.lean` derives all of this from `IsPontryaginExtremal`).

In these coordinates every transport is the margin map, and both triple-tie implications (a
bounce `i, j, i` forces `H_j = 0` at both of its ends) follow from one forward identity
(`GnSeq.bounce`).

## Main API

* `Fin 3` helpers: `gn_add_one_ne`, `gn_add_two_ne`, `gn_add_two_ne_add_one`, `gn_fin3_cases`,
  `gn_ne_cases`, `gn_cover`, `gn_add_one_add_one`, `gn_add_two_add_two`, `gn_three_cases`.
* `gnL i q v`: the one-arc transfer; `gnL_self`, `gnL_add_one`, `gnL_add_two`, `gnL_pair`
  (`v_i + v_j ↦ (v_i + v_j) ρ`, `ρ = gnRho i j q ∈ {q, q⁻¹}`), `gnRho_sq`, `gnRho_pos`,
  `gnRho_ne_one`, `gnRho_add_one`, `gnRho_add_two`, `gnRho_succ_add_two`, `gnRho_add_two_succ`;
  `gn_perp_rel` (the form `∑_{j ≠ l} v_j m_l` in relabeled coordinates).
* `gn_core_forward`, `gn_core_reverse`: the scalar cores of the exclusion of three equal switch
  signs (`+ + +` and `- - -`).
* `GnSeq`: an abstract abnormal sequence indexed by the switching times `k : ℕ` (labels, factors,
  margins, `α`, `β`, transports, `⟨b, X⟩ = 0`, `H_{i_k} = 0`, `H_j ≤ 0`, nontriviality).
* `GnSeq.sig k j = 2 α_j + β_j` (the vertex Hamiltonian times the margin `p_j`);
  `GnSeq.sig_succ_lab`, `GnSeq.α_pair`, `GnSeq.β_pair`, `GnSeq.sig_succ`, `GnSeq.sig_all`.
* `GnSeq.no_double_tie`: no piece has triple ties at both ends.
* `GnSeq.bounce`: for labels `i, j, i` on pieces `k, k+1, k+2`, `H_j` vanishes at the start of
  piece `k` and at the end of piece `k + 2`.
* `GnSeq.not_three`: no three consecutive equal switch signs.
* `GnSeq.lab_add_two`, `GnSeq.false_of_twist`: signs alternate, so no abnormal sequence
  satisfies the twist `i_{k+N} = i_k + 1`.
-/

@[expose] public section

namespace SmoothedOctagon.Reduction

/-! ### `Fin 3` -/

theorem gn_add_one_ne (j : Fin 3) : j + 1 ≠ j := by revert j; decide

theorem gn_add_two_ne (j : Fin 3) : j + 2 ≠ j := by revert j; decide

theorem gn_add_two_ne_add_one (j : Fin 3) : j + 2 ≠ j + 1 := by revert j; decide

theorem gn_fin3_cases (j m : Fin 3) : m = j ∨ m = j + 1 ∨ m = j + 2 := by
  revert j m; decide

theorem gn_ne_cases {j m : Fin 3} (h : m ≠ j) : m = j + 1 ∨ m = j + 2 := by
  rcases gn_fin3_cases j m with h' | h' | h'
  · exact absurd h' h
  · exact Or.inl h'
  · exact Or.inr h'

/-- Three pairwise distinct elements of `Fin 3` exhaust it. -/
theorem gn_cover {a b c : Fin 3} (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) (m : Fin 3) :
    m = a ∨ m = b ∨ m = c := by
  revert a b c m; decide

theorem gn_add_one_add_one (j : Fin 3) : j + 1 + 1 = j + 2 := by revert j; decide

theorem gn_add_two_add_two (j : Fin 3) : j + 2 + 2 = j + 1 := by revert j; decide

/-! ### The one-arc transfer -/

/-- The one-arc transfer `L_i(q)`: `v_i ↦ v_i`, `v_{i+1} ↦ (v_i + v_{i+1}) q - v_i`,
`v_{i+2} ↦ (v_i + v_{i+2}) / q - v_i`. -/
noncomputable def gnL (i : Fin 3) (q : ℝ) (v : Fin 3 → ℝ) (j : Fin 3) : ℝ :=
  if j = i then v i else if j = i + 1 then (v i + v j) * q - v i else (v i + v j) / q - v i

theorem gnL_self (i : Fin 3) (q : ℝ) (v : Fin 3 → ℝ) : gnL i q v i = v i := ite_eq_left rfl

theorem gnL_add_one (i : Fin 3) (q : ℝ) (v : Fin 3 → ℝ) :
    gnL i q v (i + 1) = (v i + v (i + 1)) * q - v i := by
  rw [gnL, ite_eq_right (gn_add_one_ne i), ite_eq_left rfl]

theorem gnL_add_two (i : Fin 3) (q : ℝ) (v : Fin 3 → ℝ) :
    gnL i q v (i + 2) = (v i + v (i + 2)) / q - v i := by
  rw [gnL, ite_eq_right (gn_add_two_ne i), ite_eq_right (gn_add_two_ne_add_one i)]

/-- The factor by which the pair sum `v_i + v_j` is multiplied: `q` if `j = i + 1`, else `q⁻¹`. -/
noncomputable def gnRho (i j : Fin 3) (q : ℝ) : ℝ := if j = i + 1 then q else q⁻¹

theorem gnL_pair {i j : Fin 3} (h : j ≠ i) (q : ℝ) (v : Fin 3 → ℝ) :
    gnL i q v i + gnL i q v j = (v i + v j) * gnRho i j q := by
  rcases gn_ne_cases h with rfl | rfl
  · rw [gnL_self, gnL_add_one, gnRho, ite_eq_left rfl]; ring
  · rw [gnL_self, gnL_add_two, gnRho, ite_eq_right (gn_add_two_ne_add_one i)]; ring

theorem gnRho_sq (i j : Fin 3) (q : ℝ) : gnRho i j (q ^ 2) = gnRho i j q ^ 2 := by
  unfold gnRho; split_ifs <;> simp [inv_pow]

theorem gnRho_pos (i j : Fin 3) {q : ℝ} (hq : 0 < q) : 0 < gnRho i j q := by
  unfold gnRho; split_ifs
  · exact hq
  · exact inv_pos.2 hq

theorem gnRho_ne_one (i j : Fin 3) {q : ℝ} (hq : 1 < q) : gnRho i j q ≠ 1 := by
  unfold gnRho; split_ifs
  · exact hq.ne'
  · rw [Ne, inv_eq_one]; exact hq.ne'

theorem gnRho_add_one (i : Fin 3) (q : ℝ) : gnRho i (i + 1) q = q := ite_eq_left rfl

theorem gnRho_add_two (i : Fin 3) (q : ℝ) : gnRho i (i + 2) q = q⁻¹ :=
  ite_eq_right (gn_add_two_ne_add_one i)

theorem gnRho_succ_add_two (j : Fin 3) (q : ℝ) : gnRho (j + 1) (j + 2) q = q := by
  rw [← gn_add_one_add_one]; exact gnRho_add_one _ _

theorem gnRho_add_two_succ (j : Fin 3) (q : ℝ) : gnRho (j + 2) (j + 1) q = q⁻¹ := by
  rw [← gn_add_two_add_two]; exact gnRho_add_two _ _

/-- The form `∑_{j ≠ l} v_j m_l` (four times `⟨b, X⟩`) is invariant under cyclic relabeling. -/
theorem gn_perp_rel (v m : Fin 3 → ℝ) (j : Fin 3) :
    v 0 * (m 1 + m 2) + v 1 * (m 0 + m 2) + v 2 * (m 0 + m 1) =
      v j * (m (j + 1) + m (j + 2)) + v (j + 1) * (m j + m (j + 2)) +
        v (j + 2) * (m j + m (j + 1)) := by
  fin_cases j
  · rfl
  · simp only [Fin.mk_one, show (1 : Fin 3) + 1 = 2 from rfl, show (1 : Fin 3) + 2 = 0 from rfl]
    ring
  · simp only [show (⟨2, by norm_num⟩ : Fin 3) = 2 from rfl, show (2 : Fin 3) + 1 = 0 from rfl,
      show (2 : Fin 3) + 2 = 1 from rfl]
    ring

/-! ### Two scalar cores of the three-equal-signs exclusion -/

/-- Forward core (`+ + +`), in coordinates relative to the label `j` of the second piece. -/
theorem gn_core_forward {A0 B0 x1 x2 y1 y2 z w M0 M1 M2 Q R : ℝ} (hQ : 1 < Q) (hR : 1 < R)
    (hM0 : 0 < M0) (hM1 : 0 < M1) (hm : M0 * Q < M0 + M2)
    (hB0 : 2 * A0 + B0 = 0) (h2 : 2 * x2 + y2 = 0) (hN1 : 2 * x1 + y1 ≤ 0)
    (h4 : 2 * x1 * Q ^ 2 + y1 * Q = 0) (hN2 : 2 * x2 + y2 * Q ≤ 0)
    (hz : z * Q ^ 2 = x1 * Q ^ 4 + x2 - 2 * A0 * Q ^ 2) (h6 : 2 * z * R ^ 2 + w * R = 0)
    (hzw : (2 * z + w) * Q ^ 2 = 2 * x2 + y2 * Q)
    (hK : B0 * (M1 + M2) + (y1 - B0) * (M0 + M2) + (y2 - B0) * (M0 + M1) = 0) :
    2 * x1 + y1 = 0 ∧ 2 * x2 + y2 * Q = 0 := by
  have hQ0 : 0 < Q := by linarith
  have hy1 : y1 = -2 * x1 * Q := by
    have : Q * (2 * x1 * Q + y1) = 0 := by linear_combination h4
    rcases mul_eq_zero.1 this with h | h
    · linarith
    · linarith
  have hy2 : y2 = -2 * x2 := by linarith
  have hx1 : 0 ≤ x1 := by
    rw [hy1] at hN1; nlinarith
  have hx2 : 0 ≤ x2 := by
    rw [hy2] at hN2; nlinarith
  have key : 2 * R * ((R - 1) * Q ^ 3 * (M0 + M2 - Q * M0) * x1 +
      ((R - 1) * Q ^ 2 * (M0 + M1) + (Q - R) * M0) * x2) = 0 := by
    linear_combination (-2 * M0 * Q ^ 2 * R * (R - 1)) * hB0 +
      (Q * R * (M0 * Q * R - M0 * Q + M0 + M1 * Q * R - M1 * Q)) * h2 +
      (Q * R * (M0 + M2) * (R - 1)) * h4 + (2 * M0 * R * (R - 1)) * hz + (-M0 * Q ^ 2) * h6 +
      (M0 * R) * hzw + (-Q ^ 2 * R * (R - 1)) * hK
  have hc1 : 0 < (R - 1) * Q ^ 3 * (M0 + M2 - Q * M0) := by
    have : 0 < M0 + M2 - Q * M0 := by linarith
    have : 0 < R - 1 := by linarith
    positivity
  have hc2 : 0 < (R - 1) * Q ^ 2 * (M0 + M1) + (Q - R) * M0 := by
    have e : (R - 1) * Q ^ 2 * (M0 + M1) + (Q - R) * M0 =
        M0 * (Q - 1) * (R * Q + R - Q) + (R - 1) * Q ^ 2 * M1 := by ring
    rw [e]
    have : 0 < R * Q + R - Q := by nlinarith
    have : 0 < Q - 1 := by linarith
    have : 0 < R - 1 := by linarith
    positivity
  have hsum : (R - 1) * Q ^ 3 * (M0 + M2 - Q * M0) * x1 +
      ((R - 1) * Q ^ 2 * (M0 + M1) + (Q - R) * M0) * x2 = 0 := by
    have : (2 * R) ≠ 0 := by positivity
    exact (mul_eq_zero.1 key).resolve_left this
  have hx1' : x1 = 0 := by nlinarith [mul_nonneg hc1.le hx1, mul_nonneg hc2.le hx2]
  have hx2' : x2 = 0 := by nlinarith [mul_nonneg hc1.le hx1, mul_nonneg hc2.le hx2]
  constructor
  · rw [hy1, hx1']; ring
  · rw [hy2, hx2']; ring

/-- Reverse core (`- - -`), in coordinates relative to the label `j` of the second piece. -/
theorem gn_core_reverse {A0 B0 x1 x2 y1 y2 z w M0 M1 M2 Q R : ℝ} (hQ : 1 < Q) (hR : 1 < R)
    (hM0 : 0 < M0) (hM1 : 0 < M1) (hm : M0 * Q < M0 + M2)
    (hB0 : 2 * A0 + B0 = 0) (h2 : 2 * x1 + y1 = 0) (hN1 : 2 * x2 + y2 ≤ 0)
    (h4 : 2 * x2 + y2 * Q = 0) (hN2 : 2 * x1 * Q ^ 2 + y1 * Q ≤ 0)
    (hz : z * Q ^ 2 = x1 * Q ^ 4 + x2 - 2 * A0 * Q ^ 2) (h6 : 2 * z + w * R = 0)
    (hzw : 2 * z + w = 2 * x1 * Q ^ 2 + y1 * Q)
    (hK : B0 * (M1 + M2) + (y1 - B0) * (M0 + M2) + (y2 - B0) * (M0 + M1) = 0) :
    2 * x2 + y2 = 0 ∧ 2 * x1 * Q ^ 2 + y1 * Q = 0 := by
  have hQ0 : 0 < Q := by linarith
  have hy1 : y1 = -2 * x1 := by linarith
  have hx1 : x1 ≤ 0 := by
    rw [hy1] at hN2
    have hpos : 0 < 2 * Q * (Q - 1) := by nlinarith
    by_contra hcon
    rw [not_le] at hcon
    nlinarith [mul_pos hpos hcon]
  have hx2 : x2 ≤ 0 := by
    have hy2 : y2 * Q = -2 * x2 := by linarith
    have : (2 * x2 + y2) * Q ≤ 0 := mul_nonpos_of_nonpos_of_nonneg hN1 hQ0.le
    nlinarith
  have key : 2 * (Q ^ 2 * (M0 * (Q - 1) * (Q + 1 - R) + (R - 1) * M2) * x1 +
      (R - 1) * ((M0 + M1) * Q - M0) * x2) = 0 := by
    linear_combination (-2 * M0 * Q ^ 2 * (R - 1)) * hB0 +
      (-Q ^ 2 * (M0 * Q * R - M0 * R + M0 - M2 * R + M2)) * h2 +
      (Q * (M0 + M1) * (R - 1)) * h4 + (2 * M0 * (R - 1)) * hz + (M0 * Q ^ 2) * h6 +
      (-M0 * Q ^ 2 * R) * hzw + (-Q ^ 2 * (R - 1)) * hK
  have hc1 : 0 < Q ^ 2 * (M0 * (Q - 1) * (Q + 1 - R) + (R - 1) * M2) := by
    have e : M0 * (Q - 1) * (Q + 1 - R) + (R - 1) * M2 =
        (R - 1) * (M0 + M2 - M0 * Q) + M0 * Q * (Q - 1) := by ring
    rw [e]
    have : 0 < M0 + M2 - M0 * Q := by linarith
    have : 0 < Q - 1 := by linarith
    have : 0 < R - 1 := by linarith
    positivity
  have hc2 : 0 < (R - 1) * ((M0 + M1) * Q - M0) := by
    have : 0 < (M0 + M1) * Q - M0 := by nlinarith
    have : 0 < R - 1 := by linarith
    positivity
  have hsum : Q ^ 2 * (M0 * (Q - 1) * (Q + 1 - R) + (R - 1) * M2) * x1 +
      (R - 1) * ((M0 + M1) * Q - M0) * x2 = 0 := by linarith
  have hx1' : x1 = 0 := by
    nlinarith [mul_nonpos_of_nonneg_of_nonpos hc1.le hx1, mul_nonpos_of_nonneg_of_nonpos hc2.le hx2]
  have hx2' : x2 = 0 := by
    nlinarith [mul_nonpos_of_nonneg_of_nonpos hc1.le hx1, mul_nonpos_of_nonneg_of_nonpos hc2.le hx2]
  constructor
  · have hy2 : y2 * Q = 0 := by rw [hx2'] at h4; linarith
    have : y2 = 0 := (mul_eq_zero.1 hy2).resolve_right hQ0.ne'
    rw [this, hx2']; ring
  · rw [hy1, hx1']; ring

theorem gn_three_cases {a j b c : Fin 3} (ha : a ≠ j) (hb : b ≠ j) (hab : b ≠ a) (hc : c ≠ b)
    (hcj : c ≠ j) :
    (a = j + 2 ∧ b = j + 1 ∧ c = j + 2) ∨ (a = j + 1 ∧ b = j + 2 ∧ c = j + 1) := by
  revert a j b c; decide

/-! ### Abstract abnormal sequences -/

/-- An **abnormal sequence**: what an abnormal (`λ = 0`) lift of a finite vertex trajectory leaves
at its switching times `τ_k`, `k : ℕ` (continued through the twist), in the coordinates
`μ_j(M) = √3 ⟨M, Z_{e_j}⟩`. Piece `k` runs from `τ_k` to `τ_{k+1}` with label `i_k`. -/
structure GnSeq where
  /-- The label `i_k` of piece `k`. -/
  lab : ℕ → Fin 3
  /-- The factor `q_k = exp(2 (τ_{k+1} - τ_k) / p_{i_k}) > 1` of piece `k`. -/
  Q : ℕ → ℝ
  /-- The margins `p_j(X(τ_k))`. -/
  m : ℕ → Fin 3 → ℝ
  /-- The coordinates `μ_j(a(τ_k))` of `a = -XΛ₁X`. -/
  α : ℕ → Fin 3 → ℝ
  /-- The coordinates `μ_j(b(τ_k))` of `b = Λ_R + 2Λ₁ + ⟨Λ₁, X⟩X`. -/
  β : ℕ → Fin 3 → ℝ
  one_lt_Q : ∀ k, 1 < Q k
  m_pos : ∀ k j, 0 < m k j
  m_succ : ∀ k, m (k + 1) = gnL (lab k) (Q k) (m k)
  α_succ : ∀ k, α (k + 1) = gnL (lab k) (Q k ^ 2) (α k)
  β_succ : ∀ k, β (k + 1) = gnL (lab k) (Q k) (β k)
  /-- `⟨b, X⟩ = 0`, i.e. `∑_{j ≠ l} β_j p_l = 0`. -/
  perp : ∀ k, β k 0 * (m k 1 + m k 2) + β k 1 * (m k 0 + m k 2) + β k 2 * (m k 0 + m k 1) = 0
  /-- The active Hamiltonian of piece `k` vanishes at `τ_k`. -/
  active : ∀ k, 2 * α k (lab k) + β k (lab k) = 0
  /-- Every vertex Hamiltonian is `≤ 0` at `τ_k`. -/
  sig_nonpos : ∀ k j, 2 * α k j + β k j ≤ 0
  /-- Nontriviality of the costate `(Λ₁, Λ_R)`. -/
  nontriv : ∀ k, α k ≠ 0 ∨ β k ≠ 0
  lab_succ_ne : ∀ k, lab (k + 1) ≠ lab k

namespace GnSeq

variable (S : GnSeq)

/-- `σ_j(k) = 2 α_j + β_j`, the vertex Hamiltonian `H_j` times the margin `p_j` at `τ_k`. -/
def sig (k : ℕ) (j : Fin 3) : ℝ := 2 * S.α k j + S.β k j

/-- The active Hamiltonian of piece `k` vanishes at its end. -/
theorem sig_succ_lab (k : ℕ) : S.sig (k + 1) (S.lab k) = 0 := by
  rw [sig, S.α_succ, S.β_succ, gnL_self, gnL_self]; exact S.active k

theorem α_pair (k : ℕ) {j : Fin 3} (h : j ≠ S.lab k) :
    S.α (k + 1) (S.lab k) + S.α (k + 1) j =
      (S.α k (S.lab k) + S.α k j) * gnRho (S.lab k) j (S.Q k) ^ 2 := by
  rw [S.α_succ, gnL_pair h, gnRho_sq]

theorem β_pair (k : ℕ) {j : Fin 3} (h : j ≠ S.lab k) :
    S.β (k + 1) (S.lab k) + S.β (k + 1) j =
      (S.β k (S.lab k) + S.β k j) * gnRho (S.lab k) j (S.Q k) := by
  rw [S.β_succ, gnL_pair h]

/-- `σ_j` at the end of piece `k`, for `j ≠ i_k`. -/
theorem sig_succ (k : ℕ) {j : Fin 3} (h : j ≠ S.lab k) :
    S.sig (k + 1) j = 2 * (S.α k (S.lab k) + S.α k j) * gnRho (S.lab k) j (S.Q k) ^ 2 +
      (S.β k (S.lab k) + S.β k j) * gnRho (S.lab k) j (S.Q k) := by
  have h1 := S.α_pair k h
  have h2 := S.β_pair k h
  have h3 := S.sig_succ_lab k
  unfold sig at h3 ⊢
  linear_combination 2 * h1 + h2 - h3

/-- A vanishing `σ_j` for three distinct labels: a triple tie. -/
theorem sig_all {k : ℕ} {a b c : Fin 3} (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (ha : S.sig k a = 0) (hb : S.sig k b = 0) (hc : S.sig k c = 0) (j : Fin 3) : S.sig k j = 0 := by
  rcases gn_cover hab hac hbc j with rfl | rfl | rfl <;> assumption

private theorem gn_eq_zero_of_mul {x ρ : ℝ} (hρ0 : ρ ≠ 0) (hρ1 : ρ - 1 ≠ 0)
    (h : 2 * x * ρ * (ρ - 1) = 0) : x = 0 := by
  rcases mul_eq_zero.1 h with h | h
  · rcases mul_eq_zero.1 h with h | h
    · linarith
    · exact absurd h hρ0
  · exact absurd h hρ1

/-- **No piece joins two triple ties**. If every vertex Hamiltonian vanishes at both ends of piece
`k`, the transport of the pair sums `α_i + α_j`, `β_i + β_j` by factors `ρ ≠ 0, 1` forces them to
vanish; then `⟨b, X⟩ = 0` gives `α_i = 0`, so `α = β = 0`, against nontriviality. -/
theorem no_double_tie (k : ℕ) (h0 : ∀ j, S.sig k j = 0) (h1 : ∀ j, S.sig (k + 1) j = 0) :
    False := by
  set i := S.lab k with hi
  have hpair : ∀ j, j ≠ i → S.α k i + S.α k j = 0 ∧ S.β k i + S.β k j = 0 := by
    intro j hj
    have e1 := S.sig_succ k hj
    rw [h1 j] at e1
    have e0 : 2 * (S.α k i + S.α k j) + (S.β k i + S.β k j) = 0 := by
      have := h0 i; have := h0 j; unfold sig at *; linarith
    have hρ0 : gnRho i j (S.Q k) ≠ 0 := (gnRho_pos i j (by linarith [S.one_lt_Q k])).ne'
    have hρ1 : gnRho i j (S.Q k) - 1 ≠ 0 := sub_ne_zero.2 (gnRho_ne_one i j (S.one_lt_Q k))
    have hx : S.α k i + S.α k j = 0 := gn_eq_zero_of_mul hρ0 hρ1 (by
      linear_combination -e1 - gnRho i j (S.Q k) * e0)
    exact ⟨hx, by linarith⟩
  obtain ⟨ha1, hb1⟩ := hpair (i + 1) (gn_add_one_ne i)
  obtain ⟨ha2, hb2⟩ := hpair (i + 2) (gn_add_two_ne i)
  have hbi : S.β k i = -2 * S.α k i := by have := h0 i; unfold sig at this; linarith
  have hK := S.perp k
  rw [gn_perp_rel (S.β k) (S.m k) i] at hK
  have h4 : 4 * S.α k i * S.m k i = 0 := by
    have e1 : S.β k (i + 1) = 2 * S.α k i := by linarith
    have e2 : S.β k (i + 2) = 2 * S.α k i := by linarith
    rw [e1, e2, hbi] at hK
    linear_combination hK
  have hai : S.α k i = 0 := by
    have hm := S.m_pos k i
    rcases mul_eq_zero.1 h4 with h | h
    · linarith
    · exact absurd h hm.ne'
  have hα : S.α k = 0 := by
    funext j
    rcases gn_fin3_cases i j with rfl | rfl | rfl
    · exact hai
    · simp only [Pi.zero_apply]; linarith
    · simp only [Pi.zero_apply]; linarith
  have hβ : S.β k = 0 := by
    funext j
    rcases gn_fin3_cases i j with rfl | rfl | rfl
    · simp only [Pi.zero_apply]; linarith
    · simp only [Pi.zero_apply]; linarith
    · simp only [Pi.zero_apply]; linarith
  rcases S.nontriv k with h | h
  · exact h hα
  · exact h hβ

/-- **A bounce forces ties at both ends**. If pieces `k, k+1, k+2` carry the labels `i, j, i`, then
`H_j` vanishes at the start of piece `k` and at the end of piece `k + 2`. -/
theorem bounce (k : ℕ) (h : S.lab (k + 2) = S.lab k) :
    S.sig k (S.lab (k + 1)) = 0 ∧ S.sig (k + 3) (S.lab (k + 1)) = 0 := by
  set i := S.lab k with hi
  set j := S.lab (k + 1) with hj
  have hji : j ≠ i := S.lab_succ_ne k
  have hij : i ≠ S.lab (k + 1) := fun e ↦ hji e.symm
  have hj2 : j ≠ S.lab (k + 2) := by rw [h]; exact hji
  -- the pair sums `x = α_i + α_j`, `y = β_i + β_j` are multiplied along each piece
  have pα0 := S.α_pair k hji
  have pβ0 := S.β_pair k hji
  have pα1 := S.α_pair (k + 1) hij
  have pβ1 := S.β_pair (k + 1) hij
  have pα2 := S.α_pair (k + 2) hj2
  have pβ2 := S.β_pair (k + 2) hj2
  rw [h] at pα2 pβ2
  simp only [← hi, ← hj, show k + 1 + 1 = k + 2 from rfl, show k + 2 + 1 = k + 3 from rfl]
    at pα0 pβ0 pα1 pβ1 pα2 pβ2
  set ρ0 := gnRho i j (S.Q k)
  set ρ1 := gnRho j i (S.Q (k + 1))
  have hρ0 : ρ0 ≠ 0 := (gnRho_pos i j (by linarith [S.one_lt_Q k])).ne'
  have hρ1 : ρ1 ≠ 0 := (gnRho_pos j i (by linarith [S.one_lt_Q (k + 1)])).ne'
  have hρ1' : ρ1 - 1 ≠ 0 := sub_ne_zero.2 (gnRho_ne_one j i (S.one_lt_Q (k + 1)))
  have s0 : S.sig k i = 0 := S.active k
  have s1 : S.sig (k + 1) i = 0 := S.sig_succ_lab k
  have s2 : S.sig (k + 1) j = 0 := S.active (k + 1)
  have s3 : S.sig (k + 2) j = 0 := S.sig_succ_lab (k + 1)
  have s4 : S.sig (k + 2) i = 0 := by have := S.active (k + 2); rwa [h] at this
  have s5 : S.sig (k + 3) i = 0 := by have := S.sig_succ_lab (k + 2); rwa [h] at this
  unfold sig at s0 s1 s2 s3 s4 s5
  -- at `τ_{k+1}` the pair sums vanish
  have hx1 : S.α (k + 1) i + S.α (k + 1) j = 0 := gn_eq_zero_of_mul hρ1 hρ1' (by
    linear_combination s3 + s4 - 2 * pα1 - pβ1 - ρ1 * (s1 + s2))
  have hy1 : S.β (k + 1) i + S.β (k + 1) j = 0 := by linarith
  have hx0 : S.α k i + S.α k j = 0 := by
    rw [hx1] at pα0
    exact (mul_eq_zero.1 pα0.symm).resolve_right (pow_ne_zero 2 hρ0)
  have hy0 : S.β k i + S.β k j = 0 := by
    rw [hy1] at pβ0
    exact (mul_eq_zero.1 pβ0.symm).resolve_right hρ0
  have hx2 : S.α (k + 2) i + S.α (k + 2) j = 0 := by
    rw [add_comm, pα1, add_comm, hx1, zero_mul]
  have hy2 : S.β (k + 2) i + S.β (k + 2) j = 0 := by
    rw [add_comm, pβ1, add_comm, hy1, zero_mul]
  rw [hx2, zero_mul] at pα2
  rw [hy2, zero_mul] at pβ2
  constructor
  · unfold sig; linarith
  · unfold sig; linarith

/-- **No three consecutive equal switch signs**. If `i_{k+2} ≠ i_k` and `i_{k+3} ≠ i_{k+1}`, the
switches `k, k+1, k+2` all go forward or all go backward; the two missing-vertex inequalities at
`τ_{k+1}`, `τ_{k+2}` then force triple ties at both ends of piece `k + 1`. -/
theorem not_three (k : ℕ) (h1 : S.lab (k + 2) ≠ S.lab k) (h2 : S.lab (k + 3) ≠ S.lab (k + 1)) :
    False := by
  set j := S.lab (k + 1) with hj
  have hQ := S.one_lt_Q (k + 1)
  have hR := S.one_lt_Q (k + 2)
  have hQ0 : 0 < S.Q (k + 1) := by linarith
  have hR0 : 0 < S.Q (k + 2) := by linarith
  have hM0 := S.m_pos (k + 1) j
  have hM1 := S.m_pos (k + 1) (j + 1)
  have hm : S.m (k + 1) j * S.Q (k + 1) < S.m (k + 1) j + S.m (k + 1) (j + 2) := by
    have h := S.m_pos (k + 2) (j + 2)
    rw [show k + 2 = k + 1 + 1 from rfl, S.m_succ, ← hj, gnL_add_two, sub_pos,
      lt_div_iff₀ hQ0] at h
    exact h
  have hK := S.perp (k + 1)
  rw [gn_perp_rel (S.β (k + 1)) (S.m (k + 1)) j] at hK
  have hα1 : S.α (k + 2) (j + 1) =
      (S.α (k + 1) j + S.α (k + 1) (j + 1)) * S.Q (k + 1) ^ 2 - S.α (k + 1) j := by
    rw [show k + 2 = k + 1 + 1 from rfl, S.α_succ, ← hj, gnL_add_one]
  have hα2 : S.α (k + 2) (j + 2) =
      (S.α (k + 1) j + S.α (k + 1) (j + 2)) / S.Q (k + 1) ^ 2 - S.α (k + 1) j := by
    rw [show k + 2 = k + 1 + 1 from rfl, S.α_succ, ← hj, gnL_add_two]
  have hz : (S.α (k + 2) (j + 1) + S.α (k + 2) (j + 2)) * S.Q (k + 1) ^ 2 =
      (S.α (k + 1) j + S.α (k + 1) (j + 1)) * S.Q (k + 1) ^ 4 +
        (S.α (k + 1) j + S.α (k + 1) (j + 2)) - 2 * S.α (k + 1) j * S.Q (k + 1) ^ 2 := by
    rw [hα1, hα2]; field_simp; ring
  have e1 := S.sig_succ (k + 1) (gn_add_one_ne j)
  have e2 := S.sig_succ (k + 1) (gn_add_two_ne j)
  rw [← hj, gnRho_add_one, show k + 1 + 1 = k + 2 from rfl] at e1
  rw [← hj, gnRho_add_two, show k + 1 + 1 = k + 2 from rfl] at e2
  have e2' : 2 * (S.α (k + 1) j + S.α (k + 1) (j + 2)) +
      (S.β (k + 1) j + S.β (k + 1) (j + 2)) * S.Q (k + 1) =
        S.Q (k + 1) ^ 2 * S.sig (k + 2) (j + 2) := by
    rw [e2]; field_simp
  have hB0 : 2 * S.α (k + 1) j + S.β (k + 1) j = 0 := S.active (k + 1)
  have hsum2 : S.sig (k + 2) (j + 1) + S.sig (k + 2) (j + 2) =
      2 * (S.α (k + 2) (j + 1) + S.α (k + 2) (j + 2)) +
        (S.β (k + 2) (j + 1) + S.β (k + 2) (j + 2)) := by unfold sig; ring
  have hsj : S.sig (k + 2) j = 0 := S.sig_succ_lab (k + 1)
  rcases gn_three_cases (S.lab_succ_ne k).symm (S.lab_succ_ne (k + 1)) h1 (S.lab_succ_ne (k + 2))
    h2 with ⟨ha, hb, hc⟩ | ⟨ha, hb, hc⟩ <;> rw [← hj] at ha hb hc
  · -- forward: labels `j + 2, j, j + 1, j + 2`
    have hs2 : S.sig (k + 1) (j + 2) = 0 := by have := S.sig_succ_lab k; rwa [ha] at this
    have hs4 : S.sig (k + 2) (j + 1) = 0 := by have := S.active (k + 2); rwa [hb] at this
    have hs6 : S.sig (k + 3) (j + 2) = 0 := by have := S.active (k + 3); rwa [hc] at this
    have e3 := S.sig_succ (k + 2) (j := j + 2) (by rw [hb]; exact gn_add_two_ne_add_one j)
    rw [hb, gnRho_succ_add_two, show k + 2 + 1 = k + 3 from rfl, hs6] at e3
    have hN2 := S.sig_nonpos (k + 2) (j + 2)
    obtain ⟨r1, r2⟩ := gn_core_forward hQ hR hM0 hM1 hm hB0
      (x1 := S.α (k + 1) j + S.α (k + 1) (j + 1)) (y1 := S.β (k + 1) j + S.β (k + 1) (j + 1))
      (x2 := S.α (k + 1) j + S.α (k + 1) (j + 2)) (y2 := S.β (k + 1) j + S.β (k + 1) (j + 2))
      (z := S.α (k + 2) (j + 1) + S.α (k + 2) (j + 2))
      (w := S.β (k + 2) (j + 1) + S.β (k + 2) (j + 2))
      (by unfold sig at hs2; linarith) (by linarith [S.sig_nonpos (k + 1) (j + 1)])
      (by linarith) (by rw [e2']; exact mul_nonpos_of_nonneg_of_nonpos (by positivity) hN2) hz
      (by linarith) (by rw [← hsum2, hs4, e2']; ring) (by linear_combination hK)
    have t1 : ∀ i, S.sig (k + 1) i = 0 := S.sig_all (gn_add_one_ne j).symm
      (gn_add_two_ne j).symm (gn_add_two_ne_add_one j).symm hB0
      (by unfold sig; linarith) hs2
    have t2 : ∀ i, S.sig (k + 2) i = 0 := by
      refine S.sig_all (gn_add_one_ne j).symm (gn_add_two_ne j).symm
        (gn_add_two_ne_add_one j).symm hsj hs4 ?_
      have : S.Q (k + 1) ^ 2 * S.sig (k + 2) (j + 2) = 0 := by rw [← e2']; exact r2
      exact (mul_eq_zero.1 this).resolve_left (by positivity)
    exact S.no_double_tie (k + 1) t1 t2
  · -- reverse: labels `j + 1, j, j + 2, j + 1`
    have hs2 : S.sig (k + 1) (j + 1) = 0 := by have := S.sig_succ_lab k; rwa [ha] at this
    have hs4 : S.sig (k + 2) (j + 2) = 0 := by have := S.active (k + 2); rwa [hb] at this
    have hs6 : S.sig (k + 3) (j + 1) = 0 := by have := S.active (k + 3); rwa [hc] at this
    have e3 := S.sig_succ (k + 2) (j := j + 1) (by rw [hb]; exact (gn_add_two_ne_add_one j).symm)
    rw [hb, gnRho_add_two_succ, show k + 2 + 1 = k + 3 from rfl, hs6] at e3
    have h6 : 2 * (S.α (k + 2) (j + 1) + S.α (k + 2) (j + 2)) +
        (S.β (k + 2) (j + 1) + S.β (k + 2) (j + 2)) * S.Q (k + 2) = 0 := by
      have : S.Q (k + 2) ^ 2 * (2 * (S.α (k + 2) (j + 2) + S.α (k + 2) (j + 1)) *
          (S.Q (k + 2))⁻¹ ^ 2 + (S.β (k + 2) (j + 2) + S.β (k + 2) (j + 1)) *
          (S.Q (k + 2))⁻¹) = 0 := by rw [← e3, mul_zero]
      rw [← this]; field_simp; ring
    obtain ⟨r1, r2⟩ := gn_core_reverse hQ hR hM0 hM1 hm hB0
      (x1 := S.α (k + 1) j + S.α (k + 1) (j + 1)) (y1 := S.β (k + 1) j + S.β (k + 1) (j + 1))
      (x2 := S.α (k + 1) j + S.α (k + 1) (j + 2)) (y2 := S.β (k + 1) j + S.β (k + 1) (j + 2))
      (z := S.α (k + 2) (j + 1) + S.α (k + 2) (j + 2))
      (w := S.β (k + 2) (j + 1) + S.β (k + 2) (j + 2))
      (by unfold sig at hs2; linarith) (by linarith [S.sig_nonpos (k + 1) (j + 2)])
      (by rw [e2', hs4, mul_zero])
      (by rw [← e1]; exact S.sig_nonpos (k + 2) (j + 1)) hz h6
      (by rw [← hsum2, hs4, add_zero, e1]) (by linear_combination hK)
    have t1 : ∀ i, S.sig (k + 1) i = 0 := S.sig_all (gn_add_one_ne j).symm
      (gn_add_two_ne j).symm (gn_add_two_ne_add_one j).symm hB0 hs2
      (by unfold sig; linarith)
    have t2 : ∀ i, S.sig (k + 2) i = 0 := S.sig_all (gn_add_one_ne j).symm
      (gn_add_two_ne j).symm (gn_add_two_ne_add_one j).symm hsj (by rw [e1]; exact r2) hs4
    exact S.no_double_tie (k + 1) t1 t2

/-- Away from the first piece, neighbouring switches have opposite signs: `i_{k+2} = i_k`. -/
theorem lab_add_two {k : ℕ} (hk : 1 ≤ k) : S.lab (k + 2) = S.lab k := by
  obtain ⟨k, rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
  by_contra hne
  by_cases ha : S.lab (k + 2) = S.lab k
  · by_cases hb : S.lab (k + 4) = S.lab (k + 2)
    · have b1 := (S.bounce k ha).2
      have b2 := (S.bounce (k + 2) hb).1
      have d12 : S.lab (k + 1) ≠ S.lab (k + 2) := (S.lab_succ_ne (k + 1)).symm
      have d23 : S.lab (k + 2) ≠ S.lab (k + 3) := (S.lab_succ_ne (k + 2)).symm
      have d13 : S.lab (k + 1) ≠ S.lab (k + 3) := fun e ↦ hne e.symm
      have t2 : ∀ i, S.sig (k + 2) i = 0 :=
        S.sig_all d12 d13 d23 (S.sig_succ_lab (k + 1)) (S.active (k + 2)) b2
      have t3 : ∀ i, S.sig (k + 3) i = 0 :=
        S.sig_all d12 d13 d23 b1 (S.sig_succ_lab (k + 2)) (S.active (k + 3))
      exact S.no_double_tie (k + 2) t2 t3
    · exact S.not_three (k + 1) hne hb
  · exact S.not_three k ha hne

/-- **No abnormal sequence closes under the twist**. Signs alternate from the second switch on, so
`i_{1+2n} = i_1`; but the twist gives `i_{1+2N} = i_1 + 2`. -/
theorem false_of_twist {N : ℕ} (htw : ∀ k, S.lab (k + N) = S.lab k + 1) : False := by
  have h2 : ∀ n, S.lab (1 + 2 * n) = S.lab 1 := by
    intro n
    induction n with
    | zero => rfl
    | succ n ih =>
      rw [show 1 + 2 * (n + 1) = 1 + 2 * n + 2 by ring, S.lab_add_two (by omega), ih]
  have := h2 N
  rw [show 1 + 2 * N = 1 + N + N by ring, htw, htw] at this
  revert this
  generalize S.lab 1 = a
  revert a; decide

end GnSeq

end SmoothedOctagon.Reduction
