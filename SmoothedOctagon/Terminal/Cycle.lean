module

public import SmoothedOctagon.Period.VertexFlow

/-!
# Terminal comparison: closed vertex cycles

The data of a normal vertex period that the terminal comparison uses, extended to all integer
indices by the twist: labels `i_k`, factors `q_k`, the margins `m_k = (p₀, p₁, p₂)(X(τ_k))` at the
switching times, the one-arc margin map, and the tangent closure written in the triangular
coordinates `X ↦ C X C⁻¹`, `C = [[√3, 1], [√3, -1]]`, in which the tangent factors are
`T₀(q) = diag(q, q⁻¹)`, `T₁(q) = [[q⁻¹, q - q⁻¹], [0, q]]`, `T₂(q) = [[q⁻¹, 0], [q⁻¹ - q, q]]` and
`R = [[0, 1], [-1, 1]]`.

* `Term.triFactor`, `Term.triR`, `Term.triC_conj_tangentFactor`, `Term.triC_conj_R`.
* `Term.Cycle N`: the abstract closed cycle; `Cycle.shift` (rebasing at a switch) and
  `Cycle.relabel` (relabeling by `R`) keep the raw cost `Cycle.rawCost`.
* `NormalPeriod.toCycle`, `NormalPeriod.cost_eq_rawCost`.
-/

@[expose] public section

namespace SmoothedOctagon

namespace Term

open SmoothedPolygons Set

private lemma tm_s3 : √3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
private lemma tm_s3pos : (0 : ℝ) < √3 := by positivity
private lemma tm_s3c : √3 ^ 3 = 3 * √3 := by rw [pow_succ, tm_s3]
private lemma tm_s3q : √3 ^ 4 = 9 := by
  rw [show (4 : ℕ) = 2 * 2 from rfl, pow_mul, tm_s3]; norm_num

/-- Normalize a polynomial identity in `√3`, using `√3² = 3`. -/
local macro "tm_ring" : tactic =>
  `(tactic| ((try ring_nf); (try simp only [tm_s3, tm_s3c, tm_s3q]); (try ring_nf)))

/-! ### Triangular coordinates -/

/-- The change of coordinates `C = [[√3, 1], [√3, -1]]`. -/
noncomputable def triC : Mat2 := !![√3, 1; √3, -1]

/-- `C⁻¹`. -/
noncomputable def triCinv : Mat2 := !![1 / (2 * √3), 1 / (2 * √3); 1 / 2, -(1 / 2)]

theorem triC_mul_triCinv : triC * triCinv = 1 := by
  have h := tm_s3pos
  rw [triC, triCinv, Matrix.mul_fin_two, Matrix.one_fin_two]
  congr 1 <;> field_simp <;> norm_num

theorem triCinv_mul_triC : triCinv * triC = 1 := by
  have h := tm_s3pos
  rw [triC, triCinv, Matrix.mul_fin_two, Matrix.one_fin_two]
  congr 1 <;> field_simp <;> norm_num

/-- The tangent factors in triangular coordinates. -/
noncomputable def triFactor (i : Fin 3) (q : ℝ) : Mat2 :=
  ![!![q, 0; 0, q⁻¹], !![q⁻¹, q - q⁻¹; 0, q], !![q⁻¹, 0; q⁻¹ - q, q]] i

/-- `R` in triangular coordinates. -/
def triR : Mat2 := !![0, 1; -1, 1]

/-- `R⁻¹` in triangular coordinates. -/
def triRinv : Mat2 := !![1, -1; 1, 0]

theorem triR_mul_triRinv : triR * triRinv = 1 := by
  rw [triR, triRinv, Matrix.mul_fin_two, Matrix.one_fin_two]; norm_num

theorem triRinv_mul_triR : triRinv * triR = 1 := by
  rw [triR, triRinv, Matrix.mul_fin_two, Matrix.one_fin_two]; norm_num

theorem triC_conj_tangentFactor (i : Fin 3) {q : ℝ} (hq : q ≠ 0) :
    triC * tangentFactor i q * triCinv = triFactor i q := by
  have h := tm_s3pos
  fin_cases i
  · rw [Fin.zero_eta, tangentFactor_zero_eq hq, triC, triCinv, triFactor]
    ext a b; fin_cases a <;> fin_cases b <;> simp [Matrix.mul_apply, Fin.sum_univ_two] <;>
      field_simp <;> tm_ring
  · rw [Fin.mk_one, tangentFactor_one_eq hq, triC, triCinv, triFactor]
    ext a b; fin_cases a <;> fin_cases b <;> simp [Matrix.mul_apply, Fin.sum_univ_two] <;>
      field_simp <;> tm_ring
  · rw [show (⟨2, by norm_num⟩ : Fin 3) = 2 from rfl, tangentFactor_two_eq hq, triC, triCinv,
      triFactor]
    ext a b; fin_cases a <;> fin_cases b <;> simp [Matrix.mul_apply, Fin.sum_univ_two] <;>
      field_simp <;> tm_ring

theorem triC_conj_R : triC * R * triCinv = triR := by
  have h := tm_s3pos
  rw [triC, triCinv, R, triR]
  simp only [Matrix.mul_fin_two]
  congr 1 <;> field_simp <;> tm_ring


theorem triFactor_succ (i : Fin 3) {q : ℝ} (hq : q ≠ 0) :
    triRinv * triFactor i q * triR = triFactor (i + 1) q := by
  fin_cases i <;> ext a b <;> fin_cases a <;> fin_cases b <;>
    simp [triFactor, triR, triRinv, Matrix.mul_apply, Fin.sum_univ_two] <;> field_simp <;> ring

theorem triFactor_mul_inv (i : Fin 3) {q : ℝ} (hq : q ≠ 0) :
    triFactor i q * triFactor i q⁻¹ = 1 := by
  fin_cases i <;> ext a b <;> fin_cases a <;> fin_cases b <;>
    simp [triFactor, Matrix.mul_apply, Fin.sum_univ_two, hq] <;> field_simp <;> ring

theorem triFactor_inv_mul (i : Fin 3) {q : ℝ} (hq : q ≠ 0) :
    triFactor i q⁻¹ * triFactor i q = 1 := by
  have := triFactor_mul_inv i (inv_ne_zero hq)
  rwa [inv_inv] at this

/-- A product of `R`-conjugates is the `R`-conjugate of the product. -/
theorem prod_conj_triR (n : ℕ) (A : ℕ → Mat2) :
    ((List.range n).map fun j ↦ triRinv * A j * triR).prod =
      triRinv * ((List.range n).map A).prod * triR := by
  induction n with
  | zero => simp [triRinv_mul_triR]
  | succ n ih =>
    rw [List.prod_range_succ, List.prod_range_succ, ih]
    simp only [Matrix.mul_assoc, ← Matrix.mul_assoc triR triRinv, triR_mul_triRinv,
      Matrix.one_mul]

/-! ### Closed vertex cycles -/

/-- The raw cost `a ((a + b)(q - 1) + (a + c)(1 - q⁻¹) - a log q)` of a vertex piece with active
margin `a`, growing margin `b`, decreasing margin `c` and factor `q`
(`arcCost = (√3/4) rawArc`). -/
noncomputable def rawArc (a b c q : ℝ) : ℝ :=
  a * ((a + b) * (q - 1) + (a + c) * (1 - q⁻¹) - a * Real.log q)

/-- **A closed vertex cycle with `N` pieces per period**: labels `lab k`, factors `q k > 1` and
switch margins `m k j > 0` (on the quadric `p₀p₁ + p₁p₂ + p₂p₀ = 4`), indexed by `ℤ` through the
twist, related by the one-arc margin map, and with the tangent closure from every switch. -/
structure Cycle (N : ℕ) where
  lab : ℤ → Fin 3
  q : ℤ → ℝ
  m : ℤ → Fin 3 → ℝ
  lab_add : ∀ k, lab (k + N) = lab k + 1
  lab_ne : ∀ k, lab (k + 1) ≠ lab k
  q_add : ∀ k, q (k + N) = q k
  one_lt_q : ∀ k, 1 < q k
  m_add : ∀ k j, m (k + N) j = m k (j - 1)
  m_pos : ∀ k j, 0 < m k j
  m_quad : ∀ k, m k 0 * m k 1 + m k 1 * m k 2 + m k 2 * m k 0 = 4
  m_act : ∀ k, m (k + 1) (lab k) = m k (lab k)
  m_grow : ∀ k, m (k + 1) (lab k + 1) = (m k (lab k) + m k (lab k + 1)) * q k - m k (lab k)
  m_decr : ∀ k, m (k + 1) (lab k - 1) = (m k (lab k) + m k (lab k - 1)) / q k - m k (lab k)
  closure : ∀ k, ((List.range N).map fun j : ℕ ↦ triFactor (lab (k + j)) (q (k + j))).prod = triR

namespace Cycle

variable {N : ℕ} (c : Cycle N)

/-- The raw cost of piece `k`. -/
noncomputable def arc (k : ℤ) : ℝ :=
  rawArc (c.m k (c.lab k)) (c.m k (c.lab k + 1)) (c.m k (c.lab k - 1)) (c.q k)

/-- The raw cost of one period: the cost is `(√3/4) rawCost`. -/
noncomputable def rawCost : ℝ := ∑ j ∈ Finset.range N, c.arc j

theorem arc_add (k : ℤ) : c.arc (k + N) = c.arc k := by
  simp only [arc, c.lab_add, c.m_add, c.q_add, add_sub_cancel_right,
    show ∀ x : Fin 3, x + 1 + 1 - 1 = x + 1 from fun x ↦ by abel]

/-- Any window of `N` consecutive pieces has the raw cost of one period. -/
theorem sum_window (k : ℤ) : ∑ j ∈ Finset.range N, c.arc (k + j) = c.rawCost := by
  have step : ∀ k : ℤ, ∑ j ∈ Finset.range N, c.arc (k + 1 + j) =
      ∑ j ∈ Finset.range N, c.arc (k + j) := by
    intro k
    rcases Nat.eq_zero_or_pos N with hN | hN
    · subst hN; simp
    obtain ⟨n, rfl⟩ : ∃ n, N = n + 1 := ⟨N - 1, by omega⟩
    rw [Finset.sum_range_succ, Finset.sum_range_succ']
    push_cast
    rw [show k + 1 + (n : ℤ) = k + ((n + 1 : ℕ) : ℤ) by push_cast; ring, c.arc_add, add_zero]
    congr 1
    refine Finset.sum_congr rfl fun j _ ↦ ?_
    congr 1; ring
  induction k using Int.induction_on with
  | zero => simp [rawCost]
  | succ i ih => rw [step, ih]
  | pred i ih => rw [← ih, ← step, sub_add_cancel]

/-- Rebasing at the switch `r`. -/
def shift (r : ℤ) : Cycle N where
  lab k := c.lab (k + r)
  q k := c.q (k + r)
  m k := c.m (k + r)
  lab_add k := by rw [show k + N + r = k + r + N by ring, c.lab_add]
  lab_ne k := by rw [show k + 1 + r = k + r + 1 by ring]; exact c.lab_ne _
  q_add k := by rw [show k + N + r = k + r + N by ring, c.q_add]
  one_lt_q k := c.one_lt_q _
  m_add k j := by rw [show k + N + r = k + r + N by ring, c.m_add]
  m_pos k j := c.m_pos _ _
  m_quad k := c.m_quad _
  m_act k := by rw [show k + 1 + r = k + r + 1 by ring]; exact c.m_act _
  m_grow k := by rw [show k + 1 + r = k + r + 1 by ring]; exact c.m_grow _
  m_decr k := by rw [show k + 1 + r = k + r + 1 by ring]; exact c.m_decr _
  closure k := by
    have := c.closure (k + r)
    rw [← this]
    congr 1
    refine List.map_congr_left fun j _ ↦ ?_
    rw [show k + j + r = k + r + j by ring]

theorem rawCost_shift (r : ℤ) : (c.shift r).rawCost = c.rawCost := by
  rw [← c.sum_window r]
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  simp only [arc, shift]
  rw [show (j : ℤ) + r = r + j by ring]

/-- Relabeling by `R`: every label increases by one. -/
def relabel : Cycle N where
  lab k := c.lab k + 1
  q := c.q
  m k j := c.m k (j - 1)
  lab_add k := by rw [c.lab_add]
  lab_ne k := by simpa using c.lab_ne k
  q_add := c.q_add
  one_lt_q := c.one_lt_q
  m_add k j := by rw [c.m_add]
  m_pos k j := c.m_pos _ _
  m_quad k := by
    have := c.m_quad k
    simp only [show (0 : Fin 3) - 1 = 2 from rfl, show (1 : Fin 3) - 1 = 0 from rfl,
      show (2 : Fin 3) - 1 = 1 from rfl]
    linarith
  m_act k := by simpa using c.m_act k
  m_grow k := by simpa using c.m_grow k
  m_decr k := by
    have := c.m_decr k
    simp only [add_sub_cancel_right]
    exact this
  closure k := by
    have h := prod_conj_triR N fun j : ℕ ↦ triFactor (c.lab (k + j)) (c.q (k + j))
    rw [c.closure k, triRinv_mul_triR, Matrix.one_mul] at h
    rw [← h]
    congr 1
    refine List.map_congr_left fun j _ ↦ ?_
    rw [triFactor_succ _ (by linarith [c.one_lt_q (k + j)] : c.q (k + j) ≠ 0)]

theorem rawCost_relabel : c.relabel.rawCost = c.rawCost := by
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  show rawArc (c.m j (c.lab j + 1 - 1)) (c.m j (c.lab j + 1 + 1 - 1)) (c.m j (c.lab j + 1 - 1 - 1))
    (c.q j) = _
  simp only [add_sub_cancel_right, arc]

theorem q_pos (k : ℤ) : 0 < c.q k := by linarith [c.one_lt_q k]

end Cycle


/-! ### The tangent closure from every switch -/

/-- If `A (k + N) = R⁻¹ A k R` and each `A k` is invertible, then the products of `N` consecutive
factors from `k` and from `k + 1` are `R` together. -/
theorem prod_window_succ_iff {N : ℕ} (A B : ℤ → Mat2) (hA : ∀ k, A (k + N) = triRinv * A k * triR)
    (hAB : ∀ k, A k * B k = 1) (hBA : ∀ k, B k * A k = 1) (k : ℤ) :
    ((List.range N).map fun j : ℕ ↦ A (k + j)).prod = triR ↔
      ((List.range N).map fun j : ℕ ↦ A (k + 1 + j)).prod = triR := by
  have hsplit : ((List.range N).map fun j : ℕ ↦ A (k + j)).prod * A (k + N) =
      A k * ((List.range N).map fun j : ℕ ↦ A (k + 1 + j)).prod := by
    have h1 := List.prod_range_succ (fun j : ℕ ↦ A (k + j)) N
    have h2 := List.prod_range_succ' (fun j : ℕ ↦ A (k + j)) N
    rw [← h1, h2]
    simp only [Nat.cast_zero, add_zero, Nat.cast_succ]
    congr 2
    refine List.map_congr_left fun j _ ↦ ?_
    congr 1; ring
  constructor
  · intro h
    rw [h, hA, ← Matrix.mul_assoc, ← Matrix.mul_assoc, triR_mul_triRinv, Matrix.one_mul] at hsplit
    have := congrArg (B k * ·) hsplit
    simpa only [← Matrix.mul_assoc, hBA, Matrix.one_mul] using this.symm
  · intro h
    rw [h] at hsplit
    have e : A k * triR = triR * A (k + N) := by
      rw [hA, ← Matrix.mul_assoc, ← Matrix.mul_assoc, triR_mul_triRinv, Matrix.one_mul]
    rw [e] at hsplit
    have := congrArg (· * B (k + N)) hsplit
    simpa only [Matrix.mul_assoc, hAB, Matrix.mul_one] using this

/-- The tangent closure from `0` gives the tangent closure from every switch. -/
theorem closure_of_closure_zero {N : ℕ} (lab : ℤ → Fin 3) (q : ℤ → ℝ)
    (hlab : ∀ k, lab (k + N) = lab k + 1) (hq : ∀ k, q (k + N) = q k) (hq0 : ∀ k, q k ≠ 0)
    (h0 : ((List.range N).map fun j : ℕ ↦ triFactor (lab j) (q j)).prod = triR) (k : ℤ) :
    ((List.range N).map fun j : ℕ ↦ triFactor (lab (k + j)) (q (k + j))).prod = triR := by
  have key := prod_window_succ_iff (N := N) (fun k ↦ triFactor (lab k) (q k))
    (fun k ↦ triFactor (lab k) (q k)⁻¹)
    (fun k ↦ by simp only [hlab, hq]; rw [triFactor_succ _ (hq0 k)])
    (fun k ↦ triFactor_mul_inv _ (hq0 k)) (fun k ↦ triFactor_inv_mul _ (hq0 k))
  induction k using Int.induction_on with
  | zero => simpa using h0
  | succ i ih => exact (key i).1 ih
  | pred i ih => exact (key _).2 (by rwa [sub_add_cancel])

/-- Conjugating an ordered product. -/
theorem prod_conj_triC (n : ℕ) (A : ℕ → Mat2) :
    ((List.range n).map fun j ↦ triC * A j * triCinv).prod =
      triC * ((List.range n).map A).prod * triCinv := by
  induction n with
  | zero => simp [triC_mul_triCinv]
  | succ n ih =>
    rw [List.prod_range_succ, List.prod_range_succ, ih]
    simp only [Matrix.mul_assoc, ← Matrix.mul_assoc triCinv triC, triCinv_mul_triC,
      Matrix.one_mul]

end Term

/-! ### The cycle of a normal period -/

namespace NormalPeriod

open Term

variable (P : NormalPeriod)

theorem term_N_pos : (0 : ℤ) < P.N := by exact_mod_cast P.rep.N_pos

theorem term_emod_nonneg (k : ℤ) : 0 ≤ k % P.N := Int.emod_nonneg k (term_N_pos P).ne'

theorem term_emod_lt (k : ℤ) : k % P.N < P.N := Int.emod_lt_of_pos k (term_N_pos P)

private lemma tm_emod_eq (k N : ℤ) : k % N = k - ((k / N : ℤ) : ℤ) * N := by
  rw [Int.emod_def]; push_cast; ring

/-- The label increments are `N`-periodic, so `i_{k+1} - i_k = i_{r+1} - i_r` for `r = k mod N`. -/
private lemma tm_label_incr (k : ℤ) :
    P.rep.label (k + 1) - P.rep.label k =
      P.rep.label (k % P.N + 1) - P.rep.label (k % P.N) := by
  have hper : Function.Periodic (fun k : ℤ ↦ P.rep.label (k + 1) - P.rep.label k) (P.N : ℤ) := by
    intro k
    simp only [show k + P.N + 1 = k + 1 + P.N by ring, P.rep.label_add_period]
    abel
  have := hper.sub_int_mul_eq (x := k) (k / P.N)
  rw [tm_emod_eq]
  exact this.symm

theorem term_factor_emod (k : ℤ) : P.factor (k % P.N) = P.factor k := by
  have hper : Function.Periodic P.factor (P.N : ℤ) := P.factor_add_N
  rw [tm_emod_eq]
  exact hper.sub_int_mul_eq (x := k) (k / P.N)

/-- The switch margins of the twisted extension:
`m_k = (p_j(R^{-n} X(τ_r) R^n))_j`, `k = nN + r`, written with the label shift `i_k - i_r = n`. -/
noncomputable def termMargin (k : ℤ) (j : Fin 3) : ℝ :=
  margin (j - (P.rep.label k - P.rep.label (k % P.N))) (P.X (P.rep.τ (k % P.N)))

private lemma tm_margin_succ (k : ℤ) (j : Fin 3) :
    P.termMargin (k + 1) j =
      margin (j - (P.rep.label k - P.rep.label (k % P.N))) (P.X (P.rep.τ (k % P.N + 1))) := by
  have h0 := term_emod_nonneg P k
  have h1 := term_emod_lt P k
  have hincr := tm_label_incr P k
  have hmod1 : (k + 1) % P.N = (k % P.N + 1) % P.N := (Int.emod_add_emod k P.N 1).symm
  rcases lt_or_eq_of_le (show k % P.N + 1 ≤ P.N by omega) with hlt | heq
  · have hmod : (k + 1) % P.N = k % P.N + 1 := by
      rw [hmod1, Int.emod_eq_of_lt (by omega) hlt]
    rw [termMargin, hmod]
    congr 1
    rw [sub_eq_iff_eq_add] at hincr
    rw [hincr]
    abel
  · have hmod : (k + 1) % P.N = 0 := by
      rw [hmod1, heq, Int.emod_self]
    rw [termMargin, hmod, heq, P.margin_τ_N, P.rep.τ_zero]
    have hN : P.rep.label P.N = P.rep.label 0 + 1 := by
      simpa using P.rep.label_add_period 0
    rw [heq, hN, sub_eq_iff_eq_add] at hincr
    congr 1
    rw [hincr]
    abel

/-- The closed cycle of a normal period. -/
noncomputable def termCycle : Cycle P.N where
  lab := P.rep.label
  q := P.factor
  m := P.termMargin
  lab_add := P.rep.label_add_period
  lab_ne := P.rep.label_ne
  q_add := P.factor_add_N
  one_lt_q := P.one_lt_factor
  m_add k j := by
    simp only [termMargin, Int.add_emod_right, P.rep.label_add_period]
    congr 1; abel
  m_pos k j := margin_pos_of_isStarState
    (P.isStarState_τ (term_emod_nonneg P k) (term_emod_lt P k).le) _
  m_quad k := by
    have hst := P.isStarState_τ (term_emod_nonneg P k) (term_emod_lt P k).le
    have h4 := margin_mul_add_eq_four _ hst.1 hst.2.1
    simp only [termMargin]
    generalize P.rep.label k - P.rep.label (k % P.N) = s
    generalize P.X (P.rep.τ (k % P.N)) = Y at h4
    fin_cases s
    · simpa using h4
    · simp only [Fin.mk_one, show (0 : Fin 3) - 1 = 2 from rfl, show (1 : Fin 3) - 1 = 0 from rfl,
        show (2 : Fin 3) - 1 = 1 from rfl]
      linarith
    · simp only [show (⟨2, by norm_num⟩ : Fin 3) = 2 from rfl, show (0 : Fin 3) - 2 = 1 from rfl,
        show (1 : Fin 3) - 2 = 2 from rfl, show (2 : Fin 3) - 2 = 0 from rfl]
      linarith
  m_act k := by
    have hp := (P.piece_margin (term_emod_nonneg P k) (term_emod_lt P k)).1
    rw [tm_margin_succ, termMargin, sub_sub_cancel, hp, P.activeMargin_eq (term_emod_nonneg P k)
      (term_emod_lt P k)]
  m_grow k := by
    have hp := (P.piece_margin (term_emod_nonneg P k) (term_emod_lt P k)).2.1
    rw [tm_margin_succ, termMargin, termMargin,
      show P.rep.label k + 1 - (P.rep.label k - P.rep.label (k % P.N)) =
        P.rep.label (k % P.N) + 1 by abel, sub_sub_cancel, hp,
      P.activeMargin_eq (term_emod_nonneg P k) (term_emod_lt P k), term_factor_emod]
  m_decr k := by
    have hp := (P.piece_margin (term_emod_nonneg P k) (term_emod_lt P k)).2.2
    rw [tm_margin_succ, termMargin, termMargin,
      show P.rep.label k - 1 - (P.rep.label k - P.rep.label (k % P.N)) =
        P.rep.label (k % P.N) - 1 by abel, sub_sub_cancel, hp,
      P.activeMargin_eq (term_emod_nonneg P k) (term_emod_lt P k), term_factor_emod]
  closure k := by
    refine closure_of_closure_zero _ _ P.rep.label_add_period P.factor_add_N
      (fun k ↦ (P.factor_pos k).ne') ?_ k
    have h := P.tangentProduct_N
    have hc := prod_conj_triC P.N fun j : ℕ ↦ tangentFactor (P.rep.label j) (P.factor j)
    rw [← tangentProduct, h, triC_conj_R] at hc
    rw [← hc]
    congr 1
    refine List.map_congr_left fun j _ ↦ ?_
    rw [triC_conj_tangentFactor _ (P.factor_pos j).ne']

/-- **The cost of a normal period is `(√3/4)` times the raw cost of its cycle.** -/
theorem cost_eq_rawCost : P.cost = √3 / 4 * P.termCycle.rawCost := by
  rw [P.cost_eq_sum, Cycle.rawCost, Finset.mul_sum]
  refine Finset.sum_congr rfl fun k hk ↦ ?_
  have hk0 : (0 : ℤ) ≤ k := by positivity
  have hkN : (k : ℤ) < P.N := by exact_mod_cast Finset.mem_range.1 hk
  have hmod : (k : ℤ) % P.N = k := Int.emod_eq_of_lt hk0 hkN
  simp only [Cycle.arc, termCycle, termMargin, hmod, sub_self, sub_zero, arcCost, rawArc,
    P.activeMargin_eq hk0 hkN]
  ring

end NormalPeriod

end SmoothedOctagon
