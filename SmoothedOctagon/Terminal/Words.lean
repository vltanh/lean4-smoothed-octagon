module

public import SmoothedOctagon.Terminal.Cycle

/-!
# Terminal comparison: the words of at most five pieces

The tangent closure `T_{i_0}(q_0) ⋯ T_{i_{N-1}}(q_{N-1}) = R` (triangular coordinates) with all
factors `q_k > 1` excludes every reduced word of at most five letters except the octagon word
(four pieces, all forward), the orbit of `0 1 0 2 0` under rebasing and relabeling, and the
entirely reverse word `0 2 1 0 2`.

Route: the notes exclude most of these words with the fixed-edge obstruction and twisted rebasing
(`SMALL_PERIOD_COST_EQUALITY_AUDIT` §1); here every excluded word already contradicts two entries
of the tangent closure (the table of `legacy/FOUR_LINK_HAND_PROOF` (3), extended to five letters).

* `Term.word_*_false`: the excluded words.
* `Term.Cycle.cycle_one_false`, `cycle_two_false`, `cycle_three_false`;
  `cycle_four_forward` (four pieces are all forward); `cycle_five` (five pieces are entirely
  reverse, or rebase and relabel to `0 1 0 2 0` with the same raw cost).
* `Term.Cycle.exists_relabel_zero`, `incr_emod`, `lab_succ_of_window`.
-/

@[expose] public section

namespace SmoothedOctagon
namespace Term

open SmoothedPolygons

private lemma tm_entries {M : Mat2} (h : M = triR) :
    M 0 0 = 0 ∧ M 0 1 = 1 ∧ M 1 0 = -1 ∧ M 1 1 = 1 := by
  subst h; simp [triR]

theorem word_0_false {q0 : ℝ} (h0 : 1 < q0)
    (h : triFactor 0 q0 = triR) : False := by
  have p0 : (0:ℝ) < q0 := by linarith
  obtain ⟨e00, e01, e10, e11⟩ := tm_entries h
  simp [triFactor, Matrix.mul_apply, Fin.sum_univ_two] at e00 e01 e10 e11
  all_goals (try field_simp at e00 e01 e10 e11)
  all_goals (try (rcases e00 with e | e | e | e | e <;> linarith))
  all_goals nlinarith [p0]

theorem word_02_false {q0 q1 : ℝ} (h0 : 1 < q0) (h1 : 1 < q1)
    (h : triFactor 0 q0 * triFactor 2 q1 = triR) : False := by
  have p0 : (0:ℝ) < q0 := by linarith
  have p1 : (0:ℝ) < q1 := by linarith
  obtain ⟨e00, e01, e10, e11⟩ := tm_entries h
  simp [triFactor, Matrix.mul_apply, Fin.sum_univ_two] at e00 e01 e10 e11
  all_goals (try field_simp at e00 e01 e10 e11)
  all_goals (try (rcases e00 with e | e | e | e | e <;> linarith))
  all_goals nlinarith [p0, p1]

theorem word_012_false {q0 q1 q2 : ℝ} (h0 : 1 < q0) (h1 : 1 < q1) (h2 : 1 < q2)
    (h : triFactor 0 q0 * (triFactor 1 q1 * triFactor 2 q2) = triR) : False := by
  have p0 : (0:ℝ) < q0 := by linarith
  have p1 : (0:ℝ) < q1 := by linarith
  have p2 : (0:ℝ) < q2 := by linarith
  obtain ⟨e00, e01, e10, e11⟩ := tm_entries h
  simp [triFactor, Matrix.mul_apply, Fin.sum_univ_two] at e00 e01 e10 e11
  all_goals (try field_simp at e00 e01 e10 e11)
  all_goals (try (rcases e00 with e | e | e | e | e <;> linarith))
  all_goals nlinarith [p0, p1, p2]

theorem word_010_false {q0 q1 q2 : ℝ} (h0 : 1 < q0) (h1 : 1 < q1) (h2 : 1 < q2)
    (h : triFactor 0 q0 * (triFactor 1 q1 * triFactor 0 q2) = triR) : False := by
  have p0 : (0:ℝ) < q0 := by linarith
  have p1 : (0:ℝ) < q1 := by linarith
  have p2 : (0:ℝ) < q2 := by linarith
  obtain ⟨e00, e01, e10, e11⟩ := tm_entries h
  simp [triFactor, Matrix.mul_apply, Fin.sum_univ_two] at e00 e01 e10 e11
  all_goals (try field_simp at e00 e01 e10 e11)
  all_goals (try (rcases e00 with e | e | e | e | e <;> linarith))
  all_goals nlinarith [p0, p1, p2]

theorem word_020_false {q0 q1 q2 : ℝ} (h0 : 1 < q0) (h1 : 1 < q1) (h2 : 1 < q2)
    (h : triFactor 0 q0 * (triFactor 2 q1 * triFactor 0 q2) = triR) : False := by
  have p0 : (0:ℝ) < q0 := by linarith
  have p1 : (0:ℝ) < q1 := by linarith
  have p2 : (0:ℝ) < q2 := by linarith
  obtain ⟨e00, e01, e10, e11⟩ := tm_entries h
  simp [triFactor, Matrix.mul_apply, Fin.sum_univ_two] at e00 e01 e10 e11
  all_goals (try field_simp at e00 e01 e10 e11)
  all_goals (try (rcases e00 with e | e | e | e | e <;> linarith))
  all_goals nlinarith [p0, p1, p2]

theorem word_0102_false {q0 q1 q2 q3 : ℝ} (h0 : 1 < q0) (h1 : 1 < q1) (h2 : 1 < q2) (h3 : 1 < q3)
    (h : triFactor 0 q0 * (triFactor 1 q1 * (triFactor 0 q2 * triFactor 2 q3)) = triR) : False := by
  have p0 : (0:ℝ) < q0 := by linarith
  have p1 : (0:ℝ) < q1 := by linarith
  have p2 : (0:ℝ) < q2 := by linarith
  have p3 : (0:ℝ) < q3 := by linarith
  obtain ⟨e00, e01, e10, e11⟩ := tm_entries h
  simp [triFactor, Matrix.mul_apply, Fin.sum_univ_two] at e00 e01 e10 e11
  all_goals (try field_simp at e00 e01 e10 e11)
  all_goals (try (rcases e00 with e | e | e | e | e <;> linarith))
  all_goals nlinarith [p0, p1, p2, p3]

theorem word_0202_false {q0 q1 q2 q3 : ℝ} (h0 : 1 < q0) (h1 : 1 < q1) (h2 : 1 < q2) (h3 : 1 < q3)
    (h : triFactor 0 q0 * (triFactor 2 q1 * (triFactor 0 q2 * triFactor 2 q3)) = triR) : False := by
  have p0 : (0:ℝ) < q0 := by linarith
  have p1 : (0:ℝ) < q1 := by linarith
  have p2 : (0:ℝ) < q2 := by linarith
  have p3 : (0:ℝ) < q3 := by linarith
  obtain ⟨e00, e01, e10, e11⟩ := tm_entries h
  simp [triFactor, Matrix.mul_apply, Fin.sum_univ_two] at e00 e01 e10 e11
  all_goals (try field_simp at e00 e01 e10 e11)
  all_goals (try (rcases e00 with e | e | e | e | e <;> linarith))
  all_goals nlinarith [p0, p1, p2, p3]

theorem word_0212_false {q0 q1 q2 q3 : ℝ} (h0 : 1 < q0) (h1 : 1 < q1) (h2 : 1 < q2) (h3 : 1 < q3)
    (h : triFactor 0 q0 * (triFactor 2 q1 * (triFactor 1 q2 * triFactor 2 q3)) = triR) : False := by
  have p0 : (0:ℝ) < q0 := by linarith
  have p1 : (0:ℝ) < q1 := by linarith
  have p2 : (0:ℝ) < q2 := by linarith
  have p3 : (0:ℝ) < q3 := by linarith
  obtain ⟨e00, e01, e10, e11⟩ := tm_entries h
  simp [triFactor, Matrix.mul_apply, Fin.sum_univ_two] at e00 e01 e10 e11
  all_goals (try field_simp at e00 e01 e10 e11)
  all_goals (try (rcases e00 with e | e | e | e | e <;> linarith))
  all_goals nlinarith [p0, p1, p2, p3]

theorem word_0210_false {q0 q1 q2 q3 : ℝ} (h0 : 1 < q0) (h1 : 1 < q1) (h2 : 1 < q2) (h3 : 1 < q3)
    (h : triFactor 0 q0 * (triFactor 2 q1 * (triFactor 1 q2 * triFactor 0 q3)) = triR) : False := by
  have p0 : (0:ℝ) < q0 := by linarith
  have p1 : (0:ℝ) < q1 := by linarith
  have p2 : (0:ℝ) < q2 := by linarith
  have p3 : (0:ℝ) < q3 := by linarith
  obtain ⟨e00, e01, e10, e11⟩ := tm_entries h
  simp [triFactor, Matrix.mul_apply, Fin.sum_univ_two] at e00 e01 e10 e11
  all_goals (try field_simp at e00 e01 e10 e11)
  all_goals (try (rcases e00 with e | e | e | e | e <;> linarith))
  all_goals nlinarith [p0, p1, p2, p3]

theorem word_01212_false {q0 q1 q2 q3 q4 : ℝ} (h0 : 1 < q0) (h1 : 1 < q1) (h2 : 1 < q2) (h3 : 1 < q3) (h4 : 1 < q4)
    (h : triFactor 0 q0 * (triFactor 1 q1 * (triFactor 2 q2 * (triFactor 1 q3 * triFactor 2 q4))) = triR) : False := by
  have p0 : (0:ℝ) < q0 := by linarith
  have p1 : (0:ℝ) < q1 := by linarith
  have p2 : (0:ℝ) < q2 := by linarith
  have p3 : (0:ℝ) < q3 := by linarith
  have p4 : (0:ℝ) < q4 := by linarith
  obtain ⟨e00, e01, e10, e11⟩ := tm_entries h
  simp [triFactor, Matrix.mul_apply, Fin.sum_univ_two] at e00 e01 e10 e11
  all_goals (try field_simp at e00 e01 e10 e11)
  all_goals (try (rcases e00 with e | e | e | e | e <;> linarith))
  all_goals nlinarith [p0, p1, p2, p3, p4]

theorem word_01012_false {q0 q1 q2 q3 q4 : ℝ} (h0 : 1 < q0) (h1 : 1 < q1) (h2 : 1 < q2) (h3 : 1 < q3) (h4 : 1 < q4)
    (h : triFactor 0 q0 * (triFactor 1 q1 * (triFactor 0 q2 * (triFactor 1 q3 * triFactor 2 q4))) = triR) : False := by
  have p0 : (0:ℝ) < q0 := by linarith
  have p1 : (0:ℝ) < q1 := by linarith
  have p2 : (0:ℝ) < q2 := by linarith
  have p3 : (0:ℝ) < q3 := by linarith
  have p4 : (0:ℝ) < q4 := by linarith
  obtain ⟨e00, e01, e10, e11⟩ := tm_entries h
  simp [triFactor, Matrix.mul_apply, Fin.sum_univ_two] at e00 e01 e10 e11
  all_goals (try field_simp at e00 e01 e10 e11)
  all_goals (try (rcases e00 with e | e | e | e | e <;> linarith))
  all_goals nlinarith [p0, p1, p2, p3, p4]

theorem word_01010_false {q0 q1 q2 q3 q4 : ℝ} (h0 : 1 < q0) (h1 : 1 < q1) (h2 : 1 < q2) (h3 : 1 < q3) (h4 : 1 < q4)
    (h : triFactor 0 q0 * (triFactor 1 q1 * (triFactor 0 q2 * (triFactor 1 q3 * triFactor 0 q4))) = triR) : False := by
  have p0 : (0:ℝ) < q0 := by linarith
  have p1 : (0:ℝ) < q1 := by linarith
  have p2 : (0:ℝ) < q2 := by linarith
  have p3 : (0:ℝ) < q3 := by linarith
  have p4 : (0:ℝ) < q4 := by linarith
  obtain ⟨e00, e01, e10, e11⟩ := tm_entries h
  simp [triFactor, Matrix.mul_apply, Fin.sum_univ_two] at e00 e01 e10 e11
  all_goals (try field_simp at e00 e01 e10 e11)
  all_goals (try (rcases e00 with e | e | e | e | e <;> linarith))
  all_goals nlinarith [p0, p1, p2, p3, p4]

theorem word_02010_false {q0 q1 q2 q3 q4 : ℝ} (h0 : 1 < q0) (h1 : 1 < q1) (h2 : 1 < q2) (h3 : 1 < q3) (h4 : 1 < q4)
    (h : triFactor 0 q0 * (triFactor 2 q1 * (triFactor 0 q2 * (triFactor 1 q3 * triFactor 0 q4))) = triR) : False := by
  have p0 : (0:ℝ) < q0 := by linarith
  have p1 : (0:ℝ) < q1 := by linarith
  have p2 : (0:ℝ) < q2 := by linarith
  have p3 : (0:ℝ) < q3 := by linarith
  have p4 : (0:ℝ) < q4 := by linarith
  obtain ⟨e00, e01, e10, e11⟩ := tm_entries h
  simp [triFactor, Matrix.mul_apply, Fin.sum_univ_two] at e00 e01 e10 e11
  all_goals (try field_simp at e00 e01 e10 e11)
  all_goals (try (rcases e00 with e | e | e | e | e <;> linarith))
  all_goals nlinarith [p0, p1, p2, p3, p4]

theorem word_02020_false {q0 q1 q2 q3 q4 : ℝ} (h0 : 1 < q0) (h1 : 1 < q1) (h2 : 1 < q2) (h3 : 1 < q3) (h4 : 1 < q4)
    (h : triFactor 0 q0 * (triFactor 2 q1 * (triFactor 0 q2 * (triFactor 2 q3 * triFactor 0 q4))) = triR) : False := by
  have p0 : (0:ℝ) < q0 := by linarith
  have p1 : (0:ℝ) < q1 := by linarith
  have p2 : (0:ℝ) < q2 := by linarith
  have p3 : (0:ℝ) < q3 := by linarith
  have p4 : (0:ℝ) < q4 := by linarith
  obtain ⟨e00, e01, e10, e11⟩ := tm_entries h
  simp [triFactor, Matrix.mul_apply, Fin.sum_univ_two] at e00 e01 e10 e11
  all_goals (try field_simp at e00 e01 e10 e11)
  all_goals (try (rcases e00 with e | e | e | e | e <;> linarith))
  all_goals nlinarith [p0, p1, p2, p3, p4]

/-! ### Normalizing the first label -/

namespace Cycle

variable {N : ℕ}

private lemma tm_fin3 (x : Fin 3) : x = 0 ∨ x = 1 ∨ x = 2 := by fin_cases x <;> simp

/-- Relabel a cycle so that its first label is `0`, keeping the raw cost; the labels change by a
constant. -/
theorem exists_relabel_zero (c : Cycle N) :
    ∃ c' : Cycle N, c'.lab 0 = 0 ∧ c'.rawCost = c.rawCost ∧ ∃ s : Fin 3, ∀ k, c'.lab k = c.lab k + s ∧
      c'.q k = c.q k ∧ ∀ j, c'.m k j = c.m k (j - s) := by
  rcases tm_fin3 (c.lab 0) with h | h | h
  · exact ⟨c, h, rfl, 0, fun k ↦ by simp⟩
  · refine ⟨c.relabel.relabel, ?_, by rw [rawCost_relabel, rawCost_relabel], 2, fun k ↦ ?_⟩
    · show c.lab 0 + 1 + 1 = 0; rw [h]; rfl
    · refine ⟨?_, rfl, fun j ↦ ?_⟩
      · show c.lab k + 1 + 1 = c.lab k + 2; abel_nf; rfl
      · show c.m k (j - 1 - 1) = c.m k (j - 2); congr 1; abel_nf; rfl
  · refine ⟨c.relabel, ?_, rawCost_relabel _, 1, fun k ↦ ⟨rfl, rfl, fun j ↦ rfl⟩⟩
    show c.lab 0 + 1 = 0; rw [h]; rfl

/-- The tangent closure from `0`, written as a right-nested product. -/
private lemma tm_closure_zero_five (c : Cycle 5) :
    triFactor (c.lab 0) (c.q 0) * (triFactor (c.lab 1) (c.q 1) * (triFactor (c.lab 2) (c.q 2) *
      (triFactor (c.lab 3) (c.q 3) * triFactor (c.lab 4) (c.q 4)))) = triR := by
  have h := c.closure 0
  simp only [List.range_succ, List.range_zero, List.map_append, List.map_cons, List.map_nil,
    List.prod_append, List.prod_cons, List.prod_nil, Matrix.mul_one, List.nil_append] at h
  simpa [Matrix.mul_assoc] using h

private lemma tm_rot_01020 (c : Cycle 5) (h0 : c.lab 0 = 0) (h1 : c.lab 1 = 1)
    (h2 : c.lab 2 = 0) (h3 : c.lab 3 = 2) (h4 : c.lab 4 = 0) :
    ∃ c' : Cycle 5, c'.rawCost = c.rawCost ∧ c'.lab 0 = 0 ∧ c'.lab 1 = 1 ∧ c'.lab 2 = 0 ∧
      c'.lab 3 = 2 ∧ c'.lab 4 = 0 := by
  refine ⟨c, by simp only [], ?_, ?_, ?_, ?_, ?_⟩
  · show c.lab (0 + 0) = 0
    rw [show (0 : ℤ) + 0 = 0 by norm_num, h0] <;> rfl
  · show c.lab (1 + 0) = 1
    rw [show (1 : ℤ) + 0 = 1 by norm_num, h1] <;> rfl
  · show c.lab (2 + 0) = 0
    rw [show (2 : ℤ) + 0 = 2 by norm_num, h2] <;> rfl
  · show c.lab (3 + 0) = 2
    rw [show (3 : ℤ) + 0 = 3 by norm_num, h3] <;> rfl
  · show c.lab (4 + 0) = 0
    rw [show (4 : ℤ) + 0 = 4 by norm_num, h4] <;> rfl

private lemma tm_rot_02120 (c : Cycle 5) (h0 : c.lab 0 = 0) (h1 : c.lab 1 = 2)
    (h2 : c.lab 2 = 1) (h3 : c.lab 3 = 2) (h4 : c.lab 4 = 0) :
    ∃ c' : Cycle 5, c'.rawCost = c.rawCost ∧ c'.lab 0 = 0 ∧ c'.lab 1 = 1 ∧ c'.lab 2 = 0 ∧
      c'.lab 3 = 2 ∧ c'.lab 4 = 0 := by
  refine ⟨c.shift 4, by simp only [rawCost_shift], ?_, ?_, ?_, ?_, ?_⟩
  · show c.lab (0 + 4) = 0
    rw [show (0 : ℤ) + 4 = 4 by norm_num, h4] <;> rfl
  · show c.lab (1 + 4) = 1
    rw [show (1 : ℤ) + 4 = 0 + ((5 : ℕ) : ℤ) by norm_num, c.lab_add, h0] <;> rfl
  · show c.lab (2 + 4) = 0
    rw [show (2 : ℤ) + 4 = 1 + ((5 : ℕ) : ℤ) by norm_num, c.lab_add, h1] <;> rfl
  · show c.lab (3 + 4) = 2
    rw [show (3 : ℤ) + 4 = 2 + ((5 : ℕ) : ℤ) by norm_num, c.lab_add, h2] <;> rfl
  · show c.lab (4 + 4) = 0
    rw [show (4 : ℤ) + 4 = 3 + ((5 : ℕ) : ℤ) by norm_num, c.lab_add, h3] <;> rfl

private lemma tm_rot_02012 (c : Cycle 5) (h0 : c.lab 0 = 0) (h1 : c.lab 1 = 2)
    (h2 : c.lab 2 = 0) (h3 : c.lab 3 = 1) (h4 : c.lab 4 = 2) :
    ∃ c' : Cycle 5, c'.rawCost = c.rawCost ∧ c'.lab 0 = 0 ∧ c'.lab 1 = 1 ∧ c'.lab 2 = 0 ∧
      c'.lab 3 = 2 ∧ c'.lab 4 = 0 := by
  refine ⟨((c.shift 3).relabel).relabel, by simp only [rawCost_relabel, rawCost_relabel, rawCost_shift], ?_, ?_, ?_, ?_, ?_⟩
  · show c.lab (0 + 3) + 1 + 1 = 0
    rw [show (0 : ℤ) + 3 = 3 by norm_num, h3] <;> rfl
  · show c.lab (1 + 3) + 1 + 1 = 1
    rw [show (1 : ℤ) + 3 = 4 by norm_num, h4] <;> rfl
  · show c.lab (2 + 3) + 1 + 1 = 0
    rw [show (2 : ℤ) + 3 = 0 + ((5 : ℕ) : ℤ) by norm_num, c.lab_add, h0] <;> rfl
  · show c.lab (3 + 3) + 1 + 1 = 2
    rw [show (3 : ℤ) + 3 = 1 + ((5 : ℕ) : ℤ) by norm_num, c.lab_add, h1] <;> rfl
  · show c.lab (4 + 3) + 1 + 1 = 0
    rw [show (4 : ℤ) + 3 = 2 + ((5 : ℕ) : ℤ) by norm_num, c.lab_add, h2] <;> rfl

private lemma tm_rot_01202 (c : Cycle 5) (h0 : c.lab 0 = 0) (h1 : c.lab 1 = 1)
    (h2 : c.lab 2 = 2) (h3 : c.lab 3 = 0) (h4 : c.lab 4 = 2) :
    ∃ c' : Cycle 5, c'.rawCost = c.rawCost ∧ c'.lab 0 = 0 ∧ c'.lab 1 = 1 ∧ c'.lab 2 = 0 ∧
      c'.lab 3 = 2 ∧ c'.lab 4 = 0 := by
  refine ⟨(c.shift 2).relabel, by simp only [rawCost_relabel, rawCost_shift], ?_, ?_, ?_, ?_, ?_⟩
  · show c.lab (0 + 2) + 1 = 0
    rw [show (0 : ℤ) + 2 = 2 by norm_num, h2] <;> rfl
  · show c.lab (1 + 2) + 1 = 1
    rw [show (1 : ℤ) + 2 = 3 by norm_num, h3] <;> rfl
  · show c.lab (2 + 2) + 1 = 0
    rw [show (2 : ℤ) + 2 = 4 by norm_num, h4] <;> rfl
  · show c.lab (3 + 2) + 1 = 2
    rw [show (3 : ℤ) + 2 = 0 + ((5 : ℕ) : ℤ) by norm_num, c.lab_add, h0] <;> rfl
  · show c.lab (4 + 2) + 1 = 0
    rw [show (4 : ℤ) + 2 = 1 + ((5 : ℕ) : ℤ) by norm_num, c.lab_add, h1] <;> rfl

private lemma tm_rot_01210 (c : Cycle 5) (h0 : c.lab 0 = 0) (h1 : c.lab 1 = 1)
    (h2 : c.lab 2 = 2) (h3 : c.lab 3 = 1) (h4 : c.lab 4 = 0) :
    ∃ c' : Cycle 5, c'.rawCost = c.rawCost ∧ c'.lab 0 = 0 ∧ c'.lab 1 = 1 ∧ c'.lab 2 = 0 ∧
      c'.lab 3 = 2 ∧ c'.lab 4 = 0 := by
  refine ⟨((c.shift 1).relabel).relabel, by simp only [rawCost_relabel, rawCost_relabel, rawCost_shift], ?_, ?_, ?_, ?_, ?_⟩
  · show c.lab (0 + 1) + 1 + 1 = 0
    rw [show (0 : ℤ) + 1 = 1 by norm_num, h1] <;> rfl
  · show c.lab (1 + 1) + 1 + 1 = 1
    rw [show (1 : ℤ) + 1 = 2 by norm_num, h2] <;> rfl
  · show c.lab (2 + 1) + 1 + 1 = 0
    rw [show (2 : ℤ) + 1 = 3 by norm_num, h3] <;> rfl
  · show c.lab (3 + 1) + 1 + 1 = 2
    rw [show (3 : ℤ) + 1 = 4 by norm_num, h4] <;> rfl
  · show c.lab (4 + 1) + 1 + 1 = 0
    rw [show (4 : ℤ) + 1 = 0 + ((5 : ℕ) : ℤ) by norm_num, c.lab_add, h0] <;> rfl

private lemma tm_closure_zero_1 (c : Cycle 1) :
    triFactor (c.lab 0) (c.q 0) = triR := by
  have h := c.closure 0
  simp only [List.range_succ, List.range_zero, List.map_append, List.map_cons, List.map_nil,
    List.prod_append, List.prod_cons, List.prod_nil, Matrix.mul_one, List.nil_append] at h
  simpa [Matrix.mul_assoc] using h

private lemma tm_closure_zero_2 (c : Cycle 2) :
    triFactor (c.lab 0) (c.q 0) * triFactor (c.lab 1) (c.q 1) = triR := by
  have h := c.closure 0
  simp only [List.range_succ, List.range_zero, List.map_append, List.map_cons, List.map_nil,
    List.prod_append, List.prod_cons, List.prod_nil, Matrix.mul_one, List.nil_append] at h
  simpa [Matrix.mul_assoc] using h

private lemma tm_closure_zero_3 (c : Cycle 3) :
    triFactor (c.lab 0) (c.q 0) * (triFactor (c.lab 1) (c.q 1) * triFactor (c.lab 2) (c.q 2)) = triR := by
  have h := c.closure 0
  simp only [List.range_succ, List.range_zero, List.map_append, List.map_cons, List.map_nil,
    List.prod_append, List.prod_cons, List.prod_nil, Matrix.mul_one, List.nil_append] at h
  simpa [Matrix.mul_assoc] using h

private lemma tm_closure_zero_4 (c : Cycle 4) :
    triFactor (c.lab 0) (c.q 0) * (triFactor (c.lab 1) (c.q 1) * (triFactor (c.lab 2) (c.q 2) * triFactor (c.lab 3) (c.q 3))) = triR := by
  have h := c.closure 0
  simp only [List.range_succ, List.range_zero, List.map_append, List.map_cons, List.map_nil,
    List.prod_append, List.prod_cons, List.prod_nil, Matrix.mul_one, List.nil_append] at h
  simpa [Matrix.mul_assoc] using h

/-- The label increments are `N`-periodic. -/
theorem incr_emod (c : Cycle N) (hN : 0 < N) (k : ℤ) :
    c.lab (k + 1) - c.lab k = c.lab (k % N + 1) - c.lab (k % N) := by
  have hper : Function.Periodic (fun k : ℤ ↦ c.lab (k + 1) - c.lab k) (N : ℤ) := by
    intro k
    simp only [show k + N + 1 = k + 1 + N by ring, c.lab_add]
    abel
  have := hper.sub_int_mul_eq (x := k) (k / N)
  rw [show k % (N : ℤ) = k - ((k / N : ℤ) : ℤ) * N by rw [Int.emod_def]; push_cast; ring]
  exact this.symm

/-- A label increment that holds on one period holds everywhere. -/
theorem lab_succ_of_window (c : Cycle N) (hN : 0 < N) (δ : Fin 3)
    (h : ∀ j : ℕ, j < N → c.lab (j + 1) = c.lab j + δ) (k : ℤ) : c.lab (k + 1) = c.lab k + δ := by
  have hN' : (0 : ℤ) < N := by exact_mod_cast hN
  have h0 := Int.emod_nonneg k hN'.ne'
  have h1 := Int.emod_lt_of_pos k hN'
  have hr := h (k % N).toNat (by omega)
  rw [Int.toNat_of_nonneg h0] at hr
  have := c.incr_emod hN k
  rw [hr, add_sub_cancel_left] at this
  rw [← this]; abel

theorem cycle_one_false (c : Cycle 1) : False := by
  obtain ⟨c0, h0, -, -⟩ := exists_relabel_zero c
  have hcl := tm_closure_zero_1 c0
  rw [h0] at hcl
  exact word_0_false (c0.one_lt_q 0) hcl

theorem cycle_two_false (c : Cycle 2) : False := by
  obtain ⟨c0, h0, -, -⟩ := exists_relabel_zero c
  have hcl := tm_closure_zero_2 c0
  have n0 : c0.lab 1 ≠ c0.lab 0 := by simpa using c0.lab_ne 0
  have n1 : c0.lab 2 ≠ c0.lab 1 := by simpa using c0.lab_ne 1
  have l2 : c0.lab 2 = 1 := by simpa [h0] using c0.lab_add 0
  rw [h0] at hcl n0
  rw [l2] at n1
  rcases tm_fin3 (c0.lab 1) with h1 | h1 | h1 <;> rw [h1] at hcl n0 n1 <;>
    first | exact absurd rfl n0 | exact absurd rfl n1 |
      exact word_02_false (c0.one_lt_q 0) (c0.one_lt_q 1) hcl

theorem cycle_three_false (c : Cycle 3) : False := by
  obtain ⟨c0, h0, -, -⟩ := exists_relabel_zero c
  have hcl := tm_closure_zero_3 c0
  have n0 : c0.lab 1 ≠ c0.lab 0 := by simpa using c0.lab_ne 0
  have n1 : c0.lab 2 ≠ c0.lab 1 := by simpa using c0.lab_ne 1
  have n2 : c0.lab 3 ≠ c0.lab 2 := by simpa using c0.lab_ne 2
  have l3 : c0.lab 3 = 1 := by simpa [h0] using c0.lab_add 0
  rw [h0] at hcl n0
  rw [l3] at n2
  have q := c0.one_lt_q
  rcases tm_fin3 (c0.lab 1) with h1 | h1 | h1 <;> rcases tm_fin3 (c0.lab 2) with h2 | h2 | h2 <;>
    rw [h1, h2] at hcl <;> rw [h1] at n0 n1 <;> rw [h2] at n1 n2 <;>
    first | exact absurd rfl n0 | exact absurd rfl n1 | exact absurd rfl n2 |
      exact word_012_false (q 0) (q 1) (q 2) hcl | exact word_010_false (q 0) (q 1) (q 2) hcl |
      exact word_020_false (q 0) (q 1) (q 2) hcl

/-- **Four pieces are all forward.** -/
theorem cycle_four_forward (c : Cycle 4) (k : ℤ) : c.lab (k + 1) = c.lab k + 1 := by
  obtain ⟨c0, h0, -, s, hs⟩ := exists_relabel_zero c
  suffices H : ∀ k, c0.lab (k + 1) = c0.lab k + 1 by
    have := H k
    rw [(hs (k + 1)).1, (hs k).1, show c.lab k + s + 1 = c.lab k + 1 + s by abel] at this
    exact add_right_cancel this
  refine c0.lab_succ_of_window (by norm_num) 1 ?_
  have hcl := tm_closure_zero_4 c0
  have n0 : c0.lab 1 ≠ c0.lab 0 := by simpa using c0.lab_ne 0
  have n1 : c0.lab 2 ≠ c0.lab 1 := by simpa using c0.lab_ne 1
  have n2 : c0.lab 3 ≠ c0.lab 2 := by simpa using c0.lab_ne 2
  have n3 : c0.lab 4 ≠ c0.lab 3 := by simpa using c0.lab_ne 3
  have l4 : c0.lab 4 = 1 := by simpa [h0] using c0.lab_add 0
  have q := c0.one_lt_q
  intro j hj
  rcases tm_fin3 (c0.lab 1) with h1 | h1 | h1
  · exact (n0 (by rw [h1, h0])).elim
  · rcases tm_fin3 (c0.lab 2) with h2 | h2 | h2
    · rcases tm_fin3 (c0.lab 3) with h3 | h3 | h3
      · exact (n2 (by rw [h3, h2])).elim
      · exact (n3 (by rw [l4, h3])).elim
      · rw [h0, h1, h2, h3] at hcl
        exact (word_0102_false (q 0) (q 1) (q 2) (q 3) hcl).elim
    · exact (n1 (by rw [h2, h1])).elim
    · rcases tm_fin3 (c0.lab 3) with h3 | h3 | h3
      · interval_cases j <;> simp [h0, h1, h2, h3, l4] <;> rfl
      · exact (n3 (by rw [l4, h3])).elim
      · exact (n2 (by rw [h3, h2])).elim
  · rcases tm_fin3 (c0.lab 2) with h2 | h2 | h2
    · rcases tm_fin3 (c0.lab 3) with h3 | h3 | h3
      · exact (n2 (by rw [h3, h2])).elim
      · exact (n3 (by rw [l4, h3])).elim
      · rw [h0, h1, h2, h3] at hcl
        exact (word_0202_false (q 0) (q 1) (q 2) (q 3) hcl).elim
    · rcases tm_fin3 (c0.lab 3) with h3 | h3 | h3
      · rw [h0, h1, h2, h3] at hcl
        exact (word_0210_false (q 0) (q 1) (q 2) (q 3) hcl).elim
      · exact (n2 (by rw [h3, h2])).elim
      · rw [h0, h1, h2, h3] at hcl
        exact (word_0212_false (q 0) (q 1) (q 2) (q 3) hcl).elim
    · exact (n1 (by rw [h2, h1])).elim

/-- **Five pieces**: the period is entirely reverse, or a rebasing and relabeling of it has the
word `0 1 0 2 0`. -/
theorem cycle_five (c : Cycle 5) :
    (∀ k, c.lab (k + 1) = c.lab k - 1) ∨
      ∃ c' : Cycle 5, c'.rawCost = c.rawCost ∧ c'.lab 0 = 0 ∧ c'.lab 1 = 1 ∧ c'.lab 2 = 0 ∧
        c'.lab 3 = 2 ∧ c'.lab 4 = 0 := by
  obtain ⟨c0, h0, hcost, s, hs⟩ := exists_relabel_zero c
  have hcl := tm_closure_zero_five c0
  have n0 : c0.lab 1 ≠ c0.lab 0 := by simpa using c0.lab_ne 0
  have n1 : c0.lab 2 ≠ c0.lab 1 := by simpa using c0.lab_ne 1
  have n2 : c0.lab 3 ≠ c0.lab 2 := by simpa using c0.lab_ne 2
  have n3 : c0.lab 4 ≠ c0.lab 3 := by simpa using c0.lab_ne 3
  have n4 : c0.lab 5 ≠ c0.lab 4 := by simpa using c0.lab_ne 4
  have l5 : c0.lab 5 = 1 := by simpa [h0] using c0.lab_add 0
  have hrev : (∀ j : ℕ, j < 5 → c0.lab (j + 1) = c0.lab j + 2) →
      ∀ k, c.lab (k + 1) = c.lab k - 1 := by
    intro hw k
    have := c0.lab_succ_of_window (by norm_num) 2 hw k
    rw [(hs (k + 1)).1, (hs k).1, show c.lab k + s + 2 = c.lab k + 2 + s by abel] at this
    rw [add_right_cancel this]; abel_nf; rfl
  have hfwd : (∃ c' : Cycle 5, c'.rawCost = c0.rawCost ∧ c'.lab 0 = 0 ∧ c'.lab 1 = 1 ∧
      c'.lab 2 = 0 ∧ c'.lab 3 = 2 ∧ c'.lab 4 = 0) →
      (∀ k, c.lab (k + 1) = c.lab k - 1) ∨
        ∃ c' : Cycle 5, c'.rawCost = c.rawCost ∧ c'.lab 0 = 0 ∧ c'.lab 1 = 1 ∧ c'.lab 2 = 0 ∧
          c'.lab 3 = 2 ∧ c'.lab 4 = 0 := fun ⟨c', h1, h2⟩ ↦
    Or.inr ⟨c', h1.trans hcost, h2⟩
  have q := c0.one_lt_q
  rcases tm_fin3 (c0.lab 1) with h1 | h1 | h1
  · exact (n0 (by rw [h1, h0])).elim
  · rcases tm_fin3 (c0.lab 2) with h2 | h2 | h2
    · rcases tm_fin3 (c0.lab 3) with h3 | h3 | h3
      · exact (n2 (by rw [h3, h2])).elim
      · rcases tm_fin3 (c0.lab 4) with h4 | h4 | h4
        · rw [h0, h1, h2, h3, h4] at hcl
          exact (word_01010_false (q 0) (q 1) (q 2) (q 3) (q 4) hcl).elim
        · exact (n3 (by rw [h4, h3])).elim
        · rw [h0, h1, h2, h3, h4] at hcl
          exact (word_01012_false (q 0) (q 1) (q 2) (q 3) (q 4) hcl).elim
      · rcases tm_fin3 (c0.lab 4) with h4 | h4 | h4
        · exact hfwd (tm_rot_01020 c0 h0 h1 h2 h3 h4)
        · exact (n4 (by rw [l5, h4])).elim
        · exact (n3 (by rw [h4, h3])).elim
    · exact (n1 (by rw [h2, h1])).elim
    · rcases tm_fin3 (c0.lab 3) with h3 | h3 | h3
      · rcases tm_fin3 (c0.lab 4) with h4 | h4 | h4
        · exact (n3 (by rw [h4, h3])).elim
        · exact (n4 (by rw [l5, h4])).elim
        · exact hfwd (tm_rot_01202 c0 h0 h1 h2 h3 h4)
      · rcases tm_fin3 (c0.lab 4) with h4 | h4 | h4
        · exact hfwd (tm_rot_01210 c0 h0 h1 h2 h3 h4)
        · exact (n3 (by rw [h4, h3])).elim
        · rw [h0, h1, h2, h3, h4] at hcl
          exact (word_01212_false (q 0) (q 1) (q 2) (q 3) (q 4) hcl).elim
      · exact (n2 (by rw [h3, h2])).elim
  · rcases tm_fin3 (c0.lab 2) with h2 | h2 | h2
    · rcases tm_fin3 (c0.lab 3) with h3 | h3 | h3
      · exact (n2 (by rw [h3, h2])).elim
      · rcases tm_fin3 (c0.lab 4) with h4 | h4 | h4
        · rw [h0, h1, h2, h3, h4] at hcl
          exact (word_02010_false (q 0) (q 1) (q 2) (q 3) (q 4) hcl).elim
        · exact (n3 (by rw [h4, h3])).elim
        · exact hfwd (tm_rot_02012 c0 h0 h1 h2 h3 h4)
      · rcases tm_fin3 (c0.lab 4) with h4 | h4 | h4
        · rw [h0, h1, h2, h3, h4] at hcl
          exact (word_02020_false (q 0) (q 1) (q 2) (q 3) (q 4) hcl).elim
        · exact (n4 (by rw [l5, h4])).elim
        · exact (n3 (by rw [h4, h3])).elim
    · rcases tm_fin3 (c0.lab 3) with h3 | h3 | h3
      · rcases tm_fin3 (c0.lab 4) with h4 | h4 | h4
        · exact (n3 (by rw [h4, h3])).elim
        · exact (n4 (by rw [l5, h4])).elim
        · exact Or.inl (hrev fun j hj ↦ by interval_cases j <;> simp [h0, h1, h2, h3, h4, l5] <;> rfl)
      · exact (n2 (by rw [h3, h2])).elim
      · rcases tm_fin3 (c0.lab 4) with h4 | h4 | h4
        · exact hfwd (tm_rot_02120 c0 h0 h1 h2 h3 h4)
        · exact (n4 (by rw [l5, h4])).elim
        · exact (n3 (by rw [h4, h3])).elim
    · exact (n1 (by rw [h2, h1])).elim

end Cycle

end Term
end SmoothedOctagon
