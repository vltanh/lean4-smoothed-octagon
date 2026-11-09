module

public import SmoothedOctagon.Exclusion.Mixed.Frames

/-!
# Case M2: one-arc transports of the multiplier, entry by entry

The transport `M (i + 1) = A_i⁻¹ (M i) A_i` of the covector calculus, with `A_i = T₀(q) R⁻¹` after
a forward switch and `A_i = T₀(q) R` after a reverse one (triangular `R = [[0, 1], [-1, 1]]`),
written out entry by entry.

## Main API

* `CostateCycle.extr_m2A_fwd`, `extr_m2A_rev`, `extr_m2A_inv_fwd`, `extr_m2A_inv_rev`: `A_i` and `A_i⁻¹`.
* `CostateCycle.extr_next_fwd`, `extr_next_rev`: the entries of `M (i + 1)` in terms of those of `M i`
  and `q = q_i`.
-/

@[expose] public section

namespace SmoothedOctagon

open SmoothedPolygons

namespace CostateCycle

variable {N : ℕ} (C : CostateCycle N)

theorem extr_m2A_fwd {i : ℤ} (h : C.m2Fwd i) :
    C.m2A i = !![C.q i, -C.q i; (C.q i)⁻¹, 0] := by
  have hq := (C.q_pos i).ne'
  rw [m2A]; simp only [h, ↓reduceIte]; rw [m2T0, Term.triRinv]
  ext a b; fin_cases a <;> fin_cases b <;> simp [Matrix.mul_apply, Fin.sum_univ_two]

theorem extr_m2A_rev {i : ℤ} (h : ¬ C.m2Fwd i) :
    C.m2A i = !![0, C.q i; -(C.q i)⁻¹, (C.q i)⁻¹] := by
  have hq := (C.q_pos i).ne'
  rw [m2A]; simp only [h, ↓reduceIte]; rw [m2T0, Term.triR]
  ext a b; fin_cases a <;> fin_cases b <;> simp [Matrix.mul_apply, Fin.sum_univ_two]

theorem extr_m2A_inv_fwd {i : ℤ} (h : C.m2Fwd i) :
    (C.m2A i)⁻¹ = !![0, C.q i; -(C.q i)⁻¹, C.q i] := by
  have hq := (C.q_pos i).ne'
  rw [C.extr_m2A_fwd h]
  refine Matrix.inv_eq_left_inv ?_
  ext a b; fin_cases a <;> fin_cases b <;> simp [Matrix.mul_apply, Fin.sum_univ_two, hq]

theorem extr_m2A_inv_rev {i : ℤ} (h : ¬ C.m2Fwd i) :
    (C.m2A i)⁻¹ = !![(C.q i)⁻¹, -C.q i; (C.q i)⁻¹, 0] := by
  have hq := (C.q_pos i).ne'
  rw [C.extr_m2A_rev h]
  refine Matrix.inv_eq_left_inv ?_
  ext a b; fin_cases a <;> fin_cases b <;> simp [Matrix.mul_apply, Fin.sum_univ_two, hq]

/-- **Transport across a forward switch**, entry by entry (`q = q_i`). -/
theorem extr_next_fwd {M : ℤ → Mat2} (hM : ∀ i, M (i + 1) = (C.m2A i)⁻¹ * M i * C.m2A i) {i : ℤ}
    (h : C.m2Fwd i) :
    M (i + 1) 0 0 = C.q i ^ 2 * M i 1 0 + M i 1 1 ∧
      M (i + 1) 0 1 = -(C.q i ^ 2 * M i 1 0) ∧
      M (i + 1) 1 0 = -M i 0 0 + C.q i ^ 2 * M i 1 0 - M i 0 1 / C.q i ^ 2 + M i 1 1 ∧
      M (i + 1) 1 1 = M i 0 0 - C.q i ^ 2 * M i 1 0 := by
  have hq := (C.q_pos i).ne'
  rw [hM i, C.extr_m2A_inv_fwd h, C.extr_m2A_fwd h]
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.vecMul, dotProduct] <;> field_simp <;> ring

/-- **Transport across a reverse switch**, entry by entry (`q = q_i`). -/
theorem extr_next_rev {M : ℤ → Mat2} (hM : ∀ i, M (i + 1) = (C.m2A i)⁻¹ * M i * C.m2A i) {i : ℤ}
    (h : ¬ C.m2Fwd i) :
    M (i + 1) 0 0 = M i 1 1 - M i 0 1 / C.q i ^ 2 ∧
      M (i + 1) 0 1 = M i 0 0 - C.q i ^ 2 * M i 1 0 + M i 0 1 / C.q i ^ 2 - M i 1 1 ∧
      M (i + 1) 1 0 = -(M i 0 1 / C.q i ^ 2) ∧
      M (i + 1) 1 1 = M i 0 0 + M i 0 1 / C.q i ^ 2 := by
  have hq := (C.q_pos i).ne'
  rw [hM i, C.extr_m2A_inv_rev h, C.extr_m2A_rev h]
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.vecMul, dotProduct] <;> field_simp <;> ring

end CostateCycle

end SmoothedOctagon
