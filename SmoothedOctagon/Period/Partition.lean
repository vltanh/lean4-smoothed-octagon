module

public import SmoothedOctagon.Period.Defs

/-!
# The five classes of switch-sign sequences

Every switch of a vertex representation is forward or reverse, because neighbouring labels differ
and labels live in `ℤ/3`. Hence the cyclic sign sequence of a period is entirely reverse (class R),
entirely forward (class F), or mixed; a mixed sequence has a maximal reverse run of length other
than two (M3), or all its reverse runs have length two and then either all its forward runs have
length one (M1) or one has length at least two (M2). The proof of the main theorem excludes each
class for minimizing periods with at least six pieces.
-/

@[expose] public section

namespace SmoothedOctagon

namespace VertexRepresentation

variable {T : ℝ} {u : ℝ → Fin 3 → ℝ} (ρ : VertexRepresentation T u)

lemma fin3_eq_add_one_or_sub_one {a b : Fin 3} (h : b ≠ a) : b = a + 1 ∨ b = a - 1 := by
  revert a b; decide

/-- Every switch is forward or reverse. -/
theorem isForward_or_isReverse (k : ℤ) : ρ.IsForward k ∨ ρ.IsReverse k :=
  fin3_eq_add_one_or_sub_one (ρ.label_ne k)

/-- No switch is both forward and reverse. -/
theorem not_isForward_and_isReverse (k : ℤ) : ¬ (ρ.IsForward k ∧ ρ.IsReverse k) := by
  rintro ⟨hf, hr⟩
  unfold IsForward at hf
  unfold IsReverse at hr
  rw [hf] at hr
  generalize ρ.label k = a at hr
  revert a hr; decide

/-- **The sign partition.** The cyclic sign sequence of a vertex representation is in class R, F,
M3, M1 or M2. -/
theorem partition : ρ.AllReverse ∨ ρ.AllForward ∨ ρ.ClassM3 ∨ ρ.ClassM1 ∨ ρ.ClassM2 := by
  by_cases hR : ρ.AllReverse
  · exact Or.inl hR
  by_cases hF : ρ.AllForward
  · exact Or.inr (Or.inl hF)
  have hmix : ρ.IsMixed := by
    refine ⟨?_, ?_⟩
    · obtain ⟨k, hk⟩ := not_forall.mp hR
      exact ⟨k, (ρ.isForward_or_isReverse k).resolve_right hk⟩
    · obtain ⟨k, hk⟩ := not_forall.mp hF
      exact ⟨k, (ρ.isForward_or_isReverse k).resolve_left hk⟩
  right; right
  by_cases h3 : ∃ k L, ρ.IsReverseRun k L ∧ L ≠ 2
  · exact Or.inl ⟨hmix, h3⟩
  have hrev : ∀ k L, ρ.IsReverseRun k L → L = 2 := by
    intro k L hkL
    by_contra hL
    exact h3 ⟨k, L, hkL, hL⟩
  right
  by_cases h1 : ∀ k L, ρ.IsForwardRun k L → L = 1
  · exact Or.inl ⟨hmix, hrev, h1⟩
  · right
    push Not at h1
    obtain ⟨k, L, hkL, hL⟩ := h1
    exact ⟨hmix, hrev, k, L, hkL, by have := hkL.1; omega⟩

end VertexRepresentation

end SmoothedOctagon
