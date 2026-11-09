module

public import SmoothedOctagon.Period.Defs
public import SmoothedOctagon.Exclusion.MinimumStructure.ThreeArc

/-!
# Case M3: reverse runs have exactly two switches

In a mixed normal vertex period every maximal run of reverse switches has exactly two switches, and
the active margin of its centre piece is strictly smaller than the active margins of the two pieces
on each side. The positive form is used again by cases F and M2; case M3 itself is the first half.

The proof works on the costate cycle of the period (`NormalPeriod.costateCycle`): turn feasibility
(`CostateCycle.turn_up`, `turn_down`) and three-arc log-concavity (`CostateCycle.three_arc`) exclude
a run minimum at either end of the run, and the reverse-four principle in its two interior positions
(`CostateCycle.reverse_four_third`, `reverse_four_second`) excludes it in the interior of a run with
at least three switches. The reverse-four principle and three-arc log-concavity are proved from
exact identities of the explicit costate (`Exclusion/Reverse/Four.lean`,
`Exclusion/MinimumStructure/ThreeArc.lean`). Mixedness is not used: a maximal reverse run is bounded by
forward switches by definition.
-/

@[expose] public section

namespace SmoothedOctagon

/-- **Reverse runs.** In a mixed normal vertex period, a maximal run of reverse switches
`k, …, k + L - 1` has `L = 2`, and the centre piece `k + 1` has an active margin strictly smaller
than those of the pieces `k - 1`, `k`, `k + 2` and `k + 3`. -/
theorem reverseRun_two_and_centre_min (P : NormalPeriod) (hmix : P.rep.IsMixed) {k : ℤ} {L : ℕ}
    (h : P.rep.IsReverseRun k L) :
    L = 2 ∧ P.activeMargin (k + 1) < P.activeMargin (k - 1) ∧
      P.activeMargin (k + 1) < P.activeMargin k ∧ P.activeMargin (k + 1) < P.activeMargin (k + 2) ∧
      P.activeMargin (k + 1) < P.activeMargin (k + 3) := by
  obtain ⟨-, -⟩ := hmix
  set C := P.costateCycle with hC
  have hact : ∀ j, P.activeMargin j = C.act j := fun j ↦ (P.costateCycle_m_lab j).symm
  simp only [hact]
  obtain ⟨hL1, hf0, hfL, hrev⟩ := h
  -- the switch signs, on the cycle
  have fwd : ∀ j j' j'', P.rep.IsForward j → j' = j + 1 → j'' = j →
      C.lab j' = C.lab j'' + 1 := by
    intro j j' j'' hj e e'; subst e e'; exact hj
  have rev : ∀ j j' j'', k ≤ j → j < k + L → j' = j + 1 → j'' = j →
      C.lab j' = C.lab j'' - 1 := by
    intro j j' j'' h1 h2 e e'; subst e e'; exact hrev _ h1 h2
  -- start of the run: `a_{k+1} < a_{k-1}` and `a_{k+1} < a_k`
  have hstart1 : C.act (k + 1) < C.act (k - 1) := by
    have := C.turn_down (k - 1) (fwd _ _ _ hf0 (by ring) (by ring))
      (rev k _ _ le_rfl (by omega) (by ring) (by ring))
    rwa [show k - 1 + 2 = k + 1 by ring] at this
  have hstart2 : C.act (k + 1) < C.act k := by
    by_contra hcon
    push Not at hcon
    have h3 : C.lab (k - 1 + 2) = C.lab (k - 1) := by
      rw [rev k (k - 1 + 2) k le_rfl (by omega) (by ring) rfl,
        fwd (k - 1) k (k - 1) hf0 (by ring) rfl, add_sub_cancel_right]
    refine C.three_arc_not_min (k - 1) h3 ⟨?_, ?_⟩
    · rw [show k - 1 + 1 = k by ring]; linarith
    · rw [show k - 1 + 1 = k by ring, show k - 1 + 2 = k + 1 by ring]; exact hcon
  -- end of the run: `a_{k+L-1} < a_{k+L}`
  have hend : C.act (k + L - 1) < C.act (k + L) := by
    have r1 := rev (k + L - 1) (k + L - 1 + 1) (k + L - 1) (by omega) (by omega) rfl rfl
    have f1 := fwd (k + L) (k + L - 1 + 2) (k + L) hfL (by ring) rfl
    have hup := C.turn_up (k + L - 1) r1 (by rw [f1, show k + L - 1 + 1 = k + L by ring])
    by_contra hcon
    push Not at hcon
    have r1' : C.lab (k + L) = C.lab (k + L - 1) - 1 := by
      rwa [show k + L - 1 + 1 = k + L by ring] at r1
    have h3 : C.lab (k + L - 1 + 2) = C.lab (k + L - 1) := by
      rw [f1, r1', sub_add_cancel]
    refine C.three_arc_not_min (k + L - 1) h3 ⟨?_, ?_⟩
    · rw [show k + L - 1 + 1 = k + L by ring]; exact hcon
    · rw [show k + L - 1 + 1 = k + L by ring]; linarith
  -- the length is two
  have hL : L = 2 := by
    rcases (show L = 1 ∨ L = 2 ∨ 3 ≤ L by omega) with h1 | h2 | h3
    · subst h1
      have : C.act (k + 1) < C.act k := hstart2
      rw [show k + ((1 : ℕ) : ℤ) - 1 = k by push_cast; ring,
        show k + ((1 : ℕ) : ℤ) = k + 1 by push_cast; ring] at hend
      linarith
    · exact h2
    · exfalso
      obtain ⟨m, hm, hmin⟩ := (Finset.Icc k (k + L)).exists_min_image C.act
        ⟨k, Finset.mem_Icc.2 ⟨le_rfl, by omega⟩⟩
      rw [Finset.mem_Icc] at hm
      have hmin' : ∀ x, k ≤ x → x ≤ k + L → C.act m ≤ C.act x := fun x h1 h2 ↦
        hmin x (Finset.mem_Icc.2 ⟨h1, h2⟩)
      rcases (show m = k ∨ m = k + 1 ∨ (k + 2 ≤ m ∧ m ≤ k + L - 1) ∨ m = k + L by omega) with
        hm0 | hm1 | hm2 | hm3
      · subst hm0
        have := hmin' (m + 1) (by omega) (by omega)
        linarith
      · subst hm1
        refine C.reverse_four_second k (rev k _ _ le_rfl (by omega) (by ring) (by ring))
          (rev (k + 1) _ _ (by omega) (by omega) (by ring) (by ring))
          (rev (k + 2) _ _ (by omega) (by omega) (by ring) (by ring)) ⟨?_, ?_, ?_⟩
        · exact hmin' k le_rfl (by omega)
        · exact hmin' (k + 2) (by omega) (by omega)
        · exact hmin' (k + 3) (by omega) (by omega)
      · refine C.reverse_four_third (m - 2)
          (rev (m - 2) _ _ (by omega) (by omega) (by ring) (by ring))
          (rev (m - 2 + 1) _ _ (by omega) (by omega) (by ring) (by ring))
          (rev (m - 2 + 2) _ _ (by omega) (by omega) (by ring) (by ring)) ⟨?_, ?_, ?_⟩
        · rw [show m - 2 + 2 = m by ring]; exact hmin' _ (by omega) (by omega)
        · rw [show m - 2 + 2 = m by ring]; exact hmin' _ (by omega) (by omega)
        · rw [show m - 2 + 2 = m by ring]; exact hmin' _ (by omega) (by omega)
      · subst hm3
        have := hmin' (k + L - 1) (by omega) (by omega)
        linarith
  subst hL
  push_cast at hend
  refine ⟨rfl, hstart1, hstart2, by rwa [show k + 2 - 1 = k + 1 by ring] at hend, ?_⟩
  -- exit of the run: `a_{k+1} < a_{k+3}`
  have := C.turn_up (k + 1) (rev (k + 1) _ _ (by omega) (by omega) (by ring) (by ring))
    (fwd (k + 2) _ _ hfL (by ring) (by ring))
  rwa [show k + 1 + 2 = k + 3 by ring] at this

/-- **Case M3.** No normal vertex period has mixed switch signs with a maximal reverse run of
length other than two. -/
theorem minimumStructure_exclusion (P : NormalPeriod) (h : P.rep.ClassM3) : False := by
  obtain ⟨hmix, k, L, hrun, hL⟩ := h
  exact hL (reverseRun_two_and_centre_min P hmix hrun).1

end SmoothedOctagon
