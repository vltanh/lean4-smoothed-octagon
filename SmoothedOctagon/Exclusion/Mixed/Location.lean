module

public import SmoothedOctagon.Exclusion.Mixed.Centre
public import SmoothedOctagon.Exclusion.Mixed.SmallForwardMinimum

/-!
# Case M2: the global active-margin minimum is a reverse centre

`MIXED_GLOBAL_NONSHORT_PERIOD_EXCLUSION` §2 (inventory E2, entry 30). Take a global minimum `m` of
the (periodic) active margins of a competitive M2 period with at least six pieces. At a turn the
three-arc log-concavity (`CostateCycle.three_arc_not_min`) excludes it. If both incident switches
are forward, the strict centre minimum of the neighbouring reverse runs
(`reverseRun_two_and_centre_min`) forces four consecutive forward switches; some reverse centre has
`a² < 12/17` (`m2_centre`, `m2_scale`), so `a_m² ≤ 4/3` and the small-forward-minimum theorem
(`m2_small_forward_minimum`) excludes this pattern. Hence both incident switches are reverse, and
(reverse runs having two switches) `m` is the centre of a reverse run.

Route: the "phase/scale bound `a² < 4/3`" is replaced by the reverse-centre scale bound
`a² < 12/17`, which holds at every reverse centre (`MIXED_REVERSE_CENTRE_SCALE_BOUND`).

## Main API

* `m2_fwd_or_rev`, `m2_fwd_add_N`: switch signs.
* `m2_exists_reverseRun`: every reverse switch of a mixed representation lies in a maximal run.
* `m2_min_centre`: the global minimum is a reverse centre.
-/

@[expose] public section

namespace SmoothedOctagon

namespace VertexRepresentation

variable {T : ℝ} {u : ℝ → Fin 3 → ℝ} (ρ : VertexRepresentation T u)

/-- The switch signs are `N`-periodic. -/
theorem m2_fwd_add_N (k : ℤ) : ρ.IsForward (k + ρ.N) ↔ ρ.IsForward k := by
  unfold IsForward
  rw [show k + ρ.N + 1 = k + 1 + ρ.N by ring, ρ.label_add_period, ρ.label_add_period]
  constructor
  · intro h; have := congrArg (· - 1) h; simpa using this
  · intro h; rw [h]

theorem m2_fwd_sub_mul_N (k : ℤ) (n : ℕ) : ρ.IsForward (k - n * ρ.N) ↔ ρ.IsForward k := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [← ih, ← ρ.m2_fwd_add_N (k - (n + 1 : ℕ) * ρ.N),
      show k - ((n + 1 : ℕ) : ℤ) * ρ.N + ρ.N = k - (n : ℤ) * ρ.N by push_cast; ring]

theorem m2_fwd_add_mul_N (k : ℤ) (n : ℕ) : ρ.IsForward (k + n * ρ.N) ↔ ρ.IsForward k := by
  rw [← ρ.m2_fwd_sub_mul_N (k + n * ρ.N) n, add_sub_cancel_right]

/-- **Maximal reverse runs exist**: in a representation with some forward switch, every reverse
switch `j` lies in a maximal reverse run `k, …, k + L - 1`. -/
theorem m2_exists_reverseRun {f j : ℤ} (hf : ρ.IsForward f) (hj : ρ.IsReverse j) :
    ∃ k : ℤ, ∃ L : ℕ, ρ.IsReverseRun k L ∧ k ≤ j ∧ j < k + L := by
  have hN : (1 : ℤ) ≤ ρ.N := by exact_mod_cast ρ.N_pos
  have hjf : ¬ ρ.IsForward j := (ρ.m2_rev_iff_not_fwd j).1 hj
  -- a forward switch below `j` and one above `j`
  set n : ℕ := (f - j).toNat + (j - f).toNat + 1 with hn
  have hbelow : f - n * ρ.N < j := by
    have : (n : ℤ) ≤ n * ρ.N := le_mul_of_one_le_right (by positivity) hN
    have : f - j < n := by rw [hn]; push_cast; omega
    linarith
  have habove : j < f + n * ρ.N := by
    have : (n : ℤ) ≤ n * ρ.N := le_mul_of_one_le_right (by positivity) hN
    have : j - f < n := by rw [hn]; push_cast; omega
    linarith
  obtain ⟨k0, ⟨hk0j, hk0f⟩, hk0max⟩ := Int.exists_greatest_of_bdd
    (P := fun i => i < j ∧ ρ.IsForward i) ⟨j, fun z hz => hz.1.le⟩
    ⟨f - n * ρ.N, hbelow, (ρ.m2_fwd_sub_mul_N f n).2 hf⟩
  obtain ⟨k1, ⟨hk1j, hk1f⟩, hk1min⟩ := Int.exists_least_of_bdd
    (P := fun i => j < i ∧ ρ.IsForward i) ⟨j, fun z hz => hz.1.le⟩
    ⟨f + n * ρ.N, habove, (ρ.m2_fwd_add_mul_N f n).2 hf⟩
  refine ⟨k0 + 1, (k1 - k0 - 1).toNat, ⟨?_, ?_, ?_, fun i hi1 hi2 => ?_⟩, by omega, by omega⟩
  · omega
  · rwa [add_sub_cancel_right]
  · rwa [show k0 + 1 + ((k1 - k0 - 1).toNat : ℤ) = k1 by omega]
  · rw [ρ.m2_rev_iff_not_fwd]
    intro hif
    rcases lt_trichotomy i j with h | h | h
    · have := hk0max i ⟨h, hif⟩; omega
    · exact hjf (h ▸ hif)
    · have := hk1min i ⟨h, hif⟩; omega

end VertexRepresentation

/-- **The global minimum is a reverse centre** (`MIXED_GLOBAL_NONSHORT_PERIOD_EXCLUSION` §2). -/
theorem m2_min_centre (P : NormalPeriod) (hc : P.IsCompetitive) (h : P.rep.ClassM2)
    (hN : 6 ≤ P.N) :
    ∃ m : ℤ, (∀ k, P.costateCycle.act m ≤ P.costateCycle.act k) ∧
      P.costateCycle.m2Fwd (m - 2) ∧ ¬ P.costateCycle.m2Fwd (m - 1) ∧
      ¬ P.costateCycle.m2Fwd m ∧ P.costateCycle.m2Fwd (m + 1) := by
  set C := P.costateCycle with hC
  obtain ⟨K⟩ := P.m2_calculus
  obtain ⟨hmix, hrev2, -⟩ := h
  obtain ⟨⟨f, hf⟩, ⟨j0, hj0⟩⟩ := hmix
  have hmix' : P.rep.IsMixed := ⟨⟨f, hf⟩, ⟨j0, hj0⟩⟩
  have fwd_iff : ∀ i, C.m2Fwd i ↔ P.rep.IsForward i := fun i => Iff.rfl
  have rev_iff : ∀ i, ¬ C.m2Fwd i ↔ P.rep.IsReverse i := fun i =>
    (P.rep.m2_rev_iff_not_fwd i).symm
  -- the maximal reverse run through a reverse switch has two switches
  have run2 : ∀ i, ¬ C.m2Fwd i → ∃ k, P.rep.IsReverseRun k 2 ∧ k ≤ i ∧ i < k + 2 := by
    intro i hi
    obtain ⟨k, L, hrun, h1, h2⟩ := P.rep.m2_exists_reverseRun hf ((rev_iff i).1 hi)
    have hL := hrev2 k L hrun
    subst hL
    exact ⟨k, hrun, h1, by exact_mod_cast h2⟩
  obtain ⟨m, hm⟩ := C.exists_act_min P.rep.N_pos
  have hact : ∀ i, C.act i = P.activeMargin i := fun i => P.costateCycle_m_lab i
  refine ⟨m, hm, ?_⟩
  by_cases h1 : C.m2Fwd (m - 1) <;> by_cases h0 : C.m2Fwd m
  · -- both incident switches forward: four forward switches, excluded
    exfalso
    have h3 : C.m2Fwd (m + 1) := by
      by_contra h3
      obtain ⟨k, hrun, hk1, hk2⟩ := run2 _ h3
      have hk : k = m + 1 := by
        by_contra hne
        have : P.rep.IsReverse m := hrun.2.2.2 m (by omega) (by push_cast; omega)
        exact (rev_iff m).2 this h0
      subst hk
      have := (reverseRun_two_and_centre_min P hmix' hrun).2.1
      rw [← hact, ← hact, show m + 1 + 1 = m + 2 by ring, show m + 1 - 1 = m by ring] at this
      linarith [hm (m + 2)]
    have h2 : C.m2Fwd (m - 2) := by
      by_contra h2
      obtain ⟨k, hrun, hk1, hk2⟩ := run2 _ h2
      have hk : k = m - 3 := by
        by_contra hne
        have : P.rep.IsReverse (m - 1) := hrun.2.2.2 (m - 1) (by omega) (by push_cast; omega)
        exact (rev_iff _).2 this h1
      subst hk
      have := (reverseRun_two_and_centre_min P hmix' hrun).2.2.2.2
      rw [← hact, ← hact, show m - 3 + 1 = m - 2 by ring, show m - 3 + 3 = m by ring] at this
      linarith [hm (m - 2)]
    -- some reverse centre has `a² < 12/17`
    have hj0' : ¬ C.m2Fwd j0 := (rev_iff j0).2 hj0
    obtain ⟨k, hrun, -, -⟩ := run2 _ hj0'
    obtain ⟨-, hfk, hfk2, hrk⟩ := hrun
    have hk0 : ¬ C.m2Fwd k := (rev_iff k).2 (hrk k le_rfl (by push_cast; omega))
    have hk1 : ¬ C.m2Fwd (k + 1) := (rev_iff _).2 (hrk (k + 1) (by omega) (by push_cast; omega))
    obtain ⟨D, -, -, hDa, -, -, hDΓ⟩ := m2_centre P K hmix'
      (k := k + 1) (by rw [show k + 1 - 2 = k - 1 by ring]; exact hfk)
      (by rw [show k + 1 - 1 = k by ring]; exact hk0) hk1
      (by rw [show k + 1 + 1 = k + ((2 : ℕ) : ℤ) by push_cast; ring]; exact hfk2)
    have hsc := m2_scale D (by rw [hDΓ]; linarith [K.cas_lt hc])
    rw [hDa] at hsc
    have hpos := C.act_pos m
    have hle := hm (k + 1)
    have hsq : C.act m ^ 2 ≤ 4 / 3 := by nlinarith
    exact m2_small_forward_minimum P K (by omega) h2 h1 h0 h3 (fun j _ _ => hm j) hsq
  · -- a turn `+ -`: three-arc log-concavity
    exfalso
    have hlab : C.lab (m - 1 + 2) = C.lab (m - 1) := by
      have e1 : C.lab m = C.lab (m - 1) + 1 := by
        have := h1; unfold CostateCycle.m2Fwd at this; rwa [sub_add_cancel] at this
      have e2 : C.lab (m + 1) = C.lab m - 1 := (rev_iff m).1 h0
      rw [show m - 1 + 2 = m + 1 by ring, e2, e1, add_sub_cancel_right]
    refine C.three_arc_not_min (m - 1) hlab ⟨?_, ?_⟩
    · rw [show m - 1 + 1 = m by ring]; exact hm _
    · rw [show m - 1 + 1 = m by ring]; exact hm _
  · -- a turn `- +`
    exfalso
    have hlab : C.lab (m - 1 + 2) = C.lab (m - 1) := by
      have e1 : C.lab m = C.lab (m - 1) - 1 := by
        have := (rev_iff (m - 1)).1 h1
        unfold VertexRepresentation.IsReverse at this; rwa [sub_add_cancel] at this
      have e2 : C.lab (m + 1) = C.lab m + 1 := h0
      rw [show m - 1 + 2 = m + 1 by ring, e2, e1, sub_add_cancel]
    refine C.three_arc_not_min (m - 1) hlab ⟨?_, ?_⟩
    · rw [show m - 1 + 1 = m by ring]; exact hm _
    · rw [show m - 1 + 1 = m by ring]; exact hm _
  · -- both reverse: the centre of a run of two
    obtain ⟨k, hrun, hk1, hk2⟩ := run2 _ h1
    have hk : k = m - 1 := by
      by_contra hne
      have hk' : k = m - 2 := by omega
      subst hk'
      exact h0 (by have := hrun.2.2.1; rwa [show m - 2 + ((2 : ℕ) : ℤ) = m by push_cast; ring]
        at this)
    subst hk
    obtain ⟨-, hfk, hfk2, -⟩ := hrun
    refine ⟨?_, h1, h0, ?_⟩
    · rw [show m - 2 = m - 1 - 1 by ring]; exact hfk
    · rw [show m + 1 = m - 1 + ((2 : ℕ) : ℤ) by push_cast; ring]; exact hfk2

end SmoothedOctagon
