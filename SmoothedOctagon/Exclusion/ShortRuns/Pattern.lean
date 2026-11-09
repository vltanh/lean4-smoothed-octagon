module

public import SmoothedOctagon.Period.Elliptic

/-!
# Case M1: the sign pattern `(− − +)^m`

A class-M1 vertex representation (mixed, every maximal reverse run of length two, every maximal
forward run of length one) has `N = 3m` pieces with the cyclic sign word `(− − +)^m`, and the label
twist forces `m ≡ 2 (mod 3)`.

## Main API

* `m1_pattern`: for a class-M1 representation there are `k₀` and `m > 0` with `N = 3m`,
  `m % 3 = 2`, and the switches `k₀ + 3j`, `k₀ + 3j + 1` reverse, `k₀ + 3j + 2` forward.
-/

@[expose] public section

namespace SmoothedOctagon

namespace VertexRepresentation

variable {T : ℝ} {u : ℝ → Fin 3 → ℝ} (ρ : VertexRepresentation T u)

/-- A mixed representation has a forward switch followed by a reverse one. -/
theorem m1_exists_fwd_rev (hmix : ρ.IsMixed) : ∃ k, ρ.IsForward k ∧ ρ.IsReverse (k + 1) := by
  obtain ⟨⟨f, hf⟩, ⟨r, hr⟩⟩ := hmix
  by_contra hcon
  push Not at hcon
  have hall : ∀ n : ℕ, ρ.IsForward (f + n) := by
    intro n
    induction n with
    | zero => simpa using hf
    | succ n ih =>
      have := hcon _ ih
      rcases ρ.el_fwd_or_rev (f + n + 1) with h | h
      · rw [show f + ((n + 1 : ℕ) : ℤ) = f + n + 1 by push_cast; ring]; exact h
      · exact absurd h this
  have hN : (0 : ℤ) < ρ.N := by exact_mod_cast ρ.N_pos
  obtain ⟨t, ht⟩ : ∃ t : ℕ, f ≤ r + t * ρ.N := by
    refine ⟨(f - r).toNat, ?_⟩
    have h1 : (f - r) ≤ ((f - r).toNat : ℤ) := Int.self_le_toNat _
    have h2 : ((f - r).toNat : ℤ) ≤ (f - r).toNat * ρ.N := by
      have : (0 : ℤ) ≤ (f - r).toNat := by positivity
      nlinarith
    linarith
  have h1 := hall (r + t * ρ.N - f).toNat
  rw [Int.toNat_of_nonneg (by linarith), show f + (r + t * ρ.N - f) = r + t * ρ.N by ring,
    ρ.el_fwd_add_mul_N] at h1
  exact ρ.el_not_fwd_rev r ⟨h1, hr⟩

/-- **The class-M1 step.** In a class-M1 representation, a forward switch followed by a reverse
switch is followed by the pattern `− + −`. -/
theorem m1_step (h : ρ.ClassM1) {k : ℤ} (hf : ρ.IsForward k) (hr : ρ.IsReverse (k + 1)) :
    ρ.IsReverse (k + 2) ∧ ρ.IsForward (k + 3) ∧ ρ.IsReverse (k + 4) := by
  obtain ⟨-, hrev, hfwd⟩ := h
  -- the reverse run from `k + 1`
  classical
  have hex : ∃ L : ℕ, 1 ≤ L ∧ ρ.IsForward (k + 1 + L) := by
    refine ⟨ρ.N - 1, ?_, ?_⟩
    · by_contra hc
      push Not at hc
      have hN1 : ρ.N = 1 := by have := ρ.N_pos; omega
      have := (ρ.el_fwd_add_N k).2 hf
      rw [hN1, Nat.cast_one] at this
      exact ρ.el_not_fwd_rev (k + 1) ⟨this, hr⟩
    · have hN := ρ.N_pos
      rw [show k + 1 + ((ρ.N - 1 : ℕ) : ℤ) = k + ρ.N by push_cast [Nat.cast_sub hN]; ring]
      exact (ρ.el_fwd_add_N k).2 hf
  let L := Nat.find hex
  have hL : 1 ≤ L ∧ ρ.IsForward (k + 1 + L) := Nat.find_spec hex
  have hLmin : ∀ l : ℕ, 1 ≤ l → l < L → ¬ ρ.IsForward (k + 1 + l) := fun l h1 h2 h3 ↦
    Nat.find_min hex h2 ⟨h1, h3⟩
  have hrun : ρ.IsReverseRun (k + 1) L := by
    refine ⟨hL.1, by simpa using hf, hL.2, fun j hj1 hj2 ↦ ?_⟩
    rcases eq_or_lt_of_le hj1 with hj | hj
    · rw [← hj]; exact hr
    · have hl : (j - (k + 1)).toNat < L := by omega
      have := hLmin (j - (k + 1)).toNat (by omega) hl
      rw [Int.toNat_of_nonneg (by omega), show k + 1 + (j - (k + 1)) = j by ring] at this
      exact (ρ.el_fwd_or_rev j).resolve_left this
  have hL2 : L = 2 := hrev _ _ hrun
  have hr2 : ρ.IsReverse (k + 2) := hrun.2.2.2 (k + 2) (by omega) (by rw [hL2]; push_cast; omega)
  have hf3 : ρ.IsForward (k + 3) := by
    have := hrun.2.2.1; rw [hL2] at this; rw [show k + 3 = k + 1 + ((2 : ℕ) : ℤ) by push_cast; ring]
    exact this
  -- the forward run from `k + 3`
  have hex' : ∃ L : ℕ, 1 ≤ L ∧ ρ.IsReverse (k + 3 + L) := by
    refine ⟨ρ.N - 1, ?_, ?_⟩
    · by_contra hc
      push Not at hc
      have hN1 : ρ.N = 1 := by have := ρ.N_pos; omega
      have := (ρ.el_rev_add_N (k + 2)).2 hr2
      rw [hN1, Nat.cast_one, show k + 2 + 1 = k + 3 by ring] at this
      exact ρ.el_not_fwd_rev (k + 3) ⟨hf3, this⟩
    · have hN := ρ.N_pos
      rw [show k + 3 + ((ρ.N - 1 : ℕ) : ℤ) = k + 2 + ρ.N by push_cast [Nat.cast_sub hN]; ring]
      exact (ρ.el_rev_add_N (k + 2)).2 hr2
  let L' := Nat.find hex'
  have hL' : 1 ≤ L' ∧ ρ.IsReverse (k + 3 + L') := Nat.find_spec hex'
  have hLmin' : ∀ l : ℕ, 1 ≤ l → l < L' → ¬ ρ.IsReverse (k + 3 + l) := fun l h1 h2 h3 ↦
    Nat.find_min hex' h2 ⟨h1, h3⟩
  have hrun' : ρ.IsForwardRun (k + 3) L' := by
    refine ⟨hL'.1, by rw [show k + 3 - 1 = k + 2 by ring]; exact hr2, hL'.2, fun j hj1 hj2 ↦ ?_⟩
    rcases eq_or_lt_of_le hj1 with hj | hj
    · rw [← hj]; exact hf3
    · have hl : (j - (k + 3)).toNat < L' := by omega
      have := hLmin' (j - (k + 3)).toNat (by omega) hl
      rw [Int.toNat_of_nonneg (by omega), show k + 3 + (j - (k + 3)) = j by ring] at this
      exact (ρ.el_fwd_or_rev j).resolve_right this
  have hL'1 : L' = 1 := hfwd _ _ hrun'
  have hr4 : ρ.IsReverse (k + 4) := by
    have := hrun'.2.2.1; rw [hL'1] at this
    rw [show k + 4 = k + 3 + ((1 : ℕ) : ℤ) by push_cast; ring]; exact this
  exact ⟨hr2, hf3, hr4⟩

/-- **The sign pattern of class M1.** The switch word is `(− − +)^m` with `N = 3m`; each block of
three switches lowers the label by one, and the twist raises it by one over the period, so
`m ≡ 2 (mod 3)`. -/
theorem m1_pattern (h : ρ.ClassM1) :
    ∃ (k₀ : ℤ) (m : ℕ), 0 < m ∧ ρ.N = 3 * m ∧ m % 3 = 2 ∧
      ∀ j : ℤ, ρ.IsReverse (k₀ + 3 * j) ∧ ρ.IsReverse (k₀ + 3 * j + 1) ∧
        ρ.IsForward (k₀ + 3 * j + 2) := by
  obtain ⟨k₁, hf, hr⟩ := ρ.m1_exists_fwd_rev h.1
  -- forward induction
  have hfwd : ∀ n : ℕ, ρ.IsForward (k₁ + 3 * n) ∧ ρ.IsReverse (k₁ + 3 * n + 1) := by
    intro n
    induction n with
    | zero => simpa using ⟨hf, hr⟩
    | succ n ih =>
      obtain ⟨-, h3, h4⟩ := ρ.m1_step h ih.1 ih.2
      refine ⟨?_, ?_⟩
      · rw [show k₁ + 3 * ((n + 1 : ℕ) : ℤ) = k₁ + 3 * n + 3 by push_cast; ring]; exact h3
      · rw [show k₁ + 3 * ((n + 1 : ℕ) : ℤ) + 1 = k₁ + 3 * n + 4 by push_cast; ring]; exact h4
  have hpat : ∀ n : ℕ, ρ.IsForward (k₁ + 3 * n) ∧ ρ.IsReverse (k₁ + 3 * n + 1) ∧
      ρ.IsReverse (k₁ + 3 * n + 2) := fun n ↦
    ⟨(hfwd n).1, (hfwd n).2, (ρ.m1_step h (hfwd n).1 (hfwd n).2).1⟩
  -- `N` is a multiple of three
  have hN0 := ρ.N_pos
  have h3 : ρ.N % 3 = 0 := by
    have hfN := (ρ.el_fwd_add_N k₁).2 hf
    obtain ⟨q, hq⟩ : ∃ q, ρ.N = 3 * q + ρ.N % 3 := ⟨ρ.N / 3, (Nat.div_add_mod _ _).symm⟩
    rcases (show ρ.N % 3 = 0 ∨ ρ.N % 3 = 1 ∨ ρ.N % 3 = 2 by omega) with h0 | h1 | h2
    · exact h0
    · exfalso
      have := (hpat q).2.1
      rw [show k₁ + 3 * (q : ℤ) + 1 = k₁ + ρ.N by rw [hq, h1]; push_cast; ring] at this
      exact ρ.el_not_fwd_rev _ ⟨hfN, this⟩
    · exfalso
      have := (hpat q).2.2
      rw [show k₁ + 3 * (q : ℤ) + 2 = k₁ + ρ.N by rw [hq, h2]; push_cast; ring] at this
      exact ρ.el_not_fwd_rev _ ⟨hfN, this⟩
  obtain ⟨m, hm⟩ : ∃ m, ρ.N = 3 * m := ⟨ρ.N / 3, by omega⟩
  have hm0 : 0 < m := by omega
  -- the pattern for every integer
  have hall : ∀ j : ℤ, ρ.IsForward (k₁ + 3 * j) ∧ ρ.IsReverse (k₁ + 3 * j + 1) ∧
      ρ.IsReverse (k₁ + 3 * j + 2) := by
    intro j
    obtain ⟨t, n, ht⟩ : ∃ (t : ℤ) (n : ℕ), j = n - t * m := by
      refine ⟨j.natAbs, (j + j.natAbs * m).toNat, ?_⟩
      have : 0 ≤ j + j.natAbs * m := by
        have : (j.natAbs : ℤ) ≤ j.natAbs * m := by
          have : (1 : ℤ) ≤ m := by exact_mod_cast hm0
          nlinarith [abs_nonneg j]
        have := Int.natAbs_eq j
        rcases this with h | h <;> omega
      rw [Int.toNat_of_nonneg this]; ring
    subst ht
    have hNm : (ρ.N : ℤ) = 3 * m := by exact_mod_cast hm
    obtain ⟨p1, p2, p3⟩ := hpat n
    refine ⟨?_, ?_, ?_⟩
    · have := (ρ.el_fwd_shift (k₁ + 3 * (n - t * m)) t).1
      rw [show k₁ + 3 * ((n : ℤ) - t * m) + t * ρ.N = k₁ + 3 * n by rw [hNm]; ring] at this
      exact this p1
    · have := (ρ.el_rev_shift (k₁ + 3 * (n - t * m) + 1) t).1
      rw [show k₁ + 3 * ((n : ℤ) - t * m) + 1 + t * ρ.N = k₁ + 3 * n + 1 by rw [hNm]; ring] at this
      exact this p2
    · have := (ρ.el_rev_shift (k₁ + 3 * (n - t * m) + 2) t).1
      rw [show k₁ + 3 * ((n : ℤ) - t * m) + 2 + t * ρ.N = k₁ + 3 * n + 2 by rw [hNm]; ring] at this
      exact this p3
  -- the label twist
  have hstep : ∀ n : ℕ, ρ.label (k₁ + 1 + 3 * ((n + 1 : ℕ) : ℤ)) =
      ρ.label (k₁ + 1 + 3 * (n : ℤ)) - 1 := by
    intro n
    obtain ⟨-, r1, r2⟩ := hall n
    obtain ⟨f3, -, -⟩ := hall (n + 1)
    unfold IsReverse at r1 r2
    unfold IsForward at f3
    have e1 : ρ.label (k₁ + 1 + 3 * ((n + 1 : ℕ) : ℤ)) =
        ρ.label (k₁ + 3 * ((n : ℤ) + 1)) + 1 := by
      rw [← f3]; congr 1; push_cast; ring
    have e2 : ρ.label (k₁ + 3 * ((n : ℤ) + 1)) = ρ.label (k₁ + 3 * n + 2) - 1 := by
      rw [show k₁ + 3 * ((n : ℤ) + 1) = k₁ + 3 * n + 2 + 1 by ring]; exact r2
    have e3 : ρ.label (k₁ + 3 * n + 2) = ρ.label (k₁ + 1 + 3 * n) - 1 := by
      rw [show k₁ + 3 * (n : ℤ) + 2 = k₁ + 3 * n + 1 + 1 by ring, r1]
      congr 2; ring
    rw [e1, e2, e3]
    generalize ρ.label (k₁ + 1 + 3 * (n : ℤ)) = i
    revert i; decide
  set f : ℕ → Fin 3 := fun n ↦ ρ.label (k₁ + 1 + 3 * (n : ℤ)) with hf_def
  have hf1 : ∀ n, f (n + 1) = f n - 1 := hstep
  have hf3 : ∀ n, f (n + 3) = f n := by
    intro n
    rw [hf1, hf1, hf1]
    generalize f n = i; revert i; decide
  have hfq : ∀ q r : ℕ, f (3 * q + r) = f r := by
    intro q r
    induction q with
    | zero => simp
    | succ q ih => rw [show 3 * (q + 1) + r = 3 * q + r + 3 by ring, hf3, ih]
  have htw := ρ.label_add_period (k₁ + 1)
  have hfm : f m = f 0 + 1 := by
    simp only [hf_def, Nat.cast_zero, mul_zero, add_zero]
    rw [← htw, hm]; congr 1
  have hm3 : m % 3 = 2 := by
    have hdiv := Nat.div_add_mod m 3
    rw [← hdiv, hfq] at hfm
    rcases (show m % 3 = 0 ∨ m % 3 = 1 ∨ m % 3 = 2 by omega) with h0 | h1 | h2
    · rw [h0] at hfm; exfalso; revert hfm; generalize f 0 = i; revert i; decide
    · rw [h1, hf1] at hfm; exfalso; revert hfm; generalize f 0 = i; revert i; decide
    · exact h2
  refine ⟨k₁ + 1, m, hm0, hm, hm3, fun j ↦ ?_⟩
  obtain ⟨-, r1, r2⟩ := hall j
  obtain ⟨f3, -, -⟩ := hall (j + 1)
  refine ⟨by rw [show k₁ + 1 + 3 * j = k₁ + 3 * j + 1 by ring]; exact r1,
    by rw [show k₁ + 1 + 3 * j + 1 = k₁ + 3 * j + 2 by ring]; exact r2,
    by rw [show k₁ + 1 + 3 * j + 2 = k₁ + 3 * (j + 1) by ring]; exact f3⟩

end VertexRepresentation

end SmoothedOctagon
