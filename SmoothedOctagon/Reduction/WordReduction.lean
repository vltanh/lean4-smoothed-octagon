module

public import SmoothedOctagon.Reduction.Defs

/-!
# Reduced vertex words: merging, and rebasing at a genuine switch

A control that is a.e. a concatenation of `n` vertex pieces on `[0, T]` has, after extending it by
the twist (labels go up by one per period), deleting nothing (all pieces have positive length) and
merging equal neighbours, also across the twisted seam, a cyclically reduced word with `1 ≤ N ≤ n`
letters per period. Rebased at one of its genuine switches, the control has a `VertexRepresentation`
with `N` pieces.

No optimality and no PMP is used. A genuine switch exists by the twist alone: the twist adds `+1`
to the labels per period, so the increments `i_{k+1} - i_k` of one period sum to `1 ≠ 0` in `ℤ/3`,
and some increment is nonzero.

Main API:

* `exists_rebase_vertexRepresentation`: rebasing at a genuine switch gives a vertex
  representation with at most `n` pieces.
-/

@[expose] public section

namespace SmoothedOctagon.Reduction

open SmoothedPolygons MeasureTheory Set

/-! ### Almost-everywhere statements on intervals -/

/-- Two a.e. statements on adjacent open intervals glue across the common endpoint (a null set). -/
private theorem ae_Ioo_join {P : ℝ → Prop} {a c b : ℝ} (h₁ : ∀ᵐ t, t ∈ Ioo a c → P t)
    (h₂ : ∀ᵐ t, t ∈ Ioo c b → P t) : ∀ᵐ t, t ∈ Ioo a b → P t := by
  have hc : ∀ᵐ t : ℝ, t ≠ c := by
    rw [ae_iff]
    simp
  filter_upwards [h₁, h₂, hc] with t ht₁ ht₂ htc ht
  rcases lt_or_gt_of_ne htc with h | h
  · exact ht₁ ⟨ht.1, h⟩
  · exact ht₂ ⟨h, ht.2⟩

/-- Translating an a.e. statement by `c`. -/
private theorem ae_comp_add {P : ℝ → Prop} (h : ∀ᵐ x, P x) (c : ℝ) : ∀ᵐ t, P (t + c) :=
  (measurePreserving_add_right volume c).quasiMeasurePreserving.ae h

/-! ### Reduced words on an interval -/

/-- On `[a, b]` the control `w` is a.e. a concatenation of `N` vertex pieces of positive length with
distinct neighbouring labels, the first label `i` and the last label `j`. -/
private def ReducedWord (w : ℝ → Fin 3 → ℝ) (a b : ℝ) (N : ℕ) (i j : Fin 3) : Prop :=
  ∃ (τ : ℕ → ℝ) (l : ℕ → Fin 3), τ 0 = a ∧ τ N = b ∧ (∀ k < N, τ k < τ (k + 1)) ∧
    (∀ k < N, ∀ᵐ t, t ∈ Ioo (τ k) (τ (k + 1)) → w t = vertex (l k)) ∧
    (∀ k, k + 1 < N → l (k + 1) ≠ l k) ∧ l 0 = i ∧ l (N - 1) = j

/-- Appending a piece to a reduced word: merged into the last piece if the labels agree, a new
piece otherwise. The first label is kept. -/
private theorem ReducedWord.append {w : ℝ → Fin 3 → ℝ} {a c b : ℝ} {N : ℕ} {i j k : Fin 3}
    (h : ReducedWord w a c N i j) (hN : 1 ≤ N) (hcb : c < b)
    (hk : ∀ᵐ t, t ∈ Ioo c b → w t = vertex k) :
    ∃ N', 1 ≤ N' ∧ N' ≤ N + 1 ∧ ReducedWord w a b N' i k := by
  obtain ⟨τ, l, h0, hN', hmono, hae, hne, hl0, hlN⟩ := h
  by_cases hkj : k = j
  · subst hkj
    refine ⟨N, hN, by omega, fun m ↦ if m = N then b else τ m, l, ?_, by simp, ?_, ?_, hne,
      hl0, hlN⟩
    · simp only [ite_eq_right (show (0 : ℕ) ≠ N by omega), h0]
    · intro m hm
      simp only [ite_eq_right (show m ≠ N by omega)]
      by_cases hm1 : m + 1 = N
      · rw [ite_eq_left hm1]
        have := hmono m hm
        rw [hm1, hN'] at this
        exact this.trans hcb
      · rw [ite_eq_right hm1]
        exact hmono m hm
    · intro m hm
      simp only [ite_eq_right (show m ≠ N by omega)]
      by_cases hm1 : m + 1 = N
      · rw [ite_eq_left hm1]
        have h1 := hae m hm
        rw [hm1, hN'] at h1
        have hm' : m = N - 1 := by omega
        rw [hm', hlN] at h1 ⊢
        exact ae_Ioo_join h1 hk
      · rw [ite_eq_right hm1]
        exact hae m hm
  · refine ⟨N + 1, by omega, le_rfl, fun m ↦ if m = N + 1 then b else τ m,
      fun m ↦ if m = N then k else l m, ?_, by simp, ?_, ?_, ?_, ?_, ?_⟩
    · simp only [ite_eq_right (show (0 : ℕ) ≠ N + 1 by omega), h0]
    · intro m hm
      simp only [ite_eq_right (show m ≠ N + 1 by omega)]
      by_cases hmN : m = N
      · subst hmN
        rw [ite_eq_left rfl, hN']
        exact hcb
      · rw [ite_eq_right (show m + 1 ≠ N + 1 by omega)]
        exact hmono m (by omega)
    · intro m hm
      simp only [ite_eq_right (show m ≠ N + 1 by omega)]
      by_cases hmN : m = N
      · subst hmN
        rw [ite_eq_left rfl, ite_eq_left rfl, hN']
        exact hk
      · rw [ite_eq_right (show m + 1 ≠ N + 1 by omega), ite_eq_right hmN]
        exact hae m (by omega)
    · intro m hm
      dsimp only
      by_cases hmN : m + 1 = N
      · rw [ite_eq_left hmN, ite_eq_right (show m ≠ N by omega), show m = N - 1 by omega, hlN]
        exact hkj
      · rw [ite_eq_right hmN, ite_eq_right (show m ≠ N by omega)]
        exact hne m (by omega)
    · simp only [ite_eq_right (show (0 : ℕ) ≠ N by omega), hl0]
    · simp

/-- **Merging.** A concatenation of `n ≥ 1` vertex pieces is a reduced word with at most `n` pieces
and the same first and last labels. -/
private theorem reducedWord_of_pieces {w : ℝ → Fin 3 → ℝ} {τ : ℕ → ℝ} {l : ℕ → Fin 3} {n : ℕ}
    (hn : 1 ≤ n) (hmono : ∀ k < n, τ k < τ (k + 1))
    (hae : ∀ k < n, ∀ᵐ t, t ∈ Ioo (τ k) (τ (k + 1)) → w t = vertex (l k)) :
    ∃ N, 1 ≤ N ∧ N ≤ n ∧ ReducedWord w (τ 0) (τ n) N (l 0) (l (n - 1)) := by
  induction n, hn using Nat.le_induction with
  | base => exact ⟨1, le_rfl, le_rfl, τ, l, rfl, rfl, hmono, hae, fun k hk ↦ by omega, rfl, rfl⟩
  | succ n hn ih =>
    obtain ⟨N, hN1, hNn, hR⟩ :=
      ih (fun k hk ↦ hmono k (by omega)) (fun k hk ↦ hae k (by omega))
    obtain ⟨N', h1, h2, hR'⟩ := hR.append hN1 (hmono n (by omega)) (hae n (by omega))
    exact ⟨N', h1, by omega, by simpa using hR'⟩

/-- Restarting a reduced word at time `c`. -/
private theorem ReducedWord.shift {w : ℝ → Fin 3 → ℝ} {c a b : ℝ} {N : ℕ} {i j : Fin 3}
    (h : ReducedWord w (c + a) (c + b) N i j) : ReducedWord (fun t ↦ w (c + t)) a b N i j := by
  obtain ⟨τ, l, h0, hN, hmono, hae, hne, hl0, hlN⟩ := h
  refine ⟨fun k ↦ τ k - c, l, by simp [h0], by simp [hN], fun k hk ↦ by simpa using hmono k hk,
    fun k hk ↦ ?_, hne, hl0, hlN⟩
  filter_upwards [ae_comp_add (hae k hk) c] with t ht hmem
  have := ht ⟨by linarith [hmem.1], by linarith [hmem.2]⟩
  simpa [add_comm] using this

/-! ### Periodic extension of a reduced word -/

/-- The label shift `q mod 3` of the `q`-th period. -/
private def periodShift (q : ℤ) : Fin 3 := ⟨(q % 3).toNat, by omega⟩

private theorem periodShift_zero : periodShift 0 = 0 := rfl

private theorem periodShift_add_one (q : ℤ) : periodShift (q + 1) = periodShift q + 1 := by
  ext
  simp [periodShift, Fin.val_add]
  omega

/-- Every integer is `q N + r` with `0 ≤ r < N`. -/
private theorem exists_decomp {N : ℕ} (hN : 0 < N) (k : ℤ) :
    ∃ (q : ℤ) (r : ℕ), r < N ∧ k = q * N + r := by
  have hN' : (0 : ℤ) < N := by exact_mod_cast hN
  refine ⟨k / N, (k % N).toNat, ?_, ?_⟩
  · have := Int.emod_lt_of_pos k hN'
    have := Int.emod_nonneg k hN'.ne'
    omega
  · rw [Int.toNat_of_nonneg (Int.emod_nonneg k hN'.ne')]
    exact (Int.ediv_mul_add_emod k N).symm

/-- A reduced word on `[0, T]` whose last label is not the first label plus one extends by the
twist to a vertex representation with the same number of pieces. -/
private theorem exists_vertexRepresentation {T : ℝ} {w : ℝ → Fin 3 → ℝ} {N : ℕ} {i j : Fin 3}
    (h : ReducedWord w 0 T N i j) (hN : 1 ≤ N) (hseam : j ≠ i + 1) :
    ∃ ρ : VertexRepresentation T w, ρ.N = N := by
  obtain ⟨τ₀, l₀, h0, hT, hmono, hae, hne, hl0, hlN⟩ := h
  have hN' : (N : ℤ) ≠ 0 := by exact_mod_cast (show N ≠ 0 by omega)
  let τ : ℤ → ℝ := fun k ↦ τ₀ (k % N).toNat + (k / N : ℤ) * T
  let label : ℤ → Fin 3 := fun k ↦ l₀ (k % N).toNat + periodShift (k / N)
  have hdiv : ∀ (q : ℤ) (r : ℕ), r < N →
      ((q * N + r : ℤ) / N = q ∧ ((q * N + r : ℤ) % N).toNat = r) := by
    intro q r hr
    have hr' : (r : ℤ) < N := by exact_mod_cast hr
    constructor
    · rw [add_comm, Int.add_mul_ediv_right _ _ hN', Int.ediv_eq_zero_of_lt (by positivity) hr',
        zero_add]
    · rw [add_comm, Int.add_mul_emod_self_right, Int.emod_eq_of_lt (by positivity) hr']
      simp
  have hτ : ∀ (q : ℤ) (r : ℕ), r ≤ N → τ (q * N + r) = τ₀ r + q * T := by
    intro q r hr
    rcases lt_or_eq_of_le hr with hr | hr
    · simp only [τ, (hdiv q r hr).1, (hdiv q r hr).2]
    · rw [hr]
      have := (hdiv (q + 1) 0 (by omega))
      simp only [Nat.cast_zero, add_zero] at this
      simp only [τ, show (q * N + N : ℤ) = (q + 1) * N by ring, this.1, this.2, h0, hT]
      push_cast
      ring
  have hlabel : ∀ (q : ℤ) (r : ℕ), r < N → label (q * N + r) = l₀ r + periodShift q := by
    intro q r hr
    simp only [label, (hdiv q r hr).1, (hdiv q r hr).2]
  have hlabelN : ∀ q : ℤ, label (q * N + N) = l₀ 0 + periodShift q + 1 := by
    intro q
    have := hlabel (q + 1) 0 (by omega)
    simp only [Nat.cast_zero, add_zero] at this
    rw [show (q * N + N : ℤ) = (q + 1) * N by ring, this, periodShift_add_one, add_assoc]
  refine ⟨⟨N, τ, label, hN, ?_, ?_, ?_, ?_, ?_, ?_⟩, rfl⟩
  · simpa [h0] using hτ 0 0 (by omega)
  · refine strictMono_int_of_lt_succ fun k ↦ ?_
    obtain ⟨q, r, hr, rfl⟩ := exists_decomp hN k
    rw [hτ q r hr.le, add_assoc, show ((r : ℤ) + 1) = ((r + 1 : ℕ) : ℤ) by push_cast; ring,
      hτ q (r + 1) hr]
    linarith [hmono r hr]
  · intro k
    obtain ⟨q, r, hr, rfl⟩ := exists_decomp hN k
    rw [show q * N + r + N = (q + 1) * N + r by ring, hτ q r hr.le, hτ (q + 1) r hr.le]
    push_cast
    ring
  · intro k
    obtain ⟨q, r, hr, rfl⟩ := exists_decomp hN k
    rw [show q * N + r + N = (q + 1) * N + r by ring, hlabel q r hr, hlabel (q + 1) r hr,
      periodShift_add_one, add_assoc]
  · intro k
    obtain ⟨q, r, hr, rfl⟩ := exists_decomp hN k
    rw [hlabel q r hr, add_assoc]
    by_cases hr1 : r + 1 < N
    · rw [show ((r : ℤ) + 1) = ((r + 1 : ℕ) : ℤ) by push_cast; ring, hlabel q (r + 1) hr1]
      intro heq
      exact hne r hr1 (add_right_cancel heq)
    · have hrN : r = N - 1 := by omega
      rw [show ((r : ℤ) + 1) = N by rw [hrN]; push_cast [show 1 ≤ N from hN]; ring, hlabelN,
        hrN, hlN, hl0]
      intro heq
      apply hseam
      have : j + periodShift q = i + 1 + periodShift q := by rw [← heq]; abel
      exact add_right_cancel this
  · intro k hk0 hkN
    lift k to ℕ using hk0
    have hkN' : k < N := by exact_mod_cast hkN
    have e1 := hτ 0 k hkN'.le
    have e2 := hτ 0 (k + 1) hkN'
    have e3 := hlabel 0 k hkN'
    simp only [zero_mul, zero_add, Int.cast_zero, add_zero, periodShift_zero] at e1 e2 e3
    push_cast at e2
    rw [e1, e2, e3]
    exact hae k hkN'

/-- **Merging and rebasing at a genuine switch**. If on `[0, T]` the control is a.e. a concatenation
of `n` vertex pieces, there is a time `s ∈ [0, T)` such that the rebased control `û(t) = v(s + t)`
(twisted extension `v`) has a vertex representation (distinct neighbouring labels, also across the
twisted seam) with at most `n` pieces.

Proof outline: extend the pieces to a bi-infinite sequence by the twist, `τ_{k+n} = τ_k + T`,
`l_{k+n} = l_k + 1`. The boundaries `τ_k` with `l_k ≠ l_{k-1}` (genuine switches) form a set that
is invariant under `+T` and nonempty (the increments of one period sum to `1` in `ℤ/3`), so one,
`s`, lies in `[0, T)`. Take as `τ̂` the genuine switches after `s`, shifted by `-s`, and as labels
the common labels of the merged runs; there are `N ≤ n` of them per period, neighbours differ, and
`û = e_{label}` a.e. on each merged piece (a finite union of the original pieces up to their
endpoints, a null set).

Concretely, the genuine switch `s = τ_{k₀}` is chosen first, with `k₀ < n`; the `n` pieces of
`[s, s + T]` are merged by a left-to-right scan that keeps the first and the last label, so the
seam condition of the reduced word is exactly the genuine switch at `s`; the reduced word is then
extended to `ℤ` by the twist. -/
theorem exists_rebase_vertexRepresentation {T : ℝ} (hT : 0 < T) {u : ℝ → Fin 3 → ℝ} {n : ℕ}
    (hu : IsPiecewiseVertex u 0 T n) :
    ∃ s : ℝ, 0 ≤ s ∧ s < T ∧ ∃ ρ : VertexRepresentation T (rebaseControl T u s), ρ.N ≤ n := by
  obtain ⟨τ, l, h0, hn, hmono, hae⟩ := hu
  have hn1 : 1 ≤ n := by
    rcases Nat.eq_zero_or_pos n with rfl | h
    · rw [h0] at hn
      exact absurd hn hT.ne
    · exact h
  -- `τ` is monotone on `0, …, n`, so the pieces lie in `[0, T]`
  have hle : ∀ j k, j ≤ k → k ≤ n → τ j ≤ τ k := by
    intro j k hjk hkn
    induction k, hjk using Nat.le_induction with
    | base => exact le_rfl
    | succ k hjk ih => exact (ih (by omega)).trans (hmono k (by omega)).le
  have hτ0 : ∀ k ≤ n, 0 ≤ τ k := fun k hk ↦ h0 ▸ hle 0 k (Nat.zero_le k) hk
  have hτT : ∀ k ≤ n, τ k ≤ T := fun k hk ↦ hn ▸ hle k n hk le_rfl
  -- the pieces of the twisted control on `[0, 2T]`
  let σ : ℕ → ℝ := fun m ↦ if m ≤ n then τ m else τ (m - n) + T
  let lab : ℕ → Fin 3 := fun m ↦ if m < n then l m else l (m - n) + 1
  have hσlo : ∀ m ≤ n, σ m = τ m := fun m hm ↦ ite_eq_left hm
  have hσhi : ∀ m, n ≤ m → σ m = τ (m - n) + T := by
    intro m hm
    by_cases hmn : m ≤ n
    · have : m = n := le_antisymm hmn hm
      subst this
      simp [σ, h0, hn]
    · exact ite_eq_right hmn
  have hσmono : ∀ m < 2 * n, σ m < σ (m + 1) := by
    intro m hm
    by_cases hmn : m < n
    · rw [hσlo m hmn.le, hσlo (m + 1) hmn]
      exact hmono m hmn
    · rw [hσhi m (by omega), hσhi (m + 1) (by omega), show m + 1 - n = m - n + 1 by omega]
      linarith [hmono (m - n) (by omega)]
  have hσae : ∀ m < 2 * n, ∀ᵐ t, t ∈ Ioo (σ m) (σ (m + 1)) →
      twistedControl T u t = vertex (lab m) := by
    intro m hm
    by_cases hmn : m < n
    · rw [hσlo m hmn.le, hσlo (m + 1) hmn]
      filter_upwards [hae m hmn] with t ht hmem
      have hfl : ⌊t / T⌋₊ = 0 := Nat.floor_eq_zero.mpr ((div_lt_one hT).mpr
        (lt_of_lt_of_le hmem.2 (hτT (m + 1) hmn)))
      have hlab : lab m = l m := ite_eq_left hmn
      rw [hlab, ← ht hmem]
      funext j
      simp [twistedControl, hfl]
    · obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le (not_lt.mp hmn)
      have hkn : k < n := by omega
      rw [hσhi (n + k) (by omega), hσhi (n + k + 1) (by omega), show n + k - n = k by omega,
        show n + k + 1 - n = k + 1 by omega]
      have hlab : lab (n + k) = l k + 1 := by
        simp only [lab, ite_eq_right hmn, show n + k - n = k by omega]
      filter_upwards [ae_comp_add (hae k hkn) (-T)] with t ht hmem
      have hmem' : t + -T ∈ Ioo (τ k) (τ (k + 1)) :=
        ⟨by linarith [hmem.1], by linarith [hmem.2]⟩
      have hfl : ⌊t / T⌋₊ = 1 := by
        rw [Nat.floor_eq_iff (div_nonneg (by linarith [hmem.1, hτ0 k hkn.le]) hT.le),
          le_div_iff₀ hT, div_lt_iff₀ hT]
        push_cast
        constructor
        · linarith [hmem.1, hτ0 k hkn.le]
        · linarith [hmem.2, hτT (k + 1) hkn]
      rw [hlab]
      funext j
      simp only [twistedControl, hfl, Nat.cast_one, one_mul]
      rw [show t - T = t + -T by ring, ht hmem']
      fin_cases j <;> generalize l k = i <;> fin_cases i <;>
        simp [vertex, Pi.single_apply] <;> decide
  -- a genuine switch in the first period: the seam condition at `k₀`
  obtain ⟨k₀, hk₀, hseam⟩ : ∃ k₀ < n, lab (k₀ + (n - 1)) ≠ lab (k₀ + 0) + 1 := by
    by_contra hcon
    push Not at hcon
    have hfirst : l (n - 1) = l 0 + 1 := by
      have := hcon 0 (by omega)
      simpa [lab, show n - 1 < n by omega, show 0 < n by omega] using this
    have hconst : ∀ k < n, l k = l 0 := by
      intro k hk
      induction k with
      | zero => rfl
      | succ k ih =>
        have h1 := hcon (k + 1) hk
        have h2 : lab (k + 1 + (n - 1)) = l k + 1 := by
          simp only [lab, ite_eq_right (show ¬ (k + 1 + (n - 1) < n) by omega),
            show k + 1 + (n - 1) - n = k by omega]
        rw [h2, add_zero, show lab (k + 1) = l (k + 1) from ite_eq_left hk] at h1
        rw [← ih (by omega)]
        exact (add_right_cancel h1).symm
    have := hconst (n - 1) (by omega)
    rw [this] at hfirst
    generalize l 0 = x at hfirst
    revert x hfirst
    decide
  -- merge the `n` pieces of `[τ k₀, τ k₀ + T]` and restart at `τ k₀`
  obtain ⟨N, hN1, hNn, hR⟩ := reducedWord_of_pieces (w := twistedControl T u)
    (τ := fun k ↦ σ (k₀ + k)) (l := fun k ↦ lab (k₀ + k)) hn1
    (fun k hk ↦ hσmono (k₀ + k) (by omega)) (fun k hk ↦ hσae (k₀ + k) (by omega))
  have ha : σ (k₀ + 0) = τ k₀ + 0 := by rw [add_zero, add_zero, hσlo k₀ hk₀.le]
  have hb : σ (k₀ + n) = τ k₀ + T := by rw [hσhi (k₀ + n) (by omega), Nat.add_sub_cancel]
  rw [ha, hb] at hR
  obtain ⟨ρ, hρ⟩ := exists_vertexRepresentation hR.shift hN1 hseam
  refine ⟨τ k₀, hτ0 k₀ hk₀.le, ?_, ρ, hρ ▸ hNn⟩
  calc τ k₀ < τ (k₀ + 1) := hmono k₀ hk₀
    _ ≤ T := hτT (k₀ + 1) hk₀

end SmoothedOctagon.Reduction
