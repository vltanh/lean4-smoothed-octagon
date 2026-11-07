module

public import SmoothedOctagon.Reduction.Defs

/-!
# Gluing finite vertex descriptions

The combinatorial half of the switch count (`Reduction/SwitchCount.lean`): finite vertex
descriptions (`IsPiecewiseVertex`) of neighbouring intervals concatenate, and a description of
`[0, T]` follows from local descriptions by compactness.

Main API:

* `qrsb_isPiecewiseVertex_append`: `n` pieces on `[a, b]` and `m` pieces on `[b, c]` give `n + m`
  pieces on `[a, c]` (no merging).
* `qrsb_isPiecewiseVertex_of_local`: if every `t₀ ∈ [0, T]` has a `δ > 0` such that every
  subinterval `[a, b]` of `[0, T]` inside `(t₀ - δ, t₀ + δ)` has a finite vertex description, then
  so has `[0, T]` (Lebesgue number lemma, then induction along a uniform partition).
-/

@[expose] public section

namespace SmoothedOctagon.Reduction

open SmoothedPolygons MeasureTheory Set

/-- Concatenation of finite vertex descriptions of `[a, b]` and `[b, c]`. -/
theorem qrsb_isPiecewiseVertex_append {u : ℝ → Fin 3 → ℝ} {a b c : ℝ} {n m : ℕ}
    (h₁ : IsPiecewiseVertex u a b n) (h₂ : IsPiecewiseVertex u b c m) :
    IsPiecewiseVertex u a c (n + m) := by
  obtain ⟨τ, l, hτ0, hτn, hmono, hpiece⟩ := h₁
  obtain ⟨τ', l', hτ'0, hτ'm, hmono', hpiece'⟩ := h₂
  obtain ⟨σ, hσ⟩ : ∃ σ : ℕ → ℝ, ∀ k, σ k = if k ≤ n then τ k else τ' (k - n) :=
    ⟨_, fun _ ↦ rfl⟩
  obtain ⟨ll, hll⟩ : ∃ ll : ℕ → Fin 3, ∀ k, ll k = if k < n then l k else l' (k - n) :=
    ⟨_, fun _ ↦ rfl⟩
  have hσ_le : ∀ k ≤ n, σ k = τ k := fun k hk ↦ by rw [hσ, ite_eq_left hk]
  have hσ_ge : ∀ k, n ≤ k → σ k = τ' (k - n) := by
    intro k hk
    rcases hk.lt_or_eq with hk | rfl
    · rw [hσ, ite_eq_right (not_le.2 hk)]
    · rw [hσ, ite_eq_left le_rfl, hτn, Nat.sub_self, hτ'0]
  refine ⟨σ, ll, ?_, ?_, ?_, ?_⟩
  · rw [hσ_le 0 (Nat.zero_le _), hτ0]
  · rw [hσ_ge (n + m) (Nat.le_add_right _ _), Nat.add_sub_cancel_left, hτ'm]
  · intro k hk
    by_cases hkn : k < n
    · rw [hσ_le k hkn.le, hσ_le (k + 1) hkn]
      exact hmono k hkn
    · push Not at hkn
      rw [hσ_ge k hkn, hσ_ge (k + 1) (hkn.trans (Nat.le_succ k)), Nat.sub_add_comm hkn]
      exact hmono' (k - n) (by omega)
  · intro k hk
    by_cases hkn : k < n
    · rw [hσ_le k hkn.le, hσ_le (k + 1) hkn, hll, ite_eq_left hkn]
      exact hpiece k hkn
    · push Not at hkn
      rw [hσ_ge k hkn, hσ_ge (k + 1) (hkn.trans (Nat.le_succ k)), Nat.sub_add_comm hkn, hll,
        ite_eq_right (not_lt.2 hkn)]
      exact hpiece' (k - n) (by omega)

/-- **Local to global.** If every point of `[0, T]` has a neighbourhood in which every subinterval
of `[0, T]` has a finite vertex description, then `[0, T]` has one. -/
theorem qrsb_isPiecewiseVertex_of_local {u : ℝ → Fin 3 → ℝ} {T : ℝ} (hT : 0 ≤ T)
    (hloc : ∀ t₀ ∈ Icc 0 T, ∃ δ > 0, ∀ a b, 0 ≤ a → a < b → b ≤ T → t₀ - δ < a →
      b < t₀ + δ → ∃ n, IsPiecewiseVertex u a b n) :
    ∃ n, IsPiecewiseVertex u 0 T n := by
  choose! δ hδpos hδ using hloc
  obtain ⟨ε, hε, hleb⟩ := lebesgue_number_lemma_of_metric (isCompact_Icc (a := (0 : ℝ)) (b := T))
    (c := fun t : Icc (0 : ℝ) T ↦ Metric.ball (t : ℝ) (δ t)) (fun _ ↦ Metric.isOpen_ball)
    (fun x hx ↦ mem_iUnion.2 ⟨⟨x, hx⟩, Metric.mem_ball_self (hδpos x hx)⟩)
  -- every short subinterval has a finite description
  have hshort : ∀ a b, 0 ≤ a → a < b → b ≤ T → b - a < ε → ∃ n, IsPiecewiseVertex u a b n := by
    intro a b ha hab hb hba
    obtain ⟨t, ht⟩ := hleb a ⟨ha, hab.le.trans hb⟩
    have hamem : a ∈ Metric.ball (t : ℝ) (δ t) := ht (Metric.mem_ball_self hε)
    have hbmem : b ∈ Metric.ball (t : ℝ) (δ t) := ht (by
      rw [Metric.mem_ball, Real.dist_eq, abs_of_pos (by linarith)]
      exact hba)
    rw [Metric.mem_ball, Real.dist_eq, abs_lt] at hamem hbmem
    exact hδ t t.2 a b ha hab hb (by linarith) (by linarith)
  -- induction along the partition of step `ε / 2`
  have hind : ∀ k : ℕ, ∀ x, 0 < x → x ≤ T → x ≤ k * (ε / 2) →
      ∃ n, IsPiecewiseVertex u 0 x n := by
    intro k
    induction k with
    | zero =>
      intro x hx _ hxk
      simp only [CharP.cast_eq_zero, zero_mul] at hxk
      linarith
    | succ k ih =>
      intro x hx hxT hxk
      by_cases hle : x ≤ k * (ε / 2)
      · exact ih x hx hxT hle
      push Not at hle
      push_cast at hxk
      rcases (Nat.zero_le k).eq_or_lt with hk | hk
      · subst hk
        simp only [CharP.cast_eq_zero, zero_add, one_mul] at hxk
        exact hshort 0 x le_rfl hx hxT (by linarith)
      · have hy : 0 < (k : ℝ) * (ε / 2) := by
          have : (0 : ℝ) < k := by exact_mod_cast hk
          positivity
        obtain ⟨n, hn⟩ := ih _ hy (hle.le.trans hxT) le_rfl
        obtain ⟨m, hm⟩ := hshort _ x hy.le hle hxT (by linarith)
        exact ⟨n + m, qrsb_isPiecewiseVertex_append hn hm⟩
  rcases hT.eq_or_lt with rfl | hT
  · exact ⟨0, fun _ ↦ 0, fun _ ↦ 0, rfl, rfl, fun k hk ↦ absurd hk (Nat.not_lt_zero k),
      fun k hk ↦ absurd hk (Nat.not_lt_zero k)⟩
  · obtain ⟨k, hk⟩ := exists_nat_ge (T / (ε / 2))
    exact hind k T hT le_rfl (by rwa [div_le_iff₀ (by positivity)] at hk)

end SmoothedOctagon.Reduction
