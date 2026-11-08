module

public import SmoothedOctagon.Period.Costate
public import SmoothedOctagon.Exclusion.Forward.Edge

/-!
# Case F: the all-forward cycle and its global-minimum window

Period-level facts of the all-forward case that follow from the costate cycle alone (no Pontryagin
identity).

## Main API

* `NormalPeriod.ff_N_mod_three`: every switch forward forces `N ≡ 1 (mod 3)`.
* For a cycle with every switch forward (`hF : ∀ k, lab (k + 1) = lab k + 1`):
  `CostateCycle.ff_m_prev` (`m_k(i_k - 1) = a_{k-1}`), `ff_m_next`
  (`m_k(i_k + 1) = (4 - a_{k-1} a_k)/(a_{k-1} + a_k)`), `ff_act_mul_lt` (`a_{k-1} a_k < 4`),
  `ff_q_eq` (`q_k = (a_{k-1} + a_k)(a_k + a_{k+1})/(a_k² + 4)`).
* `CostateCycle.ff_rawCost`: the raw cost is `∑_{j<N} G(a_j, a_{j+1})`.
* `ff_sum_shift`: a sum over one period of a periodic function may start anywhere.
* `ff_seven_le`: the seven-entry lower bound: at a global minimum `a = f m` with
  `N ≥ 7`, `∑_{j<N} G(f_j, f_{j+1}) ≥ G(a, p) + G(p, b) + G(b, a) + G(a, c) + G(c, d) + G(d, a) +
  (n + 1) G(a, a)` with `n = N - 7`.
-/

@[expose] public section

namespace SmoothedOctagon

open SmoothedPolygons Set Real

/-! ### The count `N ≡ 1 (mod 3)` -/

namespace NormalPeriod

variable (P : NormalPeriod)

/-- **`N ≡ 1 (mod 3)`** for an all-forward period: the labels advance by one at every switch and by
one across the twisted seam. -/
theorem ff_N_mod_three (hF : P.rep.AllForward) : P.N % 3 = 1 := by
  have hlab : ∀ n : ℕ, (P.rep.label (n : ℤ)).val = ((P.rep.label 0).val + n) % 3 := by
    intro n
    induction n with
    | zero => simp [Nat.mod_eq_of_lt (P.rep.label 0).isLt]
    | succ n ih =>
      have := hF (n : ℤ)
      rw [VertexRepresentation.IsForward] at this
      push_cast
      rw [this, Fin.val_add, ih]
      simp only [Fin.val_one]
      omega
  have h1 := hlab P.N
  have h2 := P.rep.label_add_period 0
  rw [zero_add] at h2
  rw [h2, Fin.val_add] at h1
  simp only [Fin.val_one] at h1
  have := (P.rep.label 0).isLt
  omega

end NormalPeriod

/-! ### The all-forward cycle -/

namespace CostateCycle

variable {N : ℕ} (C : CostateCycle N)

private lemma ff_quad_rot (f : Fin 3 → ℝ) (i : Fin 3) :
    f 0 * f 1 + f 1 * f 2 + f 2 * f 0 = f i * f (i + 1) + f (i + 1) * f (i - 1) + f (i - 1) * f i := by
  fin_cases i
  · simp only [Fin.zero_eta, zero_add, show (0 : Fin 3) - 1 = 2 from rfl]
  · simp only [Fin.mk_one, show (1 : Fin 3) + 1 = 2 from rfl, show (1 : Fin 3) - 1 = 0 from rfl]
    ring
  · simp only [show (⟨2, by norm_num⟩ : Fin 3) = 2 from rfl, show (2 : Fin 3) + 1 = 0 from rfl,
      show (2 : Fin 3) - 1 = 1 from rfl]
    ring

variable (hF : ∀ k, C.lab (k + 1) = C.lab k + 1)
include hF

/-- The decreasing margin at the switch `k` is the active margin of the previous piece. -/
theorem ff_m_prev (k : ℤ) : C.m k (C.lab k - 1) = C.act (k - 1) := by
  have h := hF (k - 1)
  rw [sub_add_cancel] at h
  rw [h, add_sub_cancel_right]
  have := C.m_act (k - 1)
  rw [sub_add_cancel] at this
  exact this

/-- The third margin at the switch `k`: `m_k(i_k + 1) = (4 - a_{k-1} a_k)/(a_{k-1} + a_k)`. -/
theorem ff_m_next (k : ℤ) :
    C.m k (C.lab k + 1) = (4 - C.act (k - 1) * C.act k) / (C.act (k - 1) + C.act k) := by
  have hq := C.m_quad k
  rw [ff_quad_rot (C.m k) (C.lab k), C.ff_m_prev hF k] at hq
  have hp := C.act_pos (k - 1)
  have ha := C.act_pos k
  rw [eq_div_iff (by linarith)]
  unfold act at hq ⊢
  linear_combination hq

/-- Consecutive active margins have product less than `4` (strict star). -/
theorem ff_act_mul_lt (k : ℤ) : C.act (k - 1) * C.act k < 4 := by
  have h := C.m_pos k (C.lab k + 1)
  rw [C.ff_m_next hF k] at h
  have hp := C.act_pos (k - 1)
  have ha := C.act_pos k
  have := (div_pos_iff_of_pos_right (by linarith : 0 < C.act (k - 1) + C.act k)).1 h
  linarith

/-- The factor of piece `k`: `q_k = (a_{k-1} + a_k)(a_k + a_{k+1})/(a_k² + 4)`. -/
theorem ff_q_eq (k : ℤ) : C.q k = ff_fac (C.act (k - 1)) (C.act k) (C.act (k + 1)) := by
  have hg := C.m_grow k
  rw [C.ff_m_next hF k, ← hF k] at hg
  have hp := C.act_pos (k - 1)
  have ha := C.act_pos k
  have hq := C.q_pos k
  change C.act (k + 1) = (C.act k + _) * C.q k - C.act k at hg
  unfold ff_fac
  have hs : 0 < C.act (k - 1) + C.act k := by linarith
  have e : C.act k + (4 - C.act (k - 1) * C.act k) / (C.act (k - 1) + C.act k) =
      (C.act k ^ 2 + 4) / (C.act (k - 1) + C.act k) := by field_simp; ring
  rw [e] at hg
  field_simp
  rw [hg]
  field_simp
  ring

/-- The arc potential `ψ_j = a_j (a_{j-1} - b_j) - a_j² log(a_{j-1} + a_j) + a_j² log(a_j² + 4)/2`
of the telescoping `arc_j = G(a_j, a_{j+1}) + ψ_j - ψ_{j+1}`. -/
private noncomputable def ffPsi (k : ℤ) : ℝ :=
  C.act k * (C.act (k - 1) - (4 - C.act (k - 1) * C.act k) / (C.act (k - 1) + C.act k)) -
    C.act k ^ 2 * Real.log (C.act (k - 1) + C.act k) + C.act k ^ 2 * Real.log (C.act k ^ 2 + 4) / 2

omit hF in
private lemma ffPsi_add (k : ℤ) : C.ffPsi (k + N) = C.ffPsi k := by
  simp only [ffPsi, show k + N - 1 = k - 1 + N by ring, C.act_add]

private lemma ff_arc_eq (k : ℤ) :
    C.toCycle.arc k = ff_G (C.act k) (C.act (k + 1)) + C.ffPsi k - C.ffPsi (k + 1) := by
  have hp := C.act_pos (k - 1)
  have ha := C.act_pos k
  have hn := C.act_pos (k + 1)
  simp only [Term.Cycle.arc, Term.rawArc]
  rw [C.ff_m_next hF k, C.ff_m_prev hF k, C.ff_q_eq hF k]
  have hact : C.m k (C.lab k) = C.act k := rfl
  rw [hact]
  unfold ff_fac ff_G ffPsi
  rw [show k + 1 - 1 = k by ring]
  have hs : 0 < C.act (k - 1) + C.act k := by linarith
  have ht : 0 < C.act k + C.act (k + 1) := by linarith
  have hK : 0 < C.act k ^ 2 + 4 := by positivity
  rw [Real.log_div (by positivity) hK.ne', Real.log_mul hs.ne' ht.ne']
  generalize Real.log (C.act (k - 1) + C.act k) = L1
  generalize Real.log (C.act k + C.act (k + 1)) = L2
  generalize Real.log (C.act k ^ 2 + 4) = L3
  generalize Real.log (C.act (k + 1) ^ 2 + 4) = L4
  field_simp
  ring

/-- **The cost as a sum of edge functions**: `rawCost = ∑_{j<N} G(a_j, a_{j+1})`. -/
theorem ff_rawCost : C.toCycle.rawCost = ∑ j ∈ Finset.range N, ff_G (C.act j) (C.act (j + 1)) := by
  rw [Term.Cycle.rawCost]
  have e : ∀ j ∈ Finset.range N, C.toCycle.arc (j : ℤ) =
      ff_G (C.act j) (C.act (j + 1)) + (C.ffPsi j - C.ffPsi ((j + 1 : ℕ) : ℤ)) := by
    intro j _
    rw [C.ff_arc_eq hF]; push_cast; ring
  rw [Finset.sum_congr rfl e, Finset.sum_add_distrib, Finset.sum_range_sub' (fun j : ℕ ↦ C.ffPsi j)]
  have := C.ffPsi_add 0
  rw [zero_add] at this
  push_cast
  rw [this]
  ring

end CostateCycle

/-! ### Sums over one period and the seven-entry bound -/

/-- A sum over one period of an `N`-periodic function may start at any index. -/
theorem ff_sum_shift {N : ℕ} (g : ℤ → ℝ) (hper : ∀ k, g (k + N) = g k) (r : ℤ) :
    ∑ i ∈ Finset.range N, g (r + i) = ∑ i ∈ Finset.range N, g i := by
  have step : ∀ k : ℤ, ∑ i ∈ Finset.range N, g (k + 1 + i) = ∑ i ∈ Finset.range N, g (k + i) := by
    intro k
    rcases Nat.eq_zero_or_pos N with hN | hN
    · subst hN; simp
    obtain ⟨n, rfl⟩ : ∃ n, N = n + 1 := ⟨N - 1, by omega⟩
    rw [Finset.sum_range_succ, Finset.sum_range_succ']
    push_cast
    rw [show k + 1 + (n : ℤ) = k + ((n + 1 : ℕ) : ℤ) by push_cast; ring, hper, add_zero]
    congr 1
    refine Finset.sum_congr rfl fun j _ ↦ ?_
    congr 1; ring
  induction r using Int.induction_on with
  | zero => simp
  | succ i ih => rw [step, ih]
  | pred i ih => rw [← ih, ← step, sub_add_cancel]

/-- **The seven-entry lower bound.** For an `N`-periodic positive sequence with consecutive products
below `4`, `N ≥ 7`, and a global minimum `a = f m`, lowering every margin outside the window
`(p, b, a, c, d) = (f (m-2), …, f (m+2))` to `a` gives
`∑_{j<N} G(f_j, f_{j+1}) ≥ G(a,p) + G(p,b) + G(b,a) + G(a,c) + G(c,d) + G(d,a) + (n+1) G(a,a)`,
`n = N - 7`. -/
theorem ff_seven_le {N : ℕ} (f : ℤ → ℝ) (hper : ∀ k, f (k + N) = f k) (hpos : ∀ k, 0 < f k)
    (hprod : ∀ k, f k * f (k + 1) < 4) (m : ℤ) (hmin : ∀ k, f m ≤ f k) (hN : 7 ≤ N) :
    ∃ n : ℕ, ff_G (f m) (f (m - 2)) + ff_G (f (m - 2)) (f (m - 1)) + ff_G (f (m - 1)) (f m) +
      ff_G (f m) (f (m + 1)) + ff_G (f (m + 1)) (f (m + 2)) + ff_G (f (m + 2)) (f m) +
      (n + 1) * ff_G (f m) (f m) ≤ ∑ j ∈ Finset.range N, ff_G (f j) (f (j + 1)) := by
  obtain ⟨n, rfl⟩ : ∃ n, N = 5 + (n + 1) + 1 := ⟨N - 7, by omega⟩
  refine ⟨n, ?_⟩
  set g : ℤ → ℝ := fun j ↦ ff_G (f j) (f (j + 1)) with hg
  have hgper : ∀ k, g (k + ((5 + (n + 1) + 1 : ℕ) : ℤ)) = g k := by
    intro k; simp only [hg, show k + ((5 + (n + 1) + 1 : ℕ) : ℤ) + 1 = k + 1 +
      ((5 + (n + 1) + 1 : ℕ) : ℤ) by ring, hper]
  have hsum : ∑ j ∈ Finset.range (5 + (n + 1) + 1), ff_G (f j) (f (j + 1)) =
      ∑ i ∈ Finset.range (5 + (n + 1) + 1), g (m - 2 + i) := by
    rw [ff_sum_shift g hgper]
  rw [hsum, Finset.sum_range_succ, Finset.sum_range_add, Finset.sum_range_add]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add, hg]
  push_cast
  -- the generic monotonicity step
  have hmono : ∀ x y x' y' : ℤ, f x' ≤ f x → f y' ≤ f y → y = x + 1 →
      ff_G (f x') (f y') ≤ ff_G (f x) (f y) := by
    intro x y x' y' hx hy hxy
    subst hxy
    exact ff_G_mono (hpos x') (hpos y') hx hy (by linarith [hprod x])
  have hmono' : ∀ x y : ℤ, ∀ a b : ℝ, 0 < a → 0 < b → a ≤ f x → b ≤ f y → y = x + 1 →
      ff_G a b ≤ ff_G (f x) (f y) := by
    intro x y a b ha hb hx hy hxy
    subst hxy
    exact ff_G_mono ha hb hx hy (by linarith [hprod x])
  -- term 4: `G(d, a_{m+3}) ≥ G(d, a)`
  have t4 : ff_G (f (m + 2)) (f m) ≤ ff_G (f (m - 2 + 4)) (f (m - 2 + 4 + 1)) :=
    hmono' _ _ _ _ (hpos _) (hpos _) (le_of_eq (by ring_nf)) (hmin _) rfl
  -- the middle terms: `≥ G(a, a)`
  have tmid : ∀ x ∈ Finset.range (n + 1), ff_G (f m) (f m) ≤
      ff_G (f (m - 2 + ((5 + x : ℕ) : ℤ))) (f (m - 2 + ((5 + x : ℕ) : ℤ) + 1)) :=
    fun x _ ↦ hmono' _ _ _ _ (hpos _) (hpos _) (hmin _) (hmin _) rfl
  have hmid := Finset.sum_le_sum tmid
  rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul] at hmid
  push_cast at hmid
  -- the last term: `G(a_{m-3}, p) ≥ G(a, p)`
  have tlast : ff_G (f m) (f (m - 2)) ≤ ff_G (f (m - 2 + ((5 + (n + 1) : ℕ) : ℤ)))
      (f (m - 2 + ((5 + (n + 1) : ℕ) : ℤ) + 1)) := by
    refine hmono' _ _ _ _ (hpos _) (hpos _) (hmin _) ?_ rfl
    have := hper (m - 2)
    push_cast at this ⊢
    rw [show m - 2 + (5 + ((n : ℤ) + 1)) + 1 = m - 2 + ((5 + (n + 1) + 1 : ℕ) : ℤ) by push_cast; ring,
      hper]
  push_cast at tlast
  rw [Finset.sum_range_succ] at hmid
  simp only [add_zero] at hmid ⊢
  have r0 : ff_G (f (m - 2)) (f (m - 2 + 1)) = ff_G (f (m - 2)) (f (m - 1)) := by ring_nf
  have r1 : ff_G (f (m - 2 + 1)) (f (m - 2 + 1 + 1)) = ff_G (f (m - 1)) (f m) := by ring_nf
  have r2 : ff_G (f (m - 2 + 2)) (f (m - 2 + 2 + 1)) = ff_G (f m) (f (m + 1)) := by ring_nf
  have r3 : ff_G (f (m - 2 + 3)) (f (m - 2 + 3 + 1)) = ff_G (f (m + 1)) (f (m + 2)) := by ring_nf
  linarith

end SmoothedOctagon
