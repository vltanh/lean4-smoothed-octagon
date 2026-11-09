module

public import SmoothedOctagon.Period.Defs
public import SmoothedPolygons.Ch7.SmoothedPolygonDisk
public import SmoothedOctagon.Exclusion.Reverse
public import SmoothedOctagon.Terminal.FourPiece
public import SmoothedOctagon.Terminal.FivePiece
public import SmoothedOctagon.Terminal.Identification

/-!
# The terminal comparison: periods with at most five pieces

* Fewer than four pieces are impossible: every such word contradicts the tangent closure
  (`Terminal.Words`).
* Four pieces: tangent closure forces alternating factors and state closure forces the initial
  state; the cost, as a function of the factors, has its unique minimum `A_oct` at the octagon's
  factors `√2`, initial state `Φ(0, y₀)` and word `e₂ e₀ e₁ e₂`.
* Five pieces: every five-piece word outside two orbits contradicts the tangent closure
  (`Terminal.Words`). With the twist, the remaining words are mixed (the orbit of `01020`), which
  costs strictly more than `A_oct`, or entirely reverse (the orbit of `02102`), which case R
  excludes.

Equality therefore forces the smoothed octagon's trajectory, up to the relabeling of the vertices
by a power of `R`.
-/

@[expose] public section

namespace SmoothedOctagon

open SmoothedPolygons Set

namespace Term

/-- The raw-cost form of the terminal bound: a closed cycle of at most five pieces per period that
is not entirely reverse has raw cost at least `8 δ_oct`. -/
theorem rawCost_ge_of_le_five (n : ℕ) (c : Cycle n) (hn : n ≤ 5) (hn0 : 0 < n)
    (hR : ¬ ∀ k, c.lab (k + 1) = c.lab k - 1) : 8 * octagonDensity ≤ c.rawCost := by
  interval_cases n
  · exact c.cycle_one_false.elim
  · exact c.cycle_two_false.elim
  · exact c.cycle_three_false.elim
  · obtain ⟨c0, h0, hcost, -⟩ := c.exists_relabel_zero
    have hf := c0.cycle_four_forward
    have l1 : c0.lab 1 = 1 := by simpa [h0] using hf 0
    have l2 : c0.lab 2 = 2 := by have := hf 1; norm_num [l1] at this; rw [this]
    have l3 : c0.lab 3 = 0 := by have := hf 2; norm_num [l2] at this; rw [this]
    rw [← hcost, ← Cycle.rawCost_relabel, ← Cycle.rawCost_relabel]
    refine c0.relabel.relabel.four_rawCost_ge ?_ ?_ ?_ ?_
    · show c0.lab 0 + 1 + 1 = 2; rw [h0]; rfl
    · show c0.lab 1 + 1 + 1 = 0; rw [l1]; rfl
    · show c0.lab 2 + 1 + 1 = 1; rw [l2]; rfl
    · show c0.lab 3 + 1 + 1 = 2; rw [l3]; rfl
  · rcases c.cycle_five with h | ⟨c', hc', h0, h1, h2, h3, h4⟩
    · exact absurd h hR
    · rw [← hc']; exact (c'.five_rawCost_gt h0 h1 h2 h3 h4).le

end Term

/-- **Terminal cost bound.** A normal vertex period with at most five pieces costs at least
`A_oct`. -/
theorem terminal_cost (P : NormalPeriod) (hN : P.N ≤ 5) : octagonCost ≤ P.cost := by
  have hR : ¬ ∀ k, P.termCycle.lab (k + 1) = P.termCycle.lab k - 1 :=
    fun h ↦ reverse_exclusion P h
  have h := Term.rawCost_ge_of_le_five P.N P.termCycle hN P.rep.N_pos hR
  rw [P.cost_eq_rawCost, octagonCost, show √12 = 2 * √3 by
    rw [show (12 : ℝ) = 2 ^ 2 * 3 by norm_num, Real.sqrt_mul (by norm_num),
      Real.sqrt_sq (by norm_num)]]
  have h3 : (0 : ℝ) < √3 := by positivity
  nlinarith

namespace Term

/-- **The equality data of a four-piece cycle**: if the raw cost is `8 δ_oct`, every factor is
`√2`, the word is all forward, and the initial margins are those of the octagon. -/
theorem four_equality_data (n : ℕ) (c : Cycle n) (hn : n = 4)
    (heq : c.rawCost = 8 * octagonDensity) :
    (∀ k, c.q k = √2) ∧ (∀ k, c.lab (k + 1) = c.lab k + 1) ∧
      c.m 0 (c.lab 0) = octActive ∧ c.m 0 (c.lab 0 + 1) = octThird ∧
      c.m 0 (c.lab 0 + 2) = octActive := by
  subst hn
  obtain ⟨c0, h0, hcost, s, hs⟩ := c.exists_relabel_zero
  have hf := c0.cycle_four_forward
  have l1 : c0.lab 1 = 1 := by simpa [h0] using hf 0
  have l2 : c0.lab 2 = 2 := by have := hf 1; norm_num [l1] at this; rw [this]
  have l3 : c0.lab 3 = 0 := by have := hf 2; norm_num [l2] at this; rw [this]
  obtain ⟨a, b, ha, hb, hab, hq0, hq1, hq2, hq3, hm0, hm1, hm2, hc⟩ :=
    c0.relabel.relabel.four_param (by show c0.lab 0 + 1 + 1 = 2; rw [h0]; rfl)
      (by show c0.lab 1 + 1 + 1 = 0; rw [l1]; rfl) (by show c0.lab 2 + 1 + 1 = 1; rw [l2]; rfl)
      (by show c0.lab 3 + 1 + 1 = 2; rw [l3]; rfl)
  have heq2 : fourDensity a b = octagonDensity := by
    rw [Cycle.rawCost_relabel, Cycle.rawCost_relabel, hcost, heq] at hc
    linarith
  have hab' := fourPiece_density_eq ha hb hab heq2
  subst hab'
  have h2 : (0 : ℝ) < √2 := by positivity
  have hs2 : √2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have ha' : a = √2 / 2 := by
    have : (a - √2 / 2) * (a + √2 / 2) = 0 := by nlinarith [hs2]
    rcases mul_eq_zero.1 this with h | h
    · linarith
    · nlinarith
  have hinv : a⁻¹ = √2 := by rw [ha']; field_simp; linarith
  have hN : (a + a - 1) * (a + a + 3) = 2 * √2 - 1 := by
    rw [ha']; ring_nf; rw [hs2]; ring
  have hq : ∀ k, (0 : ℤ) ≤ k → k < 4 → c.q k = √2 := by
    intro k hk0 hk4
    rw [← (hs k).2.1]
    show c0.relabel.relabel.q k = √2
    interval_cases k
    · rw [hq0, hinv]
    · rw [hq1, hinv]
    · rw [hq2, hinv]
    · rw [hq3, hinv]
  refine ⟨fun k ↦ ?_, c.cycle_four_forward, ?_, ?_, ?_⟩
  · have hper : Function.Periodic c.q ((4 : ℕ) : ℤ) := c.q_add
    have := hper.sub_int_mul_eq (x := k) (k / 4)
    rw [← this]
    apply hq <;> push_cast <;> omega
  · have hl : c.lab 0 = -s := by rw [← sub_eq_zero, sub_neg_eq_add, ← (hs 0).1, h0]
    have := hm2
    rw [hN, show 1 + a - a = 1 by ring, mul_one] at this
    show c.m 0 (c.lab 0) = 2 / √(2 * √2 - 1)
    rw [← this]
    show c.m 0 (c.lab 0) = c0.m 0 (2 - 1 - 1)
    rw [(hs 0).2.2, hl]; congr 1
  · have hl : c.lab 0 = -s := by rw [← sub_eq_zero, sub_neg_eq_add, ← (hs 0).1, h0]
    have := hm0
    rw [hN, show a + a - 1 = √2 - 1 by rw [ha']; ring] at this
    show c.m 0 (c.lab 0 + 1) = 2 * (√2 - 1) / √(2 * √2 - 1)
    rw [← this]
    show c.m 0 (c.lab 0 + 1) = c0.m 0 (0 - 1 - 1)
    rw [(hs 0).2.2, hl]; congr 1; abel_nf; rfl
  · have hl : c.lab 0 = -s := by rw [← sub_eq_zero, sub_neg_eq_add, ← (hs 0).1, h0]
    have := hm1
    rw [hN, show 1 - a + a = 1 by ring, mul_one] at this
    show c.m 0 (c.lab 0 + 2) = 2 / √(2 * √2 - 1)
    rw [← this]
    show c.m 0 (c.lab 0 + 2) = c0.m 0 (1 - 1 - 1)
    rw [(hs 0).2.2, hl]; congr 1; abel_nf; rfl

/-- A cycle with at most five pieces and raw cost `8 δ_oct` that is not entirely reverse has
four pieces. -/
theorem four_of_rawCost_eq (n : ℕ) (c : Cycle n) (hn : n ≤ 5) (hn0 : 0 < n)
    (hR : ¬ ∀ k, c.lab (k + 1) = c.lab k - 1) (heq : c.rawCost = 8 * octagonDensity) : n = 4 := by
  interval_cases n
  · exact c.cycle_one_false.elim
  · exact c.cycle_two_false.elim
  · exact c.cycle_three_false.elim
  · rfl
  · rcases c.cycle_five with h | ⟨c', hc', h0, h1, h2, h3, h4⟩
    · exact absurd h hR
    · have := c'.five_rawCost_gt h0 h1 h2 h3 h4
      rw [hc', heq] at this
      exact (lt_irrefl _ this).elim

end Term

/-- **Terminal equality.** A normal vertex period with at most five pieces and cost `A_oct` is the
smoothed octagon's trajectory, after relabeling the vertices by `C = R^r`:
`C⁻¹ g C` and `C⁻¹ X C` are the octagon's frame and state on `[0, t_f]`. -/
theorem terminal_equality (P : NormalPeriod) (hN : P.N ≤ 5) (heq : P.cost = octagonCost) :
    P.T = tf 1 ∧ ∃ r : ℕ, ∀ t ∈ Icc 0 P.T,
      (R ^ r)⁻¹ * P.g t * R ^ r = smoothedPolygonG 1 t ∧
        (R ^ r)⁻¹ * P.X t * R ^ r = smoothedPolygonX 1 t := by
  have hR : ¬ ∀ k, P.termCycle.lab (k + 1) = P.termCycle.lab k - 1 :=
    fun h ↦ reverse_exclusion P h
  have h3 : (0 : ℝ) < √3 := by positivity
  have hraw : P.termCycle.rawCost = 8 * octagonDensity := by
    rw [P.cost_eq_rawCost, octagonCost, show √12 = 2 * √3 by
      rw [show (12 : ℝ) = 2 ^ 2 * 3 by norm_num, Real.sqrt_mul (by norm_num),
        Real.sqrt_sq (by norm_num)]] at heq
    have : √3 * (P.termCycle.rawCost - 8 * octagonDensity) = 0 := by linarith
    rcases mul_eq_zero.1 this with h | h
    · exact absurd h h3.ne'
    · linarith
  have h4 := Term.four_of_rawCost_eq P.N P.termCycle hN P.rep.N_pos hR hraw
  obtain ⟨hq, hfwd, m0, m1, m2⟩ := Term.four_equality_data P.N P.termCycle h4 hraw
  have hm : ∀ j, P.termCycle.m 0 j = margin j (P.X 0) := by
    intro j
    simp [NormalPeriod.termCycle, NormalPeriod.termMargin, P.rep.τ_zero]
  rw [hm] at m0 m1 m2
  exact Term.octagon_identification P h4 hq hfwd m0 m1 m2

end SmoothedOctagon
