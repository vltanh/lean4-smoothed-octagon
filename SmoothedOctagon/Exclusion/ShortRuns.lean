module

public import SmoothedOctagon.Period.Defs
public import SmoothedOctagon.Exclusion.ShortRun.Winding
public import SmoothedOctagon.Exclusion.ShortRun.TwoCentre

/-!
# Case M1: no competitive all-short mixed period

A competitive normal vertex period whose cyclic sign word is `(− − +)^m` does not exist: the
whole-period winding identity of the centre angles and the lower bound on each centre angle of a
competitive period are incompatible.

The proof: the word is `(− − +)^m` with `m ≡ 2 (mod 3)` (`m1_pattern`); the normal multiplier is
elliptic (`NormalPeriod.gam2_pos_of_mixed`) and, the period being competitive, its Casimir is capped
(`NormalPeriod.gam2_le_cap`); at every centre the scalar data (`NormalPeriod.m1_centreData`) and the
cap give `cos φ_j < 3/10` (`m1_angle_gap`), so `φ_j > 2π/5`; for `m ≥ 5` this contradicts
`∑ φ_j = (m + 1)π/3` (`m1_winding`), and `m = 2` is excluded by its cost (`m1_two_centre`).
-/

@[expose] public section

namespace SmoothedOctagon

open Real

/-- **Case M1.** No competitive normal vertex period has mixed signs with every reverse run of
length two and every forward run of length one. -/
theorem shortRuns_exclusion (P : NormalPeriod) (hc : P.IsCompetitive) (h : P.rep.ClassM1) :
    False := by
  obtain ⟨k₀, m, hm0, hN, hm3, hpat⟩ := P.rep.m1_pattern h
  have hpat' : P.m1_IsPattern k₀ := hpat
  have hpos := P.gam2_pos_of_mixed h.1
  have hd : 0 < P.costateCycle.swd 0 := by
    have := P.swd_ge_of_mixed h.1 0
    linarith
  have hcap := P.gam2_le_cap hc hpos hd
  rcases (show m = 2 ∨ 5 ≤ m by omega) with h2 | h5
  · exact m1_two_centre P hc hpat' (by show P.rep.N = 6; rw [hN, h2])
  · have hw := m1_winding P hc hpat' hN hpos
    have hgt : ∀ j ∈ Finset.range m, 2 * π / 5 < Real.arccos (P.m1_E (m1_centre k₀ j) /
        (2 * √(P.m1_u (m1_centre k₀ j) * P.m1_v (m1_centre k₀ j)))) := by
      intro j _
      have hD := P.m1_centreData hpat' j
      have hgap := m1_angle_gap hD hcap
      have hW : 0 < √(P.m1_u (m1_centre k₀ j) * P.m1_v (m1_centre k₀ j)) := by
        have := hD.u_ge; have := hD.v_ge
        exact Real.sqrt_pos.2 (by positivity)
      refine m1_arccos_gt ?_
      rw [div_lt_iff₀ (by positivity)]
      linarith
    have hsum := Finset.sum_lt_sum_of_nonempty (Finset.nonempty_range_iff.2 (by omega)) hgt
    rw [hw, Finset.sum_const, Finset.card_range, nsmul_eq_mul] at hsum
    have h5' : (5 : ℝ) ≤ m := by exact_mod_cast h5
    nlinarith [Real.pi_pos]

end SmoothedOctagon
