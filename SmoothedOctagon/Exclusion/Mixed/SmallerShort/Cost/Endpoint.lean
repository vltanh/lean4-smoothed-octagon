module

public import SmoothedOctagon.Exclusion.Mixed.ShortHand.Heavy.S6HandD

/-!
# The leaf `hs6_B_endpoint`: the hand proof

The two endpoint polynomials of gate S6. For `1/3 ≤ R ≤ 7/19`, `0 ≤ d ≤ 1/19` and
`e ∈ {13/5, 3}`: `𝓑(u_q; R, T(e), d) > b*`.

The argument: in the cancelled form (`hl46_S6F_eq`) the score is concave
in `R` (`hl46_S6F_concave`), so it suffices to take `R ∈ {1/3, 7/19}`; on these four
curves the score decreases in `d` (`hl46_corr_mono` and the endpoint recipe `hl46M`,
six rows, one split at `d = 1/38` for `e = 3`), so it suffices to take `d = 1/19`; the four
values there exceed `b*`.

## Main API

`hs6_B_endpoint_proof`.
-/

@[expose] public section

namespace SmoothedOctagon

/-- The six rows of the endpoint-recipe table: `hl46M ≤ 0` on each displacement interval. -/
theorem hl46_M_rows :
    hl46M (13 / 5) (1 / 3) 0 (1 / 19) ≤ 0 ∧ hl46M (13 / 5) (7 / 19) 0 (1 / 19) ≤ 0 ∧
      hl46M 3 (1 / 3) 0 (1 / 38) ≤ 0 ∧ hl46M 3 (1 / 3) (1 / 38) (1 / 19) ≤ 0 ∧
      hl46M 3 (7 / 19) 0 (1 / 38) ≤ 0 ∧ hl46M 3 (7 / 19) (1 / 38) (1 / 19) ≤ 0 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
  norm_num [hl46M, hl46k1, hl46Td, hl46Bd, hl46vd, hl46Hf, hl46g, hl46v, hl46Qn, hl46g1, hl46zd,
    hl46p, hs6ZU, hl46p1, hl46q, hl46q1, hs6T]

/-- The four values at `d = 1/19`: each exceeds `b*`. -/
theorem hl46_corners :
    hs6bstar < hl46S6F (13 / 5) (1 / 19) (1 / 3) ∧ hs6bstar < hl46S6F (13 / 5) (1 / 19) (7 / 19) ∧
      hs6bstar < hl46S6F 3 (1 / 19) (1 / 3) ∧ hs6bstar < hl46S6F 3 (1 / 19) (7 / 19) := by
  rw [← hl46_S6F_eq (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    ← hl46_S6F_eq (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    ← hl46_S6F_eq (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    ← hl46_S6F_eq (by norm_num) (by norm_num) (by norm_num) (by norm_num)]
  refine ⟨?_, ?_, ?_, ?_⟩ <;> norm_num [hs6B, hs6L, hs6T, hs6uq, hs6ZU, hs6ZL, hs6bstar]

/-- At `R ∈ {1/3, 7/19}` and `e ∈ {13/5, 3}`, the cancelled score exceeds `b*` for every
`0 ≤ d ≤ 1/19`. -/
theorem hl46_ends {e r d : ℝ} (he : e = 13 / 5 ∨ e = 3) (hr : r = 1 / 3 ∨ r = 7 / 19) (hd : 0 ≤ d)
    (hd' : d ≤ 1 / 19) : hs6bstar < hl46S6F e d r := by
  obtain ⟨M1, M2, M3, M4, M5, M6⟩ := hl46_M_rows
  obtain ⟨C1, C2, C3, C4⟩ := hl46_corners
  have he1 : 13 / 5 ≤ e := by rcases he with rfl | rfl <;> norm_num
  have he2 : e ≤ 3 := by rcases he with rfl | rfl <;> norm_num
  have hr1 : 1 / 3 ≤ r := by rcases hr with rfl | rfl <;> norm_num
  have hr2 : r ≤ 7 / 19 := by rcases hr with rfl | rfl <;> norm_num
  -- `G₀` decreases on the whole interval (one or two rows)
  have hG : hl46G0 e (1 / 19) r ≤ hl46G0 e d r := by
    rcases he with rfl | rfl
    · have hM : hl46M (13 / 5) r 0 (1 / 19) ≤ 0 := by rcases hr with rfl | rfl <;> assumption
      exact hl46_G0_anti he1 he2 hr1 hr2 le_rfl le_rfl hM hd hd' le_rfl
    · have hMa : hl46M 3 r 0 (1 / 38) ≤ 0 := by rcases hr with rfl | rfl <;> assumption
      have hMb : hl46M 3 r (1 / 38) (1 / 19) ≤ 0 := by rcases hr with rfl | rfl <;> assumption
      have hb := fun {u v : ℝ} (hu : 1 / 38 ≤ u) (huv : u ≤ v) (hv : v ≤ 1 / 19) =>
        hl46_G0_anti he1 he2 hr1 hr2 (by norm_num) le_rfl hMb hu huv hv
      rcases le_total d (1 / 38) with h | h
      · exact (hb le_rfl (by norm_num) le_rfl).trans
          (hl46_G0_anti he1 he2 hr1 hr2 le_rfl (by norm_num) hMa hd h le_rfl)
      · exact hb h hd' le_rfl
  refine lt_of_lt_of_le ?_ (hl46_S6F_dmono he1 he2 hr1 hr2 hd hd' hG)
  rcases he with rfl | rfl <;> rcases hr with rfl | rfl <;> assumption

/-- **The two endpoint polynomials**: for
`1/3 ≤ R ≤ 7/19`, `0 ≤ δ ≤ 1/19` and `e ∈ {13/5, 3}`: `𝓑(u_q; R, T(e), δ) > b*`. -/
theorem hs6_B_endpoint_proof {R δ e : ℝ} (hR : 1 / 3 ≤ R) (hR' : R ≤ 7 / 19) (hδ : 0 ≤ δ)
    (hδ2 : δ ≤ 1 / 19) (he : e = 13 / 5 ∨ e = 3) :
    hs6bstar < hs6B R (hs6T R δ e) δ (hs6uq R δ) := by
  have he1 : 13 / 5 ≤ e := by rcases he with rfl | rfl <;> norm_num
  have he2 : e ≤ 3 := by rcases he with rfl | rfl <;> norm_num
  rw [hl46_S6F_eq hδ (by linarith) (by linarith) (by linarith)]
  exact hl46_S6F_concave he1 he2 hδ hδ2 (hl46_ends he (Or.inl rfl) hδ hδ2)
    (hl46_ends he (Or.inr rfl) hδ hδ2) hR hR'

end SmoothedOctagon
