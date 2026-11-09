module

public import SmoothedOctagon.Exclusion.Mixed.SmallerShort.Cost.EndpointCurves

/-!
# Smaller-short window, cost: the two endpoint polynomials

The two endpoint polynomials of the cost bound. For `1/3 ≤ R ≤ 7/19`, `0 ≤ d ≤ 1/19` and
`e ∈ {13/5, 3}`: `𝓑(u_q; R, T(e), d) > b*`.

The argument: in the cancelled form (`cost_score_eq`) the score is concave
in `R` (`cost_score_concave`), so it suffices to take `R ∈ {1/3, 7/19}`; on these four
curves the score decreases in `d` (`cost_corr_mono` and the endpoint recipe `costM`,
six rows, one split at `d = 1/38` for `e = 3`), so it suffices to take `d = 1/19`; the four
values there exceed `b*`.

## Main API

`cost_B_endpoint_proof`.
-/

@[expose] public section

namespace SmoothedOctagon

/-- The six rows of the endpoint-recipe table: `costM ≤ 0` on each displacement interval. -/
theorem cost_M_rows :
    costM (13 / 5) (1 / 3) 0 (1 / 19) ≤ 0 ∧ costM (13 / 5) (7 / 19) 0 (1 / 19) ≤ 0 ∧
      costM 3 (1 / 3) 0 (1 / 38) ≤ 0 ∧ costM 3 (1 / 3) (1 / 38) (1 / 19) ≤ 0 ∧
      costM 3 (7 / 19) 0 (1 / 38) ≤ 0 ∧ costM 3 (7 / 19) (1 / 38) (1 / 19) ≤ 0 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
  norm_num [costM, jetk1, costTd, costBd, costvd, costHf, jetg, costv, costQn, jetg1, costzd,
    jetp, costZU, jetp1, jetq, jetq1, costT]

/-- The four values at `d = 1/19`: each exceeds `b*`. -/
theorem cost_corners :
    costbstar < costScore (13 / 5) (1 / 19) (1 / 3) ∧ costbstar < costScore (13 / 5) (1 / 19) (7 / 19) ∧
      costbstar < costScore 3 (1 / 19) (1 / 3) ∧ costbstar < costScore 3 (1 / 19) (7 / 19) := by
  rw [← cost_score_eq (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    ← cost_score_eq (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    ← cost_score_eq (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    ← cost_score_eq (by norm_num) (by norm_num) (by norm_num) (by norm_num)]
  refine ⟨?_, ?_, ?_, ?_⟩ <;> norm_num [costB, costL, costT, costuq, costZU, costZL, costbstar]

/-- At `R ∈ {1/3, 7/19}` and `e ∈ {13/5, 3}`, the cancelled score exceeds `b*` for every
`0 ≤ d ≤ 1/19`. -/
theorem cost_ends {e r d : ℝ} (he : e = 13 / 5 ∨ e = 3) (hr : r = 1 / 3 ∨ r = 7 / 19) (hd : 0 ≤ d)
    (hd' : d ≤ 1 / 19) : costbstar < costScore e d r := by
  obtain ⟨M1, M2, M3, M4, M5, M6⟩ := cost_M_rows
  obtain ⟨C1, C2, C3, C4⟩ := cost_corners
  have he1 : 13 / 5 ≤ e := by rcases he with rfl | rfl <;> norm_num
  have he2 : e ≤ 3 := by rcases he with rfl | rfl <;> norm_num
  have hr1 : 1 / 3 ≤ r := by rcases hr with rfl | rfl <;> norm_num
  have hr2 : r ≤ 7 / 19 := by rcases hr with rfl | rfl <;> norm_num
  -- `G₀` decreases on the whole interval (one or two rows)
  have hG : costG0 e (1 / 19) r ≤ costG0 e d r := by
    rcases he with rfl | rfl
    · have hM : costM (13 / 5) r 0 (1 / 19) ≤ 0 := by rcases hr with rfl | rfl <;> assumption
      exact cost_G0_anti he1 he2 hr1 hr2 le_rfl le_rfl hM hd hd' le_rfl
    · have hMa : costM 3 r 0 (1 / 38) ≤ 0 := by rcases hr with rfl | rfl <;> assumption
      have hMb : costM 3 r (1 / 38) (1 / 19) ≤ 0 := by rcases hr with rfl | rfl <;> assumption
      have hb := fun {u v : ℝ} (hu : 1 / 38 ≤ u) (huv : u ≤ v) (hv : v ≤ 1 / 19) =>
        cost_G0_anti he1 he2 hr1 hr2 (by norm_num) le_rfl hMb hu huv hv
      rcases le_total d (1 / 38) with h | h
      · exact (hb le_rfl (by norm_num) le_rfl).trans
          (cost_G0_anti he1 he2 hr1 hr2 le_rfl (by norm_num) hMa hd h le_rfl)
      · exact hb h hd' le_rfl
  refine lt_of_lt_of_le ?_ (cost_score_dmono he1 he2 hr1 hr2 hd hd' hG)
  rcases he with rfl | rfl <;> rcases hr with rfl | rfl <;> assumption

/-- **The two endpoint polynomials**: for
`1/3 ≤ R ≤ 7/19`, `0 ≤ δ ≤ 1/19` and `e ∈ {13/5, 3}`: `𝓑(u_q; R, T(e), δ) > b*`. -/
theorem cost_B_endpoint_proof {R δ e : ℝ} (hR : 1 / 3 ≤ R) (hR' : R ≤ 7 / 19) (hδ : 0 ≤ δ)
    (hδ2 : δ ≤ 1 / 19) (he : e = 13 / 5 ∨ e = 3) :
    costbstar < costB R (costT R δ e) δ (costuq R δ) := by
  have he1 : 13 / 5 ≤ e := by rcases he with rfl | rfl <;> norm_num
  have he2 : e ≤ 3 := by rcases he with rfl | rfl <;> norm_num
  rw [cost_score_eq hδ (by linarith) (by linarith) (by linarith)]
  exact cost_score_concave he1 he2 hδ hδ2 (cost_ends he (Or.inl rfl) hδ hδ2)
    (cost_ends he (Or.inr rfl) hδ hδ2) hR hR'

end SmoothedOctagon
