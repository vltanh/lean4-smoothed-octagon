module

public import SmoothedOctagon.Exclusion.Mixed.SmallerShort.CasimirFloor.Endpoints
public import SmoothedOctagon.Exclusion.Mixed.SmallerShort.CasimirFloor.PhiDisplacement
public import SmoothedOctagon.Exclusion.Mixed.SmallerShort.CasimirFloor.PsiShape
public import SmoothedOctagon.Exclusion.Mixed.SmallerShort.CasimirFloor.PsiRatio
public import SmoothedOctagon.Exclusion.Mixed.SmallerShort.CasimirFloor.PhiRatio
public import SmoothedOctagon.Exclusion.Mixed.SmallerShort.CasimirFloor.PhiShape
public import SmoothedOctagon.Exclusion.Mixed.SmallerShort.CasimirFloor.TerminalConcavity

/-!
# Smaller-short window, Casimir floor: the floor at the central scale

The original-Casimir floor `Φ, Ψ > 1829/10000` at the central scale. On the closed box
`2 ≤ x ≤ 13/6`, `0 ≤ δ ≤ 1/19`, `13δ/5 ≤ α - 1 ≤ 3δ`, write `α = 1 + eδ` with `13/5 ≤ e ≤ 3`
(any such `e` at `δ = 0`, where `α = 1`). The six comparisons are applied in this order:

* `Φ`: W1 raises `δ` to `1/19`, W4 raises `x` to `13/6`, W5 raises `e` to `3`;
* `Ψ`: W2 lowers `e` to `13/5`, W3 raises `x` to `13/6`, W6 (concavity in `δ`) leaves the two ends
  `δ = 0`, `δ = 1/19`;

and the three scalar endpoints (`cas_closed_ends`) exceed `1829/10000`.

## Main API

`cas_floor_box_proof`.
-/

@[expose] public section

namespace SmoothedOctagon

/-- **The extended original-Casimir floor at the central scale**: on the closed box
`2 ≤ x ≤ 13/6`, `0 ≤ δ ≤ 1/19`, `13δ/5 ≤ α - 1 ≤ 3δ`, `β = x(1 + δ)`, with `u = ū(x, β)`:
`Φ > 1829/10000` and `Ψ > 1829/10000`. -/
theorem cas_floor_box_proof {x δ al : ℝ} (hx : 2 ≤ x) (hx2 : x ≤ 13 / 6) (hδ : 0 ≤ δ)
    (hδ2 : δ ≤ 1 / 19) (hal : 13 / 5 * δ ≤ al - 1) (hal' : al - 1 ≤ 3 * δ) :
    1829 / 10000 < casPhi x (x * (1 + δ)) al (ssUbar x (x * (1 + δ))) ∧
      1829 / 10000 < casPsi x (x * (1 + δ)) al (ssUbar x (x * (1 + δ))) := by
  have hx0 : 0 < x := by linarith
  have hal0 : 0 < al := by linarith
  have hb0 : 0 < x * (1 + δ) := by positivity
  rw [cas_closed_phi_eq hx0 hal0 hb0, cas_closed_psi_eq hx0 hal0 hb0]
  -- the shape slope `e` with `α = 1 + eδ`
  obtain ⟨e, he, he', hae⟩ : ∃ e : ℝ, 13 / 5 ≤ e ∧ e ≤ 3 ∧ al = 1 + e * δ := by
    rcases eq_or_lt_of_le hδ with h | h
    · subst h
      exact ⟨13 / 5, by norm_num, by norm_num, by linarith⟩
    · refine ⟨(al - 1) / δ, ?_, ?_, ?_⟩
      · rw [le_div_iff₀ h]; linarith
      · rw [div_le_iff₀ h]; linarith
      · field_simp; ring
  have hΦ : casClosedPhiC x (x * (1 + δ)) al (ssUbar x (x * (1 + δ))) = casPhiC x δ e := by
    rw [hae]; rfl
  have hΨ : casClosedPsiC x (x * (1 + δ)) al (ssUbar x (x * (1 + δ))) = casPsiC x δ e := by
    rw [hae]; rfl
  rw [hΦ, hΨ]
  obtain ⟨E1, E2, E3⟩ := cas_closed_ends
  refine ⟨?_, ?_⟩
  · -- `Φ`: W1, W4, W5 and the endpoint
    have w1 := cas_W1 hx hx2 he he' hδ hδ2 le_rfl
    have w4 := cas_W4 he he' hx hx2 le_rfl
    have w5 := cas_W5 he he' le_rfl
    linarith
  · -- `Ψ`: W2, W3, W6 and the two endpoints
    have w2 := cas_W2 hx hx2 hδ hδ2 le_rfl he he'
    have w3 := cas_W3 hδ hδ2 hx hx2 le_rfl
    have w6 := cas_W6 hδ hδ2 E2 E3
    linarith

end SmoothedOctagon
