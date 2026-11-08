module

public import SmoothedOctagon.Exclusion.Mixed.ShortHand.Heavy.S4HandEnd
public import SmoothedOctagon.Exclusion.Mixed.ShortHand.Heavy.S4HandW1
public import SmoothedOctagon.Exclusion.Mixed.ShortHand.Heavy.S4HandW2
public import SmoothedOctagon.Exclusion.Mixed.ShortHand.Heavy.S4HandW3
public import SmoothedOctagon.Exclusion.Mixed.ShortHand.Heavy.S4HandW4
public import SmoothedOctagon.Exclusion.Mixed.ShortHand.Heavy.S4HandW5
public import SmoothedOctagon.Exclusion.Mixed.ShortHand.Heavy.S4HandW6

/-!
# Heavy leaf `hs4_floor_box`: the hand proof

`archive/lighter-proofs/SHORT_CASIMIR_COMPLETE.md` (replacing `EXTENDED_CASIMIR_DERIVATIVES`
(4)-(30); `EXTENDED_CASIMIR_FLOOR` (9)-(10); inventory HS-S4 R20-R22). On the closed box
`2 ≤ x ≤ 13/6`, `0 ≤ δ ≤ 1/19`, `13δ/5 ≤ α - 1 ≤ 3δ`, write `α = 1 + eδ` with `13/5 ≤ e ≤ 3`
(any such `e` at `δ = 0`, where `α = 1`). The note's caller order (§2):

* `Φ`: W1 raises `δ` to `1/19`, W4 raises `x` to `13/6`, W5 raises `e` to `3`;
* `Ψ`: W2 lowers `e` to `13/5`, W3 raises `x` to `13/6`, W6 (concavity in `δ`) leaves the two ends
  `δ = 0`, `δ = 1/19`;

and the three scalar endpoints (§3, `hl46_s4_ends`) exceed `1829/10000`.

## Main API

`hs4_floor_box_proof`.
-/

@[expose] public section

namespace SmoothedOctagon

/-- **The extended original-Casimir floor at the central scale** (`EXTENDED_CASIMIR_DERIVATIVES`
(4)-(31), `EXTENDED_CASIMIR_FLOOR` (9)-(10); inventory HS-S4 R20-R22): on the closed box
`2 ≤ x ≤ 13/6`, `0 ≤ δ ≤ 1/19`, `13δ/5 ≤ α - 1 ≤ 3δ`, `β = x(1 + δ)`, with `u = ū(x, β)`:
`Φ > 1829/10000` and `Ψ > 1829/10000`. -/
theorem hs4_floor_box_proof {x δ al : ℝ} (hx : 2 ≤ x) (hx2 : x ≤ 13 / 6) (hδ : 0 ≤ δ)
    (hδ2 : δ ≤ 1 / 19) (hal : 13 / 5 * δ ≤ al - 1) (hal' : al - 1 ≤ 3 * δ) :
    1829 / 10000 < hs4Phi x (x * (1 + δ)) al (hsUbar x (x * (1 + δ))) ∧
      1829 / 10000 < hs4Psi x (x * (1 + δ)) al (hsUbar x (x * (1 + δ))) := by
  have hx0 : 0 < x := by linarith
  have hal0 : 0 < al := by linarith
  have hb0 : 0 < x * (1 + δ) := by positivity
  rw [hh46_s4_phi_eq hx0 hal0 hb0, hh46_s4_psi_eq hx0 hal0 hb0]
  -- the shape slope `e` with `α = 1 + eδ`
  obtain ⟨e, he, he', hae⟩ : ∃ e : ℝ, 13 / 5 ≤ e ∧ e ≤ 3 ∧ al = 1 + e * δ := by
    rcases eq_or_lt_of_le hδ with h | h
    · subst h
      exact ⟨13 / 5, by norm_num, by norm_num, by linarith⟩
    · refine ⟨(al - 1) / δ, ?_, ?_, ?_⟩
      · rw [le_div_iff₀ h]; linarith
      · rw [div_le_iff₀ h]; linarith
      · field_simp; ring
  have hΦ : hh46S4PhiC x (x * (1 + δ)) al (hsUbar x (x * (1 + δ))) = hl46PhiC x δ e := by
    rw [hae]; rfl
  have hΨ : hh46S4PsiC x (x * (1 + δ)) al (hsUbar x (x * (1 + δ))) = hl46PsiC x δ e := by
    rw [hae]; rfl
  rw [hΦ, hΨ]
  obtain ⟨E1, E2, E3⟩ := hl46_s4_ends
  refine ⟨?_, ?_⟩
  · -- `Φ`: W1, W4, W5 and the endpoint
    have w1 := hl46_W1 hx hx2 he he' hδ hδ2 le_rfl
    have w4 := hl46_W4 he he' hx hx2 le_rfl
    have w5 := hl46_W5 he he' le_rfl
    linarith
  · -- `Ψ`: W2, W3, W6 and the two endpoints
    have w2 := hl46_W2 hx hx2 hδ hδ2 le_rfl he he'
    have w3 := hl46_W3 hδ hδ2 hx hx2 le_rfl
    have w6 := hl46_W6 hδ hδ2 E2 E3
    linarith

end SmoothedOctagon
