module

public import SmoothedOctagon.Exclusion.Mixed.ShortHand.Heavy.S4Beta2
public import SmoothedOctagon.Exclusion.Mixed.ShortHand.Heavy.S4Face

/-!
# Heavy leaf `hs4_floor_box`: the extended original-Casimir floor at the central scale

`EXTENDED_CASIMIR_DERIVATIVES` (4)-(31), `EXTENDED_CASIMIR_FLOOR` (9)-(10); inventory HS-S4
R20-R22. On `2 ≤ x ≤ 13/6`, `0 ≤ δ ≤ 1/19`, `13δ/5 ≤ α - 1 ≤ 3δ`, `β = x(1 + δ)`, `u = ū(x, β)`:
`Φ, Ψ > 1829/10000`.

Route: replaces the six derivative signs of the notes. `β` is raised at fixed `x, α` to
`x(1 + δ')`, `δ' = min(5(α - 1)/13, 1/19)` (`hh46_s4_beta_mono`, which keeps `13δ'/5 ≤ α - 1 ≤ 3δ'`),
landing on the face `η = 13/5` (`α = 1 + 13δ'/5`) or on the face `δ = 1/19`; on each face both
`Φ` and `Ψ` exceed the floor by the surrogate certificates of `S4Face` (one bivariate Bernstein
certificate per face and function, no subdivision). The three rational log estimates of R22
appear as the constants `L₀` of the surrogates.

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
  have hal1 : 1 ≤ al := by linarith
  have hal2 : al ≤ 22 / 19 := by linarith
  have hal0 : 0 < al := by linarith
  have hb0 : 0 < x * (1 + δ) := by positivity
  rw [hh46_s4_phi_eq hx0 hal0 hb0, hh46_s4_psi_eq hx0 hal0 hb0]
  have hb1 : x ≤ x * (1 + δ) := by nlinarith
  rcases le_total (al - 1) (13 / 95) with hA | hB
  · -- face `η = 13/5` at `δ' = 5(α - 1)/13`
    set d' := 5 * (al - 1) / 13 with hd'
    have hdd : δ ≤ d' := by rw [hd']; linarith
    have hd'2 : d' ≤ 1 / 19 := by rw [hd']; linarith
    have hd'0 : 0 ≤ d' := by linarith
    have hm := hh46_s4_beta_mono hx hx2 hal1 hal2 hb1 (by nlinarith : x * (1 + δ) ≤ x * (1 + d'))
      (by nlinarith : x * (1 + d') ≤ 20 / 19 * x)
    have hal_eq : al = 1 + 13 / 5 * d' := by rw [hd']; ring
    have h1 := hh46_s4_facePhiA hx hx2 hd'0 hd'2
    have h2 := hh46_s4_facePsiA hx hx2 hd'0 hd'2
    rw [← hal_eq] at h1 h2
    exact ⟨h1.trans_le hm.1, h2.trans_le hm.2⟩
  · -- face `δ = 1/19`
    have hm := hh46_s4_beta_mono hx hx2 hal1 hal2 hb1 (by nlinarith : x * (1 + δ) ≤ 20 / 19 * x)
      le_rfl
    have h1 := hh46_s4_facePhiB hx hx2 (by linarith : 108 / 95 ≤ al) hal2
    have h2 := hh46_s4_facePsiB hx hx2 (by linarith : 108 / 95 ≤ al) hal2
    exact ⟨h1.trans_le hm.1, h2.trans_le hm.2⟩

end SmoothedOctagon
