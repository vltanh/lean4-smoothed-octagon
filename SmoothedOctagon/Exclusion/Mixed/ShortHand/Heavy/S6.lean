module

public import SmoothedOctagon.Exclusion.Mixed.ShortHand.Heavy.S6Link
public import SmoothedOctagon.Exclusion.Mixed.ShortHand.Heavy.S6Pos135
public import SmoothedOctagon.Exclusion.Mixed.ShortHand.Heavy.S6Pos3

/-!
# Heavy leaf `hs6_B_endpoint`: the two endpoint polynomials

`SMALL_SHAPE_COST_EXCLUSION` (20)-(31); inventory HS-S567 S6.6-S6.7. For `1/3 ≤ R ≤ 7/19`,
`0 ≤ δ ≤ 1/19` and `e ∈ {13/5, 3}`: `𝓑(u_q; R, T(e), δ) > b*`.

Route: the notes' cleared polynomial `W_e = 𝒟(𝓑 - b*)` of degree `(24, 14)` (`hh46S6St`, with the
denominator `hh46S6Dn > 0`, `hh46_s6_link`), whose tensor Bernstein coefficients on the whole box
`[1/3, 7/19] × [0, 1/19]` are all positive (the smallest is the corner value, attained at
`R = 7/19`, `δ = 1/19`); no subdivision. This replaces the notes' concavity in `d` and the two
endpoint univariate bounds (26)-(31) by one positivity certificate (`hh46_s6_pos135`,
`hh46_s6_pos3`).

## Main API

`hs6_B_endpoint_proof`.
-/

@[expose] public section

namespace SmoothedOctagon

/-- `u_q = nu/du` with `du = 1260(2 + R)³`. -/
theorem hh46_s6_uq (R d : ℝ) (hR : 0 ≤ R) :
    hs6uq R d = (945 * (2 + R) ^ (3 : ℕ) + 84 * (3 * R ^ (2 : ℕ) + 10 * R + 10) * R ^ (2 : ℕ) -
      42 * (3 * R ^ (2 : ℕ) + 10 * R + 10) * R * (1 + R) * d +
      19 * (3 * R ^ (2 : ℕ) + 10 * R + 10) * (1 + R) ^ (2 : ℕ) * d ^ (2 : ℕ)) /
      (1260 * (2 + R) ^ (3 : ℕ)) := by
  have h : (2 + R) ≠ 0 := by linarith
  unfold hs6uq
  field_simp
  ring

/-- **The two endpoint polynomials** (`SMALL_SHAPE_COST_EXCLUSION` (20)-(31); inventory HS-S567
S6.6, S6.7): for `1/3 ≤ R ≤ 7/19`, `0 ≤ δ ≤ 1/19` and `e ∈ {13/5, 3}`: `𝓑(u_q; R, T(e), δ) > b*`. -/
theorem hs6_B_endpoint_proof {R δ e : ℝ} (hR : 1 / 3 ≤ R) (hR' : R ≤ 7 / 19) (hδ : 0 ≤ δ)
    (hδ2 : δ ≤ 1 / 19) (he : e = 13 / 5 ∨ e = 3) :
    hs6bstar < hs6B R (hs6T R δ e) δ (hs6uq R δ) := by
  have hR0 : 0 < R := by linarith
  have hR1 : R < 1 := by linarith
  have hdu : 0 < 1260 * (2 + R) ^ (3 : ℕ) := by positivity
  rw [hh46_s6_uq R δ hR0.le]
  rcases he with rfl | rfl
  · have hb : 0 < 10 + (18 - 8 * R) * δ := by nlinarith
    have hT : hs6T R δ (13 / 5) = (10 * R + (18 * R - 8) * δ) / (10 + (18 - 8 * R) * δ) := by
      unfold hs6T
      rw [div_eq_div_iff (by nlinarith) hb.ne']
      ring
    rw [hT, ← sub_pos, hh46_s6_link hR0 hR1 hδ hb hdu]
    refine div_pos ?_ (hh46_s6_Dn_pos hR0 hR1 hδ hb hdu)
    have h := hh46_s6_pos135 hR hR' hδ hδ2
    rw [← hh46_s6_id135] at h
    linarith
  · have hb : 0 < 2 + (4 - 2 * R) * δ := by nlinarith
    have hT : hs6T R δ 3 = (2 * R + (4 * R - 2) * δ) / (2 + (4 - 2 * R) * δ) := by
      unfold hs6T
      rw [div_eq_div_iff (by nlinarith) hb.ne']
      ring
    rw [hT, ← sub_pos, hh46_s6_link hR0 hR1 hδ hb hdu]
    refine div_pos ?_ (hh46_s6_Dn_pos hR0 hR1 hδ hb hdu)
    have h := hh46_s6_pos3 hR hR' hδ hδ2
    rw [← hh46_s6_id3] at h
    linarith

end SmoothedOctagon
