module

public import SmoothedOctagon.Exclusion.Mixed.Chart

/-!
# Case M2: the forward successor reduces to the two endpoint covers

`MIXED_NONSHORT_FORWARD_BOUNDARY_REDUCTION` (FWDRED) (2)-(9) and
`MIXED_NONSHORT_FORWARD_BOUNDARY_EXCLUSION` (inventory E2 entries 25-29). Along the root set
`R_d = 0` (fixed `a, c, d, r, v`) the diagonal at `d` is the affine function
`H(w) = Q(Wv + Zw - C_d)/(16 d)` of the transported norm, the next norm
`𝒯(w) = (Q²v - 16 H(w) Z² + w Z⁴)/K_r²` is affine with slope `-B < 0`, and the squared Casimir
`Γ(w) = Q²vw/64 - H(w)²` is a concave quadratic (`Γ'' = -2C`). The actual point and the boundary
point of `m2_comparison` both lie on the root set, with `w* < w_act ≤ w_cap := w* + τ/B`,
`τ = t* - 3/4 ≥ t_act - 3/4 ≥ 0` (forward switching inequality at the next switch). Concavity gives
`min(Γ(w*), Γ(w_cap)) ≤ Γ(w_act) < 23/125`, which is the extra residual of Cert-FWD0 or of
Cert-FWD1 (FWDRED (9): `B²(Γ(w_cap) - 23/125) = B² E* + B Γ'(w*) τ - C τ²`).

## Main API

* `m2_forward_extra`: at the boundary point, `ForwardLowerExtra ∨ ForwardUpperExtra`.
* `m2_forward_exclusion`: no actual window has a forward successor (the low-scale part through
  `m2_lowScale_hand`, the rest through the covers Cert-FWD0 and Cert-FWD1).
-/

@[expose] public section

namespace SmoothedOctagon

/-- A concave quadratic on `[w₀, w₁]` is at least its smaller endpoint value. -/
private lemma m2_quad_concave (k L μ w0 w1 w : ℝ) (h0 : w0 ≤ w) (h1 : w ≤ w1) :
    min (k * w0 - (L + μ * w0) ^ 2) (k * w1 - (L + μ * w1) ^ 2) ≤ k * w - (L + μ * w) ^ 2 := by
  set f : ℝ → ℝ := fun x => k * x - (L + μ * x) ^ 2 with hf
  have key : (w1 - w0) * f w - (w1 - w) * f w0 - (w - w0) * f w1 =
      μ ^ 2 * (w - w0) * (w1 - w) * (w1 - w0) := by simp only [hf]; ring
  have hm0 := min_le_left (f w0) (f w1)
  have hm1 := min_le_right (f w0) (f w1)
  rcases eq_or_lt_of_le (le_trans h0 h1) with he | hlt
  · have : w = w0 := le_antisymm (he ▸ h1) h0
    subst this; exact hm0
  · have hp : 0 ≤ μ ^ 2 * (w - w0) * (w1 - w) * (w1 - w0) := by
      have := sub_nonneg.2 h0; have := sub_nonneg.2 h1; have := sub_nonneg.2 (le_trans h0 h1)
      positivity
    have hA : (w1 - w) * min (f w0) (f w1) ≤ (w1 - w) * f w0 :=
      mul_le_mul_of_nonneg_left hm0 (sub_nonneg.2 h1)
    have hB : (w - w0) * min (f w0) (f w1) ≤ (w - w0) * f w1 :=
      mul_le_mul_of_nonneg_left hm1 (sub_nonneg.2 h0)
    have : (w1 - w0) * min (f w0) (f w1) ≤ (w1 - w0) * f w := by nlinarith
    exact le_of_mul_le_mul_left this (by linarith)

/-- The cleared upper-endpoint residual (FWDRED (9)): for `B ≠ 0`, with `f(x) = kx - (L + μx)²`,
`B² (f(w) - c) + B f'(w) τ - μ² τ² = B² (f(w + τ/B) - c)`. -/
private lemma m2_endpoint_identity (k L μ w τ B c : ℝ) (hB : B ≠ 0) :
    B ^ 2 * (k * w - (L + μ * w) ^ 2 - c) + B * (k - 2 * μ * (L + μ * w)) * τ - μ ^ 2 * τ ^ 2 =
      B ^ 2 * (k * (w + τ / B) - (L + μ * (w + τ / B)) ^ 2 - c) := by
  field_simp
  ring

/-- **The forward endpoint alternative** (FWDRED (5)-(9), inventory E2 entries 25-28). If the first
switch after `r` is forward, the boundary point satisfies the extra residuals of Cert-FWD0 or of
Cert-FWD1. -/
theorem m2_forward_extra (W : M2Window) (hF : W.ForwardNext) :
    W.chartPt.ForwardLowerExtra ∨ W.chartPt.ForwardUpperExtra := by
  obtain ⟨hw, htn, hex, hB, hG, hC⟩ := m2_chart_boundary W
  obtain ⟨-, hroot, -, hlt⟩ := m2_comparison W
  obtain ⟨s, has, -, -, hts, -, -⟩ := hF
  have ha := W.a_pos
  have hd0 : 0 < W.d := by linarith [W.a_lt_d]
  have hr0 : 0 < W.r := by linarith [W.a_le_r]
  have hs0 : 0 < s := by linarith
  have hQ : 0 < W.d ^ 2 + 4 := by positivity
  have hKr : 0 < W.r ^ 2 + 4 := by positivity
  have hZ : 0 < W.d + W.r := by linarith
  -- the diagonal at `d` is affine in `w` on the root set (FWDRED (2))
  set μ : ℝ := (W.d ^ 2 + 4) * (W.d + W.r) / (16 * W.d) with hμ
  set L : ℝ := (W.d ^ 2 + 4) * ((W.c + W.d) * W.v - m2Stat W.c W.d W.r) / (16 * W.d) with hL
  have hdiag : ∀ u h, m2Root W.a W.c W.d W.r u W.v h = 0 →
      m2hd W.a W.c W.d W.v h = L + μ * m2wOf W.a W.c W.d u W.v h := by
    intro u h e
    unfold m2Root at e
    rw [hL, hμ]
    field_simp
    field_simp at e
    linarith
  have hd_act := hdiag W.u W.h W.root
  rw [← W.w_eq] at hd_act
  have hd_star := hdiag W.uStar W.hStar hroot
  have hwS : m2wOf W.a W.c W.d W.uStar W.v W.hStar = W.wStar := rfl
  rw [hwS] at hd_star
  -- the next norm is affine in `w` with slope `-B` (FWDRED (3)-(4))
  set B : ℝ := (W.d + W.r) ^ 3 * (4 - W.d * W.r) / (W.d * (W.r ^ 2 + 4) ^ 2) with hBdef
  have hBpos : 0 < B := by
    have : 0 < 4 - W.d * W.r := by linarith [W.star_dr]
    positivity
  set α0 : ℝ := ((W.d ^ 2 + 4) ^ 2 * W.v - 16 * L * (W.d + W.r) ^ 2) / (W.r ^ 2 + 4) ^ 2 with hα0
  have hnext : ∀ u h, m2hd W.a W.c W.d W.v h = L + μ * m2wOf W.a W.c W.d u W.v h →
      m2Next W.a W.c W.d W.r u W.v h = α0 - B * m2wOf W.a W.c W.d u W.v h := by
    intro u h e
    unfold m2Next
    rw [e, hα0, hBdef, hμ]
    field_simp
    ring
  have ht_act : W.t = α0 - B * W.w := by
    have := hnext W.u W.h (by rw [← W.w_eq]; exact hd_act)
    rw [← W.w_eq] at this; exact this
  have ht_star : W.tStar = α0 - B * W.wStar := by
    have := hnext W.uStar W.hStar (by rw [hwS]; exact hd_star)
    rw [hwS] at this; exact this
  -- the squared Casimir along the root set (FWDRED (7))
  have hcas : ∀ u h, m2Cas W.a u W.v h =
      (W.d ^ 2 + 4) ^ 2 * W.v / 64 * m2wOf W.a W.c W.d u W.v h - m2hd W.a W.c W.d W.v h ^ 2 := by
    intro u h
    unfold m2Cas m2wOf m2hd
    field_simp
    ring
  set Γf : ℝ → ℝ := fun w => (W.d ^ 2 + 4) ^ 2 * W.v / 64 * w - (L + μ * w) ^ 2 with hΓf
  have hΓact : m2Cas W.a W.u W.v W.h = Γf W.w := by
    rw [hcas, ← W.w_eq, hd_act]
  have hΓstar : m2Cas W.a W.uStar W.v W.hStar = Γf W.wStar := by
    rw [hcas, hwS, hd_star]
  -- the forward switching inequality at the next switch: `t ≥ g_r(s) ≥ 3/4`
  have hg34 : 3 / 4 ≤ m2g W.r s := by
    unfold m2g
    rw [le_div_iff₀ (by positivity)]
    nlinarith [sq_nonneg (W.r - s)]
  have htau : 0 ≤ W.tStar - 3 / 4 := by
    have : 0 < B * (W.w - W.wStar) := mul_pos hBpos (by linarith)
    rw [ht_star]; rw [ht_act] at hts; nlinarith
  set τ : ℝ := W.tStar - 3 / 4 with hτ
  set wc : ℝ := W.wStar + τ / B with hwc
  have hwle : W.w ≤ wc := by
    have h1 : W.w - W.wStar ≤ τ / B := by
      rw [le_div_iff₀ hBpos, hτ, ht_star]
      rw [ht_act] at hts
      linarith
    rw [hwc]; linarith
  -- concavity: `min(Γ(w*), Γ(w_cap)) ≤ Γ(w)`
  have hconc : min (Γf W.wStar) (Γf wc) ≤ Γf W.w :=
    m2_quad_concave _ L μ W.wStar wc W.w hlt.le hwle
  have hΓlt : Γf W.w < 23 / 125 := by rw [← hΓact]; linarith [W.cas_lt]
  by_cases hlo : Γf W.wStar ≤ 23 / 125
  · left
    refine ⟨?_, ?_⟩
    · unfold Certificates.Nonshort.Point.tau; rw [htn]; exact htau
    · rw [hex, hΓstar]; linarith
  · right
    have hcap : Γf wc < 23 / 125 := by
      by_contra hcon
      push Not at hcon
      have : min (Γf W.wStar) (Γf wc) ≥ 23 / 125 := le_min (by linarith) hcon
      linarith
    refine ⟨?_, ?_⟩
    · unfold Certificates.Nonshort.Point.tau; rw [htn]; exact htau
    · unfold Certificates.Nonshort.Point.endpointExcess
      have htau' : W.chartPt.tau = τ := by
        unfold Certificates.Nonshort.Point.tau; rw [htn]
      rw [hB, hG, hC, hex, htau', hΓstar]
      have hE : B ^ 2 * (Γf W.wStar - 23 / 125) +
          B * ((W.d ^ 2 + 4) ^ 2 * W.v / 64 -
            m2hd W.a W.c W.d W.v W.hStar * (W.d ^ 2 + 4) * (W.d + W.r) / (8 * W.d)) * τ -
          (W.d ^ 2 + 4) ^ 2 * (W.d + W.r) ^ 2 / (256 * W.d ^ 2) * τ ^ 2 =
          B ^ 2 * (Γf wc - 23 / 125) := by
        have e1 : m2hd W.a W.c W.d W.v W.hStar * (W.d ^ 2 + 4) * (W.d + W.r) / (8 * W.d) =
            2 * μ * (L + μ * W.wStar) := by rw [hd_star, hμ]; field_simp; ring
        have e2 : (W.d ^ 2 + 4) ^ 2 * (W.d + W.r) ^ 2 / (256 * W.d ^ 2) = μ ^ 2 := by
          rw [hμ]; field_simp; ring
        rw [e1, e2, hwc]
        exact m2_endpoint_identity _ L μ W.wStar τ B _ hBpos.ne'
      rw [hE]
      have h1 : 0 < B ^ 2 := by positivity
      have h2 := mul_neg_of_pos_of_neg h1 (sub_neg.2 hcap)
      linarith

end SmoothedOctagon
