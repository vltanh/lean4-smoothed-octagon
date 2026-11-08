module

public import SmoothedOctagon.Exclusion.Mixed.Comparison
public import SmoothedOctagon.Certificates.Nonshort

/-!
# Case M2: the two boundary charts of the nonshort covers

`MIXED_NONSHORT_BLOWUP_REDUCTION` (1)-(17) (BLOWUP), `MIXED_NONSHORT_REVERSE_BOUNDARY_EXCLUSION` §4,
`MIXED_GLOBAL_NONSHORT_PERIOD_EXCLUSION` (6), inventory E2 entries 10-16, 22 and §3.1. At the
boundary `b = b*` the central parameter is `δ₀ = 0`; with `δ₁ = (d - a)/(a + c)`,
`δ₂ = (c + d)(d + r)/(d² + 4) - 1` and `ε' = max(δ₁, δ₂)`, the boundary point is the point
`(a, c, ε', ℓ)` of chart 1 (`δ₁ ≥ δ₂`, `ℓ = δ₂/ε'`) or chart 2 (`δ₂ > δ₁`, `ℓ = δ₁/ε'`) of the
covers in `Certificates/Nonshort.lean` (`M2Window.chartPt`).

## Main API

* `M2Window.δ1`, `δ2`, `eps`, `IsChart2`, `chartPt`.
* `m2_envelope_gap`: `δ₁ > 1/10` (`MIXED_NONSHORT_UPPER_ENVELOPE_GAP`, Lemma 2 and Corollary), so
  the small-parameter corner `ε' ≤ 1/32` is empty (Route: replaces
  `MIXED_NONSHORT_SMALL_PARAMETER_EXCLUSION`, as in `docs/HAND_PROOF_STATUS.md`).
* `m2_chart_box`: `a ∈ [2/15, 17/20]`, `c ∈ [2/15, 2]`, `ε' ∈ [1/32, 15]`, `ℓ ∈ [0, 1]`.
* `m2_chart_retained`: the sixteen common residuals `g₀, …, g₁₅` and, in chart 2, `g₁₆`.
* `m2_chart_boundary`: the cover's `w`, `tn`, `excess`, `B`, `Gprime`, `C` are the boundary
  values `w*`, `t*`, `γ²(u*, v, h*) - 23/125` and the forward-reduction coefficients.
-/

@[expose] public section

namespace SmoothedOctagon

namespace M2Window

variable (W : M2Window)

/-- `δ₁ = (d - a)/(a + c)` (BLOWUP (1)). -/
noncomputable def δ1 : ℝ := (W.d - W.a) / (W.a + W.c)

/-- `δ₂ = WZ/Q - 1` (BLOWUP (1)). -/
noncomputable def δ2 : ℝ := (W.c + W.d) * (W.d + W.r) / (W.d ^ 2 + 4) - 1

/-- The recomputed maximum `ε' = max(δ₁, δ₂)` (`MIXED_GLOBAL_NONSHORT_PERIOD_EXCLUSION` (6)). -/
noncomputable def eps : ℝ := max W.δ1 W.δ2

/-- The boundary point lies in chart 2 (`δ₂ > δ₁`). -/
def IsChart2 : Prop := W.δ1 < W.δ2

/-- The boundary point of the covers: chart 1 `(a, c, ε', δ₂/ε')` if `δ₂ ≤ δ₁`, chart 2
`(a, c, ε', δ₁/ε')` otherwise. -/
noncomputable def chartPt : Certificates.Nonshort.Point :=
  if W.δ2 ≤ W.δ1 then Certificates.Nonshort.chart1 W.a W.c W.eps (W.δ2 / W.eps)
  else Certificates.Nonshort.chart2 W.a W.c W.eps (W.δ1 / W.eps)

/-- The chart weight `ℓ`. -/
noncomputable def ell : ℝ := if W.δ2 ≤ W.δ1 then W.δ2 / W.eps else W.δ1 / W.eps

end M2Window

/-- **The uniform duration-ratio gap** (`MIXED_NONSHORT_UPPER_ENVELOPE_GAP`, Lemma 2
`d² + 2cd > 4` and its Corollary (8), with the sharpened scale `a² < 2/3` of
`HAND_PROOF_REFINEMENTS` §2): `δ₁ > 1/10`. -/
theorem m2_envelope_gap (W : M2Window) : 1 / 10 < W.δ1 := by
  sorry

/-- **The root box** (BLOWUP (2), inventory E2 entry 10): `a ∈ [2/15, 17/20]`, `c ∈ [2/15, 2]`,
`ε' ∈ [1/32, 15]`, `ℓ ∈ [0, 1]`. -/
theorem m2_chart_box (W : M2Window) :
    W.a ∈ Set.Icc (2 / 15 : ℝ) (17 / 20) ∧ W.c ∈ Set.Icc (2 / 15 : ℝ) 2 ∧
      W.eps ∈ Set.Icc (1 / 32 : ℝ) 15 ∧ W.ell ∈ Set.Icc (0 : ℝ) 1 := by
  have ha := W.a_pos
  have hgap := m2_envelope_gap W
  have hc0 : 0 < W.c := by linarith [W.a_lt_c]
  have hd0 : 0 < W.d := by linarith [W.a_lt_d]
  have hr0 : 0 < W.r := by linarith [W.a_le_r]
  have hT : 0 < W.a + W.c := by linarith
  have hQ : 0 < W.d ^ 2 + 4 := by positivity
  -- `c < 2`
  have hc2 : W.c < 2 := by
    have h1 : (W.a + W.c) ^ 2 ≤ (W.a + W.b) * (W.a + W.c) := by
      have := W.c_le_b; nlinarith
    nlinarith [W.central]
  -- `c/a < 15`
  have hca : W.c < 15 * W.a := by linarith [W.a_ge]
  -- `δ₁ < 15`
  have hδ1 : W.δ1 < 15 := by
    unfold M2Window.δ1
    rw [div_lt_iff₀ hT]
    have hd : W.a * W.d < W.c ^ 2 := W.logconc
    have : W.d * W.a < W.c * (15 * W.a) := by nlinarith
    have : W.d < 15 * W.c := by nlinarith
    nlinarith
  -- `δ₂ < 15`
  have hδ2 : W.δ2 < 15 := by
    unfold M2Window.δ2
    rw [sub_lt_iff_lt_add, div_lt_iff₀ hQ]
    have hdr := W.star_dr
    have : W.c * (W.d + W.r) < 15 * W.d * (W.d + W.r) := by
      have : W.c < 15 * W.d := by linarith [W.a_lt_d]
      have : 0 < W.d + W.r := by linarith
      nlinarith
    nlinarith
  have hδ2nn : 0 ≤ W.δ2 := by
    unfold M2Window.δ2
    rw [sub_nonneg, le_div_iff₀ hQ]
    linarith [W.factor_d]
  refine ⟨⟨W.a_ge, ?_⟩, ⟨by linarith [W.a_ge, W.a_lt_c], hc2.le⟩, ⟨?_, ?_⟩, ?_⟩
  · nlinarith [W.scale]
  · unfold M2Window.eps; linarith [le_max_left W.δ1 W.δ2]
  · unfold M2Window.eps; exact (max_lt hδ1 hδ2).le
  · unfold M2Window.ell
    split_ifs with h12
    · have he : W.eps = W.δ1 := max_eq_left h12
      rw [he]
      have : 0 < W.δ1 := by linarith
      exact ⟨div_nonneg hδ2nn this.le, (div_le_one this).2 h12⟩
    · have he : W.eps = W.δ2 := max_eq_right (le_of_not_ge h12)
      rw [he]
      have h12' : W.δ1 < W.δ2 := lt_of_not_ge h12
      have : 0 < W.δ2 := by linarith
      exact ⟨div_nonneg (by linarith) this.le, (div_le_one this).2 h12'.le⟩

/-- **The common residuals at the boundary point** (BLOWUP §1, (2b)-(2c), (13), (17)-(17b);
`MIXED_NONSHORT_REVERSE_BOUNDARY_EXCLUSION` §4; inventory E2 §3.1 table): `g₀, …, g₁₅ ≥ 0`, and
`g₁₆ ≥ 0` (`d ≤ c`) in chart 2. `g₇ = -Φ* ≥ 0` is the comparison `G(b*) < 0` (`m2_comparison`)
through `R_d(U*; b*) = ε'² Φ*`. -/
theorem m2_chart_retained (W : M2Window) :
    W.chartPt.Retained ∧ (W.IsChart2 → 0 ≤ W.chartPt.g16) := by
  sorry

/-- **The boundary values in the cover's coordinates** (BLOWUP (13)-(16), inventory E2 §1.7-1.8):
the cover's `w`, `tn` and `excess` are `w*`, `t*` and `γ²(u*, v, h*) - 23/125`, and its `B`,
`Gprime`, `C` are the slope `Z³(4 - dr)/(d K_r²)` of `𝒯`, the derivative
`Q²v/64 - h_{d*} QZ/(8d)` of `Γ` at `w*` and its half curvature `Q²Z²/(256 d²)`
(`MIXED_NONSHORT_FORWARD_BOUNDARY_REDUCTION` (2)-(9)). -/
theorem m2_chart_boundary (W : M2Window) :
    W.chartPt.w = W.wStar ∧ W.chartPt.tn = W.tStar ∧
      W.chartPt.excess = m2Cas W.a W.uStar W.v W.hStar - 23 / 125 ∧
      W.chartPt.B = (W.d + W.r) ^ 3 * (4 - W.d * W.r) / (W.d * (W.r ^ 2 + 4) ^ 2) ∧
      W.chartPt.Gprime = (W.d ^ 2 + 4) ^ 2 * W.v / 64 -
        m2hd W.a W.c W.d W.v W.hStar * (W.d ^ 2 + 4) * (W.d + W.r) / (8 * W.d) ∧
      W.chartPt.C = (W.d ^ 2 + 4) ^ 2 * (W.d + W.r) ^ 2 / (256 * W.d ^ 2) := by
  sorry

end SmoothedOctagon
