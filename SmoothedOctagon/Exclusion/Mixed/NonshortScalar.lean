module

public import SmoothedOctagon.Exclusion.Mixed.ForwardEndpoint
public import SmoothedOctagon.Exclusion.Mixed.ReverseHand
public import SmoothedOctagon.Exclusion.Mixed.LowScaleHand
public import SmoothedOctagon.Certificates.Covers

/-!
# Case M2: the scalar exclusion of the smaller-nonshort window

`MIXED_GLOBAL_NONSHORT_PERIOD_EXCLUSION` §§4-5. The first actual switch after `r` is forward or
reverse (CONT §3). A reverse successor is excluded by hand (`m2_reverse_hand`). For a forward
successor, `a ≤ 1/2` is excluded by hand (`m2_lowScale_hand`); for `a > 1/2` the boundary point lies
in the root box `[1/2, 17/20] × [2/15, 2] × [1/32, 15] × [0, 1]` of chart 1 or 2 with every common
residual and the extra residuals of Cert-FWD0 or Cert-FWD1 (`m2_chart_box`, `m2_chart_retained`,
`m2_forward_extra`), which the covers exclude.

## Main API

* `m2_forward_exclusion`: no actual window has a forward successor (given Cert-FWD0, Cert-FWD1).
* `m2_nonshort_scalar`: no actual window exists (given the covers).
-/

@[expose] public section

namespace SmoothedOctagon

open Certificates Certificates.Nonshort

/-- **The forward successor is excluded** (`MIXED_NONSHORT_FORWARD_BOUNDARY_EXCLUSION`, with the
hand low-scale theorem in place of Cert-LOWA). -/
theorem m2_forward_exclusion (hF0 : CertNonshortForwardLower) (hF1 : CertNonshortForwardUpper)
    (W : M2Window) (hF : W.ForwardNext) : False := by
  by_cases ha : W.a ≤ 1 / 2
  · exact m2_lowScale_hand W ha
  push Not at ha
  obtain ⟨⟨-, ha2⟩, hc, heps, hell⟩ := m2_chart_box W
  obtain ⟨hret, h16⟩ := m2_chart_retained W
  have hext := m2_forward_extra W hF
  have ha' : W.a ∈ Set.Icc (1 / 2 : ℝ) (17 / 20) := ⟨ha.le, ha2⟩
  by_cases h12 : W.δ2 ≤ W.δ1
  · have hpt : W.chartPt = chart1 W.a W.c W.eps W.ell := by
      simp only [M2Window.chartPt, M2Window.ell, h12, ite_true]
    rw [hpt] at hret hext
    rcases hext with h | h
    · exact (hF0 W.a W.c W.eps W.ell ha' hc heps hell).1 ⟨hret, h⟩
    · exact (hF1 W.a W.c W.eps W.ell ha' hc heps hell).1 ⟨hret, h⟩
  · have hpt : W.chartPt = chart2 W.a W.c W.eps W.ell := by
      simp only [M2Window.chartPt, M2Window.ell, h12, ite_false]
    have h16' := h16 (lt_of_not_ge h12)
    rw [hpt] at hret hext h16'
    rcases hext with h | h
    · exact (hF0 W.a W.c W.eps W.ell ha' hc heps hell).2 ⟨hret, h16', h⟩
    · exact (hF1 W.a W.c W.eps W.ell ha' hc heps hell).2 ⟨hret, h16', h⟩

/-- **No actual smaller-nonshort window** (`MIXED_GLOBAL_NONSHORT_PERIOD_EXCLUSION` §§4-5): both
successor alternatives of CONT (15) are excluded. -/
theorem m2_nonshort_scalar (hcov : MixedCovers) (W : M2Window)
    (h : W.ForwardNext ∨ W.ReverseNext) : False := by
  rcases h with hF | hR
  · exact m2_forward_exclusion hcov.nonshortForwardLower hcov.nonshortForwardUpper W hF
  · exact m2_reverse_hand W hR

end SmoothedOctagon
