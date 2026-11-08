module

public import SmoothedOctagon.Exclusion.Mixed.FwdHand.SmallGap

/-!
# Case M2: the forward successor, by hand

`MIXED_NONSHORT_FORWARD_HAND_EXCLUSION` (accepted in `MIXED_NONSHORT_FORWARD_HAND_AUDIT`); it
replaces the two interval covers Cert-FWD0 and Cert-FWD1 (`CertNonshortForwardLower/Upper`) used by
`m2_forward_exclusion`.

For an actual smaller-nonshort window with a forward successor, in the normalized coordinates
`t = a/T`, `x = (d - a)/T`, `k = K/T²`, `q = WZ/Q`, `j = 2t + x - 1`:

* §1 (`FwdHand/Window`): `N < 0`, `𝒯_* ≥ 3/4` (through the exact transport identity
  `𝒯_* = 𝒯_U + e(Je² - 1)N/(tW²DE²)`), the incoming floor, `1/4 < t < 2/5`, `k < 2t + x`,
  `k > 29t²/4` and the swap bound `q < W/(1 + 2j)`;
* §2 (`FwdHand/LowRatio`): `t > 1/3`;
* §3 (`FwdHand/LargeGap`): `j < 1/30`;
* §4 (`FwdHand/SmallGap`): the actual Casimir exceeds `9193/50000`, contradicting the cap.

The polynomial signs are generated Bernstein certificates (`FwdHand/Cert*`, generators in
`scripts/certificates/m2-forward/`), checked by `ring`. The inputs are fields of `M2Window` and the
upstream boundary comparison `m2_comparison`.

Route: the shape monotonicity steps of the notes are replaced by concavity in `k` with certificates
at both shape endpoints; the small-gap `χ` bound uses one certificate on the whole `q` interval in
place of concavity in `q`.
-/

@[expose] public section

namespace SmoothedOctagon

/-- **The forward successor is excluded by hand** (`MIXED_NONSHORT_FORWARD_HAND_EXCLUSION`). -/
theorem m2_forward_hand (W : M2Window) (hF : W.ForwardNext) : False := fh_small_gap W hF

end SmoothedOctagon
