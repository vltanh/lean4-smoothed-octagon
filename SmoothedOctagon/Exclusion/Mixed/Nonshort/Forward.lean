module

public import SmoothedOctagon.Exclusion.Mixed.Nonshort.Forward.SmallGap

/-!
# Case M2: the forward successor

For an actual smaller-nonshort window with a forward successor, four steps exclude the window, in
the normalized coordinates `t = a/T`, `x = (d - a)/T`, `k = K/T²`, `q = WZ/Q`, `j = 2t + x - 1`:

* `Nonshort/Forward/Window`: `N < 0`, `𝒯_* ≥ 3/4` (through the exact transport identity
  `𝒯_* = 𝒯_U + e(Je² - 1)N/(tW²DE²)`), the incoming floor, `1/4 < t < 2/5`, `k < 2t + x`,
  `k > 29t²/4` and the swap bound `q < W/(1 + 2j)`;
* `Nonshort/Forward/LowRatio`: `t > 1/3`;
* `Nonshort/Forward/LargeGap`: `j < 1/30`;
* `Nonshort/Forward/SmallGap`: the actual Casimir exceeds `9193/50000`, contradicting the cap.

The polynomial signs are Bernstein certificates (the `*Signs` modules, generators in
`scripts/certificates/nonshort-forward/`), checked by `ring`. The inputs are fields of `M2Window` and the
boundary comparison `m2_comparison`.

The shape monotonicity steps use concavity in `k` with certificates at both shape endpoints; the
small-gap `χ` bound uses one certificate on the whole `q` interval.
-/

@[expose] public section

namespace SmoothedOctagon

/-- **The forward successor is excluded**: no actual smaller-nonshort window has a forward
successor. -/
theorem m2_forward_exclusion (W : M2Window) (hF : W.ForwardNext) : False := nsf_small_gap W hF

end SmoothedOctagon
