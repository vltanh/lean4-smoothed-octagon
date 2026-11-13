module

public import SmoothedOctagon.Exclusion.Mixed.Comparison
public import SmoothedOctagon.Exclusion.Mixed.Nonshort.Core
public import SmoothedOctagon.Exclusion.Mixed.Nonshort.NecessaryBounds

/-!
# Case M2: the reverse successor

In the normalized coordinates `t = a/T`, `x = (d - a)/T`, `k = K/T²`, `q = WZ/Q` (`T = a + c`) the
actual reverse-next window satisfies the necessary conditions
`0 < t < 2/5`, `x > 0`, `k ≥ 1`, `k ≥ 2t + x`, `k ≥ 29t²/4`, `k < 2t + 2x + x²`,
`x < 7/3 - (10/3)t`, `1 < q < W/p`, `v = Sec(t, 1 - t, t + x) < U(t)`, `v ≥ F_{p/W}(q)`, `N_k < 0`,
from

* `N_k < 0`: the boundary comparison `G(b*) < 0` (`m2_comparison`);
* `k ≥ 2t + x`: the reverse order bound `d ≤ b*` (`nsr_reverse_order`; the only use of the reverse
  successor, with `w ≤ Sec(a, r, d)` from `M2Window.ReverseNext`);
* `k ≥ 29t²/4`: the scale `a < 4/5` (`nsr_scale_lt`, from the high-ratio exclusion `t < 2/5`,
  `nsr_high_t`);
* `k < 2t + 2x + x²`: the centre gap `d² + 2cd > 4` (`nsr_centre_gap`);
* `x < 7/3 - (10/3)t`: the duration bound `d < 7c/3` (`nsr_window_dur`);

and the three exhaustive cases (the unit shape, the order face and the scale strip) each give
`N_{k'} > 0` at a smaller shape `k' ≤ k`, contradicting the strict increase of `N` in `k`.

The scalar argument is `nsr_reverse_core` (`Nonshort/Core`), the window-level bounds are in
`WindowData`, `OrderBounds`, `CentreGap`, `CentralScale` and `HighRatio`
(`Nonshort/NecessaryBounds`).

The order face uses positive factorizations in its two order gaps. The scale strip reduces to
the unit shape by monotonicity. On the unit shape, the reciprocal-mean secant ceiling and
square decompositions reduce the cubic to monotonicity and concavity at the shape boundary.
The bound `t < 2/5` follows from the incoming floor and
the same-lift quadratic identity, while `a < 4/5` uses the window's `a² < 12/17` (`ρ < 3/20`)
and a discriminant form of the turn floor.
-/
@[expose] public section

namespace SmoothedOctagon

/-- **The reverse successor is excluded**: the actual normalized data satisfy every condition of
`nsr_reverse_core`, which gives `N_k > 0`, contrary to `N_k < 0` (`nsr_window_N_neg`). -/
theorem m2_reverse_exclusion (W : M2Window) (hR : W.ReverseNext) : False := by
  obtain ⟨ht, -, hx, hk1, hq, hqW, hv, hvU, -, hF, -⟩ := nsr_window_basic W
  have hN := nsr_reverse_core ht (nsr_high_t W) hx hk1.le (nsr_reverse_order_k W hR)
    (nsr_scale_k W).le (nsr_centre_gap_k W) (nsr_window_dur_x W) hq hqW hv hvU hF
  linarith [nsr_window_N_neg W]

end SmoothedOctagon
