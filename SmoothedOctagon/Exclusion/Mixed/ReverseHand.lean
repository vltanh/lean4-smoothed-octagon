module

public import SmoothedOctagon.Exclusion.Mixed.Comparison
public import SmoothedOctagon.Exclusion.Mixed.Hand.ReverseCore
public import SmoothedOctagon.Exclusion.Mixed.Hand.Prereq

/-!
# Case M2: the reverse successor, by hand

`MIXED_NONSHORT_REVERSE_HAND_EXCLUSION` (accepted in `MIXED_NONSHORT_REVERSE_HAND_AUDIT`); it
replaces the cover Cert-REV (`MIXED_NONSHORT_REVERSE_BOUNDARY_EXCLUSION`), which is not used.

In the normalized coordinates `t = a/T`, `x = (d - a)/T`, `k = K/T²`, `q = WZ/Q` (`T = a + c`) the
actual reverse-next window satisfies the necessary conditions (12) of the note:
`0 < t < 2/5`, `x > 0`, `k ≥ 1`, `k ≥ 2t + x`, `k ≥ 29t²/4`, `k < 2t + 2x + x²`,
`x < 7/3 - (10/3)t`, `1 < q < W/p`, `v = Sec(t, 1 - t, t + x) < U(t)`, `v ≥ F_{p/W}(q)`, `N_k < 0`,
from

* `N_k < 0`: the boundary comparison `G(b*) < 0` (`m2_comparison`);
* `k ≥ 2t + x`: `MIXED_NONSHORT_REVERSE_ORDER_BOUND` (the only use of the reverse successor, with
  `w ≤ Sec(a, r, d)` from `M2Window.ReverseNext` and CONT (17)-(18));
* `k ≥ 29t²/4`: the scale `a < 4/5` (`MIXED_NONSHORT_HIGH_T_HAND_EXCLUSION` `t < 2/5` and
  `MIXED_NONSHORT_CONDITIONAL_SCALE_BOUND`);
* `k < 2t + 2x + x²`: `MIXED_NONSHORT_UPPER_ENVELOPE_GAP` Lemma 2;
* `x < 7/3 - (10/3)t`: `MIXED_NONSHORT_REVERSE_EXACT_SHAPE_COMPARISON`;

and the three exhaustive cases of §4 (unit shape `MIXED_NONSHORT_UNIT_SHAPE_HAND_EXCLUSION`, order
face `MIXED_NONSHORT_REVERSE_ORDER_FACE_REDUCTION` in the form of §1, scale strip §§2-3) each give
`N_{k'} > 0` at a smaller shape `k' ≤ k`, contradicting the strict increase of `N` in `k`.

The scalar argument is `nh_reverse_core` (`Hand/ReverseCore`), the window-level bounds are in
`Hand/Link`, `Hand/Order`, `Hand/Gap`, `Hand/Scale`, `Hand/HighT` (`Hand/Prereq`). The only
unproved input is the upstream `m2_comparison`.

Route: the polynomial signs of the notes (unit shape §§4-8, order face (15)-(18), high-ratio
§4) are proved by generated Bernstein certificates checked by `ring` (`Hand/Cert*`); the scale
strip is closed by the six unit-shape signs at `k = 29t²/4` directly (no comparison with
`t₀ = 13/35`); `t < 2/5` uses row bounds on `C₁, C₂, C₃` on the whole rectangle; `a < 4/5` uses the
window's `a² < 12/17` (`ρ < 3/20`) in place of `ρ < 1/7` and a discriminant form of the turn floor.
-/

@[expose] public section

namespace SmoothedOctagon

/-- **The reverse successor is excluded** (`MIXED_NONSHORT_REVERSE_HAND_EXCLUSION` §4): the
actual normalized data satisfy every condition of `nh_reverse_core`, which gives `N_k > 0`,
contrary to `N_k < 0` (`nh_window_N_neg`). -/
theorem m2_reverse_hand (W : M2Window) (hR : W.ReverseNext) : False := by
  obtain ⟨ht, -, hx, hk1, hq, hqW, hv, hvU, -, hF, -⟩ := nh_window_basic W
  have hN := nh_reverse_core ht (nh_high_t W) hx hk1.le (nh_reverse_order_k W hR)
    (nh_scale_k W).le (nh_centre_gap_k W) (nh_window_dur_x W) hq hqW hv hvU hF
  linarith [nh_window_N_neg W]

end SmoothedOctagon
