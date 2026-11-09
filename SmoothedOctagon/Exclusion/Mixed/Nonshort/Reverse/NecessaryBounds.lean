module

public import SmoothedOctagon.Exclusion.Mixed.Hand.Link
public import SmoothedOctagon.Exclusion.Mixed.Hand.Gap
public import SmoothedOctagon.Exclusion.Mixed.Hand.HighT

/-!
# Case M2 by hand: necessary bounds of an actual window

The three actual-window bounds used by the hand exclusions, and their normalized forms
(proved in `Hand/Gap`, `Hand/HighT`, `Hand/Scale`).

* `nh_centre_gap`: `d² + 2cd > 4` (Lemma 2 of `Hand/Gap`), i.e. `k < 2t + 2x + x²`
  (`nh_centre_gap_k`).
* `nh_high_t`: `t = a/(a + c) < 2/5` (the high-ratio exclusion of `Hand/HighT`).
* `nh_scale_lt`: `a < 4/5` (the conditional scale bound of `Hand/Scale`), i.e. `k > 29t²/4`
  (`nh_scale_k`).
-/

@[expose] public section

namespace SmoothedOctagon

/-- **The centre gap** `d² + 2cd > 4` (`nh_centre_gap'`). -/
theorem nh_centre_gap (W : M2Window) : 4 < W.d ^ 2 + 2 * W.c * W.d := nh_centre_gap' W

/-- **The high-ratio exclusion** `t < 2/5` (`nh_high_t'`). -/
theorem nh_high_t (W : M2Window) : W.nt < 2 / 5 := nh_high_t' W

/-- **The nonshort scale** `a < 4/5` (the conditional scale bound `nh_scale_of_t` with
`nh_high_t`). -/
theorem nh_scale_lt (W : M2Window) : W.a < 4 / 5 := nh_scale_of_t W (nh_high_t' W).le

/-- The centre gap in normalized form: `k < 2t + 2x + x²`. -/
theorem nh_centre_gap_k (W : M2Window) : W.nk < 2 * W.nt + 2 * W.nx + W.nx ^ 2 := by
  have h := nh_centre_gap W
  have hT : 0 < W.a + W.c := by linarith [W.a_pos, W.a_lt_c]
  unfold M2Window.nk M2Window.nt M2Window.nx
  rw [div_lt_iff₀ (by positivity)]
  field_simp
  nlinarith

/-- The scale in normalized form: `k > 29t²/4`. -/
theorem nh_scale_k (W : M2Window) : 29 / 4 * W.nt ^ 2 < W.nk := by
  have h := nh_scale_lt W
  have ha := W.a_pos
  have hT : 0 < W.a + W.c := by linarith [W.a_lt_c]
  unfold M2Window.nk M2Window.nt
  rw [div_pow, lt_div_iff₀ (by positivity)]
  field_simp
  nlinarith

end SmoothedOctagon
