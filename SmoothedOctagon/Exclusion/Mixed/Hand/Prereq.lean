module

public import SmoothedOctagon.Exclusion.Mixed.Hand.Link
public import SmoothedOctagon.Exclusion.Mixed.Hand.Gap
public import SmoothedOctagon.Exclusion.Mixed.Hand.HighT

/-!
# Case M2 by hand: necessary bounds of an actual window

The three actual-window bounds used by the hand exclusions, and their normalized forms
(proved in `Hand/Gap`, `Hand/HighT`, `Hand/Scale`).

* `nh_centre_gap`: `d² + 2cd > 4` (`MIXED_NONSHORT_UPPER_ENVELOPE_GAP`, Lemma 2), i.e.
  `k < 2t + 2x + x²` (`nh_centre_gap_k`).
* `nh_high_t`: `t = a/(a + c) < 2/5` (`MIXED_NONSHORT_HIGH_T_HAND_EXCLUSION`).
* `nh_scale_lt`: `a < 4/5` (`MIXED_NONSHORT_CONDITIONAL_SCALE_BOUND`), i.e. `k > 29t²/4`
  (`nh_scale_k`).
-/

@[expose] public section

namespace SmoothedOctagon

/-- **The centre gap** `d² + 2cd > 4` (`MIXED_NONSHORT_UPPER_ENVELOPE_GAP`, Lemma 2). -/
theorem nh_centre_gap (W : M2Window) : 4 < W.d ^ 2 + 2 * W.c * W.d := nh_centre_gap' W

/-- **The high-ratio exclusion** `t < 2/5` (`MIXED_NONSHORT_HIGH_T_HAND_EXCLUSION`). -/
theorem nh_high_t (W : M2Window) : W.nt < 2 / 5 := nh_high_t' W

/-- **The nonshort scale** `a < 4/5` (`MIXED_NONSHORT_CONDITIONAL_SCALE_BOUND` with
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
