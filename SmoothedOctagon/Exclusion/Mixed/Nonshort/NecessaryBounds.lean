module

public import SmoothedOctagon.Exclusion.Mixed.WindowData
public import SmoothedOctagon.Exclusion.Mixed.Nonshort.CentreGap
public import SmoothedOctagon.Exclusion.Mixed.Nonshort.HighRatio

/-!
# Case M2, reverse successor: necessary bounds of an actual window

The three actual-window bounds used by the exclusions of both successors, and their normalized forms
(proved in `Nonshort/CentreGap`, `Nonshort/HighRatio`, `CentralScale`).

* `nsr_centre_gap`: `d² + 2cd > 4` (Lemma 2 of `Nonshort/CentreGap`), i.e. `k < 2t + 2x + x²`
  (`nsr_centre_gap_k`).
* `nsr_high_t`: `t = a/(a + c) < 2/5` (the high-ratio exclusion of `Nonshort/HighRatio`).
* `nsr_scale_lt`: `a < 4/5` (the conditional scale bound of `CentralScale`), i.e. `k > 29t²/4`
  (`nsr_scale_k`).
-/

@[expose] public section

namespace SmoothedOctagon

/-- **The centre gap** `d² + 2cd > 4` (`nsr_centre_gap'`). -/
theorem nsr_centre_gap (W : M2Window) : 4 < W.d ^ 2 + 2 * W.c * W.d := nsr_centre_gap' W

/-- **The high-ratio exclusion** `t < 2/5` (`nsr_high_t'`). -/
theorem nsr_high_t (W : M2Window) : W.nt < 2 / 5 := nsr_high_t' W

/-- **The nonshort scale** `a < 4/5` (the conditional scale bound `nsr_scale_of_t` with
`nsr_high_t`). -/
theorem nsr_scale_lt (W : M2Window) : W.a < 4 / 5 := nsr_scale_of_t W (nsr_high_t' W).le

/-- The centre gap in normalized form: `k < 2t + 2x + x²`. -/
theorem nsr_centre_gap_k (W : M2Window) : W.nk < 2 * W.nt + 2 * W.nx + W.nx ^ 2 := by
  have h := nsr_centre_gap W
  have hT : 0 < W.a + W.c := by linarith [W.a_pos, W.a_lt_c]
  unfold M2Window.nk M2Window.nt M2Window.nx
  rw [div_lt_iff₀ (by positivity)]
  field_simp
  nlinarith

/-- The scale in normalized form: `k > 29t²/4`. -/
theorem nsr_scale_k (W : M2Window) : 29 / 4 * W.nt ^ 2 < W.nk := by
  have h := nsr_scale_lt W
  have ha := W.a_pos
  have hT : 0 < W.a + W.c := by linarith [W.a_lt_c]
  unfold M2Window.nk M2Window.nt
  rw [div_pow, lt_div_iff₀ (by positivity)]
  field_simp
  nlinarith

end SmoothedOctagon
