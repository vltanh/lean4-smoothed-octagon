module

public import SmoothedOctagon.Exclusion.Mixed.SmallerShort.Displacement.OuterFace.Decomposition

/-!
# Smaller-short window, displacement, outer face: convexity in reciprocal shape

The outer face sign `dsp_outer_face_proof`, second part. On the
rectangle `2 ≤ x ≤ 13/6`, `3/5 ≤ C ≤ 5/6`, `1/x ≤ r ≤ 7/8`, `5/2 ≤ n ≤ 7/2`:
`P_n'' > 2/5` (from its value and slope at `r = 1/x` and the leading coefficient), `1 < A_n < 5`,
`A_n' > 0`, `A_n'' > -1`, `0 < V < 1/100`, `V' > 0`, `|V''| < 1/125` and
`[1/Z - 56/K]'' > -1/10`, so `G'' > 1/4 > 0`. Hence `G < 0` between two shapes where
it is negative (`dspo_neg_between`).

Each printed polynomial `Q(h, v)`, `h = x - 2`, `v = C - 3/5`, is positive by a box rule
(the tactic `dsp_box`): within each power of `h` its `v`-monomials are bounded with `v ≤ 7/30`,
then each power of `h` with `0 ≤ hⁱ ≤ 6⁻ⁱ`. The values at `n = 5/2` and `n = 7/2` give every
`n ∈ [5/2, 7/2]` by linear interpolation (`dsp_interp`).

## Main API

* `dsp_mono1`, `dsp_mono2`, the tactic `dsp_box`; `dsp_interp`, `dsp_interp'`.
* `dspof_lt`, `dspof_ge`, `dspof1_ge`: bounds for `f(z) = -1/z² + 280/(5z + 14)²` on `[23/10, 3]`.
* `dspo_A_bds`: `1 < A_n < 5`, `A_n' > 0`, `A_n'' > -1`.
* `dspo_V_bds`: `0 ≤ V ≤ 1/100`.
* `dspo_G2_pos`, `dspo_neg_between`.
-/

@[expose] public section

namespace SmoothedOctagon

open Real Set

theorem dsp_mono1 {h : ℝ} (hh : 0 ≤ h) (hh6 : h ≤ 1 / 6) (i : ℕ) : 0 ≤ h ^ i ∧ h ^ i ≤ (1 / 6) ^ i :=
  ⟨by positivity, pow_le_pow_left₀ hh hh6 i⟩

theorem dsp_mono2 {h v : ℝ} (hh : 0 ≤ h) (hv : 0 ≤ v) (hv7 : v ≤ 7 / 30) (i j : ℕ) :
    0 ≤ h ^ i * v ^ j ∧ h ^ i * v ^ j ≤ (7 / 30) ^ j * h ^ i := by
  refine ⟨by positivity, ?_⟩
  rw [mul_comm]
  exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hv hv7 j) (by positivity)

set_option hygiene false in
/-- The sign of a printed polynomial in `0 ≤ h ≤ 1/6`, `0 ≤ v ≤ 7/30` (the box rule): within
each power of `h`, the `v`-monomials are bounded by `v ≤ 7/30`; then each power of `h` by
`0 ≤ hⁱ ≤ 6⁻ⁱ`. It needs hypotheses `hh : 0 ≤ h`, `hh6 : h ≤ 1/6`, `hv : 0 ≤ v`, `hv7 : v ≤ 7/30`. -/
macro "dsp_box" : tactic => `(tactic| linarith
    [(dsp_mono1 hh hh6 1).1, (dsp_mono1 hh hh6 1).2, (dsp_mono1 hh hh6 2).1,
      (dsp_mono1 hh hh6 2).2, (dsp_mono1 hh hh6 3).1, (dsp_mono1 hh hh6 3).2,
      (dsp_mono1 hh hh6 4).1, (dsp_mono1 hh hh6 4).2, (dsp_mono1 hh hh6 5).1,
      (dsp_mono1 hh hh6 5).2, (dsp_mono1 hh hh6 6).1, (dsp_mono1 hh hh6 6).2,
      (dsp_mono1 hh hh6 7).1, (dsp_mono1 hh hh6 7).2, (dsp_mono1 hh hh6 8).1,
      (dsp_mono1 hh hh6 8).2, (dsp_mono2 hh hv hv7 0 1).1, (dsp_mono2 hh hv hv7 0 1).2,
      (dsp_mono2 hh hv hv7 0 2).1, (dsp_mono2 hh hv hv7 0 2).2, (dsp_mono2 hh hv hv7 1 1).1,
      (dsp_mono2 hh hv hv7 1 1).2, (dsp_mono2 hh hv hv7 1 2).1, (dsp_mono2 hh hv hv7 1 2).2,
      (dsp_mono2 hh hv hv7 2 1).1, (dsp_mono2 hh hv hv7 2 1).2, (dsp_mono2 hh hv hv7 2 2).1,
      (dsp_mono2 hh hv hv7 2 2).2, (dsp_mono2 hh hv hv7 3 1).1, (dsp_mono2 hh hv hv7 3 1).2,
      (dsp_mono2 hh hv hv7 3 2).1, (dsp_mono2 hh hv hv7 3 2).2, (dsp_mono2 hh hv hv7 4 1).1,
      (dsp_mono2 hh hv hv7 4 1).2, (dsp_mono2 hh hv hv7 4 2).1, (dsp_mono2 hh hv hv7 4 2).2,
      (dsp_mono2 hh hv hv7 5 1).1, (dsp_mono2 hh hv hv7 5 1).2, (dsp_mono2 hh hv hv7 5 2).1,
      (dsp_mono2 hh hv hv7 5 2).2, (dsp_mono2 hh hv hv7 6 1).1, (dsp_mono2 hh hv hv7 6 1).2,
      (dsp_mono2 hh hv hv7 6 2).1, (dsp_mono2 hh hv hv7 6 2).2])

/-! ### The printed polynomials, in `h = x - 2`, `v = C - 3/5` -/

/-- The polynomial `T`: `P_n'''(1/x) = 3n(x - 1)T(h, v)/(1225S)` (`dspo_T_id`). -/
noncomputable def dspoT (h v : ℝ) : ℝ :=
    h ^ 3 * (300 * v + 480) +
    h ^ 2 * (-300 * v ^ 2 + 1315 * v + 2922) +
    h * (-1500 * v ^ 2 + 750 * v + 5215) +
    (-1800 * v ^ 2 - 1285 * v + 2677)

/-- The polynomial `B`: `A_3 + 4A_4/x = 2nB(h, v)/1225` (`dspo_B_id`). -/
noncomputable def dspoBq (h v : ℝ) : ℝ :=
    h ^ 3 * (100 * v + 160) +
    h ^ 2 * (-100 * v ^ 2 + 205 * v + 534) +
    h * (-300 * v ^ 2 - 60 * v + 397) +
    (-200 * v ^ 2 - 65 * v + 33)

/-- The polynomial `Vl`: `980xS(P_{5/2}''(1/x) - 2/5) = Vl(h, v)` (`dspo_Vl_id`). -/
noncomputable def dspoVl (h v : ℝ) : ℝ :=
    h ^ 5 * (-300) +
    h ^ 4 * (300 * v ^ 2 + 1260 * v - 1812) +
    h ^ 3 * (2100 * v ^ 2 + 9280 * v - 1953) +
    h ^ 2 * (5100 * v ^ 2 + 22990 * v + 4156) +
    h * (5100 * v ^ 2 + 22580 * v + 7667) +
    (1800 * v ^ 2 + 7130 * v + 2238)

/-- The polynomial `Vh`: `700xS(P_{7/2}''(1/x) - 2/5) = Vh(h, v)` (`dspo_Vh_id`). -/
noncomputable def dspoVh (h v : ℝ) : ℝ :=
    h ^ 5 * (-300) +
    h ^ 4 * (300 * v ^ 2 + 1260 * v - 2052) +
    h ^ 3 * (2100 * v ^ 2 + 9520 * v - 3869) +
    h ^ 2 * (5100 * v ^ 2 + 24670 * v - 1164) +
    h * (5100 * v ^ 2 + 26420 * v + 1791) +
    (1800 * v ^ 2 + 10010 * v + 278)

/-- The polynomial `El`: `245x(A_{5/2}''(1/x) + 1) = El(h, v)` (`dspo_El_id`). -/
noncomputable def dspoEl (h v : ℝ) : ℝ :=
    h ^ 4 * (300) +
    h ^ 3 * (100 * v ^ 2 + 20 * v + 2656) +
    h ^ 2 * (400 * v ^ 2 - 1100 * v + 7041) +
    h * (500 * v ^ 2 - 4170 * v + 6338) +
    (200 * v ^ 2 - 3630 * v + 1200)

/-- The polynomial `Eh`: `175x(A_{7/2}''(1/x) + 1) = Eh(h, v)` (`dspo_Eh_id`). -/
noncomputable def dspoEh (h v : ℝ) : ℝ :=
    h ^ 4 * (300) +
    h ^ 3 * (100 * v ^ 2 + 20 * v + 2576) +
    h ^ 2 * (400 * v ^ 2 - 1020 * v + 6669) +
    h * (500 * v ^ 2 - 3850 * v + 5760) +
    (200 * v ^ 2 - 3310 * v + 892)

/-- The polynomial `Fl`: `7840(A_{5/2}''(7/8) + 1) = Fl(h, v)` (`dspo_Fl_id`). -/
noncomputable def dspoFl (h v : ℝ) : ℝ :=
    h ^ 4 * (14700) +
    h ^ 3 * (-12600 * v + 80790) +
    h ^ 2 * (1100 * v ^ 2 - 53630 * v + 166286) +
    h * (400 * v ^ 2 - 94530 * v + 137933) +
    (-400 * v ^ 2 - 74100 * v + 23034)

/-- The polynomial `Fh`: `5600(A_{7/2}''(7/8) + 1) = Fh(h, v)` (`dspo_Fh_id`). -/
noncomputable def dspoFh (h v : ℝ) : ℝ :=
    h ^ 4 * (14700) +
    h ^ 3 * (-12600 * v + 80790) +
    h ^ 2 * (1100 * v ^ 2 - 53630 * v + 163726) +
    h * (400 * v ^ 2 - 91970 * v + 131149) +
    (-400 * v ^ 2 - 68980 * v + 18106)

/-- The polynomial `Gl`: `245x²(A_{5/2}'(1/x) - 1) = Gl(h, v)` (`dspo_Gl_id`). -/
noncomputable def dspoGl (h v : ℝ) : ℝ :=
    h ^ 4 * (150 * v + 240) +
    h ^ 3 * (1290 * v + 2159) +
    h ^ 2 * (3580 * v + 5953) +
    h * (3690 * v + 5494) +
    (1005 * v + 673)

/-- The polynomial `Gh`: `35x²(A_{7/2}'(1/x) - 1) = Gh(h, v)` (`dspo_Gh_id`). -/
noncomputable def dspoGh (h v : ℝ) : ℝ :=
    h ^ 4 * (30 * v + 48) +
    h ^ 3 * (250 * v + 405) +
    h ^ 2 * (690 * v + 1069) +
    h * (730 * v + 938) +
    (225 * v + 85)

/-- The polynomial `Hl`: `2007040(5 - A_{5/2}(7/8)) = Hl(h, v)` (`dspo_Hl_id`). -/
noncomputable def dspoHl (h v : ℝ) : ℝ :=
    h ^ 4 * (-240100) +
    h ^ 3 * (-68600 * v - 1993810) +
    h ^ 2 * (-4900 * v ^ 2 - 343630 * v - 6372394) +
    h * (-8400 * v ^ 2 - 730570 * v - 8863063) +
    (-3600 * v ^ 2 - 667820 * v + 3642234)

/-- The polynomial `Hh`: `1433600(5 - A_{7/2}(7/8)) = Hh(h, v)` (`dspo_Hh_id`). -/
noncomputable def dspoHh (h v : ℝ) : ℝ :=
    h ^ 4 * (-240100) +
    h ^ 3 * (-68600 * v - 1993810) +
    h ^ 2 * (-4900 * v ^ 2 - 343630 * v - 6121514) +
    h * (-8400 * v ^ 2 - 694730 * v - 7319639) +
    (-3600 * v ^ 2 - 565420 * v + 3715194)
theorem dspoT_pos {h v : ℝ} (hh : 0 ≤ h) (hh6 : h ≤ 1 / 6) (hv : 0 ≤ v) (hv7 : v ≤ 7 / 30) :
    0 < dspoT h v := by
  unfold dspoT; dsp_box

theorem dspoBq_pos {h v : ℝ} (hh : 0 ≤ h) (hh6 : h ≤ 1 / 6) (hv : 0 ≤ v) (hv7 : v ≤ 7 / 30) :
    0 < dspoBq h v := by
  unfold dspoBq; dsp_box

theorem dspoVl_pos {h v : ℝ} (hh : 0 ≤ h) (hh6 : h ≤ 1 / 6) (hv : 0 ≤ v) (hv7 : v ≤ 7 / 30) :
    0 < dspoVl h v := by
  unfold dspoVl; dsp_box

theorem dspoVh_pos {h v : ℝ} (hh : 0 ≤ h) (hh6 : h ≤ 1 / 6) (hv : 0 ≤ v) (hv7 : v ≤ 7 / 30) :
    0 < dspoVh h v := by
  unfold dspoVh; dsp_box

theorem dspoEl_pos {h v : ℝ} (hh : 0 ≤ h) (hh6 : h ≤ 1 / 6) (hv : 0 ≤ v) (hv7 : v ≤ 7 / 30) :
    0 < dspoEl h v := by
  unfold dspoEl; dsp_box

theorem dspoEh_pos {h v : ℝ} (hh : 0 ≤ h) (hh6 : h ≤ 1 / 6) (hv : 0 ≤ v) (hv7 : v ≤ 7 / 30) :
    0 < dspoEh h v := by
  unfold dspoEh; dsp_box

theorem dspoFl_pos {h v : ℝ} (hh : 0 ≤ h) (hh6 : h ≤ 1 / 6) (hv : 0 ≤ v) (hv7 : v ≤ 7 / 30) :
    0 < dspoFl h v := by
  unfold dspoFl; dsp_box

theorem dspoFh_pos {h v : ℝ} (hh : 0 ≤ h) (hh6 : h ≤ 1 / 6) (hv : 0 ≤ v) (hv7 : v ≤ 7 / 30) :
    0 < dspoFh h v := by
  unfold dspoFh; dsp_box

theorem dspoGl_pos {h v : ℝ} (hh : 0 ≤ h) (hh6 : h ≤ 1 / 6) (hv : 0 ≤ v) (hv7 : v ≤ 7 / 30) :
    0 < dspoGl h v := by
  unfold dspoGl; dsp_box

theorem dspoGh_pos {h v : ℝ} (hh : 0 ≤ h) (hh6 : h ≤ 1 / 6) (hv : 0 ≤ v) (hv7 : v ≤ 7 / 30) :
    0 < dspoGh h v := by
  unfold dspoGh; dsp_box

theorem dspoHl_pos {h v : ℝ} (hh : 0 ≤ h) (hh6 : h ≤ 1 / 6) (hv : 0 ≤ v) (hv7 : v ≤ 7 / 30) :
    0 < dspoHl h v := by
  unfold dspoHl; dsp_box

theorem dspoHh_pos {h v : ℝ} (hh : 0 ≤ h) (hh6 : h ≤ 1 / 6) (hv : 0 ≤ v) (hv7 : v ≤ 7 / 30) :
    0 < dspoHh h v := by
  unfold dspoHh; dsp_box

/-! ### The boundary identities -/

section Identities

variable {x C n : ℝ}

/-- `P_n'''(1/x) = 3n(x - 1)T(h, v)/(1225S)`. -/
theorem dspo_T_id (hx : 0 < x) :
    (6 * dspoPc3 x C n + 24 * dspoPc4 x C n * (1 / x)) * (1225 * (x + 1)) =
      3 * n * (x - 1) * dspoT (x - 2) (C - 3 / 5) := by
  unfold dspoPc3 dspoPc4 dspoAc3 dspoAc4 dspoα3 dspoα4 dspoγ3 dspoγ4 dspoT
  have : x + 1 ≠ 0 := by linarith
  field_simp
  ring

/-- `A_3 + 4A_4/x = 2nB(h, v)/1225`. -/
theorem dspo_B_id (hx : 0 < x) :
    (dspoAc3 x C n + 4 * dspoAc4 x C n / x) * 1225 = 2 * n * dspoBq (x - 2) (C - 3 / 5) := by
  unfold dspoAc3 dspoAc4 dspoα3 dspoα4 dspoBq
  field_simp
  ring

theorem dspo_Vl_id (hx : 0 < x) :
    (dspoP2 x C (5 / 2) (1 / x) - 2 / 5) * (980 * x * (x + 1)) = dspoVl (x - 2) (C - 3 / 5) := by
  unfold dspoP2 dspoPc2 dspoPc3 dspoPc4 dspoAc2 dspoAc3 dspoAc4 dspoα2 dspoα3 dspoα4 dspoβ2 dspoγ2
    dspoγ3 dspoγ4 dspoδ2 dspoVl
  have : x + 1 ≠ 0 := by linarith
  field_simp
  ring

theorem dspo_Vh_id (hx : 0 < x) :
    (dspoP2 x C (7 / 2) (1 / x) - 2 / 5) * (700 * x * (x + 1)) = dspoVh (x - 2) (C - 3 / 5) := by
  unfold dspoP2 dspoPc2 dspoPc3 dspoPc4 dspoAc2 dspoAc3 dspoAc4 dspoα2 dspoα3 dspoα4 dspoβ2 dspoγ2
    dspoγ3 dspoγ4 dspoδ2 dspoVh
  have : x + 1 ≠ 0 := by linarith
  field_simp
  ring

theorem dspo_El_id (hx : 0 < x) :
    (dspoA2 x C (5 / 2) (1 / x) + 1) * (245 * x) = dspoEl (x - 2) (C - 3 / 5) := by
  unfold dspoA2 dspoAc2 dspoAc3 dspoAc4 dspoα2 dspoα3 dspoα4 dspoβ2 dspoEl
  field_simp
  ring

theorem dspo_Eh_id (hx : 0 < x) :
    (dspoA2 x C (7 / 2) (1 / x) + 1) * (175 * x) = dspoEh (x - 2) (C - 3 / 5) := by
  unfold dspoA2 dspoAc2 dspoAc3 dspoAc4 dspoα2 dspoα3 dspoα4 dspoβ2 dspoEh
  field_simp
  ring

theorem dspo_Fl_id : (dspoA2 x C (5 / 2) (7 / 8) + 1) * 7840 = dspoFl (x - 2) (C - 3 / 5) := by
  unfold dspoA2 dspoAc2 dspoAc3 dspoAc4 dspoα2 dspoα3 dspoα4 dspoβ2 dspoFl
  ring

theorem dspo_Fh_id : (dspoA2 x C (7 / 2) (7 / 8) + 1) * 5600 = dspoFh (x - 2) (C - 3 / 5) := by
  unfold dspoA2 dspoAc2 dspoAc3 dspoAc4 dspoα2 dspoα3 dspoα4 dspoβ2 dspoFh
  ring

theorem dspo_Gl_id (hx : 0 < x) :
    (dspoA1 x C (5 / 2) (1 / x) - 1) * (245 * x ^ 2) = dspoGl (x - 2) (C - 3 / 5) := by
  unfold dspoA1 dspoAc1 dspoAc2 dspoAc3 dspoAc4 dspoα1 dspoα2 dspoα3 dspoα4 dspoβ1 dspoβ2 dspoGl
  field_simp
  ring

theorem dspo_Gh_id (hx : 0 < x) :
    (dspoA1 x C (7 / 2) (1 / x) - 1) * (35 * x ^ 2) = dspoGh (x - 2) (C - 3 / 5) := by
  unfold dspoA1 dspoAc1 dspoAc2 dspoAc3 dspoAc4 dspoα1 dspoα2 dspoα3 dspoα4 dspoβ1 dspoβ2 dspoGh
  field_simp
  ring

theorem dspo_Hl_id : (5 - dspoA x C (5 / 2) (7 / 8)) * 2007040 = dspoHl (x - 2) (C - 3 / 5) := by
  unfold dspoA dspoAc0 dspoAc1 dspoAc2 dspoAc3 dspoAc4 dspoα0 dspoα1 dspoα2 dspoα3 dspoα4 dspoβ0
    dspoβ1 dspoβ2 dspoHl
  ring

theorem dspo_Hh_id : (5 - dspoA x C (7 / 2) (7 / 8)) * 1433600 = dspoHh (x - 2) (C - 3 / 5) := by
  unfold dspoA dspoAc0 dspoAc1 dspoAc2 dspoAc3 dspoAc4 dspoα0 dspoα1 dspoα2 dspoα3 dspoα4 dspoβ0
    dspoβ1 dspoβ2 dspoHh
  ring

/-- The leading coefficient of `P_n`:
`nx(2(x - C) - 1)/49 · ((3/4)(2x(x - C - 1) - 1) + (x² + x + 1)/S)`. -/
theorem dspo_lead_id (hx : 0 < x) :
    dspoPc4 x C n = n * x * (2 * (x - C) - 1) / 49 *
      (3 / 4 * (2 * x * (x - C - 1) - 1) + (x ^ 2 + x + 1) / (x + 1)) := by
  unfold dspoPc4 dspoAc4 dspoα4 dspoγ4
  have : x + 1 ≠ 0 := by linarith
  field_simp
  ring

/-- `A_n(1/x)` decreases in `n`. -/
theorem dspo_An_id (hx : 0 < x) :
    dspoA x C n (1 / x) = dspoA x C (7 / 2) (1 / x) + (7 / 2 - n) * (x + 1) ^ 3 * (6 * x - 1) /
      (49 * x ^ 3) := by
  unfold dspoA dspoAc0 dspoAc1 dspoAc2 dspoAc3 dspoAc4 dspoα0 dspoα1 dspoα2 dspoα3 dspoα4 dspoβ0
    dspoβ1 dspoβ2
  field_simp
  ring

/-- `14x³(A_{7/2}(1/x) - 1) = 14Cx²(x - 1) + 6h⁴ + 53h³ + 153h² + 163h + 43`. -/
theorem dspo_A72_id (hx : 0 < x) :
    (dspoA x C (7 / 2) (1 / x) - 1) * (14 * x ^ 3) = 14 * C * x ^ 2 * (x - 1) +
      (6 * (x - 2) ^ 4 + 53 * (x - 2) ^ 3 + 153 * (x - 2) ^ 2 + 163 * (x - 2) + 43) := by
  unfold dspoA dspoAc0 dspoAc1 dspoAc2 dspoAc3 dspoAc4 dspoα0 dspoα1 dspoα2 dspoα3 dspoα4 dspoβ0
    dspoβ1 dspoβ2
  field_simp
  ring

end Identities

/-! ### Interpolation in the duration weight -/

/-- A convex combination of two values above `c` is above `c`. -/
theorem dsp_interp {w₁ w₂ Q₁ Q₂ c : ℝ} (h₁ : 0 ≤ w₁) (h₂ : 0 ≤ w₂) (hs : w₁ + w₂ = 1)
    (hQ₁ : c < Q₁) (hQ₂ : c < Q₂) : c < w₁ * Q₁ + w₂ * Q₂ := by
  have e : w₁ * Q₁ + w₂ * Q₂ - c = w₁ * (Q₁ - c) + w₂ * (Q₂ - c) := by linear_combination c * hs
  have h1 : 0 ≤ w₁ * (Q₁ - c) := mul_nonneg h₁ (by linarith)
  have h2 : 0 ≤ w₂ * (Q₂ - c) := mul_nonneg h₂ (by linarith)
  rcases eq_or_lt_of_le h₁ with e1 | e1
  · have : w₂ = 1 := by linarith
    subst this
    have : 0 < 1 * (Q₂ - c) := by linarith
    linarith
  · have : 0 < w₁ * (Q₁ - c) := mul_pos e1 (by linarith)
    linarith

/-- A convex combination of two values below `c` is below `c`. -/
theorem dsp_interp' {w₁ w₂ Q₁ Q₂ c : ℝ} (h₁ : 0 ≤ w₁) (h₂ : 0 ≤ w₂) (hs : w₁ + w₂ = 1)
    (hQ₁ : Q₁ < c) (hQ₂ : Q₂ < c) : w₁ * Q₁ + w₂ * Q₂ < c := by
  have := dsp_interp (c := -c) (Q₁ := -Q₁) (Q₂ := -Q₂) h₁ h₂ hs (by linarith) (by linarith)
  linarith

/-! ### The function `f(z) = -1/z² + 280/(5z + 14)²` on `[23/10, 3]` -/

/-- `f'' = -6/z⁴ + 42000/(5z + 14)⁴`. -/
noncomputable def dspof2 (z : ℝ) : ℝ := -6 / z ^ 4 + 42000 / (5 * z + 14) ^ 4

theorem dsp_hd_f {z : ℝ} (hz : 0 < z) : HasDerivAt dspof (dspof1 z) z := by
  have h5 : 5 * z + 14 ≠ 0 := by positivity
  have := ((hasDerivAt_const z (-1 : ℝ)).fun_div ((hasDerivAt_id z).fun_pow 2)
    (pow_ne_zero 2 hz.ne')).add
    ((hasDerivAt_const z (280 : ℝ)).fun_div ((((hasDerivAt_id z).const_mul 5).add_const 14).fun_pow 2)
      (pow_ne_zero 2 h5))
  unfold dspof dspof1
  refine this.congr_deriv ?_
  simp only [id]
  push_cast
  field_simp
  ring

theorem dsp_hd_f1 {z : ℝ} (hz : 0 < z) : HasDerivAt dspof1 (dspof2 z) z := by
  have h5 : 5 * z + 14 ≠ 0 := by positivity
  have := ((hasDerivAt_const z (2 : ℝ)).fun_div ((hasDerivAt_id z).fun_pow 3)
    (pow_ne_zero 3 hz.ne')).sub
    ((hasDerivAt_const z (2800 : ℝ)).fun_div ((((hasDerivAt_id z).const_mul 5).add_const 14).fun_pow 3)
      (pow_ne_zero 3 h5))
  unfold dspof1 dspof2
  refine this.congr_deriv ?_
  simp only [id]
  push_cast
  field_simp
  ring

/-- `f' < 0` on `[23/10, ∞)`: `(5z + 14)³ < 1400z³`, as `(255/23)³ < 1400`. -/
theorem dspof1_neg {z : ℝ} (hz : 23 / 10 ≤ z) : dspof1 z < 0 := by
  unfold dspof1
  have hz0 : 0 < z := by linarith
  have h1 : 23 * (5 * z + 14) ≤ 255 * z := by linarith
  have h2 : (23 * (5 * z + 14)) ^ 3 ≤ (255 * z) ^ 3 := pow_le_pow_left₀ (by positivity) h1 3
  have h3 : (5 * z + 14) ^ 3 < 1400 * z ^ 3 := by nlinarith [pow_pos hz0 3]
  rw [sub_neg, div_lt_div_iff₀ (by positivity) (by positivity)]
  nlinarith

/-- `f'' < 0` on `(0, 3]`: `7000z⁴ < (5z + 14)⁴`, as `(29/3)⁴ > 7000`. -/
theorem dspof2_neg {z : ℝ} (hz : 0 < z) (hz3 : z ≤ 3) : dspof2 z < 0 := by
  unfold dspof2
  have h1 : 29 * z ≤ 3 * (5 * z + 14) := by linarith
  have h2 : (29 * z) ^ 4 ≤ (3 * (5 * z + 14)) ^ 4 := pow_le_pow_left₀ (by positivity) h1 4
  have h3 : 7000 * z ^ 4 < (5 * z + 14) ^ 4 := by nlinarith [pow_pos hz 4]
  have h4 : 42000 / (5 * z + 14) ^ 4 < 6 / z ^ 4 := by
    rw [div_lt_div_iff₀ (by positivity) (by positivity)]; nlinarith
  have h5 : -6 / z ^ 4 = -(6 / z ^ 4) := neg_div _ _
  linarith

/-- `f` decreases on `[23/10, ∞)`. -/
theorem dspof_anti {z₁ z₂ : ℝ} (h1 : 23 / 10 ≤ z₁) (h12 : z₁ ≤ z₂) : dspof z₂ ≤ dspof z₁ := by
  have := ss_le_of_deriv (f := fun t => -dspof t) (f' := fun t => -dspof1 t) h12
    (fun t ht => (dsp_hd_f (by linarith [ht.1])).neg)
    (fun t ht => by linarith [dspof1_neg (z := t) (by linarith [ht.1])])
  linarith

/-- `f(z) < 121/500` on `[23/10, ∞)` (`f(23/10) = 121/500 - 297409/687964500`). -/
theorem dspof_lt {z : ℝ} (hz : 23 / 10 ≤ z) : dspof z < 121 / 500 := by
  have := dspof_anti (le_refl (23 / 10 : ℝ)) hz
  have e : dspof (23 / 10) = 121 / 500 - 297409 / 687964500 := by unfold dspof; norm_num
  linarith

/-- `f(z) ≥ f(3) = 1679/7569` on `[23/10, 3]`. -/
theorem dspof_ge {z : ℝ} (hz : 23 / 10 ≤ z) (hz3 : z ≤ 3) : 1679 / 7569 ≤ dspof z := by
  have := dspof_anti hz hz3
  have e : dspof 3 = 1679 / 7569 := by unfold dspof; norm_num
  linarith

/-- `f(z) < 8/35` on `[17/6, ∞)`. -/
theorem dspof_lt' {z : ℝ} (hz : 17 / 6 ≤ z) : dspof z < 8 / 35 := by
  have := dspof_anti (by norm_num : (23 / 10 : ℝ) ≤ 17 / 6) hz
  have e : dspof (17 / 6) = 1884924 / 8254129 := by unfold dspof; norm_num
  linarith

/-- `f'(z) ≥ f'(3) = -26822/658503` on `(0, 3]`. -/
theorem dspof1_ge {z : ℝ} (hz : 0 < z) (hz3 : z ≤ 3) : -(26822 / 658503) ≤ dspof1 z := by
  have := ss_le_of_deriv (f := fun t => -dspof1 t) (f' := fun t => -dspof2 t) hz3
    (fun t ht => (dsp_hd_f1 (by linarith [ht.1])).neg)
    (fun t ht => by linarith [dspof2_neg (z := t) (by linarith [ht.1]) ht.2.le])
  have e : dspof1 3 = -(26822 / 658503) := by unfold dspof1; norm_num
  linarith

/-! ### The bounds on the comparison rectangle -/

section Rect

variable {x C n r : ℝ}

/-- `P_n'' > 2/5` for `r ≥ 1/x`, from its value and its slope at `r = 1/x` and the leading
coefficient. -/
theorem dspo_P2_gt (hx : 2 ≤ x) (hx2 : x ≤ 13 / 6) (hC : 3 / 5 ≤ C) (hC' : C ≤ 5 / 6) (hn : 5 / 2 ≤ n)
    (hn' : n ≤ 7 / 2) (hr : 1 / x ≤ r) : 2 / 5 < dspoP2 x C n r := by
  have hx0 : 0 < x := by linarith
  have hh : 0 ≤ x - 2 := by linarith
  have hh6 : x - 2 ≤ 1 / 6 := by linarith
  have hv : 0 ≤ C - 3 / 5 := by linarith
  have hv7 : C - 3 / 5 ≤ 7 / 30 := by linarith
  -- the boundary value, by affinity in `n`
  have hP2 : 2 / 5 < dspoP2 x C n (1 / x) := by
    have e : dspoP2 x C n (1 / x) = (7 / 2 - n) * dspoP2 x C (5 / 2) (1 / x) +
        (n - 5 / 2) * dspoP2 x C (7 / 2) (1 / x) := by
      unfold dspoP2 dspoPc2 dspoPc3 dspoPc4 dspoAc2 dspoAc3 dspoAc4; ring
    have hl : 2 / 5 < dspoP2 x C (5 / 2) (1 / x) := by
      have := dspoVl_pos hh hh6 hv hv7
      rw [← dspo_Vl_id hx0] at this
      have := pos_of_mul_pos_left this (by positivity)
      linarith
    have hh' : 2 / 5 < dspoP2 x C (7 / 2) (1 / x) := by
      have := dspoVh_pos hh hh6 hv hv7
      rw [← dspo_Vh_id hx0] at this
      have := pos_of_mul_pos_left this (by positivity)
      linarith
    rw [e]
    exact dsp_interp (by linarith) (by linarith) (by ring) hl hh'
  -- the third derivative and the leading coefficient
  have hP3 : 0 < 6 * dspoPc3 x C n + 24 * dspoPc4 x C n * (1 / x) := by
    have := dspoT_pos hh hh6 hv hv7
    have h2 := dspo_T_id (x := x) (C := C) (n := n) hx0
    have : 0 < (6 * dspoPc3 x C n + 24 * dspoPc4 x C n * (1 / x)) * (1225 * (x + 1)) := by
      rw [h2]; have : 0 < x - 1 := by linarith
      positivity
    exact pos_of_mul_pos_left this (by positivity)
  have hP4 : 0 < dspoPc4 x C n := by
    rw [dspo_lead_id hx0]
    have h1 : 0 < 2 * (x - C) - 1 := by linarith
    have h2 : 7 / 3 ≤ (x ^ 2 + x + 1) / (x + 1) := by
      rw [le_div_iff₀ (by linarith)]; nlinarith
    have h3 : 0 < 3 / 4 * (2 * x * (x - C - 1) - 1) + (x ^ 2 + x + 1) / (x + 1) := by
      have : 0 ≤ 2 * x * (x - C - 1) := by
        have : 0 ≤ x - C - 1 := by linarith
        positivity
      linarith
    have : 0 < n := by linarith
    positivity
  -- Taylor at `1/x`
  have e : dspoP2 x C n r = dspoP2 x C n (1 / x) +
      (6 * dspoPc3 x C n + 24 * dspoPc4 x C n * (1 / x)) * (r - 1 / x) +
      12 * dspoPc4 x C n * (r - 1 / x) ^ 2 := by
    unfold dspoP2; ring
  rw [e]
  have : 0 ≤ (6 * dspoPc3 x C n + 24 * dspoPc4 x C n * (1 / x)) * (r - 1 / x) :=
    mul_nonneg hP3.le (by linarith)
  have : 0 ≤ 12 * dspoPc4 x C n * (r - 1 / x) ^ 2 := by positivity
  linarith

/-- `A_n'' > -1` on `[1/x, 7/8]`. -/
theorem dspo_A2_gt (hx : 2 ≤ x) (hx2 : x ≤ 13 / 6) (hC : 3 / 5 ≤ C) (hC' : C ≤ 5 / 6) (hn : 5 / 2 ≤ n)
    (hn' : n ≤ 7 / 2) (hr : 1 / x ≤ r) (hr' : r ≤ 7 / 8) : -1 < dspoA2 x C n r := by
  have hx0 : 0 < x := by linarith
  have hh : 0 ≤ x - 2 := by linarith
  have hh6 : x - 2 ≤ 1 / 6 := by linarith
  have hv : 0 ≤ C - 3 / 5 := by linarith
  have hv7 : C - 3 / 5 ≤ 7 / 30 := by linarith
  have hx12 : 1 / x ≤ 1 / 2 := by rw [div_le_div_iff₀ hx0 (by norm_num)]; linarith
  have hA0 : -1 < dspoA2 x C n (1 / x) := by
    have e : dspoA2 x C n (1 / x) = (7 / 2 - n) * dspoA2 x C (5 / 2) (1 / x) +
        (n - 5 / 2) * dspoA2 x C (7 / 2) (1 / x) := by
      unfold dspoA2 dspoAc2 dspoAc3 dspoAc4; ring
    have hl : -1 < dspoA2 x C (5 / 2) (1 / x) := by
      have := dspoEl_pos hh hh6 hv hv7
      rw [← dspo_El_id hx0] at this
      have := pos_of_mul_pos_left this (by positivity)
      linarith
    have hh' : -1 < dspoA2 x C (7 / 2) (1 / x) := by
      have := dspoEh_pos hh hh6 hv hv7
      rw [← dspo_Eh_id hx0] at this
      have := pos_of_mul_pos_left this (by positivity)
      linarith
    rw [e]
    exact dsp_interp (by linarith) (by linarith) (by ring) hl hh'
  have hA1 : -1 < dspoA2 x C n (7 / 8) := by
    have e : dspoA2 x C n (7 / 8) = (7 / 2 - n) * dspoA2 x C (5 / 2) (7 / 8) +
        (n - 5 / 2) * dspoA2 x C (7 / 2) (7 / 8) := by
      unfold dspoA2 dspoAc2 dspoAc3 dspoAc4; ring
    have hl : -1 < dspoA2 x C (5 / 2) (7 / 8) := by
      have := dspoFl_pos hh hh6 hv hv7
      rw [← dspo_Fl_id] at this
      linarith
    have hh' : -1 < dspoA2 x C (7 / 2) (7 / 8) := by
      have := dspoFh_pos hh hh6 hv hv7
      rw [← dspo_Fh_id] at this
      linarith
    rw [e]
    exact dsp_interp (by linarith) (by linarith) (by ring) hl hh'
  have hB : 0 < dspoAc3 x C n + 4 * dspoAc4 x C n / x := by
    have := dspoBq_pos hh hh6 hv hv7
    have h2 := dspo_B_id (x := x) (C := C) (n := n) hx0
    have : 0 < (dspoAc3 x C n + 4 * dspoAc4 x C n / x) * 1225 := by
      rw [h2]; have : 0 < n := by linarith
      positivity
    linarith
  rcases le_or_gt 0 (dspoAc4 x C n) with h4 | h4
  · -- `A''` increases on `[1/x, ∞)`
    have e : dspoA2 x C n r = dspoA2 x C n (1 / x) +
        (r - 1 / x) * (6 * (dspoAc3 x C n + 4 * dspoAc4 x C n / x) +
          12 * dspoAc4 x C n * (r - 1 / x)) := by
      unfold dspoA2; field_simp; ring
    rw [e]
    have : 0 ≤ (r - 1 / x) * (6 * (dspoAc3 x C n + 4 * dspoAc4 x C n / x) +
        12 * dspoAc4 x C n * (r - 1 / x)) := by
      apply mul_nonneg (by linarith)
      have : 0 ≤ 12 * dspoAc4 x C n * (r - 1 / x) := mul_nonneg (by linarith) (by linarith)
      linarith
    linarith
  · -- `A''` is concave: above its chord
    have e : (7 / 8 - 1 / x) * dspoA2 x C n r = (7 / 8 - r) * dspoA2 x C n (1 / x) +
        (r - 1 / x) * dspoA2 x C n (7 / 8) -
        12 * dspoAc4 x C n * (r - 1 / x) * (7 / 8 - r) * (7 / 8 - 1 / x) := by
      unfold dspoA2; ring
    have h1 : 0 ≤ -(12 * dspoAc4 x C n * (r - 1 / x) * (7 / 8 - r) * (7 / 8 - 1 / x)) := by
      have : 0 ≤ (r - 1 / x) * (7 / 8 - r) * (7 / 8 - 1 / x) :=
        mul_nonneg (mul_nonneg (by linarith) (by linarith)) (by linarith)
      nlinarith
    have h2 : (7 / 8 - r) * (-1) ≤ (7 / 8 - r) * dspoA2 x C n (1 / x) :=
      mul_le_mul_of_nonneg_left hA0.le (by linarith)
    have h3 : (r - 1 / x) * (-1) ≤ (r - 1 / x) * dspoA2 x C n (7 / 8) :=
      mul_le_mul_of_nonneg_left hA1.le (by linarith)
    have h5 : 0 < 7 / 8 - 1 / x := by linarith
    by_contra hc
    rw [not_lt] at hc
    have h6 : (7 / 8 - 1 / x) * dspoA2 x C n r ≤ (7 / 8 - 1 / x) * (-1) :=
      mul_le_mul_of_nonneg_left hc h5.le
    rcases eq_or_lt_of_le (show 1 / x ≤ r from hr) with hr0 | hr0
    · subst hr0; linarith
    · have h7 : (r - 1 / x) * (-1) < (r - 1 / x) * dspoA2 x C n (7 / 8) :=
        mul_lt_mul_of_pos_left hA1 (by linarith)
      linarith

/-- `1 < A_n < 5`, `A_n' > 0` on `[1/x, 7/8]`. -/
theorem dspo_A_bds (hx : 2 ≤ x) (hx2 : x ≤ 13 / 6) (hC : 3 / 5 ≤ C) (hC' : C ≤ 5 / 6) (hn : 5 / 2 ≤ n)
    (hn' : n ≤ 7 / 2) (hr : 1 / x ≤ r) (hr' : r ≤ 7 / 8) :
    1 < dspoA x C n r ∧ dspoA x C n r < 5 ∧ 0 < dspoA1 x C n r := by
  have hx0 : 0 < x := by linarith
  have hh : 0 ≤ x - 2 := by linarith
  have hh6 : x - 2 ≤ 1 / 6 := by linarith
  have hv : 0 ≤ C - 3 / 5 := by linarith
  have hv7 : C - 3 / 5 ≤ 7 / 30 := by linarith
  have hx12 : 1 / x ≤ 1 / 2 := by rw [div_le_div_iff₀ hx0 (by norm_num)]; linarith
  -- `A'(1/x) > 1`
  have hG : 1 < dspoA1 x C n (1 / x) := by
    have e : dspoA1 x C n (1 / x) = (7 / 2 - n) * dspoA1 x C (5 / 2) (1 / x) +
        (n - 5 / 2) * dspoA1 x C (7 / 2) (1 / x) := by
      unfold dspoA1 dspoAc1 dspoAc2 dspoAc3 dspoAc4; ring
    have hl : 1 < dspoA1 x C (5 / 2) (1 / x) := by
      have := dspoGl_pos hh hh6 hv hv7
      rw [← dspo_Gl_id hx0] at this
      have := pos_of_mul_pos_left this (by positivity)
      linarith
    have hh' : 1 < dspoA1 x C (7 / 2) (1 / x) := by
      have := dspoGh_pos hh hh6 hv hv7
      rw [← dspo_Gh_id hx0] at this
      have := pos_of_mul_pos_left this (by positivity)
      linarith
    rw [e]
    exact dsp_interp (by linarith) (by linarith) (by ring) hl hh'
  -- `A' + r` increases (`A'' > -1`), so `A' > 1 - (r - 1/x) > 0` on `[1/x, 7/8]`
  have hA1 : ∀ t ∈ Icc (1 / x) (7 / 8), 0 < dspoA1 x C n t := by
    intro t ht
    have := ss_le_of_deriv (f := fun s => dspoA1 x C n s + s) (f' := fun s => dspoA2 x C n s + 1) ht.1
      (fun s _ => (dspo_hd_A1 (x := x) (C := C) (n := n) (t := s)).add (hasDerivAt_id s))
      (fun s hs => by linarith [dspo_A2_gt hx hx2 hC hC' hn hn' hs.1.le (hs.2.le.trans ht.2)])
    have : 0 < 1 / x := by positivity
    linarith [ht.2]
  -- `A(1/x) > 1`
  have hA0 : 1 < dspoA x C n (1 / x) := by
    rw [dspo_An_id hx0]
    have h1 : 0 < (dspoA x C (7 / 2) (1 / x) - 1) * (14 * x ^ 3) := by
      rw [dspo_A72_id hx0]
      have : 0 ≤ 14 * C * x ^ 2 * (x - 1) := by
        have : 0 ≤ x - 1 := by linarith
        positivity
      have : 0 < 6 * (x - 2) ^ 4 + 53 * (x - 2) ^ 3 + 153 * (x - 2) ^ 2 + 163 * (x - 2) + 43 := by
        positivity
      linarith
    have h2 := pos_of_mul_pos_left h1 (by positivity)
    have h3 : 0 ≤ (7 / 2 - n) * (x + 1) ^ 3 * (6 * x - 1) / (49 * x ^ 3) := by
      apply div_nonneg _ (by positivity)
      apply mul_nonneg (mul_nonneg (by linarith) (by positivity)) (by linarith)
    linarith
  -- `A(7/8) < 5`
  have hA7 : dspoA x C n (7 / 8) < 5 := by
    have e : dspoA x C n (7 / 8) = (7 / 2 - n) * dspoA x C (5 / 2) (7 / 8) +
        (n - 5 / 2) * dspoA x C (7 / 2) (7 / 8) := by
      unfold dspoA dspoAc0 dspoAc1 dspoAc2 dspoAc3 dspoAc4; ring
    have hl : dspoA x C (5 / 2) (7 / 8) < 5 := by
      have := dspoHl_pos hh hh6 hv hv7
      rw [← dspo_Hl_id] at this
      linarith
    have hh' : dspoA x C (7 / 2) (7 / 8) < 5 := by
      have := dspoHh_pos hh hh6 hv hv7
      rw [← dspo_Hh_id] at this
      linarith
    rw [e]
    exact dsp_interp' (by linarith) (by linarith) (by ring) hl hh'
  have hmono : ∀ s t, 1 / x ≤ s → s ≤ t → t ≤ 7 / 8 → dspoA x C n s ≤ dspoA x C n t := by
    intro s t hs hst ht
    exact ss_le_of_deriv hst (fun z _ => dspo_hd_A (x := x) (C := C) (n := n) (t := z))
      (fun z hz => (hA1 z ⟨hs.trans hz.1.le, hz.2.le.trans ht⟩).le)
  refine ⟨?_, ?_, hA1 r ⟨hr, hr'⟩⟩
  · linarith [hmono (1 / x) r le_rfl hr hr']
  · linarith [hmono r (7 / 8) hr hr' le_rfl]

/-- `H = C + (x - C - 1)r ≥ 4/5` and `23/10 ≤ Z ≤ 3` on the rectangle. -/
theorem dspo_HZ (hx : 2 ≤ x) (hx2 : x ≤ 13 / 6) (hC : 3 / 5 ≤ C) (hC' : C ≤ 5 / 6)
    (hr : 1 / x ≤ r) (hr' : r ≤ 7 / 8) :
    4 / 5 ≤ C + (x - C - 1) * r ∧ 23 / 10 ≤ 1 + C + (x - C) * r ∧ 1 + C + (x - C) * r ≤ 3 := by
  have hx0 : 0 < x := by linarith
  have hxr : 1 ≤ x * r := by rwa [div_le_iff₀ hx0, mul_comm] at hr
  refine ⟨?_, ?_, ?_⟩
  · nlinarith [mul_le_mul_of_nonneg_left hxr (by linarith : (0 : ℝ) ≤ x - C - 1)]
  · nlinarith [mul_le_mul_of_nonneg_left hxr (by linarith : (0 : ℝ) ≤ x - C)]
  · nlinarith [mul_le_mul_of_nonneg_left hr' (by linarith : (0 : ℝ) ≤ x - C)]

/-- `0 ≤ V ≤ 2c ≤ 1/100`, `V' ≥ 0`, `V'' ≥ -1/125`. -/
theorem dspo_V_bds (hx : 2 ≤ x) (hx2 : x ≤ 13 / 6) (hC : 3 / 5 ≤ C) (hC' : C ≤ 5 / 6)
    (hr : 1 / x ≤ r) (hr' : r ≤ 7 / 8) :
    0 ≤ dspoV x C r ∧ dspoV x C r ≤ 1 / 100 ∧ 0 ≤ dspoV1 x C r ∧ -(1 / 125) ≤ dspoV2 x C r := by
  obtain ⟨hH, -, -⟩ := dspo_HZ hx hx2 hC hC' hr hr'
  have hr0 : 0 ≤ r := le_trans (by positivity) hr
  have hc0 : 0 ≤ dspoc x := by unfold dspoc; positivity
  have hc : dspoc x ≤ 1 / 200 := by
    unfold dspoc
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]
    nlinarith [mul_nonneg (sub_nonneg.2 hx) (sub_nonneg.2 hx2)]
  have hH0 : 0 < C + (x - C - 1) * r := by linarith
  refine ⟨?_, ?_, ?_, ?_⟩
  · unfold dspoV
    have : 0 ≤ dspoc x * (x - 1) * r / (C + (x - C - 1) * r) := by
      apply div_nonneg _ hH0.le
      have : 0 ≤ x - 1 := by linarith
      positivity
    linarith
  · unfold dspoV
    have : dspoc x * (x - 1) * r / (C + (x - C - 1) * r) ≤ dspoc x := by
      rw [div_le_iff₀ hH0]
      have : (x - 1) * r ≤ C + (x - C - 1) * r := by nlinarith
      nlinarith [mul_le_mul_of_nonneg_left this hc0]
    linarith
  · unfold dspoV1
    have : 0 ≤ x - 1 := by linarith
    have : 0 ≤ C := by linarith
    positivity
  · have e : dspoV2 x C r = -(2 * dspoc x * (x - 1) * C * (x - C - 1) / (C + (x - C - 1) * r) ^ 3) := by
      unfold dspoV2; ring
    rw [e]
    have hd : 0 ≤ x - C - 1 := by linarith
    have hCd : C * (x - C - 1) ≤ 49 / 144 := by nlinarith [sq_nonneg (C - (x - C - 1))]
    have hcx : dspoc x * (x - 1) ≤ 1 / 200 * (7 / 6) :=
      mul_le_mul hc (by linarith) (by linarith) (by norm_num)
    have hH3 : (4 / 5) ^ 3 ≤ (C + (x - C - 1) * r) ^ 3 := pow_le_pow_left₀ (by norm_num) hH 3
    have hnum : 2 * dspoc x * (x - 1) * C * (x - C - 1) ≤ 2 * (1 / 200 * (7 / 6)) * (49 / 144) := by
      have h1 : 0 ≤ dspoc x * (x - 1) := by
        have : 0 ≤ x - 1 := by linarith
        positivity
      have h2 : 0 ≤ C * (x - C - 1) := mul_nonneg (by linarith) hd
      nlinarith [mul_le_mul hcx hCd h2 (by norm_num)]
    rw [neg_le_neg_iff, div_le_iff₀ (by positivity)]
    nlinarith

/-- `[1/Z - 56/K]'' = (x - C)²f'(Z) > -1/10`. -/
theorem dspo_Phi2_gt (hx : 2 ≤ x) (hx2 : x ≤ 13 / 6) (hC : 3 / 5 ≤ C) (hC' : C ≤ 5 / 6)
    (hr : 1 / x ≤ r) (hr' : r ≤ 7 / 8) :
    -(1 / 10) < (x - C) ^ 2 * dspof1 (1 + C + (x - C) * r) := by
  obtain ⟨-, hZ1, hZ2⟩ := dspo_HZ hx hx2 hC hC' hr hr'
  have h1 := dspof1_ge (z := 1 + C + (x - C) * r) (by linarith) hZ2
  have h2 := dspof1_neg (z := 1 + C + (x - C) * r) hZ1
  have he : (x - C) ^ 2 ≤ (47 / 30) ^ 2 := pow_le_pow_left₀ (by linarith) (by linarith) 2
  have : (47 / 30) ^ 2 * dspof1 (1 + C + (x - C) * r) ≤ (x - C) ^ 2 * dspof1 (1 + C + (x - C) * r) :=
    mul_le_mul_of_nonpos_right he h2.le
  nlinarith

/-- **Uniform convexity** `G'' > 0` on the rectangle, from the bounds above. -/
theorem dspo_G2_pos (hx : 2 ≤ x) (hx2 : x ≤ 13 / 6) (hC : 3 / 5 ≤ C) (hC' : C ≤ 5 / 6)
    (hn : 5 / 2 ≤ n) (hn' : n ≤ 7 / 2) (hr : 1 / x ≤ r) (hr' : r ≤ 7 / 8) : 0 < dspoG2 x C n r := by
  have hP := dspo_P2_gt hx hx2 hC hC' hn hn' hr
  obtain ⟨hA1, hA5, hA1'⟩ := dspo_A_bds hx hx2 hC hC' hn hn' hr hr'
  have hA2 := dspo_A2_gt hx hx2 hC hC' hn hn' hr hr'
  obtain ⟨hV0, hV1, hV1', hV2⟩ := dspo_V_bds hx hx2 hC hC' hr hr'
  have hF := dspo_Phi2_gt hx hx2 hC hC' hr hr'
  unfold dspoG2
  have e1 : -(1 / 125) * dspoA x C n r ≤ dspoV2 x C r * dspoA x C n r :=
    mul_le_mul_of_nonneg_right hV2 (by linarith)
  have e2 : 0 ≤ 2 * dspoV1 x C r * dspoA1 x C n r := by positivity
  have e3 : dspoV x C r * (-1) ≤ dspoV x C r * dspoA2 x C n r := mul_le_mul_of_nonneg_left hA2.le hV0
  linarith

/-- **Negative between two negative shapes** (by convexity): for `1/x ≤ r₁ ≤ r ≤ r₂ ≤ 7/8`. -/
theorem dspo_neg_between {r₁ r₂ : ℝ} (hx : 2 ≤ x) (hx2 : x ≤ 13 / 6) (hC : 3 / 5 ≤ C)
    (hC' : C ≤ 5 / 6) (hn : 5 / 2 ≤ n) (hn' : n ≤ 7 / 2) (h1 : 1 / x ≤ r₁) (h2 : r₂ ≤ 7 / 8)
    (hr : r ∈ Icc r₁ r₂) (hg1 : dspoG x C n r₁ < 0) (hg2 : dspoG x C n r₂ < 0) :
    dspoG x C n r < 0 := by
  have hdom : ∀ t ∈ Icc r₁ r₂, 1 / x ≤ t ∧ t ≤ 7 / 8 := fun t ht => ⟨h1.trans ht.1, ht.2.trans h2⟩
  refine dsp_neg_of_convex (g' := dspoG1 x C n) (g'' := dspoG2 x C n) (fun t ht => ?_)
    (fun t ht => ?_) (fun t ht => ?_) hg1 hg2 hr
  · obtain ⟨hH, hZ, -⟩ := dspo_HZ hx hx2 hC hC' (hdom t ht).1 (hdom t ht).2
    exact dspo_hd_G (by linarith) (by linarith)
  · obtain ⟨hH, hZ, -⟩ := dspo_HZ hx hx2 hC hC' (hdom t ht).1 (hdom t ht).2
    exact dspo_hd_G1 (by linarith) (by linarith)
  · exact (dspo_G2_pos hx hx2 hC hC' hn hn' (hdom t ht).1 (hdom t ht).2).le

end Rect

end SmoothedOctagon
