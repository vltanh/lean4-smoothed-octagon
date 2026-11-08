module

public import SmoothedOctagon.Exclusion.Mixed.FwdHand.HighRatioLower
public import SmoothedOctagon.Exclusion.Mixed.FwdHand.LowTTools

/-!
# Case M2, forward successor by hand: the low-`t` residual with the new multipliers

`docs/lighter-proofs/NONSHORT_LOW_T_SHAPE.md` (5), (9) and `NONSHORT_LOW_T_CURVATURE.md` §1 (PR #2,
branch `proof/lighter-signs`). In the low-`t` large-gap branch (`1/3 ≤ t ≤ 3/8`) the combined
residual is taken with the multipliers `a = 7/2 - 10(q - 1)` (`nltAl`) and
`m = 8j + 8(q - 1) - 1/6` (`nltM`), the incoming majorant `V_L = hrlVL` (`T_L = (912 - 401x)/(24D)`),
the logarithm majorant `L₊` and the floor `F_ℓ`. At the unit shape `k = 1` its positive multiple
`S = 24(q + 1)WD · fhComb` (`W = 1 + x`, `D = 17x + 76`) is the source circuit (C3)
`S = 24WD(q + 1)C + 4(q + 1)AV_n - 16W²DpqB(q² + 10q + 1)` (`nltS`, `nlt_link`), whose coefficients
in `y = q - 1` are the bivariate polynomials `nltSt0`, …, `nltSt6` (`nlt_S_split`).

## Main API

* `nltAl`, `nltM`; `nltA0`, …, `nltC5`; `nltS`, `nlt_link`.
* `nltSt0`, …, `nltSt6`, `nlt_S_split`.
-/

@[expose] public section

namespace SmoothedOctagon

/-- The multiplier `a = 7/2 - 10(q - 1)` (`NONSHORT_LOW_T_SHAPE` (5)). -/
noncomputable def nltAl (q : ℝ) : ℝ := 7 / 2 - 10 * (q - 1)

/-- The multiplier `m = 8j + 8(q - 1) - 1/6`, `j = 2t + x - 1` (`NONSHORT_LOW_T_SHAPE` (5)). -/
noncomputable def nltM (t x q : ℝ) : ℝ := 8 * (2 * t + x - 1) + 8 * (q - 1) - 1 / 6

/-- `A_0` of `NONSHORT_LOW_T_CURVATURE` (C2). -/
noncomputable def nltA0 (t x : ℝ) : ℝ :=
  t * x + t ^ 2 + 4 * t * x ^ 2 + 4 * t ^ 2 * x + 6 * t * x ^ 3 + 6 * t ^ 2 * x ^ 2 + 4 * t * x ^ 4 + 4 * t ^ 2 * x ^ 3 + t * x ^ 5 + t ^ 2 * x ^ 4

/-- `A_1` of `NONSHORT_LOW_T_CURVATURE` (C2). -/
noncomputable def nltA1 (t x : ℝ) : ℝ :=
  (97 / 6) + (49 / 6) * x - 16 * t - 8 * x ^ 2 - 18 * t * x - t ^ 2 - 7 * t * x ^ 2 - 3 * t ^ 2 * x - 9 * t * x ^ 3 - 3 * t ^ 2 * x ^ 2 - 5 * t * x ^ 4 - t ^ 2 * x ^ 3 - t * x ^ 5

/-- `A_2` of `NONSHORT_LOW_T_CURVATURE` (C2). -/
noncomputable def nltA2 (t x : ℝ) : ℝ :=
  -8 + (11 / 2) * x - t + 27 * x ^ 2 - (33 / 2) * t * x + (27 / 2) * x ^ 3 + (19 / 2) * t * x ^ 2 + 25 * t ^ 2 * x + 77 * t * x ^ 3 + 48 * t ^ 2 * x ^ 2 + (129 / 2) * t * x ^ 4 + 21 * t ^ 2 * x ^ 3 + (25 / 2) * t * x ^ 5 - 2 * t ^ 2 * x ^ 4

/-- `A_3` of `NONSHORT_LOW_T_CURVATURE` (C2). -/
noncomputable def nltA3 (t x : ℝ) : ℝ :=
  -37 * x + t - (121 / 2) * x ^ 2 + 11 * t * x - (47 / 2) * x ^ 3 - 60 * t * x ^ 2 - 16 * t ^ 2 * x - 160 * t * x ^ 3 - 34 * t ^ 2 * x ^ 2 - (225 / 2) * t * x ^ 4 - 18 * t ^ 2 * x ^ 3 - (45 / 2) * t * x ^ 5

/-- `A_4` of `NONSHORT_LOW_T_CURVATURE` (C2). -/
noncomputable def nltA4 (t x : ℝ) : ℝ :=
  20 * x + 30 * x ^ 2 + t * x + 10 * x ^ 3 + 43 * t * x ^ 2 + t ^ 2 * x + 79 * t * x ^ 3 - 3 * t ^ 2 * x ^ 2 - 2 * t ^ 3 * x + 49 * t * x ^ 4 + t ^ 2 * x ^ 3 + 10 * t * x ^ 5 + t ^ 2 * x ^ 4

/-- `B_0` of `NONSHORT_LOW_T_CURVATURE` (C2). -/
noncomputable def nltB0 (t x : ℝ) : ℝ :=
  -(97 / 6) + 8 * x + (3 / 2) * t - 29 * t * x - 29 * t * x ^ 2 - 29 * t ^ 2 * x - 29 * t * x ^ 3 - 58 * t ^ 2 * x ^ 2 - (29 / 2) * t * x ^ 4 - 29 * t ^ 2 * x ^ 3

/-- `B_1` of `NONSHORT_LOW_T_CURVATURE` (C2). -/
noncomputable def nltB1 (t x : ℝ) : ℝ :=
  8 + (49 / 2) * t + 49 * t * x + 49 * t * x ^ 2 + 49 * t ^ 2 * x + 49 * t * x ^ 3 + 98 * t ^ 2 * x ^ 2 + (49 / 2) * t * x ^ 4 + 49 * t ^ 2 * x ^ 3

/-- `B_2` of `NONSHORT_LOW_T_CURVATURE` (C2). -/
noncomputable def nltB2 (t x : ℝ) : ℝ :=
  -10 * t - 18 * t * x + t ^ 2 - 19 * t * x ^ 2 - 20 * t ^ 2 * x - 18 * t * x ^ 3 - 35 * t ^ 2 * x ^ 2 + 2 * t ^ 3 * x - 9 * t * x ^ 4 - 18 * t ^ 2 * x ^ 3

/-- `B_3` of `NONSHORT_LOW_T_CURVATURE` (C2). -/
noncomputable def nltB3 (t x : ℝ) : ℝ :=
  -2 * t * x - t ^ 2 - t * x ^ 2 - 2 * t * x ^ 3 - 5 * t ^ 2 * x ^ 2 - 2 * t ^ 3 * x - t * x ^ 4 - 2 * t ^ 2 * x ^ 3

/-- `C_0` of `NONSHORT_LOW_T_CURVATURE` (C2). -/
noncomputable def nltC0 (t x : ℝ) : ℝ :=
  -3 * t * x - 3 * t ^ 2 - 15 * t * x ^ 2 - 15 * t ^ 2 * x - 30 * t * x ^ 3 - 30 * t ^ 2 * x ^ 2 - 30 * t * x ^ 4 - 30 * t ^ 2 * x ^ 3 - 15 * t * x ^ 5 - 15 * t ^ 2 * x ^ 4 - 3 * t * x ^ 6 - 3 * t ^ 2 * x ^ 5

/-- `C_1` of `NONSHORT_LOW_T_CURVATURE` (C2). -/
noncomputable def nltC1 (t x : ℝ) : ℝ :=
  -(194 / 3) - (292 / 3) * x + 64 * t - (2 / 3) * x ^ 2 + 134 * t * x + 3 * t ^ 2 + 32 * x ^ 3 + 45 * t * x ^ 2 - 80 * t ^ 2 * x - 46 * t ^ 3 - 136 * t * x ^ 3 - 350 * t ^ 2 * x ^ 2 - 184 * t ^ 3 * x - 234 * t * x ^ 4 - 540 * t ^ 2 * x ^ 3 - 276 * t ^ 3 * x ^ 2 - 166 * t * x ^ 5 - 365 * t ^ 2 * x ^ 4 - 184 * t ^ 3 * x ^ 3 - 43 * t * x ^ 6 - 92 * t ^ 2 * x ^ 5 - 46 * t ^ 3 * x ^ 4

/-- `C_2` of `NONSHORT_LOW_T_CURVATURE` (C2). -/
noncomputable def nltC2 (t x : ℝ) : ℝ :=
  32 + 10 * x + 4 * t - (584 / 3) * x ^ 2 - (370 / 3) * t * x - (386 / 3) * t ^ 2 - 130 * x ^ 3 + 138 * t * x ^ 2 + 174 * t ^ 2 * x + 196 * t ^ 3 - 54 * x ^ 4 + 160 * t * x ^ 3 + 672 * t ^ 2 * x ^ 2 + 450 * t ^ 3 * x - 8 * t ^ 4 + 304 * t * x ^ 4 + 944 * t ^ 2 * x ^ 3 + 210 * t ^ 3 * x ^ 2 - 140 * t ^ 4 * x + 162 * t * x ^ 5 + 248 * t ^ 2 * x ^ 4 - 402 * t ^ 3 * x ^ 3 - 256 * t ^ 4 * x ^ 2 + 10 * t * x ^ 6 - 102 * t ^ 2 * x ^ 5 - 294 * t ^ 3 * x ^ 4 - 124 * t ^ 4 * x ^ 3

/-- `C_3` of `NONSHORT_LOW_T_CURVATURE` (C2). -/
noncomputable def nltC3 (t x : ℝ) : ℝ :=
  148 * x - 4 * t + 422 * x ^ 2 + 68 * t * x + 136 * t ^ 2 + 336 * x ^ 3 + 154 * t * x ^ 2 + 60 * t ^ 2 * x - 114 * t ^ 3 + 94 * x ^ 4 + 244 * t * x ^ 3 - 524 * t ^ 2 * x ^ 2 - 164 * t ^ 3 * x + 12 * t ^ 4 + 154 * t * x ^ 4 - 408 * t ^ 2 * x ^ 3 + 576 * t ^ 3 * x ^ 2 + 128 * t ^ 4 * x + 148 * t * x ^ 5 + 476 * t ^ 2 * x ^ 4 + 1188 * t ^ 3 * x ^ 3 + 220 * t ^ 4 * x ^ 2 + 92 * t * x ^ 6 + 404 * t ^ 2 * x ^ 5 + 562 * t ^ 3 * x ^ 4 + 104 * t ^ 4 * x ^ 3

/-- `C_4` of `NONSHORT_LOW_T_CURVATURE` (C2). -/
noncomputable def nltC4 (t x : ℝ) : ℝ :=
  -80 * x - 200 * x ^ 2 - 3 * t * x - 39 * t ^ 2 - 160 * x ^ 3 - 111 * t * x ^ 2 - 31 * t ^ 2 * x + 28 * t ^ 3 - 40 * x ^ 4 - 206 * t * x ^ 3 + 182 * t ^ 2 * x ^ 2 - 24 * t ^ 3 * x - 4 * t ^ 4 - 178 * t * x ^ 4 + 10 * t ^ 2 * x ^ 3 - 444 * t ^ 3 * x ^ 2 - 40 * t ^ 4 * x - 127 * t * x ^ 5 - 335 * t ^ 2 * x ^ 4 - 576 * t ^ 3 * x ^ 3 - 12 * t ^ 4 * x ^ 2 + 8 * t ^ 5 * x - 55 * t * x ^ 6 - 203 * t ^ 2 * x ^ 5 - 232 * t ^ 3 * x ^ 4 - 8 * t ^ 4 * x ^ 3

/-- `C_5` of `NONSHORT_LOW_T_CURVATURE` (C2). -/
noncomputable def nltC5 (t x : ℝ) : ℝ :=
  -2 * t * x - t ^ 2 - t * x ^ 2 - 4 * t * x ^ 3 - 10 * t ^ 2 * x ^ 2 - 4 * t ^ 3 * x - 2 * t * x ^ 4 - 4 * t ^ 2 * x ^ 3 - 2 * t * x ^ 5 - 9 * t ^ 2 * x ^ 4 - 12 * t ^ 3 * x ^ 3 - 4 * t ^ 4 * x ^ 2 - t * x ^ 6 - 4 * t ^ 2 * x ^ 5 - 4 * t ^ 3 * x ^ 4

/-- **The source circuit** (`NONSHORT_LOW_T_CURVATURE` (C3)). -/
noncomputable def nltS (t x q : ℝ) : ℝ :=
  24 * (1 + x) * (17 * x + 76) * (q + 1) * (nltC0 t x * q ^ 0 + nltC1 t x * q ^ 1 + nltC2 t x * q ^ 2 + nltC3 t x * q ^ 3 + nltC4 t x * q ^ 4 + nltC5 t x * q ^ 5) + 4 * (q + 1) * (nltA0 t x * q ^ 0 + nltA1 t x * q ^ 1 + nltA2 t x * q ^ 2 + nltA3 t x * q ^ 3 + nltA4 t x * q ^ 4) * hrlVn t x
    - 16 * (1 + x) ^ 2 * (17 * x + 76) * (t + x) * q * (nltB0 t x * q ^ 0 + nltB1 t x * q ^ 1 + nltB2 t x * q ^ 2 + nltB3 t x * q ^ 3) * (q ^ 2 + 10 * q + 1)

/-- **The link** (`NONSHORT_LOW_T_CURVATURE` (C2)-(C3)): `24(q + 1)WD · fhComb = S` at `k = 1`. -/
theorem nlt_link (t x q : ℝ) (hq : 0 < q) (hx : 0 < x) :
    24 * (q + 1) * (1 + x) * (17 * x + 76) *
        fhComb (nltAl q) (nltM t x q) t x 1 q (hrlVL t x) (nhLp q) (nhFl t x q) = nltS t x q := by
  have hW : (1 : ℝ) + x ≠ 0 := by positivity
  have hD : (17 : ℝ) * x + 76 ≠ 0 := by positivity
  have hq1 : q + 1 ≠ 0 := by positivity
  have hq0 : q ≠ 0 := hq.ne'
  have hA : fhCv (nltAl q) (nltM t x q) t x 1 q = 4 * (1 + x) * (nltA0 t x * q ^ 0 + nltA1 t x * q ^ 1 + nltA2 t x * q ^ 2 + nltA3 t x * q ^ 3 + nltA4 t x * q ^ 4) := by
    unfold fhCv nhNv fhTPv nltAl nltM nltA0 nltA1 nltA2 nltA3 nltA4; ring
  have hC : fhComb (nltAl q) (nltM t x q) t x 1 q 0 0 0 =
      (nltC0 t x * q ^ 0 + nltC1 t x * q ^ 1 + nltC2 t x * q ^ 2 + nltC3 t x * q ^ 3 + nltC4 t x * q ^ 4 + nltC5 t x * q ^ 5) - 4 * q * (1 + x) ^ 2 * nltM t x q - 4 * (t + x) ^ 2 * q ^ 2 * nltM t x q := by
    unfold fhComb fhTP fhKt fhHt fhE0 nhN nltAl nltM nltC0 nltC1 nltC2 nltC3 nltC4 nltC5; ring
  have hB : fhCL (nltAl q) t x 1 q * (q - 1) =
      -4 * q ^ 2 * (t + x) * (1 + x) * ((nltB0 t x * q ^ 0 + nltB1 t x * q ^ 1 + nltB2 t x * q ^ 2 + nltB3 t x * q ^ 3) - nltM t x q) := by
    unfold fhCL nhNL nltAl nltM nltB0 nltB1 nltB2 nltB3; ring
  have hV : hrlVL t x = hrlVn t x / (24 * (17 * x + 76) * (1 + x) ^ 2) := by
    unfold hrlVL hrlVn; field_simp; ring
  rw [fh_comb_dec, hA, hC, hV]
  have hL : nhLp q * fhCL (nltAl q) t x 1 q =
      (q ^ 2 + 10 * q + 1) / (6 * q * (q + 1)) * (fhCL (nltAl q) t x 1 q * (q - 1)) := by
    unfold nhLp; field_simp
  rw [hL, hB]
  unfold nhFl nltS
  field_simp
  ring

/-- The coefficient of `y^0` in `S(t, x, 1 + y)`. -/
noncomputable def nltSt0 (t x : ℝ) : ℝ :=
  59584 * x + (1660 / 3) * x ^ 2 - 295488 * t * x - (32144 / 3) * x ^ 3 - (514972 / 3) * t * x ^ 2 + 469376 * t ^ 2 * x + 48316 * x ^ 4 - (16876 / 3) * t * x ^ 3 + 507872 * t ^ 2 * x ^ 2 - 233472 * t ^ 3 * x - 167848 * t * x ^ 4 + 209148 * t ^ 2 * x ^ 3 - 336768 * t ^ 3 * x ^ 2 - 51464 * t * x ^ 5 + 245788 * t ^ 2 * x ^ 4 - 197720 * t ^ 3 * x ^ 3 - 11424 * t * x ^ 6 + 102928 * t ^ 2 * x ^ 5 - 129520 * t ^ 3 * x ^ 4 + 4912 * t ^ 4 * x ^ 3 + 22848 * t ^ 2 * x ^ 6 - 51464 * t ^ 3 * x ^ 5 + 3264 * t ^ 4 * x ^ 4 - 11424 * t ^ 3 * x ^ 6

/-- The coefficient of `y^1` in `S(t, x, 1 + y)`. -/
noncomputable def nltSt1 (t x : ℝ) : ℝ :=
  90592 * x + 59584 * t - 73266 * x ^ 2 - 490704 * t * x - 235904 * t ^ 2 - 30628 * x ^ 3 + 2730 * t * x ^ 2 + 583200 * t ^ 2 * x + 233472 * t ^ 3 + 168938 * x ^ 4 + 368154 * t * x ^ 3 + 373216 * t ^ 2 * x ^ 2 + 74112 * t ^ 3 * x + 35708 * x ^ 5 - 448976 * t * x ^ 4 - 517738 * t ^ 2 * x ^ 3 + 156920 * t ^ 3 * x ^ 2 - 14592 * t ^ 4 * x - 389384 * t * x ^ 5 + 132822 * t ^ 2 * x ^ 4 + 539308 * t ^ 3 * x ^ 3 - 61632 * t ^ 4 * x ^ 2 - 129476 * t * x ^ 6 + 396664 * t ^ 2 * x ^ 5 + 270496 * t ^ 3 * x ^ 4 - 49320 * t ^ 4 * x ^ 3 - 11620 * t * x ^ 7 + 192788 * t ^ 2 * x ^ 6 - 26668 * t ^ 3 * x ^ 5 - 12960 * t ^ 4 * x ^ 4 + 23044 * t ^ 2 * x ^ 7 - 63312 * t ^ 3 * x ^ 6 - 3264 * t ^ 4 * x ^ 5 - 11424 * t ^ 3 * x ^ 7

/-- The coefficient of `y^2` in `S(t, x, 1 + y)`. -/
noncomputable def nltSt2 (t x : ℝ) : ℝ :=
  -(139840 / 3) * x + (33440 / 3) * t - (949322 / 3) * x ^ 2 - (511144 / 3) * t * x - 165376 * t ^ 2 - 318394 * x ^ 3 + (3357062 / 3) * t * x ^ 2 + 596544 * t ^ 2 * x + 277248 * t ^ 3 - (98162 / 3) * x ^ 4 + (6719906 / 3) * t * x ^ 3 - 458872 * t ^ 2 * x ^ 2 + 14592 * t ^ 3 * x + 14592 * t ^ 4 + 15846 * x ^ 5 + 1155202 * t * x ^ 4 - 2977544 * t ^ 2 * x ^ 3 - 31268 * t ^ 3 * x ^ 2 + 54336 * t ^ 4 * x + 153566 * t * x ^ 5 - 2869760 * t ^ 2 * x ^ 4 + 541892 * t ^ 3 * x ^ 3 + 55200 * t ^ 4 * x ^ 2 - 105394 * t * x ^ 6 - 1419048 * t ^ 2 * x ^ 5 + 648876 * t ^ 3 * x ^ 4 + 165824 * t ^ 4 * x ^ 3 - 62074 * t * x ^ 7 - 359646 * t ^ 2 * x ^ 6 + 441492 * t ^ 3 * x ^ 5 + 220032 * t ^ 4 * x ^ 4 - 5712 * t * x ^ 8 - 14054 * t ^ 2 * x ^ 7 + 153280 * t ^ 3 * x ^ 6 + 95904 * t ^ 4 * x ^ 5 + 10608 * t ^ 3 * x ^ 7 + 13056 * t ^ 4 * x ^ 6

/-- The coefficient of `y^3` in `S(t, x, 1 + y)`. -/
noncomputable def nltSt3 (t x : ℝ) : ℝ :=
  -(262048 / 3) * x - (174496 / 3) * t - (1307128 / 3) * x ^ 2 - (455512 / 3) * t * x + 68704 * t ^ 2 - (2314502 / 3) * x ^ 3 + (3771112 / 3) * t * x ^ 2 + 1131656 * t ^ 2 * x + 150784 * t ^ 3 - (1586270 / 3) * x ^ 4 + (11915512 / 3) * t * x ^ 3 + 1145840 * t ^ 2 * x ^ 2 - 314048 * t ^ 3 * x - 7296 * t ^ 4 - 105616 * x ^ 5 + 4737180 * t * x ^ 4 - 1503410 * t ^ 2 * x ^ 3 - 1115040 * t ^ 3 * x ^ 2 - 35680 * t ^ 4 * x + 2950196 * t * x ^ 5 - 3922626 * t ^ 2 * x ^ 4 - 1298292 * t ^ 3 * x ^ 3 - 141376 * t ^ 4 * x ^ 2 + 913512 * t * x ^ 6 - 3581408 * t ^ 2 * x ^ 5 - 425280 * t ^ 3 * x ^ 4 + 14192 * t ^ 4 * x ^ 3 + 67696 * t * x ^ 7 - 1414224 * t ^ 2 * x ^ 6 + 596932 * t ^ 3 * x ^ 5 + 229312 * t ^ 4 * x ^ 4 - 136 * t * x ^ 8 - 134536 * t ^ 2 * x ^ 7 + 474016 * t ^ 3 * x ^ 6 + 133248 * t ^ 4 * x ^ 5 + 65280 * t ^ 3 * x ^ 7 + 19584 * t ^ 4 * x ^ 6

/-- The coefficient of `y^4` in `S(t, x, 1 + y)`. -/
noncomputable def nltSt4 (t x : ℝ) : ℝ :=
  -9728 * x - 9728 * t - 266048 * x ^ 2 - 328672 * t * x - 69920 * t ^ 2 - 647180 * x ^ 3 + 160452 * t * x ^ 2 + 740712 * t ^ 2 * x + 167808 * t ^ 3 - 508974 * x ^ 4 + 2544776 * t * x ^ 3 + 1902580 * t ^ 2 * x ^ 2 - 25696 * t ^ 3 * x - 21888 * t ^ 4 - 118114 * x ^ 5 + 4301358 * t * x ^ 4 + 924340 * t ^ 2 * x ^ 3 - 960192 * t ^ 3 * x ^ 2 - 92448 * t ^ 4 * x + 3274634 * t * x ^ 5 - 1850968 * t ^ 2 * x ^ 4 - 1841080 * t ^ 3 * x ^ 3 - 260352 * t ^ 4 * x ^ 2 + 1174482 * t * x ^ 6 - 2861136 * t ^ 2 * x ^ 5 - 1207632 * t ^ 3 * x ^ 4 - 199632 * t ^ 4 * x ^ 3 + 134826 * t * x ^ 7 - 1343394 * t ^ 2 * x ^ 6 + 156096 * t ^ 3 * x ^ 5 + 32256 * t ^ 4 * x ^ 4 + 3944 * t * x ^ 8 - 150786 * t ^ 2 * x ^ 7 + 365368 * t ^ 3 * x ^ 6 + 56832 * t ^ 4 * x ^ 5 + 61200 * t ^ 3 * x ^ 7 + 9792 * t ^ 4 * x ^ 6

/-- The coefficient of `y^5` in `S(t, x, 1 + y)`. -/
noncomputable def nltSt5 (t x : ℝ) : ℝ :=
  -72960 * x ^ 2 - 157472 * t * x - 71744 * t ^ 2 - 174160 * x ^ 3 - 163512 * t * x ^ 2 + 92784 * t ^ 2 * x + 69312 * t ^ 3 - 133560 * x ^ 4 + 423428 * t * x ^ 3 + 445688 * t ^ 2 * x ^ 2 + 17936 * t ^ 3 * x - 7296 * t ^ 4 - 32360 * x ^ 5 + 988412 * t * x ^ 4 + 219496 * t ^ 2 * x ^ 3 - 343584 * t ^ 3 * x ^ 2 - 23520 * t ^ 4 * x + 813596 * t * x ^ 5 - 636472 * t ^ 2 * x ^ 4 - 766484 * t ^ 3 * x ^ 3 - 85152 * t ^ 4 * x ^ 2 + 272548 * t * x ^ 6 - 982504 * t ^ 2 * x ^ 5 - 620332 * t ^ 3 * x ^ 4 - 88456 * t ^ 4 * x ^ 3 + 14896 * t * x ^ 7 - 466344 * t ^ 2 * x ^ 6 - 86476 * t ^ 3 * x ^ 5 - 14688 * t ^ 4 * x ^ 4 - 2176 * t * x ^ 8 - 56176 * t ^ 2 * x ^ 7 + 78372 * t ^ 3 * x ^ 6 + 7296 * t ^ 4 * x ^ 5 + 16320 * t ^ 3 * x ^ 7 + 1632 * t ^ 4 * x ^ 6

/-- The coefficient of `y^6` in `S(t, x, 1 + y)`. -/
noncomputable def nltSt6 (t x : ℝ) : ℝ :=
  -3648 * t * x - 1824 * t ^ 2 - 3856 * t * x ^ 2 + 1416 * t ^ 2 * x + 1216 * t ^ 3 - 3720 * t * x ^ 3 - 9320 * t ^ 2 * x ^ 2 - 4592 * t ^ 3 * x - 4328 * t * x ^ 4 - 13120 * t ^ 2 * x ^ 3 + 1344 * t ^ 3 * x ^ 2 + 2432 * t ^ 4 * x - 816 * t * x ^ 5 - 4272 * t ^ 2 * x ^ 4 - 1888 * t ^ 3 * x ^ 3 - 1888 * t ^ 4 * x ^ 2 - 608 * t * x ^ 6 - 8312 * t ^ 2 * x ^ 5 - 16352 * t ^ 3 * x ^ 4 - 5408 * t ^ 4 * x ^ 3 - 744 * t * x ^ 7 - 5416 * t ^ 2 * x ^ 6 - 8400 * t ^ 3 * x ^ 5 - 1088 * t ^ 4 * x ^ 4 - 136 * t * x ^ 8 - 816 * t ^ 2 * x ^ 7 - 1088 * t ^ 3 * x ^ 6

/-- **The `y`-split of the circuit**, one power of `y` at a time. -/
theorem nlt_S_split (t x y : ℝ) :
    nltS t x (1 + y) = nltSt0 t x * y ^ 0 + nltSt1 t x * y ^ 1 + nltSt2 t x * y ^ 2 + nltSt3 t x * y ^ 3 + nltSt4 t x * y ^ 4 + nltSt5 t x * y ^ 5 + nltSt6 t x * y ^ 6 := by
  have e0 : nltSt0 t x = (3648 + 4464 * x + 816 * x ^ 2) * nltC0 t x + (3648 + 4464 * x + 816 * x ^ 2) * nltC1 t x + (3648 + 4464 * x + 816 * x ^ 2) * nltC2 t x + (3648 + 4464 * x + 816 * x ^ 2) * nltC3 t x + (3648 + 4464 * x + 816 * x ^ 2) * nltC4 t x + (3648 + 4464 * x + 816 * x ^ 2) * nltC5 t x + (8) * nltA0 t x * hrlVn t x + (8) * nltA1 t x * hrlVn t x + (8) * nltA2 t x * hrlVn t x + (8) * nltA3 t x * hrlVn t x + (8) * nltA4 t x * hrlVn t x + (-14592 * x - 14592 * t - 32448 * x ^ 2 - 32448 * t * x - 21120 * x ^ 3 - 21120 * t * x ^ 2 - 3264 * x ^ 4 - 3264 * t * x ^ 3) * nltB0 t x + (-14592 * x - 14592 * t - 32448 * x ^ 2 - 32448 * t * x - 21120 * x ^ 3 - 21120 * t * x ^ 2 - 3264 * x ^ 4 - 3264 * t * x ^ 3) * nltB1 t x + (-14592 * x - 14592 * t - 32448 * x ^ 2 - 32448 * t * x - 21120 * x ^ 3 - 21120 * t * x ^ 2 - 3264 * x ^ 4 - 3264 * t * x ^ 3) * nltB2 t x + (-14592 * x - 14592 * t - 32448 * x ^ 2 - 32448 * t * x - 21120 * x ^ 3 - 21120 * t * x ^ 2 - 3264 * x ^ 4 - 3264 * t * x ^ 3) * nltB3 t x := by
    simp only [nltSt0, nltA0, nltA1, nltA2, nltA3, nltA4, nltB0, nltB1, nltB2, nltB3, nltC0, nltC1, nltC2, nltC3, nltC4, nltC5, hrlVn]; ring
  have e1 : nltSt1 t x = (1824 + 2232 * x + 408 * x ^ 2) * nltC0 t x + (5472 + 6696 * x + 1224 * x ^ 2) * nltC1 t x + (9120 + 11160 * x + 2040 * x ^ 2) * nltC2 t x + (12768 + 15624 * x + 2856 * x ^ 2) * nltC3 t x + (16416 + 20088 * x + 3672 * x ^ 2) * nltC4 t x + (20064 + 24552 * x + 4488 * x ^ 2) * nltC5 t x + (4) * nltA0 t x * hrlVn t x + (12) * nltA1 t x * hrlVn t x + (20) * nltA2 t x * hrlVn t x + (28) * nltA3 t x * hrlVn t x + (36) * nltA4 t x * hrlVn t x + (-29184 * x - 29184 * t - 64896 * x ^ 2 - 64896 * t * x - 42240 * x ^ 3 - 42240 * t * x ^ 2 - 6528 * x ^ 4 - 6528 * t * x ^ 3) * nltB0 t x + (-43776 * x - 43776 * t - 97344 * x ^ 2 - 97344 * t * x - 63360 * x ^ 3 - 63360 * t * x ^ 2 - 9792 * x ^ 4 - 9792 * t * x ^ 3) * nltB1 t x + (-58368 * x - 58368 * t - 129792 * x ^ 2 - 129792 * t * x - 84480 * x ^ 3 - 84480 * t * x ^ 2 - 13056 * x ^ 4 - 13056 * t * x ^ 3) * nltB2 t x + (-72960 * x - 72960 * t - 162240 * x ^ 2 - 162240 * t * x - 105600 * x ^ 3 - 105600 * t * x ^ 2 - 16320 * x ^ 4 - 16320 * t * x ^ 3) * nltB3 t x := by
    simp only [nltSt1, nltA0, nltA1, nltA2, nltA3, nltA4, nltB0, nltB1, nltB2, nltB3, nltC0, nltC1, nltC2, nltC3, nltC4, nltC5, hrlVn]; ring
  have e2 : nltSt2 t x = (1824 + 2232 * x + 408 * x ^ 2) * nltC1 t x + (7296 + 8928 * x + 1632 * x ^ 2) * nltC2 t x + (16416 + 20088 * x + 3672 * x ^ 2) * nltC3 t x + (29184 + 35712 * x + 6528 * x ^ 2) * nltC4 t x + (45600 + 55800 * x + 10200 * x ^ 2) * nltC5 t x + (4) * nltA1 t x * hrlVn t x + (16) * nltA2 t x * hrlVn t x + (36) * nltA3 t x * hrlVn t x + (64) * nltA4 t x * hrlVn t x + (-15808 * x - 15808 * t - 35152 * x ^ 2 - 35152 * t * x - 22880 * x ^ 3 - 22880 * t * x ^ 2 - 3536 * x ^ 4 - 3536 * t * x ^ 3) * nltB0 t x + (-44992 * x - 44992 * t - 100048 * x ^ 2 - 100048 * t * x - 65120 * x ^ 3 - 65120 * t * x ^ 2 - 10064 * x ^ 4 - 10064 * t * x ^ 3) * nltB1 t x + (-88768 * x - 88768 * t - 197392 * x ^ 2 - 197392 * t * x - 128480 * x ^ 3 - 128480 * t * x ^ 2 - 19856 * x ^ 4 - 19856 * t * x ^ 3) * nltB2 t x + (-147136 * x - 147136 * t - 327184 * x ^ 2 - 327184 * t * x - 212960 * x ^ 3 - 212960 * t * x ^ 2 - 32912 * x ^ 4 - 32912 * t * x ^ 3) * nltB3 t x := by
    simp only [nltSt2, nltA1, nltA2, nltA3, nltA4, nltB0, nltB1, nltB2, nltB3, nltC1, nltC2, nltC3, nltC4, nltC5, hrlVn]; ring
  have e3 : nltSt3 t x = (1824 + 2232 * x + 408 * x ^ 2) * nltC2 t x + (9120 + 11160 * x + 2040 * x ^ 2) * nltC3 t x + (25536 + 31248 * x + 5712 * x ^ 2) * nltC4 t x + (54720 + 66960 * x + 12240 * x ^ 2) * nltC5 t x + (4) * nltA2 t x * hrlVn t x + (20) * nltA3 t x * hrlVn t x + (56) * nltA4 t x * hrlVn t x + (-1216 * x - 1216 * t - 2704 * x ^ 2 - 2704 * t * x - 1760 * x ^ 3 - 1760 * t * x ^ 2 - 272 * x ^ 4 - 272 * t * x ^ 3) * nltB0 t x + (-17024 * x - 17024 * t - 37856 * x ^ 2 - 37856 * t * x - 24640 * x ^ 3 - 24640 * t * x ^ 2 - 3808 * x ^ 4 - 3808 * t * x ^ 3) * nltB1 t x + (-62016 * x - 62016 * t - 137904 * x ^ 2 - 137904 * t * x - 89760 * x ^ 3 - 89760 * t * x ^ 2 - 13872 * x ^ 4 - 13872 * t * x ^ 3) * nltB2 t x + (-150784 * x - 150784 * t - 335296 * x ^ 2 - 335296 * t * x - 218240 * x ^ 3 - 218240 * t * x ^ 2 - 33728 * x ^ 4 - 33728 * t * x ^ 3) * nltB3 t x := by
    simp only [nltSt3, nltA2, nltA3, nltA4, nltB0, nltB1, nltB2, nltB3, nltC2, nltC3, nltC4, nltC5, hrlVn]; ring
  have e4 : nltSt4 t x = (1824 + 2232 * x + 408 * x ^ 2) * nltC3 t x + (10944 + 13392 * x + 2448 * x ^ 2) * nltC4 t x + (36480 + 44640 * x + 8160 * x ^ 2) * nltC5 t x + (4) * nltA3 t x * hrlVn t x + (24) * nltA4 t x * hrlVn t x + (-1216 * x - 1216 * t - 2704 * x ^ 2 - 2704 * t * x - 1760 * x ^ 3 - 1760 * t * x ^ 2 - 272 * x ^ 4 - 272 * t * x ^ 3) * nltB1 t x + (-18240 * x - 18240 * t - 40560 * x ^ 2 - 40560 * t * x - 26400 * x ^ 3 - 26400 * t * x ^ 2 - 4080 * x ^ 4 - 4080 * t * x ^ 3) * nltB2 t x + (-80256 * x - 80256 * t - 178464 * x ^ 2 - 178464 * t * x - 116160 * x ^ 3 - 116160 * t * x ^ 2 - 17952 * x ^ 4 - 17952 * t * x ^ 3) * nltB3 t x := by
    simp only [nltSt4, nltA3, nltA4, nltB1, nltB2, nltB3, nltC3, nltC4, nltC5, hrlVn]; ring
  have e5 : nltSt5 t x = (1824 + 2232 * x + 408 * x ^ 2) * nltC4 t x + (12768 + 15624 * x + 2856 * x ^ 2) * nltC5 t x + (4) * nltA4 t x * hrlVn t x + (-1216 * x - 1216 * t - 2704 * x ^ 2 - 2704 * t * x - 1760 * x ^ 3 - 1760 * t * x ^ 2 - 272 * x ^ 4 - 272 * t * x ^ 3) * nltB2 t x + (-19456 * x - 19456 * t - 43264 * x ^ 2 - 43264 * t * x - 28160 * x ^ 3 - 28160 * t * x ^ 2 - 4352 * x ^ 4 - 4352 * t * x ^ 3) * nltB3 t x := by
    simp only [nltSt5, nltA4, nltB2, nltB3, nltC4, nltC5, hrlVn]; ring
  have e6 : nltSt6 t x = (1824 + 2232 * x + 408 * x ^ 2) * nltC5 t x + (-1216 * x - 1216 * t - 2704 * x ^ 2 - 2704 * t * x - 1760 * x ^ 3 - 1760 * t * x ^ 2 - 272 * x ^ 4 - 272 * t * x ^ 3) * nltB3 t x := by
    simp only [nltSt6, nltB3, nltC5]; ring
  unfold nltS
  rw [e0, e1, e2, e3, e4, e5, e6]
  ring

end SmoothedOctagon
