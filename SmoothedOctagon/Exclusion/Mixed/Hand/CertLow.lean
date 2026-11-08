module

public import SmoothedOctagon.Exclusion.Mixed.Hand.Bern

/-!
# Case M2 by hand: generated sign certificates for the low-scale faces

The cleared low-scale quartic `Q = P₀ + P₁y + ⋯ + P₄y⁴` on the unit face `k = 1` (`nhLU0`, …,
`nhLU4`) and on the high-ratio face `k = 2t + 1/2` (`nhLH0`, …, `nhLH4`), and Bernstein
certificates (generated; every identity is checked by `ring`) for the six signs `J₀ = P₀`,
`J₁ = P₁ + 2P₀`, `J₂ = P₂ + 48P₀`, `J₃ = P₃ + 4P₂`, `J₄ = P₃ - P₀`, `J₅ = P₄ - P₀`:

* unit face (`nhLUJ i`, `nhLUJ_dom i`): `1/2 < x ≤ 7/3`, `0 ≤ t ≤ 1/4`, `x ≥ 1 - 2t`,
  `3(x + 2)³t ≤ -2x³ - x² + 10x + 12` (i.e. `t ≤ T(x)`); for `x ≥ 1` the constraint `t ≤ T(x)` is
  used through `T(x) ≤ T(x_a)` on subintervals `[x_a, x_b]` (`nh_T_anti`);
* high-ratio face (`nhLHJ i`, `nhLHJ_dom i`): `1/4 ≤ t ≤ 7/20`, `1/2 ≤ x ≤ 1`.
-/

@[expose] public section

namespace SmoothedOctagon

/-- `T` is decreasing: for `0 ≤ x_a ≤ x`, `N(x)(x_a + 2)³ ≤ N(x_a)(x + 2)³`,
`N(z) = -2z³ - z² + 10z + 12`. -/
theorem nh_T_anti {xa x t : ℝ} (ha : 0 ≤ xa) (hax : xa ≤ x) (ht : 0 ≤ t)
    (hT : 3 * (x + 2) ^ 3 * t ≤ -2 * x ^ 3 - x ^ 2 + 10 * x + 12) :
    3 * (xa + 2) ^ 3 * t ≤ -2 * xa ^ 3 - xa ^ 2 + 10 * xa + 12 := by
  have hx : 0 ≤ x := le_trans ha hax
  have hQ : 0 ≤ (x - xa) * (11 * xa ^ 2 * x ^ 2 + 34 * xa ^ 2 * x + 28 * xa ^ 2 + 34 * xa * x ^ 2
      + 100 * xa * x + 80 * xa + 28 * x ^ 2 + 80 * x + 64) := mul_nonneg (by linarith) (by positivity)
  have e : (-2 * xa ^ 3 - xa ^ 2 + 10 * xa + 12) * (x + 2) ^ 3 -
      (-2 * x ^ 3 - x ^ 2 + 10 * x + 12) * (xa + 2) ^ 3 =
      (x - xa) * (11 * xa ^ 2 * x ^ 2 + 34 * xa ^ 2 * x + 28 * xa ^ 2 + 34 * xa * x ^ 2
      + 100 * xa * x + 80 * xa + 28 * x ^ 2 + 80 * x + 64) := by ring
  have h1 : 3 * (x + 2) ^ 3 * t * (xa + 2) ^ 3 ≤ (-2 * x ^ 3 - x ^ 2 + 10 * x + 12) * (xa + 2) ^ 3 :=
    mul_le_mul_of_nonneg_right hT (by positivity)
  have h2 : 3 * (xa + 2) ^ 3 * t * (x + 2) ^ 3 ≤ (-2 * xa ^ 3 - xa ^ 2 + 10 * xa + 12) * (x + 2) ^ 3 := by
    nlinarith
  have hx3 : 0 < (x + 2) ^ 3 := by positivity
  nlinarith

/-- The coefficient `P_0` of the low-scale quartic on the unit face. -/
noncomputable def nhLU0 (t x : ℝ) : ℝ :=
  64 * x ^ 3 + 80 * x ^ 4 + 28 * x ^ 5 - 96 * t * x ^ 2 - 432 * t * x ^ 3 - 472 * t * x ^ 4 - 212 * t * x ^ 5 - 52 * t * x ^ 6 - 12 * t * x ^ 7 + 384 * t ^ 2 * x ^ 2 + 1152 * t ^ 2 * x ^ 3 + 1136 * t ^ 2 * x ^ 4 + 508 * t ^ 2 * x ^ 5 + 128 * t ^ 2 * x ^ 6 + 24 * t ^ 2 * x ^ 7 - 480 * t ^ 3 * x ^ 2 - 1264 * t ^ 3 * x ^ 3 - 1176 * t ^ 3 * x ^ 4 - 492 * t ^ 3 * x ^ 5 - 100 * t ^ 3 * x ^ 6 - 12 * t ^ 3 * x ^ 7 + 192 * t ^ 4 * x ^ 2 + 480 * t ^ 4 * x ^ 3 + 432 * t ^ 4 * x ^ 4 + 168 * t ^ 4 * x ^ 5 + 24 * t ^ 4 * x ^ 6

/-- The coefficient `P_1` of the low-scale quartic on the unit face. -/
noncomputable def nhLU1 (t x : ℝ) : ℝ :=
  -48 * x ^ 2 + 200 * x ^ 3 + 380 * x ^ 4 + 208 * x ^ 5 + 34 * x ^ 6 + 48 * t * x + 120 * t * x ^ 2 - 1076 * t * x ^ 3 - 2134 * t * x ^ 4 - 1618 * t * x ^ 5 - 624 * t * x ^ 6 - 126 * t * x ^ 7 - 8 * t * x ^ 8 - 240 * t ^ 2 * x - 120 * t ^ 2 * x ^ 2 + 2100 * t ^ 2 * x ^ 3 + 3902 * t ^ 2 * x ^ 4 + 3144 * t ^ 2 * x ^ 5 + 1412 * t ^ 2 * x ^ 6 + 348 * t ^ 2 * x ^ 7 + 32 * t ^ 2 * x ^ 8 + 384 * t ^ 3 * x + 240 * t ^ 3 * x ^ 2 - 1512 * t ^ 3 * x ^ 3 - 2628 * t ^ 3 * x ^ 4 - 1962 * t ^ 3 * x ^ 5 - 858 * t ^ 3 * x ^ 6 - 222 * t ^ 3 * x ^ 7 - 24 * t ^ 3 * x ^ 8 - 192 * t ^ 4 * x - 192 * t ^ 4 * x ^ 2 + 288 * t ^ 4 * x ^ 3 + 480 * t ^ 4 * x ^ 4 + 228 * t ^ 4 * x ^ 5 + 36 * t ^ 4 * x ^ 6

/-- The coefficient `P_2` of the low-scale quartic on the unit face. -/
noncomputable def nhLU2 (t x : ℝ) : ℝ :=
  -152 * x ^ 2 + 132 * x ^ 3 + 514 * x ^ 4 + 373 * x ^ 5 + 95 * x ^ 6 + 6 * x ^ 7 + 40 * t * x + 620 * t * x ^ 2 - 594 * t * x ^ 3 - 2779 * t * x ^ 4 - 2784 * t * x ^ 5 - 1277 * t * x ^ 6 - 284 * t * x ^ 7 - 24 * t * x ^ 8 + 48 * t ^ 2 - 128 * t ^ 2 * x - 1136 * t ^ 2 * x ^ 2 + 100 * t ^ 2 * x ^ 3 + 3145 * t ^ 2 * x ^ 4 + 3853 * t ^ 2 * x ^ 5 + 2118 * t ^ 2 * x ^ 6 + 572 * t ^ 2 * x ^ 7 + 60 * t ^ 2 * x ^ 8 - 96 * t ^ 3 + 112 * t ^ 3 * x + 680 * t ^ 3 * x ^ 2 - 4 * t ^ 3 * x ^ 3 - 1420 * t ^ 3 * x ^ 4 - 1742 * t ^ 3 * x ^ 5 - 1008 * t ^ 3 * x ^ 6 - 300 * t ^ 3 * x ^ 7 - 36 * t ^ 3 * x ^ 8 - 288 * t ^ 4 * x - 624 * t ^ 4 * x ^ 2 - 408 * t ^ 4 * x ^ 3 - 36 * t ^ 4 * x ^ 4 + 48 * t ^ 4 * x ^ 5 + 12 * t ^ 4 * x ^ 6

/-- The coefficient `P_3` of the low-scale quartic on the unit face. -/
noncomputable def nhLU3 (t x : ℝ) : ℝ :=
  -120 * x ^ 2 + 44 * x ^ 3 + 350 * x ^ 4 + 305 * x ^ 5 + 100 * x ^ 6 + 11 * x ^ 7 - 32 * t * x + 560 * t * x ^ 2 + 536 * t * x ^ 3 - 268 * t * x ^ 4 - 296 * t * x ^ 5 + 170 * t * x ^ 6 + 238 * t * x ^ 7 + 84 * t * x ^ 8 + 10 * t * x ^ 9 + 40 * t ^ 2 + 268 * t ^ 2 * x - 34 * t ^ 2 * x ^ 2 + 621 * t ^ 2 * x ^ 3 + 2544 * t ^ 2 * x ^ 4 + 3017 * t ^ 2 * x ^ 5 + 1668 * t ^ 2 * x ^ 6 + 450 * t ^ 2 * x ^ 7 + 48 * t ^ 2 * x ^ 8 - 48 * t ^ 3 - 24 * t ^ 3 * x + 692 * t ^ 3 * x ^ 2 + 1366 * t ^ 3 * x ^ 3 + 962 * t ^ 3 * x ^ 4 + 154 * t ^ 3 * x ^ 5 - 148 * t ^ 3 * x ^ 6 - 80 * t ^ 3 * x ^ 7 - 12 * t ^ 3 * x ^ 8 - 96 * t ^ 4 * x - 240 * t ^ 4 * x ^ 2 - 216 * t ^ 4 * x ^ 3 - 84 * t ^ 4 * x ^ 4 - 12 * t ^ 4 * x ^ 5

/-- The coefficient `P_4` of the low-scale quartic on the unit face. -/
noncomputable def nhLU4 (t x : ℝ) : ℝ :=
  -16 * x ^ 2 + 48 * x ^ 3 + 136 * x ^ 4 + 112 * x ^ 5 + 39 * x ^ 6 + 5 * x ^ 7 - 16 * t * x + 144 * t * x ^ 2 + 296 * t * x ^ 3 + 336 * t * x ^ 4 + 407 * t * x ^ 5 + 371 * t * x ^ 6 + 190 * t * x ^ 7 + 49 * t * x ^ 8 + 5 * t * x ^ 9 + 96 * t ^ 2 * x + 160 * t ^ 2 * x ^ 2 + 416 * t ^ 2 * x ^ 3 + 848 * t ^ 2 * x ^ 4 + 846 * t ^ 2 * x ^ 5 + 430 * t ^ 2 * x ^ 6 + 109 * t ^ 2 * x ^ 7 + 11 * t ^ 2 * x ^ 8 + 192 * t ^ 3 * x ^ 2 + 480 * t ^ 3 * x ^ 3 + 480 * t ^ 3 * x ^ 4 + 240 * t ^ 3 * x ^ 5 + 60 * t ^ 3 * x ^ 6 + 6 * t ^ 3 * x ^ 7

/-- The coefficient `P_0` of the low-scale quartic on the high-ratio face. -/
noncomputable def nhLH0 (t x : ℝ) : ℝ :=
  32 * x ^ 3 + 40 * x ^ 4 + 14 * x ^ 5 - 96 * t * x ^ 2 - 256 * t * x ^ 3 - 272 * t * x ^ 4 - 160 * t * x ^ 5 - 60 * t * x ^ 6 - 12 * t * x ^ 7 + 336 * t ^ 2 * x ^ 2 + 824 * t ^ 2 * x ^ 3 + 868 * t ^ 2 * x ^ 4 + 500 * t ^ 2 * x ^ 5 + 162 * t ^ 2 * x ^ 6 + 24 * t ^ 2 * x ^ 7 - 240 * t ^ 3 * x ^ 2 - 600 * t ^ 3 * x ^ 3 - 636 * t ^ 3 * x ^ 4 - 354 * t ^ 3 * x ^ 5 - 102 * t ^ 3 * x ^ 6 - 12 * t ^ 3 * x ^ 7

/-- The coefficient `P_1` of the low-scale quartic on the high-ratio face. -/
noncomputable def nhLH1 (t x : ℝ) : ℝ :=
  -24 * x ^ 2 + 100 * x ^ 3 + 190 * x ^ 4 + 104 * x ^ 5 + 17 * x ^ 6 + 24 * t * x - 252 * t * x ^ 2 - 1062 * t * x ^ 3 - 1673 * t * x ^ 4 - 1386 * t * x ^ 5 - 626 * t * x ^ 6 - 135 * t * x ^ 7 - 8 * t * x ^ 8 - 120 * t ^ 2 * x + 1092 * t ^ 2 * x ^ 2 + 3746 * t ^ 2 * x ^ 3 + 5203 * t ^ 2 * x ^ 4 + 3988 * t ^ 2 * x ^ 5 + 1740 * t ^ 2 * x ^ 6 + 390 * t ^ 2 * x ^ 7 + 32 * t ^ 2 * x ^ 8 + 240 * t ^ 3 * x - 240 * t ^ 3 * x ^ 2 - 1848 * t ^ 3 * x ^ 3 - 2928 * t ^ 3 * x ^ 4 - 2337 * t ^ 3 * x ^ 5 - 1041 * t ^ 3 * x ^ 6 - 246 * t ^ 3 * x ^ 7 - 24 * t ^ 3 * x ^ 8

/-- The coefficient `P_2` of the low-scale quartic on the high-ratio face. -/
noncomputable def nhLH2 (t x : ℝ) : ℝ :=
  -76 * x ^ 2 + 66 * x ^ 3 + 257 * x ^ 4 + (373 / 2) * x ^ 5 + (95 / 2) * x ^ 6 + 3 * x ^ 7 + 20 * t * x - 282 * t * x ^ 2 - 1453 * t * x ^ 3 - (5391 / 2) * t * x ^ 4 - 2501 * t * x ^ 5 - 1222 * t * x ^ 6 - (579 / 2) * t * x ^ 7 - 24 * t * x ^ 8 + 24 * t ^ 2 - 224 * t ^ 2 * x + 1084 * t ^ 2 * x ^ 2 + 4612 * t ^ 2 * x ^ 3 + (14195 / 2) * t ^ 2 * x ^ 4 + 5868 * t ^ 2 * x ^ 5 + (5445 / 2) * t ^ 2 * x ^ 6 + 651 * t ^ 2 * x ^ 7 + 60 * t ^ 2 * x ^ 8 + 744 * t ^ 3 * x + 1212 * t ^ 3 * x ^ 2 - 186 * t ^ 3 * x ^ 3 - 2127 * t ^ 3 * x ^ 4 - 2382 * t ^ 3 * x ^ 5 - 1263 * t ^ 3 * x ^ 6 - 336 * t ^ 3 * x ^ 7 - 36 * t ^ 3 * x ^ 8

/-- The coefficient `P_3` of the low-scale quartic on the high-ratio face. -/
noncomputable def nhLH3 (t x : ℝ) : ℝ :=
  -60 * x ^ 2 + 22 * x ^ 3 + 175 * x ^ 4 + (305 / 2) * x ^ 5 + 50 * x ^ 6 + (11 / 2) * x ^ 7 - 16 * t * x - 56 * t * x ^ 2 - 196 * t * x ^ 3 - 270 * t * x ^ 4 + 4 * t * x ^ 5 + 296 * t * x ^ 6 + 252 * t * x ^ 7 + 84 * t * x ^ 8 + 10 * t * x ^ 9 + 20 * t ^ 2 - 26 * t ^ 2 * x + 1079 * t ^ 2 * x ^ 2 + (7285 / 2) * t ^ 2 * x ^ 3 + 5306 * t ^ 2 * x ^ 4 + (8579 / 2) * t ^ 2 * x ^ 5 + 1983 * t ^ 2 * x ^ 6 + 485 * t ^ 2 * x ^ 7 + 48 * t ^ 2 * x ^ 8 + 32 * t ^ 3 + 872 * t ^ 3 * x + 2196 * t ^ 3 * x ^ 2 + 2346 * t ^ 3 * x ^ 3 + 1125 * t ^ 3 * x ^ 4 + 21 * t ^ 3 * x ^ 5 - 224 * t ^ 3 * x ^ 6 - 92 * t ^ 3 * x ^ 7 - 12 * t ^ 3 * x ^ 8

/-- The coefficient `P_4` of the low-scale quartic on the high-ratio face. -/
noncomputable def nhLH4 (t x : ℝ) : ℝ :=
  -8 * x ^ 2 + 24 * x ^ 3 + 68 * x ^ 4 + 56 * x ^ 5 + (39 / 2) * x ^ 6 + (5 / 2) * x ^ 7 - 8 * t * x + 40 * t * x ^ 2 + 228 * t * x ^ 3 + 480 * t * x ^ 4 + (1175 / 2) * t * x ^ 5 + (887 / 2) * t * x ^ 6 + 200 * t * x ^ 7 + 49 * t * x ^ 8 + 5 * t * x ^ 9 + 16 * t ^ 2 * x + 352 * t ^ 2 * x ^ 2 + 1000 * t ^ 2 * x ^ 3 + 1336 * t ^ 2 * x ^ 4 + 1017 * t ^ 2 * x ^ 5 + 452 * t ^ 2 * x ^ 6 + 109 * t ^ 2 * x ^ 7 + 11 * t ^ 2 * x ^ 8 + 192 * t ^ 3 * x + 576 * t ^ 3 * x ^ 2 + 768 * t ^ 3 * x ^ 3 + 576 * t ^ 3 * x ^ 4 + 252 * t ^ 3 * x ^ 5 + 60 * t ^ 3 * x ^ 6 + 6 * t ^ 3 * x ^ 7

/-- The sign `J_0` on the unit face. -/
noncomputable def nhLUJ0 (t x : ℝ) : ℝ :=
  64 * x ^ 3 + 80 * x ^ 4 + 28 * x ^ 5 - 96 * t * x ^ 2 - 432 * t * x ^ 3 - 472 * t * x ^ 4 - 212 * t * x ^ 5 - 52 * t * x ^ 6 - 12 * t * x ^ 7 + 384 * t ^ 2 * x ^ 2 + 1152 * t ^ 2 * x ^ 3 + 1136 * t ^ 2 * x ^ 4 + 508 * t ^ 2 * x ^ 5 + 128 * t ^ 2 * x ^ 6 + 24 * t ^ 2 * x ^ 7 - 480 * t ^ 3 * x ^ 2 - 1264 * t ^ 3 * x ^ 3 - 1176 * t ^ 3 * x ^ 4 - 492 * t ^ 3 * x ^ 5 - 100 * t ^ 3 * x ^ 6 - 12 * t ^ 3 * x ^ 7 + 192 * t ^ 4 * x ^ 2 + 480 * t ^ 4 * x ^ 3 + 432 * t ^ 4 * x ^ 4 + 168 * t ^ 4 * x ^ 5 + 24 * t ^ 4 * x ^ 6

private theorem nhLUJ0_p0_g0_bp0 (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    0 ≤ 6615 * a * b ^ 9 + 84510 * a ^ 2 * b ^ 8 + 483660 * a ^ 3 * b ^ 7 + 1623332 * a ^ 4 * b ^ 6 + 3514088 * a ^ 5 * b ^ 5 + 5079956 * a ^ 6 * b ^ 4 + 4898160 * a ^ 7 * b ^ 3 + 3035026 * a ^ 8 * b ^ 2 + 1095940 * a ^ 9 * b + 175642 * a ^ 10 := by positivity

private theorem nhLUJ0_p0_g0_l0 (x : ℝ) (h0 : (1 / 2) ≤ x) (h1 : x ≤ 1) :
    0 < -128 * x ^ 3 - 320 * x ^ 4 + 160 * x ^ 5 + 1424 * x ^ 6 + 2128 * x ^ 7 + 1552 * x ^ 8 + 592 * x ^ 9 + 96 * x ^ 10 := by
  linear_combination (1 / 32 : ℝ) * nhLUJ0_p0_g0_bp0 (2 * x - 1) (2 - 2 * x) (by linarith) (by linarith)

theorem nhLUJ0_p0_g0 (x : ℝ) (h0 : (1 / 2) ≤ x) (h1 : x ≤ 1) :
    0 < -128 * x ^ 3 - 320 * x ^ 4 + 160 * x ^ 5 + 1424 * x ^ 6 + 2128 * x ^ 7 + 1552 * x ^ 8 + 592 * x ^ 9 + 96 * x ^ 10 := by
  exact nhLUJ0_p0_g0_l0 x h0 h1

private theorem nhLUJ0_p0_g1_bp0 (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    0 ≤ 47385 * a * b ^ 9 + 575820 * a ^ 2 * b ^ 8 + 3123336 * a ^ 3 * b ^ 7 + 9909896 * a ^ 4 * b ^ 6 + 20244752 * a ^ 5 * b ^ 5 + 27589536 * a ^ 6 * b ^ 4 + 25065088 * a ^ 7 * b ^ 3 + 14631184 * a ^ 8 * b ^ 2 + 4977696 * a ^ 9 * b + 751824 * a ^ 10 := by positivity

private theorem nhLUJ0_p0_g1_l0 (x : ℝ) (h0 : (1 / 2) ≤ x) (h1 : x ≤ 1) :
    0 < -192 * x ^ 2 - 608 * x ^ 3 + 80 * x ^ 4 + 2504 * x ^ 5 + 4232 * x ^ 6 + 3536 * x ^ 7 + 1736 * x ^ 8 + 472 * x ^ 9 + 48 * x ^ 10 := by
  linear_combination (1 / 64 : ℝ) * nhLUJ0_p0_g1_bp0 (2 * x - 1) (2 - 2 * x) (by linarith) (by linarith)

theorem nhLUJ0_p0_g1 (x : ℝ) (h0 : (1 / 2) ≤ x) (h1 : x ≤ 1) :
    0 < -192 * x ^ 2 - 608 * x ^ 3 + 80 * x ^ 4 + 2504 * x ^ 5 + 4232 * x ^ 6 + 3536 * x ^ 7 + 1736 * x ^ 8 + 472 * x ^ 9 + 48 * x ^ 10 := by
  exact nhLUJ0_p0_g1_l0 x h0 h1

private theorem nhLUJ0_p0_g2_bp0 (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    0 ≤ 62775 * a * b ^ 8 + 664056 * a ^ 2 * b ^ 7 + 3074616 * a ^ 3 * b ^ 6 + 8129416 * a ^ 4 * b ^ 5 + 13416864 * a ^ 5 * b ^ 4 + 14149664 * a ^ 6 * b ^ 3 + 9312224 * a ^ 7 * b ^ 2 + 3497592 * a ^ 8 * b + 574264 * a ^ 9 := by positivity

private theorem nhLUJ0_p0_g2_l0 (x : ℝ) (h0 : (1 / 2) ≤ x) (h1 : x ≤ 1) :
    0 < -672 * x ^ 2 - 432 * x ^ 3 + 2344 * x ^ 4 + 3820 * x ^ 5 + 2376 * x ^ 6 + 1024 * x ^ 7 + 484 * x ^ 8 + 120 * x ^ 9 := by
  linear_combination (1 / 64 : ℝ) * nhLUJ0_p0_g2_bp0 (2 * x - 1) (2 - 2 * x) (by linarith) (by linarith)

theorem nhLUJ0_p0_g2 (x : ℝ) (h0 : (1 / 2) ≤ x) (h1 : x ≤ 1) :
    0 < -672 * x ^ 2 - 432 * x ^ 3 + 2344 * x ^ 4 + 3820 * x ^ 5 + 2376 * x ^ 6 + 1024 * x ^ 7 + 484 * x ^ 8 + 120 * x ^ 9 := by
  exact nhLUJ0_p0_g2_l0 x h0 h1

private theorem nhLUJ0_p0_g3_bp0 (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    0 ≤ 36315 * a * b ^ 7 + 329652 * a ^ 2 * b ^ 6 + 1273704 * a ^ 3 * b ^ 5 + 2710584 * a ^ 4 * b ^ 4 + 3427248 * a ^ 5 * b ^ 3 + 2572608 * a ^ 6 * b ^ 2 + 1060992 * a ^ 7 * b + 185424 * a ^ 8 := by positivity

private theorem nhLUJ0_p0_g3_l0 (x : ℝ) (h0 : (1 / 2) ≤ x) (h1 : x ≤ 1) :
    0 < -720 * x ^ 2 + 504 * x ^ 3 + 2316 * x ^ 4 + 1206 * x ^ 5 - 234 * x ^ 6 - 150 * x ^ 7 + 36 * x ^ 8 := by
  linear_combination (1 / 64 : ℝ) * nhLUJ0_p0_g3_bp0 (2 * x - 1) (2 - 2 * x) (by linarith) (by linarith)

theorem nhLUJ0_p0_g3 (x : ℝ) (h0 : (1 / 2) ≤ x) (h1 : x ≤ 1) :
    0 < -720 * x ^ 2 + 504 * x ^ 3 + 2316 * x ^ 4 + 1206 * x ^ 5 - 234 * x ^ 6 - 150 * x ^ 7 + 36 * x ^ 8 := by
  exact nhLUJ0_p0_g3_l0 x h0 h1

private theorem nhLUJ0_p0_g4_bp0 (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    0 ≤ 7695 * a * b ^ 6 + 59166 * a ^ 2 * b ^ 5 + 186084 * a ^ 3 * b ^ 4 + 304524 * a ^ 4 * b ^ 3 + 271476 * a ^ 5 * b ^ 2 + 123660 * a ^ 6 * b + 22068 * a ^ 7 := by positivity

private theorem nhLUJ0_p0_g4_l0 (x : ℝ) (h0 : (1 / 2) ≤ x) (h1 : x ≤ 1) :
    0 < -216 * x ^ 2 + 324 * x ^ 3 + 522 * x ^ 4 - 9 * x ^ 5 - 207 * x ^ 6 - 54 * x ^ 7 := by
  linear_combination (1 / 64 : ℝ) * nhLUJ0_p0_g4_bp0 (2 * x - 1) (2 - 2 * x) (by linarith) (by linarith)

theorem nhLUJ0_p0_g4 (x : ℝ) (h0 : (1 / 2) ≤ x) (h1 : x ≤ 1) :
    0 < -216 * x ^ 2 + 324 * x ^ 3 + 522 * x ^ 4 - 9 * x ^ 5 - 207 * x ^ 6 - 54 * x ^ 7 := by
  exact nhLUJ0_p0_g4_l0 x h0 h1

theorem nhLUJ0_p0 (x t : ℝ) (hx0 : (1 / 2) ≤ x) (hx1 : x ≤ 1)
    (hs0 : (1 / 2) - (1 / 2) * x ≤ t) (hs1 : t ≤ (1 / 4)) (hgap : (0 : ℝ) < ((1 / 4)) - ((1 / 2) - (1 / 2) * x)) :
    0 < nhLUJ0 t x := by
  have hpos := nh_bern_pos4 (a := (t - ((1 / 2) - (1 / 2) * x))) (b := (((1 / 4)) - t)) (by linarith) (by linarith) (hgap.trans_eq (by ring))
    (nhLUJ0_p0_g0 x hx0 hx1) (nhLUJ0_p0_g1 x hx0 hx1) (nhLUJ0_p0_g2 x hx0 hx1) (nhLUJ0_p0_g3 x hx0 hx1) (nhLUJ0_p0_g4 x hx0 hx1)
  have e : 32 * (((1 / 4)) - ((1 / 2) - (1 / 2) * x)) ^ 4 * (nhLUJ0 t x) = (-128 * x ^ 3 - 320 * x ^ 4 + 160 * x ^ 5 + 1424 * x ^ 6 + 2128 * x ^ 7 + 1552 * x ^ 8 + 592 * x ^ 9 + 96 * x ^ 10) * (((1 / 4)) - t) ^ 4 + (-192 * x ^ 2 - 608 * x ^ 3 + 80 * x ^ 4 + 2504 * x ^ 5 + 4232 * x ^ 6 + 3536 * x ^ 7 + 1736 * x ^ 8 + 472 * x ^ 9 + 48 * x ^ 10) * (t - ((1 / 2) - (1 / 2) * x)) * (((1 / 4)) - t) ^ 3 + (-672 * x ^ 2 - 432 * x ^ 3 + 2344 * x ^ 4 + 3820 * x ^ 5 + 2376 * x ^ 6 + 1024 * x ^ 7 + 484 * x ^ 8 + 120 * x ^ 9) * (t - ((1 / 2) - (1 / 2) * x)) ^ 2 * (((1 / 4)) - t) ^ 2 + (-720 * x ^ 2 + 504 * x ^ 3 + 2316 * x ^ 4 + 1206 * x ^ 5 - 234 * x ^ 6 - 150 * x ^ 7 + 36 * x ^ 8) * (t - ((1 / 2) - (1 / 2) * x)) ^ 3 * (((1 / 4)) - t) + (-216 * x ^ 2 + 324 * x ^ 3 + 522 * x ^ 4 - 9 * x ^ 5 - 207 * x ^ 6 - 54 * x ^ 7) * (t - ((1 / 2) - (1 / 2) * x)) ^ 4 := by unfold nhLUJ0; ring
  have h2 : 0 < 32 * (((1 / 4)) - ((1 / 2) - (1 / 2) * x)) ^ 4 * (nhLUJ0 t x) := lt_of_lt_of_eq hpos e.symm
  exact pos_of_mul_pos_right h2 (by positivity)

private theorem nhLUJ0_p1_g0_bp0 (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    0 ≤ 3118495788 * a * b ^ 4 + 13991778648 * a ^ 2 * b ^ 3 + 23617238040 * a ^ 3 * b ^ 2 + 17772095628 * a ^ 4 * b + 5029793820 * a ^ 5 := by positivity

private theorem nhLUJ0_p1_g0_l0 (x : ℝ) (h0 : 1 ≤ x) (h1 : x ≤ (4 / 3)) :
    0 < 918330048 * x ^ 3 + 1147912560 * x ^ 4 + 401769396 * x ^ 5 := by
  linear_combination (1 / 1 : ℝ) * nhLUJ0_p1_g0_bp0 (3 * x - 3) (4 - 3 * x) (by linarith) (by linarith)

theorem nhLUJ0_p1_g0 (x : ℝ) (h0 : 1 ≤ x) (h1 : x ≤ (4 / 3)) :
    0 < 918330048 * x ^ 3 + 1147912560 * x ^ 4 + 401769396 * x ^ 5 := by
  exact nhLUJ0_p1_g0_l0 x h0 h1

private theorem nhLUJ0_p1_g1_bp0 (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    0 ≤ 7052812560 * a * b ^ 6 + 45629602992 * a ^ 2 * b ^ 5 + 123031845756 * a ^ 3 * b ^ 4 + 176929970868 * a ^ 4 * b ^ 3 + 143098544700 * a ^ 5 * b ^ 2 + 61702792308 * a ^ 6 * b + 11079144684 * a ^ 7 := by positivity

private theorem nhLUJ0_p1_g1_l0 (x : ℝ) (h0 : 1 ≤ x) (h1 : x ≤ (4 / 3)) :
    0 < -323116128 * x ^ 2 + 2219297616 * x ^ 3 + 3002995944 * x ^ 4 + 893529468 * x ^ 5 - 175021236 * x ^ 6 - 40389516 * x ^ 7 := by
  linear_combination (1 / 1 : ℝ) * nhLUJ0_p1_g1_bp0 (3 * x - 3) (4 - 3 * x) (by linarith) (by linarith)

theorem nhLUJ0_p1_g1 (x : ℝ) (h0 : 1 ≤ x) (h1 : x ≤ (4 / 3)) :
    0 < -323116128 * x ^ 2 + 2219297616 * x ^ 3 + 3002995944 * x ^ 4 + 893529468 * x ^ 5 - 175021236 * x ^ 6 - 40389516 * x ^ 7 := by
  exact nhLUJ0_p1_g1_l0 x h0 h1

private theorem nhLUJ0_p1_g2_bp0 (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    0 ≤ 5669704188 * a * b ^ 6 + 36442684728 * a ^ 2 * b ^ 5 + 97493177880 * a ^ 3 * b ^ 4 + 138895945344 * a ^ 4 * b ^ 3 + 111093511536 * a ^ 5 * b ^ 2 + 47275136880 * a ^ 6 * b + 8357326608 * a ^ 7 := by positivity

private theorem nhLUJ0_p1_g2_l0 (x : ℝ) (h0 : 1 ≤ x) (h1 : x ≤ (4 / 3)) :
    0 < -666177696 * x ^ 2 + 2057424624 * x ^ 3 + 3018392424 * x ^ 4 + 671041584 * x ^ 5 - 424006812 * x ^ 6 - 102220380 * x ^ 7 := by
  linear_combination (1 / 1 : ℝ) * nhLUJ0_p1_g2_bp0 (3 * x - 3) (4 - 3 * x) (by linarith) (by linarith)

theorem nhLUJ0_p1_g2 (x : ℝ) (h0 : 1 ≤ x) (h1 : x ≤ (4 / 3)) :
    0 < -666177696 * x ^ 2 + 2057424624 * x ^ 3 + 3018392424 * x ^ 4 + 671041584 * x ^ 5 - 424006812 * x ^ 6 - 102220380 * x ^ 7 := by
  exact nhLUJ0_p1_g2_l0 x h0 h1

private theorem nhLUJ0_p1_g3_bp0 (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    0 ≤ 50682867696 * a * b ^ 6 + 320608577952 * a ^ 2 * b ^ 5 + 841255589232 * a ^ 3 * b ^ 4 + 1170652131504 * a ^ 4 * b ^ 3 + 909858207312 * a ^ 5 * b ^ 2 + 373801881200 * a ^ 6 * b + 63264870928 * a ^ 7 := by positivity

private theorem nhLUJ0_p1_g3_l0 (x : ℝ) (h0 : 1 ≤ x) (h1 : x ≤ (4 / 3)) :
    0 < -451899648 * x ^ 2 + 896192640 * x ^ 3 + 1401660288 * x ^ 4 + 177457392 * x ^ 5 - 341469216 * x ^ 6 - 85494528 * x ^ 7 := by
  linear_combination (1 / 27 : ℝ) * nhLUJ0_p1_g3_bp0 (3 * x - 3) (4 - 3 * x) (by linarith) (by linarith)

theorem nhLUJ0_p1_g3 (x : ℝ) (h0 : 1 ≤ x) (h1 : x ≤ (4 / 3)) :
    0 < -451899648 * x ^ 2 + 896192640 * x ^ 3 + 1401660288 * x ^ 4 + 177457392 * x ^ 5 - 341469216 * x ^ 6 - 85494528 * x ^ 7 := by
  exact nhLUJ0_p1_g3_l0 x h0 h1

private theorem nhLUJ0_p1_g4_bp0 (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    0 ≤ 151222022064 * a * b ^ 6 + 916254579168 * a ^ 2 * b ^ 5 + 2274784699104 * a ^ 3 * b ^ 4 + 2943795227904 * a ^ 4 * b ^ 3 + 2073772621248 * a ^ 5 * b ^ 2 + 741100505024 * a ^ 6 * b + 101363081792 * a ^ 7 := by positivity

private theorem nhLUJ0_p1_g4_l0 (x : ℝ) (h0 : 1 ≤ x) (h1 : x ≤ (4 / 3)) :
    0 < -100497536 * x ^ 2 + 160586944 * x ^ 3 + 257117472 * x ^ 4 + 5473856 * x ^ 5 - 91441072 * x ^ 6 - 23663664 * x ^ 7 := by
  linear_combination (1 / 729 : ℝ) * nhLUJ0_p1_g4_bp0 (3 * x - 3) (4 - 3 * x) (by linarith) (by linarith)

theorem nhLUJ0_p1_g4 (x : ℝ) (h0 : 1 ≤ x) (h1 : x ≤ (4 / 3)) :
    0 < -100497536 * x ^ 2 + 160586944 * x ^ 3 + 257117472 * x ^ 4 + 5473856 * x ^ 5 - 91441072 * x ^ 6 - 23663664 * x ^ 7 := by
  exact nhLUJ0_p1_g4_l0 x h0 h1

theorem nhLUJ0_p1 (x t : ℝ) (hx0 : 1 ≤ x) (hx1 : x ≤ (4 / 3))
    (hs0 : 0 ≤ t) (hs1 : t ≤ (19 / 81)) (hgap : (0 : ℝ) < ((19 / 81)) - (0)) :
    0 < nhLUJ0 t x := by
  have hpos := nh_bern_pos4 (a := (t - (0))) (b := (((19 / 81)) - t)) (by linarith) (by linarith) (hgap.trans_eq (by ring))
    (nhLUJ0_p1_g0 x hx0 hx1) (nhLUJ0_p1_g1 x hx0 hx1) (nhLUJ0_p1_g2 x hx0 hx1) (nhLUJ0_p1_g3 x hx0 hx1) (nhLUJ0_p1_g4 x hx0 hx1)
  have e : 14348907 * (((19 / 81)) - (0)) ^ 4 * (nhLUJ0 t x) = (918330048 * x ^ 3 + 1147912560 * x ^ 4 + 401769396 * x ^ 5) * (((19 / 81)) - t) ^ 4 + (-323116128 * x ^ 2 + 2219297616 * x ^ 3 + 3002995944 * x ^ 4 + 893529468 * x ^ 5 - 175021236 * x ^ 6 - 40389516 * x ^ 7) * (t - (0)) * (((19 / 81)) - t) ^ 3 + (-666177696 * x ^ 2 + 2057424624 * x ^ 3 + 3018392424 * x ^ 4 + 671041584 * x ^ 5 - 424006812 * x ^ 6 - 102220380 * x ^ 7) * (t - (0)) ^ 2 * (((19 / 81)) - t) ^ 2 + (-451899648 * x ^ 2 + 896192640 * x ^ 3 + 1401660288 * x ^ 4 + 177457392 * x ^ 5 - 341469216 * x ^ 6 - 85494528 * x ^ 7) * (t - (0)) ^ 3 * (((19 / 81)) - t) + (-100497536 * x ^ 2 + 160586944 * x ^ 3 + 257117472 * x ^ 4 + 5473856 * x ^ 5 - 91441072 * x ^ 6 - 23663664 * x ^ 7) * (t - (0)) ^ 4 := by unfold nhLUJ0; ring
  have h2 : 0 < 14348907 * (((19 / 81)) - (0)) ^ 4 * (nhLUJ0 t x) := lt_of_lt_of_eq hpos e.symm
  exact pos_of_mul_pos_right h2 (by positivity)

private theorem nhLUJ0_p2_g0_bp0 (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    0 ≤ 61000000000000 * a * b ^ 4 + 267375000000000 * a ^ 2 * b ^ 3 + 440468750000000 * a ^ 3 * b ^ 2 + 323203125000000 * a ^ 4 * b + 89123046875000 * a ^ 5 := by positivity

private theorem nhLUJ0_p2_g0_l0 (x : ℝ) (h0 : (4 / 3) ≤ x) (h1 : x ≤ (5 / 3)) :
    0 < 843750000000 * x ^ 3 + 1054687500000 * x ^ 4 + 369140625000 * x ^ 5 := by
  linear_combination (1 / 9 : ℝ) * nhLUJ0_p2_g0_bp0 (3 * x - 4) (5 - 3 * x) (by linarith) (by linarith)

theorem nhLUJ0_p2_g0 (x : ℝ) (h0 : (4 / 3) ≤ x) (h1 : x ≤ (5 / 3)) :
    0 < 843750000000 * x ^ 3 + 1054687500000 * x ^ 4 + 369140625000 * x ^ 5 := by
  exact nhLUJ0_p2_g0_l0 x h0 h1

private theorem nhLUJ0_p2_g1_bp0 (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    0 ≤ 1462321000000000 * a * b ^ 6 + 9305792062500000 * a ^ 2 * b ^ 5 + 24680126593750000 * a ^ 3 * b ^ 4 + 34913541265625000 * a ^ 4 * b ^ 3 + 27782661351562500 * a ^ 5 * b ^ 2 + 11790130289062500 * a ^ 6 * b + 2084353679687500 * a ^ 7 := by positivity

private theorem nhLUJ0_p2_g1_l0 (x : ℝ) (h0 : (4 / 3) ≤ x) (h1 : x ≤ (5 / 3)) :
    0 < -214312500000 * x ^ 2 + 2410593750000 * x ^ 3 + 3165046875000 * x ^ 4 + 1003289062500 * x ^ 5 - 116085937500 * x ^ 6 - 26789062500 * x ^ 7 := by
  linear_combination (1 / 81 : ℝ) * nhLUJ0_p2_g1_bp0 (3 * x - 4) (5 - 3 * x) (by linarith) (by linarith)

theorem nhLUJ0_p2_g1 (x : ℝ) (h0 : (4 / 3) ≤ x) (h1 : x ≤ (5 / 3)) :
    0 < -214312500000 * x ^ 2 + 2410593750000 * x ^ 3 + 3165046875000 * x ^ 4 + 1003289062500 * x ^ 5 - 116085937500 * x ^ 6 - 26789062500 * x ^ 7 := by
  exact nhLUJ0_p2_g1_l0 x h0 h1

private theorem nhLUJ0_p2_g2_bp0 (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    0 ≤ 4201983928000000 * a * b ^ 6 + 26593092529500000 * a ^ 2 * b ^ 5 + 70090783072750000 * a ^ 3 * b ^ 4 + 98460681988625000 * a ^ 4 * b ^ 3 + 77734440331218750 * a ^ 5 * b ^ 2 + 32696086145625000 * a ^ 6 * b + 5722645410156250 * a ^ 7 := by positivity

private theorem nhLUJ0_p2_g2_l0 (x : ℝ) (h0 : (4 / 3) ≤ x) (h1 : x ≤ (5 / 3)) :
    0 < -497776500000 * x ^ 2 + 2604764250000 * x ^ 3 + 3596450250000 * x ^ 4 + 987059343750 * x ^ 5 - 299870812500 * x ^ 6 - 71294625000 * x ^ 7 := by
  linear_combination (1 / 243 : ℝ) * nhLUJ0_p2_g2_bp0 (3 * x - 4) (5 - 3 * x) (by linarith) (by linarith)

theorem nhLUJ0_p2_g2 (x : ℝ) (h0 : (4 / 3) ≤ x) (h1 : x ≤ (5 / 3)) :
    0 < -497776500000 * x ^ 2 + 2604764250000 * x ^ 3 + 3596450250000 * x ^ 4 + 987059343750 * x ^ 5 - 299870812500 * x ^ 6 - 71294625000 * x ^ 7 := by
  exact nhLUJ0_p2_g2_l0 x h0 h1

private theorem nhLUJ0_p2_g3_bp0 (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    0 ≤ 5027417886736000 * a * b ^ 6 + 31480458238257000 * a ^ 2 * b ^ 5 + 81968749937189500 * a ^ 3 * b ^ 4 + 113550980304298250 * a ^ 4 * b ^ 3 + 88221739188310875 * a ^ 5 * b ^ 2 + 36426907548016125 * a ^ 6 * b + 6240418081599625 * a ^ 7 := by positivity

private theorem nhLUJ0_p2_g3_l0 (x : ℝ) (h0 : (4 / 3) ≤ x) (h1 : x ≤ (5 / 3)) :
    0 < -383341245000 * x ^ 2 + 1271836121500 * x ^ 3 + 1841231799750 * x ^ 4 + 409320111375 * x ^ 5 - 257885009375 * x ^ 6 - 62990206125 * x ^ 7 := by
  linear_combination (1 / 729 : ℝ) * nhLUJ0_p2_g3_bp0 (3 * x - 4) (5 - 3 * x) (by linarith) (by linarith)

theorem nhLUJ0_p2_g3 (x : ℝ) (h0 : (4 / 3) ≤ x) (h1 : x ≤ (5 / 3)) :
    0 < -383341245000 * x ^ 2 + 1271836121500 * x ^ 3 + 1841231799750 * x ^ 4 + 409320111375 * x ^ 5 - 257885009375 * x ^ 6 - 62990206125 * x ^ 7 := by
  exact nhLUJ0_p2_g3_l0 x h0 h1

private theorem nhLUJ0_p2_g4_bp0 (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    0 ≤ 668826376825600 * a * b ^ 6 + 4089157236648960 * a ^ 2 * b ^ 5 + 10349889167455152 * a ^ 3 * b ^ 4 + 13859720599878160 * a ^ 4 * b ^ 3 + 10335335759822388 * a ^ 5 * b ^ 2 + 4057992104209470 * a ^ 6 * b + 652812475085575 * a ^ 7 := by positivity

private theorem nhLUJ0_p2_g4_l0 (x : ℝ) (h0 : (4 / 3) ≤ x) (h1 : x ≤ (5 / 3)) :
    0 < -97796087872 * x ^ 2 + 239118514320 * x ^ 3 + 359823528288 * x ^ 4 + 58230217612 * x ^ 5 - 73839989734 * x ^ 6 - 18484643625 * x ^ 7 := by
  linear_combination (1 / 729 : ℝ) * nhLUJ0_p2_g4_bp0 (3 * x - 4) (5 - 3 * x) (by linarith) (by linarith)

theorem nhLUJ0_p2_g4 (x : ℝ) (h0 : (4 / 3) ≤ x) (h1 : x ≤ (5 / 3)) :
    0 < -97796087872 * x ^ 2 + 239118514320 * x ^ 3 + 359823528288 * x ^ 4 + 58230217612 * x ^ 5 - 73839989734 * x ^ 6 - 18484643625 * x ^ 7 := by
  exact nhLUJ0_p2_g4_l0 x h0 h1

theorem nhLUJ0_p2 (x t : ℝ) (hx0 : (4 / 3) ≤ x) (hx1 : x ≤ (5 / 3))
    (hs0 : 0 ≤ t) (hs1 : t ≤ (127 / 750)) (hgap : (0 : ℝ) < ((127 / 750)) - (0)) :
    0 < nhLUJ0 t x := by
  have hpos := nh_bern_pos4 (a := (t - (0))) (b := (((127 / 750)) - t)) (by linarith) (by linarith) (hgap.trans_eq (by ring))
    (nhLUJ0_p2_g0 x hx0 hx1) (nhLUJ0_p2_g1 x hx0 hx1) (nhLUJ0_p2_g2 x hx0 hx1) (nhLUJ0_p2_g3 x hx0 hx1) (nhLUJ0_p2_g4 x hx0 hx1)
  have e : 13183593750 * (((127 / 750)) - (0)) ^ 4 * (nhLUJ0 t x) = (843750000000 * x ^ 3 + 1054687500000 * x ^ 4 + 369140625000 * x ^ 5) * (((127 / 750)) - t) ^ 4 + (-214312500000 * x ^ 2 + 2410593750000 * x ^ 3 + 3165046875000 * x ^ 4 + 1003289062500 * x ^ 5 - 116085937500 * x ^ 6 - 26789062500 * x ^ 7) * (t - (0)) * (((127 / 750)) - t) ^ 3 + (-497776500000 * x ^ 2 + 2604764250000 * x ^ 3 + 3596450250000 * x ^ 4 + 987059343750 * x ^ 5 - 299870812500 * x ^ 6 - 71294625000 * x ^ 7) * (t - (0)) ^ 2 * (((127 / 750)) - t) ^ 2 + (-383341245000 * x ^ 2 + 1271836121500 * x ^ 3 + 1841231799750 * x ^ 4 + 409320111375 * x ^ 5 - 257885009375 * x ^ 6 - 62990206125 * x ^ 7) * (t - (0)) ^ 3 * (((127 / 750)) - t) + (-97796087872 * x ^ 2 + 239118514320 * x ^ 3 + 359823528288 * x ^ 4 + 58230217612 * x ^ 5 - 73839989734 * x ^ 6 - 18484643625 * x ^ 7) * (t - (0)) ^ 4 := by unfold nhLUJ0; ring
  have h2 : 0 < 13183593750 * (((127 / 750)) - (0)) ^ 4 * (nhLUJ0 t x) := lt_of_lt_of_eq hpos e.symm
  exact pos_of_mul_pos_right h2 (by positivity)

private theorem nhLUJ0_p3_g0_bp0 (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    0 ≤ 1573607988087909400 * a * b ^ 4 + 7294209696039879360 * a ^ 2 * b ^ 3 + 12751710676314574448 * a ^ 3 * b ^ 2 + 9962426179647032256 * a ^ 4 * b + 2934129243109969784 * a ^ 5 := by positivity

private theorem nhLUJ0_p3_g0_l0 (x : ℝ) (h0 : (5 / 3) ≤ x) (h1 : x ≤ (7 / 3)) :
    0 < 5423204234973888 * x ^ 3 + 6779005293717360 * x ^ 4 + 2372651852801076 * x ^ 5 := by
  linear_combination (1 / 288 : ℝ) * nhLUJ0_p3_g0_bp0 (3 * x - 5) (7 - 3 * x) (by linarith) (by linarith)

theorem nhLUJ0_p3_g0 (x : ℝ) (h0 : (5 / 3) ≤ x) (h1 : x ≤ (7 / 3)) :
    0 < 5423204234973888 * x ^ 3 + 6779005293717360 * x ^ 4 + 2372651852801076 * x ^ 5 := by
  exact nhLUJ0_p3_g0_l0 x h0 h1

private theorem nhLUJ0_p3_g1_bp0 (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    0 ≤ 42936179622699320320 * a * b ^ 6 + 283593870405481879584 * a ^ 2 * b ^ 5 + 781105679185988523840 * a ^ 3 * b ^ 4 + 1147938817473881918848 * a ^ 4 * b ^ 3 + 949034076014308375872 * a ^ 5 * b ^ 2 + 418309132526620687968 * a ^ 6 * b + 76765343519109477760 * a ^ 7 := by positivity

private theorem nhLUJ0_p3_g1_l0 (x : ℝ) (h0 : (5 / 3) ≤ x) (h1 : x ≤ (7 / 3)) :
    0 < -914732795455776 * x ^ 2 + 17576519360344560 * x ^ 3 + 22618584930545208 * x ^ 4 + 7470572487906132 * x ^ 5 - 495480264205212 * x ^ 6 - 114341599431972 * x ^ 7 := by
  linear_combination (1 / 10368 : ℝ) * nhLUJ0_p3_g1_bp0 (3 * x - 5) (7 - 3 * x) (by linarith) (by linarith)

theorem nhLUJ0_p3_g1 (x : ℝ) (h0 : (5 / 3) ≤ x) (h1 : x ≤ (7 / 3)) :
    0 < -914732795455776 * x ^ 2 + 17576519360344560 * x ^ 3 + 22618584930545208 * x ^ 4 + 7470572487906132 * x ^ 5 - 495480264205212 * x ^ 6 - 114341599431972 * x ^ 7 := by
  exact nhLUJ0_p3_g1_l0 x h0 h1

private theorem nhLUJ0_p3_g2_bp0 (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    0 ≤ 142782256941930935560 * a * b ^ 6 + 936608328282129185232 * a ^ 2 * b ^ 5 + 2558756803255825529016 * a ^ 3 * b ^ 4 + 3724273696695183295840 * a ^ 4 * b ^ 3 + 3043884655610259453432 * a ^ 5 * b ^ 2 + 1323519574462219215312 * a ^ 6 * b + 238973370776639101768 * a ^ 7 := by positivity

private theorem nhLUJ0_p3_g2_l0 (x : ℝ) (h0 : (5 / 3) ≤ x) (h1 : x ≤ (7 / 3)) :
    0 < -2332763349893856 * x ^ 2 + 21424637780610768 * x ^ 3 + 28398885012232152 * x ^ 4 + 8720100613913304 * x ^ 5 - 1349295780457812 * x ^ 6 - 317310108516324 * x ^ 7 := by
  linear_combination (1 / 31104 : ℝ) * nhLUJ0_p3_g2_bp0 (3 * x - 5) (7 - 3 * x) (by linarith) (by linarith)

theorem nhLUJ0_p3_g2 (x : ℝ) (h0 : (5 / 3) ≤ x) (h1 : x ≤ (7 / 3)) :
    0 < -2332763349893856 * x ^ 2 + 21424637780610768 * x ^ 3 + 28398885012232152 * x ^ 4 + 8720100613913304 * x ^ 5 - 1349295780457812 * x ^ 6 - 317310108516324 * x ^ 7 := by
  exact nhLUJ0_p3_g2_l0 x h0 h1

private theorem nhLUJ0_p3_g3_bp0 (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    0 ≤ 203611407360099925120 * a * b ^ 6 + 1321213754508379716864 * a ^ 2 * b ^ 5 + 3562516663905934069632 * a ^ 3 * b ^ 4 + 5103618169360043525632 * a ^ 4 * b ^ 3 + 4091332840026062750592 * a ^ 5 * b ^ 2 + 1737180346404105571584 * a ^ 6 * b + 304538855889838235776 * a ^ 7 := by positivity

private theorem nhLUJ0_p3_g3_l0 (x : ℝ) (h0 : (5 / 3) ≤ x) (h1 : x ≤ (7 / 3)) :
    0 < -1979158995669504 * x ^ 2 + 11660246956827392 * x ^ 3 + 15916351236187776 * x ^ 4 + 4459814726007168 * x ^ 5 - 1224198827101888 * x ^ 6 - 293041185792960 * x ^ 7 := by
  linear_combination (1 / 93312 : ℝ) * nhLUJ0_p3_g3_bp0 (3 * x - 5) (7 - 3 * x) (by linarith) (by linarith)

theorem nhLUJ0_p3_g3 (x : ℝ) (h0 : (5 / 3) ≤ x) (h1 : x ≤ (7 / 3)) :
    0 < -1979158995669504 * x ^ 2 + 11660246956827392 * x ^ 3 + 15916351236187776 * x ^ 4 + 4459814726007168 * x ^ 5 - 1224198827101888 * x ^ 6 - 293041185792960 * x ^ 7 := by
  exact nhLUJ0_p3_g3_l0 x h0 h1

private theorem nhLUJ0_p3_g4_bp0 (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    0 ≤ 34366097886689113600 * a * b ^ 6 + 218895988935891041280 * a ^ 2 * b ^ 5 + 576732524114733799936 * a ^ 3 * b ^ 4 + 802462270321281026048 * a ^ 4 * b ^ 3 + 619681055936289114624 * a ^ 5 * b ^ 2 + 250531102020376869888 * a ^ 6 * b + 41105840238964008448 * a ^ 7 := by positivity

private theorem nhLUJ0_p3_g4_l0 (x : ℝ) (h0 : (5 / 3) ≤ x) (h1 : x ≤ (7 / 3)) :
    0 < -558527291586560 * x ^ 2 + 2395427175699456 * x ^ 3 + 3362898447484416 * x ^ 4 + 839910753138176 * x ^ 5 - 370058167143680 * x ^ 6 - 90072676708608 * x ^ 7 := by
  linear_combination (1 / 93312 : ℝ) * nhLUJ0_p3_g4_bp0 (3 * x - 5) (7 - 3 * x) (by linarith) (by linarith)

theorem nhLUJ0_p3_g4 (x : ℝ) (h0 : (5 / 3) ≤ x) (h1 : x ≤ (7 / 3)) :
    0 < -558527291586560 * x ^ 2 + 2395427175699456 * x ^ 3 + 3362898447484416 * x ^ 4 + 839910753138176 * x ^ 5 - 370058167143680 * x ^ 6 - 90072676708608 * x ^ 7 := by
  exact nhLUJ0_p3_g4_l0 x h0 h1

theorem nhLUJ0_p3 (x t : ℝ) (hx0 : (5 / 3) ≤ x) (hx1 : x ≤ (7 / 3))
    (hs0 : 0 ≤ t) (hs1 : t ≤ (449 / 3993)) (hgap : (0 : ℝ) < ((449 / 3993)) - (0)) :
    0 < nhLUJ0 t x := by
  have hpos := nh_bern_pos4 (a := (t - (0))) (b := (((449 / 3993)) - t)) (by linarith) (by linarith) (hgap.trans_eq (by ring))
    (nhLUJ0_p3_g0 x hx0 hx1) (nhLUJ0_p3_g1 x hx0 hx1) (nhLUJ0_p3_g2 x hx0 hx1) (nhLUJ0_p3_g3 x hx0 hx1) (nhLUJ0_p3_g4 x hx0 hx1)
  have e : 84737566171467 * (((449 / 3993)) - (0)) ^ 4 * (nhLUJ0 t x) = (5423204234973888 * x ^ 3 + 6779005293717360 * x ^ 4 + 2372651852801076 * x ^ 5) * (((449 / 3993)) - t) ^ 4 + (-914732795455776 * x ^ 2 + 17576519360344560 * x ^ 3 + 22618584930545208 * x ^ 4 + 7470572487906132 * x ^ 5 - 495480264205212 * x ^ 6 - 114341599431972 * x ^ 7) * (t - (0)) * (((449 / 3993)) - t) ^ 3 + (-2332763349893856 * x ^ 2 + 21424637780610768 * x ^ 3 + 28398885012232152 * x ^ 4 + 8720100613913304 * x ^ 5 - 1349295780457812 * x ^ 6 - 317310108516324 * x ^ 7) * (t - (0)) ^ 2 * (((449 / 3993)) - t) ^ 2 + (-1979158995669504 * x ^ 2 + 11660246956827392 * x ^ 3 + 15916351236187776 * x ^ 4 + 4459814726007168 * x ^ 5 - 1224198827101888 * x ^ 6 - 293041185792960 * x ^ 7) * (t - (0)) ^ 3 * (((449 / 3993)) - t) + (-558527291586560 * x ^ 2 + 2395427175699456 * x ^ 3 + 3362898447484416 * x ^ 4 + 839910753138176 * x ^ 5 - 370058167143680 * x ^ 6 - 90072676708608 * x ^ 7) * (t - (0)) ^ 4 := by unfold nhLUJ0; ring
  have h2 : 0 < 84737566171467 * (((449 / 3993)) - (0)) ^ 4 * (nhLUJ0 t x) := lt_of_lt_of_eq hpos e.symm
  exact pos_of_mul_pos_right h2 (by positivity)

/-- `J_0 > 0` on the unit face. -/
theorem nhLUJ0_dom (t x : ℝ) (hx0 : 1 / 2 < x) (hx1 : x ≤ 7 / 3) (ht0 : 0 ≤ t) (ht1 : t ≤ 1 / 4)
    (hxt : 1 - 2 * t ≤ x) (hT : 3 * (x + 2) ^ 3 * t ≤ -2 * x ^ 3 - x ^ 2 + 10 * x + 12) :
    0 < nhLUJ0 t x := by
  rcases le_total x 1 with hc0 | hc0
  · exact nhLUJ0_p0 x t hx0.le hc0 (by linarith) ht1 (by linarith)
  rcases le_total x (4 / 3) with hc1 | hc1
  · have hT' := nh_T_anti (xa := 1) (by norm_num) hc0 ht0 hT
    exact nhLUJ0_p1 x t hc0 hc1 ht0 (by norm_num at hT' ⊢; linarith) (by norm_num)
  rcases le_total x (5 / 3) with hc2 | hc2
  · have hT' := nh_T_anti (xa := (4 / 3)) (by norm_num) hc1 ht0 hT
    exact nhLUJ0_p2 x t hc1 hc2 ht0 (by norm_num at hT' ⊢; linarith) (by norm_num)
  have hT' := nh_T_anti (xa := (5 / 3)) (by norm_num) hc2 ht0 hT
  exact nhLUJ0_p3 x t hc2 hx1 ht0 (by norm_num at hT' ⊢; linarith) (by norm_num)

/-- The sign `J_1` on the unit face. -/
noncomputable def nhLUJ1 (t x : ℝ) : ℝ :=
  -48 * x ^ 2 + 328 * x ^ 3 + 540 * x ^ 4 + 264 * x ^ 5 + 34 * x ^ 6 + 48 * t * x - 72 * t * x ^ 2 - 1940 * t * x ^ 3 - 3078 * t * x ^ 4 - 2042 * t * x ^ 5 - 728 * t * x ^ 6 - 150 * t * x ^ 7 - 8 * t * x ^ 8 - 240 * t ^ 2 * x + 648 * t ^ 2 * x ^ 2 + 4404 * t ^ 2 * x ^ 3 + 6174 * t ^ 2 * x ^ 4 + 4160 * t ^ 2 * x ^ 5 + 1668 * t ^ 2 * x ^ 6 + 396 * t ^ 2 * x ^ 7 + 32 * t ^ 2 * x ^ 8 + 384 * t ^ 3 * x - 720 * t ^ 3 * x ^ 2 - 4040 * t ^ 3 * x ^ 3 - 4980 * t ^ 3 * x ^ 4 - 2946 * t ^ 3 * x ^ 5 - 1058 * t ^ 3 * x ^ 6 - 246 * t ^ 3 * x ^ 7 - 24 * t ^ 3 * x ^ 8 - 192 * t ^ 4 * x + 192 * t ^ 4 * x ^ 2 + 1248 * t ^ 4 * x ^ 3 + 1344 * t ^ 4 * x ^ 4 + 564 * t ^ 4 * x ^ 5 + 84 * t ^ 4 * x ^ 6

private theorem nhLUJ1_p0_g0_bp0 (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    0 ≤ 79866 * a * b ^ 10 + 1104975 * a ^ 2 * b ^ 9 + 6924420 * a ^ 3 * b ^ 8 + 25825884 * a ^ 4 * b ^ 7 + 63374432 * a ^ 5 * b ^ 6 + 106765088 * a ^ 6 * b ^ 5 + 124919408 * a ^ 7 * b ^ 4 + 100154712 * a ^ 8 * b ^ 3 + 52628488 * a ^ 9 * b ^ 2 + 16359784 * a ^ 10 * b + 2283832 * a ^ 11 := by positivity

private theorem nhLUJ1_p0_g0_l0 (x : ℝ) (h0 : (1 / 2) ≤ x) (h1 : x ≤ 1) :
    0 < -1408 * x ^ 3 - 3776 * x ^ 4 + 1120 * x ^ 5 + 15984 * x ^ 6 + 26256 * x ^ 7 + 21328 * x ^ 8 + 9616 * x ^ 9 + 2240 * x ^ 10 + 192 * x ^ 11 := by
  linear_combination (1 / 32 : ℝ) * nhLUJ1_p0_g0_bp0 (2 * x - 1) (2 - 2 * x) (by linarith) (by linarith)

theorem nhLUJ1_p0_g0 (x : ℝ) (h0 : (1 / 2) ≤ x) (h1 : x ≤ 1) :
    0 < -1408 * x ^ 3 - 3776 * x ^ 4 + 1120 * x ^ 5 + 15984 * x ^ 6 + 26256 * x ^ 7 + 21328 * x ^ 8 + 9616 * x ^ 9 + 2240 * x ^ 10 + 192 * x ^ 11 := by
  exact nhLUJ1_p0_g0_l0 x h0 h1

private theorem nhLUJ1_p0_g1_bp0 (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    0 ≤ 541863 * a * b ^ 10 + 7197021 * a ^ 2 * b ^ 9 + 43226556 * a ^ 3 * b ^ 8 + 154372344 * a ^ 4 * b ^ 7 + 362561800 * a ^ 5 * b ^ 6 + 584560144 * a ^ 6 * b ^ 5 + 654735744 * a ^ 7 * b ^ 4 + 502733504 * a ^ 8 * b ^ 3 + 253148096 * a ^ 9 * b ^ 2 + 75460416 * a ^ 10 * b + 10109376 * a ^ 11 := by positivity

private theorem nhLUJ1_p0_g1_l0 (x : ℝ) (h0 : (1 / 2) ≤ x) (h1 : x ≤ 1) :
    0 < -1344 * x ^ 2 - 6176 * x ^ 3 - 3216 * x ^ 4 + 22168 * x ^ 5 + 50728 * x ^ 6 + 52192 * x ^ 7 + 31048 * x ^ 8 + 10968 * x ^ 9 + 2128 * x ^ 10 + 192 * x ^ 11 := by
  linear_combination (1 / 64 : ℝ) * nhLUJ1_p0_g1_bp0 (2 * x - 1) (2 - 2 * x) (by linarith) (by linarith)

theorem nhLUJ1_p0_g1 (x : ℝ) (h0 : (1 / 2) ≤ x) (h1 : x ≤ 1) :
    0 < -1344 * x ^ 2 - 6176 * x ^ 3 - 3216 * x ^ 4 + 22168 * x ^ 5 + 50728 * x ^ 6 + 52192 * x ^ 7 + 31048 * x ^ 8 + 10968 * x ^ 9 + 2128 * x ^ 10 + 192 * x ^ 11 := by
  exact nhLUJ1_p0_g1_l0 x h0 h1

private theorem nhLUJ1_p0_g2_bp0 (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    0 ≤ 667197 * a * b ^ 9 + 7800003 * a ^ 2 * b ^ 8 + 40640760 * a ^ 3 * b ^ 7 + 123735864 * a ^ 4 * b ^ 6 + 242420168 * a ^ 5 * b ^ 5 + 316781264 * a ^ 6 * b ^ 4 + 276017600 * a ^ 7 * b ^ 3 + 154610464 * a ^ 8 * b ^ 2 + 50517952 * a ^ 9 * b + 7336096 * a ^ 10 := by positivity

private theorem nhLUJ1_p0_g2_l0 (x : ℝ) (h0 : (1 / 2) ≤ x) (h1 : x ≤ 1) :
    0 < 192 * x - 5376 * x ^ 2 - 5280 * x ^ 3 + 17088 * x ^ 4 + 37100 * x ^ 5 + 34912 * x ^ 6 + 23024 * x ^ 7 + 11012 * x ^ 8 + 2824 * x ^ 9 + 224 * x ^ 10 := by
  linear_combination (1 / 64 : ℝ) * nhLUJ1_p0_g2_bp0 (2 * x - 1) (2 - 2 * x) (by linarith) (by linarith)

theorem nhLUJ1_p0_g2 (x : ℝ) (h0 : (1 / 2) ≤ x) (h1 : x ≤ 1) :
    0 < 192 * x - 5376 * x ^ 2 - 5280 * x ^ 3 + 17088 * x ^ 4 + 37100 * x ^ 5 + 34912 * x ^ 6 + 23024 * x ^ 7 + 11012 * x ^ 8 + 2824 * x ^ 9 + 224 * x ^ 10 := by
  exact nhLUJ1_p0_g2_l0 x h0 h1

private theorem nhLUJ1_p0_g3_bp0 (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    0 ≤ 347733 * a * b ^ 8 + 3487671 * a ^ 2 * b ^ 7 + 15229092 * a ^ 3 * b ^ 6 + 37757016 * a ^ 4 * b ^ 5 + 58072184 * a ^ 5 * b ^ 4 + 56696688 * a ^ 6 * b ^ 3 + 34293888 * a ^ 7 * b ^ 2 + 11743936 * a ^ 8 * b + 1742400 * a ^ 9 := by positivity

private theorem nhLUJ1_p0_g3_l0 (x : ℝ) (h0 : (1 / 2) ≤ x) (h1 : x ≤ 1) :
    0 < 384 * x - 6768 * x ^ 2 + 4552 * x ^ 3 + 21364 * x ^ 4 + 11474 * x ^ 5 - 1410 * x ^ 6 - 1430 * x ^ 7 - 100 * x ^ 8 - 112 * x ^ 9 := by
  linear_combination (1 / 64 : ℝ) * nhLUJ1_p0_g3_bp0 (2 * x - 1) (2 - 2 * x) (by linarith) (by linarith)

theorem nhLUJ1_p0_g3 (x : ℝ) (h0 : (1 / 2) ≤ x) (h1 : x ≤ 1) :
    0 < 384 * x - 6768 * x ^ 2 + 4552 * x ^ 3 + 21364 * x ^ 4 + 11474 * x ^ 5 - 1410 * x ^ 6 - 1430 * x ^ 7 - 100 * x ^ 8 - 112 * x ^ 9 := by
  exact nhLUJ1_p0_g3_l0 x h0 h1

private theorem nhLUJ1_p0_g4_bp0 (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    0 ≤ 144 * b ^ 8 + 63819 * a * b ^ 7 + 519039 * a ^ 2 * b ^ 6 + 1764162 * a ^ 3 * b ^ 5 + 3184296 * a ^ 4 * b ^ 4 + 3212352 * a ^ 5 * b ^ 3 + 1715760 * a ^ 6 * b ^ 2 + 378912 * a ^ 7 * b := by positivity

private theorem nhLUJ1_p0_g4_l0 (x : ℝ) (h0 : (1 / 2) ≤ x) (h1 : x ≤ 1) :
    0 < 144 * x - 2304 * x ^ 2 + 3840 * x ^ 3 + 5364 * x ^ 4 - 1941 * x ^ 5 - 3837 * x ^ 6 - 1062 * x ^ 7 - 24 * x ^ 8 := by
  linear_combination (1 / 64 : ℝ) * nhLUJ1_p0_g4_bp0 (2 * x - 1) (2 - 2 * x) (by linarith) (by linarith)

theorem nhLUJ1_p0_g4 (x : ℝ) (h0 : (1 / 2) ≤ x) (h1 : x ≤ 1) :
    0 < 144 * x - 2304 * x ^ 2 + 3840 * x ^ 3 + 5364 * x ^ 4 - 1941 * x ^ 5 - 3837 * x ^ 6 - 1062 * x ^ 7 - 24 * x ^ 8 := by
  exact nhLUJ1_p0_g4_l0 x h0 h1

theorem nhLUJ1_p0 (x t : ℝ) (hx0 : (1 / 2) ≤ x) (hx1 : x ≤ 1)
    (hs0 : (1 / 2) - (1 / 2) * x ≤ t) (hs1 : t ≤ (1 / 4)) (hgap : (0 : ℝ) < ((1 / 4)) - ((1 / 2) - (1 / 2) * x)) :
    0 < nhLUJ1 t x := by
  have hpos := nh_bern_pos4 (a := (t - ((1 / 2) - (1 / 2) * x))) (b := (((1 / 4)) - t)) (by linarith) (by linarith) (hgap.trans_eq (by ring))
    (nhLUJ1_p0_g0 x hx0 hx1) (nhLUJ1_p0_g1 x hx0 hx1) (nhLUJ1_p0_g2 x hx0 hx1) (nhLUJ1_p0_g3 x hx0 hx1) (nhLUJ1_p0_g4 x hx0 hx1)
  have e : 64 * (((1 / 4)) - ((1 / 2) - (1 / 2) * x)) ^ 4 * (nhLUJ1 t x) = (-1408 * x ^ 3 - 3776 * x ^ 4 + 1120 * x ^ 5 + 15984 * x ^ 6 + 26256 * x ^ 7 + 21328 * x ^ 8 + 9616 * x ^ 9 + 2240 * x ^ 10 + 192 * x ^ 11) * (((1 / 4)) - t) ^ 4 + (-1344 * x ^ 2 - 6176 * x ^ 3 - 3216 * x ^ 4 + 22168 * x ^ 5 + 50728 * x ^ 6 + 52192 * x ^ 7 + 31048 * x ^ 8 + 10968 * x ^ 9 + 2128 * x ^ 10 + 192 * x ^ 11) * (t - ((1 / 2) - (1 / 2) * x)) * (((1 / 4)) - t) ^ 3 + (192 * x - 5376 * x ^ 2 - 5280 * x ^ 3 + 17088 * x ^ 4 + 37100 * x ^ 5 + 34912 * x ^ 6 + 23024 * x ^ 7 + 11012 * x ^ 8 + 2824 * x ^ 9 + 224 * x ^ 10) * (t - ((1 / 2) - (1 / 2) * x)) ^ 2 * (((1 / 4)) - t) ^ 2 + (384 * x - 6768 * x ^ 2 + 4552 * x ^ 3 + 21364 * x ^ 4 + 11474 * x ^ 5 - 1410 * x ^ 6 - 1430 * x ^ 7 - 100 * x ^ 8 - 112 * x ^ 9) * (t - ((1 / 2) - (1 / 2) * x)) ^ 3 * (((1 / 4)) - t) + (144 * x - 2304 * x ^ 2 + 3840 * x ^ 3 + 5364 * x ^ 4 - 1941 * x ^ 5 - 3837 * x ^ 6 - 1062 * x ^ 7 - 24 * x ^ 8) * (t - ((1 / 2) - (1 / 2) * x)) ^ 4 := by unfold nhLUJ1; ring
  have h2 : 0 < 64 * (((1 / 4)) - ((1 / 2) - (1 / 2) * x)) ^ 4 * (nhLUJ1 t x) := lt_of_lt_of_eq hpos e.symm
  exact pos_of_mul_pos_right h2 (by positivity)

private theorem nhLUJ1_p1_g0_bp0 (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    0 ≤ 11196279945216 * a * b ^ 5 + 57476441044224 * a ^ 2 * b ^ 4 + 118041736223232 * a ^ 3 * b ^ 3 + 121232720563632 * a ^ 4 * b ^ 2 + 62264652178248 * a ^ 5 * b + 12793507073451 * a ^ 6 := by positivity

private theorem nhLUJ1_p1_g0_l0 (x : ℝ) (h0 : 1 ≤ x) (h1 : x ≤ (13 / 12)) :
    0 < -688747536 * x ^ 2 + 4706441496 * x ^ 3 + 7748409780 * x ^ 4 + 3788111448 * x ^ 5 + 487862838 * x ^ 6 := by
  linear_combination (1 / 2048 : ℝ) * nhLUJ1_p1_g0_bp0 (12 * x - 12) (13 - 12 * x) (by linarith) (by linarith)

theorem nhLUJ1_p1_g0 (x : ℝ) (h0 : 1 ≤ x) (h1 : x ≤ (13 / 12)) :
    0 < -688747536 * x ^ 2 + 4706441496 * x ^ 3 + 7748409780 * x ^ 4 + 3788111448 * x ^ 5 + 487862838 * x ^ 6 := by
  exact nhLUJ1_p1_g0_l0 x h0 h1

private theorem nhLUJ1_p1_g1_bp0 (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    0 ≤ 101201996906496 * a * b ^ 7 + 721023372979200 * a ^ 2 * b ^ 6 + 2201602164399360 * a ^ 3 * b ^ 5 + 3734743943535552 * a ^ 4 * b ^ 4 + 3801351473356608 * a ^ 5 * b ^ 3 + 2321503730065836 * a ^ 6 * b ^ 2 + 787644251572311 * a ^ 7 * b + 114528839653674 * a ^ 8 := by positivity

private theorem nhLUJ1_p1_g1_l0 (x : ℝ) (h0 : 1 ≤ x) (h1 : x ≤ (13 / 12)) :
    0 < 161558064 * x - 2997327240 * x ^ 2 + 12296127564 * x ^ 3 + 20633728266 * x ^ 4 + 8279496486 * x ^ 5 - 498845952 * x ^ 6 - 504868950 * x ^ 7 - 26926344 * x ^ 8 := by
  linear_combination (1 / 8192 : ℝ) * nhLUJ1_p1_g1_bp0 (12 * x - 12) (13 - 12 * x) (by linarith) (by linarith)

theorem nhLUJ1_p1_g1 (x : ℝ) (h0 : 1 ≤ x) (h1 : x ≤ (13 / 12)) :
    0 < 161558064 * x - 2997327240 * x ^ 2 + 12296127564 * x ^ 3 + 20633728266 * x ^ 4 + 8279496486 * x ^ 5 - 498845952 * x ^ 6 - 504868950 * x ^ 7 - 26926344 * x ^ 8 := by
  exact nhLUJ1_p1_g1_l0 x h0 h1

private theorem nhLUJ1_p1_g2_bp0 (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    0 ≤ 222396888563712 * a * b ^ 7 + 1579696525771776 * a ^ 2 * b ^ 6 + 4808411892405504 * a ^ 3 * b ^ 5 + 8130448985135616 * a ^ 4 * b ^ 4 + 8247712323870432 * a ^ 5 * b ^ 3 + 5019448650501060 * a ^ 6 * b ^ 2 + 1696897741461441 * a ^ 7 * b + 245824684889464 * a ^ 8 := by positivity

private theorem nhLUJ1_p1_g2_l0 (x : ℝ) (h0 : 1 ≤ x) (h1 : x ≤ (13 / 12)) :
    0 < 295192512 * x - 4347895968 * x ^ 2 + 12126722544 * x ^ 3 + 20285142336 * x ^ 4 + 5394169890 * x ^ 5 - 3106817208 * x ^ 6 - 1201962078 * x ^ 7 - 55514808 * x ^ 8 := by
  linear_combination (1 / 24576 : ℝ) * nhLUJ1_p1_g2_bp0 (12 * x - 12) (13 - 12 * x) (by linarith) (by linarith)

theorem nhLUJ1_p1_g2 (x : ℝ) (h0 : 1 ≤ x) (h1 : x ≤ (13 / 12)) :
    0 < 295192512 * x - 4347895968 * x ^ 2 + 12126722544 * x ^ 3 + 20285142336 * x ^ 4 + 5394169890 * x ^ 5 - 3106817208 * x ^ 6 - 1201962078 * x ^ 7 - 55514808 * x ^ 8 := by
  exact nhLUJ1_p1_g2_l0 x h0 h1

private theorem nhLUJ1_p1_g3_bp0 (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    0 ≤ 676680092983296 * a * b ^ 7 + 4752239663854080 * a ^ 2 * b ^ 6 + 14293954737264384 * a ^ 3 * b ^ 5 + 23868893200397184 * a ^ 4 * b ^ 4 + 23896963734195888 * a ^ 5 * b ^ 3 + 14343765203556534 * a ^ 6 * b ^ 2 + 4779115640807364 * a ^ 7 * b + 681816137416363 * a ^ 8 := by positivity

private theorem nhLUJ1_p1_g3_l0 (x : ℝ) (h0 : 1 ≤ x) (h1 : x ≤ (13 / 12)) :
    0 < 176824944 * x - 2592139320 * x ^ 2 + 5442648660 * x ^ 3 + 8740477854 * x ^ 4 + 556717536 * x ^ 5 - 2961579402 * x ^ 6 - 934874784 * x ^ 7 - 34695216 * x ^ 8 := by
  linear_combination (1 / 331776 : ℝ) * nhLUJ1_p1_g3_bp0 (12 * x - 12) (13 - 12 * x) (by linarith) (by linarith)

theorem nhLUJ1_p1_g3 (x : ℝ) (h0 : 1 ≤ x) (h1 : x ≤ (13 / 12)) :
    0 < 176824944 * x - 2592139320 * x ^ 2 + 5442648660 * x ^ 3 + 8740477854 * x ^ 4 + 556717536 * x ^ 5 - 2961579402 * x ^ 6 - 934874784 * x ^ 7 - 34695216 * x ^ 8 := by
  exact nhLUJ1_p1_g3_l0 x h0 h1

private theorem nhLUJ1_p1_g4_bp0 (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    0 ≤ 241916219945407 * b ^ 8 + 1820048495750648 * a * b ^ 7 + 5860743201512164 * a ^ 2 * b ^ 6 + 10471671590291912 * a ^ 3 * b ^ 5 + 11213222014926394 * a ^ 4 * b ^ 4 + 7196583049348856 * a ^ 5 * b ^ 3 + 2563347854375754 * a ^ 6 * b ^ 2 + 390926155389507 * a ^ 7 * b := by positivity

private theorem nhLUJ1_p1_g4_l0 (x : ℝ) (h0 : 1 ≤ x) (h1 : x ≤ (13 / 12)) :
    0 < 34849952 * x - 544482512 * x ^ 2 + 959825720 * x ^ 3 + 1399037812 * x ^ 4 - 321566968 * x ^ 5 - 837821996 * x ^ 6 - 237781656 * x ^ 7 - 6106752 * x ^ 8 := by
  linear_combination (1 / 1492992 : ℝ) * nhLUJ1_p1_g4_bp0 (12 * x - 12) (13 - 12 * x) (by linarith) (by linarith)

theorem nhLUJ1_p1_g4 (x : ℝ) (h0 : 1 ≤ x) (h1 : x ≤ (13 / 12)) :
    0 < 34849952 * x - 544482512 * x ^ 2 + 959825720 * x ^ 3 + 1399037812 * x ^ 4 - 321566968 * x ^ 5 - 837821996 * x ^ 6 - 237781656 * x ^ 7 - 6106752 * x ^ 8 := by
  exact nhLUJ1_p1_g4_l0 x h0 h1

theorem nhLUJ1_p1 (x t : ℝ) (hx0 : 1 ≤ x) (hx1 : x ≤ (13 / 12))
    (hs0 : 0 ≤ t) (hs1 : t ≤ (19 / 81)) (hgap : (0 : ℝ) < ((19 / 81)) - (0)) :
    0 < nhLUJ1 t x := by
  have hpos := nh_bern_pos4 (a := (t - (0))) (b := (((19 / 81)) - t)) (by linarith) (by linarith) (hgap.trans_eq (by ring))
    (nhLUJ1_p1_g0 x hx0 hx1) (nhLUJ1_p1_g1 x hx0 hx1) (nhLUJ1_p1_g2 x hx0 hx1) (nhLUJ1_p1_g3 x hx0 hx1) (nhLUJ1_p1_g4 x hx0 hx1)
  have e : 14348907 * (((19 / 81)) - (0)) ^ 4 * (nhLUJ1 t x) = (-688747536 * x ^ 2 + 4706441496 * x ^ 3 + 7748409780 * x ^ 4 + 3788111448 * x ^ 5 + 487862838 * x ^ 6) * (((19 / 81)) - t) ^ 4 + (161558064 * x - 2997327240 * x ^ 2 + 12296127564 * x ^ 3 + 20633728266 * x ^ 4 + 8279496486 * x ^ 5 - 498845952 * x ^ 6 - 504868950 * x ^ 7 - 26926344 * x ^ 8) * (t - (0)) * (((19 / 81)) - t) ^ 3 + (295192512 * x - 4347895968 * x ^ 2 + 12126722544 * x ^ 3 + 20285142336 * x ^ 4 + 5394169890 * x ^ 5 - 3106817208 * x ^ 6 - 1201962078 * x ^ 7 - 55514808 * x ^ 8) * (t - (0)) ^ 2 * (((19 / 81)) - t) ^ 2 + (176824944 * x - 2592139320 * x ^ 2 + 5442648660 * x ^ 3 + 8740477854 * x ^ 4 + 556717536 * x ^ 5 - 2961579402 * x ^ 6 - 934874784 * x ^ 7 - 34695216 * x ^ 8) * (t - (0)) ^ 3 * (((19 / 81)) - t) + (34849952 * x - 544482512 * x ^ 2 + 959825720 * x ^ 3 + 1399037812 * x ^ 4 - 321566968 * x ^ 5 - 837821996 * x ^ 6 - 237781656 * x ^ 7 - 6106752 * x ^ 8) * (t - (0)) ^ 4 := by unfold nhLUJ1; ring
  have h2 : 0 < 14348907 * (((19 / 81)) - (0)) ^ 4 * (nhLUJ1 t x) := lt_of_lt_of_eq hpos e.symm
  exact pos_of_mul_pos_right h2 (by positivity)

private theorem nhLUJ1_p2_g0_bp0 (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    0 ≤ 4848297584498696672046922206 * a * b ^ 5 + 24847530803289139485650932629 * a ^ 2 * b ^ 4 + 50944861705842633321542603308 * a ^ 3 * b ^ 3 + 52233593561009229798116127945 * a ^ 4 * b ^ 2 + 26781256451543971208476233162 * a ^ 5 * b + 5493291489497116017579297879 * a ^ 6 := by positivity

private theorem nhLUJ1_p2_g0_l0 (x : ℝ) (h0 : (13 / 12) ≤ x) (h1 : x ≤ (7 / 6)) :
    0 < -8531505799568685724176 * x ^ 2 + 58298622963719352448536 * x ^ 3 + 95979440245147714396980 * x ^ 4 + 46923281897627771482968 * x ^ 5 + 6043149941361152387958 * x ^ 6 := by
  linear_combination (1 / 55296 : ℝ) * nhLUJ1_p2_g0_bp0 (12 * x - 13) (14 - 12 * x) (by linarith) (by linarith)

theorem nhLUJ1_p2_g0 (x : ℝ) (h0 : (13 / 12) ≤ x) (h1 : x ≤ (7 / 6)) :
    0 < -8531505799568685724176 * x ^ 2 + 58298622963719352448536 * x ^ 3 + 95979440245147714396980 * x ^ 4 + 46923281897627771482968 * x ^ 5 + 6043149941361152387958 * x ^ 6 := by
  exact nhLUJ1_p2_g0_l0 x h0 h1

private theorem nhLUJ1_p2_g1_bp0 (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    0 ≤ 614754215484141289514848474625 * a * b ^ 7 + 4374802082071317409788446210826 * a ^ 2 * b ^ 6 + 13342736697148275999999179200148 * a ^ 3 * b ^ 5 + 22608121354725866920942199321916 * a ^ 4 * b ^ 4 + 22984761565649723228134348934720 * a ^ 5 * b ^ 3 + 14020730776108981946273744291112 * a ^ 6 * b ^ 2 + 4751511771763573143555831647408 * a ^ 7 * b + 690110037137400806143623146238 * a ^ 8 := by positivity

private theorem nhLUJ1_p2_g1_l0 (x : ℝ) (h0 : (13 / 12) ≤ x) (h1 : x ≤ (7 / 6)) :
    0 < 1854643440552727802976 * x - 36907988359103834601168 * x ^ 2 + 158235986132537994423864 * x ^ 3 + 264988750355147187222084 * x ^ 4 + 108793504556997123980268 * x ^ 5 - 3956159082938428793304 * x ^ 6 - 5795760751727274384300 * x ^ 7 - 309107240092121300496 * x ^ 8 := by
  linear_combination (1 / 2985984 : ℝ) * nhLUJ1_p2_g1_bp0 (12 * x - 13) (14 - 12 * x) (by linarith) (by linarith)

theorem nhLUJ1_p2_g1 (x : ℝ) (h0 : (13 / 12) ≤ x) (h1 : x ≤ (7 / 6)) :
    0 < 1854643440552727802976 * x - 36907988359103834601168 * x ^ 2 + 158235986132537994423864 * x ^ 3 + 264988750355147187222084 * x ^ 4 + 108793504556997123980268 * x ^ 5 - 3956159082938428793304 * x ^ 6 - 5795760751727274384300 * x ^ 7 - 309107240092121300496 * x ^ 8 := by
  exact nhLUJ1_p2_g1_l0 x h0 h1

private theorem nhLUJ1_p2_g2_bp0 (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    0 ≤ 1425820357262653055359471250269 * a * b ^ 7 + 10118789501160646831145292609894 * a ^ 2 * b ^ 6 + 30773992847790415461712897106452 * a ^ 3 * b ^ 5 + 51991580771650178076484847187180 * a ^ 4 * b ^ 4 + 52698452852888712801766015943296 * a ^ 5 * b ^ 3 + 32046186904613948060145844385832 * a ^ 6 * b ^ 2 + 10825368599393602127628231850288 * a ^ 7 * b + 1567077479896890949215759435726 * a ^ 8 := by positivity

private theorem nhLUJ1_p2_g2_l0 (x : ℝ) (h0 : (13 / 12) ≤ x) (h1 : x ≤ (7 / 6)) :
    0 < 3548048030539565550048 * x - 54092048093879121239472 * x ^ 2 + 161907660657324506290824 * x ^ 3 + 270948181533581719704060 * x ^ 4 + 79782781997947452596916 * x ^ 5 - 34116994973707806588444 * x ^ 6 - 14061076474836103685748 * x ^ 7 - 658537414793881520304 * x ^ 8 := by
  linear_combination (1 / 8957952 : ℝ) * nhLUJ1_p2_g2_bp0 (12 * x - 13) (14 - 12 * x) (by linarith) (by linarith)

theorem nhLUJ1_p2_g2 (x : ℝ) (h0 : (13 / 12) ≤ x) (h1 : x ≤ (7 / 6)) :
    0 < 3548048030539565550048 * x - 54092048093879121239472 * x ^ 2 + 161907660657324506290824 * x ^ 3 + 270948181533581719704060 * x ^ 4 + 79782781997947452596916 * x ^ 5 - 34116994973707806588444 * x ^ 6 - 14061076474836103685748 * x ^ 7 - 658537414793881520304 * x ^ 8 := by
  exact nhLUJ1_p2_g2_l0 x h0 h1

private theorem nhLUJ1_p2_g3_bp0 (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    0 ≤ 360218307127543703846107674925 * a * b ^ 7 + 2533341865468645966429102459074 * a ^ 2 * b ^ 6 + 7632052071733056319818011564548 * a ^ 3 * b ^ 5 + 12767369414224520889173786627436 * a ^ 4 * b ^ 4 + 12808135037863136278611005263552 * a ^ 5 * b ^ 3 + 7705165413666685107493752626376 * a ^ 6 * b ^ 2 + 2573666051160405242461398472048 * a ^ 7 * b + 368194774515256750648965381366 * a ^ 8 := by positivity

private theorem nhLUJ1_p2_g3_l0 (x : ℝ) (h0 : (13 / 12) ≤ x) (h1 : x ≤ (7 / 6)) :
    0 < 2233330191461957935776 * x - 32900837656298375780784 * x ^ 2 + 74925020432730977155720 * x ^ 3 + 121754646494905883720028 * x ^ 4 + 15498931884912493714548 * x ^ 5 - 34124767074456209012840 * x ^ 6 - 11184054171579156406548 * x ^ 7 - 433575887563962279408 * x ^ 8 := by
  linear_combination (1 / 8957952 : ℝ) * nhLUJ1_p2_g3_bp0 (12 * x - 13) (14 - 12 * x) (by linarith) (by linarith)

theorem nhLUJ1_p2_g3 (x : ℝ) (h0 : (13 / 12) ≤ x) (h1 : x ≤ (7 / 6)) :
    0 < 2233330191461957935776 * x - 32900837656298375780784 * x ^ 2 + 74925020432730977155720 * x ^ 3 + 121754646494905883720028 * x ^ 4 + 15498931884912493714548 * x ^ 5 - 34124767074456209012840 * x ^ 6 - 11184054171579156406548 * x ^ 7 - 433575887563962279408 * x ^ 8 := by
  exact nhLUJ1_p2_g3_l0 x h0 h1

private theorem nhLUJ1_p2_g4_bp0 (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    0 ≤ 4368747127316507253302976100 * b ^ 8 + 34284597971483388045921236925 * a * b ^ 7 + 114571931710503515634150245400 * a ^ 2 * b ^ 6 + 211542545390040433259075268300 * a ^ 3 * b ^ 5 + 233238448944619953656684196400 * a ^ 4 * b ^ 4 + 153654146877259167158150692400 * a ^ 5 * b ^ 3 + 56029828170571858715421491200 * a ^ 6 * b ^ 2 + 8727665714813192024621448000 * a ^ 7 * b := by positivity

private theorem nhLUJ1_p2_g4_l0 (x : ℝ) (h0 : (13 / 12) ≤ x) (h1 : x ≤ (7 / 6)) :
    0 < 463713378083538471200 * x - 7109059898562821700800 * x ^ 2 + 13450102396270394004000 * x ^ 3 + 20349260635064708863600 * x ^ 4 - 2189754047452835089900 * x ^ 5 - 9973738277314166604250 * x ^ 6 - 2918738448470327105100 * x ^ 7 - 84145712862202059600 * x ^ 8 := by
  linear_combination (1 / 2985984 : ℝ) * nhLUJ1_p2_g4_bp0 (12 * x - 13) (14 - 12 * x) (by linarith) (by linarith)

theorem nhLUJ1_p2_g4 (x : ℝ) (h0 : (13 / 12) ≤ x) (h1 : x ≤ (7 / 6)) :
    0 < 463713378083538471200 * x - 7109059898562821700800 * x ^ 2 + 13450102396270394004000 * x ^ 3 + 20349260635064708863600 * x ^ 4 - 2189754047452835089900 * x ^ 5 - 9973738277314166604250 * x ^ 6 - 2918738448470327105100 * x ^ 7 - 84145712862202059600 * x ^ 8 := by
  exact nhLUJ1_p2_g4_l0 x h0 h1

theorem nhLUJ1_p2 (x t : ℝ) (hx0 : (13 / 12) ≤ x) (hx1 : x ≤ (7 / 6))
    (hs0 : 0 ≤ t) (hs1 : t ≤ (33034 / 151959)) (hgap : (0 : ℝ) < ((33034 / 151959)) - (0)) :
    0 < nhLUJ1 t x := by
  have hpos := nh_bern_pos4 (a := (t - (0))) (b := (((33034 / 151959)) - t)) (by linarith) (by linarith) (hgap.trans_eq (by ring))
    (nhLUJ1_p2_g0 x hx0 hx1) (nhLUJ1_p2_g1 x hx0 hx1) (nhLUJ1_p2_g2 x hx0 hx1) (nhLUJ1_p2_g3 x hx0 hx1) (nhLUJ1_p2_g4 x hx0 hx1)
  have e : 177739704157680952587 * (((33034 / 151959)) - (0)) ^ 4 * (nhLUJ1 t x) = (-8531505799568685724176 * x ^ 2 + 58298622963719352448536 * x ^ 3 + 95979440245147714396980 * x ^ 4 + 46923281897627771482968 * x ^ 5 + 6043149941361152387958 * x ^ 6) * (((33034 / 151959)) - t) ^ 4 + (1854643440552727802976 * x - 36907988359103834601168 * x ^ 2 + 158235986132537994423864 * x ^ 3 + 264988750355147187222084 * x ^ 4 + 108793504556997123980268 * x ^ 5 - 3956159082938428793304 * x ^ 6 - 5795760751727274384300 * x ^ 7 - 309107240092121300496 * x ^ 8) * (t - (0)) * (((33034 / 151959)) - t) ^ 3 + (3548048030539565550048 * x - 54092048093879121239472 * x ^ 2 + 161907660657324506290824 * x ^ 3 + 270948181533581719704060 * x ^ 4 + 79782781997947452596916 * x ^ 5 - 34116994973707806588444 * x ^ 6 - 14061076474836103685748 * x ^ 7 - 658537414793881520304 * x ^ 8) * (t - (0)) ^ 2 * (((33034 / 151959)) - t) ^ 2 + (2233330191461957935776 * x - 32900837656298375780784 * x ^ 2 + 74925020432730977155720 * x ^ 3 + 121754646494905883720028 * x ^ 4 + 15498931884912493714548 * x ^ 5 - 34124767074456209012840 * x ^ 6 - 11184054171579156406548 * x ^ 7 - 433575887563962279408 * x ^ 8) * (t - (0)) ^ 3 * (((33034 / 151959)) - t) + (463713378083538471200 * x - 7109059898562821700800 * x ^ 2 + 13450102396270394004000 * x ^ 3 + 20349260635064708863600 * x ^ 4 - 2189754047452835089900 * x ^ 5 - 9973738277314166604250 * x ^ 6 - 2918738448470327105100 * x ^ 7 - 84145712862202059600 * x ^ 8) * (t - (0)) ^ 4 := by unfold nhLUJ1; ring
  have h2 : 0 < 177739704157680952587 * (((33034 / 151959)) - (0)) ^ 4 * (nhLUJ1 t x) := lt_of_lt_of_eq hpos e.symm
  exact pos_of_mul_pos_right h2 (by positivity)

private theorem nhLUJ1_p3_g0_bp0 (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    0 ≤ 64916495589801635203746 * a * b ^ 5 + 339852790503546745275225 * a ^ 2 * b ^ 4 + 712044046411889366585164 * a ^ 3 * b ^ 3 + 746290873992887548891137 * a ^ 4 * b ^ 2 + 391281626067553916747418 * a ^ 5 * b + 82098541199164248494703 * a ^ 6 := by positivity

private theorem nhLUJ1_p3_g0_l0 (x : ℝ) (h0 : (7 / 6) ≤ x) (h1 : x ≤ (4 / 3)) :
    0 < -2868456135109744656 * x ^ 2 + 19601116923249921816 * x ^ 3 + 32270131519984627380 * x ^ 4 + 15776508743103595608 * x ^ 5 + 2031823095702735798 * x ^ 6 := by
  linear_combination (1 / 864 : ℝ) * nhLUJ1_p3_g0_bp0 (6 * x - 7) (8 - 6 * x) (by linarith) (by linarith)

theorem nhLUJ1_p3_g0 (x : ℝ) (h0 : (7 / 6) ≤ x) (h1 : x ≤ (4 / 3)) :
    0 < -2868456135109744656 * x ^ 2 + 19601116923249921816 * x ^ 3 + 32270131519984627380 * x ^ 4 + 15776508743103595608 * x ^ 5 + 2031823095702735798 * x ^ 6 := by
  exact nhLUJ1_p3_g0_l0 x h0 h1

private theorem nhLUJ1_p3_g1_bp0 (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    0 ≤ 2134143788950911287105387 * a * b ^ 7 + 15405791025887129355130014 * a ^ 2 * b ^ 6 + 47664321741742875381829628 * a ^ 3 * b ^ 5 + 81931507530696704032863006 * a ^ 4 * b ^ 4 + 84503562139103397785816792 * a ^ 5 * b ^ 3 + 52295008088315197499795388 * a ^ 6 * b ^ 2 + 17979490693724673946963400 * a ^ 7 * b + 2649211717956154730315385 * a ^ 8 := by positivity

private theorem nhLUJ1_p3_g1_l0 (x : ℝ) (h0 : (7 / 6) ≤ x) (h1 : x ≤ (4 / 3)) :
    0 < 576005285040261696 * x - 12337832467999371168 * x ^ 2 + 55124254089289110384 * x ^ 3 + 92144187176731728264 * x ^ 4 + 38601810137993249448 * x ^ 5 - 608787773633025864 * x ^ 6 - 1800016515750817800 * x ^ 7 - 96000880840043616 * x ^ 8 := by
  linear_combination (1 / 11664 : ℝ) * nhLUJ1_p3_g1_bp0 (6 * x - 7) (8 - 6 * x) (by linarith) (by linarith)

theorem nhLUJ1_p3_g1 (x : ℝ) (h0 : (7 / 6) ≤ x) (h1 : x ≤ (4 / 3)) :
    0 < 576005285040261696 * x - 12337832467999371168 * x ^ 2 + 55124254089289110384 * x ^ 3 + 92144187176731728264 * x ^ 4 + 38601810137993249448 * x ^ 5 - 608787773633025864 * x ^ 6 - 1800016515750817800 * x ^ 7 - 96000880840043616 * x ^ 8 := by
  exact nhLUJ1_p3_g1_l0 x h0 h1

private theorem nhLUJ1_p3_g2_bp0 (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    0 ≤ 5208655608522092154188245 * a * b ^ 7 + 37417368643721076689561271 * a ^ 2 * b ^ 6 + 115172211041389296211308988 * a ^ 3 * b ^ 5 + 196898097580086547877604360 * a ^ 4 * b ^ 4 + 201913875582570543723896608 * a ^ 5 * b ^ 3 + 124196349047224930345544976 * a ^ 6 * b ^ 2 + 42426028261043007000797920 * a ^ 7 * b + 6208955218098797672511516 * a ^ 8 := by positivity

private theorem nhLUJ1_p3_g2_l0 (x : ℝ) (h0 : (7 / 6) ≤ x) (h1 : x ≤ (4 / 3)) :
    0 < 1149687178008873408 * x - 18241273165137484032 * x ^ 2 + 58378391953371379584 * x ^ 3 + 97689277628991348480 * x ^ 4 + 31170741691964643816 * x ^ 5 - 9997917589187706204 * x ^ 6 - 4445807230017799128 * x ^ 7 - 210892152238542624 * x ^ 8 := by
  linear_combination (1 / 34992 : ℝ) * nhLUJ1_p3_g2_bp0 (6 * x - 7) (8 - 6 * x) (by linarith) (by linarith)

theorem nhLUJ1_p3_g2 (x : ℝ) (h0 : (7 / 6) ≤ x) (h1 : x ≤ (4 / 3)) :
    0 < 1149687178008873408 * x - 18241273165137484032 * x ^ 2 + 58378391953371379584 * x ^ 3 + 97689277628991348480 * x ^ 4 + 31170741691964643816 * x ^ 5 - 9997917589187706204 * x ^ 6 - 4445807230017799128 * x ^ 7 - 210892152238542624 * x ^ 8 := by
  exact nhLUJ1_p3_g2_l0 x h0 h1

private theorem nhLUJ1_p3_g3_bp0 (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    0 ≤ 1457433882947239544509435 * a * b ^ 7 + 10320328286430948557817882 * a ^ 2 * b ^ 6 + 31277892000564545008204828 * a ^ 3 * b ^ 5 + 52585502155956198662080326 * a ^ 4 * b ^ 4 + 52958650367430930714141688 * a ^ 5 * b ^ 3 + 31943011231233128046629772 * a ^ 6 * b ^ 2 + 10682551898178112002372904 * a ^ 7 * b + 1527686472471491778228069 * a ^ 8 := by positivity

private theorem nhLUJ1_p3_g3_l0 (x : ℝ) (h0 : (7 / 6) ≤ x) (h1 : x ≤ (4 / 3)) :
    0 < 757170161980806336 * x - 11291270331248041824 * x ^ 2 + 27833595814222166800 * x ^ 3 + 45616774828044911928 * x ^ 4 + 8216564104986301368 * x ^ 5 - 10554129311714109320 * x ^ 6 - 3610600508164982808 * x ^ 7 - 145394890774694688 * x ^ 8 := by
  linear_combination (1 / 34992 : ℝ) * nhLUJ1_p3_g3_bp0 (6 * x - 7) (8 - 6 * x) (by linarith) (by linarith)

theorem nhLUJ1_p3_g3 (x : ℝ) (h0 : (7 / 6) ≤ x) (h1 : x ≤ (4 / 3)) :
    0 < 757170161980806336 * x - 11291270331248041824 * x ^ 2 + 27833595814222166800 * x ^ 3 + 45616774828044911928 * x ^ 4 + 8216564104986301368 * x ^ 5 - 10554129311714109320 * x ^ 6 - 3610600508164982808 * x ^ 7 - 145394890774694688 * x ^ 8 := by
  exact nhLUJ1_p3_g3_l0 x h0 h1

private theorem nhLUJ1_p3_g4_bp0 (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    0 ≤ 29562705363887438479165 * b ^ 8 + 258861633717875655258220 * a * b ^ 7 + 948243176784625170123675 * a ^ 2 * b ^ 6 + 1895223588342372370013360 * a ^ 3 * b ^ 5 + 2241164846148423144189240 * a ^ 4 * b ^ 4 + 1572483302893979174601760 * a ^ 5 * b ^ 3 + 607381506098609239254400 * a ^ 6 * b ^ 2 + 99783709864979172398080 * a ^ 7 * b := by positivity

private theorem nhLUJ1_p3_g4_l0 (x : ℝ) (h0 : (7 / 6) ≤ x) (h1 : x ≤ (4 / 3)) :
    0 < 164832153358832960 * x - 2500717383346822640 * x ^ 2 + 5099605778636826600 * x ^ 3 + 7932145665374195980 * x ^ 4 - 74073852356938720 * x ^ 5 - 3188660541263819050 * x ^ 6 - 964809793898001480 * x ^ 7 - 30503619376195680 * x ^ 8 := by
  linear_combination (1 / 23328 : ℝ) * nhLUJ1_p3_g4_bp0 (6 * x - 7) (8 - 6 * x) (by linarith) (by linarith)

theorem nhLUJ1_p3_g4 (x : ℝ) (h0 : (7 / 6) ≤ x) (h1 : x ≤ (4 / 3)) :
    0 < 164832153358832960 * x - 2500717383346822640 * x ^ 2 + 5099605778636826600 * x ^ 3 + 7932145665374195980 * x ^ 4 - 74073852356938720 * x ^ 5 - 3188660541263819050 * x ^ 6 - 964809793898001480 * x ^ 7 - 30503619376195680 * x ^ 8 := by
  exact nhLUJ1_p3_g4_l0 x h0 h1

theorem nhLUJ1_p3 (x t : ℝ) (hx0 : (7 / 6) ≤ x) (hx1 : x ≤ (4 / 3))
    (hs0 : 0 ≤ t) (hs1 : t ≤ (4132 / 20577)) (hgap : (0 : ℝ) < ((4132 / 20577)) - (0)) :
    0 < nhLUJ1 t x := by
  have hpos := nh_bern_pos4 (a := (t - (0))) (b := (((4132 / 20577)) - t)) (by linarith) (by linarith) (hgap.trans_eq (by ring))
    (nhLUJ1_p3_g0 x hx0 hx1) (nhLUJ1_p3_g1 x hx0 hx1) (nhLUJ1_p3_g2 x hx0 hx1) (nhLUJ1_p3_g3 x hx0 hx1) (nhLUJ1_p3_g4 x hx0 hx1)
  have e : 59759502814786347 * (((4132 / 20577)) - (0)) ^ 4 * (nhLUJ1 t x) = (-2868456135109744656 * x ^ 2 + 19601116923249921816 * x ^ 3 + 32270131519984627380 * x ^ 4 + 15776508743103595608 * x ^ 5 + 2031823095702735798 * x ^ 6) * (((4132 / 20577)) - t) ^ 4 + (576005285040261696 * x - 12337832467999371168 * x ^ 2 + 55124254089289110384 * x ^ 3 + 92144187176731728264 * x ^ 4 + 38601810137993249448 * x ^ 5 - 608787773633025864 * x ^ 6 - 1800016515750817800 * x ^ 7 - 96000880840043616 * x ^ 8) * (t - (0)) * (((4132 / 20577)) - t) ^ 3 + (1149687178008873408 * x - 18241273165137484032 * x ^ 2 + 58378391953371379584 * x ^ 3 + 97689277628991348480 * x ^ 4 + 31170741691964643816 * x ^ 5 - 9997917589187706204 * x ^ 6 - 4445807230017799128 * x ^ 7 - 210892152238542624 * x ^ 8) * (t - (0)) ^ 2 * (((4132 / 20577)) - t) ^ 2 + (757170161980806336 * x - 11291270331248041824 * x ^ 2 + 27833595814222166800 * x ^ 3 + 45616774828044911928 * x ^ 4 + 8216564104986301368 * x ^ 5 - 10554129311714109320 * x ^ 6 - 3610600508164982808 * x ^ 7 - 145394890774694688 * x ^ 8) * (t - (0)) ^ 3 * (((4132 / 20577)) - t) + (164832153358832960 * x - 2500717383346822640 * x ^ 2 + 5099605778636826600 * x ^ 3 + 7932145665374195980 * x ^ 4 - 74073852356938720 * x ^ 5 - 3188660541263819050 * x ^ 6 - 964809793898001480 * x ^ 7 - 30503619376195680 * x ^ 8) * (t - (0)) ^ 4 := by unfold nhLUJ1; ring
  have h2 : 0 < 59759502814786347 * (((4132 / 20577)) - (0)) ^ 4 * (nhLUJ1 t x) := lt_of_lt_of_eq hpos e.symm
  exact pos_of_mul_pos_right h2 (by positivity)

private theorem nhLUJ1_p4_g0_bp0 (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    0 ≤ 2793750000000000 * a * b ^ 5 + 15146859375000000 * a ^ 2 * b ^ 4 + 32900773437500000 * a ^ 3 * b ^ 3 + 35786847656250000 * a ^ 4 * b ^ 2 + 19491632812500000 * a ^ 5 * b + 4252482421875000 * a ^ 6 := by positivity

private theorem nhLUJ1_p4_g0_l0 (x : ℝ) (h0 : (4 / 3) ≤ x) (h1 : x ≤ (5 / 3)) :
    0 < -1265625000000 * x ^ 2 + 8648437500000 * x ^ 3 + 14238281250000 * x ^ 4 + 6960937500000 * x ^ 5 + 896484375000 * x ^ 6 := by
  linear_combination (1 / 27 : ℝ) * nhLUJ1_p4_g0_bp0 (3 * x - 4) (5 - 3 * x) (by linarith) (by linarith)

theorem nhLUJ1_p4_g0 (x : ℝ) (h0 : (4 / 3) ≤ x) (h1 : x ≤ (5 / 3)) :
    0 < -1265625000000 * x ^ 2 + 8648437500000 * x ^ 3 + 14238281250000 * x ^ 4 + 6960937500000 * x ^ 5 + 896484375000 * x ^ 6 := by
  exact nhLUJ1_p4_g0_l0 x h0 h1

private theorem nhLUJ1_p4_g1_bp0 (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    0 ≤ 196778113437500000 * a * b ^ 7 + 1454734002656250000 * a ^ 2 * b ^ 6 + 4610176469609375000 * a ^ 3 * b ^ 5 + 8118128108882812500 * a ^ 4 * b ^ 4 + 8578168821242187500 * a ^ 5 * b ^ 3 + 5438825155617187500 * a ^ 6 * b ^ 2 + 1915730806625000000 * a ^ 7 * b + 289166939789062500 * a ^ 8 := by positivity

private theorem nhLUJ1_p4_g1_l0 (x : ℝ) (h0 : (4 / 3) ≤ x) (h1 : x ≤ (5 / 3)) :
    0 < 214312500000 * x - 5383968750000 * x ^ 2 + 25931953125000 * x ^ 3 + 43210335937500 * x ^ 4 + 18726539062500 * x ^ 5 + 335531250000 * x ^ 6 - 669726562500 * x ^ 7 - 35718750000 * x ^ 8 := by
  linear_combination (1 / 729 : ℝ) * nhLUJ1_p4_g1_bp0 (3 * x - 4) (5 - 3 * x) (by linarith) (by linarith)

theorem nhLUJ1_p4_g1 (x : ℝ) (h0 : (4 / 3) ≤ x) (h1 : x ≤ (5 / 3)) :
    0 < 214312500000 * x - 5383968750000 * x ^ 2 + 25931953125000 * x ^ 3 + 43210335937500 * x ^ 4 + 18726539062500 * x ^ 5 + 335531250000 * x ^ 6 - 669726562500 * x ^ 7 - 35718750000 * x ^ 8 := by
  exact nhLUJ1_p4_g1_l0 x h0 h1

private theorem nhLUJ1_p4_g2_bp0 (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    0 ≤ 528388109190250000 * a * b ^ 7 + 3877201848292875000 * a ^ 2 * b ^ 6 + 12186972878096312500 * a ^ 3 * b ^ 5 + 21268335035606343750 * a ^ 4 * b ^ 4 + 22253324929057187500 * a ^ 5 * b ^ 3 + 13957746326332312500 * a ^ 6 * b ^ 2 + 4858485348141250000 * a ^ 7 * b + 723888026599218750 * a ^ 8 := by positivity

private theorem nhLUJ1_p4_g2_l0 (x : ℝ) (h0 : (4 / 3) ≤ x) (h1 : x ≤ (5 / 3)) :
    0 < 461486250000 * x - 8068237875000 * x ^ 2 + 29234864812500 * x ^ 3 + 48869153718750 * x ^ 4 + 17559147187500 * x ^ 5 - 3111226312500 * x ^ 6 - 1709785125000 * x ^ 7 - 82962750000 * x ^ 8 := by
  linear_combination (1 / 2187 : ℝ) * nhLUJ1_p4_g2_bp0 (3 * x - 4) (5 - 3 * x) (by linarith) (by linarith)

theorem nhLUJ1_p4_g2 (x : ℝ) (h0 : (4 / 3) ≤ x) (h1 : x ≤ (5 / 3)) :
    0 < 461486250000 * x - 8068237875000 * x ^ 2 + 29234864812500 * x ^ 3 + 48869153718750 * x ^ 4 + 17559147187500 * x ^ 5 - 3111226312500 * x ^ 6 - 1709785125000 * x ^ 7 - 82962750000 * x ^ 8 := by
  exact nhLUJ1_p4_g2_l0 x h0 h1

private theorem nhLUJ1_p4_g3_bp0 (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    0 ≤ 176508391871056000 * a * b ^ 7 + 1271946267634713000 * a ^ 2 * b ^ 6 + 3917359389909428500 * a ^ 3 * b ^ 5 + 6680889231332988750 * a ^ 4 * b ^ 4 + 6810321901130601625 * a ^ 5 * b ^ 3 + 4146645485774612250 * a ^ 6 * b ^ 2 + 1395202005122539000 * a ^ 7 * b + 199910682677369625 * a ^ 8 := by positivity

private theorem nhLUJ1_p4_g3_l0 (x : ℝ) (h0 : (4 / 3) ≤ x) (h1 : x ≤ (5 / 3)) :
    0 < 329196192000 * x - 5139246735000 * x ^ 2 + 14750403542500 * x ^ 3 + 24422865416250 * x ^ 4 + 6405268667625 * x ^ 5 - 3778558200875 * x ^ 6 - 1441884451125 * x ^ 7 - 61841824500 * x ^ 8 := by
  linear_combination (1 / 2187 : ℝ) * nhLUJ1_p4_g3_bp0 (3 * x - 4) (5 - 3 * x) (by linarith) (by linarith)

theorem nhLUJ1_p4_g3 (x : ℝ) (h0 : (4 / 3) ≤ x) (h1 : x ≤ (5 / 3)) :
    0 < 329196192000 * x - 5139246735000 * x ^ 2 + 14750403542500 * x ^ 3 + 24422865416250 * x ^ 4 + 6405268667625 * x ^ 5 - 3778558200875 * x ^ 6 - 1441884451125 * x ^ 7 - 61841824500 * x ^ 8 := by
  exact nhLUJ1_p4_g3_l0 x h0 h1

private theorem nhLUJ1_p4_g4_bp0 (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    0 ≤ 67796421116515 * b ^ 8 + 4758013782448920 * a * b ^ 7 + 29584943811614100 * a ^ 2 * b ^ 6 + 79556675112001416 * a ^ 3 * b ^ 5 + 115248935159446858 * a ^ 4 * b ^ 4 + 94315601982730856 * a ^ 5 * b ^ 3 + 41260075091253592 * a ^ 6 * b ^ 2 + 7531461228230373 * a ^ 7 * b := by positivity

private theorem nhLUJ1_p4_g4_l0 (x : ℝ) (h0 : (4 / 3) ≤ x) (h1 : x ≤ (5 / 3)) :
    0 < 77860127744 * x - 1185190295744 * x ^ 2 + 2826109397664 * x ^ 3 + 4554902584792 * x ^ 4 + 623949840752 * x ^ 5 - 1226464000888 * x ^ 6 - 401825888625 * x ^ 7 - 14597824500 * x ^ 8 := by
  linear_combination (1 / 729 : ℝ) * nhLUJ1_p4_g4_bp0 (3 * x - 4) (5 - 3 * x) (by linarith) (by linarith)

theorem nhLUJ1_p4_g4 (x : ℝ) (h0 : (4 / 3) ≤ x) (h1 : x ≤ (5 / 3)) :
    0 < 77860127744 * x - 1185190295744 * x ^ 2 + 2826109397664 * x ^ 3 + 4554902584792 * x ^ 4 + 623949840752 * x ^ 5 - 1226464000888 * x ^ 6 - 401825888625 * x ^ 7 - 14597824500 * x ^ 8 := by
  exact nhLUJ1_p4_g4_l0 x h0 h1

theorem nhLUJ1_p4 (x t : ℝ) (hx0 : (4 / 3) ≤ x) (hx1 : x ≤ (5 / 3))
    (hs0 : 0 ≤ t) (hs1 : t ≤ (127 / 750)) (hgap : (0 : ℝ) < ((127 / 750)) - (0)) :
    0 < nhLUJ1 t x := by
  have hpos := nh_bern_pos4 (a := (t - (0))) (b := (((127 / 750)) - t)) (by linarith) (by linarith) (hgap.trans_eq (by ring))
    (nhLUJ1_p4_g0 x hx0 hx1) (nhLUJ1_p4_g1 x hx0 hx1) (nhLUJ1_p4_g2 x hx0 hx1) (nhLUJ1_p4_g3 x hx0 hx1) (nhLUJ1_p4_g4 x hx0 hx1)
  have e : 26367187500 * (((127 / 750)) - (0)) ^ 4 * (nhLUJ1 t x) = (-1265625000000 * x ^ 2 + 8648437500000 * x ^ 3 + 14238281250000 * x ^ 4 + 6960937500000 * x ^ 5 + 896484375000 * x ^ 6) * (((127 / 750)) - t) ^ 4 + (214312500000 * x - 5383968750000 * x ^ 2 + 25931953125000 * x ^ 3 + 43210335937500 * x ^ 4 + 18726539062500 * x ^ 5 + 335531250000 * x ^ 6 - 669726562500 * x ^ 7 - 35718750000 * x ^ 8) * (t - (0)) * (((127 / 750)) - t) ^ 3 + (461486250000 * x - 8068237875000 * x ^ 2 + 29234864812500 * x ^ 3 + 48869153718750 * x ^ 4 + 17559147187500 * x ^ 5 - 3111226312500 * x ^ 6 - 1709785125000 * x ^ 7 - 82962750000 * x ^ 8) * (t - (0)) ^ 2 * (((127 / 750)) - t) ^ 2 + (329196192000 * x - 5139246735000 * x ^ 2 + 14750403542500 * x ^ 3 + 24422865416250 * x ^ 4 + 6405268667625 * x ^ 5 - 3778558200875 * x ^ 6 - 1441884451125 * x ^ 7 - 61841824500 * x ^ 8) * (t - (0)) ^ 3 * (((127 / 750)) - t) + (77860127744 * x - 1185190295744 * x ^ 2 + 2826109397664 * x ^ 3 + 4554902584792 * x ^ 4 + 623949840752 * x ^ 5 - 1226464000888 * x ^ 6 - 401825888625 * x ^ 7 - 14597824500 * x ^ 8) * (t - (0)) ^ 4 := by unfold nhLUJ1; ring
  have h2 : 0 < 26367187500 * (((127 / 750)) - (0)) ^ 4 * (nhLUJ1 t x) := lt_of_lt_of_eq hpos e.symm
  exact pos_of_mul_pos_right h2 (by positivity)

private theorem nhLUJ1_p5_g0_bp0 (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    0 ≤ 38714522621014636440 * a * b ^ 5 + 220772769267865758768 * a ^ 2 * b ^ 4 + 505714045985585193680 * a ^ 3 * b ^ 3 + 581529286248877514592 * a ^ 4 * b ^ 2 + 335616877138385091480 * a ^ 5 * b + 77750219448389393136 * a ^ 6 := by positivity

private theorem nhLUJ1_p5_g0_l0 (x : ℝ) (h0 : (5 / 3) ≤ x) (h1 : x ≤ (7 / 3)) :
    0 < -4067403176230416 * x ^ 2 + 27793921704241176 * x ^ 3 + 45758285732592180 * x ^ 4 + 22370717469267288 * x ^ 5 + 2881077249829878 * x ^ 6 := by
  linear_combination (1 / 1728 : ℝ) * nhLUJ1_p5_g0_bp0 (3 * x - 5) (7 - 3 * x) (by linarith) (by linarith)

theorem nhLUJ1_p5_g0 (x : ℝ) (h0 : (5 / 3) ≤ x) (h1 : x ≤ (7 / 3)) :
    0 < -4067403176230416 * x ^ 2 + 27793921704241176 * x ^ 3 + 45758285732592180 * x ^ 4 + 22370717469267288 * x ^ 5 + 2881077249829878 * x ^ 6 := by
  exact nhLUJ1_p5_g0_l0 x h0 h1

private theorem nhLUJ1_p5_g1_bp0 (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    0 ≤ 3101703485098711917248 * a * b ^ 7 + 23769131112116637847512 * a ^ 2 * b ^ 6 + 78137043559964369845568 * a ^ 3 * b ^ 5 + 142802284492001797060728 * a ^ 4 * b ^ 4 + 156662928049733638092032 * a ^ 5 * b ^ 3 + 103143166274639924398152 * a ^ 6 * b ^ 2 + 37724226497976450392576 * a ^ 7 * b + 5911317545759295786600 * a ^ 8 := by positivity

private theorem nhLUJ1_p5_g1_l0 (x : ℝ) (h0 : (5 / 3) ≤ x) (h1 : x ≤ (7 / 3)) :
    0 < 457366397727888 * x - 16955662301513496 * x ^ 2 + 92690461575462564 * x ^ 3 + 153704522676067902 * x ^ 4 + 70025741040395250 * x ^ 5 + 4587585300446544 * x ^ 6 - 1429269992899650 * x ^ 7 - 76227732954648 * x ^ 8 := by
  linear_combination (1 / 186624 : ℝ) * nhLUJ1_p5_g1_bp0 (3 * x - 5) (7 - 3 * x) (by linarith) (by linarith)

theorem nhLUJ1_p5_g1 (x : ℝ) (h0 : (5 / 3) ≤ x) (h1 : x ≤ (7 / 3)) :
    0 < 457366397727888 * x - 16955662301513496 * x ^ 2 + 92690461575462564 * x ^ 3 + 153704522676067902 * x ^ 4 + 70025741040395250 * x ^ 5 + 4587585300446544 * x ^ 6 - 1429269992899650 * x ^ 7 - 76227732954648 * x ^ 8 := by
  exact nhLUJ1_p5_g1_l0 x h0 h1

private theorem nhLUJ1_p5_g2_bp0 (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    0 ≤ 9897886937013493369072 * a * b ^ 7 + 75244573644916901846808 * a ^ 2 * b ^ 6 + 245096090468889363639760 * a ^ 3 * b ^ 5 + 443263397069146220993976 * a ^ 4 * b ^ 4 + 480496819715177767873360 * a ^ 5 * b ^ 3 + 312046111734232108219272 * a ^ 6 * b ^ 2 + 112356307264435936666096 * a ^ 7 * b + 17293005348681953465256 * a ^ 8 := by positivity

private theorem nhLUJ1_p5_g2_l0 (x : ℝ) (h0 : (5 / 3) ≤ x) (h1 : x ≤ (7 / 3)) :
    0 < 1114952295387744 * x - 25768271223109008 * x ^ 2 + 116026500075495768 * x ^ 3 + 193178957578450668 * x ^ 4 + 80310131200711302 * x ^ 5 - 1736536657957992 * x ^ 6 - 3863517597335682 * x ^ 7 - 194396945824488 * x ^ 8 := by
  linear_combination (1 / 559872 : ℝ) * nhLUJ1_p5_g2_bp0 (3 * x - 5) (7 - 3 * x) (by linarith) (by linarith)

theorem nhLUJ1_p5_g2 (x : ℝ) (h0 : (5 / 3) ≤ x) (h1 : x ≤ (7 / 3)) :
    0 < 1114952295387744 * x - 25768271223109008 * x ^ 2 + 116026500075495768 * x ^ 3 + 193178957578450668 * x ^ 4 + 80310131200711302 * x ^ 5 - 1736536657957992 * x ^ 6 - 3863517597335682 * x ^ 7 - 194396945824488 * x ^ 8 := by
  exact nhLUJ1_p5_g2_l0 x h0 h1

private theorem nhLUJ1_p5_g3_bp0 (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    0 ≤ 4359486466418943154240 * a * b ^ 7 + 32681176736634030028776 * a ^ 2 * b ^ 6 + 104725537325606224141840 * a ^ 3 * b ^ 5 + 185795437995785777030520 * a ^ 4 * b ^ 4 + 196892048349279063490336 * a ^ 5 * b ^ 3 + 124479129567950217936216 * a ^ 6 * b ^ 2 + 43406112393059172516496 * a ^ 7 * b + 6427426324470016388424 * a ^ 8 := by positivity

private theorem nhLUJ1_p5_g3_l0 (x : ℝ) (h0 : (5 / 3) ≤ x) (h1 : x ≤ (7 / 3)) :
    0 < 904069943391120 * x - 17025914269972872 * x ^ 2 + 64670560665971788 * x ^ 3 + 107677496730731730 * x ^ 4 + 39670973345002032 * x ^ 5 - 5838988680060206 * x ^ 6 - 3468863440625088 * x ^ 7 - 163002226897488 * x ^ 8 := by
  linear_combination (1 / 559872 : ℝ) * nhLUJ1_p5_g3_bp0 (3 * x - 5) (7 - 3 * x) (by linarith) (by linarith)

theorem nhLUJ1_p5_g3 (x : ℝ) (h0 : (5 / 3) ≤ x) (h1 : x ≤ (7 / 3)) :
    0 < 904069943391120 * x - 17025914269972872 * x ^ 2 + 64670560665971788 * x ^ 3 + 107677496730731730 * x ^ 4 + 39670973345002032 * x ^ 5 - 5838988680060206 * x ^ 6 - 3468863440625088 * x ^ 7 - 163002226897488 * x ^ 8 := by
  exact nhLUJ1_p5_g3_l0 x h0 h1

private theorem nhLUJ1_p5_g4_bp0 (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    0 ≤ 210699123085502656000 * a * b ^ 7 + 1533115668190842429760 * a ^ 2 * b ^ 6 + 4736205848565658909824 * a ^ 3 * b ^ 5 + 8028429521394892078528 * a ^ 4 * b ^ 4 + 8030969206062992772352 * a ^ 5 * b ^ 3 + 4711186587888523800768 * a ^ 6 * b ^ 2 + 1485884899273332574336 * a ^ 7 * b + 191026024263051817024 * a ^ 8 := by positivity

private theorem nhLUJ1_p5_g4_l0 (x : ℝ) (h0 : (5 / 3) ≤ x) (h1 : x ≤ (7 / 3)) :
    0 < 243882896086400 * x - 4143301022502080 * x ^ 2 + 13557507934389024 * x ^ 3 + 22462984143270832 * x ^ 4 + 7023506592500480 * x ^ 5 - 2394805968515920 * x ^ 6 - 1034615836189056 * x ^ 7 - 44833014027648 * x ^ 8 := by
  linear_combination (1 / 186624 : ℝ) * nhLUJ1_p5_g4_bp0 (3 * x - 5) (7 - 3 * x) (by linarith) (by linarith)

theorem nhLUJ1_p5_g4 (x : ℝ) (h0 : (5 / 3) ≤ x) (h1 : x ≤ (7 / 3)) :
    0 < 243882896086400 * x - 4143301022502080 * x ^ 2 + 13557507934389024 * x ^ 3 + 22462984143270832 * x ^ 4 + 7023506592500480 * x ^ 5 - 2394805968515920 * x ^ 6 - 1034615836189056 * x ^ 7 - 44833014027648 * x ^ 8 := by
  exact nhLUJ1_p5_g4_l0 x h0 h1

theorem nhLUJ1_p5 (x t : ℝ) (hx0 : (5 / 3) ≤ x) (hx1 : x ≤ (7 / 3))
    (hs0 : 0 ≤ t) (hs1 : t ≤ (449 / 3993)) (hgap : (0 : ℝ) < ((449 / 3993)) - (0)) :
    0 < nhLUJ1 t x := by
  have hpos := nh_bern_pos4 (a := (t - (0))) (b := (((449 / 3993)) - t)) (by linarith) (by linarith) (hgap.trans_eq (by ring))
    (nhLUJ1_p5_g0 x hx0 hx1) (nhLUJ1_p5_g1 x hx0 hx1) (nhLUJ1_p5_g2 x hx0 hx1) (nhLUJ1_p5_g3 x hx0 hx1) (nhLUJ1_p5_g4 x hx0 hx1)
  have e : 84737566171467 * (((449 / 3993)) - (0)) ^ 4 * (nhLUJ1 t x) = (-4067403176230416 * x ^ 2 + 27793921704241176 * x ^ 3 + 45758285732592180 * x ^ 4 + 22370717469267288 * x ^ 5 + 2881077249829878 * x ^ 6) * (((449 / 3993)) - t) ^ 4 + (457366397727888 * x - 16955662301513496 * x ^ 2 + 92690461575462564 * x ^ 3 + 153704522676067902 * x ^ 4 + 70025741040395250 * x ^ 5 + 4587585300446544 * x ^ 6 - 1429269992899650 * x ^ 7 - 76227732954648 * x ^ 8) * (t - (0)) * (((449 / 3993)) - t) ^ 3 + (1114952295387744 * x - 25768271223109008 * x ^ 2 + 116026500075495768 * x ^ 3 + 193178957578450668 * x ^ 4 + 80310131200711302 * x ^ 5 - 1736536657957992 * x ^ 6 - 3863517597335682 * x ^ 7 - 194396945824488 * x ^ 8) * (t - (0)) ^ 2 * (((449 / 3993)) - t) ^ 2 + (904069943391120 * x - 17025914269972872 * x ^ 2 + 64670560665971788 * x ^ 3 + 107677496730731730 * x ^ 4 + 39670973345002032 * x ^ 5 - 5838988680060206 * x ^ 6 - 3468863440625088 * x ^ 7 - 163002226897488 * x ^ 8) * (t - (0)) ^ 3 * (((449 / 3993)) - t) + (243882896086400 * x - 4143301022502080 * x ^ 2 + 13557507934389024 * x ^ 3 + 22462984143270832 * x ^ 4 + 7023506592500480 * x ^ 5 - 2394805968515920 * x ^ 6 - 1034615836189056 * x ^ 7 - 44833014027648 * x ^ 8) * (t - (0)) ^ 4 := by unfold nhLUJ1; ring
  have h2 : 0 < 84737566171467 * (((449 / 3993)) - (0)) ^ 4 * (nhLUJ1 t x) := lt_of_lt_of_eq hpos e.symm
  exact pos_of_mul_pos_right h2 (by positivity)

/-- `J_1 > 0` on the unit face. -/
theorem nhLUJ1_dom (t x : ℝ) (hx0 : 1 / 2 < x) (hx1 : x ≤ 7 / 3) (ht0 : 0 ≤ t) (ht1 : t ≤ 1 / 4)
    (hxt : 1 - 2 * t ≤ x) (hT : 3 * (x + 2) ^ 3 * t ≤ -2 * x ^ 3 - x ^ 2 + 10 * x + 12) :
    0 < nhLUJ1 t x := by
  rcases le_total x 1 with hc0 | hc0
  · exact nhLUJ1_p0 x t hx0.le hc0 (by linarith) ht1 (by linarith)
  rcases le_total x (13 / 12) with hc1 | hc1
  · have hT' := nh_T_anti (xa := 1) (by norm_num) hc0 ht0 hT
    exact nhLUJ1_p1 x t hc0 hc1 ht0 (by norm_num at hT' ⊢; linarith) (by norm_num)
  rcases le_total x (7 / 6) with hc2 | hc2
  · have hT' := nh_T_anti (xa := (13 / 12)) (by norm_num) hc1 ht0 hT
    exact nhLUJ1_p2 x t hc1 hc2 ht0 (by norm_num at hT' ⊢; linarith) (by norm_num)
  rcases le_total x (4 / 3) with hc3 | hc3
  · have hT' := nh_T_anti (xa := (7 / 6)) (by norm_num) hc2 ht0 hT
    exact nhLUJ1_p3 x t hc2 hc3 ht0 (by norm_num at hT' ⊢; linarith) (by norm_num)
  rcases le_total x (5 / 3) with hc4 | hc4
  · have hT' := nh_T_anti (xa := (4 / 3)) (by norm_num) hc3 ht0 hT
    exact nhLUJ1_p4 x t hc3 hc4 ht0 (by norm_num at hT' ⊢; linarith) (by norm_num)
  have hT' := nh_T_anti (xa := (5 / 3)) (by norm_num) hc4 ht0 hT
  exact nhLUJ1_p5 x t hc4 hx1 ht0 (by norm_num at hT' ⊢; linarith) (by norm_num)

/-- The sign `J_2` on the unit face. -/
noncomputable def nhLUJ2 (t x : ℝ) : ℝ :=
  -152 * x ^ 2 + 3204 * x ^ 3 + 4354 * x ^ 4 + 1717 * x ^ 5 + 95 * x ^ 6 + 6 * x ^ 7 + 40 * t * x - 3988 * t * x ^ 2 - 21330 * t * x ^ 3 - 25435 * t * x ^ 4 - 12960 * t * x ^ 5 - 3773 * t * x ^ 6 - 860 * t * x ^ 7 - 24 * t * x ^ 8 + 48 * t ^ 2 - 128 * t ^ 2 * x + 17296 * t ^ 2 * x ^ 2 + 55396 * t ^ 2 * x ^ 3 + 57673 * t ^ 2 * x ^ 4 + 28237 * t ^ 2 * x ^ 5 + 8262 * t ^ 2 * x ^ 6 + 1724 * t ^ 2 * x ^ 7 + 60 * t ^ 2 * x ^ 8 - 96 * t ^ 3 + 112 * t ^ 3 * x - 22360 * t ^ 3 * x ^ 2 - 60676 * t ^ 3 * x ^ 3 - 57868 * t ^ 3 * x ^ 4 - 25358 * t ^ 3 * x ^ 5 - 5808 * t ^ 3 * x ^ 6 - 876 * t ^ 3 * x ^ 7 - 36 * t ^ 3 * x ^ 8 - 288 * t ^ 4 * x + 8592 * t ^ 4 * x ^ 2 + 22632 * t ^ 4 * x ^ 3 + 20700 * t ^ 4 * x ^ 4 + 8112 * t ^ 4 * x ^ 5 + 1164 * t ^ 4 * x ^ 6

private theorem nhLUJ2_p0_g0_bp0 (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    0 ≤ 1189593 * a * b ^ 10 + 17078220 * a ^ 2 * b ^ 9 + 110016188 * a ^ 3 * b ^ 8 + 418598448 * a ^ 4 * b ^ 7 + 1041487088 * a ^ 5 * b ^ 6 + 1770191552 * a ^ 6 * b ^ 5 + 2081350976 * a ^ 7 * b ^ 4 + 1671523584 * a ^ 8 * b ^ 3 + 877488640 * a ^ 9 * b ^ 2 + 271908352 * a ^ 10 * b + 37767680 * a ^ 11 := by positivity

private theorem nhLUJ2_p0_g0_l0 (x : ℝ) (h0 : (1 / 2) ≤ x) (h1 : x ≤ 1) :
    0 < -256 * x - 1920 * x ^ 2 - 18240 * x ^ 3 - 38624 * x ^ 4 + 16096 * x ^ 5 + 154064 * x ^ 6 + 230720 * x ^ 7 + 169888 * x ^ 8 + 66560 * x ^ 9 + 11760 * x ^ 10 + 288 * x ^ 11 := by
  linear_combination (1 / 64 : ℝ) * nhLUJ2_p0_g0_bp0 (2 * x - 1) (2 - 2 * x) (by linarith) (by linarith)

theorem nhLUJ2_p0_g0 (x : ℝ) (h0 : (1 / 2) ≤ x) (h1 : x ≤ 1) :
    0 < -256 * x - 1920 * x ^ 2 - 18240 * x ^ 3 - 38624 * x ^ 4 + 16096 * x ^ 5 + 154064 * x ^ 6 + 230720 * x ^ 7 + 169888 * x ^ 8 + 66560 * x ^ 9 + 11760 * x ^ 10 + 288 * x ^ 11 := by
  exact nhLUJ2_p0_g0_l0 x h0 h1

private theorem nhLUJ2_p0_g1_bp0 (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    0 ≤ 4046247 * a * b ^ 10 + 55627794 * a ^ 2 * b ^ 9 + 342621320 * a ^ 3 * b ^ 8 + 1245079372 * a ^ 4 * b ^ 7 + 2956688280 * a ^ 5 * b ^ 6 + 4794876064 * a ^ 6 * b ^ 5 + 5378679552 * a ^ 7 * b ^ 4 + 4121696320 * a ^ 8 * b ^ 3 + 2065250176 * a ^ 9 * b ^ 2 + 611106816 * a ^ 10 * b + 81100800 * a ^ 11 := by positivity

private theorem nhLUJ2_p0_g1_l0 (x : ℝ) (h0 : (1 / 2) ≤ x) (h1 : x ≤ 1) :
    0 < 384 - 960 * x - 27808 * x ^ 2 - 82160 * x ^ 3 - 16144 * x ^ 4 + 251576 * x ^ 5 + 462608 * x ^ 6 + 405272 * x ^ 7 + 207360 * x ^ 8 + 60016 * x ^ 9 + 7632 * x ^ 10 + 288 * x ^ 11 := by
  linear_combination (1 / 64 : ℝ) * nhLUJ2_p0_g1_bp0 (2 * x - 1) (2 - 2 * x) (by linarith) (by linarith)

theorem nhLUJ2_p0_g1 (x : ℝ) (h0 : (1 / 2) ≤ x) (h1 : x ≤ 1) :
    0 < 384 - 960 * x - 27808 * x ^ 2 - 82160 * x ^ 3 - 16144 * x ^ 4 + 251576 * x ^ 5 + 462608 * x ^ 6 + 405272 * x ^ 7 + 207360 * x ^ 8 + 60016 * x ^ 9 + 7632 * x ^ 10 + 288 * x ^ 11 := by
  exact nhLUJ2_p0_g1_l0 x h0 h1

private theorem nhLUJ2_p0_g2_bp0 (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    0 ≤ 5001183 * a * b ^ 9 + 60685356 * a ^ 2 * b ^ 8 + 324952216 * a ^ 3 * b ^ 7 + 1008344860 * a ^ 4 * b ^ 6 + 1999445872 * a ^ 5 * b ^ 5 + 2628984512 * a ^ 6 * b ^ 4 + 2293613376 * a ^ 7 * b ^ 3 + 1281104960 * a ^ 8 * b ^ 2 + 415956736 * a ^ 9 * b + 59849728 * a ^ 10 := by positivity

private theorem nhLUJ2_p0_g2_l0 (x : ℝ) (h0 : (1 / 2) ≤ x) (h1 : x ≤ 1) :
    0 < 768 - 800 * x - 80112 * x ^ 2 - 75800 * x ^ 3 + 201868 * x ^ 4 + 385984 * x ^ 5 + 278172 * x ^ 6 + 142224 * x ^ 7 + 67000 * x ^ 8 + 16616 * x ^ 9 + 528 * x ^ 10 := by
  linear_combination (1 / 64 : ℝ) * nhLUJ2_p0_g2_bp0 (2 * x - 1) (2 - 2 * x) (by linarith) (by linarith)

theorem nhLUJ2_p0_g2 (x : ℝ) (h0 : (1 / 2) ≤ x) (h1 : x ≤ 1) :
    0 < 768 - 800 * x - 80112 * x ^ 2 - 75800 * x ^ 3 + 201868 * x ^ 4 + 385984 * x ^ 5 + 278172 * x ^ 6 + 142224 * x ^ 7 + 67000 * x ^ 8 + 16616 * x ^ 9 + 528 * x ^ 10 := by
  exact nhLUJ2_p0_g2_l0 x h0 h1

private theorem nhLUJ2_p0_g3_bp0 (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    0 ≤ 2621997 * a * b ^ 8 + 27558582 * a ^ 2 * b ^ 7 + 125012104 * a ^ 3 * b ^ 6 + 319802756 * a ^ 4 * b ^ 5 + 504910568 * a ^ 5 * b ^ 4 + 504112672 * a ^ 6 * b ^ 3 + 311038464 * a ^ 7 * b ^ 2 + 108507072 * a ^ 8 * b + 16397952 * a ^ 9 := by positivity

private theorem nhLUJ2_p0_g3_l0 (x : ℝ) (h0 : (1 / 2) ≤ x) (h1 : x ≤ 1) :
    0 < 480 + 144 * x - 81512 * x ^ 2 + 31716 * x ^ 3 + 215316 * x ^ 4 + 116118 * x ^ 5 - 18708 * x ^ 6 - 10956 * x ^ 7 + 4460 * x ^ 8 + 24 * x ^ 9 := by
  linear_combination (1 / 64 : ℝ) * nhLUJ2_p0_g3_bp0 (2 * x - 1) (2 - 2 * x) (by linarith) (by linarith)

theorem nhLUJ2_p0_g3 (x : ℝ) (h0 : (1 / 2) ≤ x) (h1 : x ≤ 1) :
    0 < 480 + 144 * x - 81512 * x ^ 2 + 31716 * x ^ 3 + 215316 * x ^ 4 + 116118 * x ^ 5 - 18708 * x ^ 6 - 10956 * x ^ 7 + 4460 * x ^ 8 + 24 * x ^ 9 := by
  exact nhLUJ2_p0_g3_l0 x h0 h1

private theorem nhLUJ2_p0_g4_bp0 (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    0 ≤ 477468 * a * b ^ 7 + 4233207 * a ^ 2 * b ^ 6 + 15586800 * a ^ 3 * b ^ 5 + 30734280 * a ^ 4 * b ^ 4 + 34765872 * a ^ 5 * b ^ 3 + 22234896 * a ^ 6 * b ^ 2 + 7228224 * a ^ 7 * b + 855936 * a ^ 8 := by positivity

private theorem nhLUJ2_p0_g4_l0 (x : ℝ) (h0 : (1 / 2) ≤ x) (h1 : x ≤ 1) :
    0 < 96 + 168 * x - 24564 * x ^ 2 + 30342 * x ^ 3 + 49695 * x ^ 4 - 7854 * x ^ 5 - 26757 * x ^ 6 - 7356 * x ^ 7 - 180 * x ^ 8 := by
  linear_combination (1 / 64 : ℝ) * nhLUJ2_p0_g4_bp0 (2 * x - 1) (2 - 2 * x) (by linarith) (by linarith)

theorem nhLUJ2_p0_g4 (x : ℝ) (h0 : (1 / 2) ≤ x) (h1 : x ≤ 1) :
    0 < 96 + 168 * x - 24564 * x ^ 2 + 30342 * x ^ 3 + 49695 * x ^ 4 - 7854 * x ^ 5 - 26757 * x ^ 6 - 7356 * x ^ 7 - 180 * x ^ 8 := by
  exact nhLUJ2_p0_g4_l0 x h0 h1

theorem nhLUJ2_p0 (x t : ℝ) (hx0 : (1 / 2) ≤ x) (hx1 : x ≤ 1)
    (hs0 : (1 / 2) - (1 / 2) * x ≤ t) (hs1 : t ≤ (1 / 4)) (hgap : (0 : ℝ) < ((1 / 4)) - ((1 / 2) - (1 / 2) * x)) :
    0 < nhLUJ2 t x := by
  have hpos := nh_bern_pos4 (a := (t - ((1 / 2) - (1 / 2) * x))) (b := (((1 / 4)) - t)) (by linarith) (by linarith) (hgap.trans_eq (by ring))
    (nhLUJ2_p0_g0 x hx0 hx1) (nhLUJ2_p0_g1 x hx0 hx1) (nhLUJ2_p0_g2 x hx0 hx1) (nhLUJ2_p0_g3 x hx0 hx1) (nhLUJ2_p0_g4 x hx0 hx1)
  have e : 64 * (((1 / 4)) - ((1 / 2) - (1 / 2) * x)) ^ 4 * (nhLUJ2 t x) = (-256 * x - 1920 * x ^ 2 - 18240 * x ^ 3 - 38624 * x ^ 4 + 16096 * x ^ 5 + 154064 * x ^ 6 + 230720 * x ^ 7 + 169888 * x ^ 8 + 66560 * x ^ 9 + 11760 * x ^ 10 + 288 * x ^ 11) * (((1 / 4)) - t) ^ 4 + (384 - 960 * x - 27808 * x ^ 2 - 82160 * x ^ 3 - 16144 * x ^ 4 + 251576 * x ^ 5 + 462608 * x ^ 6 + 405272 * x ^ 7 + 207360 * x ^ 8 + 60016 * x ^ 9 + 7632 * x ^ 10 + 288 * x ^ 11) * (t - ((1 / 2) - (1 / 2) * x)) * (((1 / 4)) - t) ^ 3 + (768 - 800 * x - 80112 * x ^ 2 - 75800 * x ^ 3 + 201868 * x ^ 4 + 385984 * x ^ 5 + 278172 * x ^ 6 + 142224 * x ^ 7 + 67000 * x ^ 8 + 16616 * x ^ 9 + 528 * x ^ 10) * (t - ((1 / 2) - (1 / 2) * x)) ^ 2 * (((1 / 4)) - t) ^ 2 + (480 + 144 * x - 81512 * x ^ 2 + 31716 * x ^ 3 + 215316 * x ^ 4 + 116118 * x ^ 5 - 18708 * x ^ 6 - 10956 * x ^ 7 + 4460 * x ^ 8 + 24 * x ^ 9) * (t - ((1 / 2) - (1 / 2) * x)) ^ 3 * (((1 / 4)) - t) + (96 + 168 * x - 24564 * x ^ 2 + 30342 * x ^ 3 + 49695 * x ^ 4 - 7854 * x ^ 5 - 26757 * x ^ 6 - 7356 * x ^ 7 - 180 * x ^ 8) * (t - ((1 / 2) - (1 / 2) * x)) ^ 4 := by unfold nhLUJ2; ring
  have h2 : 0 < 64 * (((1 / 4)) - ((1 / 2) - (1 / 2) * x)) ^ 4 * (nhLUJ2 t x) := lt_of_lt_of_eq hpos e.symm
  exact pos_of_mul_pos_right h2 (by positivity)

private theorem nhLUJ2_p1_g0_bp0 (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    0 ≤ 5497888942368 * a * b ^ 6 + 34372609022448 * a ^ 2 * b ^ 5 + 89564346943920 * a ^ 3 * b ^ 4 + 124499403360072 * a ^ 4 * b ^ 3 + 97370169476130 * a ^ 5 * b ^ 2 + 40623807886263 * a ^ 6 * b + 7063414926048 * a ^ 7 := by positivity

private theorem nhLUJ2_p1_g0_l0 (x : ℝ) (h0 : 1 ≤ x) (h1 : x ≤ (7 / 6)) :
    0 < -2181033864 * x ^ 2 + 45973898028 * x ^ 3 + 62475141078 * x ^ 4 + 24637073319 * x ^ 5 + 1363146165 * x ^ 6 + 86093442 * x ^ 7 := by
  linear_combination (1 / 64 : ℝ) * nhLUJ2_p1_g0_bp0 (6 * x - 6) (7 - 6 * x) (by linarith) (by linarith)

theorem nhLUJ2_p1_g0 (x : ℝ) (h0 : 1 ≤ x) (h1 : x ≤ (7 / 6)) :
    0 < -2181033864 * x ^ 2 + 45973898028 * x ^ 3 + 62475141078 * x ^ 4 + 24637073319 * x ^ 5 + 1363146165 * x ^ 6 + 86093442 * x ^ 7 := by
  exact nhLUJ2_p1_g0_l0 x h0 h1

private theorem nhLUJ2_p1_g1_bp0 (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    0 ≤ 12394432339200 * a * b ^ 7 + 89756002676880 * a ^ 2 * b ^ 6 + 278572887724752 * a ^ 3 * b ^ 5 + 480341151063288 * a ^ 4 * b ^ 4 + 496950264887724 * a ^ 5 * b ^ 3 + 308475766970343 * a ^ 6 * b ^ 2 + 106375893863004 * a ^ 7 * b + 15720558101091 * a ^ 8 := by positivity

private theorem nhLUJ2_p1_g1_l0 (x : ℝ) (h0 : 1 ≤ x) (h1 : x ≤ (7 / 6)) :
    0 < 134631720 * x - 22146917940 * x ^ 2 + 112103227422 * x ^ 3 + 164291619357 * x ^ 4 + 54927615996 * x ^ 5 - 7246552329 * x ^ 6 - 2550208212 * x ^ 7 - 80779032 * x ^ 8 := by
  linear_combination (1 / 64 : ℝ) * nhLUJ2_p1_g1_bp0 (6 * x - 6) (7 - 6 * x) (by linarith) (by linarith)

theorem nhLUJ2_p1_g1 (x : ℝ) (h0 : 1 ≤ x) (h1 : x ≤ (7 / 6)) :
    0 < 134631720 * x - 22146917940 * x ^ 2 + 112103227422 * x ^ 3 + 164291619357 * x ^ 4 + 54927615996 * x ^ 5 - 7246552329 * x ^ 6 - 2550208212 * x ^ 7 - 80779032 * x ^ 8 := by
  exact nhLUJ2_p1_g1_l0 x h0 h1

private theorem nhLUJ2_p1_g2_bp0 (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    0 ≤ 9540601529184 * a * b ^ 7 + 68824149985296 * a ^ 2 * b ^ 6 + 212720838075072 * a ^ 3 * b ^ 5 + 365150995654536 * a ^ 4 * b ^ 4 + 375955449568290 * a ^ 5 * b ^ 3 + 232159032927339 * a ^ 6 * b ^ 2 + 79612196687458 * a ^ 7 * b + 11694907285404 * a ^ 8 := by positivity

private theorem nhLUJ2_p1_g2_l0 (x : ℝ) (h0 : 1 ≤ x) (h1 : x ≤ (7 / 6)) :
    0 < 37896336 + 302838264 * x - 39699237564 * x ^ 2 + 104201823870 * x ^ 3 + 163557248814 * x ^ 4 + 39253717233 * x ^ 5 - 23395627143 * x ^ 6 - 6806075220 * x ^ 7 - 194966676 * x ^ 8 := by
  linear_combination (1 / 64 : ℝ) * nhLUJ2_p1_g2_bp0 (6 * x - 6) (7 - 6 * x) (by linarith) (by linarith)

theorem nhLUJ2_p1_g2 (x : ℝ) (h0 : 1 ≤ x) (h1 : x ≤ (7 / 6)) :
    0 < 37896336 + 302838264 * x - 39699237564 * x ^ 2 + 104201823870 * x ^ 3 + 163557248814 * x ^ 4 + 39253717233 * x ^ 5 - 23395627143 * x ^ 6 - 6806075220 * x ^ 7 - 194966676 * x ^ 8 := by
  exact nhLUJ2_p1_g2_l0 x h0 h1

private theorem nhLUJ2_p1_g3_bp0 (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    0 ≤ 71618539585536 * a * b ^ 7 + 510398815553424 * a ^ 2 * b ^ 6 + 1556722000547280 * a ^ 3 * b ^ 5 + 2633727469951440 * a ^ 4 * b ^ 4 + 2668962527314692 * a ^ 5 * b ^ 3 + 1619747441641983 * a ^ 6 * b ^ 2 + 544970251337914 * a ^ 7 * b + 78399591479868 * a ^ 8 := by positivity

private theorem nhLUJ2_p1_g3_l0 (x : ℝ) (h0 : 1 ≤ x) (h1 : x ≤ (7 / 6)) :
    0 < 58014144 + 222522984 * x - 25822772244 * x ^ 2 + 44752787118 * x ^ 3 + 73423455345 * x ^ 4 + 7576755660 * x ^ 5 - 20674613583 * x ^ 6 - 5779381104 * x ^ 7 - 154263204 * x ^ 8 := by
  linear_combination (1 / 1728 : ℝ) * nhLUJ2_p1_g3_bp0 (6 * x - 6) (7 - 6 * x) (by linarith) (by linarith)

theorem nhLUJ2_p1_g3 (x : ℝ) (h0 : 1 ≤ x) (h1 : x ≤ (7 / 6)) :
    0 < 58014144 + 222522984 * x - 25822772244 * x ^ 2 + 44752787118 * x ^ 3 + 73423455345 * x ^ 4 + 7576755660 * x ^ 5 - 20674613583 * x ^ 6 - 5779381104 * x ^ 7 - 154263204 * x ^ 8 := by
  exact nhLUJ2_p1_g3_l0 x h0 h1

private theorem nhLUJ2_p1_g4_bp0 (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    0 ≤ 6125480125481 * b ^ 8 + 127857257925064 * a * b ^ 7 + 671556036416348 * a ^ 2 * b ^ 6 + 1659779178451096 * a ^ 3 * b ^ 5 + 2266760906511710 * a ^ 4 * b ^ 4 + 1767962777055220 * a ^ 5 * b ^ 3 + 741244875785184 * a ^ 6 * b ^ 2 + 130088086520553 * a ^ 7 * b := by positivity

private theorem nhLUJ2_p1_g4_l0 (x : ℝ) (h0 : 1 ≤ x) (h1 : x ≤ (7 / 6)) :
    0 < 20117808 + 41805624 * x - 5716179412 * x ^ 2 + 7663434266 * x ^ 3 + 12581899710 * x ^ 4 - 1034030912 * x ^ 5 - 5838120386 * x ^ 6 - 1609607538 * x ^ 7 - 40075560 * x ^ 8 := by
  linear_combination (1 / 46656 : ℝ) * nhLUJ2_p1_g4_bp0 (6 * x - 6) (7 - 6 * x) (by linarith) (by linarith)

theorem nhLUJ2_p1_g4 (x : ℝ) (h0 : 1 ≤ x) (h1 : x ≤ (7 / 6)) :
    0 < 20117808 + 41805624 * x - 5716179412 * x ^ 2 + 7663434266 * x ^ 3 + 12581899710 * x ^ 4 - 1034030912 * x ^ 5 - 5838120386 * x ^ 6 - 1609607538 * x ^ 7 - 40075560 * x ^ 8 := by
  exact nhLUJ2_p1_g4_l0 x h0 h1

theorem nhLUJ2_p1 (x t : ℝ) (hx0 : 1 ≤ x) (hx1 : x ≤ (7 / 6))
    (hs0 : 0 ≤ t) (hs1 : t ≤ (19 / 81)) (hgap : (0 : ℝ) < ((19 / 81)) - (0)) :
    0 < nhLUJ2 t x := by
  have hpos := nh_bern_pos4 (a := (t - (0))) (b := (((19 / 81)) - t)) (by linarith) (by linarith) (hgap.trans_eq (by ring))
    (nhLUJ2_p1_g0 x hx0 hx1) (nhLUJ2_p1_g1 x hx0 hx1) (nhLUJ2_p1_g2 x hx0 hx1) (nhLUJ2_p1_g3 x hx0 hx1) (nhLUJ2_p1_g4 x hx0 hx1)
  have e : 14348907 * (((19 / 81)) - (0)) ^ 4 * (nhLUJ2 t x) = (-2181033864 * x ^ 2 + 45973898028 * x ^ 3 + 62475141078 * x ^ 4 + 24637073319 * x ^ 5 + 1363146165 * x ^ 6 + 86093442 * x ^ 7) * (((19 / 81)) - t) ^ 4 + (134631720 * x - 22146917940 * x ^ 2 + 112103227422 * x ^ 3 + 164291619357 * x ^ 4 + 54927615996 * x ^ 5 - 7246552329 * x ^ 6 - 2550208212 * x ^ 7 - 80779032 * x ^ 8) * (t - (0)) * (((19 / 81)) - t) ^ 3 + (37896336 + 302838264 * x - 39699237564 * x ^ 2 + 104201823870 * x ^ 3 + 163557248814 * x ^ 4 + 39253717233 * x ^ 5 - 23395627143 * x ^ 6 - 6806075220 * x ^ 7 - 194966676 * x ^ 8) * (t - (0)) ^ 2 * (((19 / 81)) - t) ^ 2 + (58014144 + 222522984 * x - 25822772244 * x ^ 2 + 44752787118 * x ^ 3 + 73423455345 * x ^ 4 + 7576755660 * x ^ 5 - 20674613583 * x ^ 6 - 5779381104 * x ^ 7 - 154263204 * x ^ 8) * (t - (0)) ^ 3 * (((19 / 81)) - t) + (20117808 + 41805624 * x - 5716179412 * x ^ 2 + 7663434266 * x ^ 3 + 12581899710 * x ^ 4 - 1034030912 * x ^ 5 - 5838120386 * x ^ 6 - 1609607538 * x ^ 7 - 40075560 * x ^ 8) * (t - (0)) ^ 4 := by unfold nhLUJ2; ring
  have h2 : 0 < 14348907 * (((19 / 81)) - (0)) ^ 4 * (nhLUJ2 t x) := lt_of_lt_of_eq hpos e.symm
  exact pos_of_mul_pos_right h2 (by positivity)

private theorem nhLUJ2_p2_g0_bp0 (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    0 ≤ 991802641045218418126291 * a * b ^ 6 + 6171105575111820548098266 * a ^ 2 * b ^ 5 + 16002535065496976791125336 * a ^ 3 * b ^ 4 + 22136463426127939022010688 * a ^ 4 * b ^ 3 + 17228229931039760541021024 * a ^ 5 * b ^ 2 + 7152498135113167294304928 * a ^ 6 * b + 1237499500984286033207392 * a ^ 7 := by positivity

private theorem nhLUJ2_p2_g0_l0 (x : ℝ) (h0 : (7 / 6) ≤ x) (h1 : x ≤ (4 / 3)) :
    0 < -9083444427847524744 * x ^ 2 + 191469447018575455788 * x ^ 3 + 260192875255579754838 * x ^ 4 + 102607066332988157799 * x ^ 5 + 5677152767404702965 * x ^ 6 + 358557016888718082 * x ^ 7 := by
  linear_combination (1 / 1728 : ℝ) * nhLUJ2_p2_g0_bp0 (6 * x - 7) (8 - 6 * x) (by linarith) (by linarith)

theorem nhLUJ2_p2_g0 (x : ℝ) (h0 : (7 / 6) ≤ x) (h1 : x ≤ (4 / 3)) :
    0 < -9083444427847524744 * x ^ 2 + 191469447018575455788 * x ^ 3 + 260192875255579754838 * x ^ 4 + 102607066332988157799 * x ^ 5 + 5677152767404702965 * x ^ 6 + 358557016888718082 * x ^ 7 := by
  exact nhLUJ2_p2_g0_l0 x h0 h1

private theorem nhLUJ2_p2_g1_bp0 (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    0 ≤ 5484170216752978583376835 * a * b ^ 7 + 39545279545576898439246524 * a ^ 2 * b ^ 6 + 122213619573310741476701370 * a ^ 3 * b ^ 5 + 209838553864471369052237626 * a ^ 4 * b ^ 4 + 216177561716771072958510440 * a ^ 5 * b ^ 3 + 133625930222100174791175564 * a ^ 6 * b ^ 2 + 45887778480660949997007016 * a ^ 7 * b + 6753366354680627949324533 * a ^ 8 := by positivity

private theorem nhLUJ2_p2_g1_l0 (x : ℝ) (h0 : (7 / 6) ≤ x) (h1 : x ≤ (4 / 3)) :
    0 < 480004404200218080 * x - 84190216810151841552 * x ^ 2 + 509915439534535531992 * x ^ 3 + 735548700501505347732 * x ^ 4 + 254906838371081973276 * x ^ 5 - 22567804356566758536 * x ^ 6 - 8885866622749816392 * x ^ 7 - 288002642520130848 * x ^ 8 := by
  linear_combination (1 / 3888 : ℝ) * nhLUJ2_p2_g1_bp0 (6 * x - 7) (8 - 6 * x) (by linarith) (by linarith)

theorem nhLUJ2_p2_g1 (x : ℝ) (h0 : (7 / 6) ≤ x) (h1 : x ≤ (4 / 3)) :
    0 < 480004404200218080 * x - 84190216810151841552 * x ^ 2 + 509915439534535531992 * x ^ 3 + 735548700501505347732 * x ^ 4 + 254906838371081973276 * x ^ 5 - 22567804356566758536 * x ^ 6 - 8885866622749816392 * x ^ 7 - 288002642520130848 * x ^ 8 := by
  exact nhLUJ2_p2_g1_l0 x h0 h1

private theorem nhLUJ2_p2_g2_bp0 (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    0 ≤ 28060057021993922327255539 * a * b ^ 7 + 201639202235339321149506107 * a ^ 2 * b ^ 6 + 620881281050730448199209650 * a ^ 3 * b ^ 5 + 1061900858704699789009288012 * a ^ 4 * b ^ 4 + 1089469299546534819953167472 * a ^ 5 * b ^ 3 + 670488565539744357318743352 * a ^ 6 * b ^ 2 + 229181073649005080733914128 * a ^ 7 * b + 33563084778488779315420226 * a ^ 8 := by positivity

private theorem nhLUJ2_p2_g2_l0 (x : ℝ) (h0 : (7 / 6) ≤ x) (h1 : x ≤ (4 / 3)) :
    0 < 115665735422382336 + 1131571251474301344 * x - 156391763866171941120 * x ^ 2 + 514417533980868275520 * x ^ 3 + 784463640783851190504 * x ^ 4 + 217120895680354681818 * x ^ 5 - 81857364964550933814 * x ^ 6 - 24654614305661192100 * x ^ 7 - 719425758282414624 * x ^ 8 := by
  linear_combination (1 / 23328 : ℝ) * nhLUJ2_p2_g2_bp0 (6 * x - 7) (8 - 6 * x) (by linarith) (by linarith)

theorem nhLUJ2_p2_g2 (x : ℝ) (h0 : (7 / 6) ≤ x) (h1 : x ≤ (4 / 3)) :
    0 < 115665735422382336 + 1131571251474301344 * x - 156391763866171941120 * x ^ 2 + 514417533980868275520 * x ^ 3 + 784463640783851190504 * x ^ 4 + 217120895680354681818 * x ^ 5 - 81857364964550933814 * x ^ 6 - 24654614305661192100 * x ^ 7 - 719425758282414624 * x ^ 8 := by
  exact nhLUJ2_p2_g2_l0 x h0 h1

private theorem nhLUJ2_p2_g3_bp0 (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    0 ≤ 1515416309663204858578643 * a * b ^ 7 + 10793205655849557403844170 * a ^ 2 * b ^ 6 + 32917757689105120203315770 * a ^ 3 * b ^ 5 + 55724083253799107900941454 * a ^ 4 * b ^ 4 + 56542730222850453394642104 * a ^ 5 * b ^ 3 + 34386902750152402175564036 * a ^ 6 * b ^ 2 + 11604478791530913479597368 * a ^ 7 * b + 1676191351977644288582727 * a ^ 8 := by positivity

private theorem nhLUJ2_p2_g3_l0 (x : ℝ) (h0 : (7 / 6) ≤ x) (h1 : x ≤ (4 / 3)) :
    0 < 184878555573803520 + 877324358164069792 * x - 107366313195139824880 * x ^ 2 + 235606359443048040104 * x ^ 3 + 375051250867797232748 * x ^ 4 + 67679197564405315708 * x ^ 5 - 76113107163675929856 * x ^ 6 - 21641283527365583208 * x ^ 7 - 592263432231047136 * x ^ 8 := by
  linear_combination (1 / 3888 : ℝ) * nhLUJ2_p2_g3_bp0 (6 * x - 7) (8 - 6 * x) (by linarith) (by linarith)

theorem nhLUJ2_p2_g3 (x : ℝ) (h0 : (7 / 6) ≤ x) (h1 : x ≤ (4 / 3)) :
    0 < 184878555573803520 + 877324358164069792 * x - 107366313195139824880 * x ^ 2 + 235606359443048040104 * x ^ 3 + 375051250867797232748 * x ^ 4 + 67679197564405315708 * x ^ 5 - 76113107163675929856 * x ^ 6 - 21641283527365583208 * x ^ 7 - 592263432231047136 * x ^ 8 := by
  exact nhLUJ2_p2_g3_l0 x h0 h1

private theorem nhLUJ2_p2_g4_bp0 (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    0 ≤ 1348534843132276337901025 * a * b ^ 7 + 9203509549277226981611411 * a ^ 2 * b ^ 6 + 26745024650944506951018182 * a ^ 3 * b ^ 5 + 42844738457118558887300288 * a ^ 4 * b ^ 4 + 40798105943984633490443200 * a ^ 5 * b ^ 3 + 23042642660648853360300624 * a ^ 6 * b ^ 2 + 7126110168121409836957024 * a ^ 7 * b + 926884934670400818530348 * a ^ 8 := by positivity

private theorem nhLUJ2_p2_g4_l0 (x : ℝ) (h0 : (7 / 6) ≤ x) (h1 : x ≤ (4 / 3)) :
    0 < 69212820151421184 + 197773337409944032 * x - 25246460535784266104 * x ^ 2 + 41833907610779846932 * x ^ 3 + 67954797798749689538 * x ^ 4 + 3646294808498979671 * x ^ 5 - 22387596621947952455 * x ^ 6 - 6231092861342925582 * x ^ 7 - 160840316468763360 * x ^ 8 := by
  linear_combination (1 / 46656 : ℝ) * nhLUJ2_p2_g4_bp0 (6 * x - 7) (8 - 6 * x) (by linarith) (by linarith)

theorem nhLUJ2_p2_g4 (x : ℝ) (h0 : (7 / 6) ≤ x) (h1 : x ≤ (4 / 3)) :
    0 < 69212820151421184 + 197773337409944032 * x - 25246460535784266104 * x ^ 2 + 41833907610779846932 * x ^ 3 + 67954797798749689538 * x ^ 4 + 3646294808498979671 * x ^ 5 - 22387596621947952455 * x ^ 6 - 6231092861342925582 * x ^ 7 - 160840316468763360 * x ^ 8 := by
  exact nhLUJ2_p2_g4_l0 x h0 h1

theorem nhLUJ2_p2 (x t : ℝ) (hx0 : (7 / 6) ≤ x) (hx1 : x ≤ (4 / 3))
    (hs0 : 0 ≤ t) (hs1 : t ≤ (4132 / 20577)) (hgap : (0 : ℝ) < ((4132 / 20577)) - (0)) :
    0 < nhLUJ2 t x := by
  have hpos := nh_bern_pos4 (a := (t - (0))) (b := (((4132 / 20577)) - t)) (by linarith) (by linarith) (hgap.trans_eq (by ring))
    (nhLUJ2_p2_g0 x hx0 hx1) (nhLUJ2_p2_g1 x hx0 hx1) (nhLUJ2_p2_g2 x hx0 hx1) (nhLUJ2_p2_g3 x hx0 hx1) (nhLUJ2_p2_g4 x hx0 hx1)
  have e : 59759502814786347 * (((4132 / 20577)) - (0)) ^ 4 * (nhLUJ2 t x) = (-9083444427847524744 * x ^ 2 + 191469447018575455788 * x ^ 3 + 260192875255579754838 * x ^ 4 + 102607066332988157799 * x ^ 5 + 5677152767404702965 * x ^ 6 + 358557016888718082 * x ^ 7) * (((4132 / 20577)) - t) ^ 4 + (480004404200218080 * x - 84190216810151841552 * x ^ 2 + 509915439534535531992 * x ^ 3 + 735548700501505347732 * x ^ 4 + 254906838371081973276 * x ^ 5 - 22567804356566758536 * x ^ 6 - 8885866622749816392 * x ^ 7 - 288002642520130848 * x ^ 8) * (t - (0)) * (((4132 / 20577)) - t) ^ 3 + (115665735422382336 + 1131571251474301344 * x - 156391763866171941120 * x ^ 2 + 514417533980868275520 * x ^ 3 + 784463640783851190504 * x ^ 4 + 217120895680354681818 * x ^ 5 - 81857364964550933814 * x ^ 6 - 24654614305661192100 * x ^ 7 - 719425758282414624 * x ^ 8) * (t - (0)) ^ 2 * (((4132 / 20577)) - t) ^ 2 + (184878555573803520 + 877324358164069792 * x - 107366313195139824880 * x ^ 2 + 235606359443048040104 * x ^ 3 + 375051250867797232748 * x ^ 4 + 67679197564405315708 * x ^ 5 - 76113107163675929856 * x ^ 6 - 21641283527365583208 * x ^ 7 - 592263432231047136 * x ^ 8) * (t - (0)) ^ 3 * (((4132 / 20577)) - t) + (69212820151421184 + 197773337409944032 * x - 25246460535784266104 * x ^ 2 + 41833907610779846932 * x ^ 3 + 67954797798749689538 * x ^ 4 + 3646294808498979671 * x ^ 5 - 22387596621947952455 * x ^ 6 - 6231092861342925582 * x ^ 7 - 160840316468763360 * x ^ 8) * (t - (0)) ^ 4 := by unfold nhLUJ2; ring
  have h2 : 0 < 59759502814786347 * (((4132 / 20577)) - (0)) ^ 4 * (nhLUJ2 t x) := lt_of_lt_of_eq hpos e.symm
  exact pos_of_mul_pos_right h2 (by positivity)

private theorem nhLUJ2_p3_g0_bp0 (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    0 ≤ 20820125000000000 * a * b ^ 6 + 133213804687500000 * a ^ 2 * b ^ 5 + 355405003906250000 * a ^ 3 * b ^ 4 + 506049982421875000 * a ^ 4 * b ^ 3 + 405564008789062500 * a ^ 5 * b ^ 2 + 173449959960937500 * a ^ 6 * b + 30924611328125000 * a ^ 7 := by positivity

private theorem nhLUJ2_p3_g0_l0 (x : ℝ) (h0 : (4 / 3) ≤ x) (h1 : x ≤ (5 / 3)) :
    0 < -4007812500000 * x ^ 2 + 84480468750000 * x ^ 3 + 114802734375000 * x ^ 4 + 45272460937500 * x ^ 5 + 2504882812500 * x ^ 6 + 158203125000 * x ^ 7 := by
  linear_combination (1 / 27 : ℝ) * nhLUJ2_p3_g0_bp0 (3 * x - 4) (5 - 3 * x) (by linarith) (by linarith)

theorem nhLUJ2_p3_g0 (x : ℝ) (h0 : (4 / 3) ≤ x) (h1 : x ≤ (5 / 3)) :
    0 < -4007812500000 * x ^ 2 + 84480468750000 * x ^ 3 + 114802734375000 * x ^ 4 + 45272460937500 * x ^ 5 + 2504882812500 * x ^ 6 + 158203125000 * x ^ 7 := by
  exact nhLUJ2_p3_g0_l0 x h0 h1

private theorem nhLUJ2_p3_g1_bp0 (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    0 ≤ 496015184343750000 * a * b ^ 7 + 3658958336359375000 * a ^ 2 * b ^ 6 + 11569589640320312500 * a ^ 3 * b ^ 5 + 20326190659589843750 * a ^ 4 * b ^ 4 + 21427436174937500000 * a ^ 5 * b ^ 3 + 13552990765675781250 * a ^ 6 * b ^ 2 + 4762130687718750000 * a ^ 7 * b + 717031921726562500 * a ^ 8 := by positivity

private theorem nhLUJ2_p3_g1_l0 (x : ℝ) (h0 : (4 / 3) ≤ x) (h1 : x ≤ (5 / 3)) :
    0 < 178593750000 * x - 33837046875000 * x ^ 2 + 242686757812500 * x ^ 3 + 345647636718750 * x ^ 4 + 123225468750000 * x ^ 5 - 6826324218750 * x ^ 6 - 3206953125000 * x ^ 7 - 107156250000 * x ^ 8 := by
  linear_combination (1 / 243 : ℝ) * nhLUJ2_p3_g1_bp0 (3 * x - 4) (5 - 3 * x) (by linarith) (by linarith)

theorem nhLUJ2_p3_g1 (x : ℝ) (h0 : (4 / 3) ≤ x) (h1 : x ≤ (5 / 3)) :
    0 < 178593750000 * x - 33837046875000 * x ^ 2 + 242686757812500 * x ^ 3 + 345647636718750 * x ^ 4 + 123225468750000 * x ^ 5 - 6826324218750 * x ^ 6 - 3206953125000 * x ^ 7 - 107156250000 * x ^ 8 := by
  exact nhLUJ2_p3_g1_l0 x h0 h1

private theorem nhLUJ2_p3_g2_bp0 (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    0 ≤ 1387942380276750000 * a * b ^ 7 + 10180989123032375000 * a ^ 2 * b ^ 6 + 31993072995810125000 * a ^ 3 * b ^ 5 + 55824708728183265625 * a ^ 4 * b ^ 4 + 58408412175864765625 * a ^ 5 * b ^ 3 + 36639537762407578125 * a ^ 6 * b ^ 2 + 12757642936565859375 * a ^ 7 * b + 1901834844215843750 * a ^ 8 := by positivity

private theorem nhLUJ2_p3_g2_l0 (x : ℝ) (h0 : (4 / 3) ≤ x) (h1 : x ≤ (5 / 3)) :
    0 < 36290250000 + 439007250000 * x - 64387678875000 * x ^ 2 + 263059433625000 * x ^ 3 + 391729995328125 * x ^ 4 + 119390136234375 * x ^ 5 - 29261810250000 * x ^ 6 - 9266653312500 * x ^ 7 - 276105937500 * x ^ 8 := by
  linear_combination (1 / 729 : ℝ) * nhLUJ2_p3_g2_bp0 (3 * x - 4) (5 - 3 * x) (by linarith) (by linarith)

theorem nhLUJ2_p3_g2 (x : ℝ) (h0 : (4 / 3) ≤ x) (h1 : x ≤ (5 / 3)) :
    0 < 36290250000 + 439007250000 * x - 64387678875000 * x ^ 2 + 263059433625000 * x ^ 3 + 391729995328125 * x ^ 4 + 119390136234375 * x ^ 5 - 29261810250000 * x ^ 6 - 9266653312500 * x ^ 7 - 276105937500 * x ^ 8 := by
  exact nhLUJ2_p3_g2_l0 x h0 h1

private theorem nhLUJ2_p3_g3_bp0 (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    0 ≤ 171053312158939000 * a * b ^ 7 + 1239261764469779500 * a ^ 2 * b ^ 6 + 3840506869597256750 * a ^ 3 * b ^ 5 + 6597461390587263000 * a ^ 4 * b ^ 4 + 6782618493995281125 * a ^ 5 * b ^ 3 + 4171309320294782125 * a ^ 6 * b ^ 2 + 1420270563316491875 * a ^ 7 * b + 206416754999403875 * a ^ 8 := by positivity

private theorem nhLUJ2_p3_g3_l0 (x : ℝ) (h0 : (4 / 3) ≤ x) (h1 : x ≤ (5 / 3)) :
    0 < 60290202000 + 356571931000 * x - 46158082367500 * x ^ 2 + 128212488380750 * x ^ 3 + 198319528784750 * x ^ 4 + 46947278961625 * x ^ 5 - 28768679622750 * x ^ 6 - 8391783719250 * x ^ 7 - 235351986750 * x ^ 8 := by
  linear_combination (1 / 243 : ℝ) * nhLUJ2_p3_g3_bp0 (3 * x - 4) (5 - 3 * x) (by linarith) (by linarith)

theorem nhLUJ2_p3_g3 (x : ℝ) (h0 : (4 / 3) ≤ x) (h1 : x ≤ (5 / 3)) :
    0 < 60290202000 + 356571931000 * x - 46158082367500 * x ^ 2 + 128212488380750 * x ^ 3 + 198319528784750 * x ^ 4 + 46947278961625 * x ^ 5 - 28768679622750 * x ^ 6 - 8391783719250 * x ^ 7 - 235351986750 * x ^ 8 := by
  exact nhLUJ2_p3_g3_l0 x h0 h1

private theorem nhLUJ2_p3_g4_bp0 (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    0 ≤ 53739026563689600 * a * b ^ 7 + 374086441773976960 * a ^ 2 * b ^ 6 + 1105686324525810552 * a ^ 3 * b ^ 5 + 1794576324352715700 * a ^ 4 * b ^ 4 + 1721805152734415926 * a ^ 5 * b ^ 3 + 972008327696153475 * a ^ 6 * b ^ 2 + 296819270476287522 * a ^ 7 * b + 37378673099324215 * a ^ 8 := by positivity

private theorem nhLUJ2_p3_g4_l0 (x : ℝ) (h0 : (4 / 3) ≤ x) (h1 : x ≤ (5 / 3)) :
    0 < 23999952000 + 89914959616 * x - 11413374304544 * x ^ 2 + 23849976611176 * x ^ 3 + 37883185306100 * x ^ 4 + 5686008317066 * x ^ 5 - 8812842373823 * x ^ 6 - 2490286656750 * x ^ 7 - 66402299250 * x ^ 8 := by
  linear_combination (1 / 729 : ℝ) * nhLUJ2_p3_g4_bp0 (3 * x - 4) (5 - 3 * x) (by linarith) (by linarith)

theorem nhLUJ2_p3_g4 (x : ℝ) (h0 : (4 / 3) ≤ x) (h1 : x ≤ (5 / 3)) :
    0 < 23999952000 + 89914959616 * x - 11413374304544 * x ^ 2 + 23849976611176 * x ^ 3 + 37883185306100 * x ^ 4 + 5686008317066 * x ^ 5 - 8812842373823 * x ^ 6 - 2490286656750 * x ^ 7 - 66402299250 * x ^ 8 := by
  exact nhLUJ2_p3_g4_l0 x h0 h1

theorem nhLUJ2_p3 (x t : ℝ) (hx0 : (4 / 3) ≤ x) (hx1 : x ≤ (5 / 3))
    (hs0 : 0 ≤ t) (hs1 : t ≤ (127 / 750)) (hgap : (0 : ℝ) < ((127 / 750)) - (0)) :
    0 < nhLUJ2 t x := by
  have hpos := nh_bern_pos4 (a := (t - (0))) (b := (((127 / 750)) - t)) (by linarith) (by linarith) (hgap.trans_eq (by ring))
    (nhLUJ2_p3_g0 x hx0 hx1) (nhLUJ2_p3_g1 x hx0 hx1) (nhLUJ2_p3_g2 x hx0 hx1) (nhLUJ2_p3_g3 x hx0 hx1) (nhLUJ2_p3_g4 x hx0 hx1)
  have e : 26367187500 * (((127 / 750)) - (0)) ^ 4 * (nhLUJ2 t x) = (-4007812500000 * x ^ 2 + 84480468750000 * x ^ 3 + 114802734375000 * x ^ 4 + 45272460937500 * x ^ 5 + 2504882812500 * x ^ 6 + 158203125000 * x ^ 7) * (((127 / 750)) - t) ^ 4 + (178593750000 * x - 33837046875000 * x ^ 2 + 242686757812500 * x ^ 3 + 345647636718750 * x ^ 4 + 123225468750000 * x ^ 5 - 6826324218750 * x ^ 6 - 3206953125000 * x ^ 7 - 107156250000 * x ^ 8) * (t - (0)) * (((127 / 750)) - t) ^ 3 + (36290250000 + 439007250000 * x - 64387678875000 * x ^ 2 + 263059433625000 * x ^ 3 + 391729995328125 * x ^ 4 + 119390136234375 * x ^ 5 - 29261810250000 * x ^ 6 - 9266653312500 * x ^ 7 - 276105937500 * x ^ 8) * (t - (0)) ^ 2 * (((127 / 750)) - t) ^ 2 + (60290202000 + 356571931000 * x - 46158082367500 * x ^ 2 + 128212488380750 * x ^ 3 + 198319528784750 * x ^ 4 + 46947278961625 * x ^ 5 - 28768679622750 * x ^ 6 - 8391783719250 * x ^ 7 - 235351986750 * x ^ 8) * (t - (0)) ^ 3 * (((127 / 750)) - t) + (23999952000 + 89914959616 * x - 11413374304544 * x ^ 2 + 23849976611176 * x ^ 3 + 37883185306100 * x ^ 4 + 5686008317066 * x ^ 5 - 8812842373823 * x ^ 6 - 2490286656750 * x ^ 7 - 66402299250 * x ^ 8) * (t - (0)) ^ 4 := by unfold nhLUJ2; ring
  have h2 : 0 < 26367187500 * (((127 / 750)) - (0)) ^ 4 * (nhLUJ2 t x) := lt_of_lt_of_eq hpos e.symm
  exact pos_of_mul_pos_right h2 (by positivity)

private theorem nhLUJ2_p4_g0_bp0 (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    0 ≤ 276526014128658060910 * a * b ^ 6 + 1842739494626464331832 * a ^ 2 * b ^ 5 + 5127050000182390036614 * a ^ 3 * b ^ 4 + 7621987758282868930432 * a ^ 4 * b ^ 3 + 6384076997376645432954 * a ^ 5 * b ^ 2 + 2855882474077529101128 * a ^ 6 * b + 532957518736833273490 * a ^ 7 := by positivity

private theorem nhLUJ2_p4_g0_l0 (x : ℝ) (h0 : (5 / 3) ≤ x) (h1 : x ≤ (7 / 3)) :
    0 < -12880110058062984 * x ^ 2 + 271499162013380268 * x ^ 3 + 368947363110567318 * x ^ 4 + 145494401116408839 * x ^ 5 + 8050068786289365 * x ^ 6 + 508425397028802 * x ^ 7 := by
  linear_combination (1 / 3456 : ℝ) * nhLUJ2_p4_g0_bp0 (3 * x - 5) (7 - 3 * x) (by linarith) (by linarith)

theorem nhLUJ2_p4_g0 (x : ℝ) (h0 : (5 / 3) ≤ x) (h1 : x ≤ (7 / 3)) :
    0 < -12880110058062984 * x ^ 2 + 271499162013380268 * x ^ 3 + 368947363110567318 * x ^ 4 + 145494401116408839 * x ^ 5 + 8050068786289365 * x ^ 6 + 508425397028802 * x ^ 7 := by
  exact nhLUJ2_p4_g0_l0 x h0 h1

private theorem nhLUJ2_p4_g1_bp0 (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    0 ≤ 7502081195196875334520 * a * b ^ 7 + 57252815893585587957308 * a ^ 2 * b ^ 6 + 187389118949100955869312 * a ^ 3 * b ^ 5 + 340907451165861333861316 * a ^ 4 * b ^ 4 + 372222165302821521041816 * a ^ 5 * b ^ 3 + 243862452291898780376388 * a ^ 6 * b ^ 2 + 88744814603320631349616 * a ^ 7 * b + 13835458530838766245820 * a ^ 8 := by positivity

private theorem nhLUJ2_p4_g1_l0 (x : ℝ) (h0 : (5 / 3) ≤ x) (h1 : x ≤ (7 / 3)) :
    0 < 381138664773240 * x - 89519965110143964 * x ^ 2 + 882754455063190842 * x ^ 3 + 1233432903979585287 * x ^ 4 + 458488677079105596 * x ^ 5 - 3750629409578403 * x ^ 6 - 6160779704509452 * x ^ 7 - 228683198863944 * x ^ 8 := by
  linear_combination (1 / 62208 : ℝ) * nhLUJ2_p4_g1_bp0 (3 * x - 5) (7 - 3 * x) (by linarith) (by linarith)

theorem nhLUJ2_p4_g1 (x : ℝ) (h0 : (5 / 3) ≤ x) (h1 : x ≤ (7 / 3)) :
    0 < 381138664773240 * x - 89519965110143964 * x ^ 2 + 882754455063190842 * x ^ 3 + 1233432903979585287 * x ^ 4 + 458488677079105596 * x ^ 5 - 3750629409578403 * x ^ 6 - 6160779704509452 * x ^ 7 - 228683198863944 * x ^ 8 := by
  exact nhLUJ2_p4_g1_l0 x h0 h1

private theorem nhLUJ2_p4_g2_bp0 (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    0 ≤ 24590844265003369706606 * a * b ^ 7 + 186435371732530936551382 * a ^ 2 * b ^ 6 + 605604662225917216181022 * a ^ 3 * b ^ 5 + 1092222667097485101815318 * a ^ 4 * b ^ 4 + 1180748688857901817508602 * a ^ 5 * b ^ 3 + 764812801355805845817042 * a ^ 6 * b ^ 2 + 274722020300396281228154 * a ^ 7 * b + 42195357777697326155074 * a ^ 8 := by positivity

private theorem nhLUJ2_p4_g2_l0 (x : ℝ) (h0 : (5 / 3) ≤ x) (h1 : x ≤ (7 / 3)) :
    0 < 51429379559184 + 1006270982161896 * x - 172747515214228020 * x ^ 2 + 1078622182902219186 * x ^ 3 + 1548408004261119012 * x ^ 4 + 532754028509961225 * x ^ 5 - 50700018989846853 * x ^ 6 - 19685719613200476 * x ^ 7 - 621762872142852 * x ^ 8 := by
  linear_combination (1 / 186624 : ℝ) * nhLUJ2_p4_g2_bp0 (3 * x - 5) (7 - 3 * x) (by linarith) (by linarith)

theorem nhLUJ2_p4_g2 (x : ℝ) (h0 : (5 / 3) ≤ x) (h1 : x ≤ (7 / 3)) :
    0 < 51429379559184 + 1006270982161896 * x - 172747515214228020 * x ^ 2 + 1078622182902219186 * x ^ 3 + 1548408004261119012 * x ^ 4 + 532754028509961225 * x ^ 5 - 50700018989846853 * x ^ 6 - 19685719613200476 * x ^ 7 - 621762872142852 * x ^ 8 := by
  exact nhLUJ2_p4_g2_l0 x h0 h1

private theorem nhLUJ2_p4_g3_bp0 (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    0 ≤ 3779744173297397243840 * a * b ^ 7 + 28341273901736302861948 * a ^ 2 * b ^ 6 + 90879817307077658953016 * a ^ 3 * b ^ 5 + 161440811177887952579924 * a ^ 4 * b ^ 4 + 171449288508683344738128 * a ^ 5 * b ^ 3 + 108749788132011616336868 * a ^ 6 * b ^ 2 + 38104926908301128134072 * a ^ 7 * b + 5681898358899845852748 * a ^ 8 := by positivity

private theorem nhLUJ2_p4_g3_l0 (x : ℝ) (h0 : (5 / 3) ≤ x) (h1 : x ≤ (7 / 3)) :
    0 < 91292622668544 + 882619795862200 * x - 131149521278380924 * x ^ 2 + 587667368509746074 * x ^ 3 + 865334778358267943 * x ^ 4 + 268964483497255216 * x ^ 5 - 58647625861015389 * x ^ 6 - 18960939519862032 * x ^ 7 - 561813448862556 * x ^ 8 := by
  linear_combination (1 / 62208 : ℝ) * nhLUJ2_p4_g3_bp0 (3 * x - 5) (7 - 3 * x) (by linarith) (by linarith)

theorem nhLUJ2_p4_g3 (x : ℝ) (h0 : (5 / 3) ≤ x) (h1 : x ≤ (7 / 3)) :
    0 < 91292622668544 + 882619795862200 * x - 131149521278380924 * x ^ 2 + 587667368509746074 * x ^ 3 + 865334778358267943 * x ^ 4 + 268964483497255216 * x ^ 5 - 58647625861015389 * x ^ 6 - 18960939519862032 * x ^ 7 - 561813448862556 * x ^ 8 := by
  exact nhLUJ2_p4_g3_l0 x h0 h1

private theorem nhLUJ2_p4_g4_bp0 (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    0 ≤ 1795033787058013836928 * a * b ^ 7 + 13177247827025651843936 * a ^ 2 * b ^ 6 + 41183697590738766876224 * a ^ 3 * b ^ 5 + 70901072205093723868160 * a ^ 4 * b ^ 4 + 72434389500492293169472 * a ^ 5 * b ^ 3 + 43764161995612906511520 * a ^ 6 * b ^ 2 + 14408857189607349144064 * a ^ 7 * b + 1979491240625635312640 * a ^ 8 := by positivity

private theorem nhLUJ2_p4_g4_l0 (x : ℝ) (h0 : (5 / 3) ≤ x) (h1 : x ≤ (7 / 3)) :
    0 < 39863243109360 + 253585754006248 * x - 34925459669626220 * x ^ 2 + 120607089171725806 * x ^ 3 + 181692751412253800 * x ^ 4 + 49314629522486252 * x ^ 5 - 19732535597314316 * x ^ 6 - 5944425008199810 * x ^ 7 - 168733775583648 * x ^ 8 := by
  linear_combination (1 / 186624 : ℝ) * nhLUJ2_p4_g4_bp0 (3 * x - 5) (7 - 3 * x) (by linarith) (by linarith)

theorem nhLUJ2_p4_g4 (x : ℝ) (h0 : (5 / 3) ≤ x) (h1 : x ≤ (7 / 3)) :
    0 < 39863243109360 + 253585754006248 * x - 34925459669626220 * x ^ 2 + 120607089171725806 * x ^ 3 + 181692751412253800 * x ^ 4 + 49314629522486252 * x ^ 5 - 19732535597314316 * x ^ 6 - 5944425008199810 * x ^ 7 - 168733775583648 * x ^ 8 := by
  exact nhLUJ2_p4_g4_l0 x h0 h1

theorem nhLUJ2_p4 (x t : ℝ) (hx0 : (5 / 3) ≤ x) (hx1 : x ≤ (7 / 3))
    (hs0 : 0 ≤ t) (hs1 : t ≤ (449 / 3993)) (hgap : (0 : ℝ) < ((449 / 3993)) - (0)) :
    0 < nhLUJ2 t x := by
  have hpos := nh_bern_pos4 (a := (t - (0))) (b := (((449 / 3993)) - t)) (by linarith) (by linarith) (hgap.trans_eq (by ring))
    (nhLUJ2_p4_g0 x hx0 hx1) (nhLUJ2_p4_g1 x hx0 hx1) (nhLUJ2_p4_g2 x hx0 hx1) (nhLUJ2_p4_g3 x hx0 hx1) (nhLUJ2_p4_g4 x hx0 hx1)
  have e : 84737566171467 * (((449 / 3993)) - (0)) ^ 4 * (nhLUJ2 t x) = (-12880110058062984 * x ^ 2 + 271499162013380268 * x ^ 3 + 368947363110567318 * x ^ 4 + 145494401116408839 * x ^ 5 + 8050068786289365 * x ^ 6 + 508425397028802 * x ^ 7) * (((449 / 3993)) - t) ^ 4 + (381138664773240 * x - 89519965110143964 * x ^ 2 + 882754455063190842 * x ^ 3 + 1233432903979585287 * x ^ 4 + 458488677079105596 * x ^ 5 - 3750629409578403 * x ^ 6 - 6160779704509452 * x ^ 7 - 228683198863944 * x ^ 8) * (t - (0)) * (((449 / 3993)) - t) ^ 3 + (51429379559184 + 1006270982161896 * x - 172747515214228020 * x ^ 2 + 1078622182902219186 * x ^ 3 + 1548408004261119012 * x ^ 4 + 532754028509961225 * x ^ 5 - 50700018989846853 * x ^ 6 - 19685719613200476 * x ^ 7 - 621762872142852 * x ^ 8) * (t - (0)) ^ 2 * (((449 / 3993)) - t) ^ 2 + (91292622668544 + 882619795862200 * x - 131149521278380924 * x ^ 2 + 587667368509746074 * x ^ 3 + 865334778358267943 * x ^ 4 + 268964483497255216 * x ^ 5 - 58647625861015389 * x ^ 6 - 18960939519862032 * x ^ 7 - 561813448862556 * x ^ 8) * (t - (0)) ^ 3 * (((449 / 3993)) - t) + (39863243109360 + 253585754006248 * x - 34925459669626220 * x ^ 2 + 120607089171725806 * x ^ 3 + 181692751412253800 * x ^ 4 + 49314629522486252 * x ^ 5 - 19732535597314316 * x ^ 6 - 5944425008199810 * x ^ 7 - 168733775583648 * x ^ 8) * (t - (0)) ^ 4 := by unfold nhLUJ2; ring
  have h2 : 0 < 84737566171467 * (((449 / 3993)) - (0)) ^ 4 * (nhLUJ2 t x) := lt_of_lt_of_eq hpos e.symm
  exact pos_of_mul_pos_right h2 (by positivity)

/-- `J_2 > 0` on the unit face. -/
theorem nhLUJ2_dom (t x : ℝ) (hx0 : 1 / 2 < x) (hx1 : x ≤ 7 / 3) (ht0 : 0 ≤ t) (ht1 : t ≤ 1 / 4)
    (hxt : 1 - 2 * t ≤ x) (hT : 3 * (x + 2) ^ 3 * t ≤ -2 * x ^ 3 - x ^ 2 + 10 * x + 12) :
    0 < nhLUJ2 t x := by
  rcases le_total x 1 with hc0 | hc0
  · exact nhLUJ2_p0 x t hx0.le hc0 (by linarith) ht1 (by linarith)
  rcases le_total x (7 / 6) with hc1 | hc1
  · have hT' := nh_T_anti (xa := 1) (by norm_num) hc0 ht0 hT
    exact nhLUJ2_p1 x t hc0 hc1 ht0 (by norm_num at hT' ⊢; linarith) (by norm_num)
  rcases le_total x (4 / 3) with hc2 | hc2
  · have hT' := nh_T_anti (xa := (7 / 6)) (by norm_num) hc1 ht0 hT
    exact nhLUJ2_p2 x t hc1 hc2 ht0 (by norm_num at hT' ⊢; linarith) (by norm_num)
  rcases le_total x (5 / 3) with hc3 | hc3
  · have hT' := nh_T_anti (xa := (4 / 3)) (by norm_num) hc2 ht0 hT
    exact nhLUJ2_p3 x t hc2 hc3 ht0 (by norm_num at hT' ⊢; linarith) (by norm_num)
  have hT' := nh_T_anti (xa := (5 / 3)) (by norm_num) hc3 ht0 hT
  exact nhLUJ2_p4 x t hc3 hx1 ht0 (by norm_num at hT' ⊢; linarith) (by norm_num)

/-- The sign `J_3` on the unit face. -/
noncomputable def nhLUJ3 (t x : ℝ) : ℝ :=
  -728 * x ^ 2 + 572 * x ^ 3 + 2406 * x ^ 4 + 1797 * x ^ 5 + 480 * x ^ 6 + 35 * x ^ 7 + 128 * t * x + 3040 * t * x ^ 2 - 1840 * t * x ^ 3 - 11384 * t * x ^ 4 - 11432 * t * x ^ 5 - 4938 * t * x ^ 6 - 898 * t * x ^ 7 - 12 * t * x ^ 8 + 10 * t * x ^ 9 + 232 * t ^ 2 - 244 * t ^ 2 * x - 4578 * t ^ 2 * x ^ 2 + 1021 * t ^ 2 * x ^ 3 + 15124 * t ^ 2 * x ^ 4 + 18429 * t ^ 2 * x ^ 5 + 10140 * t ^ 2 * x ^ 6 + 2738 * t ^ 2 * x ^ 7 + 288 * t ^ 2 * x ^ 8 - 432 * t ^ 3 + 424 * t ^ 3 * x + 3412 * t ^ 3 * x ^ 2 + 1350 * t ^ 3 * x ^ 3 - 4718 * t ^ 3 * x ^ 4 - 6814 * t ^ 3 * x ^ 5 - 4180 * t ^ 3 * x ^ 6 - 1280 * t ^ 3 * x ^ 7 - 156 * t ^ 3 * x ^ 8 - 1248 * t ^ 4 * x - 2736 * t ^ 4 * x ^ 2 - 1848 * t ^ 4 * x ^ 3 - 228 * t ^ 4 * x ^ 4 + 180 * t ^ 4 * x ^ 5 + 48 * t ^ 4 * x ^ 6

private theorem nhLUJ3_p0_g0_bp0 (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    0 ≤ 471663 * a * b ^ 10 + 6973965 * a ^ 2 * b ^ 9 + 46209381 * a ^ 3 * b ^ 8 + 180478410 * a ^ 4 * b ^ 7 + 459915350 * a ^ 5 * b ^ 6 + 798984502 * a ^ 6 * b ^ 5 + 958465314 * a ^ 7 * b ^ 4 + 784197105 * a ^ 8 * b ^ 3 + 418950267 * a ^ 9 * b ^ 2 + 132018303 * a ^ 10 * b + 18640349 * a ^ 11 := by positivity

private theorem nhLUJ3_p0_g0_l0 (x : ℝ) (h0 : (1 / 2) ≤ x) (h1 : x ≤ 1) :
    0 < 256 + 1536 * x + 640 * x ^ 2 - 11648 * x ^ 3 - 24048 * x ^ 4 + 3328 * x ^ 5 + 69552 * x ^ 6 + 109808 * x ^ 7 + 88608 * x ^ 8 + 41712 * x ^ 9 + 10976 * x ^ 10 + 1248 * x ^ 11 := by
  linear_combination (1 / 64 : ℝ) * nhLUJ3_p0_g0_bp0 (2 * x - 1) (2 - 2 * x) (by linarith) (by linarith)

theorem nhLUJ3_p0_g0 (x : ℝ) (h0 : (1 / 2) ≤ x) (h1 : x ≤ 1) :
    0 < 256 + 1536 * x + 640 * x ^ 2 - 11648 * x ^ 3 - 24048 * x ^ 4 + 3328 * x ^ 5 + 69552 * x ^ 6 + 109808 * x ^ 7 + 88608 * x ^ 8 + 41712 * x ^ 9 + 10976 * x ^ 10 + 1248 * x ^ 11 := by
  exact nhLUJ3_p0_g0_l0 x h0 h1

private theorem nhLUJ3_p0_g1_bp0 (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    0 ≤ 1664307 * a * b ^ 10 + 23837364 * a ^ 2 * b ^ 9 + 152574204 * a ^ 3 * b ^ 8 + 574942060 * a ^ 4 * b ^ 7 + 1413187800 * a ^ 5 * b ^ 6 + 2368549512 * a ^ 6 * b ^ 5 + 2742561960 * a ^ 7 * b ^ 4 + 2167223492 * a ^ 8 * b ^ 3 + 1118951532 * a ^ 9 * b ^ 2 + 340966908 * a ^ 10 * b + 46579572 * a ^ 11 := by positivity

private theorem nhLUJ3_p0_g1_l0 (x : ℝ) (h0 : (1 / 2) ≤ x) (h1 : x ≤ 1) :
    0 < 2496 + 3296 * x - 10576 * x ^ 2 - 41176 * x ^ 3 - 37528 * x ^ 4 + 75792 * x ^ 5 + 231864 * x ^ 6 + 264856 * x ^ 7 + 166192 * x ^ 8 + 61312 * x ^ 9 + 12880 * x ^ 10 + 1248 * x ^ 11 := by
  linear_combination (1 / 64 : ℝ) * nhLUJ3_p0_g1_bp0 (2 * x - 1) (2 - 2 * x) (by linarith) (by linarith)

theorem nhLUJ3_p0_g1 (x : ℝ) (h0 : (1 / 2) ≤ x) (h1 : x ≤ 1) :
    0 < 2496 + 3296 * x - 10576 * x ^ 2 - 41176 * x ^ 3 - 37528 * x ^ 4 + 75792 * x ^ 5 + 231864 * x ^ 6 + 264856 * x ^ 7 + 166192 * x ^ 8 + 61312 * x ^ 9 + 12880 * x ^ 10 + 1248 * x ^ 11 := by
  exact nhLUJ3_p0_g1_l0 x h0 h1

private theorem nhLUJ3_p0_g2_bp0 (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    0 ≤ 2162943 * a * b ^ 9 + 27602298 * a ^ 2 * b ^ 8 + 155146368 * a ^ 3 * b ^ 7 + 504614544 * a ^ 4 * b ^ 6 + 1047603104 * a ^ 5 * b ^ 5 + 1440816604 * a ^ 6 * b ^ 4 + 1313764112 * a ^ 7 * b ^ 3 + 766323414 * a ^ 8 * b ^ 2 + 259623244 * a ^ 9 * b + 38943022 * a ^ 10 := by positivity

private theorem nhLUJ3_p0_g2_l0 (x : ℝ) (h0 : (1 / 2) ≤ x) (h1 : x ≤ 1) :
    0 < 4288 + 4000 * x - 30736 * x ^ 2 - 53688 * x ^ 3 + 29016 * x ^ 4 + 171228 * x ^ 5 + 229852 * x ^ 6 + 167552 * x ^ 7 + 72184 * x ^ 8 + 17288 * x ^ 9 + 1776 * x ^ 10 := by
  linear_combination (1 / 64 : ℝ) * nhLUJ3_p0_g2_bp0 (2 * x - 1) (2 - 2 * x) (by linarith) (by linarith)

theorem nhLUJ3_p0_g2 (x : ℝ) (h0 : (1 / 2) ≤ x) (h1 : x ≤ 1) :
    0 < 4288 + 4000 * x - 30736 * x ^ 2 - 53688 * x ^ 3 + 29016 * x ^ 4 + 171228 * x ^ 5 + 229852 * x ^ 6 + 167552 * x ^ 7 + 72184 * x ^ 8 + 17288 * x ^ 9 + 1776 * x ^ 10 := by
  exact nhLUJ3_p0_g2_l0 x h0 h1

private theorem nhLUJ3_p0_g3_bp0 (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    0 ≤ 1219617 * a * b ^ 9 + 14694633 * a ^ 2 * b ^ 8 + 77832564 * a ^ 3 * b ^ 7 + 238003596 * a ^ 4 * b ^ 6 + 463343516 * a ^ 5 * b ^ 5 + 595907496 * a ^ 6 * b ^ 4 + 506567280 * a ^ 7 * b ^ 3 + 274574084 * a ^ 8 * b ^ 2 + 86132360 * a ^ 9 * b + 11915508 * a ^ 10 := by positivity

private theorem nhLUJ3_p0_g3_l0 (x : ℝ) (h0 : (1 / 2) ≤ x) (h1 : x ≤ 1) :
    0 < 2544 + 3736 * x - 34868 * x ^ 2 - 9542 * x ^ 3 + 72850 * x ^ 4 + 91498 * x ^ 5 + 53520 * x ^ 6 + 14632 * x ^ 7 - 2532 * x ^ 8 - 2488 * x ^ 9 - 320 * x ^ 10 := by
  linear_combination (1 / 64 : ℝ) * nhLUJ3_p0_g3_bp0 (2 * x - 1) (2 - 2 * x) (by linarith) (by linarith)

theorem nhLUJ3_p0_g3 (x : ℝ) (h0 : (1 / 2) ≤ x) (h1 : x ≤ 1) :
    0 < 2544 + 3736 * x - 34868 * x ^ 2 - 9542 * x ^ 3 + 72850 * x ^ 4 + 91498 * x ^ 5 + 53520 * x ^ 6 + 14632 * x ^ 7 - 2532 * x ^ 8 - 2488 * x ^ 9 - 320 * x ^ 10 := by
  exact nhLUJ3_p0_g3_l0 x h0 h1

private theorem nhLUJ3_p0_g4_bp0 (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    0 ≤ 249318 * a * b ^ 8 + 2513772 * a ^ 2 * b ^ 7 + 10866492 * a ^ 3 * b ^ 6 + 26267392 * a ^ 4 * b ^ 5 + 38784038 * a ^ 5 * b ^ 4 + 35758676 * a ^ 6 * b ^ 3 + 20057748 * a ^ 7 * b ^ 2 + 6236133 * a ^ 8 * b + 818397 * a ^ 9 := by positivity

private theorem nhLUJ3_p0_g4_l0 (x : ℝ) (h0 : (1 / 2) ≤ x) (h1 : x ≤ 1) :
    0 < 496 + 1184 * x - 13536 * x ^ 2 + 12140 * x ^ 3 + 27561 * x ^ 4 - 957 * x ^ 5 - 11896 * x ^ 6 - 2456 * x ^ 7 + 804 * x ^ 8 + 160 * x ^ 9 := by
  linear_combination (1 / 64 : ℝ) * nhLUJ3_p0_g4_bp0 (2 * x - 1) (2 - 2 * x) (by linarith) (by linarith)

theorem nhLUJ3_p0_g4 (x : ℝ) (h0 : (1 / 2) ≤ x) (h1 : x ≤ 1) :
    0 < 496 + 1184 * x - 13536 * x ^ 2 + 12140 * x ^ 3 + 27561 * x ^ 4 - 957 * x ^ 5 - 11896 * x ^ 6 - 2456 * x ^ 7 + 804 * x ^ 8 + 160 * x ^ 9 := by
  exact nhLUJ3_p0_g4_l0 x h0 h1

theorem nhLUJ3_p0 (x t : ℝ) (hx0 : (1 / 2) ≤ x) (hx1 : x ≤ 1)
    (hs0 : (1 / 2) - (1 / 2) * x ≤ t) (hs1 : t ≤ (1 / 4)) (hgap : (0 : ℝ) < ((1 / 4)) - ((1 / 2) - (1 / 2) * x)) :
    0 < nhLUJ3 t x := by
  have hpos := nh_bern_pos4 (a := (t - ((1 / 2) - (1 / 2) * x))) (b := (((1 / 4)) - t)) (by linarith) (by linarith) (hgap.trans_eq (by ring))
    (nhLUJ3_p0_g0 x hx0 hx1) (nhLUJ3_p0_g1 x hx0 hx1) (nhLUJ3_p0_g2 x hx0 hx1) (nhLUJ3_p0_g3 x hx0 hx1) (nhLUJ3_p0_g4 x hx0 hx1)
  have e : 64 * (((1 / 4)) - ((1 / 2) - (1 / 2) * x)) ^ 4 * (nhLUJ3 t x) = (256 + 1536 * x + 640 * x ^ 2 - 11648 * x ^ 3 - 24048 * x ^ 4 + 3328 * x ^ 5 + 69552 * x ^ 6 + 109808 * x ^ 7 + 88608 * x ^ 8 + 41712 * x ^ 9 + 10976 * x ^ 10 + 1248 * x ^ 11) * (((1 / 4)) - t) ^ 4 + (2496 + 3296 * x - 10576 * x ^ 2 - 41176 * x ^ 3 - 37528 * x ^ 4 + 75792 * x ^ 5 + 231864 * x ^ 6 + 264856 * x ^ 7 + 166192 * x ^ 8 + 61312 * x ^ 9 + 12880 * x ^ 10 + 1248 * x ^ 11) * (t - ((1 / 2) - (1 / 2) * x)) * (((1 / 4)) - t) ^ 3 + (4288 + 4000 * x - 30736 * x ^ 2 - 53688 * x ^ 3 + 29016 * x ^ 4 + 171228 * x ^ 5 + 229852 * x ^ 6 + 167552 * x ^ 7 + 72184 * x ^ 8 + 17288 * x ^ 9 + 1776 * x ^ 10) * (t - ((1 / 2) - (1 / 2) * x)) ^ 2 * (((1 / 4)) - t) ^ 2 + (2544 + 3736 * x - 34868 * x ^ 2 - 9542 * x ^ 3 + 72850 * x ^ 4 + 91498 * x ^ 5 + 53520 * x ^ 6 + 14632 * x ^ 7 - 2532 * x ^ 8 - 2488 * x ^ 9 - 320 * x ^ 10) * (t - ((1 / 2) - (1 / 2) * x)) ^ 3 * (((1 / 4)) - t) + (496 + 1184 * x - 13536 * x ^ 2 + 12140 * x ^ 3 + 27561 * x ^ 4 - 957 * x ^ 5 - 11896 * x ^ 6 - 2456 * x ^ 7 + 804 * x ^ 8 + 160 * x ^ 9) * (t - ((1 / 2) - (1 / 2) * x)) ^ 4 := by unfold nhLUJ3; ring
  have h2 : 0 < 64 * (((1 / 4)) - ((1 / 2) - (1 / 2) * x)) ^ 4 * (nhLUJ3 t x) := lt_of_lt_of_eq hpos e.symm
  exact pos_of_mul_pos_right h2 (by positivity)

private theorem nhLUJ3_p1_g0_bp0 (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    0 ≤ 210393240372 * a * b ^ 6 + 1525926543300 * a ^ 2 * b ^ 5 + 4639505439168 * a ^ 3 * b ^ 4 + 7562786650344 * a ^ 4 * b ^ 3 + 6964920485460 * a ^ 5 * b ^ 2 + 3433142793492 * a ^ 6 * b + 707066215416 * a ^ 7 := by positivity

private theorem nhLUJ3_p1_g0_l0 (x : ℝ) (h0 : 1 ≤ x) (h1 : x ≤ (5 / 3)) :
    0 < -10446004296 * x ^ 2 + 8207574804 * x ^ 3 + 34523470242 * x ^ 4 + 25784985879 * x ^ 5 + 6887475360 * x ^ 6 + 502211745 * x ^ 7 := by
  linear_combination (1 / 128 : ℝ) * nhLUJ3_p1_g0_bp0 (3 * x - 3) (5 - 3 * x) (by linarith) (by linarith)

theorem nhLUJ3_p1_g0 (x : ℝ) (h0 : 1 ≤ x) (h1 : x ≤ (5 / 3)) :
    0 < -10446004296 * x ^ 2 + 8207574804 * x ^ 3 + 34523470242 * x ^ 4 + 25784985879 * x ^ 5 + 6887475360 * x ^ 6 + 502211745 * x ^ 7 := by
  exact nhLUJ3_p1_g0_l0 x h0 h1

private theorem nhLUJ3_p1_g1_bp0 (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    0 ≤ 532081563552 * a * b ^ 8 + 4895046521424 * a ^ 2 * b ^ 7 + 19739204990208 * a ^ 3 * b ^ 6 + 45545049058032 * a ^ 4 * b ^ 5 + 65732697651744 * a ^ 5 * b ^ 4 + 60734824673328 * a ^ 6 * b ^ 3 + 35068389687360 * a ^ 7 * b ^ 2 + 11564417714832 * a ^ 8 * b + 1666964950272 * a ^ 9 := by positivity

private theorem nhLUJ3_p1_g1_l0 (x : ℝ) (h0 : 1 ≤ x) (h1 : x ≤ (5 / 3)) :
    0 < 430821504 * x - 31552006464 * x ^ 2 + 26637240096 * x ^ 3 + 99777693456 * x ^ 4 + 64662197940 * x ^ 5 + 10929615606 * x ^ 6 - 1013635134 * x ^ 7 - 40389516 * x ^ 8 + 33657930 * x ^ 9 := by
  linear_combination (1 / 512 : ℝ) * nhLUJ3_p1_g1_bp0 (3 * x - 3) (5 - 3 * x) (by linarith) (by linarith)

theorem nhLUJ3_p1_g1 (x : ℝ) (h0 : 1 ≤ x) (h1 : x ≤ (5 / 3)) :
    0 < 430821504 * x - 31552006464 * x ^ 2 + 26637240096 * x ^ 3 + 99777693456 * x ^ 4 + 64662197940 * x ^ 5 + 10929615606 * x ^ 6 - 1013635134 * x ^ 7 - 40389516 * x ^ 8 + 33657930 * x ^ 9 := by
  exact nhLUJ3_p1_g1_l0 x h0 h1

private theorem nhLUJ3_p1_g2_bp0 (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    0 ≤ 454213483956 * a * b ^ 8 + 4139838787716 * a ^ 2 * b ^ 7 + 16513887202164 * a ^ 3 * b ^ 6 + 37631894167188 * a ^ 4 * b ^ 5 + 53548939872396 * a ^ 5 * b ^ 4 + 48694726435020 * a ^ 6 * b ^ 3 + 27619845363004 * a ^ 7 * b ^ 2 + 8929999247900 * a ^ 8 * b + 1259575342864 * a ^ 9 := by positivity

private theorem nhLUJ3_p1_g2_l0 (x : ℝ) (h0 : 1 ≤ x) (h1 : x ≤ (5 / 3)) :
    0 < 183165624 + 1099824804 * x - 35594356662 * x ^ 2 + 31472358111 * x ^ 3 + 104132762784 * x ^ 4 + 53826503049 * x ^ 5 - 530404362 * x ^ 6 - 3892505706 * x ^ 7 + 106209468 * x ^ 8 + 100973790 * x ^ 9 := by
  linear_combination (1 / 512 : ℝ) * nhLUJ3_p1_g2_bp0 (3 * x - 3) (5 - 3 * x) (by linarith) (by linarith)

theorem nhLUJ3_p1_g2 (x : ℝ) (h0 : 1 ≤ x) (h1 : x ≤ (5 / 3)) :
    0 < 183165624 + 1099824804 * x - 35594356662 * x ^ 2 + 31472358111 * x ^ 3 + 104132762784 * x ^ 4 + 53826503049 * x ^ 5 - 530404362 * x ^ 6 - 3892505706 * x ^ 7 + 106209468 * x ^ 8 + 100973790 * x ^ 9 := by
  exact nhLUJ3_p1_g2_l0 x h0 h1

private theorem nhLUJ3_p1_g3_bp0 (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    0 ≤ 11684821872960 * a * b ^ 8 + 104518167506352 * a ^ 2 * b ^ 7 + 407721081952512 * a ^ 3 * b ^ 6 + 904959602612784 * a ^ 4 * b ^ 5 + 1248545113884864 * a ^ 5 * b ^ 4 + 1095142956467472 * a ^ 6 * b ^ 3 + 595659185981696 * a ^ 7 * b ^ 2 + 183453674328336 * a ^ 8 * b + 24464409974272 * a ^ 9 := by positivity

private theorem nhLUJ3_p1_g3_l0 (x : ℝ) (h0 : 1 ≤ x) (h1 : x ≤ (5 / 3)) :
    0 < 286327872 + 985706928 * x - 17684832600 * x ^ 2 + 16113305700 * x ^ 3 + 46152585594 * x ^ 4 + 15544450692 * x ^ 5 - 7073860842 * x ^ 6 - 2972306070 * x ^ 7 + 304697376 * x ^ 8 + 100973790 * x ^ 9 := by
  linear_combination (1 / 41472 : ℝ) * nhLUJ3_p1_g3_bp0 (3 * x - 3) (5 - 3 * x) (by linarith) (by linarith)

theorem nhLUJ3_p1_g3 (x : ℝ) (h0 : 1 ≤ x) (h1 : x ≤ (5 / 3)) :
    0 < 286327872 + 985706928 * x - 17684832600 * x ^ 2 + 16113305700 * x ^ 3 + 46152585594 * x ^ 4 + 15544450692 * x ^ 5 - 7073860842 * x ^ 6 - 2972306070 * x ^ 7 + 304697376 * x ^ 8 + 100973790 * x ^ 9 := by
  exact nhLUJ3_p1_g3_l0 x h0 h1

private theorem nhLUJ3_p1_g4_bp0 (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    0 ≤ 8299463970960 * a * b ^ 8 + 69931101228912 * a ^ 2 * b ^ 7 + 252580558866768 * a ^ 3 * b ^ 6 + 506984311012608 * a ^ 4 * b ^ 5 + 611513804409120 * a ^ 5 * b ^ 4 + 445042180802608 * a ^ 6 * b ^ 3 + 183426826247184 * a ^ 7 * b ^ 2 + 35235242476896 * a ^ 8 * b + 1372820281072 * a ^ 9 := by positivity

private theorem nhLUJ3_p1_g4_l0 (x : ℝ) (h0 : 1 ≤ x) (h1 : x ≤ (5 / 3)) :
    0 < 103162248 + 262490092 * x - 3315330858 * x ^ 2 + 2990335145 * x ^ 3 + 7264141628 * x ^ 4 + 602978964 * x ^ 5 - 2499231098 * x ^ 6 - 595647243 * x ^ 7 + 158098392 * x ^ 8 + 33657930 * x ^ 9 := by
  linear_combination (1 / 373248 : ℝ) * nhLUJ3_p1_g4_bp0 (3 * x - 3) (5 - 3 * x) (by linarith) (by linarith)

theorem nhLUJ3_p1_g4 (x : ℝ) (h0 : 1 ≤ x) (h1 : x ≤ (5 / 3)) :
    0 < 103162248 + 262490092 * x - 3315330858 * x ^ 2 + 2990335145 * x ^ 3 + 7264141628 * x ^ 4 + 602978964 * x ^ 5 - 2499231098 * x ^ 6 - 595647243 * x ^ 7 + 158098392 * x ^ 8 + 33657930 * x ^ 9 := by
  exact nhLUJ3_p1_g4_l0 x h0 h1

theorem nhLUJ3_p1 (x t : ℝ) (hx0 : 1 ≤ x) (hx1 : x ≤ (5 / 3))
    (hs0 : 0 ≤ t) (hs1 : t ≤ (19 / 81)) (hgap : (0 : ℝ) < ((19 / 81)) - (0)) :
    0 < nhLUJ3 t x := by
  have hpos := nh_bern_pos4 (a := (t - (0))) (b := (((19 / 81)) - t)) (by linarith) (by linarith) (hgap.trans_eq (by ring))
    (nhLUJ3_p1_g0 x hx0 hx1) (nhLUJ3_p1_g1 x hx0 hx1) (nhLUJ3_p1_g2 x hx0 hx1) (nhLUJ3_p1_g3 x hx0 hx1) (nhLUJ3_p1_g4 x hx0 hx1)
  have e : 14348907 * (((19 / 81)) - (0)) ^ 4 * (nhLUJ3 t x) = (-10446004296 * x ^ 2 + 8207574804 * x ^ 3 + 34523470242 * x ^ 4 + 25784985879 * x ^ 5 + 6887475360 * x ^ 6 + 502211745 * x ^ 7) * (((19 / 81)) - t) ^ 4 + (430821504 * x - 31552006464 * x ^ 2 + 26637240096 * x ^ 3 + 99777693456 * x ^ 4 + 64662197940 * x ^ 5 + 10929615606 * x ^ 6 - 1013635134 * x ^ 7 - 40389516 * x ^ 8 + 33657930 * x ^ 9) * (t - (0)) * (((19 / 81)) - t) ^ 3 + (183165624 + 1099824804 * x - 35594356662 * x ^ 2 + 31472358111 * x ^ 3 + 104132762784 * x ^ 4 + 53826503049 * x ^ 5 - 530404362 * x ^ 6 - 3892505706 * x ^ 7 + 106209468 * x ^ 8 + 100973790 * x ^ 9) * (t - (0)) ^ 2 * (((19 / 81)) - t) ^ 2 + (286327872 + 985706928 * x - 17684832600 * x ^ 2 + 16113305700 * x ^ 3 + 46152585594 * x ^ 4 + 15544450692 * x ^ 5 - 7073860842 * x ^ 6 - 2972306070 * x ^ 7 + 304697376 * x ^ 8 + 100973790 * x ^ 9) * (t - (0)) ^ 3 * (((19 / 81)) - t) + (103162248 + 262490092 * x - 3315330858 * x ^ 2 + 2990335145 * x ^ 3 + 7264141628 * x ^ 4 + 602978964 * x ^ 5 - 2499231098 * x ^ 6 - 595647243 * x ^ 7 + 158098392 * x ^ 8 + 33657930 * x ^ 9) * (t - (0)) ^ 4 := by unfold nhLUJ3; ring
  have h2 : 0 < 14348907 * (((19 / 81)) - (0)) ^ 4 * (nhLUJ3 t x) := lt_of_lt_of_eq hpos e.symm
  exact pos_of_mul_pos_right h2 (by positivity)

private theorem nhLUJ3_p2_g0_bp0 (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    0 ≤ 725326011026609909620 * a * b ^ 6 + 4932885448101183506604 * a ^ 2 * b ^ 5 + 14029446141218937115016 * a ^ 3 * b ^ 4 + 21353820653295967763256 * a ^ 4 * b ^ 3 + 18341557637128832759268 * a ^ 5 * b ^ 2 + 8427501995243186147292 * a ^ 6 * b + 1617892367425085343328 * a ^ 7 := by positivity

private theorem nhLUJ3_p2_g0_l0 (x : ℝ) (h0 : (5 / 3) ≤ x) (h1 : x ≤ (7 / 3)) :
    0 < -61688948172827976 * x ^ 2 + 48469887850079124 * x ^ 3 + 203878584208549602 * x ^ 4 + 152273406410126199 * x ^ 5 + 40674031762304160 * x ^ 6 + 2965814816001345 * x ^ 7 := by
  linear_combination (1 / 10368 : ℝ) * nhLUJ3_p2_g0_bp0 (3 * x - 5) (7 - 3 * x) (by linarith) (by linarith)

theorem nhLUJ3_p2_g0 (x : ℝ) (h0 : (5 / 3) ≤ x) (h1 : x ≤ (7 / 3)) :
    0 < -61688948172827976 * x ^ 2 + 48469887850079124 * x ^ 3 + 203878584208549602 * x ^ 4 + 152273406410126199 * x ^ 5 + 40674031762304160 * x ^ 6 + 2965814816001345 * x ^ 7 := by
  exact nhLUJ3_p2_g0_l0 x h0 h1

private theorem nhLUJ3_p2_g1_bp0 (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    0 ≤ 62070469453623967349904 * a * b ^ 8 + 545101012543725467954784 * a ^ 2 * b ^ 7 + 2097480745611506942872944 * a ^ 3 * b ^ 6 + 4618168623374993396151552 * a ^ 4 * b ^ 5 + 6362785308294163562351472 * a ^ 5 * b ^ 4 + 5616515779871483638600416 * a ^ 6 * b ^ 3 + 3101460105901412712142224 * a ^ 7 * b ^ 2 + 979412242189239806726592 * a ^ 8 * b + 135401034139373912602880 * a ^ 9 := by positivity

private theorem nhLUJ3_p2_g1_l0 (x : ℝ) (h0 : (5 / 3) ≤ x) (h1 : x ≤ (7 / 3)) :
    0 < 1219643727274368 * x - 217789254168545664 * x ^ 2 + 176347172820747456 * x ^ 3 + 707042272839734304 * x ^ 4 + 500164195248312804 * x ^ 5 + 115644558882960162 * x ^ 6 + 3306696239846142 * x ^ 7 - 114341599431972 * x ^ 8 + 95284666193310 * x ^ 9 := by
  linear_combination (1 / 1119744 : ℝ) * nhLUJ3_p2_g1_bp0 (3 * x - 5) (7 - 3 * x) (by linarith) (by linarith)

theorem nhLUJ3_p2_g1 (x : ℝ) (h0 : (5 / 3) ≤ x) (h1 : x ≤ (7 / 3)) :
    0 < 1219643727274368 * x - 217789254168545664 * x ^ 2 + 176347172820747456 * x ^ 3 + 707042272839734304 * x ^ 4 + 500164195248312804 * x ^ 5 + 115644558882960162 * x ^ 6 + 3306696239846142 * x ^ 7 - 114341599431972 * x ^ 8 + 95284666193310 * x ^ 9 := by
  exact nhLUJ3_p2_g1_l0 x h0 h1

private theorem nhLUJ3_p2_g2_bp0 (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    0 ≤ 24079478728224560320372 * a * b ^ 8 + 210910882184429085182876 * a ^ 2 * b ^ 7 + 809250946244314862903868 * a ^ 3 * b ^ 6 + 1776318751700130973869292 * a ^ 4 * b ^ 5 + 2439312519188528084088020 * a ^ 5 * b ^ 4 + 2145661950911925530036436 * a ^ 6 * b ^ 3 + 1180438171646471353072468 * a ^ 7 * b ^ 2 + 371312261795809334089892 * a ^ 8 * b + 51122736205394850679848 * a ^ 9 := by positivity

private theorem nhLUJ3_p2_g2_l0 (x : ℝ) (h0 : (5 / 3) ≤ x) (h1 : x ≤ (7 / 3)) :
    0 < 248575334536056 + 3397498502397252 * x - 288139150544126310 * x ^ 2 + 239316137122807767 * x ^ 3 + 914059853610678192 * x ^ 4 + 606597814698685425 * x ^ 5 + 113753942506933146 * x ^ 6 - 4941182650781190 * x ^ 7 - 34448520940812 * x ^ 8 + 285853998579930 * x ^ 9 := by
  linear_combination (1 / 373248 : ℝ) * nhLUJ3_p2_g2_bp0 (3 * x - 5) (7 - 3 * x) (by linarith) (by linarith)

theorem nhLUJ3_p2_g2 (x : ℝ) (h0 : (5 / 3) ≤ x) (h1 : x ≤ (7 / 3)) :
    0 < 248575334536056 + 3397498502397252 * x - 288139150544126310 * x ^ 2 + 239316137122807767 * x ^ 3 + 914059853610678192 * x ^ 4 + 606597814698685425 * x ^ 5 + 113753942506933146 * x ^ 6 - 4941182650781190 * x ^ 7 - 34448520940812 * x ^ 8 + 285853998579930 * x ^ 9 := by
  exact nhLUJ3_p2_g2_l0 x h0 h1

private theorem nhLUJ3_p2_g3_bp0 (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    0 ≤ 36444973667046089078208 * a * b ^ 8 + 318185643341903047941296 * a ^ 2 * b ^ 7 + 1216567961831947310543584 * a ^ 3 * b ^ 6 + 2660271714132623121885552 * a ^ 4 * b ^ 5 + 3638367247316604985972064 * a ^ 5 * b ^ 4 + 3186547331675222096653456 * a ^ 6 * b ^ 3 + 1745078531218397347476768 * a ^ 7 * b ^ 2 + 546293930630679788372816 * a ^ 8 * b + 74839922008348685440736 * a ^ 9 := by positivity

private theorem nhLUJ3_p2_g3_l0 (x : ℝ) (h0 : (5 / 3) ≤ x) (h1 : x ≤ (7 / 3)) :
    0 < 445103055047904 + 3187149592291456 * x - 169255251507606704 * x ^ 2 + 143632955977515312 * x ^ 3 + 521938798122078238 * x ^ 4 + 320975714566175768 * x ^ 5 + 42766726556283026 * x ^ 6 - 8093409909759746 * x ^ 7 + 255332784683328 * x ^ 8 + 285853998579930 * x ^ 9 := by
  linear_combination (1 / 1119744 : ℝ) * nhLUJ3_p2_g3_bp0 (3 * x - 5) (7 - 3 * x) (by linarith) (by linarith)

theorem nhLUJ3_p2_g3 (x : ℝ) (h0 : (5 / 3) ≤ x) (h1 : x ≤ (7 / 3)) :
    0 < 445103055047904 + 3187149592291456 * x - 169255251507606704 * x ^ 2 + 143632955977515312 * x ^ 3 + 521938798122078238 * x ^ 4 + 320975714566175768 * x ^ 5 + 42766726556283026 * x ^ 6 - 8093409909759746 * x ^ 7 + 255332784683328 * x ^ 8 + 285853998579930 * x ^ 9 := by
  exact nhLUJ3_p2_g3_l0 x h0 h1

private theorem nhLUJ3_p2_g4_bp0 (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    0 ≤ 6692822584344363633408 * a * b ^ 8 + 58195416356620884150656 * a ^ 2 * b ^ 7 + 221530388286071737428736 * a ^ 3 * b ^ 6 + 482131348387578838938192 * a ^ 4 * b ^ 5 + 656064865712664852703664 * a ^ 5 * b ^ 4 + 571516438931809882856800 * a ^ 6 * b ^ 3 + 311223652440108190941216 * a ^ 7 * b ^ 2 + 96857841827618749855952 * a ^ 8 * b + 13189321901077998980656 * a ^ 9 := by positivity

private theorem nhLUJ3_p2_g4_l0 (x : ℝ) (h0 : (5 / 3) ≤ x) (h1 : x ≤ (7 / 3)) :
    0 < 196527720511848 + 992387344476956 * x - 37253473341637394 * x ^ 2 + 32169067760044061 * x ^ 3 + 111039544277381472 * x ^ 4 + 62271127283469008 * x ^ 5 + 3983961457417098 * x ^ 6 - 2811345835133759 * x ^ 7 + 175439706192168 * x ^ 8 + 95284666193310 * x ^ 9 := by
  linear_combination (1 / 1119744 : ℝ) * nhLUJ3_p2_g4_bp0 (3 * x - 5) (7 - 3 * x) (by linarith) (by linarith)

theorem nhLUJ3_p2_g4 (x : ℝ) (h0 : (5 / 3) ≤ x) (h1 : x ≤ (7 / 3)) :
    0 < 196527720511848 + 992387344476956 * x - 37253473341637394 * x ^ 2 + 32169067760044061 * x ^ 3 + 111039544277381472 * x ^ 4 + 62271127283469008 * x ^ 5 + 3983961457417098 * x ^ 6 - 2811345835133759 * x ^ 7 + 175439706192168 * x ^ 8 + 95284666193310 * x ^ 9 := by
  exact nhLUJ3_p2_g4_l0 x h0 h1

theorem nhLUJ3_p2 (x t : ℝ) (hx0 : (5 / 3) ≤ x) (hx1 : x ≤ (7 / 3))
    (hs0 : 0 ≤ t) (hs1 : t ≤ (449 / 3993)) (hgap : (0 : ℝ) < ((449 / 3993)) - (0)) :
    0 < nhLUJ3 t x := by
  have hpos := nh_bern_pos4 (a := (t - (0))) (b := (((449 / 3993)) - t)) (by linarith) (by linarith) (hgap.trans_eq (by ring))
    (nhLUJ3_p2_g0 x hx0 hx1) (nhLUJ3_p2_g1 x hx0 hx1) (nhLUJ3_p2_g2 x hx0 hx1) (nhLUJ3_p2_g3 x hx0 hx1) (nhLUJ3_p2_g4 x hx0 hx1)
  have e : 84737566171467 * (((449 / 3993)) - (0)) ^ 4 * (nhLUJ3 t x) = (-61688948172827976 * x ^ 2 + 48469887850079124 * x ^ 3 + 203878584208549602 * x ^ 4 + 152273406410126199 * x ^ 5 + 40674031762304160 * x ^ 6 + 2965814816001345 * x ^ 7) * (((449 / 3993)) - t) ^ 4 + (1219643727274368 * x - 217789254168545664 * x ^ 2 + 176347172820747456 * x ^ 3 + 707042272839734304 * x ^ 4 + 500164195248312804 * x ^ 5 + 115644558882960162 * x ^ 6 + 3306696239846142 * x ^ 7 - 114341599431972 * x ^ 8 + 95284666193310 * x ^ 9) * (t - (0)) * (((449 / 3993)) - t) ^ 3 + (248575334536056 + 3397498502397252 * x - 288139150544126310 * x ^ 2 + 239316137122807767 * x ^ 3 + 914059853610678192 * x ^ 4 + 606597814698685425 * x ^ 5 + 113753942506933146 * x ^ 6 - 4941182650781190 * x ^ 7 - 34448520940812 * x ^ 8 + 285853998579930 * x ^ 9) * (t - (0)) ^ 2 * (((449 / 3993)) - t) ^ 2 + (445103055047904 + 3187149592291456 * x - 169255251507606704 * x ^ 2 + 143632955977515312 * x ^ 3 + 521938798122078238 * x ^ 4 + 320975714566175768 * x ^ 5 + 42766726556283026 * x ^ 6 - 8093409909759746 * x ^ 7 + 255332784683328 * x ^ 8 + 285853998579930 * x ^ 9) * (t - (0)) ^ 3 * (((449 / 3993)) - t) + (196527720511848 + 992387344476956 * x - 37253473341637394 * x ^ 2 + 32169067760044061 * x ^ 3 + 111039544277381472 * x ^ 4 + 62271127283469008 * x ^ 5 + 3983961457417098 * x ^ 6 - 2811345835133759 * x ^ 7 + 175439706192168 * x ^ 8 + 95284666193310 * x ^ 9) * (t - (0)) ^ 4 := by unfold nhLUJ3; ring
  have h2 : 0 < 84737566171467 * (((449 / 3993)) - (0)) ^ 4 * (nhLUJ3 t x) := lt_of_lt_of_eq hpos e.symm
  exact pos_of_mul_pos_right h2 (by positivity)

/-- `J_3 > 0` on the unit face. -/
theorem nhLUJ3_dom (t x : ℝ) (hx0 : 1 / 2 < x) (hx1 : x ≤ 7 / 3) (ht0 : 0 ≤ t) (ht1 : t ≤ 1 / 4)
    (hxt : 1 - 2 * t ≤ x) (hT : 3 * (x + 2) ^ 3 * t ≤ -2 * x ^ 3 - x ^ 2 + 10 * x + 12) :
    0 < nhLUJ3 t x := by
  rcases le_total x 1 with hc0 | hc0
  · exact nhLUJ3_p0 x t hx0.le hc0 (by linarith) ht1 (by linarith)
  rcases le_total x (5 / 3) with hc1 | hc1
  · have hT' := nh_T_anti (xa := 1) (by norm_num) hc0 ht0 hT
    exact nhLUJ3_p1 x t hc0 hc1 ht0 (by norm_num at hT' ⊢; linarith) (by norm_num)
  have hT' := nh_T_anti (xa := (5 / 3)) (by norm_num) hc1 ht0 hT
  exact nhLUJ3_p2 x t hc1 hx1 ht0 (by norm_num at hT' ⊢; linarith) (by norm_num)

/-- The sign `J_4` on the unit face. -/
noncomputable def nhLUJ4 (t x : ℝ) : ℝ :=
  -120 * x ^ 2 - 20 * x ^ 3 + 270 * x ^ 4 + 277 * x ^ 5 + 100 * x ^ 6 + 11 * x ^ 7 - 32 * t * x + 656 * t * x ^ 2 + 968 * t * x ^ 3 + 204 * t * x ^ 4 - 84 * t * x ^ 5 + 222 * t * x ^ 6 + 250 * t * x ^ 7 + 84 * t * x ^ 8 + 10 * t * x ^ 9 + 40 * t ^ 2 + 268 * t ^ 2 * x - 418 * t ^ 2 * x ^ 2 - 531 * t ^ 2 * x ^ 3 + 1408 * t ^ 2 * x ^ 4 + 2509 * t ^ 2 * x ^ 5 + 1540 * t ^ 2 * x ^ 6 + 426 * t ^ 2 * x ^ 7 + 48 * t ^ 2 * x ^ 8 - 48 * t ^ 3 - 24 * t ^ 3 * x + 1172 * t ^ 3 * x ^ 2 + 2630 * t ^ 3 * x ^ 3 + 2138 * t ^ 3 * x ^ 4 + 646 * t ^ 3 * x ^ 5 - 48 * t ^ 3 * x ^ 6 - 68 * t ^ 3 * x ^ 7 - 12 * t ^ 3 * x ^ 8 - 96 * t ^ 4 * x - 432 * t ^ 4 * x ^ 2 - 696 * t ^ 4 * x ^ 3 - 516 * t ^ 4 * x ^ 4 - 180 * t ^ 4 * x ^ 5 - 24 * t ^ 4 * x ^ 6

private theorem nhLUJ4_p0_g0_bp0 (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    0 ≤ 767151 * a * b ^ 10 + 8280585 * a ^ 2 * b ^ 9 + 40226509 * a ^ 3 * b ^ 8 + 115826506 * a ^ 4 * b ^ 7 + 218955878 * a ^ 5 * b ^ 6 + 284067910 * a ^ 6 * b ^ 5 + 256342034 * a ^ 7 * b ^ 4 + 159056873 * a ^ 8 * b ^ 3 + 65053731 * a ^ 9 * b ^ 2 + 15873543 * a ^ 10 * b + 1760117 * a ^ 11 := by positivity

private theorem nhLUJ4_p0_g0_l0 (x : ℝ) (h0 : (1 / 2) ≤ x) (h1 : x ≤ 1) :
    0 < 256 + 2560 * x + 8320 * x ^ 2 + 12416 * x ^ 3 + 8208 * x ^ 4 + 64 * x ^ 5 - 2736 * x ^ 6 - 176 * x ^ 7 + 1920 * x ^ 8 + 1616 * x ^ 9 + 608 * x ^ 10 + 96 * x ^ 11 := by
  linear_combination (1 / 64 : ℝ) * nhLUJ4_p0_g0_bp0 (2 * x - 1) (2 - 2 * x) (by linarith) (by linarith)

theorem nhLUJ4_p0_g0 (x : ℝ) (h0 : (1 / 2) ≤ x) (h1 : x ≤ 1) :
    0 < 256 + 2560 * x + 8320 * x ^ 2 + 12416 * x ^ 3 + 8208 * x ^ 4 + 64 * x ^ 5 - 2736 * x ^ 6 - 176 * x ^ 7 + 1920 * x ^ 8 + 1616 * x ^ 9 + 608 * x ^ 10 + 96 * x ^ 11 := by
  exact nhLUJ4_p0_g0_l0 x h0 h1

private theorem nhLUJ4_p0_g1_bp0 (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    0 ≤ 3580389 * a * b ^ 10 + 39390498 * a ^ 2 * b ^ 9 + 195166516 * a ^ 3 * b ^ 8 + 573319196 * a ^ 4 * b ^ 7 + 1105510216 * a ^ 5 * b ^ 6 + 1461743272 * a ^ 6 * b ^ 5 + 1341910120 * a ^ 7 * b ^ 4 + 844414116 * a ^ 8 * b ^ 3 + 348542988 * a ^ 9 * b ^ 2 + 85216284 * a ^ 10 * b + 9373140 * a ^ 11 := by positivity

private theorem nhLUJ4_p0_g1_l0 (x : ℝ) (h0 : (1 / 2) ≤ x) (h1 : x ≤ 1) :
    0 < 960 + 7136 * x + 27312 * x ^ 2 + 55208 * x ^ 3 + 57608 * x ^ 4 + 26016 * x ^ 5 - 1944 * x ^ 6 - 5480 * x ^ 7 - 96 * x ^ 8 + 1552 * x ^ 9 + 688 * x ^ 10 + 96 * x ^ 11 := by
  linear_combination (1 / 64 : ℝ) * nhLUJ4_p0_g1_bp0 (2 * x - 1) (2 - 2 * x) (by linarith) (by linarith)

theorem nhLUJ4_p0_g1 (x : ℝ) (h0 : (1 / 2) ≤ x) (h1 : x ≤ 1) :
    0 < 960 + 7136 * x + 27312 * x ^ 2 + 55208 * x ^ 3 + 57608 * x ^ 4 + 26016 * x ^ 5 - 1944 * x ^ 6 - 5480 * x ^ 7 - 96 * x ^ 8 + 1552 * x ^ 9 + 688 * x ^ 10 + 96 * x ^ 11 := by
  exact nhLUJ4_p0_g1_l0 x h0 h1

private theorem nhLUJ4_p0_g2_bp0 (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    0 ≤ 6138261 * a * b ^ 9 + 62510316 * a ^ 2 * b ^ 8 + 283510208 * a ^ 3 * b ^ 7 + 751175328 * a ^ 4 * b ^ 6 + 1280498576 * a ^ 5 * b ^ 5 + 1455292252 * a ^ 6 * b ^ 4 + 1101751824 * a ^ 7 * b ^ 3 + 535253286 * a ^ 8 * b ^ 2 + 151245292 * a ^ 9 * b + 18912958 * a ^ 10 := by positivity

private theorem nhLUJ4_p0_g2_l0 (x : ℝ) (h0 : (1 / 2) ≤ x) (h1 : x ≤ 1) :
    0 < 1216 + 7200 * x + 33008 * x ^ 2 + 84488 * x ^ 3 + 116952 * x ^ 4 + 86532 * x ^ 5 + 24796 * x ^ 6 - 10176 * x ^ 7 - 10928 * x ^ 8 - 3336 * x ^ 9 - 336 * x ^ 10 := by
  linear_combination (1 / 64 : ℝ) * nhLUJ4_p0_g2_bp0 (2 * x - 1) (2 - 2 * x) (by linarith) (by linarith)

theorem nhLUJ4_p0_g2 (x : ℝ) (h0 : (1 / 2) ≤ x) (h1 : x ≤ 1) :
    0 < 1216 + 7200 * x + 33008 * x ^ 2 + 84488 * x ^ 3 + 116952 * x ^ 4 + 86532 * x ^ 5 + 24796 * x ^ 6 - 10176 * x ^ 7 - 10928 * x ^ 8 - 3336 * x ^ 9 - 336 * x ^ 10 := by
  exact nhLUJ4_p0_g2_l0 x h0 h1

private theorem nhLUJ4_p0_g3_bp0 (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    0 ≤ 4603959 * a * b ^ 9 + 47644041 * a ^ 2 * b ^ 8 + 219831206 * a ^ 3 * b ^ 7 + 593224164 * a ^ 4 * b ^ 6 + 1031140060 * a ^ 5 * b ^ 5 + 1196411352 * a ^ 6 * b ^ 4 + 925942928 * a ^ 7 * b ^ 3 + 460558052 * a ^ 8 * b ^ 2 + 133475144 * a ^ 9 * b + 17155668 * a ^ 10 := by positivity

private theorem nhLUJ4_p0_g3_l0 (x : ℝ) (h0 : (1 / 2) ≤ x) (h1 : x ≤ 1) :
    0 < 624 + 3160 * x + 16140 * x ^ 2 + 56122 * x ^ 3 + 96298 * x ^ 4 + 87718 * x ^ 5 + 38964 * x ^ 6 + 1156 * x ^ 7 - 6620 * x ^ 8 - 2584 * x ^ 9 - 320 * x ^ 10 := by
  linear_combination (1 / 64 : ℝ) * nhLUJ4_p0_g3_bp0 (2 * x - 1) (2 - 2 * x) (by linarith) (by linarith)

theorem nhLUJ4_p0_g3 (x : ℝ) (h0 : (1 / 2) ≤ x) (h1 : x ≤ 1) :
    0 < 624 + 3160 * x + 16140 * x ^ 2 + 56122 * x ^ 3 + 96298 * x ^ 4 + 87718 * x ^ 5 + 38964 * x ^ 6 + 1156 * x ^ 7 - 6620 * x ^ 8 - 2584 * x ^ 9 - 320 * x ^ 10 := by
  exact nhLUJ4_p0_g3_l0 x h0 h1

private theorem nhLUJ4_p0_g4_bp0 (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    0 ≤ 1278936 * a * b ^ 8 + 12151464 * a ^ 2 * b ^ 7 + 50812866 * a ^ 3 * b ^ 6 + 122080828 * a ^ 4 * b ^ 5 + 184227686 * a ^ 5 * b ^ 4 + 178729556 * a ^ 6 * b ^ 3 + 108815316 * a ^ 7 * b ^ 2 + 37997565 * a ^ 8 * b + 5824629 * a ^ 9 := by positivity

private theorem nhLUJ4_p0_g4_l0 (x : ℝ) (h0 : (1 / 2) ≤ x) (h1 : x ≤ 1) :
    0 < 112 + 512 * x + 2208 * x ^ 2 + 14540 * x ^ 3 + 28185 * x ^ 4 + 27021 * x ^ 5 + 16058 * x ^ 6 + 6340 * x ^ 7 + 1524 * x ^ 8 + 160 * x ^ 9 := by
  linear_combination (1 / 64 : ℝ) * nhLUJ4_p0_g4_bp0 (2 * x - 1) (2 - 2 * x) (by linarith) (by linarith)

theorem nhLUJ4_p0_g4 (x : ℝ) (h0 : (1 / 2) ≤ x) (h1 : x ≤ 1) :
    0 < 112 + 512 * x + 2208 * x ^ 2 + 14540 * x ^ 3 + 28185 * x ^ 4 + 27021 * x ^ 5 + 16058 * x ^ 6 + 6340 * x ^ 7 + 1524 * x ^ 8 + 160 * x ^ 9 := by
  exact nhLUJ4_p0_g4_l0 x h0 h1

theorem nhLUJ4_p0 (x t : ℝ) (hx0 : (1 / 2) ≤ x) (hx1 : x ≤ 1)
    (hs0 : (1 / 2) - (1 / 2) * x ≤ t) (hs1 : t ≤ (1 / 4)) (hgap : (0 : ℝ) < ((1 / 4)) - ((1 / 2) - (1 / 2) * x)) :
    0 < nhLUJ4 t x := by
  have hpos := nh_bern_pos4 (a := (t - ((1 / 2) - (1 / 2) * x))) (b := (((1 / 4)) - t)) (by linarith) (by linarith) (hgap.trans_eq (by ring))
    (nhLUJ4_p0_g0 x hx0 hx1) (nhLUJ4_p0_g1 x hx0 hx1) (nhLUJ4_p0_g2 x hx0 hx1) (nhLUJ4_p0_g3 x hx0 hx1) (nhLUJ4_p0_g4 x hx0 hx1)
  have e : 64 * (((1 / 4)) - ((1 / 2) - (1 / 2) * x)) ^ 4 * (nhLUJ4 t x) = (256 + 2560 * x + 8320 * x ^ 2 + 12416 * x ^ 3 + 8208 * x ^ 4 + 64 * x ^ 5 - 2736 * x ^ 6 - 176 * x ^ 7 + 1920 * x ^ 8 + 1616 * x ^ 9 + 608 * x ^ 10 + 96 * x ^ 11) * (((1 / 4)) - t) ^ 4 + (960 + 7136 * x + 27312 * x ^ 2 + 55208 * x ^ 3 + 57608 * x ^ 4 + 26016 * x ^ 5 - 1944 * x ^ 6 - 5480 * x ^ 7 - 96 * x ^ 8 + 1552 * x ^ 9 + 688 * x ^ 10 + 96 * x ^ 11) * (t - ((1 / 2) - (1 / 2) * x)) * (((1 / 4)) - t) ^ 3 + (1216 + 7200 * x + 33008 * x ^ 2 + 84488 * x ^ 3 + 116952 * x ^ 4 + 86532 * x ^ 5 + 24796 * x ^ 6 - 10176 * x ^ 7 - 10928 * x ^ 8 - 3336 * x ^ 9 - 336 * x ^ 10) * (t - ((1 / 2) - (1 / 2) * x)) ^ 2 * (((1 / 4)) - t) ^ 2 + (624 + 3160 * x + 16140 * x ^ 2 + 56122 * x ^ 3 + 96298 * x ^ 4 + 87718 * x ^ 5 + 38964 * x ^ 6 + 1156 * x ^ 7 - 6620 * x ^ 8 - 2584 * x ^ 9 - 320 * x ^ 10) * (t - ((1 / 2) - (1 / 2) * x)) ^ 3 * (((1 / 4)) - t) + (112 + 512 * x + 2208 * x ^ 2 + 14540 * x ^ 3 + 28185 * x ^ 4 + 27021 * x ^ 5 + 16058 * x ^ 6 + 6340 * x ^ 7 + 1524 * x ^ 8 + 160 * x ^ 9) * (t - ((1 / 2) - (1 / 2) * x)) ^ 4 := by unfold nhLUJ4; ring
  have h2 : 0 < 64 * (((1 / 4)) - ((1 / 2) - (1 / 2) * x)) ^ 4 * (nhLUJ4 t x) := lt_of_lt_of_eq hpos e.symm
  exact pos_of_mul_pos_right h2 (by positivity)

private theorem nhLUJ4_p1_g0_bp0 (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    0 ≤ 54372791592 * a * b ^ 6 + 477786716640 * a ^ 2 * b ^ 5 + 1784727681480 * a ^ 3 * b ^ 4 + 3609037088640 * a ^ 4 * b ^ 3 + 4148016992568 * a ^ 5 * b ^ 2 + 2559406629024 * a ^ 6 * b + 660295418328 * a ^ 7 := by positivity

private theorem nhLUJ4_p1_g0_l0 (x : ℝ) (h0 : 1 ≤ x) (h1 : x ≤ (7 / 3)) :
    0 < -1721868840 * x ^ 2 - 286978140 * x ^ 3 + 3874204890 * x ^ 4 + 3974647239 * x ^ 5 + 1434890700 * x ^ 6 + 157837977 * x ^ 7 := by
  linear_combination (1 / 16384 : ℝ) * nhLUJ4_p1_g0_bp0 (3 * x - 3) (7 - 3 * x) (by linarith) (by linarith)

theorem nhLUJ4_p1_g0 (x : ℝ) (h0 : 1 ≤ x) (h1 : x ≤ (7 / 3)) :
    0 < -1721868840 * x ^ 2 - 286978140 * x ^ 3 + 3874204890 * x ^ 4 + 3974647239 * x ^ 5 + 1434890700 * x ^ 6 + 157837977 * x ^ 7 := by
  exact nhLUJ4_p1_g0_l0 x h0 h1

private theorem nhLUJ4_p1_g1_bp0 (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    0 ≤ 255295753344 * a * b ^ 8 + 2739732512256 * a ^ 2 * b ^ 7 + 13032384928128 * a ^ 3 * b ^ 6 + 35800796130048 * a ^ 4 * b ^ 5 + 61982881845120 * a ^ 5 * b ^ 4 + 69131926573056 * a ^ 6 * b ^ 3 + 48443833088640 * a ^ 7 * b ^ 2 + 19483831072512 * a ^ 8 * b + 3442338938880 * a ^ 9 := by positivity

private theorem nhLUJ4_p1_g1_l0 (x : ℝ) (h0 : 1 ≤ x) (h1 : x ≤ (7 / 3)) :
    0 < -107705376 * x - 4679515152 * x ^ 2 + 2110175064 * x ^ 3 + 16183441332 * x ^ 4 + 15615862344 * x ^ 5 + 6486768846 * x ^ 6 + 1472800158 * x ^ 7 + 282726612 * x ^ 8 + 33657930 * x ^ 9 := by
  linear_combination (1 / 262144 : ℝ) * nhLUJ4_p1_g1_bp0 (3 * x - 3) (7 - 3 * x) (by linarith) (by linarith)

theorem nhLUJ4_p1_g1 (x : ℝ) (h0 : 1 ≤ x) (h1 : x ≤ (7 / 3)) :
    0 < -107705376 * x - 4679515152 * x ^ 2 + 2110175064 * x ^ 3 + 16183441332 * x ^ 4 + 15615862344 * x ^ 5 + 6486768846 * x ^ 6 + 1472800158 * x ^ 7 + 282726612 * x ^ 8 + 33657930 * x ^ 9 := by
  exact nhLUJ4_p1_g1_l0 x h0 h1

private theorem nhLUJ4_p1_g2_bp0 (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    0 ≤ 469780202952 * a * b ^ 8 + 5032156701456 * a ^ 2 * b ^ 7 + 23957624043216 * a ^ 3 * b ^ 6 + 66085883824464 * a ^ 4 * b ^ 5 + 115315964125920 * a ^ 5 * b ^ 4 + 130144320237360 * a ^ 6 * b ^ 3 + 92661960942000 * a ^ 7 * b ^ 2 + 38022215685232 * a ^ 8 * b + 6880591933144 * a ^ 9 := by positivity

private theorem nhLUJ4_p1_g2_l0 (x : ℝ) (h0 : 1 ≤ x) (h1 : x ≤ (7 / 3)) :
    0 < 31580280 - 111528252 * x - 4037346342 * x ^ 2 + 7633165815 * x ^ 3 + 26416720512 * x ^ 4 + 24980576661 * x ^ 5 + 12066803118 * x ^ 6 + 3807702594 * x ^ 7 + 886076172 * x ^ 8 + 100973790 * x ^ 9 := by
  linear_combination (1 / 262144 : ℝ) * nhLUJ4_p1_g2_bp0 (3 * x - 3) (7 - 3 * x) (by linarith) (by linarith)

theorem nhLUJ4_p1_g2 (x : ℝ) (h0 : 1 ≤ x) (h1 : x ≤ (7 / 3)) :
    0 < 31580280 - 111528252 * x - 4037346342 * x ^ 2 + 7633165815 * x ^ 3 + 26416720512 * x ^ 4 + 24980576661 * x ^ 5 + 12066803118 * x ^ 6 + 3807702594 * x ^ 7 + 886076172 * x ^ 8 + 100973790 * x ^ 9 := by
  exact nhLUJ4_p1_g2_l0 x h0 h1

private theorem nhLUJ4_p1_g3_bp0 (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    0 ≤ 32106967126848 * a * b ^ 8 + 343561902091776 * a ^ 2 * b ^ 7 + 1636887488943744 * a ^ 3 * b ^ 6 + 4528084137193728 * a ^ 4 * b ^ 5 + 7941437902139904 * a ^ 5 * b ^ 4 + 9028480865553408 * a ^ 6 * b ^ 3 + 6489145007274880 * a ^ 7 * b ^ 2 + 2692906740778240 * a ^ 8 * b + 493565208828096 * a ^ 9 := by positivity

private theorem nhLUJ4_p1_g3_l0 (x : ℝ) (h0 : 1 ≤ x) (h1 : x ≤ (7 / 3)) :
    0 < 54271296 + 95614992 * x - 706576392 * x ^ 2 + 8274951468 * x ^ 3 + 20175879222 * x ^ 4 + 19131789924 * x ^ 5 + 10403973234 * x ^ 6 + 3815763498 * x ^ 7 + 921750192 * x ^ 8 + 100973790 * x ^ 9 := by
  linear_combination (1 / 21233664 : ℝ) * nhLUJ4_p1_g3_bp0 (3 * x - 3) (7 - 3 * x) (by linarith) (by linarith)

theorem nhLUJ4_p1_g3 (x : ℝ) (h0 : 1 ≤ x) (h1 : x ≤ (7 / 3)) :
    0 < 54271296 + 95614992 * x - 706576392 * x ^ 2 + 8274951468 * x ^ 3 + 20175879222 * x ^ 4 + 19131789924 * x ^ 5 + 10403973234 * x ^ 6 + 3815763498 * x ^ 7 + 921750192 * x ^ 8 + 100973790 * x ^ 9 := by
  exact nhLUJ4_p1_g3_l0 x h0 h1

private theorem nhLUJ4_p1_g4_bp0 (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    0 ≤ 92705844338208 * a * b ^ 8 + 990780612105024 * a ^ 2 * b ^ 7 + 4719449964352320 * a ^ 3 * b ^ 6 + 13067303593552704 * a ^ 4 * b ^ 5 + 22966052867676288 * a ^ 5 * b ^ 4 + 26194288884414400 * a ^ 6 * b ^ 3 + 18906219154418880 * a ^ 7 * b ^ 2 + 7884671743367616 * a ^ 8 * b + 1452943788743008 * a ^ 9 := by positivity

private theorem nhLUJ4_p1_g4_l0 (x : ℝ) (h0 : 1 ≤ x) (h1 : x ≤ (7 / 3)) :
    0 < 22691016 + 95267596 * x + 354357414 * x ^ 2 + 3008704385 * x ^ 3 + 6045979940 * x ^ 4 + 5784609108 * x ^ 5 + 3388005694 * x ^ 6 + 1323023085 * x ^ 7 + 318400632 * x ^ 8 + 33657930 * x ^ 9 := by
  linear_combination (1 / 191102976 : ℝ) * nhLUJ4_p1_g4_bp0 (3 * x - 3) (7 - 3 * x) (by linarith) (by linarith)

theorem nhLUJ4_p1_g4 (x : ℝ) (h0 : 1 ≤ x) (h1 : x ≤ (7 / 3)) :
    0 < 22691016 + 95267596 * x + 354357414 * x ^ 2 + 3008704385 * x ^ 3 + 6045979940 * x ^ 4 + 5784609108 * x ^ 5 + 3388005694 * x ^ 6 + 1323023085 * x ^ 7 + 318400632 * x ^ 8 + 33657930 * x ^ 9 := by
  exact nhLUJ4_p1_g4_l0 x h0 h1

theorem nhLUJ4_p1 (x t : ℝ) (hx0 : 1 ≤ x) (hx1 : x ≤ (7 / 3))
    (hs0 : 0 ≤ t) (hs1 : t ≤ (19 / 81)) (hgap : (0 : ℝ) < ((19 / 81)) - (0)) :
    0 < nhLUJ4 t x := by
  have hpos := nh_bern_pos4 (a := (t - (0))) (b := (((19 / 81)) - t)) (by linarith) (by linarith) (hgap.trans_eq (by ring))
    (nhLUJ4_p1_g0 x hx0 hx1) (nhLUJ4_p1_g1 x hx0 hx1) (nhLUJ4_p1_g2 x hx0 hx1) (nhLUJ4_p1_g3 x hx0 hx1) (nhLUJ4_p1_g4 x hx0 hx1)
  have e : 14348907 * (((19 / 81)) - (0)) ^ 4 * (nhLUJ4 t x) = (-1721868840 * x ^ 2 - 286978140 * x ^ 3 + 3874204890 * x ^ 4 + 3974647239 * x ^ 5 + 1434890700 * x ^ 6 + 157837977 * x ^ 7) * (((19 / 81)) - t) ^ 4 + (-107705376 * x - 4679515152 * x ^ 2 + 2110175064 * x ^ 3 + 16183441332 * x ^ 4 + 15615862344 * x ^ 5 + 6486768846 * x ^ 6 + 1472800158 * x ^ 7 + 282726612 * x ^ 8 + 33657930 * x ^ 9) * (t - (0)) * (((19 / 81)) - t) ^ 3 + (31580280 - 111528252 * x - 4037346342 * x ^ 2 + 7633165815 * x ^ 3 + 26416720512 * x ^ 4 + 24980576661 * x ^ 5 + 12066803118 * x ^ 6 + 3807702594 * x ^ 7 + 886076172 * x ^ 8 + 100973790 * x ^ 9) * (t - (0)) ^ 2 * (((19 / 81)) - t) ^ 2 + (54271296 + 95614992 * x - 706576392 * x ^ 2 + 8274951468 * x ^ 3 + 20175879222 * x ^ 4 + 19131789924 * x ^ 5 + 10403973234 * x ^ 6 + 3815763498 * x ^ 7 + 921750192 * x ^ 8 + 100973790 * x ^ 9) * (t - (0)) ^ 3 * (((19 / 81)) - t) + (22691016 + 95267596 * x + 354357414 * x ^ 2 + 3008704385 * x ^ 3 + 6045979940 * x ^ 4 + 5784609108 * x ^ 5 + 3388005694 * x ^ 6 + 1323023085 * x ^ 7 + 318400632 * x ^ 8 + 33657930 * x ^ 9) * (t - (0)) ^ 4 := by unfold nhLUJ4; ring
  have h2 : 0 < 14348907 * (((19 / 81)) - (0)) ^ 4 * (nhLUJ4 t x) := lt_of_lt_of_eq hpos e.symm
  exact pos_of_mul_pos_right h2 (by positivity)

/-- `J_4 > 0` on the unit face. -/
theorem nhLUJ4_dom (t x : ℝ) (hx0 : 1 / 2 < x) (hx1 : x ≤ 7 / 3) (ht0 : 0 ≤ t) (ht1 : t ≤ 1 / 4)
    (hxt : 1 - 2 * t ≤ x) (hT : 3 * (x + 2) ^ 3 * t ≤ -2 * x ^ 3 - x ^ 2 + 10 * x + 12) :
    0 < nhLUJ4 t x := by
  rcases le_total x 1 with hc0 | hc0
  · exact nhLUJ4_p0 x t hx0.le hc0 (by linarith) ht1 (by linarith)
  have hT' := nh_T_anti (xa := 1) (by norm_num) hc0 ht0 hT
  exact nhLUJ4_p1 x t hc0 hx1 ht0 (by norm_num at hT' ⊢; linarith) (by norm_num)

/-- The sign `J_5` on the unit face. -/
noncomputable def nhLUJ5 (t x : ℝ) : ℝ :=
  -16 * x ^ 2 - 16 * x ^ 3 + 56 * x ^ 4 + 84 * x ^ 5 + 39 * x ^ 6 + 5 * x ^ 7 - 16 * t * x + 240 * t * x ^ 2 + 728 * t * x ^ 3 + 808 * t * x ^ 4 + 619 * t * x ^ 5 + 423 * t * x ^ 6 + 202 * t * x ^ 7 + 49 * t * x ^ 8 + 5 * t * x ^ 9 + 96 * t ^ 2 * x - 224 * t ^ 2 * x ^ 2 - 736 * t ^ 2 * x ^ 3 - 288 * t ^ 2 * x ^ 4 + 338 * t ^ 2 * x ^ 5 + 302 * t ^ 2 * x ^ 6 + 85 * t ^ 2 * x ^ 7 + 11 * t ^ 2 * x ^ 8 + 672 * t ^ 3 * x ^ 2 + 1744 * t ^ 3 * x ^ 3 + 1656 * t ^ 3 * x ^ 4 + 732 * t ^ 3 * x ^ 5 + 160 * t ^ 3 * x ^ 6 + 18 * t ^ 3 * x ^ 7 - 192 * t ^ 4 * x ^ 2 - 480 * t ^ 4 * x ^ 3 - 432 * t ^ 4 * x ^ 4 - 168 * t ^ 4 * x ^ 5 - 24 * t ^ 4 * x ^ 6

private theorem nhLUJ5_p0_g0_bp0 (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    0 ≤ 283770 * a * b ^ 9 + 2767455 * a ^ 2 * b ^ 8 + 11908360 * a ^ 3 * b ^ 7 + 29575390 * a ^ 4 * b ^ 6 + 46497732 * a ^ 5 * b ^ 5 + 47641390 * a ^ 6 * b ^ 4 + 31433352 * a ^ 7 * b ^ 3 + 12598963 * a ^ 8 * b ^ 2 + 2654134 * a ^ 9 * b + 194143 * a ^ 10 := by positivity

private theorem nhLUJ5_p0_g0_l0 (x : ℝ) (h0 : (1 / 2) ≤ x) (h1 : x ≤ 1) :
    0 < 512 * x + 2560 * x ^ 2 + 5248 * x ^ 3 + 5184 * x ^ 4 + 1280 * x ^ 5 - 2864 * x ^ 6 - 3840 * x ^ 7 - 2336 * x ^ 8 - 768 * x ^ 9 - 112 * x ^ 10 := by
  linear_combination (1 / 64 : ℝ) * nhLUJ5_p0_g0_bp0 (2 * x - 1) (2 - 2 * x) (by linarith) (by linarith)

theorem nhLUJ5_p0_g0 (x : ℝ) (h0 : (1 / 2) ≤ x) (h1 : x ≤ 1) :
    0 < 512 * x + 2560 * x ^ 2 + 5248 * x ^ 3 + 5184 * x ^ 4 + 1280 * x ^ 5 - 2864 * x ^ 6 - 3840 * x ^ 7 - 2336 * x ^ 8 - 768 * x ^ 9 - 112 * x ^ 10 := by
  exact nhLUJ5_p0_g0_l0 x h0 h1

private theorem nhLUJ5_p0_g1_bp0 (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    0 ≤ 2534355 * a * b ^ 9 + 25253910 * a ^ 2 * b ^ 8 + 111562268 * a ^ 3 * b ^ 7 + 286338440 * a ^ 4 * b ^ 6 + 469668400 * a ^ 5 * b ^ 5 + 509309072 * a ^ 6 * b ^ 4 + 363928960 * a ^ 7 * b ^ 3 + 164468248 * a ^ 8 * b ^ 2 + 42360240 * a ^ 9 * b + 4684536 * a ^ 10 := by positivity

private theorem nhLUJ5_p0_g1_l0 (x : ℝ) (h0 : (1 / 2) ≤ x) (h1 : x ≤ 1) :
    0 < 1408 * x + 8896 * x ^ 2 + 21728 * x ^ 3 + 24944 * x ^ 4 + 10288 * x ^ 5 - 6392 * x ^ 6 - 10092 * x ^ 7 - 5352 * x ^ 8 - 1372 * x ^ 9 - 136 * x ^ 10 := by
  linear_combination (1 / 128 : ℝ) * nhLUJ5_p0_g1_bp0 (2 * x - 1) (2 - 2 * x) (by linarith) (by linarith)

theorem nhLUJ5_p0_g1 (x : ℝ) (h0 : (1 / 2) ≤ x) (h1 : x ≤ 1) :
    0 < 1408 * x + 8896 * x ^ 2 + 21728 * x ^ 3 + 24944 * x ^ 4 + 10288 * x ^ 5 - 6392 * x ^ 6 - 10092 * x ^ 7 - 5352 * x ^ 8 - 1372 * x ^ 9 - 136 * x ^ 10 := by
  exact nhLUJ5_p0_g1_l0 x h0 h1

private theorem nhLUJ5_p0_g2_bp0 (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    0 ≤ 4197825 * a * b ^ 9 + 42611538 * a ^ 2 * b ^ 8 + 192360316 * a ^ 3 * b ^ 7 + 506461184 * a ^ 4 * b ^ 6 + 856291616 * a ^ 5 * b ^ 5 + 963106760 * a ^ 6 * b ^ 4 + 719706016 * a ^ 7 * b ^ 3 + 344034020 * a ^ 8 * b ^ 2 + 95275144 * a ^ 9 * b + 11617396 * a ^ 10 := by positivity

private theorem nhLUJ5_p0_g2_l0 (x : ℝ) (h0 : (1 / 2) ≤ x) (h1 : x ≤ 1) :
    0 < 1344 * x + 11552 * x ^ 2 + 31952 * x ^ 3 + 42040 * x ^ 4 + 26888 * x ^ 5 + 3000 * x ^ 6 - 7756 * x ^ 7 - 5568 * x ^ 8 - 1556 * x ^ 9 - 152 * x ^ 10 := by
  linear_combination (1 / 128 : ℝ) * nhLUJ5_p0_g2_bp0 (2 * x - 1) (2 - 2 * x) (by linarith) (by linarith)

theorem nhLUJ5_p0_g2 (x : ℝ) (h0 : (1 / 2) ≤ x) (h1 : x ≤ 1) :
    0 < 1344 * x + 11552 * x ^ 2 + 31952 * x ^ 3 + 42040 * x ^ 4 + 26888 * x ^ 5 + 3000 * x ^ 6 - 7756 * x ^ 7 - 5568 * x ^ 8 - 1556 * x ^ 9 - 152 * x ^ 10 := by
  exact nhLUJ5_p0_g2_l0 x h0 h1

private theorem nhLUJ5_p0_g3_bp0 (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    0 ≤ 3062745 * a * b ^ 9 + 31600986 * a ^ 2 * b ^ 8 + 145324669 * a ^ 3 * b ^ 7 + 390758694 * a ^ 4 * b ^ 6 + 676655164 * a ^ 5 * b ^ 5 + 782077240 * a ^ 6 * b ^ 4 + 602937840 * a ^ 7 * b ^ 3 + 298767672 * a ^ 8 * b ^ 2 + 86277360 * a ^ 9 * b + 11053176 * a ^ 10 := by positivity

private theorem nhLUJ5_p0_g3_l0 (x : ℝ) (h0 : (1 / 2) ≤ x) (h1 : x ≤ 1) :
    0 < 512 * x + 6512 * x ^ 2 + 19992 * x ^ 3 + 30884 * x ^ 4 + 26802 * x ^ 5 + 11436 * x ^ 6 + 163 * x ^ 7 - 1874 * x ^ 8 - 672 * x ^ 9 - 80 * x ^ 10 := by
  linear_combination (1 / 128 : ℝ) * nhLUJ5_p0_g3_bp0 (2 * x - 1) (2 - 2 * x) (by linarith) (by linarith)

theorem nhLUJ5_p0_g3 (x : ℝ) (h0 : (1 / 2) ≤ x) (h1 : x ≤ 1) :
    0 < 512 * x + 6512 * x ^ 2 + 19992 * x ^ 3 + 30884 * x ^ 4 + 26802 * x ^ 5 + 11436 * x ^ 6 + 163 * x ^ 7 - 1874 * x ^ 8 - 672 * x ^ 9 - 80 * x ^ 10 := by
  exact nhLUJ5_p0_g3_l0 x h0 h1

private theorem nhLUJ5_p0_g4_bp0 (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    0 ≤ 831735 * a * b ^ 8 + 7876713 * a ^ 2 * b ^ 7 + 32833188 * a ^ 3 * b ^ 6 + 78649732 * a ^ 4 * b ^ 5 + 118366652 * a ^ 5 * b ^ 4 + 114556200 * a ^ 6 * b ^ 3 + 69594552 * a ^ 7 * b ^ 2 + 24254766 * a ^ 8 * b + 3711294 * a ^ 9 := by positivity

private theorem nhLUJ5_p0_g4_l0 (x : ℝ) (h0 : (1 / 2) ≤ x) (h1 : x ≤ 1) :
    0 < 64 * x + 1272 * x ^ 2 + 4652 * x ^ 3 + 8454 * x ^ 4 + 8661 * x ^ 5 + 5313 * x ^ 6 + 1955 * x ^ 7 + 414 * x ^ 8 + 40 * x ^ 9 := by
  linear_combination (1 / 128 : ℝ) * nhLUJ5_p0_g4_bp0 (2 * x - 1) (2 - 2 * x) (by linarith) (by linarith)

theorem nhLUJ5_p0_g4 (x : ℝ) (h0 : (1 / 2) ≤ x) (h1 : x ≤ 1) :
    0 < 64 * x + 1272 * x ^ 2 + 4652 * x ^ 3 + 8454 * x ^ 4 + 8661 * x ^ 5 + 5313 * x ^ 6 + 1955 * x ^ 7 + 414 * x ^ 8 + 40 * x ^ 9 := by
  exact nhLUJ5_p0_g4_l0 x h0 h1

theorem nhLUJ5_p0 (x t : ℝ) (hx0 : (1 / 2) ≤ x) (hx1 : x ≤ 1)
    (hs0 : (1 / 2) - (1 / 2) * x ≤ t) (hs1 : t ≤ (1 / 4)) (hgap : (0 : ℝ) < ((1 / 4)) - ((1 / 2) - (1 / 2) * x)) :
    0 < nhLUJ5 t x := by
  have hpos := nh_bern_pos4 (a := (t - ((1 / 2) - (1 / 2) * x))) (b := (((1 / 4)) - t)) (by linarith) (by linarith) (hgap.trans_eq (by ring))
    (nhLUJ5_p0_g0 x hx0 hx1) (nhLUJ5_p0_g1 x hx0 hx1) (nhLUJ5_p0_g2 x hx0 hx1) (nhLUJ5_p0_g3 x hx0 hx1) (nhLUJ5_p0_g4 x hx0 hx1)
  have e : 32 * (((1 / 4)) - ((1 / 2) - (1 / 2) * x)) ^ 4 * (nhLUJ5 t x) = (512 * x + 2560 * x ^ 2 + 5248 * x ^ 3 + 5184 * x ^ 4 + 1280 * x ^ 5 - 2864 * x ^ 6 - 3840 * x ^ 7 - 2336 * x ^ 8 - 768 * x ^ 9 - 112 * x ^ 10) * (((1 / 4)) - t) ^ 4 + (1408 * x + 8896 * x ^ 2 + 21728 * x ^ 3 + 24944 * x ^ 4 + 10288 * x ^ 5 - 6392 * x ^ 6 - 10092 * x ^ 7 - 5352 * x ^ 8 - 1372 * x ^ 9 - 136 * x ^ 10) * (t - ((1 / 2) - (1 / 2) * x)) * (((1 / 4)) - t) ^ 3 + (1344 * x + 11552 * x ^ 2 + 31952 * x ^ 3 + 42040 * x ^ 4 + 26888 * x ^ 5 + 3000 * x ^ 6 - 7756 * x ^ 7 - 5568 * x ^ 8 - 1556 * x ^ 9 - 152 * x ^ 10) * (t - ((1 / 2) - (1 / 2) * x)) ^ 2 * (((1 / 4)) - t) ^ 2 + (512 * x + 6512 * x ^ 2 + 19992 * x ^ 3 + 30884 * x ^ 4 + 26802 * x ^ 5 + 11436 * x ^ 6 + 163 * x ^ 7 - 1874 * x ^ 8 - 672 * x ^ 9 - 80 * x ^ 10) * (t - ((1 / 2) - (1 / 2) * x)) ^ 3 * (((1 / 4)) - t) + (64 * x + 1272 * x ^ 2 + 4652 * x ^ 3 + 8454 * x ^ 4 + 8661 * x ^ 5 + 5313 * x ^ 6 + 1955 * x ^ 7 + 414 * x ^ 8 + 40 * x ^ 9) * (t - ((1 / 2) - (1 / 2) * x)) ^ 4 := by unfold nhLUJ5; ring
  have h2 : 0 < 32 * (((1 / 4)) - ((1 / 2) - (1 / 2) * x)) ^ 4 * (nhLUJ5 t x) := lt_of_lt_of_eq hpos e.symm
  exact pos_of_mul_pos_right h2 (by positivity)

private theorem nhLUJ5_p1_g0_bp0 (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    0 ≤ 15936852708 * a * b ^ 6 + 141588636984 * a ^ 2 * b ^ 5 + 537016878972 * a ^ 3 * b ^ 4 + 1106970345360 * a ^ 4 * b ^ 3 + 1301220533916 * a ^ 5 * b ^ 2 + 823241475000 * a ^ 6 * b + 218163668868 * a ^ 7 := by positivity

private theorem nhLUJ5_p1_g0_l0 (x : ℝ) (h0 : 1 ≤ x) (h1 : x ≤ (7 / 3)) :
    0 < -229582512 * x ^ 2 - 229582512 * x ^ 3 + 803538792 * x ^ 4 + 1205308188 * x ^ 5 + 559607373 * x ^ 6 + 71744535 * x ^ 7 := by
  linear_combination (1 / 16384 : ℝ) * nhLUJ5_p1_g0_bp0 (3 * x - 3) (7 - 3 * x) (by linarith) (by linarith)

theorem nhLUJ5_p1_g0 (x : ℝ) (h0 : 1 ≤ x) (h1 : x ≤ (7 / 3)) :
    0 < -229582512 * x ^ 2 - 229582512 * x ^ 3 + 803538792 * x ^ 4 + 1205308188 * x ^ 5 + 559607373 * x ^ 6 + 71744535 * x ^ 7 := by
  exact nhLUJ5_p1_g0_l0 x h0 h1

private theorem nhLUJ5_p1_g1_bp0 (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    0 ≤ 123721354368 * a * b ^ 8 + 1326827880720 * a ^ 2 * b ^ 7 + 6326225689968 * a ^ 3 * b ^ 6 + 17473982998608 * a ^ 4 * b ^ 5 + 30510117459504 * a ^ 5 * b ^ 4 + 34407066515760 * a ^ 6 * b ^ 3 + 24427793299536 * a ^ 7 * b ^ 2 + 9967431983472 * a ^ 8 * b + 1787675708304 * a ^ 9 := by positivity

private theorem nhLUJ5_p1_g1_l0 (x : ℝ) (h0 : 1 ≤ x) (h1 : x ≤ (7 / 3)) :
    0 < -53852688 * x - 110539728 * x ^ 2 + 1531967256 * x ^ 3 + 5933715912 * x ^ 4 + 6904658619 * x ^ 5 + 3662159931 * x ^ 6 + 966868326 * x ^ 7 + 164923857 * x ^ 8 + 16828965 * x ^ 9 := by
  linear_combination (1 / 262144 : ℝ) * nhLUJ5_p1_g1_bp0 (3 * x - 3) (7 - 3 * x) (by linarith) (by linarith)

theorem nhLUJ5_p1_g1 (x : ℝ) (h0 : 1 ≤ x) (h1 : x ≤ (7 / 3)) :
    0 < -53852688 * x - 110539728 * x ^ 2 + 1531967256 * x ^ 3 + 5933715912 * x ^ 4 + 6904658619 * x ^ 5 + 3662159931 * x ^ 6 + 966868326 * x ^ 7 + 164923857 * x ^ 8 + 16828965 * x ^ 9 := by
  exact nhLUJ5_p1_g1_l0 x h0 h1

private theorem nhLUJ5_p1_g2_bp0 (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    0 ≤ 828122587812 * a * b ^ 8 + 8855681884704 * a ^ 2 * b ^ 7 + 42162167582640 * a ^ 3 * b ^ 6 + 116506617885792 * a ^ 4 * b ^ 5 + 203961855415320 * a ^ 5 * b ^ 4 + 231191677110240 * a ^ 6 * b ^ 3 + 165407842878000 * a ^ 7 * b ^ 2 + 68191902399392 * a ^ 8 * b + 12387908014436 * a ^ 9 := by positivity

private theorem nhLUJ5_p1_g2_l0 (x : ℝ) (h0 : 1 ≤ x) (h1 : x ≤ (7 / 3)) :
    0 < -85765392 * x + 869026320 * x ^ 2 + 5392319688 * x ^ 3 + 12752536968 * x ^ 4 + 13748980095 * x ^ 5 + 7867266669 * x ^ 6 + 2537245863 * x ^ 7 + 503456148 * x ^ 8 + 50486895 * x ^ 9 := by
  linear_combination (1 / 786432 : ℝ) * nhLUJ5_p1_g2_bp0 (3 * x - 3) (7 - 3 * x) (by linarith) (by linarith)

theorem nhLUJ5_p1_g2 (x : ℝ) (h0 : 1 ≤ x) (h1 : x ≤ (7 / 3)) :
    0 < -85765392 * x + 869026320 * x ^ 2 + 5392319688 * x ^ 3 + 12752536968 * x ^ 4 + 13748980095 * x ^ 5 + 7867266669 * x ^ 6 + 2537245863 * x ^ 7 + 503456148 * x ^ 8 + 50486895 * x ^ 9 := by
  exact nhLUJ5_p1_g2_l0 x h0 h1

private theorem nhLUJ5_p1_g3_bp0 (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    0 ≤ 6725602018080 * a * b ^ 8 + 71850878685648 * a ^ 2 * b ^ 7 + 341992267890480 * a ^ 3 * b ^ 6 + 945628500274704 * a ^ 4 * b ^ 5 + 1658247307014960 * a ^ 5 * b ^ 4 + 1884902490898288 * a ^ 6 * b ^ 3 + 1353871014806160 * a ^ 7 * b ^ 2 + 560944223110320 * a ^ 8 * b + 102508056022000 * a ^ 9 := by positivity

private theorem nhLUJ5_p1_g3_l0 (x : ℝ) (h0 : 1 ≤ x) (h1 : x ≤ (7 / 3)) :
    0 < -9972720 * x + 1275791472 * x ^ 2 + 5593384152 * x ^ 3 + 11224760976 * x ^ 4 + 11740778361 * x ^ 5 + 7016113917 * x ^ 6 + 2464198362 * x ^ 7 + 512140725 * x ^ 8 + 50486895 * x ^ 9 := by
  linear_combination (1 / 7077888 : ℝ) * nhLUJ5_p1_g3_bp0 (3 * x - 3) (7 - 3 * x) (by linarith) (by linarith)

theorem nhLUJ5_p1_g3 (x : ℝ) (h0 : 1 ≤ x) (h1 : x ≤ (7 / 3)) :
    0 < -9972720 * x + 1275791472 * x ^ 2 + 5593384152 * x ^ 3 + 11224760976 * x ^ 4 + 11740778361 * x ^ 5 + 7016113917 * x ^ 6 + 2464198362 * x ^ 7 + 512140725 * x ^ 8 + 50486895 * x ^ 9 := by
  exact nhLUJ5_p1_g3_l0 x h0 h1

private theorem nhLUJ5_p1_g4_bp0 (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    0 ≤ 58740839277840 * a * b ^ 8 + 626961624426144 * a ^ 2 * b ^ 7 + 2982504281395104 * a ^ 3 * b ^ 6 + 8245962892367136 * a ^ 4 * b ^ 5 + 14466257733279936 * a ^ 5 * b ^ 4 + 16459806861720544 * a ^ 6 * b ^ 3 + 11840772911412576 * a ^ 7 * b ^ 2 + 4915929821644896 * a ^ 8 * b + 900548827837744 * a ^ 9 := by positivity

private theorem nhLUJ5_p1_g4_l0 (x : ℝ) (h0 : 1 ≤ x) (h1 : x ≤ (7 / 3)) :
    0 < 21939984 * x + 517467392 * x ^ 2 + 1941762872 * x ^ 3 + 3583634904 * x ^ 4 + 3683850721 * x ^ 5 + 2250357238 * x ^ 6 + 822076290 * x ^ 7 + 173608434 * x ^ 8 + 16828965 * x ^ 9 := by
  linear_combination (1 / 191102976 : ℝ) * nhLUJ5_p1_g4_bp0 (3 * x - 3) (7 - 3 * x) (by linarith) (by linarith)

theorem nhLUJ5_p1_g4 (x : ℝ) (h0 : 1 ≤ x) (h1 : x ≤ (7 / 3)) :
    0 < 21939984 * x + 517467392 * x ^ 2 + 1941762872 * x ^ 3 + 3583634904 * x ^ 4 + 3683850721 * x ^ 5 + 2250357238 * x ^ 6 + 822076290 * x ^ 7 + 173608434 * x ^ 8 + 16828965 * x ^ 9 := by
  exact nhLUJ5_p1_g4_l0 x h0 h1

theorem nhLUJ5_p1 (x t : ℝ) (hx0 : 1 ≤ x) (hx1 : x ≤ (7 / 3))
    (hs0 : 0 ≤ t) (hs1 : t ≤ (19 / 81)) (hgap : (0 : ℝ) < ((19 / 81)) - (0)) :
    0 < nhLUJ5 t x := by
  have hpos := nh_bern_pos4 (a := (t - (0))) (b := (((19 / 81)) - t)) (by linarith) (by linarith) (hgap.trans_eq (by ring))
    (nhLUJ5_p1_g0 x hx0 hx1) (nhLUJ5_p1_g1 x hx0 hx1) (nhLUJ5_p1_g2 x hx0 hx1) (nhLUJ5_p1_g3 x hx0 hx1) (nhLUJ5_p1_g4 x hx0 hx1)
  have e : 14348907 * (((19 / 81)) - (0)) ^ 4 * (nhLUJ5 t x) = (-229582512 * x ^ 2 - 229582512 * x ^ 3 + 803538792 * x ^ 4 + 1205308188 * x ^ 5 + 559607373 * x ^ 6 + 71744535 * x ^ 7) * (((19 / 81)) - t) ^ 4 + (-53852688 * x - 110539728 * x ^ 2 + 1531967256 * x ^ 3 + 5933715912 * x ^ 4 + 6904658619 * x ^ 5 + 3662159931 * x ^ 6 + 966868326 * x ^ 7 + 164923857 * x ^ 8 + 16828965 * x ^ 9) * (t - (0)) * (((19 / 81)) - t) ^ 3 + (-85765392 * x + 869026320 * x ^ 2 + 5392319688 * x ^ 3 + 12752536968 * x ^ 4 + 13748980095 * x ^ 5 + 7867266669 * x ^ 6 + 2537245863 * x ^ 7 + 503456148 * x ^ 8 + 50486895 * x ^ 9) * (t - (0)) ^ 2 * (((19 / 81)) - t) ^ 2 + (-9972720 * x + 1275791472 * x ^ 2 + 5593384152 * x ^ 3 + 11224760976 * x ^ 4 + 11740778361 * x ^ 5 + 7016113917 * x ^ 6 + 2464198362 * x ^ 7 + 512140725 * x ^ 8 + 50486895 * x ^ 9) * (t - (0)) ^ 3 * (((19 / 81)) - t) + (21939984 * x + 517467392 * x ^ 2 + 1941762872 * x ^ 3 + 3583634904 * x ^ 4 + 3683850721 * x ^ 5 + 2250357238 * x ^ 6 + 822076290 * x ^ 7 + 173608434 * x ^ 8 + 16828965 * x ^ 9) * (t - (0)) ^ 4 := by unfold nhLUJ5; ring
  have h2 : 0 < 14348907 * (((19 / 81)) - (0)) ^ 4 * (nhLUJ5 t x) := lt_of_lt_of_eq hpos e.symm
  exact pos_of_mul_pos_right h2 (by positivity)

/-- `J_5 > 0` on the unit face. -/
theorem nhLUJ5_dom (t x : ℝ) (hx0 : 1 / 2 < x) (hx1 : x ≤ 7 / 3) (ht0 : 0 ≤ t) (ht1 : t ≤ 1 / 4)
    (hxt : 1 - 2 * t ≤ x) (hT : 3 * (x + 2) ^ 3 * t ≤ -2 * x ^ 3 - x ^ 2 + 10 * x + 12) :
    0 < nhLUJ5 t x := by
  rcases le_total x 1 with hc0 | hc0
  · exact nhLUJ5_p0 x t hx0.le hc0 (by linarith) ht1 (by linarith)
  have hT' := nh_T_anti (xa := 1) (by norm_num) hc0 ht0 hT
  exact nhLUJ5_p1 x t hc0 hx1 ht0 (by norm_num at hT' ⊢; linarith) (by norm_num)

/-- The sign `J_0` on the high-ratio face. -/
noncomputable def nhLHJ0 (t x : ℝ) : ℝ :=
  32 * x ^ 3 + 40 * x ^ 4 + 14 * x ^ 5 - 96 * t * x ^ 2 - 256 * t * x ^ 3 - 272 * t * x ^ 4 - 160 * t * x ^ 5 - 60 * t * x ^ 6 - 12 * t * x ^ 7 + 336 * t ^ 2 * x ^ 2 + 824 * t ^ 2 * x ^ 3 + 868 * t ^ 2 * x ^ 4 + 500 * t ^ 2 * x ^ 5 + 162 * t ^ 2 * x ^ 6 + 24 * t ^ 2 * x ^ 7 - 240 * t ^ 3 * x ^ 2 - 600 * t ^ 3 * x ^ 3 - 636 * t ^ 3 * x ^ 4 - 354 * t ^ 3 * x ^ 5 - 102 * t ^ 3 * x ^ 6 - 12 * t ^ 3 * x ^ 7

private theorem nhLHJ0_p0_g0_bp0 (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    0 ≤ 961875 * a * b ^ 6 + 7395750 * a ^ 2 * b ^ 5 + 23260500 * a ^ 3 * b ^ 4 + 38065500 * a ^ 4 * b ^ 3 + 33934500 * a ^ 5 * b ^ 2 + 15457500 * a ^ 6 * b + 2758500 * a ^ 7 := by positivity

private theorem nhLHJ0_p0_g0_l0 (x : ℝ) (h0 : (1 / 2) ≤ x) (h1 : x ≤ 1) :
    0 < -27000 * x ^ 2 + 40500 * x ^ 3 + 65250 * x ^ 4 - 1125 * x ^ 5 - 25875 * x ^ 6 - 6750 * x ^ 7 := by
  linear_combination (1 / 64 : ℝ) * nhLHJ0_p0_g0_bp0 (2 * x - 1) (2 - 2 * x) (by linarith) (by linarith)

theorem nhLHJ0_p0_g0 (x : ℝ) (h0 : (1 / 2) ≤ x) (h1 : x ≤ 1) :
    0 < -27000 * x ^ 2 + 40500 * x ^ 3 + 65250 * x ^ 4 - 1125 * x ^ 5 - 25875 * x ^ 6 - 6750 * x ^ 7 := by
  exact nhLHJ0_p0_g0_l0 x h0 h1

private theorem nhLHJ0_p0_g1_bp0 (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    0 ≤ 4018275 * a * b ^ 6 + 30174750 * a ^ 2 * b ^ 5 + 93330300 * a ^ 3 * b ^ 4 + 151328100 * a ^ 4 * b ^ 3 + 134804700 * a ^ 5 * b ^ 2 + 62031300 * a ^ 6 * b + 11370300 * a ^ 7 := by positivity

private theorem nhLHJ0_p0_g1_l0 (x : ℝ) (h0 : (1 / 2) ≤ x) (h1 : x ≤ 1) :
    0 < -70200 * x ^ 2 + 138900 * x ^ 3 + 212850 * x ^ 4 + 6075 * x ^ 5 - 76875 * x ^ 6 - 21150 * x ^ 7 := by
  linear_combination (1 / 64 : ℝ) * nhLHJ0_p0_g1_bp0 (2 * x - 1) (2 - 2 * x) (by linarith) (by linarith)

theorem nhLHJ0_p0_g1 (x : ℝ) (h0 : (1 / 2) ≤ x) (h1 : x ≤ 1) :
    0 < -70200 * x ^ 2 + 138900 * x ^ 3 + 212850 * x ^ 4 + 6075 * x ^ 5 - 76875 * x ^ 6 - 21150 * x ^ 7 := by
  exact nhLHJ0_p0_g1_l0 x h0 h1

private theorem nhLHJ0_p0_g2_bp0 (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    0 ≤ 6076305 * a * b ^ 6 + 44793970 * a ^ 2 * b ^ 5 + 136793420 * a ^ 3 * b ^ 4 + 220525540 * a ^ 4 * b ^ 3 + 196999580 * a ^ 5 * b ^ 2 + 91936420 * a ^ 6 * b + 17375900 * a ^ 7 := by positivity

private theorem nhLHJ0_p0_g2_l0 (x : ℝ) (h0 : (1 / 2) ≤ x) (h1 : x ≤ 1) :
    0 < -53160 * x ^ 2 + 171260 * x ^ 3 + 245590 * x ^ 4 + 24905 * x ^ 5 - 72705 * x ^ 6 - 21450 * x ^ 7 := by
  linear_combination (1 / 64 : ℝ) * nhLHJ0_p0_g2_bp0 (2 * x - 1) (2 - 2 * x) (by linarith) (by linarith)

theorem nhLHJ0_p0_g2 (x : ℝ) (h0 : (1 / 2) ≤ x) (h1 : x ≤ 1) :
    0 < -53160 * x ^ 2 + 171260 * x ^ 3 + 245590 * x ^ 4 + 24905 * x ^ 5 - 72705 * x ^ 6 - 21450 * x ^ 7 := by
  exact nhLHJ0_p0_g2_l0 x h0 h1

private theorem nhLHJ0_p0_g3_bp0 (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    0 ≤ 2874105 * a * b ^ 6 + 20971210 * a ^ 2 * b ^ 5 + 63594596 * a ^ 3 * b ^ 4 + 102237148 * a ^ 4 * b ^ 3 + 91569764 * a ^ 5 * b ^ 2 + 43148092 * a ^ 6 * b + 8314436 * a ^ 7 := by positivity

private theorem nhLHJ0_p0_g3_l0 (x : ℝ) (h0 : (1 / 2) ≤ x) (h1 : x ≤ 1) :
    0 < -10920 * x ^ 2 + 70460 * x ^ 3 + 95446 * x ^ 4 + 16289 * x ^ 5 - 22113 * x ^ 6 - 7098 * x ^ 7 := by
  linear_combination (1 / 64 : ℝ) * nhLHJ0_p0_g3_bp0 (2 * x - 1) (2 - 2 * x) (by linarith) (by linarith)

theorem nhLHJ0_p0_g3 (x : ℝ) (h0 : (1 / 2) ≤ x) (h1 : x ≤ 1) :
    0 < -10920 * x ^ 2 + 70460 * x ^ 3 + 95446 * x ^ 4 + 16289 * x ^ 5 - 22113 * x ^ 6 - 7098 * x ^ 7 := by
  exact nhLHJ0_p0_g3_l0 x h0 h1

theorem nhLHJ0_p0 (x t : ℝ) (hx0 : (1 / 2) ≤ x) (hx1 : x ≤ 1)
    (hs0 : (1 / 4) ≤ t) (hs1 : t ≤ (7 / 20)) (hgap : (0 : ℝ) < ((7 / 20)) - ((1 / 4))) :
    0 < nhLHJ0 t x := by
  have hpos := nh_bern_pos3 (a := (t - ((1 / 4)))) (b := (((7 / 20)) - t)) (by linarith) (by linarith) (hgap.trans_eq (by ring))
    (nhLHJ0_p0_g0 x hx0 hx1) (nhLHJ0_p0_g1 x hx0 hx1) (nhLHJ0_p0_g2 x hx0 hx1) (nhLHJ0_p0_g3 x hx0 hx1)
  have e : 4000 * (((7 / 20)) - ((1 / 4))) ^ 3 * (nhLHJ0 t x) = (-27000 * x ^ 2 + 40500 * x ^ 3 + 65250 * x ^ 4 - 1125 * x ^ 5 - 25875 * x ^ 6 - 6750 * x ^ 7) * (((7 / 20)) - t) ^ 3 + (-70200 * x ^ 2 + 138900 * x ^ 3 + 212850 * x ^ 4 + 6075 * x ^ 5 - 76875 * x ^ 6 - 21150 * x ^ 7) * (t - ((1 / 4))) * (((7 / 20)) - t) ^ 2 + (-53160 * x ^ 2 + 171260 * x ^ 3 + 245590 * x ^ 4 + 24905 * x ^ 5 - 72705 * x ^ 6 - 21450 * x ^ 7) * (t - ((1 / 4))) ^ 2 * (((7 / 20)) - t) + (-10920 * x ^ 2 + 70460 * x ^ 3 + 95446 * x ^ 4 + 16289 * x ^ 5 - 22113 * x ^ 6 - 7098 * x ^ 7) * (t - ((1 / 4))) ^ 3 := by unfold nhLHJ0; ring
  have h2 : 0 < 4000 * (((7 / 20)) - ((1 / 4))) ^ 3 * (nhLHJ0 t x) := lt_of_lt_of_eq hpos e.symm
  exact pos_of_mul_pos_right h2 (by positivity)

/-- `J_0 > 0` on the high-ratio face. -/
theorem nhLHJ0_dom (t x : ℝ) (ht0 : 1 / 4 ≤ t) (ht1 : t ≤ 7 / 20) (hx0 : 1 / 2 ≤ x) (hx1 : x ≤ 1) :
    0 < nhLHJ0 t x :=
  nhLHJ0_p0 x t hx0 hx1 ht0 ht1 (by norm_num)

/-- The sign `J_1` on the high-ratio face. -/
noncomputable def nhLHJ1 (t x : ℝ) : ℝ :=
  -24 * x ^ 2 + 164 * x ^ 3 + 270 * x ^ 4 + 132 * x ^ 5 + 17 * x ^ 6 + 24 * t * x - 444 * t * x ^ 2 - 1574 * t * x ^ 3 - 2217 * t * x ^ 4 - 1706 * t * x ^ 5 - 746 * t * x ^ 6 - 159 * t * x ^ 7 - 8 * t * x ^ 8 - 120 * t ^ 2 * x + 1764 * t ^ 2 * x ^ 2 + 5394 * t ^ 2 * x ^ 3 + 6939 * t ^ 2 * x ^ 4 + 4988 * t ^ 2 * x ^ 5 + 2064 * t ^ 2 * x ^ 6 + 438 * t ^ 2 * x ^ 7 + 32 * t ^ 2 * x ^ 8 + 240 * t ^ 3 * x - 720 * t ^ 3 * x ^ 2 - 3048 * t ^ 3 * x ^ 3 - 4200 * t ^ 3 * x ^ 4 - 3045 * t ^ 3 * x ^ 5 - 1245 * t ^ 3 * x ^ 6 - 270 * t ^ 3 * x ^ 7 - 24 * t ^ 3 * x ^ 8

private theorem nhLHJ1_p0_g0_bp0 (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    0 ≤ 18000 * b ^ 8 + 7977375 * a * b ^ 7 + 64879875 * a ^ 2 * b ^ 6 + 220520250 * a ^ 3 * b ^ 5 + 398037000 * a ^ 4 * b ^ 4 + 401544000 * a ^ 5 * b ^ 3 + 214470000 * a ^ 6 * b ^ 2 + 47364000 * a ^ 7 * b := by positivity

private theorem nhLHJ1_p0_g0_l0 (x : ℝ) (h0 : (1 / 2) ≤ x) (h1 : x ≤ 1) :
    0 < 18000 * x - 288000 * x ^ 2 + 480000 * x ^ 3 + 670500 * x ^ 4 - 242625 * x ^ 5 - 479625 * x ^ 6 - 132750 * x ^ 7 - 3000 * x ^ 8 := by
  linear_combination (1 / 64 : ℝ) * nhLHJ1_p0_g0_bp0 (2 * x - 1) (2 - 2 * x) (by linarith) (by linarith)

theorem nhLHJ1_p0_g0 (x : ℝ) (h0 : (1 / 2) ≤ x) (h1 : x ≤ 1) :
    0 < 18000 * x - 288000 * x ^ 2 + 480000 * x ^ 3 + 670500 * x ^ 4 - 242625 * x ^ 5 - 479625 * x ^ 6 - 132750 * x ^ 7 - 3000 * x ^ 8 := by
  exact nhLHJ1_p0_g0_l0 x h0 h1

private theorem nhLHJ1_p0_g1_bp0 (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    0 ≤ 50048775 * a * b ^ 7 + 406565475 * a ^ 2 * b ^ 6 + 1395608250 * a ^ 3 * b ^ 5 + 2607359000 * a ^ 4 * b ^ 4 + 2839276800 * a ^ 5 * b ^ 3 + 1779493200 * a ^ 6 * b ^ 2 + 581394400 * a ^ 7 * b + 72909000 * a ^ 8 := by positivity

private theorem nhLHJ1_p0_g1_l0 (x : ℝ) (h0 : (1 / 2) ≤ x) (h1 : x ≤ 1) :
    0 < 61200 * x - 621600 * x ^ 2 + 1881200 * x ^ 3 + 2383500 * x ^ 4 - 554225 * x ^ 5 - 1396825 * x ^ 6 - 390750 * x ^ 7 - 6200 * x ^ 8 := by
  linear_combination (1 / 64 : ℝ) * nhLHJ1_p0_g1_bp0 (2 * x - 1) (2 - 2 * x) (by linarith) (by linarith)

theorem nhLHJ1_p0_g1 (x : ℝ) (h0 : (1 / 2) ≤ x) (h1 : x ≤ 1) :
    0 < 61200 * x - 621600 * x ^ 2 + 1881200 * x ^ 3 + 2383500 * x ^ 4 - 554225 * x ^ 5 - 1396825 * x ^ 6 - 390750 * x ^ 7 - 6200 * x ^ 8 := by
  exact nhLHJ1_p0_g1_l0 x h0 h1

private theorem nhLHJ1_p0_g2_bp0 (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    0 ≤ 93475845 * a * b ^ 7 + 758849985 * a ^ 2 * b ^ 6 + 2624632510 * a ^ 3 * b ^ 5 + 4997277080 * a ^ 4 * b ^ 4 + 5636355520 * a ^ 5 * b ^ 3 + 3749416400 * a ^ 6 * b ^ 2 + 1354294240 * a ^ 7 * b + 203214080 * a ^ 8 := by positivity

private theorem nhLHJ1_p0_g2_l0 (x : ℝ) (h0 : (1 / 2) ≤ x) (h1 : x ≤ 1) :
    0 < 73200 * x - 281280 * x ^ 2 + 2571040 * x ^ 3 + 3058620 * x ^ 4 - 164235 * x ^ 5 - 1264355 * x ^ 6 - 364410 * x ^ 7 - 2280 * x ^ 8 := by
  linear_combination (1 / 64 : ℝ) * nhLHJ1_p0_g2_bp0 (2 * x - 1) (2 - 2 * x) (by linarith) (by linarith)

theorem nhLHJ1_p0_g2 (x : ℝ) (h0 : (1 / 2) ≤ x) (h1 : x ≤ 1) :
    0 < 73200 * x - 281280 * x ^ 2 + 2571040 * x ^ 3 + 3058620 * x ^ 4 - 164235 * x ^ 5 - 1264355 * x ^ 6 - 364410 * x ^ 7 - 2280 * x ^ 8 := by
  exact nhLHJ1_p0_g2_l0 x h0 h1

private theorem nhLHJ1_p0_g3_bp0 (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    0 ≤ 49703445 * a * b ^ 7 + 403616985 * a ^ 2 * b ^ 6 + 1401513550 * a ^ 3 * b ^ 5 + 2692167720 * a ^ 4 * b ^ 4 + 3083228032 * a ^ 5 * b ^ 3 + 2100598832 * a ^ 6 * b ^ 2 + 786341664 * a ^ 7 * b + 124403336 * a ^ 8 := by positivity

private theorem nhLHJ1_p0_g3_l0 (x : ℝ) (h0 : (1 / 2) ≤ x) (h1 : x ≤ 1) :
    0 < 31920 * x + 46560 * x ^ 2 + 1145456 * x ^ 3 + 1312020 * x ^ 4 + 123005 * x ^ 5 - 357115 * x ^ 6 - 108570 * x ^ 7 + 728 * x ^ 8 := by
  linear_combination (1 / 64 : ℝ) * nhLHJ1_p0_g3_bp0 (2 * x - 1) (2 - 2 * x) (by linarith) (by linarith)

theorem nhLHJ1_p0_g3 (x : ℝ) (h0 : (1 / 2) ≤ x) (h1 : x ≤ 1) :
    0 < 31920 * x + 46560 * x ^ 2 + 1145456 * x ^ 3 + 1312020 * x ^ 4 + 123005 * x ^ 5 - 357115 * x ^ 6 - 108570 * x ^ 7 + 728 * x ^ 8 := by
  exact nhLHJ1_p0_g3_l0 x h0 h1

theorem nhLHJ1_p0 (x t : ℝ) (hx0 : (1 / 2) ≤ x) (hx1 : x ≤ 1)
    (hs0 : (1 / 4) ≤ t) (hs1 : t ≤ (7 / 20)) (hgap : (0 : ℝ) < ((7 / 20)) - ((1 / 4))) :
    0 < nhLHJ1 t x := by
  have hpos := nh_bern_pos3 (a := (t - ((1 / 4)))) (b := (((7 / 20)) - t)) (by linarith) (by linarith) (hgap.trans_eq (by ring))
    (nhLHJ1_p0_g0 x hx0 hx1) (nhLHJ1_p0_g1 x hx0 hx1) (nhLHJ1_p0_g2 x hx0 hx1) (nhLHJ1_p0_g3 x hx0 hx1)
  have e : 8000 * (((7 / 20)) - ((1 / 4))) ^ 3 * (nhLHJ1 t x) = (18000 * x - 288000 * x ^ 2 + 480000 * x ^ 3 + 670500 * x ^ 4 - 242625 * x ^ 5 - 479625 * x ^ 6 - 132750 * x ^ 7 - 3000 * x ^ 8) * (((7 / 20)) - t) ^ 3 + (61200 * x - 621600 * x ^ 2 + 1881200 * x ^ 3 + 2383500 * x ^ 4 - 554225 * x ^ 5 - 1396825 * x ^ 6 - 390750 * x ^ 7 - 6200 * x ^ 8) * (t - ((1 / 4))) * (((7 / 20)) - t) ^ 2 + (73200 * x - 281280 * x ^ 2 + 2571040 * x ^ 3 + 3058620 * x ^ 4 - 164235 * x ^ 5 - 1264355 * x ^ 6 - 364410 * x ^ 7 - 2280 * x ^ 8) * (t - ((1 / 4))) ^ 2 * (((7 / 20)) - t) + (31920 * x + 46560 * x ^ 2 + 1145456 * x ^ 3 + 1312020 * x ^ 4 + 123005 * x ^ 5 - 357115 * x ^ 6 - 108570 * x ^ 7 + 728 * x ^ 8) * (t - ((1 / 4))) ^ 3 := by unfold nhLHJ1; ring
  have h2 : 0 < 8000 * (((7 / 20)) - ((1 / 4))) ^ 3 * (nhLHJ1 t x) := lt_of_lt_of_eq hpos e.symm
  exact pos_of_mul_pos_right h2 (by positivity)

/-- `J_1 > 0` on the high-ratio face. -/
theorem nhLHJ1_dom (t x : ℝ) (ht0 : 1 / 4 ≤ t) (ht1 : t ≤ 7 / 20) (hx0 : 1 / 2 ≤ x) (hx1 : x ≤ 1) :
    0 < nhLHJ1 t x :=
  nhLHJ1_p0 x t hx0 hx1 ht0 ht1 (by norm_num)

/-- The sign `J_2` on the high-ratio face. -/
noncomputable def nhLHJ2 (t x : ℝ) : ℝ :=
  -76 * x ^ 2 + 1602 * x ^ 3 + 2177 * x ^ 4 + (1717 / 2) * x ^ 5 + (95 / 2) * x ^ 6 + 3 * x ^ 7 + 20 * t * x - 4890 * t * x ^ 2 - 13741 * t * x ^ 3 - (31503 / 2) * t * x ^ 4 - 10181 * t * x ^ 5 - 4102 * t * x ^ 6 - (1731 / 2) * t * x ^ 7 - 24 * t * x ^ 8 + 24 * t ^ 2 - 224 * t ^ 2 * x + 17212 * t ^ 2 * x ^ 2 + 44164 * t ^ 2 * x ^ 3 + (97523 / 2) * t ^ 2 * x ^ 4 + 29868 * t ^ 2 * x ^ 5 + (20997 / 2) * t ^ 2 * x ^ 6 + 1803 * t ^ 2 * x ^ 7 + 60 * t ^ 2 * x ^ 8 + 744 * t ^ 3 * x - 10308 * t ^ 3 * x ^ 2 - 28986 * t ^ 3 * x ^ 3 - 32655 * t ^ 3 * x ^ 4 - 19374 * t ^ 3 * x ^ 5 - 6159 * t ^ 3 * x ^ 6 - 912 * t ^ 3 * x ^ 7 - 36 * t ^ 3 * x ^ 8

private theorem nhLHJ2_p0_g0_bp0 (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    0 ≤ 59683500 * a * b ^ 7 + 529150875 * a ^ 2 * b ^ 6 + 1948350000 * a ^ 3 * b ^ 5 + 3841785000 * a ^ 4 * b ^ 4 + 4345734000 * a ^ 5 * b ^ 3 + 2779362000 * a ^ 6 * b ^ 2 + 903528000 * a ^ 7 * b + 106992000 * a ^ 8 := by positivity

private theorem nhLHJ2_p0_g0_l0 (x : ℝ) (h0 : (1 / 2) ≤ x) (h1 : x ≤ 1) :
    0 < 12000 + 21000 * x - 3070500 * x ^ 2 + 3792750 * x ^ 3 + 6211875 * x ^ 4 - 981750 * x ^ 5 - 3344625 * x ^ 6 - 919500 * x ^ 7 - 22500 * x ^ 8 := by
  linear_combination (1 / 64 : ℝ) * nhLHJ2_p0_g0_bp0 (2 * x - 1) (2 - 2 * x) (by linarith) (by linarith)

theorem nhLHJ2_p0_g0 (x : ℝ) (h0 : (1 / 2) ≤ x) (h1 : x ≤ 1) :
    0 < 12000 + 21000 * x - 3070500 * x ^ 2 + 3792750 * x ^ 3 + 6211875 * x ^ 4 - 981750 * x ^ 5 - 3344625 * x ^ 6 - 919500 * x ^ 7 - 22500 * x ^ 8 := by
  exact nhLHJ2_p0_g0_l0 x h0 h1

private theorem nhLHJ2_p0_g1_bp0 (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    0 ≤ 322345200 * a * b ^ 7 + 2733959375 * a ^ 2 * b ^ 6 + 9781490000 * a ^ 3 * b ^ 5 + 19040260600 * a ^ 4 * b ^ 4 + 21647858800 * a ^ 5 * b ^ 3 + 14256222000 * a ^ 6 * b ^ 2 + 4968230400 * a ^ 7 * b + 689465400 * a ^ 8 := by positivity

private theorem nhLHJ2_p0_g1_l0 (x : ℝ) (h0 : (1 / 2) ≤ x) (h1 : x ≤ 1) :
    0 < 45600 + 101000 * x - 7784900 * x ^ 2 + 13703150 * x ^ 3 + 20640775 * x ^ 4 - 2048950 * x ^ 5 - 10039925 * x ^ 6 - 2866500 * x ^ 7 - 68100 * x ^ 8 := by
  linear_combination (1 / 64 : ℝ) * nhLHJ2_p0_g1_bp0 (2 * x - 1) (2 - 2 * x) (by linarith) (by linarith)

theorem nhLHJ2_p0_g1 (x : ℝ) (h0 : (1 / 2) ≤ x) (h1 : x ≤ 1) :
    0 < 45600 + 101000 * x - 7784900 * x ^ 2 + 13703150 * x ^ 3 + 20640775 * x ^ 4 - 2048950 * x ^ 5 - 10039925 * x ^ 6 - 2866500 * x ^ 7 - 68100 * x ^ 8 := by
  exact nhLHJ2_p0_g1_l0 x h0 h1

private theorem nhLHJ2_p0_g2_bp0 (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    0 ≤ 580297900 * a * b ^ 7 + 4817415265 * a ^ 2 * b ^ 6 + 17012774800 * a ^ 3 * b ^ 5 + 33016887480 * a ^ 4 * b ^ 4 + 37889158480 * a ^ 5 * b ^ 3 + 25598790000 * a ^ 6 * b ^ 2 + 9374612160 * a ^ 7 * b + 1423734080 * a ^ 8 := by positivity

private theorem nhLHJ2_p0_g2_l0 (x : ℝ) (h0 : (1 / 2) ≤ x) (h1 : x ≤ 1) :
    0 < 57120 + 165720 * x - 5599820 * x ^ 2 + 17822010 * x ^ 3 + 24587545 * x ^ 4 + 74350 * x ^ 5 - 9575635 * x ^ 6 - 2884980 * x ^ 7 - 66060 * x ^ 8 := by
  linear_combination (1 / 64 : ℝ) * nhLHJ2_p0_g2_bp0 (2 * x - 1) (2 - 2 * x) (by linarith) (by linarith)

theorem nhLHJ2_p0_g2 (x : ℝ) (h0 : (1 / 2) ≤ x) (h1 : x ≤ 1) :
    0 < 57120 + 165720 * x - 5599820 * x ^ 2 + 17822010 * x ^ 3 + 24587545 * x ^ 4 + 74350 * x ^ 5 - 9575635 * x ^ 6 - 2884980 * x ^ 7 - 66060 * x ^ 8 := by
  exact nhLHJ2_p0_g2_l0 x h0 h1

private theorem nhLHJ2_p0_g3_bp0 (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    0 ≤ 303571000 * a * b ^ 7 + 2497078325 * a ^ 2 * b ^ 6 + 8771581424 * a ^ 3 * b ^ 5 + 17015322920 * a ^ 4 * b ^ 4 + 19636238544 * a ^ 5 * b ^ 3 + 13445025168 * a ^ 6 * b ^ 2 + 5041678080 * a ^ 7 * b + 795637448 * a ^ 8 := by positivity

private theorem nhLHJ2_p0_g3_l0 (x : ℝ) (h0 : (1 / 2) ≤ x) (h1 : x ≤ 1) :
    0 < 23520 + 91672 * x - 967884 * x ^ 2 + 7679722 * x ^ 3 + 9897405 * x ^ 4 + 986558 * x ^ 5 - 2929607 * x ^ 6 - 945276 * x ^ 7 - 20748 * x ^ 8 := by
  linear_combination (1 / 64 : ℝ) * nhLHJ2_p0_g3_bp0 (2 * x - 1) (2 - 2 * x) (by linarith) (by linarith)

theorem nhLHJ2_p0_g3 (x : ℝ) (h0 : (1 / 2) ≤ x) (h1 : x ≤ 1) :
    0 < 23520 + 91672 * x - 967884 * x ^ 2 + 7679722 * x ^ 3 + 9897405 * x ^ 4 + 986558 * x ^ 5 - 2929607 * x ^ 6 - 945276 * x ^ 7 - 20748 * x ^ 8 := by
  exact nhLHJ2_p0_g3_l0 x h0 h1

theorem nhLHJ2_p0 (x t : ℝ) (hx0 : (1 / 2) ≤ x) (hx1 : x ≤ 1)
    (hs0 : (1 / 4) ≤ t) (hs1 : t ≤ (7 / 20)) (hgap : (0 : ℝ) < ((7 / 20)) - ((1 / 4))) :
    0 < nhLHJ2 t x := by
  have hpos := nh_bern_pos3 (a := (t - ((1 / 4)))) (b := (((7 / 20)) - t)) (by linarith) (by linarith) (hgap.trans_eq (by ring))
    (nhLHJ2_p0_g0 x hx0 hx1) (nhLHJ2_p0_g1 x hx0 hx1) (nhLHJ2_p0_g2 x hx0 hx1) (nhLHJ2_p0_g3 x hx0 hx1)
  have e : 8000 * (((7 / 20)) - ((1 / 4))) ^ 3 * (nhLHJ2 t x) = (12000 + 21000 * x - 3070500 * x ^ 2 + 3792750 * x ^ 3 + 6211875 * x ^ 4 - 981750 * x ^ 5 - 3344625 * x ^ 6 - 919500 * x ^ 7 - 22500 * x ^ 8) * (((7 / 20)) - t) ^ 3 + (45600 + 101000 * x - 7784900 * x ^ 2 + 13703150 * x ^ 3 + 20640775 * x ^ 4 - 2048950 * x ^ 5 - 10039925 * x ^ 6 - 2866500 * x ^ 7 - 68100 * x ^ 8) * (t - ((1 / 4))) * (((7 / 20)) - t) ^ 2 + (57120 + 165720 * x - 5599820 * x ^ 2 + 17822010 * x ^ 3 + 24587545 * x ^ 4 + 74350 * x ^ 5 - 9575635 * x ^ 6 - 2884980 * x ^ 7 - 66060 * x ^ 8) * (t - ((1 / 4))) ^ 2 * (((7 / 20)) - t) + (23520 + 91672 * x - 967884 * x ^ 2 + 7679722 * x ^ 3 + 9897405 * x ^ 4 + 986558 * x ^ 5 - 2929607 * x ^ 6 - 945276 * x ^ 7 - 20748 * x ^ 8) * (t - ((1 / 4))) ^ 3 := by unfold nhLHJ2; ring
  have h2 : 0 < 8000 * (((7 / 20)) - ((1 / 4))) ^ 3 * (nhLHJ2 t x) := lt_of_lt_of_eq hpos e.symm
  exact pos_of_mul_pos_right h2 (by positivity)

/-- `J_2 > 0` on the high-ratio face. -/
theorem nhLHJ2_dom (t x : ℝ) (ht0 : 1 / 4 ≤ t) (ht1 : t ≤ 7 / 20) (hx0 : 1 / 2 ≤ x) (hx1 : x ≤ 1) :
    0 < nhLHJ2 t x :=
  nhLHJ2_p0 x t hx0 hx1 ht0 ht1 (by norm_num)

/-- The sign `J_3` on the high-ratio face. -/
noncomputable def nhLHJ3 (t x : ℝ) : ℝ :=
  -364 * x ^ 2 + 286 * x ^ 3 + 1203 * x ^ 4 + (1797 / 2) * x ^ 5 + 240 * x ^ 6 + (35 / 2) * x ^ 7 + 64 * t * x - 1184 * t * x ^ 2 - 6008 * t * x ^ 3 - 11052 * t * x ^ 4 - 10000 * t * x ^ 5 - 4592 * t * x ^ 6 - 906 * t * x ^ 7 - 12 * t * x ^ 8 + 10 * t * x ^ 9 + 116 * t ^ 2 - 922 * t ^ 2 * x + 5415 * t ^ 2 * x ^ 2 + (44181 / 2) * t ^ 2 * x ^ 3 + 33696 * t ^ 2 * x ^ 4 + (55523 / 2) * t ^ 2 * x ^ 5 + 12873 * t ^ 2 * x ^ 6 + 3089 * t ^ 2 * x ^ 7 + 288 * t ^ 2 * x ^ 8 + 32 * t ^ 3 + 3848 * t ^ 3 * x + 7044 * t ^ 3 * x ^ 2 + 1602 * t ^ 3 * x ^ 3 - 7383 * t ^ 3 * x ^ 4 - 9507 * t ^ 3 * x ^ 5 - 5276 * t ^ 3 * x ^ 6 - 1436 * t ^ 3 * x ^ 7 - 156 * t ^ 3 * x ^ 8

private theorem nhLHJ3_p0_g0_bp0 (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    0 ≤ 31164750 * a * b ^ 8 + 314221500 * a ^ 2 * b ^ 7 + 1358311500 * a ^ 3 * b ^ 6 + 3283424000 * a ^ 4 * b ^ 5 + 4848004750 * a ^ 5 * b ^ 4 + 4469834500 * a ^ 6 * b ^ 3 + 2507218500 * a ^ 7 * b ^ 2 + 779516625 * a ^ 8 * b + 102299625 * a ^ 9 := by positivity

private theorem nhLHJ3_p0_g0_l0 (x : ℝ) (h0 : (1 / 2) ≤ x) (h1 : x ≤ 1) :
    0 < 62000 + 148000 * x - 1692000 * x ^ 2 + 1517500 * x ^ 3 + 3445125 * x ^ 4 - 119625 * x ^ 5 - 1487000 * x ^ 6 - 307000 * x ^ 7 + 100500 * x ^ 8 + 20000 * x ^ 9 := by
  linear_combination (1 / 64 : ℝ) * nhLHJ3_p0_g0_bp0 (2 * x - 1) (2 - 2 * x) (by linarith) (by linarith)

theorem nhLHJ3_p0_g0 (x : ℝ) (h0 : (1 / 2) ≤ x) (h1 : x ≤ 1) :
    0 < 62000 + 148000 * x - 1692000 * x ^ 2 + 1517500 * x ^ 3 + 3445125 * x ^ 4 - 119625 * x ^ 5 - 1487000 * x ^ 6 - 307000 * x ^ 7 + 100500 * x ^ 8 + 20000 * x ^ 9 := by
  exact nhLHJ3_p0_g0_l0 x h0 h1

private theorem nhLHJ3_p0_g1_bp0 (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    0 ≤ 355664250 * a * b ^ 8 + 3311164800 * a ^ 2 * b ^ 7 + 13457966300 * a ^ 3 * b ^ 6 + 31139376400 * a ^ 4 * b ^ 5 + 44801510550 * a ^ 5 * b ^ 4 + 40995467700 * a ^ 6 * b ^ 3 + 23278231700 * a ^ 7 * b ^ 2 + 7494351125 * a ^ 8 * b + 1046995725 * a ^ 9 := by positivity

private theorem nhLHJ3_p0_g1_l0 (x : ℝ) (h0 : (1 / 2) ≤ x) (h1 : x ≤ 1) :
    0 < 237200 + 703600 * x - 2800600 * x ^ 2 + 8822600 * x ^ 3 + 13864725 * x ^ 4 + 1319675 * x ^ 5 - 3776800 * x ^ 6 - 625600 * x ^ 7 + 383700 * x ^ 8 + 68000 * x ^ 9 := by
  linear_combination (1 / 64 : ℝ) * nhLHJ3_p0_g1_bp0 (2 * x - 1) (2 - 2 * x) (by linarith) (by linarith)

theorem nhLHJ3_p0_g1 (x : ℝ) (h0 : (1 / 2) ≤ x) (h1 : x ≤ 1) :
    0 < 237200 + 703600 * x - 2800600 * x ^ 2 + 8822600 * x ^ 3 + 13864725 * x ^ 4 + 1319675 * x ^ 5 - 3776800 * x ^ 6 - 625600 * x ^ 7 + 383700 * x ^ 8 + 68000 * x ^ 9 := by
  exact nhLHJ3_p0_g1_l0 x h0 h1

private theorem nhLHJ3_p0_g2_bp0 (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    0 ≤ 752388210 * a * b ^ 8 + 6914070700 * a ^ 2 * b ^ 7 + 27815560420 * a ^ 3 * b ^ 6 + 63927630080 * a ^ 4 * b ^ 5 + 91731199530 * a ^ 5 * b ^ 4 + 84102154380 * a ^ 6 * b ^ 3 + 48091991820 * a ^ 7 * b ^ 2 + 15678346915 * a ^ 8 * b + 2231071595 * a ^ 9 := by positivity

private theorem nhLHJ3_p0_g2_l0 (x : ℝ) (h0 : (1 / 2) ≤ x) (h1 : x ≤ 1) :
    0 < 299600 + 1120320 * x + 330640 * x ^ 2 + 14956060 * x ^ 3 + 19646775 * x ^ 4 + 4648725 * x ^ 5 - 2379320 * x ^ 6 - 169240 * x ^ 7 + 479580 * x ^ 8 + 76000 * x ^ 9 := by
  linear_combination (1 / 64 : ℝ) * nhLHJ3_p0_g2_bp0 (2 * x - 1) (2 - 2 * x) (by linarith) (by linarith)

theorem nhLHJ3_p0_g2 (x : ℝ) (h0 : (1 / 2) ≤ x) (h1 : x ≤ 1) :
    0 < 299600 + 1120320 * x + 330640 * x ^ 2 + 14956060 * x ^ 3 + 19646775 * x ^ 4 + 4648725 * x ^ 5 - 2379320 * x ^ 6 - 169240 * x ^ 7 + 479580 * x ^ 8 + 76000 * x ^ 9 := by
  exact nhLHJ3_p0_g2_l0 x h0 h1

private theorem nhLHJ3_p0_g3_bp0 (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    0 ≤ 428983110 * a * b ^ 8 + 3923390680 * a ^ 2 * b ^ 7 + 15725679092 * a ^ 3 * b ^ 6 + 36058223216 * a ^ 4 * b ^ 5 + 51705882674 * a ^ 5 * b ^ 4 + 47461271484 * a ^ 6 * b ^ 3 + 27225826588 * a ^ 7 * b ^ 2 + 8922538295 * a ^ 8 * b + 1279055711 * a ^ 9 := by positivity

private theorem nhLHJ3_p0_g3_l0 (x : ℝ) (h0 : (1 / 2) ≤ x) (h1 : x ≤ 1) :
    0 < 124656 + 595504 * x + 1495592 * x ^ 2 + 7663776 * x ^ 3 + 9168111 * x ^ 4 + 3133369 * x ^ 5 - 131728 * x ^ 6 + 137872 * x ^ 7 + 195132 * x ^ 8 + 28000 * x ^ 9 := by
  linear_combination (1 / 64 : ℝ) * nhLHJ3_p0_g3_bp0 (2 * x - 1) (2 - 2 * x) (by linarith) (by linarith)

theorem nhLHJ3_p0_g3 (x : ℝ) (h0 : (1 / 2) ≤ x) (h1 : x ≤ 1) :
    0 < 124656 + 595504 * x + 1495592 * x ^ 2 + 7663776 * x ^ 3 + 9168111 * x ^ 4 + 3133369 * x ^ 5 - 131728 * x ^ 6 + 137872 * x ^ 7 + 195132 * x ^ 8 + 28000 * x ^ 9 := by
  exact nhLHJ3_p0_g3_l0 x h0 h1

theorem nhLHJ3_p0 (x t : ℝ) (hx0 : (1 / 2) ≤ x) (hx1 : x ≤ 1)
    (hs0 : (1 / 4) ≤ t) (hs1 : t ≤ (7 / 20)) (hgap : (0 : ℝ) < ((7 / 20)) - ((1 / 4))) :
    0 < nhLHJ3 t x := by
  have hpos := nh_bern_pos3 (a := (t - ((1 / 4)))) (b := (((7 / 20)) - t)) (by linarith) (by linarith) (hgap.trans_eq (by ring))
    (nhLHJ3_p0_g0 x hx0 hx1) (nhLHJ3_p0_g1 x hx0 hx1) (nhLHJ3_p0_g2 x hx0 hx1) (nhLHJ3_p0_g3 x hx0 hx1)
  have e : 8000 * (((7 / 20)) - ((1 / 4))) ^ 3 * (nhLHJ3 t x) = (62000 + 148000 * x - 1692000 * x ^ 2 + 1517500 * x ^ 3 + 3445125 * x ^ 4 - 119625 * x ^ 5 - 1487000 * x ^ 6 - 307000 * x ^ 7 + 100500 * x ^ 8 + 20000 * x ^ 9) * (((7 / 20)) - t) ^ 3 + (237200 + 703600 * x - 2800600 * x ^ 2 + 8822600 * x ^ 3 + 13864725 * x ^ 4 + 1319675 * x ^ 5 - 3776800 * x ^ 6 - 625600 * x ^ 7 + 383700 * x ^ 8 + 68000 * x ^ 9) * (t - ((1 / 4))) * (((7 / 20)) - t) ^ 2 + (299600 + 1120320 * x + 330640 * x ^ 2 + 14956060 * x ^ 3 + 19646775 * x ^ 4 + 4648725 * x ^ 5 - 2379320 * x ^ 6 - 169240 * x ^ 7 + 479580 * x ^ 8 + 76000 * x ^ 9) * (t - ((1 / 4))) ^ 2 * (((7 / 20)) - t) + (124656 + 595504 * x + 1495592 * x ^ 2 + 7663776 * x ^ 3 + 9168111 * x ^ 4 + 3133369 * x ^ 5 - 131728 * x ^ 6 + 137872 * x ^ 7 + 195132 * x ^ 8 + 28000 * x ^ 9) * (t - ((1 / 4))) ^ 3 := by unfold nhLHJ3; ring
  have h2 : 0 < 8000 * (((7 / 20)) - ((1 / 4))) ^ 3 * (nhLHJ3 t x) := lt_of_lt_of_eq hpos e.symm
  exact pos_of_mul_pos_right h2 (by positivity)

/-- `J_3 > 0` on the high-ratio face. -/
theorem nhLHJ3_dom (t x : ℝ) (ht0 : 1 / 4 ≤ t) (ht1 : t ≤ 7 / 20) (hx0 : 1 / 2 ≤ x) (hx1 : x ≤ 1) :
    0 < nhLHJ3 t x :=
  nhLHJ3_p0 x t hx0 hx1 ht0 ht1 (by norm_num)

/-- The sign `J_4` on the high-ratio face. -/
noncomputable def nhLHJ4 (t x : ℝ) : ℝ :=
  -60 * x ^ 2 - 10 * x ^ 3 + 135 * x ^ 4 + (277 / 2) * x ^ 5 + 50 * x ^ 6 + (11 / 2) * x ^ 7 - 16 * t * x + 40 * t * x ^ 2 + 60 * t * x ^ 3 + 2 * t * x ^ 4 + 164 * t * x ^ 5 + 356 * t * x ^ 6 + 264 * t * x ^ 7 + 84 * t * x ^ 8 + 10 * t * x ^ 9 + 20 * t ^ 2 - 26 * t ^ 2 * x + 743 * t ^ 2 * x ^ 2 + (5637 / 2) * t ^ 2 * x ^ 3 + 4438 * t ^ 2 * x ^ 4 + (7579 / 2) * t ^ 2 * x ^ 5 + 1821 * t ^ 2 * x ^ 6 + 461 * t ^ 2 * x ^ 7 + 48 * t ^ 2 * x ^ 8 + 32 * t ^ 3 + 872 * t ^ 3 * x + 2436 * t ^ 3 * x ^ 2 + 2946 * t ^ 3 * x ^ 3 + 1761 * t ^ 3 * x ^ 4 + 375 * t ^ 3 * x ^ 5 - 122 * t ^ 3 * x ^ 6 - 80 * t ^ 3 * x ^ 7 - 12 * t ^ 3 * x ^ 8

private theorem nhLHJ4_p0_g0_bp0 (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    0 ≤ 159867000 * a * b ^ 8 + 1518933000 * a ^ 2 * b ^ 7 + 6351608250 * a ^ 3 * b ^ 6 + 15260103500 * a ^ 4 * b ^ 5 + 23028460750 * a ^ 5 * b ^ 4 + 22341194500 * a ^ 6 * b ^ 3 + 13601914500 * a ^ 7 * b ^ 2 + 4749695625 * a ^ 8 * b + 728078625 * a ^ 9 := by positivity

private theorem nhLHJ4_p0_g0_l0 (x : ℝ) (h0 : (1 / 2) ≤ x) (h1 : x ≤ 1) :
    0 < 14000 + 64000 * x + 276000 * x ^ 2 + 1817500 * x ^ 3 + 3523125 * x ^ 4 + 3377625 * x ^ 5 + 2007250 * x ^ 6 + 792500 * x ^ 7 + 190500 * x ^ 8 + 20000 * x ^ 9 := by
  linear_combination (1 / 64 : ℝ) * nhLHJ4_p0_g0_bp0 (2 * x - 1) (2 - 2 * x) (by linarith) (by linarith)

theorem nhLHJ4_p0_g0 (x : ℝ) (h0 : (1 / 2) ≤ x) (h1 : x ≤ 1) :
    0 < 14000 + 64000 * x + 276000 * x ^ 2 + 1817500 * x ^ 3 + 3523125 * x ^ 4 + 3377625 * x ^ 5 + 2007250 * x ^ 6 + 792500 * x ^ 7 + 190500 * x ^ 8 + 20000 * x ^ 9 := by
  exact nhLHJ4_p0_g0_l0 x h0 h1

private theorem nhLHJ4_p0_g1_bp0 (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    0 ≤ 601264500 * a * b ^ 8 + 5682663100 * a ^ 2 * b ^ 7 + 23636833450 * a ^ 3 * b ^ 6 + 56490811900 * a ^ 4 * b ^ 5 + 84811271350 * a ^ 5 * b ^ 4 + 81873226100 * a ^ 6 * b ^ 3 + 49611185300 * a ^ 7 * b ^ 2 + 17246433725 * a ^ 8 * b + 2632588725 * a ^ 9 := by positivity

private theorem nhLHJ4_p0_g1_l0 (x : ℝ) (h0 : (1 / 2) ≤ x) (h1 : x ≤ 1) :
    0 < 54800 + 299600 * x + 1522600 * x ^ 2 + 7069800 * x ^ 3 + 12610325 * x ^ 4 + 11836125 * x ^ 5 + 7016650 * x ^ 6 + 2761100 * x ^ 7 + 656100 * x ^ 8 + 68000 * x ^ 9 := by
  linear_combination (1 / 64 : ℝ) * nhLHJ4_p0_g1_bp0 (2 * x - 1) (2 - 2 * x) (by linarith) (by linarith)

theorem nhLHJ4_p0_g1 (x : ℝ) (h0 : (1 / 2) ≤ x) (h1 : x ≤ 1) :
    0 < 54800 + 299600 * x + 1522600 * x ^ 2 + 7069800 * x ^ 3 + 12610325 * x ^ 4 + 11836125 * x ^ 5 + 7016650 * x ^ 6 + 2761100 * x ^ 7 + 656100 * x ^ 8 + 68000 * x ^ 9 := by
  exact nhLHJ4_p0_g1_l0 x h0 h1

private theorem nhLHJ4_p0_g2_bp0 (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    0 ≤ 752345120 * a * b ^ 8 + 7076811600 * a ^ 2 * b ^ 7 + 29293628190 * a ^ 3 * b ^ 6 + 69671206660 * a ^ 4 * b ^ 5 + 104097454250 * a ^ 5 * b ^ 4 + 100018508300 * a ^ 6 * b ^ 3 + 60329241420 * a ^ 7 * b ^ 2 + 20879861995 * a ^ 8 * b + 3173729075 * a ^ 9 := by positivity

private theorem nhLHJ4_p0_g2_l0 (x : ℝ) (h0 : (1 / 2) ≤ x) (h1 : x ≤ 1) :
    0 < 71120 + 457440 * x + 2422800 * x ^ 2 + 9089340 * x ^ 3 + 15111975 * x ^ 4 + 13865035 * x ^ 5 + 8149910 * x ^ 6 + 3176780 * x ^ 7 + 743820 * x ^ 8 + 76000 * x ^ 9 := by
  linear_combination (1 / 64 : ℝ) * nhLHJ4_p0_g2_bp0 (2 * x - 1) (2 - 2 * x) (by linarith) (by linarith)

theorem nhLHJ4_p0_g2 (x : ℝ) (h0 : (1 / 2) ≤ x) (h1 : x ≤ 1) :
    0 < 71120 + 457440 * x + 2422800 * x ^ 2 + 9089340 * x ^ 3 + 15111975 * x ^ 4 + 13865035 * x ^ 5 + 8149910 * x ^ 6 + 3176780 * x ^ 7 + 743820 * x ^ 8 + 76000 * x ^ 9 := by
  exact nhLHJ4_p0_g2_l0 x h0 h1

private theorem nhLHJ4_p0_g3_bp0 (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    0 ≤ 312607220 * a * b ^ 8 + 2927611820 * a ^ 2 * b ^ 7 + 12064088318 * a ^ 3 * b ^ 6 + 28562469940 * a ^ 4 * b ^ 5 + 42481603410 * a ^ 5 * b ^ 4 + 40632678012 * a ^ 6 * b ^ 3 + 24399920284 * a ^ 7 * b ^ 2 + 8408076431 * a ^ 8 * b + 1272620471 * a ^ 9 := by positivity

private theorem nhLHJ4_p0_g3_l0 (x : ℝ) (h0 : (1 / 2) ≤ x) (h1 : x ≤ 1) :
    0 < 30576 + 228816 * x + 1195688 * x ^ 2 + 3860608 * x ^ 3 + 6038863 * x ^ 4 + 5409535 * x ^ 5 + 3139534 * x ^ 6 + 1207540 * x ^ 7 + 278124 * x ^ 8 + 28000 * x ^ 9 := by
  linear_combination (1 / 64 : ℝ) * nhLHJ4_p0_g3_bp0 (2 * x - 1) (2 - 2 * x) (by linarith) (by linarith)

theorem nhLHJ4_p0_g3 (x : ℝ) (h0 : (1 / 2) ≤ x) (h1 : x ≤ 1) :
    0 < 30576 + 228816 * x + 1195688 * x ^ 2 + 3860608 * x ^ 3 + 6038863 * x ^ 4 + 5409535 * x ^ 5 + 3139534 * x ^ 6 + 1207540 * x ^ 7 + 278124 * x ^ 8 + 28000 * x ^ 9 := by
  exact nhLHJ4_p0_g3_l0 x h0 h1

theorem nhLHJ4_p0 (x t : ℝ) (hx0 : (1 / 2) ≤ x) (hx1 : x ≤ 1)
    (hs0 : (1 / 4) ≤ t) (hs1 : t ≤ (7 / 20)) (hgap : (0 : ℝ) < ((7 / 20)) - ((1 / 4))) :
    0 < nhLHJ4 t x := by
  have hpos := nh_bern_pos3 (a := (t - ((1 / 4)))) (b := (((7 / 20)) - t)) (by linarith) (by linarith) (hgap.trans_eq (by ring))
    (nhLHJ4_p0_g0 x hx0 hx1) (nhLHJ4_p0_g1 x hx0 hx1) (nhLHJ4_p0_g2 x hx0 hx1) (nhLHJ4_p0_g3 x hx0 hx1)
  have e : 8000 * (((7 / 20)) - ((1 / 4))) ^ 3 * (nhLHJ4 t x) = (14000 + 64000 * x + 276000 * x ^ 2 + 1817500 * x ^ 3 + 3523125 * x ^ 4 + 3377625 * x ^ 5 + 2007250 * x ^ 6 + 792500 * x ^ 7 + 190500 * x ^ 8 + 20000 * x ^ 9) * (((7 / 20)) - t) ^ 3 + (54800 + 299600 * x + 1522600 * x ^ 2 + 7069800 * x ^ 3 + 12610325 * x ^ 4 + 11836125 * x ^ 5 + 7016650 * x ^ 6 + 2761100 * x ^ 7 + 656100 * x ^ 8 + 68000 * x ^ 9) * (t - ((1 / 4))) * (((7 / 20)) - t) ^ 2 + (71120 + 457440 * x + 2422800 * x ^ 2 + 9089340 * x ^ 3 + 15111975 * x ^ 4 + 13865035 * x ^ 5 + 8149910 * x ^ 6 + 3176780 * x ^ 7 + 743820 * x ^ 8 + 76000 * x ^ 9) * (t - ((1 / 4))) ^ 2 * (((7 / 20)) - t) + (30576 + 228816 * x + 1195688 * x ^ 2 + 3860608 * x ^ 3 + 6038863 * x ^ 4 + 5409535 * x ^ 5 + 3139534 * x ^ 6 + 1207540 * x ^ 7 + 278124 * x ^ 8 + 28000 * x ^ 9) * (t - ((1 / 4))) ^ 3 := by unfold nhLHJ4; ring
  have h2 : 0 < 8000 * (((7 / 20)) - ((1 / 4))) ^ 3 * (nhLHJ4 t x) := lt_of_lt_of_eq hpos e.symm
  exact pos_of_mul_pos_right h2 (by positivity)

/-- `J_4 > 0` on the high-ratio face. -/
theorem nhLHJ4_dom (t x : ℝ) (ht0 : 1 / 4 ≤ t) (ht1 : t ≤ 7 / 20) (hx0 : 1 / 2 ≤ x) (hx1 : x ≤ 1) :
    0 < nhLHJ4 t x :=
  nhLHJ4_p0 x t hx0 hx1 ht0 ht1 (by norm_num)

/-- The sign `J_5` on the high-ratio face. -/
noncomputable def nhLHJ5 (t x : ℝ) : ℝ :=
  -8 * x ^ 2 - 8 * x ^ 3 + 28 * x ^ 4 + 42 * x ^ 5 + (39 / 2) * x ^ 6 + (5 / 2) * x ^ 7 - 8 * t * x + 136 * t * x ^ 2 + 484 * t * x ^ 3 + 752 * t * x ^ 4 + (1495 / 2) * t * x ^ 5 + (1007 / 2) * t * x ^ 6 + 212 * t * x ^ 7 + 49 * t * x ^ 8 + 5 * t * x ^ 9 + 16 * t ^ 2 * x + 16 * t ^ 2 * x ^ 2 + 176 * t ^ 2 * x ^ 3 + 468 * t ^ 2 * x ^ 4 + 517 * t ^ 2 * x ^ 5 + 290 * t ^ 2 * x ^ 6 + 85 * t ^ 2 * x ^ 7 + 11 * t ^ 2 * x ^ 8 + 192 * t ^ 3 * x + 816 * t ^ 3 * x ^ 2 + 1368 * t ^ 3 * x ^ 3 + 1212 * t ^ 3 * x ^ 4 + 606 * t ^ 3 * x ^ 5 + 162 * t ^ 3 * x ^ 6 + 18 * t ^ 3 * x ^ 7

private theorem nhLHJ5_p0_g0_bp0 (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    0 ≤ 103966875 * a * b ^ 8 + 984589125 * a ^ 2 * b ^ 7 + 4104148500 * a ^ 3 * b ^ 6 + 9831216500 * a ^ 4 * b ^ 5 + 14795831500 * a ^ 5 * b ^ 4 + 14319525000 * a ^ 6 * b ^ 3 + 8699319000 * a ^ 7 * b ^ 2 + 3031845750 * a ^ 8 * b + 463911750 * a ^ 9 := by positivity

private theorem nhLHJ5_p0_g0_l0 (x : ℝ) (h0 : (1 / 2) ≤ x) (h1 : x ≤ 1) :
    0 < 8000 * x + 159000 * x ^ 2 + 581500 * x ^ 3 + 1056750 * x ^ 4 + 1082625 * x ^ 5 + 664125 * x ^ 6 + 244375 * x ^ 7 + 51750 * x ^ 8 + 5000 * x ^ 9 := by
  linear_combination (1 / 128 : ℝ) * nhLHJ5_p0_g0_bp0 (2 * x - 1) (2 - 2 * x) (by linarith) (by linarith)

theorem nhLHJ5_p0_g0 (x : ℝ) (h0 : (1 / 2) ≤ x) (h1 : x ≤ 1) :
    0 < 8000 * x + 159000 * x ^ 2 + 581500 * x ^ 3 + 1056750 * x ^ 4 + 1082625 * x ^ 5 + 664125 * x ^ 6 + 244375 * x ^ 7 + 51750 * x ^ 8 + 5000 * x ^ 9 := by
  exact nhLHJ5_p0_g0_l0 x h0 h1

private theorem nhLHJ5_p0_g1_bp0 (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    0 ≤ 364891575 * a * b ^ 8 + 3449248025 * a ^ 2 * b ^ 7 + 14350934100 * a ^ 3 * b ^ 6 + 34312402800 * a ^ 4 * b ^ 5 + 51544277800 * a ^ 5 * b ^ 4 + 49795230000 * a ^ 6 * b ^ 3 + 30198981600 * a ^ 7 * b ^ 2 + 10507498200 * a ^ 8 * b + 1605298200 * a ^ 9 := by positivity

private theorem nhLHJ5_p0_g1_l0 (x : ℝ) (h0 : (1 / 2) ≤ x) (h1 : x ≤ 1) :
    0 < 38400 * x + 595800 * x ^ 2 + 2075900 * x ^ 3 + 3655550 * x ^ 4 + 3695725 * x ^ 5 + 2263925 * x ^ 6 + 836275 * x ^ 7 + 177050 * x ^ 8 + 17000 * x ^ 9 := by
  linear_combination (1 / 128 : ℝ) * nhLHJ5_p0_g1_bp0 (2 * x - 1) (2 - 2 * x) (by linarith) (by linarith)

theorem nhLHJ5_p0_g1 (x : ℝ) (h0 : (1 / 2) ≤ x) (h1 : x ≤ 1) :
    0 < 38400 * x + 595800 * x ^ 2 + 2075900 * x ^ 3 + 3655550 * x ^ 4 + 3695725 * x ^ 5 + 2263925 * x ^ 6 + 836275 * x ^ 7 + 177050 * x ^ 8 + 17000 * x ^ 9 := by
  exact nhLHJ5_p0_g1_l0 x h0 h1

private theorem nhLHJ5_p0_g2_bp0 (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    0 ≤ 424974265 * a * b ^ 8 + 4009355215 * a ^ 2 * b ^ 7 + 16648134620 * a ^ 3 * b ^ 6 + 39725272660 * a ^ 4 * b ^ 5 + 59556920220 * a ^ 5 * b ^ 4 + 57423669480 * a ^ 6 * b ^ 3 + 34759286040 * a ^ 7 * b ^ 2 + 12072138950 * a ^ 8 * b + 1841125910 * a ^ 9 := by positivity

private theorem nhLHJ5_p0_g2_l0 (x : ℝ) (h0 : (1 / 2) ≤ x) (h1 : x ≤ 1) :
    0 < 59200 * x + 739720 * x ^ 2 + 2455380 * x ^ 3 + 4195930 * x ^ 4 + 4182435 * x ^ 5 + 2551935 * x ^ 6 + 943365 * x ^ 7 + 199290 * x ^ 8 + 19000 * x ^ 9 := by
  linear_combination (1 / 128 : ℝ) * nhLHJ5_p0_g2_bp0 (2 * x - 1) (2 - 2 * x) (by linarith) (by linarith)

theorem nhLHJ5_p0_g2 (x : ℝ) (h0 : (1 / 2) ≤ x) (h1 : x ≤ 1) :
    0 < 59200 * x + 739720 * x ^ 2 + 2455380 * x ^ 3 + 4195930 * x ^ 4 + 4182435 * x ^ 5 + 2551935 * x ^ 6 + 943365 * x ^ 7 + 199290 * x ^ 8 + 19000 * x ^ 9 := by
  exact nhLHJ5_p0_g2_l0 x h0 h1

private theorem nhLHJ5_p0_g3_bp0 (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    0 ≤ 164782165 * a * b ^ 8 + 1551274835 * a ^ 2 * b ^ 7 + 6427253948 * a ^ 3 * b ^ 6 + 15302501832 * a ^ 4 * b ^ 5 + 22890962544 * a ^ 5 * b ^ 4 + 22022642016 * a ^ 6 * b ^ 3 + 13301941296 * a ^ 7 * b ^ 2 + 4610207468 * a ^ 8 * b + 701687948 * a ^ 9 := by positivity

private theorem nhLHJ5_p0_g3_l0 (x : ℝ) (h0 : (1 / 2) ≤ x) (h1 : x ≤ 1) :
    0 < 29568 * x + 306184 * x ^ 2 + 966452 * x ^ 3 + 1601978 * x ^ 4 + 1571759 * x ^ 5 + 952783 * x ^ 6 + 351537 * x ^ 7 + 73990 * x ^ 8 + 7000 * x ^ 9 := by
  linear_combination (1 / 128 : ℝ) * nhLHJ5_p0_g3_bp0 (2 * x - 1) (2 - 2 * x) (by linarith) (by linarith)

theorem nhLHJ5_p0_g3 (x : ℝ) (h0 : (1 / 2) ≤ x) (h1 : x ≤ 1) :
    0 < 29568 * x + 306184 * x ^ 2 + 966452 * x ^ 3 + 1601978 * x ^ 4 + 1571759 * x ^ 5 + 952783 * x ^ 6 + 351537 * x ^ 7 + 73990 * x ^ 8 + 7000 * x ^ 9 := by
  exact nhLHJ5_p0_g3_l0 x h0 h1

theorem nhLHJ5_p0 (x t : ℝ) (hx0 : (1 / 2) ≤ x) (hx1 : x ≤ 1)
    (hs0 : (1 / 4) ≤ t) (hs1 : t ≤ (7 / 20)) (hgap : (0 : ℝ) < ((7 / 20)) - ((1 / 4))) :
    0 < nhLHJ5 t x := by
  have hpos := nh_bern_pos3 (a := (t - ((1 / 4)))) (b := (((7 / 20)) - t)) (by linarith) (by linarith) (hgap.trans_eq (by ring))
    (nhLHJ5_p0_g0 x hx0 hx1) (nhLHJ5_p0_g1 x hx0 hx1) (nhLHJ5_p0_g2 x hx0 hx1) (nhLHJ5_p0_g3 x hx0 hx1)
  have e : 4000 * (((7 / 20)) - ((1 / 4))) ^ 3 * (nhLHJ5 t x) = (8000 * x + 159000 * x ^ 2 + 581500 * x ^ 3 + 1056750 * x ^ 4 + 1082625 * x ^ 5 + 664125 * x ^ 6 + 244375 * x ^ 7 + 51750 * x ^ 8 + 5000 * x ^ 9) * (((7 / 20)) - t) ^ 3 + (38400 * x + 595800 * x ^ 2 + 2075900 * x ^ 3 + 3655550 * x ^ 4 + 3695725 * x ^ 5 + 2263925 * x ^ 6 + 836275 * x ^ 7 + 177050 * x ^ 8 + 17000 * x ^ 9) * (t - ((1 / 4))) * (((7 / 20)) - t) ^ 2 + (59200 * x + 739720 * x ^ 2 + 2455380 * x ^ 3 + 4195930 * x ^ 4 + 4182435 * x ^ 5 + 2551935 * x ^ 6 + 943365 * x ^ 7 + 199290 * x ^ 8 + 19000 * x ^ 9) * (t - ((1 / 4))) ^ 2 * (((7 / 20)) - t) + (29568 * x + 306184 * x ^ 2 + 966452 * x ^ 3 + 1601978 * x ^ 4 + 1571759 * x ^ 5 + 952783 * x ^ 6 + 351537 * x ^ 7 + 73990 * x ^ 8 + 7000 * x ^ 9) * (t - ((1 / 4))) ^ 3 := by unfold nhLHJ5; ring
  have h2 : 0 < 4000 * (((7 / 20)) - ((1 / 4))) ^ 3 * (nhLHJ5 t x) := lt_of_lt_of_eq hpos e.symm
  exact pos_of_mul_pos_right h2 (by positivity)

/-- `J_5 > 0` on the high-ratio face. -/
theorem nhLHJ5_dom (t x : ℝ) (ht0 : 1 / 4 ≤ t) (ht1 : t ≤ 7 / 20) (hx0 : 1 / 2 ≤ x) (hx1 : x ≤ 1) :
    0 < nhLHJ5 t x :=
  nhLHJ5_p0 x t hx0 hx1 ht0 ht1 (by norm_num)

end SmoothedOctagon
