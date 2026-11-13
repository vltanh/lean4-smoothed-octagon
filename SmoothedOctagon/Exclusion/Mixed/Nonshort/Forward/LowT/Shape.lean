module

public import SmoothedOctagon.Exclusion.Mixed.Nonshort.Forward.LowT.Circuit
public import SmoothedOctagon.Exclusion.Mixed.Nonshort.Forward.LowT.ShapeBoundary
public import SmoothedOctagon.Exclusion.Mixed.Nonshort.Forward.HighRatio.Shape

/-!
# The low-scale residual increases with the shape

The midpoint derivative is affine in the norm, logarithm, and shape.
Its comparison quartic is concave in the duration increment. On the exact
swap boundary, the smallest order gap gives a lower bound, controlled by scale concavity.
-/

@[expose] public section

namespace SmoothedOctagon

/-- The comparison incoming norm `V̄` with `T̄ = 1/2 - 7x/24`. -/
noncomputable def nltVbar (t x : ℝ) : ℝ :=
  1 - (1 - t) * (t + x) / (1 + x) ^ 2 + (1 - t) * x / (1 + x) ^ 2 * (1 / 2 - 7 / 24 * x - t)

/-- The comparison logarithm `L̄ = y - 5y²/12`, `y = q - 1`. -/
noncomputable def nltLbar (q : ℝ) : ℝ := (q - 1) - 5 / 12 * (q - 1) ^ 2

/-- `𝓑 = B₀ + B₁y + B₂y²`. -/
noncomputable def nltBs (t x y : ℝ) : ℝ :=
  7 * x - 6 * x * y + 7 * x ^ 2 - 2 * t * y + 9 * t * x - 40 * x * y ^ 2 + x ^ 2 * y - 26 * t * x * y + 14 * t * x ^ 2 - 2 * t ^ 2 * x - 60 * x ^ 2 * y ^ 2 + 7 * x ^ 3 * y - 2 * t * x * y ^ 2 - 52 * t * x ^ 2 * y + 7 * t * x ^ 3 - 4 * t ^ 2 * x * y - 20 * x ^ 3 * y ^ 2 - 6 * t * x ^ 2 * y ^ 2 - 24 * t * x ^ 3 * y - 2 * t ^ 2 * x * y ^ 2 - 2 * t * x ^ 3 * y ^ 2

/-- `S_0`: the `y^0`-coefficient of the quartic `S`. -/
noncomputable def nltSS0 (t x : ℝ) : ℝ :=
  84 * x ^ 2 + 24 * t * x + 133 * x ^ 3 - 144 * t * x ^ 2 - 72 * t ^ 2 * x + 49 * x ^ 4 - 262 * t * x ^ 3 - 12 * t ^ 2 * x ^ 2 + 48 * t ^ 3 * x - 35 * t * x ^ 4 + 115 * t ^ 2 * x ^ 3 + 72 * t ^ 3 * x ^ 2 + 49 * t * x ^ 5 - 14 * t ^ 2 * x ^ 4 + 14 * t ^ 3 * x ^ 3 - 49 * t ^ 2 * x ^ 5

/-- `S_1`: the `y^1`-coefficient of the quartic `S`. -/
noncomputable def nltSS1 (t x : ℝ) : ℝ :=
  -72 * x ^ 2 + 240 * t * x + 24 * t ^ 2 - 30 * x ^ 3 + 898 * t * x ^ 2 - 432 * t ^ 2 * x - 48 * t ^ 3 + 91 * x ^ 4 + 1000 * t * x ^ 3 - 1354 * t ^ 2 * x ^ 2 + 96 * t ^ 3 * x + 49 * x ^ 5 + 313 * t * x ^ 4 - 1382 * t ^ 2 * x ^ 3 + 384 * t ^ 3 * x ^ 2 - 49 * t * x ^ 5 - 524 * t ^ 2 * x ^ 4 + 316 * t ^ 3 * x ^ 3 + 96 * t ^ 3 * x ^ 4

/-- `S_2`: the `y^2`-coefficient of the quartic `S`. -/
noncomputable def nltSS2 (t x : ℝ) : ℝ :=
  -480 * x ^ 2 - 390 * t * x + 90 * t ^ 2 - 1000 * x ^ 3 - 784 * t * x ^ 2 + 396 * t ^ 2 * x - 164 * t ^ 3 - 660 * x ^ 4 - 854 * t * x ^ 3 + 856 * t ^ 2 * x ^ 2 - 328 * t ^ 3 * x - 140 * x ^ 5 - 830 * t * x ^ 4 + 1340 * t ^ 2 * x ^ 3 - 140 * t ^ 3 * x ^ 2 - 380 * t * x ^ 5 + 1264 * t ^ 2 * x ^ 4 + 62 * t ^ 3 * x ^ 3 + 494 * t ^ 2 * x ^ 5 + 48 * t ^ 3 * x ^ 4

/-- `S_3`: the `y^3`-coefficient of the quartic `S`. -/
noncomputable def nltSS3 (t x : ℝ) : ℝ :=
  -200 * t * x - 200 * t ^ 2 - 832 * t * x ^ 2 - 896 * t ^ 2 * x - 40 * t ^ 3 - 1280 * t * x ^ 3 - 1432 * t ^ 2 * x ^ 2 - 80 * t ^ 3 * x - 864 * t * x ^ 4 - 976 * t ^ 2 * x ^ 3 - 40 * t ^ 3 * x ^ 2 - 216 * t * x ^ 5 - 240 * t ^ 2 * x ^ 4

/-- `S_4`: the `y^4`-coefficient of the quartic `S`. -/
noncomputable def nltSS4 (t x : ℝ) : ℝ :=
  -40 * t * x ^ 2 - 60 * t ^ 2 * x - 20 * t ^ 3 - 100 * t * x ^ 3 - 140 * t ^ 2 * x ^ 2 - 40 * t ^ 3 * x - 80 * t * x ^ 4 - 100 * t ^ 2 * x ^ 3 - 20 * t ^ 3 * x ^ 2 - 20 * t * x ^ 5 - 20 * t ^ 2 * x ^ 4

/-- The quartic `S = ∑ Sᵢyⁱ`. -/
noncomputable def nltSS (t x y : ℝ) : ℝ :=
  nltSS0 t x + nltSS1 t x * y + nltSS2 t x * y ^ 2 + nltSS3 t x * y ^ 3 + nltSS4 t x * y ^ 4

theorem nlt_Kv_eq (t x q : ℝ) : hrsKv (nltAl q) t x q = -2 * q ^ 2 * (1 + x) * nltBs t x (q - 1) := by
  unfold hrsKv nltAl nltBs; ring

/-- **The comparison derivative**: at `v = V̄`, `L = L̄`, `k = 1 + j`,
`12W ∂_kF = q²S`. -/
theorem nlt_Kend_eq (t x q : ℝ) (hx : 0 < 1 + x) :
    12 * (1 + x) * hrsK (nltAl q) t x (2 * t + x) q (nltVbar t x) (nltLbar q) =
      q ^ 2 * nltSS t x (q - 1) := by
  have hV : nltVbar t x = ((1 + x) ^ 2 - (1 - t) * (t + x) + (1 - t) * x * (1 / 2 - 7 / 24 * x - t))
      / (1 + x) ^ 2 := by
    unfold nltVbar; field_simp
  rw [hV]
  unfold hrsK nsrA hrsTk nsfE0 nltLbar nltAl nltSS nltSS0 nltSS1 nltSS2 nltSS3 nltSS4
  field_simp
  ring

/-- **`𝓑 > 0`** for `1/3 ≤ t ≤ 3/8`, `x ≥ 17/60`, `0 ≤ y ≤ 9/32`: `B₁, B₂ ≤ 0`, so
`𝓑 ≥ 𝓑(9/32)`, and `512𝓑(9/32) ≥ 1100x - 288t > 0`. -/
theorem nlt_Bs_pos {t x y : ℝ} (ht0 : 1 / 3 ≤ t) (ht1 : t ≤ 3 / 8) (hx : 17 / 60 ≤ x)
    (hy0 : 0 ≤ y) (hy1 : y ≤ 9 / 32) : 0 < nltBs t x y := by
  have hx0 : 0 < x := by linarith
  have ht : 0 < t := by linarith
  have hB2 : 0 ≤ 2 * x * (t ^ 2 + t * x ^ 2 + 3 * t * x + t + 10 * x ^ 2 + 30 * x + 20) := by positivity
  have hB1 : 0 ≤ 2 * t + (4 * t ^ 2 + 26 * t + 6) * x + (52 * t - 1) * x ^ 2 + (24 * t - 7) * x ^ 3 := by
    have : 0 ≤ 52 * t - 1 := by linarith
    have : 0 ≤ 24 * t - 7 := by linarith
    positivity
  have h512 : 0 < -1681 * t ^ 2 * x + 47 * t * x ^ 3 - 563 * t * x ^ 2 + 783 * t * x - 288 * t
      + 198 * x ^ 3 + 1298 * x ^ 2 + 1100 * x := by
    have a1 : 0 ≤ t * x * (783 - 1681 * t) := mul_nonneg (by positivity) (by linarith)
    have a2 : 0 ≤ x ^ 2 * (1298 - 563 * t) := mul_nonneg (by positivity) (by linarith)
    have a3 : 0 ≤ (47 * t + 198) * x ^ 3 := by positivity
    nlinarith
  have k1 : -(2 * t + (4 * t ^ 2 + 26 * t + 6) * x + (52 * t - 1) * x ^ 2 + (24 * t - 7) * x ^ 3)
      * (9 / 32) ≤ -(2 * t + (4 * t ^ 2 + 26 * t + 6) * x + (52 * t - 1) * x ^ 2
        + (24 * t - 7) * x ^ 3) * y :=
    mul_le_mul_of_nonpos_left hy1 (by linarith)
  have k2 : -(2 * x * (t ^ 2 + t * x ^ 2 + 3 * t * x + t + 10 * x ^ 2 + 30 * x + 20)) * (9 / 32) ^ 2
      ≤ -(2 * x * (t ^ 2 + t * x ^ 2 + 3 * t * x + t + 10 * x ^ 2 + 30 * x + 20)) * y ^ 2 :=
    mul_le_mul_of_nonpos_left (pow_le_pow_left₀ hy0 hy1 2) (by linarith)
  unfold nltBs
  nlinarith

private theorem shape_zero_pos {t x : ℝ} (ht : 0 < t) (ht1 : t ≤ 3 / 8) (hx : 0 < x) :
    0 < nltSS0 t x := by
  have ht2 : t ^ 2 ≤ 9 / 64 := by nlinarith only [sq_nonneg (t - 3 / 8), ht1, ht.le]
  have c1 : 0 ≤ 84 - 60 * t - 72 * t ^ 2 := by linarith only [ht1, ht2]
  have c2 : 0 ≤ 133 - 129 * t - 14 * t ^ 2 := by linarith only [ht1, ht2]
  have hc : 0 < 1 - t := by linarith only [ht1]
  have hh : 0 < 1 - 2 * t := by linarith only [ht1]
  have he : nltSS0 t x = x * (1 - t) *
      (24 * t * (1 - 2 * t) + (84 - 60 * t - 72 * t ^ 2) * x
      + (133 - 129 * t - 14 * t ^ 2) * x ^ 2 + (49 + 14 * t) * x ^ 3 + 49 * t * x ^ 4) := by
    unfold nltSS0
    ring
  rw [he]
  positivity

private theorem shape_quad_neg {t x : ℝ} (ht : 0 < t) (ht1 : t ≤ 3 / 8)
    (hx : 0 ≤ x) (htx : 2 * t ≤ 3 * x) : nltSS2 t x < 0 := by
  have ht2 : t ^ 2 ≤ 9 / 64 := by nlinarith only [sq_nonneg (t - 3 / 8), ht1, ht.le]
  have c1 : -150 + 396 * t - 328 * t ^ 2 ≤ 0 := by nlinarith only [ht1, sq_nonneg t]
  have c2 : -784 + 856 * t - 140 * t ^ 2 ≤ 0 := by nlinarith only [ht1, sq_nonneg t]
  have c3 : -854 + 1340 * t + 62 * t ^ 2 ≤ 0 := by linarith only [ht1, ht2]
  have c4 : -830 + 1264 * t + 48 * t ^ 2 ≤ 0 := by linarith only [ht1, ht2]
  have c5 : -380 + 494 * t ≤ 0 := by linarith only [ht1]
  have p1 := mul_nonpos_of_nonneg_of_nonpos (mul_nonneg ht.le hx) c1
  have p2 := mul_nonpos_of_nonneg_of_nonpos (mul_nonneg (sq_nonneg x) ht.le) c2
  have p3 := mul_nonpos_of_nonneg_of_nonpos (mul_nonneg (pow_nonneg hx 3) ht.le) c3
  have p4 := mul_nonpos_of_nonneg_of_nonpos (mul_nonneg (pow_nonneg hx 4) ht.le) c4
  have p5 := mul_nonpos_of_nonneg_of_nonpos (mul_nonneg (pow_nonneg hx 5) ht.le) c5
  have hp := mul_le_mul_of_nonneg_left htx ht.le
  unfold nltSS2
  nlinarith only [p1, p2, p3, p4, p5, hp, pow_nonneg ht.le 3,
    sq_nonneg x, pow_nonneg hx 3, pow_nonneg hx 4, pow_nonneg hx 5, sq_pos_of_pos ht]

/-- The comparison quartic is positive between the initial and exact swap durations. -/
theorem nlt_SS_pos {t x y : ℝ} (ht0 : 1 / 3 ≤ t) (ht1 : t ≤ 3 / 8)
    (hj : 1 / 30 ≤ 2 * t + x - 1) (hj1 : 2 * t + x - 1 ≤ 1 / 4)
    (hy0 : 0 ≤ y) (hy : y * (4 * t + 2 * x - 1) ≤ 2 - 4 * t - x) :
    0 < nltSS t x y := by
  let h := 1 - 2 * t
  let j := 2 * t + x - 1
  have hh0 : 1 / 4 ≤ h := by dsimp [h]; linarith only [ht1]
  have hh1 : h ≤ 1 / 3 := by dsimp [h]; linarith only [ht0]
  have hj0 : 1 / 30 ≤ j := hj
  have hjupper : j ≤ 1 / 4 := hj1
  have hjpos : 0 < 1 + 2 * j := by linarith only [hj0]
  have hx : 0 < x := by linarith only [ht1, hj]
  have ht : 0 < t := by linarith only [ht0]
  let b := (h - j) / (1 + 2 * j)
  have hyb : y ≤ b := by
    apply (le_div_iff₀ hjpos).mpr
    dsimp [h, j]
    nlinarith only [hy]
  have hb : 0 ≤ b := hy0.trans hyb
  have s0 := shape_zero_pos ht ht1 hx
  have s2 := shape_quad_neg ht ht1 hx.le (by linarith only [ht1, hj])
  have s3 : nltSS3 t x ≤ 0 := by
    have he : nltSS3 t x = -(8 * t * (1 + x) ^ 2 * (5 * t ^ 2 + 30 * t * x ^ 2
        + 62 * t * x + 25 * t + 27 * x ^ 3 + 54 * x ^ 2 + 25 * x)) := by unfold nltSS3; ring
    rw [he]
    have : 0 ≤ 8 * t * (1 + x) ^ 2 * (5 * t ^ 2 + 30 * t * x ^ 2
        + 62 * t * x + 25 * t + 27 * x ^ 3 + 54 * x ^ 2 + 25 * x) := by positivity
    linarith only [this]
  have s4 : nltSS4 t x ≤ 0 := by
    have he : nltSS4 t x = -(20 * t * (t + x) * (1 + x) ^ 2 * (t + x ^ 2 + 2 * x)) := by
      unfold nltSS4
      ring
    rw [he]
    have : 0 ≤ 20 * t * (t + x) * (1 + x) ^ 2 * (t + x ^ 2 + 2 * x) := by positivity
    linarith only [this]
  have sb : 0 < nltSS t x b := by
    have edge := nltShapeEdge_pos hh0 hh1 hj0 hjupper
    have he : 4 * (1 + 2 * j) ^ 4 * nltSS t x b = (1 + h + j) ^ 2 * nltShapeEdge h j := by
      dsimp [h, j, b]
      unfold nltSS nltSS0 nltSS1 nltSS2 nltSS3 nltSS4 nltShapeEdge
      field_simp
      ring
    have hw : 0 < (1 + h + j) ^ 2 := by
      have : 0 < 1 + h + j := by linarith only [hh0, hj0]
      positivity
    have hp := mul_pos hw edge
    rw [← he] at hp
    exact pos_of_mul_pos_right hp (by positivity)
  by_cases hb0 : b = 0
  · have hyz : y = 0 := by linarith only [hy0, hyb, hb0]
    simpa [nltSS, hyz] using s0
  have hbpos : 0 < b := lt_of_le_of_ne hb (Ne.symm hb0)
  have key : b * nltSS t x y - ((b - y) * nltSS0 t x + y * nltSS t x b) =
      -(y * b * (b - y)) * (nltSS2 t x + nltSS3 t x * (y + b)
        + nltSS4 t x * (y ^ 2 + y * b + b ^ 2)) := by unfold nltSS; ring
  have c3 := mul_nonpos_of_nonpos_of_nonneg s3 (by positivity : (0 : ℝ) ≤ y + b)
  have c4 := mul_nonpos_of_nonpos_of_nonneg s4 (by positivity : (0 : ℝ) ≤ y ^ 2 + y * b + b ^ 2)
  have hsum : nltSS2 t x + nltSS3 t x * (y + b)
      + nltSS4 t x * (y ^ 2 + y * b + b ^ 2) ≤ 0 := by linarith only [s2, c3, c4]
  have hprod := mul_nonneg (show 0 ≤ y * b * (b - y) by positivity)
    (neg_nonneg.mpr hsum)
  have chord : 0 < (b - y) * nltSS0 t x + y * nltSS t x b := by
    rcases eq_or_lt_of_le hyb with he | he
    · rw [he]
      nlinarith only [mul_pos hbpos sb]
    · have p := mul_pos (sub_pos.mpr he) s0
      have q := mul_nonneg hy0 sb.le
      linarith only [p, q]
  have hp : 0 < b * nltSS t x y := by nlinarith only [key, hprod, chord]
  exact pos_of_mul_pos_right hp hb

/-- **Shape monotonicity**, integrated on `[1, k]`: on the low-`t` large-gap domain
`1/3 ≤ t ≤ 3/8`, `j = 2t + x - 1 ≥ 1/30`, `7x ≤ 12(1 - 2t)`, `1 ≤ q`, `q(4t + 2x - 1) ≤ 1 + x`, for
`1 ≤ k ≤ 2t + x`, the residual at the unit shape is at most its value at `k`. The bound
`Je² ≤ 17/16` (`nsf_LG_J`) is supplied by the caller. -/
theorem nlt_shape_ge {t x k q : ℝ} (ht0 : 1 / 3 ≤ t) (ht1 : t ≤ 3 / 8) (hj : 1 / 30 ≤ 2 * t + x - 1)
    (hjh : 7 * x ≤ 12 * (1 - 2 * t)) (hk1 : 1 ≤ k) (hk : k ≤ 2 * t + x) (hq : 1 ≤ q)
    (hqs : q * (4 * t + 2 * x - 1) ≤ 1 + x)
    (hJ : (t + x * (x + 2)) * q ^ 2 ≤ 17 / 16 * (1 + x) ^ 2) :
    nsfComb (nltAl q) (nltM t x q) t x 1 q (hrlVL t x) (nsrLp q) (nsrFl t x q) ≤
      nsfComb (nltAl q) (nltM t x q) t x k q (hrlVL t x) (nsrLp q) (nsrFl t x q) := by
  have hx0 : 17 / 60 ≤ x := by linarith
  have hx1 : x ≤ 4 / 7 := by linarith
  have hx : 0 < x := by linarith
  have hq0 : 0 < q := by linarith
  have ht : 0 < t := by linarith
  have hW : 0 < 1 + x := by linarith
  -- `y = q - 1 ≤ (29 - 60t)/32 < b(t)`, `y ≤ 9/32`
  have hy : (q - 1) * (1 + 2 * (2 * t + x - 1)) ≤ (1 - 2 * t) - (2 * t + x - 1) := by nlinarith
  have hyb : q - 1 ≤ (29 - 60 * t) / 32 := by
    have : 16 / 15 * (q - 1) ≤ (q - 1) * (1 + 2 * (2 * t + x - 1)) := by nlinarith
    linarith
  have hy9 : q - 1 ≤ 9 / 32 := by linarith
  -- the comparison derivative is positive
  have hKend : 0 < hrsK (nltAl q) t x (2 * t + x) q (nltVbar t x) (nltLbar q) := by
    have e := nlt_Kend_eq t x q hW
    have hS := nlt_SS_pos ht0 ht1 hj (by linarith only [ht0, hjh])
      (by linarith only [hq] : (0 : ℝ) ≤ q - 1) (by nlinarith only [hqs])
    have : 0 < q ^ 2 * nltSS t x (q - 1) := by positivity
    rw [← e] at this
    exact pos_of_mul_pos_right this (by positivity)
  -- the slopes and the comparisons `V_L < V̄`, `L₊ ≤ L̄`
  have hKv : hrsKv (nltAl q) t x q < 0 := by
    rw [nlt_Kv_eq]
    have := nlt_Bs_pos ht0 ht1 hx0 (by linarith : (0 : ℝ) ≤ q - 1) hy9
    have : 0 < 2 * q ^ 2 * (1 + x) * nltBs t x (q - 1) := by positivity
    linarith
  have hV : hrlVL t x < nltVbar t x := by
    have e : nltVbar t x - hrlVL t x = (1 - t) * x ^ 2 * (73 - 119 * x) /
        (24 * (17 * x + 76) * (1 + x) ^ 2) := by
      unfold nltVbar hrlVL; field_simp; ring
    have : 0 < (1 - t) * x ^ 2 * (73 - 119 * x) / (24 * (17 * x + 76) * (1 + x) ^ 2) := by
      have : 0 < 73 - 119 * x := by linarith
      have : 0 < 1 - t := by linarith
      positivity
    linarith
  have hL : nsrLp q ≤ nltLbar q := by
    have e : nltLbar q - nsrLp q = (q - 1) ^ 2 * (2 + 5 * q - 5 * q ^ 2) / (12 * q * (q + 1)) := by
      unfold nltLbar nsrLp; field_simp; ring
    have : 0 ≤ 2 + 5 * q - 5 * q ^ 2 := by nlinarith
    have : 0 ≤ (q - 1) ^ 2 * (2 + 5 * q - 5 * q ^ 2) / (12 * q * (q + 1)) := by positivity
    linarith
  have hKL : hrsKL (nltAl q) t x q ≤ 0 := by
    unfold hrsKL
    apply mul_nonpos_of_nonneg_of_nonpos
    · apply mul_nonneg (by positivity)
      unfold nltAl; nlinarith
    · have : 0 ≤ t * (t + x) * (1 + x) * q := by positivity
      linarith
  have hKk : hrsKk t x q ≤ 0 := by
    unfold hrsKk
    apply mul_nonpos_of_nonneg_of_nonpos
    · have h1 : (t + x) * (1 + x) ≤ t + x * (x + 2) := by nlinarith
      have h2 := mul_le_mul_of_nonneg_right hq (by positivity : (0 : ℝ) ≤ t + x * (x + 2))
      linarith
    · have : 0 ≤ 2 * t * q ^ 4 := by positivity
      linarith
  have dec := hrs_K_dec (nltAl q) t x ((k + 1) / 2) (2 * t + x) q (hrlVL t x) (nltVbar t x)
    (nsrLp q) (nltLbar q)
  have p1 : 0 < (hrlVL t x - nltVbar t x) * hrsKv (nltAl q) t x q :=
    mul_pos_of_neg_of_neg (by linarith) hKv
  have p2 : 0 ≤ (nsrLp q - nltLbar q) * hrsKL (nltAl q) t x q :=
    mul_nonneg_of_nonpos_of_nonpos (by linarith) hKL
  have p3 : 0 ≤ ((k + 1) / 2 - (2 * t + x)) * hrsKk t x q :=
    mul_nonneg_of_nonpos_of_nonpos (by linarith) hKk
  have hK : 0 < hrsK (nltAl q) t x ((k + 1) / 2) q (hrlVL t x) (nsrLp q) := by linarith
  have e := hrs_comb_sub_k (nltAl q) (nltM t x q) t x q (hrlVL t x) (nsrLp q) (nsrFl t x q) k 1
  have : 0 ≤ (k - 1) * hrsK (nltAl q) t x ((k + 1) / 2) q (hrlVL t x) (nsrLp q) :=
    mul_nonneg (by linarith) hK.le
  linarith

end SmoothedOctagon
