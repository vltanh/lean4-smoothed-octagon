module

public import SmoothedOctagon.Exclusion.Mixed.Nonshort.Forward.ResidualAffine
public import SmoothedOctagon.Exclusion.Mixed.Nonshort.Forward.Secant

/-!
# Case M2, forward successor: the high-ratio residual increases in the shape

On the high-ratio large-gap domain (`3/8 ≤ t < 2/5`, `j = 2t + x - 1 ≥ 1/30`, `7x < 12h`, `1 ≤ q`,
`q(1 + 2j) ≤ 1 + x`) the combined residual `nsfComb 4 1 … (nsfVG t x) (nsrLp q) (nsrFl t x q)`
increases in the shape `k` on `[1, 1 + j]`. The caller `nsf_LGB_core` then needs only its lower
shape endpoint `k = 29t²/4`.

The residual is quadratic in `k`, so `F(k) - F(k₀) = (k - k₀) ∂_kF((k + k₀)/2)` exactly
(`hrs_comb_sub_k`). The shape derivative `∂_kF = hrsK` is affine in `v`, `L` and `k`
(`hrs_K_dec`); its `v`-slope is negative (`hrs_Kv_neg`), its `L`-slope and `k`-slope are
nonpositive, and `v_G < U(t)`, `L₊ ≤ q - 1` (`hrs_VG_lt_U`, `hrs_Lp_le`). At `v = U(t)`,
`L = q - 1`, `k = 1 + j` it equals `2tq²(d₀ + d₁y + d₂y² + d₃y³)`, `y = q - 1` (`hrs_K_end`, via
the four coefficient identities `hrs_d_eq`), which is positive (`hrs_cubic_pos`).

The bounds `Je² ≤ 17/16`, `(qJ - pW)/x ≤ 41/24` that the caller already has (`nsf_LG_J`,
`nsf_LG_WD`, passed as hypotheses) suffice for the sign of the `v`-slope, and the derivative is
integrated through the exact midpoint identity of a quadratic.

## Main API

* `hrsTk`, `hrsK`: `∂_k` of the transport brace and of `nsfComb`; `hrs_comb_sub_k`.
* `hrsKv`, `hrsKL`, `hrsKk`, `hrs_K_dec`; `hrs_K_end`: the endpoint value.
* `hrs_shape_lt`: **`nsfComb(29t²/4) < nsfComb(k)`** for `29t²/4 < k < 2t + x` on the high-ratio
  large-gap domain (given the caller's bounds `Je² ≤ 17/16`, `qJ - pW ≤ 41x/24`).
-/

@[expose] public section

namespace SmoothedOctagon

/-- `∂_k` of the transport brace `3tE₀² - 4tvW⁴ + 4q²W²(tH_U + 2tvY) - 4q⁴tB²w_U`. -/
noncomputable def hrsTk (t x k q v : ℝ) : ℝ :=
  6 * t * q ^ (2 : ℕ) * nsfE0 t x k q + 4 * q ^ (2 : ℕ) * (1 + x) ^ (2 : ℕ) * (v - 1 + t ^ (2 : ℕ))
    - 4 * q ^ (4 : ℕ) * (t * (2 * k - t) + (v - 1 + t ^ (2 : ℕ)) * (x * (x + 2)))

/-- **The shape derivative** `∂_k nsfComb α M` (independent of `M` and `F`). -/
noncomputable def hrsK (α t x k q v L : ℝ) : ℝ :=
  4 * q * ((α + 1) * (1 + x) ^ (2 : ℕ) - (t + x * (x + 2)) * q ^ (2 : ℕ)) * nsrA t x q v L
    + (q * (t + x * (x + 2)) - (t + x) * (1 + x)) * hrsTk t x k q v

/-- The `v`-coefficient of `hrsK`. -/
noncomputable def hrsKv (α t x q : ℝ) : ℝ :=
  4 * q * ((α + 1) * (1 + x) ^ (2 : ℕ) - (t + x * (x + 2)) * q ^ (2 : ℕ))
      * (x * (1 - t) * (1 + x) * q - x * (x + 2) * q ^ (2 : ℕ))
    + (q * (t + x * (x + 2)) - (t + x) * (1 + x))
      * (4 * q ^ (2 : ℕ) * (1 + x) ^ (2 : ℕ) - 4 * q ^ (4 : ℕ) * (x * (x + 2)))

/-- The `L`-coefficient of `hrsK`. -/
noncomputable def hrsKL (α t x q : ℝ) : ℝ :=
  4 * q * ((α + 1) * (1 + x) ^ (2 : ℕ) - (t + x * (x + 2)) * q ^ (2 : ℕ))
    * (-(t * (t + x) * (1 + x) * q))

/-- The `k`-coefficient of `hrsK`: `-2tq⁴(qJ - pW)`. -/
noncomputable def hrsKk (t x q : ℝ) : ℝ :=
  (q * (t + x * (x + 2)) - (t + x) * (1 + x)) * (-(2 * t * q ^ (4 : ℕ)))

/-- **The exact midpoint identity** of the quadratic `k ↦ nsfComb`. -/
theorem hrs_comb_sub_k (α M t x q v L F k k₀ : ℝ) :
    nsfComb α M t x k q v L F - nsfComb α M t x k₀ q v L F =
      (k - k₀) * hrsK α t x ((k + k₀) / 2) q v L := by
  have e2 : nsfTP t x k q v - nsfTP t x k₀ q v =
      (k - k₀) * ((q * (t + x * (x + 2)) - (t + x) * (1 + x)) * hrsTk t x ((k + k₀) / 2) q v) := by
    unfold nsfTP hrsTk nsfKt nsfHt nsfE0
    generalize q * (t + x * (x + 2)) - (t + x) * (1 + x) = D
    ring
  unfold nsfComb hrsK
  rw [nsrN_sub_k t x k k₀ q v L]
  linear_combination e2

/-- `hrsK` is affine in `v`, `L` and `k`. -/
theorem hrs_K_dec (α t x k k' q v v' L L' : ℝ) :
    hrsK α t x k q v L = hrsK α t x k' q v' L' + (v - v') * hrsKv α t x q
      + (L - L') * hrsKL α t x q + (k - k') * hrsKk t x q := by
  unfold hrsK hrsKv hrsKL hrsKk hrsTk nsrA nsfE0
  ring

/-! ### The endpoint derivative

At `v = U(t)`, `L = q - 1`, `k = 1 + j` and with `y = q - 1`: `nsrA = tq(A₀ + A₁y)`,
`hrsTk = 2tq²(b₀ + b₁y + b₂y²)`, `5W² - Jq² = e₀ + e₁y + e₂y²` and `qJ - pW = r₀ + r₁y`. -/

/-- The coefficient `A₀` of `nsrA` at the endpoint. -/
noncomputable def hrsA0 (t x : ℝ) : ℝ := t * x ^ (2 : ℕ) - t ^ (2 : ℕ) * x ^ (2 : ℕ)
/-- The coefficient `A₁` of `nsrA` at the endpoint. -/
noncomputable def hrsA1 (t x : ℝ) : ℝ := 2 * x ^ (2 : ℕ) + x - 2 * t * x ^ (2 : ℕ) - t * x
/-- The coefficient `b₀` of `hrsTk` at the endpoint. -/
noncomputable def hrsb0 (t x : ℝ) : ℝ := 1 - 2 * t - x
/-- The coefficient `b₁` of `hrsTk` at the endpoint. -/
noncomputable def hrsb1 (t x : ℝ) : ℝ := -8 * t * x ^ (2 : ℕ) - 10 * t * x - 6 * t + 4 * x ^ (2 : ℕ)
/-- The coefficient `b₂` of `hrsTk` at the endpoint. -/
noncomputable def hrsb2 (t x : ℝ) : ℝ := 5 * x ^ (2 : ℕ) + 3 * x - 4 * t * x ^ (2 : ℕ) - 2 * t * x
/-- The coefficient `e₀` of `5W² - Jq²`. -/
noncomputable def hrse0 (t x : ℝ) : ℝ := 5 - t + 8 * x + 4 * x ^ (2 : ℕ)
/-- The coefficient `e₁` of `5W² - Jq²`. -/
noncomputable def hrse1 (t x : ℝ) : ℝ := -2 * t - 4 * x - 2 * x ^ (2 : ℕ)
/-- The coefficient `e₂` of `5W² - Jq²`. -/
noncomputable def hrse2 (t x : ℝ) : ℝ := -t - 2 * x - x ^ (2 : ℕ)
/-- The coefficient `r₀` of `qJ - pW`. -/
noncomputable def hrsr0 (t x : ℝ) : ℝ := x - t * x
/-- The coefficient `r₁` of `qJ - pW`. -/
noncomputable def hrsr1 (t x : ℝ) : ℝ := t + 2 * x + x ^ (2 : ℕ)

/-- The coefficient `d₀` of the endpoint cubic `d₀ + d₁y + d₂y² + d₃y³`. -/
noncomputable def hrsd0 (t x : ℝ) : ℝ :=
  x * (1 - t) * (1 - 2 * t + (-2 * t ^ (2 : ℕ) + 10 * t - 1) * x + 16 * t * x ^ (2 : ℕ)
    + 8 * t * x ^ (3 : ℕ))
/-- The coefficient `d₁` of the endpoint cubic. -/
noncomputable def hrsd1 (t x : ℝ) : ℝ :=
  t - 2 * t ^ (2 : ℕ) + (12 - 23 * t + 8 * t ^ (2 : ℕ)) * x
    + (35 - 52 * t + 10 * t ^ (2 : ℕ) + 4 * t ^ (3 : ℕ)) * x ^ (2 : ℕ)
    + (43 - 60 * t + 16 * t ^ (2 : ℕ)) * x ^ (3 : ℕ) + (16 - 20 * t + 4 * t ^ (2 : ℕ)) * x ^ (4 : ℕ)
/-- The coefficient `d₂` of the endpoint cubic. -/
noncomputable def hrsd2 (t x : ℝ) : ℝ :=
  -6 * t ^ (2 : ℕ) + (-16 * t - 6 * t ^ (2 : ℕ)) * x + (-5 - 27 * t + 2 * t ^ (3 : ℕ)) * x ^ (2 : ℕ)
    + (-7 - 19 * t + 8 * t ^ (2 : ℕ)) * x ^ (3 : ℕ) + (-4 - 2 * t + 2 * t ^ (2 : ℕ)) * x ^ (4 : ℕ)
/-- The coefficient `d₃` of the endpoint cubic. -/
noncomputable def hrsd3 (t x : ℝ) : ℝ := x * (1 + x) * (t + x ^ (2 : ℕ) + 2 * x)

/-- The four coefficient identities: `d₀, …, d₃` are the coefficients of
`2(e₀ + e₁y + e₂y²)(A₀ + A₁y) + (r₀ + r₁y)(b₀ + b₁y + b₂y²)`. -/
theorem hrs_d_eq (t x : ℝ) :
    hrsd0 t x = 2 * hrse0 t x * hrsA0 t x + hrsr0 t x * hrsb0 t x ∧
    hrsd1 t x = 2 * (hrse0 t x * hrsA1 t x + hrse1 t x * hrsA0 t x) + hrsr0 t x * hrsb1 t x
      + hrsr1 t x * hrsb0 t x ∧
    hrsd2 t x = 2 * (hrse1 t x * hrsA1 t x + hrse2 t x * hrsA0 t x) + hrsr0 t x * hrsb2 t x
      + hrsr1 t x * hrsb1 t x ∧
    hrsd3 t x = 2 * hrse2 t x * hrsA1 t x + hrsr1 t x * hrsb2 t x := by
  unfold hrsd0 hrsd1 hrsd2 hrsd3 hrse0 hrse1 hrse2 hrsA0 hrsA1 hrsr0 hrsr1 hrsb0 hrsb1 hrsb2
  refine ⟨?_, ?_, ?_, ?_⟩ <;> ring

/-- **The endpoint derivative**: at `v = U(t)`, `L = q - 1`, `k = 1 + j`,
`∂_kF = 2tq²(d₀ + d₁y + d₂y² + d₃y³)`, `y = q - 1`. -/
theorem hrs_K_end (t x q : ℝ) :
    hrsK 4 t x (2 * t + x) q (1 - t + t ^ (2 : ℕ)) (q - 1) =
      2 * t * q ^ (2 : ℕ) * (hrsd0 t x + hrsd1 t x * (q - 1) + hrsd2 t x * (q - 1) ^ (2 : ℕ)
        + hrsd3 t x * (q - 1) ^ (3 : ℕ)) := by
  have eN : nsrA t x q (1 - t + t ^ (2 : ℕ)) (q - 1) = t * q * (hrsA0 t x + hrsA1 t x * (q - 1)) := by
    unfold nsrA hrsA0 hrsA1; ring
  have eT : hrsTk t x (2 * t + x) q (1 - t + t ^ (2 : ℕ)) =
      2 * t * q ^ (2 : ℕ) * (hrsb0 t x + hrsb1 t x * (q - 1) + hrsb2 t x * (q - 1) ^ (2 : ℕ)) := by
    unfold hrsTk nsfE0 hrsb0 hrsb1 hrsb2; ring
  have eE : (4 + 1) * (1 + x) ^ (2 : ℕ) - (t + x * (x + 2)) * q ^ (2 : ℕ) =
      hrse0 t x + hrse1 t x * (q - 1) + hrse2 t x * (q - 1) ^ (2 : ℕ) := by
    unfold hrse0 hrse1 hrse2; ring
  have eD : q * (t + x * (x + 2)) - (t + x) * (1 + x) = hrsr0 t x + hrsr1 t x * (q - 1) := by
    unfold hrsr0 hrsr1; ring
  obtain ⟨c0, c1, c2, c3⟩ := hrs_d_eq t x
  unfold hrsK
  rw [eN, eT, eE, eD]
  linear_combination (-(2 * t * q ^ (2 : ℕ))) *
    (c0 + (q - 1) * c1 + (q - 1) ^ (2 : ℕ) * c2 + (q - 1) ^ (3 : ℕ) * c3)

/-- **The endpoint cubic is positive** for `3/8 ≤ t ≤ 2/5`, `x ≥ 1/5`, `0 ≤ y ≤ 1/4`: `d₀ > 0`,
`d₃ ≥ 0`, `d₂ ≤ 0` and `4d₁ + d₂ > 0`. -/
theorem hrs_cubic_pos {t x y : ℝ} (ht0 : 3 / 8 ≤ t) (ht1 : t ≤ 2 / 5) (hx : 1 / 5 ≤ x)
    (hy0 : 0 ≤ y) (hy1 : y ≤ 1 / 4) :
    0 < hrsd0 t x + hrsd1 t x * y + hrsd2 t x * y ^ (2 : ℕ) + hrsd3 t x * y ^ (3 : ℕ) := by
  have hx0 : 0 < x := by linarith
  have ht : 0 < t := by linarith
  -- `d₀ > 0`, `d₃ ≥ 0`
  have a1 : 0 < 1 - t := by linarith
  have a2 : 0 < 1 - 2 * t := by linarith
  have a3 : 0 < -2 * t ^ (2 : ℕ) + 10 * t - 1 := by nlinarith
  have d0 : 0 < hrsd0 t x := by unfold hrsd0; positivity
  have d3 : 0 ≤ hrsd3 t x := by unfold hrsd3; positivity
  -- `d₂ ≤ 0`: each coefficient in `x` is negative
  have b1 : 0 < 5 + 27 * t - 2 * t ^ (3 : ℕ) := by nlinarith
  have b2 : 0 < 7 + 19 * t - 8 * t ^ (2 : ℕ) := by nlinarith
  have b3 : 0 < 4 + 2 * t - 2 * t ^ (2 : ℕ) := by nlinarith
  have d2 : hrsd2 t x ≤ 0 := by
    have : 0 ≤ 6 * t ^ (2 : ℕ) + (16 * t + 6 * t ^ (2 : ℕ)) * x
        + (5 + 27 * t - 2 * t ^ (3 : ℕ)) * x ^ (2 : ℕ) + (7 + 19 * t - 8 * t ^ (2 : ℕ)) * x ^ (3 : ℕ)
        + (4 + 2 * t - 2 * t ^ (2 : ℕ)) * x ^ (4 : ℕ) := by positivity
    unfold hrsd2; linarith
  -- `4d₁ + d₂ > 0`
  have c0 : 0 ≤ 4 * t - 14 * t ^ (2 : ℕ) + 16 / 25 := by nlinarith
  have c1 : 0 ≤ (48 - 108 * t + 26 * t ^ (2 : ℕ) - 224 / 25) * x :=
    mul_nonneg (by nlinarith) hx0.le
  have c2 : 0 ≤ (135 - 235 * t + 40 * t ^ (2 : ℕ) + 18 * t ^ (3 : ℕ)) * x ^ (2 : ℕ) :=
    mul_nonneg (by nlinarith) (by positivity)
  have c3 : 0 ≤ (165 - 259 * t + 72 * t ^ (2 : ℕ)) * x ^ (3 : ℕ) :=
    mul_nonneg (by nlinarith) (by positivity)
  have c4 : 0 ≤ (60 - 82 * t + 18 * t ^ (2 : ℕ)) * x ^ (4 : ℕ) :=
    mul_nonneg (by nlinarith) (by positivity)
  have d14 : 0 < 4 * hrsd1 t x + hrsd2 t x := by unfold hrsd1 hrsd2; nlinarith
  -- `d₁ + d₂y ≥ d₁ + d₂/4 > 0`
  have e1 : hrsd2 t x / 4 ≤ hrsd2 t x * y := by nlinarith
  have e2 : 0 ≤ y * (hrsd1 t x + hrsd2 t x * y) := mul_nonneg hy0 (by linarith)
  have e3 : 0 ≤ hrsd3 t x * y ^ (3 : ℕ) := mul_nonneg d3 (by positivity)
  nlinarith

/-! ### Signs of the slopes -/

/-- `v_G < U(t)` on the high-ratio large-gap domain. -/
theorem hrs_VG_lt_U {t x : ℝ} (ht0 : 3 / 8 ≤ t) (ht1 : t ≤ 2 / 5) (hx : 1 / 5 ≤ x)
    (hjh : 7 * x < 12 * (1 - 2 * t)) : nsfVG t x < 1 - t + t ^ (2 : ℕ) := by
  have hx0 : 0 < x := by linarith
  have hR : 0 < x ^ (2 : ℕ) + 10 * x + 15 := by positivity
  have hW : 0 < 1 + x := by linarith
  have e : 1 - t + t ^ (2 : ℕ) - nsfVG t x = (1 - t) * x *
      (12 * (x ^ (2 : ℕ) + 10 * x + 15) * (1 - t * (1 + x)) - (90 - 19 * x ^ (2 : ℕ)))
        / (12 * (x ^ (2 : ℕ) + 10 * x + 15) * (1 + x) ^ (2 : ℕ)) := by
    unfold nsfVG; field_simp; ring
  -- `tW ≤ 361/672 < 11/20`
  have htw : t * (1 + x) ≤ 11 / 20 := by
    have : t * x ≤ t * (12 * (1 - 2 * t) / 7) := mul_le_mul_of_nonneg_left (by linarith) (by linarith)
    nlinarith
  have hN : 0 < 12 * (x ^ (2 : ℕ) + 10 * x + 15) * (1 - t * (1 + x)) - (90 - 19 * x ^ (2 : ℕ)) := by
    have : 0 ≤ (x ^ (2 : ℕ) + 10 * x + 15) * (11 / 20 - t * (1 + x)) :=
      mul_nonneg hR.le (by linarith)
    nlinarith
  have : 0 < 1 - t + t ^ (2 : ℕ) - nsfVG t x := by
    rw [e]; apply div_pos (mul_pos (mul_pos (by linarith) hx0) hN); positivity
  linarith

/-- `L₊(q) ≤ q - 1` for `q ≥ 1`. -/
theorem hrs_Lp_le {q : ℝ} (hq : 1 ≤ q) : nsrLp q ≤ q - 1 := by
  have hq0 : 0 < q := by linarith
  have e : q - 1 - nsrLp q = (q - 1) ^ (2 : ℕ) * (5 * q + 1) / (6 * q * (q + 1)) := by
    unfold nsrLp; field_simp; ring
  have : 0 ≤ q - 1 - nsrLp q := by rw [e]; positivity
  linarith

/-- **The `v`-slope of the shape derivative is negative**, given `Je² ≤ 17/16` and
`qJ - pW ≤ 41x/24`. -/
theorem hrs_Kv_neg {t x q : ℝ} (ht0 : 1 / 3 ≤ t) (ht1 : t ≤ 2 / 5) (hj : 1 / 30 ≤ 2 * t + x - 1)
    (hq : 1 ≤ q)
    (hJ : (t + x * (x + 2)) * q ^ 2 ≤ 17 / 16 * (1 + x) ^ 2)
    (hWD : q * (t + x * (x + 2)) - (t + x) * (1 + x) ≤ 41 / 24 * x) : hrsKv 4 t x q < 0 := by
  have hx : 0 < x := by linarith
  have hW : 0 < 1 + x := by linarith
  have hq0 : 0 < q := by linarith
  have hD0 : 0 ≤ q * (t + x * (x + 2)) - (t + x) * (1 + x) := by
    have h1 : (t + x) * (1 + x) ≤ t + x * (x + 2) := by nlinarith
    have h2 := mul_le_mul_of_nonneg_right hq (by positivity : (0 : ℝ) ≤ t + x * (x + 2))
    linarith
  -- `N_kv = -xq I`, `I = (x + 2)q - (1 - t)(1 + x) ≥ 1`
  have hI : 1 ≤ (x + 2) * q - (1 - t) * (1 + x) := by nlinarith
  have eI : x * (1 - t) * (1 + x) * q - x * (x + 2) * q ^ (2 : ℕ) =
      -(x * q) * ((x + 2) * q - (1 - t) * (1 + x)) := by ring
  have hA : 63 / 16 * (1 + x) ^ (2 : ℕ) ≤ (4 + 1) * (1 + x) ^ (2 : ℕ) - (t + x * (x + 2)) * q ^ (2 : ℕ) := by
    linarith
  have hxq : 0 < x * q := mul_pos hx hq0
  have e1 : 4 * q * ((4 + 1) * (1 + x) ^ (2 : ℕ) - (t + x * (x + 2)) * q ^ (2 : ℕ))
      * (x * (1 - t) * (1 + x) * q - x * (x + 2) * q ^ (2 : ℕ))
        ≤ 4 * q * (63 / 16 * (1 + x) ^ (2 : ℕ)) * (-(x * q)) := by
    rw [eI]
    have m1 : -(x * q) * ((x + 2) * q - (1 - t) * (1 + x)) ≤ -(x * q) := by nlinarith
    have m2 : 0 ≤ 4 * q * (63 / 16 * (1 + x) ^ (2 : ℕ)) := by positivity
    have m3 := mul_le_mul_of_nonneg_left hA (by positivity : (0 : ℝ) ≤ 4 * q)
    have m4 := mul_le_mul_of_nonneg_left m1
      (by nlinarith : (0 : ℝ) ≤ 4 * q * ((4 + 1) * (1 + x) ^ (2 : ℕ) - (t + x * (x + 2)) * q ^ (2 : ℕ)))
    have m5 := mul_le_mul_of_nonpos_right m3 (by linarith : -(x * q) ≤ 0)
    nlinarith
  have e2 : (q * (t + x * (x + 2)) - (t + x) * (1 + x))
      * (4 * q ^ (2 : ℕ) * (1 + x) ^ (2 : ℕ) - 4 * q ^ (4 : ℕ) * (x * (x + 2)))
        ≤ 41 / 24 * x * (4 * q ^ (2 : ℕ) * (1 + x) ^ (2 : ℕ)) := by
    have m1 : 4 * q ^ (2 : ℕ) * (1 + x) ^ (2 : ℕ) - 4 * q ^ (4 : ℕ) * (x * (x + 2))
        ≤ 4 * q ^ (2 : ℕ) * (1 + x) ^ (2 : ℕ) := by
      have : 0 ≤ 4 * q ^ (4 : ℕ) * (x * (x + 2)) := by positivity
      linarith
    have m2 := mul_le_mul_of_nonneg_left m1 hD0
    have m3 := mul_le_mul_of_nonneg_right hWD (by positivity : (0 : ℝ) ≤ 4 * q ^ (2 : ℕ) * (1 + x) ^ (2 : ℕ))
    linarith
  have : 0 < x * q ^ (2 : ℕ) * (1 + x) ^ (2 : ℕ) := by positivity
  unfold hrsKv
  nlinarith

/-- **The shape increases the high-ratio residual** (the shape derivative integrated on
`[29t²/4, k]` by the midpoint identity): on the
high-ratio large-gap domain, `nsfComb 4 1` at the shape `k` exceeds its value at `k₀ = 29t²/4`. -/
theorem hrs_shape_lt {t x k q : ℝ} (ht0 : 3 / 8 ≤ t) (ht1 : t < 2 / 5) (hj : 1 / 30 ≤ 2 * t + x - 1)
    (hjh : 7 * x < 12 * (1 - 2 * t)) (hks : 29 / 4 * t ^ (2 : ℕ) < k) (hko : k < 2 * t + x)
    (hq : 1 ≤ q) (hqs : q * (4 * t + 2 * x - 1) ≤ 1 + x)
    (hJ : (t + x * (x + 2)) * q ^ 2 ≤ 17 / 16 * (1 + x) ^ 2)
    (hWD : q * (t + x * (x + 2)) - (t + x) * (1 + x) ≤ 41 / 24 * x) :
    nsfComb 4 1 t x (29 / 4 * t ^ (2 : ℕ)) q (nsfVG t x) (nsrLp q) (nsrFl t x q) <
      nsfComb 4 1 t x k q (nsfVG t x) (nsrLp q) (nsrFl t x q) := by
  have hx : 1 / 5 ≤ x := by linarith
  have hx0 : 0 < x := by linarith
  have hq0 : 0 < q := by linarith
  have ht : 0 < t := by linarith
  -- `y = q - 1 ≤ h - j ≤ 1/4`
  have hy1 : q - 1 ≤ 1 / 4 := by
    have : (q - 1) * (1 + 2 * (2 * t + x - 1)) ≤ (1 - 2 * t) - (2 * t + x - 1) := by nlinarith
    nlinarith
  have hD0 : 0 ≤ q * (t + x * (x + 2)) - (t + x) * (1 + x) := by
    have h1 : (t + x) * (1 + x) ≤ t + x * (x + 2) := by nlinarith
    have h2 := mul_le_mul_of_nonneg_right hq (by positivity : (0 : ℝ) ≤ t + x * (x + 2))
    linarith
  -- the midpoint derivative is positive
  set m := (k + 29 / 4 * t ^ (2 : ℕ)) / 2 with hm
  have hmk : m ≤ 2 * t + x := by rw [hm]; linarith
  have hdec := hrs_K_dec 4 t x m (2 * t + x) q (nsfVG t x) (1 - t + t ^ (2 : ℕ)) (nsrLp q) (q - 1)
  rw [hrs_K_end] at hdec
  have p0 : 0 < 2 * t * q ^ (2 : ℕ) * (hrsd0 t x + hrsd1 t x * (q - 1)
      + hrsd2 t x * (q - 1) ^ (2 : ℕ) + hrsd3 t x * (q - 1) ^ (3 : ℕ)) :=
    mul_pos (by positivity) (hrs_cubic_pos ht0 ht1.le hx (by linarith) hy1)
  have p1 : 0 < (nsfVG t x - (1 - t + t ^ (2 : ℕ))) * hrsKv 4 t x q :=
    mul_pos_of_neg_of_neg (by linarith [hrs_VG_lt_U ht0 ht1.le hx hjh])
      (hrs_Kv_neg (by linarith) ht1.le hj hq hJ hWD)
  have p2 : 0 ≤ (nsrLp q - (q - 1)) * hrsKL 4 t x q := by
    apply mul_nonneg_of_nonpos_of_nonpos (by linarith [hrs_Lp_le hq])
    unfold hrsKL
    apply mul_nonpos_of_nonneg_of_nonpos
    · apply mul_nonneg (by positivity); linarith [sq_nonneg (1 + x)]
    · have : 0 ≤ t * (t + x) * (1 + x) * q := by positivity
      linarith
  have p3 : 0 ≤ (m - (2 * t + x)) * hrsKk t x q := by
    apply mul_nonneg_of_nonpos_of_nonpos (by linarith)
    unfold hrsKk
    apply mul_nonpos_of_nonneg_of_nonpos hD0
    have : 0 ≤ 2 * t * q ^ (4 : ℕ) := by positivity
    linarith
  have hK : 0 < hrsK 4 t x m q (nsfVG t x) (nsrLp q) := by linarith
  have e := hrs_comb_sub_k 4 1 t x q (nsfVG t x) (nsrLp q) (nsrFl t x q) k (29 / 4 * t ^ (2 : ℕ))
  rw [← hm] at e
  have : 0 < (k - 29 / 4 * t ^ (2 : ℕ)) * hrsK 4 t x m q (nsfVG t x) (nsrLp q) :=
    mul_pos (by linarith) hK
  linarith

end SmoothedOctagon
