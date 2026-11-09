module

public import SmoothedOctagon.Exclusion.Mixed.Nonshort.Forward.LowRatio
public import SmoothedOctagon.Exclusion.Mixed.Nonshort.Forward.HighRatio.Shape
public import SmoothedOctagon.Exclusion.Mixed.Nonshort.Forward.HighRatio.LowerShape
public import SmoothedOctagon.Exclusion.Mixed.Nonshort.Forward.LowT.UnitShape
public import SmoothedOctagon.Exclusion.Mixed.Nonshort.Forward.LowT.Shape

/-!
# Case M2, forward successor: the gap is smaller than one thirtieth

An actual forward window with `t ≥ 1/3` has `j = 2t + x - 1 < 1/30`.

Suppose `j ≥ 1/30`. The integral derivative floor gives `x < 3/5` and `j < 5h/7` (`h = 1 - 2t`).
* `1/3 ≤ t ≤ 3/8`: the multipliers `a = 7/2 - 10(q - 1) ≥ 11/16`,
  `m = 8j + 8(q - 1) - 1/6 ≥ 1/10` (`nltAl`, `nltM`, `nsf_LGN_mult`) make the combined residual
  `aN + C_*(3/4 - 𝒯_*) + m(F - v)` negative at the actual window (`nsf_window_comb`); its
  `v`-coefficient is negative (`nsf_LGN_Cv`, in the two cases `a ≥ 2` and `a < 2`), so
  `v ↦ v_G ≤ V_L`, `log q ↦ L₊`, `F ↦ F_ℓ` keep it negative; but it increases in the shape
  (`nlt_shape_ge`, `Nonshort/Forward/LowT/Shape`) and is positive at `k = 1` (`nlt_unit_pos`,
  `Nonshort/Forward/LowT/UnitShape`).
* `3/8 ≤ t < 2/5`: the same with `α = 4`, `M = 1`; the residual increases in the shape
  (`hrs_shape_lt`, `Nonshort/Forward/HighRatio/Shape`), and it is positive at the lower endpoint
  `k = 29t²/4` (`hrl_lower_pos`, `Nonshort/Forward/HighRatio/LowerShape`).

For `t ≤ 3/8` the actual window supplies the necessary condition with the multipliers `a`, `m`
through the general `nsf_window_comb`.

## Main API

* `nsf_LG_J`, `nsf_LG_WD`, `nsf_LG_W2Dek`: the bounds `Je² ≤ 17/16`, `WD/x ≤ 41/24` and
  `W²Dek < 3h` on the large-gap domain.
* `nsf_LGN_mult`, `nsf_LGN_Cv`, `nsf_LGN_core`, `nsf_LGB_core`; `nsf_small_gap_j`: **`j < 1/30`** for an
  actual forward window.
-/

@[expose] public section

namespace SmoothedOctagon

/-- `Je² ≤ 17/16` on the large-gap domain. -/
theorem nsf_LG_J {t x q : ℝ} (ht0 : 1 / 3 ≤ t) (ht1 : t ≤ 2 / 5) (hj : 1 / 30 ≤ 2 * t + x - 1)
    (hq : 0 ≤ q) (hqs : q * (4 * t + 2 * x - 1) ≤ 1 + x) :
    (t + x * (x + 2)) * q ^ 2 ≤ 17 / 16 * (1 + x) ^ 2 := by
  set j := 2 * t + x - 1 with hjdef
  have hx : x = 1 - 2 * t + j := by rw [hjdef]; ring
  have hJ : t + x * (x + 2) ≤ 10 / 9 + 8 / 3 * j + j ^ 2 := by
    rw [hx]; nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ t - 1 / 3)
      (by linarith : (0 : ℝ) ≤ 13 / 3 + 4 * j - 4 * (t - 1 / 3))]
  have h2 : 10 / 9 + 8 / 3 * j + j ^ 2 ≤ 17 / 16 * (1 + 2 * j) ^ 2 := by nlinarith
  have h1 : 4 * t + 2 * x - 1 = 1 + 2 * j := by rw [hjdef]; ring
  rw [h1] at hqs
  have hq2 : (q * (1 + 2 * j)) ^ 2 ≤ (1 + x) ^ 2 := by
    apply pow_le_pow_left₀ (by positivity) hqs
  have e1 : (t + x * (x + 2)) * q ^ 2 ≤ 17 / 16 * (1 + 2 * j) ^ 2 * q ^ 2 :=
    mul_le_mul_of_nonneg_right (hJ.trans h2) (sq_nonneg q)
  nlinarith

/-- `(qJ - pW)(1 + 2j) ≤ W(hW - j²)` from the swap bound (`J - p(1 + 2j) = hW - j²`). -/
theorem nsf_LG_D1 {t x q : ℝ} (_hq : 0 ≤ q) (hJ0 : 0 ≤ t + x * (x + 2))
    (hqs : q * (4 * t + 2 * x - 1) ≤ 1 + x) :
    (q * (t + x * (x + 2)) - (t + x) * (1 + x)) * (4 * t + 2 * x - 1) ≤
      (1 + x) * ((1 - 2 * t) * (1 + x) - (2 * t + x - 1) ^ 2) := by
  have := mul_le_mul_of_nonneg_right hqs hJ0
  have e : (1 + x) * ((1 - 2 * t) * (1 + x) - (2 * t + x - 1) ^ 2) =
      (1 + x) * (t + x * (x + 2)) - (t + x) * (1 + x) * (4 * t + 2 * x - 1) := by ring
  rw [e]
  nlinarith

/-- `WD/x ≤ 41/24`, i.e. `qJ - pW ≤ (41/24)x`, on the large-gap domain. -/
theorem nsf_LG_WD {t x q : ℝ} (ht0 : 1 / 3 ≤ t) (ht1 : t ≤ 2 / 5) (hj : 1 / 30 ≤ 2 * t + x - 1)
    (hq : 0 ≤ q) (hqs : q * (4 * t + 2 * x - 1) ≤ 1 + x) :
    q * (t + x * (x + 2)) - (t + x) * (1 + x) ≤ 41 / 24 * x := by
  have hx : 0 < x := by linarith
  have hJ0 : 0 ≤ t + x * (x + 2) := by positivity
  have hW : 0 < 1 + x := by linarith
  have hj2 : 0 < 4 * t + 2 * x - 1 := by linarith
  have e1 := nsf_LG_D1 hq hJ0 hqs
  have e3 : (1 - 2 * t) * (1 + x) - (2 * t + x - 1) ^ 2 ≤ x * (2 - 2 * t) := by
    nlinarith [sq_nonneg (2 * t + x - 1)]
  have e4 : (1 + x) * (2 - 2 * t) ≤ 41 / 24 * (4 * t + 2 * x - 1) := by
    have h1 : (1 + x) * (2 - 2 * t) ≤ (4 / 3 + (2 * t + x - 1)) * (4 / 3) :=
      mul_le_mul (by linarith) (by linarith) (by linarith) (by linarith)
    linarith
  have e5 : (1 + x) * ((1 - 2 * t) * (1 + x) - (2 * t + x - 1) ^ 2) ≤ x * (41 / 24 * (4 * t + 2 * x - 1)) := by
    have h1 := mul_le_mul_of_nonneg_left e3 hW.le
    have h2 := mul_le_mul_of_nonneg_left e4 hx.le
    nlinarith
  have e6 : (q * (t + x * (x + 2)) - (t + x) * (1 + x)) * (4 * t + 2 * x - 1) ≤
      41 / 24 * x * (4 * t + 2 * x - 1) := by linarith
  exact le_of_mul_le_mul_right e6 hj2

/-- `(4/3 + j)³(1 + j) < 3(1 + 2j)²` for `0 ≤ j < 1/4`. -/
theorem nsf_LG_cubic {j : ℝ} (hj0 : 0 ≤ j) (hj4 : j < 1 / 4) :
    (4 / 3 + j) ^ 3 * (1 + j) < 3 * (1 + 2 * j) ^ 2 := by
  have h1 : 0 < 8 / 3 - 5 * j - j ^ 2 := by nlinarith
  have h2 : 0 ≤ (8 / 3 - 5 * j - j ^ 2) * j ^ 2 := mul_nonneg h1.le (sq_nonneg j)
  have e : 3 * (1 + 2 * j) ^ 2 - (4 / 3 + j) ^ 3 * (1 + j) =
      17 / 27 + 116 / 27 * j + (8 / 3 - 5 * j - j ^ 2) * j ^ 2 := by ring
  nlinarith

/-- `W²Dek < 3h`, i.e. `qk(qJ - pW) < 3h`, on the large-gap domain with `j < 1/4`. -/
theorem nsf_LG_W2Dek {t x k q : ℝ} (ht0 : 1 / 3 ≤ t) (ht1 : t ≤ 2 / 5) (hj : 1 / 30 ≤ 2 * t + x - 1)
    (hj4 : 2 * t + x - 1 < 1 / 4) (hk0 : 0 ≤ k) (hk : k ≤ 2 * t + x) (hq : 0 ≤ q)
    (hqs : q * (4 * t + 2 * x - 1) ≤ 1 + x)
    (hD : (t + x) * (1 + x) ≤ q * (t + x * (x + 2))) :
    q * k * (q * (t + x * (x + 2)) - (t + x) * (1 + x)) < 3 * (1 - 2 * t) := by
  have hx : 0 < x := by linarith
  have hJ0 : 0 ≤ t + x * (x + 2) := by positivity
  have hW : 0 < 1 + x := by linarith
  have hh : 0 < 1 - 2 * t := by linarith
  have hj2 : 0 < 4 * t + 2 * x - 1 := by linarith
  have hD0 : 0 ≤ q * (t + x * (x + 2)) - (t + x) * (1 + x) := by linarith
  -- `b = (qJ - pW)(1 + 2j) ≤ hW²`
  have hb : (q * (t + x * (x + 2)) - (t + x) * (1 + x)) * (4 * t + 2 * x - 1) ≤
      (1 - 2 * t) * (1 + x) ^ 2 := by
    have e1 := nsf_LG_D1 hq hJ0 hqs
    have : (1 + x) * ((1 - 2 * t) * (1 + x) - (2 * t + x - 1) ^ 2) ≤ (1 - 2 * t) * (1 + x) ^ 2 := by
      nlinarith [mul_nonneg hW.le (sq_nonneg (2 * t + x - 1))]
    linarith
  have m1 : (q * (4 * t + 2 * x - 1)) * k * ((q * (t + x * (x + 2)) - (t + x) * (1 + x)) * (4 * t + 2 * x - 1)) ≤
      (1 + x) * (2 * t + x) * ((1 - 2 * t) * (1 + x) ^ 2) := by
    apply mul_le_mul (mul_le_mul hqs hk hk0 hW.le) hb (by positivity) (by positivity)
  have hW43 : 1 + x ≤ 4 / 3 + (2 * t + x - 1) := by linarith
  have m2 : (1 + x) * (2 * t + x) * ((1 - 2 * t) * (1 + x) ^ 2) ≤
      (1 - 2 * t) * ((4 / 3 + (2 * t + x - 1)) ^ 3 * (2 * t + x)) := by
    have h3 : (1 + x) ^ 3 ≤ (4 / 3 + (2 * t + x - 1)) ^ 3 := pow_le_pow_left₀ hW.le hW43 3
    have h4 := mul_le_mul_of_nonneg_left h3 (by positivity : (0 : ℝ) ≤ (1 - 2 * t) * (2 * t + x))
    have e : (1 + x) * (2 * t + x) * ((1 - 2 * t) * (1 + x) ^ 2) = (1 - 2 * t) * (2 * t + x) * (1 + x) ^ 3 := by
      ring
    have e' : (1 - 2 * t) * ((4 / 3 + (2 * t + x - 1)) ^ 3 * (2 * t + x)) =
        (1 - 2 * t) * (2 * t + x) * (4 / 3 + (2 * t + x - 1)) ^ 3 := by ring
    rw [e, e']; exact h4
  have m3 := nsf_LG_cubic (j := 2 * t + x - 1) (by linarith) hj4
  have m3' : (1 - 2 * t) * ((4 / 3 + (2 * t + x - 1)) ^ 3 * (1 + (2 * t + x - 1))) <
      (1 - 2 * t) * (3 * (1 + 2 * (2 * t + x - 1)) ^ 2) := mul_lt_mul_of_pos_left m3 hh
  have e1 : (q * (4 * t + 2 * x - 1)) * k * ((q * (t + x * (x + 2)) - (t + x) * (1 + x)) * (4 * t + 2 * x - 1)) =
      (4 * t + 2 * x - 1) ^ 2 * (q * k * (q * (t + x * (x + 2)) - (t + x) * (1 + x))) := by ring
  have e2 : (1 - 2 * t) * ((4 / 3 + (2 * t + x - 1)) ^ 3 * (1 + (2 * t + x - 1))) =
      (1 - 2 * t) * ((4 / 3 + (2 * t + x - 1)) ^ 3 * (2 * t + x)) := by ring
  have e3 : (1 - 2 * t) * (3 * (1 + 2 * (2 * t + x - 1)) ^ 2) = (4 * t + 2 * x - 1) ^ 2 * (3 * (1 - 2 * t)) := by
    ring
  have m4 : (4 * t + 2 * x - 1) ^ 2 * (q * k * (q * (t + x * (x + 2)) - (t + x) * (1 + x))) <
      (4 * t + 2 * x - 1) ^ 2 * (3 * (1 - 2 * t)) := by
    rw [← e1, ← e3]; rw [e2] at m3'; linarith
  exact lt_of_mul_lt_mul_left m4 (by positivity)

/-- **The integral domain bounds**: if `t ≥ 1/3` and `t < T_G(x)`, then `x < 3/5` and `7x < 12h`. -/
theorem nsf_LG_dom {t x : ℝ} (ht0 : 1 / 3 ≤ t) (hx : 0 < x)
    (hTG : 12 * (x ^ 2 + 10 * x + 15) * t < 90 - 19 * x ^ 2) :
    x < 3 / 5 ∧ 7 * x < 12 * (1 - 2 * t) := by
  have hR : 0 < x ^ 2 + 10 * x + 15 := by positivity
  have hx35 : x < 3 / 5 := by
    by_contra h
    push Not at h
    nlinarith
  refine ⟨hx35, ?_⟩
  have : 90 - 19 * x ^ 2 < 12 * (x ^ 2 + 10 * x + 15) * (1 / 2 - 7 * x / 24) := by
    nlinarith [mul_pos hx (by nlinarith : (0 : ℝ) < 15 - 20 * x - 7 * x ^ 2)]
  have ht : t < 1 / 2 - 7 * x / 24 := by
    by_contra h; push Not at h
    nlinarith [mul_le_mul_of_nonneg_left h (by positivity : (0 : ℝ) ≤ 12 * (x ^ 2 + 10 * x + 15))]
  linarith

/-- **The low-`t` multipliers are positive**: `a = 7/2 - 10(q - 1) ≥ 11/16` and
`m = 8j + 8(q - 1) - 1/6 ≥ 1/10`, since `q - 1 ≤ 9/32`. -/
theorem nsf_LGN_mult {t x q : ℝ} (ht0 : 1 / 3 ≤ t) (hj : 1 / 30 ≤ 2 * t + x - 1) (hq : 1 ≤ q)
    (hqs : q * (4 * t + 2 * x - 1) ≤ 1 + x) : 11 / 16 ≤ nltAl q ∧ 1 / 10 ≤ nltM t x q := by
  have hy : (q - 1) * (4 * t + 2 * x - 1) ≤ 2 - 4 * t - x := by linarith
  have hy' : 16 / 15 * (q - 1) ≤ (q - 1) * (4 * t + 2 * x - 1) := by
    have : 16 / 15 ≤ 4 * t + 2 * x - 1 := by linarith
    nlinarith
  unfold nltAl nltM
  constructor <;> nlinarith

/-- **The `v`-coefficient is negative for the low-`t` multipliers**, in the two cases `a ≥ 2`
(with `WD/x ≤ 41/24`) and `a < 2` (with `m > 3h` and `W²Dek < 3h`). -/
theorem nsf_LGN_Cv {t x k q : ℝ} (ht0 : 1 / 3 ≤ t) (ht1 : t ≤ 3 / 8) (hj : 1 / 30 ≤ 2 * t + x - 1)
    (hj4 : 2 * t + x - 1 < 1 / 4) (hk1 : 1 ≤ k) (hk : k ≤ 2 * t + x) (hq : 1 ≤ q)
    (hqs : q * (4 * t + 2 * x - 1) ≤ 1 + x) :
    nsfCv (nltAl q) (nltM t x q) t x k q < 0 := by
  have hx : 0 < x := by linarith
  have hW : 0 < 1 + x := by linarith
  have hq0 : 0 < q := by linarith
  have hJ0 : 0 ≤ t + x * (x + 2) := by positivity
  have hD : (t + x) * (1 + x) ≤ q * (t + x * (x + 2)) := by
    have : (t + x) * (1 + x) ≤ t + x * (x + 2) := by nlinarith
    have := mul_le_mul_of_nonneg_right hq hJ0
    linarith
  obtain ⟨hα, hM⟩ := nsf_LGN_mult ht0 hj hq hqs
  have hJ := nsf_LG_J ht0 (by linarith) hj hq0.le hqs
  have hle := nsf_Cv_le (α := nltAl q) (M := nltM t x q) (t := t) (x := x) (k := k) (q := q)
    (by linarith) (by linarith) hD (by positivity)
  have hNv := nsf_Nv_le (t := t) (x := x) (k := k) (q := q) (by linarith) hx.le hq (by linarith)
  have hA : 0 < x * q * k := by positivity
  have hneg : 4 * q * (1 + x) ^ 2 * nsrNv t x k q < 0 := by
    apply mul_neg_of_pos_of_neg (by positivity); linarith
  have hMp : 0 < 4 * q * (1 + x) ^ 2 * nltM t x q := by
    have : 0 < nltM t x q := by linarith
    positivity
  rcases le_or_gt 2 (nltAl q) with h2 | h2
  · -- `a ≥ 2`
    have hWD := nsf_LG_WD ht0 (by linarith) hj hq0.le hqs
    have e1 : 4 * q * ((nltAl q + 1) * (1 + x) ^ 2 - (t + x * (x + 2)) * q ^ 2) * nsrNv t x k q ≤
        4 * q * (31 / 16 * (1 + x) ^ 2) * nsrNv t x k q := by
      apply mul_le_mul_of_nonpos_right _ (by linarith)
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      nlinarith
    have e2 : 4 * q ^ 2 * (1 + x) ^ 2 * k * (q * (t + x * (x + 2)) - (t + x) * (1 + x)) ≤
        4 * q * (1 + x) ^ 2 * (41 / 24) * (x * q * k) := by
      have : 0 ≤ 4 * q ^ 2 * (1 + x) ^ 2 * k := by positivity
      have := mul_le_mul_of_nonneg_left hWD this
      nlinarith
    have e3 : 4 * q * (1 + x) ^ 2 * (41 / 24) * (x * q * k) ≤
        4 * q * (1 + x) ^ 2 * (41 / 24) * (-nsrNv t x k q) :=
      mul_le_mul_of_nonneg_left (by linarith) (by positivity)
    nlinarith
  · -- `a < 2`: then `q - 1 > 3/20`, `m > 13/10 > 3h` and `qk(qJ - pW) < 3h`
    have hW2 := nsf_LG_W2Dek ht0 (by linarith) hj hj4 (by linarith) hk hq0.le hqs hD
    have hM3 : 3 * (1 - 2 * t) + 3 / 10 < nltM t x q := by
      unfold nltAl at h2; unfold nltM; linarith
    have e1 : 4 * q * ((nltAl q + 1) * (1 + x) ^ 2 - (t + x * (x + 2)) * q ^ 2) * nsrNv t x k q ≤ 0 := by
      apply mul_nonpos_of_nonneg_of_nonpos _ (by linarith)
      apply mul_nonneg (by positivity)
      nlinarith
    have e2 : 4 * q ^ 2 * (1 + x) ^ 2 * k * (q * (t + x * (x + 2)) - (t + x) * (1 + x)) ≤
        4 * q * (1 + x) ^ 2 * (3 * (1 - 2 * t)) := by
      have : 4 * q ^ 2 * (1 + x) ^ 2 * k * (q * (t + x * (x + 2)) - (t + x) * (1 + x)) =
          4 * q * (1 + x) ^ 2 * (q * k * (q * (t + x * (x + 2)) - (t + x) * (1 + x))) := by ring
      rw [this]
      exact mul_le_mul_of_nonneg_left hW2.le (by positivity)
    have : 4 * q * (1 + x) ^ 2 * (3 * (1 - 2 * t)) < 4 * q * (1 + x) ^ 2 * nltM t x q :=
      mul_lt_mul_of_pos_left (by linarith) (by positivity)
    nlinarith

/-- **The `v`-coefficient is negative for the constant multipliers `4`, `1`**. -/
theorem nsf_LGB_Cv {t x k q : ℝ} (ht0 : 1 / 3 ≤ t) (ht1 : t ≤ 2 / 5) (hj : 1 / 30 ≤ 2 * t + x - 1)
    (hk1 : 1 ≤ k) (hq : 1 ≤ q) (hqs : q * (4 * t + 2 * x - 1) ≤ 1 + x) :
    nsfCv 4 1 t x k q < 0 := by
  have hx : 0 < x := by linarith
  have hW : 0 < 1 + x := by linarith
  have hq0 : 0 < q := by linarith
  have hJ0 : 0 ≤ t + x * (x + 2) := by positivity
  have hD : (t + x) * (1 + x) ≤ q * (t + x * (x + 2)) := by
    have : (t + x) * (1 + x) ≤ t + x * (x + 2) := by nlinarith
    have := mul_le_mul_of_nonneg_right hq hJ0
    linarith
  have hJ := nsf_LG_J ht0 ht1 hj hq0.le hqs
  have hWD := nsf_LG_WD ht0 ht1 hj hq0.le hqs
  have hle := nsf_Cv_le (α := 4) (M := 1) (t := t) (x := x) (k := k) (q := q)
    (by linarith) (by linarith) hD (by positivity)
  have hNv := nsf_Nv_le (t := t) (x := x) (k := k) (q := q) (by linarith) hx.le hq (by linarith)
  have hA : 0 < x * q * k := by positivity
  have e1 : 4 * q * ((4 + 1) * (1 + x) ^ 2 - (t + x * (x + 2)) * q ^ 2) * nsrNv t x k q ≤
      4 * q * (63 / 16 * (1 + x) ^ 2) * nsrNv t x k q := by
    apply mul_le_mul_of_nonpos_right _ (by linarith)
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    nlinarith
  have e2 : 4 * q ^ 2 * (1 + x) ^ 2 * k * (q * (t + x * (x + 2)) - (t + x) * (1 + x)) ≤
      4 * q * (1 + x) ^ 2 * (41 / 24) * (x * q * k) := by
    have : 0 ≤ 4 * q ^ 2 * (1 + x) ^ 2 * k := by positivity
    have := mul_le_mul_of_nonneg_left hWD this
    nlinarith
  have e3 : 4 * q * (1 + x) ^ 2 * (41 / 24) * (x * q * k) ≤
      4 * q * (1 + x) ^ 2 * (41 / 24) * (-nsrNv t x k q) :=
    mul_le_mul_of_nonneg_left (by linarith) (by positivity)
  have hneg : 4 * q * (1 + x) ^ 2 * nsrNv t x k q < 0 := by
    apply mul_neg_of_pos_of_neg (by positivity); linarith
  nlinarith

/-- The rational substitution step: with a negative `v`-coefficient, a nonpositive `log q`
coefficient and `M ≥ 0`, the combined residual stays negative after `v ↦ v_G`, `log q ↦ L₊`,
`F_{p/W}(q) ↦ F_ℓ`. -/
theorem nsf_LG_subst {α M t x k q v : ℝ} (ht : 0 < t) (hx : 0 < x) (ht1 : t < 1) (hq : 1 < q) (hM : 0 ≤ M)
    (hv : v = nsrSecN t x) (hCv : nsfCv α M t x k q < 0) (hCL : nsfCL α t x k q ≤ 0)
    (hcomb : nsfComb α M t x k q v (Real.log q) (m2F ((t + x) / (1 + x)) q) < 0) :
    nsfComb α M t x k q (nsfVG t x) (nsrLp q) (nsrFl t x q) < 0 := by
  have hVG := nsf_secN_lt_VG hx ht1
  rw [← hv] at hVG
  have hFl := nsr_m2F_gt_Fl hq (by linarith : 0 < t + x) (by linarith : 0 < 1 + x)
  have hLp := nsr_log_lt_Lp hq
  have e1 := nsf_comb_sub_v α M t x k q (nsfVG t x) v (nsrLp q) (nsrFl t x q)
  have e2 := nsf_comb_sub_L α M t x k q v (nsrLp q) (Real.log q) (nsrFl t x q)
  have e3 := nsf_comb_sub_F α M t x k q v (Real.log q) (nsrFl t x q) (m2F ((t + x) / (1 + x)) q)
  have m1 : (nsfVG t x - v) * nsfCv α M t x k q < 0 := mul_neg_of_pos_of_neg (by linarith) hCv
  have m2 : (nsrLp q - Real.log q) * nsfCL α t x k q ≤ 0 := mul_nonpos_of_nonneg_of_nonpos (by linarith) hCL
  have m3 : (nsrFl t x q - m2F ((t + x) / (1 + x)) q) * (4 * q * (1 + x) ^ 2 * M) ≤ 0 := by
    apply mul_nonpos_of_nonpos_of_nonneg (by linarith)
    have : 0 < q := by linarith
    positivity
  linarith

/-- **The large-gap exclusion for `1/3 ≤ t ≤ 3/8`** with the low-`t` multipliers: the negative
combined residual of an actual window (premise `hcomb`, from `nsf_window_comb`) contradicts the
positive unit sign and the shape monotonicity. -/
theorem nsf_LGN_core {t x k q v : ℝ} (ht0 : 1 / 3 ≤ t) (ht1 : t ≤ 3 / 8) (hj : 1 / 30 ≤ 2 * t + x - 1)
    (hjh : 7 * x < 12 * (1 - 2 * t)) (hk1 : 1 ≤ k) (hko : k < 2 * t + x) (hq : 1 < q)
    (hqs : q * (4 * t + 2 * x - 1) < 1 + x) (hv : v = nsrSecN t x)
    (hcomb : nsfComb (nltAl q) (nltM t x q) t x k q v (Real.log q)
      (m2F ((t + x) / (1 + x)) q) < 0) : False := by
  have hx : 0 < x := by linarith
  have hq0 : 0 < q := by linarith
  have hj4 : 2 * t + x - 1 < 1 / 4 := by linarith
  obtain ⟨hα, hM⟩ := nsf_LGN_mult ht0 hj hq.le hqs.le
  have hJ := nsf_LG_J ht0 (by linarith) hj hq0.le hqs.le
  have hCv := nsf_LGN_Cv ht0 ht1 hj hj4 hk1 hko.le hq.le hqs.le
  have hCL : nsfCL (nltAl q) t x k q ≤ 0 := by
    unfold nsfCL
    apply mul_nonpos_of_nonneg_of_nonpos _
      (nsrNL_nonpos (by linarith) hx.le hq0.le (by linarith))
    apply mul_nonneg (by positivity); nlinarith
  -- the rational substitutions: `G_n < 0` with `v_G`, then with `V_L`
  have hG := nsf_LG_subst (by linarith) hx (by linarith) hq (by linarith) hv hCv hCL hcomb
  have e := nsf_comb_sub_v (nltAl q) (nltM t x q) t x k q (nsfVG t x) (hrlVL t x) (nsrLp q) (nsrFl t x q)
  have hVG := hrl_VG_le_VL hx.le (by linarith : t ≤ 1)
  have : 0 ≤ (nsfVG t x - hrlVL t x) * nsfCv (nltAl q) (nltM t x q) t x k q :=
    mul_nonneg_of_nonpos_of_nonpos (by linarith) hCv.le
  -- the shape reduction (`nlt_shape_ge`) and the unit sign (`nlt_unit_pos`)
  have hs := nlt_shape_ge ht0 ht1 hj hjh.le hk1 hko.le hq.le hqs.le hJ
  have hu := nlt_unit_pos ht0 ht1 hj hjh.le hq.le hqs.le
  linarith

/-- **The large-gap exclusion for `3/8 ≤ t < 2/5`** with the constant multipliers `4`, `1`: the
negative combined residual of an actual window (premise `hcomb`) contradicts its positivity at the
lower endpoint `k = 29t²/4` and the shape monotonicity. -/
theorem nsf_LGB_core {t x k q v : ℝ} (ht0 : 3 / 8 ≤ t) (ht1 : t < 2 / 5) (hj : 1 / 30 ≤ 2 * t + x - 1)
    (hjh : 7 * x < 12 * (1 - 2 * t)) (hks : 29 / 4 * t ^ 2 < k) (hko : k < 2 * t + x) (hq : 1 < q)
    (hqs : q * (4 * t + 2 * x - 1) < 1 + x) (hv : v = nsrSecN t x)
    (hcomb : nsfComb 4 1 t x k q v (Real.log q) (m2F ((t + x) / (1 + x)) q) < 0) : False := by
  have hx : 0 < x := by linarith
  have hW : 0 < 1 + x := by linarith
  have hq0 : 0 < q := by linarith
  have hk1 : 1 ≤ k := by nlinarith
  have hCv := nsf_LGB_Cv (by linarith) ht1.le hj hk1 hq.le hqs.le
  have hCL : nsfCL 4 t x k q ≤ 0 := by
    unfold nsfCL
    have hJ := nsf_LG_J (by linarith) ht1.le hj hq0.le hqs.le
    apply mul_nonpos_of_nonneg_of_nonpos _
      (nsrNL_nonpos (by linarith) hx.le hq0.le (by linarith))
    apply mul_nonneg (by positivity); nlinarith
  have hG := nsf_LG_subst (by linarith) hx (by linarith) hq zero_le_one hv hCv hCL hcomb
  -- the lower endpoint `k₀ = 29t²/4` (`hrl_lower_pos`)
  have hA : 0 < nsfComb 4 1 t x (29 / 4 * t ^ 2) q (nsfVG t x) (nsrLp q) (nsrFl t x q) :=
    hrl_lower_pos ht0 ht1 hj hjh hq.le hqs.le
      (nsf_LGB_Cv (by linarith) ht1.le hj (by nlinarith) hq.le hqs.le)
  -- the shape monotonicity (`hrs_shape_lt`)
  have := hrs_shape_lt ht0 ht1 hj hjh hks hko hq.le hqs.le
    (nsf_LG_J (by linarith) ht1.le hj hq0.le hqs.le) (nsf_LG_WD (by linarith) ht1.le hj hq0.le hqs.le)
  linarith

/-- **The gap is smaller than one thirtieth**: an actual forward window has `j = 2t + x - 1 < 1/30`
(from `t > 1/3`, by the two large-gap exclusions). -/
theorem nsf_small_gap_j (W : M2Window) (hF : W.ForwardNext) : 2 * W.nt + W.nx - 1 < 1 / 30 := by
  by_contra hj
  push Not at hj
  obtain ⟨-, -, hx, hk1, hq, -, hv, -, hg, -, -⟩ := nsr_window_basic W
  have ht0 := (nsf_low_ratio W hF).le
  have ht1 := nsr_high_t W
  have hTG := nsf_t_lt_TG (by linarith) hx hv hg
  obtain ⟨-, hjh⟩ := nsf_LG_dom ht0 hx hTG
  have hko := nsf_window_order W
  have hqs : W.nq * (4 * W.nt + 2 * W.nx - 1) < 1 + W.nx := by
    have := nsf_window_swap W
    have hden : 0 < 4 * W.nt + 2 * W.nx - 1 := by linarith
    rwa [lt_div_iff₀ hden] at this
  rcases le_total W.nt (3 / 8) with h38 | h38
  · obtain ⟨hα, hM⟩ := nsf_LGN_mult ht0 hj hq.le hqs.le
    exact nsf_LGN_core ht0 h38 hj hjh hk1.le hko hq hqs hv
      (nsf_window_comb W hF (by linarith) (by linarith))
  · exact nsf_LGB_core h38 ht1 hj hjh (nsr_scale_k W) hko hq hqs hv
      (nsf_window_comb W hF (by norm_num) zero_le_one)

end SmoothedOctagon
