module

public import SmoothedOctagon.Exclusion.Mixed.Residual

/-!
# The feasible low-scale region

The reciprocal-mean ceiling and the endpoint norm floor give
`t(x²+6x+6) < 3+x-x²`. The right-hand quotient decreases in `x`.
Together with the scale bound `17t²`, this gives the natural cutoff
`t < 3/8`. The control floor supplies the endpoint norm floor whenever
`2t+x ≥ 1`.
-/

@[expose] public section

namespace SmoothedOctagon

/-- The gap between the reciprocal-mean ceiling and the endpoint norm floor. -/
theorem nsr_jensen_sub_g {t x : ℝ} (hx : 0 < x) :
    nsrVJensen t x - (1 - (1 - t) * (t + x) / (1 + x) ^ 2) =
      (1 - t) * x * (3 + x - x ^ 2 - t * (x ^ 2 + 6 * x + 6)) /
        ((1 + x) ^ 2 * (x ^ 2 + 6 * x + 6)) := by
  have hW : (1 + x) ≠ 0 := by positivity
  have hD : (x ^ 2 + 6 * x + 6) ≠ 0 := by positivity
  unfold nsrVJensen
  field_simp
  ring

/-- The endpoint norm floor confines `t` below a decreasing rational function. -/
theorem nsr_t_lt_jensen_T {t x v : ℝ} (ht : t < 1) (hx : 0 < x)
    (hv : v = nsrSecN t x) (hg : 1 - (1 - t) * (t + x) / (1 + x) ^ 2 ≤ v) :
    t * (x ^ 2 + 6 * x + 6) < 3 + x - x ^ 2 := by
  have hV : v < nsrVJensen t x := hv ▸ nsr_secN_lt_jensen hx ht
  have hp : 0 < nsrVJensen t x - (1 - (1 - t) * (t + x) / (1 + x) ^ 2) := by
    linarith only [hV, hg]
  rw [nsr_jensen_sub_g hx] at hp
  have hn := (div_pos_iff_of_pos_right (show 0 < (1 + x) ^ 2 * (x ^ 2 + 6 * x + 6) by positivity)).mp hp
  have hc : 0 < (1 - t) * x := mul_pos (sub_pos.mpr ht) hx
  have hs := pos_of_mul_pos_right hn hc.le
  linarith only [hs]

/-- Monotonicity of `(3+x-x²)/(x²+6x+6)`, without divisions. -/
theorem nsr_jensen_T_anti {a x t : ℝ} (ha : 0 ≤ a) (hax : a ≤ x)
    (hT : t * (x ^ 2 + 6 * x + 6) ≤ 3 + x - x ^ 2) :
    t * (a ^ 2 + 6 * a + 6) ≤ 3 + a - a ^ 2 := by
  have hx : 0 ≤ x := ha.trans hax
  have he : (3 + a - a ^ 2) * (x ^ 2 + 6 * x + 6)
      - (3 + x - x ^ 2) * (a ^ 2 + 6 * a + 6) =
      (x - a) * (7 * a * x + 9 * a + 9 * x + 12) := by ring
  have hp : 0 ≤ (x - a) * (7 * a * x + 9 * a + 9 * x + 12) := by
    have : 0 ≤ x - a := sub_nonneg.mpr hax
    positivity
  have hmul := mul_le_mul_of_nonneg_right hT
    (show 0 ≤ a ^ 2 + 6 * a + 6 by positivity)
  have hres : t * (a ^ 2 + 6 * a + 6) * (x ^ 2 + 6 * x + 6) ≤
      (3 + a - a ^ 2) * (x ^ 2 + 6 * x + 6) := by
    nlinarith only [hmul, he, hp]
  exact le_of_mul_le_mul_right hres (by positivity)

/-- Above the order boundary, the control floor is strictly above the endpoint norm floor. -/
theorem nsr_floor_gt_g {t x q : ℝ} (hx : 0 < x) (ho : 1 ≤ 2 * t + x) (hq : 1 < q) :
    1 - (1 - t) * (t + x) / (1 + x) ^ 2 < m2F ((t + x) / (1 + x)) q := by
  have hW : 0 < 1 + x := by positivity
  have hp : 0 < t + x := by linarith only [ho, hx]
  have hη : 1 / 2 ≤ (t + x) / (1 + x) := (le_div_iff₀ hW).mpr (by linarith only [ho])
  have he : nsrFl t x q - (1 - (1 - t) * (t + x) / (1 + x) ^ 2) =
      (t + x) / (1 + x) * ((t + x) / (1 + x) - 1 / 2) * (q - 1)
      + (t + x) / (1 + x) * (q - 1) ^ 2 / (3 * (q + 1)) := by
    unfold nsrFl
    field_simp
    ring
  have hy : 0 < q - 1 := sub_pos.mpr hq
  have hη0 : 0 < (t + x) / (1 + x) := div_pos hp hW
  have hη' : 0 ≤ (t + x) / (1 + x) - 1 / 2 := sub_nonneg.mpr hη
  have hgap : 0 < nsrFl t x q - (1 - (1 - t) * (t + x) / (1 + x) ^ 2) := by
    rw [he]
    positivity
  have hF := nsr_m2F_gt_Fl hq hp hW
  linarith only [hgap, hF]

/-- The low-scale region stays below the natural cutoff `3/8`. -/
theorem nsr_low_t_three_eighths {t x k v : ℝ} (ht1 : t < 1 / 2)
    (hx : 0 < x) (hk : 17 * t ^ 2 ≤ k) (hgap : k < 2 * t + 2 * x + x ^ 2)
    (hv : v = nsrSecN t x) (hg : 1 - (1 - t) * (t + x) / (1 + x) ^ 2 ≤ v) :
    t < 3 / 8 := by
  have hT := nsr_t_lt_jensen_T (by linarith only [ht1]) hx hv hg
  by_contra h
  have ht0 : 3 / 8 ≤ t := le_of_not_gt h
  have hxhalf : 1 / 2 < x := by
    by_contra hx'
    have hx' : x ≤ 1 / 2 := le_of_not_gt hx'
    have h2 : x ^ 2 ≤ x / 2 := by nlinarith only [mul_nonneg hx.le (sub_nonneg.mpr hx')]
    have hp := mul_nonneg (show 0 ≤ t - 3 / 8 by linarith only [ht0])
      (show 0 ≤ 17 * (t + 3 / 8) - 2 by linarith only [ht0])
    nlinarith only [hk, hgap, h2, hp, hx']
  have hhalf := nsr_jensen_T_anti (a := 1 / 2) (by norm_num) hxhalf.le hT.le
  norm_num at hhalf
  linarith only [hhalf, ht0]

end SmoothedOctagon
