module

public import SmoothedOctagon.Exclusion.Mixed.SmallerShort.CasimirFloor.PhiDisplacement.ShapeDerivative

/-!
# Smaller-short window, Casimir floor: `Φ_b < -9/500`, `Φ_u > -7/10` and the incoming upper value

On the containing rectangle `2 ≤ x ≤ 13/6`, `1 ≤ a ≤ 22/19`, `x ≤ b ≤ 20x/19`, `3/4 ≤ u ≤ 19/25`:

* `(R₀)_b` is affine in `u` with slope `1/a + 4η(S³ + K - 2D)/K² > 0`, and
  `(R₀)_b(b) - (R₀)_b(x) = (b - x)(12η²/K² - (bx - a²)/(B²(a + x)²))` at `u = 3/4` (the
  convexity `(R₀)_{bb} > 0` in integrated form), with
  `12η²/K² ≥ 3/40 ≥ 1/20 ≥ (bx - a²)/(B²(a + x)²)`; so `Φ_b ≤ Φ_b(x, a, x, 3/4)`, and
  `-9/500 - Φ_b(x, a, x, 3/4) = P_b/(3500a(a + x)²K²)` with the explicit polynomial `P_b > 0`
  (monomial rule, lower bound `2560`) gives `Φ_b < -9/500` (`cas_w1_Pb_le`);
* `Γ_u - 4/25 = (P_Γ(h) + 25S⁶(19/25 - u))/(200X²) ≥ 0` and
  `(R₀)_u = B/a + C(1 - 2z) - 2z(1 - z) < 33/10 + (19/6)(41/50) - 3/25`, so `Φ_u > -7/10`
  (`cas_w1_Pu_ge`);
* on `b = x(1 + d)` the incoming upper value `ū` has
  `u_d = (xd²(3(x - 1) + 2xd)/48 - xJ)/(x - 1 + xd)²`, `-9/500 ≤ u_d ≤ 0`, and
  `3/4 ≤ ū ≤ 19/25` (`cas_w1_ubar`).

## Main API

`casW1PbP`, `cas_w1_PbP_pos`, `cas_w1_Pb_diff`, `cas_w1_Pb_src`, `cas_w1_Pb_le`,
`cas_w1_Pu_ge`, `casW1ud`, `cas_w1_ud_deriv`, `cas_w1_ud_bounds`, `cas_w1_ubar`.
-/

@[expose] public section

namespace SmoothedOctagon

open Real

/-- The polynomial `P_b(c, h)` with `-9/500 - Φ_b(x, a, x, 3/4) = P_b/(3500a(a + x)²K²)`. -/
noncomputable def casW1PbP (c h : ℝ) : ℝ :=
  -63 * c ^ 7 - 126 * c ^ 6 * h + 682 * c ^ 6 - 189 * c ^ 5 * h ^ 2 + 5986 * c ^ 5 * h +
    19655 * c ^ 5 + 248 * c ^ 4 * h ^ 3 - 1836 * c ^ 4 * h ^ 2 + 23280 * c ^ 4 * h +
    73808 * c ^ 4 + 311 * c ^ 3 * h ^ 4 - 10024 * c ^ 3 * h ^ 3 - 79766 * c ^ 3 * h ^ 2 -
    124864 * c ^ 3 * h + 7463 * c ^ 3 - 626 * c ^ 2 * h ^ 5 - 6206 * c ^ 2 * h ^ 4 -
    63636 * c ^ 2 * h ^ 3 - 301372 * c ^ 2 * h ^ 2 - 530778 * c ^ 2 * h - 269590 * c ^ 2 -
    563 * c * h ^ 6 - 2010 * c * h ^ 5 + 15103 * c * h ^ 4 + 73116 * c * h ^ 3 +
    37827 * c * h ^ 2 - 162850 * c * h - 156207 * c - 688 * h ^ 6 - 3384 * h ^ 5 +
    8620 * h ^ 4 + 82480 * h ^ 3 + 179080 * h ^ 2 + 145896 * h + 33948

/-- The monomial rule on `P_b`: `L_b(h) > 2560`. -/
theorem cas_w1_PbP_pos {c h : ℝ} (hc0 : 0 ≤ c) (hc : c ≤ 3 / 19) (hh : 0 ≤ h) (hh' : h ≤ 1 / 6) :
    0 < casW1PbP c h := by
  have m := cas_w1_mon hc0 hc hh
  have n := cas_w1_nn hc0 hh
  have p := cas_w1_mon hh hh' zero_le_one
  simp only [one_pow, mul_one] at p
  unfold casW1PbP
  linarith [m 7 0, m 6 1, m 5 2, m 4 2, m 3 3, m 3 2, m 3 1, m 2 5, m 2 4, m 2 3, m 2 2, m 2 1,
    m 2 0, m 1 6, m 1 5, m 1 1, m 1 0, p 6 0, p 5 0, n 6 0, n 5 1, n 5 0, n 4 3, n 4 1, n 4 0,
    n 3 4, n 3 0, n 1 4, n 1 3, n 1 2, n 0 4, n 0 3, n 0 2, n 0 1]

/-- The reduction of `Φ_b` to its lower faces `u = 3/4`, `b = x`. -/
theorem cas_w1_Pb_diff (x be al u : ℝ) (hx : 0 < x) (hal : 0 < al) (hbe : 0 < be) :
    casW1Pb x be al u - casW1Pb x x al (3 / 4) =
      -((u - 3 / 4) * (1 / al + 4 * (x - al) * ((1 + x) ^ 3 + (x * (x + 2) + al ^ 2) -
          2 * ssDg x be al) / (x * (x + 2) + al ^ 2) ^ 2) +
        (be - x) * (12 * (x - al) ^ 2 / (x * (x + 2) + al ^ 2) ^ 2 -
          (be * x - al ^ 2) / ((al + be) ^ 2 * (al + x) ^ 2))) / 7 := by
  have hK : 0 < x * (x + 2) + al ^ 2 := by positivity
  have hB : 0 < al + be := by positivity
  have hB' : 0 < al + x := by positivity
  unfold casW1Pb casClosedP ssDg
  field_simp
  ring

/-- `-9/500 - Φ_b(x, a, x, 3/4) = P_b(a - 1, x - 2)/(3500a(a + x)²K²)`. -/
theorem cas_w1_Pb_src {x al : ℝ} (hx : 0 < x) (hal : 0 < al) :
    (-9 / 500 - casW1Pb x x al (3 / 4)) * (3500 * al * (al + x) ^ 2 * (x * (x + 2) + al ^ 2) ^ 2) =
      casW1PbP (al - 1) (x - 2) := by
  have hK : 0 < x * (x + 2) + al ^ 2 := by positivity
  have hB' : 0 < al + x := by positivity
  unfold casW1Pb casW1PbP casClosedP ssDg
  field_simp
  ring

/-- `Φ_b < -9/500` on the containing rectangle. -/
theorem cas_w1_Pb_le {x be al u : ℝ} (hx : 2 ≤ x) (hx' : x ≤ 13 / 6) (ha : 1 ≤ al)
    (ha' : al ≤ 22 / 19) (hb : x ≤ be) (hb' : be ≤ 20 * x / 19) (hu : 3 / 4 ≤ u) :
    casW1Pb x be al u ≤ -9 / 500 := by
  obtain ⟨hK1, hK2, hD1, hD2, hB1, hB2, hη⟩ := cas_w1_box hx hx' ha ha' hb hb'
  have hK0 : 0 < x * (x + 2) + al ^ 2 := by linarith
  have e := cas_w1_Pb_diff x be al u (by linarith) (by linarith) (by linarith)
  have t1 : 0 ≤ 1 / al + 4 * (x - al) * ((1 + x) ^ 3 + (x * (x + 2) + al ^ 2) -
      2 * ssDg x be al) / (x * (x + 2) + al ^ 2) ^ 2 := by
    have : 0 ≤ (1 + x) ^ 3 + (x * (x + 2) + al ^ 2) - 2 * ssDg x be al := by
      have : 0 ≤ (1 + x) ^ 3 := by positivity
      linarith
    have : 0 ≤ 4 * (x - al) * ((1 + x) ^ 3 + (x * (x + 2) + al ^ 2) - 2 * ssDg x be al) /
        (x * (x + 2) + al ^ 2) ^ 2 :=
      div_nonneg (mul_nonneg (by linarith) this) (by positivity)
    have : 0 ≤ 1 / al := by positivity
    linarith
  have t2 : 3 / 40 ≤ 12 * (x - al) ^ 2 / (x * (x + 2) + al ^ 2) ^ 2 := by
    rw [le_div_iff₀ (by positivity)]
    have k : (x * (x + 2) + al ^ 2) ^ 2 ≤ (21 / 2) ^ 2 := pow_le_pow_left₀ hK0.le hK2 2
    have k2 : (16 / 19) ^ 2 ≤ (x - al) ^ 2 := pow_le_pow_left₀ (by norm_num) hη 2
    nlinarith
  have t3 : (be * x - al ^ 2) / ((al + be) ^ 2 * (al + x) ^ 2) ≤ 1 / 20 := by
    rw [div_le_iff₀ (by positivity)]
    have k1 : (3 : ℝ) ^ 2 ≤ (al + be) ^ 2 := pow_le_pow_left₀ (by norm_num) hB1 2
    have k2 : (3 : ℝ) ^ 2 ≤ (al + x) ^ 2 := pow_le_pow_left₀ (by norm_num) (by linarith) 2
    have k3 : (3 : ℝ) ^ 2 * 3 ^ 2 ≤ (al + be) ^ 2 * (al + x) ^ 2 :=
      mul_le_mul k1 k2 (by norm_num) (by positivity)
    have k4 : be * x ≤ 20 * x / 19 * x := mul_le_mul_of_nonneg_right hb' (by linarith)
    nlinarith
  have hdiff : casW1Pb x be al u ≤ casW1Pb x x al (3 / 4) := by
    rw [← sub_nonpos, e]
    apply div_nonpos_of_nonpos_of_nonneg _ (by norm_num)
    rw [neg_nonpos]
    exact add_nonneg (mul_nonneg (by linarith) t1) (mul_nonneg (by linarith) (by linarith))
  have hs := cas_w1_Pb_src (x := x) (al := al) (by linarith) (by linarith)
  have hP := cas_w1_PbP_pos (c := al - 1) (h := x - 2) (by linarith) (by linarith) (by linarith)
    (by linarith)
  have hden : 0 < 3500 * al * (al + x) ^ 2 * (x * (x + 2) + al ^ 2) ^ 2 := by
    have : 0 < al := by linarith
    positivity
  have : 0 < -9 / 500 - casW1Pb x x al (3 / 4) := by
    by_contra hc
    have := mul_nonpos_of_nonpos_of_nonneg (not_lt.mp hc) hden.le
    linarith
  linarith

/-- `Φ_u > -7/10` on the containing rectangle. -/
theorem cas_w1_Pu_ge {x be al u : ℝ} (hx : 2 ≤ x) (hx' : x ≤ 13 / 6) (ha : 1 ≤ al)
    (ha' : al ≤ 22 / 19) (hb : x ≤ be) (hb' : be ≤ 20 * x / 19) (hu' : u ≤ 19 / 25) :
    -7 / 10 ≤ casW1Pu x be al u := by
  obtain ⟨hK1, hK2, hD1, hD2, hB1, hB2, hη⟩ := cas_w1_box hx hx' ha ha' hb hb'
  have hK0 : 0 < x * (x + 2) + al ^ 2 := by linarith
  have hal : 0 < al := by linarith
  -- `Γ_u ≥ 4/25`
  have eG : (4 * ((1 + x) ^ 2 * ((1 + x) ^ 2 - (1 + x) + 1)) - 2 * casClosedP x u * (1 + x) ^ 3) /
      (16 * x ^ 2 * (x + 2) ^ 2) - 4 / 25 =
      ((6 * (x - 2) ^ 6 + 108 * (x - 2) ^ 5 + 753 * (x - 2) ^ 4 + 2531 * (x - 2) ^ 3 +
        4101 * (x - 2) ^ 2 + 2601 * (x - 2) + 76) + 25 * (1 + x) ^ 6 * (19 / 25 - u)) /
        (200 * x ^ 2 * (x + 2) ^ 2) := by
    have : 0 < x := by linarith
    unfold casClosedP
    field_simp
    ring
  have hG : 4 / 25 ≤ (4 * ((1 + x) ^ 2 * ((1 + x) ^ 2 - (1 + x) + 1)) -
      2 * casClosedP x u * (1 + x) ^ 3) / (16 * x ^ 2 * (x + 2) ^ 2) := by
    have h0 : 0 ≤ x - 2 := by linarith
    have : 0 ≤ ((6 * (x - 2) ^ 6 + 108 * (x - 2) ^ 5 + 753 * (x - 2) ^ 4 + 2531 * (x - 2) ^ 3 +
        4101 * (x - 2) ^ 2 + 2601 * (x - 2) + 76) + 25 * (1 + x) ^ 6 * (19 / 25 - u)) /
        (200 * x ^ 2 * (x + 2) ^ 2) := by
      have : 0 ≤ 19 / 25 - u := by linarith
      positivity
    linarith
  -- `(R₀)_u < 1733/300`
  have eR : 2 * (ssDg x be al ^ 2 - ssDg x be al * (1 + x) ^ 3) / (x * (x + 2) + al ^ 2) ^ 2 +
      (al + be) / al - (2 * ssDg x be al - (1 + x) ^ 3) / (x * (x + 2) + al ^ 2) =
      (1 + be / al) + (1 + x) ^ 3 / (x * (x + 2) + al ^ 2) *
        (1 - 2 * (ssDg x be al / (x * (x + 2) + al ^ 2))) -
        2 * (ssDg x be al / (x * (x + 2) + al ^ 2)) *
          (1 - ssDg x be al / (x * (x + 2) + al ^ 2)) := by
    field_simp
    ring
  have hz1 : 9 / 100 ≤ ssDg x be al / (x * (x + 2) + al ^ 2) := by
    rw [le_div_iff₀ hK0]; linarith
  have hz2 : ssDg x be al / (x * (x + 2) + al ^ 2) ≤ 1 / 3 := by
    rw [div_le_iff₀ hK0]; linarith
  have hC0 : 0 ≤ (1 + x) ^ 3 / (x * (x + 2) + al ^ 2) := by positivity
  have hC : (1 + x) ^ 3 / (x * (x + 2) + al ^ 2) ≤ 19 / 6 := by
    rw [div_le_iff₀ hK0]
    have : (1 + x) ^ 2 ≤ x * (x + 2) + al ^ 2 := by nlinarith
    have : (1 + x) ^ 3 = (1 + x) * (1 + x) ^ 2 := by ring
    nlinarith
  have hba : be / al ≤ 130 / 57 := by
    rw [div_le_iff₀ hal]; nlinarith
  generalize ssDg x be al / (x * (x + 2) + al ^ 2) = z at hz1 hz2 eR
  generalize (1 + x) ^ 3 / (x * (x + 2) + al ^ 2) = C at hC0 hC eR
  have k1 : C * (1 - 2 * z) ≤ 19 / 6 * (41 / 50) :=
    mul_le_mul hC (by linarith) (by linarith) (by norm_num)
  have k2 : 3 / 25 ≤ 2 * z * (1 - z) := by nlinarith
  unfold casW1Pu
  rw [eR]
  linarith

/-! ### The incoming upper value on the curve -/

/-- `u_d`, the `d`-derivative of `ū(x, x(1 + d))`. -/
noncomputable def casW1ud (x d : ℝ) : ℝ :=
  (x * d ^ 2 * (3 * (x - 1) + 2 * x * d) / 48 - x * (2 * (x - 1) ^ 3 / ((x + 1) * (35 * x + 13)))) /
    (x - 1 + x * d) ^ 2

theorem cas_w1_ud_deriv {x d : ℝ} (hx : 1 < x) (hd : 0 ≤ d) :
    HasDerivAt (fun d => ssUbar x (x * (1 + d))) (casW1ud x d) d := by
  have hb : HasDerivAt (fun d : ℝ => x * (1 + d)) x d := by
    have := ((hasDerivAt_id' d).const_add 1).const_mul x
    refine this.congr_deriv ?_
    ring
  have hne : x * (1 + d) - 1 ≠ 0 := by nlinarith
  have := ((((hb.sub_const x).fun_pow 3).div_const (48 * x ^ 2)).const_add
    (2 * (x - 1) ^ 3 / ((x + 1) * (35 * x + 13)))).fun_div (hb.sub_const 1) hne |>.const_add (3 / 4)
  refine this.congr_deriv ?_
  have h1 : x - 1 + x * d ≠ 0 := by nlinarith
  have h2 : (x + 1) * (35 * x + 13) ≠ 0 := by positivity
  have h3 : x ≠ 0 := by positivity
  unfold casW1ud
  field_simp
  ring

/-- The range of `u_d` and of `ū`: `-9/500 ≤ u_d ≤ 0` and `3/4 ≤ ū ≤ 19/25`. -/
theorem cas_w1_ud_bounds {x d : ℝ} (hx : 2 ≤ x) (hx' : x ≤ 13 / 6) (hd : 0 ≤ d)
    (hd' : d ≤ 1 / 19) : -9 / 500 ≤ casW1ud x d ∧ casW1ud x d ≤ 0 := by
  have hZ : 0 < (x + 1) * (35 * x + 13) := by positivity
  have hJ0 : 0 ≤ 2 * (x - 1) ^ 3 / ((x + 1) * (35 * x + 13)) := by
    have : 0 ≤ x - 1 := by linarith
    positivity
  have hQ : (x - 1) ^ 2 ≤ (x - 1 + x * d) ^ 2 :=
    pow_le_pow_left₀ (by linarith) (by nlinarith) 2
  have hQ0 : 0 < (x - 1) ^ 2 := by nlinarith
  have hA0 : 0 ≤ x * d ^ 2 * (3 * (x - 1) + 2 * x * d) / 48 := by
    have : 0 ≤ 3 * (x - 1) + 2 * x * d := by nlinarith
    positivity
  constructor
  · -- `-u_d ≤ xJ/(x - 1)² = 2x(x - 1)/(SZ) < 9/500`
    have k1 : x * (2 * (x - 1) ^ 3 / ((x + 1) * (35 * x + 13))) / (x - 1 + x * d) ^ 2 ≤
        x * (2 * (x - 1) ^ 3 / ((x + 1) * (35 * x + 13))) / (x - 1) ^ 2 :=
      div_le_div_of_nonneg_left (by positivity) hQ0 hQ
    have k2 : x * (2 * (x - 1) ^ 3 / ((x + 1) * (35 * x + 13))) / (x - 1) ^ 2 ≤ 9 / 500 := by
      have e : x * (2 * (x - 1) ^ 3 / ((x + 1) * (35 * x + 13))) / (x - 1) ^ 2 =
          2 * x * (x - 1) / ((x + 1) * (35 * x + 13)) := by
        have : x - 1 ≠ 0 := by linarith
        field_simp
      rw [e, div_le_iff₀ hZ]
      nlinarith
    have k3 : casW1ud x d = x * d ^ 2 * (3 * (x - 1) + 2 * x * d) / 48 / (x - 1 + x * d) ^ 2 -
        x * (2 * (x - 1) ^ 3 / ((x + 1) * (35 * x + 13))) / (x - 1 + x * d) ^ 2 := by
      unfold casW1ud; ring
    have k4 : 0 ≤ x * d ^ 2 * (3 * (x - 1) + 2 * x * d) / 48 / (x - 1 + x * d) ^ 2 := by positivity
    linarith
  · unfold casW1ud
    apply div_nonpos_of_nonpos_of_nonneg _ (by positivity)
    have k1 : 72 / 10127 ≤ 2 * (x - 1) ^ 3 / ((x + 1) * (35 * x + 13)) := by
      rw [le_div_iff₀ hZ]
      have : 1 ≤ (x - 1) ^ 3 := one_le_pow₀ (by linarith)
      nlinarith
    have k2 : d ^ 2 * (3 * (x - 1) + 2 * x * d) ≤ 4 / 361 := by
      have : d ^ 2 ≤ 1 / 361 := by nlinarith
      have : 3 * (x - 1) + 2 * x * d ≤ 4 := by nlinarith
      have : 0 ≤ 3 * (x - 1) + 2 * x * d := by nlinarith
      nlinarith
    have : x * d ^ 2 * (3 * (x - 1) + 2 * x * d) / 48 ≤ x * (4 / 361) / 48 := by
      have := mul_le_mul_of_nonneg_left k2 (by linarith : (0 : ℝ) ≤ x)
      linarith
    have : x * (4 / 361) / 48 ≤ x * (2 * (x - 1) ^ 3 / ((x + 1) * (35 * x + 13))) := by
      nlinarith
    linarith

/-- The incoming upper value on the curve: nonincreasing in `d` with slope at least `-9/500`, and
in `[3/4, 19/25]`. -/
theorem cas_w1_ubar {x d₁ d₂ : ℝ} (hx : 2 ≤ x) (hx' : x ≤ 13 / 6) (h0 : 0 ≤ d₁) (h12 : d₁ ≤ d₂)
    (h2 : d₂ ≤ 1 / 19) :
    ssUbar x (x * (1 + d₂)) ≤ ssUbar x (x * (1 + d₁)) ∧
      ssUbar x (x * (1 + d₁)) - ssUbar x (x * (1 + d₂)) ≤ 9 / 500 * (d₂ - d₁) ∧
      3 / 4 ≤ ssUbar x (x * (1 + d₂)) ∧ ssUbar x (x * (1 + d₁)) ≤ 19 / 25 := by
  have hd : ∀ z ∈ Set.Icc (0 : ℝ) (1 / 19), HasDerivAt (fun d => ssUbar x (x * (1 + d)))
      (casW1ud x z) z := fun z hz => cas_w1_ud_deriv (by linarith) hz.1
  refine ⟨jet_anti_of hd (fun z hz => (cas_w1_ud_bounds hx hx' hz.1 hz.2).2) h0 h12 h2,
    ?_, ?_, ?_⟩
  · have := jet_mono_of (f := fun d => ssUbar x (x * (1 + d)) + 9 / 500 * d)
      (f₁ := fun z => casW1ud x z + 9 / 500) (a := 0) (b := 1 / 19)
      (fun z hz => (hd z hz).add ((hasDerivAt_id' z).const_mul (9 / 500) |>.congr_deriv (by ring)))
      (fun z hz => by linarith [(cas_w1_ud_bounds hx hx' hz.1 hz.2).1]) h0 h12 h2
    linarith
  · unfold ssUbar
    have : 0 ≤ (2 * (x - 1) ^ 3 / ((x + 1) * (35 * x + 13)) +
        (x * (1 + d₂) - x) ^ 3 / (48 * x ^ 2)) / (x * (1 + d₂) - 1) := by
      have : 0 ≤ x * (1 + d₂) - x := by nlinarith
      have : 0 < x * (1 + d₂) - 1 := by nlinarith
      have : 0 ≤ x - 1 := by linarith
      positivity
    linarith
  · refine (jet_anti_of hd (fun z hz => (cas_w1_ud_bounds hx hx' hz.1 hz.2).2) le_rfl h0
      (h12.trans h2)).trans ?_
    unfold ssUbar
    have hZ : 0 < (x + 1) * (35 * x + 13) := by positivity
    have e : 3 / 4 + (2 * (x - 1) ^ 3 / ((x + 1) * (35 * x + 13)) +
        (x * (1 + 0) - x) ^ 3 / (48 * x ^ 2)) / (x * (1 + 0) - 1) =
        3 / 4 + 2 * (x - 1) ^ 2 / ((x + 1) * (35 * x + 13)) := by
      have : x - 1 ≠ 0 := by linarith
      rw [show x * (1 + 0) - x = 0 by ring, show x * (1 + 0) - 1 = x - 1 by ring]
      field_simp
      ring
    rw [e]
    have : 2 * (x - 1) ^ 2 / ((x + 1) * (35 * x + 13)) ≤ 1 / 100 := by
      rw [div_le_iff₀ hZ]
      nlinarith
    linarith

end SmoothedOctagon
