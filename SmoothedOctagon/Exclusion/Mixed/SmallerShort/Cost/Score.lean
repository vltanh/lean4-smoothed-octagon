module

public import SmoothedOctagon.Exclusion.Mixed.SmallerShort.Cost.Defs
public import SmoothedOctagon.Exclusion.Mixed.SmallerShort.Jets

/-!
# Smaller-short window, cost: the score in cancelled form and its concavity in `R`

With `t = T(R, d, e) = N/B`,
`v = 4u_q - 3`, `z = Z_U` and `h = H/J` (`H = 4 + 2(e + 1)d - (e - 1)d(R + 1/R)`,
`J = 3B² + N²`), the polynomial bound is

`𝓑 = k(R) + k(t) + v(g(R) + g(t)) - z(p(R) + p(t))/8 + vz(q(R) + q(t))/8 - κ F h²`,

`κ = 161(e - 1)²d²/(432(2 + 11d))`, `F = (1 - R)²(1 + R)(3 - R)` (`cost_score_eq`). On
`1/3 ≤ R ≤ 7/19`, `0 ≤ d ≤ 1/19`, `13/5 ≤ e ≤ 3` its second `R`-derivative is negative
(the jets are composed with `SecondJet`), so the minimum over `R` is at an end
(`cost_score_concave`).

## Main API

* `costBd`, `costNd`, `costt1`, `costt2`, `costv`, `costv1`, `costv2`, `costz1`, `costz2`,
  `costcF`, `costH`, `costJd`, `costh`, `costkap`, `costScore`.
* `cost_score_eq`: `costB R (costT R d e) d (costuq R d) = costScore e d R`.
* `cost_score_concave`: the concave minimum in `R`.
-/

@[expose] public section

namespace SmoothedOctagon

open Set

/-! ### Definitions -/

/-- `B = 2 + (e + 1 - (e - 1)R)d`. -/
noncomputable def costBd (e d r : ℝ) : ℝ := 2 + (e + 1 - (e - 1) * r) * d

/-- `N = 2R + ((e + 1)R - (e - 1))d`. -/
noncomputable def costNd (e d r : ℝ) : ℝ := 2 * r + ((e + 1) * r - (e - 1)) * d

/-- `t_R = (2 + 2d)(2 + 2ed)/B²`. -/
noncomputable def costt1 (e d r : ℝ) : ℝ := (2 + 2 * d) * (2 + 2 * e * d) / costBd e d r ^ 2

/-- `t_RR = 2(e - 1)d t_R/B`. -/
noncomputable def costt2 (e d r : ℝ) : ℝ :=
  2 * (e - 1) * d * ((2 + 2 * d) * (2 + 2 * e * d)) / costBd e d r ^ 3

/-- `H_f = (3R² + 10R + 10)/(15(R + 2)³)`, so that `v = 4u_q - 3 = 4H_f Q`. -/
noncomputable def costHf (r : ℝ) : ℝ := (3 * r ^ 2 + 10 * r + 10) / (15 * (r + 2) ^ 3)

noncomputable def costHf1 (r : ℝ) : ℝ := -(3 * r ^ 2 + 8 * r + 10) / (15 * (r + 2) ^ 4)

noncomputable def costHf2 (r : ℝ) : ℝ := (6 * r ^ 2 + 12 * r + 24) / (15 * (r + 2) ^ 5)

/-- `Q = R² - R(1 + R)d/2 + 19(1 + R)²d²/84`. -/
noncomputable def costQn (d r : ℝ) : ℝ := r ^ 2 - r * (1 + r) * d / 2 + 19 * (1 + r) ^ 2 * d ^ 2 / 84

noncomputable def costQn1 (d r : ℝ) : ℝ := 2 * r - (1 + 2 * r) * d / 2 + 19 * (1 + r) * d ^ 2 / 42

noncomputable def costQn2 (d _r : ℝ) : ℝ := 2 - d + 19 * d ^ 2 / 42

/-- `v = 4u_q - 3`. -/
noncomputable def costv (d r : ℝ) : ℝ := 4 * (costHf r * costQn d r)

noncomputable def costv1 (d r : ℝ) : ℝ := 4 * (costHf1 r * costQn d r + costHf r * costQn1 d r)

noncomputable def costv2 (d r : ℝ) : ℝ :=
  4 * (costHf2 r * costQn d r + 2 * (costHf1 r * costQn1 d r) + costHf r * costQn2 d r)

/-- `z_R = z₀' + d/(1 - R)²`, `z₀' = -4R - 8 + 72/(3 - R)²`. -/
noncomputable def costz1 (d r : ℝ) : ℝ := -4 * r - 8 + 72 / (3 - r) ^ 2 + d / (1 - r) ^ 2

/-- `z_RR = -4 + 144/(3 - R)³ + 2d/(1 - R)³`. -/
noncomputable def costz2 (d r : ℝ) : ℝ := -4 + 144 / (3 - r) ^ 3 + 2 * d / (1 - r) ^ 3

/-- `F = (1 - R)²(1 + R)(3 - R)`. -/
noncomputable def costcF (r : ℝ) : ℝ := 3 - 4 * r - 2 * r ^ 2 + 4 * r ^ 3 - r ^ 4

noncomputable def costcF1 (r : ℝ) : ℝ := -4 - 4 * r + 12 * r ^ 2 - 4 * r ^ 3

noncomputable def costcF2 (r : ℝ) : ℝ := -4 + 24 * r - 12 * r ^ 2

/-- `H = 4 + 2(e + 1)d - (e - 1)d(R + 1/R)`. -/
noncomputable def costH (e d r : ℝ) : ℝ := 4 + 2 * (e + 1) * d - (e - 1) * d * (r + 1 / r)

noncomputable def costH1 (e d r : ℝ) : ℝ := (e - 1) * d * (1 / r ^ 2 - 1)

noncomputable def costH2 (e d r : ℝ) : ℝ := -(2 * (e - 1) * d / r ^ 3)

/-- `J = 3B² + N²`. -/
noncomputable def costJd (e d r : ℝ) : ℝ := 3 * costBd e d r ^ 2 + costNd e d r ^ 2

noncomputable def costJ1 (e d r : ℝ) : ℝ :=
  -(6 * (e - 1) * d * costBd e d r) + 2 * (2 + (e + 1) * d) * costNd e d r

noncomputable def costJ2 (e d _r : ℝ) : ℝ := 6 * (e - 1) ^ 2 * d ^ 2 + 2 * (2 + (e + 1) * d) ^ 2

/-- `h = H/J`. -/
noncomputable def costh (e d r : ℝ) : ℝ := costH e d r / costJd e d r

noncomputable def costh1 (e d r : ℝ) : ℝ :=
  costH1 e d r / costJd e d r - costH e d r * costJ1 e d r / costJd e d r ^ 2

noncomputable def costh2 (e d r : ℝ) : ℝ :=
  costH2 e d r / costJd e d r - 2 * (costH1 e d r * costJ1 e d r) / costJd e d r ^ 2 -
    costH e d r * costJ2 e d r / costJd e d r ^ 2 +
    2 * (costH e d r * costJ1 e d r ^ 2) / costJd e d r ^ 3

/-- `κ = 161(e - 1)²d²/(432(2 + 11d))`. -/
noncomputable def costkap (e d : ℝ) : ℝ := 161 * (e - 1) ^ 2 * d ^ 2 / (432 * (2 + 11 * d))

/-- **The score in cancelled form**
`k(R) + k(t) + v(g(R) + g(t)) - z(p(R) + p(t))/8 + vz(q(R) + q(t))/8 - κ F h²`. -/
noncomputable def costScore (e d r : ℝ) : ℝ :=
  jetk r + jetk (costT r d e) + costv d r * (jetg r + jetg (costT r d e)) -
    1 / 8 * (costZU r d * (jetp r + jetp (costT r d e))) +
    1 / 8 * (costv d r * costZU r d * (jetq r + jetq (costT r d e))) -
    costkap e d * (costcF r * (costh e d r * costh e d r))

/-! ### The cancelled form -/

theorem cost_B_pos {e d r : ℝ} (hd : 0 ≤ d) (he : 1 ≤ e) (hr : r ≤ 1) : 2 ≤ costBd e d r := by
  unfold costBd
  have : 0 ≤ (e + 1 - (e - 1) * r) * d := mul_nonneg (by nlinarith) hd
  linarith

theorem cost_T_eq_div (e d r : ℝ) : costT r d e = costNd e d r / costBd e d r := rfl

/-- The cancelled decomposition, in independent `R, T, d, u`. -/
theorem cost_B_decomp {R T d u : ℝ} (hZ : costZL R d ≠ 0) :
    costB R T d u = jetk R + jetk T + (4 * u - 3) * (jetg R + jetg T) -
      1 / 8 * (costZU R d * (jetp R + jetp T)) +
      1 / 8 * ((4 * u - 3) * costZU R d * (jetq R + jetq T)) -
      161 / 54 * ((R ^ 2 - T ^ 2) / (3 + T ^ 2)) ^ 2 / (8 * costZL R d) := by
  have h1 : (3 + R ^ 2) ≠ 0 := by positivity
  have h2 : (3 + T ^ 2) ≠ 0 := by positivity
  unfold costB costL jetk jetg jetp jetq
  field_simp
  ring

/-- The radical correction in factored form `κ F h²`. -/
theorem cost_corr_eq {e d r : ℝ} (hd : 0 ≤ d) (he : 1 ≤ e) (hr0 : 0 < r) (hr : r < 1) :
    161 / 54 * ((r ^ 2 - costT r d e ^ 2) / (3 + costT r d e ^ 2)) ^ 2 / (8 * costZL r d) =
      costkap e d * (costcF r * (costh e d r * costh e d r)) := by
  have hB := cost_B_pos (r := r) hd he hr.le
  have hJ : 0 < costJd e d r := by unfold costJd; positivity
  have hA : (r ^ 2 - costT r d e ^ 2) / (3 + costT r d e ^ 2) =
      (e - 1) * (1 - r ^ 2) * d * r * costh e d r := by
    have hB0 : costBd e d r ≠ 0 := by linarith
    have hB2 : 0 < costBd e d r ^ 2 := pow_pos (by linarith) 2
    have hJ' : 3 * costBd e d r ^ 2 + costNd e d r ^ 2 ≠ 0 := by
      nlinarith [sq_nonneg (costNd e d r)]
    have hr0' : r ≠ 0 := hr0.ne'
    rw [cost_T_eq_div, costh, costH, costJd]
    field_simp
    unfold costNd costBd
    ring
  rw [hA]
  unfold costZL costkap costcF
  have h3 : (3 - r) ≠ 0 := by linarith
  have h1 : (1 + r) ≠ 0 := by linarith
  field_simp
  ring

/-- **The cancelled form of the polynomial bound**: `𝓑(u_q; R, T(R, d, e), d)` equals the
cancelled score `costScore e d R`. -/
theorem cost_score_eq {e d r : ℝ} (hd : 0 ≤ d) (he : 1 ≤ e) (hr0 : 0 < r) (hr : r < 1) :
    costB r (costT r d e) d (costuq r d) = costScore e d r := by
  have hZ : costZL r d ≠ 0 := by
    unfold costZL
    have : 0 < 3 - r := by linarith
    positivity
  rw [cost_B_decomp hZ, cost_corr_eq hd he hr0 hr]
  have hv : 4 * costuq r d - 3 = costv d r := by
    unfold costuq costv costHf costQn
    ring
  rw [hv]
  unfold costScore
  ring

/-! ### Jets in `R` -/

theorem cost_T_jet {e d r : ℝ} (hB : costBd e d r ≠ 0) :
    SecondJet (fun y => costT y d e) (costt1 e d) (costt2 e d) r := by
  have hN : HasDerivAt (fun y : ℝ => 2 * y + ((e + 1) * y - (e - 1)) * d)
      (2 * 1 + ((e + 1) * 1) * d) r :=
    ((hasDerivAt_id' r).const_mul 2).fun_add ((((hasDerivAt_id' r).const_mul (e + 1)).sub_const
      (e - 1)).mul_const d)
  have hBd : HasDerivAt (fun y : ℝ => 2 + (e + 1 - (e - 1) * y) * d) (-((e - 1) * 1) * d) r :=
    ((((hasDerivAt_id' r).const_mul (e - 1)).const_sub (e + 1)).mul_const d).const_add 2
  constructor
  · refine (hN.fun_div hBd hB).congr_deriv ?_
    unfold costt1
    rw [show (2 + (e + 1 - (e - 1) * r) * d) = costBd e d r from rfl]
    field_simp
    unfold costBd
    ring
  · have := (hasDerivAt_const r ((2 + 2 * d) * (2 + 2 * e * d))).fun_div (hBd.fun_pow 2)
      (pow_ne_zero 2 hB)
    refine this.congr_deriv ?_
    unfold costt2
    rw [show (2 + (e + 1 - (e - 1) * r) * d) = costBd e d r from rfl]
    field_simp
    ring

theorem cost_v_jet (d r : ℝ) (hr : 0 ≤ r) : SecondJet (costv d) (costv1 d) (costv2 d) r := by
  have h2 : (0 : ℝ) < r + 2 := by linarith
  have hHf : SecondJet costHf costHf1 costHf2 r := by
    have hn := ((hasDerivAt_pow 2 r).const_mul 3).fun_add ((hasDerivAt_id' r).const_mul 10)
    have hd3 := (((hasDerivAt_id' r).add_const 2).fun_pow 3).const_mul 15
    constructor
    · refine ((hn.add_const 10).fun_div hd3 (by positivity)).congr_deriv ?_
      unfold costHf1
      push_cast
      field_simp
      ring
    · have hn' := ((hasDerivAt_pow 2 r).const_mul 3).fun_add ((hasDerivAt_id' r).const_mul 8)
      have hd4 := (((hasDerivAt_id' r).add_const 2).fun_pow 4).const_mul 15
      refine ((hn'.add_const 10).fun_neg.fun_div hd4 (by positivity)).congr_deriv ?_
      unfold costHf2
      push_cast
      field_simp
      ring
  have hQ : SecondJet (costQn d) (costQn1 d) (costQn2 d) r := by
    constructor
    · have := (((hasDerivAt_pow 2 r).fun_sub ((((hasDerivAt_id' r).fun_mul
        ((hasDerivAt_id' r).const_add 1)).mul_const d).div_const 2)).fun_add
        (((((((hasDerivAt_id' r).const_add 1).fun_pow 2).const_mul 19).mul_const (d ^ 2)).div_const
          84)))
      refine this.congr_deriv ?_
      unfold costQn1
      push_cast
      ring
    · have := ((((hasDerivAt_id' r).const_mul 2).fun_sub
        ((((hasDerivAt_id' r).const_mul 2).const_add 1).mul_const d |>.div_const 2)).fun_add
        (((((hasDerivAt_id' r).const_add 1).const_mul 19).mul_const (d ^ 2)).div_const 42))
      refine this.congr_deriv ?_
      unfold costQn2
      ring
  exact SecondJet.const_mul 4 (SecondJet.mul hHf hQ)

theorem cost_z_jet (d r : ℝ) (hr : r < 1) :
    SecondJet (fun y => costZU y d) (costz1 d) (costz2 d) r := by
  have h3 : (0 : ℝ) < 3 - r := by linarith
  have h1 : (0 : ℝ) < 1 - r := by linarith
  have hs3 : HasDerivAt (fun y : ℝ => 3 - y) (-1) r := by
    simpa using (hasDerivAt_id' r).const_sub 3
  have hs1 : HasDerivAt (fun y : ℝ => 1 - y) (-1) r := by
    simpa using (hasDerivAt_id' r).const_sub 1
  constructor
  · have := ((((hasDerivAt_pow 2 r).const_mul 2).fun_mul ((hasDerivAt_id' r).const_add 1)).fun_div
      hs3 h3.ne').fun_add ((((hasDerivAt_id' r).const_mul 2).const_add 1).fun_div (hs1.const_mul 3)
      (by positivity) |>.mul_const d)
    refine (this.sub_const (3 / 2 * d ^ 2)).congr_deriv ?_
    unfold costz1
    push_cast
    field_simp
    ring
  · have := ((((hasDerivAt_id' r).const_mul (-4)).sub_const 8).fun_add
      ((hasDerivAt_const r (72 : ℝ)).fun_div (hs3.fun_pow 2) (by positivity))).fun_add
      ((hasDerivAt_const r d).fun_div (hs1.fun_pow 2) (by positivity))
    refine this.congr_deriv ?_
    unfold costz2
    push_cast
    field_simp
    ring

theorem cost_cF_jet (r : ℝ) : SecondJet costcF costcF1 costcF2 r := by
  constructor
  · have := ((((hasDerivAt_id' r).const_mul 4).const_sub 3).fun_sub
      ((hasDerivAt_pow 2 r).const_mul 2)).fun_add ((hasDerivAt_pow 3 r).const_mul 4) |>.fun_sub
      (hasDerivAt_pow 4 r)
    refine this.congr_deriv ?_
    unfold costcF1
    push_cast
    ring
  · have := ((((hasDerivAt_id' r).const_mul 4).const_sub (-4)).fun_add
      ((hasDerivAt_pow 2 r).const_mul 12)).fun_sub ((hasDerivAt_pow 3 r).const_mul 4)
    refine this.congr_deriv ?_
    unfold costcF2
    push_cast
    ring

theorem cost_h_jet {e d r : ℝ} (hr : 0 < r) (hJ : costJd e d r ≠ 0) :
    SecondJet (costh e d) (costh1 e d) (costh2 e d) r := by
  have hH : SecondJet (costH e d) (costH1 e d) (costH2 e d) r := by
    constructor
    · have := (((hasDerivAt_id' r).fun_add ((hasDerivAt_const r (1 : ℝ)).fun_div
        (hasDerivAt_id' r) hr.ne')).const_mul ((e - 1) * d)).const_sub (4 + 2 * (e + 1) * d)
      refine this.congr_deriv ?_
      unfold costH1
      field_simp
      ring
    · have := ((((hasDerivAt_const r (1 : ℝ)).fun_div (hasDerivAt_pow 2 r)
        (pow_ne_zero 2 hr.ne')).sub_const 1).const_mul ((e - 1) * d))
      refine this.congr_deriv ?_
      unfold costH2
      push_cast
      field_simp
      ring
  have hJ' : SecondJet (costJd e d) (costJ1 e d) (costJ2 e d) r := by
    have hBd : HasDerivAt (fun y : ℝ => 2 + (e + 1 - (e - 1) * y) * d) (-((e - 1) * 1) * d) r :=
      ((((hasDerivAt_id' r).const_mul (e - 1)).const_sub (e + 1)).mul_const d).const_add 2
    have hN : HasDerivAt (fun y : ℝ => 2 * y + ((e + 1) * y - (e - 1)) * d)
        (2 * 1 + ((e + 1) * 1) * d) r :=
      ((hasDerivAt_id' r).const_mul 2).fun_add ((((hasDerivAt_id' r).const_mul (e + 1)).sub_const
        (e - 1)).mul_const d)
    constructor
    · refine ((hBd.fun_pow 2).const_mul 3 |>.fun_add (hN.fun_pow 2)).congr_deriv ?_
      unfold costJ1 costBd costNd
      push_cast
      ring
    · refine ((hBd.const_mul (6 * (e - 1) * d)).fun_neg.fun_add
        (hN.const_mul (2 * (2 + (e + 1) * d)))).congr_deriv ?_
      unfold costJ2
      ring
  constructor
  · refine (hH.1.fun_div hJ'.1 hJ).congr_deriv ?_
    unfold costh1
    field_simp
  · have := (hH.2.fun_div hJ'.1 hJ).fun_sub ((hH.1.fun_mul hJ'.2).fun_div (hJ'.1.fun_pow 2)
      (pow_ne_zero 2 hJ))
    refine this.congr_deriv ?_
    unfold costh2
    field_simp
    ring

/-! ### Bounds on the box -/

section Box

variable {e d r : ℝ}

/-- The shape facts on the box: `9/31 ≤ t ≤ R`, `1 ≤ t_R ≤ 17/16`, `0 ≤ t_RR ≤ 17/152`. -/
theorem cost_T_bounds (he : 13 / 5 ≤ e) (he' : e ≤ 3) (hd : 0 ≤ d) (hd' : d ≤ 1 / 19)
    (hr : 1 / 3 ≤ r) (hr' : r ≤ 7 / 19) :
    9 / 31 ≤ costT r d e ∧ costT r d e ≤ r ∧ 1 ≤ costt1 e d r ∧ costt1 e d r ≤ 17 / 16 ∧
      0 ≤ costt2 e d r ∧ costt2 e d r ≤ 17 / 152 := by
  have hB := cost_B_pos (e := e) (d := d) (r := r) hd (by linarith) (by linarith)
  have hB0 : 0 < costBd e d r := by linarith
  have hBu : costBd e d r ≤ 42 / 19 := by
    unfold costBd
    have : (e + 1 - (e - 1) * r) * d ≤ 4 * (1 / 19) :=
      mul_le_mul (by nlinarith) hd' hd (by norm_num)
    linarith
  have hX : (2 + 2 * d) * (2 + 2 * e * d) - costBd e d r ^ 2 =
      d * (4 * (e - 1) * r + (4 * e - (e + 1 - (e - 1) * r) ^ 2) * d) := by
    unfold costBd; ring
  have hC : (e + 1 - (e - 1) * r) ^ 2 ≤ 16 := by
    have hC0 : 0 ≤ e + 1 - (e - 1) * r := by nlinarith
    have hC4 : e + 1 - (e - 1) * r ≤ 4 := by nlinarith
    have := pow_le_pow_left₀ hC0 hC4 2
    linarith
  have hX0 : 0 ≤ d * (4 * (e - 1) * r + (4 * e - (e + 1 - (e - 1) * r) ^ 2) * d) := by
    apply mul_nonneg hd
    have : -(16 - 4 * e) * d ≤ (4 * e - (e + 1 - (e - 1) * r) ^ 2) * d :=
      mul_le_mul_of_nonneg_right (by linarith) hd
    nlinarith
  have hX1 : d * (4 * (e - 1) * r + (4 * e - (e + 1 - (e - 1) * r) ^ 2) * d) ≤ 68 / 361 := by
    have h1 : d * (4 * (e - 1) * r) ≤ 1 / 19 * (4 * 2 * (7 / 19)) :=
      mul_le_mul hd' (by nlinarith) (by nlinarith) (by norm_num)
    have h2 : d * ((4 * e - (e + 1 - (e - 1) * r) ^ 2) * d) ≤ 12 * d ^ 2 := by
      have : (4 * e - (e + 1 - (e - 1) * r) ^ 2) ≤ 12 := by nlinarith
      nlinarith [sq_nonneg d]
    have h3 : d ^ 2 ≤ (1 / 19) ^ 2 := pow_le_pow_left₀ hd hd' 2
    nlinarith
  have ht1 : 1 ≤ costt1 e d r := by
    unfold costt1
    rw [le_div_iff₀ (by positivity)]
    linarith
  have ht1' : costt1 e d r ≤ 17 / 16 := by
    unfold costt1
    rw [div_le_iff₀ (by positivity)]
    nlinarith
  refine ⟨?_, ?_, ht1, ht1', ?_, ?_⟩
  · rw [cost_T_eq_div, le_div_iff₀ hB0]
    unfold costNd costBd
    have h1 : 120 * (r - 1) ≤ 40 * e * (r - 1) := by nlinarith
    have h2 : d * (142 * r - 98) ≥ 1 / 19 * (142 * r - 98) := by nlinarith
    nlinarith
  · rw [cost_T_eq_div, div_le_iff₀ hB0]
    unfold costNd costBd
    have : 0 ≤ (e - 1) * (1 - r ^ 2) * d := mul_nonneg (mul_nonneg (by linarith) (by nlinarith)) hd
    nlinarith
  · unfold costt2
    have : 0 ≤ e - 1 := by linarith
    positivity
  · have e2 : costt2 e d r = 2 * (e - 1) * d * costt1 e d r / costBd e d r := by
      unfold costt2 costt1; field_simp
    rw [e2, div_le_iff₀ hB0]
    have : 2 * (e - 1) * d ≤ 2 * 2 * (1 / 19) := by nlinarith
    have : 2 * (e - 1) * d * costt1 e d r ≤ 2 * 2 * (1 / 19) * (17 / 16) :=
      mul_le_mul this ht1' (by linarith) (by norm_num)
    nlinarith

theorem cost_Hf_jet (r : ℝ) (hr : 0 ≤ r) : SecondJet costHf costHf1 costHf2 r := by
  have h2 : (0 : ℝ) < r + 2 := by linarith
  have hn := ((hasDerivAt_pow 2 r).const_mul 3).fun_add ((hasDerivAt_id' r).const_mul 10)
  have hd3 := (((hasDerivAt_id' r).add_const 2).fun_pow 3).const_mul 15
  constructor
  · refine ((hn.add_const 10).fun_div hd3 (by positivity)).congr_deriv ?_
    unfold costHf1
    push_cast
    field_simp
    ring
  · have hn' := ((hasDerivAt_pow 2 r).const_mul 3).fun_add ((hasDerivAt_id' r).const_mul 8)
    have hd4 := (((hasDerivAt_id' r).add_const 2).fun_pow 4).const_mul 15
    refine ((hn'.add_const 10).fun_neg.fun_div hd4 (by positivity)).congr_deriv ?_
    unfold costHf2
    push_cast
    field_simp
    ring

/-- The incoming norm on the box: `0 ≤ v ≤ 1/20`, `0 ≤ v_R ≤ 21/100`,
`0 ≤ v_RR ≤ 1/2`. -/
theorem cost_v_bounds (hd : 0 ≤ d) (hd' : d ≤ 1 / 19) (hr : 1 / 3 ≤ r) (hr' : r ≤ 7 / 19) :
    0 ≤ costv d r ∧ costv d r ≤ 1 / 20 ∧ 0 ≤ costv1 d r ∧ costv1 d r ≤ 21 / 100 ∧
      0 ≤ costv2 d r ∧ costv2 d r ≤ 1 / 2 := by
  have hJ := fun x (hx : x ∈ Icc (1 / 3 : ℝ) (7 / 19)) => cost_Hf_jet x (by linarith [hx.1])
  have hHf2 : ∀ x ∈ Icc (1 / 3 : ℝ) (7 / 19), 0 ≤ costHf2 x := fun x hx => by
    have := hx.1; unfold costHf2; positivity
  have hHf1 : ∀ x ∈ Icc (1 / 3 : ℝ) (7 / 19), costHf1 x ≤ 0 := fun x hx => by
    have := hx.1; unfold costHf1
    apply div_nonpos_of_nonpos_of_nonneg _ (by positivity)
    nlinarith
  -- `H_f` decreases and `H_f'` increases
  have a1 : costHf r ≤ costHf (1 / 3) :=
    jet_anti_of (fun x hx => (hJ x hx).1) hHf1 le_rfl hr hr'
  have a2 : costHf (7 / 19) ≤ costHf r :=
    jet_anti_of (fun x hx => (hJ x hx).1) hHf1 hr hr' le_rfl
  have a3 : costHf1 (1 / 3) ≤ costHf1 r :=
    jet_mono_of (fun x hx => (hJ x hx).2) hHf2 le_rfl hr hr'
  have a4 : costHf1 r ≤ costHf1 (7 / 19) :=
    jet_mono_of (fun x hx => (hJ x hx).2) hHf2 hr hr' le_rfl
  have b1 : costHf r ≤ 9 / 125 := a1.trans (by norm_num [costHf])
  have b2 : 7 / 100 ≤ costHf r := le_trans (by norm_num [costHf]) a2
  have b3 : -3 / 100 ≤ costHf1 r := le_trans (by norm_num [costHf1]) a3
  have b4 : costHf1 r ≤ -1 / 40 := a4.trans (by norm_num [costHf1])
  have b5 : 0 ≤ costHf2 r := hHf2 r ⟨hr, hr'⟩
  have b6 : costHf2 r ≤ 1 / 35 := by
    unfold costHf2
    rw [div_le_iff₀ (by positivity)]
    have : (7 / 3 : ℝ) ^ 5 ≤ (r + 2) ^ 5 := pow_le_pow_left₀ (by norm_num) (by linarith) 5
    nlinarith
  have hd2 : d ^ 2 ≤ (1 / 19) ^ 2 := pow_le_pow_left₀ hd hd' 2
  have q1 : 9 / 100 ≤ costQn d r := by
    unfold costQn
    have : r * (1 + r) * d ≤ 7 / 19 * (26 / 19) * (1 / 19) :=
      mul_le_mul (mul_le_mul hr' (by linarith) (by linarith) (by norm_num)) hd' hd (by norm_num)
    nlinarith [sq_nonneg ((1 + r) * d)]
  have q2 : costQn d r ≤ 7 / 50 := by
    unfold costQn
    have : 0 ≤ r * (1 + r) * d := by positivity
    have : (1 + r) ^ 2 * d ^ 2 ≤ (26 / 19) ^ 2 * (1 / 19) ^ 2 :=
      mul_le_mul (pow_le_pow_left₀ (by linarith) (by linarith) 2) hd2 (by positivity)
        (by norm_num)
    nlinarith
  have q3 : 3 / 5 ≤ costQn1 d r := by
    unfold costQn1
    have : (1 + 2 * r) * d ≤ (33 / 19) * (1 / 19) :=
      mul_le_mul (by linarith) hd' hd (by norm_num)
    have : 0 ≤ (1 + r) * d ^ 2 := by positivity
    nlinarith
  have q4 : costQn1 d r ≤ 3 / 4 := by
    unfold costQn1
    have : 0 ≤ (1 + 2 * r) * d := by positivity
    have : (1 + r) * d ^ 2 ≤ (26 / 19) * (1 / 19) ^ 2 :=
      mul_le_mul (by linarith) hd2 (by positivity) (by norm_num)
    nlinarith
  have q5 : 19 / 10 ≤ costQn2 d r := by unfold costQn2; nlinarith
  have q6 : costQn2 d r ≤ 2 := by unfold costQn2; nlinarith
  unfold costv costv1 costv2
  refine ⟨by positivity, ?_, ?_, ?_, ?_, ?_⟩
  · have := mul_le_mul b1 q2 (by linarith) (by norm_num); linarith
  · have h1 := mul_le_mul b2 q3 (by norm_num) (by linarith)
    have h2 : -3 / 100 * (7 / 50) ≤ costHf1 r * costQn d r := by nlinarith
    linarith
  · have h1 := mul_le_mul b1 q4 (by linarith) (by norm_num)
    have h2 : costHf1 r * costQn d r ≤ -1 / 40 * (9 / 100) := by nlinarith
    linarith
  · have h1 : 0 ≤ costHf2 r * costQn d r := by nlinarith
    have h2 : -3 / 100 * (3 / 4) ≤ costHf1 r * costQn1 d r := by nlinarith
    have h3 := mul_le_mul b2 q5 (by norm_num) (by linarith)
    linarith
  · have h1 : costHf2 r * costQn d r ≤ 1 / 35 * (7 / 50) := mul_le_mul b6 q2 (by linarith) (by norm_num)
    have h2 : costHf1 r * costQn1 d r ≤ -1 / 40 * (3 / 5) := by nlinarith
    have h3 := mul_le_mul b1 q6 (by linarith) (by norm_num)
    linarith

/-- The central shape function on the box: `1/10 ≤ z ≤ 1/5`, `3/4 ≤ z_R ≤ 16/15`,
`7/2 ≤ z_RR ≤ 13/3`. -/
theorem cost_z_bounds (hd : 0 ≤ d) (hd' : d ≤ 1 / 19) (hr : 1 / 3 ≤ r) (hr' : r ≤ 7 / 19) :
    1 / 10 ≤ costZU r d ∧ costZU r d ≤ 1 / 5 ∧ 3 / 4 ≤ costz1 d r ∧ costz1 d r ≤ 16 / 15 ∧
      7 / 2 ≤ costz2 d r ∧ costz2 d r ≤ 13 / 3 := by
  have hz2 : ∀ x ∈ Icc (1 / 3 : ℝ) (7 / 19), 7 / 2 ≤ costz2 d x ∧ costz2 d x ≤ 13 / 3 := by
    intro x hx
    have h3 : (50 / 19 : ℝ) ≤ 3 - x := by linarith [hx.2]
    have h3' : 3 - x ≤ 8 / 3 := by linarith [hx.1]
    have h1 : (12 / 19 : ℝ) ≤ 1 - x := by linarith [hx.2]
    have c1 : (50 / 19 : ℝ) ^ 3 ≤ (3 - x) ^ 3 := pow_le_pow_left₀ (by norm_num) h3 3
    have c2 : (3 - x) ^ 3 ≤ (8 / 3 : ℝ) ^ 3 := pow_le_pow_left₀ (by linarith) h3' 3
    have c3 : (12 / 19 : ℝ) ^ 3 ≤ (1 - x) ^ 3 := pow_le_pow_left₀ (by norm_num) h1 3
    have e1 : 144 / (8 / 3 : ℝ) ^ 3 ≤ 144 / (3 - x) ^ 3 :=
      div_le_div_of_nonneg_left (by norm_num) (by positivity) c2
    have e2 : 144 / (3 - x) ^ 3 ≤ 144 / (50 / 19 : ℝ) ^ 3 :=
      div_le_div_of_nonneg_left (by norm_num) (by positivity) c1
    have e3 : 2 * d / (1 - x) ^ 3 ≤ 2 * (1 / 19) / (12 / 19 : ℝ) ^ 3 :=
      div_le_div₀ (by norm_num) (by linarith) (by positivity) c3
    have e4 : 0 ≤ 2 * d / (1 - x) ^ 3 := by
      have : 0 < 1 - x := by linarith
      positivity
    unfold costz2
    norm_num at e1 e2 e3 ⊢
    constructor <;> linarith
  have hJ := fun x (hx : x ∈ Icc (1 / 3 : ℝ) (7 / 19)) => cost_z_jet d x (by linarith [hx.2])
  have m1 : costz1 d (1 / 3) ≤ costz1 d r :=
    jet_mono_of (fun x hx => (hJ x hx).2) (fun x hx => by linarith [(hz2 x hx).1]) le_rfl hr hr'
  have m2 : costz1 d r ≤ costz1 d (7 / 19) :=
    jet_mono_of (fun x hx => (hJ x hx).2) (fun x hx => by linarith [(hz2 x hx).1]) hr hr' le_rfl
  refine ⟨?_, ?_, ?_, ?_, (hz2 r ⟨hr, hr'⟩).1, (hz2 r ⟨hr, hr'⟩).2⟩
  · unfold costZU
    have h3 : 0 < 3 - r := by linarith
    have h1 : 0 < 1 - r := by linarith
    have a : 1 / 10 ≤ 2 * r ^ 2 * (1 + r) / (3 - r) := by
      rw [le_div_iff₀ h3]; nlinarith
    have b : 3 / 2 * d ^ 2 ≤ (1 + 2 * r) / (3 * (1 - r)) * d := by
      have : 5 / 6 ≤ (1 + 2 * r) / (3 * (1 - r)) := by
        rw [le_div_iff₀ (by positivity)]; nlinarith
      nlinarith
    linarith
  · unfold costZU
    have h3 : 50 / 19 ≤ 3 - r := by linarith
    have h1 : 12 / 19 ≤ 1 - r := by linarith
    have a : 2 * r ^ 2 * (1 + r) / (3 - r) ≤ 2 * (7 / 19) ^ 2 * (26 / 19) / (50 / 19) := by
      apply div_le_div₀ (by positivity) _ (by norm_num) h3
      have : r ^ 2 ≤ (7 / 19) ^ 2 := pow_le_pow_left₀ (by linarith) hr' 2
      have : r ^ 2 * (1 + r) ≤ (7 / 19) ^ 2 * (26 / 19) :=
        mul_le_mul this (by linarith) (by linarith) (by norm_num)
      linarith
    have b : (1 + 2 * r) / (3 * (1 - r)) * d ≤ (33 / 19) / (3 * (12 / 19)) * (1 / 19) := by
      apply mul_le_mul _ hd' hd (by norm_num)
      exact div_le_div₀ (by norm_num) (by linarith) (by norm_num) (by linarith)
    have c : 0 ≤ 3 / 2 * d ^ 2 := by positivity
    norm_num at a b
    linarith
  · refine le_trans ?_ m1
    unfold costz1
    norm_num
    linarith
  · refine m2.trans ?_
    unfold costz1
    norm_num
    linarith

/-- The quotient-rule bounds for `h = H/J` from bounds on `H, J` and their derivatives. -/
theorem cost_h_abs {H H1 H2 J J1 J2 : ℝ} (hH : 4 ≤ H) (hH' : H ≤ 22 / 5)
    (hH1' : H1 ≤ 16 / 19) (hH2 : -(108 / 19) ≤ H2) (hJ : 12 ≤ J) (hJ1 : 0 ≤ J1)
    (hJ1' : J1 ≤ 10 / 3) (hJ2 : 0 ≤ J2) (hJ2' : J2 ≤ 10) :
    0 ≤ H / J ∧ H / J ≤ 11 / 30 ∧ H1 / J - H * J1 / J ^ 2 ≤ 2 / 25 ∧
      -1 ≤ H2 / J - 2 * (H1 * J1) / J ^ 2 - H * J2 / J ^ 2 + 2 * (H * J1 ^ 2) / J ^ 3 := by
  have hJ0 : 0 < J := by linarith
  have hJsq : 144 ≤ J ^ 2 := by nlinarith
  refine ⟨div_nonneg (by linarith) hJ0.le, ?_, ?_, ?_⟩
  · rw [div_le_iff₀ hJ0]; linarith
  · have a : H1 / J ≤ 16 / 19 / 12 := div_le_div₀ (by norm_num) hH1' (by norm_num) hJ
    have b : 0 ≤ H * J1 / J ^ 2 := by
      have : 0 ≤ H := by linarith
      positivity
    norm_num at a
    linarith
  · have a : -(108 / 19) / 12 ≤ H2 / J := by
      rw [le_div_iff₀ hJ0]; nlinarith
    have b : 2 * (H1 * J1) / J ^ 2 ≤ 2 * (16 / 19 * (10 / 3)) / 144 := by
      apply div_le_div₀ (by norm_num) _ (by norm_num) hJsq
      have := mul_le_mul hH1' hJ1' hJ1 (by norm_num)
      linarith
    have c : H * J2 / J ^ 2 ≤ 22 / 5 * 10 / 144 :=
      div_le_div₀ (by norm_num) (mul_le_mul hH' hJ2' hJ2 (by norm_num)) (by norm_num) hJsq
    have d0 : 0 ≤ 2 * (H * J1 ^ 2) / J ^ 3 := by
      have : 0 ≤ H := by linarith
      positivity
    norm_num at a b c
    linarith

/-- The radical correction's factors on the box: `0 ≤ h ≤ 11/30`,
`h_R ≤ 2/25`, `h_RR ≥ -1`. -/
theorem cost_h_bounds (he : 13 / 5 ≤ e) (he' : e ≤ 3) (hd : 0 ≤ d) (hd' : d ≤ 1 / 19)
    (hr : 1 / 3 ≤ r) (hr' : r ≤ 7 / 19) :
    0 < costJd e d r ∧ 0 ≤ costh e d r ∧ costh e d r ≤ 11 / 30 ∧ costh1 e d r ≤ 2 / 25 ∧
      -1 ≤ costh2 e d r := by
  have hr0 : 0 < r := by linarith
  have hB := cost_B_pos (e := e) (d := d) (r := r) hd (by linarith) (by linarith)
  have hBu : costBd e d r ≤ 42 / 19 := by
    unfold costBd
    have : (e + 1 - (e - 1) * r) * d ≤ 4 * (1 / 19) :=
      mul_le_mul (by nlinarith) hd' hd (by norm_num)
    linarith
  have hN : 12 / 19 ≤ costNd e d r ∧ costNd e d r ≤ 14 / 19 := by
    unfold costNd
    have hE : -2 / 3 ≤ (e + 1) * r - (e - 1) := by nlinarith
    have hE' : (e + 1) * r - (e - 1) ≤ 0 := by nlinarith
    constructor <;> nlinarith
  have hJ : 12 ≤ costJd e d r := by unfold costJd; nlinarith [sq_nonneg (costNd e d r)]
  have hJ0 : 0 < costJd e d r := by linarith
  -- `H`
  have hrr : 2 ≤ r + 1 / r ∧ r + 1 / r ≤ 10 / 3 := by
    constructor
    · have : 2 * r ≤ r * r + 1 := by nlinarith [sq_nonneg (r - 1)]
      have : 2 ≤ (r * r + 1) / r := by rw [le_div_iff₀ hr0]; linarith
      calc 2 ≤ (r * r + 1) / r := this
        _ = r + 1 / r := by field_simp
    · have e1 : r + 1 / r = (r * r + 1) / r := by field_simp
      rw [e1, div_le_iff₀ hr0]
      nlinarith
  have hH : 4 ≤ costH e d r ∧ costH e d r ≤ 22 / 5 := by
    unfold costH
    have w1 : 0 ≤ 2 * (e + 1) - (e - 1) * (r + 1 / r) := by nlinarith
    have w2 : 2 * (e + 1) - (e - 1) * (r + 1 / r) ≤ 4 := by nlinarith
    have e1 : 4 + 2 * (e + 1) * d - (e - 1) * d * (r + 1 / r) =
        4 + d * (2 * (e + 1) - (e - 1) * (r + 1 / r)) := by ring
    rw [e1]
    constructor
    · nlinarith
    · have : d * (2 * (e + 1) - (e - 1) * (r + 1 / r)) ≤ 1 / 19 * 4 :=
        mul_le_mul hd' w2 w1 (by norm_num)
      linarith
  have hH1 : 0 ≤ costH1 e d r ∧ costH1 e d r ≤ 16 / 19 := by
    unfold costH1
    have a : 1 / r ^ 2 ≤ 9 := by
      rw [div_le_iff₀ (by positivity)]; nlinarith
    have b : 1 ≤ 1 / r ^ 2 := by
      rw [le_div_iff₀ (by positivity)]; nlinarith
    have c : (e - 1) * d ≤ 2 * (1 / 19) := mul_le_mul (by linarith) hd' hd (by norm_num)
    have c0 : 0 ≤ (e - 1) * d := mul_nonneg (by linarith) hd
    constructor
    · exact mul_nonneg c0 (by linarith)
    · have := mul_le_mul c (by linarith : 1 / r ^ 2 - 1 ≤ 8) (by linarith) (by norm_num)
      linarith
  have hH2 : -(108 / 19) ≤ costH2 e d r := by
    unfold costH2
    have a : 1 / r ^ 3 ≤ 27 := by
      rw [div_le_iff₀ (by positivity)]
      have : (1 / 3 : ℝ) ^ 3 ≤ r ^ 3 := pow_le_pow_left₀ (by norm_num) hr 3
      linarith
    have c : 2 * (e - 1) * d ≤ 2 * 2 * (1 / 19) := by nlinarith
    have e1 : 2 * (e - 1) * d / r ^ 3 = 2 * (e - 1) * d * (1 / r ^ 3) := by ring
    rw [e1]
    have c0 : 0 ≤ 2 * (e - 1) * d := by nlinarith
    have := mul_le_mul c a (by positivity) (by norm_num)
    linarith
  have hJ1 : 0 ≤ costJ1 e d r ∧ costJ1 e d r ≤ 10 / 3 := by
    unfold costJ1
    have a : 6 * (e - 1) * d * costBd e d r ≤ 6 * 2 * (1 / 19) * (42 / 19) :=
      mul_le_mul (by nlinarith) hBu (by linarith) (by norm_num)
    have a0 : 0 ≤ 6 * (e - 1) * d * costBd e d r :=
      mul_nonneg (by nlinarith) (by linarith)
    have b : 2 * 2 * (12 / 19) ≤ 2 * (2 + (e + 1) * d) * costNd e d r :=
      mul_le_mul (by nlinarith) hN.1 (by norm_num) (by nlinarith)
    have b' : 2 * (2 + (e + 1) * d) * costNd e d r ≤ 2 * (2 + 4 * (1 / 19)) * (14 / 19) :=
      mul_le_mul (by nlinarith) hN.2 (by linarith [hN.1]) (by norm_num)
    constructor <;> nlinarith
  have hJ2 : 0 ≤ costJ2 e d r ∧ costJ2 e d r ≤ 10 := by
    unfold costJ2
    have a : (e - 1) * d ≤ 2 * (1 / 19) := mul_le_mul (by linarith) hd' hd (by norm_num)
    have a0 : 0 ≤ (e - 1) * d := mul_nonneg (by linarith) hd
    have b : 2 + (e + 1) * d ≤ 2 + 4 * (1 / 19) := by nlinarith
    have b0 : 0 ≤ 2 + (e + 1) * d := by nlinarith
    constructor
    · positivity
    · have h1 : ((e - 1) * d) ^ 2 ≤ (2 * (1 / 19)) ^ 2 := pow_le_pow_left₀ a0 a 2
      have h2 : (2 + (e + 1) * d) ^ 2 ≤ (2 + 4 * (1 / 19)) ^ 2 := pow_le_pow_left₀ b0 b 2
      have e1 : 6 * (e - 1) ^ 2 * d ^ 2 = 6 * ((e - 1) * d) ^ 2 := by ring
      rw [e1]
      norm_num at h1 h2 ⊢
      linarith
  have := cost_h_abs hH.1 hH.2 hH1.2 hH2 hJ hJ1.1 hJ1.2 hJ2.1 hJ2.2
  unfold costh costh1 costh2
  exact ⟨hJ0, this⟩

end Box

/-! ### Concavity in `R` -/

/-- `p(a) ≥ 1/40` for `a ≥ 9/31` and `p(a) ≥ 1/28` for `a ≥ 1/3`. -/
theorem cost_p_lower {a : ℝ} (ha : 9 / 31 ≤ a) : 1 / 40 ≤ jetp a ∧ (1 / 3 ≤ a → 1 / 28 ≤ jetp a) := by
  have h3 : (0 : ℝ) < 3 + a ^ 2 := by positivity
  unfold jetp
  refine ⟨?_, fun h => ?_⟩
  · rw [le_div_iff₀ h3]; nlinarith
  · rw [le_div_iff₀ h3]; nlinarith

/-- `F` and its derivatives on `[1/3, 7/19]`: `0 ≤ F ≤ 33/20`, `-5 ≤ F' ≤ 0`, `F'' ≥ 0`. -/
theorem cost_cF_bounds {r : ℝ} (hr : 1 / 3 ≤ r) (hr' : r ≤ 7 / 19) :
    0 ≤ costcF r ∧ costcF r ≤ 33 / 20 ∧ -5 ≤ costcF1 r ∧ costcF1 r ≤ 0 ∧ 0 ≤ costcF2 r := by
  have e1 : costcF r = (1 - r) ^ 2 * ((1 + r) * (3 - r)) := by unfold costcF; ring
  have a1 : (1 - r) ^ 2 ≤ 4 / 9 := by nlinarith
  have a2 : (1 + r) * (3 - r) ≤ 37 / 10 := by nlinarith
  have a3 : 0 ≤ (1 + r) * (3 - r) := mul_nonneg (by linarith) (by linarith)
  have hr2 : r ^ 2 ≤ 49 / 361 := by nlinarith
  have hr3 : r ^ 3 ≤ 343 / 6859 := by
    have := pow_le_pow_left₀ (by linarith : (0 : ℝ) ≤ r) hr' 3; norm_num at this; linarith
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [e1]; positivity
  · rw [e1]
    have := mul_le_mul a1 a2 a3 (by norm_num)
    linarith
  · unfold costcF1; nlinarith
  · unfold costcF1; nlinarith
  · unfold costcF2; nlinarith

/-- `0 ≤ κ ≤ 1/480`. -/
theorem cost_kap_bounds {e d : ℝ} (he : 1 ≤ e) (he' : e ≤ 3) (hd : 0 ≤ d) (hd' : d ≤ 1 / 19) :
    0 ≤ costkap e d ∧ costkap e d ≤ 1 / 480 := by
  unfold costkap
  refine ⟨by positivity, ?_⟩
  rw [div_le_iff₀ (by positivity)]
  have a : (e - 1) ^ 2 ≤ 4 := by nlinarith
  have b : d ^ 2 ≤ 1 / 361 := by nlinarith
  have c := mul_le_mul a b (by positivity) (by norm_num)
  nlinarith

theorem cost_grpK {a b c t1 t2 : ℝ} (ha : a ≤ -9 / 100) (hb : b ≤ -2 / 25) (hc : c ≤ 0)
    (ht1 : 1 ≤ t1) (ht2 : 0 ≤ t2) : a + (b * t1 ^ 2 + c * t2) ≤ -17 / 100 := by
  have h0 : 1 ≤ t1 ^ 2 := by nlinarith
  have h1 : b * t1 ^ 2 ≤ b * 1 := mul_le_mul_of_nonpos_left h0 (by linarith)
  have h2 : c * t2 ≤ 0 := mul_nonpos_of_nonpos_of_nonneg hc ht2
  linarith

theorem cost_grpG {v v1 v2 G G1 G2 : ℝ} (hv : 0 ≤ v) (hv' : v ≤ 1 / 20) (hv1' : v1 ≤ 21 / 100)
    (hv2' : v2 ≤ 1 / 2) (hG : 0 ≤ G) (hG' : G ≤ 3 / 25) (hG1 : 0 ≤ G1)
    (hG1' : G1 ≤ 8 / 25) (hG2 : G2 ≤ 1 / 50) : v2 * G + 2 * (v1 * G1) + v * G2 ≤ 49 / 250 := by
  have h1 := mul_le_mul hv2' hG' hG (by norm_num)
  have h2 : v1 * G1 ≤ 21 / 100 * (8 / 25) :=
    (mul_le_mul_of_nonneg_right hv1' hG1).trans (mul_le_mul_of_nonneg_left hG1' (by norm_num))
  have h3 : v * G2 ≤ 1 / 20 * (1 / 50) :=
    (mul_le_mul_of_nonneg_left hG2 hv).trans (mul_le_mul_of_nonneg_right hv' (by norm_num))
  linarith

theorem cost_grpP {z z1 z2 P P1 P2 : ℝ} (hz : 1 / 10 ≤ z) (hz1 : 3 / 4 ≤ z1) (hz2 : 7 / 2 ≤ z2)
    (hP : 3 / 50 ≤ P) (hP1 : 7 / 20 ≤ P1) (hP2 : 1 ≤ P2) :
    1 / 10 ≤ 1 / 8 * (z2 * P + 2 * (z1 * P1) + z * P2) := by
  have h1 := mul_le_mul hz2 hP (by norm_num) (by linarith)
  have h2 := mul_le_mul hz1 hP1 (by norm_num) (by linarith)
  have h3 := mul_le_mul hz hP2 (by norm_num) (by linarith)
  linarith

theorem cost_grpQ {v v1 v2 z z1 z2 Q Q1 Q2 : ℝ} (hv : 0 ≤ v) (hv' : v ≤ 1 / 20) (hv1 : 0 ≤ v1)
    (hv1' : v1 ≤ 21 / 100) (hv2 : 0 ≤ v2) (hv2' : v2 ≤ 1 / 2) (hz : 0 ≤ z) (hz' : z ≤ 1 / 5)
    (hz1 : 0 ≤ z1) (hz1' : z1 ≤ 16 / 15) (hz2 : 0 ≤ z2) (hz2' : z2 ≤ 13 / 3) (hQ : 0 ≤ Q)
    (hQ' : Q ≤ 2 / 3) (hQ1 : Q1 ≤ 0) (hQ2 : Q2 ≤ 0) :
    1 / 8 * ((v2 * z + 2 * (v1 * z1) + v * z2) * Q + 2 * ((v1 * z + v * z1) * Q1) + v * z * Q2) ≤
      8 / 125 := by
  have a1 := mul_le_mul hv2' hz' hz (by norm_num)
  have a2 := mul_le_mul hv1' hz1' hz1 (by norm_num)
  have a3 := mul_le_mul hv' hz2' hz2 (by norm_num)
  have hX : 0 ≤ v2 * z + 2 * (v1 * z1) + v * z2 := by positivity
  have hX' : v2 * z + 2 * (v1 * z1) + v * z2 ≤ 1 / 2 * (1 / 5) + 2 * (21 / 100 * (16 / 15)) +
      1 / 20 * (13 / 3) := by linarith
  have b1 := mul_le_mul hX' hQ' hQ (by norm_num)
  have b2 : (v1 * z + v * z1) * Q1 ≤ 0 := mul_nonpos_of_nonneg_of_nonpos (by positivity) hQ1
  have b3 : v * z * Q2 ≤ 0 := mul_nonpos_of_nonneg_of_nonpos (by positivity) hQ2
  linarith

theorem cost_grpC {κ F F1 F2 h h1 h2 : ℝ} (hκ : 0 ≤ κ) (hκ' : κ ≤ 1 / 480) (hF : 0 ≤ F)
    (hF' : F ≤ 33 / 20) (hF1 : -5 ≤ F1) (hF1' : F1 ≤ 0) (hF2 : 0 ≤ F2) (hh : 0 ≤ h)
    (hh' : h ≤ 11 / 30) (hh1 : h1 ≤ 2 / 25) (hh2 : -1 ≤ h2) :
    -(1 / 200) ≤ κ * (F2 * (h * h) + 2 * (F1 * (h1 * h + h * h1)) +
      F * (h2 * h + 2 * (h1 * h1) + h * h2)) := by
  have c1 : 0 ≤ F2 * (h * h) := by positivity
  have hFh : -(11 / 6) ≤ F1 * h := by nlinarith
  have hFh0 : F1 * h ≤ 0 := mul_nonpos_of_nonpos_of_nonneg hF1' hh
  have c2 : (F1 * h) * (2 / 25) ≤ (F1 * h) * h1 := by nlinarith
  have c3 : -(11 / 15) ≤ h2 * h + 2 * (h1 * h1) + h * h2 := by nlinarith [sq_nonneg h1]
  have c4 : -(11 / 15) * (33 / 20) ≤ F * (h2 * h + 2 * (h1 * h1) + h * h2) := by nlinarith
  have hX : -(12 / 5) ≤ F2 * (h * h) + 2 * (F1 * (h1 * h + h * h1)) +
      F * (h2 * h + 2 * (h1 * h1) + h * h2) := by
    have e1 : 2 * (F1 * (h1 * h + h * h1)) = 4 * ((F1 * h) * h1) := by ring
    rw [e1]
    linarith
  nlinarith

/-- **Concavity in `R`**: on `0 ≤ d ≤ 1/19`, `13/5 ≤ e ≤ 3`, the minimum of the
cancelled score over `R ∈ [1/3, 7/19]` is at an end. -/
theorem cost_score_concave {e d c r : ℝ} (he : 13 / 5 ≤ e) (he' : e ≤ 3) (hd : 0 ≤ d)
    (hd' : d ≤ 1 / 19) (h1 : c < costScore e d (1 / 3)) (h2 : c < costScore e d (7 / 19))
    (hr : 1 / 3 ≤ r) (hr' : r ≤ 7 / 19) : c < costScore e d r := by
  have hB : ∀ x ∈ Icc (1 / 3 : ℝ) (7 / 19), costBd e d x ≠ 0 := fun x hx =>
    (by linarith [cost_B_pos (e := e) hd (by linarith) (by linarith [hx.2] : x ≤ 1)] :
      (0 : ℝ) < costBd e d x).ne'
  have hJd : ∀ x ∈ Icc (1 / 3 : ℝ) (7 / 19), costJd e d x ≠ 0 := fun x hx =>
    (cost_h_bounds he he' hd hd' hx.1 hx.2).1.ne'
  have hx0 : ∀ x ∈ Icc (1 / 3 : ℝ) (7 / 19), 0 < x := fun x hx => by linarith [hx.1]
  have hx1 : ∀ x ∈ Icc (1 / 3 : ℝ) (7 / 19), x < 1 := fun x hx => by linarith [hx.2]
  have hJ := fun x (hx : x ∈ Icc (1 / 3 : ℝ) (7 / 19)) =>
    SecondJet.sub (SecondJet.add (SecondJet.sub (SecondJet.add
      (SecondJet.add (jet_k_jet x) (SecondJet.comp (jet_k_jet _) (cost_T_jet (hB x hx))))
      (SecondJet.mul (cost_v_jet d x (hx0 x hx).le) (SecondJet.add (jet_g_jet x)
        (SecondJet.comp (jet_g_jet _) (cost_T_jet (hB x hx))))))
      (SecondJet.const_mul (1 / 8) (SecondJet.mul (cost_z_jet d x (hx1 x hx)) (SecondJet.add (jet_p_jet x)
        (SecondJet.comp (jet_p_jet _) (cost_T_jet (hB x hx)))))))
      (SecondJet.const_mul (1 / 8) (SecondJet.mul (SecondJet.mul (cost_v_jet d x (hx0 x hx).le)
        (cost_z_jet d x (hx1 x hx))) (SecondJet.add (jet_q_jet x)
        (SecondJet.comp (jet_q_jet _) (cost_T_jet (hB x hx)))))))
      (SecondJet.const_mul (costkap e d) (SecondJet.mul (cost_cF_jet x)
        (SecondJet.mul (cost_h_jet (hx0 x hx) (hJd x hx)) (cost_h_jet (hx0 x hx) (hJd x hx)))))
  refine jet_concave_lt (f := fun y => costScore e d y) hJ (fun x hx => ?_) h1 h2 ⟨hr, hr'⟩
  clear hJ hB hJd hx0 hx1
  obtain ⟨hx1, hx2⟩ := hx
  obtain ⟨T1, T2, t1a, t1b, t2a, t2b⟩ := cost_T_bounds he he' hd hd' hx1 hx2
  have hT2 : costT x d e ≤ 7 / 19 := T2.trans hx2
  have hx1' : 9 / 31 ≤ x := by linarith
  obtain ⟨gx0, gx1, g1x0, g1x1, g1x2, g2x⟩ := jet_g_bounds hx1' hx2
  obtain ⟨gT0, gT1, g1T0, g1T1, -, g2T⟩ := jet_g_bounds T1 hT2
  obtain ⟨px0, p1x0, p1x1, p2x⟩ := jet_p_bounds hx1' hx2
  obtain ⟨pT0, p1T0, -, p2T⟩ := jet_p_bounds T1 hT2
  obtain ⟨qx0, qx1, q1x, q2x⟩ := jet_q_bounds (a := x) (by linarith) (by linarith)
  obtain ⟨qT0, qT1, q1T, q2T⟩ := jet_q_bounds (a := costT x d e) (by linarith) (by linarith)
  obtain ⟨v0, v0', v10, v1', v20, v2'⟩ := cost_v_bounds hd hd' hx1 hx2
  obtain ⟨z0, z0', z10, z1', z20, z2'⟩ := cost_z_bounds hd hd' hx1 hx2
  obtain ⟨-, h0, h0', h1', h2'⟩ := cost_h_bounds he he' hd hd' hx1 hx2
  obtain ⟨F0, F0', F10, F1', F20⟩ := cost_cF_bounds hx1 hx2
  obtain ⟨κ0, κ0'⟩ := cost_kap_bounds (by linarith) he' hd hd'
  have pl := (cost_p_lower hx1').2 hx1
  have pT := (cost_p_lower T1).1
  have K := cost_grpK (jet_k2_le' hx1 hx2) (jet_k2_le T1 hT2) (jet_k1_neg T1 hT2).le t1a t2a
  have G1a : 0 ≤ jetg1 x + jetg1 (costT x d e) * costt1 e d x :=
    add_nonneg g1x0.le (mul_nonneg g1T0.le (by linarith))
  have G1b : jetg1 x + jetg1 (costT x d e) * costt1 e d x ≤ 8 / 25 := by
    have := mul_le_mul g1T1 t1b (by linarith) (by norm_num)
    linarith [g1x2 hx1]
  have G2b : jetg2 x + (jetg2 (costT x d e) * costt1 e d x ^ 2 +
      jetg1 (costT x d e) * costt2 e d x) ≤ 1 / 50 := by
    have a := mul_nonpos_of_nonpos_of_nonneg g2T (sq_nonneg (costt1 e d x))
    have b := mul_le_mul g1T1 t2b t2a (by norm_num)
    linarith
  have G := cost_grpG v0 v0' v1' v2' (add_nonneg gx0.le gT0.le) (by linarith) G1a G1b G2b
  have P1b : 7 / 20 ≤ jetp1 x + jetp1 (costT x d e) * costt1 e d x := by
    have := mul_le_mul p1T0 t1a (by norm_num) (by linarith)
    linarith [p1x1 hx1]
  have P2b : 1 ≤ jetp2 x + (jetp2 (costT x d e) * costt1 e d x ^ 2 +
      jetp1 (costT x d e) * costt2 e d x) := by
    have h1 : 1 ≤ costt1 e d x ^ 2 := one_le_pow₀ t1a
    have a := mul_le_mul p2T h1 (by norm_num) (by linarith)
    have b := mul_nonneg (by linarith : (0 : ℝ) ≤ jetp1 (costT x d e)) t2a
    linarith
  have P := cost_grpP z0 z10 z20 (by linarith : 3 / 50 ≤ jetp x + jetp (costT x d e)) P1b P2b
  have Q1b : jetq1 x + jetq1 (costT x d e) * costt1 e d x ≤ 0 := by
    have := mul_nonpos_of_nonpos_of_nonneg q1T (by linarith : (0 : ℝ) ≤ costt1 e d x)
    linarith
  have Q2b : jetq2 x + (jetq2 (costT x d e) * costt1 e d x ^ 2 +
      jetq1 (costT x d e) * costt2 e d x) ≤ 0 := by
    have a := mul_nonpos_of_nonpos_of_nonneg q2T (sq_nonneg (costt1 e d x))
    have b := mul_nonpos_of_nonpos_of_nonneg q1T t2a
    linarith
  have Q := cost_grpQ v0 v0' v10 v1' v20 v2' (by linarith) z0' (by linarith) z1' (by linarith) z2'
    (add_nonneg qx0.le qT0.le) (by linarith) Q1b Q2b
  have C := cost_grpC κ0 κ0' F0 F0' F10 F1' F20 h0 h0' h1' h2'
  linarith only [K, G, P, Q, C]

end SmoothedOctagon
