module

public import SmoothedOctagon.Exclusion.Mixed.ShortHand.Heavy.S4HandW3d

/-!
# Gate S4, hand proof W3 (e): the normalized cost numerator is positive

For fixed `x`, every atom of the numerator `N = (781250/3)n` (`a, B, K, D, v, E, B_x, D_x, E_x`) is
a polynomial of degree at most two in `d`; their second-order jets in `d` are composed by the
product rule (`HL46J`) before any expansion, and the resulting second derivative is the explicit
polynomial `N_dd = P(d, x - 2)` (`hl46_w3_n_jet`). The monomial rule gives `P > 0`,
`N_d(2 + h, 0) > 0` and `N(2 + h, 0) > 0`, hence `N_d > 0` and `N(x, d) ≥ N(x, 0) > 0`
(`hl46_w3_n_pos`), i.e. `f > -1/25`.

`N(2 + h, 0) > 0` is read off directly by the monomial rule (only its `h⁷`, `h⁸` coefficients
are positive).

## Main API

* `hl46W3P`, `hl46W3Nd0`, `hl46W3N0`, `hl46_w3_n_jet`, `hl46_w3_n_pos`.
-/

@[expose] public section

namespace SmoothedOctagon

open Set

/-- The polynomial `N_dd = P(d, h)`. -/
noncomputable def hl46W3P (d h : ℝ) : ℝ :=
  -11995620 * d ^ 6 * h ^ 2 - 110359704 * d ^ 6 * h - 172736928 * d ^ 6 + 36678915 * d ^ 5 * h ^ 3 +
    (488636967 / 2) * d ^ 5 * h ^ 2 + 1247667512 * d ^ 5 * h + (6590962651 / 5) * d ^ 5 -
    20723625 * d ^ 4 * h ^ 4 - 941376475 * d ^ 4 * h ^ 3 - (16599016915 / 2) * d ^ 4 * h ^ 2 -
    20487166960 * d ^ 4 * h - 16335523100 * d ^ 4 - 2028000 * d ^ 3 * h ^ 5 +
    281242000 * d ^ 3 * h ^ 4 + (5588014250 / 3) * d ^ 3 * h ^ 3 - (3324019790 / 3) * d ^ 3 * h ^ 2 -
    13790558990 * d ^ 3 * h - 14241417060 * d ^ 3 + 1473750 * d ^ 2 * h ^ 6 -
    20020700 * d ^ 2 * h ^ 5 + 118598600 * d ^ 2 * h ^ 4 + 2389233430 * d ^ 2 * h ^ 3 +
    6414761770 * d ^ 2 * h ^ 2 + 6307847210 * d ^ 2 * h + 2694185780 * d ^ 2 - 45000 * d * h ^ 7 +
    (12419625 / 2) * d * h ^ 6 + 69698425 * d * h ^ 5 + 488800325 * d * h ^ 4 +
    2339505200 * d * h ^ 3 + (11181177325 / 2) * d * h ^ 2 + 6979205375 * d * h + 4131923600 * d +
    28125 * h ^ 8 + (433750 / 3) * h ^ 7 + (4070875 / 6) * h ^ 6 + (49876625 / 3) * h ^ 5 +
    (477120125 / 3) * h ^ 4 + (1984816000 / 3) * h ^ 3 + (7777127875 / 6) * h ^ 2 +
    (3847984625 / 3) * h + 611261375

/-- The polynomial `N_d(2 + h, 0)`. -/
noncomputable def hl46W3Nd0 (h : ℝ) : ℝ :=
  28125 * h ^ 8 + (383125 / 3) * h ^ 7 - 1931875 * h ^ 6 - 16751875 * h ^ 5 - (86249375 / 2) * h ^ 4 -
    18388125 * h ^ 3 + 78990000 * h ^ 2 + (344264375 / 3) * h + (311725625 / 6)

/-- The polynomial `N(2 + h, 0)`. -/
noncomputable def hl46W3N0 (h : ℝ) : ℝ :=
  (28125 / 2) * h ^ 8 + (143750 / 3) * h ^ 7 - (4009375 / 3) * h ^ 6 - (36331250 / 3) * h ^ 5 -
    (126812500 / 3) * h ^ 4 - (214831250 / 3) * h ^ 3 - 56421875 * h ^ 2 - 12618750 * h +
    (8746875 / 2)

/-- `P > 0`: discard positive `d`-terms and put `d = 1/19` in the negative ones. -/
theorem hl46_w3_P_pos {d h : ℝ} (hd : 0 ≤ d) (hd' : d ≤ 1 / 19) (hh : 0 ≤ h) : 0 < hl46W3P d h := by
  unfold hl46W3P
  linarith [mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hd hd' 6) (pow_nonneg hh 2),
    mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hd hd' 6) (pow_nonneg hh 1),
    pow_le_pow_left₀ hd hd' 6,
    mul_nonneg (pow_nonneg hd 5) (pow_nonneg hh 3),
    mul_nonneg (pow_nonneg hd 5) (pow_nonneg hh 2),
    mul_nonneg (pow_nonneg hd 5) (pow_nonneg hh 1),
    pow_nonneg hd 5,
    mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hd hd' 4) (pow_nonneg hh 4),
    mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hd hd' 4) (pow_nonneg hh 3),
    mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hd hd' 4) (pow_nonneg hh 2),
    mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hd hd' 4) (pow_nonneg hh 1),
    pow_le_pow_left₀ hd hd' 4,
    mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hd hd' 3) (pow_nonneg hh 5),
    mul_nonneg (pow_nonneg hd 3) (pow_nonneg hh 4),
    mul_nonneg (pow_nonneg hd 3) (pow_nonneg hh 3),
    mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hd hd' 3) (pow_nonneg hh 2),
    mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hd hd' 3) (pow_nonneg hh 1),
    pow_le_pow_left₀ hd hd' 3,
    mul_nonneg (pow_nonneg hd 2) (pow_nonneg hh 6),
    mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hd hd' 2) (pow_nonneg hh 5),
    mul_nonneg (pow_nonneg hd 2) (pow_nonneg hh 4),
    mul_nonneg (pow_nonneg hd 2) (pow_nonneg hh 3),
    mul_nonneg (pow_nonneg hd 2) (pow_nonneg hh 2),
    mul_nonneg (pow_nonneg hd 2) (pow_nonneg hh 1),
    pow_nonneg hd 2,
    mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hd hd' 1) (pow_nonneg hh 7),
    mul_nonneg (pow_nonneg hd 1) (pow_nonneg hh 6),
    mul_nonneg (pow_nonneg hd 1) (pow_nonneg hh 5),
    mul_nonneg (pow_nonneg hd 1) (pow_nonneg hh 4),
    mul_nonneg (pow_nonneg hd 1) (pow_nonneg hh 3),
    mul_nonneg (pow_nonneg hd 1) (pow_nonneg hh 2),
    mul_nonneg (pow_nonneg hd 1) (pow_nonneg hh 1),
    pow_nonneg hd 1,
    pow_nonneg hh 8,
    pow_nonneg hh 7,
    pow_nonneg hh 6,
    pow_nonneg hh 5,
    pow_nonneg hh 4,
    pow_nonneg hh 3,
    pow_nonneg hh 2,
    pow_nonneg hh 1]

/-- `N_d(2 + h, 0) > 0` on `0 ≤ h ≤ 1/6`. -/
theorem hl46_w3_Nd0_pos {h : ℝ} (hh : 0 ≤ h) (hh' : h ≤ 1 / 6) : 0 < hl46W3Nd0 h := by
  unfold hl46W3Nd0
  linarith [pow_nonneg hh 8,
    pow_nonneg hh 7,
    pow_le_pow_left₀ hh hh' 6,
    pow_le_pow_left₀ hh hh' 5,
    pow_le_pow_left₀ hh hh' 4,
    pow_le_pow_left₀ hh hh' 3,
    pow_nonneg hh 2,
    pow_nonneg hh 1]

/-- `N(2 + h, 0) > 0` on `0 ≤ h ≤ 1/6`. -/
theorem hl46_w3_N0_pos {h : ℝ} (hh : 0 ≤ h) (hh' : h ≤ 1 / 6) : 0 < hl46W3N0 h := by
  unfold hl46W3N0
  linarith [pow_nonneg hh 8,
    pow_nonneg hh 7,
    pow_le_pow_left₀ hh hh' 6,
    pow_le_pow_left₀ hh hh' 5,
    pow_le_pow_left₀ hh hh' 4,
    pow_le_pow_left₀ hh hh' 3,
    pow_le_pow_left₀ hh hh' 2,
    pow_le_pow_left₀ hh hh' 1]

/-- Jets are unchanged by a pointwise equal function. -/
theorem hl46_w3_jet_congr {f g f₁ f₂ : ℝ → ℝ} {x : ℝ} (h : ∀ y, f y = g y)
    (hg : HL46J g f₁ f₂ x) : HL46J f f₁ f₂ x := by
  have : f = g := funext h
  subst this
  exact hg

/-- The jet of a quadratic polynomial. -/
theorem hl46_w3_qjet (c0 c1 c2 d : ℝ) :
    HL46J (fun d => c0 + c1 * d + c2 * d ^ 2) (fun d => c1 + 2 * c2 * d) (fun _ => 2 * c2) d := by
  constructor
  · have := (((hasDerivAt_id' d).const_mul c1).const_add c0).fun_add
      ((hasDerivAt_pow 2 d).const_mul c2)
    refine this.congr_deriv ?_
    push_cast
    ring
  · have := ((hasDerivAt_id' d).const_mul (2 * c2)).const_add c1
    refine this.congr_deriv ?_
    ring

/-- The jet of a constant. -/
theorem hl46_w3_cjet (c d : ℝ) : HL46J (fun _ => c) (fun _ => 0) (fun _ => 0) d :=
  ⟨hasDerivAt_const d c, hasDerivAt_const d 0⟩

/-- **The second-order `d`-jet of `n`**: the product rule on the atoms, then
`N_dd = (781250/3)n_dd = P(d, x - 2)` and `N_d(x, 0) = N_d(2 + h, 0)`. -/
theorem hl46_w3_n_jet (x : ℝ) : ∃ n₁ n₂ : ℝ → ℝ, (∀ d, HL46J (fun d => hl46W3n x d) n₁ n₂ d) ∧
    (∀ d, 781250 / 3 * n₂ d = hl46W3P d (x - 2)) ∧ 781250 / 3 * n₁ 0 = hl46W3Nd0 (x - 2) := by
  have ja := fun d => hl46_w3_jet_congr (f := fun d : ℝ => 1 + 13 / 5 * d)
    (fun y => by ring) (hl46_w3_qjet 1 (13 / 5) 0 d)
  have jB := fun d => hl46_w3_jet_congr (f := fun d => hl46W3B x d)
    (fun y => by unfold hl46W3B; ring) (hl46_w3_qjet (1 + x) (13 / 5 + x) 0 d)
  have jK := fun d => hl46_w3_jet_congr (f := fun d => hl46W3K x d)
    (fun y => by unfold hl46W3K; ring) (hl46_w3_qjet ((1 + x) ^ 2) (26 / 5) (169 / 25) d)
  have jD := fun d => hl46_w3_jet_congr (f := fun d => hl46W3D x d)
    (fun y => by unfold hl46W3D hsDg; ring)
    (hl46_w3_qjet (-2 * (x ^ 2 - 2 * x - 1)) (-2 * (5 * x ^ 2 - 18 * x - 13) / 5)
      (13 * (10 * x + 13) / 25) d)
  have jv := fun d => hl46_w3_jet_congr (f := fun d => hl46W3v x d)
    (fun y => by unfold hl46W3v; ring) (hl46_w3_qjet ((9 * x + 740) / 1000) (-9 / 500) 0 d)
  have jE := fun d => hl46_w3_jet_congr (f := fun d => hl46W3E x d)
    (fun y => by unfold hl46W3E hh46S4P hl46W3v; ring)
    (hl46_w3_qjet ((1 + x) ^ 3 * ((9 * x + 740) / 1000 - 1) + 3 * (1 + x) - 1)
      (-9 / 500 * (1 + x) ^ 3) 0 d)
  have jBx := fun d => hl46_w3_jet_congr (f := fun d : ℝ => 1 + d)
    (fun y => by ring) (hl46_w3_qjet 1 1 0 d)
  have jDx := fun d => hl46_w3_jet_congr (f := fun d => hl46W3Dx x d)
    (fun y => by unfold hl46W3Dx; ring)
    (hl46_w3_qjet (-4 * (x - 1)) (-4 * (5 * x - 9) / 5) (26 / 5) d)
  have jEx := fun d => hl46_w3_jet_congr (f := fun d => hl46W3Ex x d)
    (fun y => by unfold hl46W3Ex hl46W3v; ring)
    (hl46_w3_qjet (3 * (1 + x) ^ 2 * ((9 * x + 740) / 1000 - 1) + (1 + x) ^ 3 * (9 / 1000) + 3)
      (-27 / 500 * (1 + x) ^ 2) 0 d)
  have j1 := hl46_w3_cjet 1
  have jM := hl46_w3_cjet ((1 + x) ^ 2 * ((1 + x) ^ 2 - (1 + x) + 1))
  have jKx := hl46_w3_cjet (2 * x + 2)
  have jMx := hl46_w3_cjet (4 * (1 + x) ^ 3 - 3 * (1 + x) ^ 2 + 2 * (1 + x))
  have jvx := hl46_w3_cjet (9 / 1000)
  have jn : ∀ d, _ := fun d =>
    -- `T`
    let jvm1 := (jv d).sub (j1 d)
    let jT := (((((((jvm1.mul ((jB d).mul (jB d))).mul (jK d)).add (((ja d).mul (ja d)).mul (jK d))).add
      (((ja d).mul (jB d)).mul (jK d))).sub ((((ja d).mul (ja d)).mul (ja d)).mul (jB d))).sub
      (((ja d).mul (jB d)).mul ((((jv d).const_mul 2).mul (jD d)).sub (jE d)))).add
      (((jM d).add ((jv d).mul ((jD d).mul (jD d)))).sub ((jD d).mul (jE d)))).sub
      (((jK d).mul (jK d)).const_mul (3 / 4))
    -- the partial derivatives of `T`
    let jX1 := ((((jvm1.const_mul 2).mul (jB d)).mul (jK d)).add ((ja d).mul (jK d))).sub
      (((ja d).mul (ja d)).mul (ja d)) |>.sub ((ja d).mul ((((jv d).const_mul 2).mul (jD d)).sub (jE d)))
    let jX2 := (((jvm1.mul ((jB d).mul (jB d))).add ((ja d).mul (ja d))).add ((ja d).mul (jB d))).sub
      ((jK d).const_mul (3 / 2))
    let jX3 := ((((jv d).const_mul 2).mul (jD d)).sub ((((ja d).const_mul 2).mul (jv d)).mul (jB d))).sub
      (jE d)
    let jX4 := ((ja d).mul (jB d)).sub (jD d)
    let jX6 := ((((jB d).mul (jB d)).mul (jK d)).sub ((((ja d).const_mul 2).mul (jB d)).mul (jD d))).add
      ((jD d).mul (jD d))
    let jTx := (((((jX1.mul (jBx d)).add (jX2.mul (jKx d))).add (jX3.mul (jDx d))).add
      (jX4.mul (jEx d))).add (jMx d)).add (jX6.mul (jvx d))
    -- `n`
    ((((jTx.mul (jB d)).mul (jK d)).sub (jT.mul (((jBx d).mul (jK d)).add ((jB d).mul (jKx d))))).add
      ((((ja d).mul (jB d)).mul (jK d)).mul (((jK d).mul (jBx d)).sub ((jB d).mul (jKx d))))).add
      (((((ja d).mul (jB d)).mul (jB d)).mul (jK d)).mul (jK d) |>.const_mul (1 / 25))
  refine ⟨_, _, fun d => hl46_w3_jet_congr (fun y => ?_) (jn d), fun d => ?_, ?_⟩
  · unfold hl46W3n hl46W3TxC hl46W3TC hl46W3Tx hl46W3T
    ring
  · unfold hl46W3P hl46W3E hl46W3Ex hh46S4P hl46W3v hl46W3B hl46W3K hl46W3D hsDg hl46W3Dx
    ring
  · unfold hl46W3Nd0 hl46W3E hl46W3Ex hh46S4P hl46W3v hl46W3B hl46W3K hl46W3D hsDg hl46W3Dx
    ring

/-- The boundary value: `N(x, 0) = N(2 + h, 0)`. -/
theorem hl46_w3_n0 (x : ℝ) : 781250 / 3 * hl46W3n x 0 = hl46W3N0 (x - 2) := by
  unfold hl46W3n hl46W3TxC hl46W3TC hl46W3Tx hl46W3T hl46W3N0 hl46W3E hl46W3Ex hh46S4P hl46W3v
    hl46W3B hl46W3K hl46W3D hsDg hl46W3Dx
  ring

/-- **`N > 0`**: `N_dd = P > 0` and `N_d(x, 0) > 0` give `N_d > 0`, so
`N(x, d) ≥ N(x, 0) > 0`. -/
theorem hl46_w3_n_pos {x d : ℝ} (hx : 2 ≤ x) (hx' : x ≤ 13 / 6) (hd : 0 ≤ d) (hd' : d ≤ 1 / 19) :
    0 < hl46W3n x d := by
  obtain ⟨n₁, n₂, hJ, hP, hN1⟩ := hl46_w3_n_jet x
  have h0 : 0 ≤ x - 2 := by linarith
  have h6 : x - 2 ≤ 1 / 6 := by linarith
  have hn10 : 0 < n₁ 0 := by
    have := hl46_w3_Nd0_pos h0 h6
    linarith
  have hn1 : ∀ y ∈ Icc (0 : ℝ) (1 / 19), 0 < n₁ y := fun y hy => by
    have := hl46_mono_of (f := n₁) (f₁ := n₂) (a := 0) (b := 1 / 19) (fun z _ => (hJ z).2)
      (fun z hz => by
        have h1 := hP z
        have h2 := hl46_w3_P_pos hz.1 hz.2 h0
        linarith) le_rfl hy.1 hy.2
    linarith
  have hmono := hl46_mono_of (f := fun d => hl46W3n x d) (f₁ := n₁) (a := 0) (b := 1 / 19)
    (fun z _ => (hJ z).1) (fun z hz => (hn1 z hz).le) le_rfl hd hd'
  have hN0 : 0 < hl46W3n x 0 := by
    have h1 := hl46_w3_n0 x
    have h2 := hl46_w3_N0_pos h0 h6
    linarith
  linarith

end SmoothedOctagon
