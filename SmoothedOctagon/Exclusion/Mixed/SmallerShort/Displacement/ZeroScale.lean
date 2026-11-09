module

public import SmoothedOctagon.Exclusion.Mixed.SmallerShort.Envelope

/-!
# Smaller-short window, displacement: the zero-scale face

At scale `q = 0` the displacement-weighted envelope at fixed normalized duration `p = y r_A` is
`Φ(0) = C(p) + m/4`, `m = 4(4 - 3y)/(5α - 1)`. It increases with the incoming norm `u`, so it is at
most its value `Z(x, α, r_A, y)` at `u = U(r_A)`; `Z` decreases with `x` at fixed `(α, r)` and
increases with `r`, so it is at most its value on the two edges `x = 2` and `x = α` at
`r = r₀(α, x)` (the bound `β ≥ b₀`), where the quadratic log bound and an explicit polynomial in
`α` on each edge make it negative.

The two monotonicity steps are done separately and algebraically: `x` is lowered at fixed
`(α, β)` by a product of monotone factors, and `r` is raised by an exact divided difference.

## Main API

* `dspf_zero_neg`: the statement of `dsp_zero_neg`.
-/

@[expose] public section

namespace SmoothedOctagon

open Set Real

/-- `H = Sr(1 - r) - 1/S`. -/
private noncomputable def zH (x r : ℝ) : ℝ := (1 + x) * r * (1 - r) - 1 / (1 + x)

/-- `C = 2 + (x - 1)/α²`. -/
private noncomputable def zC (x a : ℝ) : ℝ := 2 + (x - 1) / a ^ 2

/-- The `r`-slope of `d₀`: `-1 + 2x/α + (1 + 2x)/α²`. -/
private noncomputable def zB (x a : ℝ) : ℝ := -1 + 2 * x / a + (1 + 2 * x) / a ^ 2

/-- `d₀ = D/Q` with `β = α(1 - r)/r`. -/
private noncomputable def zD (x a r : ℝ) : ℝ := 2 - 2 * x / a + r * zB x a

/-- The zero-scale function at `u = U(r)`. -/
private noncomputable def zZ (x a r y : ℝ) : ℝ :=
  -zH x r * (1 - y * zD x a r) + r * (2 - y * zC x a) + (4 - 3 * y) / (5 * a - 1) + log y

/-- `r₀(α, X) = α(9X + 8)/(α(17X + 8) + 9X²)`, the value of `r_A` at `β = b₀`. -/
private noncomputable def zR0 (a X : ℝ) : ℝ := a * (9 * X + 8) / (a * (17 * X + 8) + 9 * X ^ 2)

/-- `log y ≤ (y - 1) - (y - 1)²/2` for `0 < y ≤ 1`. -/
private lemma log_le_quad {y : ℝ} (hy : 0 < y) (hy1 : y ≤ 1) :
    log y ≤ (y - 1) - (y - 1) ^ 2 / 2 := by
  have h := ss_le_of_deriv (f := fun s => log s - (s - 1) + (s - 1) ^ 2 / 2)
    (f' := fun s => (s - 1) ^ 2 / s) hy1 (fun s hs => ?_) (fun s hs => by
      have : 0 < s := by linarith [hs.1]
      positivity)
  · simp only [log_one, sub_self, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow,
      zero_div, add_zero] at h
    linarith
  have hs0 : 0 < s := by linarith [hs.1]
  have h1 : HasDerivAt (fun t : ℝ => t - 1) 1 s := by simpa using (hasDerivAt_id s).sub_const 1
  have := ((Real.hasDerivAt_log hs0.ne').sub h1).add ((h1.pow 2).div_const 2)
  refine this.congr_deriv ?_
  field_simp
  ring

/-- `d₀ = r_A D/α²`. -/
private lemma d0_eq {x be al : ℝ} (hal : 0 < al) (hab : 0 < al + be) :
    ssRA al be * ssDg x be al / al ^ 2 = zD x al (ssRA al be) := by
  unfold ssRA ssDg zD zB
  field_simp
  ring

/-- `D < Q` at `β ≥ b₀(X, α)`. -/
private lemma D_lt_Q {X be a : ℝ} (hX : 2 ≤ X) (ha : 1 ≤ a) (haX : a ≤ X)
    (hb : X * (9 * X + 8 * a) / (9 * X + 8) ≤ be) : ssDg X be a < a * (a + be) := by
  unfold ssDg
  have h9 : 0 < 9 * X + 8 := by linarith
  rw [div_le_iff₀ h9] at hb
  nlinarith [mul_nonneg (sub_nonneg.2 hb) (by linarith : (0 : ℝ) ≤ 2 * X - a),
    mul_nonneg (mul_nonneg (sub_nonneg.2 ha) (sub_nonneg.2 haX)) (by linarith : (0 : ℝ) ≤ X),
    mul_nonneg (sub_nonneg.2 haX) (by positivity : (0 : ℝ) ≤ X * (X + 8)),
    mul_nonneg (sub_nonneg.2 hX) (by positivity : (0 : ℝ) ≤ 17 * X ^ 2 + 16 * X + 7)]

/-- `b₀(X, α) = X(9X + 8α)/(9X + 8)` increases with `X`. -/
private lemma b0_mono {x' x a : ℝ} (hx' : 0 ≤ x') (hxx : x' ≤ x) (ha : 0 ≤ a) :
    x' * (9 * x' + 8 * a) / (9 * x' + 8) ≤ x * (9 * x + 8 * a) / (9 * x + 8) := by
  have hx : 0 ≤ x := le_trans hx' hxx
  rw [div_le_div_iff₀ (by linarith) (by linarith)]
  nlinarith [mul_nonneg (sub_nonneg.2 hxx)
    (by positivity : (0 : ℝ) ≤ 81 * x * x' + 72 * (x + x') + 64 * a)]

/-- `r_A ≤ r₀(α, X)` from `β ≥ b₀(X, α)`. -/
private lemma rA_le_R0 {X be a : ℝ} (hX : 0 < X) (ha : 0 < a) (hab : 0 < a + be)
    (hb : X * (9 * X + 8 * a) / (9 * X + 8) ≤ be) : ssRA a be ≤ zR0 a X := by
  unfold ssRA zR0
  rw [div_le_iff₀ (by linarith)] at hb
  rw [div_le_div_iff₀ hab (by positivity)]
  nlinarith

/-- `r₀(α, X) ≤ 13/30` for `X ≥ 2`, `α ≤ X`. -/
private lemma R0_le {X a : ℝ} (hX : 2 ≤ X) (ha : 0 < a) (haX : a ≤ X) : zR0 a X ≤ 13 / 30 := by
  unfold zR0
  rw [div_le_div_iff₀ (by positivity) (by norm_num)]
  nlinarith [mul_nonneg ha.le (sub_nonneg.2 haX), mul_nonneg (sub_nonneg.2 hX) (by linarith : (0 : ℝ) ≤ X)]

/-- **Raise the incoming norm**: `Φ(0) ≤ Z(x, α, r_A, p/r_A)`. -/
private lemma phi0_le {x be al u p : ℝ} (hx : 2 ≤ x) (hal : 1 < al) (hxb : x ≤ be)
    (hurA : u ≤ m2U (ssRA al be)) (hDQ : ssDg x be al < al * (al + be)) (hp : 0 < p)
    (hpr : p ≤ ssRA al be) :
    ssPhi x be al u p (4 * (4 - 3 * (p / ssRA al be)) / (5 * al - 1)) 0 ≤
      zZ x al (ssRA al be) (p / ssRA al be) := by
  have hal0 : 0 < al := by linarith
  have hab : 0 < al + be := by linarith
  have hr0 : 0 < ssRA al be := div_pos hal0 hab
  have hd := d0_eq (x := x) hal0 hab
  set r := ssRA al be with hr
  simp only [ssPhi, zero_mul, mul_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow,
    add_zero]
  -- the slope in `u`
  have hpD : p * ssDg x be al < al ^ 2 := by
    rcases le_or_gt (ssDg x be al) 0 with hD | hD
    · nlinarith
    · have h1 : p * ssDg x be al ≤ r * ssDg x be al := mul_le_mul_of_nonneg_right hpr hD.le
      have h2 : r * ssDg x be al < al ^ 2 := by
        rw [hr, ssRA, div_mul_eq_mul_div, div_lt_iff₀ hab]
        nlinarith
      linarith
  have hslope : 0 < (1 + x) * (1 - p * (ssDg x be al / al ^ 2)) + 1 / r := by
    have : p * (ssDg x be al / al ^ 2) < 1 := by
      rw [← mul_div_assoc, div_lt_one (by positivity)]
      exact hpD
    have : 0 < 1 / r := by positivity
    nlinarith
  have hmono : ssCp x be al u p ≤ ssCp x be al (m2U r) p := by
    have hid : ssCp x be al (m2U r) p - ssCp x be al u p =
        (m2U r - u) * ((1 + x) * (1 - p * (ssDg x be al / al ^ 2)) + 1 / r) := by
      unfold ssCp ssA1 ssE0
      rw [← hr]
      ring
    nlinarith [mul_nonneg (sub_nonneg.2 hurA) hslope.le]
  -- the identity at `u = U(r)`
  have hD' : ssDg x be al / al ^ 2 = zD x al r / r := by
    rw [← hd]
    field_simp
  have hid : ssCp x be al (m2U r) p + 4 * (4 - 3 * (p / r)) / (5 * al - 1) / 4 =
      zZ x al r (p / r) := by
    unfold ssCp ssA1 ssE0 m2U zZ zH zC
    rw [← hr, hD', show 4 * (4 - 3 * (p / r)) / (5 * al - 1) / 4 =
      (4 - 3 * (p / r)) / (5 * al - 1) by ring]
    generalize log (p / r) = ℓ
    generalize (4 - 3 * (p / r)) / (5 * al - 1) = M
    field_simp
    ring
  linarith

/-- **Lower `x` at fixed `(α, r)`**: `Z(x) ≤ Z(x')` for `2 ≤ x' ≤ x`. -/
private lemma Z_x_mono {x x' a r y : ℝ} (hx' : 2 ≤ x') (hxx : x' ≤ x) (ha : 1 ≤ a)
    (hr : 1 / 3 ≤ r) (hr' : r ≤ 13 / 30) (hd : zD x' a r ≤ 1) (hy0 : 0 ≤ y) (hy1 : y ≤ 1) :
    zZ x a r y ≤ zZ x' a r y := by
  have hc : 2 / 9 ≤ r * (1 - r) := by nlinarith
  have hH : zH x' r ≤ zH x r := by
    unfold zH
    have : 1 / (1 + x) ≤ 1 / (1 + x') := one_div_le_one_div_of_le (by linarith) (by linarith)
    nlinarith [mul_le_mul_of_nonneg_right hxx (by linarith : (0 : ℝ) ≤ r * (1 - r))]
  have hH0 : 0 ≤ zH x' r := by
    unfold zH
    have : 1 / (1 + x') ≤ 1 / 3 := by
      rw [div_le_div_iff₀ (by linarith) (by norm_num)]
      linarith
    nlinarith [mul_le_mul_of_nonneg_right (by linarith : (3 : ℝ) ≤ 1 + x')
      (by linarith : (0 : ℝ) ≤ r * (1 - r))]
  have hD : zD x a r ≤ zD x' a r := by
    have ha0 : 0 < a := by linarith
    have hid : zD x a r - zD x' a r = (x - x') * (2 * (r * (a + 1) - a) / a ^ 2) := by
      unfold zD zB
      field_simp
      ring
    have h2 : 2 * (r * (a + 1) - a) / a ^ 2 ≤ 0 :=
      div_nonpos_of_nonpos_of_nonneg (by nlinarith) (by positivity)
    nlinarith [mul_nonpos_of_nonneg_of_nonpos (sub_nonneg.2 hxx) h2]
  have hC : zC x' a ≤ zC x a := by
    unfold zC
    gcongr
  have hg : 0 ≤ 1 - y * zD x a r := by nlinarith [mul_nonneg hy0 (by linarith : (0 : ℝ) ≤ 1 - zD x a r)]
  unfold zZ
  nlinarith [mul_nonneg (sub_nonneg.2 hH) hg, mul_nonneg hH0 (mul_nonneg hy0 (sub_nonneg.2 hD)),
    mul_nonneg (mul_nonneg (by linarith : (0 : ℝ) ≤ r) hy0) (sub_nonneg.2 hC)]

/-- **Raise `r`**: `Z(r) ≤ Z(r')` for `1/3 ≤ r ≤ r' ≤ 13/30`, by the exact
divided difference `Z(r') - Z(r) = (r' - r)((1 - y)B₀ + yB₁)`. -/
private lemma Z_r_mono {x a r r' y : ℝ} (hx : 2 ≤ x) (hx2 : x ≤ 13 / 6) (ha : 1 ≤ a)
    (hax : a ≤ x) (hr : 1 / 3 ≤ r) (hrr : r ≤ r') (hr' : r' ≤ 13 / 30) (hy0 : 0 ≤ y)
    (hy1 : y ≤ 1) : zZ x a r y ≤ zZ x a r' y := by
  have ha0 : 0 < a := by linarith
  obtain ⟨A, hA⟩ : ∃ A : ℝ, A = 2 * x / a - 1 := ⟨_, rfl⟩
  obtain ⟨B, hBd⟩ : ∃ B : ℝ, B = zB x a := ⟨_, rfl⟩
  obtain ⟨Z13, hZ13⟩ : ∃ Z : ℝ, Z = (1 + x) * (B - A) / 3 - B / (1 + x) - (x - 1) / a ^ 2 :=
    ⟨_, rfl⟩
  obtain ⟨s, hsd⟩ : ∃ s : ℝ, s = r - 1 / 3 := ⟨_, rfl⟩
  obtain ⟨s', hsd'⟩ : ∃ s : ℝ, s = r' - 1 / 3 := ⟨_, rfl⟩
  have hZ : 0 < Z13 := by
    have : Z13 = (3 * (a - x) ^ 2 + (x - 1) * (x + 1) * (2 * x - 1)) / (3 * a ^ 2 * (x + 1)) := by
      rw [hZ13, hA, hBd]
      unfold zB
      field_simp
      ring
    rw [this]
    apply div_pos _ (by positivity)
    nlinarith [sq_nonneg (a - x), mul_pos (mul_pos (by linarith : (0 : ℝ) < x - 1)
      (by linarith : (0 : ℝ) < x + 1)) (by linarith : (0 : ℝ) < 2 * x - 1)]
  have hAB : 0 ≤ A - 3 / 20 * B := by
    have : A - 3 / 20 * B = (17 * (2 * x * a - a ^ 2) - 3 * (1 + 2 * x)) / (20 * a ^ 2) := by
      rw [hA, hBd]
      unfold zB
      field_simp
      ring
    rw [this]
    apply div_nonneg _ (by positivity)
    nlinarith [mul_nonneg (sub_nonneg.2 ha) (by linarith : (0 : ℝ) ≤ 2 * x - a - 1)]
  have hB : 0 ≤ B := by
    rw [hBd]
    unfold zB
    have h1 : 2 ≤ 2 * x / a := by rw [le_div_iff₀ ha0]; linarith
    have h2 : 0 ≤ (1 + 2 * x) / a ^ 2 := by positivity
    linarith
  have hs : 0 ≤ s := by rw [hsd]; linarith
  have hss : s ≤ s' := by rw [hsd, hsd']; linarith
  have hs' : s' ≤ 1 / 10 := by rw [hsd']; linarith
  have hq : s ^ 2 + s * s' + s' ^ 2 ≤ 3 / 20 * (s + s') := by
    nlinarith [mul_nonneg (sub_nonneg.2 hss) (by linarith : (0 : ℝ) ≤ s' + 2 * s),
      mul_nonneg (by linarith : (0 : ℝ) ≤ s + s') (by linarith : (0 : ℝ) ≤ 1 / 10 - s')]
  have hB1 : 0 ≤ A * (s + s') - B * (s ^ 2 + s * s' + s' ^ 2) := by
    nlinarith [mul_le_mul_of_nonneg_left hq hB, mul_nonneg hAB (by linarith : (0 : ℝ) ≤ s + s')]
  have hB0 : 0 ≤ 2 - (1 + x) * (1 - r - r') := by
    nlinarith [mul_le_mul_of_nonneg_left (by linarith : 1 - r - r' ≤ 1 / 3)
      (by linarith : (0 : ℝ) ≤ 1 + x)]
  have hW : 0 ≤ Z13 + (1 + x) * (A * (s + s') - B * (s ^ 2 + s * s' + s' ^ 2)) :=
    add_nonneg hZ.le (mul_nonneg (by linarith) hB1)
  have hbr : 0 ≤ (1 - y) * (2 - (1 + x) * (1 - r - r')) +
      y * (Z13 + (1 + x) * (A * (s + s') - B * (s ^ 2 + s * s' + s' ^ 2))) :=
    add_nonneg (mul_nonneg (by linarith) hB0) (mul_nonneg hy0 hW)
  have hprod := mul_nonneg (sub_nonneg.2 hrr) hbr
  have hid : zZ x a r' y - zZ x a r y = (r' - r) * ((1 - y) * (2 - (1 + x) * (1 - r - r')) +
      y * (Z13 + (1 + x) * (A * (s + s') - B * (s ^ 2 + s * s' + s' ^ 2)))) := by
    rw [hZ13, hA, hBd, hsd, hsd']
    unfold zZ zH zD zC zB
    ring
  linarith only [hid, hprod]

/-- `Z(y) = E + L(1 - y) + log y`. -/
private lemma Z_eq_EL (x a r y : ℝ) : zZ x a r y =
    (-zH x r * (1 - zD x a r) + r * (2 - zC x a) + 1 / (5 * a - 1)) +
      (r * zC x a - zD x a r * zH x r + 3 / (5 * a - 1)) * (1 - y) + log y := by
  unfold zZ
  ring

/-- The quadratic log bound and the square completion:
`2E + (L - 1)² < 0` gives `Z(y) < 0` on `(0, 1]`. -/
private lemma Z_neg_of {x a r y E L : ℝ} (hy : 0 < y) (hy1 : y ≤ 1)
    (hE : -zH x r * (1 - zD x a r) + r * (2 - zC x a) + 1 / (5 * a - 1) = E)
    (hL : r * zC x a - zD x a r * zH x r + 3 / (5 * a - 1) = L)
    (h : 2 * E + (L - 1) ^ 2 < 0) : zZ x a r y < 0 := by
  rw [Z_eq_EL, hE, hL]
  have := log_le_quad hy hy1
  nlinarith [sq_nonneg ((1 - y) - (L - 1))]

/-- **The edge `x = 2`**: `Z(2, α, r₀(α, 2), y) < 0` for `1 < α ≤ 2`, `0 < y ≤ 1` (`Z_neg_of`
with an explicit polynomial in `α`). -/
private lemma edge_two {a y : ℝ} (ha : 1 < a) (ha2 : a ≤ 2) (hy : 0 < y) (hy1 : y ≤ 1) :
    zZ 2 a (zR0 a 2) y < 0 := by
  have hk : 0 < 5 * a - 1 := by linarith
  have ha0 : 0 < a := by linarith
  have hR : zR0 a 2 = 13 * a / (21 * a + 18) := by
    unfold zR0
    rw [div_eq_div_iff (by positivity) (by positivity)]
    ring
  have hδ : 0 < 9 * a * (5 * a - 1) * (7 * a + 6) ^ 3 := by positivity
  have h1 : (21 * a + 18) ≠ 0 := by positivity
  have h2 : (5 * a - 1) ≠ 0 := hk.ne'
  have h2' : a * 5 - 1 ≠ 0 := by linarith
  have h3 : (7 * a + 6) ≠ 0 := by positivity
  refine Z_neg_of hy hy1
    (E := (2200 * a ^ 5 + 4797 * a ^ 4 - 15912 * a ^ 3 - 7622 * a ^ 2 + 6 * a + 1152) /
      (9 * a * (5 * a - 1) * (7 * a + 6) ^ 3))
    (L := (11135 * a ^ 5 + 16944 * a ^ 4 + 49572 * a ^ 3 + 37214 * a ^ 2 + 7122 * a - 1152) /
      (9 * a * (5 * a - 1) * (7 * a + 6) ^ 3)) ?_ ?_ ?_
  · rw [hR]
    unfold zH zD zB zC
    field_simp
    ring
  · rw [hR]
    unfold zH zD zB zC
    field_simp
    ring
  · set δ := 9 * a * (5 * a - 1) * (7 * a + 6) ^ 3 with hδd
    set En := 2200 * a ^ 5 + 4797 * a ^ 4 - 15912 * a ^ 3 - 7622 * a ^ 2 + 6 * a + 1152
    set Ln := 11135 * a ^ 5 + 16944 * a ^ 4 + 49572 * a ^ 3 + 37214 * a ^ 2 + 7122 * a - 1152
    have hid : 2 * (En / δ) + (Ln / δ - 1) ^ 2 = (2 * En * δ + (Ln - δ) ^ 2) / δ ^ 2 := by
      field_simp
    rw [hid]
    apply div_neg_of_neg_of_pos _ (by positivity)
    set z := a - 1 with hz
    have hz0 : 0 ≤ z := by linarith
    have hz1 : z ≤ 1 := by linarith
    have hP : 2 * En * δ + (Ln - δ) ^ 2 = -(690233687 + 10582593086 * z + 37156604316 * z ^ 2 +
        52283775388 * z ^ 3 + 20843672122 * z ^ 4 - 28806946584 * z ^ 5 - 44038758296 * z ^ 6 -
        26501707700 * z ^ 7 - 8351204733 * z ^ 8 - 1342243990 * z ^ 9 - 86404000 * z ^ 10) := by
      simp only [En, Ln, δ, hz]
      ring
    rw [hP]
    have e1 : z ^ 4 ≤ z := by simpa using pow_le_pow_of_le_one hz0 hz1 (by norm_num : 1 ≤ 4)
    have e2 : z ^ 4 ≤ z ^ 2 := pow_le_pow_of_le_one hz0 hz1 (by norm_num)
    have e3 : z ^ 4 ≤ z ^ 3 := pow_le_pow_of_le_one hz0 hz1 (by norm_num)
    have e5 : z ^ 5 ≤ z ^ 4 := pow_le_pow_of_le_one hz0 hz1 (by norm_num)
    have e6 : z ^ 6 ≤ z ^ 4 := pow_le_pow_of_le_one hz0 hz1 (by norm_num)
    have e7 : z ^ 7 ≤ z ^ 4 := pow_le_pow_of_le_one hz0 hz1 (by norm_num)
    have e8 : z ^ 8 ≤ z ^ 4 := pow_le_pow_of_le_one hz0 hz1 (by norm_num)
    have e9 : z ^ 9 ≤ z ^ 4 := pow_le_pow_of_le_one hz0 hz1 (by norm_num)
    have e10 : z ^ 10 ≤ z ^ 4 := pow_le_pow_of_le_one hz0 hz1 (by norm_num)
    have e0 : 0 ≤ z ^ 4 := by positivity
    linarith

/-- **The edge `x = α`**: `Z(α, α, r₀(α, α), y) < 0` for `2 ≤ α ≤ 13/6`, `0 < y ≤ 1` (`Z_neg_of`
with an explicit polynomial in `α`). -/
private lemma edge_diag {a y : ℝ} (ha : 2 ≤ a) (ha2 : a ≤ 13 / 6) (hy : 0 < y) (hy1 : y ≤ 1) :
    zZ a a (zR0 a a) y < 0 := by
  have hk : 0 < 5 * a - 1 := by linarith
  have ha0 : 0 < a := by linarith
  have hR : zR0 a a = (9 * a + 8) / (26 * a + 8) := by
    unfold zR0
    rw [div_eq_div_iff (by positivity) (by positivity)]
    ring
  have h1 : (26 * a + 8) ≠ 0 := by positivity
  have h2 : (5 * a - 1) ≠ 0 := hk.ne'
  have h2' : a * 5 - 1 ≠ 0 := by linarith
  have h3 : (13 * a + 4) ≠ 0 := by positivity
  have h4 : (a + 1) ≠ 0 := by positivity
  refine Z_neg_of hy hy1
    (E := (-13005 * a ^ 7 - 21199 * a ^ 6 + 72156 * a ^ 5 + 40656 * a ^ 4 - 4703 * a ^ 3 +
      2415 * a ^ 2 + 2352 * a - 64) / (8 * a * (5 * a - 1) * (13 * a + 4) ^ 3 * (a + 1)))
    (L := (-6885 * a ^ 6 + 29322 * a ^ 5 + 136684 * a ^ 4 + 101398 * a ^ 3 + 16449 * a ^ 2 -
      1904 * a + 64) / (8 * a * (5 * a - 1) * (13 * a + 4) ^ 3)) ?_ ?_ ?_
  · rw [hR]
    unfold zH zD zB zC
    field_simp
    ring
  · rw [hR]
    unfold zH zD zB zC
    field_simp
    ring
  · set δ := 8 * a * (5 * a - 1) * (13 * a + 4) ^ 3 with hδd
    have hδ : 0 < δ := by positivity
    set En := -13005 * a ^ 7 - 21199 * a ^ 6 + 72156 * a ^ 5 + 40656 * a ^ 4 - 4703 * a ^ 3 +
      2415 * a ^ 2 + 2352 * a - 64
    set Ln := -6885 * a ^ 6 + 29322 * a ^ 5 + 136684 * a ^ 4 + 101398 * a ^ 3 + 16449 * a ^ 2 -
      1904 * a + 64
    have hid : 2 * (En / (δ * (a + 1))) + (Ln / δ - 1) ^ 2 =
        (2 * En * δ + (a + 1) * (Ln - δ) ^ 2) / (δ ^ 2 * (a + 1)) := by
      field_simp
    rw [hid]
    apply div_neg_of_neg_of_pos _ (by positivity)
    set v := a - 2 with hv
    have hv0 : 0 ≤ v := by linarith
    have hv1 : v ≤ 1 / 6 := by linarith
    have hQ : 2 * En * δ + (a + 1) * (Ln - δ) ^ 2 = -(335599558992 + 18835981373520 * v +
        81208201479192 * v ^ 2 + 164345667026256 * v ^ 3 + 201771400623165 * v ^ 4 +
        166252659646707 * v ^ 5 + 96321280676760 * v ^ 6 + 39931801595520 * v ^ 7 +
        11787954152298 * v ^ 8 + 2403930238142 * v ^ 9 + 314562058520 * v ^ 10 +
        21728950216 * v ^ 11 + 199528065 * v ^ 12 - 47403225 * v ^ 13) := by
      simp only [En, Ln, δ, hv]
      ring
    rw [hQ]
    have e13 : v ^ 13 ≤ v ^ 12 / 6 := by
      have : v ^ 13 = v ^ 12 * v := by ring
      rw [this]
      nlinarith [pow_nonneg hv0 12]
    have : 0 ≤ v := hv0
    have p1 : 0 ≤ v ^ 2 := by positivity
    have p3 : 0 ≤ v ^ 3 := by positivity
    have p4 : 0 ≤ v ^ 4 := by positivity
    have p5 : 0 ≤ v ^ 5 := by positivity
    have p6 : 0 ≤ v ^ 6 := by positivity
    have p7 : 0 ≤ v ^ 7 := by positivity
    have p8 : 0 ≤ v ^ 8 := by positivity
    have p9 : 0 ≤ v ^ 9 := by positivity
    have p10 : 0 ≤ v ^ 10 := by positivity
    have p11 : 0 ≤ v ^ 11 := by positivity
    have p12 : 0 ≤ v ^ 12 := by positivity
    linarith

/-- **The zero-scale face**: the statement of `dsp_zero_neg`. -/
theorem dspf_zero_neg {x be al u p : ℝ} (hx : 2 ≤ x) (hx2 : x ≤ 13 / 6) (hal : 1 < al)
    (hax : al ≤ x) (hxb : x ≤ be) (hU : x * (9 * x + 8 * al) / (9 * x + 8) ≤ be)
    (hrA : 1 / 3 < ssRA al be) (hrA' : ssRA al be ≤ 13 / 30) (hu : 3 / 4 ≤ u)
    (hurA : u ≤ m2U (ssRA al be)) (hDQ : ssDg x be al < al * (al + be)) (hp : 0 < p)
    (hpr : p ≤ ssRA al be) :
    ssPhi x be al u p (4 * (4 - 3 * (p / ssRA al be)) / (5 * al - 1)) 0 < 0 := by
  have _ : 3 / 4 ≤ u := hu  -- `u ≥ 3/4` is not needed (only `u ≤ U(r_A)`)
  have hal0 : 0 < al := by linarith
  have hab : 0 < al + be := by linarith
  refine lt_of_le_of_lt (phi0_le hx hal hxb hurA hDQ hp hpr) ?_
  have hr0 : 0 < ssRA al be := by linarith
  have hy0 : 0 < p / ssRA al be := div_pos hp hr0
  have hy1 : p / ssRA al be ≤ 1 := (div_le_one hr0).2 hpr
  -- lowering `x` to `X = max 2 α`, then raising `r` to `r₀(α, X)`
  have key : ∀ X, 2 ≤ X → X ≤ x → al ≤ X →
      zZ x al (ssRA al be) (p / ssRA al be) ≤ zZ X al (zR0 al X) (p / ssRA al be) := by
    intro X hX hXx haX
    have hb : X * (9 * X + 8 * al) / (9 * X + 8) ≤ be :=
      le_trans (b0_mono (by linarith) hXx hal0.le) hU
    have hd : zD X al (ssRA al be) ≤ 1 := by
      rw [← d0_eq hal0 hab, div_le_one (by positivity), ssRA, div_mul_eq_mul_div,
        div_le_iff₀ hab]
      nlinarith [D_lt_Q hX hal.le haX hb]
    calc zZ x al (ssRA al be) (p / ssRA al be) ≤ zZ X al (ssRA al be) (p / ssRA al be) :=
          Z_x_mono hX hXx hal.le hrA.le hrA' hd hy0.le hy1
      _ ≤ zZ X al (zR0 al X) (p / ssRA al be) :=
          Z_r_mono hX (by linarith) hal.le haX hrA.le (rA_le_R0 (by linarith) hal0 hab hb)
            (R0_le hX hal0 haX) hy0.le hy1
  rcases le_or_gt al 2 with h2 | h2
  · exact lt_of_le_of_lt (key 2 le_rfl hx h2) (edge_two hal h2 hy0 hy1)
  · exact lt_of_le_of_lt (key al h2.le hax le_rfl) (edge_diag h2.le (by linarith) hy0 hy1)

end SmoothedOctagon
