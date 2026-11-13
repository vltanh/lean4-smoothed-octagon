module

public import SmoothedOctagon.Exclusion.Mixed.SmallerShort.LowerRatio.OuterFace.SmallShape.Curvature.Norm

/-!
# The displacement comparison at the lower norm

Partial fractions in `e = x - C` give a cubic derivative numerator.
The tangent inequality `e³ ≥ 3e - 2` proves its sign on `C ≤ 4/5`.
-/

@[expose] public section
namespace SmoothedOctagon.LowerRatioCurvature

noncomputable def baseA (x : ℝ) : ℝ := x * (3 * x - 2) / 32
noncomputable def baseB (x : ℝ) : ℝ :=
  -(24 * x ^ 5 - 33 * x ^ 4 - 144 * x ^ 3 - 50 * x ^ 2 + 16 * x - 5) /
    (384 * (x + 1) ^ 2)
noncomputable def baseK (x : ℝ) : ℝ :=
  x * (34 * x ^ 2 + 67 * x - 11) / (384 * (x + 1))
noncomputable def baseH (x : ℝ) : ℝ := x * (2 * x ^ 2 + 5 * x - 1) / 192

noncomputable def base (x e : ℝ) : ℝ :=
  -baseA x * e + baseB x - baseK x / e + baseH x / e ^ 2

theorem lower_norm_eq {x C : ℝ} (hx : 0 < x) (he : 0 < x - C) :
    value x C (3 / 4) = base x (x - C) := by
  have hS : x + 1 ≠ 0 := by linarith
  simp only [value, base, baseA, baseB, baseK, baseH,
    lrb2, lrb3, lrg2, lrq2, lrq3, lrW3, lrW4, lrd1, lrd2, lrJ2, ssE0]
  field_simp
  ring

theorem baseA_nonneg {x : ℝ} (hx : 3 / 2 ≤ x) : 0 ≤ baseA x := by
  unfold baseA
  exact div_nonneg (mul_nonneg (by linarith) (by linarith)) (by norm_num)

theorem tangent_coefficient_pos {x : ℝ} (hx : 3 / 2 ≤ x) :
    0 < 3 * baseA x - baseK x := by
  have hS : x + 1 ≠ 0 := by linarith
  have ht : 0 ≤ x - 3 / 2 := by linarith
  have hid : 3 * baseA x - baseK x =
      x * (74 * (x - 3 / 2) ^ 2 + 191 * (x - 3 / 2) + 59) /
        (384 * (x + 1)) := by
    unfold baseA baseK
    field_simp
    ring
  rw [hid]
  positivity

theorem tangent_remainder_pos {x : ℝ} (hx : 3 / 2 ≤ x) :
    0 < (3 * baseA x - baseK x) * (x - 4 / 5) + 2 * baseH x - 2 * baseA x := by
  have hS : x + 1 ≠ 0 := by linarith
  have ht : 0 ≤ x - 3 / 2 := by linarith
  have hid : (3 * baseA x - baseK x) * (x - 4 / 5) + 2 * baseH x - 2 * baseA x =
      x * (410 * (x - 3 / 2) ^ 3 + 1174 * (x - 3 / 2) ^ 2 +
        (1067 / 2) * (x - 3 / 2) + 13 / 2) / (1920 * (x + 1)) := by
    unfold baseA baseK baseH
    field_simp
    ring
  rw [hid]
  positivity

/-- The cubic tangent at `e = 1` leaves two nonnegative terms and a positive remainder. -/
theorem displacement_numerator_pos {x e : ℝ} (hx : 3 / 2 ≤ x) (he : x - 4 / 5 ≤ e) :
    0 < baseA x * e ^ 3 - baseK x * e + 2 * baseH x := by
  have he0 : 0 < e := by linarith
  have h1 := mul_nonneg (baseA_nonneg hx) (mul_nonneg (sq_nonneg (e - 1))
    (show 0 ≤ e + 2 by linarith))
  have h2 := mul_nonneg (tangent_coefficient_pos hx).le (sub_nonneg.mpr he)
  have h3 := tangent_remainder_pos hx
  have hid : baseA x * e ^ 3 - baseK x * e + 2 * baseH x =
      baseA x * ((e - 1) ^ 2 * (e + 2)) +
      (3 * baseA x - baseK x) * (e - (x - 4 / 5)) +
      ((3 * baseA x - baseK x) * (x - 4 / 5) + 2 * baseH x - 2 * baseA x) := by ring
  linarith only [hid, h1, h2, h3]

theorem base_hasDerivAt {x e : ℝ} (he : 0 < e) :
    HasDerivAt (base x)
      (-(baseA x * e ^ 3 - baseK x * e + 2 * baseH x) / e ^ 3) e := by
  have h1 := ((hasDerivAt_id e).const_mul (-baseA x)).add_const (baseB x)
  have h2 := (hasDerivAt_const e (baseK x)).div (hasDerivAt_id e) he.ne'
  have h3 := (hasDerivAt_const e (baseH x)).div ((hasDerivAt_id e).pow 2)
    (pow_ne_zero 2 he.ne')
  convert (h1.sub h2).add h3 using 1
  · rfl
  · simp only [id_eq, Pi.pow_apply]
    field_simp
    ring

/-- The largest displacement gives the largest curvature coefficient. -/
theorem le_upper_displacement {x C : ℝ} (hx : 3 / 2 ≤ x) (hC : C ≤ 4 / 5) :
    value x C (3 / 4) ≤ value x (4 / 5) (3 / 4) := by
  have hm := ss_le_of_deriv (f := fun e => -base x e)
    (f' := fun e => (baseA x * e ^ 3 - baseK x * e + 2 * baseH x) / e ^ 3)
    (x := x - 4 / 5) (y := x - C) (by linarith)
    (fun e he => by
      have hd := (base_hasDerivAt (x := x) (show 0 < e by linarith [he.1])).neg
      convert hd using 1
      ring)
    (fun e he => (div_pos (displacement_numerator_pos hx (by linarith [he.1]))
      (pow_pos (by linarith [he.1]) 3)).le)
  rw [lower_norm_eq (by linarith) (by linarith),
    lower_norm_eq (by linarith) (by linarith)]
  linarith only [hm]

end SmoothedOctagon.LowerRatioCurvature
