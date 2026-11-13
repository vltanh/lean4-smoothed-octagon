module

public import SmoothedOctagon.Exclusion.Mixed.SmallerShort.LowerRatio.OuterFace.SmallShape.Curvature.Displacement
public import SmoothedOctagon.Exclusion.Mixed.Horner.DividedDifference

/-!
# The ratio comparison at the largest displacement

At `C = 4/5` and `u = 3/4`, clearing denominators gives a polynomial
quotient. Its divided difference from `x = 3/2` is a positive sextic in
`x - 1`, so the curvature is at most its value at that corner.
-/

@[expose] public section
namespace SmoothedOctagon.LowerRatioCurvature

/-- The numerator of the negative curvature after clearing `1920(x+1)²(5x-4)²`. -/
noncomputable def cornerNumerator : List ℝ :=
  let X := [0, 1]
  let S := [1, 1]
  let E := [-4, 5]
  Horner.add
    (Horner.smul 12 (Horner.mul (Horner.mul X [-2, 3])
      (Horner.mul (Horner.pow E 3) (Horner.pow S 2))))
    (Horner.add
      (Horner.smul 5 (Horner.mul [-5, 16, -50, -144, -33, 24] (Horner.pow E 2)))
      (Horner.add
        (Horner.smul 25 (Horner.mul (Horner.mul X [-11, 67, 34]) (Horner.mul S E)))
        (Horner.smul (-250) (Horner.mul (Horner.mul X [-1, 5, 2]) (Horner.pow S 2)))))

noncomputable def cornerDenominator : List ℝ :=
  Horner.smul 1920 (Horner.mul (Horner.pow [1, 1] 2) (Horner.pow [-4, 5] 2))

theorem eval_cornerNumerator (x : ℝ) :
    polyHorner cornerNumerator x =
      12 * x * (3 * x - 2) * (5 * x - 4) ^ 3 * (x + 1) ^ 2 +
      5 * (24 * x ^ 5 - 33 * x ^ 4 - 144 * x ^ 3 - 50 * x ^ 2 + 16 * x - 5) *
        (5 * x - 4) ^ 2 +
      25 * x * (34 * x ^ 2 + 67 * x - 11) * (x + 1) * (5 * x - 4) -
      250 * x * (2 * x ^ 2 + 5 * x - 1) * (x + 1) ^ 2 := by
  simp only [cornerNumerator, Horner.eval_add, Horner.eval_smul, Horner.eval_mul,
    Horner.eval_pow, polyHorner]
  ring

theorem eval_cornerDenominator (x : ℝ) :
    polyHorner cornerDenominator x = 1920 * (x + 1) ^ 2 * (5 * x - 4) ^ 2 := by
  simp only [cornerDenominator, Horner.eval_smul, Horner.eval_mul, Horner.eval_pow, polyHorner]
  ring

theorem cornerDenominator_pos {x : ℝ} (hx : 1 ≤ x) :
    0 < polyHorner cornerDenominator x := by
  rw [eval_cornerDenominator]
  have : 0 < 5 * x - 4 := by linarith
  positivity

theorem base_corner_eq {x : ℝ} (hx : 1 ≤ x) :
    base x (x - 4 / 5) = -polyHorner cornerNumerator x / polyHorner cornerDenominator x := by
  have hS : x + 1 ≠ 0 := by linarith
  have hE : 5 * x - 4 ≠ 0 := by linarith
  rw [eval_cornerNumerator, eval_cornerDenominator]
  rw [show x - 4 / 5 = (5 * x - 4) / 5 by ring]
  unfold base baseA baseB baseK baseH
  generalize x + 1 = S at *
  generalize 5 * x - 4 = E at *
  field_simp
  ring

/-- Cross multiplication compares the quotient with its value at `x = 3/2`. -/
noncomputable def cornerDifference : List ℝ :=
  Horner.add
    (Horner.smul (polyHorner cornerDenominator (3 / 2)) cornerNumerator)
    (Horner.smul (-polyHorner cornerNumerator (3 / 2)) cornerDenominator)

noncomputable def cornerQuotient : List ℝ := Horner.dividedDifference cornerDifference (3 / 2)

theorem cornerQuotient_coefficients :
    ∀ c ∈ Horner.shift 1 cornerQuotient, 0 ≤ c := by
  norm_num [cornerQuotient, cornerDifference, cornerNumerator, cornerDenominator,
    Horner.dividedDifference, Horner.shift, Horner.add, Horner.smul, Horner.mul,
    Horner.pow, polyHorner]

theorem cornerDifference_nonneg {x : ℝ} (hx : 3 / 2 ≤ x) :
    0 ≤ polyHorner cornerDifference x := by
  have hq := Horner.eval_nonneg _ cornerQuotient_coefficients
    (show 0 ≤ x - 1 by linarith)
  rw [Horner.eval_shift, show 1 + (x - 1) = x by ring] at hq
  have hd := Horner.eval_dividedDifference cornerDifference (3 / 2) x
  change (x - 3 / 2) * polyHorner cornerQuotient x =
    polyHorner cornerDifference x - polyHorner cornerDifference (3 / 2) at hd
  have hc : polyHorner cornerDifference (3 / 2) = 0 := by
    simp only [cornerDifference, Horner.eval_add, Horner.eval_smul]
    ring
  rw [hc] at hd
  nlinarith only [hd, mul_nonneg (sub_nonneg.mpr hx) hq]

theorem le_ratio_corner {x : ℝ} (hx : 3 / 2 ≤ x) :
    value x (4 / 5) (3 / 4) ≤ value (3 / 2) (4 / 5) (3 / 4) := by
  rw [lower_norm_eq (by linarith) (by linarith),
    lower_norm_eq (by norm_num) (by norm_num), base_corner_eq (by linarith),
    base_corner_eq (by norm_num)]
  apply (div_le_div_iff₀ (cornerDenominator_pos (by linarith))
    (cornerDenominator_pos (by norm_num))).mpr
  have hp := cornerDifference_nonneg hx
  simp only [cornerDifference, Horner.eval_add, Horner.eval_smul] at hp
  nlinarith only [hp]

end SmoothedOctagon.LowerRatioCurvature
