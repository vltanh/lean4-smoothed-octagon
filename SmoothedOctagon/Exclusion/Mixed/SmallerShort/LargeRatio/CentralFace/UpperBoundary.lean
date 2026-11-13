module

public import SmoothedOctagon.Exclusion.Mixed.SmallerShort.LargeRatio.CentralFace.UpperBoundary.Signs

/-!
# The central tests on the strong-order boundary

The upper beta boundary is used at its exact value. Normalizing the
position of alpha in its order interval gives `0 ≤ e ≤ 1`.
Each cleared numerator has a positive constant coefficient and nonnegative
higher coefficients in `x - 12/5`, so its sign holds for every `x ≥ 12/5`.
-/

@[expose] public section
namespace SmoothedOctagon.S0Central

noncomputable def upperBeta (x a : ℝ) : ℝ :=
  x + x * (7 * x + 1) * (a - 1) / gapDenominator x

theorem denominator_pos {x : ℝ} (hx : 0 ≤ x) : 0 < gapDenominator x := by
  unfold gapDenominator
  positivity

theorem upperBeta_eq (x a : ℝ) (hq : gapDenominator x ≠ 0) :
    upperBeta x a = betaNumerator x a / gapDenominator x := by
  unfold upperBeta betaNumerator
  field_simp

theorem upperBeta_ge {x a : ℝ} (hx : 0 ≤ x) (ha : 1 ≤ a) : x ≤ upperBeta x a := by
  have ha0 : 0 ≤ a - 1 := sub_nonneg.mpr ha
  have hp : 0 ≤ x * (7 * x + 1) * (a - 1) / gapDenominator x := by
    apply div_nonneg (by positivity) (denominator_pos hx).le
  unfold upperBeta
  linarith only [hp]

private theorem positive_of_normalization {f v : ℝ → ℝ → ℝ}
    (heq : ∀ u e, normalization * f (12 / 5 + u)
      (1 + e / 12 * (5 * (12 / 5 + u) - 8)) = v u e)
    (hpos : ∀ u e, 0 ≤ u → 0 ≤ e → e ≤ 1 → 0 < v u e)
    {x a : ℝ} (hx : 12 / 5 ≤ x) (ha : 1 ≤ a) (ha1 : a ≤ (5 * x + 4) / 12) :
    0 < f x a := by
  have hd : 0 < 5 * x - 8 := by linarith only [hx]
  let e := 12 * (a - 1) / (5 * x - 8)
  have he0 : 0 ≤ e := div_nonneg (by linarith only [ha]) hd.le
  have he1 : e ≤ 1 := by
    dsimp only [e]
    rw [div_le_iff₀ hd]
    linarith only [ha1]
  have he : 1 + e / 12 * (5 * x - 8) = a := by
    dsimp only [e]
    field_simp
    ring
  have hvalue := hpos (x - 12 / 5) e (by linarith only [hx]) he0 he1
  have hh := heq (x - 12 / 5) e
  have hs : 12 / 5 + (x - 12 / 5) = x := by ring
  rw [hs, he] at hh
  rw [← hh] at hvalue
  exact (mul_pos_iff_of_pos_left (by norm_num [normalization])).mp hvalue

theorem upper2_neg {x a : ℝ} (hx : 12 / 5 ≤ x) (ha : 1 ≤ a)
    (ha1 : a ≤ (5 * x + 4) / 12) : lgrG2 x a (upperBeta x a) < 0 := by
  have hx0 : 0 < x := by linarith only [hx]
  have hq := denominator_pos hx0.le
  apply lgr_G2_neg (by linarith only [hx]) (by linarith only [ha])
    (by linarith only [upperBeta_ge hx0.le ha, hx])
  have hp := positive_of_normalization value2_eq
    (fun _ _ hu he0 he1 => value2_pos hu he0 he1) hx ha ha1
  have he := numerator2_link x a hq.ne'
  rw [← upperBeta_eq x a hq.ne'] at he
  rw [← he] at hp
  exact (mul_pos_iff_of_pos_left (pow_pos hq 4)).mp hp

theorem upperT_neg {x a : ℝ} (hx : 12 / 5 ≤ x) (ha : 1 ≤ a)
    (ha1 : a ≤ (5 * x + 4) / 12) : lgrGT x a (upperBeta x a) < 0 := by
  have hx0 : 0 < x := by linarith only [hx]
  have hq := denominator_pos hx0.le
  apply lgr_GT_neg (by linarith only [hx]) (by linarith only [ha])
    (by linarith only [upperBeta_ge hx0.le ha, hx])
  have hp := positive_of_normalization valueT_eq
    (fun _ _ hu he0 he1 => valueT_pos hu he0 he1) hx ha ha1
  have he := numeratorT_link x a hq.ne'
  rw [← upperBeta_eq x a hq.ne'] at he
  rw [← he] at hp
  exact (mul_pos_iff_of_pos_left (pow_pos hq 4)).mp hp

theorem upper8_neg {x a : ℝ} (hx : 12 / 5 ≤ x) (ha : 1 ≤ a)
    (ha1 : a ≤ (5 * x + 4) / 12) : lgrG8 x a (upperBeta x a) < 0 := by
  have hx0 : 0 < x := by linarith only [hx]
  have hq := denominator_pos hx0.le
  apply lgr_G8_neg (by linarith only [hx]) (by linarith only [ha])
    (by linarith only [upperBeta_ge hx0.le ha, hx])
  have hp := positive_of_normalization value8_eq
    (fun _ _ hu he0 he1 => value8_pos hu he0 he1) hx ha ha1
  have he := numerator8_link x a hq.ne'
  rw [← upperBeta_eq x a hq.ne'] at he
  rw [← he] at hp
  exact (mul_pos_iff_of_pos_left (pow_pos hq 4)).mp hp

end SmoothedOctagon.S0Central
