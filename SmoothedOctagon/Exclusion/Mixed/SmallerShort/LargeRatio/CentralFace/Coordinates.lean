module

public import SmoothedOctagon.Exclusion.Mixed.SmallerShort.Basic

/-!
# Coordinates for the central order region

The substitution `x = 12/5 + X`, `a = 1 + e(5x-8)/12` identifies the
order region with `X ≥ 0`, `0 ≤ e ≤ 1`. Positivity of a normalized
expression therefore gives positivity in the original variables.
-/

@[expose] public section
namespace SmoothedOctagon.S0Central

theorem positive_of_coordinates {f v : ℝ → ℝ → ℝ} {C : ℝ}
    (hC : 0 < C)
    (heq : ∀ u e, C * f (12 / 5 + u)
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
  exact (mul_pos_iff_of_pos_left hC).mp hvalue

end SmoothedOctagon.S0Central
