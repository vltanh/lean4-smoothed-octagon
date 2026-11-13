module

public import SmoothedOctagon.Exclusion.Mixed.SmallerShort.Basic

/-!
# Coordinates for the outer strip

The alpha interval has constant width `13/55`. Its normalized position
is `e = (55a - 22x - 20)/13`, with `0 ≤ e ≤ 1`.
-/

@[expose] public section
namespace SmoothedOctagon.S0Outer

noncomputable def position (x a : ℝ) : ℝ := (55 * a - 22 * x - 20) / 13

theorem position_nonneg {x a : ℝ} (ha : (22 * x + 20) / 55 ≤ a) :
    0 ≤ position x a := by unfold position; linarith only [ha]

theorem position_le_one {x a : ℝ} (ha : a ≤ (2 * x + 3) / 5) :
    position x a ≤ 1 := by unfold position; linarith only [ha]

theorem normalization_eq {f v : ℝ → ℝ → ℝ} {C : ℝ}
    (heq : ∀ X e, C * f (12 / 5 + X) ((22 * (12 / 5 + X) + 20 + 13 * e) / 55) = v X e)
    (x a : ℝ) : C * f x a = v (x - 12 / 5) (position x a) := by
  have h := heq (x - 12 / 5) (position x a)
  rw [show (12 : ℝ) / 5 + (x - 12 / 5) = x by ring] at h
  have ha : (22 * x + 20 + 13 * position x a) / 55 = a := by unfold position; ring
  rwa [ha] at h

end SmoothedOctagon.S0Outer
