module

public import SmoothedOctagon.Exclusion.Mixed.Nonshort.UnitShape.Boundary
public import SmoothedOctagon.Exclusion.Mixed.Nonshort.UnitShape.Monotonicity

/-!
# Bounds for the value and cross term on the unit face

Move the order gap to `max 0 (1/4-x)`. Monotonicity transfers the
three boundary inequalities to the whole shape domain.
-/

@[expose] public section

namespace SmoothedOctagon.UnitShape

theorem value_cross_bounds {x r : ℝ} (hx : 0 < x) (hx1 : x ≤ 1) (hr : 0 ≤ r)
    (hr0 : 1 / 4 - x ≤ r) (hrx : r ≤ x * (1 + x)) (hr1 : r ≤ 1 - x) :
    0 < value x r ∧ 0 < constant x r + 8 * cross x r ∧
      0 < cross x r + 32 * value x r := by
  let a := max 0 (1 / 4 - x)
  have ha : 0 ≤ a := le_max_left _ _
  have har : a ≤ r := max_le hr hr0
  obtain ⟨hV, hC, hS⟩ := lower_boundary_pos hx hx1
  have hVm := value_mono hx.le hx1 ha har hrx
  have hCm := constant_mono hx.le ha har
  have hSm := cross_mono hx.le hx1 ha har hr1
  change 0 < value x a at hV
  change 0 < constant x a + 8 * cross x a at hC
  change 0 < cross x a + 32 * value x a at hS
  exact ⟨hV.trans_le hVm, by linarith only [hC, hCm, hSm], by linarith only [hS, hSm, hVm]⟩

end SmoothedOctagon.UnitShape
