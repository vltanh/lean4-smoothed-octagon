module

public import SmoothedOctagon.Exclusion.Mixed.SmallerShort.LowerRatio.OuterFace.SmallShape.Terminal.Cases

/-!
# Decreasing derivative numerators on the terminal boundaries

The coefficient signs below concern the derivative of the actual quotient-rule
numerator. Translation places each ratio interval in the nonnegative half-line.
-/

@[expose] public section
namespace SmoothedOctagon.LowerRatioTerminal

theorem fixed_hf : ∀ c ∈ Horner.derivative (Horner.shift (3 / 2) (slope .fixed (1 / 2) (3 / 4))), c ≤ 0 := by
  norm_num [slope, alpha, betaSum, slopeList, numeratorList,
    Horner.derivative, Horner.shift, Horner.pow, Horner.mul, Horner.add, Horner.smul]

theorem fixed_hv : ∀ c ∈ Horner.derivative (Horner.shift (3 / 2) (slope .fixed (1 / 2) (19 / 25))), c ≤ 0 := by
  norm_num [slope, alpha, betaSum, slopeList, numeratorList,
    Horner.derivative, Horner.shift, Horner.pow, Horner.mul, Horner.add, Horner.smul]

theorem fixed_tf : ∀ c ∈ Horner.derivative (Horner.shift (3 / 2) (slope .fixed (10 / 13) (3 / 4))), c ≤ 0 := by
  norm_num [slope, alpha, betaSum, slopeList, numeratorList,
    Horner.derivative, Horner.shift, Horner.pow, Horner.mul, Horner.add, Horner.smul]

theorem fixed_tv : ∀ c ∈ Horner.derivative (Horner.shift (3 / 2) (slope .fixed (10 / 13) (19 / 25))), c ≤ 0 := by
  norm_num [slope, alpha, betaSum, slopeList, numeratorList,
    Horner.derivative, Horner.shift, Horner.pow, Horner.mul, Horner.add, Horner.smul]

theorem line_hf : ∀ c ∈ Horner.derivative (Horner.shift (5 / 3) (slope .line (1 / 2) (3 / 4))), c ≤ 0 := by
  norm_num [slope, alpha, betaSum, slopeList, numeratorList,
    Horner.derivative, Horner.shift, Horner.pow, Horner.mul, Horner.add, Horner.smul]

theorem line_hv : ∀ c ∈ Horner.derivative (Horner.shift (5 / 3) (slope .line (1 / 2) (19 / 25))), c ≤ 0 := by
  norm_num [slope, alpha, betaSum, slopeList, numeratorList,
    Horner.derivative, Horner.shift, Horner.pow, Horner.mul, Horner.add, Horner.smul]

theorem line_tf : ∀ c ∈ Horner.derivative (Horner.shift (5 / 3) (slope .line (10 / 13) (3 / 4))), c ≤ 0 := by
  norm_num [slope, alpha, betaSum, slopeList, numeratorList,
    Horner.derivative, Horner.shift, Horner.pow, Horner.mul, Horner.add, Horner.smul]

theorem line_tv : ∀ c ∈ Horner.derivative (Horner.shift (5 / 3) (slope .line (10 / 13) (19 / 25))), c ≤ 0 := by
  norm_num [slope, alpha, betaSum, slopeList, numeratorList,
    Horner.derivative, Horner.shift, Horner.pow, Horner.mul, Horner.add, Horner.smul]

theorem unit_f : ∀ c ∈ Horner.derivative (Horner.shift (3 / 2) (slope .unit (1 / 2) (3 / 4))), c ≤ 0 := by
  norm_num [slope, alpha, betaSum, slopeList, numeratorList,
    Horner.derivative, Horner.shift, Horner.pow, Horner.mul, Horner.add, Horner.smul]

theorem unit_v : ∀ c ∈ Horner.derivative (Horner.shift (3 / 2) (slope .unit (1 / 2) (19 / 25))), c ≤ 0 := by
  norm_num [slope, alpha, betaSum, slopeList, numeratorList,
    Horner.derivative, Horner.shift, Horner.pow, Horner.mul, Horner.add, Horner.smul]

theorem derivative_coefficients (k : Shape) {C u : ℝ}
    (hC : C = 1 / 2 ∨ C = 10 / 13) (hu : u = 3 / 4 ∨ u = 19 / 25) :
    ∀ c ∈ Horner.derivative (Horner.shift (leftEnd k) (slope k C u)), c ≤ 0 := by
  cases k <;> rcases hC with rfl | rfl <;> rcases hu with rfl | rfl
  · exact fixed_hf
  · exact fixed_hv
  · exact fixed_tf
  · exact fixed_tv
  · exact line_hf
  · exact line_hv
  · exact line_tf
  · exact line_tv
  · exact unit_f
  · exact unit_v
  · exact unit_f
  · exact unit_v

end SmoothedOctagon.LowerRatioTerminal
