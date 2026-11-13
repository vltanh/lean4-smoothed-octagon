module

public import SmoothedOctagon.Exclusion.Mixed.SmallerShort.LowerRatio.OuterFace.SmallShape.Terminal.Signs

/-!
# The small-shape terminal comparison

The quotient-rule numerator decreases on each terminal interval. The
endpoint-minimum principle reduces all ten curves to their endpoints,
where the common lower bound is `1/80000`.
-/

@[expose] public section
namespace SmoothedOctagon.LowerRatioTerminal

theorem endpoint_bounds (k : Shape) {C u : ℝ}
    (hC : C = 1 / 2 ∨ C = 10 / 13) (hu : u = 3 / 4 ∨ u = 19 / 25) :
    1 / 80000 < test k C u (leftEnd k) ∧ 1 / 80000 < test k C u (rightEnd k) := by
  cases k <;> rcases hC with rfl | rfl <;> rcases hu with rfl | rfl <;>
    norm_num [test, curve, eval_numeratorList, alpha, betaSum,
      leftEnd, rightEnd, numerator, polyHorner]

theorem leftEnd_ge (k : Shape) : (3 / 2 : ℝ) ≤ leftEnd k := by
  cases k <;> norm_num [leftEnd]

theorem lower_bound (k : Shape) {C u x : ℝ}
    (hC : C = 1 / 2 ∨ C = 10 / 13) (hu : u = 3 / 4 ∨ u = 19 / 25)
    (hx : leftEnd k ≤ x) (hx' : x ≤ rightEnd k) : 1 / 80000 < test k C u x := by
  obtain ⟨hp, hq⟩ := endpoint_bounds k hC hu
  apply lt_of_lt_of_le (lt_min hp hq)
  apply endpoint_min hx hx'
  · intro s hs
    have hs0 := (leftEnd_ge k).trans hs.1
    exact curve_hasDerivAt _ _ _ (by linarith) (alpha_pos k hs0) (betaSum_pos k hC hs0)
  · intro s hs
    have hs0 := (leftEnd_ge k).trans hs.1
    exact slopeDenominator_pos (by linarith) (alpha_pos k hs0) (betaSum_pos k hC hs0)
  · intro s v hs hsv _
    have h := Horner.antitone_of_derivative_coefficients
      (Horner.shift (leftEnd k) (slope k C u)) (derivative_coefficients k hC hu)
      (show 0 ≤ s - leftEnd k by linarith) (show s - leftEnd k ≤ v - leftEnd k by linarith)
    rw [Horner.eval_shift, Horner.eval_shift,
      show leftEnd k + (v - leftEnd k) = v by ring,
      show leftEnd k + (s - leftEnd k) = s by ring] at h
    exact h

end SmoothedOctagon.LowerRatioTerminal
