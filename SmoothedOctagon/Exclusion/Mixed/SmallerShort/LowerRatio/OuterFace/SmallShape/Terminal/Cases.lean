module

public import SmoothedOctagon.Exclusion.Mixed.SmallerShort.LowerRatio.OuterFace.SmallShape.Terminal.Polynomial

/-!
# The three terminal shape boundaries

The fixed shape `6/5`, the lower line `(6x + 3)/13` and the unit shape
carry the terminal comparisons for the small-shape duration test.
-/

@[expose] public section
namespace SmoothedOctagon.LowerRatioTerminal

inductive Shape where
  | fixed
  | line
  | unit

noncomputable def alpha : Shape → List ℝ
  | .fixed => [6 / 5]
  | .line => [3 / 13, 6 / 13]
  | .unit => [1]

noncomputable def betaSum : Shape → ℝ → List ℝ
  | .fixed, C => [(6 + C) / 5, 1]
  | .line, C => [(3 - 10 * C) / 13, (19 + 6 * C) / 13]
  | .unit, _ => [1, 1]

noncomputable def leftEnd : Shape → ℝ
  | .fixed => 3 / 2
  | .line => 5 / 3
  | .unit => 3 / 2

noncomputable def rightEnd : Shape → ℝ
  | .fixed | .line => 2
  | .unit => 5 / 3

noncomputable def slope (k : Shape) (C u : ℝ) : List ℝ :=
  slopeList (numeratorList (alpha k) (betaSum k C) u) (alpha k) (betaSum k C)

noncomputable def test (k : Shape) (C u : ℝ) : ℝ → ℝ :=
  curve (numeratorList (alpha k) (betaSum k C) u) (alpha k) (betaSum k C)

theorem alpha_pos (k : Shape) {x : ℝ} (hx : 3 / 2 ≤ x) : 0 < polyHorner (alpha k) x := by
  cases k <;> simp only [alpha, polyHorner] <;> linarith

theorem betaSum_pos (k : Shape) {C x : ℝ} (hC : C = 1 / 2 ∨ C = 10 / 13)
    (hx : 3 / 2 ≤ x) : 0 < polyHorner (betaSum k C) x := by
  cases k <;> rcases hC with rfl | rfl <;> norm_num [betaSum, polyHorner] <;> linarith

theorem face_test (k : Shape) {x C u : ℝ} (hC : C = 1 / 2 ∨ C = 10 / 13) (hx : 3 / 2 ≤ x) :
    test k C u x = lroF1 x (polyHorner (alpha k) x)
      (x + C * (polyHorner (alpha k) x - 1)) u := by
  have hA := alpha_pos k hx
  have he : polyHorner (alpha k) x + (x + C * (polyHorner (alpha k) x - 1)) =
      polyHorner (betaSum k C) x := by
    cases k <;> simp only [alpha, betaSum, polyHorner] <;> ring
  rw [face_eq (by linarith) hA (he ▸ betaSum_pos k hC hx), he]
  simp only [test, curve, eval_numeratorList]

end SmoothedOctagon.LowerRatioTerminal
