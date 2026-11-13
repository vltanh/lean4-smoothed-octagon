module

public import SmoothedOctagon.Exclusion.Mixed.SmallerShort.LowerRatio.OuterFace.SmallShape.Terminal.Calculus

/-!
# The terminal curves and their derivatives

The numerator is computed from the transport formula. Clearing one copy of
each denominator factor from the quotient rule gives the derivative
numerator; no sign bound is used in these identities.
-/

@[expose] public section
namespace SmoothedOctagon.LowerRatioTerminal

local infixl:65 " +ₚ " => Horner.add
local infixl:70 " *ₚ " => Horner.mul
local infixr:80 " ^ₚ " => Horner.pow

noncomputable def numeratorList (a B : List ℝ) (u : ℝ) : List ℝ :=
  let X := [0, 1]
  let S := [1, 1]
  let K := Horner.smul 6 (a ^ₚ 2) +ₚ [1]
  let b := B +ₚ Horner.smul (-1) a
  let D := (a ^ₚ 2) +ₚ Horner.smul 2 (a *ₚ b) +ₚ [1] +ₚ
    Horner.smul 2 X +ₚ Horner.smul (-2) (b *ₚ X)
  let J := K *ₚ (Horner.smul (u - 1) (S ^ₚ 2) +ₚ [1]) +ₚ
    (Horner.smul 2 S +ₚ [-1]) *ₚ S
  let M := (K ^ₚ 2) +ₚ Horner.smul (-1) (S *ₚ K) +ₚ (S ^ₚ 2)
  let W := S *ₚ (M +ₚ Horner.smul u (D ^ₚ 2)) +ₚ Horner.smul (-1) (D *ₚ J)
  let E := Horner.smul (2 * u) (D *ₚ S) +ₚ Horner.smul (-1) J
  let L := Horner.smul 2 B +ₚ Horner.smul 7 a
  Horner.smul 2 ((Horner.smul (4 * u) (M *ₚ (S ^ₚ 2)) +ₚ Horner.smul (-1) (J ^ₚ 2)) *ₚ B *ₚ (L ^ₚ 3)) +ₚ
    Horner.smul (-12) (a *ₚ S *ₚ (L ^ₚ 3) *ₚ W) +ₚ
    Horner.smul 357 ((a ^ₚ 5) *ₚ (S ^ₚ 2) *ₚ (L ^ₚ 3)) +ₚ
    Horner.smul (-84 * (u - 1)) ((a ^ₚ 3) *ₚ (S ^ₚ 2) *ₚ (B ^ₚ 2) *ₚ (L ^ₚ 3)) +ₚ
    Horner.smul 12 ((a ^ₚ 2) *ₚ S *ₚ B *ₚ (L ^ₚ 3) *ₚ E) +ₚ
    Horner.smul (-224) ((a ^ₚ 4) *ₚ (S ^ₚ 2) *ₚ B *ₚ
      ((Horner.smul 2 B ^ₚ 3) +ₚ Horner.smul (-1) (Horner.smul 7 a ^ₚ 3))) +ₚ
    Horner.smul (-72) ((a ^ₚ 4) *ₚ (S ^ₚ 2) *ₚ B *ₚ (L ^ₚ 3))

theorem eval_numeratorList (a B : List ℝ) (u x : ℝ) :
    polyHorner (numeratorList a B u) x = numerator x (polyHorner a x) (polyHorner B x) u := by
  simp only [numeratorList, numerator, Horner.eval_add, Horner.eval_mul,
    Horner.eval_smul, Horner.eval_pow, polyHorner]
  ring

noncomputable def curve (n a B : List ℝ) (x : ℝ) : ℝ :=
  polyHorner n x / (1152 * polyHorner a x ^ 4 * (x + 1) ^ 2 * polyHorner B x *
    (2 * polyHorner B x + 7 * polyHorner a x) ^ 3) - 9193 / 50000

noncomputable def slopeList (n a B : List ℝ) : List ℝ :=
  let S := [1, 1]
  let L := Horner.smul 2 B +ₚ Horner.smul 7 a
  a *ₚ S *ₚ B *ₚ L *ₚ Horner.derivative n +ₚ Horner.smul (-1)
    ((Horner.smul 4 (Horner.derivative a *ₚ S *ₚ B *ₚ L) +ₚ
      Horner.smul 2 (a *ₚ B *ₚ L) +ₚ
      a *ₚ S *ₚ Horner.derivative B *ₚ L +ₚ
      Horner.smul 3 (a *ₚ S *ₚ B *ₚ Horner.derivative L)) *ₚ n)

noncomputable def slopeDenominator (a B : List ℝ) (x : ℝ) : ℝ :=
  1152 * polyHorner a x ^ 5 * (x + 1) ^ 3 * polyHorner B x ^ 2 *
    (2 * polyHorner B x + 7 * polyHorner a x) ^ 4

theorem slopeDenominator_pos {a B : List ℝ} {x : ℝ}
    (hx : 0 < x + 1) (ha : 0 < polyHorner a x) (hB : 0 < polyHorner B x) :
    0 < slopeDenominator a B x := by unfold slopeDenominator; positivity

theorem curve_hasDerivAt (n a B : List ℝ) {x : ℝ}
    (hx : 0 < x + 1) (ha : 0 < polyHorner a x) (hB : 0 < polyHorner B x) :
    HasDerivAt (curve n a B)
      (polyHorner (slopeList n a B) x / slopeDenominator a B x) x := by
  have hn := poly_hasDerivAt_horner n x
  have hA := poly_hasDerivAt_horner a x
  have hβ := poly_hasDerivAt_horner B x
  have hS := (hasDerivAt_id' x).add_const 1
  have hL := (hβ.const_mul 2).add (hA.const_mul 7)
  have hQ := (((((hA.fun_pow 4).const_mul 1152).mul (hS.fun_pow 2)).mul hβ).mul (hL.fun_pow 3))
  have hq0 : 1152 * polyHorner a x ^ 4 * (x + 1) ^ 2 * polyHorner B x *
      (2 * polyHorner B x + 7 * polyHorner a x) ^ 3 ≠ 0 := by positivity
  have h := (hn.div hQ hq0).sub_const (9193 / 50000)
  convert h using 1
  · rfl
  · simp only [slopeList, slopeDenominator, Horner.eval_add, Horner.eval_mul,
      Horner.eval_smul, Horner.eval_derivative, Horner.deriv_add, Horner.deriv_smul,
      polyHorner, Pi.add_apply, Pi.mul_apply]
    have hL0 : 2 * polyHorner B x + 7 * polyHorner a x ≠ 0 := by positivity
    field_simp
    ring

end SmoothedOctagon.LowerRatioTerminal
