module

public import Mathlib.Analysis.Calculus.Deriv.Add
public import Mathlib.Analysis.Calculus.Deriv.Inv
public import Mathlib.Analysis.Calculus.Deriv.Pow
public meta import Mathlib.Tactic.FieldSimp
public meta import Mathlib.Tactic.Positivity
public meta import Mathlib.Tactic.Ring

/-!
# The rational angle kernel

The exact score, central shear and pair term use the same kernel `t/(3+t²)`.
Its first two derivatives are proved here by the quotient rule.
-/

@[expose] public section

namespace SmoothedOctagon

noncomputable def costAngleKernel (t : ℝ) : ℝ := t/(3+t^2)
noncomputable def costAngleKernel1 (t : ℝ) : ℝ := (3-t^2)/(3+t^2)^2
noncomputable def costAngleKernel2 (t : ℝ) : ℝ := 2*t*(t^2-9)/(3+t^2)^3

theorem costAngleKernel_hasDerivAt (T : ℝ) : HasDerivAt costAngleKernel (costAngleKernel1 T) T := by
  have hd : 3+T^2 ≠ 0 := ne_of_gt (by positivity)
  have h := (hasDerivAt_id' T).div ((hasDerivAt_pow 2 T).const_add 3) hd
  refine h.congr_deriv ?_
  unfold costAngleKernel1
  norm_num
  field_simp
  ring

theorem costAngleKernel1_hasDerivAt (T : ℝ) : HasDerivAt costAngleKernel1 (costAngleKernel2 T) T := by
  have hd : 3+T^2 ≠ 0 := ne_of_gt (by positivity)
  have h := ((hasDerivAt_pow 2 T).const_sub 3).div
    (((hasDerivAt_pow 2 T).const_add 3).pow 2) (pow_ne_zero 2 hd)
  refine h.congr_deriv ?_
  unfold costAngleKernel2
  norm_num
  field_simp
  ring

end SmoothedOctagon
