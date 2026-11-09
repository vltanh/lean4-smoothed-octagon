module

public import Mathlib.Analysis.Calculus.Deriv.Pow
public import Mathlib.Analysis.SpecialFunctions.Log.Deriv
public meta import Mathlib.Tactic.Positivity

/-!
# Derivative rules for the scalar comparisons

These tactics compose the ordinary derivative rules for rational expressions,
with an optional logarithm rule. They leave the resulting algebraic identity to
`ring` or `field_simp` and use only the hypotheses for denominator signs.
-/

public meta section

/-- Differentiate a rational expression by the product and quotient rules. -/
syntax "rational_deriv" : tactic
macro_rules
| `(tactic| rational_deriv) => `(tactic|
  first
  | assumption
  | exact hasDerivAt_id' _
  | exact hasDerivAt_const _ _
  | apply HasDerivAt.add <;> rational_deriv
  | apply HasDerivAt.sub <;> rational_deriv
  | apply HasDerivAt.pow <;> rational_deriv
  | apply HasDerivAt.mul <;> rational_deriv
  | apply HasDerivAt.div <;> first | rational_deriv | positivity | assumption
  | apply HasDerivAt.neg <;> rational_deriv)

/-- Differentiate an expression built from rational operations and logarithms. -/
syntax "elementary_deriv" : tactic
macro_rules
| `(tactic| elementary_deriv) => `(tactic|
  first
  | assumption
  | exact hasDerivAt_id' _
  | exact hasDerivAt_const _ _
  | apply HasDerivAt.add <;> elementary_deriv
  | apply HasDerivAt.sub <;> elementary_deriv
  | apply HasDerivAt.pow <;> elementary_deriv
  | apply HasDerivAt.mul <;> elementary_deriv
  | apply HasDerivAt.div <;> first | elementary_deriv | positivity | assumption
  | apply HasDerivAt.neg <;> elementary_deriv
  | apply HasDerivAt.log <;> first | elementary_deriv | positivity | assumption)
