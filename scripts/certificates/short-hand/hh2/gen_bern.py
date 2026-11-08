"""Writes Heavy/S2Bern.lean: positivity of Bernstein forms of degree 1..24."""
from leangen import Lib
from common import write
lib = Lib('hh2')
write('S2Bern.lean', ['Mathlib.Basic.Real.Basic', 'Mathlib.Tactic.Positivity', 'Mathlib.Tactic.Linarith',
                      'Mathlib.Tactic.LinearCombination', 'Mathlib.Tactic.Ring'],
      'positivity of Bernstein forms',
      "For `a, b ≥ 0` with `a + b > 0` and positive coefficients `c₀, …, c_n`, the Bernstein form "
      "`∑ c_k a^k b^(n-k)` is positive. Used by the nested Bernstein certificates `Heavy/S2*`.",
      "* `hh2BernPos1`, …, `hh2BernPos24`.", lib.render_pos(range(1, 25)), 'gen_bern.py')
