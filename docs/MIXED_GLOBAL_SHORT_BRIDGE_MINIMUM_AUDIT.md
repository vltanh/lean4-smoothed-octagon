# Independent audit of the complete two-short-bridge minimum theorem

Date: 2026-11-07 UTC. Reviewer: `normality_audit`.

I read `MIXED_GLOBAL_SHORT_BRIDGE_MINIMUM.md` in full and checked its
actual multiplier interface, all boundary alternatives, and the
positive-component continuation. The theorem passes, with no
mathematical correction required.

## Actual period and strict root maximum

The two neighboring short bridges give one actual pair of turn norms,
not separately fitted multipliers. The exact two-secant equations
give the stated order, its quantitative strengthening, and the two
norm upper bounds. Reflection legitimately selects `C<=b`. For the
central reverse arc, positivity is exactly `q>q0`. At the transported
outer centre, its genuine opposite reverse switch gives
`2<t_act<T`, the exact equation `R(t_act)=0`, and the strict incident
bound `3/4<w<f'(t_act)`. The latter uses the already proved normal
switch rigidity. Therefore the maximum occurs at a parameter strictly
between 2 and `t_act`, and its value is strictly positive.

The broader actual interface also holds when `a` is only no larger
than its **two neighboring reverse centres** `A,Dright`, with both
intervening forward runs short. None of the scalar inequalities uses
absolute minimality elsewhere in the period. The manuscript
conservatively states the consequence needed here: a global active
minimum must touch a nonshort forward run.

## Independent review of the constituent comparisons

The general central residual and positive-diagonal scale arguments
were previously audited, including all literal coefficient tables.
I also independently reviewed the new complete endpoint package:

* The entire upper endpoint is strictly negative for both diagonal
  signs; all thirteen exact checks and its 803-entry positive table
  pass, including the strengthened-order boundary.
* The central convex-chord face now covers both signs. All ten exact
  checks and all 13,348 positive entries pass. Its norm interval is
  retained, so no chord extrapolation below `3/4` is used.
* The central truncated value also covers both signs. All fourteen
  checks, the 11,438-entry derivative table, and the 1,905-entry
  equal-turn table pass. Its polynomial monotonicity and `T=2`
  boundary comparison have the precise scope recorded in the
  companion central-R2 audit.
* The nonnegative-diagonal lower-norm numerator is strictly decreasing
  in inverse scale. All thirteen exact checks and its complete
  3,242/2,172/39 positive tables pass. Only the two now-proved endpoint
  values are used to obtain the global negative truncated value.
* The nonpositive-diagonal derivative applies to the actual truncated
  maximum through every `w<=3/4`, including negative scalar w. A root
  between its maximizing parameter and T reconstructs
  `E_L<3rho_A`; that bound is not an additional continuation
  hypothesis. The two maximum formulas are continuously
  differentiable at `w=3/4`. Its thirteen exact identities pass.

## Complete continuation and endpoints

The comparison interval `q>=max(q0,2Q-sigma)` is closed on the side
reached by increasing rho from the actual point. Its endpoint is
exactly central zero factor or `T=2`. All quantities there are finite
and the maximum over the compact interval `[2,T]` is continuous.
Intermediate comparison points need not be PMP trajectories or retain
the original covector; the needed scalar inequalities hold throughout
their stated domain.

For positive diagonal, the decreasing numerator and the two negative
endpoint values prove `R2<0` throughout the interval. Together with
the whole `R(T)<0` theorem, this forces a positive maximum to remain
strictly interior. Its derivative in rho is positive. The connected
positive component therefore cannot end at zero before the final
comparison endpoint, or meet either endpoint-maximizer branch.

For nonpositive diagonal, the correct maximum has positive derivative
whether its maximizer is 2 or interior; the formulas join with the
same derivative. The upper endpoint is again strictly negative, and
the outer reverse estimate is reconstructed at every feasible point.
No lower-norm exit, upper-derivative exit, determinant boundary, or
extra root-feasibility condition is omitted.

In either case, continuity would carry a value at least as large as
the positive actual maximum to the final endpoint. At `T=2` the
maximum equals the negative upper endpoint. At central zero factor,
the low-, middle-, and high-norm branches are respectively covered
by the truncated value, chord value, and upper endpoint. Every final
maximum is negative, giving the required contradiction.

## Scope retained

The resulting theorem places every mixed global active minimum at a
reverse centre touching a forward run of length at least two, after
the independently proved small-forward-minimum theorem. It does not
exclude those nonshort bridges, bound their number or length, or
close F or M2. The independent scale bound `a^2<12/17` applies to
that reverse centre. No endpoint rank, implicit-function theorem,
geometric comparison trajectory, Lean/Lake, typechecking, CI, floating
sign test, or increasing-length catalogue is used in this theorem.
