# Independent audit of the all-sign central truncated value

Date: 2026-11-07 UTC. Reviewer: `normality_audit`.

The scalar theorem in `MIXED_GLOBAL_SHORT_BRIDGE_TRUNCATED_FACE.md` passes review.
I read the full argument and exact replay, and independently read all
11,438 unique positive derivative coefficients and all 1,905 unique
positive equal-turn coefficients. All fourteen exact checks pass.

The rational logarithm lower bound has the correct sign in the upper
bound for `R2`. Both affine norm coefficients are positive for either
diagonal sign; the positive-diagonal comparison uses `2<=T`, and the
nonpositive case is positive term by term. Raising norms after this
step does not assume that the resulting scalar point remains in an
outer-root interval.

The monotonicity in `ell` is correctly asserted for the **cleared
polynomial**, not for the rational residual. Its positive clearing
factors and `G_ell=rden*(h+j+2)>0` mean that lowering `ell` within
the allowed domain reaches exactly `ell=0` or `G=0`. The strengthened
order and `j>0` are preserved in that comparison.

At `G=0`, the Padé logarithm is exact, and the boundary is `T=2`.
The argument correctly invokes only the independently proved initial
upper-endpoint value at `Vbar`, rather than applying that theorem to
norms outside its statement. The exact positive difference
`Vbar-Vplus` and the positive norm coefficients justify the comparison.

At `ell=0`, `G>=0` indeed forces `j>h`. Substitution `j=h+t`, with
`t>0`, gives the stated square plus positive polynomial. I checked
both strict reserves, 26748301344768 at `t^3` and 10154447732736 at
`t^3*z^5`. The complete two integer identities pass. The leading
`z^5` comparison preserves the derivative sign and both boundary
arguments, with a positive limiting clearing factor; hence the closed
strengthened-order face is included.

No mathematical correction was required. The result proves the
central `R2<0` value for either diagonal sign, including all auxiliary
norms below `3/4`. Its actual-period consequence requires the separate
scale, endpoint, and positive-component continuation lemmas. No M2
closure follows from this scalar face alone. No Lean, Lake,
typechecking, CI, floating sign test, or length catalogue was used.
