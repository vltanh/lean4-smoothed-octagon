# Independent audit of the truncated outer-root scale reduction

Date: 2026-11-07 UTC. Reviewer: `normality_audit`.

I read `MIXED_GLOBAL_SHORT_BRIDGE_TRUNCATED_SCALE.md`, its fixed checker, and all three
named CSV tables. No mathematical correction was required.

The root expression `R2` is the maximum over `[2,T]` when `w<=3/4`,
because `f'(t)>=3/4` there; it agrees with the genuine maximum at
`w=3/4`. Thus the note uses the correct lower-norm extension and does
not extrapolate the convex chord from the other face.

I independently checked the differentiation and the hand concavity
argument. In particular:

* The combined logarithm is nonpositive by `q>=S*T0` and
  `P>=2*alpha^2*TB`.
* The nonlogarithmic constant is `-5`. Replacing `S` by `TB` in the
  negative `(u-1)S` term and in `1/S` increases the upper bound in
  both places. Substitution of `u<=U(1/TB)` and `v<=U(1/T0)` gives
  exactly `-7+8*rA+4*s^2+(2D-sigma)/q`.
* The identity `2Q-D-sigma=2x(beta-1)>0` implies both the last strict
  concavity bound and `Aq=2q+sigma-2D>0`. The two coefficients of the
  norms in the first derivative are strictly positive.
* The rational `V_+` is an upper bound, and is strictly larger than
  `V` since `x,y>1`. Its use therefore gives a strict derivative
  inequality even if an endpoint polynomial certificate is only
  nonnegative. Each logarithm is bounded only on the face where its
  argument is at least one.

The checker passed all thirteen exact identities/table checks. I also
read the literal CSVs independently: 3,242 unique positive integer
central remainder entries, 2,172 unique positive integer outer
remainder entries, and 39 unique positive integer multiplier entries.
The two polynomial identities have the stated normalizations,
including the common factor 183 in the outer identity. On their
respective faces, `G`, or `-G` and `Dt`, have exactly the signs used
by the certificates. The closed upper order boundary follows by
continuity; the actual strict `alpha<x` retains `x>1`, hence retains
the strict rational norm substitution.

The actual-lift and continuation scope is accurate. The comparison
holds geometry and actual incident norms fixed while changing inverse
scale; the intermediate points are not asserted to preserve the
original path or its primary multiplier. The theorem proves only
`N2'(q)<0` for `q>=max(q0,2Q-sigma)`. Both endpoint **value** signs
remain required: the central face including `w<3/4`, and the `T=2`
face. No lower-face closure, reverse-minimum placement next to a long
run, or M2 exclusion follows from this note alone.

No Lean, Lake, typechecking, CI, floating sign calculation, or growing
word-length catalogue was used in this audit.
