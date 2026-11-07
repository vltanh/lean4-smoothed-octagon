# Independent audit of the symmetric mixed-core exclusion

Date: 2026-11-07 UTC. Independent internal mathematical review of
[MIXED_GLOBAL_SYMMETRIC_ESCAPE](MIXED_GLOBAL_SYMMETRIC_ESCAPE.md).
This is not external peer review or Lean kernel validation. No Lean,
Lake, typechecking or CI was run.

## Finding and exact scope

The theorem is valid under its stated hypotheses. It excludes a complete,
strict-star, twisted PMP period of cost at most the octagon cost whenever
that period contains the stated reflection-symmetric `2121` core, with
four common factors `h`, `1<h<2`, scale `0<v<3`, a positive left control-0
pad, and a right control-0 pad of factor at least `h`.

The proof identifies the actual normal adjoint using the retained full
endpoint-rank theorem, then uses a complete-period cost bound or a forced
finite star exit. It does not rely on a local shortening claim. The
left pad can be arbitrary and the right pad can extend beyond factor `h`.
Cuts inside longer outer vertex arcs cause no problem.

No defect requiring a mathematical repair was found. The checks below
include interfaces that the supplementary algebra checker does not by
itself justify.

## 1. Core geometry and the stationary lift

The relations `s=q(h-1)` and `b=2q(h-1)/h` give `0<s<b<q`.
On a control-2 edge, `q+x` grows by the factor; on a control-1 edge,
`q-x` decreases by its reciprocal. This gives factor `h` on all four
arcs, including the reflected negative half. The formulas agree at
each cut, and `w(0)=w(-b)=w(b)=v`.

The inner positive arc has `w(x)(q^2-x^2)=(v/3)(1-x/q)/(1+x/q)`.
The outer positive arc has the increasing expression
`(v/3)r^2(1+x/q)/(1-x/q)`, with final value
`(v/3)r(2-r)<v/3`. Reflection gives the same bound on the negative
half. At zero, the strict-star inequality is exactly `v<3`.
Thus the scale interval is the full strict-star range of this core.

In the state-only clock and frame coordinate `A_frame=gK(x)`, the edge
equations are `A_frame'=A_frame w E21`, `x'=1`, and `w'=b_i w`.
The minimizing cost `(2/3)C` has running cost `1+(1+x^2)w`.
Hence the adjoint equations are

```text
m'=0,  k'=2wm,  n'=-wk,
p_w'+b_i p_w=mu-x^2,  mu=-1-m.
```

These verify the proposed group covector and the integrating-factor
formula for `p_w`. The inner weighted moment identity makes `p_w=0`
at `-s,0,s`; both state-covector components agree across the three
switches, since the control-dependent term in `p_x` contains `p_w`.

At `b`, substitution of `p_w=-q^3 j` into the control-0 gap gives
exactly `n=Q_b`. At `-b`, the signs of `x`, `k`, and `p_w` reverse,
while `w`, `m`, and `n` are unchanged. The corresponding control-0/2
gap is zero too. The adjoint extends through the two positive control-0
pads by their smooth autonomous equations; the active Hamiltonian stays
zero.

This constructs a stationary normalized adjoint, without assuming
maximality for every parameter pair. The rank-five theorem in
[LOCAL_MIXED_SIX_RANK](LOCAL_MIXED_SIX_RANK.md) applies to every positive
strict-star `021210` window, independently of pad lengths. Its actual
PMP lift is normal, and the endpoint first-variation identity uniquely
determines its normalized cotangent. Therefore the candidate is the
actual adjoint of any hypothesized PMP occurrence.

## 2. Rotation and physical multiplier normalization

Let `L_min` be the minimizing group covector in the original frame
coordinate `g`. The shear change gives

```text
M=K(-x)L_min K(x),  L_min=K(x)M K(-x).
```

The cyclic change taking old vertex 0 to new vertex 1 sends both
`X` and `L_min` to their conjugates by `R0^T` on the left and `R0`
on the right. Returning to shear coordinates at the new abscissa `a`
gives exactly

```text
M_+=K(-a) R0^T K(b) M(b) K(-b) R0 K(a).
```

This verifies the order of every factor in equation (16). Old vertex 1
becomes new vertex 2, so the old 1/0 tie is a new 2/1 tie and gives
the new `p_w(a)=0`.

Changing maximizing physical cost `C` to minimizing scaled cost `(2/3)C`
multiplies the cotangent by `-2/3`. The state-only clock is positive
and does not further rescale that cotangent on the zero-Hamiltonian
level. Therefore `Lambda_1=-(3/2)L_min`. At the core center `x=0`,
`K(x)=I`, and the claimed relation `Lambda_1=-(3/2)M(0)` is exact.
In particular

```text
det Lambda_1=(9/4)(1+mu)n_0.
```

When the Casimir certificate gives `(1+mu)n_0>99/100`, the already
proved `mu>0` implies `n_0>0`. Thus
`(Lambda_1)21=-(3/2)n_0<0`. The proof has checked the negative
elliptic component required by
[GLOBAL_COST_CASIMIR](GLOBAL_COST_CASIMIR.md), not just the determinant.

## 3. The continuation argument includes degenerate initial ties

The exact `B` function has `B'''(S)>0`, so its derivative is convex.
If `B'(0)<=0`, the nonpositive set of `B'` is an interval containing
zero. Thus `B` decreases and then increases, or is monotone, and its
maximum on the finite arc interval is at an endpoint. The endpoint
formula and `R>=16/5` make both endpoints strictly negative. Hence
`B<0` throughout the interval before star exit.

For the other gap, suppose the actual PMP arc reaches `z>0` with
`z^2>mu`. If `p_w(z)=0`, then `E=u^2 p_w` has strictly negative
derivative there and is positive immediately to the left, contrary to
maximality on the actual preceding arc. Thus `p_w(z)<0`. For every
later `x>=z`, the derivative `E'=W(mu-x^2)` stays negative.

Both inactive vertices are then strictly worse than the active one.
The full simplex Hamiltonian is a positive weighted average of its
vertex values, so no intermediate measurable control gives an untested
continuation. Smooth state/cotangent evolution forces the same vertex.
This argument neither assumes a transverse initial tie nor a positive
initial abscissa.

For this family the necessary initial derivative condition is only
`mu_+-a^2<=0`; equality is retained. The threshold algebra gives
`v>v_X`. The formula for `a` is strictly increasing in `v`, so the
point after factor `h` satisfies `z>a` and `z>-a`. Consequently
`z>|a|` and `z^2>a^2>=mu_+`. The actual positive final pad supplies
the preceding PMP arc required for the left-sign contradiction.

The remaining physical time is `sqrt(W) log(R/h)`, positive and finite
because `R>16/5` and `h<5/3`. Twisted state/cotangent closure extends
a complete lift through every seam. Such an extension cannot meet a
strict-star boundary after this forced finite continuation. The argument
also applies to a window crossing the period cut.

## 4. Sign ranges and the small-h cost obstruction

The two rational logarithm bounds are strict for `h>1`; their
derivative differences have the stated positive numerators. Every
expression receiving affine interpolation is affine in `log h`.
The elementary polynomial estimates in Section 5 prove `A,B,C>0`
and `CB+EA>0` on all of `1<h<2`. In particular, `v>=B/A` gives
`Cv+E>0`, even at equality in the initial derivative condition.

The two endpoint substitutions for `B-3A` are nonnegative/strictly
positive on `[5/3,2]`. Because the logarithm lies strictly between
its bounds, their interpolation is strictly positive even at `h=5/3`.
This excludes that upper-h region using `v<3`.

The `v_X` threshold is strict on `1<h<=5/3`. The `v_R` threshold
is strict on `[5/4,5/3]`; its denominator sign `h-22<0` is treated
correctly. These yield the required state and exit-ratio inequalities
in the remaining large-h region.

On `1<h<=5/4`, the scaled determinant is strictly concave in `v`,
with value `1+mu>1` at `v=0`. The cleared interpolation polynomial
is concave in its logarithm-interpolation parameter: on `[1,5/4]`,
`h^2-4h+2<0` and `19h^2+24h-22>0`. All 18 recorded rational
Bernstein coefficients are positive. Thus both endpoint polynomials,
and then every interpolated polynomial, are strictly positive.
Concavity in `v` yields the claimed bound for all `0<v<=v_R`.

The resulting negative elliptic determinant is strictly larger than
`891/400`, which exceeds `(313/210)^2` by exactly `211/35280`.
Conversely the complete-period cost--Casimir inequality with
`C<=A_oct<313/100` and `pi>157/50` gives
`sqrt(det Lambda_1)<313/210`. This is a contradiction on that
subregion. The remaining small-h inputs have `v>v_R` and enter the
escape argument.

No positive-elliptic or nonelliptic alternative was silently lost:
the rejected subregion is proved negative elliptic, while the escape
argument imposes no component restriction. Conservation of determinant
alone would not prove this rejection; the full-period cost inequality
is used.

## 5. Reproduction and remaining boundaries

The reviewer ran

```text
python explorations/mixed_global_symmetric_certificate.py
```

It passed all **146 exact algebra identities and rational sign checks**
with Python 3.12.14 and SymPy 1.14.0. They include the moments, state
and group-cotangent rotations, independent `B1` differentiation,
threshold substitutions, determinant normalization, logarithm
interpolation, and the displayed Bernstein table. The manual checks
above separately justify the PMP interpretation, actual-lift
identification, component test, initial-tie equality, and use of closure.

The theorem remains restricted to the stated symmetric equal-factor
core and a right pad of factor at least `h`. It does not exclude every
asymmetric M1 window or every shorter outgoing pad. It does not claim a
uniform neighborhood or include the limiting inputs `h=1`, `h=2`,
`v=0`, or `v=3`; those limits are not needed for the open-domain theorem.

**This is a uniform exclusion of the stated two-parameter family.
The universal M1/M2/M3 gates, unrestricted octagon inequality, affine
uniqueness, and kernel validation remain open.**

