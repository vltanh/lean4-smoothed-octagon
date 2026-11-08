# Complete low-t replacement and the actual Lean caller

## Conclusion and scope

The replacement proves that an actual eligible forward window cannot satisfy

\[
 \frac13\le t\le\frac38,\qquad j=2t+x-1\ge\frac1{30}.
 \tag{1}
\]

It preserves the original geometric domain. It uses the new multipliers

\[
 a=\frac72-10(q-1),\qquad
 m=8j+8(q-1)-\frac16
 \tag{2}
\]

and the residual \(G_n\) printed in
[the shape and substitution proof](NONSHORT_LOW_T_SHAPE.md).
The complete scalar theorem is

\[
 \boxed{G_n(t,x,q,k)>0}
 \tag{3}
\]

on

\[
\begin{gathered}
 h=1-2t\in[1/4,1/3],\qquad 1/30\le j\le5h/7,\qquad x=h+j,\\
 1\le q\le\frac{1+x}{1+2j},\qquad 1\le k\le1+j.
\end{gathered}
 \tag{4}
\]

The hypothetical actual window gives the opposite strict sign. The proof
below therefore replaces the actual caller's two old shape endpoint
certificates together.

This is a caller-preserving replacement for N1 and N3. It does not assert
that the old residuals with their different multipliers have acquired new
pointwise sign proofs. In particular, the existing statement of
`fh_LGA_core` takes negativity of the **old** combined residual as a
hypothesis; that hypothesis alone is not replaced silently by negativity
of the new residual. The actual caller that supplies the new hypothesis is
`fh_small_gap_j`, through the general theorem `fh_window_comb`.

## 1. Reduce the unit sign in h

Put \(y=q-1\), \(W=1+x\), \(D=17x+76\), and

\[
 S(h,j,y)=96q(q+1)W^3D\,G_n(t,x,q,1).
 \tag{5}
\]

The multiplier is positive. The
[separate derivative proof](NONSHORT_LOW_T_H_REDUCTION.md) establishes

\[
 \frac{\partial S}{\partial h}>0
 \tag{6}
\]

on the unchanged unit-shape domain in (4). That proof uses the explicitly
printed small derivative polynomials in
[the curvature note](NONSHORT_LOW_T_CURVATURE.md) and the
[initial derivative note](NONSHORT_LOW_T_INITIAL_DERIVATIVE.md).

For fixed \(j,y\), the allowed h interval starts at

\[
 h_0=\max\left\{\frac14,\ \frac{7j}{5},\ j+(1+2j)y\right\}.
 \tag{7}
\]

Every \(h'\in[h_0,h]\) still satisfies \(j\le5h'/7\) and
\(y\le(h'-j)/(1+2j)\). Thus (6) gives
\(S(h,j,y)\ge S(h_0,j,y)\). At least one of the three boundary
conditions in (7) is an equality.

All three face signs are proved:

- At \(h=1/4\), the [unit-face proof](NONSHORT_LOW_T_UNIT_FACE.md)
  gives \(S>0\), using a cubic square completion and univariate signs.
- At \(j=5h/7\), the [outer-gap face proof](NONSHORT_LOW_T_OUTER_FACE.md)
  gives \(S(h,j,0)>10\) and \(S_y>500\), hence \(S>0\).
- At \(y=(h-j)/(1+2j)\), the
  [maximum-duration proof](NONSHORT_LOW_T_QMAX.md) gives
  \(P=576(1+2j)^4W^2(W+1+2j)D\,G_n>39\).
  The multiplier is positive, so \(G_n>0\), hence \(S>0\).

Consequently the unit-shape sign is positive throughout its full domain.
The three faces are comparison boundaries of a single interval in h;
no smaller geometric domain has been assumed.

## 2. Reduce shape to the unit face

The [shape derivative proof](NONSHORT_LOW_T_SHAPE.md) gives

\[
 \partial_kG_n>0\qquad(1\le k\le1+j).
 \tag{8}
\]

The unit sign therefore implies
\(G_n(t,x,q,k)\ge G_n(t,x,q,1)>0\), proving (3).
Both old shape endpoint premises have been replaced by one unit sign and
one monotonicity theorem.

## 3. The negative necessary condition at an actual window

The original floor, incident, and transport inequalities hold at the same
actual window. On (4),

\[
 0\le y\le9/32,\qquad a\ge11/16>0,\qquad m\ge1/10>0.
 \tag{9}
\]

The existing general theorem `fh_window_comb` in
`SmoothedOctagon/Exclusion/Mixed/FwdHand/Window.lean` accepts **any**
\(\alpha>0\), \(M\ge0\). Apply it with \(\alpha=a\), \(M=m\).
It gives the strict negativity of the new combined residual before scalar
substitution. No inference from the old multipliers is needed.

The substitution proof in the shape note establishes that the new
combined residual has a negative norm coefficient and a negative logarithm
coefficient on the required domain. It uses the single bound

\[
 \log q\le\frac{(q-1)(q^2+10q+1)}{6q(q+1)}\qquad(q\ge1)
 \tag{10}
\]

and the rational incoming majorant

\[
 T_L=\frac{912-401x}{24(17x+76)},\qquad
 V_L=1-\frac{(1-t)(t+x)}{(1+x)^2}
      +\frac{(1-t)x}{(1+x)^2}(T_L-t).
 \tag{11}
\]

Its comparison with the old incoming majorant is the positive square
identity

\[
 T_L-T_G=
 \frac{5x(7x-3)^2}{24(17x+76)(x^2+10x+15)}\ge0
 \qquad(x\ge0).
 \tag{12}
\]

These substitutions give \(G_n(t,x,q,k)<0\) at the actual point.
The positive sign (3) is a contradiction, proving (1).
There is no arctangent or square-root approximation in this replacement.

## 4. Exact integration point in the existing Lean proof

The current low-t branch of `fh_small_gap_j` in
`SmoothedOctagon/Exclusion/Mixed/FwdHand/LargeGap.lean` already has:

- `1/3 <= t <= 3/8`, after the existing low-ratio theorem and branch split;
- `j >= 1/30`, from the assumed counterexample;
- `7*x < 12*(1-2*t)`, hence `j < 5*h/7`;
- `k >= 1` and `k < 2*t+x = 1+j`;
- `q > 1` and `q*(4*t+2*x-1) < 1+x`, hence the event cap in (4);
- the unchanged identity between `v` and the incoming secant norm.

Therefore its actual point satisfies every hypothesis of (3), (9), and
the new scalar-substitution argument. Replace the low-t call with the
following mathematical steps:

1. Set a,m by (2) and prove their bounds (9).
2. Apply `fh_window_comb W hF` with these a,m to obtain the new negative
   combined residual.
3. Apply the new norm/logarithm substitution argument to obtain \(G_n<0\).
4. Apply (3), obtaining the contradiction.

The conclusion of `fh_small_gap_j`, namely
\(2W.nt+W.nx-1<1/30\), is unchanged. Its high-t branch is independent of
this replacement. The new scalar core may be given a new theorem name
and the old core retained until integration is complete.

The old low-t dependencies `fhCLGa_pos_y` / `fh_LGa_link` and
`fhCLGb_pos_y` / `fh_LGb_link`, and their use of
`fh_comb_pos_of_ends`, are then unnecessary in this actual branch.
This states precisely which caller closes and why changing multipliers is
permitted. It does not claim that the literal old scalar theorem with only
its old `hcomb` premise has been proved by a different premise.

## 5. Size budget and validation boundary

All expanded identities are univariate or bivariate of total degree at
most eight. The largest printed bivariate polynomial in the replacement
is the 44-monomial positive error factor in the maximum-duration proof.
Every expanded coefficient has at most twelve digits. High-degree
products are retained; the source connections are proved by differentiated
identities and boundary jets before expansion.

The derivative proof uses four pieces with simple rational endpoints in
one variable. The maximum-duration auxiliary proof uses a single split at
4/5 for its square completion. The remaining reductions use monotonicity,
concavity, squares, and products of signed factors. All sign polynomials,
identity counts, and scalar comparison ranges are printed in the linked
proofs; the original large coefficient tables are not used.

The complete hand argument has exact rational transcription checks and
independent mathematical review of its component notes. No Lean source is
changed by this document. Lean compilation, Lake, typechecking, and CI
have not been run; this does not assert a measured runtime or memory
improvement or completion of Lean integration.
