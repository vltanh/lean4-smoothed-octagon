# Complete actual outer displacement replacement

This replaces the outer terminal sign in
[MIXED_SMALLER_SHORT_DISPLACEMENT_OUTER_FACE](../../archive/notes/MIXED_SMALLER_SHORT_DISPLACEMENT_OUTER_FACE.md),
including the two rational tests in its equation (6) and their final
caller in Section 6. It proves both tests strictly negative at every
actual outer terminal shape supplied by the displacement reduction.

## 1. Exact caller and a smaller scalar enclosure

Retain the original hypotheses `2<=x<=13/6`, `delta=b/x-1>=1/19`,
short order, rational quadratic order and selection of the outer terminal
scale `q=1/7`. With `a=alpha`, their necessary consequences are
\[
1<a\le x,\quad a^2\ge x(x+2)/6,\quad b<2a,
\]
\[
b=x+C(a-1),\qquad
\frac{8x}{9x+8}\le C\le\frac{115x}{304}<\frac{19x}{50}.
\tag{1}
\]
The first beta inequality is exactly the lower short-order bound
`b>=x(9x+8a)/(9x+8)`. It is retained here instead of replacing it by the
weaker artificial slope bound in the archived scalar enclosure.
All original actual candidates remain included.

A convenient lower shape is
\[
a_*(x)=5(x+1)/13,
\qquad \frac{x(x+2)}6-a_*^2
=\frac{19x(x+2)-150}{1014}>0.
\tag{2}
\]
Thus `a_*<=a<=x`. Notice `a_*>1`, `a_*<5/4`, and
\[
3/5<8/13\le C<5/6,\qquad
1/x\le1/a\le13/[5(x+1)]<7/8.
\tag{3}
\]
For fixed x,C we only compare the explicit rational functions along
this shape interval.

Use the exact incoming ceiling and rational logarithm majorant from
Section 2 of the archived note:
\[
U=\frac34+\frac{(x-1)^2(x+b-2)}{(b-1)(x+1)(35x+13)},
\quad\ell=319847/180000-56a/(19a+5b).
\tag{4}
\]
Their insertion at the actual terminal shape is justified by the positive
incoming coefficient in Section 3 of
[the weight reduction](../../archive/notes/MIXED_SMALLER_SHORT_DISPLACEMENT_WEIGHT_REDUCTION.md)
and by its `b<2a` logarithm range. The original incident norm is retained
until these terminal comparisons. After (4), the compared functions are
entirely rational.

Put `rho=a/(a+b)`, `T=7rho`, `k=5a-1`, and retain the transport w,E_L
from the source note, evaluated at U. Define
\[
J=(U-1)/\rho+\rho+6/7-E_L+\ell,
\]
\[
n_0=2+\frac{16-24/T}{k},\qquad n_1=T+4/k,
\quad F_i=J+n_i(w-3/4).
\tag{5}
\]
These are exactly the two rational upper tests from the source.

## 2. Enclose the duration multipliers before comparing shape

Both multipliers are at most 7/2. For n_0 the equivalent numerator is
\[
105a^2-197a+48b\ge105-197+96=4>0;
\]
the quadratic part increases for `a>=1`.
For n_1 the equivalent numerator is
\[
(35a-15)b-35a^2-a.
\tag{6}
\]
The lower beta function `x+8x(a-1)/(9x+8)` increases with x.
If `1<=a<=2`, replace x by 2 to bound (6) below by
\[
(-175a^2+497a-270)/13>0.
\]
This concave quadratic has values 52/13 and 24/13 at 1 and 2.
If `2<=a<=x`, replace x by a to bound (6) below by
\[
a(280a^2-544a-8)/(9a+8)>0;
\]
the bracket increases for a>=2 and equals 24 at 2.

For lower bounds use `b<=13(19a+31)/300`, a consequence of (1).
The equivalent numerator for n_1>=25/8 is bounded below by
\[
\frac{15625a^2-35996a+22971}{300}>0.
\tag{7}
\]
The numerator has positive leading coefficient and discriminant
`-139975484`. For n_0>=25/8 on `1<=a<=5/4`, the equivalent numerator is
\[
767a-315a^2-192b
\ge\frac{-7875a^2+15223a-6448}{25}
\ge4417/400>0.
\tag{8}
\]
The displayed quadratic decreases for a>=1.
On the full actual domain, n_0>=5/2 follows from `b<2a`:
\[
183a-35a^2-48b>a(87-35a)>0.
\tag{9}
\]
Hence
\[
\begin{array}{ll}
a\le5/4:& n_0,n_1\in[25/8,7/2],\\
a\ge5/4:& n_0,n_1\in[5/2,7/2].
\end{array}
\tag{10}
\]
No sign of the substituted quantity `w-3/4` was used.

## 3. Constant multipliers and three shape faces

For a constant n set `R_n=J+n(w-3/4)`. The
[reciprocal-shape theorem](SHORT_DISPLACEMENT_OUTER_RECIPROCAL.md) proves
\[
\partial_{(1/a)}^2R_n>1/4\qquad(5/2\le n\le7/2)
\tag{11}
\]
on the whole comparison rectangle (3), following the exact norm U.
The [terminal proof](SHORT_DISPLACEMENT_OUTER_TERMINALS.md) gives
\[
R_{25/8}(x,a_*,C)<-1/100000,\qquad
R_{7/2}(x,a_*,C)<-1/400,
\]
\[
R_{5/2}(x,5/4,C)<0,
\qquad R_n(x,x,C)<0\quad(5/2\le n\le7/2),
\tag{12}
\]
for every slope in (1).

By convexity in 1/a, the two multipliers 25/8 and 7/2 are negative
throughout `[a_*,x]`. The multiplier 5/2 is negative throughout
`[5/4,x]`. Finally R_n is affine in n. Apply the multiplier intervals
(10) to conclude
\[
\boxed{F_0<0\quad\hbox{and}\quad F_1<0}
\tag{13}
\]
at every unchanged actual outer terminal shape.

## 4. The original duration and scale caller

Equation (13) supplies both sufficient signs in equation (21) of the
weight reduction at its outer terminal scale `q=1/7`.
Its duration comparison (19)--(20) then excludes positive weighted
residuals for every `2<=tau<=T`. The zero-scale sign and tau-two scale
continuation remain the unchanged earlier inputs; the present proof
replaces their outer positive-scale terminal obligation exactly.
The separate central terminal input remains separate.

The wider artificial `g>=1/4` scalar box from the old proof is not a
premise of the caller and is not asserted here. The retained lower
short-order inequality is a necessary condition already available in
that caller. No physical root, common covector, Casimir condition,
outgoing norm floor or cost is moved to an artificial shape.

## 5. Size and verification

The only shape split for the residual signs is at a=5/4. The elementary
multiplier estimate (6) uses the further scalar distinction a<=2 or a>=2.
The proof first removes duration by affine multiplier bounds, then shape
by reciprocal convexity, then beta at each remaining face. Every sign
polynomial and every coefficient of the quartic source is printed in the
two algebra companions. The largest sign identity has 39 monomials,
degree eight in two variables. The largest printed cleared coefficient
is 503827505900. All source contributions are checked after the stated
reductions, without a combined high-degree expansion.

Exact rational symbolic calculations were used only to reconstruct and
check the displayed identities and rational arithmetic. No Lean, Lake,
typechecking, compilation or CI was run.
