# Complete replacement of the S1 outer low-ratio sign

This closes row **S1.1** of the lighter-proof ledger. It replaces the
large sign identities (16)--(21) and Section 5 of
[MIXED_SMALLER_SHORT_LOW_RATIO_OUTER_HAND_SIGN](../../archive/notes/MIXED_SMALLER_SHORT_LOW_RATIO_OUTER_HAND_SIGN.md)
on its actual caller's full domain. The residuals, correction coefficient,
Casimir threshold, duration interval, and actual incoming norm are unchanged.

## 1. The precise conclusion

Use the original notation
\[
1<x\le2,\qquad 1\le a<x,\qquad 6a^2\ge x(x+2),
\]
\[
\beta=x+C(a-1),\qquad
\frac{8x}{9x+8}\le C\le\frac{x(7x+1)}{4x^2+11x+1},
\qquad q=\frac17.
\]
Let \(u\) be the original exact incoming secant norm. The rational tests
\(F_0,F_1\), the transported quantities \(\Gamma_*,w,E_L\), and the
single logarithm majorant are exactly those in
[the source note](SHORT_OUTER_BETA.md), equations (1)--(2).
In particular,
\[
c=\frac7{96},\quad g=\frac{9193}{50000},\quad T=\frac{7a}{a+\beta},
\quad
\ell(y)=2\frac{y-1}{y+1}+\frac23\left(\frac{y-1}{y+1}\right)^3.
\]
The completed conclusion is
\[
\boxed{F_0(x,a,\beta,u)>0,\qquad F_1(x,a,\beta,u)>0.}
\tag{1}
\]
All comparisons below concern these explicit scalar functions. No root,
physical competitive cap, or original incoming norm is transported to a
comparison geometry.

## 2. The three branches exhaust the actual domain

For \(1<x\le3/2\), the [S-branch proof](SHORT_OUTER_S_TERMINAL.md)
gives both tests the lower bound \(499/884000\). It includes the unchanged
norm interval \(u_f\le u\le u_v\) and beta-slope interval of the original
S row.

For \(3/2\le x\le2\) and \(6/5\le a<x\), the
[A-branch proof](SHORT_OUTER_LARGE_SHAPE_REDUCTION.md) gives both tests
strictly positive. Its reciprocal-shape endpoints are the shared face
\(a=6/5\) and the face \(a=x\); it preserves the original A-row domain.
The endpoint margins are respectively \(1/2000\), \(3/500\) for the
\(F_0\) upper-shape endpoint, and \(1/15000\) for the four affine-norm
\(F_1\) curves.

It remains exactly the actual B branch
\[
3/2\le x\le2,\qquad1\le a\le6/5,\qquad6a^2\ge x(x+2),
\qquad u_f\le u\le u_\ell.
\tag{2}
\]
The [completed B \(F_0\) proof](SHORT_OUTER_LOW_SHAPE_TERMINAL.md)
already gives \(F_0>0\), with a certified terminal margin
\(167/144000000\). Its actual shape and incoming-norm hypotheses are
exactly those in (2).

For the remaining \(F_1\) test, the
[reciprocal-shape reduction](SHORT_OUTER_RECIPROCAL_LOW_SHAPE.md)
first encloses \(u\) in \([3/4,19/25]\), uses beta and norm concavity,
and reduces to the four constant pairs
\[
(C,u)\in\{1/2,10/13\}\times\{3/4,19/25\}.
\]
Its independently proved reciprocal-shape curvature is strictly less than
\(-11/800\). It therefore reduces \(F_1\) to the two shape endpoints
\(a=6/5\) and
\[
a_*(x)=
\begin{cases}
1,&3/2\le x\le5/3,\\
(6x+3)/13,&5/3\le x\le2.
\end{cases}
\]
The shared [\(a=6/5\) terminal](SHORT_OUTER_UPPER_SHAPE_TERMINAL.md)
is greater than \(1/2000\). The new
[lower-shape terminal](SHORT_OUTER_LOW_SHAPE_F1_TERMINAL.md) gives
\[
F_1(x,a_*(x),x+C(a_*(x)-1),u)
\ge\frac{1597}{144000000}>0.
\tag{3}
\]
Its [source companion](SHORT_OUTER_LOW_SHAPE_F1_SOURCE.md) prints every
polynomial and verifies the derivative source by its three principal parts,
so a degree-nine common numerator is never an expanded premise.
This completes both B tests and hence proves (1) on the complete actual
outer domain.

The B proof deliberately uses the actual condition \(a\ge1\) and actual
outer-cap condition. The old generated B box included extra points failing
these conditions. Their signs are unnecessary: the exact caller below
supplies both conditions at every actual point, including its boundaries.

## 3. The original duration and actual-period callers close

The unchanged original duration comparison is
\[
R_\tau\le
\max\{R_2,R_2+(T-2)(w-3/4)\}
\qquad(2\le\tau\le T).
\]
The fixed bound \(\log(2/T)\le\ell(2/T)\), followed by (1), gives
\[
\boxed{\Gamma_*-\frac7{96}R_\tau>\frac{9193}{50000}}
\qquad(2\le\tau\le T).
\tag{4}
\]
This is precisely the original outer-face conclusion.

The exact actual-period caller is Section 3 of
[MIXED_SMALLER_SHORT_LOWER_RATIO_HAND_EXCLUSION](../../archive/notes/MIXED_SMALLER_SHORT_LOWER_RATIO_HAND_EXCLUSION.md).
On its outer alternative \(q=1/7\le q_c\), the latter inequality is
exactly \(6a^2\ge x(x+2)\). Its equations (1)--(2) supply the actual
orders, equal secants, and beta bounds; its terminal duration belongs to
\([2,T]\). It may therefore invoke (4) unchanged. Together with its
unchanged lower comparison from the actual Casimir, this contradicts the
original competitive cap. The other, central alternative is a separate
S1.2 obligation and is not claimed here.

## 4. Identity budget and verification

The last B \(F_1\) step uses only univariate expanded identities of degree
at most eight and at most nine monomials. Its four curvature identities have
degree seven. The four derivative-source circuits are checked by degree-eight
numerators and scalar principal parts before any common denominator is taken.
The largest cleared scalar numerator there is \(192108297503\); the
largest terminal grid multiplication is \(964445^2=930154158025\).
Both have twelve digits.

Reconstruction from the original transport formulas checks the source circuits,
all pole jets, four curvature identities, shifted sign polynomials, derivative
upper bounds, and directed endpoint enclosures. Every polynomial used by the
hand proof is printed in the linked notes. Exact symbolic arithmetic is a
transcription check; neither sampling nor the old coefficient tables is a
premise. No Lean compilation, typechecking, Lake, or CI is used or claimed.
