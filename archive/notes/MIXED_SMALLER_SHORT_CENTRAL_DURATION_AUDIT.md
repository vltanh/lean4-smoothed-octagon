# Independent review of the central duration faces

Date: 2026-11-08 UTC.

This review accepts the scalar theorem in
[MIXED_SMALLER_SHORT_CENTRAL_DURATION_FACES](MIXED_SMALLER_SHORT_CENTRAL_DURATION_FACES.md):
the full-duration and eight-ninths-duration floor-weighted comparison
expressions are strictly negative throughout its stated central-scale
shape domain. The review does not treat that scalar theorem as a proof
of the remaining physical completion-cost inequality.

The original rational expression was reconstructed independently from
q=alpha^2/K, lambda=S^2/K, d=D/K, the transported norm w and transported
diagonal E_L. This reconstruction preceded comparison with the note's
generating polynomial and coefficient table. No cached endpoint
polynomial from the derivation was used as a mathematical premise.

## 1. Original expression, scope, and normalization

The incoming comparison norm is exactly

\[
u=\frac34+\frac{2(x-1)^2}{S(35x+13)}
                  \frac{x-1+(\beta-x)/8}{\beta-1}.
\]

Substituting it into the original floor-weighted expression gives the
same two rational functions as equation (4) of the reviewed note.
Their reduced denominators are respectively

\[
8\alpha(\alpha+\beta)(\beta-1)S(35x+13)K^2,
\]

and nine times this denominator. Both are positive on the stated
domain. Thus the note's common normalization

\[
N_c=-2\alpha(\alpha+\beta)VK^2G_c,
\qquad V=4S(35x+13)(\beta-1),
\]

is the negative reduced numerator for c=1, and the negative reduced
numerator divided by nine for c=8/9. In particular, no factor of nine
is missing in the second face's coefficient table.

The logarithm is zero on the first face. The value -1/9 is a legitimate
upper bound for log(8/9) on the second. The scalar sign admits cT<2;
this causes no scope problem because the theorem does not identify
such a comparison point with an actual reverse arc.

The linear alpha ceiling is strictly smaller than x for x>=12/5, so
h=x-alpha>0 throughout. All partial fractions and derivatives below
therefore have the stated nondegenerate domain. The extension of the
endpoint coefficient argument to X>=0 does not extend the separate
convexity estimate beyond x<=9.

## 2. The beta-convexity proof is valid

The decomposition

\[
u=u_\infty+\frac J{\beta-1},\quad
u_\infty=\frac34+\frac{v_0}{8},\quad
J=\frac78(x-1)v_0
\]

was checked directly. The polynomial part of G_c has degree two in
beta with leading coefficient 2h^2u_infinity/K^2. Its only remaining
poles are beta=1 and beta=-alpha, as stated.

At beta=-alpha the algebraic continued diagonal is
M/K, where M=S^2-h^2>0 and M<S^3. The u coefficient of the continued
norm is consequently negative. The continued value u_N is at most
3/4 because 7(x-1)>=alpha+1. Hence replacing u_N by 3/4 gives a
lower bound for w_N, with the correct direction.

The full positive identity in equation (8) was reconstructed from this
continued norm and verified term by term. Every term on its right is
nonnegative for alpha>=1,h>0, and the term linear in h is strictly
positive. It follows that w_N-1>-q and that the pole residue satisfies

\[
P_+>\alpha(1-c)\ge0.
\]

This use of an algebraic evaluation at negative beta is confined to a
partial-fraction identity; no geometric interpretation is attached to
that evaluation.

The beta=1 residue identity (10) and its difference formula for general
0<c<=1 were independently reconstructed from the original coefficient
of u. The coefficient at c=1 is strictly negative. Thus the subsequent
replacement of beta-1 by x-1 in its negative contribution has the
correct direction. The estimate S/(35x+13)<=1/28 is valid on the whole
domain. Discarding the positive fourth-power term yields precisely the
lower bound in equation (11).

Both estimates in equation (12) were checked separately. The function
K/[alpha(x-alpha)] is convex in alpha, so its two alpha endpoints
suffice. Their displayed values are correct; their x endpoint bounds
give 25/2. The second ratio increases with alpha, and its value at
alpha=5x/9 is convex in x. Its displayed endpoint values give 45/2.
Together these estimates give exactly

\[
\frac32-\frac1{16}\frac{25}{2}
            -\frac1{32}\frac{45}{2}=\frac1{64}.
\]

Consequently half the beta second derivative is at least
h^2/(64K^2)>0. The reduction to the two beta endpoints is justified.

## 3. The generating polynomial and all finite bounds match

The factored definitions of U,V,E_N,W,Z in equation (15) reproduce
the independently reconstructed u,w,E_L. Direct multiplication of the
original G_c gives every term and sign in equation (16), hence the
normalization identity (17).

After substituting the two beta endpoints and multiplying by R^4,
the parameterization x=(12+X)/5, alpha=1+(X+4)A/12 gives the following
degrees:

| Duration factor | Beta endpoint | Degree in X | Degree in A |
|---|---|---:|---:|
| 1 | x | 18 | 6 |
| 1 | strong-order upper endpoint | 18 | 7 |
| 8/9 | x | 18 | 6 |
| 8/9 | strong-order upper endpoint | 18 | 7 |

Thus the common degree bounds and the coefficient extraction identity
in equations (19)--(21) are correct. The constant coefficient in A is
independent of the beta endpoint, as required.

Both factorizations in equation (22), including the factor 1/9 in the
eight-ninths case, agree with the original rational expression.
Every coefficient in the shifted Q_1 and Q_8 polynomials (23)--(24)
agrees. Their other factors have positive coefficients, so all 19
constants C_i^c are strictly positive.

All bounds in the 19-row table (26) were independently reconstructed
as exact rational comparisons. This includes all three pairs entering
each M row and every specified N row. The two exceptional N rows were
checked by their stated quadratic replacements: both inequalities for
lambda_i and both inequalities for mu_i in (27) hold with slack.
No omitted high-degree coefficient is needed beyond the complete
negative-part sums defined in that note.

Finally, the two completed-square identities (29)--(30) are exact.
Every other row has negative coefficient norm strictly less than its
positive constant. The estimates A^j<=1 and A^j<=A^2 therefore prove
strict positivity of every coefficient polynomial in X on 0<=A<=1.
In particular the strict signs persist at X=0 and at both alpha
endpoints.

## 4. Accepted conclusion and remaining interface

Undoing the positive factors proves G_1<0 and G_{8/9}<0 at both beta
endpoints. The verified strict convexity proves the two signs on the
whole beta interval. The theorem is accepted as written.

Application to an actual bridge still uses the incoming upper-norm
comparison, the root/floor envelope, the scale endpoint alternatives,
and the separate tau-two and outer-scale signs. None of the algebra in
this note asserts that an artificial endpoint has an actual normal
trajectory or a separately transported Casimir cap. No Lean, Lake,
typechecking, or CI was used in this review.
