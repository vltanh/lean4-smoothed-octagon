# Independent review of the conditional small-shape Casimir floor

Date: 2026-11-08 UTC. **Accepted.**

This review accepts
[MIXED_SMALLER_SHORT_SMALL_SHAPE_CASIMIR_FLOOR](MIXED_SMALLER_SHORT_SMALL_SHAPE_CASIMIR_FLOOR.md)
on its stated hypotheses
\[
2\le x\le15/7,\qquad 0\le\beta/x-1\le1/19.
\]
The conclusion is the strict lower bound
\(\Gamma_{\rm actual}>183/1000\) for the original common covector.
The two shape restrictions remain hypotheses of that theorem.

## 1. Shape bounds and the two scale comparisons

The reviewer checked the lower order coefficient, its monotonicity in
x, and its value 13/5 at x=2. The independently accepted upper order
gives alpha=1+eta*delta with 13/5<=eta<=3. The upper incoming norm
is the unchanged incoming-secant estimate; its coarse upper bound
31/40 is valid on the whole displayed rectangle.

The following estimates were checked directly:

- D>0 from alpha>=1, beta<=300/133 and x<=15/7.
- D<S from the displayed quadratic in delta, its decreasing
  dependence on x, and its value -74/361 at x=2,delta=1/19.
- q_c<=121/843<1/6.
- T=r_A/q_c>2 from alpha^2+2alpha*beta<174/25<8<=x(x+2).

The fixed-p corrected-Casimir derivative proof extends to q<=1/6
as stated. Its quantitative slope inequality is independent of q;
the new coefficient is 27/200<1/7. The comparison therefore continues
to lower a scalar bound on the original Casimir. It does not assign
the original competitive upper cap to the new point.

At tau=2, the discriminant argument proving A_2>0 remains valid for
3<=S<=22/7: its algebraic identity has no lower bound S>=17/5 as a
premise, and z=(S-2)^2/alpha^2<2 is immediate here. The reviewer
checked E_0<0<E_0+u, the formula for C_0, its upper bound five,
and the resulting strict inequality (R_2^*)'>1. The Casimir derivative
bound is
\[
(\Gamma_*)_q\le1332/13475<1/10.
\]
Thus the corrected expression has derivative strictly less than
-3/70. The two scale moves in the source theorem are consequently
valid, and the final parameter lies in [2,T].

## 2. Residual and incoming-norm comparisons

The explicit central-scale formulas for Gamma_*, w, E_L, q and T
were reconstructed from the definitions. In particular, the central
physical scale is rho=(1+x)^(-2), whereas Gamma_actual in the
conclusion remains the original covector's Casimir.

The inequality
\[
R_\tau\le\max\{R_2,R_2+(T-2)(w-3/4)\}
\]
follows by integrating R_tau'<=w-3/4 on [2,T]. Taking the maximum
is necessary when the outgoing comparison norm is below 3/4; the
source theorem handles both signs and does not transport a separate
outgoing floor to this point.

The reviewer checked the incoming-norm derivatives and bounds
\[
(R_2)_u\ge2242/693,
\]
\[
[R_2+(T-2)(w-3/4)]_u\ge1450/693,
\qquad (\Gamma_*)_u\le81/320<1450/4851.
\]
For the intermediate inequalities, D/Sigma<1/3,
S^3/Sigma>=20/7, 1/r_A>=30/11 and T<=S are valid throughout the
rectangle. The lower bound w_u>=-1 follows, for example, from
z(z-C)>=1/9-22/21=-59/63 when z=D/Sigma and C=S^3/Sigma.
The inequality E>=0 follows by evaluating its minimum at
u=3/4,S=22/7. The bound U_1<=4/5 together with S>=3 gives
the stated coarse upper bound on the Casimir derivative.

Thus both corrected expressions decrease when u is raised to the
specified rational upper value. This is a comparison of scalar
functions on a rectangle; it does not assert that the intervening
shapes satisfy the second secant equality.

## 3. Fresh reconstruction of the six polynomial signs

The review rebuilt Phi, Psi and y=2/T from the original rational
Gamma_*, w, E_L and R_2 formulas, substituted alpha=1+eta*delta,
beta=x(1+delta), and inserted the incoming rational upper bound.
It then differentiated those newly reconstructed functions, including
the logarithmic derivatives of -log(y)/7.

This reconstruction checked the following items independently of
the source calculation's saved polynomials:

- Each of the six positive clearing denominators in (15), including
  cancellation of x*delta in row two and all specializations in
  rows four through six.
- All six positive origin values, including the five values in
  (17) and 35322804569/269987074560 for row one.
- Every integer bound in the five rows of (19), using exactly the
  source's negative-coefficient, variable-weight and degree-folding
  conventions.
- The degree-sixteen positive-basis identity (20)--(21), the four
  ordinary negative contributions, all seventeen strict constant
  bounds E_i(0,0)>7/10, and every coefficient of the uniform
  negative-part bound (23).

The mathematical sign arguments following these bounds are correct:
the retained positive constant exceeds the entire negative part in
rows two through six; in row one each positive-basis coefficient is
at least 7/10-1/4>0. The basis is nonnegative and sums to one on
0<=19*delta<=1. No coefficient is discarded with an unproved sign.

The fresh exact reconstruction is an independent arithmetic audit;
the hand proof itself is the source theorem's displayed polynomial
definitions, coefficient inequalities and ensuing sign arguments.
There is no interval cover or external executable premise.

## 4. The three final endpoints

The monotonicity directions give precisely the three endpoint shapes
listed in (24)--(25). In the Psi argument the remaining delta
function is concave, so its minimum is at one of its two endpoints.
The zero eta derivative when delta=0 is handled by the polynomial
extension stated in the theorem.

The fresh reconstruction matches all three rational pairs (y,Z_0)
in (26). The odd logarithm truncation has the asserted direction
because z=(y-1)/(y+1)<0. Exact rational substitution confirms the
three strict excess bounds in (27), respectively greater than
1/20000, 1/10000 and 1/25000.

It follows that both scalar lower bounds exceed 183/1000. Chaining
them with the original corrected-envelope inequality proves the
claimed lower bound for Gamma_actual under the two stated shape
hypotheses. This review makes no claim that those hypotheses have
yet been derived from every actual short bridge.
