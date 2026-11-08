# A fourth-derivative bridge for the complete low-ratio sign

Date: 2026-11-08.

This completes the rational sign (10) of
[MIXED_NONSHORT_LOW_RATIO_HAND_EXCLUSION](../../archive/notes/MIXED_NONSHORT_LOW_RATIO_HAND_EXCLUSION.md)
with the three companion replacements:

- [The base quadratic](NONSHORT_LOW_RATIO.md).
- [Monotonicity in \(h\)](NONSHORT_LOW_RATIO_MONOTONICITY.md).
- [The factored higher coefficients](NONSHORT_LOW_RATIO_REMAINDER.md).

The former unresolved collection link is replaced here by four boundary
calculations and a fourth derivative in the gap \(j\). No expansion of the
full three-variable polynomial is required. All identities that need
polynomial expansion have at most two free variables and total degree at
most eight; the largest such identity has 41 monomials.

## 1. Exact conclusion and domain

Write
\[
\frac13\le h\le\frac12,\quad w=1+h,\quad
j\ge0,\quad0\le y\le h,\quad
 t=\frac{1-h}{2},\quad x=h+j,\quad q=1+y.
\tag{1}
\]
In the original domain (9), \(0\le j\le h\) and \(y=hz\) with
\(0\le z\le1\); thus (1) includes that entire domain.
Let \(\widehat G\) be the same unit-shape rational residual as in the
original note, with exactly its incoming majorant, logarithm majorant, and
multiplier. We prove
\[
\boxed{\widehat G(t,x,q,1)>0.}
\tag{2}
\]
The proof is purely rational. It introduces no replacement bound for a
transcendental function and changes none of the original scalar substitutions.

For fixed \(h,y\), we study the polynomial \(\Pi(h,j,y)\) defined in
Section 2. Its normalization is exactly
\[
\Pi(h,j,y)=192q(q+1)(1+x)^3(x^2+10x+15)\,
              \widehat G(t,x,q,1).
\tag{3}
\]
All factors on the right other than \(\widehat G\) are positive on (1).
In fact we obtain the quantitative bound
\[
\boxed{\Pi(h,j,y)>4h^3w^3+700j^3+3900j^4.}
\tag{4}
\]

## 2. A polynomial circuit for the original residual

Here \(t,x,q\) may first be treated as independent variables. Put
\[
\begin{gathered}
c=1-t,\quad p=t+x,\quad W=1+x,\quad R=x^2+10x+15,\\
Y=x(x+2),\quad J=t+Y,\quad B=1+2tx+x^2,\\
h_0=-1+3t^2-t^3,\qquad
m_0=t(1-t+t^2)+h_0Y,\\
E=q^2B+W^2-2pqW,\qquad
A=4q(7W^2-Jq^2),\qquad D=qJ-pW.
\end{gathered}
\tag{5}
\]
The following displayed polynomial is the numerator of the original incoming
majorant \(V\):
\[
\begin{aligned}
\mathscr D={}&12t^2x^3+132t^2x^2+300t^2x+180t^2
 +19tx^3-12tx^2-210tx-180t\\
 &+12x^4+113x^3+312x^2+390x+180,
\qquad V=\frac{\mathscr D}{12RW^2}.
\end{aligned}
\tag{6}
\]
It has 13 monomials and total degree five in \((t,x)\).
The incoming-floor numerator is the following quadratic in \(q\):
\[
\begin{aligned}
\Phi={}&W(-t+5x+6)
 +2(3t^2+tx-5t+x^2+x+3)q\\
 &+(t+x)(6t+5x-1)q^2,
\qquad F_\ell=\frac{\Phi}{6(q+1)W^2}.
\end{aligned}
\tag{7}
\]
Its three coefficient polynomials have respectively 5, 6, 5 monomials and
degree two in \((t,x)\). Define the polynomial
\[
\mathcal V=(q+1)\{4+3(q+2t+x-1)\}\mathscr D
            -6R(q+2t+x-1)\Phi.
\tag{8}
\]
The original effective norm is exactly
\[
\widehat v=V+\frac34(q+2t+x-1)(V-F_\ell)
 =\frac{\mathcal V}{48(q+1)RW^2}.
\tag{9}
\]
Each coefficient of \(\mathcal V\) in \(q\) is a polynomial in \((t,x)\)
of degree at most six and at most 20 monomials. Equations (6)–(8) print all
its factors; (9) follows by scalar fraction arithmetic.

Separate the residual's affine dependence on \(\widehat v\) and \(L\):
\[
\begin{aligned}
N_0={}&tBqWc+tq^2B^2-tBqp^2-tp^2W^2+tqWp^3-q^2m_0+qWph_0,\\
N_v={}&-xq\{c(1+2tW)+(x+2)(1+tY)(q-1)\},\\
N_L={}&-tBqWp,\\
\Theta_0={}&3tE^2+4q^2W^2h_0-4q^4m_0,\\
\Theta_v={}&4(W^2-q^2Y)\{q^2-t(W^2-q^2Y)\},\\
\mathcal T={}&A N_0+D \Theta_0.
\end{aligned}
\tag{10}
\]
Thus the original \(N\) is \(N_0+N_v\widehat v+N_LL\), and the second
brace in original equation (24) is \(\Theta_0+\Theta_v\widehat v\).
Every coefficient check here is in \((t,x)\), after collecting powers of
\(q\); its degree is at most seven. In particular the six coefficient
polynomials of \(\mathcal T\), in increasing powers of \(q\), have
12, 17, 26, 26, 22, 15 monomials, all of degree seven. Formula (10) prints
those polynomials as small products, rather than expanding their factors.

The only cancellation needed before clearing the effective-norm denominator
is the following explicitly specified polynomial identity:
\[
A N_v+D \Theta_v=4W\mathcal U,
\tag{11}
\]
where
\[
\begin{aligned}
\mathcal U={}&t \left(t + x\right) \left(x + 1\right)^{4}\\
&+\bigl(- t \left(x + 1\right)^{3} \left(t + x^{2} + 2 x\right)\bigr)q\\
&+\bigl(\left(x + 1\right)^{2} \left(- 2 t^{2} x^{2} + 10 t^{2} x + 5 t x^{3} + 17 t x^{2} - 7 t x - t + 6 x\right)\bigr)q^{2}\\
&+\bigl(- \left(x + 1\right) \left(- 2 t^{2} x^{2} - 4 t^{2} x + 5 t x^{4} + 20 t x^{3} + 20 t x^{2} - t + 6 x^{2} + 12 x\right)\bigr)q^{3}\\
&+\bigl(t x \left(t - 1\right) \left(- 2 t + x^{3} + x^{2} - 3 x - 1\right)\bigr)q^{4} .
\end{aligned}
\]

In (11), comparison of the coefficients of \(q\) gives identities in
\((t,x)\) of degree at most seven. The coefficient of \(q^5\) cancels
between the two displayed products; the remaining coefficients of
\(\mathcal U\) have 10, 9, 13, 12, 9 monomials and degree six.
No identity in three free variables is expanded.

Finally set
\[
Z(q)=q(q-1)(q^2+10q+1),
\quad
\mathcal K=-32tBpW^2R\,Z(q)(7W^2-Jq^2),
\tag{12}
\]
\[
\boxed{\mathcal P(t,x,q)=48(q+1)WR\,\mathcal T+4\mathcal U\mathcal V+\mathcal K.}
\tag{13}
\]
Define \(\Pi(h,j,y)=\mathcal P((1-h)/2,h+j,1+y)\).
To check (3), substitute (9) and
\(L=(q-1)(q^2+10q+1)/(6q(q+1))\) into the original equation (24),
use the two affine decompositions (10), and then (11). Its three terms
become exactly the three terms of (13): the \(48(q+1)WR\) factor cancels
the denominator in (9) against the explicit \(4W\), and the denominator
of \(L\) cancels directly in \(A N_LL\). This derives (3) by field
arithmetic with factored expressions. It does not expand (13).

## 3. Four boundary calculations in \(j\)

Put \(r_0=h^2+10h+15\), \(r_1=2h+10\),
\(d_1=r_0+wr_1\), and \(d_2=w+r_1\).
The polynomials \(T_i,U_i,V_i,K_i\) printed in Appendix A give these
finite congruences after \(t=(1-h)/2\), \(x=h+j\):
\[
\begin{aligned}
\mathcal T&\equiv w^3T_0+w^2T_1j+wT_2j^2+wT_3j^3,\\
\mathcal U&\equiv w^2U_0+wU_1j+wU_2j^2+U_3j^3,\\
\mathcal V&\equiv wV_0+wV_1j+V_2j^2+V_3j^3,\\
\mathcal K&\equiv Z(q)\{w^5K_0+w^4K_1j+w^3K_2j^2+w^2K_3j^3\}
                 \pmod{j^4}.
\end{aligned}
\tag{14}
\]
A congruence here asserts only the four displayed coefficients; it is
not an instruction to expand a whole multivariate polynomial. For the
first three lines, check one coefficient of \(q\) and one coefficient
of \(j\) at a time. The resulting identities are univariate in \(h\),
with degree at most seven and at most eight monomials. Appendix A gives
a separate factor-preserving check for the fourth line.

The ordinary product rule for finite polynomials, together with
\(WR=wr_0+d_1j+d_2j^2+j^3\), now gives
\[
\Pi(h,j,y)=w^3F_0+w^2F_1j+w^2F_2j^2+wF_3j^3+O(j^4),
\quad q=1+y,
\tag{15}
\]
where the following are fully specified sums of small products:
\[
\begin{aligned}
F_0={}&48(q+1)wr_0T_0+4U_0V_0+Zw^2K_0,\\
F_1={}&48(q+1)w(r_0T_1+d_1T_0)+4(wU_0V_1+U_1V_0)+Zw^2K_1,\\
F_2={}&48(q+1)(r_0T_2+d_1T_1+wd_2T_0)\\
 &+4(U_0V_2+U_1V_1+U_2V_0)+ZwK_2,\\
F_3={}&48(q+1)(wr_0T_3+d_1T_2+wd_2T_1+w^2T_0)\\
 &+4(wU_0V_3+U_1V_2+wU_2V_1+U_3V_0)+ZwK_3.
\end{aligned}
\tag{16}
\]
Here \(O(j^4)\) means a polynomial divisible by \(j^4\), so (15) gives
exactly the values of the first four derivatives at zero.

### Isolate the only degree-nine coefficient before expanding

Every coefficient in \(q\) of \(F_0,F_2,F_3\) has degree at most eight
in \(h\). Only the product \(wU_0V_1\) in \(F_1\) can have degree nine.
Write
\[
a(q)=\frac{(q-1)(q^3+11q^2-q+1)}4,\qquad b(q)=9(q+1),
\quad U_0=ah^4+\bar U,\quad V_1=bh^4+\bar V.
\tag{17}
\]
The complete lower-degree polynomials are
\[
\begin{aligned}
4\bar U={}&- 2 h^{3} + 2 h + 1\\
&+\bigl(3 h^{3} - h^{2} - 3 h - 1\bigr)q\\
&+\bigl(- 2 \left(5 h^{3} - 13 h^{2} - 11 h + 1\right)\bigr)q^{2}\\
&+\bigl(2 \left(11 h^{3} - 11 h^{2} - 24 h + 1\right)\bigr)q^{3}\\
&+\bigl(- h \left(h^{2} + 2 h - 2\right)\bigr)q^{4} .
\end{aligned}
\]
\[
\begin{aligned}
2\bar V={}&3 \left(55 h^{3} + 142 h^{2} + 628 h + 900\right)\\
&+\bigl(15 \left(17 h^{3} + 61 h^{2} + 158 h + 190\right)\bigr)q\\
&+\bigl(3 \left(14 h^{3} + 41 h^{2} + 206 h + 380\right)\bigr)q^{2}\\
&+\bigl(- 6 \left(13 h^{2} + 114 h + 155\right)\bigr)q^{3} .
\end{aligned}
\]

Both have degree at most three in \(h\). Distributing two factors gives
\[
wU_0V_1=ab h^9+ab h^8+wh^4(a\bar V+b\bar U)+w\bar U\bar V.
\tag{18}
\]
This keeps \(h^9\) as one monomial: the power identity
\((h+1)h^8=h^9+h^8\) follows directly from distributivity and the
power recursion. Define
\[
\begin{aligned}
F_1^{\rm lo}={}&48(q+1)w(r_0T_1+d_1T_0)+Zw^2K_1\\
 &+4\{ab h^8+wh^4(a\bar V+b\bar U)+w\bar U\bar V+U_1V_0\}.
\end{aligned}
\tag{19}
\]
All coefficients in \(q\) of (19) now have degree at most eight in \(h\).
The separated coefficient has the small exact factorization
\[
4a(1+y)b(1+y)=9y(y+2)(y^3+14y^2+24y+12)=:L_9(y).
\tag{20}
\]
This identity has five monomials, degree five, one variable, and
coefficients at most 540. Thus \(F_1(h,1+y)=F_1^{\rm lo}(h,1+y)+h^9L_9(y)\).

### The explicit face identities

Use the \(B_{in}(h)\) fully printed in Appendix A of
[the monotonicity note](NONSHORT_LOW_RATIO_MONOTONICITY.md), and the
\(P_{in}(h)\) fully printed in
[the remainder note](NONSHORT_LOW_RATIO_REMAINDER.md). Define
\[
\begin{aligned}
2H_0={}&h^3B_{00}+h^2yB_{01}+hy^2B_{02}+y^3B_{03}
 +y^4B_{04}+y^5B_{05}+y^6B_{06}+hy^7B_{07},\\
2H_1^{\rm lo}={}&h^2B_{10}+hy\bar B_{11}+y^2B_{12}+y^3B_{13}
 +y^4B_{14}+y^5B_{15}+y^6B_{16}+y^7B_{17},\\
2H_2={}&hB_{20}+yB_{21}+y^2B_{22}+y^3B_{23}
 +y^4B_{24}+y^5B_{25}+y^6B_{26}+y^7B_{27},\\
H_3={}&2wP_{30}+yP_{31}+\tfrac12y^2P_{32}+\tfrac12y^3P_{33}
 +y^4P_{34}+\tfrac12y^5P_{35}+\tfrac12y^6P_{36}
 +3(1-h)y^7P_{37},
\end{aligned}
\tag{21}
\]
where the stripped block is printed explicitly:
\[
\bar B_{11}=3000+1950h-45830h^2+58853h^3+296430h^4
 +276717h^5+95736h^6+12852h^7.
\tag{22}
\]
It has eight monomials and degree seven. The four boundary identities are
\[
\boxed{
F_0(h,1+y)=H_0(h,y),\quad
F_1^{\rm lo}(h,1+y)=H_1^{\rm lo}(h,y),\quad
F_2(h,1+y)=H_2(h,y),\quad F_3(h,1+y)=H_3(h,y).
}
\tag{23}
\]
They are checked by comparing coefficients of \(q\), with \(y=q-1\).
Each individual identity is now univariate in \(h\), of degree at most
eight and at most nine monomials. Every factor on both sides is printed
in this note or one of the two linked companion notes. The binomial shift
\((q-1)^n\) has \(n+1\le8\) terms and degree at most seven.

By the factored definitions of \(\mathcal A_i\) in the monotonicity note,
putting \(z=y/h\) in (21) gives
\[
H_0=h^3\mathcal A_0(h,z),\qquad
H_1^{\rm lo}+h^9L_9=h^2\mathcal A_1(h,z),\qquad
H_2=h\mathcal A_2(h,z).
\tag{24}
\]
These follow by canceling the displayed powers of \(h>0\) term by term;
no expansion is needed. Also \(wH_3=\widetilde C_3(h,y)>700\), by the
remainder note. Consequently (15) gives exactly the three original
quadratic coefficients and a positive cubic coefficient:
\[
\begin{aligned}
\Pi(h,0,y)&=h^3w^3\mathcal A_0(h,z),\\
\partial_j\Pi(h,0,y)&=h^2w^2\mathcal A_1(h,z),\\
\tfrac12\partial_j^2\Pi(h,0,y)&=hw^2\mathcal A_2(h,z),\\
\tfrac16\partial_j^3\Pi(h,0,y)&=wH_3>700.
\end{aligned}
\tag{25}
\]

## 4. One fourth derivative, with eight small identities

For \(n=0,\ldots,7\), the following polynomials \(Q_n(h,j)\) are printed
as products of the explicit univariate factors from the remainder note:
\[
\begin{aligned}
Q_0={}&w^2\{P_{40}+15jP_{50}+180j^2P_{60}+1260(1-h)j^3P_{70}\},\\
Q_1={}&\tfrac12wP_{41}+\tfrac{15}{2}wjP_{51}+90wj^2P_{61}
 +105wj^3P_{71}\\
 &+1680w(1-h)j^4P_{81}+4536w(1-h)j^5P_{91},\\
Q_2={}&\tfrac12wP_{42}+\tfrac52jP_{52}+15j^2P_{62}
 +\tfrac{35}{2}j^3P_{72}+280j^4P_{82}\\
 &+756(1-h)j^5P_{92}+90720(1-h)j^6,\\
Q_3={}&\tfrac12wP_{43}+\tfrac52jP_{53}+\tfrac{15}{2}j^2P_{63}
 +140j^3P_{73}+140j^4P_{83}\\
 &+3024(1-h)j^5P_{93}+226800(1-h)j^6,\\
Q_4={}&wP_{44}+5jP_{54}+15j^2P_{64}+35j^3P_{74}+70j^4P_{84}\\
 &+126(1-h)j^5P_{94}+201600(1-h)j^6,\\
Q_5={}&\tfrac12wP_{45}+\tfrac{15}{2}jP_{55}+\tfrac{15}{2}j^2P_{65}
 +\tfrac{35}{2}j^3P_{75}+105j^4P_{85}\\
 &+756(1-h)j^5P_{95}+63000(1-h)j^6,\\
Q_6={}&\tfrac12wP_{46}+\tfrac{15}{2}jP_{56}+\tfrac{15}{2}j^2P_{66}
 +\tfrac{35}{2}j^3P_{76}\\
 &+70(1-h)j^4P_{86}+252(1-h)j^5P_{96},\\
Q_7={}&3w(1-h)\{P_{47}+5jP_{57}+15j^2P_{67}+35j^3P_{77}+700j^4\}.
\end{aligned}
\tag{26}
\]
There are eight exact coefficient identities:
\[
\boxed{\frac1{24}\partial_j^4\Pi(h,j,y)=\sum_{n=0}^7Q_n(h,j)y^n.}
\tag{27}
\]
**Check (27) in this order.** Keep the \(q\)-polynomials in (13) factored,
apply the product rule four times with respect to \(x\) at fixed \(t,q\),
and only then collect coefficients of \(q\). Substitute
\(t=(1-h)/2,x=h+j\), and change \(q\) to \(1+y\) by the degree-seven
binomial identity. Each coefficient comparison with (26) is a polynomial
identity in just \((h,j)\) of degree at most eight. The degree bound follows
already from (13): every \(q\)-coefficient there has total degree at most
12 in \((t,x)\), and four differentiations reduce it by four before any
expansion. This order avoids the disallowed degree-12 row expansion.

The exact expansion sizes of the eight identities, with denominators cleared,
are:

| Identity | Monomials | Total degree in \((h,j)\) | Common denominator before clearing | Largest absolute coefficient after clearing |
| --- | ---: | ---: | ---: | ---: |
| \(Q_0\) | 26 | 7 | 1 | 67140 |
| \(Q_1\) | 39 | 8 | 2 | 3545640 |
| \(Q_2\) | 41 | 8 | 2 | 15828900 |
| \(Q_3\) | 41 | 8 | 2 | 38233365 |
| \(Q_4\) | 41 | 8 | 1 | 21294300 |
| \(Q_5\) | 40 | 8 | 2 | 20447265 |
| \(Q_6\) | 33 | 7 | 2 | 3317295 |
| \(Q_7\) | 24 | 6 | 1 | 31815 |

This is a size audit, not a coefficient table: the polynomials themselves
are completely printed in (26), with every \(P_{in}\) printed in the
companion remainder note.

The factor signs prove (27)'s right side positive without expanding it.
For \(j\ge0\), all terms of \(Q_0,\ldots,Q_6\) are positive or
nonnegative, and \(Q_0>4000\). Also
\[
Q_7>-600(1-h^2)\ge-600,
\]
using \(P_{47}>-200\) and the positivity of its remaining factors.
Thus, for \(0\le y\le h\le1/2\),
\[
\frac1{24}\partial_j^4\Pi
>4000-600y^7\ge4000-\frac{600}{128}>3900.
\tag{28}
\]
This is a separate fourth-derivative sign claim. It uses eight bivariate
identities of degree at most eight, followed by the univariate factor signs
already proved in the remainder note.

## 5. Taylor's theorem closes the original sign

Fix \(h,y\) satisfying (1), and put \(z=y/h\in[0,1]\) and
\(\beta=j/(hw)\ge0\). From (25), the quadratic Taylor polynomial is
\[
\begin{aligned}
&\Pi(h,0,y)+j\partial_j\Pi(h,0,y)+\tfrac12j^2\partial_j^2\Pi(h,0,y)\\
&\qquad=h^3w^3\{
\mathcal A_0(h,z)+\beta\mathcal A_1(h,z)+w\beta^2\mathcal A_2(h,z)\}
>4h^3w^3.
\end{aligned}
\tag{29}
\]
The final inequality is precisely the monotonicity result (18) of its
companion note and the strengthened base-quadratic result (1) of the
base note. The positivity of \(a_2\) there justifies replacing
\(w\ge4/3\) by \(4/3\).

Taylor's theorem with integral remainder gives
\[
\begin{aligned}
\Pi(h,j,y)={}&\Pi(h,0,y)+j\partial_j\Pi(h,0,y)
 +\tfrac12j^2\partial_j^2\Pi(h,0,y)\\
 &+\tfrac16j^3\partial_j^3\Pi(h,0,y)
 +\frac16\int_0^j(j-s)^3\partial_j^4\Pi(h,s,y)\,ds.
\end{aligned}
\tag{30}
\]
The cubic coefficient exceeds 700 by (25). The integrand's fourth
derivative exceeds \(24\cdot3900\) everywhere by (28), since the argument
proved that sign for every \(s\ge0\). Therefore the integral contribution
is at least \(3900j^4\), and (29) makes the full sum strictly exceed the
right side of (4). The case \(j=0\) is included by (29).

Equation (3) now proves (2) on the entire original domain. The actual-boundary
caller had forced \(\widehat G(t,x,q,1)<0\) after its already established
shape reduction. The contradiction still gives \(t>1/3\), with no change
in the original boundary hypotheses, actual incoming floor, or transported
norm comparison.

The current Lean caller uses two shape endpoints. In
[`LowRatio.lean`](../../SmoothedOctagon/Exclusion/Mixed/FwdHand/LowRatio.lean),
`fh_lowRatio_core` obtains its unit-shape hypothesis `hA` from
`fhCLRa_pos_y` and `fh_LRa_link`. The exact normalization is
\[
\texttt{fhComb}\ 6\ 0\ t\ x\ 1\ q\ \widehat v\ L\ 0
 =4qW^2\widehat G(t,x,q,1),
\qquad
\Pi=48(q+1)WR\,\texttt{fhComb}\ 6\ 0\ t\ x\ 1\ q\ \widehat v\ L\ 0.
\]
Thus (3) and (4) replace that unit-shape certificate and its collection
link directly. The existing upper-shape hypothesis `hB`, obtained from
`fhCLRb_pos_y` and `fh_LRb_link`, and the call to `fh_comb_pos_of_ends`
still close the caller with this new `hA`. This describes the replacement
interface; no Lean source has been changed or checked here.

The proof also gives the old full collection identity, if it is wanted:
the polynomial assembled from the displayed \(C_i\) has the same first four
\(j\)-derivatives at zero and the same fourth derivative by (27), so the
difference vanishes identically by repeated integration. That conclusion
uses derivative uniqueness, not a large ring expansion.

## Appendix A. Complete small jet polynomials and their verification

These are the polynomials used in (14)–(23). Each is printed as a polynomial
in \(q\) with explicitly factored coefficients in \(h\). Coefficientwise
checks in \(q\) use univariate identities in \(h\), never an expansion in
\((h,j,q)\). In particular \(T_2\) is kept coefficientwise; its full
bivariate degree is nine, whereas every coefficient identity required in
(14) has degree at most seven in \(h\).

### The four \(T_i\) polynomials

\[
\begin{aligned}
4T_0={}&3 \left(h - 1\right) \left(h + 1\right)^{3}\\
&+\bigl(\left(h - 1\right) \left(h + 1\right)^{2} \left(2 h + 5\right)\bigr)q\\
&+\bigl(2 \left(h + 1\right) \left(7 h^{3} + 6 h^{2} - 31 h - 6\right)\bigr)q^{2}\\
&+\bigl(- 20 h^{4} - 79 h^{3} + 33 h^{2} + 183 h + 27\bigr)q^{3}\\
&+\bigl(\left(h - 1\right) \left(h^{3} + 17 h^{2} + 26 h + 6\right)\bigr)q^{4}\\
&+\bigl(\left(h - 1\right) \left(2 h + 1\right)\bigr)q^{5} .
\end{aligned}
\]

\[
\begin{aligned}
4T_1={}&21 \left(h - 1\right) \left(h + 1\right)^{3}\\
&+\bigl(4 \left(h - 1\right) \left(h + 1\right)^{2} \left(7 h + 10\right)\bigr)q\\
&+\bigl(10 \left(h + 1\right) \left(7 h^{3} + 13 h^{2} - 31 h - 13\right)\bigr)q^{2}\\
&+\bigl(- 2 \left(65 h^{4} + 262 h^{3} - 36 h^{2} - 462 h - 165\right)\bigr)q^{3}\\
&+\bigl(\left(h - 1\right) \left(23 h^{3} + 126 h^{2} + 173 h + 58\right)\bigr)q^{4}\\
&+\bigl(2 \left(h - 1\right) \left(h + 1\right) \left(2 h + 3\right)\bigr)q^{5} .
\end{aligned}
\]

\[
\begin{aligned}
4T_2={}&60 \left(h - 1\right) \left(h + 1\right)^{3}\\
&+\bigl(2 \left(h - 1\right) \left(h + 1\right)^{2} \left(59 h + 68\right)\bigr)q\\
&+\bigl(2 \left(h + 1\right) \left(h + 3\right) \left(92 h^{2} - 81 h - 65\right)\bigr)q^{2}\\
&+\bigl(- 438 h^{4} - 1437 h^{3} - 9 h^{2} + 2021 h + 967\bigr)q^{3}\\
&+\bigl(\left(h - 1\right) \left(110 h^{3} + 417 h^{2} + 500 h + 185\right)\bigr)q^{4}\\
&+\bigl(\left(h - 1\right) \left(h + 1\right)^{2} \left(2 h + 13\right)\bigr)q^{5} .
\end{aligned}
\]

\[
\begin{aligned}
2T_3={}&45 \left(h - 1\right) \left(h + 1\right)^{2}\\
&+\bigl(2 \left(h - 1\right) \left(h + 1\right) \left(58 h + 61\right)\bigr)q\\
&+\bigl(2 \left(83 h^{3} + 139 h^{2} - 167 h - 139\right)\bigr)q^{2}\\
&+\bigl(- 3 \left(143 h^{3} + 224 h^{2} - 207 h - 224\right)\bigr)q^{3}\\
&+\bigl(2 \left(h - 1\right) \left(h + 1\right) \left(58 h + 73\right)\bigr)q^{4}\\
&+\bigl(\left(h - 1\right) \left(h + 1\right) \left(4 h + 9\right)\bigr)q^{5} .
\end{aligned}
\]


### The four \(U_i\) polynomials

\[
\begin{aligned}
4U_0={}&- \left(h - 1\right) \left(h + 1\right)^{3}\\
&+\bigl(\left(h - 1\right) \left(h + 1\right)^{2} \left(2 h + 1\right)\bigr)q\\
&+\bigl(- 2 \left(h + 1\right) \left(6 h^{3} - h^{2} - 12 h + 1\right)\bigr)q^{2}\\
&+\bigl(2 \left(5 h^{4} + 11 h^{3} - 11 h^{2} - 24 h + 1\right)\bigr)q^{3}\\
&+\bigl(h \left(h - 1\right) \left(h^{2} - 2\right)\bigr)q^{4} .
\end{aligned}
\]

\[
\begin{aligned}
4U_1={}&- 6 \left(h - 1\right) \left(h + 1\right)^{3}\\
&+\bigl(\left(h - 1\right) \left(h + 1\right)^{2} \left(10 h + 7\right)\bigr)q\\
&+\bigl(- 2 \left(h + 1\right) \left(29 h^{3} + 8 h^{2} - 53 h - 8\right)\bigr)q^{2}\\
&+\bigl(2 \left(25 h^{4} + 53 h^{3} - 33 h^{2} - 90 h - 21\right)\bigr)q^{3}\\
&+\bigl(\left(h - 1\right)^{2} \left(4 h^{2} + 7 h + 2\right)\bigr)q^{4} .
\end{aligned}
\]

\[
\begin{aligned}
4U_2={}&- 14 \left(h - 1\right) \left(h + 1\right)^{2}\\
&+\bigl(\left(h - 1\right) \left(h + 1\right) \left(20 h + 17\right)\bigr)q\\
&+\bigl(- 2 \left(56 h^{3} + 35 h^{2} - 86 h - 35\right)\bigr)q^{2}\\
&+\bigl(2 \left(50 h^{3} + 53 h^{2} - 86 h - 53\right)\bigr)q^{3}\\
&+\bigl(3 \left(h - 1\right) \left(h + 1\right) \left(2 h - 1\right)\bigr)q^{4} .
\end{aligned}
\]

\[
\begin{aligned}
4U_3={}&- 16 \left(h - 1\right) \left(h + 1\right)^{2}\\
&+\bigl(\left(h - 1\right) \left(h + 1\right) \left(20 h + 19\right)\bigr)q\\
&+\bigl(- 2 \left(54 h^{3} + 47 h^{2} - 66 h - 47\right)\bigr)q^{2}\\
&+\bigl(2 \left(50 h^{3} + 51 h^{2} - 62 h - 51\right)\bigr)q^{3}\\
&+\bigl(\left(h - 1\right) \left(h + 1\right) \left(4 h + 1\right)\bigr)q^{4} .
\end{aligned}
\]


### The four \(V_i\) polynomials

\[
\begin{aligned}
2V_0={}&4 \left(6 h^{4} + 53 h^{3} + 228 h^{2} + 450 h + 270\right)\\
&+\bigl(42 h^{4} + 305 h^{3} + 870 h^{2} + 1500 h + 900\bigr)q\\
&+\bigl(3 \left(6 h^{4} + 43 h^{3} + 118 h^{2} + 200 h + 120\right)\bigr)q^{2}\\
&+\bigl(- 12 \left(h + 1\right) \left(h^{2} + 10 h + 15\right)\bigr)q^{3} .
\end{aligned}
\]

\[
\begin{aligned}
2V_1={}&3 \left(6 h^{4} + 55 h^{3} + 142 h^{2} + 628 h + 900\right)\\
&+\bigl(3 \left(6 h^{4} + 85 h^{3} + 305 h^{2} + 790 h + 950\right)\bigr)q\\
&+\bigl(3 \left(14 h^{3} + 41 h^{2} + 206 h + 380\right)\bigr)q^{2}\\
&+\bigl(- 6 \left(13 h^{2} + 114 h + 155\right)\bigr)q^{3} .
\end{aligned}
\]

\[
\begin{aligned}
2V_2={}&3 \left(18 h^{4} + 73 h^{3} + 49 h^{2} + 576 h + 774\right)\\
&+\bigl(3 \left(18 h^{4} + 145 h^{3} + 538 h^{2} + 1475 h + 1280\right)\bigr)q\\
&+\bigl(- 3 \left(8 h^{3} + 179 h^{2} + 149 h - 118\right)\bigr)q^{2}\\
&+\bigl(- 12 \left(15 h^{2} + 106 h + 121\right)\bigr)q^{3} .
\end{aligned}
\]

\[
\begin{aligned}
2V_3={}&54 h^{3} - 3 h^{2} - 85 h + 812\\
&+\bigl(54 h^{3} + 267 h^{2} + 1376 h + 2315\bigr)q\\
&+\bigl(- 3 \left(54 h^{2} + 387 h + 325\right)\bigr)q^{2}\\
&+\bigl(- 6 \left(29 h + 109\right)\bigr)q^{3} .
\end{aligned}
\]


### The four \(K_i\) polynomials

\[
\begin{aligned}
K_0={}&56 \left(h - 1\right) \left(h + 1\right) \left(h^{2} + 10 h + 15\right)\\
&+\bigl(- 4 \left(h - 1\right) \left(2 h + 1\right) \left(h^{2} + 10 h + 15\right)\bigr)q^{2} .
\end{aligned}
\]

\[
\begin{aligned}
K_1={}&56 \left(h - 1\right) \left(h + 1\right) \left(h^{3} + 19 h^{2} + 97 h + 115\right)\\
&+\bigl(- 4 \left(h - 1\right) \left(2 h^{4} + 39 h^{3} + 215 h^{2} + 347 h + 145\right)\bigr)q^{2} .
\end{aligned}
\]

\[
\begin{aligned}
K_2={}&56 \left(h - 1\right) \left(h + 1\right) \left(9 h^{3} + 118 h^{2} + 411 h + 386\right)\\
&+\bigl(- 4 \left(h - 1\right) \left(18 h^{4} + 247 h^{3} + 975 h^{2} + 1347 h + 571\right)\bigr)q^{2} .
\end{aligned}
\]

\[
\begin{aligned}
K_3={}&56 \left(h - 1\right) \left(h + 1\right) \left(35 h^{3} + 371 h^{2} + 997 h + 757\right)\\
&+\bigl(- 8 \left(h - 1\right) \left(35 h^{4} + 396 h^{3} + 1274 h^{2} + 1541 h + 622\right)\bigr)q^{2} .
\end{aligned}
\]


### Why the \(K_i\) checks do not expand a degree-ten polynomial

For the fourth line of (14), set \(j=w\xi\). The following factor identities
follow from the quadratic inputs in (5):
\[
\begin{gathered}
B=w(1+w\xi+w\xi^2),\qquad p=w(1/2+\xi),\qquad W=w(1+\xi),\\
R=r_0+wr_1\xi+w^2\xi^2,\\
7W^2-Jq^2=w\{d_0+2w(7-q^2)\xi+w(7-q^2)\xi^2\},\\
d_0=7w-(h+1/2)q^2.
\end{gathered}
\tag{31}
\]
Each is checked separately, coefficientwise in \(q\) when necessary;
these identities have at most nine monomials and degree at most four in
\((h,\xi)\). Pulling out their displayed powers of \(w\) gives
\[
\begin{aligned}
\mathcal K((1-h)/2,h+w\xi,q)=w^5Z(q)\bigl[&-32t(1+w\xi+w\xi^2)(1/2+\xi)(1+\xi)^2\\
 &\cdot(r_0+wr_1\xi+w^2\xi^2)\\
 &\cdot\{d_0+2w(7-q^2)\xi+w(7-q^2)\xi^2\}\bigr].
\end{aligned}
\tag{32}
\]
The bracket's first four coefficients in \(\xi\) are exactly
\(K_0,K_1,K_2,K_3\). Each such coefficient identity has two variables
\((h,q)\), degree at most seven, and respectively 10, 12, 12, 12 monomials.
Comparing powers of \(j=w\xi\) gives the factors \(w^{5-i}\) in (14).
This verifies the fourth line with ordinary short coefficient products,
without clearing or expanding the full polynomial \(\mathcal K\).

## Appendix B. Remaining expansion counts and implementation boundary

The first three lines of (14) are checked one \(q\)-coefficient at a time.
The largest degree is seven, with at most eight monomials per identity;
this bound follows from the degrees of the original \((t,x)\) coefficient
polynomials before substitution. The six \(\mathcal T\)-coefficients have
12, 17, 26, 26, 22, 15 monomials; the five \(\mathcal U\)-coefficients have
10, 9, 13, 12, 9. Their denominators are small powers of two after
\(t=(1-h)/2\). No high-degree coefficient is concealed in an unprinted
auxiliary definition.

For the four families in (23), the exact counts of the coefficients of
\(q^0,\ldots,q^7\), in order, are:

| Face family | Monomial counts of the eight univariate identities | Maximum degree in \(h\) | Common denominator before clearing | Largest coefficient after clearing |
| --- | --- | ---: | ---: | ---: |
| \(F_0\) | 7, 9, 9, 9, 9, 9, 9, 7 | 8 | 2 | 53004 |
| \(F_1^{\rm lo}\) | 9, 9, 9, 9, 9, 9, 9, 8 | 8 | 2 | 424386 |
| \(F_2\) | 9, 9, 9, 9, 9, 9, 8, 7 | 8 | 2 | 742680 |
| \(F_3\) | 9, 9, 9, 9, 9, 9, 8, 7 | 8 | 2 | 1414154 |

The separated leading coefficient (20) is a five-monomial univariate
identity of degree five. All other named scalar polynomials required for
signs, including the base square completions and all \(B_{in},P_{in}\),
are completely printed in the companion notes with their own counts.

For formalization, preserve the exact verification order stated above:
affine scalar decomposition, coefficientwise clearing, four small jets,
coefficientwise normalized faces, then the fourth derivative before
expanding. A single global \(\texttt{ring}\) call on (13), (14), or (27)
would discard this structure and is not the proposed implementation.

All identities and arithmetic comparisons in these notes can be checked
from the displayed expressions. Exact symbolic algebra was used to check
the transcription and the expansion-size audit. Executing that check is
not a proof premise. This is a hand replacement; no Lean compilation or
measured Lean performance improvement is claimed.
