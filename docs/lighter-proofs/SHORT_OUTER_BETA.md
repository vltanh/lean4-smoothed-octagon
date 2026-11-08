# A small beta-concavity proof for the first S1 outer sign

This note reduces the \(F_1\) test in
[MIXED_SMALLER_SHORT_LOW_RATIO_OUTER_HAND_SIGN](../../archive/notes/MIXED_SMALLER_SHORT_LOW_RATIO_OUTER_HAND_SIGN.md)
to two beta endpoints, before any shape substitution or large polynomial
expansion. It is a partial replacement: **the resulting \(F_1\) signs
remain to be proved.** The companion \(F_0\) sign is now proved on the
[actual small-shape branch](SHORT_OUTER_LOW_SHAPE_TERMINAL.md); its other
branches and S1 as a whole remain open.

The largest expanded identity used below has 19 monomials, total degree
seven in two variables, and coefficients of absolute value at most 1242.

## 1. Statement on a fixed incoming norm

Fix

\[
1\le x\le2,\quad 1\le a\le x,\quad
u\le u_0(x):=\frac34+\frac{(x-1)^2}{12(x+1)^2}.
\]

The variable \(a\) is the original \(\alpha\). Let

\[
x\le\beta\le ax,\qquad B=a+\beta,\qquad S=x+1,\qquad K=6a^2+1.
\]

Use precisely the original outer-face functions at \(q=1/7\):

\[
\begin{aligned}
D&=a^2+2a\beta+1+2x-2\beta x,\\
E_0&=S(u-1)+S^{-1},\qquad J=KE_0+2S-1,\\
M&=K^2-SK+S^2,\\
w&=\frac{M+uD^2-DJ}{49a^4},\qquad
E_L=\frac{2uD-J}{7a^2},\\
T&=\frac{7a}{B},\qquad
\ell(y)=2\frac{y-1}{y+1}+\frac23\left(\frac{y-1}{y+1}\right)^3.
\end{aligned}
\tag{1}
\]

For completeness, the central-envelope quantities used in the companion
norm and shape derivatives are the following small rational expressions:
\[
U(r)=1-r+r^2,\qquad
v=U(S/K)=1-S/K+S^2/K^2,\qquad
E=E_0+(2S-1)/K,
\]
\[
\Gamma_*=\frac{K^2(4uv-E^2)}{576a^4},\qquad
\lambda=\frac{K}{7a^2},\quad\delta=\frac{D}{7a^2}.
\]
Thus the same transport can be written, without changing any scalar norm,
\(w=\lambda^2v+\delta^2u-\delta\lambda E\) and
\(E_L=2\delta u-\lambda E\). These follow from the displayed definitions
of \(M,J\); all polynomial factors are printed above.

The one logarithm bound is the original
\(\log y\le\ell(y)\) for \(0<y\le1\). Here its argument
\(y=2B/(7a)\) belongs to \([4/7,6/7]\), since
\(2a\le B\le a(1+x)\le3a\).

Define

\[
\begin{aligned}
\overline R_2&=2w-\frac12+(u-1)\frac Ba+\frac aB-\frac17-E_L
                       +\ell\!\left(\frac{2B}{7a}\right),\\
R_1&=\overline R_2+(T-2)(w-3/4),\\
F_1&=\Gamma_*-\frac7{96}R_1-\frac{9193}{50000}.
\end{aligned}
\tag{2}
\]

At fixed \(x,a,u\), the central-envelope Casimir \(\Gamma_*\) is
independent of \(\beta\). We prove

\[
\boxed{\frac{\partial^2F_1}{\partial\beta^2}<0.}
\tag{3}
\]

All norms are frozen while taking this derivative. Section 6 specifies
how to use (3) with the actual incoming interval, including the
beta-dependent upper bound \(u_\ell\) in the old note.

## 2. Polynomial division exposes the only nonlinear beta terms

Write

\[
\eta=x-a,\qquad
D_0=(a+1)(2x+1-a)=-a^2+2ax+2x+1.
\]

Then

\[
D=D_0-2\eta B,\qquad
w=w_0+w_1B+w_2B^2,
\tag{4}
\]

where

\[
\begin{aligned}
w_0&=\frac{M+uD_0^2-D_0J}{49a^4},\\
w_1&=\frac{2\eta(J-2uD_0)}{49a^4},\qquad
w_2=\frac{4u\eta^2}{49a^4},\\
E_L&=\frac{2uD_0-J}{7a^2}-\frac{4u\eta}{7a^2}B.
\end{aligned}
\]

Only the three-term square identity

\[
(D_0-2\eta B)^2=D_0^2-4D_0\eta B+4\eta^2B^2
\tag{5}
\]

is needed for this division. It has total degree four in the three
displayed scalar arguments \(D_0,\eta,B\). The coefficient functions
in (4) stay opaque; they are not expanded into the beta polynomial.

Substituting (4) into (2) leaves

\[
R_1=A_0+A_1B+\frac{a(7w_0-17/4)}{B}
                    +\ell\!\left(\frac{2B}{7a}\right),
\tag{6}
\]

with the beta-independent coefficients

\[
A_0=7aw_1+\frac67-\frac{2uD_0-J}{7a^2},
\qquad
A_1=7aw_2+\frac{u-1}{a}+\frac{4u\eta}{7a^2}.
\]

Consequently

\[
\frac{\partial^2R_1}{\partial\beta^2}
=\frac{2a(7w_0-17/4)}{B^3}
 +\left(\frac2{7a}\right)^2
       \ell''\!\left(\frac{2B}{7a}\right).
\tag{7}
\]

The notation \(w_0\) is a polynomial-division coefficient. It can also
be obtained by the formal substitution \(\beta=-a\), which is not an
actual geometry.

## 3. A six-term logarithm derivative identity

Direct differentiation gives

\[
\ell''(y)+\frac1{y^2}
 =\frac{(1-y)^3(1+8y-y^2)}{y^2(1+y)^5}\ge0
 \qquad(0<y\le1).
\tag{8}
\]

The complete expanded numerator is

\[
1+5y-22y^2+26y^3-11y^4+y^5.
\]

It has six monomials and degree five. Its sign follows from the
displayed factorization, since \(1+8y-y^2\ge8y>0\). Thus

\[
\frac{\partial^2R_1}{\partial\beta^2}
\ge \frac{2a(7w_0-17/4)-B}{B^3}.
\tag{9}
\]

It remains to prove a beta-independent lower bound on \(w_0\).

## 4. The lower bound on the division coefficient uses two variables

First \(w_0\) strictly decreases with \(u\). Its exact derivative is

\[
\frac{\partial w_0}{\partial u}
=-\frac{(a+1)(2x+1-a)(6a^2x+7a^2-2ax-x)}{49a^4}<0.
\tag{10}
\]

The last factor equals
\(x(6a^2-2a-1)+7a^2>0\), because

\[
6a^2-2a-1=3+2(a-1)(3a+2)\ge3.
\]

For an expanded check, the numerator without its minus sign in (10)
is the 11-monomial, degree-five bivariate polynomial

\[
\begin{aligned}
{}&-6a^4x-7a^4+12a^3x^2+16a^3x
 +8a^2x^2+21a^2x+7a^2\\
&\qquad-6ax^2-2ax-2x^2-x.
\end{aligned}
\]

It follows that \(w_0(x,a,u)\ge w_0(x,a,u_0(x))\). Define the last
expression as \(W_0(x,a)\).

Next \(W_0\) strictly decreases with \(a\) for \(1\le a\le x\le2\).
Put \(z=x-1,\ c=a-1\), so \(0\le c\le z\le1\). The required
derivative identity is

\[
-147a^5(x+1)^2\,\partial_a W_0=P(c,z),
\tag{11}
\]

where the complete polynomial is

\[
\begin{aligned}
P(c,z)={}&
c^3(6z^4+44z^3+74z^2-36)\\
&+c^2(50z^4+313z^3+558z^2+216z-72)\\
&+c(109z^4+653z^3+1242z^2+756z+72)\\
&+73z^4+434z^3+872z^2+648z+144.
\end{aligned}
\tag{12}
\]

This has 19 monomials and total degree seven in two variables. The
only negative terms are \(-36c^3-72c^2\). Since \(0\le c\le1\), all
remaining terms give the immediate bound

\[
P(c,z)\ge144-36c^3-72c^2\ge36>0.
\tag{13}
\]

The endpoint \(a=x\) has the five-term expression

\[
W_0(x,x)=
\frac{12x^4+502x^3-70x^2+26x-2}{588x^3}.
\tag{14}
\]

Its difference from the desired lower bound factors as

\[
\begin{aligned}
W_0(x,x)-\frac{19+2x}{28}
&=\frac{-30x^4+103x^3-70x^2+26x-2}{588x^3}\\
&=\frac{(10x-1)(-3x^3+10x^2-6x+2)}{588x^3}>0.
\end{aligned}
\tag{15}
\]

Indeed the cubic factor at \(x=1+z\) is

\[
3+5z+z^2-3z^3
\ge3+5z-2z^2\ge3\qquad(0\le z\le1).
\tag{16}
\]

Combining the two monotonicities and the endpoint yields

\[
\boxed{w_0(x,a,u)>\frac{19+2x}{28}.}
\tag{17}
\]

No upper or lower beta endpoint, norm ceiling or physical root is
assigned to the formal division value.

## 5. Strict concavity

By (17),

\[
2a(7w_0-17/4)>a(1+x)\ge a+\beta=B.
\]

Equation (9) therefore gives \(R_{1,\beta\beta}>0\), and multiplying
by \(-7/96\) proves (3). This proof reduces one free shape variable
using only the explicit small derivative signs above.

## 6. Exact caller reduction, with the incoming norm frozen

The actual ordered secants give

\[
\begin{aligned}
\beta_-&=x+\frac{8x}{9x+8}(a-1),\\
\beta_+&=x+\frac{x(7x+1)}{4x^2+11x+1}(a-1),\\
\beta_-&\le\beta\le\beta_+.
\end{aligned}
\tag{18}
\]

Both endpoints belong to \([x,ax]\): each coefficient of \(a-1\)
is nonnegative and at most \(x\). Their ordering follows from the
positive difference

\[
\frac{x(7x+1)}{4x^2+11x+1}-\frac{8x}{9x+8}
=\frac{x^2(31x-23)}
 {(4x^2+11x+1)(9x+8)}>0.
\]

The actual norm has the beta-independent interval

\[
u_f(x)=\frac34+\frac{(x-1)^2}{28(x+1)^2}
\le u\le
u_v(x)=\frac34+\frac{2(x-1)^2}{(x+1)(35x+13)}.
\tag{19}
\]

The actual upper bound \(u\le u_v\) is the equal-secant comparison
already cited in Section 1 of the old outer-face note. Moreover

\[
u_0-u_v=\frac{11(x-1)^3}{12(x+1)^2(35x+13)}\ge0.
\]

Thus (3) applies with the **same** \(u\) at both beta endpoints:

\[
F_1(x,a,\beta,u)\ge
\min\{F_1(x,a,\beta_-,u),F_1(x,a,\beta_+,u)\}.
\tag{20}
\]

At each endpoint \(F_1\) is concave in \(u\), as in the original note.
In detail its second derivative is

\[
F_{1,uu}=-\frac{K^2S^2}{288a^4}<0.
\]

The positive numerator has the nine-term, degree-six expansion

\[
36a^4x^2+72a^4x+36a^4
 +12a^2x^2+24a^2x+12a^2+x^2+2x+1.
\]

Consequently it is sufficient to prove the **four bivariate signs**

\[
\boxed{F_1(x,a,\beta_\pm,u_f(x))>0,\qquad
       F_1(x,a,\beta_\pm,u_v(x))>0}
\tag{21}
\]

on the actual outer-face domain
\(1\le x\le2,\ 1\le a\le x,\ 6a^2\ge x(x+2)\).
They are the remaining obligations of this route; their positivity
is not proved here.

The old sharper endpoint \(u_\ell(x,\beta)\) depends on \(\beta\).
One cannot apply fixed-\(u\) concavity directly to
\(F_1(x,a,\beta,u_\ell(x,\beta))\), or move \(\beta\) while silently
substituting the new endpoint's value of \(u_\ell\). Formula (19)
deliberately enlarges to the beta-independent interval \([u_f,u_v]\)
before (20). This enlargement still contains the actual norm and is
valid for every endpoint used here. It leaves the \(F_0\) problem
untouched; its old \(u_\ell\) endpoint cannot be discarded on this basis.

## Identity sizes and validation

The expanded identities that require sign arithmetic have sizes:

| Polynomial | Monomials | Variables | Total degree | Largest coefficient magnitude |
|---|---:|---:|---:|---:|
| Square identity (5) | 3 | 3 | 4 | 4 |
| Logarithm derivative numerator (8) | 6 | 1 | 5 | 26 |
| Incoming derivative numerator (10) | 11 | 2 | 5 | 21 |
| Shape derivative \(P\), (12) | 19 | 2 | 7 | 1242 |
| Endpoint numerator (14) | 5 | 1 | 4 | 502 |
| Endpoint difference numerator (15) | 5 | 1 | 4 | 103 |
| Cubic (16) | 4 | 1 | 3 | 5 |
| Norm-concavity numerator | 9 | 2 | 6 | 72 |

The smaller auxiliary identities use
\(D_0=-a^2+2ax+2x+1\) (four terms, degree two),
\(6a^2-2a-1\) (three terms, degree two),
and \(11(x-1)^3=11x^3-33x^2+33x-11\) (four terms, degree three).
The coefficient functions in (4) and (6) remain unexpanded products
throughout the beta differentiation.

All displayed identities were independently reconstructed with exact
rational symbolic arithmetic as a transcription check. The signs are
proved by the displayed factorizations and inequalities. No Lean
compilation or CI was run.
