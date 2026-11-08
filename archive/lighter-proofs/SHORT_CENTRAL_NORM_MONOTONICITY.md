# Central S1: a small proof of incoming-norm monotonicity

This replaces the norm-derivative sign in Appendix A, equation (18), of
[MIXED_SMALLER_SHORT_LOW_RATIO_CENTRAL_HAND_SIGN](../../archive/notes/MIXED_SMALLER_SHORT_LOW_RATIO_CENTRAL_HAND_SIGN.md).
The conclusion and its full containing domain are unchanged:
\[
 \boxed{\left.(F_1)_u\right|_{u=3/4}<0}
 \quad\left(\frac85\le x\le2,\quad1\le a\le\frac76,
 \quad b=x+C(a-1),\quad\frac12\le C\le\frac45\right).
 \tag{1}
\]
No actual-cap or cone hypothesis is added. This derivative sign is a subordinate
step of the central S1 proof, not a replacement of its beta, shape, or terminal
signs.

The proof first moves beta to its lower endpoint, then raises a to 7/6, and
finally proves a univariate residual increasing before checking one rational
endpoint. The largest expanded polynomial identity has 41 monomials and degree
eight in two variables. The final derivative has nine monomials and degree
eight in one variable.

## 1. Exact differentiated source

Use the original central-scale functions and set
\[
 S=x+1,\quad X=x(x+2)=x^2+2x,\quad K=X+a^2,\quad B=a+b,
\]
\[
 D=a^2+2ab+1+2x-2bx,\qquad c=7/96.
\]
The only three-variable polynomial here, D, has six monomials and degree two.
Differentiating the original rational source in u gives, at u=3/4,
\[
 \Psi(x,a,b):=\left.(F_1)_u\right|_{u=3/4}=G(x)-cH(x,a,b),
 \tag{2}
\]
\[
 G(x)=\frac{G_n(x)}{32X^2},\qquad
 H=\frac Ba+\frac{S^3-2D}{K}+\frac{D(D-S^3)}{aBK},
\]
\[
\begin{aligned}
G_n(x)={}&x^{6} + 6 x^{5} + 11 x^{4} - 13 x^{2}\\
&{}- 6 x + 1
\end{aligned}
\]
This polynomial has 6 monomials, total degree 6, and largest cleared coefficient 13.

The source identity for this numerator is
\[
 G_n=S^6-4S^4-4S^3+8S^2.
\]
This is a six-monomial degree-six identity in x. It is the same as the original
Casimir derivative
\((S^6/2-2S^4-2S^3+4S^2)/(16X^2)\).
The logarithm and the target constant have zero u derivative. No logarithm
estimate is used in this note.

## 2. Beta is eliminated by a positive derivative

Write
\[
 D_0=(a+1)(2x+1-a)=-a^2+2ax+2x+1,\qquad d=2(a-x).
\]
Then \(D=D_0+dB\). This is a quadratic coefficient identity in B; its
coefficient checks in a,x have degree at most two. The complete four- and
five-monomial polynomials relevant to the signs are
\[
 D_0=-a^2+2ax+2x+1,
 \qquad S^3-D_0=a^2-2ax+x^3+3x^2+x.
\]
They have degrees two and three. On (1),
\[
 0<D_0\le\frac{13}{6}\cdot4=\frac{26}{3}
 <\left(\frac{13}{5}\right)^3\le S^3.
\]
Thus \(D_0(S^3-D_0)>0\).

Divide the quadratic numerator in B before expanding any coefficient:
\[
 H=\alpha B+\eta-\frac{\gamma}{B},
\]
\[
 \alpha=\frac{(a-2x)^2+X}{aK}>0,
 \quad \eta=\frac{(2x-a)(S^3-2D_0)}{aK},
 \quad \gamma=\frac{D_0(S^3-D_0)}{aK}>0.
 \tag{3}
\]
For a direct check, multiplying H by aKB gives the three coefficients
\[
 \begin{aligned}
 [B^2]&=K-2ad+d^2=a^2-4ax+5x^2+2x,\\
 [B]&=(a-d)(S^3-2D_0)=(2x-a)(S^3-2D_0),\\
 [1]&=D_0(D_0-S^3).
 \end{aligned}
\]
The first coefficient has four monomials and degree two. The other two are
retained as the printed products, of total degrees four and five in a,x.
This is univariate quadratic arithmetic in B with its coefficients held fixed;
no polynomial in a,x,B of degree greater than four is expanded.

It follows at once that
\[
 H_b=\alpha+\gamma/B^2>0,\qquad \Psi_b<0.
\]
Since a≥1, lower C to 1/2. Set
\[
 \phi(x,a)=\Psi\bigl(x,a,x+(a-1)/2\bigr).
\]
Then \(\Psi\le\phi\) on the whole original rectangle.

## 3. A separate two-variable shape derivative

On this beta face put
\[
 L_a=3a+2x-1=2B,\qquad
 D_c=2a^2+ax-a-2x^2+3x+1.
\]
The latter is a six-monomial quadratic. Define
\[
 V=aKL_a,\qquad
 N=KL_a^2+2aL_a(S^3-2D_c)+4D_c(D_c-S^3).
 \tag{4}
\]
Then \(H=N/(2V)\), and
\[
 \phi_a=\frac{P_a(x,a)}{192V^2},
 \qquad P_a=7(NV_a-VN_a).
 \tag{5}
\]
Here all the numerator and derivative inputs are printed, so (5) can be checked
as two separate products of total degree at most eight:
\[
\begin{aligned}
N(x,a)={}&a^{4} - 2 a^{3} - 2 a^{2} x^{3} - 5 a^{2} x^{2}\\
&{}+ 24 a^{2} x + 3 a^{2} + 14 a x^{3} + 32 a x^{2}\\
&{}- 18 a x - 2 a + 8 x^{5} + 32 x^{4}\\
&{}- 60 x^{3} - 27 x^{2} + 2 x
\end{aligned}
\]
This polynomial has 15 monomials, total degree 5, and largest cleared coefficient 60.

\[
\begin{aligned}
V(x,a)={}&3 a^{4} + 2 a^{3} x - a^{3} + 3 a^{2} x^{2}\\
&{}+ 6 a^{2} x + 2 a x^{3} + 3 a x^{2} - 2 a x
\end{aligned}
\]
This polynomial has 8 monomials, total degree 4, and largest cleared coefficient 6.

\[
\begin{aligned}
\partial_aN(x,a)={}&4 a^{3} - 6 a^{2} - 4 a x^{3} - 10 a x^{2}\\
&{}+ 48 a x + 6 a + 14 x^{3} + 32 x^{2}\\
&{}- 18 x -2
\end{aligned}
\]
This polynomial has 10 monomials, total degree 4, and largest cleared coefficient 48.

\[
\begin{aligned}
\partial_aV(x,a)={}&12 a^{3} + 6 a^{2} x - 3 a^{2} + 6 a x^{2}\\
&{}+ 12 a x + 2 x^{3} + 3 x^{2} - 2 x
\end{aligned}
\]
This polynomial has 8 monomials, total degree 3, and largest cleared coefficient 12.

\[
\begin{aligned}
P_a(x,a)={}&- 14 a^{6} x - 35 a^{6} - 84 a^{5} x^{3} - 252 a^{5} x^{2}\\
&{}+ 924 a^{5} x + 126 a^{5} - 28 a^{4} x^{4} + 784 a^{4} x^{3}\\
&{}+ 2366 a^{4} x^{2} - 1134 a^{4} x - 147 a^{4} + 672 a^{3} x^{5}\\
&{}+ 3080 a^{3} x^{4} - 4284 a^{3} x^{3} - 3136 a^{3} x^{2} + 308 a^{3} x\\
&{}+ 28 a^{3} + 364 a^{2} x^{6} + 1582 a^{2} x^{5} - 2191 a^{2} x^{4}\\
&{}+ 476 a^{2} x^{3} + 126 a^{2} x^{2} - 84 a^{2} x + 336 a x^{7}\\
&{}+ 2016 a x^{6} + 168 a x^{5} - 6174 a x^{4} - 2184 a x^{3}\\
&{}+ 168 a x^{2} + 112 x^{8} + 616 x^{7} - 280 x^{6}\\
&{}- 2086 x^{5} + 301 x^{4} + 420 x^{3} - 28 x^{2}
\end{aligned}
\]
This polynomial has 36 monomials, total degree 8, and largest cleared coefficient 6174.

For the sign put \(A=a-1\in[0,1/6]\), \(z=x-3/2\in[1/10,1/2]\).
The proof also works on the slightly larger interval 0≤z≤1/2. The complete shift is
\[
\begin{aligned}
P_a(3/2+z,1+A)={}&- 14 A^{6} z - 56 A^{6} - 84 A^{5} z^{3} - 630 A^{5} z^{2}\\
&{}- 483 A^{5} z + \frac{651 A^{5}}{2} - 28 A^{4} z^{4} + 196 A^{4} z^{3}\\
&{}+ 2366 A^{4} z^{2} + 8673 A^{4} z + \frac{33789 A^{4}}{4} + 672 A^{3} z^{5}\\
&{}+ 8008 A^{3} z^{4} + 30940 A^{3} z^{3} + 57610 A^{3} z^{2} + 59815 A^{3} z\\
&{}+ 29085 A^{3} + 364 A^{2} z^{6} + 6874 A^{2} z^{5} + 46151 A^{2} z^{4}\\
&{}+ 138299 A^{2} z^{3} + \frac{824229 A^{2} z^{2}}{4} + \frac{1226757 A^{2} z}{8} + \frac{759969 A^{2}}{16}\\
&{}+ 336 A z^{7} + 6272 A z^{6} + 45920 A z^{5} + 170982 A z^{4}\\
&{}+ 345149 A z^{3} + 371231 A z^{2} + \frac{379155 A z}{2} + \frac{250383 A}{8}\\
&{}+ 112 z^{8} + 2296 z^{7} + 19152 z^{6} + 85386 z^{5}\\
&{}+ 220528 z^{4} + \frac{661353 z^{3}}{2} + 268002 z^{2} + \frac{740691 z}{8}\\
&{}+ \frac{33005}{16}
\end{aligned}
\]
This polynomial has 41 monomials, total degree 8, and largest cleared coefficient 5939696.

The only negative terms lie in the A⁶ and A⁵ groups, and in \(-28A^4z^4\).
Use \(A^6\le A^4/36\), \(A^5\le A^4/6\), and \(z^4\le z^3/2\) only on
these negative terms. Together with the positive A⁴ group, they leave
\[
 A^4\left(168z^3+2261z^2+\frac{77329}{9}z+\frac{304045}{36}\right)\ge0.
 \tag{6}
\]
The polynomial in parentheses has four monomials and degree three, with largest
cleared coefficient 304045. Every other printed term is nonnegative, and the
constant is \(33005/16>0\). Thus \(P_a>0\) and \(\phi_a>0\).
Consequently
\[
 \Psi(x,a,b)\le\phi(x,a)\le\phi(x,7/6).
 \tag{7}
\]
No beta or norm condition has been changed during this shape comparison.

## 4. The final univariate comparison uses its first derivative

Now set a=7/6, b=x+1/12. Define the complete small factors
\[
 L=4x+5,\quad M=36x^2+72x+49,\quad J=-36x^2+75x+46.
\]
They have respectively two, three, and three monomials, of degrees one, two,
and two. At this face,
\[
 B=L/4,\quad K=M/36,\quad D=J/18.
\]
The exact residual is the following fully specified sum of six products:
\[
\begin{aligned}
 \mathcal P(x)={}&-18LMG_n+9X^2L^2M+1512X^2LS^3\\
 &-168X^2LJ+16X^2J^2-288X^2JS^3.
\end{aligned}
 \tag{8}
\]
Substitution into (2), with the scalar cancellations performed separately in
each of its three H terms, gives
\[
 -\phi(x,7/6)=\frac{\mathcal P(x)}{576X^2LM}.
 \tag{9}
\]
For example, the Casimir part gives \(-18LMG_n\), while the three terms of H
contribute respectively \(9X^2L^2M\),
\(1512X^2LS^3-168X^2LJ\), and
\(16X^2J^2-288X^2JS^3\). This is a sequence of scalar fraction cancellations,
not an expanded identity for a degree-nine numerator.

The source circuit (8) has degree nine. Its degree-nine products are never
expanded. Differentiate each of its six displayed products first, then collect
its derivative of degree eight. The exact result is
\[
\begin{aligned}
\mathcal P\prime(x)={}&69984 x^{8} + 471744 x^{7} + 407232 x^{6} - 1362852 x^{5}\\
&{}- 1536660 x^{4} + 664972 x^{3} + 753348 x^{2} + 222332 x\\
&{}+ 16452
\end{aligned}
\]
This polynomial has 9 monomials, total degree 8, and largest cleared coefficient 1536660.

Its positive shift is
\[
\begin{aligned}
4\mathcal P\prime(3/2+z)={}&279936 z^{8} + 5246208 z^{7} + 39078144 z^{6} + 151276464 z^{5}\\
&{}+ 330045480 z^{4} + 406467352 z^{3} + 261910740 z^{2} + 69853979 z\\
&{}+ 2612775
\end{aligned}
\]
This polynomial has 9 monomials, total degree 8, and largest cleared coefficient 406467352.

All coefficients are positive. Thus \(\mathcal P'(x)>0\) for x≥3/2.
Each of the six source derivatives has degree at most eight before collecting
it with the others. Every factor in (8), and the entire derivative polynomial,
is printed; no generated coefficient table or unnamed polynomial is a premise.

## 5. One scalar initial value

At x=8/5 on the same face, the four separate pieces of (2) have the exact values
and directed bounds
\[
\begin{aligned}
 G&=\frac{190801}{1843200}\le\frac{259}{2500},\\
 B/a&=\frac{171}{70}\ge\frac{6107}{2500},\\
 (S^3-2D)/K&=\frac{3244}{2465}\ge\frac{329}{250},\\
 D(D-S^3)/(aBK)&=-\frac{34438976}{14753025}\ge-\frac{1459}{625}.
\end{aligned}
 \tag{10}
\]
The last three bounds sum to \(3561/2500\). Therefore
\[
 -\phi(8/5,7/6)\ge
 \frac7{96}\frac{3561}{2500}-\frac{259}{2500}
 =\frac{21}{80000}>0.
 \tag{11}
\]
The largest integer required by an individual cross multiplication in (10)
is 21524663475, eleven digits. There is no common denominator for all the
original residual terms.

By (9), \(\mathcal P(8/5)>0\). Its positive derivative from Section 4 now
gives \(\mathcal P(x)>0\) throughout \([8/5,2]\), so
\(\phi(x,7/6)<0\). Combining this with (7) proves the unchanged claim (1).

## 6. The original norm-replacement caller still closes

The original central note's Section 3 uses exactly (1), its equation (18).
Both tests have
\[
 (F_j)_{uu}=-\frac{S^6}{8X^2}<0.
\]
The expanded numerator is
\(x^6+6x^5+15x^4+20x^3+15x^2+6x+1\), seven monomials and degree six.
Thus \((F_1)_u<0\) for every u≥3/4, at each point of the same shape rectangle.

For completeness, the other original factors used to pass from F1 to F0
also have small bounds there. We have
\[
 14/15\le D\le229/36<S^3,
 \qquad w_u=D(D-S^3)/K^2<0.
\]
For the lower bound, use \(a^2+1\ge2\), \(2x\ge16/5\),
\(b\le32/15\), and \(x-a\le1\). For the upper bound discard
\(-2b(x-a)\), then use \(a\le7/6,x\le2\).
Also, with \(T=K/(aB)\),
\[
 K-2aB\ge x^2+2x-\frac{13}{5}a^2-2ax+\frac85a
 \ge x^2-\frac x3-\frac{301}{180}\ge\frac{319}{900}>0.
\]
The middle expression decreases with a; its a derivative is
\(-26a/5-2x+8/5<0\). The last quadratic increases for x≥8/5.
These polynomials have at most five monomials and degree two.
Thus T>2, and the original exact relation gives
\[
 (F_1)_u=(F_0)_u-c(T-2)w_u>(F_0)_u.
\]
Both tests therefore decrease for u≥3/4. The caller can replace its actual
norm by the original ceiling \(u_\ell\), obtaining its equation (19), with
no new hypothesis and without changing the ceiling or logarithm treatment.

## 7. Expansion audit

All beta reductions use a quadratic in B with separately checked coefficients.
The nontrivial shape identity (5) has 36 collected monomials and degree eight;
each of its two separate product contributions has at most 38 monomials.
The shifted identity has 41 monomials and degree eight, with largest cleared
coefficient 5939696. Including the individual products before collection raises
that bound only to 7621908.

The terminal residual (8) is retained as a product circuit. Its first derivative
is the only expanded source identity on that face. Each source derivative and
its shift has at most nine monomials and degree eight; the largest coefficient
before collection is 488872854. The two-variable and univariate checks thus
stay within the requested size, degree, and coefficient limits. No Lean source
change or Lean resource measurement is claimed by this hand proof.
