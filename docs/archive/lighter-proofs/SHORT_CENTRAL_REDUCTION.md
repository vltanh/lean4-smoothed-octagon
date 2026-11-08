# Central S1: norm and beta reduction with the original norm curve

This note uses the original central functions in
[MIXED_SMALLER_SHORT_LOW_RATIO_CENTRAL_HAND_SIGN](../../archive/notes/MIXED_SMALLER_SHORT_LOW_RATIO_CENTRAL_HAND_SIGN.md).
It replaces its beta-derivative certificate and provides the quantitative norm bound needed by the new shape proof.
No beta-dependent norm ceiling is frozen during a beta comparison.

Write \(S=x+1\), \(X=x(x+2)\), \(Z=35x+13\), \(K=X+a^2\), \(B=a+b\),
\(c=7/96\), and
\[
 D=a^2+2ab+1+2x-2bx,\quad D_0=(a+1)(2x+1-a),\quad \eta=x-a,
\]
\[
 E=S^3(u-1)+3S-1,\quad M=S^2(S^2-S+1),\quad
 w=(M+uD^2-DE)/K^2,\quad E_L=(2Du-E)/K,
\]
\[
 \Gamma=(4Mu-E^2)/(16X^2),\quad
 R_0=(u-1)B/a+a/B+1-a^2/K-E_L+2(w-3/4),
\]
\[
 R_1=(u-1)B/a+a/B+1-a^2/K-E_L+K(w-3/4)/(aB),\quad
 F_j=\Gamma-c\{R_j+\log(2aB/K)\}-9193/50000.
\]
The three-variable source D has degree two. Its use in the displayed products requires no three-variable expansion of higher degree.

All reductions below hold on the containing rectangle
\[
 8/5\le x\le2,\quad 1\le a\le7/6,\quad
 b=x+C(a-1),\quad1/2\le C\le4/5,\quad3/4\le u\le19/25.
 \tag{1}
\]
In particular \(x\le b\le ax\), \(0<D<K\), \(D<S^3\), and \(T=K/(aB)>2\).
The original note's elementary bounds \(14/15\le D\le229/36\) and
\(K-2aB\ge319/900\) prove the needed signs on all of (1).

## 1. A quantitative norm derivative

The [small norm proof](SHORT_CENTRAL_NORM_MONOTONICITY.md) proves \((F_1)_u<0\) at \(u=3/4\).
Both norm derivatives decrease in u because their only quadratic term comes from \(-E^2/(16X^2)\).
Also
\[
 (F_1)_u-(F_0)_u=-c(T-2)w_u>0,\qquad w_u=D(D-S^3)/K^2<0.
\]
We now establish the other half of the uniform estimate
\[
 \boxed{-1/5<(F_0)_u\le(F_1)_u<0.}\tag{2}
\]

Put \(d=D/K\), \(L=S^3/K\). Direct differentiation gives
\[
 (F_0)_u=\Gamma_u-cH_0,\qquad H_0=B/a+L(1-2d)+2d(d-1).
\]
Here \(B/a\le S\), \(L\le S\), and \(0<d<1\). Define
\[
 d_0=\frac{2+4x-2x^2}{S^2}>0.
\]
Since \(b\le ax\), \(D\ge D_m=(1+2x)(a^2+1)-2ax^2\).
The complete small comparison identity is
\[
 D_mS^2-(2+4x-2x^2)K
 =(a-1)\{a(2x^3+7x^2-1)-(2x^4+2x^3-5x^2+1)\}.
\]
The brace is at least \(2(6x^2-x^4-1)\ge14\): the last quadratic in \(x^2\) is concave and its endpoint values on \([64/25,4]\) are at least seven. Thus \(d\ge d_0\).

If \(d\ge1/2\), then \(H_0\le S\le3\). Otherwise the expression
\(2S-2(S+1)d+2d^2\) decreases in d, giving
\[
 H_0\le H(x)=\frac{2(x-1)(3x+1)(x^3+5x^2-x-1)}{S^4}.
\]
The two complete derivative numerators used for the ensuing scalar bounds are
\[
 H'(x)=\frac{2(3x^5+15x^4+66x^3-30x^2-21x-1)}{S^5}>0,
\]
\[
 \Gamma_u\big|_{u=19/25}=G(x)
 =\frac{S^2(6x^4+24x^3+11x^2-51x+6)}{200X^2},
\]
\[
 G'(x)=\frac{S(12x^6+72x^5+144x^4+121x^3+39x^2+78x-24)}{200x^3(x+2)^3}>0.
\]
Both positivity claims already hold for x≥1: in the first numerator, the three adverse terms are bounded by \(52x^3\), and in the second \(78x-24>0\).
Since \(\Gamma_u\ge G\), the only split needed is x=9/5.
The exact scalar inequalities
\[
 G(8/5)>9/100,\quad G(9/5)>127/1000,\quad
 H(9/5)<13/4,\quad H(2)=350/81<13/3
\]
prove (2): use \(9/100-c(13/4)>-1/5\) on the first piece and
\(127/1000-c(13/3)>-1/5\) on the second. The alternative \(H_0\le3\) gives \(9/100-3c>-1/5\).

## 2. Fixed-norm beta derivatives have a uniform positive lower bound

Let \(r_j=R_j+\log(2aB/K)\). Differentiating gives the exact sources
\[
 (r_0)_b=(u-1)/a+b/B^2+4\eta\{E+u(K-2D)\}/K^2,
\]
\[
 (r_1)_b=(u-1)/a+4u\eta x/(aK)+1/B-Q_0/B^2,
\]
\[
 Q_0=\frac{a^2K+M+uD_0^2-D_0E-3K^2/4}{aK}.
\]
These derivatives increase in u. For j=0 this follows from
\(1/a+4\eta(K+S^3-2D)/K^2>0\), since \(S^3>2D\).
For j=1 their u derivative is \(H_b=\alpha+\gamma/B^2>0\), as proved by the explicit division in Section 2 of the norm note.

They also increase in b. For j=0,
\[
 (r_0)_{bb}=(a-b)/B^3+16u\eta^2/K^2>0.
\]
Indeed \(B^3-27a^2(b-a)=(b-2a)^2(b+7a)\ge0\), while
\(18a(x-a)>K\). The latter is the separately concave quadratic
\(18ax-19a^2-x^2-2x>0\); its four rectangle-corner values are positive.
For j=1, \((r_1)_{bb}=(2Q_0-B)/B^3>0\), because \(B\le3a\) and \(Q_0>3a/2\).
The last claim follows from the first of the three small identities below. Q0 decreases in u because \(D_0(D_0-S^3)<0\), so use u=19/25 there.

Put \(A=a-1\in[0,1/6]\), \(z=x-8/5\in[0,2/5]\).
Here are the three full sign polynomials, with their positive denominators:
\[
 Q_0\big|_{u=19/25}-3a/2=\frac{P_Q(A,z)}{625\cdot100aK},
\]
\[
 (r_0)_b\big|_{b=x,u=3/4}-1/40
 =\frac{P_0(A,z)}{15625\cdot40a(a+x)^2K^2},
\]
\[
 (r_1)_b\big|_{b=x,u=3/4}-1/40
 =\frac{P_1(A,z)}{625\cdot40a(a+x)^2K}.
\]
\[
\begin{aligned}
P_Q={}&- 30625 A^{4} - 190000 A^{3} z - 426500 A^{3}\\
&{}- 15000 A^{2} z^{3} - 52000 A^{2} z^{2} - 918700 A^{2} z\\
&{}- 1566990 A^{2} + 30000 A z^{4} + 252000 A z^{3}\\
&{}+ 883800 A z^{2} + 189320 A z - 1216532 A\\
&{}+ 75625 z^{4} + 664000 z^{3} + 2153100 z^{2}\\
&{}+ 2526940 z + 739671
\end{aligned}
\]
\[
\begin{aligned}
P_0={}&- 15625 A^{7} - 31250 A^{6} z + 1559375 A^{6}\\
&{}- 46875 A^{5} z^{2} + 9287500 A^{5} z + 24964375 A^{5}\\
&{}+ 562500 A^{4} z^{3} - 3125 A^{4} z^{2} + 40826250 A^{4} z\\
&{}+ 92243375 A^{4} + 578125 A^{3} z^{4} - 10425000 A^{3} z^{3}\\
&{}- 69951250 A^{3} z^{2} - 49308000 A^{3} z + 85020925 A^{3}\\
&{}- 656250 A^{2} z^{5} - 4109375 A^{2} z^{4} - 54750000 A^{2} z^{3}\\
&{}- 243903750 A^{2} z^{2} - 326929750 A^{2} z - 81196955 A^{2}\\
&{}- 640625 A z^{6} + 287500 A z^{5} + 30509375 A z^{4}\\
&{}+ 91420000 A z^{3} + 32772125 A z^{2} - 111032140 A z\\
&{}- 65572299 A - 796875 z^{6} - 1181250 z^{5}\\
&{}+ 23571875 z^{4} + 102382500 z^{3} + 156120875 z^{2}\\
&{}+ 94531710 z + 18520541
\end{aligned}
\]
\[
\begin{aligned}
P_1={}&- 625 A^{5} - 1250 A^{4} z - 11375 A^{4}\\
&{}- 1250 A^{3} z^{2} + 2250 A^{3} z - 24450 A^{3}\\
&{}+ 5000 A^{2} z^{3} - 88500 A^{2} z^{2} - 214100 A^{2} z\\
&{}- 145520 A^{2} - 13125 A z^{4} - 25250 A z^{3}\\
&{}- 153350 A z^{2} - 308090 A z - 158401 A\\
&{}+ 36875 z^{4} + 233500 z^{3} + 425650 z^{2}\\
&{}+ 270460 z + 44699
\end{aligned}
\]

For a direct hand sign, discard positive A terms and replace A by 1/6 only in adverse A monomials. The resulting coefficientwise lower bounds are
\[
 P_Q>490000+2500000z+2150000z^2+660000z^3+75000z^4>0,
\]
\[
 P_1>14000+210000z+390000z^2+220000z^3+34000z^4>0,
\]
\[
 P_0>5000000+60000000z+140000000z^2+100000000z^3
       +23000000z^4-1200000z^5-1000000z^6>0.
\]
For the last inequality, the two negative terms cost at most \(640000z^4\).
These are individual degree-five or degree-seven identities, with at most 35 monomials and coefficients at most 326929750.
The two monotonicities now prove
\[
 \boxed{(r_0)_b>1/40,\qquad(r_1)_b>1/40.}\tag{3}
\]

## 3. Follow the norm ceiling, then increase beta

Retain exactly the original curve
\[
 u_\ell(x,b)=3/4+\frac{(x-1)^2(b+15x-16)}{8SZ(b-1)},\qquad
 (u_\ell)_b=-\frac{15(x-1)^3}{8SZ(b-1)^2}.
\]
It lies in \([3/4,19/25]\): since b≥x, its increment is at most
\(2(x-1)^2/(SZ)\le2/249<1/100\).
Also
\[
 |(u_\ell)_b|\le\frac{15(x-1)}{8SZ}\le5/664.
\]
For completeness, the two rational functions used in these scalar comparisons increase up to x=2: their derivative numerators, after positive factors are removed, are respectively \((x-1)(59x+37)\) and \(-35x^2+70x+61\).
Combining (2) and (3) proves the total-derivative bound
\[
 \boxed{\frac d{db}F_j(x,a,b,u_\ell(x,b))
 <-\frac7{3840}+\frac1{664}=-\frac{101}{318720}<0.}\tag{4}
\]
The original incoming-norm estimate supplies u≤u_l. Norm monotonicity therefore first gives \(F_j(u)\ge F_j(u_\ell)\), and (4) then permits increasing beta to \(b_+=x+(10/13)(a-1)\).
This exactly preserves the ceiling's beta dependence.
For the second test alone, the stronger convenient reduction
\(F_1(u)\ge F_1(19/25)\) followed by fixed-norm beta monotonicity is also valid.
