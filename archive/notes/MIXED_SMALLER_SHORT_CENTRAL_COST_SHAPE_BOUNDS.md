# Analytic bounds for the central short-shape cost

Date: 2026-11-08 UTC. Conditional scalar hand lemmas for the
small-shape completion-cost argument. No ratio or displacement
restriction is derived here.

Assume
\[
2\le x\le13/6,\quad0\le d\le1/19,\quad13/5\le\eta\le3,
\qquad\alpha=1+\eta d,\quad\beta=x(1+d).
\tag{1}
\]
Put
\[
S=x+1,\quad B=\alpha+\beta,\quad
R=\frac{x-1}{x+1},\quad T=\frac{\beta-\alpha}{\beta+\alpha},
\quad U_1=\frac{3+R^2}{4},\quad U_2=\frac{3+T^2}{4},
\]
\[
A=U_1/U_2-1,\quad Q=2\beta x-x-\alpha\beta,
\quad Z=\frac{2U_1Q}{x(x+2)}-R-(1+A)T.
\tag{2}
\]
The last quantity is exactly -sqrt(3)*h at the central scalar scale.
Indeed the scale-independent part of sqrt(3)*h simplifies to
\[
\frac{(\beta x-\alpha)[(x+2)\alpha+(2x+1)\beta]}
 {S^2(\alpha^2+\alpha\beta+\beta^2)}
 =\frac{(R+T)(3+RT)}{3+T^2}=R+(1+A)T.
\tag{3}
\]

## 1. Shape and incoming-norm bounds

The angle coordinates satisfy
\[
1/3\le R\le7/19,\qquad9/31\le T\le R,
\qquad0\le A<1/100.
\tag{4}
\]
The ratio beta/alpha decreases with d and eta, and increases with x.
Its minimum is 20/11, giving T>=9/31. The inequality beta<=alpha*x
proves T<=R.

Since U(1/(1+y)) increases for y>1, A increases with d and eta.
At their upper endpoints it becomes
\[
a(x)=\frac{x(10x^2-11)}{(x+1)^2(100x^2+110x+121)}.
\]
Its derivative has positive denominator and numerator
\[
-(10x+11)(100x^4-210x^3-440x^2-231x+121)>0.
\]
For the sign, on [2,9/4] the first two terms in the last parenthesis
are at most 15*12, and the others are at most -440*4-231*2+121.
Thus
\[
A\le a(13/6)=25233/2692699<1/100.
\]

Let u be the original incoming secant Sec(1,x,beta). It satisfies
\[
u\le3/4+R^2/12.
\tag{5}
\]
The incoming integral over [1,x] has mean at most R^2/12, by the
[incoming norm lemma](MIXED_SMALLER_SHORT_INCOMING_NORM_BOUND.md).
On [x,beta], (s-x)/(s+x)<=1/39<R/2, so its corresponding mean is
at most R^2/16. Their weighted average proves (5).

A convenient, sharper lower bound is quadratic in d. Define
\[
H_R=3R^2+10R+10,
\]
\[
\boxed{
u_q=\frac34+\frac{H_R}{15(2+R)^3}
 \left\{R^2-\frac{R(1+R)}2d
                  +\frac{19(1+R)^2}{84}d^2\right\}<u.}
\tag{6}
\]
Here is a direct positive-integral proof. For V(x)=Sec(1,x,x),
\[
V(x)-3/4=\frac{R^2}{2}
             \int_0^1\frac{t(1-t)}{1+Rt}\,dt.
\tag{7}
\]
This identity also follows by integrating and using the displayed
logarithmic formula for V in the incoming norm lemma. Pair t with
1-t, and set a=1+R/2. The geometric identity for
1/[a^2-R^2(t-1/2)^2] gives
\[
V(x)-3/4>
\frac{R^2}{12a}+\frac{R^4}{240a^3}
=\frac{R^2H_R}{15(2+R)^3}.
\tag{8}
\]
The two moments used here are 1/6 and 1/120. The discarded remainder
is positive because R>0. Discarding the positive incoming tail after
x gives u-3/4>(x-1)[V(x)-3/4]/(beta-1).
Finally put z=xd/(x-1)<=2/19 and use
\[
\frac1{1+z}=1-z+\frac{z^2}{1+z}
 \ge1-z+\frac{19}{21}z^2.
\]
Substitution in (8) proves (6). In particular uq>3/4.

## 2. Explicit central-shear bounds

Define
\[
Z_0=\frac{2x(x-1)^2}{(x+1)^2(x+2)}
    =\frac{2R^2(1+R)}{3-R},
\]
\[
\boxed{Z_L=Z_0(1+11d/2),\qquad
Z_U=Z_0+(x/2-1/6)d-3d^2/2.}
\tag{9}
\]
Then throughout (1),
\[
\boxed{0<1/9\le Z_L\le Z\le Z_U
             \le20063/108300<1/5.}
\tag{10}
\]
The non-strict 1/9 bound includes x=2,d=0.

### 2.1. A uniform second derivative

At fixed x and eta, put M=x+eta, L=2x(eta-1), so that
\[
T'= -L/B^2,\quad T''=2LM/B^3.
\]
For g(t)=t/(3+t^2),
\[
g'(t)=\frac{3-t^2}{(3+t^2)^2},\quad
 g''(t)=-\frac{2t(9-t^2)}{(3+t^2)^3}.
\]
The scale-independent term in (3) is R+(3+R^2)g(T). Its second
d derivative is
\[
\frac{(3+R^2)2LM}{B^3}g'(T)
 \left\{1-\frac{L}{MB}
                \frac{T(9-T^2)}{9-T^4}\right\}.
\tag{11}
\]
We bound its three positive factors explicitly. First
\[
g'(T)\ge\frac{186637}{640712}>29/100.
\]
Next L/(MB)<=8/15: replace B by x+1, increase eta to 3,
and then decrease x to 2. Also
\[
\frac8{15}\frac{9(7/19)}{9-(7/19)^4}
=\frac{144039}{731555}<1/5.
\]
Thus the braces in (11) exceed 4/5.

For the remaining factor write
G=4x(eta-1)(x+eta)/B^3. It decreases with d and x and increases
with eta on (1). For x, the logarithmic derivative has numerator
\[
-x^2+2(1-\eta)x+\eta+d(x+\eta)(\eta-x)
 \le-37/5+31/114<0.
\]
For eta, its logarithmic derivative is
1/(eta-1)+1/(x+eta)-3d/B>1/2-1/19>0.
Consequently
\[
(3+R^2)G\ge\frac{28}{9}G(13/6,13/5,1/19)
 =\frac{1785123340}{346503909}>5.
\]
Equation (11) is therefore greater than 29/25.
The other part of Z has second derivative
\[
-\frac{(3+R^2)\eta}{x+2}\le-728/375.
\]
We have proved
\[
\boxed{Z_{dd}<-1163/375<-3.}\tag{12}
\]

### 2.2. The upper bound

At d=0, Z=Z0 and
\[
Z_d(0)=\frac{(x-1)
\{-\eta x^3+\eta x^2+4\eta x+2\eta
           +4x^4+9x^3+11x^2+4x+2\}}
 {(x+1)^2(x+2)(x^2+x+1)}.
\tag{13}
\]
Its eta derivative is positive, since x^2-2x-2<0 on the interval.
At eta=3 it is at most x/2-1/6. After clearing the positive
denominator, the difference has numerator, with h=x-2,
\[
12-69h+80h^2+159h^3+93h^4+26h^5+3h^6\ge1/2.
\]
Taylor's formula with (12) now proves Z<=ZU. The function ZU
increases with x and d in the stated rectangle. Its upper endpoint
is 20063/108300, proving the upper part of (10).

### 2.3. The lower bound

At fixed x,beta, Z is concave in alpha. Its non-affine contribution
is the negative of (3), whose second alpha derivative equals
\[
\frac{4\beta(3+R^2)}{B^3}
 \frac{9-9T-9T^2+T^3}{(3+T^2)^3}>0.
\]
The numerator is positive already from T<=3/8. Hence Z is concave
in eta as well. It suffices to use eta=13/5 and eta=3.
For either endpoint, (12) makes Z concave in d, so it suffices to
check Z>=Z0(1+11d/2) at d=0 and d=1/19. The first is equality.

At d=1/19, the two differences have the following positive
denominators and complete numerator polynomials in h=x-2:
\[
\begin{array}{c|l}
\eta&\text{denominator}\\ \hline
13/5&361(x+1)^2(x+2)(625x^2+675x+729)\\
3&361(x+1)^2(x+2)(100x^2+110x+121)
\end{array}
\]
\[
\begin{aligned}
P_{13/5}(h)={}&341468-595453h-2459761h^2-2058844h^3
                    -682975h^4-83125h^5,\\
P_3(h)={}&49020-107737h-410045h^2-337211h^3
                    -110420h^4-13300h^5.
\end{aligned}
\]
They decrease on [0,1/6], and their right endpoint values are
1273940345/7776 and 4380226/243. Both are positive. Concavity first
in d and then in eta proves the lower bound in (10).
