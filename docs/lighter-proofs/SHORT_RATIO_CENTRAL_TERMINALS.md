# Central upper-ratio terminal signs

At the exact terminal curve
\[
x=13/6,\qquad b=b_+(13/6,a)=(309a+523)/384,
\qquad 1\le a\le4/3,                                  \tag{1}
\]
both duration-tangent tests F_0,F_1 in equations (4)--(6) of
[the central-ratio assembly](SHORT_RATIO_CENTRAL_COMPLETE.md) satisfy
\[
F_0<-1/6000,\qquad F_1<-1/6000.                       \tag{2}
\]
This note proves (2) at the original incoming norm. The tangent and
norm chords use the assembly's existing split at a=7/6. The
[algebra companion](SHORT_RATIO_CENTRAL_TERMINAL_ALGEBRA.md) prints all
source polynomials, the four small comparison polynomials and the
scalar recurrence used for their rounding bounds.

## 1. Two affine incoming upper bounds

At (1), the unchanged Gauss incoming ceiling is
\[
u_g=\frac{2401}{3200}+
\frac{225659}{54150(309a+139)}.                       \tag{3}
\]
It is strictly convex. The following positive differences prove the
needed endpoint upper roundings:
\[
\begin{aligned}
75962/100000-u_g(1)&=149/27075000,\\
75866/100000-u_g(7/6)&=1976863/432766800000,\\
75788/100000-u_g(4/3)&=1038791/238693200000.
\end{aligned}                                       \tag{4}
\]
The chord inequality for a convex function therefore gives
\[
u_g<u_L:=\frac{38269-288a}{50000}\quad(1\le a\le7/6),
\]
\[
u_g<u_H:=\frac{38206-234a}{50000}\quad(7/6\le a\le4/3).
\tag{5}
\]
The fixed-norm coefficient bounds in equation (16) of
[the beta proof](SHORT_RATIO_CENTRAL_BETA.md) give
\((F_0)_u=G_u>0\), \((F_1)_u=H_u>0\) on the entire enlarged
comparison domain. The tangent corrections do not depend on u.
Thus replacing (3) by the appropriate chord in (5) increases both
tests. This step keeps the direction of the norm comparison explicit.

## 2. A quadratic logarithm bound

Put y=tk, using the assembly's t=20/3-4a on the lower interval and
t=2 on the upper interval. Both y and t are positive. On the lower
interval,
\[
y=\frac{a(693a+523)(5-3a)}{8(36a^2+325)}<1,
\]
because, with c=a-1,
\[
8(36a^2+325)-a(693a+523)(5-3a)
=456+406c+4629c^2+2079c^3>0.                         \tag{6}
\]
On the upper interval,
\[
y=\frac{3a(693a+523)}{16(36a^2+325)}<1,
\]
since its denominator minus numerator is
\[
5200-1569a-1503a^2\ge436.                            \tag{7}
\]
For 0<y<=1, the second derivative of log y is at most -1.
Its tangent with this quadratic correction, based at y=4/5, gives
\[
\log y\le Q(y):=-\frac{488}{2187}
 +\frac54(y-4/5)-\frac12(y-4/5)^2.                  \tag{8}
\]
Here log(4/5)<-488/2187 follows by writing
\(\log((1+q)/(1-q))=2(q+q^3/3+q^5/5+\cdots)\) at q=-1/9;
all omitted terms are negative. Equivalently, the same inequality
follows by integrating the geometric series on [0,1/9].

Let f_{L0},f_{L1},f_{H0},f_{H1} denote the rational upper tests obtained
from the corresponding chord (5) and Q in (8). It remains to prove
these four functions below -1/6000.

## 3. A bounded eighth-order approximation

Use a centered variable z on each of the two existing intervals:
\[
a=13/12+z/12\quad(L),\qquad
a=5/4+z/12\quad(H),\qquad -1\le z\le1.              \tag{9}
\]
The companion supplies four explicitly printed integer polynomials
p_{Lj},p_{Hj} of degree at most eight. Their construction uses the
small source polynomials and the geometric-series recurrences there;
no combined high-degree numerator is cleared.

For each function f and its printed polynomial p, its first nine
Taylor coefficients at z=0 differ from the corresponding coefficients
of p/10^9 by less than 1/(2*10^9). Thus on either sign of z,
\[
\left|\sum_{k=0}^8(c_k-p_k/10^9)z^k\right|
<\frac9{2\cdot10^9}.                               \tag{10}
\]
The coefficient comparisons are nine scalar rational comparisons
per function, with their complete inputs and recurrence printed in
the companion. They are separate from the analytic remainder bound.

For that remainder the companion constructs positive power-series
majorants M_{Lj}(v), M_{Hj}(v). Their poles are outside v=5, and direct
substitution in the displayed formulas gives
\[
M_{L0}(5)<18,\qquad M_{L1}(5)<58,
\qquad M_{H0}(5)<9,\qquad M_{H1}(5)<9.               \tag{11}
\]
If m_k are the nonnegative coefficients of such an M, then the
absolute Taylor coefficients of f of order at least nine are bounded
by m_k. For |z|<=1,
\[
\left|\sum_{k\ge9}c_kz^k\right|
\le\sum_{k\ge9}m_k
\le5^{-9}\sum_{k\ge9}m_k5^k
\le5^{-9}M(5).                                     \tag{12}
\]
All these series converge absolutely, as follows from the explicit
positive denominator bounds at v=5. Equations (10)--(12) prove
\[
f_{ij}(z)<p_{ij}(z)/10^9+E_{ij}/5^9+9/(2\cdot10^9),
\quad(E_{L0},E_{L1},E_{H0},E_{H1})=(18,58,9,9).
\tag{13}
\]
This larger, simple geometric bound suffices; no exact tail coefficient
list is needed.

## 4. Signs of the four printed polynomials

For the lower first polynomial,
\[
p_{L0}''=-1617022+3066612z-1707468z^2
-602280z^3-216360z^4-62244z^5-15512z^6.              \tag{14}
\]
For z<=0, this is at most -1617022+602280+62244<0.
For z>=0, its first three terms equal
\[
-1707468(z-9/10)^2-34152z/5-5849323/25<0,
\tag{15}
\]
and the remaining terms are nonpositive. Hence p_{L0} is concave.
Since p_{L0}'(1)=2958>0, it is increasing throughout [-1,1], so
\[
p_{L0}(z)\le p_{L0}(1)=-193318.                     \tag{16}
\]

For the lower second polynomial, discard the negative even powers
of degree at least four. The three potentially positive odd terms
are bounded above by (6673+24329+1166)z^2. Consequently
\[
p_{L1}(z)\le-316335+832241z-1478574z^2<-199000.
\tag{17}
\]
The last inequality is the quadratic square-completion criterion
\[
4\cdot1478574(316335-199000)-832241^2=1328839079>0.
\tag{18}
\]

For the upper two polynomials, direct differentiation gives
\[
p_{H0}''=765740+388854z-237768z^2+14660z^3-180z^4+42z^5
\ge124236>0,                                        \tag{19}
\]
\[
p_{H1}''=2533540-1709832z+250044z^2-24340z^3+2310z^4-210z^5
\ge799158>0.                                        \tag{20}
\]
For (19), bound each nonconstant term below by minus its coefficient
magnitude. For (20), retain the nonnegative even terms and bound the
three odd terms in the same way. Convexity therefore gives
\[
\begin{aligned}
p_{H0}(z)&\le\max\{-193377,-1673381\}=-193377,\\
p_{H1}(z)&\le\max\{-1106554,-2672010\}=-1106554.
\end{aligned}                                       \tag{21}
\]
Combining (13), (16), (17) and (21), the weakest of the four scalar
upper bounds is already
\[
-199000/10^9+58/5^9+9/(2\cdot10^9)<-1/6000.          \tag{22}
\]
The other three comparisons use their respective values in (13) and
are stronger. This proves (2), including both endpoints of the shape
split, after the norm and logarithm upper comparisons.

## 5. Source and size boundary

The source is the duration-tangent pair in the assembly, at its exact
beta and x endpoint. The proof changes the incoming norm only by the
proved upper chords, and makes no outgoing-floor assumption.
It uses one variable after those prior reductions. The primitive
source identities have degree at most four; the four comparison
polynomials have degree at most eight and at most nine monomials.
Every printed integer coefficient has at most eleven digits.
Scalar Taylor-coefficient checks use rational arithmetic, with the
coefficient error explicitly included in (10); an unprinted exact
Taylor polynomial is not a sign premise.

No Lean source, compilation, Lake, typechecking or CI is involved.
