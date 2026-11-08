# Central displacement tests increase with the outer short margin

Date: 2026-11-08 UTC. Explicit analytic scalar lemma. Its hypotheses
are stated below; this note does not assert the still-open actual
ratio or displacement restrictions. No coefficient-minimum certificate
is used. The two residual signs themselves remain separate obligations.

## 1. Domain and two scalar tests

Assume

\[
2\le x\le13/6,\qquad
108/95\le\alpha,\qquad \alpha^2\le x(x+2)/6,
\]
\[
20x/19\le\beta\le
\min\{2\alpha,\ x+5x(\alpha-1)/13\}.
\tag{1}
\]

Put

\[
S=1+x,\quad K=x(x+2)+\alpha^2,\quad
q=\alpha^2/K,\quad p=\alpha/(\alpha+\beta),\quad T=p/q,
\]
\[
D=\alpha^2+2\alpha\beta+1+2x-2\beta x,
\quad \lambda=S^2/K,\quad d=D/K,\quad k=5\alpha-1.
\]

Use the explicit rational incoming ceiling

\[
g(x)=\frac{(x-1)^2(71x^2+48x+1)}
 {96xS(13x^2+14x+3)},
\qquad
u=\frac34+\frac{(x-1)g(x)+(\beta-x)/5808}{\beta-1}.
\tag{2}
\]

At central scale define

\[
v=1-S^{-1}+S^{-2},\quad
E=S(u-1)+3S^{-1}-S^{-2},
\]
\[
w=\lambda^2v+d^2u-d\lambda E,\qquad E_L=2du-\lambda E,
\quad y=2/T,
\]
\[
J=(u-1)/p+p+1-q-E_L+\log(2/T),
\]
\[
n_0=2+\frac{4(4-3y)}k,\qquad n_1=T+\frac4k,
\qquad F_i=J+n_i(w-3/4).
\tag{3}
\]

These are the two duration tests in
[the displacement-weight reduction](MIXED_SMALLER_SHORT_DISPLACEMENT_WEIGHT_REDUCTION.md):
the first is its value at tau=2; the second is its endpoint tangent
upper value. The logarithm in this lemma is exact. Any later rational
majorant is inserted only after the monotonic comparison below.

**Theorem.** At fixed x and alpha throughout (1),

\[
\boxed{(F_0)_\beta>7/1500>0,
\qquad (F_1)_\beta>1/1200>0.}
\tag{4}
\]

Thus either test can be raised to the upper beta endpoint of any
interval contained in (1). This transfers only a scalar inequality.
It does not transfer an actual root, outgoing floor, Casimir cap or
physical cost to that endpoint.

## 2. Two incoming-norm bounds

The elementary central-scale bound

\[
\alpha\le(5x+4)/12\le89/72
\tag{5}
\]

follows by squaring: the squared first upper bound exceeds
x(x+2)/6 by (x-4)^2/144. The beta ceiling in (1) then gives

\[
0\le(\beta-x)/x\le85/936<1/11.
\]

The Gauss estimate at beta=x bounds V(x)-3/4 by g(x). The positive
incoming integral split at x therefore proves that (2) bounds the
original incoming secant above: its tail is at most
(beta-x)^3/(48x^2), and hence at most (beta-x)/5808.
This uses the proved
[Gauss incoming ceiling](MIXED_SMALLER_SHORT_GAUSS_INCOMING_CEILING.md).

We shall also use

\[
u>3/4+13/2000,\qquad -7/1000<u_\beta<0.
\tag{6}
\]

For the first inequality, apply Jensen's inequality to the convex
function z -> z^{-2} with weight (x-s)^2 on [1,x]. Its weighted
mean of s is (x+3)/4. Consequently

\[
V(x)-3/4\ge\frac{4(x-1)^2}{3(5x+3)^2},\qquad
u-3/4\ge\frac{4(x-1)^3}{3(5x+3)^2(\beta-1)}.
\]

In the latter denominator use

\[
\beta-1\le x-1+5x(5x-8)/156.
\]

Subtracting 13/2000 from the resulting lower bound has the positive
denominator
2000(5x+3)^2(25x^2+116x-156). With h=x-2, its numerator is exactly

\[
29328+476008h+770835h^2+303550h^3-8125h^4>0.
\tag{7}
\]

Here 0<=h<=1/6, so the only negative term is less than 7 in
absolute value. The denominator is positive because
25x^2+116x-156>=176.

For the derivative, (2) gives

\[
-u_\beta=\frac{(x-1)(g(x)-1/5808)}{(\beta-1)^2}>0.
\]

The positivity follows from the preceding Jensen bound. Also

\[
g(x)<\frac{23(x-1)^2}{320S^2}:
\]

after clearing positive factors its numerator difference is
187h^3+898h^2+1065h+24. Thus

\[
-u_\beta<\frac{23(x-1)^3}{320S^2(20x/19-1)^2}.
\]

The last function increases on the interval: its logarithmic
derivative has the sign of -20x^2+81x-55, a concave quadratic
positive at both endpoints. Its value at x=13/6 is
23667/3410560<7/1000. This proves (6).

## 3. Bounds for transport and pairing

The following bounds will be used together:

\[
\boxed{1/6<d<1/3,\quad \lambda S>20/7,
\quad E_L<3/10,\quad w<31/40.}
\tag{8}
\]

### 3.1. The bounds for d

A useful sharper upper bound for alpha is

\[
\alpha\le\frac{3x+2}{4\sqrt3}
 <\frac{13(3x+2)}{90}.
\tag{9}
\]

The first squared difference is (x-2)^2/48; the second uses
sqrt(3)<26/15. In 3D-K use beta>=20x/19, (9), and the original
square bound for alpha. This gives

\[
3D-K\le\frac{-242x^2+370x+171}{57}<0.
\tag{10}
\]

The quadratic is decreasing on x>=2 and equals -57 at x=2 before
division. This proves d<1/3.

For the lower bound replace beta by x+5x(alpha-1)/13 in 6D-K.
Its coefficient 12(alpha-x) is negative, so this gives a lower
bound. The resulting derivative in alpha is

\[
10\alpha+(12x/13)(10\alpha+8-5x)>0.
\]

It therefore suffices to take alpha=108/95, at which that beta
upper bound is exactly 20x/19. The remaining expression is a
concave quadratic in x. Its values at x=2 and x=13/6 are,
respectively, 12014/1805 and 81199/64980, both positive. Thus
6D-K>0.

The scale square bound also gives

\[
\lambda S\ge\frac{6S^3}{7(S^2-1)}>20/7.
\]

The last numerator sign, with h=S-3, is
3S^3-10S^2+10=1+21h+17h^2+3h^3>0.

### 3.2. The outer pairing bound

At u=3/4,

\[
E_L^{(0)}=\frac{6D+S^3-12S+4}{4K}<5/16.
\tag{11}
\]

To verify this, the numerator of
16K(E_L^{(0)}-5/16) is

\[
19\alpha^2+48\beta(\alpha-x)+4x^3+7x^2+2x-4.
\]

Insert the square bound for alpha, (9), and beta>=20x/19. The
resulting upper bound is

\[
\frac{(x-2)(456x^2-1193x+228)}{114}\le0.
\]

The quadratic factor is negative: x^2<=(13/6)x makes it at most
-205x+228<0. At x=2 the strict inequality in (9) supplies
strictness in (11).

Since (E_L)_u=2d-lambda*S<-46/21, (6) improves (11) to

\[
E_L<5/16-(46/21)(13/2000)<3/10.
\tag{12}
\]

### 3.3. The outer norm bound

The lower bound alpha>=108/95 and S<=19/6 give lambda<35/36:
indeed S^2<35[(108/95)^2-1]. From beta>=20x/19 and (9),

\[
0<D\le\overline D(x)
 :=\frac{-351x^2+1006x+342}{342}.
\tag{13}
\]

This upper bound is positive on the interval and decreases there.
Moreover D<S^2, by the identity
D-S^2=(alpha-x)(alpha+x+2beta). Put z=D/S^2 and
zbar=Dbar/S^2. Since w decreases with u on this interval,

\[
w\le\lambda^2\{v+(3/4)z^2-zE^{(0)}\},
\quad E^{(0)}=-S/4+3/S-1/S^2.
\]

The expression in braces is convex in z, so it is at most the
larger of its values at 0 and zbar. The first is v<4/5<819/1000.
The second is also less than 819/1000. A complete polynomial
verification of this last small bound is

\[
\begin{split}
&S^4\{819/1000-v-(3/4)\overline z^2+
                       \overline z E^{(0)}\}\\
={}&\frac{27653}{27000}
 -\frac{357203}{64125}h
 -\frac{16397053}{9747000}h^2
 +\frac{9126797}{3249000}h^3
 +\frac{10586237}{6498000}h^4
 +\frac{39}{152}h^5>0,
\end{split}
\tag{14}
\]

where h=x-2 in [0,1/6]. The constant exceeds 1, the absolute
linear coefficient is below 28/5, and the absolute quadratic
coefficient is below 17/10. All other coefficients are positive.
Thus the displayed value exceeds
1-14/15-17/360=7/360>0.
Consequently

\[
w<(35/36)^2(819/1000)=4459/5760<31/40.
\tag{15}
\]

Every coefficient in the only quintic used here is printed. Its sign
uses the three displayed elementary bounds, not an extracted
coefficient-minimum claim.

## 4. Duration coefficients and the exact beta derivative

The assumptions give

\[
1/3\le p<1/2,\qquad 3/4<y\le6/7,
\qquad 7/3\le T<8/3.
\tag{16}
\]

For the lower y bound, use alpha>=108/95 and beta>=20x/19 in
8alpha(alpha+beta)-3K. This expression increases with alpha;
at the stated lower endpoints it is the concave quadratic
`-3(1805x^2-2150x-3888)/1805`, with values `2904/1805`
and `2623/21660` at x=2 and x=13/6. The upper y bound uses q<=1/7
and p>=1/3. In particular

\[
3<n_0<7/2,\qquad 3<n_1<53/15,
\]
\[
-3/4<(n_0)_\beta<0,
\qquad -5/6<(n_1)_\beta<0.
\tag{17}
\]

For completeness, k>=89/19 and k<=373/72. Hence
40/(7k)>1 and 7/k<=133/89<3/2 give the n0 bounds.
For n1, use T+4/k<=8/3+76/89=940/267<53/15 and
T+4/k>=7/3+288/373>3. Its derivative is -T/(alpha+beta),
with absolute value below 190/231<5/6. The n0 derivative is
-24alpha/(Kk), whose absolute value is below 190/267<3/4.

At fixed x and alpha, direct differentiation of (3) gives

\[
\boxed{
(F_i)_\beta=d_\beta(n_iE_L-2u)
 +u_\beta\{p^{-1}+\lambda S-2d+n_i d(d-\lambda S)\}
 +(n_i)_\beta(w-3/4)+\frac{u-U(p)}\alpha.}
\tag{18}
\]

Here U(p)=1-p+p^2. The last term uses the cancellation
(log(2/T))_beta=1/(alpha+beta); this is why the exact logarithm
is retained during this derivative comparison.

The remaining bounds in (18) are short:

\[
-d_\beta=2(x-\alpha)/K>7/40.
\tag{19}
\]

Indeed 80(x-alpha)-7K is at least
(-49x^2+182x-160)/6, a concave quadratic whose endpoint values
are 4/3 and 155/216.

Since d in (1/6,1/3), n_i>3, lambda*S<=19/6 and p^{-1}<=3,
the expression multiplying u_beta in (18) is at most

\[
3+\lambda S-2d+3d(d-\lambda S)
\le37/6-(23/2)d+3d^2\le13/3.
\tag{20}
\]

It therefore contributes at least -91/3000, by (6).
Also

\[
\frac{u-U(p)}\alpha
\ge-\frac{(p-1/2)^2}\alpha
\ge-\frac{95}{3888}>-1/40.
\tag{21}
\]

For i=0, (8), (17), and (19) bound the first term of (18)
below by (7/40)(3/2-(7/2)(3/10))=63/800. Its third term
is bounded below by -3/160, because w-3/4<1/40. Hence

\[
(F_0)_\beta>
63/800-91/3000-1/40-3/160=7/1500.
\]

For i=1 the corresponding first bound is
(7/40)(3/2-(53/15)(3/10))=77/1000; the third term is
at least -1/48. Thus

\[
(F_1)_\beta>
77/1000-91/3000-1/40-1/48=1/1200.
\]

This proves (4). The argument has used explicit derivative identities,
two quadratic endpoint comparisons, one fully printed quartic, and
one fully printed quintic. It neither assumes a numerical derivative
bound nor requires a coefficient sign table.
