# A uniform small-parameter exclusion for nonshort continuation

Date: 2026-11-07. Hand inequality with an exact coefficient certificate
and independent internal review. No Lean, Lake, typechecking or CI.

## Statement

Use the three maximal-parameter charts of
[MIXED_NONSHORT_BLOWUP_REDUCTION](MIXED_NONSHORT_BLOWUP_REDUCTION.md).
Every point satisfying their retained actual geometry and

\[
0\le\epsilon\le\frac1{32}
\]

has `Phi>0`. It therefore cannot satisfy the necessary upper-norm root
condition `Phi<=0`. The statement includes the whole zero-duration
shape fibre and all chart ties. It is independent of the next-switch
alternative, so it excludes the same corner in both branches.

This lemma does not exclude the complementary region `epsilon>=1/32`
or close M2 by itself.

## 1. Notation and elementary geometric bounds

Write

\[
T=a+c,\quad K=a^2+4,\quad \delta_i=\epsilon l_i,
\quad 0\le l_i\le1,\quad\max(l_0,l_1,l_2)=1,
\]

\[
d=a+T\delta_1,\quad W=T(1+\delta_1),\quad
Q=d^2+4,\quad q=1+\delta_2,\quad
Y=W^2-T^2,\quad N=dW-qY.
\]

The actual minimum and centre geometry supply

\[
0<a\le c,\qquad a^2\le12/17,\qquad T^2\le K.
\tag{1}
\]

The last inequality follows from `b>=c` and `ST<=K`, with `S=a+b`.
In particular, `c^2+2ac<=4`. Put

\[
G=4-a^2-2ac,\qquad M=a(l_0+l_2)+cl_1>0.
\]

The following convenient bounds hold throughout (1):

\[
G>1,\qquad a^2<3/4,\qquad ac<9/8,\qquad c^2<4,
\qquad a<17/20,\quad T<11/5.
\tag{2}
\]

For a direct rational check of the two less immediate bounds, put
`z=a^2`. Since `c<=sqrt(z+4)-a`,

\[
G\ge4+z-2\sqrt{z(z+4)}.
\]

Both sides of `z+3>2sqrt(z(z+4))` are positive, and their squared
difference is

\[
9-10z-3z^2\ge9-10(12/17)-3(12/17)^2=129/289>0.
\]

Thus `G>1`. Similarly

\[
(z+9/8)^2-z(z+4)
=81/64-7z/4\ge33/1088>0
\]

gives `ac<9/8`. The other bounds in (2) follow by squaring positive
rational endpoints. In the stated epsilon range,

\[
d\le17/20+(11/5)(1/32)=147/160<1,
\qquad K<5,\quad Q<5.
\tag{3}
\]

## 2. Uniform bounds for the exact polynomial coefficients

Let `P_i` be the exact coefficients in the desingularized root numerator
and put `C_i=P_i/T^3`. The blowup identity gives

\[
C_2=GM^2>M^2.
\tag{4}
\]

All weights are nonnegative and at most one. Consequently each square
of one of `a*l0,c*l1,a*l2` is at most `M^2`, while each product of
two different ones is at most `M^2/4`. The latter follows by squaring
their nonnegative difference. Additional weight factors can be dropped
in an upper estimate.

For `C3`, its five potentially negative weight coefficients have the
following lower estimates; all other coefficients are nonnegative
polynomials or positive multiples of G.

| Weight monomial | Lower estimate for its coefficient | Loss divided by `M^2` |
| --- | --- | --- |
| `l0^2*l1` | `-(25/4)ac` | `25/16` |
| `l0^2*l2` | `-(11/4)a^2` | `11/16` |
| `l1^3` | `-(41/4)c^2` | `41/4` |
| `l1^2*l2` | `-(41/2)ac` | `41/8` |
| `l1*l2^2` | `-(3/2)ac` | `3/8` |

For example, the first exact coefficient is
`a^2(4-a^2)-ac(3a^2+4)`, and the fourth is
`-ac(6a^2+8c^2-16)+c^2(12-15a^2)`.
Their displayed estimates follow directly from (2). The other three
are checked by the same substitutions; the checker verifies the exact
nonnegative slack identities. Summing the last column gives

\[
C_3\ge-18M^2.
\tag{5}
\]

For the remaining five coefficients, the complete termwise certificate
gives the stronger bounds below:

| Coefficient | `C_i>=-B_i M^2`, with |
| --- | --- |
| `C4` | `B4=1937/32` |
| `C5` | `B5=2131/32` |
| `C6` | `B6=41` |
| `C7` | `B7=383/32` |
| `C8` | `B8=7/4` |

Each is smaller than 128. Here is a reproducible rule for checking
every table entry. Expand the coefficient by weight monomial. Discard
its nonnegative terms and nonnegative multiples of G. For each remaining
monomial, select an available square or cross product from its weights
and use the preceding `M^2` bound. The remaining powers of a and c are
expressed as

\[
(a/c)^r(a^2)^j(ac)^k(c^2)^\ell,
\]

with nonnegative integer exponents. Bound these factors respectively by
`1,3/4,9/8,4`. The companion checker records every exponent identity,
selected pair and rational summand; it checks the exact original
polynomial division by `T^3`. This is a finite coefficient certificate,
with no sampled sign premise.

Since `epsilon<1`, (4)--(5) and the table imply

\[
\sum_{i=2}^8 C_i\epsilon^{i-2}
>M^2\left(1-18\epsilon-
                 \frac{128\epsilon^2}{1-\epsilon}\right).
\tag{6}
\]

## 3. The analytic remainders have a uniform bound

For nonnegative z define the continuous analytic function

\[
H(z)=\frac{\log(1+z)-z+z^2/2}{z^3}
     =\int_0^1\frac{t^2}{1+zt}\,dt,
\quad H(0)=1/3.
\]

Thus `0<H(z)<=1/3`. The exact centered root expression is

\[
\Phi=
\frac{\sum_{i=2}^8 C_i\epsilon^{i-2}}
 {2aQ(1+\delta_1)^2q}
-\frac{\epsilon K N l_0^3H(\delta_0)}{QW}
+\frac{\epsilon cT l_1^3B_vH(\delta_1)}{aQW}
-\epsilon d l_2^3H(\delta_2),
\tag{7}
\]

where

\[
B_v=c(4-a^2)+8a+a\delta_1(c^2+4)
 +\delta_2T(\delta_1+2)
 [K+aT\delta_1(\delta_1+2)]>0.
\]

Discard the nonnegative third term of (7). Because `Y>=0`,
`N<=dW`, so `N H(delta0)<=dW/3` even when N is negative.
Multiply (7) by the positive denominator

\[
D=2aQ(1+\delta_1)^2q.
\]

The two remaining analytic losses are bounded above by

\[
\frac23\epsilon(1+\delta_1)^2q
   [K a d l_0^3+Q a d l_2^3].
\tag{8}
\]

For i equal to 0 or 2, use `T<=2c` and the cross-product bound:

\[
\begin{aligned}
ad l_i^3
&=a^2l_i^3+\epsilon aT l_1l_i^3\\
&\le M^2+2\epsilon(cl_1)(al_i)l_i^2
\le(1+\epsilon/2)M^2.
\end{aligned}
\]

Equations (3) and (8) therefore give the uniform total loss

\[
\frac{20}{3}\epsilon(1+\epsilon/2)(1+\epsilon)^3M^2.
\tag{9}
\]

## 4. Exact final margin and chart coverage

Combine (6) and (9). All subtracted expressions increase with epsilon
on `[0,1/32]`, so

\[
\begin{aligned}
D\Phi
&>M^2\left[1-18\epsilon-
\frac{128\epsilon^2}{1-\epsilon}
-\frac{20}{3}\epsilon(1+\epsilon/2)(1+\epsilon)^3\right]\\
&\ge\frac{39743703}{520093696}M^2
>\frac3{40}M^2>0.
\end{aligned}
\tag{10}
\]

This proves `Phi>0` on the whole stated corner. The division by D is
legitimate because a,Q,q are positive. The final strictness uses `M>0`,
which holds in every maximal chart even at epsilon zero. No other
singular denominator occurs.

The common corner `[0,1/32]` and the closed complementary chart
intervals `[1/32,61/4]` or `[1/32,15]` cover every refined root box;
the improved first upper endpoint follows from the compact pair-sum
bound in the blowup reduction.
Their shared face may be covered twice. Both next-switch alternatives
may therefore start their interval covers at exactly `epsilon=1/32`
without losing a strict or weak boundary case.

## Exact replay and independent review

Run from the repository root:

```text
python explorations/mixed_nonshort_small_parameter_certificate.py
```

Adding `--table` prints every monomial certificate for `C4` through
`C8`. The script imports only the exact polynomial construction from
the blowup identity checker, checks the coefficient divisions and the
five C3 slack identities, and verifies the geometry and final rational
margin. The hand proof above supplies the quantified inequalities and
analytic remainder argument.

The coefficient bounds `C4`--`C8` were derived separately and then
independently checked against their displayed monomials. A second
reviewer also checked the C3 estimates, the sign of N in (8), the
analytic remainder bound, the exact fraction in (10), and all chart
limits. No material gap was found. This is an internal mathematical
review, not a Lean or external peer-review claim.
