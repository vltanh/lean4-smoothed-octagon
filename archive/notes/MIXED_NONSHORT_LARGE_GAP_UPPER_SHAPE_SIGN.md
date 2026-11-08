# The upper shape endpoint of the large-gap residual is positive

**Lighter caller replacement:** [positive shape monotonicity and the new
unit sign](../../docs/lighter-proofs/NONSHORT_LOW_T_CALLER.md) remove this
endpoint dependency from the actual low-t branch of `fh_small_gap_j`.
The replacement preserves that caller's domain and conclusion. It does not
assert a new proof of the old residual's wider scalar statement below.

Date: 2026-11-08 UTC. A closed scalar hand inequality. This note proves
one of the endpoint signs isolated in
[MIXED_NONSHORT_LARGE_GAP_MULTIPLIER_SIGNS](MIXED_NONSHORT_LARGE_GAP_MULTIPLIER_SIGNS.md).
The lower shape endpoints require their own signs.

Keep exactly the rational residual G and the quarter-version multiplier
M defined in that note. The theorem here is
\[
\boxed{G(t,x,q,1+j)>0}
\tag{1}
\]
on
\[
h=1-2t\in[1/5,1/3],\quad
1/30\le j\le5h/7,\quad x=h+j,\quad
1\le q\le\frac{1+h+j}{1+2j}.
\tag{2}
\]
This is a sign for the explicitly specified scalar function. No
incoming floor, transported norm, covector, or cost cap is newly
assigned to its upper shape endpoint.

The proof differentiates in j after a fixed change of the q coordinate,
reduces to j=1/30, and proves that endpoint with one concave quadratic.
All coefficient estimates below have complete finite defining rules and
displayed coefficient norm bounds. They do not involve subdivision or
an executable positivity premise.

## 1. A compact definition of the polynomial

In this note set
\[
t=(1-h)/2,\quad x=h+j,\quad k=1+j,\quad
c=1-t,\quad p=t+x,\quad W=1+x,
\]
\[
Y=x(x+2),\quad J=t+Y,\quad B=k+2tx+x^2=kW,
\quad R=x^2+10x+15.
\]
Use
\[
V=1-\frac{cp}{W^2}
 +\frac{cx}{W^2}\left(\frac{90-19x^2}{12R}-t\right),
\]
\[
L=\frac{(q-1)(q^2+10q+1)}{6q(q+1)},\qquad
F_\ell=1+\frac{p^2q}{W^2}
-\frac pW\frac{q^2+10q+1}{6(q+1)},
\]
\[
u=15(t-1/3),\quad
\alpha=27/4-3u-24(q-1)+16j,\quad
M=1/4-u+6(q-1)+24j.
\]
To keep the algebra polynomial, abbreviate
\[
H_t=k(V-1+t^2)+t^2(2-t),
\quad Q_t=t(k^2-kt+t^2)+H_tY+tVY^2,
\quad E_0=q^2B+W^2-2pqW.
\]
Here \(H_t=tH_U\), \(Q_t=tB^2w_U\). Define the residual numerator
directly by
\[
\begin{aligned}
N={}&tBqWc+tq^2B^2-tBqp^2-tp^2W^2+tqWp^3\\
 &-tBqWpL-tBqW^2V-q^2Q_t+qWp(H_t+2tVY).
\end{aligned}
\tag{3}
\]
The polynomial used throughout the proof is
\[
P(h,j,y)=192q(q+1)W^3R\,G(t,x,q,1+j),\qquad q=1+y.
\tag{4}
\]
For checking all coefficient data without reconstructing G, an
equivalent compact algebraic definition is
\[
\begin{aligned}
P=48(q+1)WR\big[&4q\{(\alpha+1)W^2-Jq^2\}N\\
&+(qJ-pW)\{3tE_0^2-4tVW^4
 +4q^2W^2(H_t+2tVY)-4q^4Q_t\}\\
&+4qW^2M(F_\ell-V)\big].
\end{aligned}
\tag{5}
\]
Every denominator cancels. In particular P has degree at most six in y.
All factors multiplying G in (4) are positive, so it suffices to prove
P positive.

The simplification \(B=kW\) at this endpoint also gives
\[
E=\frac{1+2ty+ky^2}{W},\qquad
C_*=\frac{t(xc+Jy)(1+2ty+ky^2)^2}{q}.
\]
These identities give another direct verification of (5).

## 2. Differentiating at fixed position in the allowed q interval

Write
\[
y=z\frac{h-j}{1+2j},\qquad0\le z\le1,
\]
and define polynomials
\[
T(h,j,z)=(1+2j)^6
 P\left(h,j,z\frac{h-j}{1+2j}\right),
\quad D=(1+2j)\partial_jT-12T.
\tag{6}
\]
Then
\[
\partial_j P\left(h,j,z\frac{h-j}{1+2j}\right)
=\frac{D(h,j,z)}{(1+2j)^7}.
\tag{7}
\]
We will prove D positive on the larger rectangle
\[
1/5\le h\le1/3,\qquad1/30\le j\le5/21,
\qquad0\le z\le1.
\tag{8}
\]

Use the elementary positive-basis expansion
\[
D(h,j,z)=\sum_{i=0}^6\binom6i D_i(h,j)z^i(1-z)^{6-i}.
\tag{9}
\]
The coefficient convention is specified exactly by
\[
D_i=\sum_{r=0}^i
 \frac{\binom ir}{\binom6r}[z^r]D.
\tag{10}
\]
Indeed it follows by inserting \((z+(1-z))^{6-r}\) after every
monomial \(z^r\). The factors in (9) are nonnegative and sum to one.
It therefore suffices to prove each \(D_i>0\).

## 3. Bound the complete negative part of each coefficient

Put
\[
a=h-1/5\in[0,2/15],\qquad b=j-1/30\in[0,43/210]
\subset[0,2/9],
\]
and define the rational coefficients by ordinary expansion:
\[
D_i(1/5+a,1/30+b)=\sum_{r,m}d_{irm}a^rb^m.
\tag{11}
\]
Only the constant term and the coefficient of \(b^2\) will be retained
from the positive part. The following integer lower bounds follow from
(3), (5), (6), and (10):

| i | lower bound for \(d_{i00}\) | lower bound for \(d_{i02}\) |
| ---: | ---: | ---: |
| 0 | 33 | 695000 |
| 1 | 205 | 730000 |
| 2 | 480 | 761000 |
| 3 | 814 | 791000 |
| 4 | 1173 | 821000 |
| 5 | 1544 | 856000 |
| 6 | 1960 | 899000 |

All comparisons in this table are strict rational comparisons. The
normalization in (10) includes \(\binom6i\); omitting it would change
these entries.

Here is a complete explicit norm specification for the discarded
negative terms. Define
\[
L_i(a)=\sum_{m<2,\ d_{irm}<0}|d_{irm}|(2/9)^m a^r,
\]
\[
K_i(a)=\sum_{m\ge2,\ d_{irm}<0}|d_{irm}|(2/9)^{m-2}a^r.
\tag{12}
\]
The coefficients of the following displayed polynomials are integer
upper bounds for these norms. More precisely, each coefficient of
\(K_i\) is rounded up to the next integer to give \(R_i\); for each
power of a the largest rounded coefficient among the seven \(L_i\)
gives the coefficient of \(L_*\). Thus these are complete coefficient
norm identities with explicit rounding, not an assertion about a
selected subset of negative monomials:
\[
L_i\preceq L_*,\qquad K_i\preceq R_i.
\tag{13}
\]
Here \(A\preceq B\) means every coefficient of \(B-A\) is
nonnegative. Zero coefficients are omitted below.

\[
\begin{aligned}
L_*(a)={}&985445a^9+6147997a^{10}+5885870a^{11}
 +3070333a^{12}\\
&+1152890a^{13}+249415a^{14}+30049a^{15}+1590a^{16}.
\end{aligned}
\tag{14}
\]

\[
R_0=a+a^2.
\]
\[
\begin{aligned}
R_1={}&1+a+9a^2+6a^3+a^4+2a^5+a^6+3a^7+2a^8\\
&+1259696a^{11}+344393a^{12}+26402a^{13}.
\end{aligned}
\]
\[
\begin{aligned}
R_2={}&52+34a+6a^2+34a^3+95a^4+79a^5+55a^6+48a^7+7a^8\\
&+11852452a^{10}+10868171a^{11}+3189304a^{12}
 +450144a^{13}+25692a^{14}.
\end{aligned}
\]
\[
\begin{aligned}
R_3={}&5084+1777a+a^3+1401a^4+1986a^5+912a^6+193a^7+16a^8\\
&+51113026a^{10}+37171062a^{11}+12361371a^{12}
 +2308227a^{13}+230984a^{14}+9447a^{15}.
\end{aligned}
\]
\[
\begin{aligned}
R_4={}&73022+20141a+a^3+6478a^4+26559a^5+14694a^6
 +3218a^7+192a^8\\
&+1272516a^9+116987484a^{10}+84321100a^{11}
 +31058400a^{12}\\
&+6808234a^{13}+869736a^{14}+56109a^{15}+1152a^{16}.
\end{aligned}
\]
\[
\begin{aligned}
R_5={}&303243+119765a+a^3+21398a^4+209521a^5+148399a^6
 +28273a^7+763a^8\\
&+8075270a^9+200015931a^{10}+152324900a^{11}
 +61331134a^{12}\\
&+15083275a^{13}+2244247a^{14}+181534a^{15}+5760a^{16}.
\end{aligned}
\]
\[
\begin{aligned}
R_6={}&681832+397253a+a^3+84840a^4+943541a^5+900700a^6
 +92043a^7+7796a^8\\
&+50199473a^9+286788588a^{10}+237163778a^{11}
 +103579860a^{12}\\
&+27948337a^{13}+4653748a^{14}+436506a^{15}+17280a^{16}.
\end{aligned}
\tag{15}
\]

Every coefficient in (14)--(15) is positive. At \(a=2/15\),
\[
L_*(2/15)=\frac{3727558762287616}{145964630126953125}<1.
\tag{16}
\]
The seven other evaluations have the following strict upper bounds:

| i | \(R_i(2/15)\) | upper bound |
| ---: | ---: | ---: |
| 0 | \(34/225\) | 1 |
| 1 | \(2546154834086029/1946195068359375\) | 2 |
| 2 | \(552505465177318616/9730975341796875\) | 57 |
| 3 | \(776760619476535958762/145964630126953125\) | 5322 |
| 4 | \(18418538643211499113076/243274383544921875\) | 75711 |
| 5 | \(139788260983067055295031/437893890380859375\) | 319229 |
| 6 | \(7151021420842529559538/9730975341796875\) | 734873 |

To see directly why these norm estimates prove the desired signs,
each negative monomial with m=0 or 1 is bounded below by its
contribution to \(-L_i(a)\). Each with \(m\ge2\) is bounded below
by its contribution to \(-b^2K_i(a)\), because \(b\le2/9\).
All unretained nonnegative monomials can be discarded. Hence
\[
D_i\ge d_{i00}+d_{i02}b^2-L_*(a)-b^2R_i(a).
\tag{17}
\]
Equations (16) and the two tables show that every right side is
strictly greater than 29, even after discarding its positive
\(b^2\)-coefficient. Thus all seven \(D_i>0\), proving D>0
on (8) and the strict derivative sign in (7).

## 4. The endpoint j=1/30

By (7), it remains to prove the sign at j=1/30. Define
\[
T_0(h,z)=T(h,1/30,z)
 =\sum_{i=0}^6\binom6i B_i(h)z^i(1-z)^{6-i}.
\tag{18}
\]
The exact coefficients are given by the same extraction rule (10),
with \(T_0\) in place of D. Let a=h-1/5 as above. For
\(i=0,\ldots,5\), the negative-coefficient part of
\(B_i(1/5+a)\) is identically zero. Their constant terms are
strictly greater than, respectively,
\[
54,\quad54,\quad47,\quad38,\quad29,\quad21.
\tag{19}
\]
These six coefficients are therefore positive for every a>=0.

For completeness the entire negative part of the last coefficient,
with coefficients rounded upward as in (12)--(15), is
\[
297a^2+8675a^3+24977a^4+5708a^5.
\tag{20}
\]
There are no other negative powers. Its constant and linear
coefficients are
\[
B_6(1/5)=\frac{558590438817825242303593}
 {33630250781250000000000}>16,
\]
\[
B_6'(1/5)=\frac{27034129751721510802310971}
 {134521003125000000000000}>200.
\]
For an exact check of the only negative terms, their absolute
coefficients in increasing order of degree are
\[
\frac{1331149885817621944737083}{4484033437500000000000},
\quad\frac{259317620895171715368523}{29893556250000000000},
\]
\[
\frac{62219906099403355406321}{2491129687500000000},
\quad\frac{947926671755959292701}{166075312500000000}.
\tag{21}
\]
Each is less than the corresponding integer in (20).

Since \(0\le a\le2/15\),
\[
297+8675a+24977a^2+5708a^3
\le\frac{6450409}{3375}<1912.
\]
Consequently
\[
B_6(1/5+a)>16+200a-1912a^2.
\tag{22}
\]
The last polynomial is concave, so its minimum on \([0,2/15]\)
is at an endpoint. Its two endpoint values are 16 and
\(1952/225>8\). Thus \(B_6>8\), and (18)--(19) give
\(T_0>0\) for \(0\le z\le1\).

## 5. Conclusion and the finite arithmetic interface

For fixed h,z, increasing j from 1/30 to any allowed value in (2)
stays inside (8). The strict derivative sign (7) and the endpoint
sign (18)--(22) imply
\[
P\left(h,j,z\frac{h-j}{1+2j}\right)>0.
\]
Every allowed q has this form. Equation (4) therefore proves (1).

Every coefficient bound used above has a specified direct expansion
check: (3) and (5) define P, (6) defines T and D, (10) fixes the
binomial basis, and (11)--(12) specify the complete negative norms.
Taking the coefficientwise ceilings gives exactly the integer
polynomials (14)--(15); substitution at a=2/15 gives the displayed
rational evaluations. At j=1/30 the same extraction gives the six
zero negative parts and the four terms (21). Thus the proof uses
finite polynomial identities, the elementary bounds on a and b,
and the single concave quadratic (22). It imports no sampled minimum
or algorithmic sign verdict.
