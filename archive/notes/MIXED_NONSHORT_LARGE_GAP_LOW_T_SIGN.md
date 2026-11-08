# A hand sign for the low-t unit-shape large-gap face

**Lighter caller replacement:** the [new unit-sign proof and caller
argument](../../docs/lighter-proofs/NONSHORT_LOW_T_CALLER.md) remove this
large-polynomial dependency from the actual low-t branch of `fh_small_gap_j`.
They use simpler positive multipliers, prove their residual on the full
comparison domain by monotonicity and three faces, and obtain the negative
actual condition from the general `fh_window_comb` theorem. The old scalar
polynomial sign below is retained as historical source; the new proof names
the caller and explains the changed intermediate premise explicitly.

Date: 2026-11-08 UTC.

This note proves the remaining unit-shape sign for the low-t part of
the proposed nonshort forward-successor gap exclusion. Its exact conclusion is
\[
\boxed{G(t,j,q,1)>0}
\tag{1}
\]
on
\[
\frac13\le t\le\frac38,\qquad h=1-2t,
\qquad\frac1{30}\le j\le\frac{5h}{7},
\qquad1\le q\le1+\frac{h-j}{1+2j}.
\tag{2}
\]
Here G is the quarter-version combined residual in
[MIXED_NONSHORT_LARGE_GAP_MULTIPLIER_SIGNS](MIXED_NONSHORT_LARGE_GAP_MULTIPLIER_SIGNS.md).
Together with that note's concave shape reduction and the
[upper-shape sign](MIXED_NONSHORT_LARGE_GAP_UPPER_SHAPE_SIGN.md),
(1) excludes an eligible actual boundary point with
\(t\le3/8\) and \(j\ge1/30\).

The proof uses one polynomial on the entire closed domain. Its
negative part has only three groups. Two groups are absorbed by
explicit squares, and the third by a positive quartic. The full sparse
negative part, its coefficient rule, and all comparisons used for the
absorptions are displayed. There is no subdivision or executable
positivity premise.

## 1. The residual and its polynomial normalization

Write
\[
x=h+j,\quad c=1-t,\quad p=t+x,\quad W=1+x,
\quad R=x^2+10x+15,\quad Y=x(x+2),\quad J=t+Y.
\]
At the unit shape, \(k=1\) and \(B=1+2tx+x^2\). Define
\[
V=1-\frac{cp}{W^2}
 +\frac{cx}{W^2}\left(\frac{90-19x^2}{12R}-t\right),
\quad
L=\frac{(q-1)(q^2+10q+1)}{6q(q+1)},
\]
\[
F_\ell=1+\frac{p^2q}{W^2}
 -\frac pW\frac{q^2+10q+1}{6(q+1)}.
\tag{3}
\]
These are exactly the integral secant majorant, the logarithm majorant,
and the resulting incoming floor in the multiplier-sign note. Put
\[
u=15(t-1/3),\quad y=q-1,
\quad\alpha=\frac{27}{4}-3u-24y+16j,
\quad\mu=\frac14-u+6y+24j.
\tag{4}
\]
The residual being estimated is
\[
G=(1-Je^2+\alpha)N
 +C_*(3/4-\mathcal T_U)+\mu(F_\ell-V),
\quad e=q/W.
\tag{5}
\]
All substitutions, their signs, and the scalar comparison are already
proved in the multiplier-sign note. Here they are fixed; only the
rational sign is in question.

For a compact algebraic specification of the polynomial, set
\[
H=V-1+t^2+t^2(2-t),\quad
K=t(1-t+t^2)+HY+tVY^2,\quad E_0=q^2B+W^2-2pqW,
\]
\[
\begin{aligned}
N={}&tBqWc+tq^2B^2-tBqp^2-tp^2W^2+tqWp^3\\
&-tBqWpL-tBqW^2V-q^2K+qWp(H+2tVY).
\end{aligned}
\tag{6}
\]
Thus \(H=tH_U\), \(K=tB^2w_U\), and this N is the original
incident-upper residual numerator, at the substitutions (3).
Define
\[
\begin{aligned}
P=48(q+1)WR\bigl[&4q\{(1+\alpha)W^2-Jq^2\}N\\
&+(qJ-pW)\{3tE_0^2-4tVW^4
 +4q^2W^2(H+2tVY)-4q^4K\}\\
&+4qW^2\mu(F_\ell-V)\bigr].
\end{aligned}
\tag{7}
\]
The exact transport identity gives
\[
P=192q(q+1)W^3R\,G.
\tag{8}
\]
After \(t=(1-h)/2,x=h+j,q=1+y\), all denominators in (7)
cancel. P is a polynomial of degrees \((12,10,6)\) in \((h,j,y)\).
Every multiplier in (8) is positive, so proving \(P>0\) proves (1).

## 2. The positive basis and the coefficient convention

Parametrize the complete domain (2) by
\[
h=\frac14+\frac a{12},\qquad
j=\frac1{30}+b\left(\frac{5h}{7}-\frac1{30}\right),\qquad
 y=z\frac{h-j}{1+2j},
\quad 0\le a,b,z\le1.
\tag{9}
\]
Use the following positive scaling constant:
\[
\sigma=2^{12}\cdot5^{16}\cdot7^{16}.
\]
There is the exact polynomial identity
\[
\begin{aligned}
&\sigma\,12^{18}(1+2j)^6P(h,j,y)\\
&\qquad=\sum_{m=0}^{18}\sum_{n=0}^{16}\sum_{r=0}^{6}
4^m d_{mnr}\,a^m(1-a)^{18-m}
 b^n(1-b)^{16-n}z^r(1-z)^{6-r}.
\end{aligned}
\tag{10}
\]
In (10)--(11), P is the polynomial in \((h,j,y)\) obtained from
(7) by \(q=1+y\). The coefficients \(d_{mnr}\) are integers. No binomial coefficient is included in a basis monomial.

For complete specificity, the following finite formula computes every
coefficient directly from the compact identity (7). Introduce a formal
variable \(w\), put
\[
h=\frac{3+w}{12+3w},\qquad
j=\frac1{30}+b\left(\frac{5h}{7}-\frac1{30}\right),\qquad
 y=z\frac{h-j}{1+2j},
\]
and form the polynomial
\[
E(w,b,z)=(12+3w)^{18}(1+2j)^6P(h,j,y).
\tag{11}
\]
Then
\[
d_{mnr}=\sigma\sum_{i=0}^n\sum_{\ell=0}^r
 \binom{16-i}{n-i}\binom{6-\ell}{r-\ell}
 [w^mb^iz^\ell]E.
\tag{12}
\]
Here brackets mean an ordinary polynomial coefficient, not an unknown
sign or an executable instruction. Formula (12) follows from
\(b^i=b^i(b+(1-b))^{16-i}\) and the identical formula for z.
Finally, substituting \(w=4a/(1-a)\) gives (10), including its endpoints
by the polynomial identity. These formulas specify all coefficient
arithmetic below.

## 3. The entire negative part

It is convenient to collect the coefficients in the formal polynomial
\[
Q(w,b,z)=\sum_{m,n,r}d_{mnr}w^m
 b^n(1-b)^{16-n}z^r(1-z)^{6-r}.
\]
The negative part means the sum of the absolute values of its negative
coefficients, with these same basis monomials. Expansion of (7) by
(11)--(12) gives exactly
\[
\begin{aligned}
Q^-={}&A(w)(1-b)^{16}z^5(1-z)\\
&+\sum_{n=3}^{6}B_n(w)b^n(1-b)^{16-n}z^4(1-z)^2\\
&+C_{12}(w)b^{12}(1-b)^4z^6
 +C_{13}(w)b^{13}(1-b)^3z^6.
\end{aligned}
\tag{13}
\]
Thus there are precisely 38 negative coefficients: 17 in A, four in
each of the four \(B_n\), two in \(C_{12}\), and three in \(C_{13}\).
Every other coefficient is nonnegative. The following lists the full
sparse identity (13), factoring out positive integers to keep its
entries shorter.

First,
\[
A(w)=2^5\cdot3\cdot7^{16}w^2\sum_{i=0}^{16}a_iw^i,
\]
where

| \(i\) | \(a_i\) |
| ---: | ---: |
| 0 | 2397707777140037293382752645570560 |
| 1 | 16353397916374426785868956015292416 |
| 2 | 28159524617291042366567637314580480 |
| 3 | 28911136663007386604169358406201344 |
| 4 | 20678765282103369757761732614362624 |
| 5 | 10985258466158523306714202588368640 |
| 6 | 4478712159213236532562643652663552 |
| 7 | 1425891375716544336674748300016640 |
| 8 | 357208519252440186256045146347296 |
| 9 | 70418425141546720451562331206736 |
| 10 | 10846375793664704984288652730640 |
| 11 | 1285423651952874409209805927248 |
| 12 | 114149841028201956784855154130 |
| 13 | 7269789871735342895061372613 |
| 14 | 307856830410297400714557893 |
| 15 | 7489050419268032483643910 |
| 16 | 72430362994787674586784 |

Next, write \(B_n(w)=\kappa_n\sum_{i=0}^3b_{ni}w^i\), where
\[
\begin{aligned}
\kappa_3&=2^{15}\cdot3^2\cdot5^3\cdot7^{13},&
\kappa_4&=2^{14}\cdot3^3\cdot5^4\cdot7^{12},\\
\kappa_5&=2^{15}\cdot3^4\cdot5^5\cdot7^{11},&
\kappa_6&=2^{16}\cdot3^7\cdot5^6\cdot7^{10}.
\end{aligned}
\]
The four coefficient rows are

| \(n\) | \(b_{n0}\) | \(b_{n1}\) | \(b_{n2}\) | \(b_{n3}\) |
| ---: | ---: | ---: | ---: | ---: |
| 3 | 1103663596940557450620613373714364 | 4770693071341682819826564503330760 | 7034267260365025670830288268850621 | 647932890581317857088943609547154 |
| 4 | 6628064773938174345140121455755164 | 29326146951082345455383936448061140 | 51786221642915422584245741246084856 | 38703237956269725710792142532989431 |
| 5 | 4346992921592769630906057276354768 | 19532480587960187633569653043128384 | 35503167995502310879853161594106403 | 28988405416205966750592041951966564 |
| 6 | 132605033522434716125366022755688 | 604543417861552793004382050904610 | 993179233393961593213204573414397 | 391647763206682977317446821680357 |

Finally,
\[
\begin{aligned}
C_{12}(w)=2^9\cdot3^5\cdot5^{12}\cdot7^4w^{17}
\bigl(&48865863158829350970808941\\
 &+1066719692814190437644576w\bigr),
\end{aligned}
\]
\[
\begin{aligned}
C_{13}(w)=2^{11}\cdot3^7\cdot5^{13}\cdot7^3w^{16}
\bigl(&20357877355965615543224261\\
 &+2377581713231589305500719w\\
 &+41099260101639484253182w^2\bigr).
\end{aligned}
\tag{14}
\]
Every displayed coefficient is positive. Equations (7), (11)--(14)
are one fully specified sparse negative-part identity; it does not
refer to an external coefficient file or a positivity program.

## 4. The comparisons needed to absorb that negative part

This section gives all the coefficient comparisons used below. Their
small rational bounds deliberately leave room, so equality is never
needed. Each table entry is an integer inequality specified by (12).
For example, an entry \(L\) in a column labelled
\(100d/B\ge L\) means exactly \(100d-LB\ge0\), with its positive
integer B provided by (13)--(14).

### 4.1. The coefficients in A

For \(m=2,\ldots,18\), put \(A_m=-d_{m,0,5}>0\). The complete
comparison table is

| \(m\) | \(100d_{m,0,4}/A_m\ge\) | \(100d_{m,0,6}/A_m\ge\) |
| ---: | ---: | ---: |
| 2 | 1969 | 2095 |
| 3 | 394 | 416 |
| 4 | 237 | 229 |
| 5 | 191 | 158 |
| 6 | 181 | 120 |
| 7 | 189 | 97 |
| 8 | 209 | 81 |
| 9 | 240 | 70 |
| 10 | 282 | 62 |
| 11 | 337 | 56 |
| 12 | 410 | 52 |
| 13 | 508 | 49 |
| 14 | 642 | 47 |
| 15 | 837 | 46 |
| 16 | 1145 | 48 |
| 17 | 1695 | 53 |
| 18 | 2958 | 69 |

In particular, every row gives the strict inequalities
\[
d_{m,0,4}>A_m,
\qquad d_{m,0,6}>\frac14A_m.
\tag{15}
\]

### 4.2. The coefficients in the four \(B_n\)

Put \(B_{mn}=-d_{m,n,4}>0\) for \(0\le m\le3\) and
\(3\le n\le6\). The complete table is

| \((m,n)\) | \(100d_{m,n,3}/B_{mn}\ge\) | \(100d_{m,n,5}/B_{mn}\ge\) |
| ---: | ---: | ---: |
| (0, 3) | 1481 | 847 |
| (1, 3) | 1867 | 910 |
| (2, 3) | 3277 | 1360 |
| (3, 3) | 57891 | 20542 |
| (0, 4) | 440 | 527 |
| (1, 4) | 607 | 556 |
| (2, 4) | 977 | 695 |
| (3, 4) | 2298 | 1298 |
| (0, 5) | 163 | 527 |
| (1, 5) | 299 | 545 |
| (2, 5) | 558 | 661 |
| (3, 5) | 1349 | 1124 |
| (0, 6) | 56 | 939 |
| (1, 6) | 273 | 951 |
| (2, 6) | 730 | 1264 |
| (3, 6) | 4131 | 4414 |

Thus every row gives
\[
d_{m,n,3}>\frac12 B_{mn},\qquad
 d_{m,n,5}>\frac12 B_{mn}.
\tag{16}
\]

### 4.3. The final three rows

For \(m=16,17,18\), set \(T_m=-d_{m,13,6}>0\). Here the negative
coefficient at \(n=12\) is absent when \(m=16\). The relevant bounds are

| \(m\) | \(100d_{m,11,6}/T_m\ge\) | \(100\max(0,-d_{m,12,6})/T_m\le\) | \(100d_{m,14,6}/T_m\ge\) | \(100d_{m,15,6}/T_m\ge\) |
| ---: | ---: | ---: | ---: | ---: |
| 16 | 11614 | 0 | 351 | 183 |
| 17 | 2863 | 80 | 80 | 48 |
| 18 | 2496 | 101 | 70 | 43 |

The four bounds needed for the proof are therefore
\[
d_{m,11,6}>6T_m,\quad d_{m,12,6}>-2T_m,
\quad d_{m,14,6}>0,\quad d_{m,15,6}>\frac14T_m.
\tag{17}
\]
The first two tables contain 34 and 32 comparisons, respectively,
and the last table contains 12. They are precisely the 78 comparisons
used in the next section. All entries come from ordinary integer
multiplication and addition in (7), (11)--(12); none is a sampled
inequality.

## 5. Three explicit positive groups

Fix a row m. The positive row factor \(4^ma^m(1-a)^{18-m}\) in (10)
can be set aside. Write \(s=1-b\).

For a negative coefficient from A, borrow \(A_m\) from its z-degree-four
neighbor and \(A_m/4\) from its z-degree-six neighbor, using (15).
Together with the negative coefficient, these form
\[
A_m(1-b)^{16}z^4
 \left((1-z)-\frac z2\right)^2\ge0.
\tag{18}
\]
Both borrowed coefficients are smaller than the available positive
coefficients. The unused amounts remain positive.

For a negative coefficient from \(B_n\), borrow \(B_{mn}/2\) from
each neighbor with z-degree three and five. Equation (16) shows that
these coefficients are available. Their sum with the negative term is
\[
\frac{B_{mn}}2 b^n(1-b)^{16-n}
 z^3(1-z)(1-2z)^2\ge0.
\tag{19}
\]
Again the unused amounts remain positive.

For one of the last three rows, use (17) on its b-degrees 11 through 15,
all with z-degree six. The resulting lower bound is
\[
T_m b^{11}s z^6
\left(6s^4-2bs^3-b^2s^2+\frac{b^4}{4}\right).
\tag{20}
\]
The elementary inequality
\[
2bs^3\le2s^4+\frac12b^2s^2
\]
follows from \(s^2(b-2s)^2\ge0\). Therefore the bracket in (20) is
at least
\[
\frac{(b^2-3s^2)^2}{4}+\frac{7s^4}{4}\ge0.
\tag{21}
\]
This is a homogeneous polynomial inequality and includes \(b=0,1\);
no division by \(1-b\) is used.

The three groups use disjoint coefficients: A has b-degree zero;
the \(B_n\) have b-degrees three through six; the final group has
b-degrees 11 through 15. Hence no coefficient is borrowed twice.
The complete negative-part identity (13) shows that every negative
coefficient has been included. All remaining terms are nonnegative.
It follows that the right side of (10) is nonnegative.

## 6. Strict positivity, including all boundary faces

Strictness comes from the four corner coefficients in rows \(m=0\)
and \(m=18\), with \((n,r)=(0,0),(0,6),(16,0),(16,6)\).
At row zero they are all positive and are not borrowed by any group.
At row 18, the three corners with \((n,r)\ne(0,6)\) are positive and
untouched. The remaining corner retains a positive amount by the
strict inequality in (15).

For an explicit check of the untouched corner signs, the following
are the positive numerators of G at the corresponding domain vertices,
after cancellation to lowest terms. Every denominator is positive by
(3), (7)--(8). These vertex values differ from the relevant basis
coefficients only by positive scaling factors.

| \(h\) | \(j\) | numerator at \(q=1\) | numerator at \(q=1+(h-j)/(1+2j)\) |
| ---: | ---: | ---: | ---: |
| \(1/4\) | \(1/30\) | 107561107183031 | 2875788000859390169502511 |
| \(1/4\) | \(5/28\) | 28211913 | 708221994591 |
| \(1/3\) | \(1/30\) | 314028068651 | 726189347055865313 |
| \(1/3\) | \(5/21\) | 1428618425 | 55235588318393083 |

For every \((b,z)\in[0,1]^2\), at least one of the four products
\[
(1-b)^{16}(1-z)^6,\quad (1-b)^{16}z^6,
\quad b^{16}(1-z)^6,\quad b^{16}z^6
\]
is strictly positive. Thus row zero, after the absorptions, is a
strictly positive polynomial on the full square, and the same is true
of row 18. If \(a<1\), row zero has the positive factor \((1-a)^{18}\).
If \(a=1\), row 18 has the positive factor \(4^{18}a^{18}\).
The right side of (10) is therefore strictly positive everywhere.
All factors on its left are positive, and (8) proves (1).

## 7. Scope of the conclusion

For an actual eligible point with \(1/3<t\le3/8\) and \(j\ge1/30\),
the multiplier-sign note proves \(G<0\) and concavity in the actual
shape interval \([1,1+j]\). This note proves positivity at its lower
endpoint. The separate upper-shape theorem proves positivity at the
other endpoint. Concavity then gives positivity throughout the interval,
a contradiction.

This conclusion uses the incoming floor and the next-norm condition
only through the already justified scalar comparison. It neither
changes the actual common covector nor transfers an artificial Casimir
cap to the comparison shapes. The region \(t\ge3/8\) is addressed by
the separate high-t argument.
