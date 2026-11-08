# A corrected Casimir floor up to short ratio thirteen sixths

Date: 2026-11-08 UTC. **Accepted hand theorem on the full extended
shape interval.** The
[six derivative signs](MIXED_SMALLER_SHORT_EXTENDED_CASIMIR_DERIVATIVES.md)
now have explicit polynomial-product majorants and elementary signs.
The [extended-shape review](MIXED_SMALLER_SHORT_EXTENDED_SHAPE_AUDIT.md)
records the analytic reductions, the new finite sign arguments and
the exact endpoint arithmetic. The actual shape hypotheses remain explicit.

**Theorem.** In the actual smaller-short setup, suppose

\[
2\le x\le\frac{13}{6},\qquad
0\le\delta=\frac\beta x-1\le\frac1{19}.
\tag{1}
\]

Then the squared Casimir of the original common covector satisfies

\[
\boxed{\Gamma_{\rm actual}>\frac{1829}{10000}.}
\tag{2}
\]

This is the interval extension of the
[small-shape floor](MIXED_SMALLER_SHORT_SMALL_SHAPE_CASIMIR_FLOOR.md),
with a slightly weaker conclusion. The argument below specifies all
changes to its analytic reduction. Only that earlier note's Sections
1--3 are reused. Its extracted coefficient-group assertions in
Section 4 are not premises: all six derivative signs, on the full
extended interval, are supplied by the new proof linked above.
This theorem retains (1) as its explicit actual-shape hypothesis.

## 1. The preliminary comparisons on the extended rectangle

The strong lower order and extended small-shape upper order give

\[
\alpha=1+\eta\delta,\quad \beta=x(1+\delta),\qquad
13/5\le\eta\le3.
\tag{3}
\]

At delta=0 the order bounds give alpha=1, and any eta in the
displayed interval represents that same shape. No division by delta
is made at this boundary.

Retain S=1+x, q_c=alpha^2/[x(x+2)+alpha^2], the original incoming
norm u, and every scalar formula of the small-shape floor. Its
incoming majorant still obeys u<=bar u<31/40. Indeed its first
positive term is at most 49/4482, and its cubic tail is at most
1/(24*19^3); their sum is less than 1/40.

Here alpha<=22/19<6/5 and beta<=130/57<23/10. Consequently

\[
0<D<S,\qquad q_c\le121/843<1/6,\qquad r_A/q_c>2.
\tag{4}
\]

For the lower D bound, use
D>=2+2x-2beta(x-1)>=6-910/171=116/171>0.
The same polynomial bound for D-S in Section 1 of the earlier
floor decreases with x>=2 and increases with delta; its value at
x=2,delta=1/19 is -74/361. The last inequality in (4) follows
from alpha^2+2alpha*beta<174/25<8<=x(x+2).

The corrected envelope inequality
Gamma_actual>=Gamma_*-R*/7 still refers to the original common
covector. Its fixed-p derivative comparison extends to q<=1/6
exactly as before, using 27/200<1/7.

For the possible continuation at tau=2, A2>0 follows from the same
discriminant identity: now 3<=S<=19/6<5 and
(S-2)^2/alpha^2<=49/36<2. The earlier bound C0<=5 in the derivative
(R2*)'=1/q-C0+4qA2 is unchanged. Hence (R2*)'>1 on q<=1/6.
The envelope Casimir derivative now has the slightly enlarged bound

\[
(\Gamma_*)_q
\le\frac{H(2S-1)}{8\alpha^2(1-q)^2}
\le\frac{49}{475}<\frac{11}{100},
\]

because H=S[U(1/S)-u]<=49/456 and 2S-1<=16/3. Thus

\[
\frac{d}{dq}(\Gamma_*-R_2^*/7)<-\frac{23}{700}<0.
\tag{5}
\]

This proves the same scalar comparison up to q=q_c, even if it
passes the original outer scale bound. No upper cap or closure is
assigned to that comparison point.

## 2. The two central lower bounds and incoming substitution

Use exactly the functions Phi and Psi defined by equations
(10)--(11) of the small-shape floor. The scale comparison and
the residual derivative bound still give

\[
\Gamma_{\rm actual}\ge\min\{\Phi,\Psi\}.
\tag{6}
\]

They both decrease with u on the extended rectangle. All estimates
in the earlier proof remain valid, except that T<=S<=19/6 changes
the second residual's derivative lower bound to

\[
\frac{2242}{693}-\frac76=\frac{2867}{1386}.
\]

The envelope derivative remains at most 81/320, and
81/320<2867/9702. Thus both decreasing signs still follow.
In particular E>=0 remains valid: its minimum is at u=3/4,S=19/6
and is positive. We may therefore substitute the same rational
incoming upper value bar u as in the original theorem.

## 3. The six derivative signs on the extended rectangle

After the incoming substitution in Section 2, put
alpha=1+eta*delta and beta=x(1+delta). The
[explicit derivative proof](MIXED_SMALLER_SHORT_EXTENDED_CASIMIR_DERIVATIVES.md)
proves on the entire box
2<=x<=13/6, 0<=delta<=1/19 and 13/5<=eta<=3 that
\[
-\Phi_\delta>0,\qquad
\frac{\Psi_\eta}{x\delta}>0,\qquad -\Psi_x>0,
\tag{7}
\]
\[
-\Phi_x\big|_{\delta=1/19}>0,\qquad
-\Phi_\eta\big|_{x=13/6,\delta=1/19}>0,\qquad
-\Psi_{\delta\delta}\big|_{x=13/6,\eta=13/5}>0.
\tag{8}
\]
The quotient is interpreted by its polynomial extension at delta=0,
where Psi_eta=0.

That proof first writes the rational parts of Phi and Psi as explicit
polynomial products. It differentiates them, clears positive
denominators and normalizes at positive rational origins. Its first
polynomial is bounded below by
(1+h)^9-(1+h)^10 M-H, with h=x-2, M<3/5 and H<10^-6;
the retained positive factor therefore proves its sign directly.
The other five complete adverse-part majorants are respectively
less than 1/2, 3/5, 1/2, 1/100 and 9/25, so their normalized
constant one proves all five signs. Every majorant is an explicitly
printed polynomial or binomial product. There is no positive-basis
minimum or extracted negative-coefficient group left as a premise.

## 4. The three remaining rational endpoints

The first, fourth and fifth derivative signs successively increase
delta to 1/19, increase x to 13/6 and increase eta to 3, giving

\[
\Phi\ge\Phi(13/6,1/19,3),
\]
\[
\Psi\ge\min\{\Psi(13/6,0,13/5),\Psi(13/6,1/19,13/5)\}.
\tag{9}
\]
For the latter inequality, first lower eta to 13/5 and increase x to
13/6, then use concavity in delta. These are comparisons of the two
scalar lower bounds, not physical continuations of the original period.

Each endpoint is Z0-log(y)/7. Their exact rational data are

| Endpoint | y | Z0 |
|---|---|---|
| Phi | 103488/134749 | 3049751009682789775721384421507415003/20993116633143718505205389691985920000 |
| Psi, delta=0 | 12/19 | 1410999866568424453/12013145998389120000 |
| Psi, delta=1/19 | 2524608/3353029 | 4487908086224060997939793560828739/31524327593235229590253113384960000 |

In every row 0<y<1. Put z=(y-1)/(y+1)<0. The positive odd
logarithm series gives log(y)<2(z+z^3/3+z^5/5). Direct rational
substitution in the three displayed rows gives, respectively,

\[
Z_0-\frac27(z+z^3/3+z^5/5)-\frac{1829}{10000}
>\frac1{12500},\qquad\frac1{5000},\qquad\frac3{10^6}.
\tag{10}
\]

All three values in (9) are therefore strictly above 1829/10000.
Combining this with (6) proves (2) for the original actual covector.
The only additional hypotheses of this theorem are the two actual
shape restrictions (1), which supply the order box (3). All six
uniform derivative signs are now proved on that full box. No
competitive upper cap, physical cost or period closure has been
assigned to an artificial scalar point.
