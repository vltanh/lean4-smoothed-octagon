# The three outer corrected-cap faces when x is at most two

**Partial lighter replacement:** the actual small-shape branch B now has a
[proof of its \(F_0\) sign](../../docs/lighter-proofs/SHORT_OUTER_LOW_SHAPE_TERMINAL.md)
using small derivative identities and a scalar endpoint bound. It covers
the original actual caller, including its shape cap, rather than all extra
points in the generated B row. The \(F_1\) sign and the S/A branches still
require replacements under the requested no-table standard; this does not
close S1. The original source argument remains below.

Date: 2026-11-08 UTC. Analytic terminal-face theorem, using the
correction coefficient supplied by the
[sharp low-ratio corrected-cap reduction](MIXED_SMALLER_SHORT_SHARP_LOW_RATIO_CORRECTED_CAP.md).
The proof uses fully specified rational polynomials and seventeen
explicit adverse-term bounds. Each bound is a finite univariate coefficient
comparison followed by an elementary inequality on [0,1].

Put

\[
c=7/96,\quad g=9193/50000,\quad S=1+x,\quad Z=35x+13,
\quad R=4x^2+11x+1.
\tag{1}
\]

We prove that the corrected cap is greater than \(g\) at every
terminal outer scale \(q=1/7\) of an actual short candidate with
\(1<x\le2\). The incoming norm remains unchanged until the
scale comparison has ended.

## 1. The incoming interval

The accepted [uniform incoming floor](MIXED_SMALLER_SHORT_UNIFORM_INCOMING_FLOOR.md)
and the [rational incoming estimate](MIXED_SMALLER_SHORT_INCOMING_NORM_BOUND.md)
give

\[
u_f=\frac34+\frac{(x-1)^2}{28S^2}<u\le
u_v=\frac34+\frac{2(x-1)^2}{SZ}.
\tag{2}
\]

The upper comparison uses \(u\le V(x)\) on the complete exact
equal-secant domain; a direct proof of this comparison appears in
Section 1 of the
[displacement weight note](MIXED_SMALLER_SHORT_DISPLACEMENT_WEIGHT_REDUCTION.md).
It imposes no upper restriction on \(\beta/x-1\).

When \(3/2\le x\le2\) and \(\alpha\le6/5\), a sharper upper
endpoint is

\[
u_\ell=\frac34+\frac{2(x-1)^2}{SZ}
             \frac{x-1+(\beta-x)/16}{\beta-1},
\qquad u\le u_\ell.
\tag{3}
\]

Indeed, the cubic tail in the incoming estimate is bounded by the
linear tail in (3) if
\((\beta-x)^2SZ\le6x^2(x-1)^2\). The strong order gives
\(\beta-x\le x(7x+1)/(5R)\), so it suffices that

\[
150R^2(x-1)^2-(7x+1)^2SZ>0.
\]

With \(h=x-3/2\ge0\), the left side is exactly

\[
2400h^6+30000h^5+137635h^4+287768h^3
 +\frac{557379}{2}h^2+104452h+\frac{74855}{16}>0.
\tag{4}
\]

For the polynomial formulas below write \(u=U/V\), using these
complete pairs:

| Endpoint | \(U\) | \(V\) |
|---|---|---|
| f | \(21S^2+(x-1)^2\) | \(28S^2\) |
| v | \(3SZ+8(x-1)^2\) | \(4SZ\) |
| ell | \(6SZ(\beta-1)+(x-1)^2(\beta+15x-16)\) | \(8SZ(\beta-1)\) |

## 2. Two rational tests and three enclosing domains

At a fixed outer scale set \(a=\alpha\), \(r_A=a/(a+\beta)\),
and \(T=7r_A\). The exact upper-envelope residual at two is

\[
R_2=2w-\frac12+(u-1)/r_A+r_A-1/7-E_L+\log(2/T).
\tag{5}
\]

Since \(R_\tau'\le w-3/4\), for \(2\le\tau\le T\),

\[
R_\tau\le\max\{R_2,R_2+(T-2)(w-3/4)\}.
\tag{6}
\]

For \(0<y\le1\), put \(z_y=(y-1)/(y+1)\). The finite
geometric-series integral gives

\[
\log y\le2z_y+\frac23z_y^3=:\ell(y).
\tag{7}
\]

At the actual shape \(T\ge7/3\), so this bound applies at
\(y=2/T\). Let \(\overline R_2\) denote (5) with this rational
upper value, and define

\[
F_0=\Gamma_*-c\overline R_2-g,
\qquad F_1=F_0-c(T-2)(w-3/4).
\tag{8}
\]

Each function is concave in \(u\): the Casimir expression is a
concave quadratic and each residual is affine. It therefore suffices
to prove both tests positive at the two indicated norm endpoints.

The ordered exact short secants give

\[
\beta=x+C(a-1),\qquad
\frac{8x}{9x+8}\le C\le
\frac{x(7x+1)}{4x^2+11x+1}.
\tag{9}
\]

Both endpoint coefficients increase with \(x\). The derivative
numerators are respectively \(64\) and
\(73x^2+14x+1\), over positive squared denominators. Thus
\(C\le10/13\) for \(x\le2\), while
\(C\ge8/17\) for \(x\ge1\) and \(C\ge24/43\) for
\(x\ge3/2\).

Put \(a_L(x)=(4375x+2797)/10000\). Use independent parameters
\(0\le z,A,t\le1\) in these three rational enclosing domains:

| Domain | \(x\) | \(a\) | \(C\) | Upper norm |
|---|---|---|---|---|
| S | \(1+z/2\) | \(1+(x-1)A\) | \(10/13-(66/221)t\) | v |
| A | \(3/2+z/2\) | \(6/5+(x-6/5)A\) | \(10/13-(118/559)t\) | v |
| B | \(3/2+z/2\) | \(a_L+(6/5-a_L)A\) | \(10/13-(118/559)t\) | ell |

Every row uses \(\beta=x+C(a-1)\), scale \(q=1/7\), and lower
norm endpoint f. These rows exhaust the actual outer face. If
\(x\le3/2\), use S. If \(x\ge3/2\) and \(a\ge6/5\), use A.
Otherwise use B. For the last inclusion, the scale condition is
\(a^2\ge x(x+2)/6\). When \(a_L\le1\), its lower bound follows
from \(a\ge1\). If \(a_L>1\), then \(x>8/5\), and the
concave quadratic \(x(x+2)/6-a_L(x)^2\) is positive on
\([8/5,2]\): its endpoint values are

\[
\frac{18791}{10^8},\qquad\frac{373}{3\cdot10^8}.
\tag{10}
\]

Some extra points in B have \(a<1\); they are only scalar
comparison points. All denominators below are positive there.
Indeed \(a\ge a_L(3/2)>9/10\) and \(x\ge3/2\).
If \(a<1\), then \(0<C<1\) gives
\(\beta>x+a-1>7/5\); if \(a\ge1\), then
\(\beta\ge x\ge3/2\).
On S and A, \(a\ge1\) and \(\beta\ge x\); their norm
denominators do not contain \(\beta-1\). Thus the closed endpoint
\(x=a=\beta=1\) in S causes no singularity in these rational
formulas. The logarithm was already bounded at the unchanged actual
shape; no additional root hypothesis is imposed on the extra points.

## 3. Complete numerator formulas

Set \(B=a+\beta\),

\[
D=a^2+2a\beta+1+2x-2\beta x,\quad K=6a^2+1,
\quad N=2B-7a,\quad P=2B+7a.
\]

For the specified norm pair \(U,V\), put

\[
H_N=(S^2-S+1)V-S^2U,
\]
\[
G_N=108a^4S^2V^2
 +[12a^2(2S-1)-72a^4]SVH_N-K^2H_N^2,
\]
\[
E_N=S^2(U-V)+V,\quad J_N=KE_N+(2S-1)SV,
\]
\[
W=(K^2-SK+S^2)SV+D^2SU-DJ_N,
\quad Z_N=2DSU-J_N.
\tag{11}
\]

Direct substitution into the normalized transport gives

\[
w=\frac{W}{49a^4SV},\quad
E_L=\frac{Z_N}{7a^2SV},\quad
\Gamma_* =\frac{G_N}{576a^4S^2V^2}.
\tag{12}
\]

Define

\[
\begin{aligned}
Q_0={}&2BW-\frac{49}{2}a^4SVB
 +49a^3SB^2(U-V)+49a^5SV\\
&-7a^4SVB-7a^2BZ_N,\\
Q_1={}&Q_0+(7a-2B)(W-147a^4SV/4).
\end{aligned}
\tag{13}
\]

The positive clearing denominator and the exact numerator are

\[
\mathcal D=a^4S^2V^2BP^3,
\]
\[
\mathcal P_i=\frac{BP^3G_N}{576}
 -\frac{cSVP^3Q_i}{49}
 -ca^4S^2V^2B(2NP^2+2N^3/3)-g\mathcal D.
\tag{14}
\]

In particular \(\mathcal P_i=\mathcal D F_i\). Cancel the
manifest positive factors by setting

\[
\widetilde{\mathcal P}_i=
\begin{cases}
\mathcal P_i/S^4&\text{for norm f},\\
\mathcal P_i/S^2&\text{for norm v or ell}.
\end{cases}
\tag{15}
\]

These quotients are ordinary polynomials. For example, in the f
case \(H_N=6S^2(x-1)^2\), which displays the factor in (15)
directly in (11)--(14). The v and ell cases have the corresponding
common factor \(S^2\). This cancellation is useful because it
removes positive factors that have no bearing on the sign.

Substitute each row of Section 2 into (15), and call the resulting
polynomial \(P_{d,n,i}(z,A,t)\), where \(d\) is S, A or B,
\(n\) is f, v or ell, and \(i=0,1\). Equations (1)--(15)
are full rational specifications of every polynomial below. Their
degree bounds \((D,m,n_t)\), in \((z,A,t)\), are:

| Domain and norm | \(i=0\) | \(i=1\) |
|---|---|---|
| S,f or A,f or B,f | \((12,8,6)\) | \((12,8,5)\) |
| S,v or A,v | \((14,8,6)\) | \((14,8,5)\) |
| B,ell | \((16,10,8)\) | \((16,10,7)\) |

## 4. Two binomial identities leave one-variable polynomial signs

Write \(b_{j,m}(A)=\binom mjA^j(1-A)^{m-j}\), and similarly
for \(t\). For each of the twelve polynomials, define

\[
B_{jk}(z)=\sum_{l=0}^j\sum_{s=0}^k
 \frac{\binom jl}{\binom ml}
 \frac{\binom ks}{\binom{n_t}s}
 \frac{\partial_A^l\partial_t^sP_{d,n,i}(z,0,0)}{l!s!}.
\tag{16}
\]

Expanding the binomial theorem twice gives the exact identity

\[
P_{d,n,i}(z,A,t)=
\sum_{j=0}^{m}\sum_{k=0}^{n_t}
b_{j,m}(A)b_{k,n_t}(t)B_{jk}(z).
\tag{17}
\]

All weights are nonnegative and sum to one on the unit square.
Thus the remaining sign concerns the completely specified
univariate polynomials

\[
B_{jk}(z)=\sum_{r=0}^D q_rz^r.
\tag{18}
\]

The coefficient bounds that prove their signs are printed in the
next section. They control every possible adverse term by one
positive initial block of the same polynomial.

## 5. Seventeen explicit adverse-term bounds

In each row of the table below, use every integer \(j\) in the
displayed inclusive range, and every \(0\le k\le n_t\).
The number \(p\) specifies an initial positive block; set

\[
R_{jk}=q_0+q_1+\cdots+q_p.
\tag{19}
\]

For the polynomials defined in (11)--(18), direct multiplication
and collection gives the following ordinary rational comparisons:

\[
q_0>1,\qquad q_1,\ldots,q_p\ge0,
\qquad
\boxed{q_r+\frac{d_r}{100000}R_{jk}\ge0
                  \quad(p<r\le D).}
\tag{20}
\]

The table prints the entire vector
\((d_{p+1},\ldots,d_D)\). Thus every higher coefficient has an
explicit individual bound. The last column is the sum of that
vector. No omitted coefficients or parameter subdivisions are
used. These finite comparisons are ordinary rational inequalities
between the completely specified coefficients in (11)--(18).

| Domain | Norm | Test | j range | p | Complete vector d | Sum |
|---|---|---:|---|---:|---|---:|
| S | f | 0 | 0--8 | 2 | `9345, 5902, 3750, 1458, 314, 431, 347, 77, 8, 1` | 21633 |
| S | f | 1 | 0--8 | 3 | `12347, 9301, 2875, 4790, 2856, 870, 150, 14, 1` | 33204 |
| S | v | 0 | 0--8 | 3 | `7467, 5671, 2996, 1104, 262, 61, 105, 33, 5, 1, 1` | 17706 |
| S | v | 1 | 0--8 | 3 | `385, 10334, 6482, 2229, 2875, 1937, 663, 138, 18, 2, 1` | 25064 |
| A | f | 0 | 0--8 | 1 | `24386, 24023, 12470, 4460, 1396, 1605, 545, 104, 12, 1, 1` | 69003 |
| A | f | 1 | 0--4 | 2 | `29712, 21684, 6755, 1183, 171, 19, 2, 1, 0, 1` | 59528 |
| A | f | 1 | 5--8 | 3 | `23248, 28253, 16904, 6338, 1572, 258, 27, 2, 1` | 76603 |
| A | v | 0 | 0--8 | 1 | `3041, 27850, 21578, 10160, 3337, 759, 904, 347, 75, 11, 1, 1, 1` | 68065 |
| A | v | 1 | 0--8 | 2 | `18122, 25882, 14281, 15991, 9059, 3352, 862, 156, 20, 2, 1, 1` | 87729 |
| B | f | 0 | 0--4 | 2 | `28477, 31229, 18365, 6420, 1451, 220, 24, 2, 1, 1` | 86190 |
| B | f | 0 | 5--8 | 1 | `24386, 29651, 21282, 8368, 2122, 351, 36, 3, 1, 0, 0` | 86200 |
| B | f | 1 | 0--8 | 2 | `29712, 27016, 17849, 6661, 1586, 255, 30, 3, 1, 1` | 83114 |
| B | ell | 0 | 0--1 | 3 | `701, 30634, 34427, 21615, 9065, 2684, 573, 89, 11, 1, 1, 1, 1` | 99803 |
| B | ell | 0 | 2--5 | 3 | `10661, 26813, 27126, 15590, 5982, 1604, 302, 39, 4, 1, 1, 1, 1` | 88125 |
| B | ell | 0 | 6--10 | 2 | `555, 23033, 30349, 21742, 9828, 3108, 709, 116, 14, 1, 1, 1, 0, 1` | 89458 |
| B | ell | 1 | 0--5 | 3 | `252, 21475, 30252, 20848, 9261, 2862, 635, 103, 13, 2, 1, 1, 1` | 85706 |
| B | ell | 1 | 6--10 | 3 | `13939, 22452, 19573, 9815, 3208, 713, 108, 11, 1, 1, 1, 0, 1` | 69823 |

Here is the common elementary sign argument. In any row, let
\(\theta=\sum_{r>p}d_r/100000<1\). On \(0\le z\le1\),
(20) gives

\[
\begin{aligned}
B_{jk}(z)
&\ge\sum_{r=0}^p q_rz^r
       -R_{jk}\sum_{r=p+1}^D\frac{d_r}{100000}z^r\\
&\ge q_0(1-z^p)+R_{jk}z^p(1-\theta)\\
&\ge q_0(1-\theta)>0.
\end{aligned}
\tag{21}
\]

The second inequality uses \(z^r\ge z^p\) for \(0\le r\le p\)
and \(z^r\le z^p\) for \(r>p\). The third uses
\(R_{jk}\ge q_0\). Every printed row has \(\theta<1\); the
largest is \(99803/100000\), still strictly below one. This proves
all the univariate signs. The binomial identity (17) proves all
twelve polynomial signs, and (12)--(15) prove \(F_i>0\) for both
norm endpoints on all three enclosing domains.

## 6. Return to the original covector

Concavity in \(u\), together with (2)--(3), extends the endpoint
signs to the unchanged actual incoming norm. Equations (6)--(8)
then give

\[
\Gamma_* -cR_\tau^*>g
\]

at every terminal outer scale allowed by the sharp corrected-cap
reduction. That reduction gives
\(\Gamma_{\mathrm{actual}}\ge\Gamma_*-cR_\tau^*\), so every
such actual outer face has \(\Gamma_{\mathrm{actual}}>g\).
It is incompatible with the competitive cap
\(\Gamma_{\mathrm{actual}}\le9193/50000\).

The original common covector supplies the cap throughout. The
enclosing shape parameters, norm endpoints and binomial coefficients
serve only the scalar inequality; no physical trajectory, root or
completion cost is assigned to any extra endpoint.
