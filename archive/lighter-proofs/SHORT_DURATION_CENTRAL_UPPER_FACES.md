# S1 central duration faces by beta enlargement and curvature

This completes both duration faces of
[the central duration note](../../archive/notes/MIXED_SMALLER_SHORT_CENTRAL_DURATION_FACES.md),
on its unchanged domain and with its unchanged rational norm ceiling.
It replaces that source's large endpoint generating-polynomial argument.
The separate duration-two test is not asserted here; its lower beta
face is included in the shared lower-face proof.

The mechanism is to enlarge the beta endpoint to four constant slopes,
then prove each resulting numerator increases in `x`. Its second
`x` derivative is expanded only after beta has been removed, and has
total degree eight. The remaining one-variable polynomials have degree
seven. Two of those terminal shape intervals use a split at `a=2`.
The [algebra appendix](SHORT_DURATION_CENTRAL_UPPER_ALGEBRA.md) prints
every expanded polynomial used below.

## 1. Exact source and caller

Assume
\[
12/5\le x\le9,\qquad1\le a\le(5x+4)/12,\qquad
x\le b\le x+\frac{x(7x+1)}{4x^2+11x+1}(a-1).
\tag{1}
\]
Put
\[
S=x+1,\quad M=35x+13,\quad K=x^2+2x+a^2,\quad B=a+b,
\]
\[
u=3/4+\frac{(x-1)^2(b+7x-8)}{4SM(b-1)},\qquad
D=a^2+2ab+1+2x-2bx,
\]
\[
E=S^3(u-1)+3S-1,\qquad
w=\frac{S^2(S^2-S+1)+D^2u-DE}{K^2},
\quad E_L=(2Du-E)/K,
\]
\[
q=a^2/K,\qquad T=K/(aB).
\]
For `(gamma,ell)=(1,0)` or `(8/9,-1/9)`, define exactly
\[
G_\gamma=(w-1)\gamma T+(\gamma T)^{-1}
 +(u-1)B/a+a/B+1-q-E_L+\ell+(w-3/4)/2.
\tag{2}
\]
The conclusion is
\[
\boxed{G_1<0,\qquad G_{8/9}<0\quad\hbox{on (1)}.}
\tag{3}
\]
We use subscript `8` for the second test below. The source's Section 2
already gives the elementary strict beta-convexity estimate
\[
\tfrac12(G_\gamma)_{bb}\ge(x-a)^2/(64K^2)>0.
\tag{4}
\]
Its proof uses the original `x,a` bounds and only `b>=x`; its upper beta
bound is not used. Thus (4) applies up to any enlarged upper endpoint
chosen below. This retains the source's residue calculation (7)--(13),
which has no large coefficient premise.

The [lower beta face](SHORT_DURATION_CENTRAL_LOWER_FACE.md) proves (3)
at `b=x`. Consequently it remains to prove it at an enlarged upper
endpoint. The argument is entirely scalar: no cap, root, covector or
physical trajectory is moved to an extra point. The original source's norm-substitution interface, its
[duration audit](../../archive/notes/MIXED_SMALLER_SHORT_CENTRAL_DURATION_AUDIT.md),
and its [floor-weighted-envelope caller](../../archive/notes/MIXED_SMALLER_SHORT_FLOOR_WEIGHTED_ENVELOPE.md)
remain unchanged.

## 2. Four constant beta slopes

The function `c_0(x)=x(7x+1)/(4x^2+11x+1)` increases because its
derivative numerator is `73x^2+14x+1>0`. The following slopes therefore
bound it on the indicated intervals.

| `j` | Ratio interval `[l_j,h_j]` | Slope `c_j` | `c_0(h_j)` | Upper shape `a_j` | Coordinate base `z_j` |
|---|---|---:|---:|---:|---:|
| 0 | `[12/5,5/2]` | `7/8` | `185/214` | `11/8` | 2 |
| 1 | `[5/2,3]` | 1 | `33/35` | `19/12` | 2 |
| 2 | `[3,5]` | `6/5` | `15/13` | `29/12` | 3 |
| 3 | `[5,9]` | `3/2` | `72/53` | `49/12` | 5 |

Evaluate (2) at `b=x+c_j(a-1)`. We prove its two signs on the larger
rectangle `[l_j,h_j] x [1,a_j]`. The actual point lies in that rectangle.
For this fixed substitution set `N_{j,f}=-Delta_{j,f}G_f`, where the
positive denominators are
\[
\Delta_{j,f}=d_{j,f}\,aSMK^2 L_jV_j.
\]
Here every factor and every scalar multiplier is listed explicitly.

| `j` | `L_j` | `V_j` | `d_{j,1}` | `d_{j,8}` |
|---|---|---|---:|---:|
| 0 | `7a+8x-15` | `15a+8x-7` | 64 | 576 |
| 1 | `a+x-2` | `2a+x-1` | 8 | 72 |
| 2 | `6a+5x-11` | `11a+5x-6` | 200 | 1800 |
| 3 | `3a+2x-5` | `5a+2x-3` | 8 | 144 |

These source definitions determine the numerators without expanding a
polynomial of degree ten. Differentiate twice in `x` first. With
`A=a-1`, `X=x-z_j`, the eight exact source identities are
\[
\tfrac12\partial_x^2N_{j,f}=P_{j,f}(X,A).
\tag{5}
\]
Their complete right sides appear in Section 1 of the appendix.

## 3. Positive second derivatives from elementary interval bounds

The following single rule suffices for the displayed `P` polynomials.
For a coefficient `p(A)=p_0+sum p_k A^k` of a power of `X`, and
`0<=A<=H_j=a_j-1`, discard its positive nonconstant terms and use
\[
p(A)\ge p_0+\sum_{p_k<0}p_k H_j^k.
\tag{6}
\]
All these are sums of at most seven explicit rational terms. For
`P_{0,1}`, `P_{2,1}`, `P_{2,8}`, `P_{3,1}`, `P_{3,8}`, this bound
is positive for every coefficient of `X`. For the three remaining
polynomials it gives the following complete lower bounds, discarding
only additional positive powers of `X`:
\[
P_{0,8}>-250000000+1000000000X,
\]
\[
P_{1,1}>-100000+100000X+1500000X^2,
\]
\[
P_{1,8}>-1500000-500000X+11000000X^2.
\tag{7}
\]
The first is positive for `X>=2/5`. The other two increase for
`X>=1/2` and are positive there (their values at `1/2` are `325000`
and `1000000`). Thus
\[
\partial_x^2N_{j,f}>0\quad(l_j\le x\le h_j,\ 1\le a\le a_j).
\tag{8}
\]
For `j=0,1`, rule (6) also makes every coefficient of `X^k`, `k>=3`,
positive for all `X>=0`. Differentiating the displayed sum three times
shows `partial_x^5 N>0` on `x>=2`. Differentiating four times also shows
`partial_x^6 N>0` there. These facts justify the short Taylor lower
bounds at the first two ratio endpoints in the next section.

## 4. Boundary signs use degree-seven polynomials

For `j=0`, define
\[
U_{0,f}^{(k)}(a)=\sum_{t=k}^4
 \frac{\partial_x^tN_{0,f}(2,a)}{(t-k)!}(2/5)^{t-k},\qquad k=0,1.
\]
For `j=1`, define
\[
U_{1,f}^{(k)}(a)=\sum_{t=k}^5
 \frac{\partial_x^tN_{1,f}(2,a)}{(t-k)!}(1/2)^{t-k},\qquad k=0,1.
\]
Taylor's integral remainder and the positive fifth or sixth derivative
proved above give
\[
N_{j,f}(l_j,a)\ge U_{j,f}^{(0)}(a),\qquad
\partial_xN_{j,f}(l_j,a)\ge U_{j,f}^{(1)}(a).
\tag{9}
\]
For `j=2,3`, let `U^{(0)}=N(l_j,a)` and `U^{(1)}=partial_xN(l_j,a)`
exactly. All eight pairs have the source identities
\[
U_{j,f}^{(0)}=r_{j,f}R_{j,f}(a),\qquad
U_{j,f}^{(1)}=s_{j,f}Q_{j,f}(a),
\tag{10}
\]
where the appendix prints all sixteen polynomials and these are their
positive multipliers:

| `(j,f)` | `r_{j,f}` | `s_{j,f}` |
|---|---:|---:|
| `(0,1)` | `4/625` | `1/125` |
| `(0,8)` | `1/625` | `1/125` |
| `(1,1)` | `1/32` | `1/16` |
| `(1,8)` | `1/32` | `1/16` |
| `(2,1)` | `40` | `8` |
| `(2,8)` | `40` | `4` |
| `(3,1)` | `8` | `2` |
| `(3,8)` | `8` | `2` |

Here are reproducible quadratic bounds for those degree-seven
polynomials. For a polynomial `F`, interval midpoint `m` and radius
`r`, put
\[
c_k=F^{(k)}(m)/k!,\qquad C=c_2-\sum_{k=3}^7|c_k|r^{k-2}.
\]
Taylor's finite identity gives, for `|t|<=r`,
\[
F(m+t)\ge c_0+c_1t+Ct^2.
\tag{11}
\]
The table reports scalar bounds for `F/div`: `c_0/div>v`,
`|c_1|/div<b`, and `C/div>c`. These are simple substitutions into the
printed degree-seven polynomials, not coefficient-sign certificates.
The last column is a nonnegative lower integer bound for
`v-b^2/(4c)` when `c>0`, and for `v-br+cr^2` when `c<=0`.
Every last entry is positive, so completing the quadratic or taking
its endpoints proves `F>0`. Only the `R` intervals in rows `j=2,3`
are split at `a=2`.

| Polynomial `F` | Shape interval | `div` | `v` | `b` | `c` | Lower bound |
|---|---|---:|---:|---:|---:|---:|
| `R_0,1` | `[1,11/8]` | 10000000 | 251 | 1126 | 4202 | 175 |
| `Q_0,1` | `[1,11/8]` | 100000000 | 131 | 180 | 924 | 122 |
| `R_0,8` | `[1,11/8]` | 10000000 | 547 | 5881 | 93281 | 454 |
| `Q_0,8` | `[1,11/8]` | 100000000 | 715 | 853 | 5400 | 681 |
| `R_1,1` | `[1,19/12]` | 10000 | 224 | 856 | 2425 | 148 |
| `Q_1,1` | `[1,19/12]` | 10000 | 642 | 829 | 3191 | 588 |
| `R_1,8` | `[1,19/12]` | 10000 | 101 | 764 | 12325 | 89 |
| `Q_1,8` | `[1,19/12]` | 100000 | 323 | 296 | 1748 | 310 |
| `R_2,1` | `[1,2]` | 100000 | 159 | 239 | 428 | 125 |
| `R_2,1` | `[2,29/12]` | 100000 | 628 | 814 | -1156 | 408 |
| `Q_2,1` | `[1,29/12]` | 1000000 | 446 | 580 | 588 | 302 |
| `R_2,8` | `[1,2]` | 100000 | 698 | 161 | 1832 | 694 |
| `R_2,8` | `[2,29/12]` | 1000000 | 162 | 21 | -1534 | 91 |
| `Q_2,8` | `[1,29/12]` | 10000000 | 518 | 373 | 602 | 460 |
| `R_3,1` | `[1,2]` | 1000000 | 273 | 78 | 17 | 183 |
| `R_3,1` | `[2,49/12]` | 1000000 | 605 | 398 | -71 | 113 |
| `Q_3,1` | `[1,49/12]` | 10000000 | 374 | 182 | 37 | 150 |
| `R_3,8` | `[1,2]` | 1000000 | 4478 | 978 | 61 | 557 |
| `R_3,8` | `[2,49/12]` | 10000000 | 834 | 435 | -278 | 79 |
| `Q_3,8` | `[1,49/12]` | 100000000 | 587 | 249 | 41 | 208 |

Equations (9)--(11) prove both `N(l_j,a)>0` and
`partial_xN(l_j,a)>0`. Integrating (8) first gives a positive first
derivative on the rectangle, then `N(x,a)>=N(l_j,a)>0`. Since every
`Delta` is positive, both upper-endpoint tests are negative. Convexity
(4), the shared lower beta face, and the slope enclosure finish (3)
on the exact original domain (1).

## 5. Size, dependency and validation audit

The only two-variable expanded identities are the eight second
derivatives in the appendix, each of total degree eight and fewer than
sixty monomials. The sixteen boundary/Taylor polynomials have degree
seven and eight monomials each. All expanded coefficients have at most
twelve digits. The scalar quadratic comparisons use the original
polynomials directly; there is no high-degree common denominator,
multivariate coefficient-norm family, or executable sign premise.
The beta-convexity residue calculation is the original source's
independent elementary Section 2. The only other sign dependency is
the completed [lower beta face](SHORT_DURATION_CENTRAL_LOWER_FACE.md).

Exact rational algebra checked the source identities, scalar bounds,
Taylor multipliers and counts. The printed identities and inequalities
supply the proof independently of that check. No Lean compilation,
Lake, typechecking or CI was run.
