# S1 central tau-two by a slanted shape boundary

This completes the central `tau=2` sign on the unchanged domain of
[the original tau-two note](../../archive/notes/MIXED_SMALLER_SHORT_CENTRAL_TAU_TWO_SIGN.md).
It replaces that note's high-degree endpoint expansion with four
second derivatives of degree eight, degree-seven boundary values,
and two one-variable third derivatives. Every polynomial used in a
sign comparison is printed in the [algebra appendix](SHORT_DURATION_CENTRAL_TAU_TWO_ALGEBRA.md).

## 1. Source, caller, and the beta reduction

Assume
\[
12/5\le x\le9,\qquad 1\le a\le(5x+4)/12,\qquad
x\le b\le x+c_0(x)(a-1),\qquad
c_0(x)=\frac{x(7x+1)}{4x^2+11x+1}.
\tag{1}
\]
Set
\[
\begin{gathered}
S=x+1,\quad M=35x+13,\quad K=x^2+2x+a^2,\quad q=a^2/K,\\
u=\frac34+\frac{(x-1)^2(b+7x-8)}{4SM(b-1)},\qquad
D=a^2+2ab+1+2x-2bx,\qquad E=S^3(u-1)+3S-1,\\
w=\frac{S^2(S^2-S+1)+D^2u-DE}{K^2},\qquad
E_L=\frac{2Du-E}{K}.
\end{gathered}
\tag{2}
\]
The rational test is exactly
\[
G_2=\frac52w+(u-1)\frac{a+b}{a}
 +\frac{a}{a+b}-q-E_L+\frac{5q(a+b)}{2a}-\frac{151}{72}.
\tag{3}
\]
The intended conclusion is `G_2<0`. Equations (1)--(3) are equations
(1)--(3) of the source after replacing its `alpha,beta,H` by `a,b,K`
and multiplying its auxiliary `E` by `S²`.

The source's Sections 1--2 already give the elementary logarithm
majorant and the valid incoming-norm comparison at the actual central
face. Its Section 3 proves `partial_b²G_2>0`: the quadratic leading
coefficient is positive, and the two pole residues are positive.
That proof uses (1)'s bounds on `x,a` and only `b>=x`, so the same
convexity holds up to every larger beta endpoint used here.
The [shared lower-face lemma](SHORT_DURATION_CENTRAL_LOWER_FACE.md)
proves (3) at `b=x`.

Thus it suffices to prove (3) at `b=x+c_j(a-1)` in each of the four
rows below. For the actual `x,a`, convexity bounds every original beta
point by the chord joining this enlarged endpoint to `b=x`.

| `j` | `[l_j,h_j]` | `c_j` | `c_0(h_j)` | `a_j=(5h_j+4)/12` | `z_j` | extra shape bound |
|---|---|---|---|---|---|---|
| 0 | `[12/5,5/2]` | `7/8` | `185/214` | `11/8` | 2 | none |
| 1 | `[5/2,3]` | `1` | `33/35` | `19/12` | 2 | `x>=2a-1/3` |
| 2 | `[3,5]` | `5/4` | `15/13` | `29/12` | 3 | `x>=2a-1/2` |
| 3 | `[5,9]` | `3/2` | `72/53` | `49/12` | 5 | `x>=2a` |

Here `c_0'(x)=(73x²+14x+1)/(4x²+11x+1)²>0`, so all slope
enclosures hold. The three extra shape bounds follow directly from
`a<=(5x+4)/12`, respectively using `x>=2`, `x>=1`, and `x>=4`.
They therefore impose no new hypothesis on the caller.

The exact caller is the central-scale `tau=2` branch in
[the floor-weighted envelope](../../archive/notes/MIXED_SMALLER_SHORT_FLOOR_WEIGHTED_ENVELOPE.md),
as audited in
[the order-and-scale audit, Section 13](../../archive/notes/MIXED_SMALLER_SHORT_ORDER_AND_SCALE_AUDIT.md).
No claim about an outer scale or a smaller ratio range is used here.

## 2. Curvature after removing beta

For each row put
\[
N_j(x,a)=-\Delta_j(x,a)\,G_2(x,a,x+c_j(a-1)),\qquad
\Delta_j=d_j aSMK^2L_jV_j,
\tag{4}
\]
where

| `j` | `d_j` | `L_j` | `V_j` |
|---|---|---|---|
| 0 | 576 | `7a+8x-15` | `15a+8x-7` |
| 1 | 72 | `a+x-2` | `2a+x-1` |
| 2 | 144 | `5a+4x-9` | `9a+4x-5` |
| 3 | 72 | `3a+2x-5` | `5a+2x-3` |

Every factor in `Delta_j` is positive when `x>=l_j,a>=1`.
Definition (4) is kept factored. Differentiating first, and then
putting `X=x-z_j`, `A=a-1`, gives the four identities
\[
\frac12\partial_x^2N_j(x,a)=P_j(X,A).
\tag{5}
\]
The appendix prints all four `P_j`: each has 41 monomials and total
degree eight. There is no expansion of (4) itself.

For a polynomial `p(A)` and `0<=A<=H`, the elementary coefficient
bound
\[
p(A)\ge p(0)+\sum_{k\ge1:\,[A^k]p<0}[A^k]p\,H^k
\tag{6}
\]
follows by discarding its positive nonconstant terms and bounding its
negative terms separately. Apply (6) to every coefficient of `X^k` in
`P_j`, with `H=a_j-1`. For `j=2,3` all resulting coefficients are
strictly positive. For `j=0,1`, the same calculation gives
\[
\begin{aligned}
P_0(X,A)&>-320000000+100000000X+4400000000X^2,\\
P_1(X,A)&>-1700000-2300000X+7000000X^2+15000000X^3.
\end{aligned}
\tag{7}
\]
All omitted coefficients have positive lower bounds. At `X=2/5` the
first displayed polynomial equals `424000000`; it increases thereafter.
At `X=1/2` the second equals `775000`; its derivative is positive
thereafter. Hence
\[
\partial_x^2N_j>0\quad
(l_j\le x\le h_j,\ 1\le a\le a_j).
\tag{8}
\]
The same coefficient calculation for `P_0` shows that every coefficient
of `X^k`, `k>=3`, is positive already for `X>=0`. Consequently the
fifth and sixth `x` derivatives of `N_0` are positive on `x>=2` for
`1<=a<=11/8`. This justifies the two short Taylor lower bounds used
in the first row of the next section.

## 3. Values and first derivatives on the horizontal edges

Put `t_0=11/8,t_1=17/12,t_2=7/4,t_3=5/2`.
The appendix prints eight degree-seven polynomials `R_j,Q_j` with
\[
N_j(l_j,a)\ge r_jR_j(a),\qquad
\partial_xN_j(l_j,a)\ge s_jQ_j(a),
\tag{9}
\]
where

| `j` | `r_j` | `s_j` | value comparison |
|---|---|---|---|
| 0 | `4/625` | `1/125` | Taylor lower bounds at `x=2`, through orders 4 and 5 respectively |
| 1 | `3/256` | `1/128` | equalities |
| 2 | `2` | `1` | equalities |
| 3 | `24` | `2` | equalities |

For clarity, the first-row polynomials are defined exactly by
\[
\begin{aligned}
\frac4{625}R_0(a)&=\sum_{k=0}^{4}
 \frac{\partial_x^kN_0(2,a)}{k!}(2/5)^k,\\
\frac1{125}Q_0(a)&=\sum_{k=1}^{5}
 \frac{\partial_x^kN_0(2,a)}{(k-1)!}(2/5)^{k-1}.
\end{aligned}
\tag{10}
\]
The positive fifth and sixth derivatives proved above give the two
lower remainders. The other six identities are direct restrictions
to a constant `x`, before expansion.

Here is a short rational check of the needed signs. For any listed
polynomial `F`, interval `[p,q]`, and positive divisor `d`, set
`m=(p+q)/2`, `rho=(q-p)/2`, and
\[
c_k=\frac{F^{(k)}(m)}{d\,k!},\qquad
C=c_2-\sum_{k=3}^{7}|c_k|\rho^{k-2}.
\]
If `c_0>=v`, `|c_1|<=b`, and `C>=c`, then, for `|t|<=rho`,
\[
F(m+t)/d\ge v-b|t|+ct^2.
\tag{11}
\]
The following integer bounds are obtained by substitution into the
printed polynomials. The last column is a lower bound for (11) on
the interval: use its endpoint, or `v-b²/(4c)` if `c>0` and the
vertex `b/(2c)` is inside `[0,rho]`. Every entry is positive.

| `F` | interval | `d` | `v` | `b` | `c` | lower bound |
|---|---|---|---|---|---|---|
| `R_0` | `[1,5/4]` | 10000000 | 234 | 41 | 18523 | 233 |
| `R_0` | `[5/4,11/8]` | 10000000 | 700 | 1780 | -38883 | 436 |
| `Q_0` | `[1,11/8]` | 100000000 | 659 | 1407 | 10323 | 611 |
| `R_1` | `[1,17/12]` | 100000 | 78 | 119 | -575 | 28 |
| `Q_1` | `[1,19/12]` | 1000000 | 269 | 663 | 2576 | 226 |
| `R_2` | `[1,7/4]` | 100000 | 563 | 79 | -1923 | 262 |
| `Q_2` | `[1,2]` | 1000000 | 891 | 1221 | 1764 | 679 |
| `Q_2` | `[2,29/12]` | 1000000 | 2766 | 1746 | -11469 | 1904 |
| `R_3` | `[1,5/2]` | 1000000 | 668 | 596 | 192 | 329 |
| `Q_3` | `[1,2]` | 100000000 | 142 | 125 | 41 | 89 |
| `Q_3` | `[2,49/12]` | 100000000 | 524 | 382 | -89 | 29 |

It follows that `N_j(l_j,a)>0` for `1<=a<=t_j`, and
`partial_xN_j(l_j,a)>0` for the full `1<=a<=a_j`.
Together with (8), the latter gives `partial_xN_j(x,a)>0` everywhere
in the rectangle. Row zero is finished, and in each other row only
`t_j<=a<=a_j` remains.

## 4. The three slanted edges

For rows `j=1,2,3`, write respectively
\[
o_1=1/3,\quad o_2=1/2,\quad o_3=0,\qquad
B_j(a)=N_j(2a-o_j,a).
\tag{12}
\]
If `a>=t_j`, the point `x=2a-o_j` belongs to `[l_j,h_j]`; the
shape bound in the first table puts the actual `x` to its right.
The positive `x` derivative therefore gives `N_j(x,a)>=B_j(a)`.

For `j=1,2`, differentiate (12) three times before expanding. With
`A=a-1`, the identities are
\[
B_1'''(a)=\frac{32}{243}H_1(A),\qquad
B_2'''(a)=\frac34H_2(A).
\tag{13}
\]
The appendix prints their eight-term degree-seven polynomials.
For `A>=5/12`, all higher coefficients of `H_1` are positive, so
\[
H_1(A)\ge5046058620A^2-592799424A-141809168>0.
\tag{14}
\]
The final quadratic has positive value and positive derivative at
`5/12`, and its second derivative is positive. For `A>=3/4`, the
only negative coefficients of `H_2` have degrees at most two. Thus
\[
\begin{aligned}
H_2(A)&\ge A^4\left(298956342370
 -\frac{36420689010}{(3/4)^2}
 -\frac{12340661469}{(3/4)^3}
 -\frac{1097447104}{(3/4)^4}\right)\\
&>200000000000A^4>0.
\end{aligned}
\tag{15}
\]

At `a=t_j`, Section 3 already gives `B_j(t_j)>0`. The two other
initial values obey
\[
\begin{array}{c|cc}
j&B_j'(t_j)&B_j''(t_j)\\\hline
1&>4800000&>89000000\\
2&>1900000000&>25000000000
\end{array}
\tag{16}
\]
These are four scalar rational evaluations, not additional polynomial
premises. They can be checked directly from the printed polynomials:
since (9) is an equality in these rows,
\[
\begin{aligned}
B_j'(t_j)&=r_jR_j'(t_j)+2s_jQ_j(t_j),\\
B_j''(t_j)&=r_jR_j''(t_j)+4s_jQ_j'(t_j)
       +8P_j(l_j-z_j,t_j-1).
\end{aligned}
\tag{17}
\]
The identities (13)--(17) imply successively `B_j''>0`, `B_j'>0`,
and `B_j>0` throughout the two remaining shape intervals.

For row three no derivative argument is necessary: after restricting
`x=2a`, remove the positive factor `3a²` before expanding. The result is
\[
B_3(a)=3a^2H_3(a-2).
\tag{18}
\]
The appendix prints all nine coefficients of the degree-eight `H_3`;
each is positive. Here `a>=5/2`, so (18) is strictly positive.

All four upper endpoints are therefore negative by (4).
The lower beta face and convexity from Section 1 complete `G_2<0`
on the entire original domain (1).

## 5. Audit and scope

The four curvature identities use 41 monomials each, total degree
eight in two variables. The eight horizontal-edge polynomials have
eight monomials each and degree seven. The two slanted-edge third
derivatives have eight monomials each and degree seven; the last
slanted edge has nine monomials and degree eight after division by
`3a²`. All displayed polynomial coefficients have at most 12 decimal
digits. There are four fixed ratio intervals, one split at `a=5/4`
for `R_0`, and a split at `a=2` for each of `Q_2,Q_3`; there is no
adaptive subdivision.

The incoming norm comparison, logarithm tangent estimate, and beta
convexity are the elementary parts of the same source statement;
they are preserved, not assumed anew. The source's high-degree
endpoint coefficient argument is replaced in full. Exact symbolic
arithmetic was used only to check the displayed source identities
and rational roundings. No executable sign cover, external coefficient
table, or Lean computation is a premise. No Lean source was changed.
