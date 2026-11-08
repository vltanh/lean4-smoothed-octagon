# S6: angle concavity and four small endpoint curves

This replaces equations (20)--(31) of
[the small-shape physical-cost exclusion](../../archive/notes/MIXED_SMALLER_SHORT_SMALL_SHAPE_COST_EXCLUSION.md).
It proves the same strict lower bound for the same scalar expression, on the
same domain. Sections 1--4 of that note, including the corrected provenance of
the original outer scale cap, are retained. Its large polynomials `W_e`, their
coefficient majorants, and their degree-24 endpoint expansions are not used.

The replacement first uses the already proved concavity in the angle `T` to
fix `e=13/5` or `e=3`. It then proves concavity in the other angle `r=R` by
ordinary differentiation of small rational functions. The four remaining
curves decrease in the displacement `d`. Only the two curves with `e=3`
use a split, at `d=1/38`.

Every expanded polynomial below is univariate, of degree at most five;
the two-variable source identities have degree at most four. Rational
functions are differentiated as quotients and products. Their denominators
are never multiplied into one polynomial.

## 1. Keep the cancellations before differentiating

Write
\[
 1/3\le r\le7/19,\qquad 0\le d\le1/19,
 \qquad e\in\{13/5,3\},\qquad c=161/54.
\]
The argument below also proves angle concavity for every `13/5<=e<=3`.
Put
\[
 C=e+1-(e-1)r,\quad E=(e+1)r-(e-1),\quad
 B=2+Cd,\quad N=2r+Ed,\quad t=N/B,
\]
\[
 v=4u_q-3=v_0(r)+dv_1(r)+d^2v_2(r),\qquad
 z=Z_U=z_0(r)+\frac{1+2r}{3(1-r)}d-\frac32d^2,
\]
\[
 z_0=\frac{2r^2(1+r)}{3-r},\qquad
 Z_L=z_0(1+11d/2),\qquad A=\frac{r^2-t^2}{3+t^2}.
\]
Here the three explicit norm coefficients are
\[
 \begin{aligned}
 v_0&=\frac{4r^2(3r^2+10r+10)}{15(r+2)^3},\\
 v_1&=-\frac{2r(r+1)(3r^2+10r+10)}{15(r+2)^3},\\
 v_2&=\frac{19(r+1)^2(3r^2+10r+10)}{315(r+2)^3}.
 \end{aligned}                                                   \tag{1}
\]
The following four one-variable functions keep the leading cubic
cancellation in the physical score:
\[
 \begin{aligned}
 k(a)&=\frac a{162}+\frac{161a^3}{1458}
                 -\frac{161a^5}{7290}-\frac{a^3}{2(3+a^2)},\\
 g(a)&=\frac{a}{2(3+a^2)},\qquad
 p(a)=\frac{a^2}{3+a^2},\qquad q(a)=\frac1{3+a^2}.
 \end{aligned}
\]
Set `K=k(r)+k(t)`, `G=g(r)+g(t)`, `P=p(r)+p(t)`,
and `Q=q(r)+q(t)`. The original score in equation (15) of the source is
exactly
\[
 \boxed{\mathcal B=K+vG-zP/8+vzQ/8-cA^2/(8Z_L).}                \tag{2}
\]
Indeed `b_i=(a_i^2-v)/(3+a_i^2)` for `a_1=r,a_2=t`, since
`4u_q=3+v`. Apply this identity separately to the two norm terms
and then to their sum multiplying `Z_U`. This checks (2) without
clearing any common denominator.

All denominators displayed in this note are positive. The original shape
bounds give `9/31<=t<=r<=7/19` and `Z_L>0`. The incoming lower bound gives
`v>0`.

## 2. Small derivative facts

### 2.1. The four primitive functions

Set `s=a^2` before collecting powers. Direct differentiation gives
\[
 \begin{aligned}
 k(a)&=-\frac{a(161s^3-322s^2+1185s-135)}{7290(s+3)},\\
 k'(a)&=-\frac{161s^4+483s^3-729s^2+2160s-81}
                    {1458(s+3)^2},\\
 \frac{k''(a)}a&=-\frac{322s^4+2415s^3+4347s^2-6534s+6642}
                         {729(s+3)^3},\\
 k'''(a)&=-\frac{322s^5+3703s^4+15456s^3+28269s^2-30672s+6642}
                         {243(s+3)^4}.
 \end{aligned}                                                   \tag{3}
\]
These are identities in the single variable `s`; the chain rule
`s'=2a` is applied before the displayed collection. For example, if
`k(a)=aJ(s)`, then `k''(a)/a=6J'(s)+4sJ''(s)`.
No degree-nine or degree-eleven polynomial in `a` is expanded.

For `9/31<=a<=7/19`, we have `1/12<s<1/7`. The numerator of `-k'`
is positive since its first, second and fourth terms, with the constant,
give at least `180-81`, while `729s^2<729/49`. The numerator of `-k'''`
exceeds `6642-30672/7>0`. Thus `k'<0`, and `k''` decreases. Exact
substitution at the two lower endpoints gives
\[
 k''(a)<-2/25\quad(a\ge9/31),\qquad
 k''(a)<-9/100\quad(a\ge1/3).                                  \tag{4}
\]

The other derivatives are
\[
 \begin{aligned}
 g'&=\frac{3-a^2}{2(3+a^2)^2},&
 g''&=\frac{a(a^2-9)}{(3+a^2)^3},\\
 p'&=\frac{6a}{(3+a^2)^2},&
 p''&=\frac{18(1-a^2)}{(3+a^2)^3},\\
 q'&=-\frac{2a}{(3+a^2)^2},&
 q''&=-\frac{6(1-a^2)}{(3+a^2)^3}.
 \end{aligned}                                                   \tag{5}
\]
In particular `g'>0,g''<0,p'>0,p''>0,q'<0,q''<0`.
The derivative of `p''` is `-72a(3-a^2)/(3+a^2)^4<0`.
Endpoint substitution therefore gives
\[
 \begin{gathered}
 g(a)<3/50,\quad g'(a)<31/200,\quad
 g'(a)<3/20\ (a\ge1/3),\\
 p'(a)>3/20,\quad p'(a)>1/5\ (a\ge1/3),\quad
 p''(a)>1/2,\quad 0<q(a)<1/3.                                  \tag{6}
 \end{gathered}
\]
The first estimate uses `g(7/19)=133/2264<3/50`.

### 2.2. The norm coefficients

For clarity, all the derivative numerators required for (1) are printed:
\[
 \begin{aligned}
 v_0'&=\frac{4r(3r^3+24r^2+50r+40)}{15(r+2)^4},&
 v_0''&=\frac{16(11r^2+20r+20)}{15(r+2)^5},\\
 v_1'&=-\frac{2(3r^4+24r^3+58r^2+60r+20)}{15(r+2)^4},&
 v_1''&=-\frac{8(7r^2+13r+10)}{15(r+2)^5},\\
 v_2'&=\frac{19(r+1)(r^3+7r^2+14r+10)}{105(r+2)^4},&
 v_2''&=\frac{38(3r^2+6r+4)}{105(r+2)^5}.
 \end{aligned}                                                   \tag{7}
\]
Positive-coefficient numerators and `1/3<=r<=7/19` give the following
loose scalar bounds. Each follows by substituting `1/3` and `7/19`
separately into numerator and denominator; for the negative row reverse
the signs. There is no coefficient sign certificate.

| Function | Lower bound | Upper bound |
|---|---:|---:|
| `v_0` | `3/100` | `201/5000` |
| `v_1` | `-3/40` | `-3/50` |
| `v_2` | `11/100` | `63/500` |
| `v_0'` | `167/1000` | `41/200` |
| `v_1'` | `-6/25` | `-1/5` |
| `v_2'` | `0` | `7/50` |
| `v_0''` | `39/100` | `223/500` |
| `v_1''` | `-1/8` | `0` |
| `v_2''` | `0` | `7/200` |

For example, in the first row the upper substitution is
`4(7/19)^2[3(7/19)^2+10(7/19)+10]/[15(7/3)^3]<201/5000`.
Applying the same operation to the other eight printed formulas is
ordinary scalar rational arithmetic. It follows that, at fixed `d`,
\[
 0<v<41/1000,
 \qquad 3/20<v_r<21/100,
 \qquad 0<v_{rr}<9/20.                                         \tag{8}
\]
For the lower derivative use `167/1000-(6/25)/19>3/20`;
for the upper second derivative use `223/500+(7/200)/361<9/20`.

### 2.3. The shape functions

The fractional-linear formula for `t` gives
\[
 t_r=\frac{(2+2d)(2+2ed)}{B^2},\qquad
 t_{rr}=\frac{2(e-1)d}{B}t_r.                                  \tag{9}
\]
To check the first numerator, cancel the quadratic terms in `r` in
`N_rB-NB_r`; the result is the printed product.
Furthermore
\[
 (2+2d)(2+2ed)-B^2
 =4(e-1)rd+(4e-C^2)d^2.
\]
Since `C<=4`, its right side is nonnegative:
`4(e-1)r-C^2d >=32/15-16/19>0` when `d>0`.
For an upper bound, divide by `B^2>=4` and discard `-C^2d^2`:
\[
 1\le t_r\le1+17/361<17/16,\qquad
 0\le t_{rr}<17/152.                                          \tag{10}
\]

The already proved central shape bound gives `1/9<=z<1/5`.
For its derivatives use the short division
\[
 z_0=-2r^2-8r-24+72/(3-r),\quad
 z_0'=-4r-8+72/(3-r)^2,\quad z_0''=-4+144/(3-r)^3.
\]
Both `z_0'` and `z_0''` increase. Also
\[
 z_r=z_0'+d/(1-r)^2,\qquad
 z_{rr}=z_0''+2d/(1-r)^3.
\]
Substitution at the two endpoints gives
\[
 19/24\le z_r<16/15,\qquad 115/32\le z_{rr}<13/3.              \tag{11}
\]

## 3. Concavity in r without a cleared polynomial

All derivatives in this section hold `d,e` fixed.
Equations (4), (9) and `k'<0` give
\[
 K_{rr}=k''(r)+k''(t)t_r^2+k'(t)t_{rr}<-17/100.                 \tag{12}
\]
From (5), (6) and (10),
\[
 0<G<3/25,\quad 0<G_r<8/25,\quad G_{rr}<1/50.
\]
For the last inequality discard the two negative `g''` terms and use
`g'(t)t_{rr}<(31/200)(17/152)<1/50`. Thus
\[
 (vG)_{rr}
 <(9/20)(3/25)+2(21/100)(8/25)+(41/1000)(1/50)
 <19/100.                                                       \tag{13}
\]
Similarly `P>3/50`, `P_r>7/20`, and `P_{rr}>1`. For the first,
`p(1/3)+p(9/31)=1/28+27/988>3/50`; the other two follow from
(6), `t_r>=1` and `t_{rr}>=0`. Consequently
\[
 (zP/8)_{rr}
 >\frac18\left\{\frac{115}{32}\frac3{50}
              +2\frac{19}{24}\frac7{20}+\frac19\right\}
 >1/10.                                                        \tag{14}
\]
We have `Q_r<0,Q_{rr}<0,Q<2/3`. The factors `v,z,v_r,z_r`
are positive, so the terms containing these negative derivatives may
be discarded from an upper bound. Hence
\[
 (vzQ/8)_{rr}
 <\frac1{12}\left\{\frac9{20}\frac15
          +2\frac{21}{100}\frac{16}{15}
          +\frac{41}{1000}\frac{13}{3}\right\}<3/50.             \tag{15}
\]

### The small radical correction

The exact cancellation
\[
 rB-N=(e-1)(1-r^2)d
\]
removes the apparent `r^{-2}` singularity before differentiation. Put
\[
 F=(1-r)^2(1+r)(3-r)=3-4r-2r^2+4r^3-r^4,
\]
\[
 H=4+2(e+1)d-(e-1)d(r+r^{-1}),\quad J=3B^2+N^2,
 \quad h=H/J.
\]
Then
\[
 \boxed{\frac{cA^2}{8Z_L}
   =\frac{161(e-1)^2d^2}{432(2+11d)}Fh^2.}                     \tag{16}
\]
The coefficient outside `Fh^2` is constant in `r`. The following
deliberately loose bounds suffice:
\[
 0<F<8/5,\quad |F_r|<21/5,\quad |F_{rr}|<10/3,
\]
\[
 4\le H<21/5,\quad 0\le H_r\le16/19,\quad -108/19\le H_{rr}\le0,
\]
\[
 J>12,\quad 0<J_r<10/3,\quad 0<J_{rr}<10.                       \tag{17}
\]
Here `F_r=-4-4r+12r^2-4r^3` and `F_{rr}=-4+24r-12r^2`.
For `H`, use `r+r^{-1}<=10/3`,
`H_r=(e-1)d(r^{-2}-1)` and `H_{rr}=-2(e-1)dr^{-3}`.
The coefficient of `d` in `H-4` is nonnegative; its minimum is
at `e=3,r=1/3`, where it is `4/3`. Its upper bound `16/5`
gives `H<=4+16/95<21/5`.

For the last row, `12/19<=N<=14/19` and `2<=B<=42/19` give
\[
 J_r=-6(e-1)dB+2N[2+(e+1)d]
 \ge408/361>0,
\]
\[
 J_r\le1176/361<10/3,\qquad
 J_{rr}=6(e-1)^2d^2+2[2+(e+1)d]^2\le3552/361<10.
\]
The quotient rule now gives directly
\[
 0<h<7/20,\qquad |h_r|<1/10,\qquad |h_{rr}|<5/6.                \tag{18}
\]
For the only slightly longer bound, use
\[
 h_{rr}=H_{rr}/J-2H_rJ_r/J^2-HJ_{rr}/J^2+2HJ_r^2/J^3.
\]
Its lower bound from (17) is
`-9/19-20/513-7/24>-5/6`; its upper bound is `35/648<5/6`.
Therefore
\[
 |(Fh^2)_{rr}|
 <\frac{10}{3}\left(\frac7{20}\right)^2
 +4\frac{21}{5}\frac7{20}\frac1{10}
 +2\frac85\left\{\frac1{100}+\frac7{20}\frac56\right\}<2.
\]
Equation (16) implies
\[
 \left|\left(\frac{cA^2}{8Z_L}\right)_{rr}\right|
 <\frac{161}{38988}<1/100.                                     \tag{19}
\]

Combining (12)--(15) and (19) in (2),
\[
 \boxed{\mathcal B_{rr}<-17/100+19/100-1/10+3/50+1/100=-1/100.} \tag{20}
\]
The minimum in `r` is consequently attained at `r=1/3` or `r=7/19`.
This conclusion holds on the entire displacement interval and has used
no domain subdivision.

## 4. The four endpoint curves decrease in d

Fix one of those two values of `r` and one of the two values of `e`.
Now differentiation means differentiation in `d`. We have
\[
 t'=-2(e-1)(1-r^2)/(2+Cd)^2<0,\qquad
 t''=-2Ct'/(2+Cd)>0.
\]
The explicit quadratic (1) gives `v'<0,v''>0`; `z'>0,z''=-3`.
These signs also follow immediately by substituting the four fixed
pairs into the printed formulas.

The correction `A^2/Z_L` is increasing. To see this at `d>0`, write
\[
 A=(e-1)(1-r^2)d(rB+N)/J.
\]
The derivative of `rB+N` is `2(e+1)r-(e-1)(1+r^2)>0`;
its minimum on the whole shape rectangle is at `e=3,r=1/3`,
where it is `4/9`. Also `J_d<=6BC<6(42/19)4`, while `J>12`.
Thus
\[
 \frac{d}{dd}\log(A^2/Z_L)
 \ge\frac2d-2J_d/J-\frac{11}{2+11d}
 >38-\frac{168}{19}-\frac{11}{2}>0.
\]
At zero the derivative extends continuously as zero. Its negative
contribution to `mathcal B'` may therefore be discarded.

Here is an explicit scalar upper-bound recipe for the other four terms;
it makes the endpoint arithmetic reproducible without any polynomial
coefficient list. On a displacement interval `[l,h]`, append subscripts
`l,h` for endpoint evaluation. Let
\[
 \begin{aligned}
 M_1={}&k'(t_l)t'_l,\\
 M_2={}&v'_h\{g(r)+g(t_h)\}+v_hg'(t_l)t'_h,\\
 M_3={}&\{-z'_h[p(r)+p(t_h)]-z_h p'(t_l)t'_l\}/8,\\
 M_4={}&\{v'_h z_l[q(r)+q(t_l)]
       +v_lz'_l[q(r)+q(t_h)]+v_lz_h q'(t_l)t'_l\}/8.
 \end{aligned}                                                   \tag{21}
\]
Then `mathcal B'<=M_1+M_2+M_3+M_4`. For example, `-k'(t)` and
`-t'` both decrease with `d`, proving the first bound. For the second,
`v'` is negative and increases, while `G` and `v` decrease; use
`g''<0` and the smallest magnitude of `t'` for its second negative
term. The third follows from `z'P` being positive and decreasing and
`-zp'(t)t'` being positive. For the fourth, bound its negative term
using `v'_h,z_l,Q_l`, and the two positive terms using their indicated
endpoints. Equations (5)--(7) give all these signs.

The table contains upward integer roundings of the four rational
numbers `10^6 M_i`, not polynomial coefficients. Each entry is obtained
by substitution into (21), whose complete functions and derivatives
are printed above.

| `r` | `e` | `[l,h]` | `10^6 M_1 <` | `10^6 M_2 <` | `10^6 M_3 <` | `10^6 M_4 <` | Sum of upper bounds |
|---|---|---|---:|---:|---:|---:|---:|
| `1/3` | `13/5` | `[0,1/19]` | 7594 | -7880 | -2683 | 1711 | -1258 |
| `7/19` | `13/5` | `[0,1/19]` | 9647 | -9627 | -3920 | 2202 | -1698 |
| `1/3` | `3` | `[0,1/38]` | 9492 | -9671 | -3280 | 1657 | -1802 |
| `1/3` | `3` | `[1/38,1/19]` | 7087 | -8473 | -2330 | 1325 | -2391 |
| `7/19` | `3` | `[0,1/38]` | 12059 | -11663 | -4575 | 2133 | -2046 |
| `7/19` | `3` | `[1/38,1/19]` | 9453 | -10323 | -3430 | 1734 | -2566 |

In particular all four curves have `mathcal B'<-1/1000` on their
whole interval. Their minima are at `d=1/19`.

## 5. Four scalar values and the original physical conclusion

At `d=1/19`, evaluate the four original summands
\[
 L(r)+L(t),\quad -(b_1r+b_2t)/2,\quad -(b_1+b_2)Z_U/8,
 \quad -cA^2/(8Z_L),
\]
where `L(a)=a/162+161a^3/1458-161a^5/7290` and
`b_1=(r^2-v)/(3+r^2), b_2=(t^2-v)/(3+t^2)`.
The following are downward integer roundings after multiplication
by `10^9`. They are four scalar substitutions, with no interval or
coefficient certificate premise.

| `r` | `e` | First summand | Second | Third | Fourth | Sum of lower bounds |
|---|---|---:|---:|---:|---:|---:|
| `1/3` | `13/5` | 10790800 | -7326631 | -867012 | -130591 | 2466566 |
| `1/3` | `3` | 10505273 | -7017008 | -837436 | -196747 | 2454082 |
| `7/19` | `13/5` | 13760080 | -10063064 | -1317484 | -118831 | 2260701 |
| `7/19` | `3` | 13424505 | -9684961 | -1278205 | -179792 | 2281547 |

All four sums exceed `2260000`. The original concavity in `T`, then
(20), and then the endpoint-curve signs prove
\[
 \boxed{\mathcal B(u_q;r,t,d)>113/50000.}                        \tag{22}
\]
The original target is
\[
 b_* =792669623/356040000000 <223/100000.
\]
Thus the replacement proves the stronger explicit margin
\[
 \mathcal B-b_*>3/100000.
\]
Section 7 of the source cost note now applies unchanged and gives
`C_period>A_oct` for the original physical period. In particular the
actual Casimir floor, the same covector, the incoming norm and both
initial scale bounds remain caller hypotheses or previously proved
facts; none is assigned to an artificial comparison point.

## 6. Identity sizes and validation boundary

The largest printed primitive numerator is the six-term degree-five
polynomial in (3), with largest coefficient `30672`. The norm formulas
(1) and (7) have expanded numerator degree at most four and at most
five monomials. The polynomial `F` has five monomials and degree four.
The fractional-linear identities (9), (16) follow from the displayed
quadratic identities for `B,N`, with `e` fixed before collection; their
two-variable expansions have degree at most four. The derivative
rules in Sections 2--4 operate on these separate factors, never on a
common high-degree numerator. The scalar comparisons in the two
endpoint tables use rationals with at most nine-digit displayed
numerators; they are not multivariate expansion coefficients.

Exact rational arithmetic was used to check the source cancellation,
the printed derivative identities, all rounded inequalities and all
scalar endpoint values. The proof consists of the displayed identities
and ordinary inequalities, and does not depend on that computation.
No Lean compilation, Lake, typechecking or CI was run.
