# A strict forward threshold at a whole-period minimum margin

Date: 2026-11-07 UTC. Hand inequalities with a supplementary exact
checker. No Lean, Lake, typechecking, or CI.

## Statement and scope

Consider an actual competitive finite normal geometric period, with
the common negative elliptic primary costate already proved in
[MIXED_GLOBAL_COSTATE_ELLIPTIC](MIXED_GLOBAL_COSTATE_ELLIPTIC.md).
Use the normalized multiplier `U`, put `gamma=sqrt(det U)>0`, and use
the auxiliary sequence `b` of
[MIXED_GLOBAL_SCALAR_DUAL](MIXED_GLOBAL_SCALAR_DUAL.md).

Suppose the active margin `a_i` is a global minimum of the period,
and both its incident switches are forward. If the period is entirely
forward, assume `N>=7`; this is exactly the remaining entirely forward
domain beyond the retained through-five comparisons. Mixed periods
need no additional piece-count assumption here. Then

\[
\boxed{b_i>2\gamma a_i^2.}
\tag{1}
\]

This statement is restricted to a **whole-period global minimum at a
`++` site**. A bound of this kind at an arbitrary forward site does
not follow from the Casimir cap and local switch inequalities.

The onsite two-variable term in the scalar dual Hessian is therefore
negative definite at this site. This is a concrete input to a possible
global negative-subspace argument. The positive contributions from
adjacent forward edges are still present, so the result is **not** a
negative principal-block theorem, an endpoint-preserving variation,
or a closure of F or M2.

## 1. A slightly sharper rational Casimir cap

The exact octagon cost in
[GLOBAL_NUMERICAL_REDUCTION](GLOBAL_NUMERICAL_REDUCTION.md) is

\[
A_{\rm oct}=2\sqrt3\,
 \frac{8-4\sqrt2-\log2}{2\sqrt2-1}.
\]

The following rational bounds suffice:

\[
\sqrt2>\frac{141421}{100000},\qquad
\sqrt3<\frac{173206}{100000},\qquad
\log2>\frac{69314}{100000}.
\tag{2}
\]

The first two follow by squaring positive numbers. For the third,
integrating five terms of the positive geometric series gives

\[
\log2=2\int_0^{1/3}\frac{dt}{1-t^2}
>2\sum_{j=0}^{4}\frac1{(2j+1)3^{2j+1}}
=\frac{4297606}{6200145}
>\frac{69314}{100000}.
\]

The numerator of the exact octagon expression is positive, as in the
earlier numerical-reduction proof. Substituting (2) in the indicated
directions yields

\[
A_{\rm oct}<\frac{649530373}{207775000}
<\frac{2501}{800}.
\tag{3}
\]

The same Machin identity used there gives
`pi=16 atan(1/5)-4 atan(1/239)`. Four alternating terms for the first
arctangent, and `atan(1/239)<1/239`, imply

\[
\pi>
16\left(\frac15-\frac1{3\cdot5^3}
 +\frac1{5\cdot5^5}-\frac1{7\cdot5^7}\right)-\frac4{239}
=\frac{1231847548}{392109375}
>\frac{6283}{2000}.
\tag{4}
\]

The complete-period cost--Casimir inequality consequently gives

\[
\kappa\le\frac{3A_{\rm oct}}{4\pi-2A_{\rm oct}}
<\frac{3(2501/800)}{4(6283/2000)-2(2501/800)}
=\frac{205}{138}.
\]

Since `kappa=sqrt(12) gamma`, this proves

\[
\boxed{\gamma^2<\frac{42025}{228528}<\frac{23}{125}<\frac3{16}.}
\tag{5}
\]

The difference between the middle two fractions is
`3019/28566000>0`. The whole-period cost bound and the actual endpoint
are essential inputs to (5); conservation of the Casimir alone would
not supply it.

## 2. The necessary scale bound at the global minimum

### Entirely forward periods

Write `m=min_i a_i`. The normalized signed cyclic action on an entirely
forward period is

\[
8J(a)=\sum_i\left[3a_i a_{i+1}-4
-a_i^2\log\frac{(a_{i-1}+a_i)(a_i+a_{i+1})}{a_i^2+4}\right],
\qquad J=C/\sqrt{12}.
\tag{6}
\]

Its every partial derivative is strictly positive on the entire
positive orthant. This is the scalar derivative calculation of
[GLOBAL_STRUCTURE_CYCLIC_COSTATE_SECTOR](GLOBAL_STRUCTURE_CYCLIC_COSTATE_SECTOR.md):
with `R=(a_(i-1)+a_i)/a_i>1`, `T=(a_i+a_(i+1))/a_i>1`, and
`V=(a_i^2+4)/a_i^2>1`, one has

\[
\frac4{a_i}\frac{\partial J}{\partial a_i}
=f(R)+f(T)+h(V)>0,
\]

where `f(x)=x-x^-1-log x` and `h(x)=log x-1+x^-1` are positive
for `x>1`. Coordinatewise comparison in (6) therefore gives

\[
J(a)\ge J(m,\ldots,m)
=\frac N8\left[3m^2-4
-m^2\log\frac{4m^2}{m^2+4}\right].
\tag{7}
\]

This is a scalar inequality, not a deformation through closed
trajectories. Some intermediate arrays may have a factor at most one;
the derivative identity remains valid there because all its logarithms
are defined for positive margins.

If `m^2>=20/11` and `N>=7`, monotonicity and (7) give

\[
J(a)\ge\frac7{22}\left[4-5\log\frac54\right]
>\frac{161}{176}.
\]

Here `log(5/4)<43/192<9/40`, using three terms of the alternating
logarithm expansion, or its integrated geometric remainder.
Since `sqrt(12)>173/50`, it follows that

\[
C>\frac{27853}{8800}>\frac{313}{100}>A_{\rm oct},
\]

contrary to competitiveness. Thus

\[
\boxed{m^2<20/11,\qquad m^2/(m^2+4)<5/16.}
\tag{8}
\]

### Mixed periods

Every reverse run has exactly two switches, with a strict central
minimum. At any such centre, positivity of its reverse factor gives
`a^2<4/3`, as in
[MIXED_GLOBAL_SHORT_RUN_PERIOD](MIXED_GLOBAL_SHORT_RUN_PERIOD.md).
Consequently the global minimum of any mixed period satisfies

\[
\boxed{m^2<4/3,\qquad m^2/(m^2+4)<1/4.}
\tag{9}
\]

This bound does not use monotonicity of the mixed signed action.
In particular, it applies when the chosen global minimum is a `++`
site. The previously proved alternation minimum principle excludes
a turn as a global minimum; a reverse centre remains a separate
possibility, to which the present forward lemma does not apply.

## 3. A scalar forward-minimum inequality

At the chosen `++` site abbreviate its margin by `a` and its adjacent
margins by `p,n`. Put

\[
K=a^2+4,\quad \rho=a^2/K,\quad
r=\frac a{a+p},\quad t=\frac a{a+n},\quad
U(s)=1-s+s^2.
\]

The global minimum and the positive forward factor imply

\[
0<r,t\le\frac12,\qquad rt<\rho.
\tag{10}
\]

The strict star domain also gives `rho<min(r,t)`, although that
additional restriction is not needed in the scalar argument below.
Let `d_-,d_+` be the two adjacent switch-vector norms and `e` their
pairing in the common positive definite costate metric. Set

\[
u=8d_-,\qquad v=8d_+,\qquad E=16e.
\]

The forward switch inequalities give

\[
u\ge U(r),\qquad v\ge U(t).
\tag{11}
\]

The exact normal stationarity equation gives

\[
E=1+r+t-\rho+\log\frac\rho{rt}
-\frac{1-u}{r}-\frac{1-v}{t}.
\tag{12}
\]

The acute-pairing theorem
[GLOBAL_STRUCTURE_FORWARD_ACUTE](GLOBAL_STRUCTURE_FORWARD_ACUTE.md)
uses only the local `++` stationarity equation, the two forward switch
inequalities, and the common competitive Casimir cap. It therefore
applies equally at this site inside a mixed period and gives `E>0`.
The determinant identity is

\[
D:=4uv-E^2>0,\qquad
\gamma^2=\frac{D}{16(1-\rho)^2}.
\tag{13}
\]

We claim

\[
\boxed{L:=\rho D-(1-\rho)^2E<0.}
\tag{14}
\]

### The range `rt<rho<=1/4`

Suppose instead that `L>=0`. Equations (5) and (13) give

\[
E\le16\rho\gamma^2<3\rho.
\tag{15}
\]

For this argument hold `r,t,u,v` fixed and regard the right side
of (12) as a function `E(x)` on `rt<=x<=rho`. Define

\[
G(x)=E(x)-3x,\qquad
F(x)=4uv-E(x)^2-3(1-x)^2.
\]

Direct differentiation gives

\[
G'(x)=1/x-4\ge0,\qquad
F'(x)=-\frac{2(1-x)}xG(x).
\tag{16}
\]

By (15), `G(rho)<0`. Thus `G(x)<0` throughout this interval and
`F(rho)>=F(rt)`. At `x=rt`, start with the lower switch bounds
`u=U(r),v=U(t)`. The exact identity

\[
4U(r)U(t)-[-1+2r+2t-rt]^2-3(1-rt)^2=0
\tag{17}
\]

gives `F(rt)=0` there. Raise `u,v` to their actual values one at a
time. The endpoint has `E(rt)<3rt`, and `E(rt)` increases with each
of these variables, so the whole comparison path has `E(rt)<=3rt`.
Along it,

\[
\partial_u(4uv-E(rt)^2)
=4v-\frac{2E(rt)}r
\ge4U(t)-6t
=2(2t-1)(t-2)\ge0.
\tag{18}
\]

The same statement holds after interchanging `(r,u)` and `(t,v)`.
It follows that the actual `F(rt)>=0`. Hence `F(rho)>=0`, in
contradiction with (13) and `gamma^2<3/16`. This proves (14) in
the first range. Only the earlier coarse competitive cap is needed
here, so (9) covers every mixed application directly.

### The range `1/4<=rho<=5/16`

This range is needed only for the entirely forward application (8).
Again suppose `L>=0`. Equations (13)--(15), with `E>0`, imply

\[
\frac94\le4uv=D+E^2
\le16\gamma^2(1-\rho)^2+256\gamma^4\rho^2.
\tag{19}
\]

The last expression increases with `gamma^2>0`. Substitute the
rational upper bound `z=23/125` from (5). Its resulting quadratic
`16z(1-rho)^2+256z^2 rho^2` is convex in `rho`, and therefore its
maximum on `[1/4,5/16]` is at an endpoint. Those endpoint values are

\[
9z+16z^2=\frac{34339}{15625}<\frac94,
\]
\[
\frac{121}{16}z+25z^2=\frac{22379}{10000}<\frac94.
\tag{20}
\]

This contradicts (19), completing the proof of (14).

## 4. Translation to the scalar dual and the remaining obstruction

The auxiliary variable at the site satisfies `b=2Ke/gamma`.
Since `a^2=K rho`, equations (13)--(14) give exactly

\[
b-2\gamma a^2
=-\frac{K L}{8\gamma(1-\rho)^2}>0.
\tag{21}
\]

This proves (1). For example, in the edge-square expansion of the
fixed-`gamma` scalar dual Hessian, its onsite term in
`v=delta a,w=delta b` is

\[
-\frac{4\gamma b a^2+8}{K^2}v^2
 +\frac{4\gamma a}{K}vw
 -\frac{\gamma b}{b^2+4}w^2.
\tag{22}
\]

Its coefficient matrix has determinant

\[
\frac{8\gamma(b-2\gamma a^2)}{K^2(b^2+4)}>0,
\]

and both diagonal entries are negative. It is therefore negative
definite. Equation (22) follows by differentiating the common scalar
dual and using its stationarity equations; it is the onsite part,
not the full diagonal block including incident edges.

In particular, each incident forward edge still contributes a
positive square and a positive switching-coefficient term in that
expansion. A complete proof still needs a simultaneous choice of
neighbouring variations, or a constrained-index argument, which
controls those contributions and retains the three actual frame
constraints. No such descent or index implication is asserted here.

## Supplementary exact checker

Run

```
python3 explorations/global_structure_forward_minimum_certificate.py
```

The checker verifies the displayed derivative identities, polynomial
identities, rational constants and the onsite determinant. The scalar
comparison paths, actual PMP/cost interfaces and scope are the hand
arguments above. No numerical period search or length enumeration is
used in this proof.
