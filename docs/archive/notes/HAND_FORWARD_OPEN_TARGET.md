# Exact forward stationary formulas and earlier stronger targets

Date: 2026-11-07. The hand-only forward theorem is now complete in
[HAND_FORWARD_PERIOD_EXCLUSION](HAND_FORWARD_PERIOD_EXCLUSION.md).
This note preserves its exact stationary formulas, earlier stronger
sufficient targets, and rigorously refuted relaxations. The completed
route uses delta u+delta v<1/35 and delta v<1/64, proved in the
[linked norm sources](HAND_FORWARD_CONDITIONAL_NORM_BOUNDS.md).
The stronger targets (7)--(8) below remain unproved and are not premises
or outstanding obligations of that completed route. The
[dependency inventory](HAND_FORWARD_DEPENDENCY_INVENTORY.md) records the
full current chain. No numerical extremum or coefficient count is a
premise.

## 1. Exact stationary formulas and an earlier stronger sum target

The strongest useful proposed target presently has the following exact,
reproducible definition. Put

\[
\begin{gathered}
11/5\le U<3,\qquad 1\le z\le w\le4/3,\\
S=1+z,\quad T=1+w,\quad K=1+U,
\quad Z=z^2+U,\quad W=w^2+U,\\
S^2/Z\le h\le S/z,\qquad T^2/W\le k\le T/w,\\
\frac{hZ}{S}+\frac{kW}{T}\le\frac{5U+1}{3}.
\end{gathered}
\tag{1}
\]

The last line is the proved exterior-factor cost budget. Its weak version
enlarges the actual competitive domain. The neighbor bound z,w<4/3 is now proved by the
[integral neighbor theorem](HAND_FORWARD_NEIGHBOR_INTEGRAL.md) and its
[asymmetric completion](HAND_FORWARD_ASYMMETRIC_NEIGHBOR_BOUND.md). It is
therefore an established actual-data input to both these formulas and
the completed norm proof.

Define

\[
d=3-U,\quad x=z-1,\quad y=w-1,\quad H=h-1,\quad I=k-1,
\quad q=ST/K,
\]
\[
f(r)=\frac{r-r^{-1}}2-\log r,
\qquad \Phi=f(S/2)+f(T/2)+f(4/K),
\]
\[
\begin{aligned}
n_L&=S^2(U-z)H/Z,&n_R&=T^2(U-w)I/W,\\
m_L&=\frac{K^2}{SZ}\{q-1+H(Sq-1)\},&
m_R&=\frac{K^2}{TW}\{q-1+I(Tq-1)\}.
\end{aligned}
\]

For

\[
P(d,x)=d^2(x^2+4x+2)+8dx(x+1)+2x^2(8+4x-x^2),
\]

set

\[
\begin{aligned}
r_L={}&\frac{dx(d+2x)+HP(d,x)}{8SZ}
 +\frac{H^2z(d+4x+x^2)}{2hZ}\\
 &+\frac{K(1+SH)}Z\Phi-zf(h),
\end{aligned}
\tag{2}
\]

and obtain `r_R` by interchanging `(z,S,Z,H,h,x)` with
`(w,T,W,I,k,y)`. These are the exact
[centered stationary residuals](GLOBAL_FORWARD_CENTERED_SYSTEM.md), not
independently relaxed expressions. Put

\[
D=m_Lm_R-n_Ln_R,
\qquad
\delta u=\frac{m_Lr_R-n_Rr_L}{D},\qquad
\delta v=\frac{m_Rr_L-n_Lr_R}{D}.
\tag{3}
\]

Here `D>0`. Indeed `q>1`, `q<min(S,T)`, `H,I>0`, and

\[
\begin{aligned}
D={}&\frac{K^4(q-1)}{STZW}
\bigl[(q-1)+H(qS-1)+I(qT-1)\\
&\hspace{26mm}+HI(q+1)\{q(S+T)-q^2-1\}\bigr]>0.
\end{aligned}
\tag{4}
\]

The genuine exterior missing-control floors must also hold:

\[
\delta u\ge L(z,h),\qquad\delta v\ge L(w,k),
\tag{5}
\]
\[
L(z,h)=\frac{x(x+2zH)}{4S^2}
       +\frac{zh}{S}\frac{f(h)}H.
\tag{6}
\]

The quotient has its continuous value zero at `H=0`. In the open
scale domain in (1), in fact `H,I>0`. These floors imply both norm
increments are nonnegative.

**Unproved sufficient target.** Under (1)--(6), prove

\[
\boxed{(m_R-n_R)r_L+(m_L-n_L)r_R\le D/39.}
\tag{7}
\]

This is precisely `delta u+delta v<=1/39`. The proved conditional
Casimir lemma then contradicts the hand cap `gamma^2<9193/50000`.
A stronger, homogeneous proposed target is

\[
(m_R-n_R)r_L+(m_L-n_L)r_R
\le\frac{(3-U)(q-1)}9D.
\tag{8}
\]

The proved product estimate `(3-U)(q-1)<3/13` makes (8) sufficient
for (7). Neither (7) nor (8) has been proved. Exploration suggested
both targets, but supplies no proof of them.

## 2. A rigorously refuted weakening

It is not enough to keep (1)--(4) and merely require
`delta u,delta v>=0`, while dropping the genuine floors (5).
The following exact point refutes (7) on that larger domain:

\[
U=\frac{13}{5},\quad z=w=\frac43,
\quad h=k=\frac{245}{197},\quad q=\frac{245}{162}.
\tag{9}
\]

Here `h=S^2/Z`, `k=T^2/W`, both exterior margin ratios equal one,
and the cost budget is exactly saturated:

\[
\frac{hZ}{S}+\frac{kW}{T}
=\frac{14}{3}=\frac{5U+1}{3}.
\]

All other structural inequalities in (1) hold. The symmetric
stationary solution has

\[
n_L=n_R=\frac{14896}{38809},\quad
m_L=m_R=\frac{55566}{38809},
\]
\[
\delta u=\delta v=\delta
=\frac{310472\log(245/197)-300348\log(245/162)+62751}{422772}.
\tag{10}
\]

These identities follow by direct substitution in (2)--(3). They
reduce the obstruction to elementary logarithm estimates. For
`0<t<1`, integration of the geometric series gives

\[
2(t+t^3/3)
<\log\frac{1+t}{1-t}
<2\left(t+\frac{t^3}{3(1-t^2)}\right).
\tag{11}
\]

Apply this with `t=24/221` for `h` and `t=83/407` for `q`.
Direct rational comparisons give

\[
\log h>\frac{109}{500},\qquad
\log q<\frac{207}{500}.
\]

For completeness, the respective rational comparison gaps in (11)
are `261151/5396930500` and `144292/605768625`, both positive.
Consequently

\[
\delta>\frac{190307}{13211625}
=\frac1{78}+\frac{181369}{114500750}.
\tag{12}
\]

Thus both increments are positive, while
`delta u+delta v>1/39`. This also refutes the stronger homogeneous
target (8) on the relaxed domain, because the product estimate
still applies there.

The obstruction is not confined to saturated cost or neighbor bounds.
Decrease `z=w` slightly, keep `U=13/5`, and retain
`h=k=S^2/Z`. The cost and neighbor bounds become strict, while
continuity of (3) and the strict gap (12) preserve the violation.

This is not a counterexample to the actual PMP conditions: the genuine
floors are violated. To verify that point without numerical evaluation,
the same estimates (11) give

\[
\log h<\frac{1091}{5000},\qquad
\log q>\frac{827}{2000},
\]

whose rational comparison gaps are `1508483/10666565000` and
`6658217/404514858000`. Therefore

\[
\delta<\frac{15755231}{1056930000}<\frac3{200}
<\frac{83}{5516}
\le L(4/3,245/197).
\tag{13}
\]

The last bound retains only the first, rational summand in (6).
The two middle gaps are respectively `98719/1056930000` and
`13/275800`. Every assertion in this obstruction is thus checkable
using the displayed identities and integer arithmetic.

## 3. The larger-neighbor reduction, now completed

The completed route proves `delta v<1/64` for the larger neighbor,
together with `delta u+delta v<1/35`. The
[conditional Casimir theorem](HAND_FORWARD_CONDITIONAL_NORM_BOUNDS.md)
shows why this pair suffices. The original reduction is retained here.
Define

\[
\mathcal E_C=r_L-n_LL(z,h)-m_L/64.
\]

If the left exterior floor holds and `delta v>=1/64`, the first
stationarity row gives `E_C>=0`. Its derivative in the larger
neighbor is

\[
\partial_w\mathcal E_C
=\alpha_L\left(1-\frac1T+\frac1{T^2}-\frac{49}{64}\right)<0,
\qquad \alpha_L=K(1+SH)/Z>0,
\]

since `2<=T<=7/3` gives the upper bound `37/49<49/64` for the
first three terms. Lowering `w` to `z` therefore increases this
residual. The cost budget and `k>=T^2/W` imply

\[
\frac{S^2}{Z}\le h\le
h_c:=\frac{S(5U-2-3z)}{3Z},
\qquad 1\le z\le4/3,\quad1+6z/5\le U\le3.
\tag{14}
\]

Here `h_c<=S/z`: after clearing positive denominators it is enough
to use `U<=3` and `6z^2-13z+9>0`. The latter polynomial is positive
on the real line because its leading coefficient is positive and
its discriminant is `-47`.

The proved exterior-factor concavity also applies to `E_C`, since
replacing the opposite norm floor by the constant `49/64` changes
only terms affine in `h`. With `h_0=S^2/Z`, the remaining sufficient
planar sign comparisons would be

\[
\mathcal E_C(U,z,z,h_0)<0,
\]
\[
\mathcal E_C(U,z,z,h_0)
 +(h_c-h_0)\partial_h\mathcal E_C(U,z,z,h_0)<0
\tag{15}
\]

on (14) with U<3. Both are now proved in
[HAND_FORWARD_LARGER_NORM_HAND_PROOF](HAND_FORWARD_LARGER_NORM_HAND_PROOF.md).
That proof displays the complete finite identities and short coefficient
bounds establishing their signs, including the near-circular region.

## 4. Completed proof boundary

The upstream U<3 and neighbor restrictions have hand proofs. The
exterior-factor concavity and stronger physical cost budget used below
also have hand proofs. The two stationary residual signs are proved in
[HAND_FORWARD_SYMMETRIC_SUM_REDUCTION](HAND_FORWARD_SYMMETRIC_SUM_REDUCTION.md),
[HAND_FORWARD_SYMMETRIC_SUM_HIGH_D](HAND_FORWARD_SYMMETRIC_SUM_HIGH_D.md),
and [HAND_FORWARD_LARGER_NORM_HAND_PROOF](HAND_FORWARD_LARGER_NORM_HAND_PROOF.md).
Their [independent audit](HAND_FORWARD_NORM_AUDIT.md) and the
[actual-period theorem](HAND_FORWARD_PERIOD_EXCLUSION.md) close H-F.

The alternate stronger inequalities in Sections 1, 5 and 6 remain
research comparisons only. They are not needed for that conclusion.
The genuine exterior floors remain essential and were retained.

## 5. An exact decomposition using only the larger-neighbor floor

There is a useful positive-weight form of the sum. Set

\[
A=m_L-n_L,\qquad B=m_R-n_R.
\]

Both are strictly positive on (1). Indeed,

\[
\begin{aligned}
SZ A={}&K(ST-K)
 +H\{S^4-K^2+KS^2(T-S)\},\\
TW B={}&K(ST-K)
 +I\{T^4-K^2-KT^2(T-S)\}.
\end{aligned}
\tag{16}
\]

The first braces are nonnegative because `T>=S>=2` and `K<4`.
The second braces have the lower bound

\[
\begin{aligned}
T^4-16-4T^2(T-2)
&=(T-2)(T^3-2T^2+4T+8)\\
&=(T-2)\{T^2(T-2)+4T+8\}\ge0.
\end{aligned}
\]

The common first term `K(ST-K)` is strictly positive. Thus

\[
D=n_LB+m_RA>0,
\qquad
D(\delta u+\delta v)=Br_L+Ar_R.
\tag{17}
\]

Also `B(n_L+m_L)+A(n_R+m_R)=2D`, so the half-sum of the
increments is a convex combination of the two row averages:

\[
\frac{\delta u+\delta v}{2}
=\frac{B(n_L+m_L)\,r_L/(n_L+m_L)
      +A(n_R+m_R)\,r_R/(n_R+m_R)}{2D}.
\tag{18}
\]

For the proposed sufficient sum bound, write `L_w=L(w,k)` and define

\[
\mathcal N
=D(1/39+L_w)
 -(2m_R-n_R)r_L-(m_L-2n_L)r_R.
\tag{19}
\]

Directly from (3), there is the exact slack identity

\[
\boxed{
D\{1/39-(\delta u+\delta v)\}
=D(\delta v-L_w)+\mathcal N.}
\tag{20}
\]

Consequently a proof of `N>=0` on the structural domain (1), with
the two reconstructed increments merely nonnegative, would prove
(7) using only the larger-neighbor exterior floor. The smaller-neighbor
floor would be unnecessary in that route. Equivalently, the new
comparison would be

\[
\delta u+2\delta v-L(w,k)\le1/39.
\tag{21}
\]

This exact reduction is proved; the nonnegativity of (19) is not.
No claim that the larger-neighbor floor suffices is being assumed.

## 6. Why a constant floor-slack coefficient cannot give the homogeneous target

A similar proposed barrier for the stronger target (8) would assert,
on the structural domain with `delta u,delta v>=0`, that

\[
\delta u+\delta v+\lambda\{\delta v-L(w,k)\}
\le\frac{(3-U)(q-1)}9
\tag{22}
\]

for a fixed nonnegative constant `lambda`. No fixed constant can
satisfy this comparison. This obstruction does not refute (8) under
the genuine floors; it only rules out this particular uniform
floor-slack proof on the enlarged domain.

The following two symmetric families prove the claim by elementary
expansion. The expansions are justified by integrating
`f'(1+t)=t^2/[2(1+t)^2]`, which gives
`f(1+t)=t^3/6+O(t^4)`.

First let `z=w=1`, `U=3-d`, and `h=k=q=4/(4-d)`, with `d>0`
tending to zero. Direct substitution gives the exact symmetric norm
increment

\[
\delta u=\delta v=\delta
=\frac{d^2}{32U}+\frac{K}{4U}f(q),
\qquad
L(1,q)=\frac{q}{2(q-1)}f(q).
\]

Therefore

\[
\delta=\frac{d^2}{96}+O(d^3),\qquad
L(1,q)=\frac{d^2}{192}+O(d^3),\qquad
\frac{d(q-1)}9=\frac{d^2}{36}+O(d^3).
\]

Dividing (22) by `d^2` and taking the limit forces

\[
\frac{4+\lambda}{192}\le\frac1{36},
\qquad\text{hence}\qquad \lambda\le\frac43.
\tag{23}
\]

For the second family take

\[
z=w=1+x,\quad U=3-x^2,
\quad h=k=1+x/2,\quad q=\frac{2+x}{2-x},
\qquad x>0,\quad x\longrightarrow0.
\]

Here `Z=2S`, so `h=S^2/Z` exactly. The cost budget holds for
small `x`, since it is equivalent to `6x+5x^2<=4`. Direct substitution
in (2) gives

\[
n_L+m_L=\frac{x(2+x)(4-x-x^2)}2=4x+O(x^2),
\]
\[
r_L=\left(\frac18+\frac18+\frac1{24}-\frac1{48}\right)x^3
 +O(x^4)=\frac{13x^3}{48}+O(x^4).
\]

The four displayed cubic terms respectively come from the
`HP/(8SZ)` term, the `H^2` term, the `Phi` term, and `-z f(h)`
in (2); the remaining first term is of order four. Thus

\[
\delta=\frac{13x^2}{192}+O(x^3),\qquad
L(1+x,1+x/2)=\frac{7x^2}{48}+O(x^3),
\]
\[
\frac{(3-U)(q-1)}9=\frac{2x^3}{9(2-x)}=O(x^3).
\]

Both reconstructed norm increments are positive for small `x`.
Dividing (22) by `x^2` and taking the limit now forces

\[
\frac{26-15\lambda}{192}\le0,
\qquad\text{hence}\qquad \lambda\ge\frac{26}{15}.
\tag{24}
\]

The incompatible bounds (23)--(24) prove the obstruction. The second
family violates the genuine floor, as its displayed leading terms
also show. A geometry-dependent multiplier, another use of the
stationary equations, or the nonhomogeneous target (21) could avoid
this obstruction; none of those alternatives is asserted proved.
