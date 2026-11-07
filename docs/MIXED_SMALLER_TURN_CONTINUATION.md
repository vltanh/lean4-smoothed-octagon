# A finite continuation alternative at the smaller adjacent turn

Date: 2026-11-07. Exact hand reduction with a supplementary symbolic
checker. No Lean, Lake, typechecking, or CI.

This note **does not exclude M2**. It gives a uniform necessary scalar
alternative for the case in which the smaller turn beside a global
minimum reverse centre belongs to a nonshort forward run. The alternative
uses the next actual switch, whatever the eventual run length. Its two
scalar branches remain to be excluded. In particular, the existence of
the first forward root by itself is not contradictory.

## 1. Actual local data and one common multiplier

Let `a` be a globally smallest active margin in a competitive finite
normal mixed period. The minimum structure puts it at a reverse centre.
Choose the reflection/time reversal, if necessary, so the smaller adjacent
turn is the outgoing turn `c`. The actual labels and margins begin

\[
0(p),\quad 1(b),\quad 0(a),\quad 2(c),\quad 0(d),\quad 1(r).
\tag{1}
\]

Thus the switches displayed after the central arc have signs `-++`.
The last switch is the assumption that the forward run on this side is
nonshort. In particular

\[
a<b,\quad a<c\le b,\quad p>a,\quad d>a,\quad r\ge a.
\tag{2}
\]

Write

\[
K=a^2+4,\quad S=a+b,\quad T=a+c,\quad
Q=d^2+4,\quad W=c+d,\quad Z=d+r,\quad Y=W^2-T^2.
\tag{3}
\]

The two positive same-sign factors obey

\[
\frac{K}{ST}>1,\qquad q:=\frac{WZ}{Q}>1.
\tag{4}
\]

All incident strict-star conditions are retained, including `cd<4`
and `dr<4`. The global compact-state theorem supplies `a>=2/15` if a
compact scalar domain is desired. The established reverse-centre scale
bound supplies `a^2<12/17`. Neither bound is needed for the algebra below.

For positive `A<P`, define the turn secant

\[
\begin{aligned}
\operatorname{Sec}(A,B,P)
&=\frac1{P-A}\int_A^P\left(1-\frac{Bx}{(B+x)^2}\right)\,dx\\
&=1+\frac{B^2}{(A+B)(P+B)}
 -\frac{B}{P-A}\log\frac{P+B}{A+B}.
\end{aligned}
\tag{5}
\]

The two actual turn norms, in the convention of eight times a switch
norm, are

\[
u=\operatorname{Sec}(a,b,p),\qquad
v=\operatorname{Sec}(a,c,d).
\tag{6}
\]

Put `U(x)=1-x+x^2` and `g_B(x)=1-Bx/(B+x)^2`.
The genuine incident switches imply

\[
\tfrac34<u<U(a/S),\qquad
\tfrac34<v<U(a/T),\qquad v>g_c(d).
\tag{7}
\]

All these quantities refer to the **same actual primary multiplier**.
In the central reverse-arc prefix frame it is

\[
U_a=\begin{pmatrix}h&-K^2v/(8S^2)\\S^2u/8&-h\end{pmatrix},
\qquad
\gamma^2=\det U_a=uvK^2/64-h^2.
\tag{8}
\]

Central stationarity determines its diagonal:

\[
\begin{aligned}
C_a&=b+a+c-a^2(S^{-1}+T^{-1})+a^3/K
       +a\log\frac K{ST},\\
h&=\frac K{16a}(Su+Tv-C_a).
\end{aligned}
\tag{9}
\]

The physical squared Casimir is `kappa^2=12 gamma^2`. The competitive
spectral inequality gives `gamma^2<23/125`; the sharper octagon expression
may be retained instead. No new costate is fitted at `d` or `r`.

## 2. Transport to the first forward root

Transport through the central reverse arc and the turn `c` gives

\[
h_d=h+vY/8,\qquad
w=\frac{uK^2+16hY+vY^2}{Q^2},
\]
\[
U_d=\begin{pmatrix}
h_d&-W^2v/8\\ Q^2w/(8W^2)&-h_d
\end{pmatrix}.
\tag{10}
\]

Here `v` and `w` are respectively the incoming and outgoing norms of
the actual forward arc `d`. Define

\[
C_d=c+d+r-d^2(W^{-1}+Z^{-1})+d^3/Q-d\log(WZ/Q).
\]

Its stationarity equation is the scalar identity

\[
\boxed{R_d(u,r):=C_d-Wv-Zw+16d h_d/Q=0.}
\tag{11}
\]

The outgoing derivative and the two missing-control inequalities give

\[
w>g_d(r),\qquad
v\ge F_{d/W}(q),\qquad w\ge F_{d/Z}(q),
\tag{12}
\]

where

\[
F_x(q)=1+x^2q-\frac{xq\log q}{q-1},\qquad F_x(1)=U(x).
\tag{13}
\]

These are necessary conditions at the actual first event. They do not
license replacing that event by an arbitrary later stationary root.
The missing-control formulas are the reflected endpoint identities in
[MIXED_GLOBAL_SMALL_FORWARD_MINIMUM](MIXED_GLOBAL_SMALL_FORWARD_MINIMUM.md),
applied to the actual arc `d`. Their algebra does not require that the
entire period be forward or that `d` be a minimum.

## 3. Exact alternative for the next switch

Let `K_r=r^2+4`, and define

\[
\boxed{
h_r=-h_d+wZ^2/8,\qquad
t=\frac{Q^2v-16h_dZ^2+wZ^4}{K_r^2}.}
\tag{14}
\]

The next actual switch after arc `r` satisfies at least one of

\[
\boxed{\quad t\ge\frac34
\qquad\text{or}\qquad
w\le\operatorname{Sec}(a,r,d).\quad}
\tag{15}
\]

This alternative is independent of the length of the complete forward
run and of the number of pieces in the period.

### Forward next switch

Let

\[
T(q)=\operatorname{diag}(q,q^{-1}),\qquad
R=\begin{pmatrix}1&-1\\1&0\end{pmatrix}.
\]

The exact forward transport to the next control frame is

\[
U_r=R^{-1}T(q)^{-1}U_dT(q)R
=\begin{pmatrix}
h_r&-Z^2w/8\\K_r^2t/(8Z^2)&-h_r
\end{pmatrix}.
\tag{16}
\]

In particular its determinant is still `gamma^2`. If the next switch
is forward, its actual norm is `t`. The forward switching derivative
inequality gives `t>=g_r(s)>=3/4`, where `s` is that next active margin.
This proves the first branch of (15). No choice of `s` or alteration of
the costate was made.

### Reverse next switch

If the next switch is reverse, write its active margin as `A`. Every
reverse run has exactly two switches, so `A` is the next reverse centre
and the global minimum property gives `A>=a`. The turn at `r` has
positive duration, so `A<d`, and its actual same-edge secant identity is

\[
w=\operatorname{Sec}(A,r,d).
\tag{17}
\]

The strict turn log-concavity and outgoing reverse derivative give

\[
r^2>Ad,\qquad w<g_r(A).
\tag{18}
\]

Together with `A<d`, the first inequality implies `A<r`. The function
`g_r` decreases on `(0,r)`. Therefore on `[a,A]` it is at least
`g_r(A)>w`. Extending the average in (17) from `[A,d]` to `[a,d]`
can only increase it, giving the second branch of (15). If `A=a`, it
gives equality; this boundary is retained. In particular, the weaker
necessary condition `r^2>ad` also follows, but it loses the information
in the secant norm.

This proof also covers a next switch across the twisted seam: the
state-closed active-margin coordinates and prefix-frame conjugations
are the actual cyclic ones. Finiteness supplies a next switch; no
finite return-time bound is being asserted.

## 4. A monotonicity along the first-root equation

For fixed `(a,b,c,d)`, keep the actual `v` in (6) fixed, regard `u`
as a scalar variable, and use (9)--(11). The coefficient of `u` is

\[
\boxed{\partial_uR_d
=\frac K{aQ^2}\{dSQ-Z(aK+SY)\}<0.}
\tag{19}
\]

Indeed `Y>0`, `Z>Q/W`, and

\[
dSQ-Z(aK+SY)
<\frac QW\{a(ST-K)+Sc(a-d)\}<0.
\tag{20}
\]

Consequently `R_d=0` determines at most one `u` for any fixed `r`.
At a genuine forward derivative point,

\[
\partial_rR_d=g_d(r)-w<0,
\qquad \frac{du}{dr}=-\frac{\partial_rR_d}{\partial_uR_d}<0.
\tag{21}
\]

On the reverse-centre upper-norm box in (7), one also has

\[
h<3a^2/16.
\tag{22}
\]

For completeness, set `x=a/S`, `y=a/T`, `rho=a^2/K`, so
`0<rho<xy` and `x,y<1/2`. Substituting the upper norms gives

\[
16h/K\le-1+2(x+y)-\rho-\log(xy/\rho)<3\rho.
\]

For the last inequality, the difference after subtracting `3rho` has
positive derivative `1/rho-4` in `rho`, and at `rho=xy` equals
`-(1-2x)(1-2y)<0`.

It follows that

\[
\partial_u\gamma^2
=\frac{vK^2}{64}-\frac{hKS}{8a}>0.
\tag{23}
\]

To check the strict sign, use `v>3/4`, `K>ST>2aS`, and (22).
Thus, while the upper-norm box and genuine outgoing derivative remain
valid, the Casimir strictly decreases along the root curve as `r`
increases. This is a scalar comparison, not an endpoint-preserving
deformation of a trajectory.

The endpoint missing gap gives a useful upper limit on this comparison.
For each `0<x<1`, the function

\[
L(q)=\frac{q-1-\log q}{(q-1)^2}
\]

strictly decreases from `1/2` to zero, and
`F_x'(q)=x^2-xL(q)`. Hence `F_x` either increases throughout or first
decreases and then increases, with a single minimum. Since the actual
turn gives `v>g_c(d)=F_{d/W}(1)`, the equation
`F_{d/W}(q)=v` has exactly one solution greater than one; (12) puts
`q` below it. Other comparison exits, including a derivative equality
or an incident-norm boundary, must still be handled. The present note
does not discard those faces or assert that the triple-gap face always
minimizes the Casimir.

## 5. A boundary comparison for the reverse-next branch

There is a useful further scalar reduction which does **not** assert
preservation of the Casimir cap. Fix `(a,c,d,r,v)` and continue the unique
root solution `u(b)` of (11) while increasing `b` to

\[
b_*:=K/T-a.
\tag{25}
\]

The actual point has `c<=b<b_*`. Set
`j=u-U(a/S)`, which is strictly negative at the actual point. Direct
implicit differentiation gives

\[
\begin{aligned}
j_b&=-\frac{K(dQ-ZY)}{aQ^2\,\partial_uR_d}\,j
       -\frac{a(b-a)}{S^3},\\
w_b&=-\frac{dK^3j}{aQ^3\,\partial_uR_d}<0.
\end{aligned}
\tag{26}
\]

The linear first equation, with its strictly negative inhomogeneous
term, preserves `j<0` as `b` increases. The denominators stay nonzero
by (19)--(20), including at `b=b_*` because `d>a`. Thus

\[
w(b)>w(b_*).
\tag{27}
\]

No lower bound on the comparison `u`, no continuation of a trajectory,
and no monotonicity of `gamma^2` under this change of `b` is needed.
In particular it would be incorrect to impose the original competitive
Casimir cap on the boundary point without another argument.

The boundary value has a relatively short formula. Put

\[
H=W^2-cT,\qquad D=ZH-dQ,\qquad L_0=a^2+ac+c^2+4,
\]
\[
P=ad(c^2+4)+d^2(4-cd)+2cd(6-cd)+4c^2.
\]

Since `H-dW=c(d-a)>0` and `Z>Q/W`, one has `D>0`.
The strict-star inequality `cd<4` gives `P>0`. Central stationarity
at `b_*` has `C_a=4/T+4c/K`, and elimination with (11) gives

\[
\boxed{
w(b_*)=\frac{HQ C_d-(d-a)Pv-4dL_0}{QD}.}
\tag{28}
\]

Its coefficient of `v` is strictly negative. This permits an elementary
upper comparison for the turn secant. Whenever `ad<c^2`, the exact
chord identity, for `a<=x<=d`, is

\[
\begin{aligned}
&\frac{(d-x)g_c(a)+(x-a)g_c(d)}{d-a}-g_c(x)\\
&=\frac{c(x-a)(d-x)
 [c^2(a+d+2c)+(c^2-ad)x]}
 {(a+c)^2(d+c)^2(x+c)^2}\ge0.
\end{aligned}
\tag{29}
\]

The strict turn log-concavity supplies `ad<c^2`. Integrating (29)
therefore gives the rational upper bound

\[
v< v_{\rm ch}:=\frac{g_c(a)+g_c(d)}2.
\tag{30}
\]

If the next switch is reverse to `A>=a`, then `r^2>ad` by (18), so
the same identity also gives

\[
\operatorname{Sec}(a,r,d)
<w_{\rm ch}:=\frac{g_r(a)+g_r(d)}2.
\tag{31}
\]

Finally, for `q>1`, let `z=(q-1)/(q+1)` and

\[
L_+(q)=2z+\frac{2z^3}{3(1-z^2)}\ge\log q.
\tag{32}
\]

This follows by comparing denominators in the positive series
`log q=2 sum_{j>=0} z^(2j+1)/(2j+1)`. Formula (28) decreases when
`log q` increases, since its coefficient is `-dH/D<0`. Consequently
one obtains a wholly rational lower comparison for the actual `w` by
using `v_ch` and `L_+(q)` in (28). Showing that this rational lower
comparison is at least `w_ch` on a correctly retained necessary domain
would exclude the reverse-next branch. No such uniform sign is claimed
here; the original inequalities, or justified relaxations of them,
remain essential.

## 6. What remains open

The exact alternative (15) reduces this particular M2 side assignment
to a finite scalar question. A sufficient remaining theorem is that
(2)--(12), the actual first-event interpretation, the competitive
Casimir cap, and the global minimum inequalities force simultaneously

\[
t<3/4,\qquad w>\operatorname{Sec}(a,r,d).
\tag{24}
\]

No uniform proof of (24) is supplied here. A proof may also use the
full-period defect budget and need not establish these two stronger
inequalities separately. The case in which the smaller adjacent turn
belongs to a short run requires its own argument. Both distinctions
are necessary before any M2 closure claim.

The companion
[`mixed_nonshort_completion_continuation_certificate.py`](../explorations/mixed_nonshort_completion_continuation_certificate.py)
checks the transport matrices, their determinants, the stationarity
coefficient (19), the numerator identity in (20), and the algebra behind
(26), (28), and (29). It certifies algebraic identities only. The
genuine-switch signs, integral comparisons, invariant half-space,
boundary discussion, and scope of the alternative are the hand argument
above.
