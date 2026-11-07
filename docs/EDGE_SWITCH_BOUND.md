# Five alternating arcs on one control edge cannot minimize

## Local exclusion at arbitrary word length

Let the reduced vertex-control word of an actual admissible trajectory contain
five consecutive positive-duration arcs using just two distinct vertices.
Their word is `ijiji`, with `i≠j`; there are four genuine switches, and
artificial subdivisions of a constant-control arc are not counted.

**There is another admissible segment with exactly the same initial and final
frame and state, and strictly smaller cost.** Its five arcs still use the
same two vertices; only the switching locations and total duration change.
The change can be arbitrarily small. Splicing it into the original trajectory
preserves both global endpoint conditions and decreases total cost.

Consequently no global minimizer can contain such a five-arc window, regardless
of the number of arcs elsewhere. This is a local exclusion, not a uniform bound
on the total number of switches. In particular, words repeatedly using all
three vertices are not excluded by this argument.

The proof uses a finite-dimensional endpoint-preserving variation and Rolle's
theorem. It does not assume a Pontryagin lift or use a numerical certificate.
The edge coordinates and group integration are those of
[SWITCHING_WORDS.md](SWITCHING_WORDS.md), also treated in
[Hales–Vajjha, §8.1](https://arxiv.org/html/2405.04331v1#Ch8.S1).
The argument below makes its own precise switch bound and scope explicit.

## 1. A linear edge problem in the increasing coordinate

Rotate the omitted control label to zero. Rotation preserves the cost and
the existence of endpoint-preserving replacements. Write

\[
q=1/\sqrt3,\qquad
X=\Phi(x,y)=\frac1y
\begin{pmatrix}x&-(x^2+y^2)\\1&-x\end{pmatrix}.
\]

The strict star domain is

\[
-q<x<q,\qquad y>0,\qquad x^2+y^2>q^2.
\tag{1}
\]

On the edge `u₀=0`, put `α=(u₁−u₂)/√3`. The actual state equations are

\[
\dot x=y,\qquad
\dot y=\frac{2\alpha y^2}{2\alpha x-2q^2}.
\tag{2}
\]

Every denominator in (2) is negative because `|α|≤q` and `|x|<q`.
The coordinate `x` is strictly increasing. Use it as the independent
variable on a fixed interval `[a,b]⊂(−q,q)` and set

\[
w(x)=y(x)^{-2}>0.
\]

The two vertex controls `α=±q` become

\[
\frac{w'}w=b_+(x):=\frac2{q-x},\qquad
\frac{w'}w=b_-(x):=-\frac2{q+x},
\tag{3}
\]

respectively. Their difference is strictly positive:

\[
b_+(x)-b_-(x)=\frac{4q}{q^2-x^2}>0.
\tag{4}
\]

Both coefficients are smooth and bounded on the fixed compact interval.
The remaining star condition is

\[
0<w(x)<\frac1{q^2-x^2}.
\tag{5}
\]

## 2. Exactly which data must be preserved

Fix `a,b`, the initial value `w(a)`, and the initial frame `g₀`. Recover
physical time by

\[
t(x)=\int_a^x\sqrt{w(r)}\,dr.
\tag{6}
\]

This is a strictly increasing `C¹` change of parameter. With

\[
s(x)=\int_a^x w(r)\,dr,\qquad
h(x)=\begin{pmatrix}1&-x\\s(x)&1-s(x)x\end{pmatrix},
\]

the exact frame is

\[
g(x)=g_0h(a)^{-1}h(x).
\tag{7}
\]

Indeed (6) gives `dx/dt=y` and `ds/dt=1/y`, and direct multiplication
gives `dh/dt=hX`. Thus (7) satisfies the full frame equation.

The final state is fixed precisely by fixing `w(b)`, because `b` is
already fixed. The final frame is fixed by fixing

\[
S(w)=\int_a^b w(x)\,dx.
\tag{8}
\]

The segment cost is

\[
\begin{aligned}
C(w)
&=\frac32\int\frac{1+x^2+y^2}{y}\,dt\\
&=\frac32\left((b-a)+S(w)+M(w)\right),
\qquad M(w)=\int_a^b x^2w(x)\,dx.
\end{aligned}
\tag{9}
\]

Therefore it suffices to decrease `M` while preserving `w(b)` and `S`.
No elapsed-time constraint is needed: terminal time in the full Reinhardt
problem is free, and the rest of the trajectory can be translated in time.

## 3. Four switching locations and two endpoint constraints

Let

\[
a<s_1<s_2<s_3<s_4<b
\]

be the four switching locations of the five alternating arcs. For nearby
strictly ordered switching tuples, let `b_s(x)` alternate between (3),
with the same initial sign as the original segment. The unique trajectory is

\[
w_s(x)=w(a)\exp\!\left(\int_a^x b_s(r)\,dr\right).
\tag{10}
\]

Write `w` for the original trajectory. At switch `s_i`, set

\[
k_i=b_{\rm before}(s_i)-b_{\rm after}(s_i)\ne0,
\quad
S_i=\int_{s_i}^b w(x)\,dx,
\quad
J_i=\int_{s_i}^b x^2w(x)\,dx.
\]

Differentiating the elementary integral in (10) gives, away from the
switch itself,

\[
\partial_{s_i}w_s(x)=
\begin{cases}
0,&x<s_i,\\
k_iw(x),&x>s_i.
\end{cases}
\]

The coefficient bounds and the continuity of `w_s` justify differentiation
under the remaining integrals. In particular the constraint map

\[
G(s)=(\log w_s(b),S(w_s))
\]

and objective `M(w_s)` are continuously differentiable, with derivatives

\[
\partial_{s_i}G=k_i(1,S_i),\qquad
\partial_{s_i}M=k_iJ_i.
\tag{11}
\]

Since `w>0` and the switching locations are strictly ordered,

\[
S_1>S_2>S_3>S_4.
\]

Thus the two rows of `DG` are independent: any two columns have nonzero
determinant `k_i k_j(S_j−S_i)`. The exact fixed-endpoint level set of `G`
is a smooth two-dimensional surface near the original tuple.

## 4. A quadratic cannot satisfy the stationarity equations

Suppose the derivative of `M` vanished on the tangent space of that
level set. Linear algebra and (11) would give constants `λ,μ` such that

\[
J_i=\lambda+\mu S_i\qquad(i=1,2,3,4).
\tag{12}
\]

Subtract adjacent equations. For each `i=1,2,3`,

\[
\int_{s_i}^{s_{i+1}}(x^2-\mu)w(x)\,dx=0.
\tag{13}
\]

Because `w` is strictly positive and continuous, (13) forces `x²−μ`
to have a zero strictly inside each of the three disjoint intervals.
If it had no zero there, continuity would give a constant strict sign
on the open interval and a nonzero integral. The polynomial cannot
vanish identically on any interval. Hence (13) requires at least three
distinct real roots of `x²−μ`, a contradiction.

It follows that the objective derivative does not vanish on the tangent
space. Choose its sign to obtain a tangent vector `v` satisfying

\[
DG\,v=0,\qquad dM(v)<0.
\]

By the implicit function theorem there is a `C¹` curve of switch tuples
on the exact level set of `G`, through the original tuple and tangent to
`v`. For every sufficiently small positive parameter on this curve,
both endpoint constraints are exactly preserved and `M` strictly decreases.
Equation (9) proves the strict cost decrease.

## 5. Feasibility and splicing the actual competitor

For small changes the switching locations remain strictly ordered.
Formula (10) varies uniformly with them on `[a,b]`. The original segment
lies in the strict star domain on a compact interval, so the strict
positive bounds in (5) have a common margin. The nearby segments retain
all of (1), not merely positive values at the switching points.

Their positive `w_s` are continuous and piecewise smooth with bounded
derivatives. Equation (6) gives an invertible `C¹` time change. Equations
(2), (3), and (7) recover an actual integral-form state trajectory with
the specified vertex controls. Its duration is positive and converges
to the original duration.

The initial and final `g,X` are exactly unchanged. Keep the original
trajectory before the window, insert the new segment, and translate the
remaining original segment in time. At both seams `X` and `g` match;
the one-sided frame derivatives agree because both equal `gX`.
Piecewise absolute continuity, the integral ODEs, and the measurable
simplex control therefore survive the splice. The final frame, twisted
state endpoint, and initial frame are unchanged, and the total cost
strictly decreases. This contradicts global minimality.

## 6. A sharper condition for four arcs

With four alternating arcs there are three switches and the same two
independent constraints. Stationarity would require (13) on the two
successive switching intervals. If all three switches lie on one side
of zero, `x²` is strictly monotone across their span, so their two
weighted averages cannot agree. Such a four-arc segment also has a
strictly cheaper endpoint-preserving nearby replacement.

More generally, a four-arc local minimum in this edge-restricted class
must have `μ>0` and

\[
s_1<-\sqrt\mu<s_2<\sqrt\mu<s_3
\]

for the scalar `μ` in (12): each switching interval must contain a
different root of the same quadratic. This is a necessary condition,
not a sufficiency or classification theorem.

## 7. Corollary for arbitrary measurable edge intervals

The direct proof in
[MEASURABLE_EDGE_PMP_BOUND](MEASURABLE_EDGE_PMP_BOUND.md) establishes:

**On every closed nondegenerate subinterval of a global minimizer on which
one control coordinate is zero almost everywhere, the control agrees
almost everywhere with at most four constant vertex pieces.**

It uses the exact coordinates, endpoint reconstruction, and cost in
Sections 1--2 above. The two-state fixed-time edge problem has a separate
nontrivial PMP multiplier. A positive integrating factor gives
`(rho*p_w)'=-rho*(p_s+lambda*x^2)`. A nonzero quadratic has at most two
roots; Rolle's theorem bounds `p_w` by three zeros and hence the control
by four pieces. The identically zero polynomial and abnormal cases are
handled explicitly. This proves (E4) from arbitrary measurable controls,
without source Theorem 8.1.4 or a pre-existing finite representation.

The earlier source-based derivation remains valid: Hales--Vajjha
Definition 8.1.1 fixes the same `s,x,y` endpoint data with physical time
free, Proposition 8.1.3 supplies edge extremality for a global minimizer,
and Theorem 8.1.4 supplies finite vertex pieces. The five-piece variation
in this note then reduces that representation to four. The direct proof
above replaces this source chain in the current uniform bound.

Both arguments use optimality for the separate edge problem. A lift for
the full system alone is insufficient: the source's Remark 8.1.6 records
abnormal full-system lifts for arbitrary measurable edge controls. Such
a lift is not substituted for the nontrivial edge multiplier.

## Scope and remaining gap

The five-arc exclusion applies to a local window at any total word length
and proves an actual strict improvement, rather than a failed endpoint
matching heuristic. It is consistent with
[LOCAL_SHORTENING_OBSTRUCTION.md](LOCAL_SHORTENING_OBSTRUCTION.md): that
note excludes replacing three positive arcs by two, whereas this argument
varies four switch positions while retaining five arcs.

The result does not exclude words such as `012012…`, does not control
windows using all three vertices, and does not supply a global switch
bound. The finite-window proof remains an independent strict-improvement
argument. The measurable-interval corollary now also has the direct PMP
proof cited in Section 7.
No Lean source,
typechecking, build, or CI execution is part of this hand argument.
