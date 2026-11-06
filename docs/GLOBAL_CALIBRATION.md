# Global calibration: exact obstructions and the remaining coupled inequality

This note studies a direct lower bound for **every** admissible Reinhardt
trajectory. Its main result is a rigorous obstruction to discarding the
state evolution: there are finite, three-piece frame paths with strict
star velocities, the prescribed frame endpoints, and cost **below the
octagon**, once the equation for the evolution of the velocity state is
removed. They are not admissible Reinhardt trajectories.

The construction rules out a global calibration depending on the frame
alone and valid for every star velocity. A second argument rules out the
separable phase-plus-state ansatz described below. Neither obstruction
rules out a genuinely coupled calibration. The last section gives its
exact three vertex inequalities in positive state coordinates, without
claiming that they have been solved.

All estimates and limiting arguments in this note are hand arguments. No
numerical optimization, symbolic computation, Lean compilation, or kernel
validation is used.

## 1. The actual problem and the desired certificate

Use the pinned reference conventions

\[
J=\begin{pmatrix}0&-1\\1&0\end{pmatrix},\qquad
R=\begin{pmatrix}1/2&-\sqrt3/2\\\sqrt3/2&1/2\end{pmatrix},
\]

\[
X=\Phi(x,y)=
\begin{pmatrix}x/y&-(x^2+y^2)/y\\1/y&-x/y\end{pmatrix},
\qquad
y>0,\quad |x|<1/\sqrt3,\quad x^2+y^2>1/3.
\]

The actual equations are

\[
g'=gX,\qquad
X'=f_u(X):=[P_u(X),X],\qquad
P_u(X)=\frac{Z_u}{\operatorname{tr}(Z_uX)},
\tag{1}
\]

\[
Z_u=\begin{pmatrix}
(u_1-u_2)/\sqrt3&(u_0-2u_1-2u_2)/3\\
u_0&(u_2-u_1)/\sqrt3
\end{pmatrix},\qquad
u_i\ge0,\quad \sum_i u_i=1.
\]

The equations hold almost everywhere with absolutely continuous state
curves. The terminal time is free and positive, and the endpoints are

\[
g(0)=I,\qquad g(T)=R,\qquad X(T)=\tau X(0),\qquad
\tau X=R^{-1}XR.
\tag{2}
\]

Write

\[
L(X)=-\frac32\operatorname{tr}(JX),\qquad
C=\int_0^T L(X(t))\,dt.
\]

For `X=[[a,b],[c,−a]]`, this is `L=3(c−b)/2`. The concrete octagon has
cost

\[
A_{\rm oct}
=2\sqrt3\,\frac{8-4\sqrt2-\log2}{2\sqrt2-1}<\pi.
\tag{3}
\]

These definitions and (3) are from the pinned
[`Defs.lean`](https://github.com/vltanh/lean4-smoothed-polygon/blob/8ce732873a1aa054e98dac46cfaa8d7bb96ffa6f/SmoothedPolygons/Defs.lean),
[`Ch4/StarDomain.lean`](https://github.com/vltanh/lean4-smoothed-polygon/blob/8ce732873a1aa054e98dac46cfaa8d7bb96ffa6f/SmoothedPolygons/Ch4/StarDomain.lean),
and
[`example7_5_smoothedOctagon`](https://github.com/vltanh/lean4-smoothed-polygon/blob/8ce732873a1aa054e98dac46cfaa8d7bb96ffa6f/SmoothedPolygons/Ch7/SmoothedPolygon.lean).

A sufficient direct certificate would be a continuously differentiable
function `S(g,X)`, on a domain containing every trajectory requiring
comparison, such that

\[
L(X)-D_gS(g,X)[gX]-D_XS(g,X)[f_u(X)]\ge0
\tag{4}
\]

for every allowed control, together with

\[
S(R,\tau X)-S(I,X)\ge A_{\rm oct}
\tag{5}
\]

for every allowed initial state. A lifted angular variable can be included
in the domain. Integrating (4) along an actual absolutely continuous
trajectory proves the desired lower bound by the chain rule. A nonsmooth
certificate would need an appropriate chain-rule or verification argument;
merely naming a value function does not supply one.

No Pontryagin lift, finite switch count, or symmetry assumption is needed
for this route. Its difficulty is constructing and verifying (4)–(5), not
the integration once they are available.

## 2. Two scalar-potential obstructions

### 2.1 A state-only endpoint potential cannot have a positive uniform gap

An inequality `L(X) ≥ DV(X)[f_u(X)]` integrates only to

\[
C\ge V(\tau X(0))-V(X(0)).
\]

At the circle state `X=J`, the endpoint difference is zero because
`τJ=J`. More generally, `τ³X=X`, since `R³=−I`. The three endpoint
differences on a `τ`-orbit sum to zero. Thus this difference cannot be
uniformly positive on the whole star domain, or on any nonempty invariant
union of such orbits.

This rules out that particular free-time endpoint argument. It does not
rule out a potential with phase dependence, an additional time term, or
other trajectory information.

### 2.2 A linear reflected-row phase plus a state potential is insufficient

Let `v=(g₀₀,−g₀₁)` and let `θ` be its continuous angle lift with
`θ(0)=0`. Since `det g=1`, `v` never vanishes. The equation `g′=gX` gives

\[
\theta'
=\frac{-b v_0^2-2a v_0v_1+c v_1^2}{v_0^2+v_1^2}>0.
\tag{6}
\]

Consider the ansatz

\[
S(\theta,X)=k\theta+V(X),
\]

with the pointwise inequality `L ≥ kθ′+DV[f_u]` required throughout the
star domain. For each `y>1/√3`, set

\[
X_y=\Phi(0,y)=\begin{pmatrix}0&-y\\1/y&0\end{pmatrix},
\quad
u_0=\frac{2}{3(y^2+1)},\quad
u_1=u_2=\frac{1-u_0}{2}.
\]

All three coordinates of this control are positive. Direct substitution
gives

\[
Z_u=\frac{2y}{3(y^2+1)}X_y,\qquad P_u(X_y)=-X_y/2,
\qquad f_u(X_y)=0.
\]

At `g=I`, equation (6) gives `θ′=y`. Consequently the proposed
inequality requires

\[
\frac32(y+y^{-1})\ge ky\quad\text{for every }y>1/\sqrt3.
\]

Letting `y→∞` forces `k≤3/2`. At the initial circle state `J`, the state
endpoint term again vanishes, and the primary terminal phase is `π/3`.
Such a certificate therefore provides at most `kπ/3≤π/2`, well below
`A_oct`.

The claim is about this separable ansatz on the stated domain. A proof
that all relevant trajectories stay in a smaller domain could change the
constraints, and a genuinely coupled `S(θ,X)` is not of this form. In
particular, this argument is not a nonexistence theorem for all possible
calibrations.

## 3. An exact frame relaxation with cost below the octagon

### 3.1 The relaxation being tested

Remove the second equation in (1) and its absolute-continuity requirement
on `X`. Permit piecewise constant strict star states, while retaining

\[
g'=gX\text{ almost everywhere},\quad \det X=1,\quad
g(0)=I,\quad g(T)=R.
\tag{7}
\]

The frame remains continuous and absolutely continuous. This relaxation
is weaker than actual admissibility. In particular, jumps of `X` are
allowed here and are prohibited by the actual integral state equation.

We construct a path satisfying (7) with cost below (3). It follows that a
certificate depending on `g` alone and satisfying

\[
DF_g[gX]\le L(X)
\tag{8}
\]

for every strict star velocity cannot have
`F(R)−F(I)≥A_oct`. Indeed (8) can be integrated on each piece of the
constructed frame path and the intermediate values telescope. The same
conclusion holds on the primary lift of the frame, as checked below.

### 3.2 An exact three-piece word

For `w>1/√3`, the state `X_w` above is strict star and satisfies
`X_w²=−I`. Hence

\[
E_w(t):=\exp(tX_w)
=\begin{pmatrix}\cos t&-w\sin t\\\sin t/w&\cos t\end{pmatrix}.
\tag{9}
\]

We will find finite `y>1`, `1/√3<z<1`, and positive `α,β` such that

\[
E_y(\alpha)E_z(\beta)E_y(\alpha)=R.
\tag{10}
\]

Taking the three constant states in this order gives duration
`T=2α+β` and exact cost

\[
C(y,z)=3\alpha(y+y^{-1})
       +\frac32\beta(z+z^{-1}).
\tag{11}
\]

Here is an explicit construction of (10). Put `ε=y⁻²` and let `q` be
the positive root of

\[
\sqrt3(1-z^2\varepsilon^2)q^2
 +2(1-z^2\varepsilon)q+\sqrt3(z^2-1)=0.
\tag{12}
\]

For `0<ε<1` and `1/√3<z<1`, the leading coefficient is positive and
the constant coefficient is negative. There is exactly one positive
root, explicitly the positive quadratic-formula root. It is continuous
in `ε` down to `ε=0`. Define

\[
\alpha=\arctan(q\sqrt\varepsilon),\qquad
C_\alpha=\cos\alpha,\quad S_\alpha=\sin\alpha,
\]

and form

\[
B=E_y(\alpha)^{-1}R E_y(\alpha)^{-1}.
\]

Direct multiplication gives `B₀₀=B₁₁=d` and

\[
\begin{aligned}
d&=\tfrac12(C_\alpha^2-S_\alpha^2)
   +\tfrac{\sqrt3}{2}C_\alpha S_\alpha(y+y^{-1}),\\
B_{01}&=yC_\alpha S_\alpha
   +\tfrac{\sqrt3}{2}(y^2S_\alpha^2-C_\alpha^2),\\
B_{10}&=-C_\alpha S_\alpha/y
   +\tfrac{\sqrt3}{2}(C_\alpha^2-S_\alpha^2/y^2).
\end{aligned}
\tag{13}
\]

The equation `B₀₁+z²B₁₀=0`, after division by `C_α²` and substitution
`tan α=q/y`, is exactly (12). Thus

\[
B=\begin{pmatrix}d&-z^2 e\\e&d\end{pmatrix},\qquad
d^2+z^2e^2=1,
\tag{14}
\]

where the determinant identity uses `det B=1`.

As `ε↓0`, equation (12) gives

\[
q\longrightarrow k(z)=\frac{\sqrt{4-3z^2}-1}{\sqrt3}>0.
\tag{15}
\]

Consequently `yα→k(z)`, `α/y→0`, and

\[
d\longrightarrow \sqrt{1-3z^2/4}>0,\qquad
e\longrightarrow\sqrt3/2>0.
\]

For all sufficiently small positive `ε`, both `d` and `e` are positive.
Equation (14) then determines `β∈(0,π/2)` by `cos β=d` and
`sin β=ze`. It gives `B=E_z(β)`, proving the exact endpoint (10).
Moreover

\[
\beta\longrightarrow\arcsin(\sqrt3 z/2).
\]

The endpoints in this construction are exact at finite `y`; they are
not merely endpoints of a limiting path.

### 3.3 The limiting cost is strictly below the target

Equations (11) and (15) show that, for fixed `z∈(1/√3,1)`,

\[
C(y,z)\longrightarrow
F(z):=3k(z)+\frac32(z+z^{-1})\arcsin(\sqrt3 z/2)
\quad(y\to\infty).
\tag{16}
\]

Taking `z↓1/√3` afterward gives

\[
F(z)\longrightarrow
C_*:=3-\sqrt3+\frac{\pi}{\sqrt3}
    =3+\frac{\pi-3}{\sqrt3}.
\tag{17}
\]

An exact rational separation avoids any reliance on decimal evaluation.
The bounds `3<π<22/7` and `√3>17/10` give

\[
C_*<3+\frac{10}{119}<\frac{31}{10}.
\]

For completeness, `π<22/7` follows by integrating the positive function

\[
0<\int_0^1\frac{x^4(1-x)^4}{1+x^2}\,dx=\frac{22}{7}-\pi;
\]

polynomial division gives the displayed identity. Also, convexity of
`1/x` and the four equal trapezoids on `[1,2]` give

\[
\log2
\le\frac14\left(\frac34+\frac45+\frac23+\frac47\right)
=\frac{1171}{1680}<\frac7{10}.
\]

Using this with `√3>173/100` and `√2<99/70`, whose squares verify the
root comparisons, yields

\[
A_{\rm oct}
>\frac{173}{50}\cdot\frac{23}{14}\cdot\frac{35}{64}
=\frac{3979}{1280}>\frac{31}{10}.
\tag{18}
\]

The numerator and denominator in (3) are positive, so all comparison
directions in (18) are preserved.

By continuity in (16)–(17), choose `z>1/√3` sufficiently close to the
boundary that `F(z)<31/10`, and then choose a **finite** `y` sufficiently
large that the exact word (10) has

\[
\boxed{\quad C(y,z)<31/10<A_{\rm oct}.\quad}
\tag{19}
\]

Both constant states are strict star states. No boundary state or infinite
velocity is used in the final finite path.

### 3.4 Winding and the precise failure of admissibility

The reflected-row quadratic form in (6) is positive definite: its matrix
is `[[−b,−a],[−a,c]]`, with determinant one and positive diagonal entries.
Its largest eigenvalue is at most its trace `c−b`. Therefore

\[
0<\theta'\le c-b,\qquad
0<\theta(T)\le\frac23 C<\frac23\pi.
\]

Here `C<A_oct<π` uses (3) and (19). Since `g(T)=R`, the endpoint angle
is `π/3` modulo `2π`. The displayed bounds force `θ(T)=π/3`. This
works piecewise and does not need a continuous velocity at the two joins.

It also identifies the primary polar lift if a frame potential uses that
lift. For `g=[[a,b],[c,d]]`, put `w=(a+d,c−b)`. Then

\[
(a,-b)\cdot(a+d,c-b)=a^2+b^2+1>0.
\]

Thus the polar angle and reflected-row angle differ continuously by an
angle in `(-π/2,π/2)`. Their difference is zero at both `I` and `R`, so
their lifts have the same winding along this path.

What fails is the second equation of (1): `X` jumps from `X_y` to `X_z`
and back. An actual integral state trajectory is continuous and cannot
make those jumps. If desired, the purely algebraic endpoint relation on
`X` in (2) can be imposed in this relaxation by assigning `X(0)=X(T)=J`;
changing two values affects neither the frame equation almost everywhere
nor its cost. It does not restore the missing integral state equation.

Consequently (19) is **not a counterexample to the Reinhardt conjecture**.
It proves that the frame equation, star restriction, frame endpoint, and
primary winding alone cannot establish its exact lower bound. The cost
of continuous, dynamically allowed state transitions is essential.

## 4. A concrete coupled calibration problem

The following positive coordinates make the missing dependence explicit.
Let

\[
D=\operatorname{diag}(3^{1/4},3^{-1/4}),\qquad
\widehat X=DXD^{-1},\qquad
\widehat Z_i=\sqrt3 D Z_{e_i}D^{-1}.
\]

Then

\[
\widehat Z_0=\begin{pmatrix}0&1\\1&0\end{pmatrix},\quad
\widehat Z_1=\begin{pmatrix}1&-2\\0&-1\end{pmatrix},\quad
\widehat Z_2=\begin{pmatrix}-1&-2\\0&1\end{pmatrix}.
\]

Put `p_i=−tr(Ẑ_i X̂)`. In the original entries these are

\[
p_0=-\frac{3b+c}{\sqrt3},\qquad
p_1=\frac{2c}{\sqrt3}-2a,\qquad
p_2=\frac{2c}{\sqrt3}+2a.
\]

The star and determinant conditions become

\[
p_i>0,\qquad p_0p_1+p_1p_2+p_2p_0=4,
\tag{20}
\]

and the cost density is

\[
L(p)=\frac{\sqrt3}{2}(p_0+p_1+p_2).
\tag{21}
\]

All indices in the rest of this section are cyclic modulo three. At
vertex control `i`, direct commutator substitution gives

\[
p_i'=0,\qquad
p_{i+1}'=\frac{2(p_i+p_{i+1})}{p_i},\qquad
p_{i-1}'=-\frac{2(p_i+p_{i-1})}{p_i}.
\tag{22}
\]

These vector fields are tangent to the surface (20). The exact
reflected-row phase equation is

\[
\theta'=Q(\theta,p):=\frac1{\sqrt3}
\left[p_0\cos^2\theta
 +p_1\cos^2(\theta-\pi/3)
 +p_2\cos^2(\theta+\pi/3)\right].
\tag{23}
\]

To check (23), solve for the matrix entries:

\[
a=(p_2-p_1)/4,\quad
c=\sqrt3(p_1+p_2)/4,\quad
b=-(4p_0+p_1+p_2)/(4\sqrt3),
\]

and substitute into
`θ′=−b cos²θ−2a sin θ cos θ+c sin²θ`.

For a general simplex control, put

\[
\omega_i(u,p)=\frac{u_i p_i}{\sum_j u_j p_j}.
\]

The denominator is positive; the weights are nonnegative and sum to one.
The state vector field is exactly the weighted average of the three
fields (22). Indeed `P_u=Σ_i ω_i P_{e_i}`, since every control denominator
is the same positive weighted sum with a common negative factor.
The phase field (23) is independent of the instantaneous control.

For low-cost trajectories `C<π`, the actual frame endpoints force
`θ(0)=0`, `θ(T)=π/3`, with `0≤θ≤π/3`; the proof is the same positive
quadratic-form argument used above. The state endpoint becomes

\[
p(T)=\tau p(0),\qquad \tau(p_0,p_1,p_2)=(p_2,p_0,p_1).
\tag{24}
\]

Thus a continuously differentiable function `F(θ,p)` satisfying

\[
\boxed{
L(p)-Q(\theta,p)F_\theta
-\frac2{p_i}
\left[(p_i+p_{i+1})F_{p_{i+1}}
      -(p_i+p_{i-1})F_{p_{i-1}}\right]\ge0,
\quad i=0,1,2,
}
\tag{25}
\]

throughout `0≤θ≤π/3` and (20), with

\[
F(\pi/3,\tau p)-F(0,p)\ge A_{\rm oct},
\tag{26}
\]

would prove the global lower bound. Partial derivatives in (25) can be
taken using any smooth extension off the surface (20); the expression
does not depend on that choice because (22) is tangent to the surface.

For arbitrary measurable controls, multiply the three inequalities (25)
by the weights `ω_i` and sum. The resulting inequality integrates along
the actual trajectory and gives (26). Trajectories with `C≥π` already
exceed `A_oct` by (3), so they need no additional certificate.

Equations (25)–(26) are a sufficient problem in one phase variable and
two independent state variables. They retain the state transitions that
the three-piece relaxation discarded. They also impose conditions on a
larger set of phase/state paths than the original full frame endpoint:
it is **not proved** that this reduced calibration problem has a
solution. If it does not, more frame information must be retained in
`S(g,X)`.

For example, even the reflected-row radius `r=|v|` carries an additional
exact endpoint constraint. Direct differentiation gives

\[
(\log r)'=-\tfrac12 Q_\theta(\theta,p),\qquad
\int_0^T Q_\theta(\theta(t),p(t))\,dt=0,
\tag{27}
\]

because `r(0)=r(T)=1`. This relation can be retained by including radius
as a variable, or by adding a constant multiple of `Q_θ` to the residual
in (25), whose integral is zero. It is one precise way to strengthen the
phase/state relaxation if required; no sign or sharp bound is asserted
for that modified residual here.

## 5. What has and has not been established

The below-octagon word (10)–(19) is a complete hand construction inside
the stated frame relaxation. It prevents treating the missing state
equation as harmless in a proposed global bound. The state-only and
separable phase-plus-state endpoint arguments also have explicit
obstructions.

The three inequalities (25) describe a possible genuinely coupled route.
They are not a verified dual certificate, a finite list of candidate
bodies, or a substitute for the unrestricted comparison. No function
satisfying (25)–(26) has been supplied. In particular, checking three
control vertices at each point still leaves a continuum of phases and
states, with noncompact directions; checking samples would not cover it.

The exact unresolved issue is how much cost the allowed continuous state
evolution forces beyond the cheaper frame relaxation, while meeting the
twisted state and full frame endpoints. The results in
[`NEAR_CIRCLE_BOUND.md`](NEAR_CIRCLE_BOUND.md) and
[`SWITCHING_WORDS.md`](SWITCHING_WORDS.md) exclude specific genuine
competitors. They do not close this quantitative gap. The global
octagon comparison and affine uniqueness remain open in this work.
