# A smallest reverse centre must touch a nonshort forward run

Research theorem, 2026-11-07. This joins the exact same-lift short-bridge
comparisons. It is a uniform local obstruction inside an actual complete
normal period, not an exclusion of the remaining M2 case. The comparison
paths below are scalar inequalities; they are not asserted to preserve a
geometric trajectory, its endpoints, or its primary multiplier.

See the [independent complete audit](MIXED_GLOBAL_SHORT_BRIDGE_MINIMUM_AUDIT.md).

## 1. Statement and actual interface

In a competitive finite normal mixed geometric period, a reverse centre
whose active margin is globally smallest cannot have short forward runs
on both sides. Thus every global minimum touches a forward run of length
at least two. This places a minimum at a genuinely nonshort bridge; it
does not bound the number or lengths of such bridges.

Suppose to the contrary that the adjacent short bridges are
`(A,B,C,a)` and `(a,b,c,Dright)`, with a the smallest active margin.
Reflect the period if necessary to make `C<=b`. Set

\[
\alpha=A/a,\quad\beta=B/a,\quad x=C/a,\quad y=b/a,
\quad\sigma=\alpha^2-1,\quad q_0=(1+x)(1+y),
\]
\[
Q=\alpha(\alpha+\beta),\quad
D=(\alpha+\beta)^2+(1+x)^2-(\beta+x)^2.
\]

The actual turn secants, centre minima, and strict incident derivatives
give

\[
1\le\alpha<x\le\beta,\quad x\le y,\qquad
\alpha\ge\beta/x+\tfrac27(\beta-x),
\]
\[
\tfrac34<u\le V(x),\quad\tfrac34<v\le V(y),\qquad
u<U\!\left(\frac\alpha{\alpha+\beta}\right),
\quad v<U\!\left(\frac1{1+y}\right),
\tag{1}
\]

where `u,v` are eight times the actual turn norms,
`U(r)=1-r+r^2`, and

\[
V(t)=1+\frac{t}{2(1+t)}-
             \frac{t}{t-1}\log\frac{2t}{1+t}.
\]

The quantitative order follows by integrating the proved exact secant
identity `d[(alpha+2x/7)/beta]/d beta>0` from `(beta,alpha)=(x,1)`.
These are necessary conditions of the same actual lift.

Let the physical central scale be `rho=a^2/(a^2+4)`. For the comparison,
fix the ratios and u,v and vary rho. Write

\[
q=1/\rho,\quad P=q+\sigma,\quad\lambda=q/P,
\quad d=D/P,\quad T=P/Q,\quad T_B=Q/\alpha^2,
\]
\[
f(t)=t-t^{-1}-\log t,\quad h(t)=\log t-1+t^{-1},
\quad G_t(z)=zt-f(t),
\]
\[
E=G_{1+x}(u)+G_{1+y}(v)-h(q),\quad
F_0=E-\rho Du,\quad F=\lambda F_0,
\]
\[
w=\lambda^2v-dF,\quad E_L=du-F,
\quad R(t)=wt-f(t)+G_{T_B}(u)-h(P/\alpha^2)-E_L.
\tag{2}
\]

At actual data, these are exactly the central stationarity and transported
outer-centre equations. The positive central reverse factor is `q>q0`.
The actual outer reverse centre supplies a parameter `t_act` with

\[
2<t_{\rm act}<T,\qquad R(t_{\rm act})=0,
\quad \tfrac34<w<f'(t_{\rm act}).
\tag{3}
\]

Strictness follows from the already proved normal-switch rigidity and
positive actual durations. In particular `T>2`.

## 2. The closed scalar interval and its maximum

The common comparison interval is

\[
q\ge q_*:=\max\{q_0,2Q-\sigma\},
\quad\text{equivalently}\quad
0<\rho\le\rho_*:=1/q_*.
\tag{4}
\]

Here `2Q-sigma=alpha^2+2alpha*beta+1>0`.
Its finite upper-rho endpoint is either the central zero-factor face
`q=q0` or the outer `T=2` face, possibly both. The actual rho is strictly
below rho_star.

For every point of (4), set

\[
M(\rho)=\max_{2\le t\le T}R(t).
\]

Since `f''(t)=(t-2)/t^3>0` for t>2, its maximizer is

* `t=2` if `w<=3/4`, with `M=R2:=R(2)`;
* the unique `tau=tau_*(w)` satisfying `f'(tau)=w` if
  `3/4<w<f'(T)`;
* `t=T` if `w>=f'(T)`.

The maximum is continuous. Its first two formulas join with matching
first derivative at `w=3/4`, since `tau_*(w)` tends to 2. At the actual
point, (3) gives a strict interior maximum `M>0`.

## 3. The established scalar inequalities used here

The following statements have separate complete hand proofs and exact
coefficient certificates. Each applies to the fixed actual ratios and
norms; none assumes that the scalar comparison points are trajectories.

1. **[Central residual](MIXED_GLOBAL_SHORT_BRIDGE_CENTRAL.md).** Throughout `0<rho<=1/q0`, `F0<0` and `F<0`.
   This is the general two-secant central comparison, valid for either
   sign of D.
2. **[Entire upper endpoint](MIXED_GLOBAL_SHORT_BRIDGE_UPPER_ENDPOINT.md).** `R(T)<0` for every `q>=q0`, for either
   sign of D. The strengthened order in (1) is retained.
3. **[Central value, ordinary maximum](MIXED_GLOBAL_SHORT_BRIDGE_CENTRAL_FACE.md).** On `q=q0,T>=2`, if
   `3/4<=w<=f'(T)`, the value at the unconstrained maximizing parameter
   is strictly negative. The convex-chord proof works for either sign
   of D under (1).
4. **[Central value, truncated maximum](MIXED_GLOBAL_SHORT_BRIDGE_TRUNCATED_FACE.md).** On `q=q0,T>=2`, `R2<0`,
   for either sign of D. This uses the actual truncated formula and
   does not extend a convex chord below its valid norm interval.
5. **[Positive-D interior derivative](MIXED_GLOBAL_SHORT_BRIDGE_SCALE.md).** If `D>0` and
   `3/4<w<f'(T)`, the interior maximum satisfies `M_rho>0`.
6. **[Nonnegative-D truncated numerator](MIXED_GLOBAL_SHORT_BRIDGE_TRUNCATED_SCALE.md).** If `D>=0`,
   `d[P^2 R2]/dq<0` for all `q>=q_star`.
7. **[Nonpositive-D feasible maximum](MIXED_GLOBAL_SHORT_BRIDGE_NONPOSITIVE_SCALE.md).** If `D<=0`, `T>2`,
   `M>0`, and `R(T)<0`, then `M_rho>0`. This includes `w<=3/4`,
   with maximizer 2. Root feasibility itself supplies the auxiliary
   reverse-centre bound `E_L<3rho_A`, where `rho_A=alpha^2/P`.

For item 7, a root between the maximizing parameter and T gives
`r=1/TB<1/2`, `t=1/t_root<1/2`, `rho_A<=rt`, and upper incident
norms `u<=U(r),w<=U(t)`. The exact reverse-centre identity implies
`E_L<3rho_A`; this bound is reconstructed at every comparison point,
so no extra feasibility boundary has been omitted.

At `q=q_star`, items 2--4 imply `M<0`: if T=2 use item 2;
otherwise q=q0, and the three norm branches use respectively items 4,
3, and 2. Thus the final scalar maximum is always negative.

## 4. Positive bridge diagonal

Suppose D>0. First, item 6 gives a global truncated value sign on (4).
At q=q_star, `R2<0`: use item 4 when q_star=q0, and item 2 when
T=2. Since `P^2 R2` strictly decreases as q increases, it follows that

\[
R2(q)<0\qquad(q\ge q_*).
\tag{5}
\]

Consider the connected component of `{rho: M(rho)>0}` that contains
the actual point. By (5), its maximum cannot occur at t=2. By item 2,
it cannot occur at t=T. Therefore throughout that component the
maximizer is strictly interior and `3/4<w<f'(T)`. Item 5 gives
`M_rho>0` there. It follows that M stays above its positive actual value
as rho increases and cannot leave this component through M=0.

Continuity therefore carries that positive value to rho=rho_star.
This contradicts the negative endpoint value established in Section 3.
There is no omitted lower-norm or upper-derivative exit: each would
put the maximizer at one of the two endpoints already excluded by
(5) or item 2.

## 5. Nonpositive bridge diagonal

Suppose D<=0. On the positive component containing actual data, item 2
excludes a maximum at T. The remaining maximizer is either 2 or the
strict interior one. Item 7 applies to both, and the two envelope
formulas join with matching derivatives. Consequently `M_rho>0`
throughout this component, including crossings of w=3/4.

Exactly as in Section 4, M cannot leave through zero as rho increases.
If T reaches 2, item 2 gives `M=R(T)<0`, contradicting continuity.
Otherwise the comparison reaches the central zero-factor face, where
items 3--4 and item 2 make every maximum branch negative. This is again
a contradiction. A negative auxiliary w is harmless: the truncated
maximum, root reconstruction, and derivative proof all still apply.

Both signs of D are excluded, proving the theorem.

## 6. Consequence and remaining cases

The earlier small-forward-minimum theorem already puts every mixed
absolute active minimum at a reverse centre. The theorem here proves
that such a centre touches a nonshort forward run. In particular a
minimum cannot remain hidden inside a chain with short runs on both
sides. The physical bound `a^2<12/17` from the independent [reverse-centre
scale theorem](MIXED_REVERSE_CENTRE_SCALE_BOUND.md) also applies to it.

F and M2 remain open. A nonshort bridge may still touch that minimum,
and no whole-period escape, cost obstruction, or constrained descent for
all such bridges is asserted here. R, sufficient all-short M1, and M3
remain closed by their separate whole-period arguments. No Lean, Lake,
typechecking, CI, or growing word-length catalogue is used in this proof.
