# A quantitative exclusion of trajectories confined near the circle state

This hand argument applies to **every** integral-admissible trajectory of cost below
`π`. It gives an integrated lower bound on the state anisotropy required to improve
on the circle, and excludes a specified neighborhood of the circle state from containing
an entire global minimizing trajectory. It does not prove the octagon lower bound.

No numerical or symbolic computation is used in the argument. The existing Lean
development supplies uncompiled source versions of its regularity and winding inputs;
no new Lean implementation is included under the current working agreement.

## Definitions and exact result

Let `(T,u,g,X)` be an actual `IsReinhardtAdmissible` trajectory, and write its
determinant-one traceless star state as

\[
X(t)=\begin{pmatrix}a(t)&b(t)\\c(t)&-a(t)\end{pmatrix}.
\]

Define

\[
m(t)=\frac{c(t)-b(t)}2,\qquad
s(t)=\frac{b(t)+c(t)}2,\qquad
n(t)=\sqrt{a(t)^2+s(t)^2},\qquad
\eta(t)=\frac{n(t)}{m(t)}.
\]

Then `m ≥ 1`, `n² = m²−1`, and `0 ≤ η < 1`. The value `n=0` is equivalent to
`X=J`; thus `n` measures deviation from the normalized circle state. The cost is

\[
C=3\int_0^T m(t)\,dt.
\]

For `C < π`, the following inequalities hold:

\[
\boxed{\quad \pi-C\le 3\int_0^T n(t)\,dt.\quad} \tag{1}
\]

If `η(t) ≤ η₀` on `[0,T]`, where `0 ≤ η₀ < 1`, then

\[
\boxed{\quad C\ge\frac{\pi}{1+\eta_0}.\quad} \tag{2}
\]

A second consequence, retaining the terminal time, is

\[
\boxed{\quad C\ge\frac{\pi^2+9T^2}{2\pi}.\quad} \tag{3}
\]

All these statements retain arbitrary measurable simplex controls. They do not assume
bang-bang structure, a switch count, a Pontryagin lift, or a symmetric polygon.

## Hand proof

### 1. The determinant and star component

The determinant identity is

\[
1=-a^2-bc=m^2-(a^2+s^2)=m^2-n^2.
\]

The positive star component implies `c>0` and `b<0`, hence `m>0`. It follows that
`m≥1`, `0≤n<m`, and `0≤η<1`. If `n=0`, then `a=s=0` and `m=1`, giving
`b=-1`, `c=1`, and `X=J`. The converse is immediate.

The interval state is Lipschitz and therefore continuous. Thus these scalar functions
are continuous and integrable on `[0,T]`. No regularity of `u` beyond admissibility is
used here.

### 2. Reflected-row angular speed

Let `v=(g₀₀,-g₀₁)`. It never vanishes because `det g=1`. From `g′=gX`,

\[
v'=\begin{pmatrix}a&-c\\-b&-a\end{pmatrix}v.
\]

Choose its continuous angle lift `θ`, normalized by `θ(0)=0`, and write
`v=r(cos θ,sin θ)`. Its angular speed is

\[
\theta'
=\frac{-b v_0^2-2a v_0v_1+c v_1^2}{v_0^2+v_1^2}
=m-s\cos(2\theta)-a\sin(2\theta).
\]

The ordinary Cauchy–Schwarz inequality gives

\[
\theta'\le m+\sqrt{s^2+a^2}=m+n. \tag{4}
\]

For cost below `π`, the endpoint `g(T)=R` and the primary-winding argument give
`θ(T)=π/3`, without an additional full turn. That argument is recorded in
[`LOW_COST_WINDING.md`](LOW_COST_WINDING.md) and is applicable to integral-admissible
trajectories through [`CYCLIC_EXTENSION.md`](CYCLIC_EXTENSION.md). Equivalently, one
can work with the original `C¹` frame on the closed interval and its integral angle.

Integrating (4) yields

\[
\frac\pi3\le\int_0^T m+\int_0^T n=\frac C3+\int_0^T n,
\]

which proves (1). If `n≤η₀m`, the same inequality is
`π≤(1+η₀)C`, proving (2). The denominator is positive.

### 3. Retaining the terminal time

Set `M=∫₀ᵀm=C/3` and `N=∫₀ᵀn`. Since `m≥1` and `n=√((m−1)(m+1))`,
integral Cauchy–Schwarz gives

\[
N^2
\le\left(\int_0^T(m-1)\right)
   \left(\int_0^T(m+1)\right)
=(M-T)(M+T)=M^2-T^2.
\]

By (1), `π/3−M≤N`. The low-cost assumption gives `π/3−M>0`, so both sides
can be squared:

\[
\left(\frac\pi3-M\right)^2\le M^2-T^2.
\]

Cancelling `M²` and rearranging gives (3). It improves the elementary `C≥3T`
bound by the nonnegative difference

\[
\frac{\pi^2+9T^2}{2\pi}-3T
=\frac{(\pi-3T)^2}{2\pi}.
\]

## What this excludes for a global minimizer

Let `A` be the area of the concrete octagon in circle representation:

\[
A=\sqrt{12}\,\frac{8-\sqrt{32}-\log2}{\sqrt8-1}.
\]

The existing concrete candidate satisfies `0<A<π`. Every full control minimizer has
`C≤A`, by the geometric/control comparison and the octagon competitor. Therefore

\[
\int_0^T n(t)\,dt\ge\frac{\pi-A}{3}>0, \tag{5}
\]

and

\[
\max_{t\in[0,T]}\eta(t)\ge\frac\pi A-1. \tag{6}
\]

To see (6), continuity on the compact interval supplies the maximum `q<1`.
Equation (2) gives `π/(1+q)≤C≤A`, which rearranges to (6). This also shows directly
that the right side of (6) is below one for a minimizer that exists.

In particular, an entire admissible trajectory satisfying

\[
\eta(t)\le\eta_0<\frac\pi A-1\qquad(0\le t\le T)
\]

has cost **strictly greater than the octagon**. If its cost is at least `π`, this follows
already from `A<π`; otherwise it follows from (2). This is an actual excluded class
of competitors, with no regular-polygon restriction.

There is also the terminal-time restriction

\[
0<T\le\frac{\sqrt{2\pi A-\pi^2}}3<\frac\pi3
\]

for every global minimizer. Its square-root argument is positive because (3) and
`T>0` imply `2πC−π²>0`, while `C≤A`.

## Limits of this argument

The inequality permits excursions outside the excluded neighborhood, including short
excursions. It supplies neither a uniform distance from the singular locus nor a lower
bound on the time between switches. It therefore does not justify finite enumeration.

The angular estimate replaces the exact directional expression
`−s cos(2θ)−a sin(2θ)` by its magnitude `n`. This loses the relation among its direction,
the original control dynamics, and the full matrix endpoint. Removing that loss while
retaining all admissible trajectories is a possible route to a stronger comparison;
the present estimate alone leaves the octagon lower bound open.

## Sources and status

- The control, cost, and star-state conventions are those of the pinned
  [reference definitions](https://github.com/vltanh/lean4-smoothed-polygon/blob/8ce732873a1aa054e98dac46cfaa8d7bb96ffa6f/SmoothedPolygons/Defs.lean).
- The exact candidate value and strict comparison with `π` are reused in
  [`CONTROL_BOUNDS.md`](CONTROL_BOUNDS.md).
- The actual geometric/control correspondence is in
  [`REVERSE_COMPARISON.md`](REVERSE_COMPARISON.md).

The algebra and integral estimates above are complete hand arguments. They do not
certify the existing uncompiled Lean files or assert the full Reinhardt conjecture.
