# Arbitrary switching words: a fixed-edge exclusion

## Proved result and scope

**Every admissible trajectory must use all three control coordinates on sets
of positive measure.** More precisely, let `T > 0`, let `g,X` be an
integral-form state trajectory on `[0,T]`, and suppose

\[
g(0)=I,\qquad g(T)=R,
\qquad
R=\begin{pmatrix}1/2&-\sqrt3/2\\ \sqrt3/2&1/2\end{pmatrix}.
\]

Then no coordinate `u_j` can vanish almost everywhere on `(0,T)`.
Equivalently, no control confined almost everywhere to any one fixed edge of
the control simplex can meet these group endpoints while its state remains
in the strict star domain.

This applies to **arbitrary measurable controls on that edge**, with
arbitrarily many switches or no finite switching description. It does not
use the terminal condition on `X`, costate equations, optimality, a cost
bound, or equal arc lengths. In particular, every finite vertex-control word
that omits any of the three vertices is excluded, regardless of its length.
This excludes all one-arc and two-arc words.

The proof below is a hand argument for the actual integral-form equations.
No new Lean file accompanies it, and no compilation or kernel validation was
run. It does not establish a lower bound on the cost of the remaining words.

## Conventions and exact equations

All vertex indices in this note are `0,1,2`, as in the pinned source. Put
`q = 1/√3` and write

\[
Z_u=\begin{pmatrix}
(u_1-u_2)/\sqrt3&(u_0-2u_1-2u_2)/3\\
u_0&(u_2-u_1)/\sqrt3
\end{pmatrix},
\qquad
X=\Phi(x,y)=
\begin{pmatrix}x/y&-(x^2+y^2)/y\\1/y&-x/y\end{pmatrix}.
\]

The state equations and star restrictions are

\[
g'=gX,\qquad
X'=[P_u(X),X],\qquad
P_u(X)=\frac{Z_u}{\operatorname{tr}(Z_uX)},
\tag{1}
\]

\[
y>0,\qquad -q<x<q,\qquad x^2+y^2>q^2.
\tag{2}
\]

The equations hold almost everywhere, with the state curves given by their
indefinite integrals. The control is measurable and has nonnegative
coordinates summing to one. These are the conventions in
[`Defs.lean`](https://github.com/vltanh/lean4-smoothed-polygon/blob/8ce732873a1aa054e98dac46cfaa8d7bb96ffa6f/SmoothedPolygons/Defs.lean)
and
[`Ch4/StarDomain.lean`](https://github.com/vltanh/lean4-smoothed-polygon/blob/8ce732873a1aa054e98dac46cfaa8d7bb96ffa6f/SmoothedPolygons/Ch4/StarDomain.lean).
In particular, `halfPlaneF₁` and `halfPlaneF₂` use the entries of `Z_u`
directly; this avoids the sign discrepancy in the printed coordinate
abbreviation noted in that source file.

The explicit integration for an edge control also appears in
[Hales and Vajjha, *Packings of Smoothed Polygons*, §8.1, equations
(8.1.1)–(8.1.3)](https://arxiv.org/html/2405.04331v1#Ch8.S1).
The endpoint contradiction below follows from that integration. The argument
is written out so that its scope includes measurable controls and does not
silently assume classical differentiability of the control.

## Hand proof for the edge `u₀ = 0`

### 1. Coordinates and almost-everywhere equations

The integral equations make `g` and `X` absolutely continuous, hence
continuous. If

\[
X=\begin{pmatrix}a&b\\c&-a\end{pmatrix},
\]

then the strict star inequalities give `c > 0`. The definitions

\[
x=a/c,\qquad y=1/c
\]

recover `X=Φ(x,y)`, because `det X = 1`. Since `c` is positive and continuous
on the compact interval, it is bounded away from zero there. Composing the
absolutely continuous entries of `X` with these smooth functions therefore
gives absolutely continuous `x,y`. Their chain-rule derivatives hold almost
everywhere.

Assume `u₀(t)=0` almost everywhere. At those times `Z_u` is upper triangular:

\[
Z_u=\begin{pmatrix}\alpha&-2/3\\0&-\alpha\end{pmatrix},
\qquad \alpha=(u_1-u_2)/\sqrt3.
\]

Substitution into (1), or direct comparison of its `(0,0)` and `(1,0)`
entries, gives

\[
x'=y\qquad\text{almost everywhere}.
\tag{3}
\]

The denominator is nonzero: `|α|≤q` and `|x|<q`, so
`2αx−2/3<0`. Thus this simplification does not divide by a possibly zero
quantity. Since `x` is absolutely continuous and `y` is continuous, (3) also
implies that `x` is continuously differentiable and `x'=y` everywhere on
the open interval.

### 2. Exact integration of the group state

Define

\[
s(t)=\int_0^t\frac{dr}{y(r)},\qquad
h(t)=\begin{pmatrix}1&-x(t)\\s(t)&1-s(t)x(t)\end{pmatrix}.
\]

Then `s(0)=0`, `s'=1/y`, and `det h=1`. Direct multiplication gives

\[
hX=
\begin{pmatrix}
0&-y\\
1/y&-x/y-sy
\end{pmatrix}=h'
\qquad\text{almost everywhere}.
\]

The entries of `h` and `h⁻¹` are absolutely continuous. Consequently
`(g h⁻¹)'=0` almost everywhere. An absolutely continuous function whose
derivative vanishes almost everywhere is constant. Using `g(0)=I` therefore
gives `g(t)=h(0)⁻¹h(t)` throughout the closed interval. With `x₀=x(0)`, this
is the explicit identity

\[
\boxed{
g(t)=
\begin{pmatrix}
1+x_0s(t)&x_0-x(t)-x_0s(t)x(t)\\
s(t)&1-s(t)x(t)
\end{pmatrix}.}
\tag{4}
\]

No derivative of `u` has been used. Altering the control at its exceptional
null set does not change this argument or the integral trajectory.

### 3. The endpoint is impossible in the strict star domain

The lower-left and upper-left entries of `g(T)=R` imply, respectively,

\[
s(T)=\sqrt3/2,\qquad
1+x_0\sqrt3/2=1/2.
\]

Hence `x₀=−1/√3`, contrary to (2) at time zero. The lower-right entry also
forces `x(T)=+1/√3`, contrary to (2) at the other endpoint. Either
contradiction proves the claim. Notice that **the terminal equation for `X`
was never used**.

There is a useful endpoint form of the same obstruction. For an arbitrary
terminal matrix `Q=g(T)` under a fixed-edge control, (4) implies

\[
Q_{00}-x_0Q_{10}=1,\qquad
Q_{11}+x(T)Q_{10}=1,\qquad Q_{10}>0.
\]

Strict star membership then requires

\[
|Q_{00}-1|<qQ_{10},\qquad
|Q_{11}-1|<qQ_{10}.
\tag{5}
\]

The prescribed matrix `R` attains equality in both inequalities and thus
lies on the excluded boundary of this endpoint region.

## Rotation covers every fixed edge

The exact conjugation identities are

\[
RZ_{e_2}R^{-1}=Z_{e_1},\qquad
RZ_{e_1}R^{-1}=Z_{e_0},\qquad
RZ_{e_0}R^{-1}=Z_{e_2}.
\]

They are recorded as `R_conj_controlMatrix_vertex` in the pinned
`Ch4/StarDomain.lean`. Thus conjugation by `R` sends the vertex index `i` to
`i−1` modulo three. If coordinate `u_j` vanishes almost everywhere, conjugate
the trajectory by `C=Rʲ`:

\[
\widetilde g=CgC^{-1},\qquad
\widetilde X=CXC^{-1},\qquad
Z_{\widetilde u}=CZ_uC^{-1}.
\]

The new coordinate `ũ₀` is the old `u_j`. Constant conjugation preserves the
integral equations, permutes the strict star inequalities, and preserves
the simplex. Moreover `C` commutes with `R`, so the group endpoints remain
`I` and `R`. The already proved `u₀=0` case gives a contradiction. This
establishes the asserted result for all three edges, with the rotation
direction made explicit.

## Consequences for arbitrary finite words

Let a vertex-control word be

\[
((i_1,\tau_1),\ldots,(i_N,\tau_N)),\qquad
i_k\in\{0,1,2\},\quad \tau_k>0.
\]

Adjacent equal letters can be merged; zero-duration entries, if present in
an alternative convention, can be deleted. Neither operation changes the
control almost everywhere or the resulting trajectory.

Every admissible such word must contain all three letters. More generally,
for any measurable admissible control, boundedness `0≤u_j≤1` makes each
coordinate integrable, and the fixed-edge exclusion proves

\[
\boxed{\int_0^T u_j(t)\,dt>0\quad(j=0,1,2).}
\tag{6}
\]

Indeed a nonnegative integrable function has integral zero precisely when
it vanishes almost everywhere. The three positive quantities in (6) sum
to `T`. This is a strict positivity result for each individual trajectory;
it does **not** provide a common positive lower bound over all trajectories.
Consequently it is not a dwell-time estimate or a uniform bound on the
number of switches.

## What remains open in this note

The exclusion leaves every word that uses all three vertices. Already at
three arcs the distinct-letter cases remain to be analyzed. No claim is
made here that the cyclic order of a minimizing word is fixed, that all its
durations are equal, or that its individual arcs satisfy the stronger
endpoint relation imposed in the symmetric `(6k+2)` family.

The result therefore removes an infinite family of candidate controls but
does not reduce unrestricted Reinhardt comparison to a finite search. A
uniform word-length bound or another argument covering unbounded word
length would still be required before any finite enumeration could be
called exhaustive.
