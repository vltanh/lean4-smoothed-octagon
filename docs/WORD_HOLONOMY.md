# Endpoint holonomy: exclusion and uniqueness for arbitrary finite words

This note gives an exact endpoint reduction for any finite word of positive
vertex-control arcs. It proves two useful restrictions:

1. A noncentral hyperbolic or parabolic endpoint holonomy cannot close a
   determinant-one star state.
2. For noncentral elliptic holonomy, the word and its exponential factors
   determine at most one admissible initial state and hence at most one
   trajectory, with the initial frame fixed to the identity.

The two central holonomies are treated separately. They do not determine
the initial state, and discarding them would leave a gap. Their feasibility
reduces to finitely many strict linear inequalities on an initial direction;
their cost is an explicit quadratic quotient on that cone.

These statements apply to arbitrary finite word length and unequal arc
durations. They do not impose Pontryagin conditions or strong
transversality on individual arcs. They do not bound the word length or
prove the octagon comparison. The proof uses elementary matrix identities
and exact constant-control integration; no numerical or symbolic
computation, Lean compilation, or kernel validation is used here.

## 1. Conventions

Use the same rational coordinates as
[`FOUR_LINK_HAND_PROOF.md`](FOUR_LINK_HAND_PROOF.md): conjugate the original
matrices by `B⁻¹(·)B`, where `B=diag(1,√3)`. In this note `g,X,R` denote
the conjugated matrices, and

\[
D_0=\begin{pmatrix}0&-1\\-1&0\end{pmatrix},\quad
D_1=\begin{pmatrix}-1&2\\0&1\end{pmatrix},\quad
D_2=\begin{pmatrix}1&2\\0&-1\end{pmatrix},\quad
R=\begin{pmatrix}1/2&-3/2\\1/2&1/2\end{pmatrix}.
\]

Here `D_i=−√3 B⁻¹Z_{e_i}B`. Each `D_i` is traceless and squares to the
identity. For a traceless matrix `Y=[[a,b],[c,−a]]`, define

\[
p_0(Y)=-b-c,\qquad p_1(Y)=2(c-a),\qquad p_2(Y)=2(c+a).
\tag{1}
\]

Equivalently, `p_i(Y)=tr(D_iY)`. Direct expansion gives

\[
p_0(Y)p_1(Y)+p_1(Y)p_2(Y)+p_2(Y)p_0(Y)=4\det Y.
\tag{2}
\]

Thus the strict star states in these coordinates are exactly the
traceless determinant-one matrices with all three `p_i>0`. In particular,
their lower-left entry is positive. Conversely, any traceless `Y` with
all `p_i(Y)>0` has positive determinant, and `Y/√det Y` is a strict star
state. This observation will handle the central case without a hidden
rank assumption.

At vertex control `i`, the actual equations are

\[
g'=gX,\qquad X'=[D_i,X]/p_i(X).
\tag{3}
\]

The normalized cost is

\[
\delta=\frac{\mathrm{cost}}{\sqrt{12}}
=\frac14\int_0^T(3X_{21}-X_{12})\,dt.
\tag{4}
\]

These are changes of coordinates in the pinned
[`reference definitions`](https://github.com/vltanh/lean4-smoothed-polygon/blob/8ce732873a1aa054e98dac46cfaa8d7bb96ffa6f/SmoothedPolygons/Defs.lean),
with no change of time. Constant-control integration is also given in
[Hales–Vajjha, *Packings of Smoothed Polygons*, §7.1](https://arxiv.org/html/2405.04331v1#Ch7.S1).
All matrix subscripts in this note are row and column numbers `1,2`.

## 2. Exact data for a finite word

Fix a word `i₁,…,i_n`, where `n≥1`, and factors `q₁,…,q_n>1`. Define

\[
H_i(q)=\exp\!\left(\frac{\log q}{2}D_i\right),\qquad
T_i(q)=\exp(-\log q\,D_i)=H_i(q)^{-2}.
\tag{5}
\]

The state conjugators multiply in chronological order on the left:

\[
H^{(0)}=I,\qquad
H^{(k)}=H_{i_k}(q_k)\cdots H_{i_1}(q_1),\qquad H=H^{(n)}.
\tag{6}
\]

The tangent transitions multiply on the right in the opposite order:

\[
F=T_{i_1}(q_1)\cdots T_{i_n}(q_n).
\tag{7}
\]

Keeping these two product orders distinct is essential.

For an initial state `X₀`, let

\[
X_k=H^{(k)}X_0(H^{(k)})^{-1}.
\tag{8}
\]

On arc `k`, write `a_k=p_{i_k}(X_{k-1})`. If this margin is positive,
the factor `q_k` corresponds to duration

\[
t_k=\frac{a_k}{2}\log q_k>0.
\tag{9}
\]

The margin `p_{i_k}` is constant on that arc by cyclic invariance of
trace, so (8) is exactly the solution of the state equation (3).

For the tangent frame `V=gX`, the identities

\[
X^2=-I,\qquad D_iX+XD_i=\operatorname{tr}(D_iX)I
\]

give

\[
V'=-\frac2{p_i(X)}VD_i.
\tag{10}
\]

Indeed, substitute (3) into `(gX)′`, and use the anticommutator identity
to combine `−g+gD_iX/p_i−gXD_i/p_i`. Equations (5), (9), and (10)
therefore imply

\[
V(T)=X_0F\qquad\text{when }g(0)=I.
\tag{11}
\]

## 3. Both endpoints reduce to two matrix conditions

The full admissible endpoint conditions are

\[
g(T)=R,\qquad X(T)=R^{-1}X_0R.
\tag{12}
\]

They imply `V(T)=X₀R`; since `X₀` is invertible, (11) gives the
shape-independent equation

\[
\boxed{F=R.}
\tag{13}
\]

By (8), the terminal state equation is equivalent to

\[
HX_0H^{-1}=R^{-1}X_0R
\quad\Longleftrightarrow\quad
[K,X_0]=0,\qquad K:=RH.
\tag{14}
\]

Conversely, suppose (13), (14), and full-arc strict star feasibility hold.
Construct the arcs with durations (9), solve `g′=gX` from `g(0)=I`,
and use (11). The determinant of the frame stays one because
`(det g)′=(det g) tr X=0`. Then

\[
g(T)=V(T)X(T)^{-1}
=X_0R\,(R^{-1}X_0^{-1}R)=R.
\]

Thus no independent position-endpoint equation remains after (13) and
(14) are imposed. In particular, a position calculation cannot impose
an additional shape parameter on a noncentral case already satisfying
these two equations.

The constructed states and frame are continuous at the finitely many
joins, piecewise continuously differentiable, and absolutely continuous.
Their controls are measurable vertex controls. Strict star feasibility
on each closed arc keeps every denominator away from zero there. Hence
this construction satisfies the actual integral-form trajectory
equations, not just formal endpoint identities.

## 4. Holonomy classification and the unique noncentral state

Because each factor in (5) and `R` has determinant one, `det K=1`.

### 4.1 The centralizer identity

For any real traceless `X` with `det X=1`, its real centralizer consists
exactly of

\[
\{\alpha I+\beta X:\alpha,\beta\in\mathbb R\}.
\tag{15}
\]

Here is a direct proof. For any nonzero vector `v`, the vectors `v,Xv`
are independent: dependence would give a real eigenvalue `λ` of `X`,
contradicting `X²=−I`. If `K` commutes with `X`, write
`Kv=αv+βXv`. Then `KXv=XKv=αXv−βv`, so `K=αI+βX` on the basis
`v,Xv`. Conversely every such matrix commutes with `X`.

Moreover

\[
\operatorname{tr}(\alpha I+\beta X)=2\alpha,\qquad
\det(\alpha I+\beta X)=\alpha^2+\beta^2.
\tag{16}
\]

### 4.2 Nonelliptic, noncentral holonomy is impossible

If a determinant-one initial state solves (14), equations (15)–(16)
force

\[
K=\alpha I+\beta X_0,\qquad
\alpha=\tfrac12\operatorname{tr}K,\qquad
\alpha^2+\beta^2=1.
\]

Consequently:

| Matrix `K` | Consequence |
| --- | --- |
| `|tr K|>2` | No determinant-one traceless state commutes with `K`. |
| `tr K=2` and `K≠I` | No such state; the only possible `β` would be zero. |
| `tr K=−2` and `K≠−I` | No such state for the same reason. |
| `K=I` or `K=−I` | Every state commutes with `K`; see Section 6. |
| `|tr K|<2` | Exactly two determinant-one traceless commuting states, opposite in sign. |

Thus every factor tuple satisfying (13) but having noncentral hyperbolic
or parabolic `K` is excluded, at any word length.

### 4.3 Elliptic holonomy determines the state and its sign

Assume `|tr K|<2`. Put

\[
\alpha=\tfrac12\operatorname{tr}K,\qquad
Y=K-\alpha I,\qquad \Delta=1-\alpha^2>0.
\tag{17}
\]

Cayley–Hamilton gives `Y²=−ΔI` and `det Y=Δ`. The only candidates are

\[
X_0=\frac{Y}{\sqrt\Delta}
\quad\text{or}\quad
X_0=-\frac{Y}{\sqrt\Delta}.
\tag{18}
\]

Since `Δ>0`, the lower-left entry `Y₂₁` cannot be zero: otherwise
`det Y=−Y₁₁²≤0`. A strict star state has positive lower-left entry, so
at most one candidate survives:

\[
\boxed{
X_0=\frac{\sigma Y}{\sqrt\Delta},\qquad
\sigma=\operatorname{sign}(Y_{21}).
}
\tag{19}
\]

This sign test alone is necessary, not sufficient. All three initial
star margins, and the arc constraints below, must still be positive.
When they are, (19) determines every intermediate state, every duration
in (9), and the full frame from its initial value. Thus the admissible
trajectory is unique for the fixed noncentral word-factor data, up to
the irrelevant values of its control at the finitely many joins.

## 5. Complete arc feasibility is a finite strict sign test

At vertex `i`, write the initial margins as
`p_i=a`, `p_{i+1}=b`, `p_{i-1}=c`, with cyclic indices modulo three.
Direct differentiation of (1), using (3), gives

\[
p_i'=0,\qquad
p_{i+1}'=2(p_i+p_{i+1})/p_i,\qquad
p_{i-1}'=-2(p_i+p_{i-1})/p_i.
\]

For a local time `t`, put `w=exp(2t/a)`. The exact margins are

\[
p_i=a,\qquad p_{i+1}=(a+b)w-a,\qquad
p_{i-1}=(a+c)/w-a.
\tag{20}
\]

For an arc of factor `q>1` starting in the strict star domain, the
constant and increasing margins stay positive. The remaining margin
decreases, so positivity on the entire closed arc is equivalent to

\[
\boxed{1<q<1+c/a.}
\tag{21}
\]

It is also equivalent to positivity of all three margins at the terminal
state. Therefore, for the noncentral elliptic candidate (19), the full
continuous feasibility test is exactly

\[
p_j\!\left(H^{(k)}(\sigma Y)(H^{(k)})^{-1}\right)>0
\qquad (j=0,1,2;\ k=0,\ldots,n).
\tag{22}
\]

Division by the common positive `√Δ` does not affect these signs. No
sampling of an arc, or unstated claim that endpoint feasibility implies
interior feasibility for an arbitrary curve, is involved: it follows
from the explicit monotone functions in (20).

Combining (13), (17), (19), and (22) gives a necessary and sufficient
test for a fixed factor tuple with noncentral holonomy to produce an
actual admissible trajectory. The necessity and sufficiency both use
the real state equations.

## 6. The central cases: a cone of initial directions

Suppose instead that `K=I` or `K=−I`, and retain (13). Equation (14)
then imposes no condition on the initial state. Define the cone

\[
\mathcal C=\left\{Y:\operatorname{tr}Y=0,\quad
p_j\!\left(H^{(k)}Y(H^{(k)})^{-1}\right)>0
\text{ for every }j,k\right\}.
\tag{23}
\]

For the fixed word factors, each condition is a homogeneous strict
linear inequality in the three entries of the traceless matrix `Y`.
Thus `𝒞` is an explicitly given open convex cone, possibly empty.
The `k=0` conditions and (2) imply `det Y>0` for every `Y∈𝒞`.

Consequently the full set of feasible initial states is exactly

\[
\boxed{\{Y/\sqrt{\det Y}:Y\in\mathcal C\}.}
\tag{24}
\]

Every such state has the actual endpoints by Section 3 and the
full-arc star property by Section 5. Conversely any admissible initial
state lies in this cone and is already normalized. If the cone is
nonempty, its normalized directions form an open set in the
two-dimensional determinant-one state surface; there is no uniqueness
conclusion in this case.

This is also an exact feasibility reduction: after word factors are
fixed, central-case existence requires only a nonzero solution to the
displayed strict linear inequalities, since determinant positivity
follows from them. No conjecture that the central cases are impossible
has been used.

## 7. Rational factor tests and an exact cost formula

The square roots in `H_i(q)` can be removed from the direction and sign
calculations. Define

\[
Q_i(q)=(q+1)I+(q-1)D_i,
\qquad H_i(q)=\frac{Q_i(q)}{2\sqrt q},
\qquad \det Q_i(q)=4q.
\]

Set

\[
\mathcal K=R Q_{i_n}(q_n)\cdots Q_{i_1}(q_1),\qquad
\mathcal Y=\mathcal K-\tfrac12\operatorname{tr}(\mathcal K)I,
\]

\[
\mathcal D=\det\mathcal K
-\tfrac14\operatorname{tr}(\mathcal K)^2.
\tag{25}
\]

Since `K` is `𝒦` divided by the positive scalar
`2ⁿ√(q₁⋯q_n)`, ellipticity is exactly `𝒟>0`, and the normalized state
in (19) is

\[
X_0=\frac{\operatorname{sign}(\mathcal Y_{21})\mathcal Y}
{\sqrt{\mathcal D}}.
\tag{26}
\]

Centrality is checked by the two off-diagonal entries and equality of
the diagonal entries of `𝒦`; there is no division by a possibly zero
off-diagonal entry. The prefix conjugations in (22)–(23) can likewise
use products of the `Q_i`: their positive scalar factors cancel in
conjugation. Their inverses are adjugates divided by the positive
determinants. Thus all these feasibility conditions are explicit
rational inequalities in the positive factors, with no matrix rank
assumption.

For completeness, the cost is also explicit. On one arc write
`D=D_i`, `c=p_i(X)`, and `ℓ=log q`. Constant-control integration gives

\[
\int X(t)\,dt
=\frac c2\sinh\ell\,X
 +\frac{c^2}{4}(\ell-\sinh\ell)D
 +\frac c4(\cosh\ell-1)[D,X].
\tag{27}
\]

Apply the linear functional `(3M₂₁−M₁₂)/4` to (27) and sum over all
arcs to obtain `δ`. This follows directly from (4); no numerical
integration is required.

Every term in (27) is homogeneous of degree two in the initial
traceless direction, because `c` is linear in that direction and the
prefix state maps are linear. Hence for fixed word factors there is an
explicit quadratic form `𝒬` such that

\[
\delta\left(\frac{Y}{\sqrt{\det Y}}\right)
=\frac{\mathcal Q(Y)}{\det Y}.
\tag{28}
\]

Its coefficients involve rational functions of the factors and their
logarithms. In the noncentral case, substitute the determined direction
`𝒴` from (25), so the cost is a function of the word factors alone. In
the central case, (28) must still be minimized over the cone (23);
pretending that the initial shape was eliminated there would be invalid.

## 8. Consequence and remaining comparison

For each finite word, the actual endpoint and star constraints can now
be tested without an additional unspecified initial-shape search in the
noncentral case:

- First impose the rational tangent product (13).
- Reject noncentral holonomy with `|tr K|≥2`.
- For elliptic holonomy, determine the only possible state by (19),
  check the finite signs (22), and evaluate its exact cost by (27).
- Retain the two central cases with their complete cone and quadratic
  quotient description (23)–(28).

This reduction applies directly to unequal five-arc families and to
longer finite words. It proves exclusion and shape uniqueness where
stated; it does not establish a universal lower bound for the resulting
cost functions. In addition, a result for all finite words still needs
a justified connection to arbitrary minimizing trajectories or a direct
argument for general measurable controls. There is no proved uniform
word-length bound in this note.

The four-link comparison is a separate proved restricted result in
[`FOUR_LINK_HAND_PROOF.md`](FOUR_LINK_HAND_PROOF.md). The general
holonomy reduction does not assume that comparison or extend its
inequality to the remaining words without further proof.
