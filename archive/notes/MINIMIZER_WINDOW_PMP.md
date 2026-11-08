# Genuine switches impose endpoint ties on minimizing windows

Date: 2026-11-07. A necessary-condition hand lemma; no new universal
local replacement or numerical search.

## Result and scope

A window selected by the coverage argument consists of **six complete
positive control pieces**. Its initial and terminal times are genuine
switches in the actual twisted extension, not arbitrary cuts through
the first and last constant-control arcs.

For L1, the full endpoint-rank theorem makes the normalized Pontryagin
covector unique. Consequently an actual selected minimizing `012012`
window must have an inactive vertex tied with the active vertex at
**each external endpoint**, for that same unique covector. This condition
is stronger than the current state, cost, and sector eligibility tests.

The exact example in [LOCAL_FORWARD_SIX.md](LOCAL_FORWARD_SIX.md) has
strictly unique active maximizers at both external endpoints. It
therefore cannot be a selected six-complete-piece window of an actual
minimizer. The same exclusion holds on an open neighborhood of that
input, using stationarity together with the endpoint ties. This is
consistent with its strong local optimality for its own arbitrary
fixed endpoints and with its separately proved nonlocal replacement.

This note does **not** silently replace the domain of the current L1
claim. That claim remains open on its stated eligibility domain. The
lemma validates an additional necessary condition available for an
explicitly strengthened bounded-reduction route. Section 6 applies
the same argument to the padded reverse-edge L3 counterexamples, using
their separately proved local endpoint rank. They also fail the
external-switch condition.

L1, L2, L4, and L5 remain open. The original L3 target is false on its
stated domain even with arbitrary measurable replacements, as recorded
in [LOCAL_REVERSE_SIX_GLOBAL_MINIMUM.md](LOCAL_REVERSE_SIX_GLOBAL_MINIMUM.md)
and its finite-piece foundation
[LOCAL_REVERSE_SIX_OBSTRUCTION.md](LOCAL_REVERSE_SIX_OBSTRUCTION.md).
The domain or reduction must be repaired. Excluding the known
counterexamples from a stronger necessary domain does not prove the
local improvement theorem on that domain.

## 1. Precise minimizer-window lemma

Take a finite, cyclically reduced vertex representative of an actual
global minimizer, with \(N\ge6\) positive pieces in one period. Use the
actual twisted extension and the P0 selection in
[MINIMIZER_WINDOW_AUDIT.md](MINIMIZER_WINDOW_AUDIT.md). Suppose the
selected six complete pieces, after cyclic relabeling, have controls

\[
(0,1,2,0,1,2).                                           \tag{1}
\]

Left normalize the initial frame to the identity. Keep its initial
state fixed and write \(q=(q_0,\ldots,q_5)\) for the six positive
factors. Let \(J(q)\) be the normalized physical window cost, and let
\(E(q)\) be any smooth local chart of its full frame-and-state endpoint.
The tangent endpoint and terminal state give the equivalent chart
used throughout the existing notes. Put \(M=dE\) and \(G=dJ\).

Then the following are necessary.

1. The global cost multiplier is nonzero. With the minimization
   multiplier normalized to one there is a unique endpoint covector
   \(\lambda\) satisfying
   \[
   G=\lambda M.                                        \tag{2}
   \]
2. Let \(\mathcal D^-_j\) and \(\mathcal D^+_j\) be the compensated
   initial and terminal log-needle derivatives defined in Section 3.
   All are nonnegative, and
   \[
   \mathcal D^-_0=0,\qquad \mathcal D^+_2=0.             \tag{3}
   \]
3. For the actual preceding and following labels \(j_-\) and \(j_+\),
   \[
   j_-\in\{1,2\},\quad j_+\in\{0,1\},\qquad
   \mathcal D^-_{j_-}=0,\quad\mathcal D^+_{j_+}=0.       \tag{4}
   \]
   Equivalently, without specifying those neighboring labels,
   \[
   \min(\mathcal D^-_1,\mathcal D^-_2)=0,\qquad
   \min(\mathcal D^+_0,\mathcal D^+_1)=0.               \tag{5}
   \]

Thus there are only the four possible pairs of necessary zero equations
indexed by \((j_-,j_+)\in\{1,2\}\times\{0,1\}\). These cases may
overlap: a three-way Hamiltonian tie is allowed. No simple-switch,
transversality, or nonsingular-costate hypothesis is added.

If \(N=6\), the twist fixes the actual neighbors more specifically:

\[
\boxed{j_-=j_+=1,\qquad
\mathcal D^-_1=\mathcal D^+_1=0.}                       \tag{6}
\]

We do not assert that the two endpoint equations are independent,
especially in this whole-period case.

## 2. Why abnormality and multiplier ambiguity cannot evade the test

[LOCAL_FORWARD_RANK.md](LOCAL_FORWARD_RANK.md) proves that the endpoint
differential \(M\) has rank five throughout the entire positive L1
domain. It includes every initial state and unequal positive factor
tuple; no generic-rank qualification is needed here.

The free-time adjoint first-variation identity on the window is

\[
\lambda_0\,dJ=p_e\circ dE,\qquad \lambda_0\ge0,          \tag{7}
\]

where \(p_e\) is a covector on the actual five-dimensional endpoint
manifold. Varying the six arc durations produces (7); the active
Hamiltonian is zero because terminal time is free. Passing to factors
is an invertible change of variables: each factor has positive
derivative with respect to its own duration, while the preceding state
depends only on earlier durations.

If \(\lambda_0=0\), surjectivity of \(dE\) forces \(p_e=0\).
Uniqueness of the homogeneous adjoint equation then makes the covector
zero on the window, contradicting Pontryagin nontriviality. This uses
the reduced cotangent manifold; an ambient normal to the determinant
constraint is not a nonzero cotangent class. Hence \(\lambda_0>0\).
After normalization, (7) is (2). Injectivity of \((dE)^*\) proves
uniqueness of \(\lambda\), and the linear adjoint equation determines
its entire trajectory uniquely on the window.

In particular, the adjoint inherited from the global minimizing lift
is exactly the one recovered from the six-window stationary multiplier.
One cannot choose another normal multiplier to manufacture an endpoint
tie. Nor can one instead choose an abnormal multiplier.

## 3. Exact endpoint equations using finite insertion derivatives

For each \(j\in\{0,1,2\}\), prepend a factor \(e^\varepsilon\) with
control \(j\) to the six old pieces, retaining the prescribed initial
state of the whole inserted path. Denote its cost and endpoint by
\(J^-_j(\varepsilon)\) and \(E^-_j(\varepsilon)\). Similarly append
such a factor to define \(J^+_j,E^+_j\). At zero these are the old cost
and endpoint. Define

\[
\boxed{
\mathcal D^\pm_j=
\left.\frac{d}{d\varepsilon}
\bigl(J^\pm_j(\varepsilon)-\lambda E^\pm_j(\varepsilon)\bigr)
\right|_{\varepsilon=0}.}                              \tag{8}
\]

The derivatives can be taken from the right; the exact flow formulas
have smooth extensions through \(\varepsilon=0\). No negative-time
piece is used as a competitor. This construction inserts at the
junction itself, so it does not create a variable negative duration
by perturbing a zero-length split arc.

Equations (8) are finite formulas in the original factors, initial
state, and \(\lambda\): use the exact tangent factors, margin updates,
and arc-cost formula in [BOUNDED_REDUCTION.md](BOUNDED_REDUCTION.md).
Any invertible five-column minor of \(M\) computes \(\lambda\) from
(2). Rank five guarantees such a minor everywhere. The full six-column
equation (2), rather than only the chosen five equations, is the
stationarity test.

To identify (8) with the maximum principle, let \(z\) denote the
frame-and-state variable, \(f_j\) its log-time vertex field, and
\(\ell_j\) its running cost in that clock. For the unique normal
adjoint \(p\), write

\[
h_j(z,p)=\langle p,f_j(z)\rangle-\ell_j(z).
\]

At the terminal endpoint, an insertion differentiates the last flow
directly. At the initial endpoint, differentiate the entire old suffix.
The adjoint first-variation identity for that suffix gives, respectively,

\[
\begin{aligned}
\mathcal D^+_j
 &=\ell_j(z_e)-\langle p_e,f_j(z_e)\rangle=-h_j(z_e,p_e),\\
\mathcal D^-_j
 &=\ell_j(z_0)+(dJ_{\rm suffix}-p_e\,dE_{\rm suffix})f_j(z_0)\\
 &=\ell_j(z_0)-\langle p_0,f_j(z_0)\rangle=-h_j(z_0,p_0).
\end{aligned}                                             \tag{9}
\]

Here the initial state remains fixed for the inserted whole path;
only the state passed into its old suffix changes. If the inserted
control agrees with the adjacent active control, the insertion merges
with that old arc. Its derivative is \(q_0\) or \(q_5\) times the
corresponding component of \(G-\lambda M\), proving (3) directly.

The log-time conversion needs the zero-Hamiltonian condition. With
physical active margin \(p_j>0\),

\[
h_j=\frac{p_j}{2}\,H^{\rm phys}_j.                     \tag{10}
\]

The positive factor depends on the vertex. Because the physical
active value is zero and every vertex value is nonpositive, (10)
preserves all maximum inequalities and every zero tie. An equality
between two nonzero physical values would not in general be preserved
by this vertex-dependent scaling; that invalid shortcut is not used.
On the zero level, the same covector also obeys the reparametrized
adjoint equation, since the extra differential of the clock factor
is multiplied by the zero physical Hamiltonian.

## 4. Complete arcs force the external ties, including the twisted seam

The published minimizing Pontryagin lift has continuous state and
costate variables. For each fixed vertex, its physical Hamiltonian is
therefore continuous: its control denominator stays nonzero on the
strict-star trajectory. On every positive open constant-control piece,
free-time PMP says that the active vertex has Hamiltonian zero almost
everywhere and all other vertices have value at most zero.
Continuity extends these statements to that piece's two closed
endpoints.

At the beginning of the selected window, the preceding positive piece
has control \(j_-\ne0\), while the first selected piece has control
zero. Taking limits from the two sides gives

\[
H^{\rm phys}_{j_-}(z_0,p_0)=H^{\rm phys}_0(z_0,p_0)=0.
\]

At its end, the last selected piece has control two and the following
positive piece has control \(j_+\ne2\). Hence

\[
H^{\rm phys}_2(z_e,p_e)=H^{\rm phys}_{j_+}(z_e,p_e)=0.
\]

Equations (9)--(10) prove (4), while the same continuity argument gives
nonnegativity of every gap. This proof permits an isolated three-way
tie and a nontransverse switch.

For a window crossing the old period boundary, use the actual extension

\[
g(t+T)=g(t)R,\quad
X(t+T)=R^{-1}X(t)R,\quad
i(t+T)=i(t)+1\pmod3.
\]

Extend both reduced costates by the same conjugation as \(X\), using
the published transversality conditions. The fixed-vertex Hamiltonian
is continuous across the resulting seams, so the preceding argument
is unchanged. Left normalization is a smooth state transformation,
and cyclic relabeling just permutes the equations and labels.

When \(N=6\), the selected six pieces occupy exactly one period. The
last control is two, so the control just before the initial cut is
\(2-1=1\). The first control is zero, so the control just after the
terminal cut is \(0+1=1\). This proves (6); an untwisted repetition
would give the wrong neighboring labels. For \(N>6\), the predecessor
and successor lie in the actual complementary part of the period,
and the universal choices are precisely the ones in (4).

## 5. Consequence for the exact unequal-factor input

For the fixed input in LOCAL_FORWARD_SIX, put \(L=\log(11/10)\).
The unique multiplier and the endpoint insertions are calculated in
[LOCAL_FORWARD_NEEDLE_AUDIT.md](LOCAL_FORWARD_NEEDLE_AUDIT.md).
They give the four external inactive gaps

\[
\begin{aligned}
\mathcal D^-_1&=
\frac{5(22129701066L-2084631761)}{154480008848},\\
\mathcal D^-_2&=
\frac{622920818386L-55119362577}{1260735609400},\\
\mathcal D^+_0&=
\frac{3(31643419579013L-1878869660311)}{504294243760000},\\
\mathcal D^+_1&=
\frac{25(965682363712L-91013321679)}{18692081070608}.
\end{aligned}                                             \tag{11}
\]

All are strictly positive. For example, the elementary bound
\(L>9531/100000\), proved in that note, makes the numerator inside
the first parentheses greater than
\(2455004760046/100000>0\). The same substitution makes each of the
other three parentheses positive. Equivalently, their signs are
certified by the strictly positive external endpoint entries in that
note's rational table.

There is therefore no choice of the actual preceding or following
distinct control satisfying (4). This input cannot occur as a selected
six-complete-piece minimizing window. The conclusion does not require
the nonlocal replacement or a new estimate on the remainder's cost.

This also yields an open exclusion. Near the input, retain the same
invertible five-column minor and define the smooth covector
\(\lambda=G_I(M_I)^{-1}\). The four functions (8) are continuous in
the two initial-state coordinates and six factors, and all four
remain strictly positive on some open neighborhood. Any actual
minimizing selected input there would have to satisfy the full
stationarity equation (2), making this covector its true normal
adjoint, and would then contradict (4). Nonstationary inputs are
already excluded by (2). No explicit numerical radius or coverage
of the remaining domain is claimed.

There is no conflict with strong local optimality for the fixed
endpoints of this example. That local problem allows the interval
to begin and end inside active arcs of its normal extremal extension;
it does not require an external control change at either endpoint.
The P0 selection requires both changes. Conversely, the standard
PMP windows in [LOCAL_FORWARD_PMP_LIMIT.md](LOCAL_FORWARD_PMP_LIMIT.md)
do begin and end at switches and satisfy the added ties. Thus the
new condition is substantive, but does not itself close L1.

## 6. The padded reverse-edge L3 counterexamples fail the external ties

The construction in
[LOCAL_REVERSE_SIX_OBSTRUCTION.md](LOCAL_REVERSE_SIX_OBSTRUCTION.md)
starts with a reverse-edge core of word `2121` and appends control-0
pieces of physical duration \(h\) at both ends. Write \(P_h\) for the
resulting word `021210`, after left normalization of its initial frame.
Its core size \(b\) is fixed with
\(0<b\le 1/(10000\sqrt3)\). For every such fixed \(b\), there is
\(h_*(b)>0\) such that

\[
\boxed{0<h<h_*(b)\quad\Longrightarrow\quad
P_h\text{ is not a selected six-complete-piece window of an actual
minimizer}.}                                             \tag{12}
\]

This is a necessary-condition exclusion of the explicit family. It
does not deny its fixed-endpoint optimality, which the companion
GLOBAL_MINIMUM note establishes for sufficiently small pads even among
all measurable controls. Nor does (12) assert a full-domain rank or
replacement theorem for L3.

### 6.1 Rank five holds with the initial state fixed

Use physical arc durations as local variables and hold the prescribed
initial frame and state fixed. At zero padding, the four middle edge
durations map with rank three to their edge endpoint coordinates
\((b',w_b,S')\). One way to see the rank is to vary the final \(x\)
coordinate and the two fixed-edge constraints
\((\log w_b,\int w\,dx)\): two distinct switch positions give the
independent columns already proved in the edge switch calculation.
Thus the middle columns span the three-dimensional tangent space to
the edge endpoint submanifold.

The base note's two normal endpoint coordinates \((N_1,N_2)\) vanish
on that submanifold. Its equations (22)--(23) give the normal
projections of the initial and final control-0 duration columns:

\[
\nu_- = A_-\,(1,2y_bL),\qquad
\nu_+ = A_+\,(1,0),\qquad A_-,A_+,y_b,L>0.              \tag{13}
\]

Their determinant is \(-2A_-A_+y_bL\ne0\). Hence three independent
middle-edge columns together with these two outer columns give an
invertible five-column minor of the full endpoint differential.

At zero padding this differential is computed using the smooth local
flow through duration zero; negative durations are used only to
describe a smooth extension, not as admissible pieces. The minor
remains invertible when the two outer durations are small and positive.
This persists while the initial state varies smoothly to the actual
initial state of \(P_h\). For each such input that state is then held
fixed in the endpoint differential. This is the rank statement in
Section 6.4 of the base note, with its fixed-initial-state quantifier
made explicit.

The same rank holds in positive factor variables. Along each vertex
arc its active margin is constant and positive, and
\(q_j=\exp(2t_j/p_j)\). The duration-to-factor map is triangular,
with positive diagonal derivatives \(2q_j/p_j\); dependence of
\(p_j\) on preceding arcs does not change invertibility. The smooth
state coordinate \((x,w,A)\), where \(A=gK(x)\), and the positive
state-only clock used in the base note also preserve this endpoint
rank. No full-domain rank assertion for arbitrary L3 inputs is needed for this
corollary. The later independent theorem in
[LOCAL_MIXED_SIX_RANK.md](LOCAL_MIXED_SIX_RANK.md) establishes that stronger
rank-five statement throughout the entire positive strict-star L3 domain.

### 6.2 Strictness holds at the external cuts, not only in open pieces

Use the base note's minimizing Hamiltonians

\[
\mathcal H_j=\mathcal L+\langle\pi,f_j\rangle,
\qquad d\tau=y\,dt,\qquad
\mathcal L=1+(1+x^2)w.
\]

Their cost is the positive rescaling \(\mathcal A=(2/3)C\).
The explicit normal adjoint in its equations (10)--(13) has active
Hamiltonian zero. On the core, its control-0 gap is

\[
\mathcal H_0-\mathcal H_{\rm edge}=-2B/d,
\qquad d>0,
\]

where, with \(\kappa_b=7b/10\), equation (17) proves

\[
B(S)\le-\kappa_b(L-|S|),\qquad B(-L)=B(L)=0.
\]

The one-sided derivatives exist on the first and last smooth core
arcs. Dividing this inequality by the distance from the appropriate
endpoint gives

\[
B_S(-L+)\le-\kappa_b<0,\qquad
B_S(L-)\ge\kappa_b>0.                                  \tag{14}
\]

On the edge \(S_\tau=w>0\). Since \(B=0\) at the two joins,
the derivative of \(-2B/d\) is strictly positive at the first join
and strictly negative at the last join. These are, respectively,
the gaps \(\mathcal H_0-\mathcal H_2\) and
\(\mathcal H_0-\mathcal H_1\).

Continue the state and adjoint backwards and forwards using control
0. For a switching function \(\Delta=\mathcal H_0-\mathcal H_j\),
the derivative computed using the two Hamiltonian vector fields
agrees at the join: the difference is the Poisson bracket
\(\{\Delta,\mathcal H_0-\mathcal H_j\}=\{\Delta,\Delta\}=0\).
The first strict crossing therefore makes control 0 strictly better
just before the core; the last makes it strictly better just after
the core. The other edge control has a strict gap at each join,
because the edge dual \(\lambda\) has no zero at \(x=\pm b\).
Continuity retains that gap on the short continuations.

Choose a fixed positive continuation length \(\varepsilon_b\) on
each side for which both strict inactive inequalities hold. Then
take \(0<h<\varepsilon_b\). The two external cuts of \(P_h\) lie
strictly inside these longer continuations. In particular, strictness
includes those cuts; it is not inferred merely by taking the closure
of an open strict inequality. At both external endpoints,

\[
\mathcal H_0=0,\qquad
\mathcal H_1>0,\qquad \mathcal H_2>0.                  \tag{15}
\]

The zero active value persists under the autonomous control-0 flow.
The positive physical clock and the positive cost rescaling preserve
the signs and the absence of ties.

### 6.3 Uniqueness makes the failure relevant to an actual minimizer

The explicit normal adjoint satisfies the free-time first-variation
identity for all six duration variations. By Section 6.1, the
endpoint differential is surjective. The proof of Section 2 therefore
applies verbatim at each \(P_h\): an abnormal covector would vanish,
and after fixing the cost multiplier the terminal covector, hence the
entire adjoint, is unique. Changing from the minimizing convention
in (15) to the maximizing convention of Sections 1--4 just reverses
the state covector and Hamiltonian signs. Any minimizing lift containing
this window must use this same normalized adjoint, after the smooth
coordinate and left-normalization transformations.

If `021210` were selected as six complete pieces, its predecessor
would have label in \(\{1,2\}\), and so would its successor.
Continuity of PMP at the two genuine external switches would require
one of those inactive vertices to tie control 0 at each endpoint.
Equation (15) forbids both ties. For a whole-period \(N=6\) window,
the actual twist specifies the predecessor as \(0-1=2\) and the
successor as \(0+1=1\), which are also excluded. Cyclic relabeling
only permutes this contradiction. This proves (12).

The argument depends only on the base note's explicit adjoint,
strict crossing estimate, and local endpoint rank. It does not use
its all-word compactness argument, its fixed-endpoint global
optimality theorem, or ASZ. The external-switch filter thus removes
the entire sufficiently small padded counterexample family from a
necessary domain for selected minimizing windows. It does not show
that the remaining filtered domain admits a cheaper replacement, or
that the five-template sufficient route has been analytically repaired.

## Sources and validation boundary

- Hales--Vajjha, [Sections 6.2 and 6.6](https://arxiv.org/html/2405.04331v1#Ch6.S6),
  supply the free-time maximum principle and the twisted costate
  transversality conditions used here. The published minimizing lift
  is a named mathematical input, not a silently validated Lean theorem.
- [MINIMIZER_WINDOW_AUDIT.md](MINIMIZER_WINDOW_AUDIT.md) supplies the
  complete-piece selection and exact twisted rebase.
- [LOCAL_FORWARD_RANK.md](LOCAL_FORWARD_RANK.md) supplies full-domain
  endpoint surjectivity.
- [LOCAL_FORWARD_NEEDLE_AUDIT.md](LOCAL_FORWARD_NEEDLE_AUDIT.md)
  supplies the exact fixed-example multiplier and gap identities.
- [LOCAL_REVERSE_SIX_OBSTRUCTION.md](LOCAL_REVERSE_SIX_OBSTRUCTION.md),
  Sections 2--4 and 6.4, supplies the padded family's explicit normal
  adjoint, crossing estimate, independent normal endpoint columns, and
  local full-rank endpoint map. Its separate all-word comparison is
  not a premise of the external-switch exclusion.

No claim of independence or generic codimension of the extra equations
is needed. No existing eligibility domain or status ledger is changed
by this note. No new numerical search, Lean, Lake, typecheck, or CI
execution was used. L1, L2, L4, and L5 remain open; the original L3
counterexample requires a repaired domain or a different sufficient
reduction. No repaired uniform improvement theorem is asserted here.
