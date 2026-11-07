# Five sufficient targets on complete-switch PMP inputs

Date: 2026-11-07. A necessary-domain and conditional-reduction theorem.
No universal local cost improvement is proved in this note.

## Result and exact status

The original local domain in [BOUNDED_REDUCTION.md](BOUNDED_REDUCTION.md)
contains strict-star, cost-eligible, sector-eligible `021210` paths which
minimize their own fixed-endpoint problem even among arbitrary measurable
controls. That original L3 statement is false. Its status is preserved;
changing its replacement-piece allowance cannot repair it.

This note defines a different, explicit domain for each of the same five
input words. In addition to the original conditions, it requires a single
nontrivial free-time Pontryagin lift on the whole window, with an inactive
Hamiltonian tied at both external endpoints. These are necessary conditions
because the coverage proof selects six **complete** pieces, whose two
external endpoints are genuine switches.

Every actual minimizing window selected by the existing coverage proof
belongs to the revised domain. Therefore strict finite-piece improvement
on each of the five revised domains would still imply the uniform bound
`N<=5`, and hence the retained global comparison and equality conclusion.
The implication is proved below. **All five revised analytic targets are
open.** This is a correction of the sufficient hypotheses, not a completed
uniform reduction or evidence that the remaining inequalities are true.

The displayed endpoint-unique L1 example and the sufficiently small padded
L3 examples are outside these revised domains, by already proved rank and
uniqueness arguments. Excluding those examples does not establish descent
at any of the remaining stationary inputs. In particular, local PMP and
both external ties still admit asymmetric eligible L1 windows.

## 1. Fixed words, original data, and physical vertex fields

Retain the five words and their full eight-coordinate input domains from
BOUNDED_REDUCTION:

| Index | Six controls | Original analytic target |
| --- | --- | --- |
| L1 | `012012` | Open |
| L2 | `021021` | Open |
| L3 | `021210` | False on the original domain, even with arbitrary measurable replacements |
| L4 | `010201` | Open |
| L5 | `021012` | Open |

For each word, the input consists of two initial-state coordinates and six
positive factors. The initial frame is left-normalized to the identity.
Each factor exceeds one; the whole trajectory remains strictly inside the
star domain, has normalized cost at most the octagon's, and satisfies the
geometric sector tests. Denote this original domain by \(D_i\).

Use the original half-plane state chart for the following definition.
Set \(r=1/\sqrt3\), and let

\[
\mathcal M=\mathrm{SL}_2(\mathbb R)\times\mathcal S,
\qquad
\mathcal S=\{(x,y):-r<x<r,\ y>0,\ x^2+y^2>r^2\}.
\]

The full state is \(z=(g,x,y)\), with

\[
X(x,y)=\frac1y
\begin{pmatrix}x&-(x^2+y^2)\\1&-x\end{pmatrix},
\qquad \dot g=gX.
\]

Write \(f_j\) for the smooth physical-time field of vertex \(j\).
Its frame component is always \(gX\); its two shape components are

\[
\begin{aligned}
f_0^{\rm shape}&=
\left(y-\frac{2y^3}{x^2+y^2-r^2},
      \frac{2xy^2}{x^2+y^2-r^2}\right),\\
f_1^{\rm shape}&=\left(y,-\frac{y^2}{r-x}\right),\\
f_2^{\rm shape}&=\left(y,\frac{y^2}{r+x}\right).
\end{aligned}                                                    \tag{1}
\]

The normalized cost \(J=C/\sqrt{12}\) has the state-only physical density

\[
\ell(z)=\frac{3(1+x^2+y^2)}{2\sqrt{12}\,y}>0.                    \tag{2}
\]

These are the same fields and costs as in the pinned geometric/control
problem. The original rational simplex control becomes a convex
combination of these vertex fields under the exact invertible change
\(\theta_j=u_j\gamma_j/\sum_k u_k\gamma_k\), with
\(\gamma_j=-\operatorname{tr}(Z_jX)>0\). Thus testing the three vertex
Hamiltonians tests the entire admissible control simplex. See
[LOCAL_REVERSE_SIX_GLOBAL_MINIMUM.md, Section 1](LOCAL_REVERSE_SIX_GLOBAL_MINIMUM.md).

For an input in \(D_i\), let \(z(t)\), \(0\le t\le T\), be its six
known positive vertex arcs. The physical times are determined by the
positive factors and active margins. This definition does not add a
closed-word condition such as \(F=R\).

## 2. Definition of the revised domain

An input lies in \(D_i^{\rm sw}\) if it lies in \(D_i\) and there exist
a constant \(\lambda_0\ge0\), an initial covector
\(p(0)\in T^*_{z(0)}\mathcal M\), and labels \(j_-,j_+\) satisfying
all of the following conditions.

**Nontriviality.** The pair \((\lambda_0,p(0))\) is nonzero.
Covectors live on the actual five-dimensional state manifold; an ambient
normal to \(\det g=1\) is the zero cotangent class.

**One continuous adjoint.** Propagate that one initial covector along the
entire prescribed trajectory using the adjoint equation of

\[
H_j(z,p)=\langle p,f_j(z)\rangle-\lambda_0\ell(z).                \tag{3}
\]

On an arc with active label \(j\), this is the Hamiltonian system for
\(H_j\). The covector is continuous at all five internal switches.
Different multipliers on different arcs are not permitted.

**Free-time maximality on complete arcs.** At every point of each closed
arc, including both endpoints,

\[
H_{\rm active}=0,\qquad H_k\le0\quad(k=0,1,2).                  \tag{4}
\]

This is a whole-interval condition. A sign test only at the switches or
at a finite grid is not its definition. Internal ties follow from (4)
and the continuity of the adjoint on adjacent arcs.

**External switch ties.** The neighboring labels must be distinct from
the adjacent active labels, and

\[
j_-\ne i_1,\quad j_+\ne i_6,\qquad
H_{j_-}(z(0),p(0))=H_{j_+}(z(T),p(T))=0.                        \tag{5}
\]

All five canonical words start with label zero. Their possible neighboring
labels in this necessary-domain definition are

| Word | Predecessor \(j_-\) | Successor \(j_+\) |
| --- | --- | --- |
| `012012` | \(1\) or \(2\) | \(0\) or \(1\) |
| `021021` | \(1\) or \(2\) | \(0\) or \(2\) |
| `021210` | \(1\) or \(2\) | \(1\) or \(2\) |
| `010201` | \(1\) or \(2\) | \(0\) or \(2\) |
| `021012` | \(1\) or \(2\) | \(0\) or \(1\) |

Three-way ties and nontransverse switches are retained. A choice of tied
neighbor labels is necessary, but not asserted to be sufficient for an
actual positive neighboring extension. Requiring only (5) deliberately
keeps a necessary superset of selected minimizer windows.

Likewise, this definition does not assert a competitive closed extension
or the global costate transversality equations. Those are additional
possible sources of restriction. They are not silently inferred from a
local Hamiltonian lift or from the sector inequalities.

The new unknowns are finite-dimensional: the scalar \(\lambda_0\) and
five initial cotangent coordinates determine the whole adjoint by a
linear equation along the fixed six arcs. If \(\lambda_0>0\), rescale it
to one. If \(\lambda_0=0\), retain a nonzero initial covector, which may
be normalized to unit length in any fixed smooth local trivialization.
The abnormal alternative is not discarded where endpoint rank has not
been established. Finite-dimensional data and a fixed word catalogue do
not make the remaining continuum inequalities a finite certified search.

## 3. Every selected minimizing window belongs to this domain

Take an actual global minimizer with normalized cost at most the octagon's.
Use the published finite bang-bang representation and the established
forward-alternation exclusion, with the premises exactly as audited in
[MINIMIZER_WINDOW_AUDIT.md](MINIMIZER_WINDOW_AUDIT.md).

If its cyclically reduced one-period description has \(N\ge6\) positive
pieces, the hand coverage theorem selects six complete pieces of one of
the five types. These pieces lie within one actual period, after rebasing the
twisted extension when necessary. P0 proves that their left-normalized,
cyclically relabeled input lies in \(D_i\).

The published free-time PMP supplies a nontrivial global cost multiplier
and continuous covector. Restrict that same lift to the six arcs. It gives
the adjoint equation and the zero active Hamiltonian almost everywhere;
continuity gives (4) on all closed arcs. The adjoint cannot become
identically zero on the window when \(\lambda_0=0\), because uniqueness
of its homogeneous differential equation would make the global lift
trivial. Thus nontriviality is retained.

The preceding and following actual positive pieces have different labels
from the first and last selected pieces, by cyclic reduction. Continuity
of their Hamiltonians gives exactly (5). The covectors across the old seam
must use the actual twisted transversality, together with

\[
g(t+T_{\rm per})=g(t)R,\qquad
X(t+T_{\rm per})=R^{-1}X(t)R,\qquad
i(t+T_{\rm per})=i(t)+1\pmod3.                              \tag{6}
\]

Left normalization and cyclic relabeling are fixed smooth transformations
of the full state, so their cotangent transformations preserve the
Hamiltonian equations and signs. This proves membership in \(D_i^{\rm sw}\)
without a rank, normality, simple-switch, or symmetry assumption.

When the six pieces are the whole period, the actual neighbors are more
specific: \(j_-=i_6-1\) and \(j_+=i_1+1\) modulo three. They must still
be distinct from the adjacent controls. The domain above allows the union
of the stated distinct-label choices and so includes every whole-period
case that can actually occur. It makes no incorrect untwisted repetition.

## 4. Rank and explicit evaluation of the necessary conditions

Fix the initial state. Let \(E(q)\) be a smooth local chart of the full
terminal frame/state, and \(J(q)\) the normalized cost. Every lift in
Section 2 satisfies the free-time first-variation identity

\[
\lambda_0\,dJ=p_e\circ dE.                                  \tag{7}
\]

One derives this by varying the six physical durations, using the adjoint
equation and the zero active Hamiltonian. The triangular duration/factor
change has positive diagonal and is invertible, so it is also valid in
the six factor coordinates.

Where \(dE\) has rank five, equation (7) rules out \(\lambda_0=0\).
After normalizing \(\lambda_0=1\), it makes \(p_e\) unique. An invertible
five-column minor computes this covector, while the remaining column is
a genuine stationarity equation. Backward propagation then determines the
entire normalized lift. There is no alternative lift that can repair a
failed sign or endpoint tie.

Full rank is proved on the entire positive strict-star domains for L1,
L3, L4, and L5, respectively, in
[LOCAL_FORWARD_RANK.md](LOCAL_FORWARD_RANK.md),
[LOCAL_MIXED_SIX_RANK.md](LOCAL_MIXED_SIX_RANK.md),
[LOCAL_SIX_VARIATION.md](LOCAL_SIX_VARIATION.md), and
[LOCAL_L5_ENDPOINT_RANK.md](LOCAL_L5_ENDPOINT_RANK.md). No uniform lower bound
on their minors at degenerating boundaries follows. Rank-degenerate L2 inputs
and possible abnormal lifts there must still be retained until separately
resolved.

For L1, [LOCAL_FORWARD_ENDPOINT_FILTER.md](LOCAL_FORWARD_ENDPOINT_FILTER.md)
expresses the four inactive external gaps using active margins and one
three-dimensional frame covector. Its two residuals must each be an
endpoint of an explicitly specified nonnegative interval. These equations
retain both neighboring-label choices and possible triple ties.

If one evaluates gaps in a vertex-dependent logarithmic clock, the
Hamiltonian is multiplied by a positive vertex-dependent factor. That
preserves (4) and the zero ties only because the active physical value is
zero. Equality of two nonzero physical Hamiltonians cannot be transferred
by that argument.

## 5. The corrected conditional implication

For each \(i=1,\ldots,5\), consider the following new analytic target:

> For every input in \(D_i^{\rm sw}\), there exists a positive finite-piece
> strict-star vertex-control path with the same initial frame/state and
> exactly the same terminal frame/state, with strictly smaller cost.

Physical elapsed time may change. The replacement need not itself satisfy
the necessary PMP conditions or the external ties: it is a competitor,
not an asserted minimizer. The P0 geometric splice gives the applicable
global eligibility argument. A theorem restricting the replacement to at
most six pieces would be a stronger sufficient result. No increasing
closed-word comparison is part of this target.

**Conditional theorem.** If these five revised targets hold, the existing
coverage and P0 results imply \(N\le5\) for every global minimizer.

Indeed, suppose a minimizer had \(N\ge6\). Section 3 places a selected
six-piece input in one \(D_i^{\rm sw}\). Its corresponding new target
gives an actual strictly cheaper path with both endpoints preserved.
Splice it into the same period and translate the subsequent time
parameter. The full frame and state agree at both joins. The P0
finite-piece geometric bridge turns the resulting lower-cost integral
trajectory into an admissible competing disk. This contradicts global
minimality.

The existing complete through-five comparison and equality
classification would then give the global cost inequality and affine
rigidity, through the explicit equality transfer in P0. The named
published reductions and retained comparison certificates are the same
inputs as before; this note does not independently re-prove their algebra.

This establishes a logically sufficient restricted package. It establishes
none of its five universal improvement assertions. In particular, the
truth of the new L3 target is not inferred from the fact that its old
counterexamples have been removed.

## 6. What the corrected domain eliminates and what it retains

[MINIMIZER_WINDOW_PMP.md](MINIMIZER_WINDOW_PMP.md) proves that the exact
unequal-factor L1 example has a unique normalized lift with strictly
positive inactive cost gaps at both external cuts. Hence it lies outside
\(D_1^{\rm sw}\). The same argument excludes an open neighborhood, using
full stationarity and smooth multiplier reconstruction.

For each fixed sufficiently small reverse-core size, every sufficiently
small positive-padding L3 example has rank five and a unique normalized
lift whose external active controls are also strictly unique. These
members lie outside \(D_3^{\rm sw}\). This exclusion uses only rank and
the exact first-order certificate; it does not depend on ASZ or on the
all-measurable optimality theorem. It concerns selected complete pieces,
not arbitrary cuts through longer arcs.

The revised domains remain substantial. The explicit five-dimensional
continuation in LOCAL_FORWARD_ENDPOINT_FILTER produces eligible
asymmetric L1 windows satisfying the full local PMP and both genuine
external ties. Their initial-state/factor image cannot lie in the
three-dimensional equal-factor locus. No competitive closed extension
is asserted for those perturbations. The standard forward reference
families also show why unrestricted periodic extendibility alone does
not retain the required total-period cost budget.

The immediate analytic problem is therefore a genuine uniform comparison
or further proved necessary restriction on the remaining inputs. A finite
list of formulas, rank theorems, or excluded illustrative families does
not settle it.

## Sources and validation boundary

- [MINIMIZER_WINDOW_AUDIT.md](MINIMIZER_WINDOW_AUDIT.md) records the exact
  minimizer representation, geometry, twist, and finite-piece splice.
- [MINIMIZER_WINDOW_PMP.md](MINIMIZER_WINDOW_PMP.md) proves the external
  ties and the endpoint-unique example exclusions.
- Hales--Vajjha, [Sections 6.2 and 6.6](https://arxiv.org/html/2405.04331v1#Ch6.S6),
  supplies the free-time PMP and twisted covector transversality.
- BOUNDED_REDUCTION supplies coverage and the unchanged original domains;
  the three rank notes above supply their explicitly stated submersions.

No original domain is silently redefined. The old L3 target remains false;
all five new targets remain open. No Lean, Lake, typecheck, kernel audit,
CI, numerical search, or growing-word enumeration was used for this note.

An independent hand review checked the physical fields and cost, the
cotangent and abnormal alternatives, the neighboring-label table, the
twisted seam, and the exact finite-splice implication. No material gap
was found. That review verifies this conditional theorem, not the five
open analytic premises.
