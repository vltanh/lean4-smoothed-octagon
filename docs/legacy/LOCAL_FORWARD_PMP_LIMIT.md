# What the maximum principle adds to L1, and what it cannot exclude

Date: 2026-11-07. Hand argument; no compilation or numerical premise.

## Result and scope

The full-domain endpoint-rank theorem in
[LOCAL_FORWARD_RANK.md](LOCAL_FORWARD_RANK.md) has a useful consequence:
an actual free-time minimizer containing a positive `012012` window is
normal, and its normalized adjoint on that window is unique. Thus a
stationary window cannot evade an unfavorable needle calculation by
choosing another endpoint multiplier or an abnormal lift.

Nevertheless, **all-control Pontryagin conditions, strict interior
maximization, transverse switches, and existence of a twisted periodic
extension do not exclude every eligible L1 window**. Six consecutive arcs
of the already constructed standard forward polygon family give explicit
examples. Their window costs tend to zero. Their entire periodic costs
are greater than the octagon's, so they do not show that such a window
occurs in a global minimizer.

This is a certificate against a proposed first-order criterion. It is
not a new closed-word comparison, a local optimality theorem for these
windows, or a counterexample to the universal L1 replacement statement.

## 1. Full endpoint rank excludes abnormal lifts

Fix the initial frame and state. Let

\[
E:(q_0,\ldots,q_5)\longmapsto (g_{\rm end},X_{\rm end})
\]

be the endpoint map for the six positive forward arcs, with its target
the five-dimensional frame-and-state manifold. Equivalently, use the
tangent endpoint and the terminal state, as in the rank note. That note
proves that \(dE\) is surjective everywhere in the positive strict-star
domain. The six factors are independent variables; the initial state
does not vary.

Suppose the window is the restriction of a free-time Pontryagin extremal.
Write \(p_e\) for its reduced terminal covector and \(\lambda_0\ge0\)
for the cost multiplier in the minimization convention. The first
variation identity for changes of the six arc durations is

\[
\lambda_0\,dJ=p_e\circ dE.                         \tag{1}
\]

One can obtain (1) directly by integrating the adjoint identity on each
smooth arc. Its boundary term is \(p_e\,dE\); the active Hamiltonian
vanishes because elapsed time is free. Changing from durations to positive
factors is a smooth invertible change of variables, so the same identity
holds for all six factor variations. In the log-time model these are
simply independent positive arc lengths.

If \(\lambda_0=0\), surjectivity of \(dE\) forces \(p_e=0\).
The homogeneous adjoint equation then forces the covector to vanish on
the entire window. This contradicts nontriviality. The covector is taken
on the actual state manifold, so no nonzero ambient normal to the
determinant constraint is being mistaken for a nonzero cotangent class.
Consequently \(\lambda_0>0\), and it may be normalized to one.

With this normalization, (1) uniquely determines \(p_e\): the difference
of two choices annihilates the surjective map \(dE\). Uniqueness of the
linear inhomogeneous adjoint equation determines the whole adjoint on
the window. In particular, at a stationary same-word point the unique
finite-dimensional multiplier is the only possible normalized Pontryagin
endpoint covector. If the window belongs to a global minimizer, its
global multiplier is therefore normal as well.

This implication does not prove Hamiltonian maximality. It makes that
additional test unambiguous.

## 2. An explicit infinite set of eligible windows satisfying full PMP

Use only the existing standard forward family in
[REGULAR_FAMILY_COMPARISON.md](REGULAR_FAMILY_COMPARISON.md).
For an integer \(k\ge2\), set

\[
N=3k+1\ge7,\qquad
q=2\cos\frac{\pi k}{3k+1},\qquad
y_0^2=\frac{4/q-1}{3},\qquad
\tau=\frac{\log q}{\sqrt3\,y_0}.                   \tag{2}
\]

Then

\[
1<q<\sqrt2,\qquad \frac1{\sqrt3}<y_0<1,
\qquad \tau>0.                                   \tag{3}
\]

These are the precise parameter range and discrete compatibility
condition of Hales--Vajjha, Lemma 7.5.5. Theorem 7.5.6 supplies a normal
Pontryagin extremal with \(N\) arcs, its actual frame endpoint \(R\),
and twisted state and costate endpoints. The positive cyclic control
order in the triangular conventions is `012012...`, after a cyclic
relabeling. The choice \(N=3k+1\), rather than an arbitrary number of
equal arcs, is what supplies the full terminal conditions.

For an explicit check of the local factors and strict star domain, put

\[
a=\frac{2}{\sqrt3\,y_0},\qquad
b=a\left(\frac2q-1\right).
\]

After a cyclic relabeling the initial margins are \((a,b,a)\).
They are positive, and

\[
a^2=\frac{4q}{4-q},\qquad a^2+2ab=4.
\]

On a control-0 arc, at partial factor \(r\in[1,q]\), they are

\[
\left(a,\frac{2ar}{q}-a,\frac{2a}{r}-a\right).
                                                               \tag{4}
\]

The second margin grows from \(b\) to \(a\), and the third decreases
from \(a\) to \(b\). Thus all of every closed arc is strict star.
The next arc is the cyclically relabeled copy. Its physical duration is
\(a\log q/2=\tau\), so (2) uses exactly the local factor convention.
Six consecutive arcs have factors \((q,q,q,q,q,q)\), all positive.

The first six arcs occupy duration \(6\tau<N\tau\): they fit strictly
inside one actual period. In particular, this construction does not
repeat the four-arc octagon to manufacture a six-arc window.

### Whole-arc sector eligibility

The standard polygon is an actual balanced convex disk. Equivalently,
its strict-star admissible cyclic trajectory has cost below \(\pi\),
so the existing low-cost reverse construction gives that balanced
representation. Apply the left normalization at the start of the
chosen window to the entire disk.

For every contact \(v_j\), the transformed contact curve begins at
\(v_j\), reaches \(v_{j+1}\) after the full period \(N\tau\), and
traverses a simple boundary with strictly positive radial speed.
The radial-order argument in
[MINIMIZER_WINDOW_AUDIT.md](MINIMIZER_WINDOW_AUDIT.md), Section 3,
uses precisely these geometric facts, not global minimality. It gives

\[
[v_j,g(t)v_j]>0,\qquad[g(t)v_j,v_{j+1}]>0
\quad(0<t\le6\tau).                               \tag{5}
\]

At zero only the expected first bracket vanishes. Because the window
is proper, its terminal brackets remain strict. Thus the complete
sector test holds on all six arcs, not merely at their endpoints.

### The window budget

All \(N\) arcs have the same cost: they are conjugate by the fixed
rotation, which preserves the running cost. The existing regular-family
comparison proves

\[
A_{\rm oct}<C_N<\pi \qquad(N=3k+1\ge7).
\]

Consequently the six-arc physical cost is exactly

\[
C_{\rm win}=\frac6N C_N<\frac{6\pi}{N}\le\frac{6\pi}{7}
<A_{\rm oct}.                                     \tag{6}
\]

Here the last comparison has a simple rational certificate. The octagon
formula, \(\sqrt2<10/7\), and \(\log2<7/10\) give
\(\delta_{\rm oct}>4/5\). Also \(\sqrt3>17/10\) and
\(\pi<22/7\). Therefore

\[
\frac{6\pi}{7}<\frac{132}{49}<\frac{68}{25}
<\frac85\sqrt3<\sqrt{12}\,\delta_{\rm oct}
=A_{\rm oct}.
\]

The middle rational comparison is \(3300<3332\). No approximation
of a factor or an initial state is used. Moreover (6) proves
\(C_{\rm win}\to0\) as \(k\to\infty\).

## 3. All controls and every point of an arc

The normal lift in Hales--Vajjha, Theorem 7.5.1 and Lemma 7.5.3, has
zero active Hamiltonian and a strictly smaller value at either other
vertex in the open arc. At a switch exactly the neighboring controls
tie. Remark 7.5.4 gives a nonzero crossing derivative; the reflected
switching-function identity gives the corresponding sign at the other
end. Conjugation supplies the same statements on every arc.

These are all-control statements. In physical time the Hamiltonian is
a weighted average of its vertex values, with weights

\[
\omega_i=\frac{u_i p_i}{\sum_j u_jp_j}\ge0,
\qquad \sum_i\omega_i=1.
\]

All margins are positive, so the maximum over the whole simplex is the
same as the maximum over its vertices. In the equivalent log clock,
the control dependence is directly affine. The full lifted trajectory
also satisfies the twisted costate endpoints over \(N\tau\), not
just the state endpoints.

By Section 1 its restriction to the six-arc window is the unique normal
adjoint compatible with the same-word first variation. A short
nonactive insertion, corrected to preserve endpoints by the rank
theorem, has first derivative equal to its compensated needle gap.
That gap is nonnegative, and is strictly positive for the missing
third control at a switch. Thus no first-order favorable-needle
criterion can exclude all these eligible windows.

## 4. The exact remaining distinction

The examples satisfy local PMP and admit an actual twisted periodic
PMP extension. They do **not** have an extension supplied here with
whole-period cost at most \(A_{\rm oct}\): their displayed extensions
have strictly larger cost. It would be incorrect to discard the total
budget and treat these two extension conditions as equivalent.

The first-order certificate here makes no second-variation assertion.
The subsequent [LOCAL_FORWARD_REGULAR_DESCENT](LOCAL_FORWARD_REGULAR_DESCENT.md)
proves that these particular standard windows do have a negative constrained
second variation, an exact cheaper same-word replacement, and open
neighborhoods of inputs with the same improvement. Its continuous-q
statement covers 1<q<=5/4 and fixes both endpoints. The separate exact example in
[LOCAL_FORWARD_SIX.md](LOCAL_FORWARD_SIX.md) already shows that universal
same-word negative second variation is false, but its further optimality
properties are a different question.

A uniform L1 route must therefore use more than first-order local PMP
and periodic extendibility. The higher-order theorem just cited resolves
this standard reference family and nearby inputs, but a replacement or
further genuine minimizer restriction on the full asymmetric domain is
still missing. L1 and the five-template implication to N<=5 remain open.
The active global route separately proves an existential uniform bound
and an effective count conditional on a supplied singular clearance.

## Sources and validation

- Hales--Vajjha, [Section 7.5](https://arxiv.org/html/2405.04331v1#Ch7.S5):
  Theorem 7.5.1, Lemma 7.5.3, Remark 7.5.4, Lemma 7.5.5, and Theorem 7.5.6.
- Their [Section 6.6](https://arxiv.org/html/2405.04331v1#Ch6.S6) gives
  the global twisted costate conditions.
- [LOCAL_FORWARD_RANK.md](LOCAL_FORWARD_RANK.md) supplies the hand
  full-domain rank certificate used in Section 1.
- [REGULAR_FAMILY_COMPARISON.md](REGULAR_FAMILY_COMPARISON.md) supplies
  the already proved full-period cost comparison; no further closed
  family has been introduced here.

The parameter identities, margin check, budget comparison, and rank
consequence above are hand arguments. Published PMP results are named
mathematical inputs. An independent review checked the reduced-cotangent
normality argument, exact parameter and orientation conventions, complete
sector eligibility, rational budget comparison, and the cited primary-source
hypotheses. A further hand review found no material issue. No exploratory
script, Lean, Lake, typecheck, or
CI execution was used for this note.
