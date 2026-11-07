# Positive vertex insertions obstruct an unconditional reverse-word bound

Date: 2026-11-07. Hand proof; no Lean, Lake, typechecking, CI,
numerical trajectory, optimization, or increasing-length enumeration.

## Result and scope

There are strictly admissible, complete closed vertex trajectories whose
every cyclic transition is reverse and whose cost is less than \(\pi\).
Their costs approach the concrete octagon cost \(A_{\rm oct}<\pi\).
Thus the proposed statement “every all-reverse closed word has cost at
least \(\pi\)” is false without further hypotheses.

This is an endpoint-preserving insertion argument, not a new
length-by-length cost comparison. It gives no trajectory of cost less
than \(A_{\rm oct}\) and makes no Pontryagin or minimizing claim for
the inserted trajectories. In particular it does not refute an exclusion
restricted to actual minimizing lifts or to suitably constrained PMP lifts.

## 1. General endpoint-preserving insertion lemma

Consider a finite positive vertex trajectory with initial frame \(I\),
initial state free in the two-dimensional strict-star domain, and actual
complete-period endpoints

\[
g(T)=R,\qquad X(T)=R^{-1}X(0)R.
\tag{1}
\]

Parameterize it by the initial state and its positive factors
\(q_j>1\). On a vertex arc its physical duration is
\(p_j(X_{\rm in})\log q_j/2\), where the active margin is positive.
The exact state and tangent-frame transitions, and the integrated cost,
are smooth in these parameters; see
[WORD_HOLONOMY](WORD_HOLONOMY.md).

Suppose the five-dimensional endpoint residual for (1) has rank five
with respect to these original parameters. Insert any fixed finite list
of additional vertex arcs at prescribed positions, allowing positions
immediately before the terminal seam. Give the inserted arcs factors
\(e^{\varepsilon_j}\); they are identity transitions at
\(\varepsilon=0\).

Then, for all sufficiently small independently prescribed
\(\varepsilon_j>0\), the original parameters can be varied smoothly
so that (1) continues to hold. Every original and inserted arc has
positive duration, the complete trajectory stays in the strict star,
and its cost tends to the original cost as \(\varepsilon\to0\).

**Proof.** In local endpoint coordinates write the enlarged residual
as \(E(v,\varepsilon)\in\mathbb R^5\), with
\(E(v_0,0)=0\). Choose five original coordinates whose derivative
minor is invertible and fix the others at their original values.
The parameterized implicit function theorem gives those five coordinates
as smooth functions of \(\varepsilon\), solving
\(E(v(\varepsilon),\varepsilon)=0\).

For this application the transition formulas extend smoothly to
\(\varepsilon_j\) of either sign near zero; their negative values
are only auxiliary arguments of the smooth map. The retained trajectories
use \(\varepsilon_j>0\). Original factors remain greater than one
by openness. The original finite trajectory has a positive uniform margin
from the strict-star boundary. Continuous dependence of each finite arc,
including the short inserted arcs, preserves that margin for small
parameters. Thus every active margin stays positive and the duration
formula gives positive durations. The cost is continuous in the same
finite parameters. This proves the lemma. \(\square\)

## 2. The complete octagon endpoint map has rank five

The octagon uses the forward word \(0120\), with common factor
\(q=\sqrt2\). Retain the determinant-one margins
\(p_0p_1+p_1p_2+p_2p_0=4\).

There are six original variables: two initial-state coordinates and four
factors. A smooth coordinate system for them near the octagon is the
forward active-margin chain

\[
(a_{-1},a_0,a_1,a_2,a_3,a_4),\qquad
a_{-1}=p_2(0),\quad a_0=p_0(0).
\]

Indeed the exact formulas are

\[
b_i=\frac{4-a_{i-1}a_i}{a_{i-1}+a_i},\qquad
q_i=\frac{(a_{i-1}+a_i)(a_i+a_{i+1})}{a_i^2+4}
\quad(0\le i\le3).
\tag{2}
\]

For fixed preceding margins,
\(\partial q_i/\partial a_{i+1}=(a_{i-1}+a_i)/(a_i^2+4)>0\).
Successive inversion of (2) therefore gives a smooth coordinate change
from the initial state and four factors. The initial margins are
\((a_0,b_0,a_{-1})\), and the terminal margins are
\((a_3,a_4,b_4)\). The twisted state endpoint is consequently exactly

\[
a_3=a_{-1},\qquad a_4=a_0.
\tag{3}
\]

The remaining margin equation follows from the determinant constraint.
The two residuals in (3) have rank two. On their four-dimensional kernel
the chain is the cyclic four-margin chart of
[GLOBAL_FORWARD_INDEX](GLOBAL_FORWARD_INDEX.md), Sections 1--3.

In the triangular tangent basis used there, put

\[
\mathsf R=\begin{pmatrix}0&1\\-1&1\end{pmatrix},\qquad
\mathsf A(q)=\begin{pmatrix}q&-q\\q^{-1}&0\end{pmatrix}.
\]

On (3), the remaining full frame endpoint is exactly
\[
\mathsf A(q_0)\mathsf A(q_1)\mathsf A(q_2)\mathsf A(q_3)=-I.
\tag{4}
\]
The cited rank proof applies at \(N=4,k=1,q=\sqrt2\) and gives rank
three for (4). Explicitly its three nonzero Fourier multipliers have
numerators \(4-q\) and \(q(q-1)\), which are positive here.

Thus the state residual has rank two and the frame residual restricted
to its kernel has rank three. The combined residual has rank five.
This is a rank statement for the actual endpoints: the tangent frame
satisfies \(g(T)=X(0)F X(T)^{-1}\), so on the state endpoint
\(F=R\) is equivalent to \(g(T)=R\), as proved in WORD_HOLONOMY.
Both initial-state variables have been retained.

## 3. Applying the lemma to reverse transitions

A forward transition from vertex \(j\) to \(j+1\) modulo three can
be refined by inserting \(j-1\):

\[
j,\ j+1\quad\longmapsto\quad j,\ j-1,\ j+1.
\tag{5}
\]

Both transitions on the right decrease the label by one modulo three.
More generally, any closed finite word with endpoint rank five can be
approximated by an all-reverse word: retain its existing reverse
transitions and use (5) at every forward transition, including the seam.
For a cyclically reduced input this adds at most one arc per original
arc. It is a refinement of a fixed input, not a search over word lengths.

Apply (5) at every forward transition of the octagon, including its
twisted seam. A representative refined period is

\[
0,2,1,0,2,1,0,2.
\]

The next twisted period begins at vertex \(1\), so the final transition
\(2\to1\) is reverse too. Setting the four inserted factors to one
recovers exactly the original \(0120\) trajectory. Section 2 verifies
the rank hypothesis of the insertion lemma. Consequently all four
inserted factors can be made independently greater than one while
correcting the original parameters to keep both exact endpoints.

The resulting trajectories are strict-star, closed, and have only
reverse transitions. Their costs converge to \(A_{\rm oct}\).
Since \(A_{\rm oct}<\pi\), continuity makes their costs less than
\(\pi\) whenever the positive insertions are sufficiently small.
This strict comparison uses the known cost margin, not a numerical
evaluation of the perturbed trajectories.

In particular, for every positive delta the same construction gives an
all-reverse admissible cost below A_oct+delta. Thus no uniform positive
cost gap above A_oct can hold on that unrestricted word class. A strict
pointwise inequality C>A_oct is not refuted by this approximation.

The argument supplies no sign for the difference between the perturbed
cost and \(A_{\rm oct}\). It also supplies no maximizing costate for
the new arcs. Those extra optimality conditions cannot be inferred from
word orientation, full endpoints, and strict-star feasibility alone.
A successful reverse-word exclusion must therefore retain such additional
hypotheses, or prove a different comparison than the unconditional
\(C\ge\pi\) statement refuted here.

The lemma and its rank-five application are hand arguments based on the
exact vertex flow and the previously proved endpoint rank. No additional
closed-word catalogue, sampled trajectory, or kernel validation is used.

Independent internal hand reviews checked the complete insertion proof,
the rank-five argument, the positive parameter cone, both endpoint equations,
the twisted seam, and the cost-continuity conclusion. No material issue
remained. This review is not external peer review or kernel validation.
