# Independent internal audit of closed-lift normality

Date: 2026-11-07 UTC. This review concerns
[GLOBAL_NORMALITY](GLOBAL_NORMALITY.md) at the PR snapshot beginning
`5638fc1`, with the clarifications included in the present revision.
It is an independent internal mathematical review, not external peer
review or Lean kernel validation. No Lean, Lake, typechecking or CI ran.

## Finding

The normality proof is valid under its stated hypotheses: a finite
positive strict-star vertex trajectory, a nontrivial free-time maximizing
PMP lift, and the actual twisted complete-period state, frame and reduced
state-cotangent endpoints. The proof excludes every abnormal lift of such
a trajectory. It does not require a cost cap, full endpoint rank, a
transverse-switch assumption, or a claim that multi-period trajectories
are minimizing.

The implication for all global minimizers additionally uses the current
finite-representation theorem and its retained geometric, compact-state
and PMP inputs. This review checked that dependency direction; it did not
reaudit every upstream geometric or compactness theorem.

## 1. Actual endpoint and cotangent interface

The paired representation is

\[
\Psi_X(F,G)=(XFG^{-1}X^{-1}G,\;G^{-1}XG)
          =(XFX_e^{-1},\;X_e).
\]

The first expanded frame expression here is only a spelling of
\(XFX_e^{-1}\); it keeps the same order of matrix factors. For right
trivialized variations \((A,B)=(\delta F F^{-1},\delta G G^{-1})\),

\[
\delta X_e=G^{-1}[X,B]G.
\]

An elliptic traceless \(X\) has trace-zero centralizer \(\mathbb RX\).
Thus a zero state variation forces \(B=rX\), and a simultaneous zero
frame variation then forces \(A=0\). The differential has the claimed
one-dimensional kernel and is onto the five-dimensional actual endpoint
manifold. Pullback therefore preserves nonzero actual cotangent vectors;
it annihilates exactly that kernel.

For clarity, the endpoint formula is best used in its unexpanded form
\(g_e=XFX_e^{-1}\). It does not identify either paired factor with the
physical frame by itself.

The zero-Hamiltonian duration-column equation follows directly from the
adjoint first-variation identity. At \(\lambda=0\), independent
variations in original positive arc durations contribute their zero
active Hamiltonians. If a missing vertex is inserted with logarithmic
factor \(\epsilon\), its physical duration has positive derivative
\(p_i/2\). Keeping the other logarithmic factors fixed changes their
physical durations, but every such term again multiplies a zero active
Hamiltonian. The insertion pairing is consequently \(p_iH_i/2\), with
no extra state-cost term. At a switch, vertex Hamiltonians are continuous,
so their maximum inequalities and the neighboring active zero values
extend from the adjacent open arcs to the cut itself.

Conjugating away the first factor must transform the lower stabilizer
from \(X\) to the state after that first arc. The proof does this: it is
precisely its margin matrix \(Y\). This is necessary for the sign
calculation and cannot be replaced by the initial state.

## 2. Exact algebra and strict signs

The added companion
[abnormal_normality_certificate.py](../explorations/abnormal_normality_certificate.py)
constructs the three generator matrices, full-factor and half-factor
products, upper/lower columns, and transfer maps directly. Its 22 named
checks include the generator identities, the two determinants, both
transfer maps, four missing-control residuals, all four fourth-column
residuals, four cross-product pairings, and the two terminal triple-tie
residuals. All passed with Python 3.12.14 and SymPy 1.14.0.

The forward first pairing is strictly negative because
\(b,c>1\), \(p_i>0\), and

\[
b^2(p_1+p_2)-p_1=(b^2-1)p_1+b^2p_2>0.
\]

Its second pairing is strictly positive because the end of the second
arc is strict star, giving \(p_0-(b-1)p_1>0\). The reverse first pairing
is strictly positive because both
\(p_1-(b-1)p_2>0\) and \(b(b-1)p_2>0\); its second pairing is strictly
negative because \(bp_0+(b-1)p_2>0\). Each pair is nonzero, so \(Y\) and
the fourth residual are independent. Their annihilator is exactly one
line. The opposite signs on that line exclude both orientations of every
nonzero abnormal covector. This excludes `0120` and `0210` without a rank
assumption on a longer word.

These are symbolic and hand sign checks on the complete strict-star
domain, not samples of factors or states.

## 3. Reverse reading uses only zero identities

The proof does not apply the maximizing principle to a time-reversed
positive control system. On a subwindow \([a,b]\), reverse the state
and covector as \(\widetilde x(s)=x(b-s)\),
\(\widetilde p(s)=p(b-s)\). The reversed vector field is \(-f_i\),
and its homogeneous adjoint equation is
\(\widetilde p'=\widetilde p Df_i\), which follows from the original
abnormal adjoint equation. Its active Hamiltonian remains zero.

The matrix inverse flow has the reciprocal factor \(q^{-1}\), so the
rational fourth-column identities remain valid. Their coefficients stay
nonzero since the original factors exceed one. They force a missing
Hamiltonian to be zero, a statement independent of time orientation.
There is no use of a reversed Hamiltonian inequality or of a
negative-duration admissible competitor. This verifies the `-++` and
`+--` implications, including their switch positions.

## 4. Triple ties and twisted closure

For a single positive arc with initial and terminal triple ties, the
initial three zero pairings force the endpoint functional into the form
\(n(l-t)\). The terminal two zero residuals force \(n_y=n_z=0\), and
\(n(Y)=0\) then forces \(n_x=0\), because the active margin is positive.
This contradicts actual cotangent nontriviality. No assumption that triple
ties never occur was made; only an arc with two triple-tied endpoints
was excluded.

Twisted state and cotangent closure allow the same nonzero lift to extend
in both time directions by cyclic relabeling. After merging equal adjacent
labels, the switches and their positive arcs repeat with the twist. A run
of three identical signs is impossible. A run of two identical signs is
therefore bracketed by opposite signs, and the two previously checked
zero identities put triple ties at the endpoints of its middle positive
arc. This is also impossible. All signs must then alternate, confining
all labels to a two-element set. Translation by one complete period adds
one modulo three to every label, contradicting that two-element set.

This checks arbitrary short periods as well as long ones: a four-arc test
may cross several seams, since its conclusion uses only PMP identities
on an extended lift. It does not compare the cost of a multi-period
replacement.

## 5. What the audit changes

The referenced algebra script was missing from the audited tree. It is
now included, with an explicit command, domains, version output, named
assertions and limits. The proof note now spells out the continuity at
switches and the reversed-adjoint zero argument, and reports this audit
with its limited scope.

A new compactness corollary in the proof note is also valid: on the compact
family of initially unit-normalized global-minimizer lifts, the continuous
function \(-\lambda\) has a strictly positive minimum. Thus rescaling
all such lifts to \(\lambda=-1\) gives another compact family. This is
qualitative; no numerical lower bound on \(-\lambda\) was obtained.

**Global normality is proved under the stated inputs. The sharp octagon
cost inequality, affine uniqueness, all five uniform case exclusions,
and Lean validation remain open.**
