# Independent audit of the common augmented-index bridge

Date: 2026-11-07 UTC. Internal hand review of
[MIXED_GLOBAL_AUGMENTED_INDEX](MIXED_GLOBAL_AUGMENTED_INDEX.md).
No Lean, Lake, typechecking, or CI.

## Outcome and boundary

The collapsed operator, its physical stationary multiplier, the full
rank-three tangent constraint, the positive turn block, and the three
bordered-Hessian pairs have been independently checked. No substantive
correction is required. In particular the negative-index identity is

\[
\operatorname{ind}_-(Q_{\rm closed})
=\operatorname{ind}_-(L_{\rm aug})-2(P-n-1)-3.
\]

The proposed bound `ind_-(L_aug)>=2P-1` remains unproved. This audit
does not turn the ordinary scalar Jacobi inertia into a cost index,
or exclude an additional period class.

## 1. Collapse and coefficient derivatives

The switch identities at turns are exactly `y_i=-y_{i-1}` throughout
the open state-closed margin family. Thus the embedding of collapsed
sequences into the original switch sequences, and the subsequent sign
gauge, depend only on the word. They are fixed linear maps when margins
are differentiated. No derivatives of a moving subspace are omitted.

The reverse-run classification permits only classes with zero, one,
or two turns. A class without a turn is a forward row; reverse-centre
edges have turn-containing classes at their ends. The isolated `+-`
row displayed in the source cancels directly. For completeness, the
opposite isolated `-+` row before the final gauge is

\[
-K_{i-1}y_{i-2}+(s_{i-1}^2-s_i^2)y_{i-1}
-K_{i+1}y_{i+1}=0.
\]

In its `P_i` frame the three required quantities are

\[
K_{i-1}y_{i-2}=-s_{i-1}(e_1+e_2),\quad
y_{i-1}=-e_1/s_{i-1},
\]
\[
K_{i+1}y_{i+1}
=(s_i^2/s_{i-1})e_1+s_{i-1}e_2.
\]

Substitution cancels both components. The two-turn class is exactly
the three-factor identity already displayed in
MIXED_GLOBAL_SHORT_RUN_PERIOD. These cases exhaust the identified
classes without an assumption of equal factors.

The positive off-diagonal coefficients and nonzero Wronskians also
hold for nearby state-closed margin chains before centrality is
imposed. Consequently two independent solutions satisfying the
prescribed boundary sign are equivalent to the recurrence monodromy
being that central scalar matrix. The recurrence basis is related by
an invertible change of basis to the actual frame basis. At a central
endpoint the derivative of this conjugating basis cancels, so their
endpoint derivative ranks agree.

Differentiating the original quadratic form before collapse gives
the stated signed Gram stationarity expression. At turns `d_i=d_{i-1}`;
at same-sign indices the usual Gram equation applies. This verifies
the joint Lagrangian with the actual normal covector, including the
sign. The scaling identities also give the factor eight and both
potential signs in the margin block.

## 2. Positive turn block

For a variation supported only on turn indices, the potential term
vanishes and the margin quadratic form is a sum of positive weighted
squares of adjacent ratios `v_i/a_i`. Each connected turn component
meets a same-sign index. A zero sum therefore forces all its ratios
to equal the adjacent zero ratio, hence the variation is zero.
The turn principal block is positive definite.

For an all-short mixed period, every remaining potential is positive
and occurs at a reverse centre. The weighted-square kernel on the
whole connected cycle consists of `v_i=t a_i`; a centre potential
eliminates this kernel unless `t=0`. Thus the stronger all-margin
positivity assertion for that branch is also correct. Neither
positivity statement determines the sign after the subsequent
kernel-vector Schur complement.

## 3. Green boundary identity and actual rank

Use the source convention that `B` has rows `z_{-1}^T,z_0^T`, and
`T` maps the scalar initial pair `(z_{-1},z_0)` to its terminal pair.
Hold this initial basis fixed while varying the recurrence. If `eta`
is its derivative, then `eta_{-1}=eta_0=0` and
`(eta_{P-1},eta_P)^T=T_v B`.

Summing the linearized recurrence gives the sole terminal Wronskian
term

\[
Z^T H_v Z
=-\epsilon c_0
 \{z_{-1}^T\eta_P-z_0^T\eta_{P-1}\}
=-\epsilon c_0 B^T
 \begin{pmatrix}0&1\\-1&0\end{pmatrix}T_v B.
\]

This confirms the sign and the coefficient `c_0`, including variation
of the coefficient across the cut. Since the monodromy has determinant
one, `T_v` is traceless at `T=epsilon I`. Multiplication by the
displayed skew matrix maps the trace-zero matrices isomorphically
to the symmetric matrices. The initial basis is invertible, so the
rank of `v -> Z^T H_v Z` is exactly the actual frame rank.

The separate local rank-five argument realizes all three frame
directions while keeping the terminal state fixed. Extending by the
unchanged tail supplies the corresponding state-closed full-period
variations. This justifies rank three without assuming it from
normality. The six arcs lie within one actual period; the cyclic
rebasing argument covers a seam-crossing window.

## 4. Curvature and the three pairs

On the tangent constraint `Z^T H_v Z=0`, the orthogonal kernel-basis
derivative is `W=-H^dagger H_v Z`. Substitution in the joint Hessian
gives the stated correction
`-2 tr(Z^T H_v H^dagger H_v Z)`. It is the full endpoint curvature,
and its indefinite sign cannot be removed.

The nonzero kernel-vector block contributes two copies of the
nonzero inertia of `H`. Its remaining four-dimensional component is
`W=Z A`, with `A` a real two-by-two matrix. The cross term pairs
`A` with the symmetric matrix `Z^T H_v Z`. Only the symmetric part
of `A` participates, with rank three; its skew part is the common
infinitesimal rotation and is an actual null direction of the whole
joint Hessian. The three symmetric directions give three positive
and three negative bordered-Hessian pairs. The leftover margin
space is exactly the actual tangent space.

This proves the subtraction by **three**, rather than zero or one,
and verifies both signed inertia formulas and the one extra null
direction in the source note. The final index inequality remains the
stated open analytic problem.
