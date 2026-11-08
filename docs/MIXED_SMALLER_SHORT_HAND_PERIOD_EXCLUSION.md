# A complete hand exclusion of the actual smaller-short period

Date: 2026-11-08 UTC. **Complete hand theorem: S7 and H-S are closed.**
All scalar inputs have separate accepted sign reviews. The complete
actual-period implication is accepted in the
[period audit](MIXED_SMALLER_SHORT_HAND_PERIOD_AUDIT.md) and the
[separate scope and boundary audit](MIXED_SMALLER_SHORT_HAND_PERIOD_SCOPE_AUDIT.md).

## Theorem and exact scope

There is no eligible competitive finite normal mixed minimizing
period with at least six positive pieces for which the chosen smaller
turn adjacent to a globally minimal active reverse centre belongs to
a short forward run.

The theorem includes repeated global minima, an equal-turn choice,
arbitrary unequal positive factors and genuine switches through the
twisted seam. It uses one original common normal PMP covector and
the original full-period cost. It imposes no uniform bound on the
number of pieces and uses no executable cover.

Here competitive means \(C_{\rm period}\le A_{\rm oct}\), with

\[
A_{\rm oct}=\sqrt{12}\,
 \frac{8-4\sqrt2-\log2}{2\sqrt2-1}.
\tag{1}
\]

## 1. Keep the actual period while choosing the short bridge

Fix such a period and a globally minimal active reverse centre.
Choose its smaller adjacent turn. If its required incoming orientation
is reversed, use reflection together with time reversal, as proved in
[the minimum-structure theorem, Sections 1--3](MIXED_GLOBAL_MINIMUM_STRUCTURE.md).
That symmetry preserves the positive physical cost multiplier, the
state and frame endpoints, both cotangent endpoints and all simplex
Hamiltonian inequalities. At a tie either turn is a permitted smaller
choice. No symmetry of the two positive factors is assumed.

The common-covector
[six-variable reduction, Sections 1--5](MIXED_SMALLER_SHORT_SIX_VARIABLE_REDUCTION.md)
then supplies the original shape

\[
1\le\alpha<x\le\beta\le\alpha x,
\qquad
\operatorname{Sec}(1,x,\beta)
 =\operatorname{Sec}(\alpha,\beta,x)=u,
\qquad \delta=\beta/x-1\ge0.
\tag{2}
\]

Its outer reverse switch is the actual first descending root, with
\(2<\tau<T\), \(R_\tau=0\), and \(w>3/4\).
The state, frame and covector are taken from their genuine twisted
extension when the window crosses the seam. The incoming and outgoing
norms come from that same covector. No replacement multiplier or
independently chosen pair of incident norms is introduced.

The physical two-turn cost and endpoint formula are those of
[the defect interface](MIXED_GENERAL_SHORT_DEFECT_INTERFACE.md) and
[the shear reduction](MIXED_SMALLER_SHORT_SHEAR_COST_REDUCTION.md).
The two charged positive arcs form a proper subperiod when \(N\ge6\).
The completion estimate uses the rest of the same period once.
Longer displays of the PMP equations may cross the seam; they do not
multiply the available physical cost budget.

## 2. The whole actual domain enters one common small-shape strip

The hand inputs apply in this order:

| Gate | Proved conclusion on the original actual data | Hand source |
|---|---|---|
| S0 | \(x<12/5\), \(D>0\), \(E_L>0\) | [Large-ratio exclusion](MIXED_SMALLER_SHORT_LARGE_RATIO_HAND_EXCLUSION.md) and [positive diagonal/pairing](MIXED_SMALLER_SHORT_POSITIVE_DIAGONAL_PAIRING.md) |
| S1 | \(x>2\) | [Lower-ratio exclusion](MIXED_SMALLER_SHORT_LOWER_RATIO_HAND_EXCLUSION.md) |
| S2 | \(x<13/6\) | [Sharp upper-ratio exclusion](MIXED_SMALLER_SHORT_SHARP_RATIO_HAND_EXCLUSION.md) |
| S3 | \(\delta<1/19\) | [Displacement exclusion](MIXED_SMALLER_SHORT_DISPLACEMENT_HAND_EXCLUSION.md), now with its actual ratio hypotheses supplied |
| S4 | \(\alpha\le1+3\delta\), \(\Gamma_{\rm actual}>1829/10000\) | [Extended upper order](MIXED_SMALLER_SHORT_SMALL_SHAPE_UPPER_ORDER.md) and [extended original-Casimir floor](MIXED_SMALLER_SHORT_EXTENDED_CASIMIR_FLOOR.md) |

S1 and S2 are independent of one another and of the small-shape
restrictions. S3 is applied only after their common interval is
established. S4 covers the full closed interval \([2,13/6]\),
including the strip \([15/7,13/6]\) outside the older Casimir proof.
The older \(183/1000\) floor is unnecessary here.

The [strong lower order](MIXED_SMALLER_SHORT_STRONG_ORDER.md) also gives

\[
\alpha\ge1+
 \left(1+\frac{4x(x+1)}{7x+1}\right)\delta
 \ge1+\frac{13}{5}\delta.
\tag{3}
\]

For the second inequality, \(4x(x+1)/(7x+1)\) increases on
\(x>0\), since its derivative has numerator
\(4(7x^2+2x+1)>0\), and its value at two is \(8/5\).
Together with S4 this supplies

\[
\alpha=1+\eta\delta,
\qquad \frac{13}{5}\le\eta\le3.
\tag{4}
\]

If \(\delta>0\), define \(\eta=(\alpha-1)/\delta\).
If \(\delta=0\), S4 and \(\alpha\ge1\) force \(\alpha=1\);
choose any \(\eta\) in the displayed interval. All subsequent
formulas are regular at this boundary, so no division by \(\delta\)
is used there. Thus every actual case is in the single common domain

\[
2<x<13/6,\quad0\le\delta<1/19,\quad
\alpha=1+\eta\delta,\quad13/5\le\eta\le3,
\quad\Gamma_{\rm actual}>1829/10000.
\tag{5}
\]

## 3. The actual root supplies the physical shear condition

Set

\[
R=\frac{x-1}{x+1},\qquad
T_s=\frac{\beta-\alpha}{\beta+\alpha},\qquad
U_1=\frac{3+R^2}{4},\quad U_2=\frac{3+T_s^2}{4},
\quad A=U_1/U_2-1\ge0.
\]

Here \(T_s\) is an angle coordinate, distinct from the duration
endpoint \(T\). The conditional
[root-to-shear theorem](MIXED_SMALLER_SHORT_SMALL_SHAPE_ROOT_SHEAR.md)
now applies to the unchanged actual first root and (5). It yields

\[
q>\frac{29}{30}q_c,
\qquad \sqrt3hR+\frac{13}{3}A<0.
\tag{6}
\]

This is a conclusion about the original physical shear \(h\).
Since \(R>0\), \(A\ge0\), and
\(13/(3\sqrt3)>5/2\), it implies

\[
h<0,\qquad -hR>\frac52 A.
\tag{7}
\]

The rational comparison scales in the proof of (6) serve only to
exclude a scalar root inequality. Equation (7) is evaluated again at
the original physical scale. It is not a shear assertion about an
unproved closed trajectory.

## 4. The original whole-period completion cost is too large

All hypotheses of the
[small-shape physical-cost theorem](MIXED_SMALLER_SHORT_SMALL_SHAPE_COST_EXCLUSION.md)
are now established by (5)--(7) and the unchanged actual root. That
theorem proves

\[
C_{\rm period}>A_{\rm oct}.
\tag{8}
\]

For clarity, its essential direction is the following. The original
Casimir floor permits lowering
\(\kappa_{\rm actual}=\sqrt{12\Gamma_{\rm actual}}\) to
\(\kappa_0=40/27\) in a proved nondecreasing relaxed completion
score. The exact physical score initially decreases with scalar
scale by (7). Its critical-angle classification and the central
angle bound keep it on that decreasing branch up to the central
scale. This produces an explicit lower bound for the original
period cost. The shear cancellation and finite rational inequalities
in the cost theorem show that lower bound strictly exceeds (1).

Only the lower bound on the original covector is used. Neither its
competitive upper cap nor its physical realization is transported
to the central scalar point. The artificial continuation is permitted
even if it passes a scale cap applicable only to actual reverse
centres, because its derivative and angle estimates cover that whole
continuation independently.

Equation (8) contradicts competitiveness. This proves the claimed
exclusion for every actual smaller-short period in the stated class.

## 5. Boundaries and dependency boundary

The ratio, displacement and cap faces are closed in their respective
scalar sign theorems and have strict contradictions. The physical
cost theorem includes \(\delta=0\), \(A=0\), equal adjacent
turns and its endpoint values of \(x\) and \(\eta\). Positive
actual durations are preserved until the contradiction; zero-duration
scalar comparisons are used only through their continuous formulas.
No strict endpoint is discarded by passing to a limit.

The invoked six-variable note also records a historical executable
cover. Only its hand-derived actual interface in Sections 1--5 is
used here. Its interval exclusion, the old small-shape coefficient
tables and the older computational smaller-short theorem are not
premises. The independent scalar and actual-period audits accept this
assembly. Lean formalization and kernel verification remain separate.
