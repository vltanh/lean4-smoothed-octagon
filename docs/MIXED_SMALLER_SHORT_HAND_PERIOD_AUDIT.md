# Independent review of the actual smaller-short hand exclusion

Date: 2026-11-08 UTC. **Accepted actual-period interface for S7.**
This review independently checks the implication in
[MIXED_SMALLER_SHORT_HAND_PERIOD_EXCLUSION](MIXED_SMALLER_SHORT_HAND_PERIOD_EXCLUSION.md),
using the completed scalar theorems and their separate reviews.
It accepts the uniform H-S conclusion, including its endpoint and
whole-period scope. It does not substitute the older computational
smaller-short exclusion for any hand input.

The central low-ratio proof has a separate review by another worker in
[LOW_RATIO_CENTRAL_HAND_AUDIT](MIXED_SMALLER_SHORT_LOW_RATIO_CENTRAL_HAND_AUDIT.md).
The outer low-ratio signs, sharp corrected comparison and extended
Casimir signs have likewise been read separately before this interface
acceptance. This review concentrates on how the actual object reaches
those scalar statements and returns to an original-period contradiction.

## 1. The initial object and orientation are the required ones

The theorem starts with a finite positive normal minimizing period,
with at least six pieces, the geometric eligibility inherited from the
retained minimizer, and cost at most

\[
A_{\rm oct}=\sqrt{12}\,
 \frac{8-4\sqrt2-\log2}{2\sqrt2-1}.
\]

The chosen centre is a global minimum in its actual finite cyclic
active-margin sequence, and the chosen adjacent turn is the smaller
one. The statement does not require that minimum or turn to be unique.
When the two adjacent turns are equal, either is an admissible choice.
The hypothesis defining this branch is that the chosen side is a short
forward run; no assertion about the other side's run length is needed.

The reflection together with time reversal is the actual transformation
of Sections 1--3 of
[MIXED_GLOBAL_MINIMUM_STRUCTURE](MIXED_GLOBAL_MINIMUM_STRUCTURE.md).
It sends the state and both matrix costates to the displayed reflected
and reversed expressions, keeps the physical normal multiplier's sign,
and preserves all simplex Hamiltonian inequalities. Its endpoint check
retains the state, frame and both twisted cotangent endpoints. Thus
orienting the chosen side as incoming is legitimate. Merely reversing a
word, without that transformation, would not supply these facts.

The same-covector formulas in Sections 1--5 of
[SIX_VARIABLE_REDUCTION](MIXED_SMALLER_SHORT_SIX_VARIABLE_REDUCTION.md)
then give the two equal secants, positive factors, actual incident norm
bounds, original outer descending root, and the physical two-turn cost.
The complete period is extended through its genuine twist when a window
crosses the seam. No local endpoint-rank solve supplies a replacement
normal covector.

The scale cap at the preceding outer reverse centre is valid even if
that centre is not the global minimum. This precise issue is resolved
by [REVERSE_CENTRE_SCALE_SCOPE_AUDIT](HAND_REVERSE_CENTRE_SCALE_SCOPE_AUDIT.md):
its \(q<1/7\) result applies at every actual competitive reverse-run
centre, using the same conserved whole-period Casimir.

## 2. The domain sequence covers every actual point

The hand statements are applied in the following logical order.

| Input | Actual conclusion used next | Scope check |
| --- | --- | --- |
| S0, large-ratio and positive-pairing theorems | \(x<12/5\), \(D>0\), \(E_L>0\) | These are actual conclusions before the sharper scalar comparisons. |
| S1, lower-ratio theorem | \(x>2\) | Its corrected comparison uses only the original cap, broad equal-secant orders and S0. It does not assume a small displacement or S2. |
| S2, sharp upper-ratio theorem | \(x<13/6\) | Its variable-floor argument is independent of S1 and excludes both scale faces. |
| S3, displacement theorem | \(0\le\delta<1/19\) | Applied after S1 and S2 provide its entire ratio interval. |
| S4, extended order and Casimir theorems | \(\alpha\le1+3\delta\), \(\Gamma_{\rm actual}>1829/10000\) | Both cover \([2,13/6]\); the older endpoint \(15/7\) is not silently enlarged. |

The sources are the
[lower-ratio theorem](MIXED_SMALLER_SHORT_LOWER_RATIO_HAND_EXCLUSION.md),
[sharp upper-ratio theorem](MIXED_SMALLER_SHORT_SHARP_RATIO_HAND_EXCLUSION.md),
[displacement theorem](MIXED_SMALLER_SHORT_DISPLACEMENT_HAND_EXCLUSION.md),
[extended upper order](MIXED_SMALLER_SHORT_SMALL_SHAPE_UPPER_ORDER.md), and
[extended Casimir floor](MIXED_SMALLER_SHORT_EXTENDED_CASIMIR_FLOOR.md).

The strong lower order gives

\[
\alpha\ge1+
 \left(1+\frac{4x(x+1)}{7x+1}\right)\delta
 \ge1+\frac{13}{5}\delta.
\]

The last rational coefficient increases with x, its derivative having
positive numerator \(4(7x^2+2x+1)\), and its value at two is \(13/5\).
For \(\delta>0\), define \(\eta=(\alpha-1)/\delta\). For
\(\delta=0\), the upper order and \(\alpha\ge1\) force \(\alpha=1\),
and any \(\eta\in[13/5,3]\) gives the same shape. There is no division
by zero or loss of the zero-displacement boundary. Therefore every
actual retained point belongs to

\[
2<x<13/6,\quad0\le\delta<1/19,\quad
\alpha=1+\eta\delta,\quad13/5\le\eta\le3,
\quad\Gamma_{\rm actual}>1829/10000.
\]

No displacement or Casimir conclusion is used to prove its own
hypothesis. In particular the conditional S3, S5 and S6 theorems are
invoked only after their actual-domain restrictions have been supplied.

## 3. The corrected comparisons preserve the required direction

In S1 the original common covector alone satisfies the competitive
upper bound \(\Gamma_{\rm actual}<9193/50000\). The sharp
corrected-cap theorem instead constructs a scalar lower bound

\[
\Gamma_{\rm actual}\ge\Gamma_*-\frac7{96}R_\tau^*.
\]

At fixed normalized duration this corrected scalar decreases toward a
scale face. If the path first reaches \(\tau=2\), its separately
proved tau-two derivative continues the same decreasing bound. Its two
terminal scale faces are exactly \(q=q_c\le1/7\) and
\(q=1/7\le q_c\). The incoming norm and actual shape are fixed.
The terminal duration belongs to \([2,T]\), with \(T\ge7/3\).

The duration tangent estimate covers either sign of the comparison
\(w-3/4\). The central and outer sign theorems make the corrected
lower bound strictly exceed the original upper cap. They never assert
that the artificial comparison norm has a physical outgoing floor or
that the altered scale is a closed period.

The same distinction is maintained by S4. Its corrected scalar is a
lower bound for the original Casimir, even when the comparison is
continued past a cap applicable only to actual reverse centres.
The extended derivative proof covers that continuation. The conclusion
\(\Gamma_{\rm actual}>1829/10000\) is therefore available at the
original physical point for the cost argument; it is not a lower cap
assigned to an artificial covector.

## 4. The actual root supplies the physical shear threshold

On the common domain, the
[root-to-shear theorem](MIXED_SMALLER_SHORT_SMALL_SHAPE_ROOT_SHEAR.md)
uses the original first descending root to prove

\[
q>\frac{29}{30}q_c,\qquad
\sqrt3\,hR+\frac{13}{3}A<0,
\quad R=\frac{x-1}{x+1}>0,
\quad A=\frac{U_1}{U_2}-1\ge0.
\]

Here h is the exact physical shear of the original two-turn endpoint
matrix. The bound on q is an actual-root conclusion. The final shear
identity is evaluated at that same q; no root is asserted at the
rational comparison value \(29q_c/30\).

Since \(13/(3\sqrt3)>5/2\), the strict shear inequality gives
\(h<0\) and \(-hR>5A/2\). At A=0 it directly gives \(h<0\),
and hence the same strict latter inequality. No division by A is used.

## 5. The physical cost remains the original one

The [physical defect interface](MIXED_GENERAL_SHORT_DEFECT_INTERFACE.md)
uses both equal secants to obtain the exact cost of the two charged
positive arcs. For N at least six these arcs form a proper subperiod.
The complementary period is charged once by the global completion
inequality. A longer display of PMP equations through the seam does
not enlarge the available physical cost budget.

The [physical-cost theorem](MIXED_SMALLER_SHORT_SMALL_SHAPE_COST_EXCLUSION.md)
first lowers \(\kappa_{\rm actual}=\sqrt{12\Gamma_{\rm actual}}\) to
\(\kappa_0=40/27\). Its exact arithmetic is

\[
12\frac{1829}{10000}-\left(\frac{40}{27}\right)^2
 =\frac{23}{1822500}>0.
\]

The direction is supplied by the nested angle disks in Section 5 of
[ROOT_AND_ANGLE_REDUCTION](MIXED_SMALLER_SHORT_ROOT_AND_ANGLE_REDUCTION.md):
the relaxed score

\[
C_{\rm br}+(\kappa+3/2)
 \max\{0,\pi/3-\Theta(3u/[2\kappa U_1])\}
\]

is nondecreasing in kappa with the original shape, incoming norm and
physical bridge fixed. Thus lowering kappa gives a lower bound for the
original period cost, as required.

At this fixed kappa, the original shear threshold makes the score
strictly decrease initially as scalar scale increases. Extending all the
way to the central cap is separately justified: the exact critical-angle
classification in [SHEAR_COST_REDUCTION](MIXED_SMALLER_SHORT_SHEAR_COST_REDUCTION.md)
has only the two angles \(|\theta_1-\theta_2|\) and
\(\theta_1+\theta_2\), and the independent central shape bound gives
\(\omega_c<13/175<5/48\le\theta_1\). The scale angle increases,
starts on the decreasing branch, and cannot meet the upper critical
angle. Clipping is absent because the fixed lower-row angle and the
maximum scale angle have sum less than \(\pi/3\). The A=0 negative
shear branch has its explicit continuous formula.

This continuation does not rely on an actual-only outer scale cap
remaining true after it has been crossed. The initial derivative uses
that cap at the actual point; the rest uses the exact critical-angle
classification and bounds valid up to central scale. The initial
same-secant physical cost formula then provides a scalar lower bound;
no continued physical period is asserted.

Finally the cost theorem cancels the leading shear term before bounding
the angle denominator. It replaces u by a lower value only in its final
explicit scalar expression, after proving that expression increases
with u. Its two eta endpoints and displacement concavity bound cover the
whole common closed domain. The resulting strict cost excess applies to
\(C_{\rm period}\) of the original object. It contradicts the original
competitive budget, completing H-S.

## 6. Boundaries, dependencies and acceptance

The scalar ratio and displacement equality faces are included with
strict signs. The original period retains positive durations and genuine
first switches throughout the deduction. Zero-duration scalar endpoints
are used only through the stated continuous formulas. Repeated minima,
equal adjacent turns, \(\delta=0\), A=0, unequal factors and successor
windows through the twisted seam all remain covered.

The actual interface is taken from Sections 1--5 of the six-variable
note. Its later interval certificate is not used. The historical
short-bridge residual coefficient tables are unnecessary: where a
secant comparison from the short-bridge continuation is used, only its
equal-secant existence and elementary norm derivative are inputs.
The old scalar covers, finite forest records and executable tests are
not premises of S7. The new finite polynomial signs are supplied by
explicit identities, complete lower polynomials or displayed product
majorants with elementary signs.

This review finds no additional actual-period hypothesis, uncharged cost,
unpreserved multiplier or omitted equality branch. It accepts the S7
implication and its H-S scope. This is an internal mathematical review;
external peer review and Lean kernel verification are not claimed.
