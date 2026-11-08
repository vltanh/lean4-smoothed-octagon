# Proof without computer assistance: finite acceptance ledger

**Correction after the lighter-proof request (8 November 2026).** The
acceptance recorded below is historical. The requested S1 replacements
and the outer S2.2 ratio replacement are now separately reviewed;
only the central S2.1 replacement remains open.
H-S and its dependent global hand conclusion therefore remain open
under the requested standard. Three reported interface gaps are repaired in
[the errata](../../docs/lighter-proofs/HS_ERRATA.md). The
[current replacement ledger](../../docs/lighter-proofs/README.md)
separates those repairs from the still-open polynomial signs. This
correction makes no change to the completed Lean exclusions outside H-S.

Date: 2026-11-08 UTC. **Authoritative accepted state.**

**The hand proof is complete under its explicitly listed external
classical geometric/PMP inputs.** H-F, both H-N successors, H-S and
H-A are closed. The [final theorem](HAND_COST_EQUALITY_THEOREM.md)
and [global dependency audit](HAND_GLOBAL_DEPENDENCY_AUDIT.md) have
separate final reviews. See the
[complete finite gate record](HAND_ONLY_COMPLETION_PLAN.md).

## Whole-period gates

| Gate | Accepted result and review |
|---|---|
| H-F | Closed by the [all-forward hand theorem](HAND_FORWARD_PERIOD_EXCLUSION.md) and [norm audit](HAND_FORWARD_NORM_AUDIT.md). Both historical forward covers have been replaced. |
| H-N | Closed for both actual successors by the [forward theorem](MIXED_NONSHORT_FORWARD_HAND_EXCLUSION.md) and [review](MIXED_NONSHORT_FORWARD_HAND_AUDIT.md), and the [reverse theorem](MIXED_NONSHORT_REVERSE_HAND_EXCLUSION.md) and [review](MIXED_NONSHORT_REVERSE_HAND_AUDIT.md). |
| H-S | Closed by the [hand period theorem](MIXED_SMALLER_SHORT_HAND_PERIOD_EXCLUSION.md), [period audit](MIXED_SMALLER_SHORT_HAND_PERIOD_AUDIT.md) and [separate scope audit](MIXED_SMALLER_SHORT_HAND_PERIOD_SCOPE_AUDIT.md). Every scalar input and actual-period boundary is covered. |
| H-A | Closed by the [global dependency audit](HAND_GLOBAL_DEPENDENCY_AUDIT.md), [finite-period review](HAND_FINITE_PERIOD_ASSEMBLY_AUDIT.md) and [inequality/equality review](HAND_GLOBAL_EQUALITY_FINAL_AUDIT.md). The unrestricted cost inequality and original-disk affine equality are accepted. |

These are uniform whole-period results. No growing word-length
catalogue, local six-window replacement or percentage completion
estimate is used.

## The actual smaller-short domain is now fully controlled

The [lower-ratio theorem](MIXED_SMALLER_SHORT_LOWER_RATIO_HAND_EXCLUSION.md)
and its [review](MIXED_SMALLER_SHORT_LOWER_RATIO_HAND_AUDIT.md) prove
\(x>2\). The [sharp upper-ratio theorem](MIXED_SMALLER_SHORT_SHARP_RATIO_HAND_EXCLUSION.md)
and [review](MIXED_SMALLER_SHORT_SHARP_RATIO_HAND_AUDIT.md) prove
\(x<13/6\). Neither assumes the final small-shape bounds.

On that actual interval the
[displacement theorem](MIXED_SMALLER_SHORT_DISPLACEMENT_HAND_EXCLUSION.md)
and [review](MIXED_SMALLER_SHORT_DISPLACEMENT_FACE_AUDIT.md) give
\(\delta=\beta/x-1<1/19\). The
[strong lower order](MIXED_SMALLER_SHORT_STRONG_ORDER.md) and
[extended upper order](MIXED_SMALLER_SHORT_SMALL_SHAPE_UPPER_ORDER.md)
then give
\[
\alpha=1+\eta\delta,\qquad13/5\le\eta\le3.
\]
When delta=0, both orders force alpha=1 and any eta in the interval
represents the same shape.

The [extended Casimir floor](MIXED_SMALLER_SHORT_EXTENDED_CASIMIR_FLOOR.md),
with its [new six-sign proof](MIXED_SMALLER_SHORT_EXTENDED_CASIMIR_DERIVATIVES.md)
and [independent review](MIXED_SMALLER_SHORT_EXTENDED_SHAPE_AUDIT.md),
proves
\[
\Gamma_{\rm actual}>1829/10000
\]
on the entire \([2,13/6]\) interval. This explicitly covers the
former gap beyond 15/7. The original common covector supplies
this lower bound; no competitive upper cap is transferred to a
scalar endpoint.

The [root-to-shear theorem](MIXED_SMALLER_SHORT_SMALL_SHAPE_ROOT_SHEAR.md)
and [review](MIXED_SMALLER_SHORT_SMALL_SHAPE_ROOT_SHEAR_AUDIT.md)
give \(h<0\) and \(-hR>5A/2\) at the original physical scale.
The [physical-cost theorem](MIXED_SMALLER_SHORT_SMALL_SHAPE_COST_EXCLUSION.md)
and [review](MIXED_SMALLER_SHORT_SMALL_SHAPE_COST_AUDIT.md)
therefore have all of their caller hypotheses and prove the strict
original-period contradiction \(C_{\rm period}>A_{\rm oct}\).

## Hand foundations and terminal result

The retained route obtains an actual free-initial-state PMP lift,
positive singular clearance and a finite vertex representation
before normalizing the same lift. Its measurable-edge argument
and finite guard count are analytic. It does not import the
later numerical finite bang-bang/basin theorem.

The [small-forward-minimum hand proof](SMALL_FORWARD_MINIMUM_HAND_PROOF.md)
supplies the shared minimum-structure prerequisite. The
[reverse-period theorem](GLOBAL_REVERSE_PERIOD_EXCLUSION.md) and
[two-switch reverse-run theorem](MIXED_GLOBAL_MINIMUM_STRUCTURE.md)
are uniform in length. At a mixed global reverse minimum, choosing
the smaller adjacent turn gives exactly the short or nonshort
alternatives, including ties and the twisted seam.

The [terminal hand count](HAND_TERMINAL_COVERAGE.md) uses the twist
congruence directly. Once every N>=6 period is excluded, it leaves
only 0120 and 01020. Their
[analytic terminal comparisons](SMALL_PERIOD_COST_EQUALITY_AUDIT.md)
give the unique four-piece octagon equality case and strict
five-piece cost excess. No terminal enumerator is required.

## Exact accepted conclusion

The complete hand chain yields
\[
C\ge\sqrt{12}\,
\frac{8-4\sqrt2-\log2}{2\sqrt2-1}
\]
for every trajectory in the original integral admissible class,
including measurable controls, and the corresponding density
bound for every centrally symmetric planar convex disk, with
equality exactly for affine images of the concrete smoothed octagon.

The proof uses the explicitly identified classical geometric,
packing-density and maximum-principle theorems. The original
equality disk remains the disk being classified throughout
the realization, rebase, state/frame uniqueness and affine transport.
All required hand exclusions and interfaces are accepted; no
mathematical gate in the stated hand route remains open.

## Proof standard and preserved baseline

Every invoked sign is an explicit analytic inequality or a finite
algebraic identity with a displayed sign argument. Symbolic and
numerical calculations are permitted for discovery and transcription
checks; executable covers and unexplained coefficient minima are
not hand-proof premises.

The [completed computational baseline](GLOBAL_COST_EQUALITY_ASSEMBLY.md),
[its audit](GLOBAL_COMPLETION_INDEPENDENT_AUDIT.md) and
[replay records](CERTIFICATE_REPLAY.md) remain intact as historical
validation. Their execution trust boundary is separate from the
hand route.

No Lean, Lake, typechecking or CI has been run in this completion.
Existing Lean sources and dependency pins remain untouched.
Internal mathematical review is distinct from external peer review
and Lean kernel verification.
