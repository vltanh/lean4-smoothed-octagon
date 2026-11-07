# Current theorem source map

Read the **[authoritative handoff](docs/HANDOFF.md)** before following any historical cross-reference. The pre-reorganization long source map is preserved in [legacy snapshots](docs/legacy/snapshots/SOURCE_MAP.md).

| Scope | Active sources |
| --- | --- |
| Geometric/control correspondence, twisted PMP | [GLOBAL_PERIODIC_PMP](docs/GLOBAL_PERIODIC_PMP.md), [MINIMIZER_WINDOW_PMP](docs/MINIMIZER_WINDOW_PMP.md), [MINIMIZER_WINDOW_AUDIT](docs/MINIMIZER_WINDOW_AUDIT.md) |
| Global sign coverage | [BOUNDED_REDUCTION](docs/BOUNDED_REDUCTION.md), [FORWARD_ALTERNATION_EXCLUSION](docs/FORWARD_ALTERNATION_EXCLUSION.md) |
| G2/G3 numerical reduction | [SINGULAR_COST_BUDGET](docs/SINGULAR_COST_BUDGET.md), [MEASURABLE_EDGE_PMP_BOUND](docs/MEASURABLE_EDGE_PMP_BOUND.md), [QUANTITATIVE_REGULAR_SWITCH_BOUND](docs/QUANTITATIVE_REGULAR_SWITCH_BOUND.md) |
| Normality/switch rules | [GLOBAL_NORMALITY](docs/GLOBAL_NORMALITY.md), [NORMAL_TIE_BRANCHING](docs/NORMAL_TIE_BRANCHING.md), [NORMAL_SWITCH_RIGIDITY](docs/NORMAL_SWITCH_RIGIDITY.md) |
| Costate and whole-period Casimir | [MIXED_GLOBAL_COSTATE_ELLIPTIC](docs/MIXED_GLOBAL_COSTATE_ELLIPTIC.md), [GLOBAL_COST_CASIMIR](docs/GLOBAL_COST_CASIMIR.md) |
| R closed | [GLOBAL_REVERSE_PERIOD_EXCLUSION](docs/GLOBAL_REVERSE_PERIOD_EXCLUSION.md) |
| M3 closed | [MIXED_GLOBAL_MINIMUM_STRUCTURE](docs/MIXED_GLOBAL_MINIMUM_STRUCTURE.md) |
| Sufficient M1 closed | [MIXED_GLOBAL_SHORT_RUN_PERIOD](docs/MIXED_GLOBAL_SHORT_RUN_PERIOD.md), [MIXED_GLOBAL_SHORT_RUN_ANGLE_EXCLUSION](docs/MIXED_GLOBAL_SHORT_RUN_ANGLE_EXCLUSION.md) |
| F open | [MIXED_GLOBAL_SMALL_FORWARD_MINIMUM](docs/MIXED_GLOBAL_SMALL_FORWARD_MINIMUM.md), [GLOBAL_STRUCTURE_FORWARD_MINIMUM_BUDGET](docs/GLOBAL_STRUCTURE_FORWARD_MINIMUM_BUDGET.md), [GLOBAL_STRUCTURE_FORWARD_ANGLE_COUNT](docs/GLOBAL_STRUCTURE_FORWARD_ANGLE_COUNT.md), [GLOBAL_STRUCTURE_FORWARD_ELLIPTIC](docs/GLOBAL_STRUCTURE_FORWARD_ELLIPTIC.md) |
| M2 open | [MIXED_GLOBAL_SHORT_BRIDGE_MINIMUM](docs/MIXED_GLOBAL_SHORT_BRIDGE_MINIMUM.md), [MIXED_REVERSE_CENTRE_SCALE_BOUND](docs/MIXED_REVERSE_CENTRE_SCALE_BOUND.md), [MIXED_GLOBAL_REVERSE_ANGLE_DENSITY](docs/MIXED_GLOBAL_REVERSE_ANGLE_DENSITY.md), [MIXED_GLOBAL_TURN_ELIMINATION](docs/MIXED_GLOBAL_TURN_ELIMINATION.md) |
| Actual constrained cost Hessian | [MIXED_GLOBAL_AUGMENTED_INDEX](docs/MIXED_GLOBAL_AUGMENTED_INDEX.md), [MIXED_GLOBAL_SCALAR_DUAL](docs/MIXED_GLOBAL_SCALAR_DUAL.md) |

Companion _AUDIT notes and exact certificate scripts remain available. Superseded plans, local comparisons, rejected shortcuts and weaker reduction estimates are [legacy](docs/legacy/INDEX.md); their old paths remain short pointers to preserve inbound links. Lean sources and scripts are unchanged.

## Current cost and continuation refinement

[GLOBAL_SPECTRAL_COST_CASIMIR](docs/GLOBAL_SPECTRAL_COST_CASIMIR.md) strengthens the whole-period bound and classifies equality. [GLOBAL_ENDPOINT_DEFECT_TEST](docs/GLOBAL_ENDPOINT_DEFECT_TEST.md) removes the conjugator from the exact window-angle calculation. These are internally audited hand results; the F/M2 exclusions remain open.

## Forward minimum refinement

[GLOBAL_FORWARD_LINEAR_BUDGET](docs/GLOBAL_FORWARD_LINEAR_BUDGET.md), [GLOBAL_FORWARD_NEIGHBOR_CONTRACTION](docs/GLOBAL_FORWARD_NEIGHBOR_CONTRACTION.md), and [GLOBAL_FORWARD_CENTERED_SYSTEM](docs/GLOBAL_FORWARD_CENTERED_SYSTEM.md) reduce the remaining pure-forward minimum domain. The linear polynomial certificate, the 8,183-node exact rational neighbor certificate, and the centered identities have independent internal checks. The complementary Casimir exclusion is not yet recorded as complete.
