# Active proof map and reproducibility

**Entry point:** [HANDOFF.md](HANDOFF.md). This index gives the short reading path, not another task ledger.

## Read in this order

1. Geometric/PMP foundation: [actual realization](ADMISSIBLE_REALIZATION.md), [arbitrary-control reverse comparison](REVERSE_COMPARISON.md), [GLOBAL_PERIODIC_PMP](GLOBAL_PERIODIC_PMP.md), [singular clearance](SINGULAR_COST_BUDGET.md), [measurable-edge finiteness](MEASURABLE_EDGE_PMP_BOUND.md), [finite switch count](QUANTITATIVE_REGULAR_SWITCH_BOUND.md), and then [GLOBAL_NORMALITY](GLOBAL_NORMALITY.md). The normal lift supplies [ellipticity](MIXED_GLOBAL_COSTATE_ELLIPTIC.md), the [spectral cost–Casimir bound](GLOBAL_SPECTRAL_COST_CASIMIR.md), and the [endpoint defect test](GLOBAL_ENDPOINT_DEFECT_TEST.md).
2. Closed global cases: [R](GLOBAL_REVERSE_PERIOD_EXCLUSION.md), [M3](MIXED_GLOBAL_MINIMUM_STRUCTURE.md), [M1](MIXED_GLOBAL_SHORT_RUN_ANGLE_EXCLUSION.md) and [two-centre base](MIXED_GLOBAL_SHORT_RUN_PERIOD.md).
3. F closed: [uniform period exclusion](GLOBAL_FORWARD_PERIOD_EXCLUSION.md) and [independent completion audit](GLOBAL_FORWARD_CASIMIR_CERTIFICATE_AUDIT.md). Supporting results: [smallest forward margin](MIXED_GLOBAL_SMALL_FORWARD_MINIMUM.md), [minimum-factor budget](GLOBAL_STRUCTURE_FORWARD_MINIMUM_BUDGET.md), [size 61](GLOBAL_STRUCTURE_FORWARD_ANGLE_COUNT.md), [forward dual Hessian](GLOBAL_STRUCTURE_FORWARD_DUAL_HESSIAN.md), [minimum-system nonsingularity](GLOBAL_FORWARD_MINIMUM_NONSINGULAR.md), [circular corner](GLOBAL_STRUCTURE_FORWARD_CIRCLE_CORNER.md), [linear neighbor budget](GLOBAL_FORWARD_LINEAR_BUDGET.md), [neighbor contraction](GLOBAL_FORWARD_NEIGHBOR_CONTRACTION.md), and [centered system / broad circular exclusion](GLOBAL_FORWARD_CENTERED_SYSTEM.md).
4. M2: [smaller-short exclusion closed](MIXED_SMALLER_SHORT_PERIOD_EXCLUSION.md) with its [completion audit](MIXED_SMALLER_SHORT_CERTIFICATE_AUDIT.md); smaller-nonshort branch open. Supporting interfaces: [short-bridge cost/angle](MIXED_GENERAL_SHORT_DEFECT_INTERFACE.md), [short-side scalar domain](MIXED_SMALLER_SHORT_SIX_VARIABLE_REDUCTION.md), [nonshort next-switch alternative](MIXED_SMALLER_TURN_CONTINUATION.md), [interface audit](MIXED_MINIMUM_CONTINUATION_INTERFACE_AUDIT.md), and [radial completion bound](GLOBAL_RADIAL_COMPLETION_BOUND.md). Earlier results: [two-short-bridge exclusion](MIXED_GLOBAL_SHORT_BRIDGE_MINIMUM.md), [reverse scale](MIXED_REVERSE_CENTRE_SCALE_BOUND.md), [angle budget](MIXED_GLOBAL_REVERSE_ANGLE_DENSITY.md), [turn elimination](MIXED_GLOBAL_TURN_ELIMINATION.md), [augmented index](MIXED_GLOBAL_AUGMENTED_INDEX.md).

5. Final assembly, conditional on M2: [global cost and equality argument](GLOBAL_COST_EQUALITY_ASSEMBLY.md) and [completed terminal comparison/equality audit](SMALL_PERIOD_COST_EQUALITY_AUDIT.md), with 72 exact identities and complete terminal word coverage.

Companion _AUDIT.md files contain the independent internal checks. Reproducible exact Python/SymPy certificate scripts and coefficient CSV files are in **[explorations](../explorations/README.md)**. The scripts are supplementary identity/sign checks, not Lean or a proof that every PMP trajectory closes.

The [replay guide](CERTIFICATE_REPLAY.md) collects the arithmetic commands
and the acceptance conditions for every full domain cover. The
[final dependency review](GLOBAL_COMPLETION_INDEPENDENT_AUDIT.md)
specifies the external geometric and standard PMP inputs and the scope
of the arbitrary-competitor and original-disk equality conclusions.

**Historical vs active:** [legacy archive](legacy/INDEX.md) holds the old five-case numerical atlas, superseded reduction plan, disproved local-shortening proposal, many local windows and weaker quantitative bounds. Old file paths provide stable pointers; do not use their historical NEXT WORKER instructions.
