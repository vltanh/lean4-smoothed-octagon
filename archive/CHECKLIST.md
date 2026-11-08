# Historical hand-proof ledger

**Current correction (8 November 2026):** the checked boxes below are
the earlier acceptance record, not acceptance under the new polynomial
size and no-table requirements. The S1 table-dependent hand premise,
and consequently H-S and its dependent global hand conclusion under
that standard, remain open. Track the finite requested replacements in
[the new ledger](../docs/lighter-proofs/README.md), with the
[three explicit interface repairs](../docs/lighter-proofs/HS_ERRATA.md)
recorded separately. Existing kernel-checked exclusions are unchanged.

Date: 2026-11-08 UTC. **The hand proof is complete under the explicit
external classical geometric/PMP inputs.** Start with the
[final theorem](notes/HAND_COST_EQUALITY_THEOREM.md),
[status](notes/HAND_PROOF_STATUS.md), and
[complete acceptance record](notes/HAND_ONLY_COMPLETION_PLAN.md).

## Completed hand gates

- [x] **Foundations:** the original measurable-control comparison,
  all-control compact domain, actual twisted PMP lift, singular
  clearance, finite vertex representation, and same-lift normality.
  The [finite-period review](notes/HAND_FINITE_PERIOD_ASSEMBLY_AUDIT.md)
  checks the required order.
- [x] **H-F:** [all-forward hand exclusion](notes/HAND_FORWARD_PERIOD_EXCLUSION.md),
  with [norm review](notes/HAND_FORWARD_NORM_AUDIT.md).
- [x] **H-N, next switch forward:**
  [hand exclusion](notes/MIXED_NONSHORT_FORWARD_HAND_EXCLUSION.md)
  and [review](notes/MIXED_NONSHORT_FORWARD_HAND_AUDIT.md).
- [x] **H-N, next switch reverse:**
  [hand exclusion](notes/MIXED_NONSHORT_REVERSE_HAND_EXCLUSION.md)
  and [review](notes/MIXED_NONSHORT_REVERSE_HAND_AUDIT.md).
- [x] **H-S:** [complete smaller-short theorem](notes/MIXED_SMALLER_SHORT_HAND_PERIOD_EXCLUSION.md),
  [period review](notes/MIXED_SMALLER_SHORT_HAND_PERIOD_AUDIT.md), and
  [scope review](notes/MIXED_SMALLER_SHORT_HAND_PERIOD_SCOPE_AUDIT.md).
- [x] **Terminal count:** [direct twisted-label count](notes/HAND_TERMINAL_COVERAGE.md)
  leaves only \(0120\) and \(01020\); the
  [analytic comparisons](notes/SMALL_PERIOD_COST_EQUALITY_AUDIT.md)
  prove unique four-piece equality and strict five-piece excess.
- [x] **H-A:** [global theorem](notes/HAND_COST_EQUALITY_THEOREM.md),
  [dependency audit](notes/HAND_GLOBAL_DEPENDENCY_AUDIT.md), and
  [final inequality/equality review](notes/HAND_GLOBAL_EQUALITY_FINAL_AUDIT.md)
  cover arbitrary original measurable competitors and affine equality
  of the original disk.

## Completed smaller-short gates

| Gate | Accepted actual conclusion | Proof |
|---|---|---|
| S0 | \(x<12/5,\ D>0,\ E_L>0\) | [Large-ratio theorem](notes/MIXED_SMALLER_SHORT_LARGE_RATIO_HAND_EXCLUSION.md) and [positive pairing](notes/MIXED_SMALLER_SHORT_POSITIVE_DIAGONAL_PAIRING.md) |
| S1 | \(x>2\) | [Lower-ratio theorem](notes/MIXED_SMALLER_SHORT_LOWER_RATIO_HAND_EXCLUSION.md) |
| S2 | \(x<13/6\) | [Sharp upper-ratio theorem](notes/MIXED_SMALLER_SHORT_SHARP_RATIO_HAND_EXCLUSION.md) |
| S3 | \(0\le\delta<1/19\) | [Displacement theorem](notes/MIXED_SMALLER_SHORT_DISPLACEMENT_HAND_EXCLUSION.md) |
| S4 | \(\alpha\le1+3\delta,\ \Gamma_{\rm actual}>1829/10000\), including the strip beyond \(15/7\) | [Upper order](notes/MIXED_SMALLER_SHORT_SMALL_SHAPE_UPPER_ORDER.md), [extended floor](notes/MIXED_SMALLER_SHORT_EXTENDED_CASIMIR_FLOOR.md), [six derivative signs](notes/MIXED_SMALLER_SHORT_EXTENDED_CASIMIR_DERIVATIVES.md) |
| S5 | Actual root gives \(h<0,\ -hR>5A/2\) | [Root-to-shear theorem](notes/MIXED_SMALLER_SHORT_SMALL_SHAPE_ROOT_SHEAR.md) |
| S6 | Original full-period cost exceeds \(A_{\rm oct}\) | [Physical-cost theorem](notes/MIXED_SMALLER_SHORT_SMALL_SHAPE_COST_EXCLUSION.md) |
| S7 | Uniform actual-period H-S exclusion | [Hand period theorem](notes/MIXED_SMALLER_SHORT_HAND_PERIOD_EXCLUSION.md) |
| A1 | Complete global assembly | [Final theorem](notes/HAND_COST_EQUALITY_THEOREM.md) and [final reviews](notes/HAND_GLOBAL_DEPENDENCY_AUDIT.md) |

Separate reviews for every scalar and actual-period gate are linked in
[the acceptance record](notes/HAND_ONLY_COMPLETION_PLAN.md).
All gates are closed. The original common covector, first switches,
unequal positive durations, equal-turn choices, zero displacement,
twisted seam and one whole-period budget are retained.

Every indispensable sign is an explicit analytic inequality or
finite algebraic identity with an elementary sign argument. Symbolic
and numerical work may aid discovery and transcription; executable
covers and unexplained coefficient minima are not proof premises.
No Lean, Lake, typechecking or CI was run. Internal acceptance is
distinct from external peer review and kernel verification.

## Historical computational baseline

The remaining checklist records the earlier hand/computer-assisted
proof. Its arithmetic results and receipts are preserved, but its
executable exclusions are not premises of the hand route above.

### Baseline proof checkpoints

- [x] G1: actual twisted state/frame and costate interface, free initial state and required geometric/PMP inputs.
- [x] G2: normalized singular clearance \(D>10^{-11}\).
- [x] G3: direct measurable-edge finiteness, hence global minimizer \(N<10^{56}\).
- [x] Global normality and outgoing tie/actual switch rules.
- [x] R: exclude every entirely reverse minimizing period.
- [x] M3: every mixed reverse run has exactly two switches.
- [x] Sufficient M1: exclude every all-short mixed period, all multiplicities.
- [x] Uniform negative elliptic costate sector; sharpened spectral cost–Casimir inequality and exact endpoint continuation budget.
- [x] F narrowing: \(N\le61\), \(4/3<a_{\min}^2<20/11\), \(1<q_{\min}<7/4\); exact three-arc nonsingularity and positive-window circular-corner exclusion.
- [x] F minimum refinement: whole-period linear neighbor budget, exact uniform neighbor contraction `1 <= z,w < 5/4`, and a broad hand exclusion `3-U+(z-1)+(w-1) <= 3/20`; centered multiplier/Casimir identities independently checked.
- [x] M2 narrowing: global minimum at a reverse centre adjacent to a nonshort forward run; all reverse centres \(a^2<12/17\); reverse angle and constrained-index density bounds.

- [x] M2 continuation interfaces: exact two-turn bridge cost/angle and compact six-variable reduction; next-actual-switch alternative on the nonshort side; radial completion penalty. Both nonshort successors and the exhaustive whole-period assembly are independently accepted.
- [x] M2 smaller-short side: complete directed cover of the fixed six-variable necessary domain, 107,977 nodes and 53,989 excluded leaves, zero unresolved boxes; independent source/interface and completion audit.
- [x] Terminal cost/equality audit: arbitrary four-piece parameters, mixed five-piece strictness, complete terminal word coverage and original-disk equality transport independently reviewed; 72 exact checks replayed. The final global cost/equality assembly is complete and independently accepted.
- [x] M2 nonshort boundary: regular five-variable charts, exact cancelled coefficients, and a uniform hand exclusion of `epsilon<=1/32`. A new scalar comparison reduces the boundary domain to two four-variable charts; the reverse-next exclusion is independently reviewed and replayed.

### Historical completed finite proof gates

- [x] **F1 / F2:** uniform pure-forward exclusion and independent completion audit. The whole-period rational cover has 20,999 nodes and zero unresolved boxes; the all-forward length catalogue is retired.
- [x] **M2.0:** the smaller-turn **short** side is excluded by a complete audited 107,977-node directed cover; the **nonshort** epsilon corner `0<=epsilon<=1/32` is excluded by hand. The nonshort coefficient formulas and caller have a source/domain audit.
- [x] **M2.1-F:** the [forward endpoint theorem](notes/MIXED_NONSHORT_FORWARD_BOUNDARY_EXCLUSION.md), [common low-a theorem](notes/MIXED_NONSHORT_LOW_A_BOUNDARY_EXCLUSION.md), and their independent audits close this branch. The 74,772-node low-a cover and both endpoint covers (37,940 and 60,976 nodes) have complete fresh independent replays, zero pending/unresolved boxes, and accepted source/interface reviews. Concavity gives an exhaustive endpoint alternative for the actual Casimir cap.
- [x] **M2.1-R:** the [reverse boundary theorem](notes/MIXED_NONSHORT_REVERSE_BOUNDARY_EXCLUSION.md) excludes the next reverse switch uniformly. Its two-root cover has 106,134 nodes and 53,068 leaves; a separate mathematical/source review and fresh replay accept it, with zero pending or unresolved boxes.
- [x] **M2.1-V:** all four boundary covers have independent source/domain reviews and fresh complete replays. Their original/replay logs, frozen sources, clean arithmetic flags, empty frontiers and exact two-root/leaf identities are recorded. `mixed_nonshort_boundary_records_verify.py` verifies every published receipt and hash. The old incomplete three-root forests are not proof premises.
- [x] **M2.2:** the [uniform M2 theorem](notes/MIXED_GLOBAL_NONSHORT_PERIOD_EXCLUSION.md) and [independent whole-period audit](notes/MIXED_GLOBAL_NONSHORT_PERIOD_AUDIT.md) close the entire remaining class for `N>=6`. The review checks smaller-turn and actual-successor exhaustiveness, the same covector, arbitrary unequal factors/run lengths, weak ties, both short-side diagonal signs, proper-subperiod cost accounting, zero-duration/edge inputs, twisted seam and rank defects.
- [x] **G4:** the [global cost/equality theorem](notes/GLOBAL_COST_EQUALITY_ASSEMBLY.md) combines all five whole-period exclusions with the audited through-five comparison. It proves the sharp cost inequality for arbitrary admissible competitors and the affine equality classification of the original minimizing disk.
- [x] **G5:** the [final independent dependency audit](notes/GLOBAL_COMPLETION_INDEPENDENT_AUDIT.md) accepts the complete chain, external inputs, exact replay records, boundary cases and theorem scope. Lean/kernel verification remains deferred and is not claimed.

**Historical baseline status:** R, M1, M2, M3, F, the global sharp cost inequality and affine uniqueness are closed at hand/computer-assisted level, with independent internal acceptance and the explicitly declared external inputs and arithmetic trust boundary. The old *local* L3 shortening lemma is false and is in [legacy](notes/legacy/INDEX.md). The \(N\le61\) theorem is not a plan for length-by-length enumeration. No Lean, Lake or CI.
