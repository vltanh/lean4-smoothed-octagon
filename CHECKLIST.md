# Active proof ledger — five finite whole-period cases

**Only authoritative next-step plan: [docs/HANDOFF.md](docs/HANDOFF.md).** The long earlier progress ledgers and abandoned targets are archived, not silently deleted.

## Active goal: proof without computer assistance

The user has requested a hand proof beyond the completed computational
baseline below. [HAND_PROOF_STATUS](docs/HAND_PROOF_STATUS.md) is the finite
replacement ledger: H-F is now closed by hand; H-S, H-N and the final
dependency audit H-A remain open. The [new hand refinements](docs/HAND_PROOF_REFINEMENTS.md) strengthen
the Casimir cap, reverse-centre scale and forward successor norm. The
closed computer-assisted gates below do not close these new obligations.

- [x] Hand replacement of the nonshort small-parameter corner:
  [strict duration-ratio gap](docs/MIXED_NONSHORT_UPPER_ENVELOPE_GAP.md),
  independently reviewed, gives `(d-a)/(a+c)>1/10`.
- [x] Accepted conditional [forward reductions](docs/HAND_FORWARD_LEMMAS.md)
  and [short-side root envelope](docs/MIXED_SMALLER_SHORT_OUTER_ENVELOPE.md).
- [x] The shared hard small-forward-minimum face has a complete
  [integral/cubic hand proof](docs/SMALL_FORWARD_MINIMUM_HAND_PROOF.md).
- [x] Both forward neighbor ratios are below 4/3 by the
  [integral proof](docs/HAND_FORWARD_NEIGHBOR_INTEGRAL.md) and
  [asymmetric completion](docs/HAND_FORWARD_ASYMMETRIC_NEIGHBOR_BOUND.md).
- [x] The smaller-nonshort case satisfies
  [t<2/5](docs/MIXED_NONSHORT_HIGH_T_HAND_EXCLUSION.md) and
  [a<4/5](docs/MIXED_NONSHORT_CONDITIONAL_SCALE_BOUND.md) by hand.
- [x] The [short opposite-norm floor](docs/MIXED_SMALLER_SHORT_NONPOSITIVE_FLOOR.md)
  is redundant by hand; the root comparison retains three other faces.
- [x] The [reverse order lower face](docs/MIXED_NONSHORT_REVERSE_ORDER_FACE_REDUCTION.md)
  is excluded by hand, including ties; the unit face is also now closed.
- [x] A reviewed [fixed outer-norm deformation](docs/MIXED_SMALLER_SHORT_OUTER_FLOOR_DEFORMATION.md)
  further reduces the nonnegative-pairing short face, with its remaining
  endpoint signs explicit.
- [x] The [uniform all-forward hand theorem](docs/HAND_FORWARD_PERIOD_EXCLUSION.md),
  with [independent norm audit](docs/HAND_FORWARD_NORM_AUDIT.md), replaces
  both forward covers. The actual norm bounds imply a strict Casimir
  contradiction.
- [x] Both [short stationary slacks](docs/MIXED_SMALLER_SHORT_SLACK_RETENTION.md)
  persist along the first root comparison; all three terminal faces
  retain these actual necessary inequalities.
- [x] The [common low-scale domain](docs/MIXED_NONSHORT_LOW_SCALE_DOMAIN_REDUCTION.md)
  has t<7/20 and x>3/13. The [forward scale-Casimir comparison](docs/MIXED_NONSHORT_FORWARD_SHAPE_CASIMIR.md)
  retains the stronger next-norm floor through a proved endpoint reduction.
- [x] The [unit-shape hand theorem](docs/MIXED_NONSHORT_UNIT_SHAPE_HAND_EXCLUSION.md)
  excludes the reverse k_min=1 face and the common low-scale d<=c part,
  with a [dedicated independent audit](docs/MIXED_NONSHORT_UNIT_SHAPE_HAND_AUDIT.md).
- [ ] Full short-side exclusion, both nonshort successors, and the final
  hand-only assembly still need proofs.

## Baseline proof checkpoints

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

## Completed finite proof gates

- [x] **F1 / F2:** uniform pure-forward exclusion and independent completion audit. The whole-period rational cover has 20,999 nodes and zero unresolved boxes; the all-forward length catalogue is retired.
- [x] **M2.0:** the smaller-turn **short** side is excluded by a complete audited 107,977-node directed cover; the **nonshort** epsilon corner `0<=epsilon<=1/32` is excluded by hand. The nonshort coefficient formulas and caller have a source/domain audit.
- [x] **M2.1-F:** the [forward endpoint theorem](docs/MIXED_NONSHORT_FORWARD_BOUNDARY_EXCLUSION.md), [common low-a theorem](docs/MIXED_NONSHORT_LOW_A_BOUNDARY_EXCLUSION.md), and their independent audits close this branch. The 74,772-node low-a cover and both endpoint covers (37,940 and 60,976 nodes) have complete fresh independent replays, zero pending/unresolved boxes, and accepted source/interface reviews. Concavity gives an exhaustive endpoint alternative for the actual Casimir cap.
- [x] **M2.1-R:** the [reverse boundary theorem](docs/MIXED_NONSHORT_REVERSE_BOUNDARY_EXCLUSION.md) excludes the next reverse switch uniformly. Its two-root cover has 106,134 nodes and 53,068 leaves; a separate mathematical/source review and fresh replay accept it, with zero pending or unresolved boxes.
- [x] **M2.1-V:** all four boundary covers have independent source/domain reviews and fresh complete replays. Their original/replay logs, frozen sources, clean arithmetic flags, empty frontiers and exact two-root/leaf identities are recorded. `mixed_nonshort_boundary_records_verify.py` verifies every published receipt and hash. The old incomplete three-root forests are not proof premises.
- [x] **M2.2:** the [uniform M2 theorem](docs/MIXED_GLOBAL_NONSHORT_PERIOD_EXCLUSION.md) and [independent whole-period audit](docs/MIXED_GLOBAL_NONSHORT_PERIOD_AUDIT.md) close the entire remaining class for `N>=6`. The review checks smaller-turn and actual-successor exhaustiveness, the same covector, arbitrary unequal factors/run lengths, weak ties, both short-side diagonal signs, proper-subperiod cost accounting, zero-duration/edge inputs, twisted seam and rank defects.
- [x] **G4:** the [global cost/equality theorem](docs/GLOBAL_COST_EQUALITY_ASSEMBLY.md) combines all five whole-period exclusions with the audited through-five comparison. It proves the sharp cost inequality for arbitrary admissible competitors and the affine equality classification of the original minimizing disk.
- [x] **G5:** the [final independent dependency audit](docs/GLOBAL_COMPLETION_INDEPENDENT_AUDIT.md) accepts the complete chain, external inputs, exact replay records, boundary cases and theorem scope. Lean/kernel verification remains deferred and is not claimed.

**Current status:** R, M1, M2, M3, F, the global sharp cost inequality and affine uniqueness are closed at hand/computer-assisted level, with independent internal acceptance and the explicitly declared external inputs and arithmetic trust boundary. The old *local* L3 shortening lemma is false and is in [legacy](docs/legacy/INDEX.md). The \(N\le61\) theorem is not a plan for length-by-length enumeration. No Lean, Lake or CI.
