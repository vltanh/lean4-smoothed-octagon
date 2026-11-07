# Active proof ledger — five finite whole-period cases

**Only authoritative next-step plan: [docs/HANDOFF.md](docs/HANDOFF.md).** The long earlier progress ledgers and abandoned targets are archived, not silently deleted.

## Completed hand-proof checkpoints

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

- [x] M2 continuation interfaces: exact two-turn bridge cost/angle and compact six-variable reduction; next-actual-switch alternative on the nonshort side; radial completion penalty. Necessary-condition interfaces audited; the nonshort exclusion remains open.
- [x] M2 smaller-short side: complete directed cover of the fixed six-variable necessary domain, 107,977 nodes and 53,989 excluded leaves, zero unresolved boxes; independent source/interface and completion audit.
- [x] Terminal cost/equality audit: arbitrary four-piece parameters, mixed five-piece strictness, complete terminal word coverage and original-disk equality transport independently reviewed; 72 exact checks replayed. The global assembly remains conditional on M2.
- [x] M2 nonshort boundary: regular five-variable charts, exact cancelled coefficients, and a uniform hand exclusion of `epsilon<=1/32`. A new scalar comparison reduces the boundary domain to two four-variable charts; the reverse-next exclusion is independently reviewed and replayed.

## Remaining finite proof gates (the only live checklist)

- [x] **F1 / F2:** uniform pure-forward exclusion and independent completion audit. The whole-period rational cover has 20,999 nodes and zero unresolved boxes; the all-forward length catalogue is retired.
- [x] **M2.0:** the smaller-turn **short** side is excluded by a complete audited 107,977-node directed cover; the **nonshort** epsilon corner `0<=epsilon<=1/32` is excluded by hand. The nonshort coefficient formulas and caller have a source/domain audit.
- [ ] **M2.1-F:** finish the independent acceptance of the [forward endpoint reduction](docs/MIXED_NONSHORT_FORWARD_BOUNDARY_REDUCTION.md), common low-a theorem and both complete endpoint covers. The concavity argument preserves the actual Casimir cap through an exhaustive endpoint alternative.
- [x] **M2.1-R:** the [reverse boundary theorem](docs/MIXED_NONSHORT_REVERSE_BOUNDARY_EXCLUSION.md) excludes the next reverse switch uniformly. Its two-root cover has 106,134 nodes and 53,068 leaves; a separate mathematical/source review and fresh replay accept it, with zero pending or unresolved boxes.
- [ ] **M2.1-V:** independently verify every full root-cover execution record used by the boundary reduction. Reverse is accepted with `106134=2*53068-2`; common low-a and forward endpoint acceptance remain to be recorded. Frozen sources, clean arithmetic flags, empty frontier and exact root/leaf accounting are required. The old incomplete three-root forests are not proof premises.
- [ ] **M2.2:** hand-audit the exhaustiveness of the two actual next switches and the same covector, arbitrary unequal factors, all nonshort run lengths, weak ties, diagonal signs, zero-duration/edge limits, twisted seam and any remaining rank issue; then close the **entire** M2 period class.
- [ ] **G4:** discharge the conditional [global cost/equality assembly](docs/GLOBAL_COST_EQUALITY_ASSEMBLY.md) using all five whole-period cases and the already reviewed through-five comparison; prove the sharp inequality and original-disk affine equality.
- [ ] **G5:** independently audit the complete dependency chain, external inputs, exact replay records, mathematical boundary cases and final theorem scope. Lean/kernel verification stays **deferred**, not falsely marked complete.

**Current status:** R, M1, M3 and F closed at hand/exact-proof level; M2, global cost inequality and affine uniqueness open. The old *local* L3 shortening lemma is false and is in [legacy](docs/legacy/INDEX.md). The \(N\le61\) theorem is not a plan for length-by-length enumeration. No Lean, Lake or CI.
