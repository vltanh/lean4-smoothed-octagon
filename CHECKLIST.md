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

## Remaining finite proof gates

- [x] **F1: uniform pure-forward exclusion.** The same-lift minimum equations, exterior floors and global cost/Casimir budget exclude every F period with \(N\ge6\), arbitrary unequal factors; the exact complementary cover has 20,999 nodes and no unresolved boxes.
- [x] **F2: F closure audit.** Independent internal review verifies the actual-lift normalization, exterior switches, whole-period budget, seam, weak ties, boundary cover, positive-window nondegeneracy, and exact rational verifier. See [the closure](docs/GLOBAL_FORWARD_PERIOD_EXCLUSION.md) and [audit](docs/GLOBAL_FORWARD_CASIMIR_CERTIFICATE_AUDIT.md).
- [ ] **M2.1: long-run minimum obstruction.** The smaller-short side is excluded. On the smaller-nonshort side, exclude both next-actual-switch alternatives in the finite scalar continuation model.
- [ ] **M2.2: M2 closure audit.** Cover arbitrary unequal margins, all nonshort run lengths, diagonal signs, degeneracies, twisted seam and rank limits. Mark M2 closed only then.
- [ ] **G4: sharp global assembly.** Combine the five sufficient exclusions to obtain \(N\le5\), apply the retained through-five comparison, and prove unrestricted affine equality rigidity.
- [ ] **G5: final mathematical dependency audit.** Verify inputs, complete exact checks and edge/equality cases. Record Lean/kernel validation as deferred.

**Current status:** R, M1, M3 and F closed at hand/exact-proof level; M2, global cost inequality and affine uniqueness open. The old *local* L3 shortening lemma is false and is in [legacy](docs/legacy/INDEX.md). The \(N\le61\) theorem is not a plan for length-by-length enumeration. No Lean, Lake or CI.
