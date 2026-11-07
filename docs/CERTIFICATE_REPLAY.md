# Reproducing the arithmetic certificates

Date: 2026-11-07. Hand and computer-assisted proof workflow.
No Lean, Lake, typechecking or CI is part of this workflow.

The theorem dependencies are in
[GLOBAL_COST_EQUALITY_ASSEMBLY](GLOBAL_COST_EQUALITY_ASSEMBLY.md) and its
[independent audit](GLOBAL_COMPLETION_INDEPENDENT_AUDIT.md). A successful
arithmetic run is used only with its stated mathematical reduction. It
does not establish that an arbitrary input trajectory belongs to the
checked domain.

**Current acceptance boundary:** the F and smaller-short covers are
complete. Both smaller-nonshort covers are still running. The commands
below identify those remaining full-domain checks without claiming their
success.

## 1. Build environment

Run the commands from the repository root. The C++ programs require a
C++17 compiler and GMP development headers and libraries. The mixed
certificates also require matching MPFR development headers and runtime.
The recorded mixed runs use GCC 14.2.0 and MPFR 4.2.2, with 80-bit
significands and explicit rounding directions. The arithmetic engine
checks the header/runtime match at startup and rejects invalid arithmetic
flags before accepting a complete cover.

The MPFR dependency and its public Custom Interface are documented in
[INTERVAL_ARITHMETIC_ENGINE](INTERVAL_ARITHMETIC_ENGINE.md). The accepted
F program instead uses exact GMP rational arithmetic and outward integer
rounding. These checks have an explicit C++ compiler, arithmetic-library
and execution-platform trust boundary. They are not kernel proofs.

The symbolic Python programs use SymPy. They verify exact identities and
rational inequalities, separately from the interval covers. Repository
Lean sources and dependency pins are not build inputs for these programs.

## 2. Complete F cover

First replay the neighbor contraction that justifies the reduced
`1<=z,w<5/4` domain of the final caller:

```sh
g++ -O2 -std=c++17 explorations/global_forward_completion_neighbor_certificate.cpp -lgmpxx -lgmp -o /tmp/forward_neighbor_certificate
/tmp/forward_neighbor_certificate
```

Its accepted replay processed 8,183 nodes and excluded 4,092 leaves from
one root, with maximum depth 20, an empty stack and zero unresolved
boxes. The source, completed result and mathematical reduction are in
[GLOBAL_FORWARD_NEIGHBOR_CONTRACTION](GLOBAL_FORWARD_NEIGHBOR_CONTRACTION.md).

Then replay the final complementary Casimir cover:

```sh
g++ -O2 -std=c++17 explorations/global_forward_completion_casimir_certificate.cpp -lgmpxx -lgmp -o /tmp/forward_casimir_certificate
/tmp/forward_casimir_certificate
```

The accepted replay processed 20,999 nodes and excluded 10,501 leaves
from three roots, with an empty stack and zero unresolved boxes. Its
[result record](../explorations/global_forward_completion_casimir_certificate_result.txt)
identifies the source and terminal output. The source/domain review is
[GLOBAL_FORWARD_CASIMIR_CERTIFICATE_AUDIT](GLOBAL_FORWARD_CASIMIR_CERTIFICATE_AUDIT.md).
Combine the computed complementary cover with the hand circular-corner
theorem, as specified in
[GLOBAL_FORWARD_PERIOD_EXCLUSION](GLOBAL_FORWARD_PERIOD_EXCLUSION.md).

## 3. Shared directed arithmetic and the smaller-short cover

The engine's exact and analytic checks can be replayed independently:

```sh
g++ -std=c++17 -O2 explorations/certified_mpfr_interval_check.cpp -lmpfr -lgmpxx -lgmp -o /tmp/certified_mpfr_interval_check
/tmp/certified_mpfr_interval_check
```

The reported engine replay passed 116,914 checks. This is a regression
check count, not a count of boxes in a mathematical cover. The engine,
caller and scalar-domain argument have separate reviews in
[MIXED_SMALLER_SHORT_CERTIFICATE_AUDIT](MIXED_SMALLER_SHORT_CERTIFICATE_AUDIT.md).

```sh
g++ -std=c++17 -O3 explorations/mixed_smaller_short_interval_certificate.cpp -lmpfr -lgmp -o /tmp/mixed_smaller_short_interval_certificate
/tmp/mixed_smaller_short_interval_certificate 2000000
```

The accepted replay processed 107,977 nodes and excluded 53,989 leaves
from one root, with an empty stack and zero unresolved boxes. Its
[result record](../explorations/mixed_smaller_short_interval_certificate_result.txt)
includes the frozen source hashes, compiler, arithmetic runtime and
terminal output. The resulting theorem is
[MIXED_SMALLER_SHORT_PERIOD_EXCLUSION](MIXED_SMALLER_SHORT_PERIOD_EXCLUSION.md).

## 4. The two smaller-nonshort continuation covers

The supporting exact checks are:

```sh
python explorations/mixed_nonshort_completion_continuation_certificate.py
python explorations/mixed_nonshort_completion_blowup_certificate.py
python explorations/mixed_nonshort_coefficients.py
python explorations/mixed_nonshort_small_parameter_certificate.py
```

The coefficient checker parses the actual committed C++ expressions;
it neither regenerates nor changes the coefficient header. The
small-parameter checker supports the hand theorem for
`0<=epsilon<=1/32`. The mathematical domain and its positive-factor
contractors are reviewed in
[MIXED_NONSHORT_INTERVAL_CERTIFICATE_AUDIT](MIXED_NONSHORT_INTERVAL_CERTIFICATE_AUDIT.md).

Compile the published caller once, then run both branch arguments:

```sh
g++ -std=c++17 -O3 explorations/mixed_nonshort_completion_interval_certificate.cpp -lmpfr -lgmp -o /tmp/mixed_nonshort_completion_interval_certificate
/tmp/mixed_nonshort_completion_interval_certificate 2000000 0
/tmp/mixed_nonshort_completion_interval_certificate 2000000 1
```

Branch 0 is the next-forward-switch alternative; branch 1 is the
next-reverse-switch alternative. Each invocation starts afresh from all
three maximal-parameter chart roots. The complementary epsilon ranges
are `[1/32,61/4]` in chart 0 and `[1/32,15]` in charts 1 and 2. Each root
has `a` in `[2/15,17/20]`, `c` in `[2/15,2]`, two weights in `[0,1]`,
and the selected third weight equal to one. Chart ties and the common
`epsilon=1/32` boundary are deliberately covered more than once.

Both branch domains must be completely excluded, by successful full
runs or by the verified complete cover chains below. Neither one branch
alone, nor the hand corner alone, nor a successful continuation from an
unverified pending-stack file covers the required domain.

### Exact parallel cover chains

The [cover-chain accounting proof](EXACT_COVER_CHAIN.md) permits finite
prefixes of the same frozen caller to be joined into a complete rooted
cover. The coordinator starts each branch from its original three roots
and assigns every emitted checkpoint record, unchanged, to exactly one
child invocation. It uses at most six child processes. On a machine with
matching MPFR development headers, a fresh replay and its independent
verification are:

```sh
python explorations/mixed_nonshort_completion_cover_chain.py /tmp/mixed_nonshort_cover_chain
python explorations/mixed_nonshort_cover_chain_verify.py /tmp/mixed_nonshort_cover_chain/manifest.json
```

The output directory must not already exist. The coordinator retains the
source snapshot, toolchain and executable hashes, every process result,
and every exact input and pending checkpoint. The independent verifier
must find a complete graph for both branches, with no omitted frontier,
unknown box, failed job or orphan. It recomputes the local and aggregate
cover identities from the actual records. A coordinator progress line
or a child's pending-domain `PASS` does not satisfy this acceptance gate.

These live chains are currently running. Their completion and the final
independent verification remain pending.

## 5. Acceptance of a cover

For each full replay, inspect the actual process exit code and terminal
output. Acceptance requires all of the following:

- The executable was built from the identified source snapshot and its
  identified headers, without edits during the run.
- The process exits successfully and prints its full-domain `PASS`.
- The final stack is empty and the unresolved-box count is zero.
- The final arithmetic-flag check succeeds for MPFR-based covers.
- Summing the reason counters gives a leaf count `L` satisfying
  `nodes=2*L-roots`, with one root for the F neighbor contraction and
  smaller-short, and three roots for the final F cover and for each
  nonshort branch.

A depth-limit or node-budget stop alone is not a proof. A valid
node-budget prefix may be used only inside the fully verified cover chain
above. An intermediate line with zero unresolved boxes is also
insufficient while boxes remain on the stack. Domain-overlap exceptions
lead to subdivision, not exclusion.
A conclusively excluded box at the permitted maximum depth is valid;
an unresolved box at that depth prevents acceptance.

Native floating-point arithmetic selects subdivisions and proposes LP
weights. Every LP rejection is independently checked using an exact
nonnegative dyadic weighted sum and a fresh directed interval Taylor
bound. The proposal's numerical answer is never itself a proof sign.
Other conforming compilers may produce a different subdivision history;
the acceptance conditions and quantified domain still have to be met.
Matching a stored node count is not a substitute for those conditions.

The published source identifiers should be checked with `sha256sum`
against the relevant audit and result record. Keep the process result,
source/header identifiers, toolchain and branch arguments together when
recording an independent replay.

## 6. Terminal comparison and equality

```sh
python explorations/small_period_cost_equality_certificate.py
```

This program checks 72 exact identities and the terminal word coverage.
The associated hand comparison, including the strict mixed-five case
and the four-piece equality parameters, is reviewed in
[SMALL_PERIOD_COST_EQUALITY_AUDIT](SMALL_PERIOD_COST_EQUALITY_AUDIT.md).
Its use of the already established reverse-period exclusion applies to
actual normal minimizing periods. The final assembly explains why
classifying those minimizers gives the inequality for arbitrary
admissible competitors, and why equality classifies the original disk.

The scripts in this guide do not replace the geometric realization,
reverse comparison, compact-domain input, maximum principle, finite
representation or same-covector reductions. Their exact scope is part
of the final dependency audit.
