# Exact accounting for parallel nonshort cover replays

Date: 2026-11-07. This note explains a replay method. The live nonshort
chains are still incomplete; no M2 exclusion is asserted here.

The mathematical domain, contractions and rejection tests remain those
of the frozen
[nonshort caller](../explorations/mixed_nonshort_completion_interval_certificate.cpp)
and its [source/interface audit](MIXED_NONSHORT_INTERVAL_CERTIFICATE_AUDIT.md).
The [coordinator](../explorations/mixed_nonshort_completion_cover_chain.py)
changes how a finite covering computation is scheduled. It performs no
geometric split, contraction, interval evaluation or exclusion itself.

## 1. What a stopped prefix proves

The caller starts with a finite list of closed boxes. It removes a box
only after a certified rejection, or replaces its contracted necessary
domain by two closed boxes meeting at the exact split point. A permitted
contractor may remove only points already excluded by proved necessary
conditions. Thus the initial necessary domain is covered by the rejected
leaves together with the pending stack.

Let a successful arithmetic prefix begin with `R` box records, process
`N` nodes, reject `L` leaves, and leave `P` pending records, with zero
unresolved boxes. Its binary forest satisfies

\[
N=2L+P-R.
\tag{1}
\]

Indeed, if `I` processed nodes split, then `N=I+L` and
`P=R+2I-N`. This counts box records with multiplicity. Closed-box
boundary overlaps and maximal-chart overlaps do not affect the identity.

A node-budget stop is therefore a valid *partial* cover, but supplies no
exclusion of its pending boxes. The final arithmetic-flag check must
already have succeeded. A depth-limited unresolved box, runtime failure,
missing checkpoint or inconsistent count is not an accepted prefix.

## 2. Exact replacement of every pending record

The caller serializes each endpoint as the exact integer and power of two
returned by `mpfr_get_z_2exp`. Its loader checks that
`mpfr_set_z_2exp` reconstructs the endpoint without rounding. A box record
also retains its chart, branch and global subdivision depth.

For each pending record, the coordinator writes exactly one child input
with that unchanged record. It does not deduplicate equal records or
recalculate their endpoints. Each child uses the same fixed executable.
If a child stops at its node budget, all its pending records are assigned
in the same way. Every assignment retains the parent identifier and the
record's ordinal in the parent's checkpoint.

The offline verifier checks a rooted, acyclic graph of these assignments.
There is exactly one fresh three-root invocation for each of the two
next-switch branches. Every nonroot invocation consumes exactly the
record assigned by its parent. Every emitted record has exactly one
child, and every terminal invocation has an empty pending stack and zero
unresolved boxes. No unprocessed queue item, orphan job or omitted
frontier is allowed.

These are partitions of checkpoint *record lists*. The mathematical
boxes may share boundary points; such overlap is harmless and must not
be removed by numerical deduplication.

## 3. The complete-chain implication

For one next-switch branch, sum (1) over every job in a complete chain.
Every noninitial input record occurs once in a parent's pending list.
Consequently

\[
\sum_j P_j=\sum_j R_j-3,
\qquad
\sum_j N_j=2\sum_j L_j-3.
\tag{2}
\]

More substantively, recursive substitution of the verified child covers
removes every pending record from the root cover. The original three
complementary chart domains are therefore excluded. The scalar caller's
proof rules have not changed; the complete computation has been divided
into finite invocations of those rules.

The aggregate count in (2) is a useful consistency check. It is not
sufficient on its own: the verifier must also establish the exact
record-by-record replacement graph. A child message saying that its
supplied pending domain is exhausted is accepted only inside this
complete rooted graph.

Both next-switch branches must be covered. The separate
[small-parameter hand theorem](MIXED_NONSHORT_SMALL_PARAMETER_EXCLUSION.md)
supplies `0<=epsilon<=1/32`; the original complementary roots include
`epsilon=1/32`. The same-covector reduction and the exhaustive
next-actual-switch alternative remain mathematical premises of the
nonshort theorem.

## 4. Evidence and independent verification

The coordinator records the four frozen mathematical source hashes, the
compiler command/version, external header provenance, executable hash,
and every process command and exit code. Each job retains its complete
output log, exact input and pending checkpoint, leaf counters and local
conservation identity. The manifest ties these records together.

The independent
[graph verifier](../explorations/mixed_nonshort_cover_chain_verify.py)
must accept this evidence before a chain is used to close a theorem. Its
live mode rechecks the executable and external header as well as the
retained sources and records. An archived bundle retains the proof
sources, coordinator, build log, manifest, job logs and exact
checkpoints; its explicit archive mode permits the recorded executable
and external dependency header to be absent. It still checks the entire
stored graph and every retained hash. A fresh computational replay is
available from the published source and toolchain instructions.

Neither coordinator nor graph verifier replaces the interval arithmetic
audit, the caller's mathematical reduction, or the MPFR/GMP/compiler
trust boundary. This is an exact accounting method for the same
computer-assisted hand certificate. No Lean, Lake, typechecking or CI
is used.
