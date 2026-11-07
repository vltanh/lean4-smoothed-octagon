# A common lower bound at every smaller-nonshort minimum

Date: 2026-11-07. Hand reduction and complete directed interval execution.

**Status: CLOSED at hand/computer-assisted proof level.** The two-root scalar exclusion has completed with zero pending or unresolved records. Its [independent boundary/source audit](MIXED_NONSHORT_LOW_A_BOUNDARY_AUDIT.md) and a separate fresh replay accept the theorem. No Lean, Lake, typechecking or CI was run.

## 1. Theorem and comparison

Every actual smaller-nonshort configuration in the retained competitive finite normal mixed minimizing-period domain satisfies

\[
\boxed{a>1/2.}
\]

This conclusion is independent of which switch follows the actual arc at r. It uses no transported next-switch bound and no Casimir cap on an artificial boundary point.

Use the b-homotopy and notation proved in Sections 1--4 of `MIXED_NONSHORT_REVERSE_BOUNDARY_EXCLUSION.md`. Its preservation of the strict upper-norm half-space does not use the reverse-next hypothesis. Every actual configuration therefore supplies a boundary solution with

\[
\delta_0=0,\qquad u_*<U(aT/K),\qquad
v=\operatorname{Sec}(a,c,d)\ge F_{d/W}(q).
\]

The unchanged a,c,d,r retain their compact and incoming-turn restrictions. In the notation of that note, retain its equations (4)--(5), **except** the reverse-only inequality r^2>=ad. From its equation (3), retain only u_*<U_*; do not retain w_*<=Sec(a,r,d).

The artificial lower incident norm, outgoing norm/derivative/missing-control conditions, acuteness, and both Casimir inequalities are all omitted. The bound b_*<=8 and its contractor are omitted too. Thus this is a common necessary domain for either possible next switch.

## 2. Exhaustion of the boundary domain with a<=1/2

The same two maximum charts use l0=0 and epsilon=max(delta1,delta2). Their bounds and the chart-2 restriction d<=c require no reverse-next hypothesis. The exact root relation is

\[
u_*=U_*+\varepsilon\Phi_*/D_1,\qquad D_1>0,
\]

so u_*<U_* requires Phi_*<0. The existing hand small-parameter theorem excludes epsilon<=1/32, with the same justification at this boundary given in the reverse note.

Assume now a<=1/2. The two complementary roots are

| Chart | a | c | epsilon | l0 | Other weight |
| --- | --- | --- | --- | --- | --- |
| 1, l1=1 | [2/15,1/2] | [2/15,2] | [1/32,15] | [0,0] | l2 in [0,1] |
| 2, l2=1 | [2/15,1/2] | [2/15,2] | [1/32,15] | [0,0] | l1 in [0,1] |

`low_a_boundary.cpp` is the frozen caller. Its branch selector is exactly 2, for which it appends neither of the next-switch alternatives. The necessary vector consists only of the common geometric/incoming restrictions and -Phi_*>=0. All contractors are identical to those in the reviewed reverse boundary reduction, apart from the smaller initial a interval; no reverse-only condition is used by a contractor.

## 3. Complete execution receipt

The fresh invocation, with no supplied pending stack, was

```sh
g++ -std=c++17 -O2 -I/workspace/scratch/5efeb2d2f42f/m2_mpfr_vendor low_a_boundary.cpp -l:libmpfr.so.6 -lgmp -o low_a_boundary
./low_a_boundary 1000000 > low_a_boundary_cover.log 2>&1
```

It returned exit status zero and:

```text
FINAL branch 2 nodes 74772 stack 0 depth 23 unknown 0 seconds 395.69
reason 1 leaves 1219
reason 15 leaves 8
reason 17 leaves 30142
reason 19 leaves 868
reason 20 leaves 2029
reason 22 leaves 13
reason 60 leaves 3108
PASS: complete two-chart low-a boundary domain excluded; interface audit still required.
```

The 37,387 rejected leaves satisfy the exact two-root forest identity

\[
74772=2(37387)-2.
\]

`low_a_boundary_unresolved_2.txt` is empty, the stack is empty, and the initial arithmetic-environment and final arithmetic-flag checks returned normally. The [published receipt](../explorations/mixed_nonshort_low_a_boundary_result.json) records the exact domain, both complete logs, execution commands and source hashes.

| Frozen artifact | SHA-256 |
| --- | --- |
| low_a_boundary.cpp | 448b6ad8858dcb6568a8748a41722d686e1fa525cc819cb87f7eff37a5e01edd |
| low_a_boundary executable | f12aed2a1ae34407eb79fc0cf41c3cdef66f2a1d05eacd6a2974cd86a8390722 |
| low_a_boundary_cover.log | 2d882a3f615ced3159132ecc4a56f82727aa7280978bb3c64094bd696e232f4f |

The three arithmetic/coefficient headers are byte-identical to the reverse boundary execution, with their hashes recorded there and in the JSON receipt. The compiled mathematical source is frozen even though its copied leading comment still mentions the reverse boundary; the explicit branch=2 and conditional clauses implement the common domain described here.

A separate build and fresh replay from both original roots returned exit
status zero with the same 74,772 nodes, 37,387 leaves, reason counters
and maximum depth 23. The replay stack and unresolved file were empty;
elapsed time was 370.73 seconds. Its full log has SHA-256
`e7942150b68464b21eb4a18a492e8c78a015ae0b6212f03a1d449d778c22d016`.
The independent review checked both complete records against the frozen
caller and its mathematical domain. Reproduce from the repository root:

```sh
g++ -std=c++17 -O2 explorations/mixed_nonshort_low_a_boundary_interval_certificate.cpp -lmpfr -lgmp -o /tmp/mixed_nonshort_low_a_boundary
/tmp/mixed_nonshort_low_a_boundary 2000000
python explorations/mixed_nonshort_boundary_records_verify.py
```

The Python command verifies the retained records and hashes; the C++
invocation re-executes the actual quantified exclusion.

## 4. Consequence and scope

The hand corner and the completed complement contradict every boundary point obtained from an actual configuration with a<=1/2. Therefore every smaller-nonshort actual configuration has a>1/2. Subsequent forward/reverse scalar covers may begin with the closed lower boundary a=1/2 and retain overlap.

The theorem is uniform in the eventual forward-run length and period length. Its only period input is the already accepted global-minimum/same-covector continuation interface and compact/scale restrictions. The numerical minimizer near a=0.63972571635 motivated this weaker rational threshold but is not a premise. The arithmetic trust boundary remains the frozen C++17/directed MPFR/GMP execution and its independently audited rejection mechanism, not a Lean kernel proof.
