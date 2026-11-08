# Excluding the nonshort forward successor through its two endpoints

Date: 2026-11-07. Hand reduction and directed interval certificates.

**Status: CLOSED at hand/computer-assisted proof level.** Both endpoint domains and their independent fresh replays have completed full two-root exclusions, with zero pending or unresolved records and observed process exit status zero. The [independent forward boundary audit](MIXED_NONSHORT_FORWARD_BOUNDARY_AUDIT.md) accepts the mathematical reduction, complete source and all four execution records. No Lean, Lake, typechecking or CI was run.

## 1. Exact obligation supplied by the actual period

The hand argument and exact identities are proved in
[MIXED_NONSHORT_FORWARD_BOUNDARY_REDUCTION](MIXED_NONSHORT_FORWARD_BOUNDARY_REDUCTION.md).
That note starts from the same-covector smaller-nonshort data of the actual competitive finite normal mixed period. It continues the unique scalar first-forward-root solution to b*=K/(a+c)-a while keeping a,c,d,r and v=Sec(a,c,d) fixed.

The comparison preserves the upper incident norm and decreases the outgoing norm w. The transported next norm increases. Along this root, the squared scalar Casimir Gamma(w) is a concave quadratic. If the next actual switch is forward, the actual norm lies between the boundary value w* and the explicit value wcap at which the transported next norm equals 3/4. Therefore the actual cap Gamma(wactual)<23/125 forces at least one endpoint to obey that cap.

The fixed scalar obligation is consequently to exclude **both** enlarged endpoint domains, not to transfer the actual Casimir cap to the artificial boundary. Each domain retains its own endpoint cap and the common condition t*>=3/4.

## 2. Common four-variable boundary domain

Use the notation of the reduction note:

\[
K=a^2+4,\ T=a+c,\ Q=d^2+4,\ W=c+d,\ Z=d+r,
\quad q=WZ/Q,\quad m=2/15.
\]

The common low-a theorem
[MIXED_NONSHORT_LOW_A_BOUNDARY_EXCLUSION](MIXED_NONSHORT_LOW_A_BOUNDARY_EXCLUSION.md)
excludes a<=1/2 for either next-switch alternative. The complementary caller uses the closed overlap a>=1/2.

The necessary common restrictions are

\[
a\le c,\quad a^2\le12/17,\quad T^2\le K,\quad
r\ge a,\quad c^2\ge ad,
\]
\[
cd+mW\le4,\quad dr+mZ\le4,\quad d,r\le8,
\quad T,W,Z\ge1/2,
\]
\[
v=\operatorname{Sec}(a,c,d),\qquad
v\le U(a/T),\quad v\ge g_c(d),\quad v\ge F_{d/W}(q),
\]
\[
u_*\le U(aT/K),\qquad t_*\ge3/4.
\tag{1}
\]

The source uses the exact desingularized root formula for u*, h*, w* and t*. The incoming upper/derivative constraints use the already proved divided regular expressions. Only a,c,d,r and v describe unchanged actual data; the root norms and diagonal at the artificial boundary have no additional lower, outgoing, acuteness or Casimir conditions.

In particular, the caller does not inherit b*<=8, u*>=3/4, h_d*>=0, w*>=g_d(r), or w*>=F_{d/Z}(q). It also does not impose the reverse-next secant ceiling or r^2>=ad.

## 3. New maximal charts cover every old chart

Set

\[
\delta_1=(d-a)/T,\qquad \delta_2=q-1,
\qquad \varepsilon'=\max(\delta_1,\delta_2).
\]

These quantities are unchanged by the b-comparison, and both deltas are positive at actual input. At the boundary delta0=0. Recompute the maximum using delta1 and delta2 only; do not retain the original three-parameter maximum.

The small-parameter hand theorem applies with l0=0 and excludes epsilon'<=1/32 from the preserved upper-norm condition u*<U*. Its shape assumptions are precisely the retained 0<a<=c, a^2<=12/17 and T^2<=K. This is valid even if delta0 was the largest parameter before the comparison, and even if that original delta0 exceeded 1/32.

The remaining two closed roots are:

| Selected maximum | a | c | epsilon' | l0 | Other weight |
| --- | --- | --- | --- | --- | --- |
| l1=1 | [1/2,17/20] | [2/15,2] | [1/32,15] | [0,0] | l2 in [0,1] |
| l2=1 | [1/2,17/20] | [2/15,2] | [1/32,15] | [0,0] | l1 in [0,1] |

The same turn/strict-star bounds give epsilon'<15. Reconstruction uses d=a+T*delta1, W=T(1+delta1), Q=d^2+4, Z=Q(1+delta2)/W and r=Z-d. In chart 2, the incoming missing-control condition and exact turn identity give d<=c, as proved in the original blowup note and rechecked for the boundary reduction. All ties and endpoint overlaps are retained.

## 4. The two exact endpoint residuals

Let E*=Gamma(w*)-23/125 be the existing centered Casimir expression, and set

\[
\tau=t_*-3/4,\qquad
B=\frac{Z^3(4-dr)}{d(r^2+4)^2}>0,
\]
\[
G_*'=\frac{Q^2v}{64}-\frac{h_{d,*}QZ}{8d},
\qquad C=\frac{Q^2Z^2}{256d^2}>0.
\]

The compact inactive-margin inequality ensures 4-dr>=mZ>0. The endpoint at t=3/4 is wcap=w*+tau/B. The exact algebra checker proves

\[
E_{\rm cap}=B^2E_*+BG_*'\tau-C\tau^2
=B^2[\Gamma(w_{\rm cap})-23/125].
\tag{2}
\]

The branch selector in
[mixed_nonshort_forward_boundary_interval_certificate.cpp](../explorations/mixed_nonshort_forward_boundary_interval_certificate.cpp)
chooses:

| Branch | Common extra residual | Endpoint cap residual |
| --- | --- | --- |
| 0, lower w endpoint | tau>=0 | -E*>=0 |
| 1, upper w endpoint | tau>=0 | -Ecap>=0 |

The second expression clears only the positive B^2; the caller never divides by B. Its implemented denominators d and r^2+4 remain strictly positive throughout the reconstructed comparison domain. The centered E* formula and transported determinant identity identify Gamma(w*) exactly with the scalar Casimir computed from u*, v and h*.

## 5. Frozen source and complete-root executions

Both branches use the same frozen caller and unchanged three shared headers. The original scratch source was `forward_boundary.cpp`, copied byte-for-byte to the published filename. Each invocation starts freshly from both stated roots, without a supplied pending-stack argument.

```sh
g++ -std=c++17 -O2 -I/workspace/scratch/5efeb2d2f42f/m2_mpfr_vendor forward_boundary.cpp -l:libmpfr.so.6 -lgmp -o forward_boundary
./forward_boundary 1000000 0 > forward_boundary_0_cover.log 2>&1
./forward_boundary 1000000 1 > forward_boundary_1_cover.log 2>&1
```

| Endpoint | Nodes N | Rejected leaves L | Pending | Unresolved | Max depth |
| --- | --- | --- | --- | --- | --- |
| 0 | 37,940 | 18,971 | 0 | 0 | 27 |
| 1 | 60,976 | 30,489 | 0 | 0 | 32 |

Each complete two-root forest satisfies N=2L-2 independently: 37940=2*18971-2 and 60976=2*30489-2. Both returned exit status zero. Both unresolved files are empty, and the arithmetic-environment/final-flag checks returned normally. The [lower-endpoint receipt](../explorations/mixed_nonshort_forward_boundary_0_result.json) and [upper-endpoint receipt](../explorations/mixed_nonshort_forward_boundary_1_result.json) record source, executable, full original/replay logs and unresolved-file hashes. The first execution took 203.56 seconds and the second 361.71 seconds; timing is not a proof premise.

| Frozen artifact | SHA-256 |
| --- | --- |
| forward_boundary.cpp | fc5a99b57c7546df86a4f800063f417a01537f0264de9b4c349ef323e839ad27 |
| certified_mpfr_interval.hpp | 1607b4f02063722506a514598d23d9b032a4aebfd6e74753bc302a7a67e32e76 |
| certified_lp_proposal.hpp | 6afe296ecd67f0ac3a48caa2460c9bf5bd58f358470a326f5a324879ba891454 |
| mixed_nonshort_coefficients.hpp | 5b0c5c70a10a058a50a2735282a640333a87def27a8dbf0def5547c46e4a266d |
| forward_boundary executable | b2915a1aad73e84008fb54ed939acffb94e10103f4e2e5ee7098388b2e0863d0 |
| forward_boundary_0_cover.log | 8312da2c0172549af162c62403d5f31afc7d9aea564325099e6bfb1c220e2d10 |
| forward_boundary_1_cover.log | b971a8bab60f7cd1e7c2c5cf6867d3d4e17b1bb58abbc21344bd9e4b6bff7659 |

The arithmetic-environment check requires matching MPFR header/runtime versions and valid fixed precision. A successful exit also requires clean arithmetic flags, no unresolved box and an empty pending stack. Natural/Taylor interval rejections and verified nonnegative LP combinations use the same audited directed-arithmetic engine as the accepted original caller; only the boundary domain and endpoint residuals change here.

A separate source snapshot was compiled with GCC 14.2.0, MPFR 4.2.2 and
GMP 6.3.0. Fresh invocations from the two original roots independently
reproduced both completed covers, including every reason counter and
maximum depth. Both returned exit status zero with empty pending and
unresolved records. The lower-endpoint replay took 203.24 seconds and
the upper-endpoint replay 360.01 seconds. Their full-log SHA-256 values
are respectively
`89a93c191c490502f1ff797ad155c33309e8d74346db66f70280623a84503b56`
and
`ac8ab0e0f5d92e2160892e39779cf2926a8a26a88cffafc32649bc32cd6a7fe1`.

With the arithmetic development dependencies installed, replay from the
repository root:

```sh
g++ -std=c++17 -O2 explorations/mixed_nonshort_forward_boundary_interval_certificate.cpp -lmpfr -lgmp -o /tmp/mixed_nonshort_forward_boundary
/tmp/mixed_nonshort_forward_boundary 2000000 0
/tmp/mixed_nonshort_forward_boundary 2000000 1
python explorations/mixed_nonshort_forward_boundary_certificate.py
python explorations/mixed_nonshort_boundary_records_verify.py
```

The first Python command checks the nine exact concavity and endpoint
identities; the second verifies all four boundary receipts, source
hashes and paired full logs. The mathematical domain review is separate
from those record checks.

## 6. Whole-period consequence and acceptance

The completed covers combine with the hand reduction in an exhaustive argument. The low-a theorem and small corner leave only the two high-a complementary charts. Actual forward-next data produce a boundary point in those charts, satisfy tau>=0, and satisfy at least one of the two endpoint caps by concavity. The corresponding complete endpoint cover contradicts that point.

This excludes the forward-next alternative for every finite normal mixed minimizing period in the stated domain, independently of run length, asymmetric margins and location of the twisted seam. The independent mathematical/source and execution acceptance records discharge the forward-next gate. The reverse-next alternative is addressed by the separate reverse-boundary theorem. Neither certificate changes the actual PMP covector or constructs an endpoint-corrected competitor.

The trust boundary is the frozen C++17/directed MPFR/GMP execution, audited analytic identities and rejection program. The hand comparison and concavity argument are explicit; no sampled optimization value is used in a proof premise. Lean kernel verification remains deferred by instruction.
