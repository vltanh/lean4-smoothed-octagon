# Smaller-nonshort reverse-next exclusion by a boundary comparison

Date: 2026-11-07. Hand reduction and complete directed interval execution.

**Status: CLOSED at hand/computer-assisted proof level.** The two-root scalar exclusion has completed, its boundary transfer and every retained contractor have passed an [independent internal review](MIXED_NONSHORT_REVERSE_BOUNDARY_AUDIT.md), and a separate fresh replay reproduced the complete cover. No Lean, Lake, typechecking or CI was run. The forward-next alternative is not addressed by this theorem.

## 1. Statement and actual-period interface

Consider the smaller-nonshort assignment at a globally smallest active margin of a competitive finite normal mixed minimizing period, with the actual same-covector data of `MIXED_SMALLER_TURN_CONTINUATION.md`:

\[
0(p),\quad 1(b),\quad 0(a),\quad 2(c),\quad 0(d),\quad 1(r),
\qquad a<b,\ a<c\le b,\ d>a,\ r\ge a.
\]

All compact-state, central reverse-scale, genuine-switch, and stationarity inputs are the retained whole-period inputs in that note and `MIXED_NONSHORT_BLOWUP_REDUCTION.md`. The next actual switch after the arc at r cannot be reverse.

Indeed the exact next-switch interface would give

\[
w\le \operatorname{Sec}(a,r,d),\qquad r^2\ge ad.
\tag{1}
\]

The proof below derives an impossible boundary scalar point from (1). It does not alter any physical trajectory, refit its costate, or replace its actual first event. The scalar comparison is applied only after all actual identities and inequalities have been obtained.

## 2. The upper-norm half-space survives the scalar comparison

Set

\[
K=a^2+4,\quad T=a+c,\quad S=a+b,\quad Q=d^2+4,
\quad W=c+d,\quad Z=d+r,\quad Y=W^2-T^2.
\]

Hold a,c,d,r and the actual incoming secant \(v=\operatorname{Sec}(a,c,d)\) fixed. Increase b along the unique solution of the first-forward stationarity equation to

\[
b_*=K/T-a>b.
\]

The root coefficient is

\[
R_u=\frac{K}{aQ^2}\{dSQ-Z(aK+SY)\}<0.
\]

This remains strict on the entire closed interval, including b=b_*: since Z>Q/W and d>a,

\[
dSQ-Z(aK+SY)
<\frac QW\{a(ST-K)+Sc(a-d)\}<0.
\]

Let \(j=u-U(a/S)\), with \(U(x)=1-x+x^2\). The exact identities in the continuation note are

\[
j_b=-\frac{K(dQ-ZY)}{aQ^2R_u}j-\frac{a(b-a)}{S^3},
\qquad
w_b=-\frac{dK^3j}{aQ^3R_u}.
\tag{2}
\]

The coefficients are continuous on the compact comparison interval. Multiplying the first equation by its positive integrating factor shows that j remains strictly negative, because j is initially negative and its inhomogeneous term is strictly negative. The second equation consequently gives w_b<0. Thus the boundary solution satisfies

\[
u_*<U_*:=U(aT/K),\qquad
w_*<w\le\operatorname{Sec}(a,r,d).
\tag{3}
\]

No Casimir inequality is transported through this comparison. Neither is a lower incident-norm bound, a forward-acuteness bound, or an outgoing missing-control/derivative inequality. None of these is present in the boundary certificate.

## 3. The exact necessary boundary domain

Write m=2/15. The unchanged variables obey

\[
m\le a\le c,\qquad a^2\le12/17,\qquad T^2\le K,
\]
\[
d\ge a,\qquad r\ge a,\qquad d,r\le8,\qquad
T,W,Z\ge1/2,
\]
\[
cd+mW\le4,\qquad dr+mZ\le4,\qquad c^2\ge ad,\qquad r^2\ge ad.
\tag{4}
\]

The incoming turn and first-forward endpoint inequalities remain

\[
v=\operatorname{Sec}(a,c,d),\qquad
v\le U(a/T),\qquad v\ge g_c(d),\qquad
v\ge F_{d/W}(q),\quad q=WZ/Q>1,
\tag{5}
\]

where \(g_B(x)=1-Bx/(B+x)^2\) and

\[
F_x(q)=1+x^2q-\frac{xq\log q}{q-1}.
\]

Central and forward stationarity at b_* determine u_*, h_* and w_* by the same exact formulas as the original caller, now with \(S=K/T\). In addition to (4)--(5), retain exactly (3).

The artificial b_* need not satisfy b_*<=8, so that bound and its lower-delta0 contractor were removed. The artificial pair sum S is also not constrained. The common boundary domain includes no gamma, h_d, u lower, w derivative, or outgoing F constraint.

## 4. Two closed maximal charts and the corner

Put

\[
\delta_1=(d-a)/T,\qquad \delta_2=q-1,
\qquad \varepsilon=\max(\delta_1,\delta_2)>0.
\]

At actual input both deltas are positive and unchanged by the scalar comparison. Use the two closed charts \(\delta_i=\varepsilon l_i\), with l0=0 and either l1=1 or l2=1. The other weight lies in [0,1]. Reconstruction is

\[
d=a+T\delta_1,\quad W=T(1+\delta_1),\quad
Z=Q(1+\delta_2)/W,\quad r=Z-d.
\]

The bounds c<2 and a>=2/15 give c/a<15. The retained turn inequality c^2>=ad gives delta1<=c/a-1<14, while dr<4 gives delta2<c/d<=c/a<15. Thus both roots may use epsilon<=15.

The previous exact cancellation identities remain valid at l0=0:

\[
R_d(U_*)=\varepsilon^2\Phi_*,\qquad
R_u=-\varepsilon D_1,
\]
\[
D_1=\frac{K^2}{aQW}
\{al_2+cl_1+T\varepsilon l_1l_2(2+\varepsilon l_1)\}>0.
\]

Therefore \(u_*=U_*+\varepsilon\Phi_*/D_1\), so (3) requires Phi_*<0. The certificate retains the weaker closed condition -Phi_*>=0.

The hand theorem in `MIXED_NONSHORT_SMALL_PARAMETER_EXCLUSION.md` proves Phi_*>0 for 0<epsilon<=1/32. Its assumptions are only \(0<a\le c\), \(a^2\le12/17\), \(T^2\le K\), and nonnegative maximal weights; it requires neither an actual positive delta0 nor the original three-parameter maximum. It applies directly to these two new charts. Hence only epsilon in [1/32,15] remains.

In chart 2, q>=W/T. The unchanged identity

\[
F_{d/W}(W/T)-v
=(d-c)\left[\frac1T-\frac{\log(W/T)}{d-a}\right]
\]

and strict increase of F_x for x>1/2 imply d<=c. This is exactly the original chart-2 restriction; it does not use delta0 or the Casimir. At delta1=0 it follows already from d=a<=c. All chart overlaps and weak endpoint ties are retained.

## 5. Frozen complementary-domain execution

The frozen source is [mixed_nonshort_reverse_boundary_interval_certificate.cpp](../explorations/mixed_nonshort_reverse_boundary_interval_certificate.cpp), originally executed as `reverse_boundary.cpp`. It retains five-coordinate storage but fixes coordinate 3, l0, to the exact interval [0,0]. Its only fresh roots are:

| Chart | a | c | epsilon | l0 | Other weight |
| --- | --- | --- | --- | --- | --- |
| 1, l1=1 | [2/15,17/20] | [2/15,2] | [1/32,15] | [0,0] | l2 in [0,1] |
| 2, l2=1 | [2/15,17/20] | [2/15,2] | [1/32,15] | [0,0] | l1 in [0,1] |

All contractions use inequalities in (4)--(5), or the chart-2 order just proved. The original contractor using b<=8 was removed. The unchanged interval kernel, H enclosures, coefficient formulas, Taylor bounds and verified nonnegative LP-combination logic are the already audited arithmetic mechanism.

The exact invocation was fresh, with no supplied pending-stack file:

```sh
g++ -std=c++17 -O2 -I/workspace/scratch/5efeb2d2f42f/m2_mpfr_vendor reverse_boundary.cpp -l:libmpfr.so.6 -lgmp -o reverse_boundary
./reverse_boundary 1000000 > reverse_boundary_cover.log 2>&1
```

It returned exit status zero and:

```text
FINAL branch 1 nodes 106134 stack 0 depth 26 unknown 0 seconds 539.67
reason 1 leaves 1409
reason 17 leaves 35210
reason 19 leaves 4405
reason 20 leaves 3948
reason 22 leaves 11
reason 26 leaves 993
reason 27 leaves 722
reason 28 leaves 5
reason 60 leaves 6365
PASS: complete two-chart reverse boundary domain excluded; interface audit still required.
```

There are 53,068 excluded leaves. The two-root forest identity is exactly

\[
106134=2(53068)-2.
\]

The pending stack is empty and `mixed_nonshort_completion_unresolved_1.txt` has zero bytes. Arithmetic-environment and final arithmetic-flag checks returned normally. The [published receipt](../explorations/mixed_nonshort_reverse_boundary_result.json) records these counts, the complete original and replay logs, source/artifact hashes, and both execution commands.

| Frozen artifact | SHA-256 |
| --- | --- |
| reverse_boundary.cpp | 984f729590c1933ad7677b0d4a7392210f36f6a49f63f607b1576a4c6b69557c |
| certified_mpfr_interval.hpp | 1607b4f02063722506a514598d23d9b032a4aebfd6e74753bc302a7a67e32e76 |
| certified_lp_proposal.hpp | 6afe296ecd67f0ac3a48caa2460c9bf5bd58f358470a326f5a324879ba891454 |
| mixed_nonshort_coefficients.hpp | 5b0c5c70a10a058a50a2735282a640333a87def27a8dbf0def5547c46e4a266d |
| reverse_boundary executable | 3fb6b180f142297b7acb18ae54eb55a2df16d5f9c2ae71f587d0cf24fa7febb0 |
| reverse_boundary_cover.log | 32d2d520054feaf9658777dc352c8ebb65b2878772da14f05e48ad64dffdd729 |

A separate build from byte-identical source and headers, followed by a
fresh invocation from the two original roots, returned exit status zero
with the same 106,134 nodes, 53,068 leaves, reason counters and maximum
depth 26. It had an empty stack and unresolved file; elapsed time was
550.63 seconds. Its full log has SHA-256
`3cd136f0e706204b4ff01b49d840be2d2fa915c8c8df722d849d80a38de6719a`.
The replay used GCC 14.2.0, MPFR 4.2.2 and GMP 6.3.0. With their
development headers installed, reproduce the accepted theorem from the
repository root by:

```sh
g++ -std=c++17 -O2 explorations/mixed_nonshort_reverse_boundary_interval_certificate.cpp -lmpfr -lgmp -o /tmp/mixed_nonshort_reverse_boundary
/tmp/mixed_nonshort_reverse_boundary 2000000
python explorations/mixed_nonshort_reverse_boundary_certificate.py
```

The original source's leading pending comment and terminal request for
an interface audit are retained byte-for-byte to preserve the executed
source identity. The linked independent audit discharges that request.

## 6. Whole-period consequence and trust boundary

The hand corner and the completed two-root complementary cover exhaust every boundary point supplied by an actual reverse-next continuation. They contradict (3), and hence exclude that next-switch alternative uniformly in the eventual forward-run length and the number of pieces in the original period. The actual frame/costate seam is unchanged because the scalar argument starts from the already established cyclic same-covector interface.

The computational trust boundary is the frozen C++17 caller, directed MPFR/GMP arithmetic, its audited analytic and LP verification code, and the successful execution records. This is a hand/computer-assisted scalar exclusion, not Lean kernel verification. The independent review accepts the boundary transfer and the omission or retention of every contractor. The forward-next case and final whole-period assembly remain separate obligations.
