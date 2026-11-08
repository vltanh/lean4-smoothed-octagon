# Independent audit of the reverse-next boundary exclusion

Date: 2026-11-07. Independent internal mathematical and source review.
No Lean, Lake, typechecking or CI.

**Reviewed result:** the boundary comparison and the retained two-chart
certificate domain are valid consequences of the actual reverse-next
alternative. The recorded fresh execution is complete: 106,134 nodes,
53,068 excluded leaves, no pending or unresolved boxes. This review
checks the mathematical reduction, source diff, hashes and record.
Separately, the integrating author rebuilt the frozen caller and
completed a fresh replay from both original roots: the counts, reason
distribution and depth agree exactly, with exit status zero and no
pending or unresolved boxes. Its complete record is in
[mixed_nonshort_reverse_boundary_result.json](../explorations/mixed_nonshort_reverse_boundary_result.json).
The forward-next alternative and final whole-period assembly are
separate obligations.

The theorem is
[MIXED_NONSHORT_REVERSE_BOUNDARY_EXCLUSION](MIXED_NONSHORT_REVERSE_BOUNDARY_EXCLUSION.md).
The source reviewed here is
[mixed_nonshort_reverse_boundary_interval_certificate.cpp](../explorations/mixed_nonshort_reverse_boundary_interval_certificate.cpp),
originally executed as `reverse_boundary.cpp`, with SHA256
`984f729590c1933ad7677b0d4a7392210f36f6a49f63f607b1576a4c6b69557c`.

## 1. The scalar comparison has the required scope

Start from the actual data and notation of
[MIXED_SMALLER_TURN_CONTINUATION](MIXED_SMALLER_TURN_CONTINUATION.md).
Fix a,c,d,r and the actual v=Sec(a,c,d). Central stationarity gives

\[
h=\frac K{16a}(Su+Tv-C_a),\qquad
\partial_b C_a=U(a/S),\qquad U(x)=1-x+x^2.
\]

Consequently, with j=u-U(a/S), the partial derivative at fixed u is
`h_b=Kj/(16a)`. Substitution into forward stationarity and transport
independently gives

\[
R_b=\frac{K(dQ-ZY)}{aQ^2}j,
\qquad
R_u=\frac K{aQ^2}[dSQ-Z(aK+SY)].
\]

Throughout b<=b*=K/T-a, ST<=K, Y>0, Z>Q/W and d>a. The exact decomposition

\[
dSQ-Z(aK+SY)
=\frac QW[a(ST-K)+Sc(a-d)]
 -(Z-Q/W)(aK+SY)
\]

is strictly negative. Thus the affine root equation determines a smooth
unique real u(b) throughout the closed comparison interval. No lower
bound on this artificial u is needed. At its endpoint, another check is

\[
R_u(b_*)=-\frac{K^2}{aQ^2T}[Z(W^2-cT)-dQ]<0,
\]

because `W^2-cT-dW=c(d-a)>0` and `Z>Q/W`.

Implicit differentiation now gives

\[
j_b=-\frac{K(dQ-ZY)}{aQ^2R_u}j-\frac{a(b-a)}{S^3},
\qquad
w_b=-\frac{dK^3j}{aQ^3R_u}.
\]

The first equation has continuous coefficients and strictly negative
forcing, since b>=c>a. Its positive integrating factor preserves the
initial j<0. Since R_u<0, the second equation then gives w_b<0. Hence

\[
u_*<U(aT/K),\qquad w_*<w\le\operatorname{Sec}(a,r,d).
\]

These are exactly the two transported inequalities used by the caller.
The comparison does not assert that the artificial endpoint is a PMP
trajectory or preserves the original Casimir, lower switch norms,
acuteness or outgoing switch inequalities. All actual premises were
obtained from one continuous normal covector before this scalar
comparison; no independent local lift is fitted.

## 2. Every retained residual remains necessary

The variables a,c,d,r and v are unchanged. Their retained inequalities
therefore require no transport of an artificial costate:

| Residuals in the caller | Source after the comparison |
| --- | --- |
| c>=a, a^2<=12/17, T^2<=K | Original minimum/scale and b>=c, ST<K |
| r>=a, c^2>=ad | Original global minimum and incoming-turn log-concavity |
| cd+mW<=4, dr+mZ<=4, with m=2/15 | Original inactive state margins at the unchanged exterior switches |
| d,r<=8 and T,W,Z>=1/2 | Compact state bounds on the same unchanged coordinates |
| Divided `upper_turn` and `turn` | Actual v<=U(a/T) and v>=g_c(d); their positive factors and continuous zero-turn limits are unchanged |
| v>=F_(d/W)(q) | Actual incoming missing-control inequality on the same forward arc |
| -Phi>=0 | The proved boundary upper norm, using `u_*=U_*+epsilon*Phi/D1` |
| r^2>=ad, `ceiling-w>=0` | Original reverse-next alternative and the proved decrease of w |
| Chart 2: d<=c | Unchanged v=Sec(a,c,d), v>=F_(d/W)(q) and delta2>=delta1 |

The code's analytic secant ceiling equals
`1+r^2/((a+r)(d+r))-r*log((d+r)/(a+r))/(d-a)` for d>a,
and uses its continuous divided-difference limit at d=a.

The diff against the old frozen caller removes `u>=3/4`, both outgoing
w floors, `h_d>=0`, both Casimir residuals, `b<=8`, and `S>=1/2`.
It also removes the contractor deriving a lower delta0 from b<=8.
None of these discarded conditions reappears in `basic_empty`, the
retained `needed` vector, or the LP rejection input. Quantities such as
the Casimir are still computed by the shared evaluator but are unused
by every rejection in this caller.

## 3. All retained contractors are valid at delta0=0

The contractions were checked against the boundary domain, rather than
accepted solely because they were valid for the original actual point.
Here z=delta1>=0 and m=2/15.

| Contraction or product bound | Necessary source |
| --- | --- |
| a<=sqrt(12/17); pair-sum lower bounds for a,c | Scale and T>=1/2 |
| c>=a(1+z), a<=c/(1+z) | c^2>=ad with d=a+(a+c)z |
| c<=sqrt(a^2+4)-a; a<=(4-c^2)/(2c) | T^2<=K; the old rationalized root formula is continuous and has denominator 2c at delta0=0 |
| a^2<=4/((2+z)^2-1) | Combine T^2<=K with c>=a(1+z) |
| a<=[4-c^2 z-mc(1+z)]/[(c+m)(1+z)] | cd+mW<=4 |
| c<=[8-a(1+z)]/z for z>0 | d<=8; skip division when the lower z endpoint is zero |
| delta0<=K/T^2-1 | At delta0=0 this enforces only T^2<=K; no positive delta0 is assumed |
| delta1<=min(c/a-1, (4-ac-mT)/(T(c+m)), (8-a)/T) | Turn log-concavity, inactive margin and d<=8 |
| Chart 2: delta1<=(c-a)/(a+c), and its rearrangements | d<=c; its cap is strictly below one because a>0 |
| delta2<=(c-m)/(a+T delta1+m) | dr+mZ<=4 |
| delta2>=(Td+ac-4)/Q; delta2<=W(d+8)/Q-1 | r>=a and r<=8; both are evaluated by natural outward interval bounds |

The delicate direct a cap decreases in c and z. Its derivatives are

\[
-\frac{4+m^2(1+z)+c^2z+2cmz}{(c+m)^2(1+z)},
\qquad
-\frac{4+c^2}{(c+m)(1+z)^2}.
\]

Both are negative. The inactive delta1 cap decreases in a; it decreases
in c whenever its necessary numerator is nonnegative. The delta2 cap
increases in c and decreases in a,z. These signs justify the retained
endpoint choices. The remaining monotone substitutions are immediate
from the displayed positive-factor bounds. Upper product contractions
round upward and divide only by positive lower endpoints; lower product
contractions round downward and divide by positive upper endpoints.

A chart-2 lower z endpoint at least one is impossible by the chart cap.
The fixed l0 coordinate remains exactly zero. No contractor assuming
that b_* is a physical compact-state margin remains.

## 4. Two roots exhaust the original reverse-next branch

After the comparison, set epsilon=max(delta1,delta2), ignoring the old
maximum that may have been delta0. Both unchanged deltas are positive
at actual input and less than 15. Choose l1=1 or l2=1, with l0=0 and
the other weight in [0,1]; ties belong to both charts. Thus points
originally in all three maximal charts are represented by the new two.

The positive coefficient D1 remains positive when l0=0, since one of
l1,l2 equals one and a,c>0. The root cancellation and reconstruction
were polynomial/analytic identities on nonnegative weights, so they
remain valid on this face. The upper-norm inequality becomes Phi<=0.

The proof of [MIXED_NONSHORT_SMALL_PARAMETER_EXCLUSION](MIXED_NONSHORT_SMALL_PARAMETER_EXCLUSION.md)
uses only `0<a<=c`, `a^2<=12/17`, `T^2<=K` and nonnegative maximal
weights. Its positive quantity `M=a(l0+l2)+c*l1` remains nonzero here.
It therefore excludes the whole new corner epsilon<=1/32, including
asymmetric shapes. Both closed complementary roots begin at 1/32,
with a in [2/15,17/20], c in [2/15,2], epsilon in [1/32,15],
l0=[0,0] and the other weight in [0,1]. No original chart-0 region is
lost when delta0 was large but the other two deltas were small.

The chart-2 implication d<=c uses only the unchanged turn and incoming
missing-control inequality. For d>c, the exact comparison at W/T is
strict and F_(d/W) increases with its argument, contradicting
q>=W/T. It retains weak missing-control ties; at d=a the conclusion
already follows from a<=c.

The initial interface already covers a next switch across the actual
twisted seam, on the same normal covector. The scalar comparison neither
constructs a competitor nor changes the original period's endpoints.
No preservation of a physical seam along the artificial homotopy is
claimed or required.

## 5. Source and execution checks

The directed arithmetic kernel, coefficient header and verified LP
proposal helper are byte-identical to the previously reviewed files:

| Artifact | SHA256 |
| --- | --- |
| certified_mpfr_interval.hpp | 1607b4f02063722506a514598d23d9b032a4aebfd6e74753bc302a7a67e32e76 |
| certified_lp_proposal.hpp | 6afe296ecd67f0ac3a48caa2460c9bf5bd58f358470a326f5a324879ba891454 |
| mixed_nonshort_coefficients.hpp | 5b0c5c70a10a058a50a2735282a640333a87def27a8dbf0def5547c46e4a266d |
| Reviewed executable | 3fb6b180f142297b7acb18ae54eb55a2df16d5f9c2ae71f587d0cf24fa7febb0 |
| Original completed log | 32d2d520054feaf9658777dc352c8ebb65b2878772da14f05e48ad64dffdd729 |

The actual quoted-header resolution under the recorded compile command
was checked against these contents. The new source changes only the
retained inequality vector, the corresponding geometric precheck and
b-bound contractor removal, and the two l0=0 roots/branch label.
The Taylor and exact nonnegative LP-combination rejections, closed
midpoint bisection, arithmetic-flag checks, depth-limit accounting and
checkpoint distinction are unchanged.

The recorded run starts from its two original roots, not a supplied
pending stack. Its leaf reasons sum to 53,068 and its complete forest
satisfies

\[
106134=2\cdot53068-2.
\]

The final stack and unresolved count are zero; maximum depth is 26,
below the limit 85. The unresolved artifact is empty, with SHA256
`e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855`.
The normal return through `check_flags` precedes the final record.
These facts were checked directly against the source, receipt and log.

This is a new two-root scalar theorem justified by Section 4. It is
not a claimed completion of the old three-root nonshort execution
forest. The arithmetic trust boundary remains the reviewed C++17
caller, MPFR/GMP implementation, compiler and successful execution,
as described by [INTERVAL_ARITHMETIC_ENGINE](INTERVAL_ARITHMETIC_ENGINE.md).

The supplementary exact check is reproducible from the repository root:

```sh
python explorations/mixed_nonshort_reverse_boundary_certificate.py
```

All **20** named identities passed. It checks both comparison
derivatives and the sensitive endpoint/contractor formulas using exact
symbolic arithmetic. The integrating-factor, sign and coverage
arguments remain the hand proof above; the script is not a replacement
for either those arguments or the complete interval execution.

## 6. Conclusion

Under the retained actual-period interface and stated arithmetic trust
boundary, the boundary cover and hand corner contradict every
reverse-next continuation. The independent review found no omitted
boundary, extra artificial-costate assumption, contractor mismatch or
whole-period/seam gap in this implication. It supports closing the
reverse-next subbranch after its reviewed execution evidence is
published. It does not assert the forward-next exclusion, the entire
M2 theorem or the final sharp cost/equality theorem.
