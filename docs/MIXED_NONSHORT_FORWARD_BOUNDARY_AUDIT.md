# Independent review of the nonshort forward endpoint reduction and caller

Date: 2026-11-07. Hand/interface and frozen-source review, with exact identity replay and original execution-record checks. No Lean, Lake, typechecking or CI.

## Verdict and acceptance boundary

I accept the four-variable forward endpoint reduction and the frozen caller with SHA-256 `fc5a99b57c7546df86a4f800063f417a01537f0264de9b4c349ef323e839ad27`. The two endpoint alternatives are exhaustive for actual smaller-nonshort data whose next switch is forward, and the source implements their enlarged necessary domains separately. I found no improper transfer of a physical condition to the artificial boundary.

Both original endpoint executions and the separate fresh replays have completed. I independently read all four final records, compared every mathematical counter, rehashed the fresh replay source and headers, and checked empty unresolved files and the absence of pending checkpoint files. Together with the accepted common lower-scale theorem, these records and this review close the forward-next alternative at the stated hand/computer-assisted level.

## 1. The actual root comparison and Casimir alternative

The comparison is along the scalar equation R_d=0 at fixed a,c,d,r and v=Sec(a,c,d), with b increased to b*=K/T-a. I independently checked the common upper-half-space argument in the low-a audit: R_u<0 remains strict at the endpoint, the continuous linear equation

j_b=A(b)j-a(b-a)/(a+b)^3

preserves j=u-U(a/(a+b))<0, and w_b<0 follows from the exact derivative formula. Therefore u*<U* and w*<w_actual. No geometric trajectory, outgoing derivative, lower norm, acuteness, or Casimir cap is claimed preserved under this comparison.

Stationarity independently gives H(w)=Q(Wv+Zw-C_d)/(16d), at both the actual and boundary solutions. The transported norm T(w) is affine with derivative

T'(w)=-B,  B=Z^3(4-dr)/(d(r^2+4)^2)>0.

The strict sign follows from the unchanged actual compact inactive-margin condition 4-dr>=(2/15)Z>0. Hence T(w*)>=T(w_actual)>=3/4. With tau=T(w*)-3/4 and wcap=w*+tau/B, actual data belong to [w*,wcap]. The degenerate tau=0 interval causes no division-by-zero inference; the endpoint conclusion then follows immediately.

The squared Casimir is the quadratic Gamma(w)=Q^2 v w/64-H(w)^2. Its curvature is -2C, where C=Q^2 Z^2/(256d^2)>0. The exact chord identity is

Gamma((1-theta)L+theta U)
=(1-theta)Gamma(L)+theta Gamma(U)+C theta(1-theta)(U-L)^2.

Consequently the actual strict cap Gamma(w_actual)<23/125 implies that at least one endpoint has Gamma<=23/125. It does **not** imply both endpoint caps or a cap on w* alone. The two separately checked source branches use precisely this disjunction.

## 2. Exact branch mapping in the source

Let E*=Gamma(w*)-23/125 and Gprime=Q^2 v/64-hd* QZ/(8d). The source appends the common condition tau>=0 and then:

| Source selector | Additional necessary condition | Mathematical endpoint |
| --- | --- | --- |
| 0 | -excess>=0 | E*<=0, the boundary outgoing norm w* |
| 1 | -(B^2 excess+B Gprime tau-C tau^2)>=0 | Gamma(wcap)<=23/125 |

The expression named `excess` is exactly E*, not Gamma itself. Its constant 7/2000 is 3/16-23/125, and its remaining terms are the exact expansion of K^2 u v/64-h^2 around the zero-duration reference. This identity and the positive desingularized root coefficient are inherited unchanged from the previously checked root formulas.

The second branch clears only the positive B^2:

B^2 E*+B Gprime tau-C tau^2=B^2[Gamma(wcap)-23/125].

It contains no division by B. The variable `hd` in Gprime is the forward-arc diagonal at the boundary, as required by the stationarity reconstruction, rather than the central diagonal h. I checked the signs, factors 8/64/256, the use of Kr=(r^2+4), and the tau normalization 3/4 against the hand formulas.

The exact checker `mixed_nonshort_forward_boundary_certificate.py` was independently replayed and passed all nine identities: forward stationarity, diagonal derivative, transported norm derivative and affinity, Casimir derivative and concavity, upper endpoint normalization, cleared endpoint cap, and nonnegative chord remainder. These algebra checks supplement the preceding sign and interval argument; they do not replace it.

## 3. Complete new chart domain, including the old delta0-maximal region

The scalar comparison sets delta0=0. The maximum is then recomputed as epsilon'=max(delta1,delta2), not retained from the original three-variable chart. Every original configuration, including one originally assigned to a delta0-maximal chart, yields one of the two new charts l1=1 or l2=1 with l0=0.

The boundary root coefficient is strictly positive after cancellation whenever one of l1,l2 is one. The preserved upper incident norm requires Phi*<0. The old hand small-parameter theorem uses only 0<a<=c, a^2<=12/17, T^2<=K and the nonnegative maximal weights, so it applies with l0=0 and excludes the **new** corner epsilon'<=1/32. Original points with large delta0 and small delta1,delta2 are therefore excluded by this corner after the comparison; they are not omitted from the complement.

The unchanged compact/order bounds give c<2, delta1<14 and delta2<15. The accepted common low-a theorem proves a>1/2 for both successor alternatives without using either endpoint cap, so the new initial interval a in [1/2,17/20] is not circular. The lower endpoint 1/2 and epsilon'=1/32 are deliberately retained in the complementary roots.

For each endpoint branch, the only fresh roots are charts 1 and 2, each with a in [1/2,17/20], c in [2/15,2], epsilon' in [1/32,15], fixed coordinate l0=[0,0], and the remaining weight in [0,1]. The a upper endpoint safely contains sqrt(12/17), which the common scale contractor enforces. The comparison does not change a,c,d,r or the incoming actual turn. All weak chart ties and zero-weight limits are included.

## 4. Retained restrictions and contractors

I compared the entire frozen forward source with `reverse_boundary.cpp` (`984f729590c1933ad7677b0d4a7392210f36f6a49f63f607b1576a4c6b69557c`). Apart from the documented endpoint expressions, branch selector validation, initial a interval, and output names, the necessary common vector, all contractors, H bounds, coefficient expressions, Taylor rejection and verified LP-combination mechanism are unchanged.

Every contractor uses only the common conditions reviewed in the low-a audit: a/c order and scale, T^2<=K, pair sums, c^2>=ad, the two compact inactive-margin conditions, d/r<=8, r>=a, and the chart-2 order d<=c obtained from v>=Fend. No contractor uses a reverse-only hypothesis or an endpoint cap.

In particular, the forward source removes r^2>=ad and w*<=Sec(a,r,d). It does not impose b*<=8, u*>=3/4, hd*>=0, the outgoing derivative/missing-control inequalities, a lower Casimir bound, or an extra cap at the other endpoint. Both branch cases retain only their selected cap residual. The artificial S* bound and the old b<=8-derived lower-delta0 contractor remain absent.

The chart-2 condition is necessary for either successor: q>=W/T, and if d>c then the monotonic F gap contradicts the unchanged incoming missing-control inequality. It does not rely on the new forward conclusion. Exact zero width in l0 does not introduce an assumption about that derivative; all Taylor and LP width contributions in that coordinate vanish.

## 5. Original executions and independent fresh replays accepted

The same frozen source was invoked fresh with branch selectors 0 and 1, without a supplied pending stack. I read the final records and verified each reason-counter sum and the two-root identity independently:

| Endpoint | Nodes | Leaves | Pending | Unresolved | Maximum depth |
| --- | ---: | ---: | ---: | ---: | ---: |
| w* | 37,940 | 18,971 | 0 | 0 | 27 |
| wcap | 60,976 | 30,489 | 0 | 0 | 32 |

Each satisfies N=2L-2 separately. The respective reason counters are:

- branch 0: 1=195, 15=25, 17=8396, 19=647, 20=3320, 26=1016, 27=782, 28=153, 60=4437;
- branch 1: 1=199, 15=28, 17=10305, 19=647, 20=5382, 26=3124, 27=2095, 28=53, 60=8656.

The full-pass messages follow the final arithmetic-flag check. The original unresolved files are empty. The original branch-1 log hash is `b971a8bab60f7cd1e7c2c5cf6867d3d4e17b1bb58abbc21344bd9e4b6bff7659`. The separate fresh replays match every displayed counter and the frozen mathematical source/header hashes. Both have zero pending and unresolved boxes, finish after the arithmetic-flag check with the full fresh two-root pass, and have no pending checkpoint file. Their elapsed times are 203.24 seconds for endpoint 0 and 360.01 seconds for endpoint 1. Their log SHA-256 values are respectively `89a93c191c490502f1ff797ad155c33309e8d74346db66f70280623a84503b56` and `ac8ab0e0f5d92e2160892e39779cf2926a8a26a88cffafc32649bc32cd6a7fe1`. I accept these complete execution records; this is not acceptance of a stopped prefix or an empty unknown counter alone. The retained full logs and receipts are `results/mixed_nonshort_forward_boundary_{0,1}_{original,replay}.log` and `explorations/mixed_nonshort_forward_boundary_{0,1}_result.json`.

The directed engine, LP helper and coefficient header retain respectively SHA-256 `1607b4f02063722506a514598d23d9b032a4aebfd6e74753bc302a7a67e32e76`, `6afe296ecd67f0ac3a48caa2460c9bf5bd58f358470a326f5a324879ba891454`, and `5b0c5c70a10a058a50a2735282a640333a87def27a8dbf0def5547c46e4a266d`.

## Scope

This is a uniform whole-period necessary-data obstruction. It neither enumerates forward-run lengths nor assumes a boundary point itself realizes a physical period. The actual same-covector and twisted-seam premises enter before the scalar comparison. The mathematical conclusion follows from the exhaustive two-endpoint alternative, accepted low-a/corner reductions, and complete fresh two-root covers. Its arithmetic trust boundary remains the reviewed C++17/directed MPFR/GMP execution; no Lean kernel or external peer-review verification is claimed.
