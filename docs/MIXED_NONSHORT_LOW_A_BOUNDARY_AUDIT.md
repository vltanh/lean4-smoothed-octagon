# Independent review of the common nonshort lower-scale exclusion

Date: 2026-11-07. Independent hand/interface, source and execution-record review. No Lean, Lake, typechecking or CI.

## Verdict

The common boundary reduction and the frozen caller justify **a>1/2 for every actual smaller-nonshort configuration**, independently of which switch follows r, under the previously retained whole-period/compact-state/PMP inputs. I found no material gap in this reduction. The original execution and the separate fresh replay both exhaust the complete two-root complementary domain with identical node, leaf, depth and reason counters.

This theorem is a necessary bound for the remaining case. It does not alone exclude the nonshort forward successor or close M2. The discarded five-variable cover is not used in this verdict.

## 1. The scalar comparison applies to both successors

I checked the comparison independently of the reverse-next conclusion. Hold a,c,d,r and v=Sec(a,c,d) fixed and increase b to b*=K/T-a. Throughout this interval ST<=K, d>a, q=WZ/Q>1 and Y=W^2-T^2>0. Thus

R_u=K[dSQ-Z(aK+SY)]/(aQ^2)<(K/(aQW))[a(ST-K)+Sc(a-d)]<0.

The denominator remains nonzero at the closed endpoint, so the linear root defines a continuous differentiable scalar solution throughout the interval. This is not a purported deformation of a physical trajectory.

For additional detail, partial differentiation of the central stationarity formula gives C_{a,b}=U(a/S) and h_b|_u=Kj/(16a), where j=u-U(a/S). Implicit differentiation of R_d=0 therefore yields

j_b=-K(dQ-ZY)j/(aQ^2 R_u)-a(b-a)/S^3.

The inhomogeneous term is strictly negative because b>=c>a. Variation of constants preserves the initial actual inequality j<0. Hence the boundary upper bound u*<U(aT/K) is necessary for **either** next-switch alternative. The outgoing comparison w_b<0 is valid but is not needed for the low-a exclusion.

No reverse-next hypothesis, r^2>=ad, or reverse secant ceiling enters this argument. The artificial boundary point is not assigned the original lower u bound, outgoing w restrictions, acuteness, or Casimir bounds.

## 2. The new maximum exhausts original delta0-maximal configurations too

After the scalar comparison, delta0 is exactly zero. The unchanged actual quantities delta1=(d-a)/(a+c)>0 and delta2=(c+d)(d+r)/(d^2+4)-1>0 admit the **new** maximum

epsilon'=max(delta1,delta2).

The two charts are l1=1 or l2=1, with l0=0 and the other weight in [0,1]. This is not a restriction to the original charts 1 and 2. An original point whose largest parameter was delta0 is first transported to b* and then assigned one of these two new charts. Thus no original delta0-maximal input is omitted.

The boundary root denominator is

D1=K^2[al2+cl1+T epsilon' l1 l2(2+epsilon' l1)]/(aQW)>0,

because at least one of l1,l2 is one and a,c>0. The exact cancelled identity gives u*=U*+epsilon' Phi*/D1. Therefore actual boundary data require Phi*<0.

The existing hand corner proof requires only 0<a<=c, a^2<=12/17, T^2<=K and nonnegative maximal weights. These hypotheses remain valid at l0=0. Consequently it excludes epsilon'<=1/32 regardless of the size or identity of the original maximum. The complement is covered by both closed roots beginning at exactly 1/32; overlaps and ties are retained.

The upper bounds are also independent of the next switch. T^2<=K gives c<2. The inequality c^2>=ad gives delta1<=c/a-1<14. Strict star dr<4 gives delta2<c/d<=c/a<15. Thus epsilon'<=15 is a valid closed enlargement.

In chart 2, delta2>=delta1 gives q>=W/T. If d>c, then d/W>1/2; monotonicity of F_{d/W} and the exact gap

F_{d/W}(W/T)-v=(d-c)[1/T-log(W/T)/(d-a)]>0

contradict v>=F_{d/W}(q). Therefore d<=c. At delta1=0 this order follows already from d=a<=c. This argument uses no reverse-next condition and no Casimir bound.

## 3. Frozen source and contractor review

The source hash is `448b6ad8858dcb6568a8748a41722d686e1fa525cc819cb87f7eff37a5e01edd`. I compared the complete source with the frozen reverse boundary caller `984f729590c1933ad7677b0d4a7392210f36f6a49f63f607b1576a4c6b69557c` and inspected the retained contractions and predicates.

The changes are the initial upper endpoint a=1/2, fixed branch selector 2, suppression of both next-switch clauses for that selector, and output filenames/messages. The numerical/analytic formulas, arithmetic engine, coefficient table, Taylor rejection and verified LP-combination mechanism are unchanged.

The common necessary vector contains only c>=a, T^2<=K, the reverse-centre scale bound, the two compact inactive-margin inequalities, r>=a, c^2>=ad, -Phi*>=0, the incoming turn upper/derivative restrictions, v>=Fend, d/r<=8, and T/W/Z>=1/2. Chart 2 additionally uses the proved order d<=c. In particular, branch=2 appends neither t>=3/4 nor r^2>=ad nor w*<=Sec(a,r,d).

All remaining contractors are justified by these common conditions:

| Contractor family | Necessary source and sign check |
| --- | --- |
| a/c scale and order | a^2<=12/17, c>=a(1+delta1), T>=1/2, T^2(1+delta0)<=K; all divided quantities are positive |
| Chart-2 order | a(1+delta1)<=c(1-delta1), hence delta1<1, with outward endpoint updates |
| Upper delta1 products | c>=a(1+delta1), cd+m(c+d)<=4, d<=8 |
| Upper delta2 product | c-m-(d+m)delta2>=0; the cap increases with c and decreases with a and delta1 |
| Lower delta2 product | r>=a, equivalently Q delta2>=T d+ac-4 |
| Remaining upper delta2 | r<=8, equivalently delta2<=W(d+8)/Q-1 |

The explicit cap from cd+mW<=4 is decreasing in a and c on its feasible domain; the retained stable quadratic-root bounds come from T^2<=K. The original lower-delta0 contractor using b<=8 is absent. The artificial inequalities b*<=8 and S*>=1/2 are absent from both the basic rejection vector and the retained necessary vector.

Five-coordinate storage causes no extra hypothesis: coordinate 3 is exactly [0,0], and the Taylor/LP widths in that coordinate are zero. The two fresh roots are charts 1 and 2 with a in [2/15,1/2], c in [2/15,2], epsilon' in [1/32,15], l0=0 and the remaining weight in [0,1]. Rational endpoints are rounded outward. No pending-stack file is supplied in the completed runs.

## 4. Completed records and independent replay

I read the original completed record and the separate fresh replay in `low_a_independent`, checked the frozen source and all unchanged header hashes, and compared every reason counter. Both runs returned the following mathematical counts:

| Nodes | Excluded leaves | Roots | Pending | Unresolved | Maximum depth |
| ---: | ---: | ---: | ---: | ---: | ---: |
| 74,772 | 37,387 | 2 | 0 | 0 | 23 |

The counters are: reason 1=1219, 15=8, 17=30142, 19=868, 20=2029, 22=13, 60=3108. Their sum is 37,387, and 74,772=2(37,387)-2. Both unresolved files are empty and both records finish with the complete two-chart pass after the final arithmetic flag check. The original elapsed time is 395.69 seconds; the separate fresh replay took 370.73 seconds.

Original log SHA-256: `2d882a3f615ced3159132ecc4a56f82727aa7280978bb3c64094bd696e232f4f`.

Separate fresh replay log SHA-256: `e7942150b68464b21eb4a18a492e8c78a015ae0b6212f03a1d449d778c22d016`.

The unchanged dependency hashes are:

- directed interval engine: `1607b4f02063722506a514598d23d9b032a4aebfd6e74753bc302a7a67e32e76`;
- verified LP proposal helper: `6afe296ecd67f0ac3a48caa2460c9bf5bd58f358470a326f5a324879ba891454`;
- exact coefficient header: `5b0c5c70a10a058a50a2735282a640333a87def27a8dbf0def5547c46e4a266d`.

## 5. Conclusion and trust boundary

Every actual smaller-nonshort input with a<=1/2 supplies a boundary point in the hand corner or one of the two completed complementary roots. Both possibilities are excluded. Therefore a>1/2 follows without assuming either successor branch has already been excluded. It may be used as an earlier input to the forward endpoint covers, with the closed root a=1/2 retained as overlap.

Acceptance remains at the stated hand/computer-assisted level: imported geometric/PMP premises, the reviewed C++17 source, directed MPFR/GMP arithmetic and the recorded completed executions. It is not Lean kernel or external peer-review verification.
