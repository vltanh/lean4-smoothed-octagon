# Independent internal audit of the forward norm and Casimir hand proof

Date: 2026-11-07 UTC.

**Verdict: accepted.** On the necessary ordered all-forward domain,
the exact stationary equations and genuine exterior norm floors imply
\[
\delta u+\delta v<1/35,\qquad \delta v<1/64.
\]
The conditional Casimir theorem then gives
\(\gamma^2>23/125\), contrary to the competitive cap.
These scalar implications are proved by hand. Neither of the old
forward interval covers, nor an executable coefficient sign test, is
a premise.

This audit concerns the scalar proof and its exact interface. The
application to every eligible actual all-forward period is assembled in
[HAND_FORWARD_PERIOD_EXCLUSION](HAND_FORWARD_PERIOD_EXCLUSION.md).
The mixed-period hand obligations are separate.

## 1. Documents and independent review allocation

The accepted proof consists of:

1. [HAND_FORWARD_CONDITIONAL_NORM_BOUNDS](HAND_FORWARD_CONDITIONAL_NORM_BOUNDS.md):
   the Casimir implication and both exact reductions to equal neighbors.
2. [HAND_FORWARD_SYMMETRIC_SUM_REDUCTION](HAND_FORWARD_SYMMETRIC_SUM_REDUCTION.md):
   the exact initial value and the complete low-D sum region.
3. [HAND_FORWARD_SYMMETRIC_SUM_HIGH_D](HAND_FORWARD_SYMMETRIC_SUM_HIGH_D.md):
   the complementary high-D sum region.
4. [HAND_FORWARD_LARGER_NORM_HAND_PROOF](HAND_FORWARD_LARGER_NORM_HAND_PROOF.md):
   the larger-neighbor norm bound.

The sum argument and conditional Casimir theorem were independently
reviewed by the root reviewer. The larger-norm argument was independently
reviewed by the cover-replay reviewer. Both reviewers also checked the
ordered-to-symmetric reductions. This is an internal mathematical
review record, not an assertion of Lean-kernel checking or external
peer review.

The local logarithmic bound
\[
f(h)\ge\frac{(h-1)^3}{3h(h+1)},\qquad
f(h)=\frac{h-h^{-1}}2-\log h,
\]
has a direct proof: the two sides agree at one and the derivative of
their difference is
\[
\frac{(h-1)^4}{6h^2(h+1)^2}\ge0.
\]
Thus the completed route does not depend on the unfinished
rational-triangle alternative.

## 2. Exact scalar interface and preserved domain

The input is
\[
11/5\le U<3,\qquad 1\le z\le w\le4/3,\qquad
z+w\le5(U-1)/3.
\]
Write
\[
S=1+z,\quad T=1+w,\quad K=1+U,\quad
Z=z^2+U,\quad W=w^2+U.
\]
The actual left exterior factor obeys
\[
S^2/Z\le h\le S(5U-2-3w)/(3Z).
\]
This cost upper bound retains the cost of the actual neighboring arcs;
the application of that budget to a full period is part of the
period-interface theorem.

The centered quantities are actual norms minus \(3/4\).
The first stationary row is
\[
n\,\delta u+m\,\delta v=r,
\]
and the actual exterior arcs supply
\[
\delta u\ge L(z,h),\qquad
\delta v\ge L(w,I),\qquad I=T^2/W.
\]
The second inequality uses monotonicity in the actual right factor,
which is at least \(I\). No exterior norm floor is discarded.

The coefficients \(n,m\) are positive, and
\[
SZ(m-n)
 =K(ST-K)+(h-1)\{S^4-K^2+KS^2(T-S)\}>0.
\]
Consequently
\[
\begin{aligned}
\delta u+\delta v\ge1/35
&\Longrightarrow
r-n/35-(m-n)L(w,I)\ge0,\\
\delta v\ge1/64
&\Longrightarrow
r-nL(z,h)-m/64\ge0.
\end{aligned}
\]
These are necessary consequences of the same exact stationary row;
no auxiliary endpoint is asserted to satisfy a PMP trajectory.

## 3. Both asymmetric residuals reduce in the correct direction

The audit checked the differentiated identities
\[
n_w=0,\qquad m_w=\alpha,\qquad
r_w=\alpha\{B(w/T)-3/4\},
\]
where
\[
\alpha=K[1+S(h-1)]/Z>0,\qquad B(s)=1-s+s^2.
\]
For \(V(w)=3/4+L(w,T^2/W)\), one has
\(V\ge B(w/T)\) and \(V_w\ge0\). The latter follows from
the explicitly increasing coefficients of the floor, the increasing
factor \(hf(h)/(h-1)\), and
\[
\frac d{dw}\frac{(1+w)^2}{w^2+U}
 =\frac{2(1+w)(U-w)}{(w^2+U)^2}>0.
\]
Therefore
\[
(\mathcal E_\Sigma)_w
 =\alpha(B-V)-(m-n)V_w\le0,
\]
and
\[
(\mathcal E_v)_w
 =\alpha\{B(w/T)-49/64\}<0,
\]
using \(B(w/T)\le37/49<49/64\).

Lowering \(w\) to \(z\) increases each residual and enlarges the
allowed cost interval for \(h\). Thus it is sufficient to exclude the
symmetric domain
\[
1\le z\le4/3,\quad 1+6z/5\le U<3,\quad
S^2/Z\le h\le S(5U-2-3z)/(3Z).
\]
Weak ties \(w=z\) and collapsed factor intervals are included.
The proof never needs the old stronger computational neighbor estimate.

## 4. Sum-residual proof

The root reviewer checked the exact initial-value identity
\(A_0=\mathcal E_\Sigma(1)\le0\), including its continuous boundary
extension and all five displayed derivative polynomials.

The low-D proof preserves the sign of every dropped term. In particular,
\(m_1-n_1>0\), the right floor is nonnegative, and \(A_0/H\le0\).
The estimates for \(P\), the logarithmic remainder, and the quadratic
envelope yield
\[
\frac{\mathcal E_\Sigma}{n_1H}
 <-1/35+D^2+D^3<0
\quad\text{for }D\le38/243.
\]
The terminal rational comparison has positive cross-product surplus
\(147167\).

For the high-D region the reviewer checked the stronger initial bound
\[
J\le-at^2/2-a^2t-a^3/3
\]
and the exact cancellation
\[
r_1-Sr_0=n_1a^2/2+SR/4,\qquad
R=D(I-zb)/I.
\]
Together with \(m_1-n_1-Sm_0=SR\), this gives the displayed formula
for \(A_1-SA_0\), without an unproved endpoint derivative substitution.

The remaining replacements have the required multiplier signs:

- \(A_0\le0\) justifies replacing \(H\) by \(H_c\) in \(A_0/H\).
- The reciprocal tangent is multiplied by \(bJ_*\le0\).
- The tangent for \(H_c/(1+H_c)\) is multiplied by
  \(D/2-19/243\ge0\).
- The lower floor for \(\Delta\) is subtracted with coefficient
  \(D(I-zb)/I\ge0\).
- The actual restriction \(U\le3\) gives
  \(t\ge39a/40\), hence \(u=1-4t\le1-39a/10\).
  This restriction is retained in the polynomial comparison.

The factored numerator, its six displayed coefficient polynomials, all
rounded upper and lower bounds, and the final quartic were checked.
The final strict sign follows from
\[
Q(a)=2013000a^4+495500a^3-439170a^2+63996a-2457>0
\]
on \(7/90\le a\le1/7\), by the two derivative arguments given in the
proof. Its three endpoint values are positive and its derivative signs
have the stated directions.

Thus the two D regions exhaust the symmetric domain and prove
\(\mathcal E_\Sigma<0\), hence \(\delta u+\delta v<1/35\).

## 5. Independent review of the larger-neighbor norm proof

### Concavity and the two tangent values

The right norm in \(\mathcal E_v\) is fixed at \(49/64\) in uncentered
notation. It enters through an affine multiple of \(m(h)\), so the
already proved exterior-factor concavity is unchanged. The tangent at
the lower factor \(I\) bounds the entire interval from above.
Checking the tangent at \(I\) and at \(h_c\) therefore suffices,
regardless of the sign of its slope. The case \(I=h_c\) is included.

### Scalar identity recipe and logarithm replacements

The reviewer independently derived the rational part in equation (12)
of the proof from the centered row and floor formula. In particular,
the coefficient of \(f(h)\) is exactly
\[
F(h)=z[1+n_1h/S],
\]
and the logarithmic remainder is exactly
\[
\Phi=S/2-2/S+2/K-K/8-\log I+\log c.
\]
Collecting the logarithms before replacing them produces precisely the
two displayed coefficients \(C_0/b^2\) and \(C_c/(3b^3)\).
Their elementary positive lower bounds hold on the full rectangle.

The coefficients of \(\log c\) are
\(c(1+St)\) and \(c(1+SH_c)\). They are positive on the actual domain.
Thus the upper bounds for both logarithms have the correct direction
even where individual uncombined logarithmic contributions would not.

Substitution and differentiation of the scalar recipe reproduce both
displayed polynomial numerator identities. Every denominator is
strictly positive. The appendix is complete; the sign argument does not
invoke an external coefficient list.

### Lower-factor numerator

The factorization of its constant-in-t part was checked, as were all
five row bounds whose sum is 70. The interpolation
\[
at\le a/12+2t/21
\]
is the convex combination with weights \(1/3,2/3\) of
\(at\le a/4\) and \(at\le t/7\).
It yields the strict bound
\[
N_0\le-a/6-11t/6<0.
\]
The actual hypothesis \(U<3\) ensures \(t>0\); the sign does not rely
on \(a>0\).

### Cost-endpoint tangent numerator

The split at \(t=1/5\) covers the full rectangle. Every discarded term
has the displayed sign. The final upper constants are exactly
\[
-\frac{150884}{117649}<0,\qquad
-\frac{2608047}{3764768}<0.
\]
For the nonmonotone coefficient \(B_1\), the stronger concavity bound
\(B_1''<-3600\) holds throughout \([1/5,1/4]\). At \(p=9/40\),
\[
B_1(p)=\frac{183891267}{16000000}<\frac{23}{2},
\qquad
B_1'(p)=\frac{9705459}{3200000}\in(0,4).
\]
The quadratic tangent bound therefore gives \(B_1<12\).
No unverified monotonicity assertion is used for this row.

Both tangent values are strictly negative. Concavity and the
ordered-to-symmetric transfer prove the actual inequality
\(\delta v<1/64\).

## 6. Conditional Casimir implication and final scalar conclusion

The root reviewer independently read the conditional theorem and
checked:

- The positive central pairing permits the replacement \(E_0\le e_0\)
  in the correct direction after squaring.
- The lower quadratic has negative definite Hessian, with determinant
  \(16(ST-1)>0\).
- Coordinate monotonicity reduces the clipped norm polygon to precisely
  \((1/35,0)\) and \((29/2240,1/64)\).
- Ordering and the actual central cost budget give
  \(S\le\min\{7/3,(5U+1)/6\}\).
- The axis bound decreases to \(U=13/5\) and then increases.
- The mixed-vertex error includes the positive norm-product correction.

The exact axis margin over \(23/125\) is \(89/9464000\).
The possible mixed-vertex loss is at most \(983/113836800\).
Their difference is
\[
\frac{89}{9464000}-\frac{983}{113836800}
 =\frac{73961}{96192096000}>0.
\]
Thus the two proved norm bounds imply the strict Casimir contradiction.

**Accepted scalar result.** Every actual ordered data set satisfying
the stated hand geometric restrictions, the exact common-covector
stationary row, and the genuine exterior floors is excluded. The
sum/larger-norm/Casimir gate has no remaining numerical or interval
premise. The separate period-interface theorem records which actual
whole periods meet those hypotheses.
