# Scope and arithmetic audit of the small-shape root-to-shear argument

Date: 2026-11-08 UTC. Audit of the proposed hand lemma in
[MIXED_SMALLER_SHORT_SMALL_SHAPE_ROOT_SHEAR](MIXED_SMALLER_SHORT_SMALL_SHAPE_ROOT_SHEAR.md).
This is an audit record for that conditional lemma; it does not certify
that every actual short bridge is in its shape domain.

## 1. Hypotheses and physical objects

The hypotheses are exactly x in [2,13/6], delta=beta/x-1 in
[0,1/19], and alpha=1+eta*delta with eta in [13/5,3]. They imply
1<=alpha<=22/19<x<=beta<=alpha*x. The proof does not derive any of
these ratio, displacement or secant-order restrictions.

An actual descending root gives a positive residual immediately before
the root, at the same physical geometry and incoming norm. The
outer-envelope comparison raises that residual. Incoming norm
monotonicity is used only after assuming q<=qb<1/7, with the original
shape and 0<p<=r. Its domain is therefore satisfied. The substitution
u<=uhat raises only the scalar residual. The argument never uses the
outer norm floor or a Casimir ceiling at the raised value of u.

The enlarged beta interval in Section 3 is used solely to prove three
rational signs. The beta=-alpha evaluation in the residue calculation
is polynomial division; it is not a geometric endpoint. Positivity of
A2 at this evaluation follows from the completed-square proof, whose
g variable is unrestricted. It does not require the beta ordering.

The final shear calculation returns to the original physical q and
original shape. The only comparison point qb enters through the
explicit identity F-Gq and its positive slope coefficient G. No actual
root is asserted at qb.

## 2. Analytic reductions checked separately

1. The incoming cubic-tail bound implies U0 on the stated box because
   (beta-x)^2 S(35x+13)<=300x^2/361<96x^2(x-1)^2. The affine
   majorant is the exact difference with numerator
   t(8715t^2+4012t+1), with positive denominator.

2. Writing A2=mathcal A-gK+uhat*g^2 gives the displayed discriminant
   identity after completing the square. Both signs are independent of
   beta. The z upper bound is 49/36, not the larger 49/25 from the
   previous wide-domain draft.

3. The tangent at 4/5 uses log(5/4)>488/2187>223/1000.
   Its intersection with y-1 is 223/250. The q=p/2 boundary has the
   continuous polynomial extension at q=0; no logarithm is evaluated
   at zero. Its constant is 3/2-1223/1000=277/1000.

4. Affinity in q leaves the three stated faces. The qb face is convex
   separately on the two tangent pieces. The tau-two face is convex
   in q because A2>0. The p=r and p=0 tests on q=0 are both strictly
   negative using A1>3/2 and the rational constant in (14).

5. The beta-squared coefficient for J2 is
   8qb^2 uhat(x-alpha)^2/alpha^4. Polynomial division for Jtau
   gives exactly the residue in (17). The bound
   D(-alpha)H>=319/108>8/3>alpha^2+S-2 proves its sign.
   Strict convexity then reduces beta to its two straight endpoints.
   The endpoint at v=5/13 is permitted to exceed delta=1/19; its
   sign was proved on c<=3/19, rather than silently retaining the
   original delta restriction there.

## 3. The exact denominator audit

For the polynomials in (19), direct substitution gives
\[
\widehat u=N_u/D_u,\quad E_0=E/D_u,
\quad A_1=N_1/(\alpha^2D_u),
\quad A_2=N_2/(\alpha^4D_u),
\quad A_3=N_3/(\alpha^2D_u).
\]
All denominators are positive on the scalar domain. Inserting these
fractions in Jtau and multiplying by alpha*B*Du*C gives the negative
of (21), term for term. In particular the tau*r*A1 term becomes
-tau*C*N1, and the qb*tau*r*A2 term becomes lambda*tau*N2.
These are common locations for a lost alpha factor.

For J2, multiplication by 2000*alpha*B*Du*C^2 gives the negative of
(20). Its linear-q term contributes
\[
1000\lambda[5\alpha^2B^2D_uC
 -2\alpha BC(2N_1+N_3+\alpha^2D_u)],
\]
and its quadratic-q term contributes 4000*lambda^2*alpha*B*N2.
Thus all comparisons are made with the sign convention needed to
prove J<0 from P>0.

The normalization values are independent of v because c=0 forces
alpha=1,beta=x. They are positive and are printed exactly in (23).

## 4. What the short arithmetic certificate contains

The terminal arithmetic consists of the explicitly defined polynomials
(19)--(23), the two adverse derivative majorants (24), and the two
univariate lower polynomials (26). The largest polynomial has only
degree (8,6); the other family has degree (7,4). There are no cells,
subdivision endpoints, basis transformations, coefficient minima, or
external executable tables in this proof.

For (25), the coefficient comparison is equivalent to checking that
\[
-\partial_c\widehat P_{2,v}-3+N_2^+,
\qquad
-\partial_c\widehat P_{\tau,v}-14/5+N_T^+
\]
have nonnegative coefficients. Every adverse monomial of the
derivatives is explicitly dominated in (24). For (26), subtract the
printed lower polynomial from the polynomial obtained by setting
c=3/19 in (20) or (21); all coefficients are nonnegative. These are
small, completely specified polynomial inequalities and can be checked
by ordinary rational multiplication. Exact arithmetic was also used
as a discovery audit, but its execution is not a premise: all bounds
needed to perform the hand check are printed in the lemma.

The subsequent sign arithmetic is especially short. At t=c=1/6,
the adverse majorants have the exact values in (27); their comparisons
with 4/3 and 3/2 follow respectively from
\[
72885297<75582720,\qquad 1673878<1679616.
\]
Thus all six normalized numerators strictly decrease with c. The
endpoint lower polynomials are positive after discarding their positive
powers and bounding the one negative highest power by one.

## 5. Shear identity and final strictness

The physical relation rho/(1-rho)=q/[alpha^2(1-q)] converts the
existing physical shear formula into (28). The two numerator
identities in (30) follow by collecting the alpha and beta terms of
H0*R+13A/3. F>0 follows directly from H0>0,R>0,A>=0, so W>0;
Q>0 then gives V>0. Consequently the comparison qb>F/G has exactly
the sign Pi=29V-30WC>0, with no sign-changing denominator.

For Pi, (33) prints every negative monomial after
x=2+t, alpha=1+(3-k)delta, beta=x(1+delta). The omitted terms,
including the retained constant 1869 and t coefficient 9378, have
nonnegative coefficients. The four linear majorants (34) follow from
k^2<=4/25 and t^j<=t/6^{j-1}. Their summed bounds give
Pi>69+5578t>0. Thus q>qb>F/G, and F-Gq<0 at the original point.

Finally R>0 and A>=0 imply h<0. The strict comparison
13/(3sqrt3)>5/2 is equivalent to 676>675, yielding the needed
physical shear condition even when A=0.

## 6. Remaining caller work

A separate second reading accepts the conditional theorem. It checked
the positive-scale face selection, the two logarithm tangents, the
positive residues in the beta-convexity argument, the positive
denominators in (22), and the return to the original physical scale
in (28)--(31). The terminal signs are fully specified finite
polynomial inequalities with explicit adverse-term majorants; their
sign argument is printed in Sections 6--7 of the source.

This lemma can discharge a caller's root-to-shear gate only after that
caller has independently established all of (1). It does not prove
S1, S2 or S3 of the hand-only completion plan. Nor does it prove the
strict physical completion-cost contradiction S6. Those obligations
must retain their separate status until their own proofs and audits
are complete.
