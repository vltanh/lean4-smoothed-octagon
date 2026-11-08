# Audit of the variable-floor reduction and rational incoming ceiling

Date: 2026-11-08 UTC. **Audited conclusion:** the reduction in
[MIXED_SMALLER_SHORT_VARIABLE_FLOOR_REDUCTION](MIXED_SMALLER_SHORT_VARIABLE_FLOOR_REDUCTION.md)
is an explicit analytic reduction to two scale faces. It does not prove
that either terminal face has negative sign. This is the reconstruction
audit of the new argument; independent reviewer acceptance must be
recorded separately before changing any completion gate.

## 1. Statement, dependencies and unchanged geometric scope

The starting object is an actual eligible smaller-short mixed bridge
with the original common covector, genuine first outer root and actual
outgoing norm floor. The ratio interval is

\[
13/6\le x<12/5,
\quad 1\le\alpha<x\le\beta\le\alpha x,
\quad \operatorname{Sec}(1,x,\beta)
 =\operatorname{Sec}(\alpha,\beta,x)=u.
\]

The reconstruction uses the following already established inputs.

| Input | Use |
| --- | --- |
| [Six-variable reduction](MIXED_SMALLER_SHORT_SIX_VARIABLE_REDUCTION.md) | Actual geometry, root, scale and covector transport formulas. |
| [Large-ratio exclusion](MIXED_SMALLER_SHORT_LARGE_RATIO_HAND_EXCLUSION.md) and [positive diagonal pairing](MIXED_SMALLER_SHORT_POSITIVE_DIAGONAL_PAIRING.md) | The remaining actual domain has \(x<12/5\), \(D>0\), \(E_L>0\). |
| [Global upper order](MIXED_SMALLER_SHORT_GLOBAL_UPPER_ORDER.md) | The beta lower bound needed for \(D<Q\). |
| [Floor-weighted envelope](MIXED_SMALLER_SHORT_FLOOR_WEIGHTED_ENVELOPE.md) | The two envelope derivative identities; their positivity is re-proved at the changed weight and the smaller ratio threshold. |
| [Normalized envelope scale formulas](MIXED_SMALLER_SHORT_ENVELOPE_SCALE_MONOTONICITY.md) | Exact expressions \(R_{p/q}^*=C(p)+qL(p)\), \(w_*=1-qA_1+q^2A_2\), and the three scale constraints. |
| [Incoming norm bound](MIXED_SMALLER_SHORT_INCOMING_NORM_BOUND.md) | \(3/4<u\le V(x)<61/80\) on the retained ratio interval. |
| [Root-floor scale argument](MIXED_SMALLER_SHORT_ROOT_FLOOR_SCALE.md), Section 3 | The elementary implication \(D>0\Rightarrow(x-1)^2<2\alpha^2\); its argument uses only \(x>1\), \(\alpha\ge1\), \(\alpha\le x\), \(\beta\ge x\), and not its later large-ratio restrictions. |

No value of the physical cost, competitive upper Casimir cap or incident
norm ceiling is transported to a changed scale. In particular, the
actual outgoing norm floor is inserted into a scalar expression before
the envelope comparison; it is not asserted separately at the envelope.

## 2. Actual positivity and scale reduction

At the actual first root, define

\[
y=\tau/T\in(0,1),\qquad m=2-7y/4\in(1/4,2),
\qquad G=R_\tau+m(w-3/4)>0.
\]

For fixed geometry, scale and duration, \(m\) is constant during the
opposite-turn comparison. Its derivative factor is the old one with
\(z=\tau+m\). The bound \(z\le T+1/4\) and the explicit inequality
\(4Q-5(D-S)\ge x(3x-5)>0\) ensure its positivity in the whole new
domain. Consequently \(0<G\le G^*\) at the original scale.

The domain bounds are obtained from the actual shape. The proof of
\(r_A<3/7\) extends to \(x\ge15/7\) because the exact endpoint
\(F(15/7)=2/351>1/196\) contradicts the alternative secant estimate.
The quadratic for the upper incoming norm bound is concave, so its two
positive endpoint values suffice. The \(D<Q\) proof uses a convex
quadratic in \(\alpha\), with strictly negative values at both
endpoints; no interior sign is inferred from a concave maximum. The
bound \(D<3\alpha^2\) follows from the displayed completed square.

At fixed normalized duration \(p=\tau q\), the weight is fixed, and
\(G^*\) is a quadratic in \(q\) with positive quadratic coefficient
\(mA_2\). The discriminant estimate proving \(A_2>0\) is displayed in
full. The actual scale lies below
\(\min(q_c,1/7,p/2)\), so convexity forces a positive value at zero
or this upper endpoint. At zero, the affine logarithm majorant has
both endpoint values strictly negative, with the explicit upper bounds
\(-1317/21280\) and \(-11/1224\). Thus the zero endpoint is removed.

If the upper endpoint is \(p/2\), then \(\tau=2\). Continuing this
face to \(\min(q_c,1/7)\) stays inside \(T>35/17>2\) and increases
\(G_2\), by Section 3 below. The two remaining scale faces are exactly
\(q=q_c\le1/7\) and \(q=1/7\le q_c\), including equality of the caps.

## 3. Replacement of the former continuation coefficient estimate

The earlier unpushed reduction gave aggregate bounds for negative
coefficients of four trivariate polynomials. The revised proof has
removed that premise. It now has the following chain of elementary
identities and signs.

1. The derivative \(qG_2'(q)\) is the cubic Bernstein polynomial
   displayed in equation (17). All four coefficients are specified.
   The first nonconstant coefficient has the explicit positive lower
   bound \(11/336\).
2. Completing the two diagonal squares gives the lower bounds
   \(B_2\ge F_2\), \(B_3\ge F_3\). Their \(a^2\) coefficients are
   positive multiples of
   \(-S^2[u-U(1/S)]^2/(4u)\), so concavity in \(a\) reduces to
   the two endpoints \(a=0,1\).
3. At those endpoints the \(p^2\) coefficient is positive. The maximum
   of each \(p\)-derivative is therefore at \(p=3/7\). The four
   factored mixed-derivative identities (24) locate their maxima in
   \(u\); all four maxima are strictly negative by (25) and its
   elementary numerator estimates. This justifies decreasing \(p\),
   rather than guessing an extremal value from numerical probes.
4. At fixed \(S,p,a\), concavity in \(u\) follows directly from the
   second derivative of \(-(A-Bu)^2/(cu)\). This gives the two
   incoming-norm endpoints.
5. The remaining eight one-variable rational functions have their
   complete quartic numerators and positive denominators printed in
   equation (26). With \(0\le h<1/4\), all negative terms are bounded
   explicitly by \(|c_4|/256\) or
   \(|c_3|/64+|c_4|/256\). The stated integer comparisons prove all
   eight strict signs. No unlisted coefficient positivity is invoked.

The polynomial identities were reconstructed algebraically as a
check on transcription. Their mathematical proof consists of the
printed substitutions, differentiations, completed squares and small
quartics; it does not depend on executing a coefficient checker.
No Lean, Lake, typechecking or CI was run.

### Independent second reading

A separate reading accepts the reduction, including the new continuation
argument, within its stated scope. In particular, the positive quadratic
coefficients in (23) justify taking the largest p before checking the
four derivatives; their u-monotonicities have opposite directions in
the two F_2 and two F_3 cases, and the proof uses the correct endpoint
in each. Concavity in u is used only after p has been fixed. The eight
fully displayed quartics are bounded on h in [0,7/30], with h<1/4;
the negative cubic and quartic terms in the last two rows are both
included. The t,v envelope and both scale motions retain only the
combined scalar. This acceptance closes that analytic reduction, not
either terminal sign, S1, S2, or H-S.

## 4. Incoming-norm monotonicity and the Gauss bound

The coefficient of \(u\) in the combined scalar is explicitly bounded
below by \(109/140\). The use of \(\lambda\le1\),
\(S\le17/5\), \(d<3/7\) and \((\tau+m)d<1+d/4\) accounts for
every bound in that estimate. This permits an independently proved
incoming upper bound to be inserted after scale reduction.

The accompanying
[Gauss incoming ceiling](MIXED_SMALLER_SHORT_GAUSS_INCOMING_CEILING.md)
is a direct specialization of the existing
[positive-integral secant bound](MIXED_NONSHORT_POSITIVE_INTEGRAL_SECANT_BOUND.md).
The substitutions

\[
c=x/(1+x),\quad t=1/(1+x),\quad p=\beta/(1+x),
\quad z=(\beta-1)/(1+x),\quad W=1+z
\]

preserve all hypotheses. The factors satisfy
\(cp/W^2=x\beta/(x+\beta)^2\) and
\(cz/W^2=x(\beta-1)/(x+\beta)^2\), giving exactly the stated ceiling.
Its remainder is a positive multiple of
\(\int_0^1(1-s)^2P(s)^2/(1+zs)\,ds\), with \(P\) printed.
The integrand is continuous, nonnegative and not identically zero;
\(z>0\), so the remainder is strictly positive. The displayed moment
\(1/1575\) gives the strict rational error upper bound. This is a
short integral identity, with no coefficient-list premise.

## 5. Remaining gap and gate status

The two scale faces in Section 7 of the reduction still require
strict upper bounds on the combined scalar. The old unpushed central
and outer sign drafts each define a rational polynomial, but their
claimed signs rest on grouped lower bounds for, respectively,
51,840 and 62,010 transformed coefficients. Although the coefficient
extraction formulas are precise, no analytic derivation of those
uniform bounds is supplied. Merely directing a reader to expand and
inspect all coefficients leaves the intended hand-proof obligation
unfulfilled.

Therefore this audit certifies no S1 or S2 closure. The exact missing
terminal obligations, and the separate lower-ratio issue, are recorded
in [RATIO_SIGN_HAND_GAP](MIXED_SMALLER_SHORT_RATIO_SIGN_HAND_GAP.md).
Neither the number of scalar faces nor successful computational
reconstruction of their signs supplies the missing analytic proof.
