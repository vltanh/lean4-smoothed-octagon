# Completed central low-ratio corrected-cap sign (S1.2)

This closes the actual central row S1.2 of the replacement ledger. It replaces the large derivative and terminal certificates in equations (20)--(25) and Appendices A--C of
[MIXED_SMALLER_SHORT_LOW_RATIO_CENTRAL_HAND_SIGN](../../archive/notes/MIXED_SMALLER_SHORT_LOW_RATIO_CENTRAL_HAND_SIGN.md).
The scalar conclusion and original caller domain are unchanged. The old auxiliary cone derivative statements are not all re-proved; the new reductions below prove exactly the two strict signs the caller needs.

## 1. Unchanged theorem and source domain

Let x,a,b,u be the actual shape and incoming norm, with
\[
 1<x\le2,\qquad1\le a<x\le b\le ax,\qquad6a^2\le x(x+2),
\]
\[
 x+\frac{8x(a-1)}{9x+8}\le b
 \le x+\frac{x(7x+1)(a-1)}{4x^2+11x+1}.
 \tag{1}
\]
The incoming norm satisfies the original incoming secant bounds. In particular,
\[
 3/4<u\le u_\ell(x,b)
 =3/4+\frac{(x-1)^2(b+15x-16)}{8(x+1)(35x+13)(b-1)}.
 \tag{2}
\]
The proof of (2) is the unchanged small-shape incoming estimate in Section 3 of the original central note; a≤2/√3<6/5 supplies its stated shape hypothesis.

Use precisely the central transport functions and tests F0,F1 printed in
[the reduction note](SHORT_CENTRAL_REDUCTION.md), with c=7/96 and g=9193/50000.
Then
\[
 \boxed{F_0\ge167/144000000>0,\qquad F_1>1/50000>0.}\tag{3}
\]
Consequently, at the central scale q=a²/(x(x+2)+a²), for every 2≤tau≤T,
\[
 \boxed{\Gamma-(7/96)R_\tau>9193/50000.}\tag{4}
\]
The duration endpoints and q=1/7 boundary are included.

## 2. The complete reduction chain

The cap in (1) implies x≥√7−1>8/5 and a≤2/√3<7/6. The old order strip is contained in
\[
 x+(1/2)(a-1)\le b\le x+(10/13)(a-1).
\]
For its upper endpoint the explicit quadratic comparison is
\[
 13x(7x+1)-10(4x^2+11x+1)=(x-2)(51x+5)\le0.
\]
All comparisons therefore lie in the containing rectangles explicitly proved in the new notes.

The [norm monotonicity proof](SHORT_CENTRAL_NORM_MONOTONICITY.md) establishes both norm derivatives negative on the full original containing rectangle. The
[quantitative reduction](SHORT_CENTRAL_REDUCTION.md) strengthens this to
\(-1/5<(F_0)_u\le(F_1)_u<0\) on [3/4,19/25], proves both exact-log cost derivatives in beta greater than 1/40, and gives
\[
 \frac d{db}F_j(x,a,b,u_\ell(x,b))<-101/318720.
\]
This is a total derivative along the original ceiling. It permits replacing the actual incoming norm by u_l and then beta by b+=x+(10/13)(a−1).

For F0, the [cap-sensitive shape proof](SHORT_CENTRAL_SHAPE_F0.md) gives
\[
 \frac d{da}F_0(x,a,b_+,u_\ell(x,b_+))<-4553/2589600
\]
wherever 6a²≤x(x+2). Increase a to its true endpoint a_c=√(x(x+2)/6), retaining both the beta and norm dependencies. At this endpoint the central and outer rational transport formulas coincide. Explicitly, the outer quantity 6a_c²+1 is (x+1)², its pairing numerator J becomes
\((x+1)^3(u-1)+3(x+1)-1\), and its M becomes
\((x+1)^2((x+1)^2-(x+1)+1)\).
The two transport denominators, scale, duration, and logarithm argument also coincide. The exact central logarithm is bounded above by the outer proof's cubic majorant, so the completed outer first-test proof supplies its certified margin 167/144000000. The shape note spells out why this proof already covers b=b+ and why u_l≥u_f at that cap. Thus no old central terminal polynomial is needed for F0.

For F1, use norm monotonicity to increase u directly to 19/25, followed by fixed-norm beta monotonicity. The
[second-test shape proof](SHORT_CENTRAL_SHAPE_F1.md) shows that the cost function can have only an interior minimum as a varies on [1,7/6]. Therefore its maximum, and hence the minimum of F1, occurs at a=1 or a=7/6. Its curvature numerator is kept as a factored source until three derivatives have reduced the degree to eight. The
[two terminal proofs](SHORT_CENTRAL_F1_TERMINALS.md) show the exact logarithmic tests decrease with x and establish the two scalar values at x=2 using the shared Padé logarithm bound. Both exceed 1/50000. This proves (3).

The norm-dependent route is necessary for the thin F0 endpoint. The constant norm 19/25 is used only in the independently proved F1 comparison.

## 3. The exact caller and duration conclusion

The caller is the central alternative in Section 3 of
[MIXED_SMALLER_SHORT_LOWER_RATIO_HAND_EXCLUSION](../../archive/notes/MIXED_SMALLER_SHORT_LOWER_RATIO_HAND_EXCLUSION.md).
Its central scale condition q_c≤1/7 is exactly 6a²≤x(x+2), so it supplies (1), the original incoming norm, and the same transport source used here.
The tangent bound remains
\[
 R_\tau\le\max\{R_2,R_2+(T-2)(w-3/4)\}\qquad(2\le\tau\le T),
\]
which follows from \(R_\tau'=w-U(1/\tau)\le w-3/4\).
It holds for either sign of w−3/4. The two entries on its right are exactly the costs in F0 and F1, so (3) gives (4).

Together with [the completed outer row](SHORT_OUTER_COMPLETE.md), both terminal alternatives in that caller now have small hand replacements. Its unchanged earlier corrected-cap comparison then contradicts the original competitive Casimir cap and proves x>2. This closes the lower-ratio S1 caller; the other separately listed scale, duration, ratio, displacement, derivative, and cost rows retain their own ledger entries.

## 4. Size and verification record

Every polynomial needed for the signs is printed in the linked notes. Dimension reduction is explicit: beta is removed first; the first shape sign uses the actual cap polynomial, with its division verified in one-variable coefficient identities; the second shape source is differentiated three times before expansion; its final shapes are constant.
No individual expanded polynomial identity has more than 45 monomials or degree greater than eight in one or two variables. The only three-variable expanded source is the degree-two D formula. The largest printed polynomial coefficient is 804306942456, twelve digits. Higher-degree rational sources are retained as product circuits and checked through their explicitly specified lower-degree coefficient or derivative identities, not as expanded sign premises.

There is one rational split, x=9/5, in the quantitative norm bound. The first test reuses the already completed outer terminal proof, including its simple existing split. There is no new parameter cover, generated coefficient table, numerical-extremum premise, or change to Lean source.

Independent exact-algebra checks reconstructed the original transport functions, norm/beta derivative identities, cap division, quotient/remainder bounds, third-derivative shape identities, endpoint derivatives, and directed scalar endpoint inequalities. The recovered norm note required one wording correction: its shifted-sign proof uses 0≤z≤1/2, not the unbounded interval z≥0. Its original stated domain and conclusion were unaffected.
No Lean, Lake, typechecking, or CI run was used or claimed.
