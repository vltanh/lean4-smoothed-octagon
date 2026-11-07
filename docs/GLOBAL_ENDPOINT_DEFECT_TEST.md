# An exact endpoint test for the full-period defect budget

Date: 2026-11-07. Hand algebra and a scoped dependency review. No Lean,
Lake, typechecking or CI. This note closes neither F nor M2.

## 1. What the review establishes

The complete-period cost--Casimir comparison uses the *physical* primary
costate and its conserved determinant, not an arbitrary multiplier for a
local state-closed action. Its conversion to the scalar switch-vector
normalization is

\[
\kappa^2=\det\Lambda_1=12\det U=12\gamma^2.
\]

The sign of the elliptic component reverses under the triangular
coordinate change. The free-initial-state boundary terms cancel only
with the actual twisted state and costate endpoints. These distinctions
are correctly retained in [GLOBAL_PERIODIC_PMP](GLOBAL_PERIODIC_PMP.md),
[GLOBAL_COST_CASIMIR](GLOBAL_COST_CASIMIR.md), and
[MIXED_GLOBAL_COSTATE_ELLIPTIC](MIXED_GLOBAL_COSTATE_ELLIPTIC.md).

The scalar angle counts and ordinary Jacobi inertia do not, by themselves,
prove a cost descent. The three frame constraints and their curvature are
present in [MIXED_GLOBAL_AUGMENTED_INDEX](MIXED_GLOBAL_AUGMENTED_INDEX.md).
The negative-index inequality left open there remains a substantive
missing theorem. No false normalization or endpoint cancellation was found
in these displayed interfaces during this review. This is not a full
review of every coefficient certificate or of the imported geometric
correspondence and compact-state theorem.

The following exact formula makes the complete-period defect test usable
without integrating the polar-angle derivative or finding a conjugating
matrix. It is a uniform necessary condition directly relevant to F1 and
M2.1, including unequal factors and weak ties.

## 2. Eliminate the elliptic conjugator exactly

Use physical coordinates, let

\[
J=\begin{pmatrix}0&-1\\1&0\end{pmatrix},\qquad
\lambda=-1,\qquad \kappa=\sqrt{\det\Lambda_1}>0,
\]

and assume the actual primary costate is negative elliptic. On a
subinterval \([s,t]\), set

\[
M=g(s)^{-1}g(t),\qquad \Lambda_s=\Lambda_1(s).
\]

Define two real numbers from endpoint matrices only:

\[
\boxed{
\begin{aligned}
A_{s,t}&=\operatorname{tr}\bigl[(I+J\Lambda_s/\kappa)M\bigr],\\
B_{s,t}&=\operatorname{tr}\bigl[(\Lambda_s/\kappa-J)M\bigr].
\end{aligned}}
\tag{1}
\]

Choose \(h\in\mathrm{SL}_2(\mathbb R)\) with
\(\Lambda_1(0)=-\kappa hJh^{-1}\), put \(G=h^{-1}g\), and use
\(z(G)=\operatorname{tr}G-i\operatorname{tr}(JG)\). The exact identity is

\[
\boxed{\overline{z(G(s))}\,z(G(t))=A_{s,t}+iB_{s,t}.}
\tag{2}
\]

Thus (1) computes the *relative* polar angle of the same fixed-conjugator
frame used in the complete-period comparison. It must not be replaced by
the polar angle of \(M\) alone.

Here is a direct proof with all conjugations retained. For arbitrary
\(2\)-by-\(2\) real matrices \(P,Q\),

\[
\begin{aligned}
\Re(\overline{z(P)}z(Q))
 &=\operatorname{tr}(P^TQ)+\operatorname{tr}(\operatorname{adj}(P)Q),\\
\Im(\overline{z(P)}z(Q))
 &=-\operatorname{tr}(P^TJQ)-\operatorname{tr}(\operatorname{adj}(P)JQ).
\end{aligned}
\tag{3}
\]

Both formulas follow by multiplying the four entries. With
\(P=G(s),Q=G(t)\), determinant one replaces \(\operatorname{adj}(P)\)
by \(P^{-1}\). The elliptic relation gives

\[
h^{-T}h^{-1}=J\Lambda_1(0)/\kappa,
\qquad hJh^{-1}=-\Lambda_1(0)/\kappa.
\]

Also \(g(s)^TJ=Jg(s)^{-1}\) and
\(g(s)^{-1}\Lambda_1(0)g(s)=\Lambda_s\). Consequently the four
terms in (3) are, respectively,

\[
\operatorname{tr}(J\Lambda_s M)/\kappa,\quad
\operatorname{tr}M,\quad
-\operatorname{tr}(JM),\quad
\operatorname{tr}(\Lambda_s M)/\kappa.
\]

Their sums prove (2). Since neither \(z(G(s))\) nor \(z(G(t))\)
vanishes, \(A_{s,t}\) and \(B_{s,t}\) cannot vanish together.

## 3. Select the correct angle branch from the cost budget

Let \(\vartheta\) be the continuous polar-angle lift for \(G\). The
identity proved in GLOBAL_COST_CASIMIR gives \(\vartheta'>0\), and
\(g(T)=R=\exp(\pi J/3)\) gives

\[
\vartheta(T)-\vartheta(0)=\pi/3+2\pi n,\qquad n\ge0.
\]

The sharper pointwise inequality independently checked below is

\[
3m_b\ge(\kappa+3/2)\vartheta'.
\tag{4}
\]

For a competitive period, \(C\le A_{\rm oct}<\pi\). If \(n\ge1\),
integration would give \(C>(3/2)(7\pi/3)=7\pi/2\), a contradiction.
Thus the same actual endpoint and cost budget imply
\(\vartheta(T)-\vartheta(0)=\pi/3\). This argument needs no additional
relative-homotopy assumption.

For \(0\le s<t\le T\), strict positivity of the derivative now gives

\[
0<\Delta\vartheta_{s,t}\le\pi/3,
\quad A_{s,t}>0,\quad B_{s,t}>0,
\quad
\boxed{\Delta\vartheta_{s,t}=\arctan(B_{s,t}/A_{s,t}).}
\tag{5}
\]

Equality in the upper bound occurs only for the full period. A proposed
proper window with nonpositive \(A\) or \(B\), or with a ratio exceeding
\(\sqrt3\), already fails this necessary complete-period branch test.
One must use the genuine physical interval and costate transport; a
hypothetical later switch preempted by a third control is not such a
window.

## 4. Independent audit of the stronger rotation bound

The proof in
[GLOBAL_SPECTRAL_COST_CASIMIR](GLOBAL_SPECTRAL_COST_CASIMIR.md)
is valid with the full hypotheses of GLOBAL_COST_CASIMIR. Here is the
independent normalization and strictness check.

Put \(Q=-JX>0\), \(P=G^{-1}G^{-T}>0\),
\(z=\|G\|_F^2/2\), and \(r=m_s/m_b>0\). Then

\[
\det P=1,\qquad \operatorname{tr}P=2z,\qquad
r=\frac{\operatorname{tr}(QP)}{\operatorname{tr}Q}.
\]

In an orthonormal eigenbasis of \(P\), the diagonal entries of
\(Q\) are strictly positive. Thus \(r\) is a convex combination
with positive weights of the two eigenvalues \(p,p^{-1}\), where
\(p\ge1\). The exact factorization

\[
p+p^{-1}-r-r^{-1}
=\frac{(p-r)(pr-1)}{pr}
\]

implies \(2z\ge r+r^{-1}\), strictly unless \(P=I\).
Also \(2\kappa r\le3\) by the actual Hamiltonian maximum. Therefore

\[
\vartheta'
=\frac{1+r}{z+1}m_b
\le\frac{2r}{1+r}m_b
\le\frac{3}{\kappa+3/2}m_b.
\]

This proves (4), with the physical cost density \(3m_b\). Equality
requires simultaneously \(G\in\mathrm{SO}_2\), \(r=1\), and
\(\kappa=3/2\). On an interval of equality, the equation
\(G'=GX\), together with \(\det X=1\) and \(X_{21}>0\), forces
\(X=J\). Full-period equality consequently gives the normal circle
with \(T=\pi/3\). For \(\kappa\ne3/2\), the pointwise inequality
is strict almost everywhere and its integral on any positive interval
is strict. This also justifies the strict competitive Casimir cap in
the new theorem.

Let \(C_{s,t}\) be the physical cost of the actual window and put
\(c_\kappa=\kappa+3/2\). Define

\[
\boxed{\mathcal D_{s,t}
=C_{s,t}-c_\kappa\Delta\vartheta_{s,t}.}
\tag{6}
\]

Writing \(F=3m_b-2\kappa m_s\ge0\) and
\(L=2z-r-r^{-1}\ge0\), the exact identity is

\[
3m_b-c_\kappa\vartheta'
=\frac{(r+1)F/(2r)+(3/2)m_b L}{z+1}\ge0.
\tag{7}
\]

All denominators are positive. Hence the defect is additive and
nonnegative. The complete-period cost cap and (5) imply

\[
\boxed{0\le\mathcal D_{s,t}
\le A_{\rm oct}-c_\kappa\pi/3.}
\tag{8}
\]

Combining (1), (5), and (8) eliminates both the elliptic conjugator
and the angular quadrature from the sharp completion test:

\[
\boxed{C\ge
C_{s,t}+\left(\kappa+\frac32\right)
\left(\frac\pi3-\arctan\frac{B_{s,t}}{A_{s,t}}\right).}
\tag{9}
\]

The complement may contain arbitrarily many arcs. Formula (9) is
independent of that count and preserves both the exact frame and the
same normal costate. A strict excess over \(A_{\rm oct}\) excludes the
entire candidate period, although the window alone may cost less than
\(A_{\rm oct}\) and its Casimir may satisfy the separate cap.

This is a necessary-condition test, not an endpoint-preserving competitor
or a proof of a negative constrained Hessian. To close F or M2 with it,
one must still prove a *uniform* lower bound for (9) on every actual
remaining minimum window, retaining first-event tests, singular limits,
and all asymmetric variables. A sampled excess is not such a proof.

## 5. Reproducibility and proof boundary

The companion
[`global_endpoint_defect_certificate.py`](../explorations/global_endpoint_defect_certificate.py)
checks the universal polynomial identities (3), the elementary
conjugator identity, and the reduction of (2) to (1) in arbitrary
symbolic determinant-one frame coordinates. The angle branch, positivity
and complete-period budget are the hand arguments above. No numerical
integration, length enumeration or claimed F/M2 closure is used.
