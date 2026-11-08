# A stronger whole-period cost--Casimir and continuation budget

Date: 2026-11-07 UTC. Hand proof. No Lean, Lake, typechecking, or CI.

## Result and scope

Under the full physical hypotheses of
[GLOBAL_COST_CASIMIR](GLOBAL_COST_CASIMIR.md), with normal physical cost
multiplier `lambda=-1` and negative elliptic primary costate of invariant
size `kappa>0`, one has the stronger estimate

\[
\boxed{C\ge \frac\pi3\left(\kappa+\frac32\right).}
\tag{1}
\]

Equality is possible only when `kappa=3/2` and the trajectory is the circle
`g(t)=exp(tJ), X(t)=J, T=pi/3` in the stated normalization. In particular,
for every competitive trajectory with `C<=A_oct<pi`,

\[
\boxed{\kappa<\frac{3A_{\rm oct}}\pi-\frac32<\frac32.}
\tag{2}
\]

This applies to complete measurable-control PMP trajectories, without a
vertex word, positive-duration lower bound, transversality, endpoint rank,
or equal-factor assumption. It supplies an exact nonnegative budget on
**every** continuation window. It does **not** exclude all M2 periods or
close F; a uniform lower bound on the defect consumed by the remaining
M2 domain is still needed.

The new ingredient is the spectral relation between the same state and
costate already present in the polar-angle proof. The old proof bounded
the Frobenius norm and stationary-control comparison separately. Retaining
their relation gives (1).

## 1. The same physical quantities

Use exactly the notation of the cited theorem:

\[
\Lambda_1(0)=-\kappa hJh^{-1},\quad B=h^{-1}g,\quad
m_b=-\tfrac12\operatorname{tr}(JX),\quad
m_s=-\tfrac12\operatorname{tr}(JBXB^{-1}),
\]
\[
z=\tfrac12\|B\|_F^2\ge1,\qquad r=m_s/m_b>0.
\tag{3}
\]

The pointwise stationary-control comparison, actual polar-angle identity,
and physical cost density are

\[
2\kappa m_s\le3m_b,\qquad
\theta'=\frac{m_b+m_s}{z+1}>0,\qquad C'=3m_b.
\tag{4}
\]

Here `theta` is the continuous argument of
`(B11+B22)+i(B21-B12)`. The complete twisted frame endpoint gives

\[
\Delta\theta=\pi/3+2\pi n,\qquad n\ge0.
\tag{5}
\]

All these are established in the original cost--Casimir proof with the
same actual primary multiplier. No new covector is fitted to a window.

## 2. An exact spectral inequality

The matrix `Q=-JX` is positive definite with determinant one. By the
same conjugation identity as in the original proof,

\[
2m_b=\operatorname{tr}Q,\qquad
2m_s=\operatorname{tr}(B^{-T}QB^{-1})
=\operatorname{tr}(Q B^{-1}B^{-T}).
\tag{6}
\]

The positive definite matrix `P=B^{-1}B^{-T}` has determinant one and
trace `2z`; its eigenvalues are `p` and `p^{-1}`, with `p>=1`.
In an orthonormal eigenbasis, the two diagonal entries of `Q` are strictly
positive. Consequently `r=tr(QP)/tr(Q)` is a weighted average of
`p,p^{-1}`, with both weights strictly positive. Therefore

\[
p^{-1}\le r\le p,
\qquad r+r^{-1}\le p+p^{-1}=2z.
\tag{7}
\]

If `p>1`, both inequalities in the first pair are strict, and hence so is
the last inequality. If `p=1`, then `z=r=1`. Thus, with

\[
L=2z-r-r^{-1},
\]

one has `L>=0`, and `L=0` if and only if `B` is orthogonal. This strict
statement uses that `Q` is positive definite, not merely semidefinite.

The elementary implication in (7) follows directly from

\[
p+p^{-1}-r-r^{-1}
=\frac{(p-r)(pr-1)}{pr}\ge0.
\tag{8}
\]

## 3. Pointwise rotation per unit cost

Equation (7) gives

\[
z+1\ge\frac{(r+1)^2}{2r}.
\]

Thus (4) implies

\[
\theta'\le\frac{2r}{r+1}m_b.
\]

The function `r/(r+1)` is strictly increasing, and (4) gives
`r<=3/(2kappa)`. Hence

\[
\boxed{3m_b\ge(\kappa+3/2)\theta'.}
\tag{9}
\]

This argument works for every `kappa>0`; it does not first assume a
subcritical Casimir. Integrating (9) and then using (5) proves (1).

For clarity, the improvement over the old estimate has exact size

\[
\frac\pi3(\kappa+3/2)
-\frac{4\pi\kappa}{2\kappa+3}
=\frac{\pi(2\kappa-3)^2}{6(2\kappa+3)}\ge0.
\tag{10}
\]

## 4. Equality and strictness

If equality holds in (9), equality must hold in both scalar comparisons.
The spectral equality forces `B` orthogonal and `r=1`. The
stationary-control equality then gives `2kappa=3`. Consequently, for
`kappa!=3/2`, (9) is strict at every time at which the differential
identities hold, and its integral on every positive interval is strict.

If equality holds in the complete estimate (1), then `kappa=3/2`,
`B` is orthogonal almost everywhere, and `n=0` in (5). Continuity puts
`B` in `SO(2)` throughout. Since `B'=BX`, its right logarithmic velocity
`X` is skew symmetric almost everywhere. Together with `det X=1` and
`X21>0`, this forces `X=J`. Therefore `g(t)=exp(tJ)` from `g(0)=I`,
and `n=0` gives `T=pi/3`. Conversely this circle attains equality with
the usual normal primary costate `Lambda1=-3J/2` and zero reduced
state covector. This proves the equality assertion.

If `C<=A_oct<pi`, (1) first gives `kappa<3/2`; strictness at that
subcritical value then gives (2).

## 5. Exact defect accounting on every continuation interval

Let

\[
F=3m_b-2\kappa m_s\ge0,
\qquad L=2z-r-r^{-1}\ge0.
\]

Direct use of `z+1=(r+1)^2/(2r)+L/2` gives the identity

\[
\boxed{
3m_b-(\kappa+3/2)\theta'
=\frac{\frac{r+1}{2r}F+\frac32m_b L}{z+1}\ge0.
}
\tag{11}
\]

This retains separately the stationary-control gap and the spectral
misalignment gap. Neither term is an independent numerical assumption.
For any subinterval `I=[t0,t1]`, define

\[
\mathcal D_I=C_I-(\kappa+3/2)
[\theta(t_1)-\theta(t_0)].
\]

It is additive on consecutive intervals and nonnegative. It follows that
any window contained in a competitive complete trajectory satisfies

\[
\boxed{
0\le\mathcal D_I\le
A_{\rm oct}-(\kappa+3/2)\pi/3.
}
\tag{12}
\]

In fact a competitive period has `n=0`: if `n>=1`, then (9) and
`kappa>0` would give `C> (3/2)(7pi/3)>pi`, contrary to its cost cap.
Thus the necessary completion test can be written as

\[
\boxed{
C_I+(\kappa+3/2)(\pi/3-\Delta\theta_I)
\le A_{\rm oct}.}
\tag{13}
\]

This test uses the angle of the actual fixed-conjugation frame, with its
continuous increasing lift. A principal argument alone must not silently
replace that lift. It remains valid across arbitrarily many switches and
for windows cut inside arcs. A window with `Delta theta_I>pi/3` is already
excluded by positive angular velocity.

The older pointwise estimate used the coefficient
`b_old=12kappa/(2kappa+3)` in place of `kappa+3/2`. Their difference is

\[
\kappa+3/2-b_{\rm old}
=\frac{(2\kappa-3)^2}{2(2\kappa+3)}\ge0.
\]

Hence (13) is at least as strong for every feasible proper window, since
`0<=Delta theta_I<=pi/3`. It still needs a **uniform M2 lower bound** or
an invariant first-event argument to exclude every smallest reverse
centre touching a nonshort forward run. No such bound is proved here.

## Supplementary exact algebra check

[`global_spectral_cost_casimir_certificate.py`](../explorations/global_spectral_cost_casimir_certificate.py)
checks (8), (10), (11), and the completion-coefficient comparison by
exact symbolic identities. The positivity, actual PMP interface,
measurable-trajectory extension, winding, and equality analysis are the
hand argument above. No sampled sign or numerical optimization is used.
