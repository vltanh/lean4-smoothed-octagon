# Final review of the unrestricted inequality and affine equality

Date: 2026-11-08 UTC. **Accepted at the stated hand-proof and external-input
boundary.** This independent review covers Sections 2, 5, 6 and 7 of
[the final hand theorem](HAND_COST_EQUALITY_THEOREM.md). It checks the
unrestricted competitor quantifier, the direct terminal count, both
terminal analytic comparisons, recovery of the original equality disk,
and the explicit external premises.

The finite-before-normal argument and the uniform exclusions that supply
\(N\le5\) have their separate reviews. The
[global dependency review](HAND_GLOBAL_DEPENDENCY_AUDIT.md) identifies
their place in the chain, and the
[smaller-short scope review](MIXED_SMALLER_SHORT_HAND_PERIOD_SCOPE_AUDIT.md)
checks the final previously missing whole-period interface. The
acceptance here does not use an executable cover or the older
computer-assisted exclusion as a substitute for any of those inputs.

## 1. Arbitrary measurable competitors are compared before classification

Let \(K_*\) be the balanced normalization of an actual geometric worst
disk, and retain the realization in
[ADMISSIBLE_REALIZATION](ADMISSIBLE_REALIZATION.md). Write \(A_*\)
for that realization's physical cost, equal to the normalized disk area.
For every integral-form admissible trajectory \(Q\), the
[reverse comparison](REVERSE_COMPARISON.md) supplies a normalized
balanced disk \(K_Q\) with

\[
\operatorname{area}(K_Q)\le C(Q).
\]

Geometric minimality of \(K_*\) therefore gives

\[
A_*=\operatorname{area}(K_*)
 \le\operatorname{area}(K_Q)\le C(Q).
\tag{1}
\]

The inequality is valid for every original admissible control, including
merely measurable controls. Below \(\pi\), the reconstruction preserves
area exactly; at or above \(\pi\), the concrete octagon supplies the
required disk. These two regimes cover the entire class.

The low-cost reconstruction does not presume that an arbitrary frame
already traverses a simple convex boundary. Its regularity and cyclic
extension give the actual frame and velocity at every seam. The
[winding argument](LOW_COST_WINDING.md) bounds the continuously lifted
angle of the reflected first row and selects its \(\pi/3\) increment.
The [geometric reconstruction](REVERSE_GEOMETRY.md) transfers this
winding to the first contact using the determinant-one obstruction to
opposite vectors. Strictly increasing contact angle then gives a single
simple traversal; the curvature inequality supplies convexity. Thus
neither simplicity nor finite switching has been inserted into (1).

The octagon competitor gives \(A_*\le A_{\rm oct}<\pi\). The subsequent
finite-representation and PMP arguments classify this actual minimizer.
Once that classification yields \(A_*=A_{\rm oct}\), equation (1)
immediately gives the unrestricted cost lower bound. Arbitrary competitors
are never required to carry a PMP lift, possess finite controls, or be
limits of a selected collection of finite words.

The equality argument has a definite order. First establish the
unrestricted inequality and hence the geometric minimum
\(\delta_{\rm oct}\). A given disk with density \(\delta_{\rm oct}\)
is then itself a worst disk. Apply the realization and comparison to
that disk, not to a replacement minimizer. Section 2 of the theorem now
states this order explicitly, so the worst-disk realization is invoked
only after its hypothesis is known.

## 2. The terminal count is an exact count through the twist

After zero durations are deleted and equal neighbors are merged,
including at the twisted seam, a genuine cut gives

\[
i_{j+N}=i_j+1\pmod3,\qquad i_{j+1}\ne i_j.
\]

The unique signs \(\epsilon_j\in\{-1,1\}\) of the label increments
therefore satisfy

\[
\sum_{j=0}^{N-1}\epsilon_j\equiv1\pmod3.
\tag{2}
\]

The last sign compares the final label with the twisted initial label.
It is not an ordinary periodic-word closing condition. Both labels and
active margins are transformed together, so the active-margin sequence
and the sign sequence are genuinely \(N\)-periodic.

The fixed-edge obstruction also applies to measurable controls. Its frame
has the form \(h(0)^{-1}h(T)\), where

\[
h(t)=\begin{pmatrix}1&-x(t)\\ z(t)&1-z(t)x(t)\end{pmatrix},
\qquad z(0)=0.
\]

The lower-left entry of \(g(T)=R\) gives \(z(T)=\sqrt3/2\);
the upper-left entry gives \(1+x(0)z(T)=1/2\), hence
\(x(0)=-1/\sqrt3\), contrary to strict star membership. This removes
the unswitched case and the one-piece case independently of normality.

The reverse-period theorem and the two-switch reverse-run theorem have
no lower period-length assumption. Their local necessary-PMP statements
apply through the genuine extension of the same normal covector, even
when a displayed local window crosses a short fundamental period.
They do not require a globally minimizing splice across several periods.

Now suppose \(N\le5\). Entirely reverse periods are excluded. Entirely
forward periods satisfy \(N\equiv1\pmod3\), so \(N=1\) or \(N=4\).
The former is impossible, and the latter has representative \(0120\).
For a mixed period, if there are \(m\) reverse runs and \(F\) forward
switches, then

\[
N=2m+F,\qquad F\ge m,\qquad N\ge3m.
\]

Thus \(m=1\). Equation (2) gives \(F-2\equiv1\pmod3\);
since \(1\le F\le3\), this forces \(F=3\), \(N=5\).
The sign order \((+,-,-,+,+)\) has labels
\(0,1,0,2,0,1\), whose last entry is the next twisted initial label.
The representative is exactly \(01020\).

This proves the coverage used in the theorem. It replaces the historical
word-generation table in Section 1 of the terminal audit; only the
analytic comparisons in its Sections 2 and 3 are needed afterward.

## 3. Both terminal costs retain arbitrary factors and the forced state

### Four positive pieces

For the relabeled word \(2012\), the tangent endpoint equation forces
alternating factors

\[
(q_1,q_2,q_3,q_4)=(1/a,1/b,1/a,1/b),
\quad a,b>0,\quad a^2+b^2=1.
\]

It does not assume them. The half-factor identity
\(RH=(2I+M)/(s+1)\), with \(s=a+b\), makes the state endpoint
equivalent to \([M,X_0]=0\). Its two independent entries and the positive
lower-left entry of the strict-star state select exactly
\(X_0=M/\sqrt{(s-1)(s+3)}\). Conversely this state endpoint and tangent
closure give the frame endpoint. No free initial-state parameter is
lost before comparing costs.

The per-arc cost integration uses the physical relation
\(q_i=\exp(2t_i/c_i)\) and the same objective \(C/\sqrt{12}\).
The cost formula in
[the terminal comparison](SMALL_PERIOD_COST_EQUALITY_AUDIT.md),
Section 2, is symmetric in \(a,b\), although the competitors need not be.
For \(a>b\), its derivative in \(1<s<\sqrt2\) is

\[
f'(s)=\frac{2}{N^2}
 \left(H(s)-\frac{s(s-1)^3}{s+1}\right),
\quad N=(s-1)(s+3),
\]

where

\[
H(s)=(s-1)^2\int_0^\infty
 \frac{2t-(s^2+1)}{(t+1)(t+a)(t+b)}\,dt.
\]

The displayed partial-fraction identity and derivative follow from the
explicit cost formula. Put \(k=1+ab\) and
\(W(t)=(t+1)^2/((t+a)(t+b))\). Both factors of \(W\) are positive and
strictly decreasing because \(0<a,b<1\). For \(t<k\) the negative
multiplier reverses the comparison; for \(t>k\) it does not. Hence

\[
(2t-2k)W(t)\le(2t-2k)W(k).
\]

After division by \((t+1)^3\), the integral is at most
\(W(k)(1-k)=-abW(k)<0\). The integrals converge. Thus \(f'(s)<0\)
throughout the asymmetric range. Continuity at \(a=b=1/\sqrt2\)
gives the unique minimum, and substitution gives \(\delta_{\rm oct}\).
The absent limits \(a=0\) or \(b=0\) cannot be positive finite factors.

### Five positive mixed pieces

Tangent closure for \(01020\) gives the complete positive-factor
parametrization

\[
\left(P(u),Q(u),
 \frac{4uv}{(1-u^2)(1-v^2)},Q(v),P(v)\right),
\quad0<u,v<1.
\]

The state endpoint again fixes the initial state through its
one-dimensional traceless centralizer; the opposite determinant-one
sign has negative margins and is excluded. The different factor of two
in the raw margin normalization is retained in the physical cost
formula of the terminal audit.

The scalar envelope has a short analytic sign. With
\(h(t)=-2t\log t/(1-t)-\log(1+t)\), its displayed derivative gives
\(th''(t)-h'(t)<0\). On \(t\le1/3\), its middle term is nonpositive;
on \(t>1/3\), the integral bound
\[
t-1-\log t\le(1-t)^2/(2t)
\]
leaves \((t^2-t-1)/(t(1+t)^2)<0\). Therefore
\(x\mapsto h(\sqrt x)\) is strictly concave. The exact logarithm
identity with
\(\alpha=2t/(1+t^2)\), \(\beta=(1-t^2)/(1+t^2)\),
\(\alpha^2+\beta^2=1\), gives the envelope's unique maximum at
\(t_*=\sqrt2-1\).

Put \(d=(1-u)(1-v)\), \(d_*=(2-\sqrt2)^2\). Positivity of the
middle duration is precisely \(u+v+uv>1\). With \(x=1-u\), \(y=1-v\),
this implies
\[
2\sqrt d\le x+y<1+d/2,
\]
and hence \(d<d_*\). The resulting scalar lower function \(B(d)\)
strictly decreases up to \(d_*\), since its derivative numerator is
\(4(4-M+\log d)-d<0\). The needed
\(M-\log d\ge(3+2\sqrt2)\log2>4\) follows from the displayed
rational lower bounds for \(\sqrt2\) and \(\log2\). Thus
\[
\delta(u,v)\ge B(d)>B(d_*)=\delta_{\rm oct}.
\]

The second inequality is strict even if the earlier concavity envelope
has equality. The limiting equality has \(u=v=t_*\) and middle factor
one; deletion then gives the four positive octagon factors. There is
no additional positive five-piece equality case.

These signs require hand algebra, integration and concavity only. The
companion exact scripts and the old enumeration output are unnecessary
for the deductions above.

## 4. Equality identifies the retained original disk

After the universal lower bound has been proved, let \(K\) be a given
disk with \(\delta(K)=\delta_{\rm oct}\). Since the concrete octagon
attains this value, \(K\) is itself a worst disk. Its own balanced
normalization, state, frame and boundary are retained through the
finite representation and terminal classification. Changing controls
on null sets and merging pieces preserve these objects.

The equality factors and state give

\[
N_0=2\sqrt2-1,\quad
X_0=\begin{pmatrix}0&-\sqrt{N_0}\\1/\sqrt{N_0}&0\end{pmatrix},
\quad c_i=2/\sqrt{N_0},
\]

in the rational basis. From \(q_i=\sqrt2=\exp(2t_i/c_i)\),
each physical duration is \(\log2/(2\sqrt{N_0})\). Conjugating back
gives \(\Phi(0,\sqrt{N_0/3})\). The constant-control vector fields
are smooth on the strict star, so successive ODE uniqueness identifies
the entire concrete octagon state and frame on all four arcs. Equality
of cost or of a terminal matrix alone would not suffice; these stronger
data are supplied.

Retain the disk normalization \(e\), the genuine cut \(s\), and the
cyclic relabeling \(C=R^r\). The classified frame is

\[
\widehat g(t)=C^{-1}G(s)^{-1}G(s+t)C.
\]

Since \(C\) permutes the six standard contacts, the union of its six
contact arcs is exactly the boundary of
\(C^{-1}G(s)^{-1}eK\). These arcs cover the full boundary by the
original cyclic contact relation. Their identification with the octagon
therefore gives equality of the compact convex radial hulls:

\[
C^{-1}G(s)^{-1}eK=K_{\rm oct},
\qquad K=e^{-1}G(s)C(K_{\rm oct}).
\tag{3}
\]

Every factor is invertible. Restoring the original centre permits a
translation. No artificial scalar comparison from the period exclusions
is substituted for the realization of \(K\).

For the converse, an invertible linear map sends \(K+\Lambda\) to
\(AK+A\Lambda\) and multiplies both area and lattice covolume by
\(|\det A|\). Applying the inverse map gives equality of the suprema
of lattice-packing densities. The declared Fejes Toth theorem then
transfers this equality to greatest packing density in the present
centrally symmetric planar class. This argument does not assume that
a general affine map sends rotated congruent packings to congruent
packings.

## 5. The external boundary is explicit and correctly restricted

The relevant statements were checked against the primary source,
Hales--Vajjha, [Packings of Smoothed Polygons, version 1](https://arxiv.org/html/2405.04331v1):

- [Chapter 2](https://arxiv.org/html/2405.04331v1#Ch2),
  Theorem 2.1.3 identifies greatest and lattice density for centrally
  symmetric planar convex disks; Theorem 2.2.2 supplies the
  critical-hexagon area ratio. Lemma 2.2.5 supplies existence and
  regularity of a worst disk. Lemmas 2.4.2--2.4.3 give the regular
  boundary parametrizations and Lipschitz tangents; Definition 2.4.7
  and its following discussion include normalized minimizers in the
  balanced class.
- [Chapter 5](https://arxiv.org/html/2405.04331v1#Ch5),
  Theorem 5.0.6 is the geometric area lower bound used by the compact-domain
  source audit. Its proof uses critical-hexagon minimality and convex
  hull area. The later bang-bang and basin results are not inputs.
- The standard free-time endpoint-submanifold and fixed-time edge
  maximum principles are explicit external results. The repository's
  PMP notes check their hypotheses and conventions.

The critical-hexagon density theorem excludes parallelograms in its
statement. That exception causes no gap: a parallelogram tiles with
density one, whereas the octagon has density less than one. Neither the
retained worst disk nor an equality disk can be that exception.

For the last item, the full system has a compact control simplex and
smooth state dynamics with denominators uniformly separated from zero
on the retained compact strict-star trajectory. The endpoint graph
retains the free initial state and its twisted terminal state. The
separate edge problem fixes its transformed independent-variable
interval and both state endpoints while leaving physical duration free.
It is not an unjustified restriction of a global multiplier.

The compact-domain audit proves the required all-time estimate using
the earlier geometric area bound, its repaired sector argument and exact
rational separation. It does not invoke later numerical basin or
finite bang-bang results. Likewise only the equality transport in
Section 6 of the historical window audit is retained; that note's older
published finite-representation premise is not used.

The accepted route therefore has no remaining terminal enumeration,
unrestricted-control approximation, or original-disk equality gap in
the sections reviewed here. Its mathematical external premises remain
those just identified. This is internal mathematical review, not
external peer review or Lean kernel certification. No Lean compilation,
Lake, typechecking or CI was performed.
