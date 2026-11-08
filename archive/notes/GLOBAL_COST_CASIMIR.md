# A complete-period cost bound for negative elliptic frame costates

Date: 2026-11-07. Hand proof; no Lean, Lake, typechecking, CI,
numerical trajectory, or symbolic certificate.

## Theorem and scope

Normalize a normal Pontryagin lift by \(\lambda=-1\). Use the original
physical-time equations and cost:

\[
J=\begin{pmatrix}0&-1\\1&0\end{pmatrix},\qquad
R=\exp(\pi J/3),\qquad
g'=gX,\qquad
C=-\frac32\int_0^T\operatorname{tr}(JX)\,dt.
\tag{1}
\]

Assume \(T>0\), \(g(0)=I\), \(g(T)=R\), and that \(X(t)\) belongs to
the positive determinant-one orbit:

\[
\operatorname{tr}X=0,\qquad \det X=1,\qquad X_{21}>0.
\tag{2}
\]

In addition, retain the actual strict-star control domain, the reduced
state-covector constraint \(\operatorname{tr}(WX)=0\), the frame-costate
equation
\(\Lambda_1'=[\Lambda_1,X]\), and the zero maximized Hamiltonian.
These are hypotheses of the full problem in
[GLOBAL_PERIODIC_PMP](GLOBAL_PERIODIC_PMP.md). Actual integral
Pontryagin trajectories have the needed continuity and absolute
continuity; no finite vertex representation is assumed.

Suppose \(\Lambda_1\) belongs to the **negative elliptic component**.
Precisely, put

\[
\kappa=\sqrt{\det\Lambda_1}>0,
\qquad
\Lambda_1(0)=-\kappa hJh^{-1}
\quad\text{for some }h\in\mathrm{SL}_2(\mathbb R).
\tag{3}
\]

Equivalently, \(\det\Lambda_1(0)>0\) and
\((\Lambda_1(0))_{21}<0\). The determinant and the component are
preserved by the frame-costate equation.

Then

\[
\boxed{\qquad C\ge\frac{4\pi\kappa}{2\kappa+3}.\qquad}
\tag{4}
\]

Consequently, a complete-period cost budget \(C\le C_0<\pi\) gives

\[
\boxed{
\kappa\le\frac{3C_0}{2(2\pi-C_0)}<\frac32,\qquad
\det\Lambda_1-\frac94
\le-\frac{9\pi(\pi-C_0)}{(2\pi-C_0)^2}<0.}
\tag{5}
\]

In particular, this applies with the known octagon budget
\(C_0=A_{\rm oct}<\pi\). A negative elliptic lift on the critical
normal slice \(\det\Lambda_1=9/4\) necessarily has \(C\ge\pi\).

The argument is for arbitrary complete PMP trajectories satisfying the
stated hypotheses, including measurable controls. It does not presume
global minimality, equal factors, a particular word, simple boundary
winding, or a previously proved switch bound. It uses neither
Hales--Vajjha Theorem 16.3.1 nor the numerical unstable-curve input
audited in [FINITE_BANG_BANG_SOURCE_AUDIT](FINITE_BANG_BANG_SOURCE_AUDIT.md).
The other components of the frame costate are not included in (4);
they must be treated separately when converting (5) into a clearance
for all minimizing lifts.

## 1. A stationary control gives a pointwise Hamiltonian comparison

The vertex matrices in the original coordinates are

\[
Z_0=\begin{pmatrix}0&1/3\\1&0\end{pmatrix},\quad
Z_1=\begin{pmatrix}1/\sqrt3&-2/3\\0&-1/\sqrt3\end{pmatrix},\quad
Z_2=\begin{pmatrix}-1/\sqrt3&-2/3\\0&1/\sqrt3\end{pmatrix}.
\tag{6}
\]

For a simplex control \(u\), write
\(Z_u=\sum_i u_iZ_i\) and
\(P_u=Z_u/\operatorname{tr}(Z_uX)\). With \(\lambda=-1\), the
reduced Hamiltonian is

\[
H(u)=\operatorname{tr}(\Lambda_1X)
       +\frac32\operatorname{tr}(JX)
       -\operatorname{tr}(WP_u),
\qquad \max_{u}H(u)=0.
\tag{7}
\]

Fix any state in (2), and write

\[
X=\begin{pmatrix}\alpha&\beta\\\gamma&-\alpha\end{pmatrix},
\qquad \gamma>0,\qquad
\beta=-\frac{1+\alpha^2}{\gamma}.
\]

Define three positive coefficients

\[
r_0=\gamma,\qquad
r_1=\frac{\gamma-3\beta+2\sqrt3\alpha}{4}
 =\frac{(\gamma+\sqrt3\alpha)^2+3}{4\gamma},\qquad
r_2=\frac{\gamma-3\beta-2\sqrt3\alpha}{4}
 =\frac{(\gamma-\sqrt3\alpha)^2+3}{4\gamma}.
\tag{8}
\]

Multiplying the three matrices in (6) by these coefficients gives

\[
X=\sum_i r_iZ_i,\qquad
\sum_i r_i=\frac32(\gamma-\beta)=3m_b,\qquad
m_b:=-\frac12\operatorname{tr}(JX)>0.
\tag{9}
\]

Thus \(u_i=r_i/(3m_b)\) is an interior simplex control, and

\[
Z_u=\frac{X}{3m_b},\qquad
\operatorname{tr}(Z_uX)=-\frac{2}{3m_b},\qquad
P_u=-\frac X2.
\tag{10}
\]

This is a pointwise comparison control. It need not equal the actual
maximizing control. Its state velocity is zero, and
\(\operatorname{tr}(WP_u)=0\) by the reduced-covector constraint.
Consequently (7) implies

\[
\boxed{\operatorname{tr}(\Lambda_1X)\le3m_b.}
\tag{11}
\]

There is no unproved assertion that the comparison control belongs to
the simplex: (8) proves strict positivity and (9) proves the
normalization. The maximum condition initially holds almost everywhere.
The three vertex Hamiltonians are continuous on the strict-star
trajectory, so their maximum is continuous and equals zero everywhere;
alternatively, its almost-everywhere form already suffices for all
integrals below.

## 2. Expressing the elliptic costate by a fixed left conjugation

The frame-costate equation and \(g'=gX\) give, almost everywhere,

\[
\frac d{dt}(g\Lambda_1g^{-1})
=g\bigl([X,\Lambda_1]+\Lambda_1'\bigr)g^{-1}=0.
\]

Absolute continuity therefore gives the exact spatial conservation law

\[
\Lambda_1(t)=g(t)^{-1}\Lambda_1(0)g(t).
\tag{12}
\]

For completeness, the conjugation in (3) is elementary. If
\(Y=-\Lambda_1(0)/\kappa
=\left(\begin{smallmatrix}\alpha&\beta\\\gamma&-\alpha\end{smallmatrix}\right)\)
has determinant one and \(\gamma>0\), then

\[
h=\begin{pmatrix}
1/\sqrt\gamma&\alpha/\sqrt\gamma\\
0&\sqrt\gamma
\end{pmatrix}
\quad\text{satisfies}\quad
\det h=1,\qquad hJh^{-1}=Y.
\tag{13}
\]

Fix such an \(h\), and put

\[
B=h^{-1}g,\qquad
m_s:=-\frac12\operatorname{tr}(J BXB^{-1}).
\tag{14}
\]

The quantities \(m_b,m_s\) are positive. Indeed, for every matrix \(X\)
in (2), the symmetric matrix \(-JX\) is positive definite: its first
diagonal entry is \(\gamma>0\), and its determinant is one.
For \(B\in\mathrm{SL}_2(\mathbb R)\),

\[
-J BXB^{-1}=B^{-T}(-JX)B^{-1}
\]

is positive definite as well. Their traces are \(2m_b\) and \(2m_s\).
This also proves directly that conjugation preserves the positive
component in (2).

By (3) and (12),

\[
\Lambda_1(t)=-\kappa B(t)^{-1}JB(t),\qquad
\operatorname{tr}(\Lambda_1X)=2\kappa m_s.
\]

The comparison (11) is consequently

\[
\boxed{2\kappa m_s\le3m_b.}
\tag{15}
\]

The fixed left multiplication defining \(B\) does not change its
right logarithmic velocity: \(B'=BX\). Its endpoints satisfy
\(B(T)=B(0)R\), although \(B(0)\) need not be \(I\).

## 3. The polar rotation and its exact derivative

For
\(B=\left(\begin{smallmatrix}a&b\\c&d\end{smallmatrix}\right)\)
of determinant one, define

\[
z(B)=(a+d)+i(c-b).
\tag{16}
\]

It never vanishes, because

\[
|z(B)|^2=(a+d)^2+(c-b)^2=\|B\|_F^2+2\ge4.
\tag{17}
\]

The last inequality follows from
\((a-d)^2+(b+c)^2=\|B\|_F^2-2\ge0\).
The argument of \(z(B)\) is the rotation angle of the polar factor of
\(B\), but that interpretation is not a premise: all that is needed is
the explicit expression (16).

Choose a continuous real lift \(\theta(t)\) of
\(z(B(t))/|z(B(t))|\). Such a lift can be constructed directly by
choosing \(\theta(0)\) and integrating
\(\operatorname{Im}(\overline z z')/|z|^2\). Differentiation shows
that the resulting \(e^{i\theta}\) equals \(z/|z|\).

The derivative is the exact identity

\[
\boxed{
\theta'=\frac{2(m_b+m_s)}{\|B\|_F^2+2}>0.}
\tag{18}
\]

Here is a coordinate check. With
\(X=\left(\begin{smallmatrix}\alpha&\beta\\
\gamma&-\alpha\end{smallmatrix}\right)\) and \(B'=BX\),

\[
\begin{aligned}
\operatorname{Im}(\overline z z')
&=2\alpha(ab+cd)
  +\gamma(1+b^2+d^2)-\beta(1+a^2+c^2),\\
2m_b&=\gamma-\beta,\\
2m_s&=2\alpha(ab+cd)
       +\gamma(b^2+d^2)-\beta(a^2+c^2).
\end{aligned}
\]

The first line is the sum of the last two, proving (18) after (17).
There is no appeal here to an assumed primary winding of a boundary
curve.

Right multiplication by a rotation has a particularly simple effect:
for every real \(\varphi\),

\[
z(B\exp(\varphi J))=e^{i\varphi}z(B).
\tag{19}
\]

This follows by multiplying the two matrices in (16). Since
\(B(T)=B(0)R\), (19) gives

\[
\theta(T)-\theta(0)=\frac\pi3+2\pi n
\quad\text{for some }n\in\mathbb Z.
\]

Equation (18) and \(T>0\) make this increment positive. Therefore
\(n\ge0\), and

\[
\boxed{\theta(T)-\theta(0)\ge\frac\pi3.}
\tag{20}
\]

In particular, (20) uses the exact full matrix endpoint. No assumption
that a trace equation alone enforces that endpoint has been made.

## 4. Integrating the comparison

Combining (15), (17), and (18) gives

\[
\theta'
\le\frac{m_b+m_s}{2}
\le\frac{2\kappa+3}{4\kappa}\,m_b.
\tag{21}
\]

The physical cost in (1) is \(C=3\int_0^T m_b\,dt\).
Integration of (21), followed by (20), yields

\[
\frac\pi3
\le\theta(T)-\theta(0)
\le\frac{2\kappa+3}{12\kappa}\,C.
\]

This proves (4). The reasoning also explains why the critical value
\(\kappa=3/2\) gives the circle threshold \(\pi\): at that value
(15) is \(m_s\le m_b\), so (21) reduces to \(\theta'\le m_b\).

Now assume \(C\le C_0<\pi\). Rearranging (4), with all denominators
positive, gives

\[
(4\pi-2C_0)\kappa\le3C_0,
\qquad
\kappa\le\frac{3C_0}{2(2\pi-C_0)}<\frac32.
\]

Squaring and subtracting \(9/4\) gives exactly (5), since

\[
\frac94-\frac{9C_0^2}{4(2\pi-C_0)^2}
=\frac{9\pi(\pi-C_0)}{(2\pi-C_0)^2}.
\tag{22}
\]

## 5. Homogeneous form and its numerical clearance application

The normal multiplier need not initially be normalized to \(-1\).
For \(\lambda=-\mu<0\), let
\(\kappa_{\rm phys}=\sqrt{\det\Lambda_1}\) in the same negative
elliptic component. Divide all costates and the cost multiplier by
\(\mu\). Applying (4) to
\(\kappa=\kappa_{\rm phys}/\mu\) gives

\[
C\ge
\frac{4\pi\kappa_{\rm phys}}{2\kappa_{\rm phys}+3\mu}.
\tag{23}
\]

For \(C\le C_0<\pi\), the invariant in
[GLOBAL_CASIMIR_CLEARANCE](GLOBAL_CASIMIR_CLEARANCE.md) therefore obeys

\[
\boxed{
\Delta=\det\Lambda_1-\frac94\lambda^2
\le-\mu^2\delta(C_0),\qquad
\delta(C_0):=\frac{9\pi(\pi-C_0)}{(2\pi-C_0)^2}>0.}
\tag{24}
\]

This is an explicit gap relative to the square of the multiplier.
An actual-covector normalization must still be retained when converting
it to a common numerical phase clearance. The small-multiplier sector
is handled separately in
[GLOBAL_SMALL_MULTIPLIER_BOUND](GLOBAL_SMALL_MULTIPLIER_BOUND.md).
Positive elliptic, nonelliptic, and abnormal costates must also be
accounted for in a complete conversion. This note does not silently
apply the negative-component hypothesis to those cases.
[GLOBAL_NUMERICAL_REDUCTION](GLOBAL_NUMERICAL_REDUCTION.md) now completes
that conversion, including every normal orbit type and abnormal lifts,
and proves the original explicit universal clearance and E4 piece bound.
The independent homogeneous argument in
[SINGULAR_COST_BUDGET](SINGULAR_COST_BUDGET.md) subsequently sharpens these
to D>10^-11 and N<10^56 using the full twisted-period seam, algebraic
covector bounds, and the direct measurable-edge proof. Both arguments
are preserved; neither supplies the final global cost comparison.

The proof adds a constraint absent from the unsuccessful relaxations in
[GLOBAL_CALIBRATION](GLOBAL_CALIBRATION.md): it uses the conserved
negative elliptic frame costate and the comparison forced by the
zero maximized Hamiltonian. An arbitrary positive frame path with the
same endpoint need not admit such a costate comparison. Thus its cost
can be below the right-hand side of (4) without contradicting this
theorem. Similarly,
[NEAR_CIRCLE_BOUND](NEAR_CIRCLE_BOUND.md) controls a whole state tube,
whereas (24) controls a conserved costate invariant; no identification
of those two restrictions is assumed.

## 6. Exact defect and equality in the cost--Casimir bound

### 6.1 Three nonnegative defects

Retain \(\lambda=-1\), the same fixed conjugator \(h\), and the real
angle lift from Section 3. Define the stationary-control slack

\[
F(t)=3m_b(t)-2\kappa m_s(t)\ge0,\qquad
Q(t)=\|B(t)\|_F^2+2.
\tag{25}
\]

The inequality for \(F\) is precisely (15). It also has the
Hamiltonian interpretation
\(F=\max_i\{-\operatorname{tr}(WP_i)\}\).
Indeed, every simplex Hamiltonian is a weighted average of the
vertex Hamiltonians: its weights are
\(u_i\gamma_i/\sum_j u_j\gamma_j\), where
\(\gamma_i=-\operatorname{tr}(Z_iX)>0\).
Thus (7) identifies the vertex maximum with zero.

Substitution of \(2\kappa m_s=3m_b-F\) into (18) gives the pointwise
identity

\[
(2\kappa+3)m_b=\kappa Q\theta'+F.
\]

Using \(C=3\int_0^T m_b\,dt\) and
\(\theta(T)-\theta(0)=\pi/3+2\pi n\), with \(n\ge0\), yields

\[
\boxed{
\begin{aligned}
(2\kappa+3)C-4\pi\kappa
={}&24\pi\kappa n\\
 &+3\kappa\int_0^T
       \bigl(\|B(t)\|_F^2-2\bigr)\theta'(t)\,dt\\
 &+3\int_0^T F(t)\,dt .
\end{aligned}}
\tag{26}
\]

All three terms on the right are nonnegative: \(\kappa>0\),
\(n\ge0\), \(\|B\|_F^2\ge2\), \(\theta'>0\), and \(F\ge0\).
This is an exact identity, not a Taylor expansion or a discarded
remainder estimate. A different permitted choice of \(h\) changes
\(B\) by a fixed left rotation, so it changes neither its Frobenius
norm nor \(\theta'\) or \(m_s\).

### 6.2 Equality forces the normal circle lift

For the classification of the actual control, retain explicitly the
full state equation \(X'=[P_u,X]\) and the traceless reduced costate
\(W\), as in the actual PMP problem. Then equality in (4) holds
if and only if

\[
\boxed{
\begin{gathered}
\kappa=\frac32,\qquad T=\frac\pi3,\qquad
X(t)=J,\qquad g(t)=\exp(tJ),\\
\Lambda_1(t)=-\frac32J,\qquad W(t)=0,\qquad
u(t)=\left(\frac13,\frac13,\frac13\right)
\quad\text{almost everywhere}.
\end{gathered}}
\tag{27}
\]

The state, frame, and costate equalities in (27) hold at every time;
only the control is specified up to a null set.

To prove necessity, equality in (4) makes the left side of (26)
zero, so \(n=0\) and both integrals vanish. Their integrands are
continuous and nonnegative, and \(\theta'\) is everywhere positive.
Therefore

\[
\|B(t)\|_F^2=2,\qquad F(t)=0
\quad\text{at every }t.
\]

For a determinant-one matrix,
\(\|B\|_F^2-2=(a-d)^2+(b+c)^2\).
Hence \(a=d\), \(c=-b\), and \(a^2+b^2=1\), so
\(B(t)\in\mathrm{SO}_2(\mathbb R)\).
Its lifted angle in (16) is its rotation angle. Consequently
\(B'=B\theta'J\), and comparison with \(B'=BX\) gives
\(X=\theta'J\). The determinant and positive-orbit conditions in
(2) now imply \((\theta')^2=1\) and \(\theta'>0\), so
\(\theta'=1\). Since \(n=0\), (20) is
\(T=\theta(T)-\theta(0)=\pi/3\).

Also \(B(0)=h^{-1}\) is orthogonal, so \(h\) is a rotation and
\(\Lambda_1=-\kappa J\). With \(X=J\) and \(B\) a rotation,
\(m_b=m_s=1\). Thus \(F=0\) is \(3-2\kappa=0\), proving
\(\kappa=3/2\). The initial frame condition and \(g'=gJ\)
give \(g(t)=\exp(tJ)\).

It remains to identify \(W\) and the control. The stationary
comparison control at \(X=J\) is the strictly interior centroid.
Its Hamiltonian is zero because \(F=0\); all three vertex
Hamiltonians are nonpositive and their weighted average is zero.
The weights are positive, so every vertex Hamiltonian vanishes.
Here \(A=0\) and \(P_i=-3Z_i/2\), hence
\(\operatorname{tr}(WZ_i)=0\) for all three \(i\).
For a traceless matrix
\(W=\left(\begin{smallmatrix}a&b\\c&-a\end{smallmatrix}\right)\)
these three measurements are

\[
b+\frac c3,\qquad
\frac{2a}{\sqrt3}-\frac{2c}{3},\qquad
-\frac{2a}{\sqrt3}-\frac{2c}{3}.
\]

Their vanishing gives \(c=0\), then \(a=0\) and \(b=0\).
Thus \(W=0\) at every time.

Finally, \(X'=0\) and the actual state equation imply
\([P_u,J]=0\) almost everywhere. A traceless matrix commuting
with \(J\) is a multiple of \(J\); since
\(\operatorname{tr}(P_uJ)=1\), this multiple is \(-1/2\).
For \(X=J\), every simplex control has
\(\operatorname{tr}(Z_uJ)=-2/3\), so \(P_u=-J/2\)
is equivalent to \(Z_u=J/3\). Comparing the lower-left and
diagonal entries of (6) gives \(u_0=1/3\) and \(u_1=u_2\);
the simplex sum then gives the stated centroid almost everywhere.

Conversely, the functions in (27), with \(\lambda=-1\), satisfy
the state equation, frame equation, both reduced adjoint equations,
and every vertex Hamiltonian is zero. Indeed \(P_u=-J/2\)
commutes with \(X=J\), \(\Lambda_1\) commutes with \(X\),
and \(A=W=0\). The full twisted state and costate endpoints hold
because all these constant matrices commute with \(R\).
The multiplier is nontrivial, \(C=3T=\pi\), and the right side
of (4) is \(\pi\), proving equality.

For the homogeneous inequality (23), equality is precisely the
positive rescaling of (27):
\(\lambda=-\mu\), \(\Lambda_1=-(3/2)\mu J\), and \(W=0\),
with the same state, frame, time, and control.

This classifies equality in the cost--Casimir bound only. In
particular, it is incompatible with the competitive budget
\(C\le A_{\rm oct}<\pi\). It is not an octagon equality theorem,
an affine-uniqueness result for Reinhardt minimizers, or a completion
of the remaining finite comparison.

### 6.3 The determinant gap does not force a local switching direction

A short exact diagnostic prevents a stronger pointwise conclusion.
Put
\[
E=\begin{pmatrix}1&0\\0&-1\end{pmatrix},\qquad
K=\begin{pmatrix}0&1\\1&0\end{pmatrix},\qquad w=\frac1{10},
\]
and consider either of the phases
\[
X=J,\quad \lambda=-1,\quad
W=w(\sqrt3E+K),\quad
A=wJ+r(\sqrt3E+K),\qquad r=\pm\frac{\sqrt6}{5}.
\tag{28}
\]
Both satisfy \(\operatorname{tr}(WX)=0\), and
\(\Lambda_1=A-(3/2)J\) is negative elliptic with
\[
\det\Lambda_1=(3/2-w)^2-4r^2=1<(313/210)^2.
\]

At \(X=J\),
\[
P_0=-\frac J2-K,\quad
P_1=-\frac J2-\frac{\sqrt3}{2}E+\frac K2,\quad
P_2=-\frac J2+\frac{\sqrt3}{2}E+\frac K2.
\]
Direct substitution gives \(H_0=H_1=0\) and \(H_2=-6w<0\).
Thus exactly controls \(0\) and \(1\) maximize. For
\(\chi=H_1-H_0=-\operatorname{tr}(W(P_1-P_0))\),
differentiate along either active constant-control flow. To check
the result, write \(A=wJ+uE+vK\), with \(u=\sqrt3r\), \(v=r\),
and \(Q=P_1-P_0\). The equations give, on either side,
\[
\operatorname{tr}(W'Q)=6u+2\sqrt3v,\qquad
\operatorname{tr}(WQ')=4\sqrt3w.
\]
Consequently
\[
\boxed{\chi'=-4\sqrt3(w+2r).}
\tag{29}
\]

For \(r<0\), this is a transverse forward switch \(0\to1\);
for \(r>0\), it is a transverse reverse switch \(1\to0\).
The strict gap to the third vertex and the nonzero derivative
persist on sufficiently short adjacent pieces. The smooth
constant-control Hamiltonian flows therefore give genuine local
PMP segments with these switches.

No full-period frame, state, or costate closure is asserted for
either segment, and no minimizing claim is made. The example is
not a counterexample to a global switch reduction. It shows only
that the determinant gap alone cannot give a pointwise
forward-only rule; such a rule would need an additional
closure-sensitive or variational argument.

### 6.4 A cubic reverse switch also lies below the determinant cap

The determinant gap does not by itself imply transverse switching.
Here is an exact local example, again with no claimed complete-period
closure. Put \(q=1/\sqrt3\) and choose \(0<\eta<3/4\). At the
switch take

\[
g_0=I,\quad X_0=J,\quad \lambda=-1,\quad
W_0=-2\eta K,\qquad
\Lambda_{1,0}=
\begin{pmatrix}0&3/2\\2\eta-3/2&0\end{pmatrix}.
\tag{30}
\]

These data satisfy \(H_1=H_2=0\), \(H_0=-6\eta<0\), and
\(\det\Lambda_1=9/4-3\eta>0\), with negative elliptic orientation.
For \(\eta=1/10\), the determinant is \(39/20<(313/210)^2\).

Solve the full physical state and adjoint equations from (30), using
control 2 backward from the switching time and control 1 forward.
Their smooth constant-control vector fields give local solutions in
strict star. The following pullback of those actual equations determines
whether the prescribed controls maximize and the order of the tie. Write
\[
X=\Phi(x,y)=\frac1y
\begin{pmatrix}x&-(x^2+y^2)\\1&-x\end{pmatrix},
\]
and use \(x\) as time on controls \(\{1,2\}\);
its physical derivative is \(dx/dt=y>0\).
With \(v=y^{-2}\), the edge frame based at \(g_0=I\) is

\[
g=L_sU_{-x},\qquad
L_s=\begin{pmatrix}1&0\\s&1\end{pmatrix},\quad
U_{-x}=\begin{pmatrix}1&-x\\0&1\end{pmatrix},\qquad
\frac{ds}{dx}=v.
\]

This follows directly by differentiating \(L_sU_{-x}\) and using
\(dg/dx=gX/y\). In this clock,
\(dv/dx=a_i(x)v\), where
\(a_1(x)=2/(q-x)\) and \(a_2(x)=-2/(q+x)\).
The physical cost per unit \(x\) is
\((3/2)[1+(1+x^2)v]\). Consequently the edge Hamiltonian for
the coordinates \((s,v)\) is

\[
\mathscr H_i
=p_s v+p_v a_i(x)v-\frac32[1+(1+x^2)v].
\]

The embedding \((s,x,v)\mapsto(L_sU_{-x},\Phi(x,v^{-1/2}))\)
is invariant under both edge vector fields. Restricting the actual
cotangent vector to this invariant manifold therefore gives the
canonical adjoint for its coordinates. With the \(x\)-covector
restored, the exact physical Hamiltonian is
\[
H_i=y\,[p_x+\mathscr H_i].
\]
Because \(H_i=0\), the factor \(p_x+\mathscr H_i\) vanishes.
It cancels the additional derivative-of-\(y\) term when changing to
the \(x\) clock, giving \(p_v'=-\partial_v\mathscr H_i\) and
\(p_s'=0\). Consequently, on either control,

\[
\frac{d}{dx}(p_vv)
=\left(\frac32(1+x^2)-p_s\right)v.
\tag{31}
\]

At (30), the frame coordinate gives
\(p_s=\operatorname{tr}(\Lambda_{1,0}E_{21})=3/2\).
The perpendicular state-covector representative is
\(\Lambda_{2,0}=[J,W_0]/4=\eta E\).
Since \(\Phi_y(0,1)=-K\), its \(y\)-covector is zero and
therefore \(p_v(0)=0\). Thus \(z=p_vv\) satisfies the exact formula

\[
z(x)=\frac32\int_0^x \xi^2v(\xi)\,d\xi.
\tag{32}
\]

Choose control \(2\) before zero and control \(1\) after zero.
The state equations have \(y(x)=1-|x|/q>0\) on a sufficiently
small interval, so \(v\) is continuous with \(v(0)=1\).
Equation (32) gives \(z<0\) for \(x<0\), \(z>0\) for \(x>0\),
and \(z(x)=x^3/2+o(x^3)\).
Moreover
\[
\mathscr H_1-\mathscr H_2
=\frac{4q}{q^2-x^2}\,z.
\]
The physical Hamiltonian difference has the same sign, since it
is multiplied by the positive clock speed \(y\). The prescribed
controls therefore maximize over the edge on their respective
sides. The strict gap to control \(0\) at (30) persists locally,
and each active physical Hamiltonian stays zero by autonomous Hamiltonian
conservation. Thus the constructed full lift is a genuine all-control PMP
segment with a cubic reverse switch \(2\to1\), not a transverse one.
More explicitly, \(x'(0)=1\) and
\[
H_1-H_2=2\sqrt3\,x^3+o(x^3)
       =2\sqrt3\,t^3+o(t^3).
\]
The two analytic one-sided expansions have the same cubic term, so the
first and second derivatives vanish at the switch and the third is
\(12\sqrt3>0\).

This example concerns only a local segment. It imposes neither the
complete frame/state/costate endpoints nor global minimizing
conditions. It shows that a further argument must justify any
simple-switch hypothesis in a proposed global index or pattern
reduction; the numerical determinant cap alone does not justify it.

## Inputs and validation boundary

The frame dynamics, cost, reduced Hamiltonian, spatial conservation,
and normal rescaling are the established optimal-control formulation;
see Hales--Vajjha, *Packings of Smoothed Polygons*,
[Sections 3.2 and 6.4--6.7](https://arxiv.org/html/2405.04331v1#Ch6.S4),
and the exact endpoint audit in
[GLOBAL_PERIODIC_PMP](GLOBAL_PERIODIC_PMP.md).
The displayed theorem is derived here from those equations by
the explicit stationary-control coefficients, a two-by-two matrix
calculation, and an integrated angle inequality.

The proof neither uses nor verifies the unstable-curve computations
in the source, and it does not require a finite bang-bang theorem.
It gives no comparison of the remaining finite words and no affine
uniqueness theorem. The unrestricted Reinhardt comparison and Lean
kernel validation are separate from this costate estimate.

Independent internal hand reviews by the root, the source/geometry
reviewer, and the optimal-control reviewer checked the stationary
simplex control, conservation and conjugation signs, direct polar
identity, lifted endpoint angle, cost inequality, and homogeneous
determinant gap. Both specialist reviewers also read the assembled
note in full. No material issue was found; this review is not Lean
kernel validation.

The Section 6 follow-up also received independent internal reviews of
its assembled argument. These checked the exact defect, continuous
nonnegative-integrand equality argument, normal circle lift and converse,
homogeneous scaling, both active-side derivatives in the transverse
example, and the full cotangent pullback and positive-clock reduction
in the cubic example. The latter's actual physical Hamiltonian stays
zero, and its third-control gap is strict on a sufficiently short
interval. No additional global competitor class is excluded by these
local diagnostics. No Lean, Lake, typechecking, or CI was run.
