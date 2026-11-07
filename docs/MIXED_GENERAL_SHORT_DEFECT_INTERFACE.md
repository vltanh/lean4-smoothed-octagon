# A rational endpoint interface for a general short bridge

Research checkpoint, 2026-11-07. The identities in Sections 1--4 are
exact. They provide a two-turn-window input to the global spectral
defect inequality. Section 6 records numerical discovery and an
obstruction to a weaker proposed reduction; it is not an exclusion of
M2. No Lean, Lake, typechecking or CI was used.

## 1. Actual data and orientation

At a globally smallest reverse centre of physical active margin `a`,
write an incoming short bridge as

\[
(a\alpha,a\beta,ax,a),\qquad
1\le\alpha<x\le\beta\le\alpha x.
\]

The other adjacent turn is `ay`, with `x<=y`. Put

\[
\rho=\frac{a^2}{a^2+4},\quad U=\frac{1-\rho}{\rho}=\frac4{a^2},
\quad S=1+x,\quad A=\alpha+\beta,\quad B=\beta+x.
\]

The two actual turn secants agree:

\[
u=1+\frac{x^2}{(1+x)(\beta+x)}
       -\frac{x}{\beta-1}\log\frac{\beta+x}{1+x}
\]
\[
\hphantom{u}
=1+\frac{\beta^2}{(\alpha+\beta)(x+\beta)}
       -\frac{\beta}{x-\alpha}\log\frac{x+\beta}{\alpha+\beta}.
\tag{1}
\]

Let `v` be the actual opposite turn norm and `E` the same-lift central
pairing, with normalization

\[
E=(u-1)(1+x)+(v-1)(1+y)+1+\frac1{1+x}+\frac1{1+y}
      -\rho+\log[\rho(1+x)(1+y)],
\]
\[
\gamma^2=\frac{4uv-E^2}{16(1-\rho)^2},\qquad
\kappa=\sqrt{12\gamma^2}.
\tag{2}
\]

Reflect the incoming two-turn window to run forward from the central
switch. Its active controls are `2,0`, with exact factors

\[
q_1=B/S>1,\qquad q_2=B/A>1.
\tag{3}
\]

This reflection is an algebraic way to compute the already existing
incoming window, including its cost and positive polar angle. It does
not posit an independently closable reflected period.

Here is why the reflected polar increment equals the original positive
incoming increment. Rebase the original central frame to `g(0)=I` and
write its incoming interval as `[-L,0]`. Let
`R=diag(1,-1)`, `g_ref(t)=R g(-t) R`, and
`Lambda_ref(t)=-R Lambda(-t) R`. The reflected state is
`X_ref(t)=-R X(-t) R`, so the physical cost is unchanged. If
`Lambda(0)=-kappa h J h^{-1}`, take `h_ref=R h R`; then

\[
h_{\rm ref}^{-1}g_{\rm ref}(t)=R[h^{-1}g(-t)]R.
\]

For the polar complex coordinate
`z(M)=tr(M)+i(M21-M12)`, one has `z(RMR)=conjugate(z(M))`.
Time reversal and complex conjugation each reverse the angular
increment. Their combination preserves its positive magnitude. Thus the
reflected two-turn defect is exactly the original incoming-window
defect, with the same kappa and the same global available allowance.

## 2. Exact rational cost

The two turn costs simplify using (1). They are

\[
C_1=\frac{\sqrt{12}a^2}{8}\,
x(\beta-1)\left[u+\frac{U}{SB}\right],
\qquad
C_2=\frac{\sqrt{12}a^2}{8}\,
\beta(x-\alpha)\left[u+\frac{U}{AB}\right].
\]

In particular,

\[
\boxed{
C_{\rm br}=\sqrt3\left[
\frac{\rho u}{1-\rho}(2\beta x-x-\alpha\beta)
+\frac{\beta x-\alpha}{(1+x)(\alpha+\beta)}\right].}
\tag{4}
\]

To check this directly, substitute either secant expression in its
corresponding vertex-arc cost. The logarithmic term cancels. The
remaining simplification is the rational identity

\[
\frac{x(\beta-1)}{SB}
+\frac{\beta(x-\alpha)}{AB}
=\frac{\beta x-\alpha}{SA}.
\]

Both secants are needed for (4). On an enlarged scalar comparison
domain, (4) may still define a useful comparison expression, but it is
the physical window cost only on the actual two-secant locus.

## 3. Rational relative-frame matrix

Put

\[
n=\frac{U-x}{S},\qquad z=\frac{U-\alpha\beta}{A},
\]
\[
P=\begin{pmatrix}-n-2&x+2\\n&x\end{pmatrix},\quad
Q=\begin{pmatrix}-z-2\beta&\alpha+2\beta\\z&\alpha\end{pmatrix},
\quad
F=\begin{pmatrix}
S/A&0\\(S^2-B^2)/(SA)&A/S
\end{pmatrix}.
\]

Then `det P=det Q=-2U` and `det F=1`. Define

\[
m=PFQ^{-1}=(m_{ij}),\qquad
D_3=\operatorname{diag}(1/\sqrt3,1).
\]

The relative physical frame of the reflected bridge is exactly

\[
\boxed{M=D_3mD_3^{-1}.}                         \tag{5}
\]

Indeed, for margins `(a,b,c)` satisfying `ab+ac+bc=4`, the fixed
matrix used in the vertex propagator satisfies

\[
\phi(a,b,c)\,\mathsf B
=\frac12\begin{pmatrix}
-(b+2a)/\sqrt3&(c+2a)/\sqrt3\\b&c
\end{pmatrix}.
\]

The initial reflected margins are `a(1,n,x)` and the final margins
are `a(beta,z,alpha)`. Multiplying the control-2 and control-0
propagators with factors (3) gives `F`. The common factor `a/2`
cancels in the relative frame. Thus (5) contains no logarithm, square
root of rho, or conjugating-frame choice.

## 4. Scalar endpoint angle and competitive-window filters

Define the three rational expressions

\[
h_{11}=E(S^{-1}-\rho S)-u(1-\rho^2S^2)+v(1-S^{-2}),
\]
\[
h_{12}=u(1+\rho S)^2+v(1+S^{-1})^2
          -E(1+S^{-1})(1+\rho S),
\]
\[
h_{21}=-u(1-\rho S)^2-v(1-S^{-1})^2
          -E(1-S^{-1})(1-\rho S),
\qquad T_\kappa=2\kappa(1-\rho)^2.
\]

Set

\[
\mathcal A=T_\kappa(m_{11}+m_{22})+h_{12}m_{22}
             -h_{11}(m_{12}+3m_{21})-3h_{21}m_{11},
\]
\[
\mathcal B=h_{11}(m_{22}-m_{11})+h_{12}m_{21}+h_{21}m_{12}
             +\frac{T_\kappa}{3}(3m_{21}-m_{12}).
\tag{6}
\]

For the reflected initial physical costate `Lambda_s`, write the two
endpoint traces of [GLOBAL_ENDPOINT_DEFECT_TEST](GLOBAL_ENDPOINT_DEFECT_TEST.md)
as

\[
A_{\rm ep}=\operatorname{tr}[(I+J\Lambda_s/\kappa)M],\qquad
B_{\rm ep}=\operatorname{tr}[(\Lambda_s/\kappa-J)M].
\]

The exact relations are

\[
\boxed{\mathcal A=T_\kappa A_{\rm ep},\qquad
\sqrt3\mathcal B=T_\kappa B_{\rm ep}.}             \tag{7}
\]

One derivation uses

\[
C_0=\begin{pmatrix}-(1+S^{-1})&1+\rho S\\
                         1-S^{-1}&1-\rho S\end{pmatrix},
\quad V=\begin{pmatrix}E&-2v\\2u&-E\end{pmatrix}.
\]

Direct multiplication gives

\[
(1-\rho)C_0VC_0^{-1}
=\begin{pmatrix}h_{11}&h_{12}\\h_{21}&-h_{11}\end{pmatrix}.
\]

The reflection changes the costate by `Lambda -> -R Lambda R`,
`R=diag(1,-1)`. Substitution in the two trace formulas yields (6)--(7).

For an actual competitive period, the global spectral bound forces
total positive polar angle `pi/3`. A proper positive-duration window
therefore has `0<theta_br<pi/3`. Consequently actual data satisfy the
necessary strict filters

\[
\mathcal A>0,\qquad 0<\mathcal B<\mathcal A,
\qquad
\theta_{\rm br}=\arctan\frac{\sqrt3\mathcal B}{\mathcal A}.
\tag{8}
\]

These signs are imported from the actual competitive window. They
need not hold on every auxiliary scalar comparison point. A certificate
may reject boxes contradicting their weak versions. It must establish
a positive denominator on every box where it uses the quotient or its
derivatives.

The exact necessary defect inequality is now

\[
\boxed{
C_{\rm br}+(\kappa+3/2)
\left(\frac\pi3-
\arctan\frac{\sqrt3\mathcal B}{\mathcal A}\right)
\le A_{\rm oct}.}                              \tag{9}
\]

Equations (1)--(9) retain the actual common primary multiplier and
the actual physical cost. They are a fixed two-turn consequence inside
the whole period; no local window is asserted to satisfy the global
seam by itself.

An additional necessary central-switch filter has a short rational form.
For `r=1/(1+x)`, put

\[
\mathcal H(r)=(1-\rho-v)r^2
 +\rho[E-(1-\rho)]r+\rho[(1-\rho)-u].             \tag{H}
\]

At the central two-control tie, the omitted Hamiltonian is nonpositive
if and only if `H(r)>=0`. Indeed the stationary control is a strictly
positive convex combination of the three vertices in the strict star,
and

\[
3m_b-\operatorname{tr}(\Lambda X)
 =\frac{\sqrt3(a^2+4)(a+ax)}{8\rho}\,\mathcal H(r).
\]

The prefactor is positive. The stationary Hamiltonian is the negative
of this quantity, so the two tied zero Hamiltonians leave exactly the
sign of the omitted third one. This is a same-lift first-event filter;
it is not implied by the two secants alone.

There are also exact stationary-slack filters at the middle and final
switches of the reflected bridge. Define

\[
\begin{aligned}
P_{\rm mid}={}&\beta^2\rho x^2-\beta^2\rho+\beta^2
 -4\beta\rho x^2-4\beta\rho x+2\beta x\\
 &+3\rho x^2+4\rho x+\rho+x^2,\\
N_{\rm mid}={}&(1-\rho)(\beta^2\rho+\beta\rho x+\rho x^2-\rho+1)
 -v-\rho E(\beta x-2x-1)-\rho uP_{\rm mid}.
\end{aligned}
\]

Then at the actual middle switch

\[
\frac{3m_b-\operatorname{tr}(\Lambda X)}{a\sqrt3}
=\frac{N_{\rm mid}}{2\rho(\beta+x)(1-\rho)},\qquad
\boxed{N_{\rm mid}\ge0.}                         \tag{M}
\]

At the outer reverse-centre entrance, use the transported quantities
`rho_A,u,w,E_L` from the short-bridge transport equations and put
`r_A=alpha/(alpha+beta)`, `Z_A=1+rho(alpha^2-1)`. Then

\[
H_A=(1-\rho_A-w)r_A^2+
 \rho_A(E_L-1+\rho_A)r_A+\rho_A(1-\rho_A-u),
\]
\[
\frac{3m_b-\operatorname{tr}(\Lambda X)}{a\sqrt3}
=\frac{(\alpha+\beta)Z_A^2}{2\rho\alpha^2(1-\rho)}H_A,
\qquad\boxed{H_A\ge0.}                          \tag{O}
\]

All prefactors are positive. These identities follow by transporting
the same physical costate with (5), once to the first turn endpoint and
once to the second. The separate
[mixed_general_short_slack_certificate.py](../explorations/mixed_general_short_slack_certificate.py)
checks both identities by exact matrix algebra. The omitted-control
sign at each actual two-control tie gives the nonnegative slack. No
new endpoint multiplier is introduced.

A useful angle/modulus bound strengthens (8). For every determinant-one
matrix B, `|z(B)|^2=||B||_F^2+2>=4`. The endpoint complex product thus
has modulus at least 4. Since
`cos(theta)+sin(theta)/sqrt(3)>=1` on `[0,pi/3]`, (7) gives

\[
\boxed{\mathcal A+\mathcal B\ge4T_\kappa.}        \tag{A}
\]

Together with `B<=A`, this also gives `mathcal A>=2T_kappa`.
These are necessary constraints at actual data; a Taylor implementation
must still verify its internal denominator on the entire comparison
rectangle before evaluating a quotient.

## 5. Eliminating the opposite turn by its exact range

There is a further exact scalar reduction. Fix `r=1/(1+x)`, rho, u and v,
with `3/4<=v<1`, and set

\[
t_0=\rho/r,\qquad
 t_1=\min\left(r,\frac{1-\sqrt{4v-3}}2\right).
\]

An opposite turn `t=1/(1+y)` satisfying the closed smaller-turn,
nonnegative-central-duration and incident-norm conditions lies precisely in
`[t0,t1]`, provided `t0<=t1`. The central pairing is

\[
\mathscr E(t)=\frac{u-1}{r}+\frac{v-1}{t}
               +1+r+t-\rho+\log\frac{\rho}{rt}.
\]

Its derivative on this interval is

\[
\mathscr E'(t)=\frac{1-t+t^2-v}{t^2}\ge0.
\]

Consequently its exact closed range is

\[
E_{\min}=\frac{u-1}{r}+\frac{(v-1)r}{\rho}
             +1+r+\frac\rho r-\rho
\ \le E\le\ \mathscr E(t_1)=E_{\max}.             \tag{10}
\]

This replaces the opposite-turn coordinate by E without changing the
listed closed scalar constraints. Further actual constraints, such as
missing-control signs at both ends of the central reverse arc, must
still be retained when they are needed. A stronger rational upper relaxation than simply dropping the logarithm
is

\[
E\le\frac{u+v-2}{r}+2r-\rho+\frac\rho{r^2}.                    \tag{11}
\]

For (11), use `log(t0/t)<=t0/t-1`, where `t0=rho/r`. The resulting
upper expression is `(u-1)/r+r-rho+t-K0/t`, with
`K0=1-v-t0>=-t0^2`. Its derivative is `1+K0/t^2>=0` for `t>=t0`.
Its value at t=r proves (11). This also remains valid beyond the true
incident-norm endpoint, so no inadmissible monotonicity extension is
being used. The full compact necessary domain is specified in
[MIXED_SMALLER_SHORT_SIX_VARIABLE_REDUCTION](MIXED_SMALLER_SHORT_SIX_VARIABLE_REDUCTION.md).
No claim that (11) completes the exclusion is made here.

## 6. Discovery status and a limitation of the Casimir-only target

The proposed exclusion using only the competitive Casimir cap, the
actual two secants, incident reverse conditions and one transported
outer reverse root is too weak. A useful numerical regression starts
from the exact rational inputs

\[
x=y=\frac{2104323328450773}{10^{15}},\quad
\alpha=\frac{11362760173636808}{10^{16}},\quad
\rho=\frac{1037582578835953}{10^{16}},\quad
\tau=\frac{2058215114674781}{10^{15}}.
\]

Solving the two secants for beta and the outer reverse-root equation
for v at 80-digit precision gives approximately

| Quantity | Numerical value |
|---|---:|
| beta | 2.20942934618043103 |
| u | 0.758217166137300032 |
| v | 0.781537241140268083 |
| gamma squared | 0.183460589767607059 |
| Outer-centre rho | 0.130036746170198349 |
| Central reverse factor | 1.00010001000100020 |
| Outer reverse factor | 1.26893475009136063 |
| Opposite turn endpoint ratio | 1.00257881862369967 |

The analytic first-event continuation independently reconstructed the
central reverse arc, its next outgoing turn, and the backward incoming
turn as genuine first events. Nevertheless the incoming turn alone has
defect about `0.00199047247939417`, exceeding the full-period allowance
`0.00147414272159819`. Thus this locally feasible small-Casimir datum
cannot complete competitively. The numerical reconstruction is
discovery/regression evidence, not a certified counterexample to any
established global theorem.

A one-turn defect exclusion also has an obstruction in the closed
necessary-condition domain: near its central zero-factor / outer
`w=3/4, tau=2` boundary, the incoming-turn defect is smaller than the
allowed defect by about `0.00014130`. For the full two-turn bridge,
the corresponding excess in (9) is about `0.00155974`.

Three wider optimization runs and 31 nearby constrained starts found
the same positive two-turn excess minimum, around
`x=y=2.12804138454`, `alpha=1.13970647125`,
`beta=2.23638067677`, `rho=0.102200970426`, and
`gamma^2=0.183276057112`. These probes retained the two actual secants,
outer reverse-root conditions, central Hamiltonian slack and reverse
scale bounds. They do not prove uniform positivity. A complete exact
cover or a hand inequality proving (9) impossible remains required.

The exact identity checker is
[mixed_general_short_defect_interface_certificate.py](../explorations/mixed_general_short_defect_interface_certificate.py).
Its scope is algebraic verification of the displayed interface, without
a sampled or uniform positivity assertion.
