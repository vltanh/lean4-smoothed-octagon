# Completing the padded L3 arcs reaches the star boundary before another switch

Date: 2026-11-07. A hand asymptotic test of the proposed external-switch
filter; no numerical search, Lean, Lake, or CI.

## Result and scope

Consider the symmetric scaled reverse-edge core of word `2121` in
[LOCAL_REVERSE_SIX_OBSTRUCTION.md](LOCAL_REVERSE_SIX_OBSTRUCTION.md),
with core size \(b>0\). Its explicit normal Pontryagin lift continues
onto control 0 before and after the core. Arbitrarily short cuts of
these continuations give the fixed-endpoint counterexamples `021210`.

For **all sufficiently small positive core sizes \(b\)**, extending
these control-0 pieces until the next genuine Hamiltonian tie does not
produce a complete six-piece PMP window: on each side, strict-star
membership ends before any next tie occurs. Moreover, the two
continuations together already exceed physical cost \(\pi\) at
suitable interior cuts before reaching that boundary.

Thus completing the arcs of this particular counterexample family does
not supply an eligible L3 input satisfying the genuine external-switch
conditions. No forbidden forward alternation is needed. The argument
does not classify arbitrary L3 windows, give an explicit numerical
upper bound for the smallness of \(b\), or prove a replacement theorem
on a filtered domain. The original broad-domain L3 statement remains
false, including with arbitrary measurable replacements, as proved in
[LOCAL_REVERSE_SIX_GLOBAL_MINIMUM.md](LOCAL_REVERSE_SIX_GLOBAL_MINIMUM.md).

## 1. The limiting state and normal lift

Write \(q_*=1/\sqrt3\) to distinguish the fixed geometric constant
from a vertex-arc factor. The core uses

\[
w=y^{-2},\qquad S(x)=\int_0^x w_*(r)\,dr,
\qquad L_b=S(b),
\]

and the costate of its Sections 1--2. On the positive half of the core,
rescale \(x=b\xi\), with fixed break at \(\xi=1/2\). The displayed
profile is a rational smooth function of \((b,\xi)\) on each of these
two fixed intervals. Consequently, as \(b\downarrow0\),

\[
w_*(b)=2+O(b),\qquad L_b=2b+O(b^2),\qquad
\mu=O(b^2),\qquad \lambda(b)=O(b^3).                       \tag{1}
\]

For example, the numerator and denominator defining \(\mu\) become
\(b^3\) and \(b\) times smooth integrals with positive limiting
denominator; the defining integral for \(\lambda(b)\) is then
\(O(b^3)\). These formulas also supply smooth extensions of the
initial state and costate to \(b=0\); no interchange of a singular
integral limit is required.

The limiting half-plane state is \((x,w)=(0,2)\). Its physical
determinant-one margins are

\[
(p_0,p_1,p_2)=(a,4a,4a),\qquad a=1/\sqrt6.                 \tag{2}
\]

Indeed \(p_0=\sqrt3(x^2+y^2-q_*^2)/y=1/\sqrt6\), reflection
gives \(p_1=p_2\), and
\(p_0p_1+p_1p_2+p_2p_0=4\) selects \(p_1=p_2=4a\).

In the base note's coordinates \((x,w,A=gK(x))\), its minimizing
normal Hamiltonian has running cost
\(\mathcal L=1+(1+x^2)w\). The limiting covector is

\[
p_x=-1,\quad p_w=0,\quad m=-1,\quad n=1,\quad k=0,        \tag{3}
\]

where \(m,n,k\) evaluate the group covector on
\(E_{21},E_{12},\operatorname{diag}(1,-1)\). All three vertex
Hamiltonians are zero at (2)--(3). Their two inactive differences have
zero first derivative along control 0 there. One can check the latter
directly from the state and adjoint equations: \(p_x'=p_w'=n'=0\)
at this point, and the bracket
\(p_x+n+2xw^2p_w\) and \(p_w\) both vanish. The nonzero value of
\(k'\) does not enter that first derivative.

## 2. Exact gaps along any normal control-0 arc

This calculation uses the triangular tangent coordinates of
BOUNDED_REDUCTION. Let \(s\) be the log factor of a control-0 arc,
starting at \(s=0\). Write its margins as

\[
p_0=a,\qquad p_1=\beta,
\qquad z=a+\beta=z_0e^s,\qquad
p_2=K/z-a,\qquad K=a^2+4.                                \tag{4}
\]

The tangent frame \(V=gX\) obeys \(V'=-VD_0\), with the three
fixed matrices

\[
D_0=\begin{pmatrix}-1&0\\0&1\end{pmatrix},\quad
D_1=\begin{pmatrix}1&-2\\0&-1\end{pmatrix},\quad
D_2=\begin{pmatrix}1&0\\2&-1\end{pmatrix}.
\]

Use normalized cost \(J=C/\sqrt{12}\). Its vertex log-time densities
are \(\ell_j=p_j(p_0+p_1+p_2)/8\). A spatial frame covector \(\nu\)
is constant, because the cost is independent of the frame. Put

\[
\phi_j(s)=\nu(\operatorname{Ad}_{V(s)}D_j),\qquad
d_0=\phi_0.
\]

Then \(d_0\) is constant, while
\(\phi_1=-d_0+c_1e^{2s}\) and
\(\phi_2=-d_0+c_2e^{-2s}\) for constants \(c_1,c_2\).
Let \(\eta_a,\eta_\beta\) be the state covector in the independent
coordinates \((a,\beta)\), with maximizing Hamiltonian convention.
The active zero-Hamiltonian equation and its adjoint equation give

\[
\eta_\beta={d_0+\ell_0\over z},\qquad
\eta_a'=\partial_a\ell_0-\eta_\beta,
\qquad \ell_0={a\over8}(z+K/z-a).
\]

Here \(\partial_a\) holds \(\beta\) fixed, so \(\partial_a z=1\).
Integrating the last equation yields

\[
\eta_a={z\over8}-{as\over4}
 -{a^2+1-2d_0\over2z}+{aK\over8z^2}+c_3.                 \tag{5}
\]

The inactive gaps, in the nonnegative minimizing-cost convention, are

\[
\begin{aligned}
\mathcal D_1&=\ell_1+\phi_1+z\eta_a,\\
\mathcal D_2&=\ell_2+\phi_2-{K\over z}\eta_a
 +(\beta+p_2)\eta_\beta.
\end{aligned}
\]

Substitution of (4)--(5) gives the exact forms

\[
\begin{aligned}
\mathcal D_1(s)
 &=A_1e^{2s}+B_1e^s-{az_0\over4}\,se^s-{a^2\over4},\\
\mathcal D_2(s)
 &=A_2e^{-2s}+B_2e^{-s}+{aK\over4z_0}\,se^{-s}-{a^2\over4},
\end{aligned}                                             \tag{6}
\]

for constants \(A_i,B_i\). In particular, the constant terms in both
gaps are exactly \(-a^2/4\); they are not independent fitting
parameters. Formula (6) is valid on the whole smooth control-0 flow.
The log fields and these gaps remain smooth when an inactive margin
reaches zero, even though the corresponding physical vertex field
would no longer be admissible there.

## 3. No further tie in the limiting strict-star arc

For (2), \(z_0=5a\) and \(K=25a^2\). The zero values and zero first
derivatives in Section 1 determine the four constants in (6):
\(A_1=A_2=a^2\), \(B_1=B_2=-3a^2/4\). Hence

\[
\boxed{
\begin{aligned}
\mathcal D_1(0,s)
 &={a^2\over4}e^s
   \bigl(4e^s-e^{-s}-3-5s\bigr),\\
\mathcal D_2(0,s)
 &={a^2\over4}e^{-s}
   \bigl(4e^{-s}-e^s-3+5s\bigr).
\end{aligned}}                                            \tag{7}
\]

The first argument denotes the core parameter \(b=0\). The margins
along the outgoing arc are
\((a,5ae^s-a,5ae^{-s}-a)\). Thus strict star holds precisely for
\(0\le s<\log5\); its first loss is \(p_2=0\).

For \(F_+(s)=4e^s-e^{-s}-3-5s\),
\(F_+(0)=F_+'(0)=0\) and \(F_+''(s)=4e^s-e^{-s}>0\) for
\(s\ge0\). For \(F_-(s)=4e^{-s}-e^s-3+5s\),

\[
F_-'(s)=-{(e^s-1)(e^s-4)\over e^s}.
\]

It increases until \(\log4\), then decreases until \(\log5\), where

\[
F_-(\log5)=5\log5-36/5>0.                                \tag{8}
\]

For a rational check of the last strict sign, the positive artanh
series at \(2/3\) gives
\(\log5>4/3+16/81=124/81\), so the right side of (8) is greater
than \(184/405\). Thus both gaps are strictly positive on
\(0<s\le\log5\), including their continuous log-field limits at the
star boundary. Their common second derivative at the initial point is

\[
\partial_s^2\mathcal D_1(0,0)
 =\partial_s^2\mathcal D_2(0,0)=1/8.                      \tag{9}
\]

## 4. Persistence for small positive cores, including near the join

The double zeros of (7) mean that continuity away from \(s=0\) alone
would be insufficient. The following first-derivative calculation
handles that endpoint.

At the right core join, the active edge vertex is 1. In the base
note's \(\tau\) clock put

\[
r=2/d,\quad d=1-w(q_*^2-x^2),\quad
\mathcal C=p_x+n+2xw^2p_w,\quad
b_+=2/(q_*-x),\quad b_-=-2/(q_*+x).
\]

On the outgoing control-0 continuation,

\[
\mathcal H_j-\mathcal H_0=r\mathcal C+b_jwp_w
\quad(j=1,2).
\]

At the join, (1) and the explicit covector give

\[
x=b,\ w=2+O(b),\ r=6+O(b),\ p_w=O(b^3),\quad
m=-1+O(b^2),\ k=-4b+O(b^2),\ \mathcal C=O(b^3).           \tag{10}
\]

The last relation also follows directly from the exact tie
\(\mathcal H_1=\mathcal H_0=0\). The control-0 adjoint equations
needed here, obtained by differentiating its displayed Hamiltonian,
are

\[
\begin{aligned}
p_x'&=-2xw+r_x\mathcal C+2rw^2p_w,\\
p_w'&=-1-x^2-m+r_w\mathcal C+4rxwp_w,\\
n'&=-wk.
\end{aligned}
\]

Here primes are \(\tau\) derivatives. Equations (10) imply
\(p_x'=-4b+O(b^2)\), \(p_w'=O(b^2)\), and
\(n'=8b+O(b^2)\). The derivative of \(2xw^2p_w\) is \(O(b^3)\),
so \(\mathcal C'=4b+O(b^2)\). Differentiating the two gaps gives

\[
{d\over d\tau}(\mathcal H_j-\mathcal H_0)
 =24b+O(b^2)\qquad(j=1,2).                               \tag{11}
\]

To convert (11) to the gaps of (6), retain the vertex-dependent clock:

\[
\mathcal D_j={\sqrt3\over8}yp_j
 (\mathcal H_j-\mathcal H_0),\qquad
{d\tau\over ds}={yp_0\over2}.                            \tag{12}
\]

This uses \(J=(\sqrt3/4)\mathcal A\) and the zero active Hamiltonian.
At \(b=0\), the two factors in (12) are \(1/4\) and
\(1/(4\sqrt3)\), respectively. The first inactive gap is zero at
the join; the other is positive and \(O(b^3)\). Therefore

\[
\mathcal D_1(b,0)=0,\qquad \mathcal D_2(b,0)>0,\qquad
\partial_s\mathcal D_j(b,0)
 ={\sqrt3\over2}b+O(b^2)>0                                \tag{13}
\]

for all sufficiently small positive \(b\).

The initial data and control-0 log flow are smooth in \((b,s)\),
including \(b=0\) and the limiting inactive-margin boundary. By (9),
there are fixed \(\varepsilon>0\) and a sufficiently small core range
on which both second derivatives are positive for
\(0\le s\le\varepsilon\). Together with (13), this proves strict
positivity of both gaps for \(0<s\le\varepsilon\).

On the remaining interval, use (7)--(8). Both limiting gaps have a
positive minimum on \([\varepsilon,\log5]\), and remain positive on
a slightly longer compact interval. The outgoing strict-star endpoint
for a positive core is

\[
s_*(b)=\log\left(1+{p_2(b,0)\over p_0(b,0)}\right)
 \longrightarrow\log5.
\]

Uniform continuity now proves

\[
\mathcal D_1(b,s)>0,\quad \mathcal D_2(b,s)>0
\qquad(0<s\le s_*(b))                                    \tag{14}
\]

for all sufficiently small positive \(b\). No compactness assertion
about arbitrary trajectories is involved; this is one explicit smooth
family of control-0 flows on a fixed compact parameter interval.

The incoming continuation is the exact reflected calculation. In the
closed state/covector equations, the map

\[
(x,w,p_x,p_w,m,n,k)
 \longmapsto(-x,w,p_x,-p_w,m,n,-k)
\]

together with reversal of time preserves the control-0 equations and
interchanges the two inactive labels. The symmetric core's endpoint
data have exactly this relation. Thus (14) also holds while extending
backwards from its first join. That side reaches \(p_1=0\) before
any further tie.

## 5. Budget and interpretation for complete minimizing windows

A minimizing continuation cannot switch away from control 0 while
both inactive gaps are strict. Equations (13)--(14) therefore show
that completing either outer arc requires leaving the strict-star
domain. An isolated triple tie, a different preceding or following
label, or a continuous simplex choice cannot avoid this: throughout
the open continuation control 0 is the unique maximizing vertex.

For the padded inputs the normal lift is unique, by the fixed-initial-
state endpoint-rank argument in
[MINIMIZER_WINDOW_PMP.md](MINIMIZER_WINDOW_PMP.md), Section 6. Hence
another normalized or abnormal lift cannot supply an earlier switch.
Any longer `0 / 2121 / 0` continuation contains one of these short
positive-pad windows, so its minimizing lift would already be fixed
by that restriction.
This challenges the filter using the actual lift of the counterexample,
rather than merely selecting a convenient covector.

There is also an independent limiting budget check. At \(b=0\),
integrating the two control-0 arcs from \(-\log5\) to \(\log5\)
gives

\[
\begin{aligned}
J_{\rm boundary}
 &=\int_{-\log5}^{\log5}
 {a^2\over8}(5e^s+5e^{-s}-1)\,ds\\
 &=1-{\log5\over24}.
\end{aligned}                                             \tag{15}
\]

Its physical cost is strictly greater than \(\pi\). Indeed
\(\log5<2\), because \(e^2>1+2+2=5\), and
\(\sqrt3>12/7\). Thus

\[
\sqrt{12}\left(1-{\log5\over24}\right)
 >{11\sqrt3\over6}>{22\over7}>\pi.                       \tag{16}
\]

The inequality is strict, so already a symmetric interior truncation
of these limiting arcs has cost greater than \(\pi\). Smooth dependence,
the vanishing core cost, and (14) retain this conclusion for all
sufficiently small positive cores, with the cuts still strictly inside
the star domain. If such an interval is contained in one actual period,
it cannot occur in a minimizer whose whole-period cost is at most
\(A_{\rm oct}<\pi\). This is the relevant budget condition for a
selected six-complete-piece window, which lies within one period.
No whole-period bound is asserted for an arbitrary longer interval of
the twisted extension. The absence of a next tie before star loss
already rules out a globally strict-star PMP continuation, independently
of this auxiliary budget comparison.

The first obstruction is the absence of any next genuine tie before
the star boundary; (16) is an additional budget check on the same
family. Neither establishes a universal comparison for another L3
input. In particular, this result does not justify replacing the open
five-template analytic work by an asserted uniform bound.

## Dependencies and validation boundary

- LOCAL_REVERSE_SIX_OBSTRUCTION, Sections 1--3: the exact core,
  normal covector, and positive short control-0 continuations.
- BOUNDED_REDUCTION and LOCAL_FORWARD_ENDPOINT_FILTER: the tangent
  coordinates, vertex log fields, and normalized cost convention.
- MINIMIZER_WINDOW_PMP, Section 6: normality and uniqueness for the
  padded inputs, with initial state fixed.

The limiting gap formulas, their signs, and the small-core persistence
argument are hand derivations. No sampled inequality, optimizer,
computer algebra identity, or numerical cutoff is a premise. The
smallness thresholds are existential and have not been quantified.
The original broad-domain L3 obstruction remains valid, and a local
improvement theorem on a repaired necessary domain remains unproved.

Independent hand review rederived the exact gap forms, limiting second
and small-core first derivatives, clock factors, reflected incoming flow,
and moving-boundary persistence. It also checked the cost integral with
its explicit one-period qualification. No material gap was found.
