# A root-preserving reduction of the smaller-short cost test

Date: 2026-11-07. Hand proof, accepted in an
[independent internal review](MIXED_SMALLER_SHORT_ROOT_AND_ANGLE_AUDIT.md).

This note gives two further scalar reductions of the smaller-short
branch. The first preserves its competitive upper Casimir bound while
moving to an explicit boundary. The second eliminates the diagonal
pairing from an upper bound for the physical two-turn polar angle. Their
combination initially retains a necessary cost inequality on four
boundary faces. The subsequent
[opposite-floor hand proof](MIXED_SMALLER_SHORT_NONPOSITIVE_FLOOR.md)
removes the separate v=3/4 face. The other three faces, t=r,
v=U(t) and w=3/4, remain **unexcluded**.

The inputs are the actual six-variable interface in
[MIXED_SMALLER_SHORT_SIX_VARIABLE_REDUCTION](MIXED_SMALLER_SHORT_SIX_VARIABLE_REDUCTION.md),
the physical cost and endpoint matrix in
[MIXED_GENERAL_SHORT_DEFECT_INTERFACE](MIXED_GENERAL_SHORT_DEFECT_INTERFACE.md),
and the proved positive factor in
[MIXED_SMALLER_SHORT_OUTER_ENVELOPE](MIXED_SMALLER_SHORT_OUTER_ENVELOPE.md).
No interval cover, optimizer, executable sign check or coefficient table
is a premise of the argument below.

## 1. Fixed geometry and one actual descending root

Retain the notation of the outer-envelope note:

\[
1\le\alpha<x\le\beta,\qquad r=(1+x)^{-1}<\tfrac12,
\qquad t_0=\rho/r\le t\le r,
\]
\[
\lambda=[1+\rho(\alpha^2-1)]^{-1},\quad
D=\alpha^2+2\alpha\beta+1+2x-2\beta x,
\quad d=\lambda\rho D,
\]
\[
T=[\lambda\rho\alpha(\alpha+\beta)]^{-1},\quad
r_A=\frac{\alpha}{\alpha+\beta},\quad
\rho_A=\alpha^2\lambda\rho,\quad T=r_A/\rho_A.
\]

The incoming norm u and all these geometry variables remain fixed.
For the opposite reciprocal turn and norm write

\[
E(t,v)=\frac{u-1}{r}+\frac{v-1}{t}
 +1+r+t-\rho+\log\frac{\rho}{rt},
\]
\[
w=\lambda^2v+d^2u-d\lambda E,
\qquad E_L=2du-\lambda E,
\qquad
\Gamma=\frac{4uv-E^2}{16(1-\rho)^2},
\quad \kappa=\sqrt{12\Gamma}.
\tag{1}
\]

Put \(U(s)=1-s+s^2\). Actual data have

\[
\tfrac34<u\le\min\{U(r),U(r_A)\},\quad
\tfrac34<v\le U(t),\quad \tfrac34<w,
\quad E>-\tfrac{23}{16}.
\tag{2}
\]

Fix the parameter \(\tau\) of the **actual** outer descending root.
Thus

\[
2<\tau<T,\qquad R_\tau(t,v)=0,
\qquad w<U(1/\tau).
\tag{3}
\]

Here, with \(f(s)=s-s^{-1}-\log s\) and
\(h(s)=\log s-1+s^{-1}\),

\[
R_\tau=\tau w-f(\tau)+u/r_A-f(1/r_A)
              -h(1/\rho_A)-E_L.
\tag{4}
\]

The scale bound \(\rho<1/7\) from
[HAND_PROOF_REFINEMENTS](HAND_PROOF_REFINEMENTS.md) is sufficient below;
the older bound \(\rho<3/20\) would also suffice for the positivity
argument. The proof does not assume that D has either particular sign.

## 2. Increase t while retaining the root and the upper Casimir cap

Define

\[
B(t)=1+\tau(\lambda t-d),\qquad \nu(t)=U(t)-v(t).
\]

The positive-factor argument of the outer-envelope note gives
\(B(t)>0\) on the entire fixed interval \([t_0,r]\). At fixed t,

\[
\frac{\partial R_\tau}{\partial v}=\frac{\lambda B(t)}t>0.
\tag{5}
\]

Consequently the affine equation \(R_\tau(t,v(t))=0\) defines a
unique smooth v(t) throughout that interval. Start at the actual t and
increase t while keeping

\[
t\le r,\qquad \nu\ge0,\qquad v\ge\tfrac34,
\qquad w\ge\tfrac34.
\tag{6}
\]

Stop at the first of the four boundary conditions

\[
\boxed{t=r,\qquad \nu=0,\qquad v=\tfrac34,
                    \qquad w=\tfrac34.}
\tag{7}
\]

If the initial point is on a listed face, no motion is needed. Otherwise
the first stopping point exists: (5) gives a smooth explicit solution
on the compact t interval, with no vanishing denominator, and r is
itself a listed endpoint.

### Exact derivatives

At fixed v, \(E_t=\nu/t^2\), whereas \(E_v=1/t\). Differentiating
(4), and then (1), gives

\[
\boxed{
v'=-\frac{(1-\tau d)\nu}{tB},\qquad
E'=\frac{\tau\lambda\nu}{tB},\qquad
w'=-\frac{\lambda^2\nu}{tB},\qquad
E_L'=\tau w'.}
\tag{8}
\]

For example,
\(v'=-(R_\tau)_t/(R_\tau)_v\), where
\((R_\tau)_t=\lambda(1-\tau d)\nu/t^2\). Substitution in
\(E'=v'/t+\nu/t^2\) gives the second formula; the other two then
follow directly from (1). Thus no sign of \(1-\tau d\) is presumed.

In particular E increases and w decreases. The strict descending-root
condition \(w<U(1/\tau)\) therefore persists. The fixed root identity
can also be written

\[
E_L=\frac{u-1}{r_A}+(w-1)\tau
 +1+r_A+\tau^{-1}-\rho_A
 +\log\frac{\rho_A\tau}{r_A}.
\tag{9}
\]

Its two incident upper bounds and \(\rho_A<r_A/\tau\) imply

\[
E_L\le3\rho_A.
\tag{10}
\]

For completeness, the elementary estimate used here says that if
\(a,b<1/2\), \(0<q\le ab\), and the incident norms are at most
U(a), U(b), then the central pairing is at most 3q. After inserting the
two norm ceilings, subtract 3q and differentiate the resulting expression
in q. Its derivative is \(1/q-4>0\), so its maximum is at q=ab,
where it equals \(-(1-2a)(1-2b)\le0\). Apply this first with
\((a,b,q)=(r_A,1/\tau,\rho_A)\).

Differentiating the Casimir gives the particularly useful identity

\[
\boxed{
\Gamma'
=-\frac{\nu\,[2u-\tau E_L]}
 {8(1-\rho)^2tB}\le0.}
\tag{11}
\]

Its bracket is strictly positive, since

\[
2u-\tau E_L\ge2u-3\tau\rho_A
>\tfrac32-3r_A>0.
\tag{12}
\]

Thus the **upper** competitive cap on Gamma survives this comparison.
This is the opposite Casimir direction from the earlier norm-raising
outer envelope.

### Ellipticity cannot be silently assumed

The path also stays strictly elliptic, for a separate explicit reason.
By (8), \(E\ge E_{\rm initial}>-23/16\). Apply the same elementary
central-pairing estimate to \((r,t,\rho)\), using the preserved bounds
\(u\le U(r),v\le U(t),\rho\le rt\). It gives

\[
E\le3\rho<3/7<23/16.
\]

Until a stopping face, u and v are at least 3/4. Therefore

\[
4uv-E^2>\frac94-\left(\frac{23}{16}\right)^2
=\frac{47}{256},\qquad
\boxed{\Gamma>\frac{47}{4096(1-\rho)^2}>0.}
\tag{13}
\]

So no additional zero-determinant face is missing from (7). The stronger
actual lower bound \(\Gamma>27/256\) is not asserted to survive. It
is deliberately dropped from this scalar relaxation; retaining it would
require stopping additionally at \(\Gamma=27/256\).

## 3. The incoming norm fixes one entry of a positive matrix

Let M be the **physical** relative frame of the reflected two-turn
bridge from the short-bridge interface. Its physical cost
\(C_{\rm br}\) and M depend only on the fixed geometry and u. They
are constant along the preceding scalar comparison. This does not make
the comparison covectors into a family of physical trajectories.

For the reflected initial primary costate write

\[
H=J\Lambda_s/\kappa,\qquad
J=\begin{pmatrix}0&-1\\1&0\end{pmatrix}.
\]

Negative ellipticity means H is symmetric positive definite with
determinant one. For the scalar comparison, the same conclusion follows
from (13): the Gram matrix with entries u, v and off-diagonal E/2 is
positive definite, and (14) is its congruence by an invertible matrix.
The exact h-entry formulas in the short-bridge
interface give the following more useful decomposition:

\[
H=\frac{u pp^T+v qq^T+(E/2)(pq^T+qp^T)}
             {2\kappa(1-\rho)^2},
\]
\[
p=\binom{\sqrt3(1-\rho/r)}{1+\rho/r},
\qquad q=\binom{\sqrt3(1-r)}{-(1+r)}.
\tag{14}
\]

For a direct check, the numerator entries are
\(-3h_{21},-\sqrt3h_{11},h_{12}\), exactly the entries of
\(2\kappa(1-\rho)^2H\) obtained from the endpoint traces.

Put

\[
e=\frac1{2\sqrt{U(r)}}
  \binom{1+r}{\sqrt3(1-r)},\qquad O=(e,Je)\in\mathrm{SO}(2).
\]

Then \(e^Tq=0\),
\(e^Tp=\sqrt3(1-\rho)/\sqrt{U(r)}\), and hence

\[
s:=e^THe=\frac{3u}{2\kappa U(r)}>0.
\tag{15}
\]

It follows that in the rotated basis every possible H with these fixed
u and kappa has the form

\[
O^THO=H_\xi=
\begin{pmatrix}s&\xi\\\xi&(1+\xi^2)/s\end{pmatrix},
\qquad \xi\in\mathbb R.
\tag{16}
\]

Thus maximizing over all real xi is a legitimate relaxation of all
remaining diagonal-pairing and opposite-norm restrictions. The actual
norm u and actual kappa are retained.

## 4. A circle gives the exact supremal endpoint angle

Write \(M'=O^TMO=(m_{ij})\). Set

\[
V=m_{22}+i m_{21},\qquad
D_0=(m_{11}-m_{22})-i(m_{12}+m_{21}),
\]
\[
\ell_s=\frac{s}{s+1},\qquad
C_s=V+\frac{\ell_s}{2}D_0,
\qquad R_s=\frac{\ell_s}{2}|D_0|.
\tag{17}
\]

Here C_s is a complex centre; it is unrelated to physical cost.
The set of possible endpoint polar quotients lies on the circle with
centre C_s and radius R_s. This assertion has a direct two-line
derivation. Choose

\[
B_\xi=\begin{pmatrix}\sqrt s&\xi/\sqrt s\\0&1/\sqrt s\end{pmatrix},
\qquad B_\xi^TB_\xi=H_\xi.
\]

For \(z(N)=\operatorname{tr}N+i(N_{21}-N_{12})\), multiplication
gives

\[
\boxed{
\frac{z(B_\xi M')}{z(B_\xi)}
=V+\frac{sD_0}{s+1-i\xi}.}
\tag{18}
\]

As xi ranges over the real line,
\(1/(s+1-i\xi)\) describes a circle with centre and radius both
\(1/[2(s+1)]\), except for its limit point 0. This proves (17).
The argument of (18) is precisely the relative polar angle associated
with H: \(-\kappa JH_\xi=-\kappa B_\xi^{-1}JB_\xi\), so this
Cholesky choice uses a valid elliptic conjugator. Left multiplication
by a rotation changes neither the relative angle nor (18).

The circle does not contain the origin. Indeed det M'=1 gives

\[
\Re(V\overline{D_0})=1-|V|^2,
\]
\[
\boxed{|C_s|^2-R_s^2
=\frac{s+m_{21}^2+m_{22}^2}{s+1}>0.}
\tag{19}
\]

For an actual proper competitive bridge, its angle is in \((0,\pi/3)\).
Choose the continuous argument branch on the disk that contains this
angle. The upper tangent ray from the origin then has angle

\[
\boxed{\Theta(s)=\arg C_s+
             \arcsin\frac{R_s}{|C_s|},
\qquad \theta_{\rm br}\le\Theta(s).}
\tag{20}
\]

The ordinary principal argument for C_s agrees with this centre branch:
the disk contains a point with argument in \((0,\pi/3)\), and its
angular half-width is less than pi/2 by (19). The formula remains valid
when R_s=0. Equivalently, a proposed bound phi can be verified without
inverse-trigonometric branch choices by the supporting-line inequality

\[
\Im(e^{-i\phi}C_s)+R_s\le0.
\tag{21}
\]

If \(0\le\phi\le\pi/3\), (21) implies that every actual angle
in \((0,\pi/3)\) is at most phi: the sign of
\(\sin(\theta_{\rm br}-\phi)\) gives exactly that implication.

## 5. The relaxed completion cost is monotone in kappa

The filled disks in (17) are nested as s increases. In fact, for
\(s_2\ge s_1\),

\[
|C_{s_2}-C_{s_1}|=R_{s_2}-R_{s_1}.
\tag{22}
\]

They are homothetic disks about the common boundary point V. Since
none contains the origin, their maximal argument on a common branch
is nondecreasing:

\[
s_2\ge s_1\quad\Longrightarrow\quad
\Theta(s_2)\ge\Theta(s_1).
\tag{23}
\]

There is a common branch for the entire family. All these disks lie in
the limiting disk with centre \(V+D_0/2\) and radius \(|D_0|/2\), and
the difference of its squared centre modulus and squared radius is
exactly det M'=1. Thus even the limiting disk avoids the origin. Fix its
argument branch by the initial actual quotient. This prevents a
principal-angle wrap from being mistaken for a monotonicity failure.

For fixed geometry and u, (15) says that s decreases when kappa
increases. Define the relaxed completion lower bound

\[
\boxed{\mathcal F(\kappa)=C_{\rm br}
 +(\kappa+\tfrac32)
 \max\{0,\pi/3-\Theta(3u/[2\kappa U(r)])\}.}
\tag{24}
\]

Both nonnegative factors in the added product are nondecreasing in
kappa, by (23). Therefore \(\mathcal F\) is nondecreasing in kappa.
No differentiation of a maximizing point is needed.

At actual data, \(\theta_{\rm br}\le\min\{\Theta,\pi/3\}\).
The exact whole-period cost test therefore implies

\[
\mathcal F(\kappa_{\rm actual})
\le C_{\rm br}+(\kappa_{\rm actual}+\tfrac32)
             (\pi/3-\theta_{\rm br})
\le A_{\rm oct}.
\tag{25}
\]

Combining (11), (13), and the monotonicity of (24), the scalar path of
Section 2 retains both necessary inequalities

\[
\Gamma\le\Gamma_{\rm actual}<\Gamma_{\rm cap},
\qquad \mathcal F(\sqrt{12\Gamma})\le A_{\rm oct}.
\tag{26}
\]

The exact physical two-turn cost has not been replaced by an off-locus
secant expression: its geometry and its equal-secant u were fixed from
the start. The angle test has intentionally been weakened by maximizing
over all diagonal pairings at each retained kappa.

One may retain the actual lower Casimir information in this *score*
without pretending that it is preserved by the artificial determinant.
The actual mixed-period bound is kappa_actual>9/8. Therefore

\[
\kappa_{\rm eff}:=\max\{\sqrt{12\Gamma},9/8\}
\le\kappa_{\rm actual},\qquad
\mathcal F(\kappa_{\rm eff})\le A_{\rm oct}.
\tag{27}
\]

The inequality follows solely from the proved monotonicity of the score.
More generally, a proved lower bound on actual kappa depending only on
the fixed short geometry may replace 9/8 in this maximum. This supplies
no additional stopping face and makes no lower-cap assertion about the
deformed Gamma.

The effective parameter and retained lower bound below are accepted in
[HAND_ENDPOINT_REDUCTIONS_AUDIT](HAND_ENDPOINT_REDUCTIONS_AUDIT.md).

### A retained lower bound from the fixed incoming norm

Such a geometry-dependent bound follows directly from the actual two
incident turns. Let

\[
m=\Phi(1-r),\qquad
\Phi(\eta)=1-\eta^2-\frac{4\eta}{3}
                  +\frac{2\eta}{3}\sqrt{12\eta-2}.
\]

The [explicit turn floor](EXPLICIT_TURN_NORM_FLOOR.md) gives
actual v>Phi(1-t)>=m>3/4, since t<=r and Phi is increasing.
Moreover

\[
U(r)-m=\frac{1-r}{6}
       \bigl(\sqrt{10-12r}-2\bigr)^2>0,
\]

so m<U(r)<=U(t) throughout t in [rho/r,r]. Keep u fixed and
lower only the actual opposite norm to m. On this norm segment the
central estimate E<=3rho applies, and

\[
\frac{\partial\Gamma}{\partial v}
=\frac{2u-E/t}{8(1-\rho)^2}
\ge\frac{2u-3r}{8(1-\rho)^2}>0.
\]

Consequently the actual Gamma is strictly greater than the scalar
value after this norm lowering. At that lowered norm put

\[
E_m(t)=\frac{u-1}{r}+\frac{m-1}{t}
       +1+r+t-\rho+\log\frac{\rho}{rt}.
\]

Its derivative is \((U(t)-m)/t^2>0\). Thus its values lie
between the two explicit endpoints

\[
E_0=\frac{u-1}{r}+\frac{(m-1)r}{\rho}
                  +1+r+\frac\rho r-\rho,
\qquad
E_r=\frac{u+m-2}{r}+1+2r-\rho+\log\frac\rho{r^2}.
\]

The square of a real number in an interval is at most the larger
endpoint square. With no sign assumption on E_m, this proves

\[
\boxed{\Gamma_{\rm actual}>
G_{\rm ret}:=
\frac{4um-\max\{E_0^2,E_r^2\}}{16(1-\rho)^2}.}
\tag{28}
\]

Every quantity in G_ret depends only on the fixed incoming norm and
fixed short geometry. Therefore this bound concerns the same actual
period at every stage of the root comparison. It does not say that the
artificial Gamma has this lower bound. In particular, the comparison
may retain both necessary conditions

\[
G_{\rm ret}<\Gamma_{\rm cap},\qquad
\mathcal F\left(\max\left\{
 \sqrt{12\Gamma},\frac98,
 \sqrt{12\max\{0,G_{\rm ret}\}}\right\}\right)
\le A_{\rm oct}.
\tag{29}
\]

The first follows from (28) and the actual upper cap. The second
follows because each entry of its maximum is at most actual kappa,
and the score is nondecreasing. The same proof with m=3/4 gives a
weaker entirely rational norm floor if preferred.

## 6. What remains after this reduction

The original four-face conclusion below can now be sharpened using the
[opposite-floor theorem](MIXED_SMALLER_SHORT_NONPOSITIVE_FLOOR.md): only
t=r, v=U(t), and w=3/4 need remain. This additional theorem does not
alter the root deformation or transfer any unjustified lower cap.

Every actual smaller-short competitive period supplies a scalar point
on at least one of the four faces (7), with the same fixed short-bridge
geometry, the same positive two-turn factors and cost, the fixed outer
descending root, the retained norm bounds, positive Gamma, the upper
Casimir cap, and the relaxed completion inequality (26).

The deformed scalar point is not asserted to satisfy every middle-switch
slack, the global lower Casimir bound, or a complete trajectory seam.
Dropping these requirements enlarges the comparison domain. The actual
twisted period and common multiplier are used only to supply the initial
data and the necessary cost test (25); no artificial path is substituted
for a physical competing period.

A hand exclusion of these four enlarged boundary domains is still
required to close the smaller-short branch. The formulas above identify
an explicit target with no residual optimization over the diagonal
pairing and with a cap-preserving root comparison. They do not relabel
the existing 107,977-node cover as a hand proof.
