# Uniform exclusion of long all-forward competitive periods

Date: 2026-11-07 UTC. Hand reduction and an exact rational interval
certificate. No Lean, Lake, typechecking, or CI.

**Verification status: the full complementary-domain exact replay is
pending.** The prerequisite lemmas and the broad circular exclusion are
proved and checked. The final checker has passed an independent source
and interface review, but its running verification has not yet returned
a complete certificate. The theorem below is the proposed final
assembly; F must remain open until Section 6 records a successful exact
replay and its audit is updated.

## Theorem and actual whole-period hypotheses

Let an actual finite positive vertex trajectory be a competitive normal
minimizing period for the Reinhardt problem, in the strict-star domain,
with entirely forward switches and at least six pieces. Retain the
actual twisted state/frame endpoint and costate seam, the free initial
state, and a single normal free-time Pontryagin lift. Normalize its
physical cost multiplier to `lambda=-1`, and assume

\[
C\le A_{\rm oct}.
\]

The proposed conclusion is that no such period exists. Factors may be
unequal. A zero first switching derivative or a third-control tie is
allowed. The argument is a uniform whole-period necessary-condition
exclusion; it does not construct a local shortcut or use an ordinary
Jacobi inertia count as a cost variation.

The finite-trajectory and normality inputs are the already established
whole-period results named in [HANDOFF](HANDOFF.md). The claim here is
only the sufficient global case F. It does not resolve M2 or by itself
establish the final sharp cost inequality and affine uniqueness.

## 1. The scale and Casimir constraints

Entirely forward active-margin coordinates have `N=3k+1`; thus `N>=6`
means `N>=7`. Choose a global minimum active margin `a`, with five
consecutive margins `(p,b,a,c,d_ext)`. Their indices are distinct.
The small-forward-minimum theorem and minimum threshold give

\[
\frac43<a^2<\frac{20}{11},\qquad
\frac{11}5<U:=\frac4{a^2}<3.
\tag{1}
\]

The actual normal primary costate is negative elliptic by
[GLOBAL_STRUCTURE_FORWARD_ELLIPTIC](GLOBAL_STRUCTURE_FORWARD_ELLIPTIC.md).
Write `kappa=sqrt(det Lambda_1)>0` in physical normalization and
`gamma^2=det mathsf U` in the normalized cyclic frame coordinates. Then

\[
\kappa^2=12\gamma^2.
\]

The exact octagon and pi bounds in
[GLOBAL_STRUCTURE_FORWARD_MINIMUM_THRESHOLD](GLOBAL_STRUCTURE_FORWARD_MINIMUM_THRESHOLD.md)
are

\[
A_{\rm oct}<2501/800,\qquad \pi>6283/2000.
\]

The complete-period cost--Casimir inequality consequently gives

\[
\kappa\le\frac{3A_{\rm oct}}{4\pi-2A_{\rm oct}}
<\frac{205}{138},
\qquad
\boxed{\gamma^2<\frac{42025}{228528}<\frac{23}{125}.}
\tag{2}
\]

The newer [spectral bound](GLOBAL_SPECTRAL_COST_CASIMIR.md) is stronger,
but this proof needs only (2). In particular `kappa<3/2`, so the
[acute-pairing theorem](GLOBAL_STRUCTURE_FORWARD_ACUTE.md) gives the
strictly positive central pairing `E=16e>0`.

## 2. The complete minimum domain

Set

\[
z=b/a,\quad w=c/a,\quad S=1+z,\quad T=1+w,
\quad K=1+U,\quad Z=z^2+U,\quad W=w^2+U,
\]
\[
h=\frac{(p+b)(a+b)}{b^2+4},\qquad
q=\frac{(a+b)(a+c)}{a^2+4}=ST/K,\qquad
k=\frac{(a+c)(c+d_{\rm ext})}{c^2+4}.
\]

These are three genuine complete positive arcs, so `h,q,k>1`.
Minimum and star inequalities give

\[
z,w\ge1,\qquad
\frac{S^2}{Z}\le h<\frac Sz\le2,\qquad
\frac{T^2}{W}\le k<\frac Tw\le2.
\tag{3}
\]

The seven-entry scalar cost comparison retains the five consecutive
actual margins and lowers all other active margins to `a`. Its use
in [GLOBAL_FORWARD_LINEAR_BUDGET](GLOBAL_FORWARD_LINEAR_BUDGET.md)
gives

\[
z+w<\frac53(U-1).
\tag{4}
\]

The independently reviewed and replayed
[neighbor contraction](GLOBAL_FORWARD_NEIGHBOR_CONTRACTION.md), using
(4) and the actual exterior floors, strengthens the neighbors to

\[
1\le z,w<5/4.
\tag{5}
\]

All comparisons behind (4) are scalar lower bounds on the original
whole-period cost; no comparison array is asserted to close its frame.
Neither (4) nor (5) uses the desired final Casimir exclusion.

The necessary scalar system is invariant under exchanging
`(z,h,u)` with `(w,k,v)`. Order `z<=w` using this algebraic symmetry.
For the finite certificate, enlarge all strict inequalities to weak
ones. The closed domain to cover is

\[
\begin{gathered}
11/5\le U\le3,\qquad1\le z\le w\le5/4,
\qquad1\le h,k\le2,\\
z+w\le5(U-1)/3,\qquad
S^2/Z\le h\le S/z,\qquad T^2/W\le k\le T/w.
\end{gathered}
\tag{6}
\]

The zero-duration circular base is handled with the explicit
nondegeneracy stated below. Every actual candidate is contained in
this closed relaxation.

## 3. Three stationary identities from the same lift

The normalized central Gram coordinates and conserved determinant are

\[
u=8d_{-1},\quad v=8d_0,\quad E=16e_0,
\qquad
\gamma^2=\frac{K^2}{16U^2}(4uv-E^2).
\tag{7}
\]

The actual free-initial-state normal stationarity equations give

\[
E=Su+Tv-A,\qquad
n_Lu+m_Lv=R_L,\qquad m_Ru+n_Rv=R_R,
\tag{8}
\]

with the exact coefficients in
[GLOBAL_FORWARD_CENTERED_SYSTEM](GLOBAL_FORWARD_CENTERED_SYSTEM.md),
Section 1. The genuine missing-control inequalities at the first and
last exterior switches give

\[
u\ge F_{z/S}(h),\qquad v\ge F_{w/T}(k),
\qquad F_\xi(r)=1+\xi^2r-\frac{\xi r\log r}{r-1}.
\tag{9}
\]

At `r=1`, use the continuous value `1-xi+xi^2`. Both floors are at
least `3/4`. They include equality at a third-control tie.

The physical rows underlying (8) are exactly `a` times the dimensionless
rows. They are supplied by the same actual primary costate in the
three consecutive prefix frames. This is not an arbitrary local
multiplier fitted to the three rows. The free-state boundary terms and
twisted costate endpoint have already been retained in deriving these
normal stationary identities.

If the chosen minimum window crosses the period seam, extend the active
coordinates cyclically with the prescribed relabeling and transport the
same costate across that seam. The local identities (8)--(9) are
unchanged. No exterior switch is removed, and the whole-period cost
used in (2) and (4) remains the original physical cost.

## 4. The central circular cube is excluded by hand

Let

\[
d=3-U,\quad x=z-1,\quad y=w-1,\quad
H=h-1,\quad I=k-1,\quad s=d+x+y.
\]

The broad circular theorem in the centered-system note proves, on the
actual stationary system,

\[
0\le s\le3/20,\quad1\le h,k\le2,
\quad s+H+I>0
\quad\Longrightarrow\quad
\gamma^2>37/200>23/125.
\tag{10}
\]

It uses only `u,v>=3/4`, not an additional cost estimate or switch gap.
Its exact lower fraction is
`5277274431423/28464128000000`. The proof first obtains
`(u-3/4)+(v-3/4)<=(9/5)s^2` by positive row sums and a cubic residual
estimate, then applies the centered Casimir identity.

Choose `eta=1/32`. The central cube

\[
95/32\le U\le3,\qquad1\le z,w\le33/32
\tag{11}
\]

has `s<=3/32<3/20`, so (10) contradicts (2) there. Every actual
window satisfies the nondegeneracy: (1) already gives `d>0`.

The algebraic base `d=x=y=H=I=0` must not be claimed impossible from
(8)--(9) alone. Its outer coefficient rows vanish and leave a fibre
of covectors. All three factors equal one there, so it is not an actual
positive window. This is the only omitted nondegeneracy point in the
hand statement; the finite cover does not silently divide by its
stationarity determinant.

## 5. Exact functions and cover for the complement

Outside (11), the positive determinant

\[
D=m_Lm_R-n_Ln_R
\]

has the exact positive factorization in the centered-system note. It
satisfies `D>=K^4(q-1)^2/(STZW)`, and `q-1>=eta/4=1/128` on every
initial complementary rectangle. Consequently the remaining two norm
coordinates are uniquely recovered from the centered rows:

\[
\delta u:=u-3/4=\frac{m_Lr_R-n_Rr_L}{D},\qquad
\delta v:=v-3/4=\frac{m_Rr_L-n_Lr_R}{D}.
\tag{12}
\]

The source
[global_forward_completion_casimir_certificate.cpp](../explorations/global_forward_completion_casimir_certificate.cpp)
starts with exactly these three rational rectangles, all with
`h,k in [1,2]`:

| Root | `U` | `z` | `w` |
|---|---|---|---|
| 1 | `[11/5,95/32]` | `[1,5/4]` | `[1,5/4]` |
| 2 | `[95/32,3]` | `[33/32,5/4]` | `[1,5/4]` |
| 3 | `[95/32,3]` | `[1,33/32]` | `[33/32,5/4]` |

These cover the complement, retaining all shared boundary faces. The
ordering, linear budget and factor bounds in (6) then contract the boxes
by necessary inequalities.

The code evaluates the actual centered logarithmic remainder
`f(r)=(r-r^{-1})/2-log r` with fourteen terms of its positive rational
series and a rigorous upper tail. It uses the actual rational formulas
for `f'` and `f''`. The two norm floors use ten positive terms of the
series for `f(h)/(h-1)`, giving fixed rational lower bounds `dl,dr` on
`F(h)-3/4`, including at `h=1`.

At every candidate the following five quantities must be nonnegative:

\[
\begin{gathered}
r_L-n_Ldl-m_Ldr,\qquad r_R-m_Rdl-n_Rdr,\\
\delta u-dl,\qquad\delta v-dr,\qquad E.
\end{gathered}
\tag{13}
\]

The remaining test is the exact centered expression for

\[
\gamma^2-23/125,
\tag{14}
\]

which must be nonpositive in the enlarged competitive domain.
Thus a negative upper bound for any member of (13), or a strictly
positive lower bound for (14), excludes the whole current box.

All value, gradient and Hessian enclosures use exact GMP rational
arithmetic rounded outward to a fixed dyadic grid after operations.
The second-order Taylor enclosure uses the exact rational midpoint,
`[0,r_i^2]` for a diagonal quadratic coordinate, and
`[-r_i r_j,r_i r_j]` for an off-diagonal one. Direct interval and Taylor
enclosures are intersected. A denominator interval containing zero
causes subdivision and never counts as an excluded box.

The checker bisects a remaining interval at its exact midpoint. A
nonempty final stack or a depth-limit box causes failure. No floating
sign, sampled trajectory, numerical optimizer, or bound on word length
is part of these exclusions. The
[independent audit](GLOBAL_FORWARD_CASIMIR_CERTIFICATE_AUDIT.md)
reviews the rational approximations, complete cover, contractions,
normalization, source operations and Taylor scope.

## 6. Pending finite verification and final implication

**Pending:** record the full exact program's completed node, leaf and
depth counts here after it returns an empty stack, zero depth-limit
boxes and its `PASS` message. No partial count is a proof. The full
source review is complete; the final replay has not yet completed at
this note's creation.

To run the exact verifier with a C++17 compiler and GMP headers:

```sh
g++ -O2 -std=c++17 explorations/global_forward_completion_casimir_certificate.cpp -lgmpxx -lgmp -o /tmp/forward_casimir_certificate
/tmp/forward_casimir_certificate
```

If this finite verification succeeds, (13)--(14) exclude every point of
the complementary domain that could come from an actual competitive
period. Equation (10) excludes its central cube. These two exhaustive
alternatives contradict (2) for the chosen global minimum and therefore
exclude every competitive all-forward minimizing period with `N>=6`.
The number and unequal factors of the rest of the period never enter a
word catalogue. This final implication will close case F only after the
pending verification is complete and independently audited.
