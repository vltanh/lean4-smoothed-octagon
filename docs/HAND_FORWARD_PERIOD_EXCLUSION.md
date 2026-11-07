# Hand exclusion of every long all-forward competitive period

Date: 2026-11-07 UTC. Complete hand argument, with independent internal
reviews of the scalar proof and the actual-period interface.

**Conclusion.** The all-forward gate H-F is closed without an interval
cover or an executable sign premise. The theorem below replaces both
computer-assisted F exclusions in the active hand route. The mixed
smaller-short and smaller-nonshort exclusions remain separate open gates;
this note does not assert completion of the full hand proof.

## 1. The actual-period theorem

Let an actual finite strict-star vertex period have positive durations,
entirely forward switches, and the full twisted frame and state
endpoints. Retain its free initial state, the twisted cotangent endpoint,
and one normal free-time Pontryagin lift, with the physical cost
multiplier normalized to \(\lambda=-1\). Suppose
\[
N\ge6,\qquad C\le A_{\rm oct}.
\tag{1}
\]
Then no such period exists.

The statement permits unequal factors, repeated minimum values, weak
missing-control ties and zero first switching derivatives. It assumes
the actual normal lift; it does not obtain a multiplier by solving a
local endpoint-rank equation.

The [cyclic forward coordinates](GLOBAL_STRUCTURE_FORWARD_ELLIPTIC.md)
give \(N=3j+1\). Thus (1) implies \(N\ge7\). Choose a global minimum
active margin \(a\), and retain the five consecutive actual margins
\[
(p,b,a,c,d_{\rm ext}).
\]
These five indices, and the two further indices needed by the
seven-entry cost comparison, are distinct when \(N=7\), and hence
also when \(N>7\). A cut through the twisted seam changes their labels,
not their identities or the physical multiplier.

Set
\[
U=\frac4{a^2},\quad z=\frac ba,\quad w=\frac ca,\quad
S=1+z,\quad T=1+w,\quad K=1+U,\quad
Z=z^2+U,\quad W=w^2+U,
\]
\[
h=\frac{(p+b)(a+b)}{b^2+4},\qquad
q=\frac{(a+b)(a+c)}{a^2+4}=\frac{ST}{K},\qquad
k=\frac{(a+c)(c+d_{\rm ext})}{c^2+4}.
\tag{2}
\]
The factors \(h,q,k\) are those of three genuine complete positive
arcs in this period.

## 2. Hand geometric restrictions and the seven-edge budget

The [small-forward-minimum hand theorem](SMALL_FORWARD_MINIMUM_HAND_PROOF.md),
together with the unchanged actual-lift identities and easy faces in
Sections 1--5 of
[MIXED_GLOBAL_SMALL_FORWARD_MINIMUM](MIXED_GLOBAL_SMALL_FORWARD_MINIMUM.md),
gives \(a^2>4/3\). Its hard face is proved by
[HAND_H5_INTEGRAL_RATIONAL_BOUND](HAND_H5_INTEGRAL_RATIONAL_BOUND.md);
the former large H5 coefficient table is not used.

The coordinatewise cost argument in Section 2 of
[GLOBAL_STRUCTURE_FORWARD_MINIMUM_THRESHOLD](GLOBAL_STRUCTURE_FORWARD_MINIMUM_THRESHOLD.md)
gives \(a^2<20/11\). Consequently
\[
\frac{11}{5}<U<3,\qquad z,w\ge1.
\tag{3}
\]
Minimum and strict-star conditions give
\[
\frac{S^2}{Z}\le h<\frac Sz,\qquad
\frac{T^2}{W}\le k<\frac Tw.
\tag{4}
\]
In particular, both lower factors in (4) are strictly greater than
one, since \(1+2z-U>0\) and \(1+2w-U>0\).

Here is the precise whole-period accounting used to retain both exterior
factors. Let \(G\) be the symmetric edge function of
[GLOBAL_STRUCTURE_FORWARD_MINIMUM_BUDGET](GLOBAL_STRUCTURE_FORWARD_MINIMUM_BUDGET.md);
the actual cost satisfies
\[
C=\frac{\sqrt{12}}8\sum_iG(a_i,a_{i+1}).
\]
Coordinatewise monotonicity of this cyclic scalar action allows all
margins outside the five retained indices to be lowered to \(a\).
For \(N=7\), the resulting seven entries are
\((a,p,b,a,c,d_{\rm ext},a)\), with their seven cyclic edges counted
once. For \(N>7\), the same expression has \(N-7\) additional copies of
\(G(a,a)>0\), which can be dropped. Positivity follows from
\(a^2>4/3\) and the diagonal edge derivative.

Moreover
\[
G_{xy}(x,y)=2\left(1-\frac{xy}{(x+y)^2}\right)>0.
\]
Integrating this derivative over the rectangle based at \((a,a)\)
gives
\[
G(ar,as)\ge G(ar,a)+G(a,as)-G(a,a),\qquad r,s\ge1.
\]
Apply this to the two distinct retained edges \((p,b)\) and
\((c,d_{\rm ext})\). With
\[
P=\frac pa=\frac{hZ}{S}-z,\qquad
D_{\rm ext}=\frac{d_{\rm ext}}a=\frac{kW}{T}-w,\qquad
g_U(r)=\frac{G(a,ar)}{a^2},
\]
the resulting cost bound is
\[
C\ge\frac{\sqrt3}{U}
 \{2g_U(P)+2g_U(z)+2g_U(w)+2g_U(D_{\rm ext})-g_U(1)\}.
\tag{5}
\]
All four ratios lie in \([1,U]\): their lower bounds follow from
global minimality, and \(Pz<U,\ wD_{\rm ext}<U,\ z<U,\ w<U\)
follow from the four actual strict-star inequalities.

Section 3 of [HAND_FORWARD_LEMMAS](HAND_FORWARD_LEMMAS.md) now applies.
The function \(g_U\) is increasing and concave on \([1,U]\). If
\[
P+z+w+D_{\rm ext}\ge2+\frac53(U-1),
\]
one lowers that sum to equality and concentrates its excess above four
in one coordinate. The scalar lower bound (5) is then at least
\[
\frac{\sqrt3}{U}
 \left\{2g_U\!\left(\frac{5U-8}{3}\right)+5g_U(1)\right\}>A_{\rm oct}.
\]
The last one-variable sign is the explicit twelve-coefficient identity
with positive coefficients in
[GLOBAL_FORWARD_LINEAR_BUDGET](GLOBAL_FORWARD_LINEAR_BUDGET.md).
Its displayed identity and sign argument are the mathematical input;
running its supplementary checker is not a premise. This contradicts
(1), so
\[
\boxed{\frac{hZ}{S}+\frac{kW}{T}<\frac{5U+1}{3}.}
\tag{6}
\]
Since \(P,D_{\rm ext}\ge1\), this also gives
\(z+w<5(U-1)/3\).

The [integral neighbor proof](HAND_FORWARD_NEIGHBOR_INTEGRAL.md)
and its [asymmetric completion](HAND_FORWARD_ASYMMETRIC_NEIGHBOR_BOUND.md)
therefore apply, giving
\[
1\le z,w<\frac43.
\tag{7}
\]
Their use of (6) is legitimate: the proof of that budget required only
(3)--(4), the actual cost and \(N\ge7\), not the neighbor conclusion.

Every comparison in this section concerns a scalar lower bound on the
original cost. No lowered array is asserted to satisfy the frame
endpoint or the Pontryagin equations.

## 3. One common covector supplies both floors and the centered row

The common-lift identities in Sections 1--2 of
[MIXED_GLOBAL_SMALL_FORWARD_MINIMUM](MIXED_GLOBAL_SMALL_FORWARD_MINIMUM.md)
and their normalized form in
[GLOBAL_FORWARD_CENTERED_SYSTEM](GLOBAL_FORWARD_CENTERED_SYSTEM.md)
give actual coordinates \(u,v,E\) of the same primary multiplier.
Write
\[
\delta u=u-\frac34,\qquad \delta v=v-\frac34,\qquad
f(s)=\frac{s-s^{-1}}2-\log s.
\]
The genuine exterior missing-control inequalities give
\[
\delta u\ge L(z,h),\qquad \delta v\ge L(w,k),
\]
where
\[
L(z,h)=\frac{(z-1)\{z-1+2z(h-1)\}}{4(1+z)^2}
       +\frac{zh}{1+z}\frac{f(h)}{h-1}\ge0.
\tag{8}
\]
The quotient has its continuous value at one. The actual factors here
are greater than one. The floor is increasing in the exterior factor,
so with \(I=T^2/W\),
\[
\delta u\ge L(z,h)\ge0,\qquad
\delta v\ge L(w,I)\ge0.
\tag{9}
\]
The inequalities remain valid when the missing Hamiltonian also ties.

Exchange the two scalar rows, together with
\((z,h,u)\) and \((w,k,v)\), if necessary so that \(z\le w\).
This is an algebraic symmetry of the equations for the same lift. It
does not posit a time-reversed physical trajectory or a new normal
multiplier. Henceforth \(v\) is the norm on the side of the larger
neighbor.

Put \(H=h-1\). The first centered stationary row is exactly
\[
n\,\delta u+m\,\delta v=r,
\tag{10}
\]
\[
n=\frac{S^2(U-z)H}{Z}>0,\qquad
m=\frac{K^2}{SZ}\{q-1+H(Sq-1)\}>0.
\]
The explicit \(r\) is equation (20) of
[HAND_FORWARD_CONDITIONAL_NORM_BOUNDS](HAND_FORWARD_CONDITIONAL_NORM_BOUNDS.md);
it is an identity obtained from the actual three stationarity equations.
Those identities use conjugates of the original covector across the
window and the true twisted seam. They do not fit independent
multipliers to the three arcs.

The exact positive difference is
\[
SZ(m-n)
 =K(ST-K)+H\{S^4-K^2+KS^2(T-S)\}>0.
\tag{11}
\]
No inverse of the two-row coefficient matrix is needed.

From (6) and \(k\ge I\), the actual left factor satisfies the weak
enlargement
\[
\frac{S^2}{Z}\le h\le\frac{S(5U-2-3w)}{3Z}.
\tag{12}
\]
Equations (3), (7), (9)--(12) are precisely the ordered scalar
hypotheses of the new norm proof.

## 4. The two hand norm bounds

Define
\[
\mathcal E_\Sigma
 =r-\frac n{35}-(m-n)L(w,I),\qquad
\mathcal E_v=r-nL(z,h)-\frac m{64}.
\tag{13}
\]
Equations (9)--(11) imply
\[
\delta u+\delta v\ge\frac1{35}\ \Longrightarrow\
 \mathcal E_\Sigma\ge0,\qquad
\delta v\ge\frac1{64}\ \Longrightarrow\ \mathcal E_v\ge0.
\tag{14}
\]

Both residuals are nonincreasing in \(w\) at fixed \(U,z,h\).
The exact derivative identities, proved in Section 4 of
[HAND_FORWARD_CONDITIONAL_NORM_BOUNDS](HAND_FORWARD_CONDITIONAL_NORM_BOUNDS.md),
are
\[
(\mathcal E_\Sigma)_w
 =\alpha\{B(w/T)-V(w)\}-(m-n)V_w\le0,
\]
\[
(\mathcal E_v)_w=\alpha\{B(w/T)-49/64\}<0,
\]
where \(\alpha=K(1+SH)/Z>0\),
\(B(s)=1-s+s^2\), and
\(V(w)=3/4+L(w,T^2/W)\ge B(w/T)\), with \(V_w\ge0\).
The final strict inequality uses \(B(w/T)\le37/49<49/64\).

Lowering \(w\) to \(z\) raises the two residuals and enlarges the upper
bound in (12). It therefore suffices to prove both strict negative
signs on
\[
1\le z\le\frac43,\qquad 1+\frac65z\le U<3,\qquad
\frac{(1+z)^2}{z^2+U}\le h\le
\frac{(1+z)(5U-2-3z)}{3(z^2+U)}.
\tag{15}
\]
The lower bound for \(U\) is exactly the nonemptiness condition for
this factor interval. This comparison never changes the actual norms
or claims that a symmetric endpoint solves the physical equations.

The [initial-value and low-D proof](HAND_FORWARD_SYMMETRIC_SUM_REDUCTION.md)
and [high-D proof](HAND_FORWARD_SYMMETRIC_SUM_HIGH_D.md) prove
\(\mathcal E_\Sigma<0\) on all of (15), splitting at \(D=38/243\).
The [larger-norm proof](HAND_FORWARD_LARGER_NORM_HAND_PROOF.md) proves
\(\mathcal E_v<0\) there, by exterior-factor concavity and two strict
tangent signs. Their displayed inequalities cover the shared boundary,
equal neighbors, and collapsed factor intervals. The
[independent scalar audit](HAND_FORWARD_NORM_AUDIT.md) accepts both
complete arguments.

The comparisons and (14) therefore imply, for the original data,
\[
\boxed{\delta u+\delta v<\frac1{35},\qquad
       \delta v<\frac1{64}.}
\tag{16}
\]

## 5. The lower and upper Casimir bounds concern the same lift

Let \(\mathsf U\) denote the normalized traceless primary multiplier in
the cyclic coordinates; this matrix is distinct from the scalar
\(U=4/a^2\). Set \(\gamma^2=\det\mathsf U\).
The exact central identity is
\[
\gamma^2=\frac{K^2}{16U^2}
 \left\{4(3/4+\delta u)(3/4+\delta v)
 -(E_0+S\delta u+T\delta v)^2\right\},
\tag{17}
\]
\[
E_0=1-\frac K8+\frac1K
     -f(S/2)-f(T/2)-f(4/K).
\]
The elementary cubic bounds for \(f\) give \(E_0>0\) throughout the
stated domain; no acute-pairing theorem is needed for this step.

Section 2 of
[HAND_FORWARD_CONDITIONAL_NORM_BOUNDS](HAND_FORWARD_CONDITIONAL_NORM_BOUNDS.md)
applies to (16)--(17) and gives
\[
\boxed{\gamma^2>\frac{23}{125}.}
\tag{18}
\]
Its proof uses a concave quadratic on the norm polygon, two norm
vertices and an explicit one-variable minimum. Its final positive
margin is
\[
\frac{89}{9464000}-\frac{983}{113836800}
 =\frac{73961}{96192096000}>0.
\]
It therefore covers the full scale interval, including parameters
arbitrarily near the circular limit. No separate interval-Hessian or
central-cube exclusion is needed.

On the other hand,
[GLOBAL_STRUCTURE_FORWARD_ELLIPTIC](GLOBAL_STRUCTURE_FORWARD_ELLIPTIC.md)
proves that this actual primary multiplier is negative elliptic.
Its physical normalization satisfies
\[
\kappa^2=12\gamma^2.
\]
The [spectral cost theorem](GLOBAL_SPECTRAL_COST_CASIMIR.md), the full
twisted frame endpoint, and \(C\le A_{\rm oct}<\pi\) give the strict
competitive cap proved in
[HAND_PROOF_REFINEMENTS, Section 1](HAND_PROOF_REFINEMENTS.md#1-a-sharper-competitive-casimir-bound):
\[
\gamma^2<\frac{9193}{50000}<\frac{23}{125}.
\tag{19}
\]
The scaling between the physical and cyclic multipliers is fixed in
the actual normal boundary identity. Thus (18) and (19) constrain the
same conserved determinant. The contradiction proves the theorem.

## 6. Boundary, period and dependency audit

An independent reading of the whole-period interface checked the
following points.

- The cyclic count \(N=3j+1\) makes seven, rather than six, the smallest
  eligible positive period. The five retained stationarity indices and
  all seven budget indices are distinct. Each edge is counted once at
  \(N=7\), and each discarded extra edge at \(N>7\) is positive.
- The strong budget precedes the neighbor proof and both norm signs.
  Its proof does not use a norm conclusion, a Casimir lower bound,
  the older factor bound \(q<7/4\), or any assumption that a scalar
  comparison closes the frame.
- The two floors are actual missing-control inequalities at the
  original exterior switches. The floor used for the larger neighbor
  is weakened only by the proved monotonicity in its exterior factor.
  The sum proof and larger-norm proof use the same stationary row.
- The exchange of the two sides preserves the meaning of the larger
  neighbor's norm in the asymmetric bound \(1/64\). Every subsequent
  symmetrization preserves the stated scalar domain and has the
  correct residual direction.
- Weak minimum ties, third-control ties and zero switching derivatives
  are retained. The proof is pointwise on \(U<3\); it assumes no
  uniform distance from \(U=3\), no positive minimum dwell time, and
  no endpoint-rank condition. Its final Casimir separation has a
  uniform positive margin.
- In the global application, zero-duration pieces are deleted and
  adjacent equal controls are merged before counting \(N\), with the
  usual twisted rebasing. If that reduced description has at least
  six positive all-forward pieces, this theorem applies. If deletion
  changes its sign class or reduces the count, the corresponding
  whole-period class or terminal theorem applies instead. This note
  makes no assertion about an unconstrained all-zero-duration
  algebraic covector fibre.

The active F chain consists of the named hand minimum, scalar cost,
neighbor, norm and Casimir arguments. It does not use either old F
interval cover, the old H5 table, a word-length enumeration, the
stronger computational neighbor bound \(5/4\), or the unfinished
rational-triangle and norm-sum-\(1/39\) alternatives. Every retained
polynomial sign is supplied by the displayed finite identities and
elementary inequalities in the linked proofs; supplementary symbolic
checks are not logical premises.

This is an internal mathematical acceptance of H-F under the theorem's
finite normal-period hypotheses. Deriving that representation from an
unrestricted minimizing disk retains the separately named geometric,
compactness, maximum-principle, finiteness and normality inputs. The
remaining mixed-period gates and final hand-only assembly must still be
completed before asserting the unrestricted sharp theorem without
computer assistance.
