# Hand exclusion of the nonshort forward successor

Date: 2026-11-08 UTC.

This note assembles a hand exclusion of the actual forward-successor
alternative at the smaller nonshort turn beside a global minimum reverse
centre. Together with the
[reverse-successor hand theorem](MIXED_NONSHORT_REVERSE_HAND_EXCLUSION.md),
it excludes both actual successor signs in the smaller-nonshort case.
All statements are under the retained geometric, finite-normal-period,
and PMP inputs of the hand-proof dependency ledger.

**Theorem.** A competitive finite normal mixed period cannot have a
smaller adjacent turn at a global minimum reverse centre whose forward
run is nonshort and whose next actual switch, in the continuation
alternative, is forward.

The proof is uniform in the number of arcs. It retains the actual
common normal covector, the actual first forward event, and the actual
next switch, including a next switch across the twisted seam. No
nonshort forward interval certificate is a premise.

## 1. Actual geometry and the retained scalar conditions

Use the actual same-covector setup of
[MIXED_SMALLER_TURN_CONTINUATION](MIXED_SMALLER_TURN_CONTINUATION.md).
After the allowed reflection/time reversal, the smaller adjacent turn
is the outgoing turn. Let the physical margins at the central reverse
arc, this turn, the first forward event, and the following arc be
\(a,c_{\rm phys},d,r_{\rm phys}\), respectively. In particular
\(a<c_{\rm phys}\), \(d>a\), and the global minimum property gives
\(r_{\rm phys}\ge a\). Put
\[
T=a+c_{\rm phys},\qquad
 t=\frac aT,\qquad x=\frac{d-a}{T},\qquad
 k=\frac{a^2+4}{T^2},
\]
\[
c=1-t,\qquad p=t+x,\qquad W=1+x,\qquad
 j=p-c=2t+x-1,
\]
\[
q=\frac{(c_{\rm phys}+d)(d+r_{\rm phys})}{d^2+4}>1,
\qquad e=q/W.
\tag{1}
\]
Here c and p are normalized margins; they are not new physical turns.
The original incoming turn norm is
\[
v=1+\frac{c^2}{W}-\frac{c\log W}{x}>\frac34,
\]
and its original missing-control condition is
\[
F_{p/W}(q)\le v,\qquad
F_\eta(q)=1+\eta^2q-\frac{\eta q\log q}{q-1}.
\tag{2}
\]
The incoming derivative inequality also gives
\(v>g:=1-cp/W^2\).

The common hand prerequisites supply
\[
\frac14<t<\frac25,\qquad
1\le k<1+j,\qquad j>0,\qquad
k>\frac{29}{4}t^2,
\]
\[
q<\frac{W}{1+2j}.
\tag{3}
\]
The references and roles of these inequalities are as follows.
The [low-scale hand theorem](MIXED_NONSHORT_LOW_SCALE_HAND_EXCLUSION.md)
and the
[conditional scale bound](MIXED_NONSHORT_CONDITIONAL_SCALE_BOUND.md)
give \(a>1/2\), \(a<4/5\), and therefore
\(k/t^2=1+4/a^2>29/4\).
The [high-ratio hand theorem](MIXED_NONSHORT_HIGH_T_HAND_EXCLUSION.md)
gives \(t<2/5\), and Section 1 of the
[ratio reduction](MIXED_NONSHORT_FORWARD_RATIO_REDUCTION.md)
gives \(t>1/4\).
The common-order corollary in Section 5 of the
[reverse-successor hand theorem](MIXED_NONSHORT_REVERSE_HAND_EXCLUSION.md)
gives \(k<2t+x=1+j\), without assuming that the actual successor is
reverse. Finally the
[quantitative swap bound](MIXED_NONSHORT_QUANTITATIVE_SWAP_BOUND.md)
gives the last inequality in (3) from the unchanged incoming secant
and floor.

The same-lift scalar comparison toward the central boundary gives two
further necessary inequalities:
\[
N<0,\qquad \mathcal T_*\ge\frac34.
\tag{4}
\]
Here N is the incident-upper residual numerator, and
\(\mathcal T_*\) is the transported next norm at the solved scalar
boundary root. The
[forward boundary reduction](MIXED_NONSHORT_FORWARD_BOUNDARY_REDUCTION.md),
Sections 1--2, proves exactly this transfer: the boundary outgoing norm
is smaller than the actual outgoing norm, and the transported next norm
strictly decreases as that outgoing norm increases. The actual forward
successor has next norm at least \(3/4\), so (4) follows. The comparison
does not assert that the scalar boundary is a trajectory or has the
actual competitive Casimir.

Equations (1)--(4) are the inputs to the ratio and gap arguments below.
Their incoming secant, missing-control floor, event factor, and physical
geometry are the original ones.

## 2. The duration ratio is strictly greater than one third

The complete
[low-ratio hand exclusion](MIXED_NONSHORT_LOW_RATIO_HAND_EXCLUSION.md)
shows that (1)--(4) are incompatible with \(t\le1/3\). Its
[independent audit](MIXED_NONSHORT_LOW_RATIO_HAND_AUDIT.md)
checks the comparison signs, the permitted scalar lowering of k, and
the entire closed polynomial domain. Therefore every hypothetical
remaining actual point satisfies
\[
\boxed{t>\frac13.}
\tag{5}
\]
This theorem uses the actual forward-successor condition in (4). It
retains (2) at its original coordinates and does not infer a physical
norm floor at an auxiliary shape.

## 3. The gap is strictly smaller than one thirtieth

Suppose, for a contradiction, that \(j\ge1/30\). Set
\(h=1-2t\). The
[large-gap multiplier theorem](MIXED_NONSHORT_LARGE_GAP_MULTIPLIER_SIGNS.md),
Section 1, uses the original incoming derivative inequality and the
positive-integral secant estimate to prove
\[
\frac15<h<\frac13,\qquad
\frac1{30}\le j<\frac{5h}{7},\qquad x=h+j.
\tag{6}
\]
Together with (3), the actual point belongs to the closed comparison
domain
\[
\frac15\le h\le\frac13,\quad
\frac1{30}\le j\le\frac{5h}{7},\quad
1\le q\le1+\frac{h-j}{1+2j},\quad
1\le k\le1+j.
\tag{7}
\]
There are two exhaustive ratio cases.

### 3.1. The range \(1/3<t\le3/8\)

Let \(u=15(t-1/3)\), \(y=q-1\), and use the positive multipliers
\[
\alpha=\frac{27}{4}-3u-24y+16j,\qquad
M=\frac14-u+6y+24j.
\]
The exact original combination is
\[
\mathcal H
=\alpha N+C_*(3/4-\mathcal T_*)
       +M\{F_{p/W}(q)-v\}<0,
\tag{8}
\]
where \(C_*>0\). The strict sign follows from \(N<0\),
\(\alpha>0\), and the two weak inequalities in (2) and (4).
The multiplier theorem proves that the coefficients of v and
\(\log q\) in this expression are strictly negative at fixed geometry.
Using the proved integral secant majorant \(V>v\) and logarithm
majorant \(L_+>\log q\) therefore gives the rational necessary sign
\[
G<0.
\tag{9}
\]
Its exact definition and the sign of every substitution are those of
the multiplier theorem; no additional bound is imposed at the enlarged
scalar norm V.

At fixed \((t,x,q)\), G is a strictly concave quadratic in k, with
quadratic coefficient
\[
-\frac{tW^2De^3}{4}<0.
\tag{10}
\]
The [low-t unit-shape sign](MIXED_NONSHORT_LARGE_GAP_LOW_T_SIGN.md)
proves \(G(t,j,q,1)>0\) on the full closed domain (7) with
\(1/3\le t\le3/8\). The
[upper-shape sign](MIXED_NONSHORT_LARGE_GAP_UPPER_SHAPE_SIGN.md)
proves \(G(t,j,q,1+j)>0\) on the larger closed domain (7).
The actual k lies between these two endpoints by (3).
Concavity consequently gives \(G>0\) at the actual k, contradicting
(9).

The weaker lower endpoint k=1 is intentional here: positivity on the
whole interval \([1,1+j]\) already covers the actual point, regardless
of its additional scale lower bound \(k>29t^2/4\).

### 3.2. The range \(3/8\le t<2/5\)

The
[high-ratio large-gap hand theorem](MIXED_NONSHORT_HIGH_RATIO_LARGE_GAP_EXCLUSION.md)
excludes exactly this case under (1)--(4) and (6).
It uses the simpler positive multipliers 4 and 1 in place of
\(\alpha,M\). After the justified scalar substitutions, its rational
residual \(G_4\) must be negative at the actual point.

That theorem proves \((G_4)_k>0\), so lowering k to \(29t^2/4\)
preserves this necessary negative sign. It then proves the opposite
strict sign on that entire scale face. Its
[polynomial monotonicity lemma](MIXED_NONSHORT_HIGH_RATIO_POLYNOMIAL_MONOTONICITY.md)
reduces the sign to \(h=1/4\), and a concavity argument in \(q-1\)
reduces it to two explicit positive endpoints. Its
[independent audit](MIXED_NONSHORT_HIGH_RATIO_LARGE_GAP_AUDIT.md)
checks both the scalar comparisons and the complete polynomial signs.
Thus this ratio case is impossible as well.

The two cases cover every \(t\) allowed by (3) and (5); their overlap
at \(t=3/8\) causes no difficulty. The supposition \(j\ge1/30\)
has been contradicted. Therefore
\[
\boxed{0<j<\frac1{30}.}
\tag{11}
\]

## 4. The remaining small-gap domain contradicts the actual Casimir cap

The actual point now satisfies (5) and (11), so the complete
[small-gap hand exclusion](MIXED_NONSHORT_SMALL_GAP_HAND_EXCLUSION.md)
applies. Its central comparison can be summarized directly.
First, \(k<1+j<31/30\), and the
[small-gap chi theorem](MIXED_NONSHORT_SMALL_GAP_CHI_BOUND.md)
gives
\[
\chi=pe>\frac47.
\]
With the unchanged actual incoming norm v, define the central upper
envelope
\[
Y=x(x+2),\quad s=k-t^2,\quad B=s+p^2,
\]
\[
H=\frac{k}{t}(v-1+t^2)+t(2-t),\qquad
w_U=\frac{k^2-kt+t^2+HY+vY^2}{B^2}.
\]
The proved upper-envelope comparison gives
\(w_U>w_{\rm actual}>3/4\).

On the original first-event stationarity line, let \(\Gamma(w)\)
be the squared Casimir as a function of the outgoing norm. The
[stationary Casimir monotonicity theorem](MIXED_NONSHORT_FORWARD_CASIMIR_MONOTONICITY.md)
uses \(t\ge1/3\) and \(\chi>4/7\) to give
\(\Gamma'(w)<0\) for every \(w\ge3/4\). Hence
\[
\Gamma_{\rm actual}>\Gamma(w_U).
\tag{12}
\]
The [event-factor elimination](MIXED_NONSHORT_FORWARD_Q_ELIMINATION.md)
uses the unchanged incoming floor (2), and the
[scalar envelope Casimir theorem](MIXED_NONSHORT_FORWARD_ENVELOPE_CASIMIR_SIGN.md)
then proves
\[
\Gamma(w_U)>\frac{9193}{50000}.
\tag{13}
\]
These statements include the sign needed before squaring the diagonal
comparison; their actual-coordinate interface is established in the
small-gap theorem and its cited audits.

The competitive period cap from
[HAND_PROOF_REFINEMENTS](HAND_PROOF_REFINEMENTS.md), Section 1, is
\[
\Gamma_{\rm actual}<\frac{9193}{50000}.
\tag{14}
\]
Equations (12)--(14) contradict each other. This completes the proof of
the theorem.

In this comparison, \(\Gamma(w_U)\) is evaluated on the original
forward-event stationarity line. Its diagonal is not identified with
the diagonal of the central upper-envelope reconstruction. The cost
cap (14) is used only for the actual common covector.

## 5. Uniform scope and the completed nonshort alternative

The continuation theorem starts from one actual common primary normal
covector and transports it by the actual prefix-frame conjugations.
The first forward event is genuine. Finiteness supplies the next actual
switch, and the same formulas remain valid when that switch crosses
the twisted seam. The comparisons in this proof are scalar
inequalities applied to those fixed data. They introduce no new
trajectory, costate, initial-state constraint, or candidate stationary
root.

No number-of-arcs bound or word enumeration was used. The theorem thus
excludes the forward-successor branch for every competitive finite
normal mixed period with the stated smaller-nonshort assignment.
The independently proved
[reverse-successor hand theorem](MIXED_NONSHORT_REVERSE_HAND_EXCLUSION.md)
excludes the other actual successor branch. Those branches are exhaustive
by the same-covector continuation alternative. Therefore the entire
smaller-nonshort case is excluded by hand.

This is the H-N conclusion. The smaller-short case and the final global
assembly are separate statements with their own hypotheses and audits.


The [independent forward hand audit](MIXED_NONSHORT_FORWARD_HAND_AUDIT.md)
accepts the complete domain, all three shape signs and the actual-period
interface, and records H-N as closed.
