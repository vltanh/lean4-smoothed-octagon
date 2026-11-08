# The nonshort forward case is excluded on the small-gap domain

Date: 2026-11-08 UTC. Hand theorem on an explicitly restricted actual
domain. The two restrictions in (1) are not asserted for every remaining
window. In particular this theorem alone does not close H-N-forward.

Use the actual smaller-nonshort window, its common normal covector,
its actual first forward event and its actual forward successor. Keep
the normalized notation
\[
t=\frac{a}{a+c_{\rm phys}},\qquad
x=\frac{d-a}{a+c_{\rm phys}},\qquad
k=\frac{a^2+4}{(a+c_{\rm phys})^2},
\]
\[
c=1-t,\quad p=t+x,\quad W=1+x,\quad j=p-c,
\quad s=k-t^2,\quad B=s+p^2,\quad e=q/W.
\]

**Theorem.** No competitive actual window of this type can satisfy
\[
\boxed{t\ge\frac13,\qquad j\le\frac1{30}.}
\tag{1}
\]

The proof below uses only the retained hand prerequisites and the new
scalar hand inequalities. It does not use either nonshort forward
interval certificate.

## 1. All parameters belong to the proved scalar domain

The common hand results give
\[
\frac14<t<\frac25,\qquad 0<j,\qquad
1\le k<1+j,\qquad k>\frac{29}{4}t^2.
\tag{2}
\]
These are respectively the
[ratio reduction](MIXED_NONSHORT_FORWARD_RATIO_REDUCTION.md),
[high-ratio exclusion](MIXED_NONSHORT_HIGH_T_HAND_EXCLUSION.md),
[common-order corollary](MIXED_NONSHORT_REVERSE_HAND_EXCLUSION.md),
and [common scale bound](MIXED_NONSHORT_CONDITIONAL_SCALE_BOUND.md).
They use the original geometry and do not assume (1).

Under (1), (2) implies \(1\le k<31/30\). The
[small-gap chi lemma](MIXED_NONSHORT_SMALL_GAP_CHI_BOUND.md) further
gives \(\chi=pe>4/7\). Its proof retains the exact original incoming
norm and lowers only a scalar residual in k.

The original incoming secant and its missing-control floor are
\[
v=1+\frac{c^2}{W}-\frac{c\log W}{x}>\frac34,
\qquad q>1,\qquad F_{p/W}(q)\le v.
\tag{3}
\]
The elementary logarithm bound in the
[factor-elimination theorem](MIXED_NONSHORT_FORWARD_Q_ELIMINATION.md)
gives
\[
v<V:=1+\frac{c^2}{W}-\frac{3c(x+2)}{x^2+6x+6}.
\tag{4}
\]
Thus every hypothesis of that theorem and the
[final scalar Casimir sign](MIXED_NONSHORT_FORWARD_ENVELOPE_CASIMIR_SIGN.md)
holds for these unchanged actual parameters.

## 2. Compare the actual norm with the central upper envelope

Put \(Y=x(x+2)\) and define the scalar central ceiling
\[
H=\frac{k}{t}(v-1+t^2)+t(2-t),\qquad
w_U=\frac{k^2-kt+t^2+HY+vY^2}{B^2}.
\tag{5}
\]
The accepted
[upper-envelope comparison](MIXED_NONSHORT_UPPER_ENVELOPE_GAP.md),
Lemma 1, proves
\[
w_U>w_{\rm actual}>\frac34.
\tag{6}
\]
This comparison uses the upper incident norm, followed by increasing the
central comparison coordinate to its established boundary. It does not
require the solved boundary root to satisfy the actual outgoing floor.

On the **original first-event stationarity line**, define
\[
L=\log q+\frac{Wv-c+p^2/W}{p},
\]
\[
H_d(w)=BL+\frac e p B^2(w-1)+\frac{p(1-pe)}e,
\quad
\Gamma(w)=\frac{4B^2vw-H_d(w)^2}{16s^2}.
\tag{7}
\]
At the actual norm, this is the squared Casimir of the same normal
covector. The
[Casimir monotonicity theorem](MIXED_NONSHORT_FORWARD_CASIMIR_MONOTONICITY.md)
applies by (1)--(3) and \(\chi>4/7\), and proves
\[
\Gamma'(w)<0\qquad(w\ge3/4).
\]
Consequently (6) gives
\[
\Gamma_{\rm actual}>\Gamma(w_U).
\tag{8}
\]
The proof of that monotonicity also establishes
\(2v-eH_d(w)/p<0\) for every \(w\ge3/4\).
Since \(v,p,e>0\), this proves \(H_d(w_U)>0\), the sign needed
for the squaring comparison below.

The diagonal in (7) at \(w_U\) is not being identified with
\(H+2vY\) from the central ceiling. Only the outgoing scalar norm
in (5) is inserted into the original stationarity line.

## 3. Remove the event factor on that line

Write
\[
\alpha=\frac{B(w_U-1)}{pW},\quad
\beta=\frac{pW}{B},\quad
g=1-\frac{cp}{W^2},
\]
\[
h(q)=\log q+\alpha q+\frac\beta q
       +\frac{Wv-c+p^2/W}{p}-\frac{p^2}{B}.
\tag{9}
\]
Direct substitution of \(e=q/W\) into (7) gives
\(H_d(w_U)/B=h(q)\). The
[factor-elimination theorem](MIXED_NONSHORT_FORWARD_Q_ELIMINATION.md)
and the original floor (3) imply
\[
0<h(q)\le h(1)+F_{p/W}(q)-g\le h(1)+v-g.
\tag{10}
\]
Both quantities to be squared are therefore positive. It follows that
\[
\Gamma(w_U)\ge
\frac{B^2\{4vw_U-[h(1)+v-g]^2\}}{16s^2}
>\frac{9193}{50000},
\tag{11}
\]
where the strict last sign is precisely the
[scalar hand theorem](MIXED_NONSHORT_FORWARD_ENVELOPE_CASIMIR_SIGN.md).
Its [independent review](MIXED_NONSHORT_FORWARD_ENVELOPE_CASIMIR_AUDIT.md)
checks the full closed parameter domain and both endpoint signs.

The competitive actual-period cap from
[HAND_PROOF_REFINEMENTS](HAND_PROOF_REFINEMENTS.md), Section 1, is
\(\Gamma_{\rm actual}<9193/50000\). This contradicts (8)--(11)
and proves the theorem.

## 4. The exact remaining domain obligation

All comparisons above retain the original incoming secant, missing
floor, event factor and common covector. The physical cost cap is used
only for \(\Gamma_{\rm actual}\). No closure, cost cap or extra switch
is assigned to an artificial trajectory.

The independently reviewed
[low-ratio theorem](MIXED_NONSHORT_LOW_RATIO_HAND_EXCLUSION.md) now
proves t>1/3 for every actual remaining forward window. Thus the exact
remaining domain obligation for this route is j>1/30: a proof that
actual data have j<=1/30 would complete H-N-forward. This restriction
does not follow merely from the scalar domain used here. Until that
obligation is closed, H-N-forward stays open.

## 5. Independent interface review

A separate reviewer checked the physical-to-normalized formula (5),
the exact identity H_d(w_U)/B=h(q), and
g=1-cp/W^2=1-eta+eta^2. The review accepts that (6) and the stationary
monotonicity cover the whole comparison interval and prove positivity
before squaring. It also checked the strict inequalities in (8)--(11),
the unchanged incoming floor, and that the competitive cap is used
only at the actual norm. The review accepts this restricted exclusion
and originally left the two domain obligations open. The later
low-ratio theorem closes the t obligation; the j obligation remains.
