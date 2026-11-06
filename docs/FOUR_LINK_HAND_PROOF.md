# Four-link classification and a strict comparison within that class

Date: 2026-11-06. Status: hand proof supplied; no Lean implementation or kernel check.
This is a restricted theorem, not the unrestricted Reinhardt conjecture. No priority claim.

## Statement and source boundary

Use the determinant-one state equations and endpoint conditions of Hales–Vajjha,
*Packings of Smoothed Polygons*, Sections 3.3–3.6 and 7.1–7.5:
https://arxiv.org/html/2405.04331v1 . The separate six-to-five link-reduction conjecture
is in Hales, *On the Reinhardt Conjecture*, Section 7:
https://arxiv.org/html/1103.4518v1 . It is NOT an input treated as proved here.

**Theorem.** An admissible trajectory with initial frame I, terminal frame R, terminal
state R⁻¹X(0)R, and exactly four positive-duration vertex-control pieces, after merging
adjacent equal controls, has

    cost / sqrt(12) >= delta_oct
    delta_oct = (8 - 4 sqrt(2) - log 2) / (2 sqrt(2) - 1).

Equality occurs only for the octagon trajectory, up to cyclic relabeling. Thus geometric
competitors represented by four such pieces cannot improve the octagon; equality is
unique up to the affine normalization used in the published reduction.

No Pontryagin condition, equal-duration assumption, reflection symmetry, or regular-polygon
hypothesis is imposed. All asymmetric four-link parameters and all reduced four-letter
words are covered. Five or more pieces and general measurable controls are NOT covered.

## 1. Rational coordinates and a shape-independent endpoint equation

Conjugate by B=diag(1,sqrt(3)). Put

    D0 = [[0,-1],[-1,0]],
    D1 = [[-1,2],[0,1]],
    D2 = [[1,2],[0,-1]],
    R  = [[1/2,-3/2],[1/2,1/2]].

These are Dj=-sqrt(3) B⁻¹Zj B. Each Dj is traceless with Dj²=I. The state satisfies
tr X=0, det X=1, X21>0, and c_j=tr(Dj X)>0 by the star inequalities. On a piece
with label j,

    g' = gX,       X' = [Dj,X]/c_j.

Cyclic invariance of trace makes c_j constant on that piece. The two-by-two identity
DX+XD=tr(DX)I and X²=-I imply, for the tangent frame V=gX,

    V' = -(2/c_j) V Dj.

For a piece of duration t define ell=2t/c_j and q=exp(ell)>1. Its tangent transition is
right multiplication by Tj(q)=cosh(ell)I-sinh(ell)Dj, explicitly

    T0(q) = 1/(2q) [[q²+1,q²-1],[q²-1,q²+1]],
    T1(q) = [[q,-q+1/q],[0,1/q]],
    T2(q) = [[1/q,-q+1/q],[0,q]].

Since V(0)=X(0) and V(T)=X(0)R, the endpoint conditions force

    T_{j1}(q1) ... T_{jn}(qn) = R.                         (1)

This tangent equation does not replace the position condition g(T)=R; Section 3 imposes
that condition separately. The original cost in these coordinates is

    delta := cost/sqrt(12) = (1/4) integral (3 X21-X12)dt.   (2)

Indeed B⁻¹JB=[[0,-sqrt(3)],[1/sqrt(3),0]], and the published cost is
-3/2 integral tr(JX). Thus (2) is the same objective, not a newly assigned density.

## 2. Exhaustive four-letter classification

Conjugation by R cyclically permutes the labels and preserves the cost and endpoint
conditions, so take the first label to be 2. Write the four factors p,q,r,z>1. Isolate
the middle factors:

    T_{j2}(q) T_{j3}(r) = T2(1/p) R T_{j4}(1/z).            (3)

There are exactly eight reduced words:

| Word | Exact consequence of (3) |
|---|---|
| 2010 | Bottom-row equality gives r²=q²/(q²-1); the lower-left entry gives pz=1/sqrt(q²-1); the left-column difference would require pz=pz-1/(pz), impossible. |
| 2012 | Exactly r=p, z=q, (p²-1)(q²-1)=1. |
| 2020 | Right-side bottom entries are equal, but their difference on the left is r/q>0. |
| 2021 | Entries force both r²=z²(q²-1) and r²=(z²-1)(q²-1), impossible. |
| 2101 | Entries force both q²=p²(r²-1) and q²=(p²-1)(r²-1), impossible. |
| 2102 | Right-side bottom entries are equal, but their difference on the left is 1/(qr)>0. |
| 2120 | Left-side lower-left entry is zero, but the right-side entry is 1/(2pz)>0. |
| 2121 | The full product is upper triangular, but R21=1/2. |

For a direct check, the right sides of (3) are

    last 0: [[pz-1/(2pz), -pz-1/(2pz)], [1/(2pz),1/(2pz)]],
    last 1: 1/(pz) [[p²-1/2,-p²-z²+1/2], [1/2,z²-1/2]],
    last 2: [[pz-z/(2p),pz-2p/z-z/(2p)], [z/(2p),z/(2p)]].

Together with the displayed T matrices these verify every row. For the surviving word,

    T0(q)T1(r) = [[r(q²+1)/(2q),-qr/2+q/r-r/(2q)],
                 [r(q²-1)/(2q),-qr/2+q/r+r/(2q)]].

Bottom-row equality gives r²=q²/(q²-1). Its lower-left entry and left-column difference
then give (p²-1)(q²-1)=1, r=p, and z=q. Set a=1/p, b=1/q. Thus

    a>0, b>0, a²+b²=1,  (q1,q2,q3,q4)=(1/a,1/b,1/a,1/b). (4)

Alternating factors have been derived from closure, not assumed by symmetry.

## 3. The position endpoint forces the initial shape

Here is a linear recurrence that makes the remaining algebra hand-checkable. Set
X0=X(0), U=X0⁻¹V, A=X0⁻¹g. Initially U=I and A=Q=-X0. Write
Q=[[u,v],[h,-u]], det Q=1. For one piece, let C=(q+1/q)/2 and S=(q-1/q)/2. Then

    c = tr(Dj adj(A) U),
    A_new = A + (c/2) U (S I-(C-1)Dj),
    U_new = U (C I-S Dj).                                  (5)

For the actual trajectory adj(A)=A⁻¹ because det A=1. Formula (5) follows by integrating
A_ell=(c/2)U and U_ell=-U Dj. It is linear in the initial Q because the two-dimensional
adjugate is linear and U is already determined by the factors. The endpoint is
A_final=QR.

Use the rational parametrization 0<w<1:

    a=(1-w²)/(1+w²), b=2w/(1+w²),
    p=(1+w²)/(1-w²), q=(1+w²)/(2w).

Four applications of (5), with word 2012 and factors p,q,p,q, reduce A_final=QR to

    2wu+v+(2w+1)h=0,
    (1+w²)u+(w²+2w-1)h=0.                                 (6)

For an explicit check of necessity, put F=A_final-QR. Then

    F00-F10 = -2w/(w+1)² [2wu+v+(2w+1)h],

and, when the first bracket vanishes,

    F10 = [(1+w²)u+(w²+2w-1)h]/2.

Substitution of (6) into (5) makes every entry of F zero, proving sufficiency. Solving
(6) makes Q proportional to

    M = [[a-b,1-2(a+b)], [1,b-a]].

Let s=a+b. Then 1<s<=sqrt(2) and

    N=det M=(s-1)(s+3)>0.

Normalization det X0=1 and the sign X21>0 therefore force

    X0=M/sqrt(N).                                          (7)

No unconstrained initial-shape parameter remains. Necessity suffices for the lower bound.

## 4. Exact cost, without numerical integration

For a piece starting at X, write D=Dj, c=tr(DX), ell=log q. Solving X_ell=[D,X]/2 gives

    X(ell)=cosh(ell)X-(c/2)(cosh(ell)-1)D
                     +(1/2)sinh(ell)[D,X].

Since dt=(c/2)dell,

    integral X(t)dt = (c/2)sinh(ell)X
      +(c²/4)(ell-sinh(ell))D
      +(c/4)(cosh(ell)-1)[D,X].                            (8)

Use (7), apply (8) four times, and contract with (2). The following per-piece table
records the contribution to N*delta and permits direct checking of the addition.

| Pieces | Algebraic contribution | Logarithmic contribution |
|---|---|---|
| 1,3 | 8w²(1-w)/(1+w²)² | -2(1-w)² log(p)/(1+w²)² |
| 2,4 | 4w(1-w)²(1+w)/(1+w²)² | -2w²(1+w)² log(q)/(1+w²)² |

Adding and using log p=-log a, log q=-log b yields

    delta(a,b) = [4s(s-1)+2(1+a)(1-b)log a
                            +2(1-a)(1+b)log b]/[(s-1)(s+3)]. (9)

This formula is symmetric in a,b, but individual competitors are not assumed symmetric.

## 5. A strict hand-proof inequality

By symmetry take a>b. Write d=a-b=sqrt(2-s²), p0=ab=(s²-1)/2,
r=log(a/b), N=(s-1)(s+3). Equation (9) becomes

    f(s)=[4s(s-1)+(3-s²)log p0+2d r]/N,  1<s<sqrt(2).      (10)

Using d'=-s/d, (log p0)'=2s/(s²-1), r'=-2/[d(s²-1)] and collecting terms gives

    f'(s)=2/N² [H(s)-s(s-1)³/(s+1)],                       (11)
    H(s)=-(s²+3)log p0-(4+s-s³)r/d.

We prove H(s)<0 without sampled bounds. Elementary partial fractions give

    -log(ab)=integral_0^infty [1/(t+a)+1/(t+b)-2/(t+1)]dt,
    log(a/b)/(a-b)=integral_0^infty 1/[(t+a)(t+b)]dt.

After substitution and a common denominator,

    H(s)=(s-1)² integral_0^infty
          [2t-(s²+1)]/[(t+1)(t+a)(t+b)]dt.                (12)

The numerator identity is polynomial, using 2ab=s²-1. All these integrals converge
for a,b>0. Put k=(s²+1)/2=1+p0 and

    W(t)=(t+1)²/[(t+a)(t+b)].

Because 0<a,b<1, both factors (t+1)/(t+a) and (t+1)/(t+b) are positive and strictly
decreasing, so W is strictly decreasing. For every t>=0,

    (2t-2k)W(t) <= (2t-2k)W(k).

For t<k the multiplier is negative and W(t)>=W(k); for t>k the multiplier is positive
and W(t)<=W(k). Divide by (t+1)³ and integrate. Since

    integral_0^infty 2t/(t+1)³ dt=1,
    integral_0^infty 1/(t+1)³ dt=1/2,

the integral in (12) is at most W(k)(1-k)=-p0 W(k)<0. Thus H(s)<0, and (11) gives

    f'(s)<0 throughout 1<s<sqrt(2).

Formula (9) is continuous at a=b=1/sqrt(2); hence its unique minimum is at that point.
Evaluation gives

    f(sqrt(2))=(8-4sqrt(2)-log 2)/(2sqrt(2)-1)=delta_oct.

At equality all four factors are sqrt(2) and

    X0=[[0,-sqrt(2sqrt(2)-1)], [1/sqrt(2sqrt(2)-1),0]].

In the original half-plane coordinates x0=0 and 3y0²=2sqrt(2)-1. These factors, initial
state, and cyclic controls are the k=1 smoothed-octagon data in Hales–Vajjha Section 7.5.
Uniqueness of the explicit constant-control solutions identifies the equality trajectory.
This completes the restricted theorem.

## Progress boundary and validation

Every smaller-cost asymmetric four-link competitor is excluded; the other seven reduced
four-letter words are impossible by endpoint algebra. The known concrete octagon supplies
equality. No global minimizer is assumed to have four links.

A proof excluding all cheaper longer trajectories, or a global replacement theorem, is
still required. In particular, no six-to-five reduction, uniform link bound, or unrestricted
affine rigidity theorem is claimed.

Computer algebra suggested and cross-checked the finite identities, and floating-point
optimization suggested the minimum. Neither is a premise of the displayed hand proof.
The algebra, elementary integrals, and monotonicity argument above are the certificate.
No Lean source was added or executed for this result.
