# A complete six-arc comparison: the reverse-block orbit

Status: complete hand proof, 2026-11-06. Computer algebra and finite floating-point
experiments suggested the coordinates; none of their outputs is a proof premise.
No Lean source, compilation, Lake command, or CI execution is involved.

## Result

Every admissible six-positive-piece trajectory in the cyclic orbit

    010202, 020212, 021210

has cost strictly larger than the smoothed octagon. Initial state and all six
durations are unrestricted. The proof constructs a continuous family of actual
closed admissible trajectories, strictly decreases their cost, and reaches a
trajectory with at most five positive pieces, to which the existing hand
comparison applies.

The deformation preserves g(0)=I, g(T)=R, and X(T)=R^(-1)X(0)R. It generally
CHANGES X(0) and T. It is therefore a global closed-trajectory deformation,
not a replacement of an arbitrary interior window with both endpoint states
held fixed. In particular it does not prove the general six-to-five link
reduction conjecture.

Write delta=C/sqrt(12) for normalized cost and delta_oct for the octagon's
normalized cost. We use the previously proved comparison through five pieces
in FOUR_LINK_HAND_PROOF.md, FIVE_ARC_PROGRESS.md, and REVERSE_FIVE_ARC.md.

## 1. Exhaustive tangent-closure parametrization

Work in the triangular coordinates of FIVE_ARC_PROGRESS.md. The tangent
transitions and endpoint rotation are

    T_0(q) = [[q,0],[0,1/q]],
    T_1(q) = [[1/q,q-1/q],[0,q]],
    T_2(q) = [[1/q,0],[1/q-q,q]],
    R     = [[0,1],[-1,1]].

The generators satisfying T_i(q)=exp(-log(q) D_i) are

    D_0=[[-1,0],[0,1]],
    D_1=[[1,-2],[0,-1]],
    D_2=[[1,0],[2,-1]].

For a traceless state X put p_i=tr(D_i X). The strict star conditions are
p_i>0 and p_0*p_1+p_1*p_2+p_2*p_0=4. These quantities are invariant under the
coordinate change used here.

Choose the representative 021210 and write its factors as

    (a,p,q,r,z,f),     all greater than 1.

Tangent closure is T_0(a) T_2(p) T_1(q) T_2(r) T_1(z) T_0(f)=R.
Let M be the product of the four middle matrices. Its upper-left entry is

    M_00 = (q^2+r^2-q^2*r^2)/(p*q*r*z).

Since the outer matrices are diagonal, M_00=0. Hence, with m=sqrt(q^2-1),

    r=q/m.

Substitution in the remaining entries gives

    M_01=z*m/p,
    M_10=-p/(z*m),
    M_11=p/(z*m)+z*m/p.

The upper-right and lower-right endpoint equations now give

    a^2=1+p^2/(z^2*m^2),
    f^2=1+z^2*m^2/p^2.                              (1)

All roots are positive, so there are no further branches in (1).
Set u=p/(z*m)>0 and introduce x,y in (0,1) by

    u=2x/(1-x^2),       m=2y/(1-y^2).

Each positive u,m has exactly one such x,y: for example
x=u/(sqrt(1+u^2)+1). Define

    Q(t)=(1+t^2)/(1-t^2),
    P(t)=(1+t^2)/(2t),
    h(t)=(1+t)/(1-t),
    k=4xy/((1-x^2)(1-y^2)),
    z_* = max(1,1/k).

Every positive tangent-closed factor tuple in this orbit is now exactly

    word:     0      2       1      2       1     0
    factor:   Q(x)   p=kz    Q(y)   P(y)    z     P(x),             (2)

where 0<x,y<1 and z>z_*. Conversely (2) satisfies tangent closure by the
matrix calculation above. We will also use z=z_*, allowing zero-duration
pieces of factor one.

## 2. State holonomy and a complete margin table

Let H_i(q)=exp((log q)D_i/2). The state transition is conjugation by

    H=H_0(P(x)) H_1(z) H_2(P(y)) H_1(Q(y)) H_2(p) H_0(Q(x)).

The reverse product order matters. Each half-factor has the elementary form

    H_0(q)=diag(1,q)/sqrt(q),
    H_1(q)=[[q,1-q],[0,1]]/sqrt(q),
    H_2(q)=[[q,0],[q-1,1]]/sqrt(q).

Put A=Q(x), l=(1-y)/z and retain u=2x/(1-x^2). Multiplying these six
half-factors and cancelling their common scalar gives the compact identity

    H = [[(u+1-l)/A, l-1], [1-l/u, A*l/u]].          (3)

For instance, the product of the six factors in (2) is A^2 Q(y)^2 z^2,
so their square-root denominator is A Q(y) z. Also A^2=1+u^2.
These two identities reduce the product directly to (3).

Set

    d_0=(1-x)(1-y),       d=d_0/z,
    K=R H,               Y=2K-tr(K) I,
    N=d(4-d).

Equation (3) gives det K=1 and tr K=2-d. Since 0<d<1 for z>=z_*,
K is noncentral elliptic and det Y=N>0. The unique possible strict-star
initial state is

    X_0=Y/sqrt(N).                                    (4)

Indeed the endpoint condition is [K,X_0]=0; the elementary centralizer
argument in WORD_HOLONOMY.md leaves only the two signs of Y/sqrt(N).
The positive p_0 sign selects (4).

Here is a finite algebra certificate for every intermediate state. Divide
its three margins by the common positive number 2d/sqrt(N). Define

    B(x,y,z)=[4xz/(1-y)+x^2-2x-1]/(1+x^2).

The resulting margin triples at the seven successive endpoints are

| Endpoint | p_0 / (2d/sqrt(N)) | p_1 / (2d/sqrt(N)) | p_2 / (2d/sqrt(N)) |
| --- | --- | --- | --- |
| 0 | 1/x | B(x,y,z) | h(x) |
| 1 | 1/x | p(1+1/y)-1 | 1 |
| 2 | p(1+1/x)-1 | 1/y | 1 |
| 3 | B(y,x,z) | 1/y | h(y) |
| 4 | 2z/(1-x)-1 | 1 | h(y) |
| 5 | h(x) | 1 | 2z/(1-y)-1 |
| 6 | h(x) | 1/x | B(x,y,z) |

The initial row follows by taking tr(D_i Y) in (3). Every subsequent row
follows from the same three elementary updates: on control i of factor q,

    p_i=a -> a,
    p_(i+1)=b -> (a+b)q-a,
    p_(i-1)=c -> (a+c)/q-a.                           (5)

Thus the table is verifiable row by row without any differential-equation
solver or computer-algebra premise. Its final row is exactly the required
cyclic permutation of the first row.

## 3. Feasibility throughout the entire deformation

All entries in the table except the two B entries are visibly positive
when p=kz>=1 and z>=1. To prove B(x,y,z)>0, distinguish two cases.

If x^2+2x-1>=0, use z>=1 and y>0 to get

    4xz/(1-y)+x^2-2x-1
       > 4x+x^2-2x-1 = x^2+2x-1 >=0.

If x^2+2x-1<0, then 1-x^2>2x. The inequality p>=1 gives

    4xz/(1-y) >= (1-x^2)(1+y)/y.

Consequently the same numerator is at least

    (1-x^2)/y-2x > 1-x^2-2x >0.

This proves B>0, and interchanging x,y proves the other entry positive.
Importantly, positivity persists at z=z_*; it is not obtained merely by
taking an unspecified limit in a strict inequality.

On a positive-duration vertex arc, the first margin in (5) is constant,
the successor margin increases, and the predecessor margin decreases.
Positive endpoint margins therefore imply strict positivity along the
whole closed arc. The table proves full strict-star feasibility for every
z>=z_*, including the endpoint with factor-one pieces deleted.

Tangent closure and commuting holonomy give BOTH original endpoint equations,
not just the tangent endpoint: for V=gX one has V(T)=X_0 R, and the terminal
state is R^(-1)X_0 R, hence g(T)=R. The finite piecewise-smooth reconstruction
satisfies the actual integral state equations. This proves that varying z
at fixed x,y is a family of actual admissible closed trajectories.

## 4. Exact cost on the family

For an arc with initial margins a,b,c in cyclic order and factor q, direct
integration of (5), with dt=(a/2)dq/q, gives normalized cost

    delta_arc = (a/8)[(a+b)(q-1)+(a+c)(1-1/q)-a log q].             (6)

Define

    F(t)=log(Q(t))/t^2 + h(t)^2 log(P(t)),
    Gamma=(F(x)+F(y)+log k)/2-3.

Substitution of the margin table into (6) and summation give

    delta(z) = [4+2d-(d/2)(F(x)+F(y)+log p+log z)]/(4-d)
             = 1 - d_0 (Gamma+log z)/(4z-d_0).       (7)

A short way to check every normalization and rational term is the following.
Let v_j be row j of the table, let i_j be the six control labels in (2),
and put A_j=v_(j-1),i_j. The six A_j are

    1/x, 1, 1/y, h(y), 1, h(x).

The log coefficients in (6) are therefore exactly
-d/(2(4-d)) times the squares of these six numbers. Multiplying them by
the logs of (2) gives the log term in (7). For the non-logarithmic part,
use (5) to replace (b+a)(q-1) and (c+a)(1-1/q) by endpoint differences.
In the units of the displayed table, the required elementary sum is

    sum_(j=1)^6 A_j [
        v_j,(i_j+1)-v_(j-1),(i_j+1)
        +v_(j-1),(i_j-1)-v_j,(i_j-1)]
       = 8/d+4.                                      (8)

Indices in (8) are modulo three. Substituting the seven rows, using
p=4xyz/((1-x^2)(1-y^2)), and cancelling gives (8); it uses no logarithms.
The common factor in (6) is d/(2(4-d)), so (8) becomes (4+2d)/(4-d),
as asserted in (7). Equations (2), the complete table, and (8) constitute
an exact finite algebra certificate for the cost formula.

## 5. A two-line logarithm bound makes the deformation monotone

For every r>1,

    log r > 2(r-1)/(r+1).                             (9)

For a direct proof, the difference is zero at r=1 and has derivative
(r-1)^2/[r(r+1)^2]>0 for r>1. Both Q(t),P(t) are greater than one for
0<t<1, and

    (Q(t)-1)/(Q(t)+1)=t^2,
    (P(t)-1)/(P(t)+1)=1/h(t)^2.

Applying (9) twice proves the strict uniform bound

    F(t)>2+2=4.                                      (10)

Since p,z>=1, (10) gives

    Gamma+log z
       = (F(x)+F(y)+log p+log z)/2-3 >1.             (11)

Differentiate (7) at fixed x,y:

    delta'(z)
       = d_0/[ (4z-d_0)^2 ]
           * [4(Gamma+log z)-4+d_0/z]
       > d_0^2/[ z(4z-d_0)^2 ] >0.                  (12)

All denominators are positive because 0<d_0<1 and z>=1. Thus the cost
strictly increases with z on its ENTIRE unbounded admissible interval.
No compact search box, sampled gradient sign, or assumption of symmetry
has been used.

## 6. The boundary is already compared with the octagon

At z=z_*=max(1,1/k), at least one of z,p equals one. Delete its
zero-duration piece and merge any adjacent equal controls. The resulting
trajectory has at most five positive vertex pieces and is still strict-star
and admissible by Section 3. The established through-five comparison gives

    delta(z_*) >= delta_oct.

A genuine six-piece tuple has p,z>1 and hence z>z_*. By (12),

    delta(z) > delta(z_*) >= delta_oct.

This proves the full claimed comparison. Cyclic rebasing and relabeling
preserve cost and the actual endpoints, so the other two representatives
010202 and 020212 are covered as well. There is no equality case in the
genuine six-positive-piece orbit.

## Boundary of the result

The family 010120 is separately excluded from global minimizers by
FORWARD_ALTERNATION_EXCLUSION.md. The remaining genuine six-piece orbit
010210 is not covered by this proof. Arbitrary longer words and global
affine rigidity remain open.

Even a complete comparison at six pieces would not give a uniform bound
on all minimizing words. This note must not be used as an interior-window
replacement theorem: its initial state varies with z.

## Discovery and validation

The exploratory derivation used the triangular tangent products and the
exact vertex cost. Sampling suggested all tuples in this orbit were
feasible; the displayed table and the two-case proof of B>0 replace that
observation by a hand proof on the full domain. Symbolic simplification
suggested (7); the finite algebra certificate above is independent of the
software. The decisive inequality is the elementary logarithm bound (9).

The proof and its signs have been checked within this session. No claim
of independent peer review, Lean elaboration, kernel validation, or a full
solution of the Reinhardt conjecture is made.
