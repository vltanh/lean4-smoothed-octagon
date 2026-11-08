# A displacement-adapted floor weight and its exact reductions

Date: 2026-11-08 UTC. **Analytic reduction, not a displacement
exclusion.** The terminal boundary signs remain explicit obligations.
This note proves the envelope, incoming-norm
comparison, scale convexity and a two-value duration reduction for a
weight suited to the proposed displacement restriction. The separate
[tau-two continuation proof](MIXED_SMALLER_SHORT_DISPLACEMENT_SCALE_CONTINUATION.md)
completes the positive-scale continuation used below, and the
[zero-scale sign](MIXED_SMALLER_SHORT_DISPLACEMENT_ZERO_SCALE.md)
removes the zero endpoint using the original incident norm ceiling.

Use the original smaller-short common-covector geometry and actual
first outer root. Assume the candidate excluded range

\[
2\le x\le13/6,\qquad \delta=\beta/x-1\ge1/19.
\tag{1}
\]

The exact equal secants and already proved short-order estimates give

\[
1\le\alpha<x\le\beta\le\alpha x,\qquad
\alpha\ge1+c(x)\delta,\qquad
c(x)=\frac{4x^2+11x+1}{7x+1},
\]
\[
\beta\ge b_0:=\frac{x(9x+8\alpha)}{9x+8}.
\tag{2}
\]

Put \(S=1+x\), \(Q=\alpha(\alpha+\beta)\),
\(r_A=\alpha/(\alpha+\beta)\), \(q=\rho_A\),
\(T=r_A/q\), and \(k=5\alpha-1\). Preserve the definitions of
\(D,\lambda,d,w,E_L,R_\tau\) from the
[outer envelope](MIXED_SMALLER_SHORT_OUTER_ENVELOPE.md).
The actual scale satisfies \(0<q<1/7\), and the actual root has
\(2<\tau<T\), \(R_\tau=0\), \(w>3/4\).

## 1. Elementary bounds on this domain

Since \(c(x)\ge13/5\), (1)--(2) imply
\(\alpha\ge108/95>11/10\). The function
\((1+\delta)/(1+c\delta)\) decreases in \(\delta\), so

\[
\frac\beta\alpha\le\frac{20x}{19+c(x)}<2.
\tag{3}
\]

For the last sign,

\[
(19+c(x)-10x)(7x+1)=-66x^2+134x+20\ge1/2>0;
\]

the quadratic decreases on the interval and takes the displayed
terminal value at \(x=13/6\). On the other side, (2) and
\(\alpha\le x\) give

\[
\frac\beta\alpha\ge\frac{17x}{9x+8}\ge\frac{17}{13}.
\]

Consequently

\[
\boxed{1/3<r_A\le13/30,\qquad T>7/3.}
\tag{4}
\]

The complete equal-secant domain has \(u\le V(x)\), with
\(V(x)=\operatorname{Sec}(1,x,x)\). This is the comparison in
Section 1 of the
[exact short-bridge continuation](MIXED_GLOBAL_SHORT_BRIDGE_CENTRAL.md);
it requires no upper restriction on \(\delta\).
One can also check its full scope directly. Put
\(g(t)=1-t/(1+t)^2\) and
\(f(B)=(B-1)^{-1}\int_1^B g(t/x)\,dt\).
The second equal secant implies
\(f(\beta)>g(x/\beta)=g(\beta/x)\), because
\(g\) strictly decreases on \((0,1)\) and \(\alpha<x\le\beta\).
For \(B\ge x\), the function
\((B-1)[f(B)-g(B/x)]\) has derivative
\(-(B-1)g'(B/x)/x\le0\). It is therefore positive throughout
\([x,\beta]\), so \(f'(B)<0\) there. Hence
\(u=f(\beta)\le f(x)=V(x)\).
Combining this with Section 1, equation (3), of the accepted
[rational incoming-norm bound](MIXED_SMALLER_SHORT_INCOMING_NORM_BOUND.md)
gives

\[
\frac34<u\le\frac34+
\frac{2(x-1)^2}{(x+1)(35x+13)}
\le\frac{30773}{40508}<\frac{19}{25}.
\tag{5}
\]

The rational expression increases for \(x>1\); its derivative has
positive numerator \(4(x-1)(59x+37)\) over
\((x+1)^2(35x+13)^2\).

Two diagonal bounds used below follow directly from (2):

\[
D<Q,\qquad D<3\alpha^2.
\tag{6}
\]

For the first, \(D-Q\le1+2x+b_0(\alpha-2x)\). This is convex in
\(\alpha\), and its endpoint values at \(1,x\) are
\(1+3x-2x^2<0\) and \(1+2x-17x^3/(9x+8)<0\) for \(x\ge2\).
For the second,

\[
3\alpha^2-D\ge2(\alpha-x/2)^2+3x^2/2-2x-1>0.
\]

In particular \(0<d<3/7\) when the actual positive-diagonal result
is used. None of these estimates changes the actual incoming norm.

## 2. The weight preserves the complete opposite-turn envelope

Set

\[
y=\tau/T,\qquad m(y)=\frac{4(4-3y)}k,
\qquad G_\tau=R_\tau+m(y)(w-3/4).
\tag{7}
\]

Since \(0<y<1\), the weight is positive. Thus \(G_\tau>0\) at
the actual root. With geometry and \(\tau\) fixed, \(m\) is
independent of the opposite-turn variables \(t,v\). The exact
comparison derivatives are

\[
(G_\tau)_v=\frac\lambda t B_{\tau+m}(t),\qquad
\frac{d}{dt}G_\tau(t,U(t))
=\frac{\lambda(2t-1)}t B_{\tau+m}(t),
\]
\[
B_z(t)=1+z(\lambda t-d).
\tag{8}
\]

Here is a uniform proof that the common factor is positive. Write
\(p=\tau q\), so \(2q\le p\le r_A\). Since \(m\ge0\),

\[
p+mq\le p\left(1+\frac{8-6p/r_A}{k}\right)
\le\frac{r_A(k+2)}k.
\tag{9}
\]

The last quadratic increases on \([0,r_A]\): its derivative is
\(1+(8-12p/r_A)/k\ge1-4/k\ge0\).
If \(D\le S\), positivity in (8) is immediate from
\(t\ge\rho S\). If \(D>S\), (9) gives

\[
B_{\tau+m}(t)\ge
1-\frac{(k+2)(D-S)}{kQ}>0.
\tag{10}
\]

The last numerator is the explicit polynomial

\[
kQ-(k+2)(D-S)
=\beta[-5\alpha^2+10\alpha x-3\alpha+2x]
 -2\alpha^2-5\alpha x-x.
\tag{11}
\]

The coefficient of \(\beta\) is concave in \(\alpha\), and its
values at \(\alpha=1,x\) are respectively \(12x-8>0\) and
\(5x^2-x>0\). Hence replacing \(\beta\) by \(x\) lowers (11).
The resulting polynomial is again concave in \(\alpha\); its two
endpoint values are

\[
12x^2-14x-2>0,\qquad x(5x^2-8x-1)>0\quad(x\ge2).
\]

This proves (10) using only short order and \(x\ge2\).
The signs in (8) now prove

\[
\boxed{0<G_\tau\le G_\tau^*
:=R_\tau^*+m(y)(w_*-3/4).}
\tag{12}
\]

The norm floor is incorporated at the actual root before the
comparison; no separate floor assertion at \(w_*\) is required.

## 3. Increasing the incoming norm is a legitimate scalar comparison

First, throughout \(2\le\tau\le T\),

\[
\tau+m(\tau/T)\le T+1.
\tag{13}
\]

The left side is affine in \(\tau\), so its two endpoint values
suffice. At \(\tau=T\), use \(4/k<1\). At \(\tau=2\), the
required inequality is

\[
kT^2-(k+16)T+24\ge0.
\]

Its discriminant is
\(25\alpha^2-330\alpha+321<0\) on
\([11/10,13/6]\). This convex quadratic is negative at both
endpoints, and the leading coefficient \(k\) is positive.

The coefficient of \(u\) in the explicit envelope is

\[
(G_\tau^*)_u=\frac1{r_A}+\lambda S-2d
 +(\tau+m)d(d-\lambda S).
\tag{14}
\]

By (6) and (13), \((\tau+m)d<1+d\). Discarding the nonnegative
term \((\tau+m)d^2\), and using (4), gives

\[
(G_\tau^*)_u>
\frac1{r_A}-d(2+\lambda S)
\ge\frac{30}{13}-\frac37\frac{31}{6}
=\frac{17}{182}>0.
\tag{15}
\]

Thus a proved incoming upper bound may be inserted after any scale
comparisons that require the original incident norm ceilings. The
coefficient is independent of \(u\), so its sign holds on the
entire substitution segment.

## 4. Convexity at fixed normalized duration

Use \(A_1,A_2,A_3,C,L\) from the
[normalized scale identity](MIXED_SMALLER_SHORT_ENVELOPE_SCALE_MONOTONICITY.md).
At fixed \(p=\tau q\), both \(y=p/r_A\) and \(m(y)\) are fixed.
Exactly,

\[
G^*(q)=C(p)+m/4+q[L(p)-mA_1]+mq^2A_2.
\tag{16}
\]

Here \(A_2>0\) has a short completed-square proof. Put
\(b=\alpha^{-2}\), \(\varepsilon=1-b\), \(\Delta=D/\alpha^2\),
\(H=S(1-u)-1/S\),

\[
A=\varepsilon^2+\varepsilon Sb+S^2b^2,
\quad K=\varepsilon H+(2S-1)b,
\quad \overline K=\varepsilon(S/4-1/S)+(2S-1)b.
\]

Then \(A_2=A-\Delta K+u\Delta^2\), and completing the square gives
\(A_2\ge A-\overline K^2/3\) for \(\Delta>0\). With
\(Z=(S-2)^2b<2\), direct collection gives

\[
\overline K^2-3A
=\frac{S^4-56S^2+16+2(7S^2-4)Z+Z^2}{16S^2}
<\frac{S^4-28S^2+4}{16S^2}<0.
\tag{17}
\]

The last sign uses \(3\le S\le19/6\), so \(S^2<11\).
Consequently (16) is strictly convex. A positive value can occur
only if a positive value occurs at one of

\[
q=0,\qquad q=\min\{q_c,1/7,p/2\},
\quad q_c=\frac{\alpha^2}{S^2+\alpha^2-1}.
\tag{18}
\]

The separate [zero-scale proof](MIXED_SMALLER_SHORT_DISPLACEMENT_ZERO_SCALE.md)
shows that the first endpoint is strictly negative, by preserving
\(u\le U(r_A)\) before the incoming-norm substitution. For the
\(q=p/2\) case the tau-two continuation proof shows that
the scalar value strictly increases until
\(q=\min\{q_c,1/7\}\); it uses the original incoming norm and
does not transport the outgoing floor separately.

## 5. Only two duration tests are needed at a fixed positive scale

At fixed geometry and scale let \(F=w_*-3/4\), which is independent
of \(\tau\), and let
\(B=1-12/(Tk)\). The derivative identity is exact:

\[
\frac{d}{d\tau}G_\tau^*
=B F-\frac{(\tau-2)^2}{4\tau^2}.
\tag{19}
\]

Integrating its nonpositive second term gives

\[
G_\tau^*\le
\max\{G_2^*,\ G_2^*+(T-2)BF\}
\qquad(2\le\tau\le T).
\tag{20}
\]

Equivalently the two sufficient signs are those of

\[
R_2^*+\frac{16-24/T}{k}(w_*-3/4),
\qquad
R_2^*+\left(T-2+\frac4k\right)(w_*-3/4).
\tag{21}
\]

This removes the duration variable analytically; it assumes no
maximizing-root continuation or numerical optimizer.

## 6. The tau-two scale derivative

For clarity, the continuation has a compact explicit form. Set
\(M=16/k\), \(N=24/(kr_A)\). At \(\tau=2\),
\(m=M-Nq\), and differentiating (16) with \(p=2q\) gives

\[
(G_2^*)'(q)=q^{-1}-K_1+K_2q-3NA_2q^2,
\]
\[
K_1=(2+M)A_1+1+A_3+N/4,
\qquad K_2=(4+2M)A_2+2NA_1.
\tag{22}
\]

Thus \(q(G_2^*)'\), written in the cubic Bernstein basis on
\(0\le7q\le1\), has the exact four coefficients

\[
1,\quad
1-K_1/21,\quad
1-2K_1/21+K_2/147,\quad
1-K_1/7+K_2/49-3NA_2/343.
\tag{23}
\]

The [continuation lemma](MIXED_SMALLER_SHORT_DISPLACEMENT_SCALE_CONTINUATION.md)
proves all three positive on the enclosing domain
\(11/10\le\alpha\le13/6\), \(3\le S\le19/6\),
\(1/3\le r_A\le\alpha/(\alpha+2)\),
\(3/4\le u\le19/25\), and \(0<D/\alpha^2<3\).
Its proof completes the square, uses two elementary monotonicity
reductions, and prints the four remaining low-degree polynomials
and every coefficient used in their explicit sign argument.
Thus \((G_2^*)'>0\) for \(0<q\le1/7\).

## 7. Scope

This note establishes the comparisons (12), (15), (16)--(20) and the
exact remaining scalar formulas. It does not establish
\(\delta<1/19\), the final central or outer boundary signs, a
Casimir floor, a physical-cost inequality, or the global H-S exclusion.
The original common covector and actual outer root supply (12).
All subsequent objects are scalar bounds, without an assertion of
physical realization at an artificial endpoint.
