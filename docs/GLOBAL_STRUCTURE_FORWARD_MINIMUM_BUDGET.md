# The whole forward budget bounds the minimum's central factor

Date: 2026-11-07 UTC. Hand proof with an exact algebra certificate.
No Lean, Lake, typechecking, or CI.

## Result and scope

Let a competitive entirely forward normal period have \(N\ge7\) pieces,
and choose a global minimum active margin \(a\). Write its two neighboring
active margins as \(b,c\), and put

\[
q=\frac{(a+b)(a+c)}{a^2+4}.
\]

The small-forward-minimum theorem and the earlier monotone-cost estimate
give

\[
\frac43<a^2<\frac{20}{11}.
\tag{1}
\]

The actual whole-period budget implies the additional necessary condition

\[
\boxed{q<\frac74.}
\tag{2}
\]

More precisely, it supplies the explicit two-variable bound (12) below.
The proof uses the whole period's scalar action before frame constraints;
the comparison arrays are scalar lower bounds, not claimed closed or PMP
trajectories. This reduces the remaining F domain. A cost--Casimir
comparison or a negative constrained variation on that domain is still
required.

The inputs are the cyclic action and its positive partial derivatives in
[GLOBAL_STRUCTURE_CYCLIC_COSTATE_SECTOR](GLOBAL_STRUCTURE_CYCLIC_COSTATE_SECTOR.md),
the upper minimum bound in
[GLOBAL_STRUCTURE_FORWARD_MINIMUM_THRESHOLD](GLOBAL_STRUCTURE_FORWARD_MINIMUM_THRESHOLD.md),
and the lower minimum bound in
[MIXED_GLOBAL_SMALL_FORWARD_MINIMUM](MIXED_GLOBAL_SMALL_FORWARD_MINIMUM.md).

## 1. A uniform lower bound from seven scalar entries

Define the symmetric edge function

\[
G(a,b)=3ab-4-(a^2+b^2)\log(a+b)
 +\frac{a^2\log(a^2+4)+b^2\log(b^2+4)}2.
\tag{3}
\]

The normalized cyclic cost is

\[
8J=\sum_iG(a_i,a_{i+1}),\qquad C=\sqrt{12}J.
\]

Every partial derivative of \(J\) is positive on the entire positive
orthant. This statement does not require the interpolated factors to
remain above one. Lower every active margin except the chosen \(a,b,c\)
to \(a\). The resulting cyclic scalar expression is

\[
8J\ge2G(a,b)+2G(a,c)+(N-4)G(a,a).
\tag{4}
\]

Since \(a^2>4/3\), one has \(G(a,a)>0\): its value at \(a^2=4/3\)
is zero, and its derivative is positive by the same action monotonicity.
Thus \(N\ge7\) gives the uniform lower bound

\[
\boxed{C\ge\frac{\sqrt{12}}8
 \{2G(a,b)+2G(a,c)+3G(a,a)\}.}
\tag{5}
\]

Equivalently, keeping the five consecutive margins \((p,b,a,c,d)\)
first gives the seven-entry comparison array
\((a,p,b,a,c,d,a)\). Lowering \(p,d\) to \(a\) gives (5).
No enumeration of period lengths is used.

## 2. Ordinary concavity of one edge

The mixed partial derivative is

\[
G_{ab}=2\left(1-\frac{ab}{(a+b)^2}\right)>0,
\qquad G_{abb}=\frac{2a(b-a)}{(a+b)^3}.
\tag{6}
\]

For \(a\ge2/\sqrt3\), \(a\le b\), and \(ab<4\), we claim

\[
G_{bb}(a,b)<0.
\tag{7}
\]

For fixed \(b\), (6) shows that \(G_{bb}(a,b)\) increases with
\(a\le b\). If \(b\le2\), bound it by its diagonal value. With
\(\rho=b^2/(b^2+4)\in[1/4,1/2]\), this value is

\[
G_{bb}(b,b)=-\log(4\rho)-\frac32+5\rho-2\rho^2.
\]

Its derivative in \(\rho\) is
\(-(4\rho-1)(\rho-1)/\rho\ge0\), so it is at most
\(1/2-\log2<0\). If \(b\ge2\), instead bound \(a\) above by
\(4/b\). At that endpoint the exact value is

\[
G_{bb}(4/b,b)=\log\rho+1-\rho<0,
\qquad \rho=\frac{b^2}{b^2+4}<1.
\]

This proves (7). Also \(G_b>0\), because
\(G_b(a,b)=4C_b(a,b,a)\) and the cyclic action derivative is positive.
Symmetry and (6)--(7) give

\[
G_a(a,b)\ge G_b(a,b)>0\qquad(b\ge a),
\tag{8}
\]

by differentiating \(G_a-G_b\) in \(b\) from its zero diagonal value.

One optional explicit consequence of (7) is a linear neighbor bound.
Let

\[
L(a)=\frac{G(a,4/a)-G(a,a)}{4/a-a}>0,
\]
\[
G(a,4/a)=8-\frac{a^2}{2}\log(1+4/a^2)
 -\frac8{a^2}\log(1+a^2/4).
\]

The chord inequality for a concave function and (5) imply

\[
7G(a,a)+2L(a)(b+c-2a)\le\frac{8A_{\rm oct}}{\sqrt{12}}.
\tag{9}
\]

Ordinary averaging of \(b,c\) raises the edge sum. The different
symmetrization used next preserves their central factor instead.

## 3. Convexity in the logarithm of the adjacent sum

Put \(u=4/a^2\in[11/5,3]\), \(x=b/a\ge1\), and define

\[
g_u(x)=\frac{G(a,ax)}{a^2}
=3x-u-\frac12\log\frac{(1+x)^2}{1+u}
 -\frac{x^2}{2}\log\frac{(1+x)^2}{x^2+u}.
\]

The function \(w\mapsto g_u(e^w-1)\) is strictly convex for
\(w\ge\log2\). To prove this, write
\(H=(1+x)^2/(x^2+u)\). Direct differentiation gives

\[
\frac{1}{1+x}\frac{d^2}{dw^2}g_u(e^w-1)
=\frac{N(u,x)}{(x^2+u)^2}-(2x+1)\log H,
\]
\[
N=-4u^2x+3u^2-2ux^3+11ux^2+6x^4.
\]

Here \(H\ge1\). Use \(\log H\le H-1\), put
\(d=3-u\in[0,4/5]\) and \(y=x-1\ge0\), and clear the positive
denominator. The resulting lower numerator is exactly

\[
2y^4+4y^3+(23-8d)y^2+(12-2d^2)y+(24-15d+2d^2)>0.
\tag{10}
\]

All five coefficients are positive on the stated interval for \(d\).

Apply this convexity to \(\log((a+b)/a)\) and
\(\log((a+c)/a)\). Their sum is fixed by \(q\), so with

\[
b_*(a,q)=\sqrt{q(a^2+4)}-a
\]

one obtains

\[
G(a,b)+G(a,c)\ge2G(a,b_*(a,q)).
\tag{11}
\]

The geometric mean of the two adjacent sums shows
\(b_*\ge a\) and \(ab_*<4\). Thus (5) becomes

\[
\boxed{C\ge\mathcal B(a,q):=
\frac{\sqrt{12}}8\{4G(a,b_*(a,q))+3G(a,a)\}.}
\tag{12}
\]

## 4. Reduce the scale at a fixed central factor

For fixed \(q\), decrease \(a\) to \(a_0=2/\sqrt3\).
The condition \(b_*(a,q)\ge a\) persists, because it is equivalent to
\(q\ge4a^2/(a^2+4)\), whose right side increases with \(a\).
The strict-star condition persists for the same reason: it is
\(q<1+4/a^2\). Along this scalar path,

\[
-1<\partial_a b_*=
\frac{qa}{\sqrt{q(a^2+4)}}-1<0.
\]

Using (8),

\[
\frac{d}{da}\{4G(a,b_*)+3G(a,a)\}
=4(G_a+G_b\partial_a b_*)+6G_a(a,a)>0.
\tag{13}
\]

Consequently \(\mathcal B(a,q)\ge\mathcal B(a_0,q)\).
For fixed \(a\), \(\mathcal B\) also increases with \(q\), because
\(G_b>0\) and \(\partial_q b_*>0\).

## 5. An exact rational cutoff

Suppose \(q\ge7/4\). Equations (12)--(13) imply

\[
C\ge\mathcal B(a_0,7/4)
=\frac{4\sqrt3}{3}\,g_3(\sqrt7-1).
\tag{14}
\]

For \(v\ge1\), the elementary upper logarithm bound

\[
\log v\le U(v):=\frac{(v-1)(v^2+10v+1)}{6v(v+1)}
\]

follows from \(U(1)=0\) and
\(U'(v)-1/v=(v-1)^4/[6v^2(v+1)^2]\ge0\).
The exact rational inequalities

\[
\frac{26457}{10000}<\sqrt7<\frac{26458}{10000},
\qquad \sqrt3>\frac{1732}{1000}
\]

are checked by squaring. At \(z=\sqrt7-1\),

\[
g_3(z)=3\sqrt7-6-\frac12\log(7/4)
 -(4-\sqrt7)\log\frac7{11-2\sqrt7}.
\]

Since \(7/(11-2\sqrt7)<17500/14271\), the displayed log bound gives

\[
\begin{aligned}
g_3(z)&>
3\frac{26457}{10000}-6
-\frac12U(7/4)-\frac{13543}{10000}U(17500/14271)\\
&=\frac{7231126442093904703}{5236815518550000000}.
\end{aligned}
\]

Thus (14) yields

\[
C>\frac{3131077749426660736399}{981902909728125000000}
>\frac{313}{100}>A_{\rm oct},
\]

contradicting the actual whole-period budget. This proves (2).

In the dimensionless minimum variables
\(\rho=a^2/(a^2+4)\), \(r=a/(a+b)\), \(t=a/(a+c)\), the remaining
domain therefore satisfies

\[
\frac14<\rho<\frac5{16},\qquad
\frac{8\rho}{7}<r,t\le\frac12,\qquad
q=\frac{\rho}{rt}<\frac74.
\tag{15}
\]

The actual exterior factors and the two actual exterior missing-control
inequalities remain necessary. They have not been replaced by presumed
equalities or by an unproved Casimir symmetrization.

## Verification boundary

The companion
[`global_structure_forward_minimum_budget_certificate.py`](../explorations/global_structure_forward_minimum_budget_certificate.py)
checks the scalar derivatives, the convexity polynomial, the exact
rational cutoff, and the diagonal/star boundary identities. These exact
checks supplement the displayed hand proof. There is no sampled sign,
word-length catalogue, asserted closed competitor, or new F exclusion.

The [independent internal audit](GLOBAL_STRUCTURE_FORWARD_MINIMUM_BUDGET_AUDIT.md)
checks the whole-period normalization, both distinct convexity/concavity
arguments, comparison paths, exact cutoff, and scope. All 21 exact
checks pass; this is hand review, not kernel validation.
