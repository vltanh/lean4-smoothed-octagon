# Reverse four-arc windows can be uniquely optimal at arbitrarily small cost

## Result and scope

There are strict-star four-arc trajectories with the reverse control word
**2121**, with arbitrarily small positive physical cost, that uniquely
minimize cost among **all measurable simplex controls with the same initial
and final frame and state**. Terminal time is free. Uniqueness means equality
of the state and frame trajectories with their prescribed time parameter,
and equality of the controls almost everywhere.

This is an actual obstruction to an orientation-free version of
[FORWARD_ALTERNATION_EXCLUSION.md](FORWARD_ALTERNATION_EXCLUSION.md).
The forward word 1212 always admits a strict local improvement; the reverse
word 2121 can be globally optimal for its local endpoint problem, even far
below the octagon's total cost.

These local endpoint data are not the closed Reinhardt endpoints
\(g(0)=I, g(T)=R\) with a twisted state endpoint. The result neither
constructs a global Reinhardt minimizer containing such a window nor
contradicts a possible six-to-five theorem under additional hypotheses.
It shows that cost smallness and the local endpoint problem alone cannot
exclude both orientations of four alternating arcs.

The proof has two parts. An exact dual certificate proves unique optimality
over the entire edge-control problem, including measurable nonvertex
controls. A tangent-angle argument shows that any nonedge competitor with
the same endpoints must cost more than \(3\pi\). The constructed competitor
costs less than \(\pi\), so the edge certificate is already globally decisive.
No numerical calculation, Lean source, build, or CI is used in this proof.

## 1. The actual edge problem is linear in a positive function

Use the original upper-half-plane state coordinates, without the later
triangular matrix change of basis:

\[
q=\frac1{\sqrt3},\qquad
X=\Phi(x,y)=\frac1y
\begin{pmatrix}x&-(x^2+y^2)\\1&-x\end{pmatrix}.
\]

The strict star domain is

\[
-q<x<q,\qquad y>0,\qquad x^2+y^2>q^2.
\tag{1}
\]

On the edge \(u_0=0\), put \(\alpha=(u_1-u_2)/\sqrt3\in[-q,q]\).
The actual equations, derived in [EDGE_SWITCH_BOUND.md](EDGE_SWITCH_BOUND.md),
give

\[
\dot x=y>0,\qquad
\frac{d\log w}{dx}=\frac{2\alpha}{q^2-\alpha x},
\qquad w(x)=y(x)^{-2}.
\tag{2}
\]

For fixed \(x\in(-q,q)\), the last expression is strictly increasing
in \(\alpha\), because its derivative is
\(2q^2/(q^2-\alpha x)^2>0\). Consequently arbitrary measurable edge
controls correspond exactly to positive absolutely continuous functions
with

\[
b_-(x)w(x)\le w'(x)\le b_+(x)w(x)\quad\text{a.e.},
\qquad
b_-(x)=-\frac2{q+x},\quad b_+(x)=\frac2{q-x}.
\tag{3}
\]

The inverse is explicit: if \(\beta=w'/w\), then
\(\alpha=\beta q^2/(2+\beta x)\). The denominator is positive throughout
the interval between the two bounds in (3), so this gives a measurable
control in \([-q,q]\). The remaining star inequality is the linear
pointwise bound

\[
0<w(x)<\frac1{q^2-x^2}.
\tag{4}
\]

Fix a compact \(x\)-interval \([a,b]\subset(-q,q)\), both endpoint
values of \(w\), the initial frame, and

\[
S(w)=\int_a^b w(x)\,dx.
\]

These are exactly the edge endpoint data. Indeed,

\[
t(x)=\int_a^x\sqrt{w(r)}\,dr,\qquad
s(x)=\int_a^xw(r)\,dr,\qquad
h(x)=\begin{pmatrix}1&-x\\s(x)&1-s(x)x\end{pmatrix},
\]
\[
g(x)=g(a)h(a)^{-1}h(x).
\tag{5}
\]

The final state is fixed by the final \(x,w\), and (5) fixes the final
frame from \(S\). The physical cost is

\[
C(w)=\frac32\left[(b-a)+S(w)+M(w)\right],\qquad
M(w)=\int_a^b x^2w(x)\,dx.
\tag{6}
\]

Thus the endpoint-constrained edge problem minimizes the linear functional
\(M\) subject to linear differential inequalities, endpoint conditions,
and one linear integral condition. Its admissible set of \(w\)'s is convex.

## 2. An explicit reverse four-arc trajectory

Choose

\[
0<b\le\frac q4,\qquad s=\frac b2.
\]

On \([0,b]\), define

\[
w_*(x)=
\begin{cases}
\displaystyle\frac{q^2}{(q+x)^2},&0\le x\le s,\\[6pt]
\displaystyle\frac{q^2(q-s)^2}{(q+s)^2(q-x)^2},&s\le x\le b,
\end{cases}
\qquad w_*(-x)=w_*(x).
\tag{7}
\]

The pieces agree at \(s\), and \(w_*\) is continuous, positive, and
piecewise smooth. Its logarithmic derivative on the four successive
intervals \((-b,-s),(-s,0),(0,s),(s,b)\) is

\[
b_-,\quad b_+,\quad b_-,\quad b_+,
\]

so its control word is exactly 2121. All four physical durations are
positive by (5). The elementary bounds

\[
\frac{16}{25}\le w_*(x)\le\frac{16}{9}<3
\le\frac1{q^2-x^2}
\qquad(-b\le x\le b)
\tag{8}
\]

prove strict star membership, including at all switches. For the upper
bound use \(q/(q-b)\le4/3\); the lower bound follows from
\(q/(q+b)\ge4/5\) and the fact that the minimum is attained at
\(x=\pm s\).

Write

\[
S_*=\int_{-b}^b w_*(x)\,dx,
\qquad y_b=w_*(b)^{-1/2}=w_*(-b)^{-1/2}.
\]

Set the initial frame to \(I\). The exact endpoint data of this local
problem are

\[
X_- =\Phi(-b,y_b),\qquad X_+=\Phi(b,y_b),\qquad
g_- =I,
\]
\[
g_+=\Gamma:=
\begin{pmatrix}
1-bS_*&-2b+b^2S_*\\
S_*&1-bS_*
\end{pmatrix}.
\tag{9}
\]

This follows directly from (5); in particular \(\det\Gamma=1\).
Every edge competitor for these data has the same two endpoint values
of \(w\) and \(S(w)=S_*\), because its final frame's lower-left entry
is precisely \(S(w)\).

## 3. A dual certificate over all measurable edge controls

Define

\[
\mu=\frac{\int_0^s x^2w_*(x)\,dx}{\int_0^s w_*(x)\,dx},
\qquad 0<\mu<s^2,
\]
\[
\lambda(x)=\frac1{w_*(x)}
\int_0^x(r^2-\mu)w_*(r)\,dr.
\tag{10}
\]

Let \(b_*\) be the successive coefficient function
\(b_-,b_+,b_-,b_+\) of (7). The function \(\lambda\) is absolutely
continuous and satisfies

\[
\lambda'+b_*\lambda=x^2-\mu\quad\text{a.e.}
\tag{11}
\]

It vanishes at exactly \(-s,0,s\). To verify all signs, put
\(r_0=\sqrt\mu\in(0,s)\). On \((0,r_0)\), the integral in (10)
strictly decreases from zero. On \((r_0,s)\), it strictly increases
to zero at \(s\), so it remains negative until that endpoint. On
\((s,b)\), the integrand is strictly positive and the integral is
positive. Since \(w_*\) is even, \(\lambda\) is odd. Therefore

| Interval | \(b_*\) | Sign of \(\lambda\) |
| --- | --- | --- |
| \((-b,-s)\) | \(b_-\) | negative |
| \((-s,0)\) | \(b_+\) | positive |
| \((0,s)\) | \(b_-\) | negative |
| \((s,b)\) | \(b_+\) | positive |

Take any admissible measurable edge competitor \(w\) with the data (9).
The endpoint values of \(w-w_*\) vanish, and its integral is zero.
Integration by parts, using (11) and \(w_*'=b_*w_*\), gives

\[
\begin{aligned}
M(w)-M(w_*)
&=\int_{-b}^b(x^2-\mu)(w-w_*)\,dx\\
&=-\int_{-b}^b\lambda(x)\bigl(w'(x)-b_*(x)w(x)\bigr)\,dx
\ge0.
\end{aligned}
\tag{12}
\]

Every integrand in the last expression is nonnegative: where
\(\lambda>0\), \(b_*=b_+\) and the upper bound in (3) applies;
where \(\lambda<0\), \(b_*=b_-\) and the lower bound applies.

The equality case is exact. If (12) is zero, its nonnegative integrand
vanishes almost everywhere. The only zeros of \(\lambda\) are the
three switch points, so \(w'=b_*w\) almost everywhere. The fixed
initial value and uniqueness for this scalar linear equation imply
\(w=w_*\) on the whole interval. Formula (2) then fixes the edge control
almost everywhere, while (5) fixes physical time, state, and frame.
Thus \(w_*\) is the unique global minimizer of the full edge problem,
not merely a minimum among nearby four-arc descriptions.

## 4. The physical cost can be arbitrarily small

From (8),

\[
S_*\le\frac{32b}{9},\qquad
M(w_*)\le b^2S_*,\qquad
C_*\le\frac{25b}{3}+\frac{16b^3}{3}
\le\frac{76b}{9}<9b.
\tag{13}
\]

Here \(b^2\le q^2/16=1/48\). In particular
\(C_*<9b\le3\sqrt3/4<3/2<\pi\). Taking \(b\) arbitrarily small
gives arbitrarily small cost, without collapsing any of the four arcs
at a fixed positive \(b\).

The same bounds give

\[
0<bS_*\le\frac{32b^2}{9}\le\frac2{27}<1.
\tag{14}
\]

Consequently both the first column of \(\Gamma\) and its reflected
first row lie strictly in the first quadrant:

\[
(1-bS_*,S_*),\qquad
(1-bS_*,2b-b^2S_*).
\tag{15}
\]

These explicit signs will fix the angle branches in the full-control
comparison.

## 5. Full-control competitors: a tangent winding costs more than \(3\pi\)

Consider any strict-star integral trajectory on \([0,T]\), with arbitrary
measurable simplex control \(u=(u_0,u_1,u_2)\), having precisely the data
(9). Its terminal time is unrestricted. In the original coordinates,

\[
Z_u=
\begin{pmatrix}
(u_1-u_2)/\sqrt3&(u_0-2u_1-2u_2)/3\\
u_0&(u_2-u_1)/\sqrt3
\end{pmatrix},\qquad
\gamma_u=-\operatorname{tr}(Z_uX)>0.
\]

The actual equations are \(g'=gX\) and
\(X'=[Z_u,X]/\operatorname{tr}(Z_uX)\). For \(V=gX\), the
traceless two-by-two identity \(XZ_u+Z_uX=\operatorname{tr}(XZ_u)I\)
gives

\[
V'=-\frac{2}{\operatorname{tr}(Z_uX)}VZ_u
\quad\text{a.e.}
\tag{16}
\]

Let \(e_1=(1,0)^\mathsf T\), \(c(t)=g(t)e_1\), and
\(v(t)=V(t)e_1=c'(t)\). The vectors are continuous and nonzero,
and their relevant derivatives exist almost everywhere. Since
\(\det g=\det X=1\), (16) gives

\[
\det(v,v')=
-\frac{2u_0}{\operatorname{tr}(Z_uX)}
=\frac{2u_0}{\gamma_u}\ge0,
\qquad
\det(c,v)=X_{21}>0.
\tag{17}
\]

Continuous nonzero absolutely continuous planar curves have absolutely
continuous lifted arguments, with derivative \(\det(v,v')/\|v\|^2\).
This follows by differentiating a local argument chart; finitely many
charts cover the compact image. Thus the lifted tangent angle \(\psi\)
satisfies

\[
\psi'=\frac{2u_0}{\gamma_u\|v\|^2}\ge0
\quad\text{a.e.}
\tag{18}
\]

The endpoint data fix the tangent vectors themselves:

\[
v(0)=X_-e_1=\frac1{y_b}(-b,1)^\mathsf T,
\qquad
v(T)=\Gamma X_+e_1=v(0).
\tag{19}
\]

Hence \(\psi(T)-\psi(0)=2\pi m\) for an integer \(m\ge0\).
We now show that if \(m\ge1\), the cost exceeds \(3\pi\).

### Matching the three winding integers

Let \(\phi\) be the lifted angle of the first column \(c=ge_1\),
with \(\phi(0)=0\). Equation (17) keeps
\(\psi-\phi\) in the interval \((0,\pi)\), choosing the branch
containing its initial value. Let
\(\phi_f\in(0,\pi/2)\) be the ordinary angle of the first vector
in (15). The fixed endpoint vectors in (19) give
\(\psi(0)\in(\pi/2,\pi)\) and
\(\psi(0)-\phi_f\in(0,\pi)\). Therefore

\[
\phi(T)=\phi_f+2\pi m.
\tag{20}
\]

Next write \(g=\left(\begin{smallmatrix}a&b_1\\c_1&d_1\end{smallmatrix}\right)\)
and let \(\theta\) be the lifted angle of its reflected first row
\(r=(a,-b_1)\), with \(\theta(0)=0\). Its direction can never be
opposite to that of the first column \((a,c_1)\). Indeed, if
\((a,c_1)=-\lambda(a,-b_1)\) with \(\lambda>0\), then \(a=0\),
\(c_1=\lambda b_1\), and
\(\det g=-\lambda b_1^2\le0\), a contradiction.
Consequently the continuous difference \(\phi-\theta\), initially
zero, stays in \((-\pi,\pi)\).

Let \(\theta_f\in(0,\pi/2)\) be the ordinary angle of the second
vector in (15). Since \(\phi_f-\theta_f\in(-\pi/2,\pi/2)\), (20)
and this non-antipodality imply

\[
\theta(T)=\theta_f+2\pi m.
\tag{21}
\]

### Cost controls the reflected-row angle

Write \(X=\left(\begin{smallmatrix}\alpha&\beta\\\gamma&-\alpha\end{smallmatrix}\right)\).
Strict star implies \(\gamma>0\), \(\beta<0\), and
\(-\alpha^2-\beta\gamma=1\). Differentiating the reflected row gives

\[
\theta'
=\frac{-\beta a^2+2\alpha a b_1+\gamma b_1^2}{a^2+b_1^2}
\le\gamma-\beta=-\operatorname{tr}(JX),
\qquad J=\begin{pmatrix}0&-1\\1&0\end{pmatrix}.
\tag{22}
\]

For the inequality, the difference between the right numerator
\((\gamma-\beta)(a^2+b_1^2)\) and the left numerator is the positive
quadratic form
\(\gamma a^2-2\alpha a b_1-\beta b_1^2\). Its matrix has positive
leading entry \(\gamma\) and determinant one. Integrating (22),

\[
C=-\frac32\int_0^T\operatorname{tr}(JX)\,dt
\ge\frac32\theta(T)
=\frac32(\theta_f+2\pi m)>3\pi
\qquad(m\ge1).
\tag{23}
\]

All branch choices are forced by (14)–(21); no closeness convention or
compactness assertion about competitors has been inserted.

## 6. Unique optimality for the entire fixed-endpoint problem

If \(m=0\), equation (18) has a nonnegative integrand and zero
integral. Since its denominator is positive, \(u_0=0\) almost
everywhere. The competitor is therefore an edge trajectory. Its state
coordinate \(x\) increases from \(-b\) to \(b\), so it has precisely
the representation and endpoint constraints of Sections 1–3. Equation
(12) gives \(C\ge C_*\), with equality only for the constructed
trajectory and its control almost everywhere.

If \(m\ge1\), equation (23) gives \(C>3\pi>C_*\).
These cases exhaust every measurable simplex control. Thus the trajectory
(7) is the unique global minimizer with endpoint data (9), and its cost
can be made arbitrarily small by (13).

This also proves the weaker neighborhood statement directly: any competitor
whose contact-0 tangent remains in the open half-plane about the direction
\((-b,1)\) has \(m=0\), hence must remain on the edge. The full winding
argument shows that no distant lower-cost competitor was missed.

## Consequence for further exclusions

The forward four-arc exclusion is intrinsically oriented. It cannot be
extended to reverse four-arc windows by imposing a small total window cost,
by allowing arbitrary measurable third-vertex perturbations, or by appealing
only to local optimality with the full frame and state endpoints fixed.
The explicit examples satisfy all of those stronger tests.

Their global optimality for this endpoint problem also means that necessary
conditions such as an edge maximum principle cannot exclude them. A proposed
new global Reinhardt exclusion must use additional information from the
closed endpoint condition, adjoining arcs, or a larger deformation. This
note does not rule out such arguments and does not settle any remaining
closed word class.
