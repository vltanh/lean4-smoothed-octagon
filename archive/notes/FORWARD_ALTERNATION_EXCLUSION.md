# Forward four-arc alternation admits a strict endpoint-preserving improvement

Status: complete hand argument, 2026-11-06. No new Lean source, compilation,
Lake invocation, or CI execution. The proof uses ordinary differentiation,
linear algebra, and the implicit function theorem; no computer output is a
proof premise.

## Theorem and exact scope

Use the control labels and orientation of `VERTEX_WORD_REDUCTION.md`, with
indices modulo three. Suppose a strict-star admissible trajectory contains
four consecutive positive-duration vertex-control arcs with word

    i, i+1, i, i+1.

There are arbitrarily close admissible replacements with the same initial
and final frame AND state and strictly smaller cost. Elapsed time is free.
Consequently this window cannot occur in a global minimizer, at any total
word length. The reverse word `i,i-1,i,i-1` is NOT excluded by this theorem.

This strengthens `EDGE_SWITCH_BOUND.md`: its five-arc alternating exclusion
follows because any five alternating arcs contain a forward four-arc window.
It does not bound the total number of arcs involving all three controls.

## 1. Edge coordinates and the endpoint constraints

Cyclically rotate labels so that the omitted vertex is zero. The forbidden
word is then `1212`. Put q=1/sqrt(3) and use the upper-half-plane state

    X = (1/y) [[x, -(x^2+y^2)], [1, -x]].

On the edge u_0=0 the coordinate x is strictly increasing. Set w(x)=y(x)^(-2)
and let [a,b] be the x-interval of the window, with -q<a<b<q. The strict
star inequalities are

    0 < w(x) < 1/(q^2-x^2).

Controls 1 and 2 have respective logarithmic derivatives

    w'/w = b_+(x) = 2/(q-x),
    w'/w = b_-(x) = -2/(q+x).

Their difference is d(x)=4q/(q^2-x^2)>0. These equations, and the following
frame formula, are derived directly from the actual state equations in
`EDGE_SWITCH_BOUND.md`, Sections 1-2.

Keep a,b,w(a), and the initial frame fixed. Define

    t(x) = integral_a^x sqrt(w(r)) dr,
    s(x) = integral_a^x w(r) dr,
    h(x) = [[1,-x],[s(x),1-s(x)*x]].

The frame is g(x)=g(a) h(a)^(-1) h(x). Thus both terminal endpoints are
preserved exactly by keeping

    G_0 = log(w(b)),       G_1 = integral_a^b w(x) dx.

The physical cost of the window is

    C = (3/2) [(b-a) + G_1 + M],
    M = integral_a^b x^2 w(x) dx.

It therefore suffices to decrease M while fixing G_0,G_1. Fixing these two
numbers is not a substitute for the full endpoint conditions: the explicit
frame formula proves that these numbers are precisely the remaining endpoint
data in these coordinates.

## 2. A smooth one-dimensional exact endpoint fiber

Write a<s_1<s_2<s_3<b for the switches. Nearby ordered tuples determine the
same sequence of controls +,-,+,- and the unique function

    w_s(x)=w(a) exp(integral_a^x b_s(r) dr).

All integrals here are finite sums over intervals with smooth moving
endpoints and smooth positive integrands. The endpoint map G=(G_0,G_1) and
M are C^2 (indeed smooth) in the switch tuple.

At the original tuple put

    k_i = b_before(s_i)-b_after(s_i),
    S_i = integral_(s_i)^b w(x) dx,
    J_i = integral_(s_i)^b x^2 w(x) dx.

The signs for +,-,+,- are

    k_1>0,    k_2<0,    k_3>0.

Differentiating the exponential solution gives

    partial_i G_0 = k_i,
    partial_i G_1 = k_i S_i,
    partial_i M   = k_i J_i.                         (1)

Because w>0, S_1>S_2>S_3. Any two columns k_i(1,S_i) and k_j(1,S_j)
of DG are independent. The exact level set G=G(original) is consequently
a smooth one-dimensional curve near the original switch tuple.

If dM does not vanish on its tangent line, select the tangent direction
with negative dM. The implicit function theorem gives an exact
constraint-preserving curve with smaller M. The only remaining case is
stationarity on this endpoint fiber.

## 3. Stationarity forces the two roots into distinct intervals

At a stationary tuple, independence of DG gives real multipliers lambda,mu
with

    J_i = lambda + mu S_i,        i=1,2,3.             (2)

Subtracting consecutive equations yields

    integral_(s_1)^(s_2) (x^2-mu) w(x) dx = 0,
    integral_(s_2)^(s_3) (x^2-mu) w(x) dx = 0.        (3)

A continuous function of one strict sign has a nonzero integral against
the positive weight w. Since the polynomial x^2-mu cannot vanish on an
interval, each interval in (3) must contain a root strictly in its interior.
There must therefore be two distinct real roots, in their natural order:

    mu>0,
    s_1 < -sqrt(mu) < s_2 < sqrt(mu) < s_3.            (4)

In particular

    mu-s_1^2<0,    mu-s_2^2>0,    mu-s_3^2<0.         (5)

This step does not assume that the switches are symmetrically placed or
that any of the four arcs has equal duration.

## 4. The constrained second variation is strictly negative

Consider the Lagrangian

    L = M - mu G_1 - lambda G_0,

with the multipliers fixed at their stationary values. Set
A_i=J_i-mu S_i. For i not equal to j, differentiation of the tail
integral gives

    partial_j A_i = k_j A_max(i,j).

For the diagonal it gives

    partial_i A_i = -(s_i^2-mu) w(s_i) + k_i A_i.

Since partial_i L=k_i(A_i-lambda) and A_i=lambda at the stationary tuple,
the terms containing partial_i k_i cancel. The full Hessian is exactly

    Hess(L) = lambda k k^T
              + diag(k_i w(s_i) (mu-s_i^2)).         (6)

For clarity, the off-diagonal entry is lambda k_i k_j. Its diagonal entry
is lambda k_i^2+k_i w(s_i)(mu-s_i^2); no mixed term is omitted.

Let v be a nonzero tangent vector to the endpoint fiber. The first
constraint in (1) gives k dot v=0. Therefore

    v^T Hess(L) v = sum_i k_i w(s_i) (mu-s_i^2) v_i^2. (7)

Each of the three coefficients in (7) is strictly negative, by (5), the
signs +,-,+ of k, and w(s_i)>0. Hence (7) is strictly negative for every
nonzero v, including the nonzero tangent direction furnished by rank(DG)=2.

Take a C^2 parametrization s(epsilon) of the exact endpoint fiber with
s'(0)=v. Along this curve the constraints are constant. At stationarity
its first cost derivative is zero, and the ordinary constrained-Hessian
identity gives

    (d^2/d epsilon^2) M(s(epsilon)) at 0
       = v^T Hess(L) v < 0.

This identity also follows by differentiating G(s(epsilon))=constant twice
and using grad M=lambda grad G_0+mu grad G_1. Taylor's theorem shows that
M(s(epsilon))<M(s(0)) for all sufficiently small nonzero epsilon.
Thus a stationary tuple is a strict local maximum on its endpoint fiber,
not a local minimum. Together with the nonstationary case, this proves the
strict improvement for every tuple.

## 5. The variation is an actual admissible replacement

The original compact window has a positive uniform margin in all its strict
star inequalities. The explicit w_s varies uniformly with its switch tuple;
small variations preserve those margins and keep the three switches strictly
ordered. The positive time change t_s(x) has a C^1 inverse. The reconstructed
states and frames are continuous, piecewise smooth, and absolutely continuous,
and satisfy the actual integral state equations with measurable vertex control.

Both g and X match their original values at each endpoint. Insert the new
window and translate the subsequent original segment by the change in elapsed
time. State and frame continuity persist; the one-sided frame derivatives at
each seam agree because both equal gX. This gives an admissible full trajectory
with the same global endpoints and lower cost. The total terminal time is free
in the original problem, so its change is permitted.

## 6. Consequences and the unresolved reverse orientation

1. No minimizing finite word, or finite window of a longer minimizing word,
   contains `i,(i+1),i,(i+1)`. This is valid across a cyclic seam after the
   actual rebasing operation in `VERTEX_WORD_REDUCTION.md`.
2. Among the three genuine six-piece cyclic word orbits passing the existing
   ordering test, the orbit represented by `010120` is excluded from global
   minimizers: its initial four pieces are `0101`. Its other representatives
   are `012010`, `012012`, `012020`, `012120`, and `020120`.
3. At a stationary reverse alternating window, the signs of all k_i are
   reversed. Formula (7) is then strictly positive. Therefore the same
   edge-restricted argument cannot exclude that orientation. Extending the
   conclusion to both orientations would be a sign error.

The other genuine six-piece orbits, represented by `010202` and `010210`,
are not excluded here. General three-letter windows, all longer words, the
unrestricted lower bound, and global affine rigidity remain unresolved.
The theorem is a strict local non-minimality result; it does not itself
state C>=A_oct for every trajectory containing the forbidden window, nor
does it prove a six-to-five replacement theorem.

## Sources and checks

- `EDGE_SWITCH_BOUND.md`: exact edge flow, endpoint map, cost, and first
  derivatives, with an independent five-piece first-variation argument.
- `VERTEX_WORD_REDUCTION.md`: control orientation and actual cyclic rebasing.
- Hales-Vajjha, Packings of Smoothed Polygons, Section 8.1,
  https://arxiv.org/html/2405.04331v1#Ch8.S1 : the underlying edge problem.
- Hales, On the Reinhardt Conjecture, Section 7.6,
  https://arxiv.org/html/1103.4518#S7.SS6 : the larger link-reduction goal.

The new step is the explicit constrained Hessian (6)-(7). Its signs, the
rank-two endpoint map, strict interior feasibility, and the full endpoint
splice have been checked in the hand argument above. This is not an
independent peer review or a kernel-validation claim.
