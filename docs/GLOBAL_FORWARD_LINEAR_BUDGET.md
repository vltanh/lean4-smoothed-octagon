# A linear neighbor budget at an all-forward minimum

Date: 2026-11-07. Hand reduction with an exact rational polynomial
certificate. No Lean, Lake, typechecking, or CI.

## Statement

In the remaining all-forward case with `N>=7` pieces, let `a` be the
global active-margin minimum, and let `b,c` be its two neighbors. Use the established bounds
`4/3<a²<20/11`, the strict-star inequalities `ab,ac<4`, and the
whole-period cost budget `C<=A_oct`. Set

\[
U=4/a^2,\qquad z=b/a,\qquad w=c/a.
\]

Then

\[
\boxed{\quad z+w<\frac53(U-1).\quad}                 \tag{1}
\]

This supplies a rational linear restriction on the three central
variables in the fixed minimum system. It uses the existing seven-entry
scalar cost lower bound and applies uniformly in the number of pieces.
It does not close F or claim a new endpoint-preserving deformation.

## 1. Reduce a violation to one scalar curve

Let `G` be the edge function in
[GLOBAL_STRUCTURE_FORWARD_MINIMUM_BUDGET](GLOBAL_STRUCTURE_FORWARD_MINIMUM_BUDGET.md).
Define

\[
g_U(x)=3x-U-\frac12\log\frac{(1+x)^2}{1+U}
       -\frac{x^2}{2}\log\frac{(1+x)^2}{x^2+U}.
\tag{2}
\]

Direct substitution gives `G(a,ax)=a² g_U(x)`. Therefore the existing
minimum budget gives

\[
C\ge\frac{\sqrt3}{U}\{2g_U(z)+2g_U(w)+3g_U(1)\}.
\tag{3}
\]

On `1<=x<=U`, this function is increasing and concave in `x`; these are
exactly the edge derivative and concavity statements in Sections 1–2
of that note. The statements extend to the closed comparison domain.

Suppose (1) fails. Put

\[
r=\frac53(U-1),\qquad x_* =r-1=\frac{5U-8}{3}.
\]

Since `11/5<=U<=3`, one has `2<=r<=U+1` and `1<=x_*<=U`.
Lower `z,w` if needed, retaining values at least one, until their sum is
`r`. Monotonicity does not increase the right side of (3). At fixed sum,
concavity places the minimum of the two-edge sum at an endpoint of the
segment, namely `(1,x_*)` or `(x_*,1)`. Consequently

\[
C\ge\frac{\sqrt3}{U}\{2g_U(x_*)+5g_U(1)\}.          \tag{4}
\]

These changes are comparisons of scalar expressions only. No modified
array is asserted to close or to satisfy PMP.

## 2. A positive polynomial proves the uniform contradiction

For `v>=1`, put `t=(v-1)/(v+1)` and

\[
L_+(v)=2t+\frac{2t^3}{3(1-t^2)}.
\]

The convergent expansion of `2 atanh t` gives `log v<=L_+(v)`:
after its linear term, every coefficient is at most `1/3`. Let
`gbar_U(x)` be (2) with both logarithms replaced by `L_+`. On the
present domain both logarithm arguments are at least one. Thus
`g_U(x)>=gbar_U(x)`.

Define the rational function

\[
D(U)=2\overline g_U((5U-8)/3)+5\overline g_U(1)
     -\frac{2501}{1384}U.                           \tag{5}
\]

Writing `D=P/Q` in the normalization below gives

\[
\begin{aligned}
Q(U)= {}&934200(U-1)^2(U+1)(U+5)\\
&\cdot(25U^2-71U+64)(25U^2-41U+34)
       (50U^2-121U+89).
\end{aligned}                                      \tag{6}
\]

This is positive on the entire interval: the three quadratic
discriminants are respectively `-1359,-1719,-3159`, and their leading
coefficients are positive. The numerator has degree eleven and satisfies

\[
\frac{15625}{4096}(1+t)^{11}
P\!\left(\frac{11+15t}{5+5t}\right)
=\sum_{j=0}^{11}c_jt^j,\qquad t\ge0,               \tag{7}
\]

with the following positive integer coefficients, in increasing order.

| `j` | `c_j` |
|---:|---:|
| 0 | 892004586624 |
| 1 | 18085304987172 |
| 2 | 155004439305393 |
| 3 | 758740802025942 |
| 4 | 2383177735230363 |
| 5 | 5068582904755656 |
| 6 | 7455203371987515 |
| 7 | 7562347243116750 |
| 8 | 5144863695643125 |
| 9 | 2199783702600000 |
| 10 | 513318352762500 |
| 11 | 44906296750000 |

The substitution covers `11/5<=U<3`; the positive leading coefficient
also gives positivity at `U=3`. Equations (5)–(7) therefore prove
`D(U)>0` throughout the closed interval. Since `sqrt3>173/100`, (4)
implies

\[
C>\frac{173}{100}\frac{2501}{1384}=\frac{2501}{800}
>A_{\rm oct}.
\]

The last octagon bound is established in
[GLOBAL_STRUCTURE_FORWARD_MINIMUM_THRESHOLD](GLOBAL_STRUCTURE_FORWARD_MINIMUM_THRESHOLD.md).
This contradicts the whole-period budget and proves (1).

## Verification and remaining scope

The exact checker
[global_forward_completion_linear_budget.py](../explorations/global_forward_completion_linear_budget.py)
constructs (5), clears denominators, checks (6)–(7) and every coefficient,
and checks the three discriminants and the final rational constant.
The monotonicity/concavity reduction and the logarithm inequality are the
hand argument above. The proof does not use a numerical optimizer or a
sampled sign, and excludes no complete class beyond the stated scalar
necessary condition.
