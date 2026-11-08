# Every finite normal vertex period has negative elliptic primary costate

Date: 2026-11-07 UTC. Hand proof with a supplementary exact identity
checker and an [independent internal audit](GLOBAL_NORMAL_PERIOD_STRUCTURE_AUDIT.md).
No Lean, Lake, typechecking, or CI.

## Theorem and scope

Let a strict-star trajectory have a finite positive vertex representation,
the actual twisted frame, state, and costate endpoints, and a normal
free-time Pontryagin lift with free-initial-state transversality. Normalize
its physical cost multiplier to `lambda=-1`. Then

\[
\boxed{\Lambda_1(t)\text{ is negative elliptic for every }t.}
\tag{1}
\]

This extends the pure-forward theorem in
[GLOBAL_STRUCTURE_FORWARD_ELLIPTIC](GLOBAL_STRUCTURE_FORWARD_ELLIPTIC.md)
to every possible mixed period. The proof uses the reverse-run
classification in
[MIXED_GLOBAL_MINIMUM_STRUCTURE](MIXED_GLOBAL_MINIMUM_STRUCTURE.md):
every surviving mixed reverse run has exactly two switches and a strict
middle active-margin minimum. Entirely reverse periods are already
impossible. The same proof below also gives a projective form of the
pure-forward ellipticity argument.

There is no equal-factor, transverse-switch, endpoint-rank, geometric
ray-coverage, or cost-budget hypothesis. The projective contradiction
comes from the **full central frame monodromy and exact PMP identities**;
cyclic permutations of the control labels alone would not suffice.
The theorem is not asserted for arbitrary local PMP windows.

For an actual minimizer, finite representation and normality are supplied
by the established global inputs. For a competitive period, (1) makes the
existing cost--Casimir bound available in all remaining cases F/M1/M2.
It gives no opposite Casimir inequality and no negative cost variation,
so it does not close those remaining comparison cases.

## 1. One state-closed action for all sign patterns

Use the determinant-one triangular coordinates of
[VERTEX_WORD_REDUCTION](VERTEX_WORD_REDUCTION.md). They reverse the
orientation of the physical coordinates. Let `a_i>0` be the constant
active margin on arc `i`, and let `epsilon_i=+1` or `-1` be the switch
direction immediately after that arc. All indices are extended with the
actual period `N`, so `a_(i+N)=a_i` and `epsilon_(i+N)=epsilon_i`.
Write

\[
s_i=a_i+a_{i+1},\qquad K_i=a_i^2+4,
\qquad a_i a_{i+1}<4.
\]

The exact factor on arc `i` is

\[
\boxed{
q_i=s_{i-1}^{\epsilon_{i-1}}s_i^{\epsilon_i}
K_i^{-(\epsilon_{i-1}+\epsilon_i)/2}>1.
}
\tag{2}
\]

For the four possible incident sign pairs this reads

| Incident signs | Factor `q_i` |
|---|---|
| `++` | `s_(i-1) s_i / K_i` |
| `--` | `K_i / (s_(i-1) s_i)` |
| `-+` | `s_i / s_(i-1)` |
| `+-` | `s_(i-1) / s_i` |

The initial state is reconstructed from the two incident active margins
and the third margin `(4-a_(i-1)a_i)/s_(i-1)`, assigned to the corresponding
labels. Formula (2) is the ordinary increasing/decreasing margin update.
The periodic chain therefore resolves the twisted state endpoint while
allowing the initial state to vary. Strict positivity and the strict
factor inequalities give an open smooth family around each period.

Set `J=C/sqrt(12)` and define the symmetric function

\[
\begin{aligned}
G(a,b)={}&3ab-4-(a^2+b^2)\log(a+b)\\
&+\tfrac12a^2\log(a^2+4)
 +\tfrac12b^2\log(b^2+4).
\end{aligned}
\]

The cost of the state-closed chain is exactly

\[
\boxed{8J=\sum_i\epsilon_i G(a_i,a_{i+1}).}
\tag{3}
\]

To verify the sign in (3), put
`b_i=(4-a_(i-1)a_i)/s_(i-1)`. The initial difference between the
decreasing and increasing margins of arc `i` is
`epsilon_(i-1)(a_(i-1)-b_i)`; its final increasing-minus-decreasing
difference is `epsilon_i(a_(i+1)-b_(i+1))`. The exact arc cost is
their sum times `a_i`, minus `a_i^2 log q_i`, all divided by eight.
Summing the two contributions at edge `i` gives
`epsilon_i(3a_i a_(i+1)-4)`. Substituting (2) into the logarithmic
terms gives the other terms of (3). No formal reversal of an admissible
curve is used.

For later differentiation, define

\[
f(t)=t-t^{-1}-\log t,\qquad h(t)=\log t-1+t^{-1}.
\]

Direct differentiation gives

\[
\frac{G_a(a,b)}a
=2f(1+b/a)+h(1+4/a^2).
\tag{4}
\]

At an index with equal incident signs `epsilon`, write
`a=a_i`, `p=a_(i-1)`, `n=a_(i+1)`,
`s_-=p+a`, `s_+=a+n`, `K=a^2+4`, and `r=s_-s_+/K`.
Then

\[
J_{a_i}=\epsilon\mathcal C_i,
\qquad
\mathcal C_i=\frac14\left[
p+a+n-a^2\left(\frac1{s_-}+\frac1{s_+}\right)
+\frac{a^3}{K}-a\log r\right].
\tag{5}
\]

At an index with opposite signs, (4) instead gives

\[
J_{a_i}=\frac{\epsilon_i a}{4}
\bigl[f(1+n/a)-f(1+p/a)\bigr].
\tag{6}
\]

The strict factor inequality in (2) says
`epsilon_i(n-p)>0` at such a turn.

## 2. The full frame monodromy and the actual normal multiplier

Put

\[
R=\begin{pmatrix}0&1\\-1&1\end{pmatrix},\quad
E=\begin{pmatrix}1&0\\0&-1\end{pmatrix},\quad
T_0(q)=\operatorname{diag}(q,q^{-1}),
\]
\[
A_i=T_0(q_i)R^{-\epsilon_i},\qquad
P_0=I,\qquad P_i=A_0\cdots A_{i-1},\qquad M=P_N.
\]

The label twist forces `sum epsilon_i=3k+1` for an integer `k`.
The actual tangent product is `F=M R^(sum epsilon_i)`. Its complete
frame endpoint `F=R` is therefore exactly

\[
M=\sigma I,\qquad\sigma=(-1)^k.
\tag{7}
\]

In particular `P_(i+N)=sigma P_i`. This is full matrix centrality,
not just a scalar trace equation.

For `V_i=(partial M/partial a_i) M^-1`, the same full normal PMP
boundary identity as in
[GLOBAL_STRUCTURE_CYCLIC_COSTATE_SECTOR, Section 3](GLOBAL_STRUCTURE_CYCLIC_COSTATE_SECTOR.md#3-use-the-actual-periodic-pmp-boundary-term)
gives

\[
\boxed{
J_{a_i}=\operatorname{tr}(UV_i),\qquad
U=\frac1{\sqrt{12}}\operatorname{Ad}_{X_0^{-1}}
\Lambda_1^{\rm tri}(0).
}
\tag{8}
\]

Indeed `g_T=X_0 F X_T^-1` and the state-closed family has
`X_T=R^-1 X_0 R`. At the actual period the two initial-state
differential terms in this frame identity cancel. The terminal and
initial state-covector terms cancel separately by the actual twisted
free-state transversality. The remaining spatial primary covector is
the one in (8). This argument does not invert an endpoint Jacobian.

Writing `Z_i=Ad_(P_i) E`, direct differentiation of (2) gives

\[
V_i=\frac{\epsilon_{i-1}}{s_{i-1}}(Z_{i-1}+Z_i)
    +\frac{\epsilon_i}{s_i}(Z_i+Z_{i+1})
    -\frac{(\epsilon_{i-1}+\epsilon_i)a_i}{K_i}Z_i.
\tag{9}
\]

The seam is legitimate because (7) makes these adjoint columns periodic.
In the prefix frame `P_i`, the four columns are

\[
\begin{array}{c|c}
++&2\begin{pmatrix}-a/K&q_i^2/s_+\\-1/s_-&a/K\end{pmatrix}\\[3pt]
--&2\begin{pmatrix}a/K&-1/s_-\\1/(q_i^2s_+)&-a/K\end{pmatrix}\\[3pt]
-+&2(n-p)E_{12}/s_-^2\\[3pt]
+-&2(n-p)E_{21}/s_-^2.
\end{array}
\tag{10}
\]

The last two columns are genuine parabolic directions. Their different
prefixes must be retained; a cyclic label rotation does not supply
coverage of spatial projective directions.

## 3. Switch vectors and their quadratic pairings

Let `J_0=[[0,-1],[1,0]]` and define the real symmetric matrix

\[
S=-J_0U,
\qquad \det S=\det U.
\]

At switch `i` define a vector by its actual prefix and switch sign:

\[
y_i=\begin{cases}
q_iP_i e_1/s_i,&\epsilon_i=+1,\\
P_i e_2/(q_i s_i),&\epsilon_i=-1.
\end{cases}
\tag{11}
\]

It satisfies `y_(i+N)=sigma y_i`. Put

\[
d_i=y_i^TSy_i,\qquad e_i=y_{i-1}^TSy_i.
\tag{12}
\]

In the `P_i` frame, the incoming vector is `-e_2/s_-` for an
incoming forward sign and `-e_1/s_-` for an incoming reverse sign.
The outgoing vector is respectively `q_i e_1/s_+` or
`e_2/(q_i s_+)`. Thus (2) immediately gives

\[
\begin{array}{c|c}
++&\det(y_{i-1},y_i)=1/K_i\\
--&\det(y_{i-1},y_i)=-1/K_i\\
-+\text{ or }+-&y_i=-y_{i-1}.
\end{array}
\tag{13}
\]

For either same-sign case, if `M_i=P_i^-1 U P_i`, the local
cross pairing is `e_i=(M_i)_(11)/K_i`, and (8)--(10) give

\[
\boxed{
\mathcal C_i=2(s_-d_{i-1}+s_+d_i-2a_i e_i),\qquad
d_{i-1}d_i-e_i^2=\frac{\det U}{K_i^2}.
}
\tag{14}
\]

The first identity has the same sign in both cases because both the
actual cost derivative and the frame column change by `epsilon`.

At a turn, (10)--(13) instead give

\[
\operatorname{tr}(UV_i)=2\epsilon_i(n-p)d_i.
\]

Comparing with (6) proves the exact secant formula

\[
\boxed{
d_i=d_{i-1}
=\frac18\frac{f(1+n/a)-f(1+p/a)}{(n-p)/a}.
}
\tag{15}
\]

The arguments of `f` are distinct and greater than one. For `t>1`,

\[
f'(t)=1-\frac1t+\frac1{t^2},\qquad
f'(t)-\frac34=\frac{(t-2)^2}{4t^2},\qquad
1-f'(t)=\frac{t-1}{t^2}>0.
\]

Integrating over a nondegenerate interval gives the strict bounds

\[
\boxed{\frac3{32}<d_{i-1}=d_i<\frac18\quad\text{at every turn}.}
\tag{16}
\]

This uses exact stationarity of the actual period. It is stronger than
the positive sign of an unconstrained action derivative.

## 4. Both weak switching derivative inequalities

Define

\[
j_i=\frac{a_i^2+a_i a_{i+1}+a_{i+1}^2}{4s_i^2}.
\]

The actual weak switch inequalities are

\[
\boxed{
\epsilon_i=+1\Longrightarrow d_i\ge j_i/2\ge3/32,
\qquad
\epsilon_i=-1\Longrightarrow d_i\le j_i/2.
}
\tag{17}
\]

Here is the reverse-sign calculation as well as the common interface.
Rotate the old label to 0, write the old/new active margins as `a,b`,
and put `Kappa=F^-1 U F` at the switch. The positive vertex log-clock
Hamiltonians are

\[
\widehat H_j=-\operatorname{tr}(Kappa D_j)
             +\eta\cdot f_j-\ell_j,
\qquad\ell_j=p_j(p_0+p_1+p_2)/8.
\]

They are the physical maximizing Hamiltonians times the positive
factors `p_j/(2 sqrt(12))`. On a `0 -> 1` switch, differentiating
the new zero Hamiltonian along the old log flow gives

\[
2Kappa_{21}-(a^2+ab+b^2)/4\ge0.
\]

On a `0 -> 2` switch the corresponding result is

\[
2Kappa_{12}+(a^2+ab+b^2)/4\ge0.
\tag{18}
\]

For an explicit check, use independent state margins `(a,b_1)` with
`c=(4-ab_1)/(a+b_1)` and

\[
f_0=(0,a+b_1),\quad f_1=(-(a+b_1),0),\quad
f_2=(a+c,-b_1-c).
\]

Their brackets satisfy `[f_0,f_1]=f_0+f_1` and
`[f_0,f_2]=-f_0-f_2`, where the bracket is `Df_j f_0-Df_0 f_j`.
For the group matrices

\[
D_0=\operatorname{diag}(-1,1),\quad
D_1=\begin{pmatrix}1&-2\\0&-1\end{pmatrix},\quad
D_2=\begin{pmatrix}1&0\\2&-1\end{pmatrix},
\]

the combined group brackets are respectively
`[D_0,D_1]+D_0+D_1=2E_12` and
`[D_0,D_2]-D_0-D_2=2E_21`. Differentiating the displayed `ell_j`
gives the two opposite scalar terms in (18), with `b=c` in the
reverse case. These substitutions yield both formulas directly.

The physical switching function is nonpositive before the switch and
nonnegative after it. Its common one-sided derivative is therefore
nonnegative. That derivative is the displayed log-clock derivative
times the positive factor `4 sqrt(12)/(ab)`. Equality, including a
cubic or triple tie, is retained. Finally

\[
d_i=Kappa_{21}/s_i^2\quad(\epsilon_i=+1),\qquad
d_i=-Kappa_{12}/s_i^2\quad(\epsilon_i=-1),
\]

which proves (17). The numerical threshold follows from
`j_i/2-3/32=(a_i-a_(i+1))^2/(32s_i^2)`.

In a mixed period every reverse run has length two. Each of its two
reverse switches abuts one of the turn indices, so (16) applies to
both reverse-edge values. Together with the forward part of (17), this
proves

\[
\boxed{d_i\ge3/32>0\quad\text{at every switch}.}
\tag{19}
\]

For a pure-forward period (19) follows directly from (17).

## 5. The cross pairings have the required signs if the multiplier is nonelliptic

Suppose for contradiction that `det U<=0`. Equations (14) and (19)
give, at every same-sign index,

\[
|e_i|\ge\sqrt{d_{i-1}d_i}\ge3/32.
\tag{20}
\]

We show that `e_i>0` at `++` and `e_i<0` at `--`.
Set `ell=1/s_-+1/s_+`. Direct scalar differentiation of (5) gives

\[
s_-j_{i-1}+s_+j_i=(p+n+a^2\ell)/4,
\]
\[
\frac{s_-j_{i-1}+s_+j_i-\mathcal C_i}{4a}
=\frac{-1+2a\ell-a^2/K+\log r}{16}.
\tag{21}
\]

At `++`, both bounds in (17) are lower bounds. Using (14),

\[
e_i\ge\frac{-1+2a\ell-a^2/K+\log r}{16}>-\frac1{16}.
\tag{22}
\]

Indeed `r=q_i>1`, while strict star gives `a s_-<K` and
`a s_+<K`; hence `a ell>2a^2/K`. Equation (20) excludes the
negative alternative in (22), so `e_i>0`.

At `--`, both switch inequalities in (17) are upper bounds. The
index is the centre of a length-two reverse run, so the minimum
principle gives `a<p` and `a<n`. Thus `a ell<1`, while
`r=q_i^-1<1`. Equations (14) and (21) yield

\[
e_i\le\frac{-1+2a\ell-a^2/K+\log r}{16}<\frac1{16}.
\tag{23}
\]

Equation (20) excludes the positive alternative, so `e_i<0`.
Combining these conclusions with (13),

\[
\boxed{
\operatorname{sign}(e_i)
=\operatorname{sign}\det(y_{i-1},y_i)
\quad\text{at every same-sign index}.
}
\tag{24}
\]

At a turn `y_i=-y_(i-1)` and `e_i=-d_i<0` instead; those two
vectors define the same projective point.

## 6. A monotone projective coordinate contradicts the complete monodromy

Because every `d_i>0`, the real symmetric form `S` with `det S<=0`
is either positive semidefinite of rank one or indefinite. In both
cases there is a real linear functional `h` satisfying

\[
h(y_i)\ne0,\qquad
\operatorname{sign}\bigl(h(y_{i-1})h(y_i)\bigr)
=\operatorname{sign}(e_i)
\tag{25}
\]

at every same-sign index. For rank one write `S=h^T h` after
rescaling. For the indefinite case choose real coordinates with
`S=u^2-v^2` and take `h=u`. The inequalities `d_i>0` give
`|u_i|>|v_i|`, so the sign of `u_(i-1)u_i-v_(i-1)v_i` is
exactly the sign of `u_(i-1)u_i`. This proves (25).

Choose a second linear functional `l` independent of `h`, with the
matrix having rows `h,l` of positive determinant. Define the finite
projective coordinate

\[
z_i=\frac{l(y_i)}{h(y_i)}.
\]

At every same-sign index, (13), (24), and (25) give

\[
z_i-z_{i-1}
=\frac{\det\binom{h}{l}\,\det(y_{i-1},y_i)}
       {h(y_{i-1})h(y_i)}>0.
\tag{26}
\]

At every turn the two vectors are negatives of one another, so the
increment is zero. There is at least one same-sign index: a pure-forward
period has one at every index, and a mixed period has a centre `--`
in each reverse run. Therefore the sum of these increments over a full
period is strictly positive.

But the full central monodromy (7) gives `y_(i+N)=sigma y_i` and
hence `z_(i+N)=z_i`. Its increments must sum to zero. This
contradiction excludes `det U<=0` without presuming any projective
coverage from the control-label twist.

Thus `det U>0`. The symmetric form `S` has positive values by (19),
so it is positive definite. Therefore `U=J_0 S` is positive elliptic
in triangular coordinates. Formula (8) preserves this component, and
the orientation-reversing change to physical coordinates makes
`Lambda_1(0)` negative elliptic. Primary-costate conservation transports
it by determinant-one conjugation, proving (1) at every time.

## Consequence and remaining comparison

For a competitive period, write
`kappa=sqrt(det Lambda_1)>0`. The established complete-period inequality
in [GLOBAL_COST_CASIMIR](GLOBAL_COST_CASIMIR.md) now applies to every
remaining F/M1/M2 candidate:

\[
C\ge\frac{4\pi\kappa}{2\kappa+3},\qquad
\kappa\le\frac{3A_{\rm oct}}{2(2\pi-A_{\rm oct})}<\frac{313}{210}.
\]

These are upper restrictions on the allowed Casimir. No lower bound
contradicting them has been proved here. The local short-pad obstruction
already has negative elliptic primary costate, so the present global
sector theorem does not by itself exclude the remaining double-reverse
runs. A complete cost, continuation, or higher-order argument remains
necessary for M1/M2 and for asymmetric F.

## Validation boundary

[mixed_global_ellipticity_certificate.py](../explorations/mixed_global_ellipticity_certificate.py)
checks the four frame columns, Wronskians, Gram identities, turn secant,
both physical switching brackets, and the scalar threshold identities.
All 32 exact checks pass with Python 3.12.14 and SymPy 1.14.0. The script
uses no sampled period, numerical solver, word-length enumeration, or
trajectory integration. The full-covector interpretation, reverse-run
input, and projective periodicity contradiction are the hand arguments
above. Internal review is not external peer review or kernel validation.
