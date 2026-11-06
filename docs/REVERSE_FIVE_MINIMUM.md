# The symmetric member minimizes the full reverse five-arc family

## Statement and inputs

Within the entire positive-duration vertex-word family `02102`, the
normalized cost has its unique minimum at the symmetric factors

\[
Q_0=Q_1=Q_2=Q_3=Q_4=\varphi,\qquad
\varphi=\frac{1+\sqrt5}{2}.
\]

The exact minimum is

\[
\boxed{
\delta_{\rm sym}
=\frac{5(2\sqrt5-2-\log\varphi)}{2(1+2\sqrt5)},
\qquad \delta=\frac{\mathrm{cost}}{\sqrt{12}}.
}
\tag{1}
\]

The comparison includes arbitrary unequal durations and arbitrary
initial states allowed by the actual endpoints and strict star
conditions. It imposes no Pontryagin or reflection-symmetry hypothesis.
The uniqueness is within this five-arc family and its cyclic rebases at
switching times and control relabelings. It is not an unrestricted equality theorem for
the Reinhardt conjecture.

The exact trajectory reduction and algebraic identities are proved in
[`REVERSE_FIVE_ARC.md`](REVERSE_FIVE_ARC.md). This note supplies a sharper
analytic comparison for that reduction. It uses no additional numerical
exploration, symbolic computation, Lean implementation, or kernel check.

Here are the inputs, with all indices modulo five. The positive factors
`Q_i>1` obey

\[
Q_i^2=(Q_{i-1}^2-1)(Q_{i+1}^2-1).
\tag{2}
\]

Set

\[
S=\sum_iQ_i,\qquad V=\sum_iQ_i^{-1},\qquad
F=1-S+\sum_iQ_iQ_{i+2},\qquad D=2S+F+1.
\]

The exact cost identity from the reference note is

\[
\boxed{
\delta=1-\frac{\sum_i f(Q_i)-6}{2D},
\qquad f(Q)=\frac{Q+1}{Q-1}\log Q.
}
\tag{3}
\]

For clarity, (3) follows there from `N=UD`,
`B_i²=4U(Q_i+1)/(Q_i−1)`, and
`ΣB_iB_{i+1}=4N−8U`, substituted into the actual constant-control cost.
It is not a newly assigned objective.

## 1. Two algebraic lower bounds

Multiplying (2) and taking the positive square root gives

\[
\prod_i(Q_i^2-1)=\prod_i Q_i,
\qquad
\prod_i(Q_i-Q_i^{-1})=1.
\]

All five factors in the last product are positive. The arithmetic–geometric
mean inequality gives

\[
S-V\ge5.
\tag{4}
\]

Cauchy–Schwarz gives `SV≥25`. Combining it with `V≤S−5` yields

\[
S(S-5)\ge25,\qquad
\boxed{S\ge5\varphi.}
\tag{5}
\]

If `S=5φ`, both inequalities must be equalities. Equality in
Cauchy–Schwarz forces all `Q_i` to be equal, and their sum then gives
`Q_i=φ` for every `i`.

We also have

\[
\boxed{F\ge6.}
\tag{6}
\]

To verify it directly, put
`A=√(Q_i²−1)` and `B=√(Q_{i+2}²−1)`. Equation (2) gives
`AB=Q_{i+1}`. Then

\[
(Q_iQ_{i+2})^2-(Q_{i+1}+1)^2=(A-B)^2\ge0.
\]

Both quantities being compared are positive, so
`Q_iQ_{i+2}≥Q_{i+1}+1`. Sum over `i` to obtain (6). In particular,

\[
D\ge2S+7>0.
\tag{7}
\]

## 2. A strictly concave function of `Q+Q⁻¹`

For `z≥2`, define

\[
G(z)=2\int_0^1
\frac{z+2}{(1-t^2)z+2(1+t^2)}\,dt.
\tag{8}
\]

For `Q>1`, put `v=(Q−1)/(Q+1)`. The elementary logarithm integral
gives

\[
\log Q=2\operatorname{arctanh}v,
\qquad
\frac{\operatorname{arctanh}v}{v}
=\int_0^1\frac{dt}{1-v^2t^2}.
\]

Since `v²=(z−2)/(z+2)` when `z=Q+Q⁻¹`, equation (8) says exactly

\[
\boxed{f(Q)=G(Q+Q^{-1}).}
\tag{9}
\]

Write `A_t(z)=(1−t²)z+2(1+t²)`. For `z≥2`, its value is at least
four. Thus differentiating the integral on compact `z` intervals is
justified by a uniform positive denominator, and

\[
G'(z)=8\int_0^1\frac{t^2}{A_t(z)^2}\,dt>0,
\]

\[
G''(z)=-16\int_0^1\frac{t^2(1-t^2)}{A_t(z)^3}\,dt<0.
\tag{10}
\]

Therefore `G` is strictly increasing and strictly concave. Direct
evaluation at `z=2` gives

\[
G(2)=2,\qquad G'(2)=\frac16,
\qquad 0<G'(z)\le\frac16\quad(z\ge2).
\tag{11}
\]

Also `f(Q)>2` for `Q>1`: the integrand
`1/(1−v²t²)` is strictly greater than one for `t∈(0,1]`.
In particular, the numerator in (3) is positive:

\[
\sum_i f(Q_i)-6>4>0.
\tag{12}
\]

## 3. Reduction to one scalar with the correct denominator direction

By Jensen's inequality and then the increase of `G`,

\[
\sum_i f(Q_i)
=\sum_iG(Q_i+Q_i^{-1})
\le5G\!\left(\frac{S+V}{5}\right)
\le5G\!\left(\frac{2S-5}{5}\right),
\tag{13}
\]

where the last step uses (4). Set

\[
z=\frac{2S}{5}-1\ge2\varphi-1=\sqrt5.
\tag{14}
\]

Equations (7), (12), and (13) give

\[
\begin{aligned}
\delta
&=1-\frac{\sum_i f(Q_i)-6}{2D}\\
&\ge1-\frac{5G(z)-6}{2D}\\
&\ge1-\frac{5G(z)-6}{2(5z+12)}.
\end{aligned}
\tag{15}
\]

The positivity in (12) ensures the final denominator comparison has
the stated direction; it is not valid to omit that sign check.

## 4. The remaining quotient strictly decreases

Define

\[
\mathcal R(z)=\frac{5G(z)-6}{5z+12},\qquad z\ge2.
\]

Its derivative is

\[
\mathcal R'(z)=\frac{25}{(5z+12)^2}
\left[\left(z+\frac{12}{5}\right)G'(z)-G(z)+\frac65\right].
\tag{16}
\]

Concavity places the tangent at `z` above the graph at `2`, so

\[
G(z)\ge G(2)+(z-2)G'(z)=2+(z-2)G'(z).
\]

Use this and (11) in the bracket in (16):

\[
\begin{aligned}
\left(z+\frac{12}{5}\right)G'(z)-G(z)+\frac65
&\le\frac{22}{5}G'(z)-\frac45\\
&\le\frac{22}{30}-\frac45=-\frac1{15}<0.
\end{aligned}
\tag{17}
\]

Thus `𝓡` is strictly decreasing throughout the entire needed domain.
From (14)–(15),

\[
\delta\ge1-\frac12\mathcal R(z)
\ge1-\frac12\mathcal R(\sqrt5).
\tag{18}
\]

## 5. Exact value and equality

Since `φ+φ⁻¹=√5`, formula (9) gives

\[
G(\sqrt5)=\frac{\varphi+1}{\varphi-1}\log\varphi
=(2+\sqrt5)\log\varphi.
\]

Substitution into (18), using
`12+5√5=(2+√5)(1+2√5)`, gives exactly the right side of (1).

If any `Q_i` differs from `φ`, equation (5) has `S>5φ`, hence
`z>√5`. The strict decrease in (17) makes the second inequality in
(18) strict. Therefore

\[
\delta>\delta_{\rm sym}
\quad\text{unless every }Q_i=\varphi.
\tag{19}
\]

Conversely, at the golden tuple all the inequalities used above are
equalities: `S=5φ`, `V=S−5`, `F=6`, and all five arguments of `G` are
equal. The exact endpoint construction in
[`REVERSE_FIVE_ARC.md`](REVERSE_FIVE_ARC.md) realizes this tuple as an
actual strict star trajectory. Hence the minimum is attained.

The active margins and physical durations there are also equal:

\[
a_i^2=\frac4{1+2\sqrt5},\qquad
t_i=\frac{\log\varphi}{\sqrt{1+2\sqrt5}}
\quad(i=0,\ldots,4).
\]

The noncentral holonomy determines the initial state uniquely when the
initial frame is fixed to the identity. Thus the equality factors
identify the unique normalized symmetric reverse five-arc trajectory,
with the cyclic rebasing and relabeling qualifications in the statement.

## Scope

The companion note already proves that every member of this family has
cost strictly greater than the circle, hence greater than the octagon.
The present result additionally locates its exact minimum and proves
strictness for every asymmetric factor tuple.

This is a global comparison within the complete reverse five-arc
family. It does not classify trajectories with six or more arcs, give
a uniform switch bound, or settle the unrestricted Reinhardt comparison.
