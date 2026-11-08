# Five-arc comparison: complete coverage and the noncyclic proof

## Established comparison and complete coverage

Every admissible trajectory with five positive-duration vertex-control pieces,
after merging adjacent equal controls, falls into one of three classes under
cyclic rebasing and relabeling:

- A four-arc trajectory, covered by [FOUR_LINK_HAND_PROOF.md](FOUR_LINK_HAND_PROOF.md).
- The five-arc word **01020**.
- The reverse cyclic five-arc word **02102**.

This note proves that **every admissible 01020 trajectory has cost strictly
greater than the octagon**, with arbitrary positive durations and initial
state. Endpoint closure determines a two-parameter family; a global analytic
inequality bounds its exact cost. No Pontryagin condition, equal-duration
hypothesis, or symmetry of the competitor is assumed.

The separate hand proof in [REVERSE_FIVE_ARC.md](REVERSE_FIVE_ARC.md) now
proves that every 02102 trajectory has normalized cost greater than `10/11`,
which is greater than the circle's `π/√12` and the octagon's density.
Together these results compare every admissible trajectory representable
with at most five positive-duration vertex-control pieces. Equality can
occur only in the four-arc octagon case, including a five-piece description
that rebases and merges to that case.

There is no conclusion about all longer words or all measurable controls.

This is a hand proof. Exact symbolic calculations suggested and checked finite
algebra, but are not premises of the inequalities below. No Lean source was
added or executed.

## 1. Exhausting the five-letter words

The necessary condition from
[VERTEX_WORD_REDUCTION.md](VERTEX_WORD_REDUCTION.md) is

\[
\operatorname{last}(j)>\operatorname{first}(j-1),\qquad j\bmod3. \tag{1}
\]

It follows by rebasing an actual admissible trajectory and applying the
measurable-control fixed-edge exclusion. A rebase after \(r\) arcs replaces
\(i_0\cdots i_4\) by \(i_r\cdots i_4,(i_0+1)\cdots(i_{r-1}+1)\), modulo three.
It preserves cost and all endpoint conditions.

After relabeling the first letter to 0, exactly seven of the sixteen reduced
five-letter words pass (1):

\[
01020,\quad01201,\quad01202,\quad01210,\quad02012,\quad02102,\quad02120.
\]

For an enumeration check, the excluded words are 01010, 01012, 01021, 01212,
02010, 02020, 02021, 02101, and 02121. The first and sixth omit a letter;
each of the others violates (1).

Rebasing 01201 after its first arc gives 12011. Its two final pieces merge to
the four-arc word 1201. The five rebases of 01020 give the following orbit:

| Cut | Rebased word after relabeling its first letter to 0 |
| ---: | --- |
| 0 | 01020 |
| 1 | 02120 |
| 2 | 02012 |
| 3 | 01202 |
| 4 | 01210 |

The remaining word 02102 returns to itself under rebasing and relabeling.
Thus the two genuine five-arc comparisons, supplied here and in the
separate reverse-orbit proof, exhaust this arc count. This is a coverage
argument for at most five pieces, not a uniform bound on every minimizer.

## 2. Tangent closure for 01020

Use the rational coordinates in
[FOUR_LINK_HAND_PROOF.md](FOUR_LINK_HAND_PROOF.md). Write \(D_i=-Z_i\), where
the integer matrices \(Z_i\) are those of
[VERTEX_WORD_REDUCTION.md](VERTEX_WORD_REDUCTION.md). On a vertex piece,

\[
c_i=\operatorname{tr}(D_iX)>0,\qquad
X'=[D_i,X]/c_i,\qquad V=gX,\qquad V'=-(2/c_i)VD_i.
\]

For duration \(t_i>0\), put \(q_i=\exp(2t_i/c_i)>1\). The tangent transition is
\(T_i(q_i)=\exp(-(\log q_i)D_i)\). The group and state endpoints force

\[
T_{i_1}(q_1)\cdots T_{i_5}(q_5)=R. \tag{2}
\]

Conjugate by \(L=\left(\begin{smallmatrix}1&1\\1&-1\end{smallmatrix}\right)\).
Traces and determinants are unchanged. In this basis,

\[
R'=\begin{pmatrix}0&1\\-1&1\end{pmatrix},\qquad
T_0(q)=\begin{pmatrix}q&0\\0&q^{-1}\end{pmatrix},
\]
\[
T_1(q)=\begin{pmatrix}q^{-1}&q-q^{-1}\\0&q\end{pmatrix},\qquad
T_2(q)=\begin{pmatrix}q^{-1}&0\\q^{-1}-q&q\end{pmatrix}. \tag{3}
\]

Let the five factors of 01020 be \(p,q,r,s,z>1\). Direct multiplication gives

\[
T_1(q)T_0(r)T_2(s)=
\begin{pmatrix}
\dfrac{r^2-(q^2-1)(s^2-1)}{qrs}&\dfrac{s(q^2-1)}{qr}\\[5pt]
-\dfrac{q(s^2-1)}{rs}&\dfrac{qs}{r}
\end{pmatrix}. \tag{4}
\]

Multiplying by \(T_0(p)\) on the left and \(T_0(z)\) on the right must give
\(R'\). Its upper-left entry is zero. The other entries then give

\[
r=\sqrt{(q^2-1)(s^2-1)},\qquad
p=\frac q{\sqrt{q^2-1}},\qquad z=\frac s{\sqrt{s^2-1}}. \tag{5}
\]

For example, the upper-right and lower-right entries of the middle product
are \(z/p\) and \(pz\); their ratio gives \(p^2=q^2/(q^2-1)\). All roots are
positive. No alternating-factor or symmetry condition was imposed.

Introduce auxiliary scalar parameters, distinct from the control coordinates,

\[
u=\sqrt{\frac{q-1}{q+1}},\qquad
v=\sqrt{\frac{s-1}{s+1}},\qquad 0<u,v<1.
\]

Then

\[
\begin{aligned}
p&=P(u):=\frac{1+u^2}{2u},&
q&=Q(u):=\frac{1+u^2}{1-u^2},\\
r&=\frac{4uv}{(1-u^2)(1-v^2)},&
s&=Q(v),\qquad z=P(v).
\end{aligned} \tag{6}
\]

The middle duration is positive exactly when

\[
r>1\quad\Longleftrightarrow\quad u+v+uv>1. \tag{7}
\]

Indeed its numerator minus denominator factors as
\((u+v-1+uv)(u+v+1-uv)\), whose second factor is positive.

## 3. The state endpoint fixes the initial shape

The state transition on a vertex arc is conjugation by
\(H_i(q)=\exp((\log q)D_i/2)=T_i(q^{-1/2})\). Set

\[
H=H_0(z)H_2(s)H_0(r)H_1(q)H_0(p).
\]

The order is reversed because these factors act by conjugation on the state.
The terminal state condition is equivalent to

\[
HX_0H^{-1}=R'^{-1}X_0R',\qquad [R'H,X_0]=0. \tag{8}
\]

Multiplying the triangular half-factors in (3) gives

\[
H=\frac1{\sqrt{pqrsz}}
\begin{pmatrix}
qs&ps(1-q)\\
zq(s-1)&pz\bigl(r-(s-1)(q-1)\bigr)
\end{pmatrix}.
\]

By (5), \(\sqrt{pqrsz}=qs\). Substituting (6) reduces this exactly to

\[
\boxed{H=\begin{pmatrix}1&-u\\v&1-uv\end{pmatrix}.} \tag{9}
\]

Put \(d=(1-u)(1-v)\), \(N=d(4-d)>0\), and \(K=R'H\).
Then \(\det K=1\), \(\operatorname{tr}K=2-d\), and \(K_{01}=1-uv>0\).
Thus \(K\) is noncentral and elliptic. A traceless matrix commuting with
\(K\) is proportional to \(2K-\operatorname{tr}(K)I\); its determinant is \(N\).
This follows either from the two-by-two characteristic identity or by solving
the commutator entries using \(K_{01}\ne0\). Consequently

\[
X_0=\pm\frac{2K-\operatorname{tr}(K)I}{\sqrt N}. \tag{10}
\]

In the current basis,

\[
Z_0=\begin{pmatrix}1&0\\0&-1\end{pmatrix},\quad
Z_1=\begin{pmatrix}-1&2\\0&1\end{pmatrix},\quad
Z_2=\begin{pmatrix}-1&0\\-2&1\end{pmatrix}.
\]

The margins \(p_i=-\operatorname{tr}(Z_iX_0)\) for the plus sign in (10) are

\[
(p_0,p_1,p_2)=\frac2{\sqrt N}(A,d,B),\qquad
A=(1+u)(1-v),\quad B=(1-u)(1+v). \tag{11}
\]

All are positive. The minus sign makes all negative, so strict star membership
selects the plus sign. No unconstrained initial-state variable remains.

## 4. Exact cost of the asymmetric family

Write each margin as \(2/\sqrt N\) times a raw margin. The invariant becomes

\[
r_0r_1+r_1r_2+r_2r_0=N. \tag{12}
\]

The exact vertex recurrence gives this table:

| Stage | Raw state | Next active raw margin |
| --- | --- | --- |
| Initial | \((A,d,B)\) | \(A\) |
| After 0 with factor \(P(u)\) | \((A,d/u,L_u)\) | \(d/u\) |
| After 1 with factor \(Q(u)\) | \((d,d/u,K_u)\) | \(d\) |
| After 0 with factor \(r\) | \((d,K_v,d/v)\) | \(d/v\) |
| After 2 with factor \(Q(v)\) | \((B,L_v,d/v)\) | \(B\) |
| After 0 with factor \(P(v)\) | \((B,A,d)\) | — |

Here the unlisted coordinates are fixed by (12):

\[
\begin{aligned}
(A+d/u)L_u&=N-Ad/u,&(d+d/u)K_u&=N-d^2/u,\\
(B+d/v)L_v&=N-Bd/v,&(d+d/v)K_v&=N-d^2/v.
\end{aligned} \tag{13}
\]

For example, \((A+d)P(u)-A=d/u\), and
\((A+d/u)/Q(u)-d/u=d\). Moreover \(K_u=4u/(1+u)-d\), so the middle factor
in (6) sends the decreasing coordinate to \(d/v\). The final two steps are
the same identities with \(u,v\) interchanged. This checks the table and
the terminal permutation.

Only necessary consequences of actual admissibility are required here.
Bounding the resulting expression for every pair in (7) is sufficient;
additional intermediate star restrictions could only shrink the set compared.

Let \(\delta=\operatorname{cost}/\sqrt{12}\). With active raw margin \(a\),
growing coordinate \(b\), decreasing coordinate \(c\), and factor \(w\), the
exact arc-cost formula gives

\[
N\delta_{\rm arc}
=\frac a2\bigl((a+b)(w-1)+(a+c)(1-w^{-1})\bigr)
-\frac{a^2}2\log w. \tag{14}
\]

Its algebraic term is \(a((b_{\rm new}-b)+(c-c_{\rm new}))/2\).
Sum these terms over the table and use (13). The weighted \(K\) terms sum to
\(N-(d^2/2)(u^{-1}+v^{-1})\); the weighted \(L\) terms subtract
\(N-(d/2)(A/u+B/v)\). Collecting what remains gives

\[
\begin{aligned}
&AB-\frac d2(A+B)+\frac{3d}2
  \left(\frac{A-d}{u}+\frac{B-d}{v}\right)\\
&\qquad=AB-\frac d2(A+B)+3d(2-u-v)=2d(d+2).
\end{aligned} \tag{15}
\]

The last equality uses \(A-d=2u(1-v)\), \(B-d=2v(1-u)\),
\(AB=d(1+u)(1+v)\), and \(A+B=2(1-uv)\). This supplies the finite
cost calculation without a large polynomial expansion.

The logarithmic coefficients follow from the five active margins. Thus

\[
\begin{aligned}
N\delta={}&2d(d+2)\\
&-\frac12\left(
A^2\log P(u)+\frac{d^2}{u^2}\log Q(u)+d^2\log r
+\frac{d^2}{v^2}\log Q(v)+B^2\log P(v)\right).
\end{aligned} \tag{16}
\]

For \(0<t<1\), define

\[
F(t)=\left(\frac{1+t}{1-t}\right)^2\log\frac{1+t^2}{2t}
+\frac1{t^2}\log\frac{1+t^2}{1-t^2}
+\log\frac{2t}{1-t^2}. \tag{17}
\]

Since \(A/d=(1+u)/(1-u)\), \(B/d=(1+v)/(1-v)\), and
\(r=[2u/(1-u^2)][2v/(1-v^2)]\), (16) becomes

\[
\boxed{\delta(u,v)=
\frac{2(d+2)-(d/2)(F(u)+F(v))}{4-d}.} \tag{18}
\]

## 5. A sharp global logarithmic envelope

The needed scalar estimate is

\[
\boxed{F(t)+2\log(1-t)\le M\qquad(0<t<1),} \tag{19}
\]

with equality only at \(t_*=\sqrt2-1\), where

\[
M=F(t_*)+2\log(1-t_*),\qquad F(t_*)=(3+2\sqrt2)\log2. \tag{20}
\]

Here is a complete proof. Set

\[
h(t)=-\frac{2t\log t}{1-t}-\log(1+t),\qquad 0<t<1.
\]

The function \(x\mapsto h(\sqrt x)\) is strictly concave on \((0,1)\).
Indeed, with \(E=t-1-\log t\ge0\),

\[
h'(t)=\frac{2E}{(1-t)^2}-\frac1{1+t},
\]
\[
t h''(t)-h'(t)
=-\frac2{1-t}
+\frac{2(3t-1)E}{(1-t)^3}
+\frac{1+2t}{(1+t)^2}. \tag{21}
\]

For \(t\le1/3\), the middle term is nonpositive and the other two have
strictly negative sum. For \(t>1/3\), use

\[
E=\int_t^1\frac{1-s}{s}\,ds\le\frac{(1-t)^2}{2t}.
\]

Equation (21) is then at most

\[
-\frac1t+\frac{1+2t}{(1+t)^2}
=\frac{t^2-t-1}{t(1+t)^2}<0.
\]

The second derivative of \(h(\sqrt x)\) at \(x=t^2\) is
\((t h''-h')/(4t^3)\), proving the strict concavity.

For the original parameter \(t\), put

\[
a=\frac{2t}{1+t^2},\qquad b=\frac{1-t^2}{1+t^2}.
\]

Then \(a,b\in(0,1)\), \(a^2+b^2=1\), and logarithm simplification in (17)
gives the exact identity

\[
F(t)+2\log(1-t)=\log2+h(a)+h(b). \tag{22}
\]

For a direct check, use \(P(t)=1/a\), \(Q(t)=1/b\),
\(2t/(1-t^2)=a/b\), and
\(2\log((1-t)/b)=\log2-\log(1+a)-\log(1+b)\).
Jensen's inequality now gives \(h(a)+h(b)\le2h(1/\sqrt2)\), with equality
only when \(a=b\), equivalently \(t=\sqrt2-1\). This proves (19) and its
equality statement.

## 6. Strict comparison with the octagon

Set \(d_*=(2-\sqrt2)^2\). The positive middle duration gives \(d<d_*\).
To see this, write \(x=1-u\), \(y=1-v\). Equation (7) says
\(x+y<1+d/2\), whereas \(x+y\ge2\sqrt d\). Hence \(4\sqrt d<2+d\).
As \(0<\sqrt d<1\), this is equivalent to \(\sqrt d<2-\sqrt2\).

Apply (19) to both parameters. Then \(F(u)+F(v)\le2M-2\log d\), so

\[
\delta(u,v)\ge B(d):=
\frac{2(d+2)-d(M-\log d)}{4-d}. \tag{23}
\]

The function \(B\) is strictly decreasing on \(0<d\le d_*\), because

\[
B'(d)=\frac{4(4-M+\log d)-d}{(4-d)^2}<0. \tag{24}
\]

For an exact sign check, \(M=F(t_*)+\log d_*\), and therefore
\(4-M+\log d\le4-F(t_*)\). Elementary integration gives

\[
\log2=2\int_0^{1/3}\frac{dx}{1-x^2}
>2\int_0^{1/3}(1+x^2)\,dx=\frac{56}{81},\qquad
\sqrt2>\frac75.
\]

Consequently

\[
F(t_*)=(3+2\sqrt2)\log2
>\frac{29}{5}\frac{56}{81}=\frac{1624}{405}>4,
\]

which proves (24). Since \(d<d_*\), the resulting comparison is strict:

\[
\delta(u,v)>B(d_*).
\]

Finally \(d_*(3+2\sqrt2)=2\), so

\[
\boxed{B(d_*)=
\frac{8-4\sqrt2-\log2}{2\sqrt2-1}
=\delta_{\rm oct}.} \tag{25}
\]

This excludes every smaller-cost admissible member of the entire asymmetric
01020 orbit. At the limiting pair \(u=v=\sqrt2-1\), the middle factor is one
and that piece disappears. The remaining four factors are all \(\sqrt2\),
consistent with the four-link octagon equality case. Every positive middle
duration has strictly larger cost.

## 7. A failed shortcut retained

Global concavity of \(x\mapsto F(1-e^{-x})\) would have given a tempting
fixed-\(d\) symmetrization, but it is false. Elementary logarithm expansion gives

\[
F(1-e^{-x})=2+2x+(2x-1)e^{-x}+O(xe^{-2x}),
\]

and expansion of the differentiated logarithms gives

\[
\frac{d^2}{dx^2}F(1-e^{-x})
=(2x-5)e^{-x}+O(xe^{-2x})>0
\]

for sufficiently large \(x\). These expansions come from the convergent
power series in \(e^{-x}\), which may be differentiated termwise there;
the derivative claim is not obtained by differentiating an unspecified
remainder bound.
The successful proof uses the different strictly concave function
\(h(\sqrt x)\) to obtain the sharp global envelope (19), then compares
\(B(d)\). It does not use the false concavity assertion.

## Reproducibility of the exploratory algebra

The retained script
[five_arc_01020.py](../explorations/five_arc_01020.py) specifies the domain
and every factor explicitly. It was run with Python 3.12.14 and SymPy 1.14.0.
Its exact residuals were zero for the tangent endpoint, half-factor
monodromy, determinant normalization, initial margin numerators, final
state twist, active-margin table, and algebraic part of the cost. It also
prints the five logarithmic coefficients from (14).

The script performs no numerical optimization or sampled inequality check.
It is not the proof of the comparison: Sections 2–6 give the finite
identities, the cost cancellation, and the independent logarithmic
inequality with their hypotheses. No kernel validation is claimed.

## Remaining five-arc case

The reverse cyclic word 02102 is not covered by (25). Its endpoint equations
admit a separate exact parameterization, but its cost comparison is not yet
proved in this note. Until that case is resolved, the established result is
the complete classification in Section 1 and the strict comparison for
01020 and all its rebases. No uniform bound on word length, unrestricted
Reinhardt comparison, or global affine equality classification is asserted.

