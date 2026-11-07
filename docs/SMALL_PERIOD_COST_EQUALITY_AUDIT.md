# Independent review of the small-period cost and equality step

Date: 2026-11-07. Internal mathematical review, with supplementary exact
identities. No Lean, Lake, typechecking or CI.

## Conclusion and precise scope

The retained asymmetric four-piece comparison and the mixed five-piece
comparison have the scope needed for the final **minimizer-only**
assembly. Their endpoint equations, physical cost normalization, strict
inequalities and equality data pass the review below. The entirely
reverse five-piece word can be excluded by the already established
normal-PMP reverse-period theorem. Its separate long arbitrary-trajectory
cost calculation is therefore not a required dependency of this assembly.

The resulting conditional statement is:

> An actual global minimizer with a finite positive vertex representation
> of at most five pieces has octagon cost and is the concrete octagon
> trajectory after twisted rebasing and cyclic relabeling. Applied to the
> actual realization of any minimizing disk, this gives affine octagon
> rigidity for that disk.

This review does **not** establish that every minimizer has at most five
pieces. M2 remains open, and the global gates G4 and G5 are not marked
complete by this note. The status in [HANDOFF](HANDOFF.md) is authoritative.

Reviewed sources are the active [vertex-word reduction](VERTEX_WORD_REDUCTION.md),
the retained [four-piece proof](legacy/FOUR_LINK_HAND_PROOF.md),
[mixed five-piece proof and coverage](legacy/FIVE_ARC_PROGRESS.md),
[normality](GLOBAL_NORMALITY.md), [reverse-period exclusion](GLOBAL_REVERSE_PERIOD_EXCLUSION.md),
[equality transport, Section 6](MINIMIZER_WINDOW_AUDIT.md), and
[the conditional final assembly](GLOBAL_COST_EQUALITY_ASSEMBLY.md).
The supplementary checker is
[small_period_cost_equality_certificate.py](../explorations/small_period_cost_equality_certificate.py).

## 1. Coverage, rebasing and the reverse-five simplification

On a fixed control edge, the half-plane equations give `x'=y`. With
`z(t)=integral_0^t 1/y`, the matrix

\[
h(t)=\begin{pmatrix}1&-x(t)\\z(t)&1-z(t)x(t)\end{pmatrix}
\]

satisfies `h'=hX` almost everywhere. Thus the frame is `h(0)^{-1}h(t)`.
The terminal frame equation forces `z(T)=sqrt(3)/2` and
`x(0)=-1/sqrt(3)`, contradicting strict star membership. Cyclic
conjugation gives the same exclusion for every missing control. This
argument applies to measurable edge controls, without any PMP premise.

For a finite vertex representation, a rebase after its first `r` arcs
replaces the word by its suffix followed by the prefix with every label
increased by one modulo three. This is the actual twist
`G(t+T)=G(t)R`, `X(t+T)=R^{-1}X(t)R`. It preserves both endpoints and
the whole-period cost; equal adjacent controls can then be merged.

Every rebase must contain all three labels. Equivalently,

\[
\operatorname{last}(j)>\operatorname{first}(j-1)
\quad(j\bmod3).
\tag{1}
\]

If this failed, a cut after the last `j` and before the first `j-1`
would omit `j` after wrapping. Conversely an omitted label gives just
such a cut. Interior cuts retain the limiting letter sets, so this is
not a restriction to a sampled set of cut times.

The elementary terminal coverage is as follows. The exact checker
independently exhausts the reduced words starting in label zero for
`N=1,...,5`, and verifies the rebase interpretation of (1).

| Positive pieces | Words surviving (1), up to cyclic relabeling |
| --- | --- |
| At most three | None |
| Four | `0120` |
| Five | `01020`, `01201`, `01202`, `01210`, `02012`, `02102`, `02120` |

The five rebases of `01020` account for `01020`, `02120`, `02012`,
`01202`, `01210`. Rebasing `01201` after its first arc gives `12011`,
which merges to the four-piece word `1201`. The remaining word is
`02102`.

For `02102`, every interior switch is reverse. The seam is reverse as
well: the final label 2 is followed by the twisted initial label 1.
The [normality theorem](GLOBAL_NORMALITY.md) has no lower bound on the
number of positive pieces, and its hypotheses hold for the actual
minimizing period. The [reverse-period theorem](GLOBAL_REVERSE_PERIOD_EXCLUSION.md)
also has no lower bound on period length. Its four-arc minimum-margin
needle contradiction applies at a minimum of the finite cyclic margin
sequence. Twisted extension preserves that sequence and the same normal
covector. It therefore excludes the reverse-five minimizer.

This simplification does not assert a cost bound for arbitrary reverse-five
admissible trajectories, which need not carry a PMP lift. It removes
[REVERSE_FIVE_ARC](legacy/REVERSE_FIVE_ARC.md) only from the dependency
chain that classifies actual global minimizers. Its 801-line comparison
need not be re-proved for that purpose. Historical status sentences in
the archived five-piece note do not alter this current scope.

The finite enumeration above supplies terminal coverage once `N<=5` is
known. It is not an enumeration strategy for proving a uniform length
bound.

## 2. Four pieces: arbitrary factors and both endpoints

Use the rational basis and matrices of the four-piece note. The cost is
`delta=C/sqrt(12)`, with density one fourth of the sum of the three
positive margins. On an arc with active margin `c_i`, its physical
duration and factor satisfy `q_i=exp(2t_i/c_i)`. No rescaling of physical
time or of the objective is introduced.

For the surviving word, relabeled `2012`, let the positive factors be
`p,q,r,z>1`. The tangent endpoint equation is

\[
T_0(q)T_1(r)=T_2(1/p)RT_2(1/z).
\]

The right-hand bottom entries are equal. The difference of the left-hand
bottom entries is

\[
\frac{q^2-(q^2-1)r^2}{qr}.
\]

Hence `r^2=q^2/(q^2-1)`. The lower-left entry and the difference of the
two left-column entries then give `(p^2-1)(q^2-1)=1`. Positivity selects
`r=p`, `z=q`. Thus, with `a=1/p`, `b=1/q`,

\[
a,b>0,\qquad a^2+b^2=1,\qquad
(q_1,q_2,q_3,q_4)=(1/a,1/b,1/a,1/b).
\tag{2}
\]

This derives alternating factors from closure; no symmetry assumption
has been imposed on the competitor.

Put `s=a+b`, `N=(s-1)(s+3)` and

\[
M=\begin{pmatrix}a-b&1-2s\\1&b-a\end{pmatrix}.
\]

The half-factor product `H` satisfies `RH=(2I+M)/(s+1)`. The true state
endpoint is therefore `[M,X_0]=0`. The two independent commutator entries
force `X_0=hM`; determinant one and the positive lower-left entry give

\[
X_0=M/\sqrt N.
\tag{3}
\]

Conversely, tangent closure and this state endpoint imply the frame
endpoint: `V(T)=X_0R`, `X(T)=R^{-1}X_0R`, and `g(T)=V(T)X(T)^{-1}=R`.
Thus the initial state is forced by the full endpoint conditions, not
chosen to simplify the cost calculation.

### Cost and the strict asymmetric comparison

Set `A=2(s-1)`, `B=2(1-a+b)`, `C=2(1+a-b)`. The raw margin states are

\[
(A,B,C),(B,A,C),(B,C,A),(A,C,B),(C,A,B),
\]

each divided by `sqrt(N)` to obtain the actual margins. Every entry is
positive. On each arc one margin is constant, one increases and one
decreases, so the endpoint inequalities cover the entire arc.

The active raw margins are `C,B,C,B`. Direct integration gives individual
contributions `C(1-a)-C^2 log(1/a)/8` and
`B(1-b)-B^2 log(1/b)/8` to `N delta`, each used twice. Therefore

\[
\delta(a,b)=
\frac{4s(s-1)+2(1+a)(1-b)\log a+
                   2(1-a)(1+b)\log b}{(s-1)(s+3)}.
\tag{4}
\]

Independent reconstruction of every arc and the complete cost confirms
this normalization. The formula is symmetric in `a,b`; the trajectory
has not been assumed symmetric.

Take `a>b`, write `d=a-b=sqrt(2-s^2)` and `p_0=ab=(s^2-1)/2`. For the
function `f(s)` defined by (4), differentiating gives

\[
f'(s)=\frac2{N^2}\left(H(s)-\frac{s(s-1)^3}{s+1}\right),
\quad
H(s)=(s-1)^2\int_0^\infty
\frac{2t-(s^2+1)}{(t+1)(t+a)(t+b)}\,dt.
\tag{5}
\]

Both the derivative formula and the partial-fraction numerator were
checked exactly. Put `k=1+ab` and
`W(t)=(t+1)^2/((t+a)(t+b))`. Since `0<a,b<1`, `W` is strictly decreasing.
For all `t>=0`,

\[
(2t-2k)W(t)\le(2t-2k)W(k).
\]

The sign reversal for `t<k` is essential and has the displayed direction.
Dividing by `(t+1)^3` and integrating bounds the integral in (5) by
`W(k)(1-k)=-ab W(k)<0`. All integrals converge. Hence `f'(s)<0` on
`1<s<sqrt(2)`; continuity at the symmetric endpoint gives a unique
minimum at `a=b=1/sqrt(2)`.

This proves the lower bound with no endpoint-limit gap. Neither `a=0`
nor `b=0` represents a positive finite factor, and every admissible
asymmetric point has strictly larger cost. The equality data are

\[
\delta_{\rm oct}=\frac{8-4\sqrt2-\log2}{2\sqrt2-1},\qquad
q_i=\sqrt2,\qquad
X_0=\begin{pmatrix}0&-\sqrt{2\sqrt2-1}\\
1/\sqrt{2\sqrt2-1}&0\end{pmatrix}.
\tag{6}
\]

## 3. Mixed five pieces: strictness throughout the positive domain

For `01020`, the tangent equation in the triangular basis forces

\[
(p,q,r,s,z)=
\left(P(u),Q(u),\frac{4uv}{(1-u^2)(1-v^2)},Q(v),P(v)\right),
\]

\[
P(t)=\frac{1+t^2}{2t},\qquad Q(t)=\frac{1+t^2}{1-t^2},
\qquad0<u,v<1.
\tag{7}
\]

For clarity, before parametrization the central tangent product has
upper-left entry `[r^2-(q^2-1)(s^2-1)]/(qrs)`. Its vanishing and the
remaining endpoint entries give
`r^2=(q^2-1)(s^2-1)`, `p=q/sqrt(q^2-1)`,
`z=s/sqrt(s^2-1)`. All roots are positive. Thus (7) covers arbitrary
positive factors satisfying closure.

The condition `r>1` is exactly `u+v+uv>1`. The half-holonomy is
`H=[[1,-u],[v,1-uv]]`. Set `d=(1-u)(1-v)`, `N=d(4-d)`, `K=R'H`.
Then `det K=1`, `tr K=2-d`, and `K_01=1-uv>0`. The trace-zero
centralizer is one-dimensional, so the state endpoint forces

\[
X_0=\frac{2K-\operatorname{tr}(K)I}{\sqrt N}.
\tag{8}
\]

The other determinant-one sign makes all three initial margins negative.
The positive sign gives actual margins `2(A,d,B)/sqrt(N)`, where
`A=(1+u)(1-v)`, `B=(1-u)(1+v)`. There is again no free initial-state
parameter left out of the cost comparison.

The active raw margins are `A,d/u,d,d/v,B`. Because the actual margins
are **twice** the raw ones divided by `sqrt(N)` here, the individual
cost formula differs by a factor four from the raw normalization in
Section 2. The exact checker reconstructs that formula from the common
physical density and confirms the algebraic sum `2d(d+2)` and all
logarithmic coefficients. The result is

\[
\delta(u,v)=\frac{2(d+2)-(d/2)(F(u)+F(v))}{4-d},
\tag{9}
\]

\[
F(t)=\left(\frac{1+t}{1-t}\right)^2\log\frac{1+t^2}{2t}
 +t^{-2}\log\frac{1+t^2}{1-t^2}
 +\log\frac{2t}{1-t^2}.
\]

The scalar comparison applies to the entire domain in (7) with `r>1`.
Even if some algebraically parametrized points failed an intermediate
strict-star condition, this would enlarge the comparison domain and
would not omit any actual trajectory.

### Independent sign audit of the envelope

Define `h(t)=-2t log(t)/(1-t)-log(1+t)` and
`E=t-1-log(t)>=0`. Direct differentiation yields

\[
th''(t)-h'(t)=-\frac2{1-t}
 +\frac{2(3t-1)E}{(1-t)^3}
 +\frac{1+2t}{(1+t)^2}.
\]

For `t<=1/3`, the middle term is nonpositive and the sum of the others
is negative. For `t>1/3`, use
`E=integral_t^1 (1-s)/s ds <= (1-t)^2/(2t)`. The expression is then
at most `(t^2-t-1)/(t(1+t)^2)<0`. Thus `x -> h(sqrt(x))` is strictly
concave on `(0,1)`.

For `alpha=2t/(1+t^2)`, `beta=(1-t^2)/(1+t^2)`, one has
`alpha^2+beta^2=1` and the exact logarithmic identity

\[
F(t)+2\log(1-t)=\log2+h(\alpha)+h(\beta).
\tag{10}
\]

The checker compares the coefficients of both independent logarithms
and verifies the residual product identity; all logarithm arguments are
positive. Strict Jensen concavity proves that (10) has its unique maximum
at `t_*=sqrt(2)-1`. Write

\[
d_*=(2-\sqrt2)^2,\qquad
M=F(t_*)+\log d_*,\qquad F(t_*)=(3+2\sqrt2)\log2.
\]

Summing the envelope gives `F(u)+F(v)<=2M-2 log d`, and hence

\[
\delta(u,v)\ge B(d):=
\frac{2(d+2)-d(M-\log d)}{4-d}.
\tag{11}
\]

The positive middle duration forces `d<d_*`: put `x=1-u`, `y=1-v`;
then `x+y<1+d/2`, whereas `x+y>=2sqrt(d)`. Since `0<sqrt(d)<1`,
this gives `sqrt(d)<2-sqrt(2)`.

Finally,

\[
B'(d)=\frac{4(4-M+\log d)-d}{(4-d)^2}<0
\quad(0<d\le d_*).
\]

Indeed `M-log d>=F(t_*)>4`. An entirely rational strict check is
`sqrt(2)>7/5` and
`log2=2 integral_0^(1/3) 1/(1-x^2) dx >56/81`, giving
`(3+2sqrt(2))log2>(29/5)(56/81)>4`. Thus (11) and `d<d_*` imply

\[
\delta(u,v)>B(d_*)=\delta_{\rm oct}.
\tag{12}
\]

The inequality is strict even if an earlier non-strict envelope has
equality. The only limiting equality is `u=v=t_*`, where the middle
factor is exactly one; deleting that zero-duration piece leaves four
factors `sqrt(2)`. It is not a positive five-piece equality case.

## 4. Equality transport and the active dependency chain

The octagon competitor gives `C_min<=A_oct`. Sections 1--3 then imply
that any actual minimizer having at most five pieces must attain the
four-piece equality in (6). Put `N_0=2sqrt(2)-1`. Its active margins are
`2/sqrt(N_0)`, so each physical duration is
`log(2)/(2sqrt(N_0))`. Undoing the rational basis gives
`Phi(0,sqrt(N_0/3))`. Successive uniqueness of the smooth constant-vertex
state/frame equations identifies the entire concrete octagon trajectory,
including its endpoints. This uses ODE uniqueness at the stated strict
star states; it does not assume that an uncompiled Lean statement is
kernel-validated.

For rigidity, retain the original arbitrary minimizing disk `K`, its
normalization `e`, the rebase cut `s` and cyclic relabeling `C=R^r`.
The classified frame is

\[
\widehat g(t)=C^{-1}G(s)^{-1}G(s+t)C.
\]

Its six contact arcs over one period constitute the entire boundary of
the transformed actual disk. Equality of the state/frame with the
octagon therefore identifies those arcs, and their compact convex
radial hulls give

\[
C^{-1}G(s)^{-1}eK=K_{\rm oct},\qquad
K=e^{-1}G(s)C(K_{\rm oct}).
\tag{13}
\]

The map is invertible and linear; undoing any initial centering makes
it affine. No unrelated equal-cost minimizer is substituted for the
realization of `K`, and cost equality alone is not used to identify an
arbitrary curve. Conversely affine invariance of packing density gives
equality for every affine octagon.

The finite representation used here must come from the **active**
independent chain: [singular clearance](SINGULAR_COST_BUDGET.md), the
[measurable-edge theorem](MEASURABLE_EDGE_PMP_BOUND.md), and the
[three-guard finite count](QUANTITATIVE_REGULAR_SWITCH_BOUND.md).
That representation changes controls only on null sets and leaves the
same actual state, frame, cost and geometric boundary. Section 1 of
the older `MINIMIZER_WINDOW_AUDIT` uses the published finite bang-bang
theorem; that older premise is not needed in the current assembly.
Only its equality transport in Section 6 is used here.

[GLOBAL_COST_EQUALITY_ASSEMBLY](GLOBAL_COST_EQUALITY_ASSEMBLY.md) correctly
retains this current chain and states the remaining M2 condition. Its
passage from minimizer classification to the unrestricted inequality
uses the actual geometric/control comparison: an actual geometric worst
disk realizes a global minimizer against all integral-form admissible
controls. The cost of this minimizer is then a lower bound for every
competitor. The equality argument applies that same comparison to the
realization of each arbitrary worst disk. These are the correct
quantifiers; finite controls are a derived property of the minimizer,
not a restriction on the class being compared.

## 5. Verification and remaining boundary

Run, from the repository root:

```sh
python explorations/small_period_cost_equality_certificate.py
```

The exact checker verifies the finite terminal coverage, generic tangent
matrix entries used for factor elimination, both forced-state products,
each raw-margin update and cost addition, the four-piece derivative and
integral numerator, the five-piece envelope identities, and the equality
normalizations. Its rational circle parametrization is used only for
algebraic identities; the hand inequalities cover the entire indicated
positive domains. It performs no numerical optimization or Lean command.

This review supplies an independently readable terminal comparison and
equality audit. It does not independently re-prove every geometric
existence, compact-domain or maximum-principle input, and it does not
close M2. The final mathematical dependency review must still verify
the completed whole-period case partition and the successful full-domain
certificates used by it before declaring the unrestricted sharp cost
inequality and affine uniqueness proved.
