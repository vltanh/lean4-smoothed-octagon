# Analytic refinements for the proof without computer assistance

Date: 2026-11-07 UTC. All estimates in this note have the displayed hand
proofs below. No interval subdivision, coefficient table or execution
result is a premise. These are refinements of necessary conditions; they
do not by themselves replace the completed computer-assisted F and M2
exclusions.

An [independent internal hand review](HAND_PROOF_REFINEMENTS_AUDIT.md)
accepts the inequalities and their actual-period interfaces.

## 1. A sharper competitive Casimir bound

For the same normal physical multiplier as in
[the spectral cost theorem](GLOBAL_SPECTRAL_COST_CASIMIR.md), write
`kappa=sqrt(12)*gamma`. Every competitive complete period satisfies

\[
\boxed{\kappa<\frac{29707}{20000},\qquad
        \gamma^2<\frac{9193}{50000}.}
\tag{1}
\]

The elementary square-root and logarithm estimates in
[the minimum-threshold proof, Section 1](GLOBAL_STRUCTURE_FORWARD_MINIMUM_THRESHOLD.md#1-a-slightly-sharper-rational-casimir-cap)
give

\[
A_{\rm oct}<\frac{649530373}{207775000}
             <\frac{312613}{100000},\qquad
\pi>\frac{6283}{2000}.
\tag{2}
\]

For completeness, the first estimate uses
`sqrt(2)>141421/100000`, `sqrt(3)<173206/100000` and
`log(2)>69314/100000` in the exact expression

\[
A_{\rm oct}=2\sqrt3\,
\frac{8-4\sqrt2-\log2}{2\sqrt2-1}.
\]

The square-root comparisons follow by squaring. The logarithm comparison
follows by integrating five terms of the positive geometric series for
`2*atanh(1/3)`. The stated lower bound for pi follows from four alternating
terms in Machin's identity `pi=16*atan(1/5)-4*atan(1/239)`, as detailed
in the cited hand proof. The second comparison for the octagon cost has
positive difference `5151/831100000`.

The spectral theorem gives `C>pi*(kappa+3/2)/3` for a competitive
noncircular trajectory. Consequently

\[
\kappa<\frac{3(312613/100000)}{6283/2000}-\frac32
       <\frac{29707}{20000}.
\]

The difference in the last comparison is `3481/125660000`. Finally,

\[
\frac{9193}{50000}
-\frac1{12}\left(\frac{29707}{20000}\right)^2
=\frac{22151}{4800000000}>0.
\]

The whole-period endpoint and the same actual primary multiplier are
essential here. This is not a cap on an independently fitted local
costate.

## 2. Every competitive reverse centre satisfies a^2 < 2/3

At any actual reverse-run centre of a competitive finite normal period,
use the notation of
[the reverse-centre scale proof](MIXED_REVERSE_CENTRE_SCALE_BOUND.md):

\[
\rho=\frac{a^2}{a^2+4},\qquad
0<\rho<rt<\frac14,\qquad 0<r,t<\frac12.
\]

The incident norms satisfy `3/4<u<=1-r+r^2` and
`3/4<v<=1-t+t^2`. With

\[
E=1+r+t-\rho+\log\frac{\rho}{rt}
  -\frac{1-u}{r}-\frac{1-v}{t},
\]

the squared Casimir is

\[
\gamma^2=\frac{4uv-E^2}{16(1-\rho)^2}.
\tag{3}
\]

The incident orders, positive reverse factor, norm bounds and exact
identities used here hold at every reverse-run centre by Section 1
of that cited proof. The competitive cap is the conserved cap of the
same complete period. These are all the hypotheses of the argument
below. Thus the conclusion applies both to the global minimum centre
and to the adjacent outer centre of a short bridge; in particular it
gives rho_A<1/7 at that actual outer centre. The
[independent scope audit](HAND_REVERSE_CENTRE_SCALE_SCOPE_AUDIT.md)
checks these inputs and this extension explicitly.

Here is the short reduction to the same one-variable lower bound, with
the new threshold included. Throughout the norm rectangle,

\[
E<-1+2r+2t-rt<\frac32r,\frac32t.
\]

The first comparison uses the monotonicity of
`-rho+log(rho/(rt))` up to `rho=rt`; substitution
of the upper norm bounds then gives the displayed expression. The second
comparison, for example, follows from
`-1+r/2+t(2-r)<0` because `t<1/2`; the other is symmetric.
Thus the numerator in (3) has positive partial derivatives in both
`u` and `v`: for example `4v-2E/r>3-3=0`.
Lowering both norms to `3/4` strictly lowers (3).

At these lower norms put

\[
E_0=1+r+t-\rho+\log\frac{\rho}{rt}
    -\frac1{4r}-\frac1{4t}.
\]

Its two partial derivatives are nonnegative:

\[
\partial_r E_0=\frac{(2r-1)^2}{4r^2},\qquad
\partial_t E_0=\frac{(2t-1)^2}{4t^2}.
\]

Suppose for contradiction that `rho>=1/7`. The bound proved in the
scale note is

\[
E_0\ge1+\rho-\frac1{8\rho}\ge\frac{15}{56}>0.
\tag{4}
\]

To see it directly, the derivative signs allow `r,t` to be lowered
to the boundary `rt=rho`. There `r+t<=1/2+2rho`, as follows by
expanding `(1/2-r)(1/2-t)>=0`, and

\[
E_0=1-\rho+(r+t)\left(1-\frac1{4\rho}\right)
\ge1+\rho-\frac1{8\rho}.
\]

The negative coefficient reverses the direction of the bound for `r+t`.
Raising `r,t` instead to `1/2` raises the positive `E_0`, and hence lowers
the Casimir expression. We obtain

\[
\gamma^2>G(\rho):=
\frac{9/4-B(\rho)^2}{16(1-\rho)^2},\qquad
B(\rho)=1-\rho+\log(4\rho)>0.
\tag{5}
\]

The function `G` is increasing on `[1/7,1/4)`. For an explicit sign proof,
the elementary inequality `log x<2(x-1)/(x+1)` for `0<x<1` gives

\[
0<B(\rho)<\widehat B(\rho)
=\frac{-4\rho^2+11\rho-1}{4\rho+1}.
\]

Differentiating (5), the sign of `G'` is the sign of
`9/4-B^2-B*(1-rho)^2/rho`. This expression decreases with positive `B`,
and direct multiplication gives the short identity

\[
\frac94-\widehat B^2-
\widehat B\frac{(1-\rho)^2}{\rho}
=\frac{(4\rho-1)^2(4\rho^2+\rho+4)}
 {4\rho(4\rho+1)^2}>0.
\tag{6}
\]

It remains to compare the value at `rho=1/7` with (1). Three terms of
the same positive geometric integral give

\[
\log\frac74
>2\left(\frac3{11}+\frac{(3/11)^3}{3}
                    +\frac{(3/11)^5}{5}\right)
=\frac{450606}{805255}>\frac{2448}{4375}.
\]

The last difference is `27402/704598125`. Therefore
`0<B(1/7)<186/625`, and

\[
G(1/7)>
\frac{9/4-(186/625)^2}{16(6/7)^2}
=\frac{18387201}{100000000}
>\frac{9193}{50000}.
\tag{7}
\]

The final difference is `1201/100000000`. Equations (1), (5)--(7)
contradict `rho>=1/7`. Hence

\[
\boxed{\rho<\frac17,\qquad a^2<\frac23.}
\tag{8}
\]

## 3. A quantitative lower bound at a forward successor

For `q>=1` and `0<eta<=1`, define the continuous function

\[
f_\eta(q)=1+\frac{\eta^2}{q}
             -\eta\frac{\log q}{q-1},\qquad
f_\eta(1)=1-\eta+\eta^2.
\]

Then the following bounds require no geometric assumptions:

\[
\boxed{
f_\eta(q)\ge\Psi(\eta):=
\begin{cases}
\displaystyle \frac34+(\eta-\frac12)^2,
     &0<\eta\le\frac12,\\[4pt]
\displaystyle \frac34+
\frac{(\eta-\frac12)^2}{4(4\eta-1)},
     &\frac12\le\eta\le1.
\end{cases}}
\tag{9}
\]

The two definitions agree at `eta=1/2`; the comparison is strict when
`q>1`.

For `eta<=1/2`, convexity of `1/x` gives the trapezoid bound

\[
\frac{\log q}{q-1}\le\frac{q+1}{2q}.
\]

It follows that

\[
f_\eta(q)\ge1-\frac\eta2+
                 \frac{\eta^2-\eta/2}{q}
\ge1-\eta+\eta^2,
\]

because `eta^2-eta/2<=0`. The trapezoid comparison is strict for `q>1`.

For `eta>=1/2`, put `z=(q-1)/(q+1)`. The identity

\[
\log q=2\int_0^z\frac{ds}{1-s^2}
\le2z+\frac{2z^3}{3(1-z^2)}
\]

follows from `1/(1-s^2)=1+s^2/(1-s^2)` and
`1/(1-s^2)<=1/(1-z^2)` in the second integrand. Thus

\[
\frac{\log q}{q-1}
\le\frac{q^2+10q+1}{6q(q+1)}.
\tag{10}
\]

Again this comparison is strict for `q>1`.
Write `k=1/[4(4eta-1)]`. After multiplying the desired lower bound
by `12q(q+1)>0`, (10) reduces it to the nonnegativity of the quadratic

\[
P(q)=3q(q+1)+12\eta^2(q+1)
 -2\eta(q^2+10q+1)
 -12kq(q+1)(\eta-\tfrac12)^2.
\tag{11}
\]

Its leading coefficient is

\[
3-2\eta-\frac{3(\eta-1/2)^2}{4\eta-1}>0.
\]

For instance, the first two terms are at least 1 and the subtracted
term is at most `3/4`. Its discriminant, by expanding the three
coefficients of (11), is

\[
\operatorname{disc}P=
\frac{3(2\eta-1)^3(16\eta-3)
       (96\eta^2-130\eta+25)}{16(4\eta-1)^2}.
\tag{12}
\]

The last quadratic is convex and has values `-16` and `-9` at the
endpoints `eta=1/2` and `eta=1`. It is therefore negative throughout
that interval. For `eta>1/2`, (12) is negative, so the positive-leading
quadratic (11) is positive for every real `q`. At `eta=1/2`, it is
exactly `2(q-1)^2`. This proves (9), including both boundary cases.

## 4. Application to the same actual nonshort successor

Use the actual data `a,c,d,r,v,w,t` of
[the nonshort continuation interface](MIXED_SMALLER_TURN_CONTINUATION.md).
If the next switch after `r` is forward, let `s` be its actual active
margin. The positive forward factor is

\[
q_r=\frac{(d+r)(r+s)}{r^2+4}>1,
\qquad \eta=\frac{r(d+r)}{r^2+4}.
\]

The strict-star inequality `dr<4` gives `0<eta<1`.
The outgoing missing-control inequality at the actual arc `r` is

\[
t\ge F_{r/(r+s)}(q_r)
=1+\frac{\eta^2}{q_r}
       -\eta\frac{\log q_r}{q_r-1}.
\]

Consequently (9) proves the stronger necessary condition

\[
\boxed{t>\Psi(\eta)\ge\frac34.}
\tag{13}
\]

No multiplier or switch is independently selected. The expression
`eta` depends only on the unchanged actual `d,r`, so the comparison
increasing `b` to `b_*` preserves this threshold. In the notation of
[the forward concavity reduction](MIXED_NONSHORT_FORWARD_BOUNDARY_REDUCTION.md),
put

\[
\tau_\Psi=\mathcal T(w_*)-\Psi(\eta),\qquad
w_\Psi=w_*+\tau_\Psi/B.
\]

Since `B>0`, `w_*<w_actual` and (13) hold, one has

\[
\tau_\Psi>0,\qquad
w_*<w_{\rm actual}<w_\Psi\le w_{\rm cap}.
\tag{14}
\]

Concavity of `Gamma` therefore still gives the exhaustive endpoint
alternative, now with the stronger cap from (1):

\[
\boxed{\Gamma(w_*)<\frac{9193}{50000}
\quad\hbox{or}\quad
\Gamma(w_\Psi)<\frac{9193}{50000}.}
\tag{15}
\]

This supplies smaller analytic endpoint domains for further hand work.
It makes no assertion that either endpoint is a physical trajectory,
and does not by itself exclude those domains.
