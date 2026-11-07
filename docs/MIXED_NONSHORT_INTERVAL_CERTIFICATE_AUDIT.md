# Independent audit of the smaller nonshort continuation certificate

Date: 2026-11-07. Mathematical and source review; no Lean, Lake,
typechecking, or CI.

**Status:** the necessary-condition reduction and the inspected interval
caller are accepted at the hand/exact-algebra level. A complete successful
interval cover of **both** next-switch branches is still required. A
prefix run, a numerical search, or the symbolic identities alone does
not exclude this part of M2.

The latest inspected caller is the strengthened v3 snapshot identified
in Sections 8--9. Its closed complementary roots are combined with the
independently reviewed hand corner `epsilon<=1/32`.

The reviewed mathematical interface is
[MIXED_SMALLER_TURN_CONTINUATION](MIXED_SMALLER_TURN_CONTINUATION.md).
The interval arithmetic engine has its separate review in
[MIXED_SMALLER_SHORT_CERTIFICATE_AUDIT](MIXED_SMALLER_SHORT_CERTIFICATE_AUDIT.md)
and specification in [INTERVAL_ARITHMETIC_ENGINE](INTERVAL_ARITHMETIC_ENGINE.md).
This audit concerns its new scalar caller and the coverage of the actual
nonshort branch.

## 1. Actual data, one multiplier, and the two branches

Choose the smaller turn beside a globally smallest reverse centre and
orient it to be outgoing. The actual word begins with margins

\[
p,b,a,c,d,r
\]

and labels `0,1,0,2,0,1`. Set

\[
K=a^2+4,\quad T=a+c,\quad S=a+b,\quad
Q=d^2+4,\quad W=c+d,\quad Z=d+r.
\]

All transports in the caller refer to the same primary multiplier.
The incoming norm at the centre is solved from the actual first forward
root, whose coefficient is strictly negative. No new multiplier is
chosen at the forward arc or at its successor.

The next actual switch gives the two alternatives established in the
continuation note: its transported norm is at least `3/4`, or the actual
reverse turn gives the upper secant bound on `[a,d]`. These alternatives
include the possibility that the next reverse centre equals the global
minimum. They impose no upper bound on the eventual forward-run length.
The caller must therefore be completed once for each branch.

## 2. Base maximal-parameter domain before the final refinements

This section records the original enclosing domain. Section 8 gives the
stronger compact bounds and the exact complementary roots used by the
frozen published caller. The original boxes below are not its final
replay roots.

Define three strictly positive actual parameters

\[
\delta_0=K/(ST)-1,\qquad
\delta_1=(d-a)/T,\qquad
\delta_2=WZ/Q-1.
\]

Choose a largest one, write it as `epsilon`, and write the other two as
`epsilon*l_i`, with `0<=l_i<=1`. In chart j, `l_j=1`. Every actual
point belongs to at least one of the three charts; ties are covered
repeatedly. The independent coordinates are `a,c,epsilon` and the two
free weights. The inverse formulas used by the caller are

\[
S=\frac K{T(1+\delta_0)},\quad b=S-a,\quad
d=a+T\delta_1,\quad W=T(1+\delta_1),\quad
Z=\frac{Q(1+\delta_2)}W,\quad r=Z-d.
\]

The original rational enclosing boxes are

\[
2/15\le a\le17/20,\quad 2/15\le c\le2,
\]

with `0<=epsilon<=56` in chart 0, `0<=epsilon<=15` in charts 1
and 2, and both free weights in `[0,1]`. They follow from the compact
state bound, `a^2<12/17`, `a<=c<=b`, strict star, and the actual turn
inequality `ad<c^2`:

\[
\delta_0\le\frac1{a^2}-\frac34<56,\qquad
\delta_1<\frac ca-1<15,\qquad
\delta_2<\frac cd<\frac ca\le15.
\]

For the last implication, `dr<4` gives
`1+delta_2=W(d+r)/Q<W/d`, so `delta_2<c/d`.
The closed boxes also contain every relevant limiting face.

## 3. Base directed contractors preserve every actual point

These are the first reviewed geometric contractors. The frozen caller's
additional and stronger contractors are reviewed in Section 8.

The base contractions use only necessary geometric inequalities. From
`S>=T` and `ST<=K` it obtains

\[
c\le\sqrt{a^2+4}-a,\qquad
a\le\frac{4-c^2}{2c},\qquad a\le\sqrt{12/17}.
\]

The first bound decreases with a; the second decreases with positive c.
Their upper endpoint evaluations are therefore valid contractions.
The three parameter caps are

\[
\delta_0\le\frac{a^2+4}{(a+c)^2}-1,
\]
\[
\delta_1\le\min\left\{\frac ca-1,
               \frac{4-ac}{c(a+c)}\right\},\qquad
\delta_2\le\frac{c}{a+(a+c)\delta_1}.
\]

The first cap decreases in a and c throughout the initial box: its a
derivative has the sign of `ac-4`, which is negative there. The second
cap is bounded above by evaluating `c/a-1` at the upper c and lower a;
its other expression decreases in both positive variables when its
numerator is nonnegative. If that numerator is negative, the box has no
actual point. The final expression increases in c and decreases in a
and `delta_1`, so its evaluation at upper c and lower a and `delta_1`
is an upper bound.

Each cap is applied to `epsilon*l_i` by dividing only by a strictly
positive lower endpoint. For the maximal coordinate `l_j=1`, it directly
contracts epsilon. The implementation uses upward-rounded bounds for
all these upper caps. Thus no feasible point is discarded by an
inexact quotient or by choosing one particular maximal chart.

## 4. Desingularization and the zero-duration face

The exact algebra checker proves that the upper-norm root residual has
the form

\[
R(U)=\epsilon^2\Phi,\qquad R_u=-\epsilon D_1,
\]

where

\[
D_1=\frac{K^2}{aQW(1+\delta_0)}
\{a(l_0+l_2)+cl_1+a\epsilon l_0l_2
  +T\epsilon l_1l_2(2+\epsilon l_1)\}.
\]

In each closed maximal chart, at least one weight equals one and a,c are
strictly positive. Consequently `D_1>0`, including at epsilon zero.
The actual first-root equation gives

\[
u=U(a/S)+\epsilon\Phi/D_1.
\]

The strict actual upper norm therefore implies `Phi<0`; the caller uses
the weaker closed condition `-Phi>=0`.

The formal polynomial used in Phi has degree at most eight. Its
constant and linear coefficients vanish identically, and its quadratic
coefficient is exactly

\[
P_2=T^3(4-a^2-2ac)[a(l_0+l_2)+cl_1]^2.
\]

The implementation replaces that coefficient by this factorization and
evaluates the remaining coefficients by Horner's rule. It never divides
an interval by epsilon or epsilon squared. All three analytic logarithm
remainders in Phi explicitly have a factor epsilon. The factored
coefficient of the middle remainder was independently verified:

\[
R_v=-\frac{\delta_1 T^2}{aQW}B_v,
\]
\[
B_v=c(4-a^2)+8a+a\delta_1(c^2+4)
 +\delta_2T(\delta_1+2)
    [K+aT\delta_1(\delta_1+2)].
\]

The centered Casimir expression is an exact identity. At epsilon zero,
its value is `gamma^2=3/16` for every shape and every chart weight, which
violates the competitive cap `23/125`. This is the continuous extension
of the solved root and does not supply a spurious free choice of u at a
singular endpoint.

## 5. Two less immediate sign filters

The caller's divided turn expression is

\[
L=\frac12-
\frac{1-c/T+\delta_1}{(1+\delta_1)^2}
-\delta_1 H(\delta_1),\qquad
H(z)=\frac{\log(1+z)-z+z^2/2}{z^3}.
\]

At the actual turn one has the exact identity

\[
v-g_c(d)=\frac cT\delta_1 L.
\]

Because `c/T>0` and the actual `delta_1>0`, the genuine outgoing
switch inequality gives `L>0`. The nonnegative filter in the caller is
therefore necessary, and its continuous value can be retained on the
closed charts.

The diagonal of the transported multiplier at d satisfies

\[
h_d=Qe_d.
\]

This follows from the prefix-frame pairing identity in
[MIXED_GLOBAL_COSTATE_ELLIPTIC, Section 3](MIXED_GLOBAL_COSTATE_ELLIPTIC.md#3-switch-vectors-and-their-quadratic-pairings).
The determinant-triangle argument in
[GLOBAL_STRUCTURE_FORWARD_ACUTE, Sections 1--2](GLOBAL_STRUCTURE_FORWARD_ACUTE.md#1-a-determinant-minimization-on-a-triangle)
is local to a forward arc: it uses its stationarity, the two incident
derivative floors, strict star, and `q>1`. These hypotheses hold at d in
the mixed period. Its application to mixed forward arcs is also stated
explicitly in
[MIXED_GLOBAL_PHASE_DENSITY, Section 1](MIXED_GLOBAL_PHASE_DENSITY.md#1-forward-pairings-are-positive-also-inside-mixed-periods).
If `e_d<=0`, that argument gives `gamma^2>3/16`, contradicting the
competitive cap. Thus `h_d>0`, and the caller's weak diagonal filter is
valid. No all-forward-period assumption is imported at this step.

## 6. Analytic enclosure and rejection logic

The auxiliary function has the integral representation

\[
H(z)=\int_0^1\frac{t^2}{1+zt}\,dt\quad(z\ge0).
\]

Hence H decreases, H' is negative and increases, and H'' is positive and
decreases. The caller evaluates their interval ranges using the
appropriate endpoints. Near zero it uses the positive series in
`eta=z/(1+z)` with a positive geometric tail; away from zero it uses
the exact logarithmic formulas with directed MPFR arithmetic. The
first two derivatives, series coefficients, tail indices, and endpoint
directions were independently checked. No zero-denominator divided
difference occurs at the corner.

Natural interval evaluation and second-order interval Taylor evaluation
are performed on the whole rectangular box. A box is rejected only if
a necessary nonnegative expression has strictly negative upper bound.
Arithmetic domain exceptions cause subdivision; they do not reject a
box. Unresolved boxes, a remaining stack, or arithmetic range failures
prevent a successful result. Midpoint rounding and split-choice doubles
affect the cover's efficiency, not the validity of a rejection.

## 7. Original reviewed snapshot and exact identity replays

The initial caller inspected in this audit was the scratch source
`mixed_nonshort_completion_interval.cpp`, with SHA256

`e6e64e0e6e5fdc530a4f5d04beb5c70a3ffcd9eb0a5d47e9dd0baa05bda662d0`.

Its symbolic dependencies were independently replayed successfully:

- `explorations/mixed_nonshort_completion_continuation_certificate.py`:
  `93b3760b83385ddf9b6b3e5aeeeca041f017815a67a717be7d095f7afb3a8b7e`;
- `explorations/mixed_nonshort_completion_blowup_certificate.py`:
  `6a2dc9d04670f8211e8d5d1cc76557e5ec768ba6065afafe8876b7630ec84d84`.

The replays verified the actual transports, their determinant
preservation, the first-root derivative identities, the boundary and
secant comparisons, the desingularized polynomial and denominator, all
three analytic remainder coefficients, and the entire zero-duration
Casimir identity. These checks support the displayed exact identities;
the domain and sign implications are the hand arguments above.

Before closing the smaller nonshort case, a final repository source
snapshot must be fixed and both complete branch covers must finish with
an empty stack and zero unresolved boxes. Any mathematical changes from
the reviewed snapshot require corresponding review. Until then this
audit certifies the reduction and source logic, not the claimed global
exclusion.

## 8. Strengthened v3 caller: compact constraints and complementary roots

The subsequent complete caller review covered
`mixed_nonshort_completion_interval_v3.cpp`, SHA256

`40fcd0bc53e8b73b1f2a60cf7038a4fe03510c2f43a5c7472a91f71df7dc5581`.

Its additional inspected headers are

- `certified_lp_proposal.hpp`:
  `acc1fd51a44321d7bf34c64a972546905d72ffa48377d7debb38ddfc4608d5c7`;
- `mixed_nonshort_coefficients.hpp`:
  `5b0c5c70a10a058a50a2735282a640333a87def27a8dbf0def5547c46e4a266d`.

The directed MPFR kernel is unchanged from the independently audited
smaller-short certificate. The coefficient header evaluates the exact
polynomial after cancelling the common positive `T^3`. Exact polynomial
division and reconstruction verify that cancellation, and the generated
common-subexpression formulas represent those coefficients. Neither the
division nor a subtraction of its zero coefficients occurs at runtime.

The generic LP helper retains the reviewed verification rule: floating
LP calculations propose weights, every accepted weight is an exact
nonnegative multiple of `2^-20`, and only a new directed Taylor bound
strictly below zero rejects a box. Generalizing the dimension from six
to five changes none of this argument. It cannot turn the LP's own
numerical infeasibility assertion into a proof rejection.

### Additional compact constraints

The same margin normalization gives

\[
p_1=2(1/\sqrt3-x)/y,\qquad
p_2=2(1/\sqrt3+x)/y.
\]

The retained compact height bound `y<=9/2` therefore implies

\[
p_1+p_2\ge8/(9\sqrt3)>1/2.
\]

The final strict comparison squares to `256>243`. Cyclic symmetry of
the same compact domain gives this bound for every pair. The identity
`p0(p1+p2)+p1*p2=4` and positivity then give `p0<8`, and similarly
every margin is less than eight. These facts justify the new residuals
`8-b,8-d,8-r,S-1/2,T-1/2,W-1/2,Z-1/2`.

Every inactive margin is also at least `m=2/15`. At the two forward
switches these are exactly

\[
4-cd-m(c+d)\ge0,\qquad
c-m-(d+m)\delta_2\ge0.
\]

The second formula follows from `(4-dr)/(d+r)>=m`, using
`Z=Q(1+delta2)/W`. It is not an extra bound on a covector component.

The following replacement residuals have positive clearing factors:

\[
K-T^2(1+\delta_0)=(b-c)T(1+\delta_0),
\]
\[
4-a^2-2ac-T^2\delta_1+Q\delta_2=W(r-a),
\]
\[
c-a(1+\delta_1)=(c^2-ad)/T.
\]

The new divided upper-turn residual is necessary because

\[
V_0-v=\frac cT\delta_1
\left[\frac cT-\frac12-
\delta_1\left(\frac{c/T}{1+\delta_1}-H(\delta_1)\right)\right].
\]

The actual `delta1` is positive. At its closed zero face the bracket
becomes `c/T-1/2>=0`, so the retained extension is consistent with the
minimum geometry.

### Chart 2 has a stronger order constraint

When `delta2` is maximal, `q>=W/T`. The exact identity

\[
F_{d/W}(W/T)-\operatorname{Sec}(a,c,d)
=(d-c)\left[\frac1T-
\frac{\log(W/T)}{d-a}\right]
\]

is positive if `d>c`, since `log(W/T)<(d-a)/T`. In that case
`d/W>1/2`, so `F_{d/W}(q)` strictly increases for `q>1`. This
contradicts the actual exterior condition
`v=Sec(a,c,d)>=F_{d/W}(q)`. Thus every actual point of chart 2 has
`d<=c`, including equality in the exterior gap. If `delta1=0`, this
already follows from `d=a<=c`.

Its equivalent cap is

\[
\delta_1\le\frac{c-a}{a+c}<1.
\]

The v3 caller uses this cap and its rearrangements
`c>=a(1+delta1)/(1-delta1)` and
`a<=c(1-delta1)/(1+delta1)`. All evaluated endpoint directions are
correct. A chart-2 box with lower `delta1>=1` has no actual point and
can be rejected before the denominator is used.

### Stronger contractors and root coverage

The positive quadratic root of
`(a+c)^2(1+delta0)<=a^2+4` bounds a. The rationalized formula in the
caller has a strictly positive denominator and is continuous at
`delta0=0`; it is evaluated at the lower c and lower `delta0`, giving
an upper bound. The joint bound

\[
a^2\le\frac4{(2+\delta_1)^2(1+\delta_0)-1}
\]

uses `c>=a(1+delta1)` and the same centre inequality. Its denominator
is at least three on the entire chart domain.

The inactive-margin cap for `delta2` becomes

\[
\delta_2\le\frac{c-m}{a+(a+c)\delta_1+m}.
\]

This increases with c and decreases with a and `delta1`; the endpoint
substitutions in v3 therefore give an upper bound. The analogous
inactive-margin cap for `delta1` is evaluated with the same valid
monotone directions. Its direct a bound and the `d<=8` contraction
were independently checked by rearranging the positive-factor
inequalities.

Three further bounds use natural outward interval enclosures, with no
assumed monotonicity:

\[
\delta_0\ge\frac K{T(a+8)}-1,\qquad
\delta_2\ge\frac{Td+ac-4}Q,\qquad
\delta_2\le\frac{W(d+8)}Q-1.
\]

They follow respectively from `b<=8`, `r>=a`, and `r<=8`.
The lower product contractor divides a positive lower bound only by an
upper positive endpoint and rounds downward. The upper product
contractor divides an upper bound only by a lower positive endpoint
and rounds upward. Empty products are rejected only when their signs
make the relevant positive bound impossible.

Finally `T>=1/2` improves `delta0<=61/4`: if `a<=1/4`, use
`K/T^2-1<=4a^2+15`; if `a>=1/4`, use
`K/T^2-1<=1/a^2-3/4`. Both are at most `61/4`.
The independently reviewed
[small-parameter theorem](MIXED_NONSHORT_SMALL_PARAMETER_EXCLUSION.md)
excludes all `epsilon<=1/32`. The v3 interval roots therefore use
`[1/32,61/4]` in chart 0 and `[1/32,15]` in charts 1 and 2. Together
with that hand corner they retain the entire original actual domain,
including shared boundaries.

Checkpoint serialization uses exact dyadic endpoints and verifies exact
reconstruction. A resumed pending stack alone is correctly labelled as
not being a stand-alone quantified proof. Final closure must retain
either a full run from the stated roots or a verified complete chain of
cover records. No complete v3 replay is claimed by this source audit.

## 9. Frozen published source for the full replays

The final caller is published as
[mixed_nonshort_completion_interval_certificate.cpp](../explorations/mixed_nonshort_completion_interval_certificate.cpp),
with SHA256

`fc15bd27e0c19700297717747fc70209ac3a2f2eacb0f677a11e3e97e056d560`.

Its content was independently compared with the Section 8 scratch
snapshot. The only difference is replacing the scratch-specific engine
include path by the repository-local path. The published
[LP proposal header](../explorations/certified_lp_proposal.hpp) likewise
differs only in that include path and has hash

`6afe296ecd67f0ac3a48caa2460c9bf5bd58f358470a326f5a324879ba891454`.

The published [coefficient header](../explorations/mixed_nonshort_coefficients.hpp)
is byte-identical to the reviewed header, with hash

`5b0c5c70a10a058a50a2735282a640333a87def27a8dbf0def5547c46e4a266d`.

The directed kernel remains unchanged, with hash

`1607b4f02063722506a514598d23d9b032a4aebfd6e74753bc302a7a67e32e76`.

The final blowup identity checker, including the divided upper-turn and
chart-2 identities, has hash

`135d379567edd888e1dea4c6eeb081ae4db39556b26f0d9d3d67263a1d6e3a78`.

It was independently replayed successfully after publication. All ten
reported identity groups passed, including the strengthened compact
constraints. The continuation checker is unchanged from Section 7.

Both full runs start from these published sources and the original three
complementary roots, rather than from an unverified pending-stack file.
Their success is still pending. Publishing these source identifiers
records the audited proof program; it does not assert that its covers
have finished.

## 10. Independent review of parallel cover accounting

The same frozen caller can also complete a recorded chain of finite
prefixes. The proof of this method is given in
[EXACT_COVER_CHAIN](EXACT_COVER_CHAIN.md). Its scheduling and offline
verification programs have been independently reviewed:

| Program | SHA256 |
| --- | --- |
| `mixed_nonshort_completion_cover_chain.py` | `a458da4a7b3f1f0e33a26f00448229aca4e9271c5883a8354f3479618f704e79` |
| `mixed_nonshort_cover_chain_verify.py` | `36d27e66d6c259d4248fa6c5d500f3354e084006145cf7159f197abfad2a458c` |

The coordinator compiles a copy of the four frozen mathematical sources
and uses that unchanged executable throughout. Each fresh branch begins
without a supplied stack, so it uses all three original complementary
roots. Every record of a stopped prefix is copied verbatim, including
its subdivision depth, into exactly one child invocation. Repeated equal
records retain their multiplicity; no numerical deduplication or new
mathematical subdivision is performed by the coordinator.

The independent verifier reconstructs the exact 80-bit outward endpoints
of the initial roots. It strictly parses complete checkpoint records,
normalizes exact zero before interpreting its MPFR exponent sentinel,
and checks containment in the corresponding initial root. For every job
it verifies the actual final log counters, return code, footer, empty
unresolved file, source and executable identities, and the local forest
identity `N=2L+P-R`. The build source argument is bound to the retained
source snapshot; an explicit MPFR include directory is bound to its
recorded header. These bindings were tightened during the independent
review and agree with the actual coordinator records.

Every graph edge is checked in both directions by parent identifier,
frontier ordinal, branch, and the exact bytes of the assigned record.
The verifier rejects missing or duplicate jobs, unassigned frontiers,
cycles, orphan jobs, changed records and unresolved boxes. A complete
graph has one fresh three-root invocation per branch and satisfies
`N=2L-3` independently for each branch. These checks establish complete
record replacement, rather than relying on aggregate counts alone.

The optional archive mode permits the recorded executable and external
MPFR header to be absent after archiving. It does not relax the retained
source, log, checkpoint or graph checks, and it explicitly retains the
arithmetic and execution trust boundary. A resumed child's successful
footer is not accepted outside a complete rooted graph.

The coordinator and verifier source audits are accepted. The live chains
are still pending; this section records no completed nonshort cover and
does not change the M2 status.
