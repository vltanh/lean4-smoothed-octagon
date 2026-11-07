# Independent audit of the sharper angle and mixed-density bound

Date: 2026-11-07 UTC. Independent internal hand review of
[MIXED_GLOBAL_REVERSE_ANGLE_DENSITY](MIXED_GLOBAL_REVERSE_ANGLE_DENSITY.md).
No Lean, Lake, typechecking, or CI was run.

## Result

The proof passes review. Every actual competitive reverse centre in
the stated normal geometric domain has `cos(phi)<1/4`, hence an
unsigned angle greater than `5pi/12`. With `m` reverse centres and
`E` forward same-sign arcs, the actual winding then gives
`m<=2E+3`. The previously proved cost-index bound independently gives
`m<=E+8`. Neither inequality bounds `E` or closes M2.

## Reuse of the fixed-angle comparison

The comparison in MIXED_GLOBAL_SHORT_RUN_ANGLE_EXCLUSION was presented
under a contradiction hypothesis `c>=3/10`. Its derivative signs,
implicit continuation, and boundary reductions use only `0<c<1/2`.
In particular, positivity of the scalar derivative numerator follows
from the domain inequalities and the positive-cosine equation; no
lower constant `3/10` enters. That constant is first used to select
the old rational symmetric cutoff. Thus the same proved comparison
applies to the new contradiction range `1/4<=c<1/2`.

The source theorem also proves `cos(phi)<1/2` before this comparison,
and nonpositive cosines need no comparison at all. These alternatives
cover every reverse centre without a missing angle branch.

## Exact logarithm and Casimir separation

At `rho=5/32`, the lower bound
`log(5/8)>-3/5` makes `B(rho)` strictly positive. The integral identity
for the logarithm and `1/(1-s^2)>1+s^2` give

\[
\log(5/8)<-1032/2197<-15/32.
\]

The last rational difference is `69/(32*2197)>0` in the required
direction. Therefore `0<B(5/32)<3/8`. Since `B` is strictly
increasing, the symmetric point for `c>=1/4` lies strictly to its
right. The already checked monotonicity of the symmetric squared
Casimir gives the lower bound

\[
\gamma^2>\frac{9/4-(3/8)^2}{16(27/32)^2}
=\frac5{27}=\frac{98000}{529200}
>\frac{97969}{529200}.
\]

The final strict gap is exactly `31/529200`. This contradicts the
same actual complete-period costate cap, with physical normalization
`kappa=sqrt(12) gamma`. No numerical cosine evaluation or optimization
is an input. The comparison with 75 degrees follows by squaring
positive quantities in `sqrt(6)>1+sqrt(2)` and then using the strict
monotonicity of cosine on `(0,pi)`.

## Winding, counts, and strictness

After collapse and the reverse sign gauge, the cycle contains exactly
`E` forward angles and `m` reverse angles. Its total is
`n*pi`, with `n=(E+2m-1)/3`, including the actual twisted seam.
Each reverse angle becomes `pi-phi`; each forward angle remains
`theta` in `(0,pi/2)` by the localized acuteness theorem. Rearranging
this identity gives exactly

\[
\sum_{++}(\pi/3-\theta)+\sum_{--}(\phi-\pi/3)=\pi/3.
\]

There is at least one reverse centre in a mixed period, so the strict
reverse lower bound alone already makes the summed comparison strict.
The forward bounds are strict as well when forward same-sign arcs
are present. Consequently `m<2E+4`, and integrality gives
`m<=2E+3`. The independent bound `2m<=P+8`, with `P=m+E`, is
exactly `m<=E+8`. The combined minimum in the statement is correct.

## Whole-mixed lower Casimir bound

The additional bound `gamma^2>27/256` also passes review. Since
`m>=1`, the actual average gauged angle is at least `pi/3`.
Every gauged angle is below `2pi/3`, using forward acuteness and
the reverse-angle bound. A selected angle at least the average
therefore has sine at least `sqrt(3)/2`. The exact metric Wronskian
identity, `K_i>4`, and both adjacent norms at least `3/32` give
the strict bound `gamma>3*sqrt(3)/16`. Multiplying by `sqrt(12)`
gives `kappa>9/8`. The selection of this angle uses the whole
geometric period and is unavailable on an arbitrary local window.

The supplementary checker passed all 13 exact checks. The domain,
comparison continuation, actual covector normalization, and geometric
winding are hand arguments reviewed above. This is internal review,
not external peer review or kernel validation.
