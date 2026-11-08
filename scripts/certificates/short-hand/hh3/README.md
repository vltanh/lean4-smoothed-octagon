# Generators for the heavy S3 leaves (prefix `hh3`)

These scripts (Python 3, sympy, fractions) write the Lean modules
`SmoothedOctagon/Exclusion/Mixed/ShortHand/Heavy/S3*.lean`, which prove the two heavy leaves of
gate S3 of the smaller-short hand proof:

* `hs3_outer_face_proof` (statement of `hs3_outer_face`, `DISPLACEMENT_OUTER_FACE` (4)-(21));
* `hs3_central_alpha_proof` (statement of `hs3_central_alpha`, `DISPLACEMENT_CENTRAL_FACE` §2).

Lean re-checks every identity (`ring`, `field_simp`, `linear_combination`); nothing computed here is
trusted. The only skeleton leaves used are the stable `hs3_log_maj` and `hs3_central_endpoint`.

## Files

* `hh3_common.py`: polynomial printing (expanded and Horner forms) and the certificate finders.
  A bivariate polynomial `P(h, v)` on a box `[0, H] × [0, V]` is written as an explicit nonnegative
  combination of facts plus a positive constant, checked by `linear_combination`:
  * kind `c`: all adverse monomials bounded at the corner (`h^r v^l ≤ H^r V^l`);
  * kind `a`: adverse monomials bounded at `h = H`, exact in `v` (all resulting `v`-coefficients
    nonnegative);
  * kind `bv`: Bernstein form in `v` for each power of `h`, adverse Bernstein coefficients bounded at
    `h = H`.
* `hh3_outer.py`: `S3OuterA{0,1}.lean` (clearing, shift `β = U - W y`, Bernstein coefficients in `y`)
  and `S3OuterB{0,1}{a,b,c,d}.lean` (each Bernstein coefficient expanded in `(h, v)` and certified).
* `hh3_outer_assembly.py`: `S3Outer.lean`.
* `hh3_central_compute.py`, `hh3_central.py`: `S3CentralA{0,1}.lean` (cleared test at frozen incoming
  norm, logarithmic derivatives, cleared α-derivative `P_i`, incoming-norm slope) and
  `S3CentralB{0,1}.lean` (certificates at `c = 3/4`, `c = 4/5`, slope numerator).
* `hh3_central_assembly.py`: `S3Central.lean`.

`S3Base.lean` (Horner polynomials and their derivative, Bernstein lemmas of degree 5 and 6 with
abstract coefficients, the `u`-affinity of `hs3Fn`) is written by hand.

No declaration raises `maxHeartbeats`; the generated declarations set `maxRecDepth 20000` (elaboration
of long sums).

## Run

From this directory (`HH3_CACHE` is where the pickled computations are kept, default `/tmp`):

```sh
python3 hh3_outer.py --fresh && python3 hh3_outer_assembly.py
python3 hh3_central.py --fresh && python3 hh3_central_assembly.py
```

The outer computation takes about 30 s, the central one about 40 s.

## Routes (differences from the notes)

* Outer face: the note expands `N_i = -𝒟_i F̄_i` in `(h, v, t)` (1173 and 795 terms) and then takes
  Bernstein coefficients in `t`. Here the cleared numerator is kept in the atoms `(x, α, β)`
  (205 and 166 terms), `β = U - W y` is substituted by a generic shift identity, Bernstein positivity
  in `y` is applied with abstract coefficients, and each of the 13 Bernstein coefficients (92 / 76
  terms in `(x, α)`) is expanded in `(h, v)` separately. The certificates are the same signs as the
  note's (14)-(21), proved by explicit nonnegative combinations.
* Central face: the note differentiates `F_i(x, α, b(x, α), ū(x, b(x, α)))` (numerators of 274 and 222
  terms including the `u_b` term). Here `u` is first raised to the endpoint value
  `u₀ = ū(x, 20x/19)` (ū decreases along the path; the test increases with `u`, slope numerators of
  66 / 56 terms), so the α-derivative at frozen `u₀` has cleared numerator `P_i(x, α, c)`
  (286 / 222 terms, affine in `c`), certified at `c = 3/4` and `c = 4/5` by the corner bound.
