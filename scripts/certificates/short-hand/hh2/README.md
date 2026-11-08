# Generators of the S2 heavy face signs (prefix `hh2`)

These Python scripts (sympy, fractions) write the Lean modules
`SmoothedOctagon/Exclusion/Mixed/ShortHand/Heavy/S2*.lean` (except the hand-written
`Heavy/S2Face.lean`) that prove the three heavy leaves of gate S2 of the smaller-short hand proof:

| leaf (in `ShortHand/S2.lean`) | proof | modules |
|---|---|---|
| `hs2_outer_sign_large` | `hs2_outer_sign_large_proof` | `S2LargeCertA`, `S2LargeCertB`, `S2Large` |
| `hs2_outer_sign_small` | `hs2_outer_sign_small_proof` | `S2SmallPolyA`, `S2SmallCertA0`, `S2SmallCertA1`, `S2SmallCertB`, `S2SmallShift`, `S2SmallLink{A,B}`, `S2Small` |
| `hs2_central_sign` | `hs2_central_sign_proof` | `S2CenPoly`, `S2CenStage`, `S2CenLink{G,A,D}`, `S2CenL{0..4}a`, `S2CenL{0..4}`, `S2Central` |

Shared: `S2Face` (face value, duration elimination, log majorant, face transport formulas) and
`S2Bern` (positivity of Bernstein forms). Lean re-checks every identity (`ring`,
`linear_combination`, `field_simp`); nothing computed here is trusted.

## The argument

All three signs are about `G(τ) = (w - 1)τ + 1/τ + c + log(τk) + (2 - 7τk/4)(w - 3/4)`
(`hh2_hsF_face`).

* Duration. `G(τ) - G(2) = (τ - 2)A + log(τ/2) - (τ² - 4)/(4τ)`, `A = (1 - 7k/4)(w - 3/4)`.
  Outer faces: `log z ≤ (z - 1/z)/2` gives `G(τ) ≤ max(G₂, G₂ + (T - 2)A)` (`hh2_tau_outer`).
  Central face: `log z ≤ (z - 1/z)/2 - (z - 1)³/(6z²)` gives
  `G(τ) ≤ G₂ + (τ - 2)A - (τ - 2)³/(12τ²)` (`hh2_tau_cubic`); with `τ ≤ 7/2` the right side is
  below `G₂ + ℓᵢ(A)` for the chord `ℓᵢ` of the interval of `A` (breakpoints `0, 1/250, 3/250, 9/196`;
  each chord is checked at its endpoints by a cubic in `τ`).
* Logarithm. `log y ≤ -296/1029 + t - t²/2 + t³/3`, `t = 4y/3 - 1` (Taylor at `3/4`,
  `log(4/3) ≥ 296/1029`), polynomial in `k`.
* Shape. Each resulting rational sign is a polynomial sign on a box: large face `(c, α, x)` on
  `[5/8, 7/8] × [3/2, 12/5] × [13/6, 12/5]` (`c = (β - x)/(α - 1)`); small face `(c, s, x)`,
  `α = (36x + 25)/84 + s`, two `x`-boxes for `H₀`; central face `(t, x, α)`,
  `β = x + ((24x + 51)/128 - t)(α - 1)`, on `[0, 229/1024] × [13/6, 12/5] × [1, 4/3]`.
  Positivity is a nested Bernstein certificate: Bernstein in the first variable with abstract
  coefficients (generic interval lemma), Bernstein in the second with abstract coefficients, and
  univariate Bernstein certificates (with subdivision and degree elevation) in the last variable,
  each checked by one `linear_combination`.
* Clearing denominators. Large outer face: `field_simp; ring` on the face expression. Small outer
  face and central face: two stages (stage 1: the face in abstract atoms `S, D, B, α, u` (and `K`),
  by `field_simp; ring`; stage 2: the expansion of the atom polynomials with `u = U_n/U_d`, by
  `ring`), so that no `field_simp` sees the expanded polynomials.

## Files and run order

* `bern.py` (exact Bernstein arithmetic), `leangen.py` (Lean emitters: generic interval lemmas,
  univariate leaves, nested certificates), `shiftgen.py` (nested definitions and shift identities),
  `common.py` (output directory, module writer), `nest.py` (planner used for design checks).
* Run from this directory:
  `python3 gen_bern.py; python3 gen_large.py; python3 gen_large_link.py; python3 gen_small.py;`
  `python3 gen_small_stage.py; python3 gen_small_link.py; python3 gen_central_mods.py;`
  `python3 gen_central_lines.py; python3 gen_central_main.py` (about two minutes).
* `check_design.py` re-computes the numerical margins quoted in the module docstrings (sampling;
  for orientation only).
