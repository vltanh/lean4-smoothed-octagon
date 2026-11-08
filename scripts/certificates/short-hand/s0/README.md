# Generators of the heavy S0 face-sign certificates (prefix `hh0`)

These scripts (sympy, exact rationals) wrote the Lean modules
`SmoothedOctagon/Exclusion/Mixed/ShortHand/Heavy/S0*.lean`, which prove the three heavy leaves of
gate S0 of the smaller-short hand proof with their exact skeleton statements:
`hs0_central_tau_two_proof` (`CENTRAL_TAU_TWO_SIGN` (3)), `hs0_central_duration_proof`
(`CENTRAL_DURATION_FACES` (5)) and `hs0_outer_tests_proof` (`OUTER_SCALE_LARGE_RATIO_SIGN` (7)).
Lean re-checks every identity (`field_simp`, `ring`) and every sign (`positivity`); nothing
computed here is trusted.

## The certificate

Each of the six face tests (central face `q = q_c`, `u = û`: `F(2, 5/(2T) - 11/9)`, `F(T, 0)`,
`F(8T/9, -1/9)`; outer face `q = 1/7`, `u = ū`: the same three) is `hsF = -N/Den` with an explicit
polynomial `N(x, α, β)` (120-162 terms, degree at most 10) and `Den > 0`. Positivity of `N`:

1. Level 1: with `b = β - x` and `a' = α - 1`, `N = Σ_k c_k(X, a') b^k` (`X = x - 12/5`), and
   `0 ≤ b ≤ gn/gd` with `gn = x(7x + 1)(α - 1)`, `gd = 4x² + 11x + 1` (the upper order bound).
   Bernstein positivity on `[0, gn/gd]` (`hh0_bern4`, `hh0_bern6`) needs the scaled Bernstein
   coefficients `B_m = Σ_{i ≤ m} C(d - i, m - i) c_i gnⁱ gd^(m - i)` to be positive.
2. Level 2: `B_m` is a polynomial in `a = α - α₀` (`α₀ = 1` central, `α₀ = (22x + 20)/55` outer) on
   `[0, (5x - 8)/12]` (central) or `[0, x - α₀]` (outer); Bernstein positivity again
   (`hh0_bern5`-`hh0_bern8`).
3. Level 3: the resulting Bernstein coefficients are polynomials in `X ≥ 0` with nonnegative
   coefficients and positive constant term (`ring_nf; positivity`).

No subdivision is needed, and the bound `x ≤ 9` is never used. The outer certificates use the
larger strip `x ≤ β` instead of the lower order bound `x + 4x(α - 1)/(5x + 4) ≤ β` (the probe shows
the outer signs hold there, the largest value being `-0.0068` at `x = α = β = 12/5`).

## Files

* `model.py`: exact sympy model of the Lean definitions (`hsF`, `hsUhat`, `hsUbar`, ...).
* `nums.py`: the cleared numerators and denominators (writes `nums.pkl`).
* `probe.py`: numerical probe of the largest value of each test (discovery only).
* `leanpoly.py`: Lean printing of polynomials.
* `bernlemmas.py`: writes `Heavy/S0Bern.lean` (generic Bernstein lemmas, degrees 4-8).
* `gens0.py`: plans the certificates (asserting every level-3 sign) and writes `Heavy/S0<T>.lean`
  for `T ∈ {C2, CT, C8}` and `Heavy/S0<T>Cert.lean`, `Heavy/S0<T>.lean` for `T ∈ {OT, O8, O2}`.
* `mkfaces.py`: writes `Heavy/S0Faces.lean` from the leaf statements in `ShortHand/S0.lean`.

Run, from this directory:

```sh
python3 nums.py
H=../../../../SmoothedOctagon/Exclusion/Mixed/ShortHand/Heavy
python3 bernlemmas.py $H/S0Bern.lean
python3 gens0.py $H C2 CT C8 OT O8 O2
(cd ../../../.. && python3 scripts/certificates/short-hand/s0/mkfaces.py)
```

## Build cost (snapshot check, loaded machine)

| Module | time | memory |
|---|---|---|
| `S0Bern` | 5 s | 1.2 GB |
| `S0C2`, `S0CT`, `S0C8` | 26-33 s each | 3.2 GB |
| `S0OTCert`, `S0O8Cert`, `S0O2Cert` | 33-45 s each | 3.3 GB |
| `S0OT`, `S0O8`, `S0O2` | 44-53 s each | 3.5 GB |
| `S0Faces` | 2 s | 1.5 GB |

Total about 6 CPU-minutes: `hs0_central_tau_two_proof` about 30 s, `hs0_central_duration_proof`
about 65 s, `hs0_outer_tests_proof` about 4.5 min (most of it the kernel check of the level-1
`ring` identities of degree 6 in `b`).
