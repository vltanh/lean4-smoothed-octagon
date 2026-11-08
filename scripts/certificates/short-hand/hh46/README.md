# Heavy leaves `hs4_floor_box` and `hs6_B_endpoint`: generators

Generators of the certificate modules in `SmoothedOctagon/Exclusion/Mixed/ShortHand/Heavy/`
(`S4*`, `S6*`). The scripts are not trusted: every identity is checked by `ring`/`field_simp`,
and every Bernstein coefficient by `norm_num`.

```sh
python3 gen_all.py OUTDIR    # writes the generated modules; they must equal the committed ones
```

Requires `sympy`. Generated modules: `S6Bern`, `S6Id135`, `S6Pos135`, `S6Id3`, `S6Pos3`,
`S4Bern`, `S4Surr` (from `S4Surr_head.lean.in`, the numerators of `s4ndefs.py` and
`S4Surr_tail.lean.in`), `S4Id{Phi,Psi}{A,B}`, `S4Pos{Phi,Psi}{A,B}`, `S4Face`, `S4Beta1`.
Hand-written: `S6Link`, `S6`, `S4Closed`, `S4Beta`, `S4Beta2`, `S4`.

## `hs6_B_endpoint` (`S6*`)

`SMALL_SHAPE_COST_EXCLUSION` (20)-(31). In the atoms `b = qB`, `n = qN` (`T = n/b`) and
`u = nu/du`, `𝓑 - b* = hh46S6St/hh46S6Dn` is a formal identity (`S6Link`, no expansion). At
`e = 13/5` and `e = 3` the numerator times `1251703125` is expanded once (`S6Id*`, degree
`(24, 14)` in `(R, d)`), and its tensor Bernstein coefficients on `[1/3, 7/19] × [0, 1/19]` are all
positive (the smallest is the corner value); `S6Pos*` checks them by nested Bernstein (`d` outer,
`R - 1/3` inner). This replaces the notes' concavity in `d` plus endpoint bounds.

## `hs4_floor_box` (`S4*`)

`EXTENDED_CASIMIR_DERIVATIVES` (4)-(31), `EXTENDED_CASIMIR_FLOOR` (9)-(10). Route (the notes use six
derivative signs of degrees up to `(19, 16, 10)`):

1. `S4Closed`: `Φ`, `Ψ` at `q = q_c` in closed form (`ρ(q_c) = 1/S²`).
2. `S4Beta`, `S4Beta2`, `S4Beta1`: at fixed `x, α`, `Φ` and `Ψ` (with `u = ū(x, β)`) decrease in
   `β ∈ [x, 20x/19]`. Exact divided differences in `β` (fixed `u`) and in `u` (fixed `β`; `Φ, Ψ` are
   quadratic in `u`), `log(A₂/A₁) ≥ (β₂ - β₁)/A₂`, the bounds `0 ≤ ū(β₁) - ū(β₂) ≤ (β₂ - β₁)/100`,
   `757/1000 ≤ ū ≤ 19/25`, and four functions of `(x, α, u)`, affine in `u`, bounded by small
   bivariate Bernstein certificates at `u = 757/1000, 19/25` (`S4Beta1`: `k_Φ, k_I, k_II ≥ 1/15`,
   `∂_uΦ ≥ -13/20`). Then `F(β₁) - F(β₂) ≥ (β₂ - β₁)(1/105 - 13/2000)`.
3. Raising `β` to `x(1 + min(5(α - 1)/13, 1/19))` lands on the face `η = 13/5` (A: `(x, δ)`) or
   `δ = 1/19` (B: `(x, α)`).
4. `S4Surr`, `S4Id*`, `S4Pos*`, `S4Face`: on each face, `log y ≤ L₀ + h - h²/2 + h³/3`,
   `h = y/y₀ - 1`, with `y₀` the value at the minimizing corner (`2524608/3353029` on A,
   `103488/134749` on B, inventory R22) and `L₀ ≥ log y₀` from three terms of `2 artanh`. The
   cleared surrogates (degree `(19, 14)` on A, `(19, 8)` on B) have all Bernstein coefficients
   positive on the whole face; no subdivision.
