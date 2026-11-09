module

public import SmoothedOctagon.Exclusion.Mixed.Nonshort.Forward.LowRatio.UnitShape.Coefficients

/-!
# Case M2, forward successor: the low-ratio unit-shape sign

The sign of the low-ratio combined residual at the unit shape `k = 1`, at the effective norm `v̂`
and with `log q ↦ L₊`, used in `nsf_lowRatio_core`.

The cleared residual `48(q + 1)WR · nsfComb 6 0 t x 1 q v̂ L₊ 0` is the polynomial circuit
`𝒫 = 48(q + 1)WR 𝒯 + 4𝒰𝒱 + 𝒦` (`nlr_link`). With `h = 1 - 2t`,
`j = 2t + x - 1`, `y = q - 1`, `𝒫 = ∑ᵢ C̃ᵢ(h, y) jⁱ` (`nlr_collect`), which is positive by
`nlr_sum_pos` (`Nonshort/Forward/LowRatio/UnitShape/Coefficients`).

The exact collection identity `𝒫 = ∑ C̃ᵢ jⁱ` is checked one power of `y`
at a time (`nlr_coef0`, …, `nlr_coef7`: identities in `(h, j)` with at most 86
monomials and degree at most 12), after expanding the circuit factors `𝒯`, `𝒰`, `𝒱` in `y`
(`nlr_T_y`, `nlr_U_y`, `nlr_V_y`: at most 195 monomials); no identity in three variables beyond
these factor expansions is expanded.

## Main API

* `nlrCU`, `nlrCV`, `nlrCK`, `nlrCP`: the circuit; `nlr_link`; `nlr_collect`.
* `nlr_unit_pos`: **the unit-shape residual at `v̂`, `L₊` is positive.**
-/

@[expose] public section

namespace SmoothedOctagon

/-! ### The circuit of the unit-shape residual -/

/-- The circuit factor `𝒰`, a quartic in `q`. -/
noncomputable def nlrCU (t x q : ℝ) : ℝ :=
  t * (t + x) * (x + 1) ^ (4 : ℕ) - t * (x + 1) ^ (3 : ℕ) * (t + x ^ (2 : ℕ) + 2 * x) * q + (x + 1) ^ (2 : ℕ) * (-2 * t ^ (2 : ℕ) * x ^ (2 : ℕ) + 10 * t ^ (2 : ℕ) * x + 5 * t * x ^ (3 : ℕ) + 17 * t * x ^ (2 : ℕ) - 7 * t * x - t + 6 * x) * q ^ (2 : ℕ) - (x + 1) * (-2 * t ^ (2 : ℕ) * x ^ (2 : ℕ) - 4 * t ^ (2 : ℕ) * x + 5 * t * x ^ (4 : ℕ) + 20 * t * x ^ (3 : ℕ) + 20 * t * x ^ (2 : ℕ) - t + 6 * x ^ (2 : ℕ) + 12 * x) * q ^ (3 : ℕ) + t * x * (t - 1) * (-2 * t + x ^ (3 : ℕ) + x ^ (2 : ℕ) - 3 * x - 1) * q ^ (4 : ℕ)

/-- `𝒱 = 48(q + 1)RW² v̂`. -/
noncomputable def nlrCV (t x q : ℝ) : ℝ :=
  (q + 1) * (4 + 3 * (q + 2 * t + x - 1)) * (12 * t ^ (2 : ℕ) * x ^ (3 : ℕ) + 132 * t ^ (2 : ℕ) * x ^ (2 : ℕ) + 300 * t ^ (2 : ℕ) * x + 180 * t ^ (2 : ℕ) + 19 * t * x ^ (3 : ℕ) - 12 * t * x ^ (2 : ℕ) - 210 * t * x - 180 * t + 12 * x ^ (4 : ℕ) + 113 * x ^ (3 : ℕ) + 312 * x ^ (2 : ℕ) + 390 * x + 180) - 6 * (x ^ (2 : ℕ) + 10 * x + 15) * (q + 2 * t + x - 1) * ((1 + x) * (-t + 5 * x + 6) + 2 * (3 * t ^ (2 : ℕ) + t * x - 5 * t + x ^ (2 : ℕ) + x + 3) * q + (t + x) * (6 * t + 5 * x - 1) * q ^ (2 : ℕ))

/-- `WR = (1 + x)(x² + 10x + 15)`. -/
noncomputable def nlrWRx (x : ℝ) : ℝ := (1 + x) * (x ^ (2 : ℕ) + 10 * x + 15)

/-- `-32 t B p W² R` with `B = 1 + 2tx + x²`. -/
noncomputable def nlrGtx (t x : ℝ) : ℝ :=
  -32 * t * (1 + 2 * t * x + x ^ (2 : ℕ)) * (t + x) * (1 + x) ^ (2 : ℕ) * (x ^ (2 : ℕ) + 10 * x + 15)

/-- `7W²`. -/
noncomputable def nlrSevx (x : ℝ) : ℝ := 7 * (1 + x) ^ (2 : ℕ)

/-- `J = t + x(x + 2)`. -/
noncomputable def nlrJtx (t x : ℝ) : ℝ := t + x * (x + 2)

/-- `𝒦 = -32tBpW²R Z(q)(7W² - Jq²)`, `Z(q) = q(q - 1)(q² + 10q + 1)`. -/
noncomputable def nlrCK (t x q : ℝ) : ℝ :=
  nlrGtx t x * (q * (q - 1) * (q ^ (2 : ℕ) + 10 * q + 1)) * (nlrSevx x - nlrJtx t x * q ^ (2 : ℕ))

/-- **The polynomial circuit** `𝒫 = 48(q + 1)WR 𝒯 + 4𝒰𝒱 + 𝒦`, with
`𝒯 = nsfComb 6 0 t x 1 q 0 0 0`. -/
noncomputable def nlrCP (t x q : ℝ) : ℝ :=
  48 * (q + 1) * nlrWRx x * nsfComb 6 0 t x 1 q 0 0 0 + 4 * nlrCU t x q * nlrCV t x q + nlrCK t x q

/-- **The link**: the cleared unit-shape residual at
`v = v̂`, `log q = L₊` is the circuit `𝒫`. -/
theorem nlr_link (t x q : ℝ) (hq : 0 < q) (hx : 0 < x) :
    48 * (q + 1) * nlrWRx x * nsfComb 6 0 t x 1 q
        (nsfVG t x + 3 / 4 * (q + 2 * t + x - 1) * (nsfVG t x - nsrFl t x q)) (nsrLp q) 0 =
      nlrCP t x q := by
  have hW : (1 + x) ≠ 0 := by linarith
  have hR : x ^ (2 : ℕ) + 10 * x + 15 ≠ 0 := by positivity
  have hq1 : q + 1 ≠ 0 := by linarith
  have hCv : nsfCv 6 0 t x 1 q = 4 * (1 + x) * nlrCU t x q := by
    unfold nsfCv nsrNv nsfTPv nlrCU; ring
  have hv : nsfVG t x + 3 / 4 * (q + 2 * t + x - 1) * (nsfVG t x - nsrFl t x q) =
      nlrCV t x q / (48 * (q + 1) * (x ^ (2 : ℕ) + 10 * x + 15) * (1 + x) ^ (2 : ℕ)) := by
    unfold nsfVG nsrFl nlrCV; field_simp; ring
  have h1 : 48 * (q + 1) * nlrWRx x * (nlrCV t x q / (48 * (q + 1) * (x ^ (2 : ℕ) + 10 * x + 15) * (1 + x) ^ (2 : ℕ))
      * (4 * (1 + x) * nlrCU t x q)) = 4 * nlrCU t x q * nlrCV t x q := by
    unfold nlrWRx; field_simp
  have h2 : 48 * (q + 1) * nlrWRx x * (nsrLp q * nsfCL 6 t x 1 q) = nlrCK t x q := by
    unfold nlrWRx nsrLp nsfCL nsrNL nlrCK nlrGtx nlrSevx nlrJtx; field_simp; ring
  rw [nsf_comb_dec, hCv, hv]
  unfold nlrCP
  linear_combination h1 + h2

/-! ### The collection identity, one power of `y` at a time -/

/-- The coefficient of `y^0` in `𝒯(t, x, q)` at `t = (1 - h)/2`, `x = h + j`, `q = 1 + y`. -/
noncomputable def nlrYT0 (h j : ℝ) : ℝ :=
  (75 / 4) * j + (75 / 4) * h + (183 / 4) * j ^ (2 : ℕ) + (405 / 4) * h * j + (111 / 2) * h ^ (2 : ℕ) + 36 * j ^ (3 : ℕ) + (247 / 2) * h * j ^ (2 : ℕ) + (271 / 2) * h ^ (2 : ℕ) * j + 48 * h ^ (3 : ℕ) + 9 * j ^ (4 : ℕ) + 39 * h * j ^ (3 : ℕ) + 47 * h ^ (2 : ℕ) * j ^ (2 : ℕ) + (31 / 2) * h ^ (3 : ℕ) * j - (3 / 2) * h ^ (4 : ℕ) - 3 * h * j ^ (4 : ℕ) - 33 * h ^ (2 : ℕ) * j ^ (3 : ℕ) - (145 / 2) * h ^ (3 : ℕ) * j ^ (2 : ℕ) - (245 / 4) * h ^ (4 : ℕ) * j - (75 / 4) * h ^ (5 : ℕ) - 9 * h ^ (2 : ℕ) * j ^ (4 : ℕ) - 27 * h ^ (3 : ℕ) * j ^ (3 : ℕ) - (131 / 4) * h ^ (4 : ℕ) * j ^ (2 : ℕ) - (83 / 4) * h ^ (5 : ℕ) * j - 6 * h ^ (6 : ℕ) + 3 * h ^ (3 : ℕ) * j ^ (4 : ℕ) + 9 * h ^ (4 : ℕ) * j ^ (3 : ℕ) + 9 * h ^ (5 : ℕ) * j ^ (2 : ℕ) + 3 * h ^ (6 : ℕ) * j

/-- The coefficient of `y^1` in `𝒯(t, x, q)` at `t = (1 - h)/2`, `x = h + j`, `q = 1 + y`. -/
noncomputable def nlrYT1 (h j : ℝ) : ℝ :=
  (23 / 4) + 107 * j + (189 / 2) * h + 295 * j ^ (2 : ℕ) + 550 * h * j + 261 * h ^ (2 : ℕ) + (709 / 2) * j ^ (3 : ℕ) + (1821 / 2) * h * j ^ (2 : ℕ) + (1601 / 2) * h ^ (2 : ℕ) * j + 245 * h ^ (3 : ℕ) + 245 * j ^ (4 : ℕ) + 652 * h * j ^ (3 : ℕ) + 597 * h ^ (2 : ℕ) * j ^ (2 : ℕ) + 211 * h ^ (3 : ℕ) * j + (85 / 4) * h ^ (4 : ℕ) + 108 * j ^ (5 : ℕ) + 217 * h * j ^ (4 : ℕ) - 57 * h ^ (2 : ℕ) * j ^ (3 : ℕ) - 420 * h ^ (3 : ℕ) * j ^ (2 : ℕ) - 347 * h ^ (4 : ℕ) * j - 93 * h ^ (5 : ℕ) + 24 * j ^ (6 : ℕ) - 245 * h ^ (2 : ℕ) * j ^ (4 : ℕ) - 532 * h ^ (3 : ℕ) * j ^ (3 : ℕ) - 496 * h ^ (4 : ℕ) * j ^ (2 : ℕ) - 233 * h ^ (5 : ℕ) * j - 48 * h ^ (6 : ℕ) - 24 * h * j ^ (6 : ℕ) - 108 * h ^ (2 : ℕ) * j ^ (5 : ℕ) - 193 * h ^ (3 : ℕ) * j ^ (4 : ℕ) - (355 / 2) * h ^ (4 : ℕ) * j ^ (3 : ℕ) - (189 / 2) * h ^ (5 : ℕ) * j ^ (2 : ℕ) - (65 / 2) * h ^ (6 : ℕ) * j - (13 / 2) * h ^ (7 : ℕ)

/-- The coefficient of `y^2` in `𝒯(t, x, q)` at `t = (1 - h)/2`, `x = h + j`, `q = 1 + y`. -/
noncomputable def nlrYT2 (h j : ℝ) : ℝ :=
  (23 / 4) + 113 * j + (207 / 2) * h + (1271 / 4) * j ^ (2 : ℕ) + (1253 / 2) * h * j + (1227 / 4) * h ^ (2 : ℕ) + 386 * j ^ (3 : ℕ) + 1072 * h * j ^ (2 : ℕ) + (2017 / 2) * h ^ (2 : ℕ) * j + 328 * h ^ (3 : ℕ) + (537 / 2) * j ^ (4 : ℕ) + (1565 / 2) * h * j ^ (3 : ℕ) + 843 * h ^ (2 : ℕ) * j ^ (2 : ℕ) + 411 * h ^ (3 : ℕ) * j + (329 / 4) * h ^ (4 : ℕ) + 120 * j ^ (5 : ℕ) + (511 / 2) * h * j ^ (4 : ℕ) + (21 / 2) * h ^ (2 : ℕ) * j ^ (3 : ℕ) - (695 / 2) * h ^ (3 : ℕ) * j ^ (2 : ℕ) - 308 * h ^ (4 : ℕ) * j - (171 / 2) * h ^ (5 : ℕ) + 28 * j ^ (6 : ℕ) - (537 / 2) * h ^ (2 : ℕ) * j ^ (4 : ℕ) - (1157 / 2) * h ^ (3 : ℕ) * j ^ (3 : ℕ) - (2195 / 4) * h ^ (4 : ℕ) * j ^ (2 : ℕ) - (539 / 2) * h ^ (5 : ℕ) * j - (235 / 4) * h ^ (6 : ℕ) - 28 * h * j ^ (6 : ℕ) - 120 * h ^ (2 : ℕ) * j ^ (5 : ℕ) - (415 / 2) * h ^ (3 : ℕ) * j ^ (4 : ℕ) - (385 / 2) * h ^ (4 : ℕ) * j ^ (3 : ℕ) - (225 / 2) * h ^ (5 : ℕ) * j ^ (2 : ℕ) - (91 / 2) * h ^ (6 : ℕ) * j - 10 * h ^ (7 : ℕ)

/-- The coefficient of `y^3` in `𝒯(t, x, q)` at `t = (1 - h)/2`, `x = h + j`, `q = 1 + y`. -/
noncomputable def nlrYT3 (h j : ℝ) : ℝ :=
  -(7 / 4) + (19 / 2) * j + 18 * h + (97 / 4) * j ^ (2 : ℕ) + 125 * h * j + (347 / 4) * h ^ (2 : ℕ) - j ^ (3 : ℕ) + 177 * h * j ^ (2 : ℕ) + (603 / 2) * h ^ (2 : ℕ) * j + 131 * h ^ (3 : ℕ) - (61 / 2) * j ^ (4 : ℕ) + (115 / 2) * h * j ^ (3 : ℕ) + 261 * h ^ (2 : ℕ) * j ^ (2 : ℕ) + 248 * h ^ (3 : ℕ) * j + (299 / 4) * h ^ (4 : ℕ) - 22 * j ^ (5 : ℕ) - (41 / 2) * h * j ^ (4 : ℕ) + (119 / 2) * h ^ (2 : ℕ) * j ^ (3 : ℕ) + (187 / 2) * h ^ (3 : ℕ) * j ^ (2 : ℕ) + (69 / 2) * h ^ (4 : ℕ) * j - h ^ (5 : ℕ) - 4 * j ^ (6 : ℕ) + (61 / 2) * h ^ (2 : ℕ) * j ^ (4 : ℕ) + (77 / 2) * h ^ (3 : ℕ) * j ^ (3 : ℕ) - (37 / 4) * h ^ (4 : ℕ) * j ^ (2 : ℕ) - 37 * h ^ (5 : ℕ) * j - (63 / 4) * h ^ (6 : ℕ) + 4 * h * j ^ (6 : ℕ) + 22 * h ^ (2 : ℕ) * j ^ (5 : ℕ) + (89 / 2) * h ^ (3 : ℕ) * j ^ (4 : ℕ) + (75 / 2) * h ^ (4 : ℕ) * j ^ (3 : ℕ) + (11 / 2) * h ^ (5 : ℕ) * j ^ (2 : ℕ) - (19 / 2) * h ^ (6 : ℕ) * j - 4 * h ^ (7 : ℕ)

/-- The coefficient of `y^4` in `𝒯(t, x, q)` at `t = (1 - h)/2`, `x = h + j`, `q = 1 + y`. -/
noncomputable def nlrYT4 (h j : ℝ) : ℝ :=
  -(11 / 4) - 22 * j - (29 / 2) * h - (125 / 2) * j ^ (2 : ℕ) - (311 / 4) * h * j - (89 / 4) * h ^ (2 : ℕ) - (191 / 2) * j ^ (3 : ℕ) - 160 * h * j ^ (2 : ℕ) - (281 / 4) * h ^ (2 : ℕ) * j - (13 / 4) * h ^ (3 : ℕ) - (171 / 2) * j ^ (4 : ℕ) - (327 / 2) * h * j ^ (3 : ℕ) - 63 * h ^ (2 : ℕ) * j ^ (2 : ℕ) + (71 / 2) * h ^ (3 : ℕ) * j + (81 / 4) * h ^ (4 : ℕ) - (177 / 4) * j ^ (5 : ℕ) - (311 / 4) * h * j ^ (4 : ℕ) + (55 / 2) * h ^ (2 : ℕ) * j ^ (3 : ℕ) + 130 * h ^ (3 : ℕ) * j ^ (2 : ℕ) + (173 / 2) * h ^ (4 : ℕ) * j + (35 / 2) * h ^ (5 : ℕ) - 10 * j ^ (6 : ℕ) + (171 / 2) * h ^ (2 : ℕ) * j ^ (4 : ℕ) + (327 / 2) * h ^ (3 : ℕ) * j ^ (3 : ℕ) + (251 / 2) * h ^ (4 : ℕ) * j ^ (2 : ℕ) + (169 / 4) * h ^ (5 : ℕ) * j + (19 / 4) * h ^ (6 : ℕ) + 10 * h * j ^ (6 : ℕ) + (177 / 4) * h ^ (2 : ℕ) * j ^ (5 : ℕ) + (311 / 4) * h ^ (3 : ℕ) * j ^ (4 : ℕ) + 68 * h ^ (4 : ℕ) * j ^ (3 : ℕ) + 30 * h ^ (5 : ℕ) * j ^ (2 : ℕ) + (23 / 4) * h ^ (6 : ℕ) * j + (1 / 4) * h ^ (7 : ℕ)

/-- The coefficient of `y^5` in `𝒯(t, x, q)` at `t = (1 - h)/2`, `x = h + j`, `q = 1 + y`. -/
noncomputable def nlrYT5 (h j : ℝ) : ℝ :=
  -(1 / 4) - (3 / 2) * j - h - (13 / 4) * j ^ (2 : ℕ) - 4 * h * j - h ^ (2 : ℕ) - (9 / 2) * j ^ (3 : ℕ) - 7 * h * j ^ (2 : ℕ) - 2 * h ^ (2 : ℕ) * j + (1 / 2) * h ^ (3 : ℕ) - (15 / 4) * j ^ (4 : ℕ) - (13 / 2) * h * j ^ (3 : ℕ) - h ^ (2 : ℕ) * j ^ (2 : ℕ) + 3 * h ^ (3 : ℕ) * j + (5 / 4) * h ^ (4 : ℕ) - 2 * j ^ (5 : ℕ) - 3 * h * j ^ (4 : ℕ) + (5 / 2) * h ^ (2 : ℕ) * j ^ (3 : ℕ) + (13 / 2) * h ^ (3 : ℕ) * j ^ (2 : ℕ) + (7 / 2) * h ^ (4 : ℕ) * j + (1 / 2) * h ^ (5 : ℕ) - (1 / 2) * j ^ (6 : ℕ) + (15 / 4) * h ^ (2 : ℕ) * j ^ (4 : ℕ) + (13 / 2) * h ^ (3 : ℕ) * j ^ (3 : ℕ) + (17 / 4) * h ^ (4 : ℕ) * j ^ (2 : ℕ) + h ^ (5 : ℕ) * j + (1 / 2) * h * j ^ (6 : ℕ) + 2 * h ^ (2 : ℕ) * j ^ (5 : ℕ) + 3 * h ^ (3 : ℕ) * j ^ (4 : ℕ) + 2 * h ^ (4 : ℕ) * j ^ (3 : ℕ) + (1 / 2) * h ^ (5 : ℕ) * j ^ (2 : ℕ)

/-- The coefficient of `y^0` in `𝒰(t, x, q)` at `t = (1 - h)/2`, `x = h + j`, `q = 1 + y`. -/
noncomputable def nlrYU0 (h j : ℝ) : ℝ :=
  -(25 / 4) * j - (25 / 4) * h - 9 * j ^ (2 : ℕ) - (85 / 4) * h * j - (49 / 4) * h ^ (2 : ℕ) - 3 * j ^ (3 : ℕ) - 12 * h * j ^ (2 : ℕ) - (47 / 4) * h ^ (2 : ℕ) * j - (11 / 4) * h ^ (3 : ℕ) + 6 * h ^ (2 : ℕ) * j ^ (2 : ℕ) + (49 / 4) * h ^ (3 : ℕ) * j + (25 / 4) * h ^ (4 : ℕ) + 3 * h ^ (2 : ℕ) * j ^ (3 : ℕ) + 9 * h ^ (3 : ℕ) * j ^ (2 : ℕ) + 9 * h ^ (4 : ℕ) * j + 3 * h ^ (5 : ℕ)

/-- The coefficient of `y^1` in `𝒰(t, x, q)` at `t = (1 - h)/2`, `x = h + j`, `q = 1 + y`. -/
noncomputable def nlrYU1 (h j : ℝ) : ℝ :=
  (1 / 4) - (93 / 4) * j - (93 / 4) * h - (183 / 4) * j ^ (2 : ℕ) - (197 / 2) * h * j - 53 * h ^ (2 : ℕ) - (141 / 4) * j ^ (3 : ℕ) - (399 / 4) * h * j ^ (2 : ℕ) - (177 / 2) * h ^ (2 : ℕ) * j - 24 * h ^ (3 : ℕ) - 15 * j ^ (4 : ℕ) - 36 * h * j ^ (3 : ℕ) - (33 / 4) * h ^ (2 : ℕ) * j ^ (2 : ℕ) + (65 / 2) * h ^ (3 : ℕ) * j + (79 / 4) * h ^ (4 : ℕ) - 3 * j ^ (5 : ℕ) + (141 / 4) * h ^ (2 : ℕ) * j ^ (3 : ℕ) + (303 / 4) * h ^ (3 : ℕ) * j ^ (2 : ℕ) + (243 / 4) * h ^ (4 : ℕ) * j + (69 / 4) * h ^ (5 : ℕ) + 3 * h * j ^ (5 : ℕ) + 15 * h ^ (2 : ℕ) * j ^ (4 : ℕ) + 30 * h ^ (3 : ℕ) * j ^ (3 : ℕ) + 30 * h ^ (4 : ℕ) * j ^ (2 : ℕ) + 15 * h ^ (5 : ℕ) * j + 3 * h ^ (6 : ℕ)

/-- The coefficient of `y^2` in `𝒰(t, x, q)` at `t = (1 - h)/2`, `x = h + j`, `q = 1 + y`. -/
noncomputable def nlrYU2 (h j : ℝ) : ℝ :=
  1 - (49 / 2) * j - (51 / 2) * h - (115 / 2) * j ^ (2 : ℕ) - (249 / 2) * h * j - 67 * h ^ (2 : ℕ) - (109 / 2) * j ^ (3 : ℕ) - (305 / 2) * h * j ^ (2 : ℕ) - 139 * h ^ (2 : ℕ) * j - 41 * h ^ (3 : ℕ) - 26 * j ^ (4 : ℕ) - 66 * h * j ^ (3 : ℕ) - (75 / 2) * h ^ (2 : ℕ) * j ^ (2 : ℕ) + (41 / 2) * h ^ (3 : ℕ) * j + 18 * h ^ (4 : ℕ) - 5 * j ^ (5 : ℕ) + (109 / 2) * h ^ (2 : ℕ) * j ^ (3 : ℕ) + (227 / 2) * h ^ (3 : ℕ) * j ^ (2 : ℕ) + (177 / 2) * h ^ (4 : ℕ) * j + (49 / 2) * h ^ (5 : ℕ) + 5 * h * j ^ (5 : ℕ) + 26 * h ^ (2 : ℕ) * j ^ (4 : ℕ) + 54 * h ^ (3 : ℕ) * j ^ (3 : ℕ) + 56 * h ^ (4 : ℕ) * j ^ (2 : ℕ) + 29 * h ^ (5 : ℕ) * j + 6 * h ^ (6 : ℕ)

/-- The coefficient of `y^3` in `𝒰(t, x, q)` at `t = (1 - h)/2`, `x = h + j`, `q = 1 + y`. -/
noncomputable def nlrYU3 (h j : ℝ) : ℝ :=
  (1 / 2) - (17 / 2) * j - 9 * h - (47 / 2) * j ^ (2 : ℕ) - (101 / 2) * h * j - 27 * h ^ (2 : ℕ) - (53 / 2) * j ^ (3 : ℕ) - (145 / 2) * h * j ^ (2 : ℕ) - (133 / 2) * h ^ (2 : ℕ) * j - (41 / 2) * h ^ (3 : ℕ) - (27 / 2) * j ^ (4 : ℕ) - 35 * h * j ^ (3 : ℕ) - (51 / 2) * h ^ (2 : ℕ) * j ^ (2 : ℕ) + h ^ (3 : ℕ) * j + 5 * h ^ (4 : ℕ) - (5 / 2) * j ^ (5 : ℕ) + (53 / 2) * h ^ (2 : ℕ) * j ^ (3 : ℕ) + (109 / 2) * h ^ (3 : ℕ) * j ^ (2 : ℕ) + 42 * h ^ (4 : ℕ) * j + (23 / 2) * h ^ (5 : ℕ) + (5 / 2) * h * j ^ (5 : ℕ) + (27 / 2) * h ^ (2 : ℕ) * j ^ (4 : ℕ) + 29 * h ^ (3 : ℕ) * j ^ (3 : ℕ) + 31 * h ^ (4 : ℕ) * j ^ (2 : ℕ) + (33 / 2) * h ^ (5 : ℕ) * j + (7 / 2) * h ^ (6 : ℕ)

/-- The coefficient of `y^4` in `𝒰(t, x, q)` at `t = (1 - h)/2`, `x = h + j`, `q = 1 + y`. -/
noncomputable def nlrYU4 (h j : ℝ) : ℝ :=
  (1 / 2) * j + (1 / 2) * h + (3 / 4) * j ^ (2 : ℕ) + (5 / 4) * h * j + (1 / 2) * h ^ (2 : ℕ) - (1 / 4) * j ^ (3 : ℕ) - (3 / 4) * h * j ^ (2 : ℕ) - (5 / 4) * h ^ (2 : ℕ) * j - (3 / 4) * h ^ (3 : ℕ) - (1 / 4) * j ^ (4 : ℕ) - h * j ^ (3 : ℕ) - (9 / 4) * h ^ (2 : ℕ) * j ^ (2 : ℕ) - (9 / 4) * h ^ (3 : ℕ) * j - (3 / 4) * h ^ (4 : ℕ) + (1 / 4) * h ^ (2 : ℕ) * j ^ (3 : ℕ) + (3 / 4) * h ^ (3 : ℕ) * j ^ (2 : ℕ) + (3 / 4) * h ^ (4 : ℕ) * j + (1 / 4) * h ^ (5 : ℕ) + (1 / 4) * h ^ (2 : ℕ) * j ^ (4 : ℕ) + h ^ (3 : ℕ) * j ^ (3 : ℕ) + (3 / 2) * h ^ (4 : ℕ) * j ^ (2 : ℕ) + h ^ (5 : ℕ) * j + (1 / 4) * h ^ (6 : ℕ)

/-- The coefficient of `y^0` in `𝒱(t, x, q)` at `t = (1 - h)/2`, `x = h + j`, `q = 1 + y`. -/
noncomputable def nlrYV0 (h j : ℝ) : ℝ :=
  1080 + 2880 * j + 2880 * h + 2532 * j ^ (2 : ℕ) + 4974 * h * j + 2802 * h ^ (2 : ℕ) + 749 * j ^ (3 : ℕ) + 2217 * h * j ^ (2 : ℕ) + 2787 * h ^ (2 : ℕ) * j + 1319 * h ^ (3 : ℕ) + 21 * j ^ (4 : ℕ) - 22 * h * j ^ (3 : ℕ) + 522 * h ^ (2 : ℕ) * j ^ (2 : ℕ) + 924 * h ^ (3 : ℕ) * j + 359 * h ^ (4 : ℕ) - 57 * h * j ^ (4 : ℕ) + 51 * h ^ (2 : ℕ) * j ^ (3 : ℕ) + 315 * h ^ (3 : ℕ) * j ^ (2 : ℕ) + 249 * h ^ (4 : ℕ) * j + 42 * h ^ (5 : ℕ) + 18 * h ^ (2 : ℕ) * j ^ (4 : ℕ) + 54 * h ^ (3 : ℕ) * j ^ (3 : ℕ) + 54 * h ^ (4 : ℕ) * j ^ (2 : ℕ) + 18 * h ^ (5 : ℕ) * j

/-- The coefficient of `y^1` in `𝒱(t, x, q)` at `t = (1 - h)/2`, `x = h + j`, `q = 1 + y`. -/
noncomputable def nlrYV1 (h j : ℝ) : ℝ :=
  540 + 1170 * j + 1440 * h + 96 * j ^ (2 : ℕ) + 1947 * h * j + 1491 * h ^ (2 : ℕ) - (1597 / 2) * j ^ (3 : ℕ) - (285 / 2) * h * j ^ (2 : ℕ) + (2481 / 2) * h ^ (2 : ℕ) * j + (1709 / 2) * h ^ (3 : ℕ) - (807 / 2) * j ^ (4 : ℕ) - 734 * h * j ^ (3 : ℕ) + 633 * h ^ (3 : ℕ) * j + (605 / 2) * h ^ (4 : ℕ) - 36 * j ^ (5 : ℕ) - (237 / 2) * h * j ^ (4 : ℕ) - (57 / 2) * h ^ (2 : ℕ) * j ^ (3 : ℕ) + (387 / 2) * h ^ (3 : ℕ) * j ^ (2 : ℕ) + (357 / 2) * h ^ (4 : ℕ) * j + 39 * h ^ (5 : ℕ) + 9 * h ^ (2 : ℕ) * j ^ (4 : ℕ) + 27 * h ^ (3 : ℕ) * j ^ (3 : ℕ) + 27 * h ^ (4 : ℕ) * j ^ (2 : ℕ) + 9 * h ^ (5 : ℕ) * j

/-- The coefficient of `y^2` in `𝒱(t, x, q)` at `t = (1 - h)/2`, `x = h + j`, `q = 1 + y`. -/
noncomputable def nlrYV2 (h j : ℝ) : ℝ :=
  -90 - 825 * j - 240 * h - 2001 * j ^ (2 : ℕ) - 1542 * h * j - 171 * h ^ (2 : ℕ) - (2937 / 2) * j ^ (3 : ℕ) - (4263 / 2) * h * j ^ (2 : ℕ) - (1545 / 2) * h ^ (2 : ℕ) * j + (51 / 2) * h ^ (3 : ℕ) - 393 * j ^ (4 : ℕ) - (1683 / 2) * h * j ^ (3 : ℕ) - (1077 / 2) * h ^ (2 : ℕ) * j ^ (2 : ℕ) - (69 / 2) * h ^ (3 : ℕ) * j + (111 / 2) * h ^ (4 : ℕ) - 30 * j ^ (5 : ℕ) - 87 * h * j ^ (4 : ℕ) - 81 * h ^ (2 : ℕ) * j ^ (3 : ℕ) - 12 * h ^ (3 : ℕ) * j ^ (2 : ℕ) + 21 * h ^ (4 : ℕ) * j + 9 * h ^ (5 : ℕ)

/-- The coefficient of `y^3` in `𝒱(t, x, q)` at `t = (1 - h)/2`, `x = h + j`, `q = 1 + y`. -/
noncomputable def nlrYV3 (h j : ℝ) : ℝ :=
  -90 - 465 * j - 240 * h - 726 * j ^ (2 : ℕ) - 807 * h * j - 216 * h ^ (2 : ℕ) - 327 * j ^ (3 : ℕ) - 636 * h * j ^ (2 : ℕ) - 381 * h ^ (2 : ℕ) * j - 72 * h ^ (3 : ℕ) - 30 * j ^ (4 : ℕ) - 87 * h * j ^ (3 : ℕ) - 90 * h ^ (2 : ℕ) * j ^ (2 : ℕ) - 39 * h ^ (3 : ℕ) * j - 6 * h ^ (4 : ℕ)

theorem nlr_T_y (h j y : ℝ) :
    nsfComb 6 0 ((1 - h) / 2) (h + j) 1 (1 + y) 0 0 0 = nlrYT0 h j + nlrYT1 h j * y + nlrYT2 h j * y ^ (2 : ℕ) + nlrYT3 h j * y ^ (3 : ℕ) + nlrYT4 h j * y ^ (4 : ℕ) + nlrYT5 h j * y ^ (5 : ℕ) := by
  unfold nsfComb nsfTP nsfKt nsfHt nsfE0 nsrN nlrYT0 nlrYT1 nlrYT2 nlrYT3 nlrYT4 nlrYT5
  ring

theorem nlr_U_y (h j y : ℝ) :
    nlrCU ((1 - h) / 2) (h + j) (1 + y) = nlrYU0 h j + nlrYU1 h j * y + nlrYU2 h j * y ^ (2 : ℕ) + nlrYU3 h j * y ^ (3 : ℕ) + nlrYU4 h j * y ^ (4 : ℕ) := by
  unfold nlrCU nlrYU0 nlrYU1 nlrYU2 nlrYU3 nlrYU4
  ring

theorem nlr_V_y (h j y : ℝ) :
    nlrCV ((1 - h) / 2) (h + j) (1 + y) = nlrYV0 h j + nlrYV1 h j * y + nlrYV2 h j * y ^ (2 : ℕ) + nlrYV3 h j * y ^ (3 : ℕ) := by
  unfold nlrCV nlrYV0 nlrYV1 nlrYV2 nlrYV3
  ring

/-- The coefficient of `y^0` in the collection identity. -/
theorem nlr_coef0 (h j : ℝ) :
    96 * nlrWRx (h + j) * nlrYT0 h j + 4 * nlrYU0 h j * nlrYV0 h j =
      ((1 + h) ^ (3 : ℕ) * h ^ (3 : ℕ) * nlrB00 h / 2) +
      ((1 + h) ^ (2 : ℕ) * h ^ (2 : ℕ) * nlrB10 h / 2) * j +
      ((1 + h) ^ (2 : ℕ) * h * nlrB20 h / 2) * j ^ (2 : ℕ) +
      (2 * (h + 1) ^ (2 : ℕ) * nlrP30 h) * j ^ (3 : ℕ) +
      ((h + 1) ^ (2 : ℕ) * nlrP40 h) * j ^ (4 : ℕ) +
      (3 * (h + 1) ^ (2 : ℕ) * nlrP50 h) * j ^ (5 : ℕ) +
      (12 * (h + 1) ^ (2 : ℕ) * nlrP60 h) * j ^ (6 : ℕ) +
      (36 * (h + 1) ^ (2 : ℕ) * (1 - h) * nlrP70 h) * j ^ (7 : ℕ) := by
  unfold nlrWRx nlrYT0 nlrYU0 nlrYV0 nlrB00 nlrB10 nlrB20 nlrP30 nlrP40 nlrP50 nlrP60 nlrP70
  ring

/-- The coefficient of `y^1` in the collection identity. -/
theorem nlr_coef1 (h j : ℝ) :
    48 * nlrWRx (h + j) * nlrYT0 h j + 96 * nlrWRx (h + j) * nlrYT1 h j + 12 * nlrGtx ((1 - h) / 2) (h + j) * nlrSevx (h + j) - 12 * nlrGtx ((1 - h) / 2) (h + j) * nlrJtx ((1 - h) / 2) (h + j) + 4 * nlrYU0 h j * nlrYV1 h j + 4 * nlrYU1 h j * nlrYV0 h j =
      ((1 + h) ^ (3 : ℕ) * h ^ (2 : ℕ) * nlrB01 h / 2) +
      ((1 + h) ^ (2 : ℕ) * h * nlrB11 h / 2) * j +
      ((1 + h) ^ (2 : ℕ) * nlrB21 h / 2) * j ^ (2 : ℕ) +
      ((h + 1) * nlrP31 h) * j ^ (3 : ℕ) +
      ((h + 1) * nlrP41 h / 2) * j ^ (4 : ℕ) +
      (3 * (h + 1) * nlrP51 h / 2) * j ^ (5 : ℕ) +
      (6 * (h + 1) * nlrP61 h) * j ^ (6 : ℕ) +
      (3 * (h + 1) * nlrP71 h) * j ^ (7 : ℕ) +
      (24 * (h + 1) * (1 - h) * nlrP81 h) * j ^ (8 : ℕ) +
      (36 * (h + 1) * (1 - h) * nlrP91 h) * j ^ (9 : ℕ) := by
  unfold nlrWRx nlrGtx nlrSevx nlrJtx nlrYT0 nlrYT1 nlrYU0 nlrYU1 nlrYV0 nlrYV1 nlrB01 nlrB11 nlrB21 nlrP31 nlrP41 nlrP51 nlrP61 nlrP71 nlrP81 nlrP91
  ring

/-- The coefficient of `y^2` in the collection identity. -/
theorem nlr_coef2 (h j : ℝ) :
    48 * nlrWRx (h + j) * nlrYT1 h j + 96 * nlrWRx (h + j) * nlrYT2 h j + 24 * nlrGtx ((1 - h) / 2) (h + j) * nlrSevx (h + j) - 48 * nlrGtx ((1 - h) / 2) (h + j) * nlrJtx ((1 - h) / 2) (h + j) + 4 * nlrYU0 h j * nlrYV2 h j + 4 * nlrYU1 h j * nlrYV1 h j + 4 * nlrYU2 h j * nlrYV0 h j =
      ((1 + h) ^ (3 : ℕ) * h * nlrB02 h / 2) +
      ((1 + h) ^ (2 : ℕ) * (1080 * h ^ (9 : ℕ) + nlrB12 h) / 2) * j +
      ((1 + h) ^ (2 : ℕ) * nlrB22 h / 2) * j ^ (2 : ℕ) +
      ((h + 1) * nlrP32 h / 2) * j ^ (3 : ℕ) +
      ((h + 1) * nlrP42 h / 2) * j ^ (4 : ℕ) +
      (nlrP52 h / 2) * j ^ (5 : ℕ) +
      (nlrP62 h) * j ^ (6 : ℕ) +
      (nlrP72 h / 2) * j ^ (7 : ℕ) +
      (4 * nlrP82 h) * j ^ (8 : ℕ) +
      (6 * (1 - h) * nlrP92 h) * j ^ (9 : ℕ) +
      (432 * (1 - h)) * j ^ (10 : ℕ) := by
  unfold nlrWRx nlrGtx nlrSevx nlrJtx nlrYT1 nlrYT2 nlrYU0 nlrYU1 nlrYU2 nlrYV0 nlrYV1 nlrYV2 nlrB02 nlrB12 nlrB22 nlrP32 nlrP42 nlrP52 nlrP62 nlrP72 nlrP82 nlrP92
  ring

/-- The coefficient of `y^3` in the collection identity. -/
theorem nlr_coef3 (h j : ℝ) :
    48 * nlrWRx (h + j) * nlrYT2 h j + 96 * nlrWRx (h + j) * nlrYT3 h j + 13 * nlrGtx ((1 - h) / 2) (h + j) * nlrSevx (h + j) - 73 * nlrGtx ((1 - h) / 2) (h + j) * nlrJtx ((1 - h) / 2) (h + j) + 4 * nlrYU0 h j * nlrYV3 h j + 4 * nlrYU1 h j * nlrYV2 h j + 4 * nlrYU2 h j * nlrYV1 h j + 4 * nlrYU3 h j * nlrYV0 h j =
      ((1 + h) ^ (3 : ℕ) * nlrB03 h / 2) +
      ((1 + h) ^ (2 : ℕ) * (936 * h ^ (9 : ℕ) + nlrB13 h) / 2) * j +
      ((1 + h) ^ (2 : ℕ) * nlrB23 h / 2) * j ^ (2 : ℕ) +
      ((h + 1) * nlrP33 h / 2) * j ^ (3 : ℕ) +
      ((h + 1) * nlrP43 h / 2) * j ^ (4 : ℕ) +
      (nlrP53 h / 2) * j ^ (5 : ℕ) +
      (nlrP63 h / 2) * j ^ (6 : ℕ) +
      (4 * nlrP73 h) * j ^ (7 : ℕ) +
      (2 * nlrP83 h) * j ^ (8 : ℕ) +
      (24 * (1 - h) * nlrP93 h) * j ^ (9 : ℕ) +
      (1080 * (1 - h)) * j ^ (10 : ℕ) := by
  unfold nlrWRx nlrGtx nlrSevx nlrJtx nlrYT2 nlrYT3 nlrYU0 nlrYU1 nlrYU2 nlrYU3 nlrYV0 nlrYV1 nlrYV2 nlrYV3 nlrB03 nlrB13 nlrB23 nlrP33 nlrP43 nlrP53 nlrP63 nlrP73 nlrP83 nlrP93
  ring

/-- The coefficient of `y^4` in the collection identity. -/
theorem nlr_coef4 (h j : ℝ) :
    48 * nlrWRx (h + j) * nlrYT3 h j + 96 * nlrWRx (h + j) * nlrYT4 h j + nlrGtx ((1 - h) / 2) (h + j) * nlrSevx (h + j) - 51 * nlrGtx ((1 - h) / 2) (h + j) * nlrJtx ((1 - h) / 2) (h + j) + 4 * nlrYU1 h j * nlrYV3 h j + 4 * nlrYU2 h j * nlrYV2 h j + 4 * nlrYU3 h j * nlrYV1 h j + 4 * nlrYU4 h j * nlrYV0 h j =
      ((1 + h) ^ (3 : ℕ) * nlrB04 h / 2) +
      ((1 + h) ^ (2 : ℕ) * (288 * h ^ (9 : ℕ) + nlrB14 h) / 2) * j +
      ((1 + h) ^ (2 : ℕ) * nlrB24 h / 2) * j ^ (2 : ℕ) +
      ((h + 1) * nlrP34 h) * j ^ (3 : ℕ) +
      ((h + 1) * nlrP44 h) * j ^ (4 : ℕ) +
      (nlrP54 h) * j ^ (5 : ℕ) +
      (nlrP64 h) * j ^ (6 : ℕ) +
      (nlrP74 h) * j ^ (7 : ℕ) +
      (nlrP84 h) * j ^ (8 : ℕ) +
      ((1 - h) * nlrP94 h) * j ^ (9 : ℕ) +
      (960 * (1 - h)) * j ^ (10 : ℕ) := by
  unfold nlrWRx nlrGtx nlrSevx nlrJtx nlrYT3 nlrYT4 nlrYU1 nlrYU2 nlrYU3 nlrYU4 nlrYV0 nlrYV1 nlrYV2 nlrYV3 nlrB04 nlrB14 nlrB24 nlrP34 nlrP44 nlrP54 nlrP64 nlrP74 nlrP84 nlrP94
  ring

/-- The coefficient of `y^5` in the collection identity. -/
theorem nlr_coef5 (h j : ℝ) :
    48 * nlrWRx (h + j) * nlrYT4 h j + 96 * nlrWRx (h + j) * nlrYT5 h j - 15 * nlrGtx ((1 - h) / 2) (h + j) * nlrJtx ((1 - h) / 2) (h + j) + 4 * nlrYU2 h j * nlrYV3 h j + 4 * nlrYU3 h j * nlrYV2 h j + 4 * nlrYU4 h j * nlrYV1 h j =
      ((1 + h) ^ (3 : ℕ) * nlrB05 h / 2) +
      ((1 + h) ^ (2 : ℕ) * (18 * h ^ (9 : ℕ) + nlrB15 h) / 2) * j +
      ((1 + h) ^ (2 : ℕ) * nlrB25 h / 2) * j ^ (2 : ℕ) +
      ((h + 1) * nlrP35 h / 2) * j ^ (3 : ℕ) +
      ((h + 1) * nlrP45 h / 2) * j ^ (4 : ℕ) +
      (3 * nlrP55 h / 2) * j ^ (5 : ℕ) +
      (nlrP65 h / 2) * j ^ (6 : ℕ) +
      (nlrP75 h / 2) * j ^ (7 : ℕ) +
      (3 * nlrP85 h / 2) * j ^ (8 : ℕ) +
      (6 * (1 - h) * nlrP95 h) * j ^ (9 : ℕ) +
      (300 * (1 - h)) * j ^ (10 : ℕ) := by
  unfold nlrWRx nlrGtx nlrJtx nlrYT4 nlrYT5 nlrYU2 nlrYU3 nlrYU4 nlrYV1 nlrYV2 nlrYV3 nlrB05 nlrB15 nlrB25 nlrP35 nlrP45 nlrP55 nlrP65 nlrP75 nlrP85 nlrP95
  ring

/-- The coefficient of `y^6` in the collection identity. -/
theorem nlr_coef6 (h j : ℝ) :
    48 * nlrWRx (h + j) * nlrYT5 h j - nlrGtx ((1 - h) / 2) (h + j) * nlrJtx ((1 - h) / 2) (h + j) + 4 * nlrYU3 h j * nlrYV3 h j + 4 * nlrYU4 h j * nlrYV2 h j =
      ((1 + h) ^ (3 : ℕ) * nlrB06 h / 2) +
      ((1 + h) ^ (2 : ℕ) * nlrB16 h / 2) * j +
      ((1 + h) ^ (2 : ℕ) * nlrB26 h / 2) * j ^ (2 : ℕ) +
      ((h + 1) * nlrP36 h / 2) * j ^ (3 : ℕ) +
      ((h + 1) * nlrP46 h / 2) * j ^ (4 : ℕ) +
      (3 * nlrP56 h / 2) * j ^ (5 : ℕ) +
      (nlrP66 h / 2) * j ^ (6 : ℕ) +
      (nlrP76 h / 2) * j ^ (7 : ℕ) +
      ((1 - h) * nlrP86 h) * j ^ (8 : ℕ) +
      (2 * (1 - h) * nlrP96 h) * j ^ (9 : ℕ) := by
  unfold nlrWRx nlrGtx nlrJtx nlrYT5 nlrYU3 nlrYU4 nlrYV2 nlrYV3 nlrB06 nlrB16 nlrB26 nlrP36 nlrP46 nlrP56 nlrP66 nlrP76 nlrP86 nlrP96
  ring

/-- The coefficient of `y^7` in the collection identity. -/
theorem nlr_coef7 (h j : ℝ) :
    4 * nlrYU4 h j * nlrYV3 h j =
      ((1 + h) ^ (3 : ℕ) * h * nlrB07 h / 2) +
      ((1 + h) ^ (2 : ℕ) * nlrB17 h / 2) * j +
      ((1 + h) ^ (2 : ℕ) * nlrB27 h / 2) * j ^ (2 : ℕ) +
      (3 * (h + 1) * (1 - h) * nlrP37 h) * j ^ (3 : ℕ) +
      (3 * (h + 1) * (1 - h) * nlrP47 h) * j ^ (4 : ℕ) +
      (3 * (h + 1) * (1 - h) * nlrP57 h) * j ^ (5 : ℕ) +
      (3 * (h + 1) * (1 - h) * nlrP67 h) * j ^ (6 : ℕ) +
      (3 * (h + 1) * (1 - h) * nlrP77 h) * j ^ (7 : ℕ) +
      (30 * (h + 1) * (1 - h)) * j ^ (8 : ℕ) := by
  unfold nlrYU4 nlrYV3 nlrB07 nlrB17 nlrB27 nlrP37 nlrP47 nlrP57 nlrP67 nlrP77
  ring

/-- **The collection identity** `Π = ∑ C̃ᵢ jⁱ` (checked one power of `y` at a time). -/
theorem nlr_collect (h j y : ℝ) :
    nlrCP ((1 - h) / 2) (h + j) (1 + y) =
      nlrC0 h y + nlrC1 h y * j + nlrC2 h y * j ^ (2 : ℕ) + nlrC3 h y * j ^ (3 : ℕ) + nlrC4 h y * j ^ (4 : ℕ)
        + nlrC5 h y * j ^ (5 : ℕ) + nlrC6 h y * j ^ (6 : ℕ) + nlrC7 h y * j ^ (7 : ℕ) + nlrC8 h y * j ^ (8 : ℕ)
        + nlrC9 h y * j ^ (9 : ℕ) + nlrC10 h y * j ^ (10 : ℕ) := by
  unfold nlrCP nlrCK
  rw [nlr_T_y, nlr_U_y, nlr_V_y]
  have e0 := nlr_coef0 h j
  have e1 := nlr_coef1 h j
  have e2 := nlr_coef2 h j
  have e3 := nlr_coef3 h j
  have e4 := nlr_coef4 h j
  have e5 := nlr_coef5 h j
  have e6 := nlr_coef6 h j
  have e7 := nlr_coef7 h j
  unfold nlrC0 nlrC1 nlrC2 nlrC3 nlrC4 nlrC5 nlrC6 nlrC7 nlrC8 nlrC9 nlrC10
  linear_combination e0 + y * e1 + y ^ (2 : ℕ) * e2 + y ^ (3 : ℕ) * e3 + y ^ (4 : ℕ) * e4 + y ^ (5 : ℕ) * e5 + y ^ (6 : ℕ) * e6 + y ^ (7 : ℕ) * e7

/-- **The unit-shape residual is positive**, through the circuit `𝒫` and `nlr_sum_pos`: for
`1/4 ≤ t ≤ 1/3`, `2t + x ≥ 1`, `1 ≤ q ≤ 2 - 2t`. -/
theorem nlr_unit_pos {t x q : ℝ} (ht0 : 1 / 4 ≤ t) (ht1 : t ≤ 1 / 3) (hj : 1 ≤ 2 * t + x)
    (hq : 1 ≤ q) (hy : q - 1 ≤ 1 - 2 * t) :
    0 < nsfComb 6 0 t x 1 q (nsfVG t x + 3 / 4 * (q + 2 * t + x - 1) * (nsfVG t x - nsrFl t x q))
      (nsrLp q) 0 := by
  have hx : 0 < x := by linarith
  have hq0 : 0 < q := by linarith
  have hP : 0 < nlrCP t x q := by
    have e : nlrCP t x q = nlrCP ((1 - (1 - 2 * t)) / 2) ((1 - 2 * t) + (2 * t + x - 1))
        (1 + (q - 1)) := by congr 1 <;> ring
    rw [e, nlr_collect]
    exact nlr_sum_pos (by linarith) (by linarith) (by linarith) hy (by linarith)
  rw [← nlr_link t x q hq0 hx] at hP
  have hpos : 0 ≤ 48 * (q + 1) * nlrWRx x := by unfold nlrWRx; positivity
  exact pos_of_mul_pos_right hP hpos

end SmoothedOctagon
