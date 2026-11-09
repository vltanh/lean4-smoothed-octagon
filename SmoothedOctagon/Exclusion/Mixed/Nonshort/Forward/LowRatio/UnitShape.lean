module

public import SmoothedOctagon.Exclusion.Mixed.FwdHand.LowRatioHandSigns

/-!
# Case M2, forward successor by hand: the low-ratio unit-shape sign

The sign of the low-ratio combined residual at the unit shape `k = 1`, at the effective norm `v̂`
and with `log q ↦ L₊`, used in `fh_lowRatio_core`.

The cleared residual `48(q + 1)WR · fhComb 6 0 t x 1 q v̂ L₊ 0` is the polynomial circuit
`𝒫 = 48(q + 1)WR 𝒯 + 4𝒰𝒱 + 𝒦` (`lrh_link`). With `h = 1 - 2t`,
`j = 2t + x - 1`, `y = q - 1`, `𝒫 = ∑ᵢ C̃ᵢ(h, y) jⁱ` (`lrh_collect`), which is positive by
`lrh_sum_pos` (`FwdHand/LowRatioHandSigns`).

The exact collection identity `𝒫 = ∑ C̃ᵢ jⁱ` is checked one power of `y`
at a time (`lrh_coef0`, …, `lrh_coef7`: identities in `(h, j)` with at most 86
monomials and degree at most 12), after expanding the circuit factors `𝒯`, `𝒰`, `𝒱` in `y`
(`lrh_T_y`, `lrh_U_y`, `lrh_V_y`: at most 195 monomials); no identity in three variables beyond
these factor expansions is expanded.

## Main API

* `lrhCU`, `lrhCV`, `lrhCK`, `lrhCP`: the circuit; `lrh_link`; `lrh_collect`.
* `lrh_unit_pos`: **the unit-shape residual at `v̂`, `L₊` is positive.**
-/

@[expose] public section

namespace SmoothedOctagon

/-! ### The circuit of the unit-shape residual -/

/-- The circuit factor `𝒰`, a quartic in `q`. -/
noncomputable def lrhCU (t x q : ℝ) : ℝ :=
  t * (t + x) * (x + 1) ^ (4 : ℕ) - t * (x + 1) ^ (3 : ℕ) * (t + x ^ (2 : ℕ) + 2 * x) * q + (x + 1) ^ (2 : ℕ) * (-2 * t ^ (2 : ℕ) * x ^ (2 : ℕ) + 10 * t ^ (2 : ℕ) * x + 5 * t * x ^ (3 : ℕ) + 17 * t * x ^ (2 : ℕ) - 7 * t * x - t + 6 * x) * q ^ (2 : ℕ) - (x + 1) * (-2 * t ^ (2 : ℕ) * x ^ (2 : ℕ) - 4 * t ^ (2 : ℕ) * x + 5 * t * x ^ (4 : ℕ) + 20 * t * x ^ (3 : ℕ) + 20 * t * x ^ (2 : ℕ) - t + 6 * x ^ (2 : ℕ) + 12 * x) * q ^ (3 : ℕ) + t * x * (t - 1) * (-2 * t + x ^ (3 : ℕ) + x ^ (2 : ℕ) - 3 * x - 1) * q ^ (4 : ℕ)

/-- `𝒱 = 48(q + 1)RW² v̂`. -/
noncomputable def lrhCV (t x q : ℝ) : ℝ :=
  (q + 1) * (4 + 3 * (q + 2 * t + x - 1)) * (12 * t ^ (2 : ℕ) * x ^ (3 : ℕ) + 132 * t ^ (2 : ℕ) * x ^ (2 : ℕ) + 300 * t ^ (2 : ℕ) * x + 180 * t ^ (2 : ℕ) + 19 * t * x ^ (3 : ℕ) - 12 * t * x ^ (2 : ℕ) - 210 * t * x - 180 * t + 12 * x ^ (4 : ℕ) + 113 * x ^ (3 : ℕ) + 312 * x ^ (2 : ℕ) + 390 * x + 180) - 6 * (x ^ (2 : ℕ) + 10 * x + 15) * (q + 2 * t + x - 1) * ((1 + x) * (-t + 5 * x + 6) + 2 * (3 * t ^ (2 : ℕ) + t * x - 5 * t + x ^ (2 : ℕ) + x + 3) * q + (t + x) * (6 * t + 5 * x - 1) * q ^ (2 : ℕ))

/-- `WR = (1 + x)(x² + 10x + 15)`. -/
noncomputable def lrhWRx (x : ℝ) : ℝ := (1 + x) * (x ^ (2 : ℕ) + 10 * x + 15)

/-- `-32 t B p W² R` with `B = 1 + 2tx + x²`. -/
noncomputable def lrhGtx (t x : ℝ) : ℝ :=
  -32 * t * (1 + 2 * t * x + x ^ (2 : ℕ)) * (t + x) * (1 + x) ^ (2 : ℕ) * (x ^ (2 : ℕ) + 10 * x + 15)

/-- `7W²`. -/
noncomputable def lrhSevx (x : ℝ) : ℝ := 7 * (1 + x) ^ (2 : ℕ)

/-- `J = t + x(x + 2)`. -/
noncomputable def lrhJtx (t x : ℝ) : ℝ := t + x * (x + 2)

/-- `𝒦 = -32tBpW²R Z(q)(7W² - Jq²)`, `Z(q) = q(q - 1)(q² + 10q + 1)`. -/
noncomputable def lrhCK (t x q : ℝ) : ℝ :=
  lrhGtx t x * (q * (q - 1) * (q ^ (2 : ℕ) + 10 * q + 1)) * (lrhSevx x - lrhJtx t x * q ^ (2 : ℕ))

/-- **The polynomial circuit** `𝒫 = 48(q + 1)WR 𝒯 + 4𝒰𝒱 + 𝒦`, with
`𝒯 = fhComb 6 0 t x 1 q 0 0 0`. -/
noncomputable def lrhCP (t x q : ℝ) : ℝ :=
  48 * (q + 1) * lrhWRx x * fhComb 6 0 t x 1 q 0 0 0 + 4 * lrhCU t x q * lrhCV t x q + lrhCK t x q

/-- **The link**: the cleared unit-shape residual at
`v = v̂`, `log q = L₊` is the circuit `𝒫`. -/
theorem lrh_link (t x q : ℝ) (hq : 0 < q) (hx : 0 < x) :
    48 * (q + 1) * lrhWRx x * fhComb 6 0 t x 1 q
        (fhVG t x + 3 / 4 * (q + 2 * t + x - 1) * (fhVG t x - nhFl t x q)) (nhLp q) 0 =
      lrhCP t x q := by
  have hW : (1 + x) ≠ 0 := by linarith
  have hR : x ^ (2 : ℕ) + 10 * x + 15 ≠ 0 := by positivity
  have hq1 : q + 1 ≠ 0 := by linarith
  have hCv : fhCv 6 0 t x 1 q = 4 * (1 + x) * lrhCU t x q := by
    unfold fhCv nhNv fhTPv lrhCU; ring
  have hv : fhVG t x + 3 / 4 * (q + 2 * t + x - 1) * (fhVG t x - nhFl t x q) =
      lrhCV t x q / (48 * (q + 1) * (x ^ (2 : ℕ) + 10 * x + 15) * (1 + x) ^ (2 : ℕ)) := by
    unfold fhVG nhFl lrhCV; field_simp; ring
  have h1 : 48 * (q + 1) * lrhWRx x * (lrhCV t x q / (48 * (q + 1) * (x ^ (2 : ℕ) + 10 * x + 15) * (1 + x) ^ (2 : ℕ))
      * (4 * (1 + x) * lrhCU t x q)) = 4 * lrhCU t x q * lrhCV t x q := by
    unfold lrhWRx; field_simp
  have h2 : 48 * (q + 1) * lrhWRx x * (nhLp q * fhCL 6 t x 1 q) = lrhCK t x q := by
    unfold lrhWRx nhLp fhCL nhNL lrhCK lrhGtx lrhSevx lrhJtx; field_simp; ring
  rw [fh_comb_dec, hCv, hv]
  unfold lrhCP
  linear_combination h1 + h2

/-! ### The collection identity, one power of `y` at a time -/

/-- The coefficient of `y^0` in `𝒯(t, x, q)` at `t = (1 - h)/2`, `x = h + j`, `q = 1 + y`. -/
noncomputable def lrhYT0 (h j : ℝ) : ℝ :=
  (75 / 4) * j + (75 / 4) * h + (183 / 4) * j ^ (2 : ℕ) + (405 / 4) * h * j + (111 / 2) * h ^ (2 : ℕ) + 36 * j ^ (3 : ℕ) + (247 / 2) * h * j ^ (2 : ℕ) + (271 / 2) * h ^ (2 : ℕ) * j + 48 * h ^ (3 : ℕ) + 9 * j ^ (4 : ℕ) + 39 * h * j ^ (3 : ℕ) + 47 * h ^ (2 : ℕ) * j ^ (2 : ℕ) + (31 / 2) * h ^ (3 : ℕ) * j - (3 / 2) * h ^ (4 : ℕ) - 3 * h * j ^ (4 : ℕ) - 33 * h ^ (2 : ℕ) * j ^ (3 : ℕ) - (145 / 2) * h ^ (3 : ℕ) * j ^ (2 : ℕ) - (245 / 4) * h ^ (4 : ℕ) * j - (75 / 4) * h ^ (5 : ℕ) - 9 * h ^ (2 : ℕ) * j ^ (4 : ℕ) - 27 * h ^ (3 : ℕ) * j ^ (3 : ℕ) - (131 / 4) * h ^ (4 : ℕ) * j ^ (2 : ℕ) - (83 / 4) * h ^ (5 : ℕ) * j - 6 * h ^ (6 : ℕ) + 3 * h ^ (3 : ℕ) * j ^ (4 : ℕ) + 9 * h ^ (4 : ℕ) * j ^ (3 : ℕ) + 9 * h ^ (5 : ℕ) * j ^ (2 : ℕ) + 3 * h ^ (6 : ℕ) * j

/-- The coefficient of `y^1` in `𝒯(t, x, q)` at `t = (1 - h)/2`, `x = h + j`, `q = 1 + y`. -/
noncomputable def lrhYT1 (h j : ℝ) : ℝ :=
  (23 / 4) + 107 * j + (189 / 2) * h + 295 * j ^ (2 : ℕ) + 550 * h * j + 261 * h ^ (2 : ℕ) + (709 / 2) * j ^ (3 : ℕ) + (1821 / 2) * h * j ^ (2 : ℕ) + (1601 / 2) * h ^ (2 : ℕ) * j + 245 * h ^ (3 : ℕ) + 245 * j ^ (4 : ℕ) + 652 * h * j ^ (3 : ℕ) + 597 * h ^ (2 : ℕ) * j ^ (2 : ℕ) + 211 * h ^ (3 : ℕ) * j + (85 / 4) * h ^ (4 : ℕ) + 108 * j ^ (5 : ℕ) + 217 * h * j ^ (4 : ℕ) - 57 * h ^ (2 : ℕ) * j ^ (3 : ℕ) - 420 * h ^ (3 : ℕ) * j ^ (2 : ℕ) - 347 * h ^ (4 : ℕ) * j - 93 * h ^ (5 : ℕ) + 24 * j ^ (6 : ℕ) - 245 * h ^ (2 : ℕ) * j ^ (4 : ℕ) - 532 * h ^ (3 : ℕ) * j ^ (3 : ℕ) - 496 * h ^ (4 : ℕ) * j ^ (2 : ℕ) - 233 * h ^ (5 : ℕ) * j - 48 * h ^ (6 : ℕ) - 24 * h * j ^ (6 : ℕ) - 108 * h ^ (2 : ℕ) * j ^ (5 : ℕ) - 193 * h ^ (3 : ℕ) * j ^ (4 : ℕ) - (355 / 2) * h ^ (4 : ℕ) * j ^ (3 : ℕ) - (189 / 2) * h ^ (5 : ℕ) * j ^ (2 : ℕ) - (65 / 2) * h ^ (6 : ℕ) * j - (13 / 2) * h ^ (7 : ℕ)

/-- The coefficient of `y^2` in `𝒯(t, x, q)` at `t = (1 - h)/2`, `x = h + j`, `q = 1 + y`. -/
noncomputable def lrhYT2 (h j : ℝ) : ℝ :=
  (23 / 4) + 113 * j + (207 / 2) * h + (1271 / 4) * j ^ (2 : ℕ) + (1253 / 2) * h * j + (1227 / 4) * h ^ (2 : ℕ) + 386 * j ^ (3 : ℕ) + 1072 * h * j ^ (2 : ℕ) + (2017 / 2) * h ^ (2 : ℕ) * j + 328 * h ^ (3 : ℕ) + (537 / 2) * j ^ (4 : ℕ) + (1565 / 2) * h * j ^ (3 : ℕ) + 843 * h ^ (2 : ℕ) * j ^ (2 : ℕ) + 411 * h ^ (3 : ℕ) * j + (329 / 4) * h ^ (4 : ℕ) + 120 * j ^ (5 : ℕ) + (511 / 2) * h * j ^ (4 : ℕ) + (21 / 2) * h ^ (2 : ℕ) * j ^ (3 : ℕ) - (695 / 2) * h ^ (3 : ℕ) * j ^ (2 : ℕ) - 308 * h ^ (4 : ℕ) * j - (171 / 2) * h ^ (5 : ℕ) + 28 * j ^ (6 : ℕ) - (537 / 2) * h ^ (2 : ℕ) * j ^ (4 : ℕ) - (1157 / 2) * h ^ (3 : ℕ) * j ^ (3 : ℕ) - (2195 / 4) * h ^ (4 : ℕ) * j ^ (2 : ℕ) - (539 / 2) * h ^ (5 : ℕ) * j - (235 / 4) * h ^ (6 : ℕ) - 28 * h * j ^ (6 : ℕ) - 120 * h ^ (2 : ℕ) * j ^ (5 : ℕ) - (415 / 2) * h ^ (3 : ℕ) * j ^ (4 : ℕ) - (385 / 2) * h ^ (4 : ℕ) * j ^ (3 : ℕ) - (225 / 2) * h ^ (5 : ℕ) * j ^ (2 : ℕ) - (91 / 2) * h ^ (6 : ℕ) * j - 10 * h ^ (7 : ℕ)

/-- The coefficient of `y^3` in `𝒯(t, x, q)` at `t = (1 - h)/2`, `x = h + j`, `q = 1 + y`. -/
noncomputable def lrhYT3 (h j : ℝ) : ℝ :=
  -(7 / 4) + (19 / 2) * j + 18 * h + (97 / 4) * j ^ (2 : ℕ) + 125 * h * j + (347 / 4) * h ^ (2 : ℕ) - j ^ (3 : ℕ) + 177 * h * j ^ (2 : ℕ) + (603 / 2) * h ^ (2 : ℕ) * j + 131 * h ^ (3 : ℕ) - (61 / 2) * j ^ (4 : ℕ) + (115 / 2) * h * j ^ (3 : ℕ) + 261 * h ^ (2 : ℕ) * j ^ (2 : ℕ) + 248 * h ^ (3 : ℕ) * j + (299 / 4) * h ^ (4 : ℕ) - 22 * j ^ (5 : ℕ) - (41 / 2) * h * j ^ (4 : ℕ) + (119 / 2) * h ^ (2 : ℕ) * j ^ (3 : ℕ) + (187 / 2) * h ^ (3 : ℕ) * j ^ (2 : ℕ) + (69 / 2) * h ^ (4 : ℕ) * j - h ^ (5 : ℕ) - 4 * j ^ (6 : ℕ) + (61 / 2) * h ^ (2 : ℕ) * j ^ (4 : ℕ) + (77 / 2) * h ^ (3 : ℕ) * j ^ (3 : ℕ) - (37 / 4) * h ^ (4 : ℕ) * j ^ (2 : ℕ) - 37 * h ^ (5 : ℕ) * j - (63 / 4) * h ^ (6 : ℕ) + 4 * h * j ^ (6 : ℕ) + 22 * h ^ (2 : ℕ) * j ^ (5 : ℕ) + (89 / 2) * h ^ (3 : ℕ) * j ^ (4 : ℕ) + (75 / 2) * h ^ (4 : ℕ) * j ^ (3 : ℕ) + (11 / 2) * h ^ (5 : ℕ) * j ^ (2 : ℕ) - (19 / 2) * h ^ (6 : ℕ) * j - 4 * h ^ (7 : ℕ)

/-- The coefficient of `y^4` in `𝒯(t, x, q)` at `t = (1 - h)/2`, `x = h + j`, `q = 1 + y`. -/
noncomputable def lrhYT4 (h j : ℝ) : ℝ :=
  -(11 / 4) - 22 * j - (29 / 2) * h - (125 / 2) * j ^ (2 : ℕ) - (311 / 4) * h * j - (89 / 4) * h ^ (2 : ℕ) - (191 / 2) * j ^ (3 : ℕ) - 160 * h * j ^ (2 : ℕ) - (281 / 4) * h ^ (2 : ℕ) * j - (13 / 4) * h ^ (3 : ℕ) - (171 / 2) * j ^ (4 : ℕ) - (327 / 2) * h * j ^ (3 : ℕ) - 63 * h ^ (2 : ℕ) * j ^ (2 : ℕ) + (71 / 2) * h ^ (3 : ℕ) * j + (81 / 4) * h ^ (4 : ℕ) - (177 / 4) * j ^ (5 : ℕ) - (311 / 4) * h * j ^ (4 : ℕ) + (55 / 2) * h ^ (2 : ℕ) * j ^ (3 : ℕ) + 130 * h ^ (3 : ℕ) * j ^ (2 : ℕ) + (173 / 2) * h ^ (4 : ℕ) * j + (35 / 2) * h ^ (5 : ℕ) - 10 * j ^ (6 : ℕ) + (171 / 2) * h ^ (2 : ℕ) * j ^ (4 : ℕ) + (327 / 2) * h ^ (3 : ℕ) * j ^ (3 : ℕ) + (251 / 2) * h ^ (4 : ℕ) * j ^ (2 : ℕ) + (169 / 4) * h ^ (5 : ℕ) * j + (19 / 4) * h ^ (6 : ℕ) + 10 * h * j ^ (6 : ℕ) + (177 / 4) * h ^ (2 : ℕ) * j ^ (5 : ℕ) + (311 / 4) * h ^ (3 : ℕ) * j ^ (4 : ℕ) + 68 * h ^ (4 : ℕ) * j ^ (3 : ℕ) + 30 * h ^ (5 : ℕ) * j ^ (2 : ℕ) + (23 / 4) * h ^ (6 : ℕ) * j + (1 / 4) * h ^ (7 : ℕ)

/-- The coefficient of `y^5` in `𝒯(t, x, q)` at `t = (1 - h)/2`, `x = h + j`, `q = 1 + y`. -/
noncomputable def lrhYT5 (h j : ℝ) : ℝ :=
  -(1 / 4) - (3 / 2) * j - h - (13 / 4) * j ^ (2 : ℕ) - 4 * h * j - h ^ (2 : ℕ) - (9 / 2) * j ^ (3 : ℕ) - 7 * h * j ^ (2 : ℕ) - 2 * h ^ (2 : ℕ) * j + (1 / 2) * h ^ (3 : ℕ) - (15 / 4) * j ^ (4 : ℕ) - (13 / 2) * h * j ^ (3 : ℕ) - h ^ (2 : ℕ) * j ^ (2 : ℕ) + 3 * h ^ (3 : ℕ) * j + (5 / 4) * h ^ (4 : ℕ) - 2 * j ^ (5 : ℕ) - 3 * h * j ^ (4 : ℕ) + (5 / 2) * h ^ (2 : ℕ) * j ^ (3 : ℕ) + (13 / 2) * h ^ (3 : ℕ) * j ^ (2 : ℕ) + (7 / 2) * h ^ (4 : ℕ) * j + (1 / 2) * h ^ (5 : ℕ) - (1 / 2) * j ^ (6 : ℕ) + (15 / 4) * h ^ (2 : ℕ) * j ^ (4 : ℕ) + (13 / 2) * h ^ (3 : ℕ) * j ^ (3 : ℕ) + (17 / 4) * h ^ (4 : ℕ) * j ^ (2 : ℕ) + h ^ (5 : ℕ) * j + (1 / 2) * h * j ^ (6 : ℕ) + 2 * h ^ (2 : ℕ) * j ^ (5 : ℕ) + 3 * h ^ (3 : ℕ) * j ^ (4 : ℕ) + 2 * h ^ (4 : ℕ) * j ^ (3 : ℕ) + (1 / 2) * h ^ (5 : ℕ) * j ^ (2 : ℕ)

/-- The coefficient of `y^0` in `𝒰(t, x, q)` at `t = (1 - h)/2`, `x = h + j`, `q = 1 + y`. -/
noncomputable def lrhYU0 (h j : ℝ) : ℝ :=
  -(25 / 4) * j - (25 / 4) * h - 9 * j ^ (2 : ℕ) - (85 / 4) * h * j - (49 / 4) * h ^ (2 : ℕ) - 3 * j ^ (3 : ℕ) - 12 * h * j ^ (2 : ℕ) - (47 / 4) * h ^ (2 : ℕ) * j - (11 / 4) * h ^ (3 : ℕ) + 6 * h ^ (2 : ℕ) * j ^ (2 : ℕ) + (49 / 4) * h ^ (3 : ℕ) * j + (25 / 4) * h ^ (4 : ℕ) + 3 * h ^ (2 : ℕ) * j ^ (3 : ℕ) + 9 * h ^ (3 : ℕ) * j ^ (2 : ℕ) + 9 * h ^ (4 : ℕ) * j + 3 * h ^ (5 : ℕ)

/-- The coefficient of `y^1` in `𝒰(t, x, q)` at `t = (1 - h)/2`, `x = h + j`, `q = 1 + y`. -/
noncomputable def lrhYU1 (h j : ℝ) : ℝ :=
  (1 / 4) - (93 / 4) * j - (93 / 4) * h - (183 / 4) * j ^ (2 : ℕ) - (197 / 2) * h * j - 53 * h ^ (2 : ℕ) - (141 / 4) * j ^ (3 : ℕ) - (399 / 4) * h * j ^ (2 : ℕ) - (177 / 2) * h ^ (2 : ℕ) * j - 24 * h ^ (3 : ℕ) - 15 * j ^ (4 : ℕ) - 36 * h * j ^ (3 : ℕ) - (33 / 4) * h ^ (2 : ℕ) * j ^ (2 : ℕ) + (65 / 2) * h ^ (3 : ℕ) * j + (79 / 4) * h ^ (4 : ℕ) - 3 * j ^ (5 : ℕ) + (141 / 4) * h ^ (2 : ℕ) * j ^ (3 : ℕ) + (303 / 4) * h ^ (3 : ℕ) * j ^ (2 : ℕ) + (243 / 4) * h ^ (4 : ℕ) * j + (69 / 4) * h ^ (5 : ℕ) + 3 * h * j ^ (5 : ℕ) + 15 * h ^ (2 : ℕ) * j ^ (4 : ℕ) + 30 * h ^ (3 : ℕ) * j ^ (3 : ℕ) + 30 * h ^ (4 : ℕ) * j ^ (2 : ℕ) + 15 * h ^ (5 : ℕ) * j + 3 * h ^ (6 : ℕ)

/-- The coefficient of `y^2` in `𝒰(t, x, q)` at `t = (1 - h)/2`, `x = h + j`, `q = 1 + y`. -/
noncomputable def lrhYU2 (h j : ℝ) : ℝ :=
  1 - (49 / 2) * j - (51 / 2) * h - (115 / 2) * j ^ (2 : ℕ) - (249 / 2) * h * j - 67 * h ^ (2 : ℕ) - (109 / 2) * j ^ (3 : ℕ) - (305 / 2) * h * j ^ (2 : ℕ) - 139 * h ^ (2 : ℕ) * j - 41 * h ^ (3 : ℕ) - 26 * j ^ (4 : ℕ) - 66 * h * j ^ (3 : ℕ) - (75 / 2) * h ^ (2 : ℕ) * j ^ (2 : ℕ) + (41 / 2) * h ^ (3 : ℕ) * j + 18 * h ^ (4 : ℕ) - 5 * j ^ (5 : ℕ) + (109 / 2) * h ^ (2 : ℕ) * j ^ (3 : ℕ) + (227 / 2) * h ^ (3 : ℕ) * j ^ (2 : ℕ) + (177 / 2) * h ^ (4 : ℕ) * j + (49 / 2) * h ^ (5 : ℕ) + 5 * h * j ^ (5 : ℕ) + 26 * h ^ (2 : ℕ) * j ^ (4 : ℕ) + 54 * h ^ (3 : ℕ) * j ^ (3 : ℕ) + 56 * h ^ (4 : ℕ) * j ^ (2 : ℕ) + 29 * h ^ (5 : ℕ) * j + 6 * h ^ (6 : ℕ)

/-- The coefficient of `y^3` in `𝒰(t, x, q)` at `t = (1 - h)/2`, `x = h + j`, `q = 1 + y`. -/
noncomputable def lrhYU3 (h j : ℝ) : ℝ :=
  (1 / 2) - (17 / 2) * j - 9 * h - (47 / 2) * j ^ (2 : ℕ) - (101 / 2) * h * j - 27 * h ^ (2 : ℕ) - (53 / 2) * j ^ (3 : ℕ) - (145 / 2) * h * j ^ (2 : ℕ) - (133 / 2) * h ^ (2 : ℕ) * j - (41 / 2) * h ^ (3 : ℕ) - (27 / 2) * j ^ (4 : ℕ) - 35 * h * j ^ (3 : ℕ) - (51 / 2) * h ^ (2 : ℕ) * j ^ (2 : ℕ) + h ^ (3 : ℕ) * j + 5 * h ^ (4 : ℕ) - (5 / 2) * j ^ (5 : ℕ) + (53 / 2) * h ^ (2 : ℕ) * j ^ (3 : ℕ) + (109 / 2) * h ^ (3 : ℕ) * j ^ (2 : ℕ) + 42 * h ^ (4 : ℕ) * j + (23 / 2) * h ^ (5 : ℕ) + (5 / 2) * h * j ^ (5 : ℕ) + (27 / 2) * h ^ (2 : ℕ) * j ^ (4 : ℕ) + 29 * h ^ (3 : ℕ) * j ^ (3 : ℕ) + 31 * h ^ (4 : ℕ) * j ^ (2 : ℕ) + (33 / 2) * h ^ (5 : ℕ) * j + (7 / 2) * h ^ (6 : ℕ)

/-- The coefficient of `y^4` in `𝒰(t, x, q)` at `t = (1 - h)/2`, `x = h + j`, `q = 1 + y`. -/
noncomputable def lrhYU4 (h j : ℝ) : ℝ :=
  (1 / 2) * j + (1 / 2) * h + (3 / 4) * j ^ (2 : ℕ) + (5 / 4) * h * j + (1 / 2) * h ^ (2 : ℕ) - (1 / 4) * j ^ (3 : ℕ) - (3 / 4) * h * j ^ (2 : ℕ) - (5 / 4) * h ^ (2 : ℕ) * j - (3 / 4) * h ^ (3 : ℕ) - (1 / 4) * j ^ (4 : ℕ) - h * j ^ (3 : ℕ) - (9 / 4) * h ^ (2 : ℕ) * j ^ (2 : ℕ) - (9 / 4) * h ^ (3 : ℕ) * j - (3 / 4) * h ^ (4 : ℕ) + (1 / 4) * h ^ (2 : ℕ) * j ^ (3 : ℕ) + (3 / 4) * h ^ (3 : ℕ) * j ^ (2 : ℕ) + (3 / 4) * h ^ (4 : ℕ) * j + (1 / 4) * h ^ (5 : ℕ) + (1 / 4) * h ^ (2 : ℕ) * j ^ (4 : ℕ) + h ^ (3 : ℕ) * j ^ (3 : ℕ) + (3 / 2) * h ^ (4 : ℕ) * j ^ (2 : ℕ) + h ^ (5 : ℕ) * j + (1 / 4) * h ^ (6 : ℕ)

/-- The coefficient of `y^0` in `𝒱(t, x, q)` at `t = (1 - h)/2`, `x = h + j`, `q = 1 + y`. -/
noncomputable def lrhYV0 (h j : ℝ) : ℝ :=
  1080 + 2880 * j + 2880 * h + 2532 * j ^ (2 : ℕ) + 4974 * h * j + 2802 * h ^ (2 : ℕ) + 749 * j ^ (3 : ℕ) + 2217 * h * j ^ (2 : ℕ) + 2787 * h ^ (2 : ℕ) * j + 1319 * h ^ (3 : ℕ) + 21 * j ^ (4 : ℕ) - 22 * h * j ^ (3 : ℕ) + 522 * h ^ (2 : ℕ) * j ^ (2 : ℕ) + 924 * h ^ (3 : ℕ) * j + 359 * h ^ (4 : ℕ) - 57 * h * j ^ (4 : ℕ) + 51 * h ^ (2 : ℕ) * j ^ (3 : ℕ) + 315 * h ^ (3 : ℕ) * j ^ (2 : ℕ) + 249 * h ^ (4 : ℕ) * j + 42 * h ^ (5 : ℕ) + 18 * h ^ (2 : ℕ) * j ^ (4 : ℕ) + 54 * h ^ (3 : ℕ) * j ^ (3 : ℕ) + 54 * h ^ (4 : ℕ) * j ^ (2 : ℕ) + 18 * h ^ (5 : ℕ) * j

/-- The coefficient of `y^1` in `𝒱(t, x, q)` at `t = (1 - h)/2`, `x = h + j`, `q = 1 + y`. -/
noncomputable def lrhYV1 (h j : ℝ) : ℝ :=
  540 + 1170 * j + 1440 * h + 96 * j ^ (2 : ℕ) + 1947 * h * j + 1491 * h ^ (2 : ℕ) - (1597 / 2) * j ^ (3 : ℕ) - (285 / 2) * h * j ^ (2 : ℕ) + (2481 / 2) * h ^ (2 : ℕ) * j + (1709 / 2) * h ^ (3 : ℕ) - (807 / 2) * j ^ (4 : ℕ) - 734 * h * j ^ (3 : ℕ) + 633 * h ^ (3 : ℕ) * j + (605 / 2) * h ^ (4 : ℕ) - 36 * j ^ (5 : ℕ) - (237 / 2) * h * j ^ (4 : ℕ) - (57 / 2) * h ^ (2 : ℕ) * j ^ (3 : ℕ) + (387 / 2) * h ^ (3 : ℕ) * j ^ (2 : ℕ) + (357 / 2) * h ^ (4 : ℕ) * j + 39 * h ^ (5 : ℕ) + 9 * h ^ (2 : ℕ) * j ^ (4 : ℕ) + 27 * h ^ (3 : ℕ) * j ^ (3 : ℕ) + 27 * h ^ (4 : ℕ) * j ^ (2 : ℕ) + 9 * h ^ (5 : ℕ) * j

/-- The coefficient of `y^2` in `𝒱(t, x, q)` at `t = (1 - h)/2`, `x = h + j`, `q = 1 + y`. -/
noncomputable def lrhYV2 (h j : ℝ) : ℝ :=
  -90 - 825 * j - 240 * h - 2001 * j ^ (2 : ℕ) - 1542 * h * j - 171 * h ^ (2 : ℕ) - (2937 / 2) * j ^ (3 : ℕ) - (4263 / 2) * h * j ^ (2 : ℕ) - (1545 / 2) * h ^ (2 : ℕ) * j + (51 / 2) * h ^ (3 : ℕ) - 393 * j ^ (4 : ℕ) - (1683 / 2) * h * j ^ (3 : ℕ) - (1077 / 2) * h ^ (2 : ℕ) * j ^ (2 : ℕ) - (69 / 2) * h ^ (3 : ℕ) * j + (111 / 2) * h ^ (4 : ℕ) - 30 * j ^ (5 : ℕ) - 87 * h * j ^ (4 : ℕ) - 81 * h ^ (2 : ℕ) * j ^ (3 : ℕ) - 12 * h ^ (3 : ℕ) * j ^ (2 : ℕ) + 21 * h ^ (4 : ℕ) * j + 9 * h ^ (5 : ℕ)

/-- The coefficient of `y^3` in `𝒱(t, x, q)` at `t = (1 - h)/2`, `x = h + j`, `q = 1 + y`. -/
noncomputable def lrhYV3 (h j : ℝ) : ℝ :=
  -90 - 465 * j - 240 * h - 726 * j ^ (2 : ℕ) - 807 * h * j - 216 * h ^ (2 : ℕ) - 327 * j ^ (3 : ℕ) - 636 * h * j ^ (2 : ℕ) - 381 * h ^ (2 : ℕ) * j - 72 * h ^ (3 : ℕ) - 30 * j ^ (4 : ℕ) - 87 * h * j ^ (3 : ℕ) - 90 * h ^ (2 : ℕ) * j ^ (2 : ℕ) - 39 * h ^ (3 : ℕ) * j - 6 * h ^ (4 : ℕ)

theorem lrh_T_y (h j y : ℝ) :
    fhComb 6 0 ((1 - h) / 2) (h + j) 1 (1 + y) 0 0 0 = lrhYT0 h j + lrhYT1 h j * y + lrhYT2 h j * y ^ (2 : ℕ) + lrhYT3 h j * y ^ (3 : ℕ) + lrhYT4 h j * y ^ (4 : ℕ) + lrhYT5 h j * y ^ (5 : ℕ) := by
  unfold fhComb fhTP fhKt fhHt fhE0 nhN lrhYT0 lrhYT1 lrhYT2 lrhYT3 lrhYT4 lrhYT5
  ring

theorem lrh_U_y (h j y : ℝ) :
    lrhCU ((1 - h) / 2) (h + j) (1 + y) = lrhYU0 h j + lrhYU1 h j * y + lrhYU2 h j * y ^ (2 : ℕ) + lrhYU3 h j * y ^ (3 : ℕ) + lrhYU4 h j * y ^ (4 : ℕ) := by
  unfold lrhCU lrhYU0 lrhYU1 lrhYU2 lrhYU3 lrhYU4
  ring

theorem lrh_V_y (h j y : ℝ) :
    lrhCV ((1 - h) / 2) (h + j) (1 + y) = lrhYV0 h j + lrhYV1 h j * y + lrhYV2 h j * y ^ (2 : ℕ) + lrhYV3 h j * y ^ (3 : ℕ) := by
  unfold lrhCV lrhYV0 lrhYV1 lrhYV2 lrhYV3
  ring

/-- The coefficient of `y^0` in the collection identity. -/
theorem lrh_coef0 (h j : ℝ) :
    96 * lrhWRx (h + j) * lrhYT0 h j + 4 * lrhYU0 h j * lrhYV0 h j =
      ((1 + h) ^ (3 : ℕ) * h ^ (3 : ℕ) * lrhB00 h / 2) +
      ((1 + h) ^ (2 : ℕ) * h ^ (2 : ℕ) * lrhB10 h / 2) * j +
      ((1 + h) ^ (2 : ℕ) * h * lrhB20 h / 2) * j ^ (2 : ℕ) +
      (2 * (h + 1) ^ (2 : ℕ) * lrhP30 h) * j ^ (3 : ℕ) +
      ((h + 1) ^ (2 : ℕ) * lrhP40 h) * j ^ (4 : ℕ) +
      (3 * (h + 1) ^ (2 : ℕ) * lrhP50 h) * j ^ (5 : ℕ) +
      (12 * (h + 1) ^ (2 : ℕ) * lrhP60 h) * j ^ (6 : ℕ) +
      (36 * (h + 1) ^ (2 : ℕ) * (1 - h) * lrhP70 h) * j ^ (7 : ℕ) := by
  unfold lrhWRx lrhYT0 lrhYU0 lrhYV0 lrhB00 lrhB10 lrhB20 lrhP30 lrhP40 lrhP50 lrhP60 lrhP70
  ring

/-- The coefficient of `y^1` in the collection identity. -/
theorem lrh_coef1 (h j : ℝ) :
    48 * lrhWRx (h + j) * lrhYT0 h j + 96 * lrhWRx (h + j) * lrhYT1 h j + 12 * lrhGtx ((1 - h) / 2) (h + j) * lrhSevx (h + j) - 12 * lrhGtx ((1 - h) / 2) (h + j) * lrhJtx ((1 - h) / 2) (h + j) + 4 * lrhYU0 h j * lrhYV1 h j + 4 * lrhYU1 h j * lrhYV0 h j =
      ((1 + h) ^ (3 : ℕ) * h ^ (2 : ℕ) * lrhB01 h / 2) +
      ((1 + h) ^ (2 : ℕ) * h * lrhB11 h / 2) * j +
      ((1 + h) ^ (2 : ℕ) * lrhB21 h / 2) * j ^ (2 : ℕ) +
      ((h + 1) * lrhP31 h) * j ^ (3 : ℕ) +
      ((h + 1) * lrhP41 h / 2) * j ^ (4 : ℕ) +
      (3 * (h + 1) * lrhP51 h / 2) * j ^ (5 : ℕ) +
      (6 * (h + 1) * lrhP61 h) * j ^ (6 : ℕ) +
      (3 * (h + 1) * lrhP71 h) * j ^ (7 : ℕ) +
      (24 * (h + 1) * (1 - h) * lrhP81 h) * j ^ (8 : ℕ) +
      (36 * (h + 1) * (1 - h) * lrhP91 h) * j ^ (9 : ℕ) := by
  unfold lrhWRx lrhGtx lrhSevx lrhJtx lrhYT0 lrhYT1 lrhYU0 lrhYU1 lrhYV0 lrhYV1 lrhB01 lrhB11 lrhB21 lrhP31 lrhP41 lrhP51 lrhP61 lrhP71 lrhP81 lrhP91
  ring

/-- The coefficient of `y^2` in the collection identity. -/
theorem lrh_coef2 (h j : ℝ) :
    48 * lrhWRx (h + j) * lrhYT1 h j + 96 * lrhWRx (h + j) * lrhYT2 h j + 24 * lrhGtx ((1 - h) / 2) (h + j) * lrhSevx (h + j) - 48 * lrhGtx ((1 - h) / 2) (h + j) * lrhJtx ((1 - h) / 2) (h + j) + 4 * lrhYU0 h j * lrhYV2 h j + 4 * lrhYU1 h j * lrhYV1 h j + 4 * lrhYU2 h j * lrhYV0 h j =
      ((1 + h) ^ (3 : ℕ) * h * lrhB02 h / 2) +
      ((1 + h) ^ (2 : ℕ) * (1080 * h ^ (9 : ℕ) + lrhB12 h) / 2) * j +
      ((1 + h) ^ (2 : ℕ) * lrhB22 h / 2) * j ^ (2 : ℕ) +
      ((h + 1) * lrhP32 h / 2) * j ^ (3 : ℕ) +
      ((h + 1) * lrhP42 h / 2) * j ^ (4 : ℕ) +
      (lrhP52 h / 2) * j ^ (5 : ℕ) +
      (lrhP62 h) * j ^ (6 : ℕ) +
      (lrhP72 h / 2) * j ^ (7 : ℕ) +
      (4 * lrhP82 h) * j ^ (8 : ℕ) +
      (6 * (1 - h) * lrhP92 h) * j ^ (9 : ℕ) +
      (432 * (1 - h)) * j ^ (10 : ℕ) := by
  unfold lrhWRx lrhGtx lrhSevx lrhJtx lrhYT1 lrhYT2 lrhYU0 lrhYU1 lrhYU2 lrhYV0 lrhYV1 lrhYV2 lrhB02 lrhB12 lrhB22 lrhP32 lrhP42 lrhP52 lrhP62 lrhP72 lrhP82 lrhP92
  ring

/-- The coefficient of `y^3` in the collection identity. -/
theorem lrh_coef3 (h j : ℝ) :
    48 * lrhWRx (h + j) * lrhYT2 h j + 96 * lrhWRx (h + j) * lrhYT3 h j + 13 * lrhGtx ((1 - h) / 2) (h + j) * lrhSevx (h + j) - 73 * lrhGtx ((1 - h) / 2) (h + j) * lrhJtx ((1 - h) / 2) (h + j) + 4 * lrhYU0 h j * lrhYV3 h j + 4 * lrhYU1 h j * lrhYV2 h j + 4 * lrhYU2 h j * lrhYV1 h j + 4 * lrhYU3 h j * lrhYV0 h j =
      ((1 + h) ^ (3 : ℕ) * lrhB03 h / 2) +
      ((1 + h) ^ (2 : ℕ) * (936 * h ^ (9 : ℕ) + lrhB13 h) / 2) * j +
      ((1 + h) ^ (2 : ℕ) * lrhB23 h / 2) * j ^ (2 : ℕ) +
      ((h + 1) * lrhP33 h / 2) * j ^ (3 : ℕ) +
      ((h + 1) * lrhP43 h / 2) * j ^ (4 : ℕ) +
      (lrhP53 h / 2) * j ^ (5 : ℕ) +
      (lrhP63 h / 2) * j ^ (6 : ℕ) +
      (4 * lrhP73 h) * j ^ (7 : ℕ) +
      (2 * lrhP83 h) * j ^ (8 : ℕ) +
      (24 * (1 - h) * lrhP93 h) * j ^ (9 : ℕ) +
      (1080 * (1 - h)) * j ^ (10 : ℕ) := by
  unfold lrhWRx lrhGtx lrhSevx lrhJtx lrhYT2 lrhYT3 lrhYU0 lrhYU1 lrhYU2 lrhYU3 lrhYV0 lrhYV1 lrhYV2 lrhYV3 lrhB03 lrhB13 lrhB23 lrhP33 lrhP43 lrhP53 lrhP63 lrhP73 lrhP83 lrhP93
  ring

/-- The coefficient of `y^4` in the collection identity. -/
theorem lrh_coef4 (h j : ℝ) :
    48 * lrhWRx (h + j) * lrhYT3 h j + 96 * lrhWRx (h + j) * lrhYT4 h j + lrhGtx ((1 - h) / 2) (h + j) * lrhSevx (h + j) - 51 * lrhGtx ((1 - h) / 2) (h + j) * lrhJtx ((1 - h) / 2) (h + j) + 4 * lrhYU1 h j * lrhYV3 h j + 4 * lrhYU2 h j * lrhYV2 h j + 4 * lrhYU3 h j * lrhYV1 h j + 4 * lrhYU4 h j * lrhYV0 h j =
      ((1 + h) ^ (3 : ℕ) * lrhB04 h / 2) +
      ((1 + h) ^ (2 : ℕ) * (288 * h ^ (9 : ℕ) + lrhB14 h) / 2) * j +
      ((1 + h) ^ (2 : ℕ) * lrhB24 h / 2) * j ^ (2 : ℕ) +
      ((h + 1) * lrhP34 h) * j ^ (3 : ℕ) +
      ((h + 1) * lrhP44 h) * j ^ (4 : ℕ) +
      (lrhP54 h) * j ^ (5 : ℕ) +
      (lrhP64 h) * j ^ (6 : ℕ) +
      (lrhP74 h) * j ^ (7 : ℕ) +
      (lrhP84 h) * j ^ (8 : ℕ) +
      ((1 - h) * lrhP94 h) * j ^ (9 : ℕ) +
      (960 * (1 - h)) * j ^ (10 : ℕ) := by
  unfold lrhWRx lrhGtx lrhSevx lrhJtx lrhYT3 lrhYT4 lrhYU1 lrhYU2 lrhYU3 lrhYU4 lrhYV0 lrhYV1 lrhYV2 lrhYV3 lrhB04 lrhB14 lrhB24 lrhP34 lrhP44 lrhP54 lrhP64 lrhP74 lrhP84 lrhP94
  ring

/-- The coefficient of `y^5` in the collection identity. -/
theorem lrh_coef5 (h j : ℝ) :
    48 * lrhWRx (h + j) * lrhYT4 h j + 96 * lrhWRx (h + j) * lrhYT5 h j - 15 * lrhGtx ((1 - h) / 2) (h + j) * lrhJtx ((1 - h) / 2) (h + j) + 4 * lrhYU2 h j * lrhYV3 h j + 4 * lrhYU3 h j * lrhYV2 h j + 4 * lrhYU4 h j * lrhYV1 h j =
      ((1 + h) ^ (3 : ℕ) * lrhB05 h / 2) +
      ((1 + h) ^ (2 : ℕ) * (18 * h ^ (9 : ℕ) + lrhB15 h) / 2) * j +
      ((1 + h) ^ (2 : ℕ) * lrhB25 h / 2) * j ^ (2 : ℕ) +
      ((h + 1) * lrhP35 h / 2) * j ^ (3 : ℕ) +
      ((h + 1) * lrhP45 h / 2) * j ^ (4 : ℕ) +
      (3 * lrhP55 h / 2) * j ^ (5 : ℕ) +
      (lrhP65 h / 2) * j ^ (6 : ℕ) +
      (lrhP75 h / 2) * j ^ (7 : ℕ) +
      (3 * lrhP85 h / 2) * j ^ (8 : ℕ) +
      (6 * (1 - h) * lrhP95 h) * j ^ (9 : ℕ) +
      (300 * (1 - h)) * j ^ (10 : ℕ) := by
  unfold lrhWRx lrhGtx lrhJtx lrhYT4 lrhYT5 lrhYU2 lrhYU3 lrhYU4 lrhYV1 lrhYV2 lrhYV3 lrhB05 lrhB15 lrhB25 lrhP35 lrhP45 lrhP55 lrhP65 lrhP75 lrhP85 lrhP95
  ring

/-- The coefficient of `y^6` in the collection identity. -/
theorem lrh_coef6 (h j : ℝ) :
    48 * lrhWRx (h + j) * lrhYT5 h j - lrhGtx ((1 - h) / 2) (h + j) * lrhJtx ((1 - h) / 2) (h + j) + 4 * lrhYU3 h j * lrhYV3 h j + 4 * lrhYU4 h j * lrhYV2 h j =
      ((1 + h) ^ (3 : ℕ) * lrhB06 h / 2) +
      ((1 + h) ^ (2 : ℕ) * lrhB16 h / 2) * j +
      ((1 + h) ^ (2 : ℕ) * lrhB26 h / 2) * j ^ (2 : ℕ) +
      ((h + 1) * lrhP36 h / 2) * j ^ (3 : ℕ) +
      ((h + 1) * lrhP46 h / 2) * j ^ (4 : ℕ) +
      (3 * lrhP56 h / 2) * j ^ (5 : ℕ) +
      (lrhP66 h / 2) * j ^ (6 : ℕ) +
      (lrhP76 h / 2) * j ^ (7 : ℕ) +
      ((1 - h) * lrhP86 h) * j ^ (8 : ℕ) +
      (2 * (1 - h) * lrhP96 h) * j ^ (9 : ℕ) := by
  unfold lrhWRx lrhGtx lrhJtx lrhYT5 lrhYU3 lrhYU4 lrhYV2 lrhYV3 lrhB06 lrhB16 lrhB26 lrhP36 lrhP46 lrhP56 lrhP66 lrhP76 lrhP86 lrhP96
  ring

/-- The coefficient of `y^7` in the collection identity. -/
theorem lrh_coef7 (h j : ℝ) :
    4 * lrhYU4 h j * lrhYV3 h j =
      ((1 + h) ^ (3 : ℕ) * h * lrhB07 h / 2) +
      ((1 + h) ^ (2 : ℕ) * lrhB17 h / 2) * j +
      ((1 + h) ^ (2 : ℕ) * lrhB27 h / 2) * j ^ (2 : ℕ) +
      (3 * (h + 1) * (1 - h) * lrhP37 h) * j ^ (3 : ℕ) +
      (3 * (h + 1) * (1 - h) * lrhP47 h) * j ^ (4 : ℕ) +
      (3 * (h + 1) * (1 - h) * lrhP57 h) * j ^ (5 : ℕ) +
      (3 * (h + 1) * (1 - h) * lrhP67 h) * j ^ (6 : ℕ) +
      (3 * (h + 1) * (1 - h) * lrhP77 h) * j ^ (7 : ℕ) +
      (30 * (h + 1) * (1 - h)) * j ^ (8 : ℕ) := by
  unfold lrhYU4 lrhYV3 lrhB07 lrhB17 lrhB27 lrhP37 lrhP47 lrhP57 lrhP67 lrhP77
  ring

/-- **The collection identity** `Π = ∑ C̃ᵢ jⁱ` (checked one power of `y` at a time). -/
theorem lrh_collect (h j y : ℝ) :
    lrhCP ((1 - h) / 2) (h + j) (1 + y) =
      lrhC0 h y + lrhC1 h y * j + lrhC2 h y * j ^ (2 : ℕ) + lrhC3 h y * j ^ (3 : ℕ) + lrhC4 h y * j ^ (4 : ℕ)
        + lrhC5 h y * j ^ (5 : ℕ) + lrhC6 h y * j ^ (6 : ℕ) + lrhC7 h y * j ^ (7 : ℕ) + lrhC8 h y * j ^ (8 : ℕ)
        + lrhC9 h y * j ^ (9 : ℕ) + lrhC10 h y * j ^ (10 : ℕ) := by
  unfold lrhCP lrhCK
  rw [lrh_T_y, lrh_U_y, lrh_V_y]
  have e0 := lrh_coef0 h j
  have e1 := lrh_coef1 h j
  have e2 := lrh_coef2 h j
  have e3 := lrh_coef3 h j
  have e4 := lrh_coef4 h j
  have e5 := lrh_coef5 h j
  have e6 := lrh_coef6 h j
  have e7 := lrh_coef7 h j
  unfold lrhC0 lrhC1 lrhC2 lrhC3 lrhC4 lrhC5 lrhC6 lrhC7 lrhC8 lrhC9 lrhC10
  linear_combination e0 + y * e1 + y ^ (2 : ℕ) * e2 + y ^ (3 : ℕ) * e3 + y ^ (4 : ℕ) * e4 + y ^ (5 : ℕ) * e5 + y ^ (6 : ℕ) * e6 + y ^ (7 : ℕ) * e7

/-- **The unit-shape residual is positive**, through the circuit `𝒫` and `lrh_sum_pos`: for
`1/4 ≤ t ≤ 1/3`, `2t + x ≥ 1`, `1 ≤ q ≤ 2 - 2t`. -/
theorem lrh_unit_pos {t x q : ℝ} (ht0 : 1 / 4 ≤ t) (ht1 : t ≤ 1 / 3) (hj : 1 ≤ 2 * t + x)
    (hq : 1 ≤ q) (hy : q - 1 ≤ 1 - 2 * t) :
    0 < fhComb 6 0 t x 1 q (fhVG t x + 3 / 4 * (q + 2 * t + x - 1) * (fhVG t x - nhFl t x q))
      (nhLp q) 0 := by
  have hx : 0 < x := by linarith
  have hq0 : 0 < q := by linarith
  have hP : 0 < lrhCP t x q := by
    have e : lrhCP t x q = lrhCP ((1 - (1 - 2 * t)) / 2) ((1 - 2 * t) + (2 * t + x - 1))
        (1 + (q - 1)) := by congr 1 <;> ring
    rw [e, lrh_collect]
    exact lrh_sum_pos (by linarith) (by linarith) (by linarith) hy (by linarith)
  rw [← lrh_link t x q hq0 hx] at hP
  have hpos : 0 ≤ 48 * (q + 1) * lrhWRx x := by unfold lrhWRx; positivity
  exact pos_of_mul_pos_right hP hpos

end SmoothedOctagon
