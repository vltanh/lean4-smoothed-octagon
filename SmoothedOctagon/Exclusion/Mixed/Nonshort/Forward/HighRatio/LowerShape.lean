module

public import SmoothedOctagon.Exclusion.Mixed.Nonshort.Forward.Clearing
public import SmoothedOctagon.Exclusion.Mixed.Nonshort.Forward.HighRatio.LowerShape.TerminalFace
public import SmoothedOctagon.Exclusion.Mixed.Nonshort.Forward.HighRatio.LowerShape.Scale

/-!
# The high-ratio lower-shape sign

At the lower shape `k₀ = 29t²/4`, the cleared residual is positive.
The incoming majorant `V_L ≥ V_G` gives a polynomial residual `S`.
Its negative scale derivative increases with scale and order gap, and its
corner value is at least `500`. Hence `S` decreases with scale and its
minimum lies on the terminal face `h = 1/4`, where `S ≥ 1`.
The negative incoming-norm coefficient transfers positivity back to `V_G`.

`hrlS` defines the cleared residual, `hrl_scale_link` identifies its duration
coefficients, and `hrl_lower_pos` gives the sign used by the large-gap exclusion.
-/

@[expose] public section
namespace SmoothedOctagon

/-! ### The circuit

At `k₀ = 29t²/4`, with `W = 1 + x`, `p = t + x`: the `v`-coefficient is
`nsfCv 4 1 t x k₀ q = 4W ∑ Aᵢ qⁱ`, the `log q`-coefficient satisfies
`(q - 1) nsfCL = -4q²pW(∑ Bᵢ qⁱ - 1)`, and the residual at `v = L = F = 0` is
`∑ Cᵢ qⁱ - 4qW² - 4p²q²`. -/

/-- The coefficient `A_0(t, x)` of `q^0` in the `v`-coefficient at `k₀`. -/
noncomputable def hrlA0 (t x : ℝ) : ℝ :=
  t * x + t ^ (2 : ℕ) + 4 * t * x ^ (2 : ℕ) + 4 * t ^ (2 : ℕ) * x + 6 * t * x ^ (3 : ℕ) + 6 * t ^ (2 : ℕ) * x ^ (2 : ℕ) + 4 * t * x ^ (4 : ℕ) + 4 * t ^ (2 : ℕ) * x ^ (3 : ℕ) + t * x ^ (5 : ℕ) + t ^ (2 : ℕ) * x ^ (4 : ℕ)

/-- The coefficient `A_1(t, x)` of `q^1` in the `v`-coefficient at `k₀`. -/
noncomputable def hrlA1 (t x : ℝ) : ℝ :=
  -1 - x - 2 * t * x - t ^ (2 : ℕ) - 7 * t * x ^ (2 : ℕ) - 3 * t ^ (2 : ℕ) * x - 9 * t * x ^ (3 : ℕ) - 3 * t ^ (2 : ℕ) * x ^ (2 : ℕ) - 5 * t * x ^ (4 : ℕ) - t ^ (2 : ℕ) * x ^ (3 : ℕ) - t * x ^ (5 : ℕ)

/-- The coefficient `A_2(t, x)` of `q^2` in the `v`-coefficient at `k₀`. -/
noncomputable def hrlA2 (t x : ℝ) : ℝ :=
  11 * t * x ^ (2 : ℕ) + 35 * t ^ (2 : ℕ) * x - (29 / 4) * t ^ (3 : ℕ) + 25 * t * x ^ (3 : ℕ) + 68 * t ^ (2 : ℕ) * x ^ (2 : ℕ) - (203 / 4) * t ^ (3 : ℕ) * x + 17 * t * x ^ (4 : ℕ) + 31 * t ^ (2 : ℕ) * x ^ (3 : ℕ) - (319 / 4) * t ^ (3 : ℕ) * x ^ (2 : ℕ) + 3 * t * x ^ (5 : ℕ) - 2 * t ^ (2 : ℕ) * x ^ (4 : ℕ) - (145 / 4) * t ^ (3 : ℕ) * x ^ (3 : ℕ)

/-- The coefficient `A_3(t, x)` of `q^3` in the `v`-coefficient at `k₀`. -/
noncomputable def hrlA3 (t x : ℝ) : ℝ :=
  -12 * t * x ^ (2 : ℕ) - 54 * t ^ (2 : ℕ) * x + (29 / 4) * t ^ (3 : ℕ) - 24 * t * x ^ (3 : ℕ) - 81 * t ^ (2 : ℕ) * x ^ (2 : ℕ) + (29 / 4) * t ^ (3 : ℕ) * x - 15 * t * x ^ (4 : ℕ) - 27 * t ^ (2 : ℕ) * x ^ (3 : ℕ) - 3 * t * x ^ (5 : ℕ)

/-- The coefficient `A_4(t, x)` of `q^4` in the `v`-coefficient at `k₀`. -/
noncomputable def hrlA4 (t x : ℝ) : ℝ :=
  -2 * t * x ^ (3 : ℕ) - 3 * t ^ (2 : ℕ) * x ^ (2 : ℕ) + (21 / 4) * t ^ (3 : ℕ) * x - t * x ^ (4 : ℕ) + t ^ (2 : ℕ) * x ^ (3 : ℕ) + (87 / 4) * t ^ (3 : ℕ) * x ^ (2 : ℕ) + (29 / 4) * t ^ (4 : ℕ) * x + t ^ (2 : ℕ) * x ^ (4 : ℕ) + (29 / 4) * t ^ (3 : ℕ) * x ^ (3 : ℕ)

/-- The coefficient `B_0(t, x)` of `q^0` in the `log q`-coefficient at `k₀`. -/
noncomputable def hrlBs0 (t x : ℝ) : ℝ :=
  1 - 5 * t * x ^ (2 : ℕ) - 10 * t ^ (2 : ℕ) * x - (145 / 4) * t ^ (3 : ℕ) - 10 * t * x ^ (3 : ℕ) - 20 * t ^ (2 : ℕ) * x ^ (2 : ℕ) - (145 / 2) * t ^ (3 : ℕ) * x - 5 * t * x ^ (4 : ℕ) - 10 * t ^ (2 : ℕ) * x ^ (3 : ℕ) - (145 / 4) * t ^ (3 : ℕ) * x ^ (2 : ℕ)

/-- The coefficient `B_1(t, x)` of `q^1` in the `log q`-coefficient at `k₀`. -/
noncomputable def hrlBs1 (t x : ℝ) : ℝ :=
  5 * t * x ^ (2 : ℕ) + 10 * t ^ (2 : ℕ) * x + (145 / 4) * t ^ (3 : ℕ) + 10 * t * x ^ (3 : ℕ) + 20 * t ^ (2 : ℕ) * x ^ (2 : ℕ) + (145 / 2) * t ^ (3 : ℕ) * x + 5 * t * x ^ (4 : ℕ) + 10 * t ^ (2 : ℕ) * x ^ (3 : ℕ) + (145 / 4) * t ^ (3 : ℕ) * x ^ (2 : ℕ)

/-- The coefficient `B_2(t, x)` of `q^2` in the `log q`-coefficient at `k₀`. -/
noncomputable def hrlBs2 (t x : ℝ) : ℝ :=
  2 * t * x ^ (3 : ℕ) + 5 * t ^ (2 : ℕ) * x ^ (2 : ℕ) + (33 / 2) * t ^ (3 : ℕ) * x + (29 / 4) * t ^ (4 : ℕ) + t * x ^ (4 : ℕ) + 2 * t ^ (2 : ℕ) * x ^ (3 : ℕ) + (29 / 4) * t ^ (3 : ℕ) * x ^ (2 : ℕ)

/-- The coefficient `B_3(t, x)` of `q^3` in the `log q`-coefficient at `k₀`. -/
noncomputable def hrlBs3 (t x : ℝ) : ℝ :=
  -2 * t * x ^ (3 : ℕ) - 5 * t ^ (2 : ℕ) * x ^ (2 : ℕ) - (33 / 2) * t ^ (3 : ℕ) * x - (29 / 4) * t ^ (4 : ℕ) - t * x ^ (4 : ℕ) - 2 * t ^ (2 : ℕ) * x ^ (3 : ℕ) - (29 / 4) * t ^ (3 : ℕ) * x ^ (2 : ℕ)

/-- The coefficient `C_0(t, x)` of `q^0` in the residual at `k₀`, `v = L = F = 0`. -/
noncomputable def hrlCs0 (t x : ℝ) : ℝ :=
  -3 * t * x - 3 * t ^ (2 : ℕ) - 15 * t * x ^ (2 : ℕ) - 15 * t ^ (2 : ℕ) * x - 30 * t * x ^ (3 : ℕ) - 30 * t ^ (2 : ℕ) * x ^ (2 : ℕ) - 30 * t * x ^ (4 : ℕ) - 30 * t ^ (2 : ℕ) * x ^ (3 : ℕ) - 15 * t * x ^ (5 : ℕ) - 15 * t ^ (2 : ℕ) * x ^ (4 : ℕ) - 3 * t * x ^ (6 : ℕ) - 3 * t ^ (2 : ℕ) * x ^ (5 : ℕ)

/-- The coefficient `C_1(t, x)` of `q^1` in the residual at `k₀`, `v = L = F = 0`. -/
noncomputable def hrlCs1 (t x : ℝ) : ℝ :=
  4 + 8 * x + 4 * x ^ (2 : ℕ) + 6 * t * x + 3 * t ^ (2 : ℕ) + 19 * t * x ^ (2 : ℕ) - 4 * t ^ (2 : ℕ) * x - 8 * t ^ (3 : ℕ) + 16 * t * x ^ (3 : ℕ) - 46 * t ^ (2 : ℕ) * x ^ (2 : ℕ) - 32 * t ^ (3 : ℕ) * x - 6 * t * x ^ (4 : ℕ) - 84 * t ^ (2 : ℕ) * x ^ (3 : ℕ) - 48 * t ^ (3 : ℕ) * x ^ (2 : ℕ) - 14 * t * x ^ (5 : ℕ) - 61 * t ^ (2 : ℕ) * x ^ (4 : ℕ) - 32 * t ^ (3 : ℕ) * x ^ (3 : ℕ) - 5 * t * x ^ (6 : ℕ) - 16 * t ^ (2 : ℕ) * x ^ (5 : ℕ) - 8 * t ^ (3 : ℕ) * x ^ (4 : ℕ)

/-- The coefficient `C_2(t, x)` of `q^2` in the residual at `k₀`, `v = L = F = 0`. -/
noncomputable def hrlCs2 (t x : ℝ) : ℝ :=
  4 * x ^ (2 : ℕ) + 8 * t * x + 4 * t ^ (2 : ℕ) - 4 * t * x ^ (2 : ℕ) - 80 * t ^ (2 : ℕ) * x + 49 * t ^ (3 : ℕ) - 22 * t * x ^ (3 : ℕ) - 266 * t ^ (2 : ℕ) * x ^ (2 : ℕ) + (119 / 2) * t ^ (3 : ℕ) * x - (393 / 2) * t ^ (4 : ℕ) - 62 * t * x ^ (4 : ℕ) - 398 * t ^ (2 : ℕ) * x ^ (3 : ℕ) - (721 / 2) * t ^ (3 : ℕ) * x ^ (2 : ℕ) - (1607 / 2) * t ^ (4 : ℕ) * x - 29 * t ^ (5 : ℕ) - 74 * t * x ^ (5 : ℕ) - 318 * t ^ (2 : ℕ) * x ^ (4 : ℕ) - (1407 / 2) * t ^ (3 : ℕ) * x ^ (3 : ℕ) - (1803 / 2) * t ^ (4 : ℕ) * x ^ (2 : ℕ) + 58 * t ^ (5 : ℕ) * x - 30 * t * x ^ (6 : ℕ) - 106 * t ^ (2 : ℕ) * x ^ (5 : ℕ) - (665 / 2) * t ^ (3 : ℕ) * x ^ (4 : ℕ) - (357 / 2) * t ^ (4 : ℕ) * x ^ (3 : ℕ) + 203 * t ^ (5 : ℕ) * x ^ (2 : ℕ) + 116 * t ^ (4 : ℕ) * x ^ (4 : ℕ) + 116 * t ^ (5 : ℕ) * x ^ (3 : ℕ)

/-- The coefficient `C_3(t, x)` of `q^3` in the residual at `k₀`, `v = L = F = 0`. -/
noncomputable def hrlCs3 (t x : ℝ) : ℝ :=
  168 * t ^ (2 : ℕ) * x - 41 * t ^ (3 : ℕ) + 44 * t * x ^ (3 : ℕ) + 530 * t ^ (2 : ℕ) * x ^ (2 : ℕ) + 113 * t ^ (3 : ℕ) * x + (401 / 2) * t ^ (4 : ℕ) + 142 * t * x ^ (4 : ℕ) + 728 * t ^ (2 : ℕ) * x ^ (3 : ℕ) + (1883 / 2) * t ^ (3 : ℕ) * x ^ (2 : ℕ) + 947 * t ^ (4 : ℕ) * x + 116 * t ^ (5 : ℕ) + 152 * t * x ^ (5 : ℕ) + 538 * t ^ (2 : ℕ) * x ^ (4 : ℕ) + 1380 * t ^ (3 : ℕ) * x ^ (3 : ℕ) + (2353 / 2) * t ^ (4 : ℕ) * x ^ (2 : ℕ) + 232 * t ^ (5 : ℕ) * x + 54 * t * x ^ (6 : ℕ) + 172 * t ^ (2 : ℕ) * x ^ (5 : ℕ) + (1185 / 2) * t ^ (3 : ℕ) * x ^ (4 : ℕ) + 314 * t ^ (4 : ℕ) * x ^ (3 : ℕ) + 116 * t ^ (5 : ℕ) * x ^ (2 : ℕ) - 116 * t ^ (4 : ℕ) * x ^ (4 : ℕ)

/-- The coefficient `C_4(t, x)` of `q^4` in the residual at `k₀`, `v = L = F = 0`. -/
noncomputable def hrlCs4 (t x : ℝ) : ℝ :=
  -8 * t * x ^ (3 : ℕ) - 20 * t ^ (2 : ℕ) * x ^ (2 : ℕ) - 41 * t ^ (3 : ℕ) * x - 4 * t ^ (4 : ℕ) - 44 * t * x ^ (4 : ℕ) - 132 * t ^ (2 : ℕ) * x ^ (3 : ℕ) - 344 * t ^ (3 : ℕ) * x ^ (2 : ℕ) - 268 * t ^ (4 : ℕ) * x - 87 * t ^ (5 : ℕ) - 47 * t * x ^ (5 : ℕ) - 135 * t ^ (2 : ℕ) * x ^ (4 : ℕ) - (743 / 2) * t ^ (3 : ℕ) * x ^ (3 : ℕ) - (575 / 2) * t ^ (4 : ℕ) * x ^ (2 : ℕ) - (423 / 16) * t ^ (5 : ℕ) * x + (841 / 16) * t ^ (6 : ℕ) - 15 * t * x ^ (6 : ℕ) - 43 * t ^ (2 : ℕ) * x ^ (5 : ℕ) - (267 / 2) * t ^ (3 : ℕ) * x ^ (4 : ℕ) - (277 / 2) * t ^ (4 : ℕ) * x ^ (3 : ℕ) - (551 / 16) * t ^ (5 : ℕ) * x ^ (2 : ℕ) + (377 / 16) * t ^ (6 : ℕ) * x

/-- The coefficient `C_5(t, x)` of `q^5` in the residual at `k₀`, `v = L = F = 0`. -/
noncomputable def hrlCs5 (t x : ℝ) : ℝ :=
  -2 * t * x ^ (5 : ℕ) - 9 * t ^ (2 : ℕ) * x ^ (4 : ℕ) - 41 * t ^ (3 : ℕ) * x ^ (3 : ℕ) - (153 / 2) * t ^ (4 : ℕ) * x ^ (2 : ℕ) - (1073 / 8) * t ^ (5 : ℕ) * x - (841 / 16) * t ^ (6 : ℕ) - t * x ^ (6 : ℕ) - 4 * t ^ (2 : ℕ) * x ^ (5 : ℕ) - (37 / 2) * t ^ (3 : ℕ) * x ^ (4 : ℕ) - 29 * t ^ (4 : ℕ) * x ^ (3 : ℕ) - (841 / 16) * t ^ (5 : ℕ) * x ^ (2 : ℕ)

/-- `V_n = 24DW²V_L`. -/
noncomputable def hrlVn (t x : ℝ) : ℝ :=
  1824 + 3144 * x - 1824 * t + 1831 * x ^ (2 : ℕ) - 1320 * t * x + 1824 * t ^ (2 : ℕ) + 408 * x ^ (3 : ℕ) + 401 * t * x ^ (2 : ℕ) + 2232 * t ^ (2 : ℕ) * x + 408 * t ^ (2 : ℕ) * x ^ (2 : ℕ)

/-- The incoming majorant `V_L` with `T_L = (912 - 401x)/(24(17x + 76))`. -/
noncomputable def hrlVL (t x : ℝ) : ℝ :=
  1 - (1 - t) * (t + x) / (1 + x) ^ (2 : ℕ) + (1 - t) * x / (1 + x) ^ (2 : ℕ) * ((912 - 401 * x) / (24 * (17 * x + 76)) - t)

/-- **The circuit** `S = 24WD(q + 1)C + 4(q + 1)AV_n - 16W²DpqB(q² + 10q + 1)`. -/
noncomputable def hrlS (t x q : ℝ) : ℝ :=
  24 * (1 + x) * (17 * x + 76) * (q + 1) * (hrlCs0 t x * q ^ (0 : ℕ) + hrlCs1 t x * q ^ (1 : ℕ) + hrlCs2 t x * q ^ (2 : ℕ) + hrlCs3 t x * q ^ (3 : ℕ) + hrlCs4 t x * q ^ (4 : ℕ) + hrlCs5 t x * q ^ (5 : ℕ)) + 4 * (q + 1) * (hrlA0 t x * q ^ (0 : ℕ) + hrlA1 t x * q ^ (1 : ℕ) + hrlA2 t x * q ^ (2 : ℕ) + hrlA3 t x * q ^ (3 : ℕ) + hrlA4 t x * q ^ (4 : ℕ)) * hrlVn t x
    - 16 * (1 + x) ^ (2 : ℕ) * (17 * x + 76) * (t + x) * q * (hrlBs0 t x * q ^ (0 : ℕ) + hrlBs1 t x * q ^ (1 : ℕ) + hrlBs2 t x * q ^ (2 : ℕ) + hrlBs3 t x * q ^ (3 : ℕ)) * (q ^ (2 : ℕ) + 10 * q + 1)

/-- `V_G ≤ V_L` for `x ≥ 0`, `t ≤ 1`. -/
theorem hrl_VG_le_VL {t x : ℝ} (hx : 0 ≤ x) (ht : t ≤ 1) : nsfVG t x ≤ hrlVL t x := by
  have hW : 0 < 1 + x := by linarith
  have e : hrlVL t x - nsfVG t x = (1 - t) * x / (1 + x) ^ (2 : ℕ) *
      (5 * x * (7 * x - 3) ^ (2 : ℕ) / (24 * (17 * x + 76) * (x ^ (2 : ℕ) + 10 * x + 15))) := by
    unfold hrlVL nsfVG; field_simp; ring
  have : 0 ≤ hrlVL t x - nsfVG t x := by
    rw [e]; apply mul_nonneg (div_nonneg (mul_nonneg (by linarith) hx) (by positivity)); positivity
  linarith

/-- **The link**: clearing the denominators of `V_L`, `L₊` and `F_ℓ`,
`24(q + 1)WD · nsfComb 4 1 t x (29t²/4) q V_L L₊ F_ℓ = S`. -/
theorem hrl_link (t x q : ℝ) (hq : 0 < q) (hx : 0 < x) :
    24 * (q + 1) * (1 + x) * (17 * x + 76) *
        nsfComb 4 1 t x (29 / 4 * t ^ (2 : ℕ)) q (hrlVL t x) (nsrLp q) (nsrFl t x q) = hrlS t x q := by
  have hW : (1 : ℝ) + x ≠ 0 := by positivity
  have hD : (17 : ℝ) * x + 76 ≠ 0 := by positivity
  have hq1 : q + 1 ≠ 0 := by positivity
  have hq0 : q ≠ 0 := hq.ne'
  have hA : nsfCv 4 1 t x (29 / 4 * t ^ (2 : ℕ)) q = 4 * (1 + x) * (hrlA0 t x * q ^ (0 : ℕ) + hrlA1 t x * q ^ (1 : ℕ) + hrlA2 t x * q ^ (2 : ℕ) + hrlA3 t x * q ^ (3 : ℕ) + hrlA4 t x * q ^ (4 : ℕ)) := by
    unfold nsfCv nsrNv nsfTPv hrlA0 hrlA1 hrlA2 hrlA3 hrlA4; ring
  have hC : nsfComb 4 1 t x (29 / 4 * t ^ (2 : ℕ)) q 0 0 0 =
      (hrlCs0 t x * q ^ (0 : ℕ) + hrlCs1 t x * q ^ (1 : ℕ) + hrlCs2 t x * q ^ (2 : ℕ) + hrlCs3 t x * q ^ (3 : ℕ) + hrlCs4 t x * q ^ (4 : ℕ) + hrlCs5 t x * q ^ (5 : ℕ)) - 4 * q * (1 + x) ^ (2 : ℕ) - 4 * (t + x) ^ (2 : ℕ) * q ^ (2 : ℕ) := by
    unfold nsfComb nsfTP nsfKt nsfHt nsfE0 nsrN hrlCs0 hrlCs1 hrlCs2 hrlCs3 hrlCs4 hrlCs5; ring
  have hB : nsfCL 4 t x (29 / 4 * t ^ (2 : ℕ)) q * (q - 1) =
      -4 * q ^ (2 : ℕ) * (t + x) * (1 + x) * ((hrlBs0 t x * q ^ (0 : ℕ) + hrlBs1 t x * q ^ (1 : ℕ) + hrlBs2 t x * q ^ (2 : ℕ) + hrlBs3 t x * q ^ (3 : ℕ)) - 1) := by
    unfold nsfCL nsrNL hrlBs0 hrlBs1 hrlBs2 hrlBs3; ring
  have hV : hrlVL t x = hrlVn t x / (24 * (17 * x + 76) * (1 + x) ^ (2 : ℕ)) := by
    unfold hrlVL hrlVn; field_simp; ring
  rw [nsf_comb_dec, hA, hC, hV]
  have hL : nsrLp q * nsfCL 4 t x (29 / 4 * t ^ (2 : ℕ)) q =
      (q ^ (2 : ℕ) + 10 * q + 1) / (6 * q * (q + 1)) * (nsfCL 4 t x (29 / 4 * t ^ (2 : ℕ)) q * (q - 1)) := by
    unfold nsrLp; field_simp
  rw [hL, hB]
  unfold nsrFl hrlS
  field_simp
  ring

/-- The coefficient of `y^0` in `S(t, x, 1 + y)`. -/
noncomputable def hrlSt0 (t x : ℝ) : ℝ :=
  -7296 * x - 4088 * x ^ (2 : ℕ) + 18240 * t * x + 3208 * x ^ (3 : ℕ) - 48184 * t * x ^ (2 : ℕ) - 10944 * t ^ (2 : ℕ) * x - 171120 * t * x ^ (3 : ℕ) + 329520 * t ^ (2 : ℕ) * x ^ (2 : ℕ) + 52896 * t ^ (3 : ℕ) * x - 162464 * t * x ^ (4 : ℕ) + 732920 * t ^ (2 : ℕ) * x ^ (3 : ℕ) - 371208 * t ^ (3 : ℕ) * x ^ (2 : ℕ) - 52896 * t ^ (4 : ℕ) * x - 71648 * t * x ^ (5 : ℕ) + 493512 * t ^ (2 : ℕ) * x ^ (4 : ℕ) - 841302 * t ^ (3 : ℕ) * x ^ (3 : ℕ) + 41064 * t ^ (4 : ℕ) * x ^ (2 : ℕ) - 191748 * t ^ (5 : ℕ) * x - 13056 * t * x ^ (6 : ℕ) + 130464 * t ^ (2 : ℕ) * x ^ (5 : ℕ) - 359832 * t ^ (3 : ℕ) * x ^ (4 : ℕ) + 229372 * t ^ (4 : ℕ) * x ^ (3 : ℕ) - 181743 * t ^ (5 : ℕ) * x ^ (2 : ℕ) + 191748 * t ^ (6 : ℕ) * x + 26112 * t ^ (2 : ℕ) * x ^ (6 : ℕ) + 34216 * t ^ (3 : ℕ) * x ^ (5 : ℕ) + 28784 * t ^ (4 : ℕ) * x ^ (4 : ℕ) + 4031 * t ^ (5 : ℕ) * x ^ (3 : ℕ) + 234639 * t ^ (6 : ℕ) * x ^ (2 : ℕ) - 13056 * t ^ (3 : ℕ) * x ^ (6 : ℕ) - 93032 * t ^ (4 : ℕ) * x ^ (5 : ℕ) + 42891 * t ^ (6 : ℕ) * x ^ (3 : ℕ)

/-- The coefficient of `y^1` in `S(t, x, 1 + y)`. -/
noncomputable def hrlSt1 (t x : ℝ) : ℝ :=
  -18240 * x - 7296 * t - 7764 * x ^ (2 : ℕ) + 36672 * t * x + 10944 * t ^ (2 : ℕ) + 12108 * x ^ (3 : ℕ) - 266820 * t * x ^ (2 : ℕ) - 130704 * t ^ (2 : ℕ) * x + 1632 * x ^ (4 : ℕ) - 963488 * t * x ^ (3 : ℕ) + 994672 * t ^ (2 : ℕ) * x ^ (2 : ℕ) + 852720 * t ^ (3 : ℕ) * x + 52896 * t ^ (4 : ℕ) - 1178968 * t * x ^ (4 : ℕ) + 2897188 * t ^ (2 : ℕ) * x ^ (3 : ℕ) + 907770 * t ^ (3 : ℕ) * x ^ (2 : ℕ) - 663960 * t ^ (4 : ℕ) * x - 715960 * t * x ^ (5 : ℕ) + 2581004 * t ^ (2 : ℕ) * x ^ (4 : ℕ) - 338341 * t ^ (3 : ℕ) * x ^ (3 : ℕ) - 2210938 * t ^ (4 : ℕ) * x ^ (2 : ℕ) - 1140570 * t ^ (5 : ℕ) * x - 191748 * t ^ (6 : ℕ) - 199264 * t * x ^ (6 : ℕ) + 1118488 * t ^ (2 : ℕ) * x ^ (5 : ℕ) + 148848 * t ^ (3 : ℕ) * x ^ (4 : ℕ) - 2477200 * t ^ (4 : ℕ) * x ^ (3 : ℕ) - (1852491 / 2) * t ^ (5 : ℕ) * x ^ (2 : ℕ) + 628227 * t ^ (6 : ℕ) * x - 13280 * t * x ^ (7 : ℕ) + 309856 * t ^ (2 : ℕ) * x ^ (6 : ℕ) + 493936 * t ^ (3 : ℕ) * x ^ (5 : ℕ) - 1893436 * t ^ (4 : ℕ) * x ^ (4 : ℕ) + (901581 / 2) * t ^ (5 : ℕ) * x ^ (3 : ℕ) + (2025969 / 2) * t ^ (6 : ℕ) * x ^ (2 : ℕ) + 26336 * t ^ (2 : ℕ) * x ^ (7 : ℕ) - 15936 * t ^ (3 : ℕ) * x ^ (6 : ℕ) - 943792 * t ^ (4 : ℕ) * x ^ (5 : ℕ) + 310677 * t ^ (5 : ℕ) * x ^ (4 : ℕ) + (386019 / 2) * t ^ (6 : ℕ) * x ^ (3 : ℕ) - 13056 * t ^ (3 : ℕ) * x ^ (7 : ℕ) - 94656 * t ^ (4 : ℕ) * x ^ (6 : ℕ) + 47328 * t ^ (5 : ℕ) * x ^ (5 : ℕ)

/-- The coefficient of `y^2` in `S(t, x, 1 + y)`. -/
noncomputable def hrlSt2 (t x : ℝ) : ℝ :=
  -12160 * x - 8512 * t + 916 * x ^ (2 : ℕ) + 32144 * t * x + 20064 * t ^ (2 : ℕ) + 16068 * x ^ (3 : ℕ) - 472084 * t * x ^ (2 : ℕ) - 351192 * t ^ (2 : ℕ) * x - 58368 * t ^ (3 : ℕ) + 2992 * x ^ (4 : ℕ) - 1824372 * t * x ^ (3 : ℕ) + 729068 * t ^ (2 : ℕ) * x ^ (2 : ℕ) + 1881168 * t ^ (3 : ℕ) * x + 411312 * t ^ (4 : ℕ) - 2616956 * t * x ^ (4 : ℕ) + 3351148 * t ^ (2 : ℕ) * x ^ (3 : ℕ) + 4256987 * t ^ (3 : ℕ) * x ^ (2 : ℕ) - 597468 * t ^ (4 : ℕ) * x - 158688 * t ^ (5 : ℕ) - 1916140 * t * x ^ (5 : ℕ) + 3464980 * t ^ (2 : ℕ) * x ^ (4 : ℕ) + 3226511 * t ^ (3 : ℕ) * x ^ (3 : ℕ) - 5497459 * t ^ (4 : ℕ) * x ^ (2 : ℕ) - 3665484 * t ^ (5 : ℕ) * x - 862866 * t ^ (6 : ℕ) - 705664 * t * x ^ (6 : ℕ) + 1701740 * t ^ (2 : ℕ) * x ^ (5 : ℕ) + 2046912 * t ^ (3 : ℕ) * x ^ (4 : ℕ) - 7792559 * t ^ (4 : ℕ) * x ^ (3 : ℕ) - 3665049 * t ^ (5 : ℕ) * x ^ (2 : ℕ) + (956217 / 2) * t ^ (6 : ℕ) * x - 107968 * t * x ^ (7 : ℕ) + 520416 * t ^ (2 : ℕ) * x ^ (6 : ℕ) + 1150668 * t ^ (3 : ℕ) * x ^ (5 : ℕ) - 5108660 * t ^ (4 : ℕ) * x ^ (4 : ℕ) + (944675 / 2) * t ^ (5 : ℕ) * x ^ (3 : ℕ) + (3368205 / 2) * t ^ (6 : ℕ) * x ^ (2 : ℕ) - 6528 * t * x ^ (8 : ℕ) + 59200 * t ^ (2 : ℕ) * x ^ (7 : ℕ) + 67456 * t ^ (3 : ℕ) * x ^ (6 : ℕ) - 1919596 * t ^ (4 : ℕ) * x ^ (5 : ℕ) + (1640733 / 2) * t ^ (5 : ℕ) * x ^ (4 : ℕ) + 343128 * t ^ (6 : ℕ) * x ^ (3 : ℕ) - 26112 * t ^ (3 : ℕ) * x ^ (7 : ℕ) - 223584 * t ^ (4 : ℕ) * x ^ (6 : ℕ) + 141984 * t ^ (5 : ℕ) * x ^ (5 : ℕ)

/-- The coefficient of `y^3` in `S(t, x, 1 + y)`. -/
noncomputable def hrlSt3 (t x : ℝ) : ℝ :=
  -1216 * x - 1216 * t + 4592 * x ^ (2 : ℕ) + 11888 * t * x + 7296 * t ^ (2 : ℕ) + 7168 * x ^ (3 : ℕ) - 348704 * t * x ^ (2 : ℕ) - 319392 * t ^ (2 : ℕ) * x - 72960 * t ^ (3 : ℕ) + 1360 * x ^ (4 : ℕ) - 1441744 * t * x ^ (3 : ℕ) - 64512 * t ^ (2 : ℕ) * x ^ (2 : ℕ) + 1522528 * t ^ (3 : ℕ) * x + 583376 * t ^ (4 : ℕ) - 2338652 * t * x ^ (4 : ℕ) + 1180764 * t ^ (2 : ℕ) * x ^ (3 : ℕ) + 4256740 * t ^ (3 : ℕ) * x ^ (2 : ℕ) + 131708 * t ^ (4 : ℕ) * x - 361456 * t ^ (5 : ℕ) - 1987108 * t * x ^ (5 : ℕ) + 1262248 * t ^ (2 : ℕ) * x ^ (4 : ℕ) + 3298124 * t ^ (3 : ℕ) * x ^ (3 : ℕ) - 5846604 * t ^ (4 : ℕ) * x ^ (2 : ℕ) - 5901616 * t ^ (5 : ℕ) * x - 1533984 * t ^ (6 : ℕ) - 905232 * t * x ^ (6 : ℕ) + 468764 * t ^ (2 : ℕ) * x ^ (5 : ℕ) + 982713 * t ^ (3 : ℕ) * x ^ (4 : ℕ) - 9328274 * t ^ (4 : ℕ) * x ^ (3 : ℕ) - 7078697 * t ^ (5 : ℕ) * x ^ (2 : ℕ) - 534876 * t ^ (6 : ℕ) * x - 200016 * t * x ^ (7 : ℕ) + 121952 * t ^ (2 : ℕ) * x ^ (6 : ℕ) + 300039 * t ^ (3 : ℕ) * x ^ (5 : ℕ) - 5392077 * t ^ (4 : ℕ) * x ^ (4 : ℕ) - 1046523 * t ^ (5 : ℕ) * x ^ (3 : ℕ) + 1299345 * t ^ (6 : ℕ) * x ^ (2 : ℕ) - 17408 * t * x ^ (8 : ℕ) + 19920 * t ^ (2 : ℕ) * x ^ (7 : ℕ) + 5272 * t ^ (3 : ℕ) * x ^ (6 : ℕ) - 1533295 * t ^ (4 : ℕ) * x ^ (5 : ℕ) + 687648 * t ^ (5 : ℕ) * x ^ (4 : ℕ) + 300237 * t ^ (6 : ℕ) * x ^ (3 : ℕ) - 19584 * t ^ (3 : ℕ) * x ^ (7 : ℕ) - 169728 * t ^ (4 : ℕ) * x ^ (6 : ℕ) + 153816 * t ^ (5 : ℕ) * x ^ (5 : ℕ)

/-- The coefficient of `y^4` in `S(t, x, 1 + y)`. -/
noncomputable def hrlSt4 (t x : ℝ) : ℝ :=
  -87552 * t * x ^ (2 : ℕ) - 87552 * t ^ (2 : ℕ) * x - 21888 * t ^ (3 : ℕ) - 426944 * t * x ^ (3 : ℕ) - 209280 * t ^ (2 : ℕ) * x ^ (2 : ℕ) + 377536 * t ^ (3 : ℕ) * x + 224960 * t ^ (4 : ℕ) - 826944 * t * x ^ (4 : ℕ) - 243720 * t ^ (2 : ℕ) * x ^ (3 : ℕ) + 1147199 * t ^ (3 : ℕ) * x ^ (2 : ℕ) + 77376 * t ^ (4 : ℕ) * x - 238032 * t ^ (5 : ℕ) - 857344 * t * x ^ (5 : ℕ) - 483876 * t ^ (2 : ℕ) * x ^ (4 : ℕ) + 20593 * t ^ (3 : ℕ) * x ^ (3 : ℕ) - 3576067 * t ^ (4 : ℕ) * x ^ (2 : ℕ) - 4635360 * t ^ (5 : ℕ) * x - 1342236 * t ^ (6 : ℕ) - 496700 * t * x ^ (6 : ℕ) - 558060 * t ^ (2 : ℕ) * x ^ (5 : ℕ) - 1353182 * t ^ (3 : ℕ) * x ^ (4 : ℕ) - 5764587 * t ^ (4 : ℕ) * x ^ (3 : ℕ) - 6340995 * t ^ (5 : ℕ) * x ^ (2 : ℕ) - 1067229 * t ^ (6 : ℕ) * x - 144612 * t * x ^ (7 : ℕ) - 231276 * t ^ (2 : ℕ) * x ^ (6 : ℕ) - 752118 * t ^ (3 : ℕ) * x ^ (5 : ℕ) - 2866062 * t ^ (4 : ℕ) * x ^ (4 : ℕ) - 1897122 * t ^ (5 : ℕ) * x ^ (3 : ℕ) + 403680 * t ^ (6 : ℕ) * x ^ (2 : ℕ) - 15232 * t * x ^ (8 : ℕ) - 25212 * t ^ (2 : ℕ) * x ^ (7 : ℕ) - 100732 * t ^ (3 : ℕ) * x ^ (6 : ℕ) - 526706 * t ^ (4 : ℕ) * x ^ (5 : ℕ) + 135459 * t ^ (5 : ℕ) * x ^ (4 : ℕ) + 128673 * t ^ (6 : ℕ) * x ^ (3 : ℕ) - 4896 * t ^ (3 : ℕ) * x ^ (7 : ℕ) - 37536 * t ^ (4 : ℕ) * x ^ (6 : ℕ) + 70992 * t ^ (5 : ℕ) * x ^ (5 : ℕ)

/-- The coefficient of `y^5` in `S(t, x, 1 + y)`. -/
noncomputable def hrlSt5 (t x : ℝ) : ℝ :=
  -29184 * t * x ^ (3 : ℕ) - 58368 * t ^ (2 : ℕ) * x ^ (2 : ℕ) - 36480 * t ^ (3 : ℕ) * x - 7296 * t ^ (4 : ℕ) - 94080 * t * x ^ (4 : ℕ) - 173568 * t ^ (2 : ℕ) * x ^ (3 : ℕ) - 80208 * t ^ (3 : ℕ) * x ^ (2 : ℕ) - 49968 * t ^ (4 : ℕ) * x - 26448 * t ^ (5 : ℕ) - 140600 * t * x ^ (5 : ℕ) - 309540 * t ^ (2 : ℕ) * x ^ (4 : ℕ) - 586053 * t ^ (3 : ℕ) * x ^ (3 : ℕ) - 1122540 * t ^ (4 : ℕ) * x ^ (2 : ℕ) - 1675446 * t ^ (5 : ℕ) * x - 575244 * t ^ (6 : ℕ) - 111460 * t * x ^ (6 : ℕ) - 301740 * t ^ (2 : ℕ) * x ^ (5 : ℕ) - 930555 * t ^ (3 : ℕ) * x ^ (4 : ℕ) - 1773820 * t ^ (4 : ℕ) * x ^ (3 : ℕ) - (5130651 / 2) * t ^ (5 : ℕ) * x ^ (2 : ℕ) - 608043 * t ^ (6 : ℕ) * x - 41064 * t * x ^ (7 : ℕ) - 124144 * t ^ (2 : ℕ) * x ^ (6 : ℕ) - 451037 * t ^ (3 : ℕ) * x ^ (5 : ℕ) - 789945 * t ^ (4 : ℕ) * x ^ (4 : ℕ) - (1990183 / 2) * t ^ (5 : ℕ) * x ^ (3 : ℕ) - (22707 / 2) * t ^ (6 : ℕ) * x ^ (2 : ℕ) - 4896 * t * x ^ (8 : ℕ) - 15096 * t ^ (2 : ℕ) * x ^ (7 : ℕ) - 57760 * t ^ (3 : ℕ) * x ^ (6 : ℕ) - 87563 * t ^ (4 : ℕ) * x ^ (5 : ℕ) - 63945 * t ^ (5 : ℕ) * x ^ (4 : ℕ) + (42891 / 2) * t ^ (6 : ℕ) * x ^ (3 : ℕ) + 1632 * t ^ (4 : ℕ) * x ^ (6 : ℕ) + 11832 * t ^ (5 : ℕ) * x ^ (5 : ℕ)

/-- The coefficient of `y^6` in `S(t, x, 1 + y)`. -/
noncomputable def hrlSt6 (t x : ℝ) : ℝ :=
  2432 * t * x ^ (4 : ℕ) + 8512 * t ^ (2 : ℕ) * x ^ (3 : ℕ) + 26144 * t ^ (3 : ℕ) * x ^ (2 : ℕ) + 28880 * t ^ (4 : ℕ) * x + 8816 * t ^ (5 : ℕ) + 2976 * t * x ^ (5 : ℕ) + 6160 * t ^ (2 : ℕ) * x ^ (4 : ℕ) - 5400 * t ^ (3 : ℕ) * x ^ (3 : ℕ) - 66500 * t ^ (4 : ℕ) * x ^ (2 : ℕ) - 225040 * t ^ (5 : ℕ) * x - 95874 * t ^ (6 : ℕ) - 64 * t * x ^ (6 : ℕ) - 6952 * t ^ (2 : ℕ) * x ^ (5 : ℕ) - 62404 * t ^ (3 : ℕ) * x ^ (4 : ℕ) - 162240 * t ^ (4 : ℕ) * x ^ (3 : ℕ) - 382481 * t ^ (5 : ℕ) * x ^ (2 : ℕ) - (234639 / 2) * t ^ (6 : ℕ) * x - 744 * t * x ^ (7 : ℕ) - 5416 * t ^ (2 : ℕ) * x ^ (6 : ℕ) - 35892 * t ^ (3 : ℕ) * x ^ (5 : ℕ) - 76720 * t ^ (4 : ℕ) * x ^ (4 : ℕ) - (340141 / 2) * t ^ (5 : ℕ) * x ^ (3 : ℕ) - (42891 / 2) * t ^ (6 : ℕ) * x ^ (2 : ℕ) - 136 * t * x ^ (8 : ℕ) - 816 * t ^ (2 : ℕ) * x ^ (7 : ℕ) - 5032 * t ^ (3 : ℕ) * x ^ (6 : ℕ) - 9860 * t ^ (4 : ℕ) * x ^ (5 : ℕ) - (42891 / 2) * t ^ (5 : ℕ) * x ^ (4 : ℕ)

/-- The `y`-split of the circuit, one power of `y` at a time. -/
theorem hrl_S_split (t x y : ℝ) :
    hrlS t x (1 + y) = hrlSt0 t x * y ^ (0 : ℕ) + hrlSt1 t x * y ^ (1 : ℕ) + hrlSt2 t x * y ^ (2 : ℕ) + hrlSt3 t x * y ^ (3 : ℕ) + hrlSt4 t x * y ^ (4 : ℕ) + hrlSt5 t x * y ^ (5 : ℕ) + hrlSt6 t x * y ^ (6 : ℕ) := by
  have e0 : hrlSt0 t x = (8) * hrlA0 t x * hrlVn t x + (8) * hrlA1 t x * hrlVn t x + (8) * hrlA2 t x * hrlVn t x + (8) * hrlA3 t x * hrlVn t x + (8) * hrlA4 t x * hrlVn t x + (-14592 * x - 14592 * t - 32448 * x ^ (2 : ℕ) - 32448 * t * x - 21120 * x ^ (3 : ℕ) - 21120 * t * x ^ (2 : ℕ) - 3264 * x ^ (4 : ℕ) - 3264 * t * x ^ (3 : ℕ)) * hrlBs0 t x + (-14592 * x - 14592 * t - 32448 * x ^ (2 : ℕ) - 32448 * t * x - 21120 * x ^ (3 : ℕ) - 21120 * t * x ^ (2 : ℕ) - 3264 * x ^ (4 : ℕ) - 3264 * t * x ^ (3 : ℕ)) * hrlBs1 t x + (-14592 * x - 14592 * t - 32448 * x ^ (2 : ℕ) - 32448 * t * x - 21120 * x ^ (3 : ℕ) - 21120 * t * x ^ (2 : ℕ) - 3264 * x ^ (4 : ℕ) - 3264 * t * x ^ (3 : ℕ)) * hrlBs2 t x + (-14592 * x - 14592 * t - 32448 * x ^ (2 : ℕ) - 32448 * t * x - 21120 * x ^ (3 : ℕ) - 21120 * t * x ^ (2 : ℕ) - 3264 * x ^ (4 : ℕ) - 3264 * t * x ^ (3 : ℕ)) * hrlBs3 t x + (3648 + 4464 * x + 816 * x ^ (2 : ℕ)) * hrlCs0 t x + (3648 + 4464 * x + 816 * x ^ (2 : ℕ)) * hrlCs1 t x + (3648 + 4464 * x + 816 * x ^ (2 : ℕ)) * hrlCs2 t x + (3648 + 4464 * x + 816 * x ^ (2 : ℕ)) * hrlCs3 t x + (3648 + 4464 * x + 816 * x ^ (2 : ℕ)) * hrlCs4 t x + (3648 + 4464 * x + 816 * x ^ (2 : ℕ)) * hrlCs5 t x := by
    simp only [hrlSt0, hrlA0, hrlA1, hrlA2, hrlA3, hrlA4, hrlBs0, hrlBs1, hrlBs2, hrlBs3, hrlCs0, hrlCs1, hrlCs2, hrlCs3, hrlCs4, hrlCs5, hrlVn]; ring
  have e1 : hrlSt1 t x = (4) * hrlA0 t x * hrlVn t x + (12) * hrlA1 t x * hrlVn t x + (20) * hrlA2 t x * hrlVn t x + (28) * hrlA3 t x * hrlVn t x + (36) * hrlA4 t x * hrlVn t x + (-29184 * x - 29184 * t - 64896 * x ^ (2 : ℕ) - 64896 * t * x - 42240 * x ^ (3 : ℕ) - 42240 * t * x ^ (2 : ℕ) - 6528 * x ^ (4 : ℕ) - 6528 * t * x ^ (3 : ℕ)) * hrlBs0 t x + (-43776 * x - 43776 * t - 97344 * x ^ (2 : ℕ) - 97344 * t * x - 63360 * x ^ (3 : ℕ) - 63360 * t * x ^ (2 : ℕ) - 9792 * x ^ (4 : ℕ) - 9792 * t * x ^ (3 : ℕ)) * hrlBs1 t x + (-58368 * x - 58368 * t - 129792 * x ^ (2 : ℕ) - 129792 * t * x - 84480 * x ^ (3 : ℕ) - 84480 * t * x ^ (2 : ℕ) - 13056 * x ^ (4 : ℕ) - 13056 * t * x ^ (3 : ℕ)) * hrlBs2 t x + (-72960 * x - 72960 * t - 162240 * x ^ (2 : ℕ) - 162240 * t * x - 105600 * x ^ (3 : ℕ) - 105600 * t * x ^ (2 : ℕ) - 16320 * x ^ (4 : ℕ) - 16320 * t * x ^ (3 : ℕ)) * hrlBs3 t x + (1824 + 2232 * x + 408 * x ^ (2 : ℕ)) * hrlCs0 t x + (5472 + 6696 * x + 1224 * x ^ (2 : ℕ)) * hrlCs1 t x + (9120 + 11160 * x + 2040 * x ^ (2 : ℕ)) * hrlCs2 t x + (12768 + 15624 * x + 2856 * x ^ (2 : ℕ)) * hrlCs3 t x + (16416 + 20088 * x + 3672 * x ^ (2 : ℕ)) * hrlCs4 t x + (20064 + 24552 * x + 4488 * x ^ (2 : ℕ)) * hrlCs5 t x := by
    simp only [hrlSt1, hrlA0, hrlA1, hrlA2, hrlA3, hrlA4, hrlBs0, hrlBs1, hrlBs2, hrlBs3, hrlCs0, hrlCs1, hrlCs2, hrlCs3, hrlCs4, hrlCs5, hrlVn]; ring
  have e2 : hrlSt2 t x = (4) * hrlA1 t x * hrlVn t x + (16) * hrlA2 t x * hrlVn t x + (36) * hrlA3 t x * hrlVn t x + (64) * hrlA4 t x * hrlVn t x + (-15808 * x - 15808 * t - 35152 * x ^ (2 : ℕ) - 35152 * t * x - 22880 * x ^ (3 : ℕ) - 22880 * t * x ^ (2 : ℕ) - 3536 * x ^ (4 : ℕ) - 3536 * t * x ^ (3 : ℕ)) * hrlBs0 t x + (-44992 * x - 44992 * t - 100048 * x ^ (2 : ℕ) - 100048 * t * x - 65120 * x ^ (3 : ℕ) - 65120 * t * x ^ (2 : ℕ) - 10064 * x ^ (4 : ℕ) - 10064 * t * x ^ (3 : ℕ)) * hrlBs1 t x + (-88768 * x - 88768 * t - 197392 * x ^ (2 : ℕ) - 197392 * t * x - 128480 * x ^ (3 : ℕ) - 128480 * t * x ^ (2 : ℕ) - 19856 * x ^ (4 : ℕ) - 19856 * t * x ^ (3 : ℕ)) * hrlBs2 t x + (-147136 * x - 147136 * t - 327184 * x ^ (2 : ℕ) - 327184 * t * x - 212960 * x ^ (3 : ℕ) - 212960 * t * x ^ (2 : ℕ) - 32912 * x ^ (4 : ℕ) - 32912 * t * x ^ (3 : ℕ)) * hrlBs3 t x + (1824 + 2232 * x + 408 * x ^ (2 : ℕ)) * hrlCs1 t x + (7296 + 8928 * x + 1632 * x ^ (2 : ℕ)) * hrlCs2 t x + (16416 + 20088 * x + 3672 * x ^ (2 : ℕ)) * hrlCs3 t x + (29184 + 35712 * x + 6528 * x ^ (2 : ℕ)) * hrlCs4 t x + (45600 + 55800 * x + 10200 * x ^ (2 : ℕ)) * hrlCs5 t x := by
    simp only [hrlSt2, hrlA1, hrlA2, hrlA3, hrlA4, hrlBs0, hrlBs1, hrlBs2, hrlBs3, hrlCs1, hrlCs2, hrlCs3, hrlCs4, hrlCs5, hrlVn]; ring
  have e3 : hrlSt3 t x = (4) * hrlA2 t x * hrlVn t x + (20) * hrlA3 t x * hrlVn t x + (56) * hrlA4 t x * hrlVn t x + (-1216 * x - 1216 * t - 2704 * x ^ (2 : ℕ) - 2704 * t * x - 1760 * x ^ (3 : ℕ) - 1760 * t * x ^ (2 : ℕ) - 272 * x ^ (4 : ℕ) - 272 * t * x ^ (3 : ℕ)) * hrlBs0 t x + (-17024 * x - 17024 * t - 37856 * x ^ (2 : ℕ) - 37856 * t * x - 24640 * x ^ (3 : ℕ) - 24640 * t * x ^ (2 : ℕ) - 3808 * x ^ (4 : ℕ) - 3808 * t * x ^ (3 : ℕ)) * hrlBs1 t x + (-62016 * x - 62016 * t - 137904 * x ^ (2 : ℕ) - 137904 * t * x - 89760 * x ^ (3 : ℕ) - 89760 * t * x ^ (2 : ℕ) - 13872 * x ^ (4 : ℕ) - 13872 * t * x ^ (3 : ℕ)) * hrlBs2 t x + (-150784 * x - 150784 * t - 335296 * x ^ (2 : ℕ) - 335296 * t * x - 218240 * x ^ (3 : ℕ) - 218240 * t * x ^ (2 : ℕ) - 33728 * x ^ (4 : ℕ) - 33728 * t * x ^ (3 : ℕ)) * hrlBs3 t x + (1824 + 2232 * x + 408 * x ^ (2 : ℕ)) * hrlCs2 t x + (9120 + 11160 * x + 2040 * x ^ (2 : ℕ)) * hrlCs3 t x + (25536 + 31248 * x + 5712 * x ^ (2 : ℕ)) * hrlCs4 t x + (54720 + 66960 * x + 12240 * x ^ (2 : ℕ)) * hrlCs5 t x := by
    simp only [hrlSt3, hrlA2, hrlA3, hrlA4, hrlBs0, hrlBs1, hrlBs2, hrlBs3, hrlCs2, hrlCs3, hrlCs4, hrlCs5, hrlVn]; ring
  have e4 : hrlSt4 t x = (4) * hrlA3 t x * hrlVn t x + (24) * hrlA4 t x * hrlVn t x + (-1216 * x - 1216 * t - 2704 * x ^ (2 : ℕ) - 2704 * t * x - 1760 * x ^ (3 : ℕ) - 1760 * t * x ^ (2 : ℕ) - 272 * x ^ (4 : ℕ) - 272 * t * x ^ (3 : ℕ)) * hrlBs1 t x + (-18240 * x - 18240 * t - 40560 * x ^ (2 : ℕ) - 40560 * t * x - 26400 * x ^ (3 : ℕ) - 26400 * t * x ^ (2 : ℕ) - 4080 * x ^ (4 : ℕ) - 4080 * t * x ^ (3 : ℕ)) * hrlBs2 t x + (-80256 * x - 80256 * t - 178464 * x ^ (2 : ℕ) - 178464 * t * x - 116160 * x ^ (3 : ℕ) - 116160 * t * x ^ (2 : ℕ) - 17952 * x ^ (4 : ℕ) - 17952 * t * x ^ (3 : ℕ)) * hrlBs3 t x + (1824 + 2232 * x + 408 * x ^ (2 : ℕ)) * hrlCs3 t x + (10944 + 13392 * x + 2448 * x ^ (2 : ℕ)) * hrlCs4 t x + (36480 + 44640 * x + 8160 * x ^ (2 : ℕ)) * hrlCs5 t x := by
    simp only [hrlSt4, hrlA3, hrlA4, hrlBs1, hrlBs2, hrlBs3, hrlCs3, hrlCs4, hrlCs5, hrlVn]; ring
  have e5 : hrlSt5 t x = (4) * hrlA4 t x * hrlVn t x + (-1216 * x - 1216 * t - 2704 * x ^ (2 : ℕ) - 2704 * t * x - 1760 * x ^ (3 : ℕ) - 1760 * t * x ^ (2 : ℕ) - 272 * x ^ (4 : ℕ) - 272 * t * x ^ (3 : ℕ)) * hrlBs2 t x + (-19456 * x - 19456 * t - 43264 * x ^ (2 : ℕ) - 43264 * t * x - 28160 * x ^ (3 : ℕ) - 28160 * t * x ^ (2 : ℕ) - 4352 * x ^ (4 : ℕ) - 4352 * t * x ^ (3 : ℕ)) * hrlBs3 t x + (1824 + 2232 * x + 408 * x ^ (2 : ℕ)) * hrlCs4 t x + (12768 + 15624 * x + 2856 * x ^ (2 : ℕ)) * hrlCs5 t x := by
    simp only [hrlSt5, hrlA4, hrlBs2, hrlBs3, hrlCs4, hrlCs5, hrlVn]; ring
  have e6 : hrlSt6 t x = (-1216 * x - 1216 * t - 2704 * x ^ (2 : ℕ) - 2704 * t * x - 1760 * x ^ (3 : ℕ) - 1760 * t * x ^ (2 : ℕ) - 272 * x ^ (4 : ℕ) - 272 * t * x ^ (3 : ℕ)) * hrlBs3 t x + (1824 + 2232 * x + 408 * x ^ (2 : ℕ)) * hrlCs5 t x := by
    simp only [hrlSt6, hrlBs3, hrlCs5]; ring
  unfold hrlS
  rw [e0, e1, e2, e3, e4, e5, e6]
  ring

theorem hrl_St_face0 (x : ℝ) : hrlSt0 (3 / 8) x = hrlCF0 x := by
  unfold hrlSt0 hrlCF0; ring

theorem hrl_St_face1 (x : ℝ) : hrlSt1 (3 / 8) x = hrlCF1 x := by
  unfold hrlSt1 hrlCF1; ring

theorem hrl_St_face2 (x : ℝ) : hrlSt2 (3 / 8) x = hrlCF2 x := by
  unfold hrlSt2 hrlCF2; ring

theorem hrl_St_face3 (x : ℝ) : hrlSt3 (3 / 8) x = hrlCF3 x := by
  unfold hrlSt3 hrlCF3; ring

theorem hrl_St_face4 (x : ℝ) : hrlSt4 (3 / 8) x = hrlCF4 x := by
  unfold hrlSt4 hrlCF4; ring

theorem hrl_St_face5 (x : ℝ) : hrlSt5 (3 / 8) x = hrlCF5 x := by
  unfold hrlSt5 hrlCF5; ring

theorem hrl_St_face6 (x : ℝ) : hrlSt6 (3 / 8) x = hrlCF6 x := by
  unfold hrlSt6 hrlCF6; ring

private theorem scale_row0_link (h j : ℝ) :
    128 * hrlSt0 ((1 - h) / 2) (h + j) = HighRatioScale.row0 h j := by
  unfold hrlSt0 HighRatioScale.row0
  ring

private theorem scale_row1_link (h j : ℝ) :
    128 * hrlSt1 ((1 - h) / 2) (h + j) = HighRatioScale.row1 h j := by
  unfold hrlSt1 HighRatioScale.row1
  ring

private theorem scale_row2_link (h j : ℝ) :
    128 * hrlSt2 ((1 - h) / 2) (h + j) = HighRatioScale.row2 h j := by
  unfold hrlSt2 HighRatioScale.row2
  ring

private theorem scale_row3_link (h j : ℝ) :
    128 * hrlSt3 ((1 - h) / 2) (h + j) = HighRatioScale.row3 h j := by
  unfold hrlSt3 HighRatioScale.row3
  ring

private theorem scale_row4_link (h j : ℝ) :
    128 * hrlSt4 ((1 - h) / 2) (h + j) = HighRatioScale.row4 h j := by
  unfold hrlSt4 HighRatioScale.row4
  ring

private theorem scale_row5_link (h j : ℝ) :
    128 * hrlSt5 ((1 - h) / 2) (h + j) = HighRatioScale.row5 h j := by
  unfold hrlSt5 HighRatioScale.row5
  ring

private theorem scale_row6_link (h j : ℝ) :
    128 * hrlSt6 ((1 - h) / 2) (h + j) = HighRatioScale.row6 h j := by
  unfold hrlSt6 HighRatioScale.row6
  ring

theorem hrl_scale_link (h j y : ℝ) :
    128 * hrlS ((1 - h) / 2) (h + j) (1 + y) = HighRatioScale.value h j y := by
  rw [hrl_S_split]
  unfold HighRatioScale.value
  linear_combination scale_row0_link h j + y * scale_row1_link h j +
    y ^ 2 * scale_row2_link h j + y ^ 3 * scale_row3_link h j +
    y ^ 4 * scale_row4_link h j + y ^ 5 * scale_row5_link h j + y ^ 6 * scale_row6_link h j

theorem hrl_h_reduce {h j y : ℝ} (h0 : 1 / 5 ≤ h) (h1 : h ≤ 1 / 4)
    (j0 : 1 / 30 ≤ j) (j1 : j ≤ 5 / 28) (y0 : 0 ≤ y) (y1 : y ≤ 1 / 4) :
    hrlS (3 / 8) (1 / 4 + j) (1 + y) ≤ hrlS ((1 - h) / 2) (h + j) (1 + y) := by
  have he0 := hrl_scale_link (1 / 4) j y
  have he1 := hrl_scale_link h j y
  have hm := HighRatioScale.scale_reduce h0 h1 j0 (by linarith only [j1]) y0 y1
  norm_num only at he0
  linarith only [he0, he1, hm]

private theorem hrl_face_link (x y : ℝ) : hrlS (3 / 8) x (1 + y) = hrlP x y := by
  rw [hrl_S_split, hrl_St_face0, hrl_St_face1, hrl_St_face2, hrl_St_face3, hrl_St_face4,
    hrl_St_face5, hrl_St_face6]
  unfold hrlP
  ring

/-- **The high-ratio lower-shape sign**: on the high-ratio
large-gap domain, the combined residual at `k₀ = 29t²/4` with `v_G`, `L₊`, `F_ℓ` is positive. The
negative `v`-coefficient (`nsf_LGB_Cv`) is supplied by the caller. -/
theorem hrl_lower_pos {t x q : ℝ} (ht0 : 3 / 8 ≤ t) (ht1 : t < 2 / 5) (hj : 1 / 30 ≤ 2 * t + x - 1)
    (hjh : 7 * x < 12 * (1 - 2 * t)) (hq : 1 ≤ q) (hqs : q * (4 * t + 2 * x - 1) ≤ 1 + x)
    (hCv : nsfCv 4 1 t x (29 / 4 * t ^ (2 : ℕ)) q < 0) :
    0 < nsfComb 4 1 t x (29 / 4 * t ^ (2 : ℕ)) q (nsfVG t x) (nsrLp q) (nsrFl t x q) := by
  have hx : 0 < x := by linarith
  have hq0 : 0 < q := by linarith
  -- `y(1 + 2j) ≤ h - j`
  have hy : (q - 1) * (1 + 2 * (2 * t + x - 1)) ≤ (1 - 2 * t) - (2 * t + x - 1) := by nlinarith
  have hy1 : q - 1 ≤ 1 / 4 := by nlinarith
  have hS : 0 < hrlS t x q := by
    have red := hrl_h_reduce (h := 1 - 2 * t) (j := 2 * t + x - 1) (y := q - 1)
      (by linarith only [ht1]) (by linarith only [ht0]) hj
      (by linarith only [ht0, hjh]) (by linarith only [hq]) hy1
    have he : hrlS ((1 - (1 - 2 * t)) / 2) (1 - 2 * t + (2 * t + x - 1)) (1 + (q - 1)) =
        hrlS t x q := by congr 1 <;> ring
    rw [he, hrl_face_link] at red
    have face := hrl_face (x := 1 / 4 + (2 * t + x - 1)) (y := q - 1)
      (by linarith only [hj]) (by linarith only [ht0, hjh])
      (by linarith only [hq]) (by nlinarith only [hy, ht0])
    linarith only [red, face]
  rw [← hrl_link t x q hq0 hx] at hS
  have hL : 0 < nsfComb 4 1 t x (29 / 4 * t ^ (2 : ℕ)) q (hrlVL t x) (nsrLp q) (nsrFl t x q) :=
    pos_of_mul_pos_right hS (by positivity)
  have e := nsf_comb_sub_v 4 1 t x (29 / 4 * t ^ (2 : ℕ)) q (nsfVG t x) (hrlVL t x) (nsrLp q) (nsrFl t x q)
  have := hrl_VG_le_VL hx.le (by linarith : t ≤ 1)
  have : 0 ≤ (nsfVG t x - hrlVL t x) * nsfCv 4 1 t x (29 / 4 * t ^ (2 : ℕ)) q :=
    mul_nonneg_of_nonpos_of_nonpos (by linarith) hCv.le
  linarith

end SmoothedOctagon
