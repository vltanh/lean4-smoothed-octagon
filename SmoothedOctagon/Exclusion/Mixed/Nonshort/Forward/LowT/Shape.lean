module

public import SmoothedOctagon.Exclusion.Mixed.Nonshort.Forward.LowT.Circuit
public import SmoothedOctagon.Exclusion.Mixed.Nonshort.Forward.HighRatio.Shape

/-!
# Case M2, forward successor: the low-`t` residual increases in the shape

On the low-`t` large-gap domain the combined residual with the multipliers `a = nltAl q`,
`m = nltM t x q`, the majorants `V_L`, `L₊` and the floor `F_ℓ` satisfies
`nsfComb(1) ≤ nsfComb(k)` for `1 ≤ k ≤ 1 + j` (`nlt_shape_ge`), so the unit shape is the worst case.

The residual is quadratic in `k` (`hrs_comb_sub_k`): its shape derivative at the midpoint is affine
in `v`, `L`, `k` (`hrs_K_dec`). Its `v`-slope is `-2q²W𝓑` with `𝓑 > 0` (`nlt_Kv_eq`,
`nlt_Bs_pos`); its `L`- and `k`-slopes are nonpositive; `V_L < V̄` and `L₊ ≤ L̄`. At `v = V̄`,
`L = L̄`, `k = 1 + j` it equals `q²S/(12W)` (`nlt_Kend_eq`), and the quartic `S` is positive:
`S₂, S₃, S₄ ≤ 0` (concavity in `y`), `S(y = 0) = S₀ > 0`, and `8000S(t, x, b(t))` is a positive
combination of `Z₀, …, Z₅ > 0` (`nlt_SS_b_eq`, `nlt_SS_pos`).

The one-variable signs of `Z₀, …, Z₅` and the coefficient signs of `S₂`, `S₀` use termwise
monomial bounds, after each monomial in `t` is compared with its value at `t = 1/3` or `t = 3/8`
(`nlt_lo`, `nlt_hi`); the identities `nlt_Kv_eq`, `nlt_Kend_eq` are checked by direct expansion.

## Main API

* `nltVbar`, `nltLbar`, `nltBs`, `nltSS0`, …, `nltSS4`, `nltSS`, `nltZ0`, …, `nltZ5`.
* `nlt_Kv_eq`, `nlt_Kend_eq`, `nlt_SS_b_eq`, `nlt_Bs_pos`, `nlt_SS_pos`, `nlt_shape_ge`.
-/

@[expose] public section

namespace SmoothedOctagon

/-- The comparison incoming norm `V̄` with `T̄ = 1/2 - 7x/24`. -/
noncomputable def nltVbar (t x : ℝ) : ℝ :=
  1 - (1 - t) * (t + x) / (1 + x) ^ 2 + (1 - t) * x / (1 + x) ^ 2 * (1 / 2 - 7 / 24 * x - t)

/-- The comparison logarithm `L̄ = y - 5y²/12`, `y = q - 1`. -/
noncomputable def nltLbar (q : ℝ) : ℝ := (q - 1) - 5 / 12 * (q - 1) ^ 2

/-- `𝓑 = B₀ + B₁y + B₂y²`. -/
noncomputable def nltBs (t x y : ℝ) : ℝ :=
  7 * x - 6 * x * y + 7 * x ^ 2 - 2 * t * y + 9 * t * x - 40 * x * y ^ 2 + x ^ 2 * y - 26 * t * x * y + 14 * t * x ^ 2 - 2 * t ^ 2 * x - 60 * x ^ 2 * y ^ 2 + 7 * x ^ 3 * y - 2 * t * x * y ^ 2 - 52 * t * x ^ 2 * y + 7 * t * x ^ 3 - 4 * t ^ 2 * x * y - 20 * x ^ 3 * y ^ 2 - 6 * t * x ^ 2 * y ^ 2 - 24 * t * x ^ 3 * y - 2 * t ^ 2 * x * y ^ 2 - 2 * t * x ^ 3 * y ^ 2

/-- `S_0`: the `y^0`-coefficient of the quartic `S`. -/
noncomputable def nltSS0 (t x : ℝ) : ℝ :=
  84 * x ^ 2 + 24 * t * x + 133 * x ^ 3 - 144 * t * x ^ 2 - 72 * t ^ 2 * x + 49 * x ^ 4 - 262 * t * x ^ 3 - 12 * t ^ 2 * x ^ 2 + 48 * t ^ 3 * x - 35 * t * x ^ 4 + 115 * t ^ 2 * x ^ 3 + 72 * t ^ 3 * x ^ 2 + 49 * t * x ^ 5 - 14 * t ^ 2 * x ^ 4 + 14 * t ^ 3 * x ^ 3 - 49 * t ^ 2 * x ^ 5

/-- `S_1`: the `y^1`-coefficient of the quartic `S`. -/
noncomputable def nltSS1 (t x : ℝ) : ℝ :=
  -72 * x ^ 2 + 240 * t * x + 24 * t ^ 2 - 30 * x ^ 3 + 898 * t * x ^ 2 - 432 * t ^ 2 * x - 48 * t ^ 3 + 91 * x ^ 4 + 1000 * t * x ^ 3 - 1354 * t ^ 2 * x ^ 2 + 96 * t ^ 3 * x + 49 * x ^ 5 + 313 * t * x ^ 4 - 1382 * t ^ 2 * x ^ 3 + 384 * t ^ 3 * x ^ 2 - 49 * t * x ^ 5 - 524 * t ^ 2 * x ^ 4 + 316 * t ^ 3 * x ^ 3 + 96 * t ^ 3 * x ^ 4

/-- `S_2`: the `y^2`-coefficient of the quartic `S`. -/
noncomputable def nltSS2 (t x : ℝ) : ℝ :=
  -480 * x ^ 2 - 390 * t * x + 90 * t ^ 2 - 1000 * x ^ 3 - 784 * t * x ^ 2 + 396 * t ^ 2 * x - 164 * t ^ 3 - 660 * x ^ 4 - 854 * t * x ^ 3 + 856 * t ^ 2 * x ^ 2 - 328 * t ^ 3 * x - 140 * x ^ 5 - 830 * t * x ^ 4 + 1340 * t ^ 2 * x ^ 3 - 140 * t ^ 3 * x ^ 2 - 380 * t * x ^ 5 + 1264 * t ^ 2 * x ^ 4 + 62 * t ^ 3 * x ^ 3 + 494 * t ^ 2 * x ^ 5 + 48 * t ^ 3 * x ^ 4

/-- `S_3`: the `y^3`-coefficient of the quartic `S`. -/
noncomputable def nltSS3 (t x : ℝ) : ℝ :=
  -200 * t * x - 200 * t ^ 2 - 832 * t * x ^ 2 - 896 * t ^ 2 * x - 40 * t ^ 3 - 1280 * t * x ^ 3 - 1432 * t ^ 2 * x ^ 2 - 80 * t ^ 3 * x - 864 * t * x ^ 4 - 976 * t ^ 2 * x ^ 3 - 40 * t ^ 3 * x ^ 2 - 216 * t * x ^ 5 - 240 * t ^ 2 * x ^ 4

/-- `S_4`: the `y^4`-coefficient of the quartic `S`. -/
noncomputable def nltSS4 (t x : ℝ) : ℝ :=
  -40 * t * x ^ 2 - 60 * t ^ 2 * x - 20 * t ^ 3 - 100 * t * x ^ 3 - 140 * t ^ 2 * x ^ 2 - 40 * t ^ 3 * x - 80 * t * x ^ 4 - 100 * t ^ 2 * x ^ 3 - 20 * t ^ 3 * x ^ 2 - 20 * t * x ^ 5 - 20 * t ^ 2 * x ^ 4

/-- The quartic `S = ∑ Sᵢyⁱ`. -/
noncomputable def nltSS (t x y : ℝ) : ℝ :=
  nltSS0 t x + nltSS1 t x * y + nltSS2 t x * y ^ 2 + nltSS3 t x * y ^ 3 + nltSS4 t x * y ^ 4

/-- `Z_0(t)`: the coefficient of `t²(18 - 37t)` in `8000S(t, x, b(t))` (`nlt_SS_b_eq`). -/
noncomputable def nltZ0 (t : ℝ) : ℝ :=
  -22800 + 102768 * t - 63196 * t ^ 2 - 128686 * t ^ 3 + 50653 * t ^ 4

/-- `Z_1(t)`: the coefficient of `tx` in `8000S(t, x, b(t))` (`nlt_SS_b_eq`). -/
noncomputable def nltZ1 (t : ℝ) : ℝ :=
  -1773600 + 7369680 * t + 3467160 * t ^ 2 - 41328112 * t ^ 3 + 36108744 * t ^ 4 + 5723789 * t ^ 5 - 3748322 * t ^ 6

/-- `Z_2(t)`: the coefficient of `x²` in `8000S(t, x, b(t))` (`nlt_SS_b_eq`). -/
noncomputable def nltZ2 (t : ℝ) : ℝ :=
  -2956800 + 9023904 * t + 12717104 * t ^ 2 - 31421920 * t ^ 3 - 51268680 * t ^ 4 + 84864310 * t ^ 5 - 7445991 * t ^ 6 - 1874161 * t ^ 7

/-- `Z_3(t)`: the coefficient of `x³` in `8000S(t, x, b(t))` (`nlt_SS_b_eq`). -/
noncomputable def nltZ3 (t : ℝ) : ℝ :=
  -5632000 + 18664240 * t + 24356048 * t ^ 2 - 104352976 * t ^ 3 + 27973184 * t ^ 4 + 59999163 * t ^ 5 - 9370805 * t ^ 6

/-- `Z_4(t)`: the coefficient of `x⁴` in `8000S(t, x, b(t))` (`nlt_SS_b_eq`). -/
noncomputable def nltZ4 (t : ℝ) : ℝ :=
  -3229600 + 7372048 * t + 36734704 * t ^ 2 - 112663832 * t ^ 3 + 69857480 * t ^ 4 + 9621332 * t ^ 5 - 1874161 * t ^ 6

/-- `Z_5(t)`: the coefficient of `x⁵` in `8000S(t, x, b(t))` (`nlt_SS_b_eq`). -/
noncomputable def nltZ5 (t : ℝ) : ℝ :=
  -554400 - 783488 * t + 18455680 * t ^ 2 - 42193912 * t ^ 3 + 28113784 * t ^ 4 - 1874161 * t ^ 5

/-- The `v`-slope of the shape derivative: `-2q²W𝓑`. -/
theorem nlt_Kv_eq (t x q : ℝ) : hrsKv (nltAl q) t x q = -2 * q ^ 2 * (1 + x) * nltBs t x (q - 1) := by
  unfold hrsKv nltAl nltBs; ring

/-- **The comparison derivative**: at `v = V̄`, `L = L̄`, `k = 1 + j`,
`12W ∂_kF = q²S`. -/
theorem nlt_Kend_eq (t x q : ℝ) (hx : 0 < 1 + x) :
    12 * (1 + x) * hrsK (nltAl q) t x (2 * t + x) q (nltVbar t x) (nltLbar q) =
      q ^ 2 * nltSS t x (q - 1) := by
  have hV : nltVbar t x = ((1 + x) ^ 2 - (1 - t) * (t + x) + (1 - t) * x * (1 / 2 - 7 / 24 * x - t))
      / (1 + x) ^ 2 := by
    unfold nltVbar; field_simp
  rw [hV]
  unfold hrsK nsrA hrsTk nsfE0 nltLbar nltAl nltSS nltSS0 nltSS1 nltSS2 nltSS3 nltSS4
  field_simp
  ring

/-- **The endpoint identity** at `y = b(t) = (18 - 37t)/20`. -/
theorem nlt_SS_b_eq (t x : ℝ) : 8000 * nltSS t x ((18 - 37 * t) / 20) =
    t ^ 2 * (18 - 37 * t) * nltZ0 t + t * x * nltZ1 t + x ^ 2 * nltZ2 t + x ^ 3 * nltZ3 t
      + x ^ 4 * nltZ4 t + x ^ 5 * nltZ5 t := by
  unfold nltSS nltSS0 nltSS1 nltSS2 nltSS3 nltSS4 nltZ0 nltZ1 nltZ2 nltZ3 nltZ4 nltZ5; ring

/-- `Z_0 > 0` on `[1/3, 3/8]`. -/
theorem nltZ0_pos {t : ℝ} (h1 : (1 / 3) ≤ t) (h2 : t ≤ (3 / 8)) : 0 < nltZ0 t := by
  obtain ⟨z, rfl⟩ : ∃ z, t = (1 / 3) + z := ⟨t - (1 / 3), by ring⟩
  have z0 : 0 ≤ z := by linarith
  have z1 : z ≤ (1 / 24) := by linarith
  have p2 : z ^ 2 ≤ (1 / 24) * z ^ 1 := nlt_pw z0 z1 1
  have q2 : 0 ≤ z ^ 2 := pow_nonneg z0 2
  have p3 : z ^ 3 ≤ (1 / 24) * z ^ 2 := nlt_pw z0 z1 2
  have q3 : 0 ≤ z ^ 3 := pow_nonneg z0 3
  have p4 : z ^ 4 ≤ (1 / 24) * z ^ 3 := nlt_pw z0 z1 3
  have q4 : 0 ≤ z ^ 4 := pow_nonneg z0 4
  have e : nltZ0 ((1 / 3) + z) = (23767 / 81) + (681646 / 27) * z - (474340 / 3) * z ^ 2 - (183446 / 3) * z ^ 3 + 50653 * z ^ 4 := by unfold nltZ0; ring
  rw [e]; linarith only [z0, z1, p2, q2, p3, q3, p4, q4]

/-- `Z_1 > 0` on `[1/3, 3/8]`. -/
theorem nltZ1_pos {t : ℝ} (h1 : (1 / 3) ≤ t) (h2 : t ≤ (3 / 8)) : 0 < nltZ1 t := by
  obtain ⟨z, rfl⟩ : ∃ z, t = (1 / 3) + z := ⟨t - (1 / 3), by ring⟩
  have z0 : 0 ≤ z := by linarith
  have z1 : z ≤ (1 / 24) := by linarith
  have p2 : z ^ 2 ≤ (1 / 24) * z ^ 1 := nlt_pw z0 z1 1
  have q2 : 0 ≤ z ^ 2 := pow_nonneg z0 2
  have p3 : z ^ 3 ≤ (1 / 24) * z ^ 2 := nlt_pw z0 z1 2
  have q3 : 0 ≤ z ^ 3 := pow_nonneg z0 3
  have p4 : z ^ 4 ≤ (1 / 24) * z ^ 3 := nlt_pw z0 z1 3
  have q4 : 0 ≤ z ^ 4 := pow_nonneg z0 4
  have p5 : z ^ 5 ≤ (1 / 24) * z ^ 4 := nlt_pw z0 z1 4
  have q5 : 0 ≤ z ^ 5 := pow_nonneg z0 5
  have p6 : z ^ 6 ≤ (1 / 24) * z ^ 5 := nlt_pw z0 z1 5
  have q6 : 0 ≤ z ^ 6 := pow_nonneg z0 6
  have e : nltZ1 ((1 / 3) + z) = (1260517 / 729) + (40912975 / 27) * z - (333792032 / 27) * z ^ 2 + (280802990 / 27) * z ^ 3 + 39401189 * z ^ 4 - 1772855 * z ^ 5 - 3748322 * z ^ 6 := by unfold nltZ1; ring
  rw [e]; linarith only [z0, z1, p2, q2, p3, q3, p4, q4, p5, q5, p6, q6]

/-- `Z_2 > 0` on `[1/3, 3/8]`. -/
theorem nltZ2_pos {t : ℝ} (h1 : (1 / 3) ≤ t) (h2 : t ≤ (3 / 8)) : 0 < nltZ2 t := by
  obtain ⟨z, rfl⟩ : ∃ z, t = (1 / 3) + z := ⟨t - (1 / 3), by ring⟩
  have z0 : 0 ≤ z := by linarith
  have z1 : z ≤ (1 / 24) := by linarith
  have p2 : z ^ 2 ≤ (1 / 24) * z ^ 1 := nlt_pw z0 z1 1
  have q2 : 0 ≤ z ^ 2 := pow_nonneg z0 2
  have p3 : z ^ 3 ≤ (1 / 24) * z ^ 2 := nlt_pw z0 z1 2
  have q3 : 0 ≤ z ^ 3 := pow_nonneg z0 3
  have p4 : z ^ 4 ≤ (1 / 24) * z ^ 3 := nlt_pw z0 z1 3
  have q4 : 0 ≤ z ^ 4 := pow_nonneg z0 4
  have p5 : z ^ 5 ≤ (1 / 24) * z ^ 4 := nlt_pw z0 z1 4
  have q5 : 0 ≤ z ^ 5 := pow_nonneg z0 5
  have p6 : z ^ 6 ≤ (1 / 24) * z ^ 5 := nlt_pw z0 z1 5
  have q6 : 0 ≤ z ^ 6 := pow_nonneg z0 6
  have p7 : z ^ 7 ≤ (1 / 24) * z ^ 6 := nlt_pw z0 z1 6
  have q7 : 0 ≤ z ^ 7 := pow_nonneg z0 7
  have e : nltZ2 ((1 / 3) + z) = (12297464 / 2187) + (3258141545 / 729) * z - (1862478508 / 81) * z ^ 2 - (956760155 / 81) * z ^ 3 + (2033974360 / 27) * z ^ 4 + (196797857 / 3) * z ^ 5 - (35457100 / 3) * z ^ 6 - 1874161 * z ^ 7 := by unfold nltZ2; ring
  rw [e]; linarith only [z0, z1, p2, q2, p3, q3, p4, q4, p5, q5, p6, q6, p7, q7]

/-- `Z_3 > 0` on `[1/3, 3/8]`. -/
theorem nltZ3_pos {t : ℝ} (h1 : (1 / 3) ≤ t) (h2 : t ≤ (3 / 8)) : 0 < nltZ3 t := by
  obtain ⟨z, rfl⟩ : ∃ z, t = (1 / 3) + z := ⟨t - (1 / 3), by ring⟩
  have z0 : 0 ≤ z := by linarith
  have z1 : z ≤ (1 / 24) := by linarith
  have p2 : z ^ 2 ≤ (1 / 24) * z ^ 1 := nlt_pw z0 z1 1
  have q2 : 0 ≤ z ^ 2 := pow_nonneg z0 2
  have p3 : z ^ 3 ≤ (1 / 24) * z ^ 2 := nlt_pw z0 z1 2
  have q3 : 0 ≤ z ^ 3 := pow_nonneg z0 3
  have p4 : z ^ 4 ≤ (1 / 24) * z ^ 3 := nlt_pw z0 z1 3
  have q4 : 0 ≤ z ^ 4 := pow_nonneg z0 4
  have p5 : z ^ 5 ≤ (1 / 24) * z ^ 4 := nlt_pw z0 z1 4
  have q5 : 0 ≤ z ^ 5 := pow_nonneg z0 5
  have p6 : z ^ 6 ≤ (1 / 24) * z ^ 5 := nlt_pw z0 z1 5
  have q6 : 0 ≤ z ^ 6 := pow_nonneg z0 6
  have e : nltZ3 ((1 / 3) + z) = (7377196 / 729) + (626432093 / 81) * z - (1103262139 / 27) * z ^ 2 - (197936938 / 27) * z ^ 3 + (337061342 / 3) * z ^ 4 + 41257553 * z ^ 5 - 9370805 * z ^ 6 := by unfold nltZ3; ring
  rw [e]; linarith only [z0, z1, p2, q2, p3, q3, p4, q4, p5, q5, p6, q6]

/-- `Z_4 > 0` on `[1/3, 3/8]`. -/
theorem nltZ4_pos {t : ℝ} (h1 : (1 / 3) ≤ t) (h2 : t ≤ (3 / 8)) : 0 < nltZ4 t := by
  obtain ⟨z, rfl⟩ : ∃ z, t = (1 / 3) + z := ⟨t - (1 / 3), by ring⟩
  have z0 : 0 ≤ z := by linarith
  have z1 : z ≤ (1 / 24) := by linarith
  have p2 : z ^ 2 ≤ (1 / 24) * z ^ 1 := nlt_pw z0 z1 1
  have q2 : 0 ≤ z ^ 2 := pow_nonneg z0 2
  have p3 : z ^ 3 ≤ (1 / 24) * z ^ 2 := nlt_pw z0 z1 2
  have q3 : 0 ≤ z ^ 3 := pow_nonneg z0 3
  have p4 : z ^ 4 ≤ (1 / 24) * z ^ 3 := nlt_pw z0 z1 3
  have q4 : 0 ≤ z ^ 4 := pow_nonneg z0 4
  have p5 : z ^ 5 ≤ (1 / 24) * z ^ 4 := nlt_pw z0 z1 4
  have q5 : 0 ≤ z ^ 5 := pow_nonneg z0 5
  have p6 : z ^ 6 ≤ (1 / 24) * z ^ 5 := nlt_pw z0 z1 5
  have q6 : 0 ≤ z ^ 6 := pow_nonneg z0 6
  have e : nltZ4 ((1 / 3) + z) = (26323979 / 729) + (421534538 / 81) * z - (235269767 / 9) * z ^ 2 - (275897444 / 27) * z ^ 3 + (248308295 / 3) * z ^ 4 + 5873010 * z ^ 5 - 1874161 * z ^ 6 := by unfold nltZ4; ring
  rw [e]; linarith only [z0, z1, p2, q2, p3, q3, p4, q4, p5, q5, p6, q6]

/-- `Z_5 > 0` on `[1/3, 3/8]`. -/
theorem nltZ5_pos {t : ℝ} (h1 : (1 / 3) ≤ t) (h2 : t ≤ (3 / 8)) : 0 < nltZ5 t := by
  obtain ⟨z, rfl⟩ : ∃ z, t = (1 / 3) + z := ⟨t - (1 / 3), by ring⟩
  have z0 : 0 ≤ z := by linarith
  have z1 : z ≤ (1 / 24) := by linarith
  have p2 : z ^ 2 ≤ (1 / 24) * z ^ 1 := nlt_pw z0 z1 1
  have q2 : 0 ≤ z ^ 2 := pow_nonneg z0 2
  have p3 : z ^ 3 ≤ (1 / 24) * z ^ 2 := nlt_pw z0 z1 2
  have q3 : 0 ≤ z ^ 3 := pow_nonneg z0 3
  have p4 : z ^ 4 ≤ (1 / 24) * z ^ 3 := nlt_pw z0 z1 3
  have q4 : 0 ≤ z ^ 4 := pow_nonneg z0 4
  have p5 : z ^ 5 ≤ (1 / 24) * z ^ 4 := nlt_pw z0 z1 4
  have q5 : 0 ≤ z ^ 5 := pow_nonneg z0 5
  have e : nltZ5 ((1 / 3) + z) = (2843615 / 243) + (121903171 / 81) * z - (153625762 / 27) * z ^ 2 - (61121410 / 9) * z ^ 3 + (74970547 / 3) * z ^ 4 - 1874161 * z ^ 5 := by unfold nltZ5; ring
  rw [e]; linarith only [z0, z1, p2, q2, p3, q3, p4, q4, p5, q5]

/-- `-S₂`. -/
noncomputable def nltSSc2 (t x : ℝ) : ℝ := -nltSS2 t x

/-- The univariate lower polynomial of `nltSSc2 t x` (monomial comparison in `t`). -/
noncomputable def nltSSc2_posQ (x : ℝ) : ℝ :=
  -(5687 / 864) + (37351 / 432) * x + (135247 / 216) * x ^ 2 + (839393 / 768) * x ^ 3 + (72613 / 96) * x ^ 4 + (18931 / 96) * x ^ 5

/-- The univariate bound for `nltSSc2_pos`. -/
theorem nltSSc2_posQ_pos {x : ℝ} (h1 : (17 / 60) ≤ x) (h2 : x ≤ (4 / 7)) : 0 < nltSSc2_posQ x := by
  obtain ⟨z, rfl⟩ : ∃ z, x = (17 / 60) + z := ⟨x - (17 / 60), by ring⟩
  have z0 : 0 ≤ z := by linarith
  have z1 : z ≤ (121 / 420) := by linarith
  have p2 : z ^ 2 ≤ (121 / 420) * z ^ 1 := nlt_pw z0 z1 1
  have q2 : 0 ≤ z ^ 2 := pow_nonneg z0 2
  have p3 : z ^ 3 ≤ (121 / 420) * z ^ 2 := nlt_pw z0 z1 2
  have q3 : 0 ≤ z ^ 3 := pow_nonneg z0 3
  have p4 : z ^ 4 ≤ (121 / 420) * z ^ 3 := nlt_pw z0 z1 3
  have q4 : 0 ≤ z ^ 4 := pow_nonneg z0 4
  have p5 : z ^ 5 ≤ (121 / 420) * z ^ 4 := nlt_pw z0 z1 4
  have q5 : 0 ≤ z ^ 5 := pow_nonneg z0 5
  have e : nltSSc2_posQ ((17 / 60) + z) = (7336174877297 / 74649600000) + (194006277553 / 248832000) * z + (407325179 / 207360) * z ^ 2 + (9108731 / 4320) * z ^ 3 + (1193183 / 1152) * z ^ 4 + (18931 / 96) * z ^ 5 := by unfold nltSSc2_posQ; ring
  rw [e]; linarith only [z0, z1, p2, q2, p3, q3, p4, q4, p5, q5]

/-- `S₂ < 0` on `1/3 ≤ t ≤ 3/8`, `17/60 ≤ x ≤ 4/7`. -/
theorem nltSSc2_pos {t x : ℝ} (ht0 : (1 / 3) ≤ t) (ht1 : t ≤ (3 / 8)) (hx0 : (17 / 60) ≤ x) (hx1 : x ≤ (4 / 7)) :
    0 < nltSSc2 t x := by
  have hx : (0 : ℝ) ≤ x := by linarith
  have ht : (0 : ℝ) ≤ t := by linarith
  have hq := nltSSc2_posQ_pos hx0 hx1
  have m0 := nlt_hi 3 4 (by norm_num : ((3 / 8) : ℝ) ^ 3 = (27 / 512)) ht ht1 hx
  have m1 := nlt_hi 3 3 (by norm_num : ((3 / 8) : ℝ) ^ 3 = (27 / 512)) ht ht1 hx
  have m2 := nlt_lo 3 2 (by norm_num : ((1 / 3) : ℝ) ^ 3 = (1 / 27)) (by norm_num) ht0 hx
  have m3 := nlt_lo 3 1 (by norm_num : ((1 / 3) : ℝ) ^ 3 = (1 / 27)) (by norm_num) ht0 hx
  have m4 := nlt_lo 3 0 (by norm_num : ((1 / 3) : ℝ) ^ 3 = (1 / 27)) (by norm_num) ht0 hx
  have m5 := nlt_hi 2 5 (by norm_num : ((3 / 8) : ℝ) ^ 2 = (9 / 64)) ht ht1 hx
  have m6 := nlt_hi 2 4 (by norm_num : ((3 / 8) : ℝ) ^ 2 = (9 / 64)) ht ht1 hx
  have m7 := nlt_hi 2 3 (by norm_num : ((3 / 8) : ℝ) ^ 2 = (9 / 64)) ht ht1 hx
  have m8 := nlt_hi 2 2 (by norm_num : ((3 / 8) : ℝ) ^ 2 = (9 / 64)) ht ht1 hx
  have m9 := nlt_hi 2 1 (by norm_num : ((3 / 8) : ℝ) ^ 2 = (9 / 64)) ht ht1 hx
  have m10 := nlt_hi 2 0 (by norm_num : ((3 / 8) : ℝ) ^ 2 = (9 / 64)) ht ht1 hx
  have m11 := nlt_lo 1 5 (by norm_num : ((1 / 3) : ℝ) ^ 1 = (1 / 3)) (by norm_num) ht0 hx
  have m12 := nlt_lo 1 4 (by norm_num : ((1 / 3) : ℝ) ^ 1 = (1 / 3)) (by norm_num) ht0 hx
  have m13 := nlt_lo 1 3 (by norm_num : ((1 / 3) : ℝ) ^ 1 = (1 / 3)) (by norm_num) ht0 hx
  have m14 := nlt_lo 1 2 (by norm_num : ((1 / 3) : ℝ) ^ 1 = (1 / 3)) (by norm_num) ht0 hx
  have m15 := nlt_lo 1 1 (by norm_num : ((1 / 3) : ℝ) ^ 1 = (1 / 3)) (by norm_num) ht0 hx
  unfold nltSSc2 nltSS2 nltSSc2_posQ at *
  linarith

/-- The bracket of `S₀ = x(1 - t)[…]`. -/
noncomputable def nltSSb0 (t x : ℝ) : ℝ :=
  24 * t * (1 - 2 * t) + (84 - 60 * t - 72 * t ^ 2) * x + (133 - 129 * t - 14 * t ^ 2) * x ^ 2
    + (49 + 14 * t) * x ^ 3 + 49 * t * x ^ 4

/-- The univariate lower polynomial of `nltSSb0 t x` (monomial comparison in `t`). -/
noncomputable def nltSSb0_posQ (x : ℝ) : ℝ :=
  (5 / 4) + (411 / 8) * x + (2645 / 32) * x ^ 2 + (161 / 3) * x ^ 3 + (49 / 3) * x ^ 4

/-- The univariate bound for `nltSSb0_pos`. -/
theorem nltSSb0_posQ_pos {x : ℝ} (h1 : (17 / 60) ≤ x) (h2 : x ≤ (4 / 7)) : 0 < nltSSb0_posQ x := by
  obtain ⟨z, rfl⟩ : ∃ z, x = (17 / 60) + z := ⟨x - (17 / 60), by ring⟩
  have z0 : 0 ≤ z := by linarith
  have z1 : z ≤ (121 / 420) := by linarith
  have p2 : z ^ 2 ≤ (121 / 420) * z ^ 1 := nlt_pw z0 z1 1
  have q2 : 0 ≤ z ^ 2 := pow_nonneg z0 2
  have p3 : z ^ 3 ≤ (121 / 420) * z ^ 2 := nlt_pw z0 z1 2
  have q3 : 0 ≤ z ^ 3 := pow_nonneg z0 3
  have p4 : z ^ 4 ≤ (121 / 420) * z ^ 3 := nlt_pw z0 z1 3
  have q4 : 0 ≤ z ^ 4 := pow_nonneg z0 4
  have e : nltSSb0_posQ ((17 / 60) + z) = (1848171593 / 77760000) + (72980543 / 648000) * z + (980209 / 7200) * z ^ 2 + (3248 / 45) * z ^ 3 + (49 / 3) * z ^ 4 := by unfold nltSSb0_posQ; ring
  rw [e]; linarith only [z0, z1, p2, q2, p3, q3, p4, q4]

/-- The bracket of `S₀` is positive on `1/3 ≤ t ≤ 3/8`, `17/60 ≤ x ≤ 4/7`. -/
theorem nltSSb0_pos {t x : ℝ} (ht0 : (1 / 3) ≤ t) (ht1 : t ≤ (3 / 8)) (hx0 : (17 / 60) ≤ x) (hx1 : x ≤ (4 / 7)) :
    0 < nltSSb0 t x := by
  have hx : (0 : ℝ) ≤ x := by linarith
  have ht : (0 : ℝ) ≤ t := by linarith
  have hq := nltSSb0_posQ_pos hx0 hx1
  have m0 := nlt_hi 2 2 (by norm_num : ((3 / 8) : ℝ) ^ 2 = (9 / 64)) ht ht1 hx
  have m1 := nlt_hi 2 1 (by norm_num : ((3 / 8) : ℝ) ^ 2 = (9 / 64)) ht ht1 hx
  have m2 := nlt_hi 2 0 (by norm_num : ((3 / 8) : ℝ) ^ 2 = (9 / 64)) ht ht1 hx
  have m3 := nlt_lo 1 4 (by norm_num : ((1 / 3) : ℝ) ^ 1 = (1 / 3)) (by norm_num) ht0 hx
  have m4 := nlt_lo 1 3 (by norm_num : ((1 / 3) : ℝ) ^ 1 = (1 / 3)) (by norm_num) ht0 hx
  have m5 := nlt_hi 1 2 (by norm_num : ((3 / 8) : ℝ) ^ 1 = (3 / 8)) ht ht1 hx
  have m6 := nlt_hi 1 1 (by norm_num : ((3 / 8) : ℝ) ^ 1 = (3 / 8)) ht ht1 hx
  have m7 := nlt_lo 1 0 (by norm_num : ((1 / 3) : ℝ) ^ 1 = (1 / 3)) (by norm_num) ht0 hx
  unfold nltSSb0 nltSSb0_posQ at *
  linarith

/-- **`𝓑 > 0`** for `1/3 ≤ t ≤ 3/8`, `x ≥ 17/60`, `0 ≤ y ≤ 9/32`: `B₁, B₂ ≤ 0`, so
`𝓑 ≥ 𝓑(9/32)`, and `512𝓑(9/32) ≥ 1100x - 288t > 0`. -/
theorem nlt_Bs_pos {t x y : ℝ} (ht0 : 1 / 3 ≤ t) (ht1 : t ≤ 3 / 8) (hx : 17 / 60 ≤ x)
    (hy0 : 0 ≤ y) (hy1 : y ≤ 9 / 32) : 0 < nltBs t x y := by
  have hx0 : 0 < x := by linarith
  have ht : 0 < t := by linarith
  have hB2 : 0 ≤ 2 * x * (t ^ 2 + t * x ^ 2 + 3 * t * x + t + 10 * x ^ 2 + 30 * x + 20) := by positivity
  have hB1 : 0 ≤ 2 * t + (4 * t ^ 2 + 26 * t + 6) * x + (52 * t - 1) * x ^ 2 + (24 * t - 7) * x ^ 3 := by
    have : 0 ≤ 52 * t - 1 := by linarith
    have : 0 ≤ 24 * t - 7 := by linarith
    positivity
  have h512 : 0 < -1681 * t ^ 2 * x + 47 * t * x ^ 3 - 563 * t * x ^ 2 + 783 * t * x - 288 * t
      + 198 * x ^ 3 + 1298 * x ^ 2 + 1100 * x := by
    have a1 : 0 ≤ t * x * (783 - 1681 * t) := mul_nonneg (by positivity) (by linarith)
    have a2 : 0 ≤ x ^ 2 * (1298 - 563 * t) := mul_nonneg (by positivity) (by linarith)
    have a3 : 0 ≤ (47 * t + 198) * x ^ 3 := by positivity
    nlinarith
  have k1 : -(2 * t + (4 * t ^ 2 + 26 * t + 6) * x + (52 * t - 1) * x ^ 2 + (24 * t - 7) * x ^ 3)
      * (9 / 32) ≤ -(2 * t + (4 * t ^ 2 + 26 * t + 6) * x + (52 * t - 1) * x ^ 2
        + (24 * t - 7) * x ^ 3) * y :=
    mul_le_mul_of_nonpos_left hy1 (by linarith)
  have k2 : -(2 * x * (t ^ 2 + t * x ^ 2 + 3 * t * x + t + 10 * x ^ 2 + 30 * x + 20)) * (9 / 32) ^ 2
      ≤ -(2 * x * (t ^ 2 + t * x ^ 2 + 3 * t * x + t + 10 * x ^ 2 + 30 * x + 20)) * y ^ 2 :=
    mul_le_mul_of_nonpos_left (pow_le_pow_left₀ hy0 hy1 2) (by linarith)
  unfold nltBs
  nlinarith

/-- **The quartic `S` is positive** for `1/3 ≤ t ≤ 3/8`, `17/60 ≤ x ≤ 4/7`,
`0 ≤ y ≤ b(t) = (18 - 37t)/20`. -/
theorem nlt_SS_pos {t x y : ℝ} (ht0 : 1 / 3 ≤ t) (ht1 : t ≤ 3 / 8) (hx0 : 17 / 60 ≤ x)
    (hx1 : x ≤ 4 / 7) (hy0 : 0 ≤ y) (hy : y ≤ (18 - 37 * t) / 20) : 0 < nltSS t x y := by
  have hx : 0 < x := by linarith
  have ht : 0 < t := by linarith
  set b := (18 - 37 * t) / 20 with hb
  have hb0 : 0 < b := by rw [hb]; linarith
  -- `S₀ > 0`, `S₂ < 0`, `S₃, S₄ ≤ 0`
  have s0 : 0 < nltSS0 t x := by
    have := nltSSb0_pos ht0 ht1 hx0 hx1
    have e : nltSS0 t x = x * (1 - t) * nltSSb0 t x := by unfold nltSS0 nltSSb0; ring
    rw [e]; exact mul_pos (mul_pos hx (by linarith)) this
  have s2 : nltSS2 t x < 0 := by
    have := nltSSc2_pos ht0 ht1 hx0 hx1
    unfold nltSSc2 at this; linarith
  have s3 : nltSS3 t x ≤ 0 := by
    have e : nltSS3 t x = -(8 * t * (1 + x) ^ 2 * (5 * t ^ 2 + 30 * t * x ^ 2 + 62 * t * x + 25 * t
        + 27 * x ^ 3 + 54 * x ^ 2 + 25 * x)) := by unfold nltSS3; ring
    rw [e]
    have : 0 ≤ 8 * t * (1 + x) ^ 2 * (5 * t ^ 2 + 30 * t * x ^ 2 + 62 * t * x + 25 * t
        + 27 * x ^ 3 + 54 * x ^ 2 + 25 * x) := by positivity
    linarith
  have s4 : nltSS4 t x ≤ 0 := by
    have e : nltSS4 t x = -(20 * t * (t + x) * (1 + x) ^ 2 * (t + x ^ 2 + 2 * x)) := by
      unfold nltSS4; ring
    rw [e]
    have : 0 ≤ 20 * t * (t + x) * (1 + x) ^ 2 * (t + x ^ 2 + 2 * x) := by positivity
    linarith
  -- `S(b(t)) > 0` (`nlt_SS_b_eq`)
  have sb : 0 < nltSS t x b := by
    have z0 := nltZ0_pos ht0 ht1
    have z1 := nltZ1_pos ht0 ht1
    have z2 := nltZ2_pos ht0 ht1
    have z3 := nltZ3_pos ht0 ht1
    have z4 := nltZ4_pos ht0 ht1
    have z5 := nltZ5_pos ht0 ht1
    have e := nlt_SS_b_eq t x
    rw [← hb] at e
    have : 0 < t ^ 2 * (18 - 37 * t) * nltZ0 t + t * x * nltZ1 t + x ^ 2 * nltZ2 t
        + x ^ 3 * nltZ3 t + x ^ 4 * nltZ4 t + x ^ 5 * nltZ5 t := by
      have : 0 < 18 - 37 * t := by linarith
      positivity
    linarith
  -- concavity in `y`: `b S(y) ≥ (b - y) S₀ + y S(b)`
  have key : b * nltSS t x y - ((b - y) * nltSS0 t x + y * nltSS t x b) =
      -(y * b * (b - y)) * (nltSS2 t x + nltSS3 t x * (y + b) + nltSS4 t x * (y ^ 2 + y * b + b ^ 2)) := by
    unfold nltSS; ring
  have q1 : nltSS2 t x + nltSS3 t x * (y + b) + nltSS4 t x * (y ^ 2 + y * b + b ^ 2) ≤ 0 := by
    have := mul_nonpos_of_nonpos_of_nonneg s3 (by positivity : (0 : ℝ) ≤ y + b)
    have := mul_nonpos_of_nonpos_of_nonneg s4 (by positivity : (0 : ℝ) ≤ y ^ 2 + y * b + b ^ 2)
    linarith
  have q2 : 0 ≤ y * b * (b - y) := mul_nonneg (mul_nonneg hy0 hb0.le) (by linarith)
  have q3 := mul_nonneg q2 (by linarith : (0 : ℝ) ≤ -(nltSS2 t x + nltSS3 t x * (y + b)
    + nltSS4 t x * (y ^ 2 + y * b + b ^ 2)))
  have q4 : 0 < (b - y) * nltSS0 t x + y * nltSS t x b := by
    rcases eq_or_lt_of_le hy with h | h
    · rw [h]; nlinarith
    · nlinarith [mul_pos (sub_pos.2 h) s0, mul_nonneg hy0 sb.le]
  have : 0 < b * nltSS t x y := by nlinarith
  exact pos_of_mul_pos_right this hb0.le

/-- **Shape monotonicity**, integrated on `[1, k]`: on the low-`t` large-gap domain
`1/3 ≤ t ≤ 3/8`, `j = 2t + x - 1 ≥ 1/30`, `7x ≤ 12(1 - 2t)`, `1 ≤ q`, `q(4t + 2x - 1) ≤ 1 + x`, for
`1 ≤ k ≤ 2t + x`, the residual at the unit shape is at most its value at `k`. The bound
`Je² ≤ 17/16` (`nsf_LG_J`) is supplied by the caller. -/
theorem nlt_shape_ge {t x k q : ℝ} (ht0 : 1 / 3 ≤ t) (ht1 : t ≤ 3 / 8) (hj : 1 / 30 ≤ 2 * t + x - 1)
    (hjh : 7 * x ≤ 12 * (1 - 2 * t)) (hk1 : 1 ≤ k) (hk : k ≤ 2 * t + x) (hq : 1 ≤ q)
    (hqs : q * (4 * t + 2 * x - 1) ≤ 1 + x)
    (hJ : (t + x * (x + 2)) * q ^ 2 ≤ 17 / 16 * (1 + x) ^ 2) :
    nsfComb (nltAl q) (nltM t x q) t x 1 q (hrlVL t x) (nsrLp q) (nsrFl t x q) ≤
      nsfComb (nltAl q) (nltM t x q) t x k q (hrlVL t x) (nsrLp q) (nsrFl t x q) := by
  have hx0 : 17 / 60 ≤ x := by linarith
  have hx1 : x ≤ 4 / 7 := by linarith
  have hx : 0 < x := by linarith
  have hq0 : 0 < q := by linarith
  have ht : 0 < t := by linarith
  have hW : 0 < 1 + x := by linarith
  -- `y = q - 1 ≤ (29 - 60t)/32 < b(t)`, `y ≤ 9/32`
  have hy : (q - 1) * (1 + 2 * (2 * t + x - 1)) ≤ (1 - 2 * t) - (2 * t + x - 1) := by nlinarith
  have hyb : q - 1 ≤ (29 - 60 * t) / 32 := by
    have : 16 / 15 * (q - 1) ≤ (q - 1) * (1 + 2 * (2 * t + x - 1)) := by nlinarith
    linarith
  have hy9 : q - 1 ≤ 9 / 32 := by linarith
  -- the comparison derivative is positive
  have hKend : 0 < hrsK (nltAl q) t x (2 * t + x) q (nltVbar t x) (nltLbar q) := by
    have e := nlt_Kend_eq t x q hW
    have hS := nlt_SS_pos ht0 ht1 hx0 hx1 (by linarith : (0 : ℝ) ≤ q - 1) (by linarith)
    have : 0 < q ^ 2 * nltSS t x (q - 1) := by positivity
    rw [← e] at this
    exact pos_of_mul_pos_right this (by positivity)
  -- the slopes and the comparisons `V_L < V̄`, `L₊ ≤ L̄`
  have hKv : hrsKv (nltAl q) t x q < 0 := by
    rw [nlt_Kv_eq]
    have := nlt_Bs_pos ht0 ht1 hx0 (by linarith : (0 : ℝ) ≤ q - 1) hy9
    have : 0 < 2 * q ^ 2 * (1 + x) * nltBs t x (q - 1) := by positivity
    linarith
  have hV : hrlVL t x < nltVbar t x := by
    have e : nltVbar t x - hrlVL t x = (1 - t) * x ^ 2 * (73 - 119 * x) /
        (24 * (17 * x + 76) * (1 + x) ^ 2) := by
      unfold nltVbar hrlVL; field_simp; ring
    have : 0 < (1 - t) * x ^ 2 * (73 - 119 * x) / (24 * (17 * x + 76) * (1 + x) ^ 2) := by
      have : 0 < 73 - 119 * x := by linarith
      have : 0 < 1 - t := by linarith
      positivity
    linarith
  have hL : nsrLp q ≤ nltLbar q := by
    have e : nltLbar q - nsrLp q = (q - 1) ^ 2 * (2 + 5 * q - 5 * q ^ 2) / (12 * q * (q + 1)) := by
      unfold nltLbar nsrLp; field_simp; ring
    have : 0 ≤ 2 + 5 * q - 5 * q ^ 2 := by nlinarith
    have : 0 ≤ (q - 1) ^ 2 * (2 + 5 * q - 5 * q ^ 2) / (12 * q * (q + 1)) := by positivity
    linarith
  have hKL : hrsKL (nltAl q) t x q ≤ 0 := by
    unfold hrsKL
    apply mul_nonpos_of_nonneg_of_nonpos
    · apply mul_nonneg (by positivity)
      unfold nltAl; nlinarith
    · have : 0 ≤ t * (t + x) * (1 + x) * q := by positivity
      linarith
  have hKk : hrsKk t x q ≤ 0 := by
    unfold hrsKk
    apply mul_nonpos_of_nonneg_of_nonpos
    · have h1 : (t + x) * (1 + x) ≤ t + x * (x + 2) := by nlinarith
      have h2 := mul_le_mul_of_nonneg_right hq (by positivity : (0 : ℝ) ≤ t + x * (x + 2))
      linarith
    · have : 0 ≤ 2 * t * q ^ 4 := by positivity
      linarith
  have dec := hrs_K_dec (nltAl q) t x ((k + 1) / 2) (2 * t + x) q (hrlVL t x) (nltVbar t x)
    (nsrLp q) (nltLbar q)
  have p1 : 0 < (hrlVL t x - nltVbar t x) * hrsKv (nltAl q) t x q :=
    mul_pos_of_neg_of_neg (by linarith) hKv
  have p2 : 0 ≤ (nsrLp q - nltLbar q) * hrsKL (nltAl q) t x q :=
    mul_nonneg_of_nonpos_of_nonpos (by linarith) hKL
  have p3 : 0 ≤ ((k + 1) / 2 - (2 * t + x)) * hrsKk t x q :=
    mul_nonneg_of_nonpos_of_nonpos (by linarith) hKk
  have hK : 0 < hrsK (nltAl q) t x ((k + 1) / 2) q (hrlVL t x) (nsrLp q) := by linarith
  have e := hrs_comb_sub_k (nltAl q) (nltM t x q) t x q (hrlVL t x) (nsrLp q) (nsrFl t x q) k 1
  have : 0 ≤ (k - 1) * hrsK (nltAl q) t x ((k + 1) / 2) q (hrlVL t x) (nsrLp q) :=
    mul_nonneg (by linarith) hK.le
  linarith

end SmoothedOctagon
