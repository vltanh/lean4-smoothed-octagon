module

public import SmoothedOctagon.Exclusion.Mixed.FwdHand.LowTHorner

/-!
# Case M2, forward successor by hand: the initial `h`-derivative of the low-`t` circuit

At `h = 1/4` (`t = 3/8`, `x = j + 1/4`), `P₀ = 𝓗S = ∑ cᵢ(x) yⁱ` (`nltc0`, …, `nlt_c_eq0`, …)
satisfies `P₀ ≥ 68` on `17/60 ≤ x ≤ 3/7`, `0 ≤ y ≤ b(x) = 3931/8640 - 8x/9` (`nlt_P0_pos`). The
coefficient signs `c₁, c₅, c₆ < 0`, `c₂ < -48000`, `c₃, c₄ < 3500000x³` and `x³y < 13/2000` give
`∂_yP₀ < 0`, so `P₀(x, y) ≥ P₀(x, b(x))`.

The line value `P₀(x, b(x))` is expanded as a degree-14 polynomial in `x` and bounded by a
termwise monomial bound after a shift on two subintervals; the coefficient signs use the same
one-variable bounds.

## Main API

* `nltc0`, …, `nltc6`, `nlt_c_eq0`, …, `nlt_c_eq6`; `nlt_P0_pos`.
-/

@[expose] public section

namespace SmoothedOctagon

/-- `c_0(x)`: the `y^0`-coefficient of `𝓗S` at `h = 1/4`. -/
noncomputable def nltc0 (x : ℝ) : ℝ :=
  2470 + (3961 / 6) * x - (11376409 / 768) * x ^ 2 + (876287 / 48) * x ^ 3 - (1213663 / 64) * x ^ 4 - (192815 / 16) * x ^ 5 - (1785 / 4) * x ^ 6

theorem nlt_c_eq0 (j : ℝ) : lrhHorner (nltDer (nltL0 j)) (1 / 4) = nltc0 (j + 1 / 4) := by
  simp only [nltL0, nltDer, nltDerAux, lrhHorner]; unfold nltc0; ring

/-- `c_1(x)`: the `y^1`-coefficient of `𝓗S` at `h = 1/4`. -/
noncomputable def nltc1 (x : ℝ) : ℝ :=
  (26147 / 16) - (205551 / 16) * x + (9390957 / 512) * x ^ 2 + (1105573 / 32) * x ^ 3 - (20610059 / 128) * x ^ 4 - (3096829 / 32) * x ^ 5 - (24953 / 4) * x ^ 6 - (1687 / 4) * x ^ 7

theorem nlt_c_eq1 (j : ℝ) : lrhHorner (nltDer (nltL1 j)) (1 / 4) = nltc1 (j + 1 / 4) := by
  simp only [nltL1, nltDer, nltDerAux, lrhHorner]; unfold nltc1; ring

/-- `c_2(x)`: the `y^2`-coefficient of `𝓗S` at `h = 1/4`. -/
noncomputable def nltc2 (x : ℝ) : ℝ :=
  -(5443517 / 192) - (6826585 / 96) * x + (6734773 / 384) * x ^ 2 + (108121 / 16) * x ^ 3 - (2659679 / 16) * x ^ 4 - (4429505 / 32) * x ^ 5 - (304129 / 16) * x ^ 6 + (135469 / 8) * x ^ 7 + 2856 * x ^ 8

theorem nlt_c_eq2 (j : ℝ) : lrhHorner (nltDer (nltL2 j)) (1 / 4) = nltc2 (j + 1 / 4) := by
  simp only [nltL2, nltDer, nltDerAux, lrhHorner]; unfold nltc2; ring

/-- `c_3(x)`: the `y^3`-coefficient of `𝓗S` at `h = 1/4`. -/
noncomputable def nltc3 (x : ℝ) : ℝ :=
  -(11571361 / 384) - (256361 / 32) * x + (389312905 / 768) * x ^ 2 + (150040261 / 96) * x ^ 3 + (233452331 / 128) * x ^ 4 + (23757343 / 32) * x ^ 5 + (327123 / 8) * x ^ 6 + 2425 * x ^ 7 + 68 * x ^ 8

theorem nlt_c_eq3 (j : ℝ) : lrhHorner (nltDer (nltL3 j)) (1 / 4) = nltc3 (j + 1 / 4) := by
  simp only [nltL3, nltDer, nltDerAux, lrhHorner]; unfold nltc3; ring

/-- `c_4(x)`: the `y^4`-coefficient of `𝓗S` at `h = 1/4`. -/
noncomputable def nltc4 (x : ℝ) : ℝ :=
  -(4352657 / 128) - (691873 / 8) * x + (113788653 / 256) * x ^ 2 + (15305443 / 8) * x ^ 3 + (19033415 / 8) * x ^ 4 + (8180407 / 8) * x ^ 5 + (532071 / 8) * x ^ 6 - (95565 / 8) * x ^ 7 - 1972 * x ^ 8

theorem nlt_c_eq4 (j : ℝ) : lrhHorner (nltDer (nltL4 j)) (1 / 4) = nltc4 (j + 1 / 4) := by
  simp only [nltL4, nltDer, nltDerAux, lrhHorner]; unfold nltc4; ring

/-- `c_5(x)`: the `y^5`-coefficient of `𝓗S` at `h = 1/4`. -/
noncomputable def nltc5 (x : ℝ) : ℝ :=
  -(4156227 / 128) - (8970893 / 64) * x - (42983895 / 512) * x ^ 2 + (5365343 / 16) * x ^ 3 + (67540595 / 128) * x ^ 4 + (3581741 / 16) * x ^ 5 + (375341 / 32) * x ^ 6 + (7295 / 2) * x ^ 7 + 1088 * x ^ 8

theorem nlt_c_eq5 (j : ℝ) : lrhHorner (nltDer (nltL5 j)) (1 / 4) = nltc5 (j + 1 / 4) := by
  simp only [nltL5, nltDer, nltDerAux, lrhHorner]; unfold nltc5; ring

/-- `c_6(x)`: the `y^6`-coefficient of `𝓗S` at `h = 1/4`. -/
noncomputable def nltc6 (x : ℝ) : ℝ :=
  -(14967 / 16) - (220227 / 64) * x - (640115 / 128) * x ^ 2 - (74907 / 16) * x ^ 3 - (72295 / 32) * x ^ 4 - (7881 / 8) * x ^ 5 - (767 / 4) * x ^ 6 + 270 * x ^ 7 + 68 * x ^ 8

theorem nlt_c_eq6 (j : ℝ) : lrhHorner (nltDer (nltL6 j)) (1 / 4) = nltc6 (j + 1 / 4) := by
  simp only [nltL6, nltDer, nltDerAux, lrhHorner]; unfold nltc6; ring

/-- `-c₁(x)`, a coefficient sign for `∂_yP₀ < 0`. -/
noncomputable def nltIc1 (x : ℝ) : ℝ := -nltc1 x

/-- `nltIc1 > 0` on `[17/60, 3/7]`. -/
theorem nltIc1_pos {x : ℝ} (h1 : (17 / 60) ≤ x) (h2 : x ≤ (3 / 7)) : 0 < nltIc1 x := by
  obtain ⟨z, rfl⟩ : ∃ z, x = (17 / 60) + z := ⟨x - (17 / 60), by ring⟩
  have z0 : 0 ≤ z := by linarith
  have z1 : z ≤ (61 / 420) := by linarith
  have p2 : z ^ 2 ≤ (61 / 420) * z ^ 1 := nlt_pw z0 z1 1
  have q2 : 0 ≤ z ^ 2 := pow_nonneg z0 2
  have p3 : z ^ 3 ≤ (61 / 420) * z ^ 2 := nlt_pw z0 z1 2
  have q3 : 0 ≤ z ^ 3 := pow_nonneg z0 3
  have p4 : z ^ 4 ≤ (61 / 420) * z ^ 3 := nlt_pw z0 z1 3
  have q4 : 0 ≤ z ^ 4 := pow_nonneg z0 4
  have p5 : z ^ 5 ≤ (61 / 420) * z ^ 4 := nlt_pw z0 z1 4
  have q5 : 0 ≤ z ^ 5 := pow_nonneg z0 5
  have p6 : z ^ 6 ≤ (61 / 420) * z ^ 5 := nlt_pw z0 z1 5
  have q6 : 0 ≤ z ^ 6 := pow_nonneg z0 6
  have p7 : z ^ 7 ≤ (61 / 420) * z ^ 6 := nlt_pw z0 z1 6
  have q7 : 0 ≤ z ^ 7 := pow_nonneg z0 7
  have e : nltIc1 ((17 / 60) + z) = (10807560892333871 / 11197440000000) + (2233970933756131 / 186624000000) * z + (54410055104213 / 1036800000) * z ^ 2 + (2369691867949 / 10368000) * z ^ 3 + (52870394177 / 172800) * z ^ 4 + (518841271 / 4800) * z ^ 5 + (1697933 / 240) * z ^ 6 + (1687 / 4) * z ^ 7 := by unfold nltIc1 nltc1; ring
  rw [e]; linarith only [z0, z1, p2, q2, p3, q3, p4, q4, p5, q5, p6, q6, p7, q7]


/-- `-c₂(x)`, a coefficient sign for `∂_yP₀ < 0`. -/
noncomputable def nltIc2 (x : ℝ) : ℝ := -nltc2 x

/-- `nltIc2 > 48000` on `[17/60, 3/7]`. -/
theorem nltIc2_pos {x : ℝ} (h1 : (17 / 60) ≤ x) (h2 : x ≤ (3 / 7)) : 48000 < nltIc2 x := by
  obtain ⟨z, rfl⟩ : ∃ z, x = (17 / 60) + z := ⟨x - (17 / 60), by ring⟩
  have z0 : 0 ≤ z := by linarith
  have z1 : z ≤ (61 / 420) := by linarith
  have p2 : z ^ 2 ≤ (61 / 420) * z ^ 1 := nlt_pw z0 z1 1
  have q2 : 0 ≤ z ^ 2 := pow_nonneg z0 2
  have p3 : z ^ 3 ≤ (61 / 420) * z ^ 2 := nlt_pw z0 z1 2
  have q3 : 0 ≤ z ^ 3 := pow_nonneg z0 3
  have p4 : z ^ 4 ≤ (61 / 420) * z ^ 3 := nlt_pw z0 z1 3
  have q4 : 0 ≤ z ^ 4 := pow_nonneg z0 4
  have p5 : z ^ 5 ≤ (61 / 420) * z ^ 4 := nlt_pw z0 z1 4
  have q5 : 0 ≤ z ^ 5 := pow_nonneg z0 5
  have p6 : z ^ 6 ≤ (61 / 420) * z ^ 5 := nlt_pw z0 z1 5
  have q6 : 0 ≤ z ^ 6 := pow_nonneg z0 6
  have p7 : z ^ 7 ≤ (61 / 420) * z ^ 6 := nlt_pw z0 z1 6
  have q7 : 0 ≤ z ^ 7 := pow_nonneg z0 7
  have p8 : z ^ 8 ≤ (61 / 420) * z ^ 7 := nlt_pw z0 z1 7
  have q8 : 0 ≤ z ^ 8 := pow_nonneg z0 8
  have e : nltIc2 ((17 / 60) + z) = (1801636828156307267 / 37324800000000) + (147940735163592929 / 1866240000000) * z + (2781207778023757 / 31104000000) * z ^ 2 + (51372377630719 / 172800000) * z ^ 3 + (640133533279 / 1728000) * z ^ 4 + (19951295683 / 144000) * z ^ 5 - (16797291 / 800) * z ^ 6 - (936289 / 40) * z ^ 7 - 2856 * z ^ 8 := by unfold nltIc2 nltc2; ring
  rw [e]; linarith only [z0, z1, p2, q2, p3, q3, p4, q4, p5, q5, p6, q6, p7, q7, p8, q8]


/-- `3500000x³ - c₃(x)`, a coefficient sign for `∂_yP₀ < 0`. -/
noncomputable def nltIc3 (x : ℝ) : ℝ := 3500000 * x ^ 3 - nltc3 x

/-- `nltIc3 > 0` on `[17/60, 3/7]`. -/
theorem nltIc3_pos {x : ℝ} (h1 : (17 / 60) ≤ x) (h2 : x ≤ (3 / 7)) : 0 < nltIc3 x := by
  obtain ⟨z, rfl⟩ : ∃ z, x = (17 / 60) + z := ⟨x - (17 / 60), by ring⟩
  have z0 : 0 ≤ z := by linarith
  have z1 : z ≤ (61 / 420) := by linarith
  have p2 : z ^ 2 ≤ (61 / 420) * z ^ 1 := nlt_pw z0 z1 1
  have q2 : 0 ≤ z ^ 2 := pow_nonneg z0 2
  have p3 : z ^ 3 ≤ (61 / 420) * z ^ 2 := nlt_pw z0 z1 2
  have q3 : 0 ≤ z ^ 3 := pow_nonneg z0 3
  have p4 : z ^ 4 ≤ (61 / 420) * z ^ 3 := nlt_pw z0 z1 3
  have q4 : 0 ≤ z ^ 4 := pow_nonneg z0 4
  have p5 : z ^ 5 ≤ (61 / 420) * z ^ 4 := nlt_pw z0 z1 4
  have q5 : 0 ≤ z ^ 5 := pow_nonneg z0 5
  have p6 : z ^ 6 ≤ (61 / 420) * z ^ 5 := nlt_pw z0 z1 5
  have q6 : 0 ≤ z ^ 6 := pow_nonneg z0 6
  have p7 : z ^ 7 ≤ (61 / 420) * z ^ 6 := nlt_pw z0 z1 6
  have q7 : 0 ≤ z ^ 7 := pow_nonneg z0 7
  have p8 : z ^ 8 ≤ (61 / 420) * z ^ 7 := nlt_pw z0 z1 7
  have q8 : 0 ≤ z ^ 8 := pow_nonneg z0 8
  have e : nltIc3 ((17 / 60) + z) = (1901161447505072681 / 83980800000000) - (4261017095607781 / 1399680000000) * z + (2057586706009937 / 23328000000) * z ^ 2 - (72423364600807 / 97200000) * z ^ 3 - (3793137626471 / 1296000) * z ^ 4 - (88139379577 / 108000) * z ^ 5 - (82535053 / 1800) * z ^ 6 - (38687 / 15) * z ^ 7 - 68 * z ^ 8 := by unfold nltIc3 nltc3; ring
  rw [e]; linarith only [z0, z1, p2, q2, p3, q3, p4, q4, p5, q5, p6, q6, p7, q7, p8, q8]


/-- `3500000x³ - c₄(x)`, a coefficient sign for `∂_yP₀ < 0`. -/
noncomputable def nltIc4 (x : ℝ) : ℝ := 3500000 * x ^ 3 - nltc4 x

/-- `nltIc4 > 0` on `[17/60, 3/7]`. -/
theorem nltIc4_pos {x : ℝ} (h1 : (17 / 60) ≤ x) (h2 : x ≤ (3 / 7)) : 0 < nltIc4 x := by
  obtain ⟨z, rfl⟩ : ∃ z, x = (17 / 60) + z := ⟨x - (17 / 60), by ring⟩
  have z0 : 0 ≤ z := by linarith
  have z1 : z ≤ (61 / 420) := by linarith
  have p2 : z ^ 2 ≤ (61 / 420) * z ^ 1 := nlt_pw z0 z1 1
  have q2 : 0 ≤ z ^ 2 := pow_nonneg z0 2
  have p3 : z ^ 3 ≤ (61 / 420) * z ^ 2 := nlt_pw z0 z1 2
  have q3 : 0 ≤ z ^ 3 := pow_nonneg z0 3
  have p4 : z ^ 4 ≤ (61 / 420) * z ^ 3 := nlt_pw z0 z1 3
  have q4 : 0 ≤ z ^ 4 := pow_nonneg z0 4
  have p5 : z ^ 5 ≤ (61 / 420) * z ^ 4 := nlt_pw z0 z1 4
  have q5 : 0 ≤ z ^ 5 := pow_nonneg z0 5
  have p6 : z ^ 6 ≤ (61 / 420) * z ^ 5 := nlt_pw z0 z1 5
  have q6 : 0 ≤ z ^ 6 := pow_nonneg z0 6
  have p7 : z ^ 7 ≤ (61 / 420) * z ^ 6 := nlt_pw z0 z1 6
  have q7 : 0 ≤ z ^ 7 := pow_nonneg z0 7
  have p8 : z ^ 8 ≤ (61 / 420) * z ^ 7 := nlt_pw z0 z1 7
  have q8 : 0 ≤ z ^ 8 := pow_nonneg z0 8
  have e : nltIc4 ((17 / 60) + z) = (14003626680138920879 / 335923200000000) - (186583558642197379 / 5598720000000) * z - (44807122690324117 / 93312000000) * z ^ 2 - (3044803615645927 / 1555200000) * z ^ 3 - (20204531213039 / 5184000) * z ^ 4 - (480801231193 / 432000) * z ^ 5 - (276365527 / 7200) * z ^ 6 + (1969859 / 120) * z ^ 7 + 1972 * z ^ 8 := by unfold nltIc4 nltc4; ring
  rw [e]; linarith only [z0, z1, p2, q2, p3, q3, p4, q4, p5, q5, p6, q6, p7, q7, p8, q8]


/-- `-c₅(x)`, a coefficient sign for `∂_yP₀ < 0`. -/
noncomputable def nltIc5 (x : ℝ) : ℝ := -nltc5 x

/-- `nltIc5 > 0` on `[17/60, 3/7]`. -/
theorem nltIc5_pos {x : ℝ} (h1 : (17 / 60) ≤ x) (h2 : x ≤ (3 / 7)) : 0 < nltIc5 x := by
  obtain ⟨z, rfl⟩ : ∃ z, x = (17 / 60) + z := ⟨x - (17 / 60), by ring⟩
  have z0 : 0 ≤ z := by linarith
  have z1 : z ≤ (61 / 420) := by linarith
  have p2 : z ^ 2 ≤ (61 / 420) * z ^ 1 := nlt_pw z0 z1 1
  have q2 : 0 ≤ z ^ 2 := pow_nonneg z0 2
  have p3 : z ^ 3 ≤ (61 / 420) * z ^ 2 := nlt_pw z0 z1 2
  have q3 : 0 ≤ z ^ 3 := pow_nonneg z0 3
  have p4 : z ^ 4 ≤ (61 / 420) * z ^ 3 := nlt_pw z0 z1 3
  have q4 : 0 ≤ z ^ 4 := pow_nonneg z0 4
  have p5 : z ^ 5 ≤ (61 / 420) * z ^ 4 := nlt_pw z0 z1 4
  have q5 : 0 ≤ z ^ 5 := pow_nonneg z0 5
  have p6 : z ^ 6 ≤ (61 / 420) * z ^ 5 := nlt_pw z0 z1 5
  have q6 : 0 ≤ z ^ 6 := pow_nonneg z0 6
  have p7 : z ^ 7 ≤ (61 / 420) * z ^ 6 := nlt_pw z0 z1 6
  have q7 : 0 ≤ z ^ 7 := pow_nonneg z0 7
  have p8 : z ^ 8 ≤ (61 / 420) * z ^ 7 := nlt_pw z0 z1 7
  have q8 : 0 ≤ z ^ 8 := pow_nonneg z0 8
  have e : nltIc5 ((17 / 60) + z) = (22668685040099743259 / 335923200000000) + (144503692692508183 / 2799360000000) * z - (47350669476331807 / 93312000000) * z ^ 2 - (108798707970787 / 97200000) * z ^ 3 - (4470230186519 / 5184000) * z ^ 4 - (54288081389 / 216000) * z ^ 5 - (154146217 / 7200) * z ^ 6 - (183409 / 30) * z ^ 7 - 1088 * z ^ 8 := by unfold nltIc5 nltc5; ring
  rw [e]; linarith only [z0, z1, p2, q2, p3, q3, p4, q4, p5, q5, p6, q6, p7, q7, p8, q8]


/-- `-c₆(x)`, a coefficient sign for `∂_yP₀ < 0`. -/
noncomputable def nltIc6 (x : ℝ) : ℝ := -nltc6 x

/-- `nltIc6 > 0` on `[17/60, 3/7]`. -/
theorem nltIc6_pos {x : ℝ} (h1 : (17 / 60) ≤ x) (h2 : x ≤ (3 / 7)) : 0 < nltIc6 x := by
  obtain ⟨z, rfl⟩ : ∃ z, x = (17 / 60) + z := ⟨x - (17 / 60), by ring⟩
  have z0 : 0 ≤ z := by linarith
  have z1 : z ≤ (61 / 420) := by linarith
  have p2 : z ^ 2 ≤ (61 / 420) * z ^ 1 := nlt_pw z0 z1 1
  have q2 : 0 ≤ z ^ 2 := pow_nonneg z0 2
  have p3 : z ^ 3 ≤ (61 / 420) * z ^ 2 := nlt_pw z0 z1 2
  have q3 : 0 ≤ z ^ 3 := pow_nonneg z0 3
  have p4 : z ^ 4 ≤ (61 / 420) * z ^ 3 := nlt_pw z0 z1 3
  have q4 : 0 ≤ z ^ 4 := pow_nonneg z0 4
  have p5 : z ^ 5 ≤ (61 / 420) * z ^ 4 := nlt_pw z0 z1 4
  have q5 : 0 ≤ z ^ 5 := pow_nonneg z0 5
  have p6 : z ^ 6 ≤ (61 / 420) * z ^ 5 := nlt_pw z0 z1 5
  have q6 : 0 ≤ z ^ 6 := pow_nonneg z0 6
  have p7 : z ^ 7 ≤ (61 / 420) * z ^ 6 := nlt_pw z0 z1 6
  have q7 : 0 ≤ z ^ 7 := pow_nonneg z0 7
  have p8 : z ^ 8 ≤ (61 / 420) * z ^ 7 := nlt_pw z0 z1 7
  have q8 : 0 ≤ z ^ 8 := pow_nonneg z0 8
  have e : nltIc6 ((17 / 60) + z) = (3194896903975829 / 1312200000000) + (2673644000674361 / 349920000000) * z + (120136766892931 / 11664000000) * z ^ 2 + (782688073193 / 97200000) * z ^ 3 + (2358779477 / 648000) * z ^ 4 + (20771387 / 27000) * z ^ 5 - (446939 / 900) * z ^ 6 - (6362 / 15) * z ^ 7 - 68 * z ^ 8 := by unfold nltIc6 nltc6; ring
  rw [e]; linarith only [z0, z1, p2, q2, p3, q3, p4, q4, p5, q5, p6, q6, p7, q7, p8, q8]


/-- `13/2000 - x³b(x)`, which bounds `x³y` for `y ≤ b(x)`. -/
noncomputable def nltIcb (x : ℝ) : ℝ := 13 / 2000 - x ^ 3 * (3931 / 8640 - 8 / 9 * x)

/-- `nltIcb > 0` on `[17/60, 3/7]`. -/
theorem nltIcb_pos {x : ℝ} (h1 : (17 / 60) ≤ x) (h2 : x ≤ (3 / 7)) : 0 < nltIcb x := by
  rcases le_total x (299 / 840) with hm | hm
  · obtain ⟨z, rfl⟩ : ∃ z, x = (299 / 840) - z := ⟨(299 / 840) - x, by ring⟩
    have z0 : 0 ≤ z := by linarith
    have z1 : z ≤ (61 / 840) := by linarith
    have p2 : z ^ 2 ≤ (61 / 840) * z ^ 1 := nlt_pw z0 z1 1
    have q2 : 0 ≤ z ^ 2 := pow_nonneg z0 2
    have p3 : z ^ 3 ≤ (61 / 840) * z ^ 2 := nlt_pw z0 z1 2
    have q3 : 0 ≤ z ^ 3 := pow_nonneg z0 3
    have p4 : z ^ 4 ≤ (61 / 840) * z ^ 3 := nlt_pw z0 z1 3
    have q4 : 0 ≤ z ^ 4 := pow_nonneg z0 4
    have e : nltIcb ((299 / 840) - z) = (8972131961 / 35846737920000) + (537031807 / 42674688000) * z + (71461 / 376320) * z ^ 2 - (49027 / 60480) * z ^ 3 + (8 / 9) * z ^ 4 := by unfold nltIcb; ring
    rw [e]; linarith only [z0, z1, p2, q2, p3, q3, p4, q4]
  · rcases le_total x (659 / 1680) with hm | hm
    · rcases le_total x (419 / 1120) with hm | hm
      · obtain ⟨z, rfl⟩ : ∃ z, x = (299 / 840) + z := ⟨x - (299 / 840), by ring⟩
        have z0 : 0 ≤ z := by linarith
        have z1 : z ≤ (61 / 3360) := by linarith
        have p2 : z ^ 2 ≤ (61 / 3360) * z ^ 1 := nlt_pw z0 z1 1
        have q2 : 0 ≤ z ^ 2 := pow_nonneg z0 2
        have p3 : z ^ 3 ≤ (61 / 3360) * z ^ 2 := nlt_pw z0 z1 2
        have q3 : 0 ≤ z ^ 3 := pow_nonneg z0 3
        have p4 : z ^ 4 ≤ (61 / 3360) * z ^ 3 := nlt_pw z0 z1 3
        have q4 : 0 ≤ z ^ 4 := pow_nonneg z0 4
        have e : nltIcb ((299 / 840) + z) = (8972131961 / 35846737920000) - (537031807 / 42674688000) * z + (71461 / 376320) * z ^ 2 + (49027 / 60480) * z ^ 3 + (8 / 9) * z ^ 4 := by unfold nltIcb; ring
        rw [e]; linarith only [z0, z1, p2, q2, p3, q3, p4, q4]
      · obtain ⟨z, rfl⟩ : ∃ z, x = (419 / 1120) + z := ⟨x - (419 / 1120), by ring⟩
        have z0 : 0 ≤ z := by linarith
        have z1 : z ≤ (61 / 3360) := by linarith
        have p2 : z ^ 2 ≤ (61 / 3360) * z ^ 1 := nlt_pw z0 z1 1
        have q2 : 0 ≤ z ^ 2 := pow_nonneg z0 2
        have p3 : z ^ 3 ≤ (61 / 3360) * z ^ 2 := nlt_pw z0 z1 2
        have q3 : 0 ≤ z ^ 3 := pow_nonneg z0 3
        have p4 : z ^ 4 ≤ (61 / 3360) * z ^ 3 := nlt_pw z0 z1 3
        have q4 : 0 ≤ z ^ 4 := pow_nonneg z0 4
        have e : nltIcb ((419 / 1120) + z) = (1518611693 / 16994009088000) - (123068261 / 25288704000) * z + (5324233 / 22579200) * z ^ 2 + (52931 / 60480) * z ^ 3 + (8 / 9) * z ^ 4 := by unfold nltIcb; ring
        rw [e]; linarith only [z0, z1, p2, q2, p3, q3, p4, q4]
    · obtain ⟨z, rfl⟩ : ∃ z, x = (659 / 1680) + z := ⟨x - (659 / 1680), by ring⟩
      have z0 : 0 ≤ z := by linarith
      have z1 : z ≤ (61 / 1680) := by linarith
      have p2 : z ^ 2 ≤ (61 / 1680) * z ^ 1 := nlt_pw z0 z1 1
      have q2 : 0 ≤ z ^ 2 := pow_nonneg z0 2
      have p3 : z ^ 3 ≤ (61 / 1680) * z ^ 2 := nlt_pw z0 z1 2
      have q3 : 0 ≤ z ^ 3 := pow_nonneg z0 3
      have p4 : z ^ 4 ≤ (61 / 1680) * z ^ 3 := nlt_pw z0 z1 3
      have q4 : 0 ≤ z ^ 4 := pow_nonneg z0 4
      have e : nltIcb ((659 / 1680) + z) = (8035760683 / 95591301120000) + (782140081 / 170698752000) * z + (9660281 / 33868800) * z ^ 2 + (421 / 448) * z ^ 3 + (8 / 9) * z ^ 4 := by unfold nltIcb; ring
      rw [e]; linarith only [z0, z1, p2, q2, p3, q3, p4, q4]


/-- The line value `P₀(x, b(x))`, `b(x) = 3931/8640 - 8x/9`. -/
noncomputable def nltIline (x : ℝ) : ℝ := nltc0 x + nltc1 x * (3931 / 8640 - 8 / 9 * x) ^ 1 + nltc2 x * (3931 / 8640 - 8 / 9 * x) ^ 2 + nltc3 x * (3931 / 8640 - 8 / 9 * x) ^ 3 + nltc4 x * (3931 / 8640 - 8 / 9 * x) ^ 4 + nltc5 x * (3931 / 8640 - 8 / 9 * x) ^ 5 + nltc6 x * (3931 / 8640 - 8 / 9 * x) ^ 6

/-- `nltIline > 68` on `[17/60, 3/7]`. -/
theorem nltIline_pos {x : ℝ} (h1 : (17 / 60) ≤ x) (h2 : x ≤ (3 / 7)) : 68 < nltIline x := by
  rcases le_total x (299 / 840) with hm | hm
  · obtain ⟨z, rfl⟩ : ∃ z, x = (17 / 60) + z := ⟨x - (17 / 60), by ring⟩
    have z0 : 0 ≤ z := by linarith
    have z1 : z ≤ (61 / 840) := by linarith
    have p2 : z ^ 2 ≤ (61 / 840) * z ^ 1 := nlt_pw z0 z1 1
    have q2 : 0 ≤ z ^ 2 := pow_nonneg z0 2
    have p3 : z ^ 3 ≤ (61 / 840) * z ^ 2 := nlt_pw z0 z1 2
    have q3 : 0 ≤ z ^ 3 := pow_nonneg z0 3
    have p4 : z ^ 4 ≤ (61 / 840) * z ^ 3 := nlt_pw z0 z1 3
    have q4 : 0 ≤ z ^ 4 := pow_nonneg z0 4
    have p5 : z ^ 5 ≤ (61 / 840) * z ^ 4 := nlt_pw z0 z1 4
    have q5 : 0 ≤ z ^ 5 := pow_nonneg z0 5
    have p6 : z ^ 6 ≤ (61 / 840) * z ^ 5 := nlt_pw z0 z1 5
    have q6 : 0 ≤ z ^ 6 := pow_nonneg z0 6
    have p7 : z ^ 7 ≤ (61 / 840) * z ^ 6 := nlt_pw z0 z1 6
    have q7 : 0 ≤ z ^ 7 := pow_nonneg z0 7
    have p8 : z ^ 8 ≤ (61 / 840) * z ^ 7 := nlt_pw z0 z1 7
    have q8 : 0 ≤ z ^ 8 := pow_nonneg z0 8
    have p9 : z ^ 9 ≤ (61 / 840) * z ^ 8 := nlt_pw z0 z1 8
    have q9 : 0 ≤ z ^ 9 := pow_nonneg z0 9
    have p10 : z ^ 10 ≤ (61 / 840) * z ^ 9 := nlt_pw z0 z1 9
    have q10 : 0 ≤ z ^ 10 := pow_nonneg z0 10
    have p11 : z ^ 11 ≤ (61 / 840) * z ^ 10 := nlt_pw z0 z1 10
    have q11 : 0 ≤ z ^ 11 := pow_nonneg z0 11
    have p12 : z ^ 12 ≤ (61 / 840) * z ^ 11 := nlt_pw z0 z1 11
    have q12 : 0 ≤ z ^ 12 := pow_nonneg z0 12
    have p13 : z ^ 13 ≤ (61 / 840) * z ^ 12 := nlt_pw z0 z1 12
    have q13 : 0 ≤ z ^ 13 := pow_nonneg z0 13
    have p14 : z ^ 14 ≤ (61 / 840) * z ^ 13 := nlt_pw z0 z1 13
    have q14 : 0 ≤ z ^ 14 := pow_nonneg z0 14
    have e : nltIline ((17 / 60) + z) = (25094595692146902147805117 / 360694789491916800000000) + (9533644918985900819141679979 / 1082084368475750400000000) * z - (1207187964621924707938317499939 / 14608138974422630400000000) * z ^ 2 + (1621641912197340648285455161673 / 16434156346225459200000000) * z ^ 3 + (12818022764789119543437294051389 / 24651234519338188800000000) * z ^ 4 - (59454134434493800871448790153181 / 83197916502766387200000000) * z ^ 5 - (732061364859376379736911638735717 / 374390624262448742400000000) * z ^ 6 - (569703188596965258564800506139 / 3119921868853739520000000) * z ^ 7 + (116114180031936886980279612761 / 103997395628457984000000) * z ^ 8 + (2230445239989043514061551 / 6770663777894400000) * z ^ 9 - (1344353957188447109 / 14105549537280) * z ^ 10 - (1035964893324767 / 57395628000) * z ^ 11 - (472260178276 / 119574225) * z ^ 12 - (3511816192 / 7971615) * z ^ 13 + (17825792 / 531441) * z ^ 14 := by unfold nltIline nltc0 nltc1 nltc2 nltc3 nltc4 nltc5 nltc6; ring
    rw [e]; linarith only [z0, z1, p2, q2, p3, q3, p4, q4, p5, q5, p6, q6, p7, q7, p8, q8, p9, q9, p10, q10, p11, q11, p12, q12, p13, q13, p14, q14]
  · obtain ⟨z, rfl⟩ : ∃ z, x = (3 / 7) - z := ⟨(3 / 7) - x, by ring⟩
    have z0 : 0 ≤ z := by linarith
    have z1 : z ≤ (61 / 840) := by linarith
    have p2 : z ^ 2 ≤ (61 / 840) * z ^ 1 := nlt_pw z0 z1 1
    have q2 : 0 ≤ z ^ 2 := pow_nonneg z0 2
    have p3 : z ^ 3 ≤ (61 / 840) * z ^ 2 := nlt_pw z0 z1 2
    have q3 : 0 ≤ z ^ 3 := pow_nonneg z0 3
    have p4 : z ^ 4 ≤ (61 / 840) * z ^ 3 := nlt_pw z0 z1 3
    have q4 : 0 ≤ z ^ 4 := pow_nonneg z0 4
    have p5 : z ^ 5 ≤ (61 / 840) * z ^ 4 := nlt_pw z0 z1 4
    have q5 : 0 ≤ z ^ 5 := pow_nonneg z0 5
    have p6 : z ^ 6 ≤ (61 / 840) * z ^ 5 := nlt_pw z0 z1 5
    have q6 : 0 ≤ z ^ 6 := pow_nonneg z0 6
    have p7 : z ^ 7 ≤ (61 / 840) * z ^ 6 := nlt_pw z0 z1 6
    have q7 : 0 ≤ z ^ 7 := pow_nonneg z0 7
    have p8 : z ^ 8 ≤ (61 / 840) * z ^ 7 := nlt_pw z0 z1 7
    have q8 : 0 ≤ z ^ 8 := pow_nonneg z0 8
    have p9 : z ^ 9 ≤ (61 / 840) * z ^ 8 := nlt_pw z0 z1 8
    have q9 : 0 ≤ z ^ 9 := pow_nonneg z0 9
    have p10 : z ^ 10 ≤ (61 / 840) * z ^ 9 := nlt_pw z0 z1 9
    have q10 : 0 ≤ z ^ 10 := pow_nonneg z0 10
    have p11 : z ^ 11 ≤ (61 / 840) * z ^ 10 := nlt_pw z0 z1 10
    have q11 : 0 ≤ z ^ 11 := pow_nonneg z0 11
    have p12 : z ^ 12 ≤ (61 / 840) * z ^ 11 := nlt_pw z0 z1 11
    have q12 : 0 ≤ z ^ 12 := pow_nonneg z0 12
    have p13 : z ^ 13 ≤ (61 / 840) * z ^ 12 := nlt_pw z0 z1 12
    have q13 : 0 ≤ z ^ 13 := pow_nonneg z0 13
    have p14 : z ^ 14 ≤ (61 / 840) * z ^ 13 := nlt_pw z0 z1 13
    have q14 : 0 ≤ z ^ 14 := pow_nonneg z0 14
    have e : nltIline ((3 / 7) - z) = (2411791843488518369968269030172923143 / 32100549168435624809798622511104000) + (2419701346697963006653878593800835797 / 491334936251565685864264630272000) * z - (36709574003888779818437263052928690629 / 4211442310727705878836553973760000) * z ^ 2 - (16500468825410167306955999138467279757 / 125340544962134103536802201600000) * z ^ 3 - (9208370340386867164936973900464679519 / 15347821832098053494302310400000) * z ^ 4 + (14651094524817464510137637925923938967 / 6394925763374188955959296000000) * z ^ 5 - (1927026328239735383730177237234180353 / 1370341235008754776276992000000) * z ^ 6 - (75765169841426089335139173515208323 / 57097551458698115678208000000) * z ^ 7 + (2528526948187421656544149110673679 / 1747884228327493337088000000) * z ^ 8 - (906388186388330609661052933 / 5418787910241484800000) * z ^ 9 - (5241897488430872509609 / 40318362427392000) * z ^ 10 + (2058699857092229 / 80353879200) * z ^ 11 - (263209724548 / 55801305) * z ^ 12 + (989376512 / 2657205) * z ^ 13 + (17825792 / 531441) * z ^ 14 := by unfold nltIline nltc0 nltc1 nltc2 nltc3 nltc4 nltc5 nltc6; ring
    rw [e]; linarith only [z0, z1, p2, q2, p3, q3, p4, q4, p5, q5, p6, q6, p7, q7, p8, q8, p9, q9, p10, q10, p11, q11, p12, q12, p13, q13, p14, q14]


/-- **The initial derivative**: `P₀ = 𝓗S(3/8, x, 1 + y)
≥ 68` for `17/60 ≤ x ≤ 3/7`, `0 ≤ y ≤ 3931/8640 - 8x/9`. -/
theorem nlt_P0_pos {x y : ℝ} (h1 : 17 / 60 ≤ x) (h2 : x ≤ 3 / 7) (hy0 : 0 ≤ y)
    (hy : y ≤ 3931 / 8640 - 8 / 9 * x) :
    68 < nltc0 x + nltc1 x * y + nltc2 x * y ^ 2 + nltc3 x * y ^ 3 + nltc4 x * y ^ 4
      + nltc5 x * y ^ 5 + nltc6 x * y ^ 6 := by
  have b1 := nltIc1_pos h1 h2
  have b2 := nltIc2_pos h1 h2
  have b3 := nltIc3_pos h1 h2
  have b4 := nltIc4_pos h1 h2
  have b5 := nltIc5_pos h1 h2
  have b6 := nltIc6_pos h1 h2
  have bb := nltIcb_pos h1 h2
  have bl := nltIline_pos h1 h2
  unfold nltIc1 nltIc2 nltIc3 nltIc4 nltIc5 nltIc6 nltIcb nltIline at *
  have hx3 : 0 ≤ x ^ 3 := by positivity
  set cs : List ℝ := [nltc0 x, nltc1 x, nltc2 x, nltc3 x, nltc4 x, nltc5 x, nltc6 x] with hcs
  have hf : ∀ w, lrhHorner cs w = nltc0 x + nltc1 x * w + nltc2 x * w ^ 2 + nltc3 x * w ^ 3
      + nltc4 x * w ^ 4 + nltc5 x * w ^ 5 + nltc6 x * w ^ 6 := fun w => by
    rw [hcs]; simp only [lrhHorner]; ring
  have hf1 : ∀ w, lrhHorner (nltDer cs) w = nltc1 x + 2 * nltc2 x * w + 3 * nltc3 x * w ^ 2
      + 4 * nltc4 x * w ^ 3 + 5 * nltc5 x * w ^ 4 + 6 * nltc6 x * w ^ 5 := fun w => by
    rw [hcs]; simp only [nltDer, nltDerAux, lrhHorner]; ring
  -- `∂_yP₀ < 0` on `[0, b(x)]`
  have neg : ∀ w, y ≤ w → w ≤ 3931 / 8640 - 8 / 9 * x → lrhHorner (nltDer cs) w ≤ 0 := by
    intro w w0 w1
    rw [hf1]
    have w0' : 0 ≤ w := by linarith
    have w13 : w ≤ 13 / 64 := by linarith
    have hxw : x ^ 3 * w ≤ 13 / 2000 := by
      have := mul_le_mul_of_nonneg_left w1 hx3
      linarith
    have k3 : nltc3 x * w ^ 2 ≤ 3500000 * x ^ 3 * w ^ 2 :=
      mul_le_mul_of_nonneg_right (by linarith) (pow_nonneg w0' 2)
    have k3' : x ^ 3 * w ^ 2 ≤ 13 / 2000 * w := by
      have := mul_le_mul_of_nonneg_right hxw w0'
      nlinarith
    have k4 : nltc4 x * w ^ 3 ≤ 3500000 * x ^ 3 * w ^ 3 :=
      mul_le_mul_of_nonneg_right (by linarith) (pow_nonneg w0' 3)
    have k4' : x ^ 3 * w ^ 3 ≤ 13 / 2000 * w ^ 2 := by
      have := mul_le_mul_of_nonneg_right hxw (pow_nonneg w0' 2)
      nlinarith
    have w2 : w ^ 2 ≤ 13 / 64 * w := by nlinarith
    have k5 : nltc5 x * w ^ 4 ≤ 0 := mul_nonpos_of_nonpos_of_nonneg (by linarith) (pow_nonneg w0' 4)
    have k6 : nltc6 x * w ^ 5 ≤ 0 := mul_nonpos_of_nonpos_of_nonneg (by linarith) (pow_nonneg w0' 5)
    have k2 : nltc2 x * w ≤ -48000 * w := mul_le_mul_of_nonneg_right (by linarith) w0'
    nlinarith
  have hd : ∀ s, HasDerivAt (lrhHorner cs) (lrhHorner (nltDer cs) s) s :=
    fun s => nlt_hasDerivAt_horner cs s
  have anti := hrl_anti hd neg le_rfl hy le_rfl
  rw [hf, hf] at anti
  linarith

end SmoothedOctagon
