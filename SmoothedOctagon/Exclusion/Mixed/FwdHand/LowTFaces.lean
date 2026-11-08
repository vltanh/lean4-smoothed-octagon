module

public import SmoothedOctagon.Exclusion.Mixed.FwdHand.LowTCircuit

/-!
# Case M2, forward successor by hand: the low-`t` unit sign on the faces `h = 1/4` and `j = 5h/7`

The circuit `S = ∑ nltStᵢ(t, x) yⁱ` is positive

* on the initial face `t = 3/8` (`h = 1/4`), `17/60 ≤ x ≤ 3/7`, `0 ≤ y ≤ (1 - 2x)/(1 + 4x)`
  (`nlt_face_unit`): with `Cᵢ = 1536 nltStᵢ(3/8, x)` (`nltCuᵢ`), the bounds `y ≤ 13/64`, `C₄ > 0`,
  `C₅ > -144000000x`, `C₆ > -6100000x` reduce `S` to the cubic `C₀ + C₁y + C₂y² + B_*y³`,
  `B_* = C₃ - 6000000x`, the square completion `(79/20)y³ - y² + 1/105 > 0` bounds
  `C₂y² + B_*y³ ≥ min(0, C₂/105)`, and the remaining one-variable signs close it;
* on the outer face `t = (12 - 7x)/24` (`j = 5h/7`), `3/7 ≤ x ≤ 4/7`, `0 ≤ y ≤ 2/31`
  (`nlt_face_outer`): `S(x, 0) = C₀ > 10` and the coefficient bounds `C₁ > 800`, `C₂ > -2000`,
  `C₃, C₄ > 0`, `C₅ > -50000`, `C₆ > -3000` give `S_y > 0`.

Every one-variable sign is proved on its interval by a termwise monomial bound after a shift of the
variable (a negative power is absorbed into the next lower one, `nlt_pw`), with at most a few
subintervals; the outer-face coefficients are linked by direct expansion.

## Main API

* `nltCu0`, …, `nltCu6`, `nlt_face_unit`.
* `nltCo0`, …, `nltCo6`, `nlt_face_outer`.
-/

@[expose] public section

namespace SmoothedOctagon

/-- `C_0 = 1536 nltSt0 (3/8) x` on the initial face. -/
noncomputable def nltCu0 (x : ℝ) : ℝ :=
  3793920 * x - 15602560 * x ^ 2 + 9611930 * x ^ 3 + 20231160 * x ^ 4 - 11579400 * x ^ 5 - 2570400 * x ^ 6

theorem nlt_Cu0_eq (x : ℝ) : 1536 * nltSt0 (3 / 8) x = nltCu0 x := by
  unfold nltSt0 nltCu0; ring

/-- `C_1 = 1536 nltSt1 (3/8) x` on the initial face. -/
noncomputable def nltCu1 (x : ℝ) : ℝ :=
  2276352 - 11965152 * x - 19510992 * x ^ 2 + 95366541 * x ^ 3 + 51084660 * x ^ 4 - 86017524 * x ^ 5 - 38064240 * x ^ 6 - 2640960 * x ^ 7

theorem nlt_Cu1_eq (x : ℝ) : 1536 * nltSt1 (3 / 8) x = nltCu1 x := by
  unfold nltSt1 nltCu1; ring

/-- `C_2 = 1536 nltSt2 (3/8) x` on the initial face. -/
noncomputable def nltCu2 (x : ℝ) : ℝ :=
  -6400416 - 38051816 * x + 58530680 * x ^ 2 + 206949420 * x ^ 3 + 54511676 * x ^ 4 - 155046960 * x ^ 5 - 125578224 * x ^ 6 - 37931040 * x ^ 7 - 3290112 * x ^ 8

theorem nlt_Cu2_eq (x : ℝ) : 1536 * nltSt2 (3 / 8) x = nltCu2 x := by
  unfold nltSt2 nltCu2; ring

/-- `C_3 = 1536 nltSt3 (3/8) x` on the initial face. -/
noncomputable def nltCu3 (x : ℝ) : ℝ :=
  -6671280 - 3710852 * x + 207692872 * x ^ 2 + 673286150 * x ^ 3 + 1041675896 * x ^ 4 + 815901492 * x ^ 5 + 259700688 * x ^ 6 + 15220800 * x ^ 7 - 78336 * x ^ 8

theorem nlt_Cu3_eq (x : ℝ) : 1536 * nltSt3 (3 / 8) x = nltCu3 x := by
  unfold nltSt3 nltCu3; ring

/-- `C_4 = 1536 nltSt4 (3/8) x` on the initial face. -/
noncomputable def nltCu4 (x : ℝ) : ℝ :=
  -7778448 - 49152972 * x + 9044160 * x ^ 2 + 516188634 * x ^ 3 + 1199150640 * x ^ 4 + 1101130752 * x ^ 5 + 416220768 * x ^ 6 + 50047200 * x ^ 7 + 2271744 * x ^ 8

theorem nlt_Cu4_eq (x : ℝ) : 1536 * nltSt4 (3 / 8) x = nltCu4 x := by
  unfold nltSt4 nltCu4; ring

/-- `C_5 = 1536 nltSt5 (3/8) x` on the initial face. -/
noncomputable def nltCu5 (x : ℝ) : ℝ :=
  -10104048 - 69924132 * x - 140397660 * x ^ 2 - 40976151 * x ^ 3 + 176006160 * x ^ 4 + 199922532 * x ^ 5 + 62655048 * x ^ 6 - 2232000 * x ^ 7 - 1253376 * x ^ 8

theorem nlt_Cu5_eq (x : ℝ) : 1536 * nltSt5 (3 / 8) x = nltCu5 x := by
  unfold nltSt5 nltCu5; ring

/-- `C_6 = 1536 nltSt6 (3/8) x` on the initial face. -/
noncomputable def nltCu6 (x : ℝ) : ℝ :=
  -295488 - 2093472 * x - 4182660 * x ^ 2 - 5293836 * x ^ 3 - 4773240 * x ^ 4 - 2945808 * x ^ 5 - 1608192 * x ^ 6 - 604800 * x ^ 7 - 78336 * x ^ 8

theorem nlt_Cu6_eq (x : ℝ) : 1536 * nltSt6 (3 / 8) x = nltCu6 x := by
  unfold nltSt6 nltCu6; ring

/-- `C_0 = nltSt0 ((12 - 7x)/24) x` on the outer face. -/
noncomputable def nltCo0 (x : ℝ) : ℝ :=
  -(146 / 3) * x ^ 2 + (1703 / 18) * x ^ 3 - (11383 / 12) * x ^ 4 + (8491 / 36) * x ^ 5 + (273903 / 64) * x ^ 6 + (92134651 / 20736) * x ^ 7 + (42875 / 24) * x ^ 8 + (40817 / 144) * x ^ 9

theorem nlt_Co0_eq (x : ℝ) : nltSt0 ((12 - 7 * x) / 24) x = nltCo0 x := by
  unfold nltSt0 nltCo0; ring

/-- `C_1 = nltSt1 ((12 - 7x)/24) x` on the outer face. -/
noncomputable def nltCo1 (x : ℝ) : ℝ :=
  -(760 / 3) * x + (52450 / 9) * x ^ 2 + (85877 / 18) * x ^ 3 - (1972985 / 144) * x ^ 4 - (18808865 / 1728) * x ^ 5 + (43245665 / 3456) * x ^ 6 + (240616649 / 13824) * x ^ 7 + (14201327 / 1728) * x ^ 8 + (3542161 / 1728) * x ^ 9 + (40817 / 144) * x ^ 10

theorem nlt_Co1_eq (x : ℝ) : nltSt1 ((12 - 7 * x) / 24) x = nltCo1 x := by
  unfold nltSt1 nltCo1; ring

/-- `C_2 = nltSt2 ((12 - 7x)/24) x` on the outer face. -/
noncomputable def nltCo2 (x : ℝ) : ℝ :=
  -(608 / 3) + (42836 / 9) * x + (281723 / 18) * x ^ 2 - (468623 / 72) * x ^ 3 - (38213467 / 864) * x ^ 4 - (136385543 / 3456) * x ^ 5 - (16090531 / 864) * x ^ 6 - (113883629 / 10368) * x ^ 7 - (2481899 / 384) * x ^ 8 - (6680317 / 3456) * x ^ 9 - (145775 / 864) * x ^ 10

theorem nlt_Co2_eq (x : ℝ) : nltSt2 ((12 - 7 * x) / 24) x = nltCo2 x := by
  unfold nltSt2 nltCo2; ring

/-- `C_3 = nltSt3 ((12 - 7x)/24) x` on the outer face. -/
noncomputable def nltCo3 (x : ℝ) : ℝ :=
  (19456 / 3) + (388496 / 9) * x + (286657 / 2) * x ^ 2 + (62450465 / 216) * x ^ 3 + (94747547 / 288) * x ^ 4 + (1262385373 / 10368) * x ^ 5 - (1352480477 / 10368) * x ^ 6 - (3407982385 / 20736) * x ^ 7 - (745859959 / 10368) * x ^ 8 - (12825239 / 864) * x ^ 9 - (425663 / 288) * x ^ 10

theorem nlt_Co3_eq (x : ℝ) : nltSt3 ((12 - 7 * x) / 24) x = nltCo3 x := by
  unfold nltSt3 nltCo3; ring

/-- `C_4 = nltSt4 ((12 - 7x)/24) x` on the outer face. -/
noncomputable def nltCo4 (x : ℝ) : ℝ :=
  -2736 - (24484 / 3) * x + (1172225 / 18) * x ^ 2 + (21947915 / 72) * x ^ 3 + (398494483 / 864) * x ^ 4 + (260416511 / 1152) * x ^ 5 - (205809391 / 1728) * x ^ 6 - (1271989063 / 6912) * x ^ 7 - (7644493 / 96) * x ^ 8 - (8817613 / 576) * x ^ 9 - (833833 / 576) * x ^ 10

theorem nlt_Co4_eq (x : ℝ) : nltSt4 ((12 - 7 * x) / 24) x = nltCo4 x := by
  unfold nltSt4 nltCo4; ring

/-- `C_5 = nltSt5 ((12 - 7x)/24) x` on the outer face. -/
noncomputable def nltCo5 (x : ℝ) : ℝ :=
  -9728 - (143822 / 3) * x - (642419 / 9) * x ^ 2 + (4375 / 2) * x ^ 3 + (14398915 / 144) * x ^ 4 + (261991735 / 3456) * x ^ 5 - (13547797 / 864) * x ^ 6 - (1808944133 / 41472) * x ^ 7 - (4407155 / 216) * x ^ 8 - (13943027 / 3456) * x ^ 9 - (1358623 / 3456) * x ^ 10

theorem nlt_Co5_eq (x : ℝ) : nltSt5 ((12 - 7 * x) / 24) x = nltCo5 x := by
  unfold nltSt5 nltCo5; ring

/-- `C_6 = nltSt6 ((12 - 7x)/24) x` on the outer face. -/
noncomputable def nltCo6 (x : ℝ) : ℝ :=
  -304 - 1626 * x - (17443 / 6) * x ^ 2 - (448201 / 216) * x ^ 3 - (86123 / 864) * x ^ 4 + (1915051 / 2592) * x ^ 5 + (4339501 / 10368) * x ^ 6 + (628367 / 10368) * x ^ 7 - (62327 / 5184) * x ^ 8 - (595 / 216) * x ^ 9

theorem nlt_Co6_eq (x : ℝ) : nltSt6 ((12 - 7 * x) / 24) x = nltCo6 x := by
  unfold nltSt6 nltCo6; ring

/-- An auxiliary sign of the initial face: `C₄`. -/
noncomputable def nltUf4 (x : ℝ) : ℝ := nltCu4 x

/-- `nltUf4 > 0` on `[17/60, 3/7]`. -/
theorem nltUf4_pos {x : ℝ} (h1 : (17 / 60) ≤ x) (h2 : x ≤ (3 / 7)) : 0 < nltUf4 x := by
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
  have e : nltUf4 ((17 / 60) + z) = (105434659104797377 / 145800000000) + (557960027723263423 / 2430000000) * z + (53380570488213529 / 40500000) * z ^ 2 + (1998035158444099 / 675000) * z ^ 3 + (7427591643443 / 2250) * z ^ 4 + (710989090682 / 375) * z ^ 5 + (13014685592 / 25) * z ^ 6 + (275982432 / 5) * z ^ 7 + 2271744 * z ^ 8 := by unfold nltUf4 nltCu4; ring
  rw [e]; linarith only [z0, z1, p2, q2, p3, q3, p4, q4, p5, q5, p6, q6, p7, q7, p8, q8]


/-- An auxiliary sign of the initial face: `C₅ + 144000000x`. -/
noncomputable def nltUf5 (x : ℝ) : ℝ := nltCu5 x + 144000000 * x

/-- `nltUf5 > 0` on `[17/60, 3/7]`. -/
theorem nltUf5_pos {x : ℝ} (h1 : (17 / 60) ≤ x) (h2 : x ≤ (3 / 7)) : 0 < nltUf5 x := by
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
  have e : nltUf5 ((17 / 60) + z) = (31003466485985917 / 145800000000) + (9453883071083879 / 1215000000) * z - (1580511790435391 / 40500000) * z ^ 2 + (117065756531477 / 337500) * z ^ 3 + (1197752805803 / 2250) * z ^ 4 + (112903821572 / 375) * z ^ 5 + (1385273432 / 25) * z ^ 6 - (25364928 / 5) * z ^ 7 - 1253376 * z ^ 8 := by unfold nltUf5 nltCu5; ring
  rw [e]; linarith only [z0, z1, p2, q2, p3, q3, p4, q4, p5, q5, p6, q6, p7, q7, p8, q8]


/-- An auxiliary sign of the initial face: `C₆ + 6100000x`. -/
noncomputable def nltUf6 (x : ℝ) : ℝ := nltCu6 x + 6100000 * x

/-- `nltUf6 > 0` on `[17/60, 3/7]`. -/
theorem nltUf6_pos {x : ℝ} (h1 : (17 / 60) ≤ x) (h2 : x ≤ (3 / 7)) : 0 < nltUf6 x := by
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
  have e : nltUf6 ((17 / 60) + z) = (6313977893019389 / 18225000000) - (114013901208203 / 607500000) * z - (119792442267719 / 10125000) * z ^ 2 - (2353107945989 / 168750) * z ^ 3 - (12824788346 / 1125) * z ^ 4 - (2549664808 / 375) * z ^ 5 - (74594848 / 25) * z ^ 6 - (3911808 / 5) * z ^ 7 - 78336 * z ^ 8 := by unfold nltUf6 nltCu6; ring
  rw [e]; linarith only [z0, z1, p2, q2, p3, q3, p4, q4, p5, q5, p6, q6, p7, q7, p8, q8]


/-- An auxiliary sign of the initial face: `B_* = C₃ - 6000000x`. -/
noncomputable def nltUfB (x : ℝ) : ℝ := nltCu3 x - 6000000 * x

/-- `nltUfB > 0` on `[17/60, 3/7]`. -/
theorem nltUfB_pos {x : ℝ} (h1 : (17 / 60) ≤ x) (h2 : x ≤ (3 / 7)) : 0 < nltUfB x := by
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
  have e : nltUfB ((17 / 60) + z) = (2252905816642888181 / 72900000000) + (239412981348056047 / 607500000) * z + (7558280495127203 / 5062500) * z ^ 2 + (887761581453647 / 337500) * z ^ 3 + (2837633638279 / 1125) * z ^ 4 + (481107230192 / 375) * z ^ 5 + (7242813152 / 25) * z ^ 6 + (75216192 / 5) * z ^ 7 - 78336 * z ^ 8 := by unfold nltUfB nltCu3; ring
  rw [e]; linarith only [z0, z1, p2, q2, p3, q3, p4, q4, p5, q5, p6, q6, p7, q7, p8, q8]


/-- An auxiliary sign of the initial face: `B_* + (79/20)C₂`. -/
noncomputable def nltUfE (x : ℝ) : ℝ := nltCu3 x - 6000000 * x + 79 / 20 * nltCu2 x

/-- `nltUfE > 0` on `[17/60, 3/7]`. -/
theorem nltUfE_pos {x : ℝ} (h1 : (17 / 60) ≤ x) (h2 : x ≤ (3 / 7)) : 0 < nltUfE x := by
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
  have e : nltUfE ((17 / 60) + z) = (523289938338708581 / 2916000000000) + (27484997977884150269 / 48600000000) * z + (1886936244013512437 / 810000000) * z ^ 2 + (39682745522494997 / 13500000) * z ^ 3 + (51641952998179 / 45000) * z ^ 4 - (1657044335377 / 3750) * z ^ 5 - (66586442306 / 125) * z ^ 6 - (4106045976 / 25) * z ^ 7 - (65371392 / 5) * z ^ 8 := by unfold nltUfE nltCu3 nltCu2; ring
  rw [e]; linarith only [z0, z1, p2, q2, p3, q3, p4, q4, p5, q5, p6, q6, p7, q7, p8, q8]


/-- An auxiliary sign of the initial face: `C₀`. -/
noncomputable def nltUf0 (x : ℝ) : ℝ := nltCu0 x

/-- `nltUf0 > 0` on `[17/60, 3/7]`. -/
theorem nltUf0_pos {x : ℝ} (h1 : (17 / 60) ≤ x) (h2 : x ≤ (3 / 7)) : 0 < nltUf0 x := by
  obtain ⟨z, rfl⟩ : ∃ z, x = (3 / 7) - z := ⟨(3 / 7) - x, by ring⟩
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
  have e : nltUf0 ((3 / 7) - z) = (268671150 / 16807) + (214560810 / 2401) * z + (2961975530 / 343) * z ^ 2 - (929968010 / 49) * z ^ 3 - (81644880 / 7) * z ^ 4 + 18189000 * z ^ 5 - 2570400 * z ^ 6 := by unfold nltUf0 nltCu0; ring
  rw [e]; linarith only [z0, z1, p2, q2, p3, q3, p4, q4, p5, q5, p6, q6]


/-- An auxiliary sign of the initial face: `C₀ + C₂/105`. -/
noncomputable def nltUfR0 (x : ℝ) : ℝ := nltCu0 x + nltCu2 x / 105

/-- `nltUfR0 > 0` on `[17/60, 3/7]`. -/
theorem nltUfR0_pos {x : ℝ} (h1 : (17 / 60) ≤ x) (h2 : x ≤ (3 / 7)) : 0 < nltUfR0 x := by
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
    have e : nltUfR0 ((17 / 60) + z) = (127335525328536331 / 1701000000000) - (74837141002368443 / 85050000000) * z + (2051149655734061 / 1417500000) * z ^ 2 + (19968170107083 / 875000) * z ^ 3 - (203396147713 / 78750) * z ^ 4 - (37702133966 / 1875) * z ^ 5 - (3984129672 / 875) * z ^ 6 - (10806816 / 25) * z ^ 7 - (156672 / 5) * z ^ 8 := by unfold nltUfR0 nltCu0 nltCu2; ring
    rw [e]; linarith only [z0, z1, p2, q2, p3, q3, p4, q4, p5, q5, p6, q6, p7, q7, p8, q8]
  · obtain ⟨z, rfl⟩ : ∃ z, x = (299 / 840) + z := ⟨x - (299 / 840), by ring⟩
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
    have e : nltUfR0 ((299 / 840) + z) = (14640976208382827852465057 / 537925110912000000000) - (67353216044090966463977 / 213462345600000000) * z + (681559191523181977903 / 108909360000000) * z ^ 2 + (2719470931875487919 / 129654000000) * z ^ 3 - (5022446031997 / 490000) * z ^ 4 - (4068276881831 / 183750) * z ^ 5 - (4180449388 / 875) * z ^ 6 - (78833376 / 175) * z ^ 7 - (156672 / 5) * z ^ 8 := by unfold nltUfR0 nltCu0 nltCu2; ring
    rw [e]; linarith only [z0, z1, p2, q2, p3, q3, p4, q4, p5, q5, p6, q6, p7, q7, p8, q8]


/-- An auxiliary sign of the initial face: `C₀ + bC₁`, `b = (15/16)(1/2 - x)`. -/
noncomputable def nltUfRb (x : ℝ) : ℝ := nltCu0 x + 15 / 16 * (1 / 2 - x) * nltCu1 x

/-- `nltUfRb > 0` on `[17/60, 3/7]`. -/
theorem nltUfRb_pos {x : ℝ} (h1 : (17 / 60) ≤ x) (h2 : x ≤ (3 / 7)) : 0 < nltUfRb x := by
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
    have e : nltUfRb ((17 / 60) + z) = (4730729860808777 / 62208000000) - (698164968297727 / 1036800000) * z + (1468810502203 / 135000) * z ^ 2 - (6722617878211 / 288000) * z ^ 3 - (41057271511 / 480) * z ^ 4 + (5105787491 / 80) * z ^ 5 + 134114118 * z ^ 6 + 40059315 * z ^ 7 + 2475900 * z ^ 8 := by unfold nltUfRb nltCu0 nltCu1; ring
    rw [e]; linarith only [z0, z1, p2, q2, p3, q3, p4, q4, p5, q5, p6, q6, p7, q7, p8, q8]
  · obtain ⟨z, rfl⟩ : ∃ z, x = (299 / 840) + z := ⟨x - (299 / 840), by ring⟩
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
    have e : nltUfRb ((299 / 840) + z) = (962045111314263803648081 / 13115126513664000000) + (3255680009735690745721 / 7806622924800000) * z + (4501254674838490327 / 1327656960000) * z ^ 2 - (69158958188369249 / 1580544000) * z ^ 3 - (9636016442567 / 188160) * z ^ 4 + (283913747701 / 2240) * z ^ 5 + (1238745531 / 8) * z ^ 6 + 41497695 * z ^ 7 + 2475900 * z ^ 8 := by unfold nltUfRb nltCu0 nltCu1; ring
    rw [e]; linarith only [z0, z1, p2, q2, p3, q3, p4, q4, p5, q5, p6, q6, p7, q7, p8, q8]


/-- An auxiliary sign of the initial face: `C₀ + bC₁ + C₂/105`, `b = (15/16)(1/2 - x)`. -/
noncomputable def nltUfR (x : ℝ) : ℝ := nltCu0 x + 15 / 16 * (1 / 2 - x) * nltCu1 x + nltCu2 x / 105

/-- `nltUfR > 0` on `[17/60, 3/7]`. -/
theorem nltUfR_pos {x : ℝ} (h1 : (17 / 60) ≤ x) (h2 : x ≤ (3 / 7)) : 0 < nltUfR x := by
  rcases le_total x (299 / 840) with hm | hm
  · rcases le_total x (179 / 560) with hm | hm
    · rcases le_total x (1013 / 3360) with hm | hm
      · rcases le_total x (131 / 448) with hm | hm
        · obtain ⟨z, rfl⟩ : ∃ z, x = (131 / 448) - z := ⟨(131 / 448) - x, by ring⟩
          have z0 : 0 ≤ z := by linarith
          have z1 : z ≤ (61 / 6720) := by linarith
          have p2 : z ^ 2 ≤ (61 / 6720) * z ^ 1 := nlt_pw z0 z1 1
          have q2 : 0 ≤ z ^ 2 := pow_nonneg z0 2
          have p3 : z ^ 3 ≤ (61 / 6720) * z ^ 2 := nlt_pw z0 z1 2
          have q3 : 0 ≤ z ^ 3 := pow_nonneg z0 3
          have p4 : z ^ 4 ≤ (61 / 6720) * z ^ 3 := nlt_pw z0 z1 3
          have q4 : 0 ≤ z ^ 4 := pow_nonneg z0 4
          have p5 : z ^ 5 ≤ (61 / 6720) * z ^ 4 := nlt_pw z0 z1 4
          have q5 : 0 ≤ z ^ 5 := pow_nonneg z0 5
          have p6 : z ^ 6 ≤ (61 / 6720) * z ^ 5 := nlt_pw z0 z1 5
          have q6 : 0 ≤ z ^ 6 := pow_nonneg z0 6
          have p7 : z ^ 7 ≤ (61 / 6720) * z ^ 6 := nlt_pw z0 z1 6
          have q7 : 0 ≤ z ^ 7 := pow_nonneg z0 7
          have p8 : z ^ 8 ≤ (61 / 6720) * z ^ 7 := nlt_pw z0 z1 7
          have q8 : 0 ≤ z ^ 8 := pow_nonneg z0 8
          have e : nltUfR ((131 / 448) - z) = (264484885559741500332335 / 405661806804141604864) + (10775703484910011725359 / 339560664177573888) * z + (2650274097005181089809 / 216556546031616) * z ^ 2 + (31144784878021174111 / 1208462868480) * z ^ 3 - (18932507082762083 / 220200960) * z ^ 4 - (134328625851663 / 2007040) * z ^ 5 + (1206507324159 / 8960) * z ^ 6 - (2786319507 / 70) * z ^ 7 + (12222828 / 5) * z ^ 8 := by unfold nltUfR nltCu0 nltCu1 nltCu2; ring
          rw [e]; linarith only [z0, z1, p2, q2, p3, q3, p4, q4, p5, q5, p6, q6, p7, q7, p8, q8]
        · obtain ⟨z, rfl⟩ : ∃ z, x = (131 / 448) + z := ⟨x - (131 / 448), by ring⟩
          have z0 : 0 ≤ z := by linarith
          have z1 : z ≤ (61 / 6720) := by linarith
          have p2 : z ^ 2 ≤ (61 / 6720) * z ^ 1 := nlt_pw z0 z1 1
          have q2 : 0 ≤ z ^ 2 := pow_nonneg z0 2
          have p3 : z ^ 3 ≤ (61 / 6720) * z ^ 2 := nlt_pw z0 z1 2
          have q3 : 0 ≤ z ^ 3 := pow_nonneg z0 3
          have p4 : z ^ 4 ≤ (61 / 6720) * z ^ 3 := nlt_pw z0 z1 3
          have q4 : 0 ≤ z ^ 4 := pow_nonneg z0 4
          have p5 : z ^ 5 ≤ (61 / 6720) * z ^ 4 := nlt_pw z0 z1 4
          have q5 : 0 ≤ z ^ 5 := pow_nonneg z0 5
          have p6 : z ^ 6 ≤ (61 / 6720) * z ^ 5 := nlt_pw z0 z1 5
          have q6 : 0 ≤ z ^ 6 := pow_nonneg z0 6
          have p7 : z ^ 7 ≤ (61 / 6720) * z ^ 6 := nlt_pw z0 z1 6
          have q7 : 0 ≤ z ^ 7 := pow_nonneg z0 7
          have p8 : z ^ 8 ≤ (61 / 6720) * z ^ 7 := nlt_pw z0 z1 7
          have q8 : 0 ≤ z ^ 8 := pow_nonneg z0 8
          have e : nltUfR ((131 / 448) + z) = (264484885559741500332335 / 405661806804141604864) - (10775703484910011725359 / 339560664177573888) * z + (2650274097005181089809 / 216556546031616) * z ^ 2 - (31144784878021174111 / 1208462868480) * z ^ 3 - (18932507082762083 / 220200960) * z ^ 4 + (134328625851663 / 2007040) * z ^ 5 + (1206507324159 / 8960) * z ^ 6 + (2786319507 / 70) * z ^ 7 + (12222828 / 5) * z ^ 8 := by unfold nltUfR nltCu0 nltCu1 nltCu2; ring
          rw [e]; linarith only [z0, z1, p2, q2, p3, q3, p4, q4, p5, q5, p6, q6, p7, q7, p8, q8]
      · obtain ⟨z, rfl⟩ : ∃ z, x = (1013 / 3360) + z := ⟨x - (1013 / 3360), by ring⟩
        have z0 : 0 ≤ z := by linarith
        have z1 : z ≤ (61 / 3360) := by linarith
        have p2 : z ^ 2 ≤ (61 / 3360) * z ^ 1 := nlt_pw z0 z1 1
        have q2 : 0 ≤ z ^ 2 := pow_nonneg z0 2
        have p3 : z ^ 3 ≤ (61 / 3360) * z ^ 2 := nlt_pw z0 z1 2
        have q3 : 0 ≤ z ^ 3 := pow_nonneg z0 3
        have p4 : z ^ 4 ≤ (61 / 3360) * z ^ 3 := nlt_pw z0 z1 3
        have q4 : 0 ≤ z ^ 4 := pow_nonneg z0 4
        have p5 : z ^ 5 ≤ (61 / 3360) * z ^ 4 := nlt_pw z0 z1 4
        have q5 : 0 ≤ z ^ 5 := pow_nonneg z0 5
        have p6 : z ^ 6 ≤ (61 / 3360) * z ^ 5 := nlt_pw z0 z1 5
        have q6 : 0 ≤ z ^ 6 := pow_nonneg z0 6
        have p7 : z ^ 7 ≤ (61 / 3360) * z ^ 6 := nlt_pw z0 z1 6
        have q7 : 0 ≤ z ^ 7 := pow_nonneg z0 7
        have p8 : z ^ 8 ≤ (61 / 3360) * z ^ 7 := nlt_pw z0 z1 7
        have q8 : 0 ≤ z ^ 8 := pow_nonneg z0 8
        have e : nltUfR ((1013 / 3360) + z) = (3051497841102512558380218402683 / 2256221444398645248000000000) + (35716399415062384000426313 / 194298170572800000000) * z + (82041297910083104081992957 / 7137483816960000000) * z ^ 2 - (312534684526685570407 / 10838016000000) * z ^ 3 - (6977419069564829899 / 84295680000) * z ^ 4 + (249754117152227 / 3360000) * z ^ 5 + (7682624525537 / 56000) * z ^ 6 + (6996865122 / 175) * z ^ 7 + (12222828 / 5) * z ^ 8 := by unfold nltUfR nltCu0 nltCu1 nltCu2; ring
        rw [e]; linarith only [z0, z1, p2, q2, p3, q3, p4, q4, p5, q5, p6, q6, p7, q7, p8, q8]
    · obtain ⟨z, rfl⟩ : ∃ z, x = (179 / 560) + z := ⟨x - (179 / 560), by ring⟩
      have z0 : 0 ≤ z := by linarith
      have z1 : z ≤ (61 / 1680) := by linarith
      have p2 : z ^ 2 ≤ (61 / 1680) * z ^ 1 := nlt_pw z0 z1 1
      have q2 : 0 ≤ z ^ 2 := pow_nonneg z0 2
      have p3 : z ^ 3 ≤ (61 / 1680) * z ^ 2 := nlt_pw z0 z1 2
      have q3 : 0 ≤ z ^ 3 := pow_nonneg z0 3
      have p4 : z ^ 4 ≤ (61 / 1680) * z ^ 3 := nlt_pw z0 z1 3
      have q4 : 0 ≤ z ^ 4 := pow_nonneg z0 4
      have p5 : z ^ 5 ≤ (61 / 1680) * z ^ 4 := nlt_pw z0 z1 4
      have q5 : 0 ≤ z ^ 5 := pow_nonneg z0 5
      have p6 : z ^ 6 ≤ (61 / 1680) * z ^ 5 := nlt_pw z0 z1 5
      have q6 : 0 ≤ z ^ 6 := pow_nonneg z0 6
      have p7 : z ^ 7 ≤ (61 / 1680) * z ^ 6 := nlt_pw z0 z1 6
      have q7 : 0 ≤ z ^ 7 := pow_nonneg z0 7
      have p8 : z ^ 8 ≤ (61 / 1680) * z ^ 7 := nlt_pw z0 z1 7
      have q8 : 0 ≤ z ^ 8 := pow_nonneg z0 8
      have e : nltUfR ((179 / 560) + z) = (300918589160644552662702581 / 36268991840256000000000) + (9240937144764258122228303 / 16191514214400000000) * z + (10083380124113867233979 / 1032622080000000) * z ^ 2 - (255103637954752091567 / 7375872000000) * z ^ 3 - (396922761741295549 / 5268480000) * z ^ 4 + (702095664068721 / 7840000) * z ^ 5 + (996053384031 / 7000) * z ^ 6 + (7058997831 / 175) * z ^ 7 + (12222828 / 5) * z ^ 8 := by unfold nltUfR nltCu0 nltCu1 nltCu2; ring
      rw [e]; linarith only [z0, z1, p2, q2, p3, q3, p4, q4, p5, q5, p6, q6, p7, q7, p8, q8]
  · obtain ⟨z, rfl⟩ : ∃ z, x = (299 / 840) + z := ⟨x - (299 / 840), by ring⟩
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
    have e : nltUfR ((299 / 840) + z) = (1380973599556292440617176273 / 34427207098368000000000) + (7715063814989581608458611 / 6830795059200000000) * z + (18987100516566320401271 / 3485099520000000) * z ^ 2 - (183419973692741665217 / 4148928000000) * z ^ 3 - (1321804498856731 / 23520000) * z ^ 4 + (715454682696533 / 5880000) * z ^ 5 + (1068451544521 / 7000) * z ^ 6 + (7183263249 / 175) * z ^ 7 + (12222828 / 5) * z ^ 8 := by unfold nltUfR nltCu0 nltCu1 nltCu2; ring
    rw [e]; linarith only [z0, z1, p2, q2, p3, q3, p4, q4, p5, q5, p6, q6, p7, q7, p8, q8]


/-- A coefficient bound of the outer face: `C_0`. -/
noncomputable def nltOf0 (x : ℝ) : ℝ := nltCo0 x

/-- `nltOf0 > 10` on `[3/7, 4/7]`. -/
theorem nltOf0_pos {x : ℝ} (h1 : (3 / 7) ≤ x) (h2 : x ≤ (4 / 7)) : 10 < nltOf0 x := by
  obtain ⟨z, rfl⟩ : ∃ z, x = (3 / 7) + z := ⟨x - (3 / 7), by ring⟩
  have z0 : 0 ≤ z := by linarith
  have z1 : z ≤ (1 / 7) := by linarith
  have p2 : z ^ 2 ≤ (1 / 7) * z ^ 1 := nlt_pw z0 z1 1
  have q2 : 0 ≤ z ^ 2 := pow_nonneg z0 2
  have p3 : z ^ 3 ≤ (1 / 7) * z ^ 2 := nlt_pw z0 z1 2
  have q3 : 0 ≤ z ^ 3 := pow_nonneg z0 3
  have p4 : z ^ 4 ≤ (1 / 7) * z ^ 3 := nlt_pw z0 z1 3
  have q4 : 0 ≤ z ^ 4 := pow_nonneg z0 4
  have p5 : z ^ 5 ≤ (1 / 7) * z ^ 4 := nlt_pw z0 z1 4
  have q5 : 0 ≤ z ^ 5 := pow_nonneg z0 5
  have p6 : z ^ 6 ≤ (1 / 7) * z ^ 5 := nlt_pw z0 z1 5
  have q6 : 0 ≤ z ^ 6 := pow_nonneg z0 6
  have p7 : z ^ 7 ≤ (1 / 7) * z ^ 6 := nlt_pw z0 z1 6
  have q7 : 0 ≤ z ^ 7 := pow_nonneg z0 7
  have p8 : z ^ 8 ≤ (1 / 7) * z ^ 7 := nlt_pw z0 z1 7
  have q8 : 0 ≤ z ^ 8 := pow_nonneg z0 8
  have p9 : z ^ 9 ≤ (1 / 7) * z ^ 8 := nlt_pw z0 z1 8
  have q9 : 0 ≤ z ^ 9 := pow_nonneg z0 9
  have e : nltOf0 ((3 / 7) + z) = (44778525 / 4302592) + (31292075 / 87808) * z + (115345429 / 37632) * z ^ 2 + (1408918489 / 112896) * z ^ 3 + (50757671 / 1792) * z ^ 4 + (86305327 / 2304) * z ^ 5 + (198174991 / 6912) * z ^ 6 + (258007099 / 20736) * z ^ 7 + (138229 / 48) * z ^ 8 + (40817 / 144) * z ^ 9 := by unfold nltOf0 nltCo0; ring
  rw [e]; linarith only [z0, z1, p2, q2, p3, q3, p4, q4, p5, q5, p6, q6, p7, q7, p8, q8, p9, q9]


/-- A coefficient bound of the outer face: `C_1`. -/
noncomputable def nltOf1 (x : ℝ) : ℝ := nltCo1 x

/-- `nltOf1 > 800` on `[3/7, 4/7]`. -/
theorem nltOf1_pos {x : ℝ} (h1 : (3 / 7) ≤ x) (h2 : x ≤ (4 / 7)) : 800 < nltOf1 x := by
  obtain ⟨z, rfl⟩ : ∃ z, x = (3 / 7) + z := ⟨x - (3 / 7), by ring⟩
  have z0 : 0 ≤ z := by linarith
  have z1 : z ≤ (1 / 7) := by linarith
  have p2 : z ^ 2 ≤ (1 / 7) * z ^ 1 := nlt_pw z0 z1 1
  have q2 : 0 ≤ z ^ 2 := pow_nonneg z0 2
  have p3 : z ^ 3 ≤ (1 / 7) * z ^ 2 := nlt_pw z0 z1 2
  have q3 : 0 ≤ z ^ 3 := pow_nonneg z0 3
  have p4 : z ^ 4 ≤ (1 / 7) * z ^ 3 := nlt_pw z0 z1 3
  have q4 : 0 ≤ z ^ 4 := pow_nonneg z0 4
  have p5 : z ^ 5 ≤ (1 / 7) * z ^ 4 := nlt_pw z0 z1 4
  have q5 : 0 ≤ z ^ 5 := pow_nonneg z0 5
  have p6 : z ^ 6 ≤ (1 / 7) * z ^ 5 := nlt_pw z0 z1 5
  have q6 : 0 ≤ z ^ 6 := pow_nonneg z0 6
  have p7 : z ^ 7 ≤ (1 / 7) * z ^ 6 := nlt_pw z0 z1 6
  have q7 : 0 ≤ z ^ 7 := pow_nonneg z0 7
  have p8 : z ^ 8 ≤ (1 / 7) * z ^ 7 := nlt_pw z0 z1 7
  have q8 : 0 ≤ z ^ 8 := pow_nonneg z0 8
  have p9 : z ^ 9 ≤ (1 / 7) * z ^ 8 := nlt_pw z0 z1 8
  have q9 : 0 ≤ z ^ 9 := pow_nonneg z0 9
  have p10 : z ^ 10 ≤ (1 / 7) * z ^ 9 := nlt_pw z0 z1 9
  have q10 : 0 ≤ z ^ 10 := pow_nonneg z0 10
  have e : nltOf1 ((3 / 7) + z) = (7331303925 / 8605184) + (84109882625 / 25815552) * z + (2446084793 / 1580544) * z ^ 2 + (2112065321 / 225792) * z ^ 3 + (1728936649 / 25088) * z ^ 4 + (13005856019 / 96768) * z ^ 5 + (1694249183 / 13824) * z ^ 6 + (854525609 / 13824) * z ^ 7 + (3989041 / 216) * z ^ 8 + (5641321 / 1728) * z ^ 9 + (40817 / 144) * z ^ 10 := by unfold nltOf1 nltCo1; ring
  rw [e]; linarith only [z0, z1, p2, q2, p3, q3, p4, q4, p5, q5, p6, q6, p7, q7, p8, q8, p9, q9, p10, q10]


/-- A coefficient bound of the outer face: `C_2`. -/
noncomputable def nltOf2 (x : ℝ) : ℝ := nltCo2 x

/-- `nltOf2 > -2000` on `[3/7, 4/7]`. -/
theorem nltOf2_pos {x : ℝ} (h1 : (3 / 7) ≤ x) (h2 : x ≤ (4 / 7)) : (-2000) < nltOf2 x := by
  obtain ⟨z, rfl⟩ : ∃ z, x = (3 / 7) + z := ⟨x - (3 / 7), by ring⟩
  have z0 : 0 ≤ z := by linarith
  have z1 : z ≤ (1 / 7) := by linarith
  have p2 : z ^ 2 ≤ (1 / 7) * z ^ 1 := nlt_pw z0 z1 1
  have q2 : 0 ≤ z ^ 2 := pow_nonneg z0 2
  have p3 : z ^ 3 ≤ (1 / 7) * z ^ 2 := nlt_pw z0 z1 2
  have q3 : 0 ≤ z ^ 3 := pow_nonneg z0 3
  have p4 : z ^ 4 ≤ (1 / 7) * z ^ 3 := nlt_pw z0 z1 3
  have q4 : 0 ≤ z ^ 4 := pow_nonneg z0 4
  have p5 : z ^ 5 ≤ (1 / 7) * z ^ 4 := nlt_pw z0 z1 4
  have q5 : 0 ≤ z ^ 5 := pow_nonneg z0 5
  have p6 : z ^ 6 ≤ (1 / 7) * z ^ 5 := nlt_pw z0 z1 5
  have q6 : 0 ≤ z ^ 6 := pow_nonneg z0 6
  have p7 : z ^ 7 ≤ (1 / 7) * z ^ 6 := nlt_pw z0 z1 6
  have q7 : 0 ≤ z ^ 7 := pow_nonneg z0 7
  have p8 : z ^ 8 ≤ (1 / 7) * z ^ 7 := nlt_pw z0 z1 7
  have q8 : 0 ≤ z ^ 8 := pow_nonneg z0 8
  have p9 : z ^ 9 ≤ (1 / 7) * z ^ 8 := nlt_pw z0 z1 8
  have q9 : 0 ≤ z ^ 9 := pow_nonneg z0 9
  have p10 : z ^ 10 ≤ (1 / 7) * z ^ 9 := nlt_pw z0 z1 9
  have q10 : 0 ≤ z ^ 10 := pow_nonneg z0 10
  have e : nltOf2 ((3 / 7) + z) = (104568054525 / 52706752) - (159622647725 / 19361664) * z - (1676664355057 / 19361664) * z ^ 2 - (62508941757 / 307328) * z ^ 3 - (2427636979 / 10584) * z ^ 4 - (252567101 / 1512) * z ^ 5 - (113808371 / 1152) * z ^ 6 - (492676241 / 10368) * z ^ 7 - (735049 / 48) * z ^ 8 - (9179317 / 3456) * z ^ 9 - (145775 / 864) * z ^ 10 := by unfold nltOf2 nltCo2; ring
  rw [e]; linarith only [z0, z1, p2, q2, p3, q3, p4, q4, p5, q5, p6, q6, p7, q7, p8, q8, p9, q9, p10, q10]


/-- A coefficient bound of the outer face: `C_3`. -/
noncomputable def nltOf3 (x : ℝ) : ℝ := nltCo3 x

/-- `nltOf3 > 0` on `[3/7, 4/7]`. -/
theorem nltOf3_pos {x : ℝ} (h1 : (3 / 7) ≤ x) (h2 : x ≤ (4 / 7)) : 0 < nltOf3 x := by
  obtain ⟨z, rfl⟩ : ∃ z, x = (3 / 7) + z := ⟨x - (3 / 7), by ring⟩
  have z0 : 0 ≤ z := by linarith
  have z1 : z ≤ (1 / 7) := by linarith
  have p2 : z ^ 2 ≤ (1 / 7) * z ^ 1 := nlt_pw z0 z1 1
  have q2 : 0 ≤ z ^ 2 := pow_nonneg z0 2
  have p3 : z ^ 3 ≤ (1 / 7) * z ^ 2 := nlt_pw z0 z1 2
  have q3 : 0 ≤ z ^ 3 := pow_nonneg z0 3
  have p4 : z ^ 4 ≤ (1 / 7) * z ^ 3 := nlt_pw z0 z1 3
  have q4 : 0 ≤ z ^ 4 := pow_nonneg z0 4
  have p5 : z ^ 5 ≤ (1 / 7) * z ^ 4 := nlt_pw z0 z1 4
  have q5 : 0 ≤ z ^ 5 := pow_nonneg z0 5
  have p6 : z ^ 6 ≤ (1 / 7) * z ^ 5 := nlt_pw z0 z1 5
  have q6 : 0 ≤ z ^ 6 := pow_nonneg z0 6
  have p7 : z ^ 7 ≤ (1 / 7) * z ^ 6 := nlt_pw z0 z1 6
  have q7 : 0 ≤ z ^ 7 := pow_nonneg z0 7
  have p8 : z ^ 8 ≤ (1 / 7) * z ^ 7 := nlt_pw z0 z1 7
  have q8 : 0 ≤ z ^ 8 := pow_nonneg z0 8
  have p9 : z ^ 9 ≤ (1 / 7) * z ^ 8 := nlt_pw z0 z1 8
  have q9 : 0 ≤ z ^ 9 := pow_nonneg z0 9
  have p10 : z ^ 10 ≤ (1 / 7) * z ^ 9 := nlt_pw z0 z1 9
  have q10 : 0 ≤ z ^ 10 := pow_nonneg z0 10
  have e : nltOf3 ((3 / 7) + z) = (126319474958325 / 1475789056) + (814618118345825 / 1897443072) * z + (25406693754293 / 30118144) * z ^ 2 + (10137680555491 / 16595712) * z ^ 3 - (998482060115 / 2370816) * z ^ 4 - (25571726191 / 20736) * z ^ 5 - (159971159683 / 145152) * z ^ 6 - (75930666439 / 145152) * z ^ 7 - (1466141767 / 10368) * z ^ 8 - (18298049 / 864) * z ^ 9 - (425663 / 288) * z ^ 10 := by unfold nltOf3 nltCo3; ring
  rw [e]; linarith only [z0, z1, p2, q2, p3, q3, p4, q4, p5, q5, p6, q6, p7, q7, p8, q8, p9, q9, p10, q10]


/-- A coefficient bound of the outer face: `C_4`. -/
noncomputable def nltOf4 (x : ℝ) : ℝ := nltCo4 x

/-- `nltOf4 > 0` on `[3/7, 4/7]`. -/
theorem nltOf4_pos {x : ℝ} (h1 : (3 / 7) ≤ x) (h2 : x ≤ (4 / 7)) : 0 < nltOf4 x := by
  obtain ⟨z, rfl⟩ : ∃ z, x = (3 / 7) + z := ⟨x - (3 / 7), by ring⟩
  have z0 : 0 ≤ z := by linarith
  have z1 : z ≤ (1 / 7) := by linarith
  have p2 : z ^ 2 ≤ (1 / 7) * z ^ 1 := nlt_pw z0 z1 1
  have q2 : 0 ≤ z ^ 2 := pow_nonneg z0 2
  have p3 : z ^ 3 ≤ (1 / 7) * z ^ 2 := nlt_pw z0 z1 2
  have q3 : 0 ≤ z ^ 3 := pow_nonneg z0 3
  have p4 : z ^ 4 ≤ (1 / 7) * z ^ 3 := nlt_pw z0 z1 3
  have q4 : 0 ≤ z ^ 4 := pow_nonneg z0 4
  have p5 : z ^ 5 ≤ (1 / 7) * z ^ 4 := nlt_pw z0 z1 4
  have q5 : 0 ≤ z ^ 5 := pow_nonneg z0 5
  have p6 : z ^ 6 ≤ (1 / 7) * z ^ 5 := nlt_pw z0 z1 5
  have q6 : 0 ≤ z ^ 6 := pow_nonneg z0 6
  have p7 : z ^ 7 ≤ (1 / 7) * z ^ 6 := nlt_pw z0 z1 6
  have q7 : 0 ≤ z ^ 7 := pow_nonneg z0 7
  have p8 : z ^ 8 ≤ (1 / 7) * z ^ 7 := nlt_pw z0 z1 7
  have q8 : 0 ≤ z ^ 8 := pow_nonneg z0 8
  have p9 : z ^ 9 ≤ (1 / 7) * z ^ 8 := nlt_pw z0 z1 8
  have q9 : 0 ≤ z ^ 9 := pow_nonneg z0 9
  have p10 : z ^ 10 ≤ (1 / 7) * z ^ 9 := nlt_pw z0 z1 9
  have q10 : 0 ≤ z ^ 10 := pow_nonneg z0 10
  have e : nltOf4 ((3 / 7) + z) = (69696025133625 / 1475789056) + (239591939072275 / 632481024) * z + (274256615061895 / 271063296) * z ^ 2 + (1904816954279 / 1843968) * z ^ 3 - (254493242485 / 2370816) * z ^ 4 - (19537330349 / 16128) * z ^ 5 - (57682729039 / 48384) * z ^ 6 - (27672782497 / 48384) * z ^ 7 - (7230803 / 48) * z ^ 8 - (12391183 / 576) * z ^ 9 - (833833 / 576) * z ^ 10 := by unfold nltOf4 nltCo4; ring
  rw [e]; linarith only [z0, z1, p2, q2, p3, q3, p4, q4, p5, q5, p6, q6, p7, q7, p8, q8, p9, q9, p10, q10]


/-- A coefficient bound of the outer face: `C_5`. -/
noncomputable def nltOf5 (x : ℝ) : ℝ := nltCo5 x

/-- `nltOf5 > -50000` on `[3/7, 4/7]`. -/
theorem nltOf5_pos {x : ℝ} (h1 : (3 / 7) ≤ x) (h2 : x ≤ (4 / 7)) : (-50000) < nltOf5 x := by
  obtain ⟨z, rfl⟩ : ∃ z, x = (3 / 7) + z := ⟨x - (3 / 7), by ring⟩
  have z0 : 0 ≤ z := by linarith
  have z1 : z ≤ (1 / 7) := by linarith
  have p2 : z ^ 2 ≤ (1 / 7) * z ^ 1 := nlt_pw z0 z1 1
  have q2 : 0 ≤ z ^ 2 := pow_nonneg z0 2
  have p3 : z ^ 3 ≤ (1 / 7) * z ^ 2 := nlt_pw z0 z1 2
  have q3 : 0 ≤ z ^ 3 := pow_nonneg z0 3
  have p4 : z ^ 4 ≤ (1 / 7) * z ^ 3 := nlt_pw z0 z1 3
  have q4 : 0 ≤ z ^ 4 := pow_nonneg z0 4
  have p5 : z ^ 5 ≤ (1 / 7) * z ^ 4 := nlt_pw z0 z1 4
  have q5 : 0 ≤ z ^ 5 := pow_nonneg z0 5
  have p6 : z ^ 6 ≤ (1 / 7) * z ^ 5 := nlt_pw z0 z1 5
  have q6 : 0 ≤ z ^ 6 := pow_nonneg z0 6
  have p7 : z ^ 7 ≤ (1 / 7) * z ^ 6 := nlt_pw z0 z1 6
  have q7 : 0 ≤ z ^ 7 := pow_nonneg z0 7
  have p8 : z ^ 8 ≤ (1 / 7) * z ^ 7 := nlt_pw z0 z1 7
  have q8 : 0 ≤ z ^ 8 := pow_nonneg z0 8
  have p9 : z ^ 9 ≤ (1 / 7) * z ^ 8 := nlt_pw z0 z1 8
  have q9 : 0 ≤ z ^ 9 := pow_nonneg z0 9
  have p10 : z ^ 10 ≤ (1 / 7) * z ^ 9 := nlt_pw z0 z1 9
  have q10 : 0 ≤ z ^ 10 := pow_nonneg z0 10
  have e : nltOf5 ((3 / 7) + z) = -(115056278209125 / 2951578112) - (28409039811125 / 421654016) * z + (41298065724095 / 542126592) * z ^ 2 + (267876639209 / 1229312) * z ^ 3 + (67993669423 / 1580544) * z ^ 4 - (23348103761 / 96768) * z ^ 5 - (3020556179 / 10752) * z ^ 6 - (41793160499 / 290304) * z ^ 7 - (67762081 / 1728) * z ^ 8 - (19765697 / 3456) * z ^ 9 - (1358623 / 3456) * z ^ 10 := by unfold nltOf5 nltCo5; ring
  rw [e]; linarith only [z0, z1, p2, q2, p3, q3, p4, q4, p5, q5, p6, q6, p7, q7, p8, q8, p9, q9, p10, q10]


/-- A coefficient bound of the outer face: `C_6`. -/
noncomputable def nltOf6 (x : ℝ) : ℝ := nltCo6 x

/-- `nltOf6 > -3000` on `[3/7, 4/7]`. -/
theorem nltOf6_pos {x : ℝ} (h1 : (3 / 7) ≤ x) (h2 : x ≤ (4 / 7)) : (-3000) < nltOf6 x := by
  obtain ⟨z, rfl⟩ : ∃ z, x = (3 / 7) + z := ⟨x - (3 / 7), by ring⟩
  have z0 : 0 ≤ z := by linarith
  have z1 : z ≤ (1 / 7) := by linarith
  have p2 : z ^ 2 ≤ (1 / 7) * z ^ 1 := nlt_pw z0 z1 1
  have q2 : 0 ≤ z ^ 2 := pow_nonneg z0 2
  have p3 : z ^ 3 ≤ (1 / 7) * z ^ 2 := nlt_pw z0 z1 2
  have q3 : 0 ≤ z ^ 3 := pow_nonneg z0 3
  have p4 : z ^ 4 ≤ (1 / 7) * z ^ 3 := nlt_pw z0 z1 3
  have q4 : 0 ≤ z ^ 4 := pow_nonneg z0 4
  have p5 : z ^ 5 ≤ (1 / 7) * z ^ 4 := nlt_pw z0 z1 4
  have q5 : 0 ≤ z ^ 5 := pow_nonneg z0 5
  have p6 : z ^ 6 ≤ (1 / 7) * z ^ 5 := nlt_pw z0 z1 5
  have q6 : 0 ≤ z ^ 6 := pow_nonneg z0 6
  have p7 : z ^ 7 ≤ (1 / 7) * z ^ 6 := nlt_pw z0 z1 6
  have q7 : 0 ≤ z ^ 7 := pow_nonneg z0 7
  have p8 : z ^ 8 ≤ (1 / 7) * z ^ 7 := nlt_pw z0 z1 7
  have q8 : 0 ≤ z ^ 8 := pow_nonneg z0 8
  have p9 : z ^ 9 ≤ (1 / 7) * z ^ 8 := nlt_pw z0 z1 8
  have q9 : 0 ≤ z ^ 9 := pow_nonneg z0 9
  have e : nltOf6 ((3 / 7) + z) = -(622822179375 / 368947264) - (540700978875 / 105413504) * z - (110129391125 / 22588608) * z ^ 2 - (1406613805 / 8297856) * z ^ 3 + (136827601 / 49392) * z ^ 4 + (144002083 / 72576) * z ^ 5 + (18881375 / 36288) * z ^ 6 + (84953 / 72576) * z ^ 7 - (117407 / 5184) * z ^ 8 - (595 / 216) * z ^ 9 := by unfold nltOf6 nltCo6; ring
  rw [e]; linarith only [z0, z1, p2, q2, p3, q3, p4, q4, p5, q5, p6, q6, p7, q7, p8, q8, p9, q9]


/-- The cubic square completion: `(79/20)y³ - y² + 1/105 > 0` for
`y ≥ 0`. -/
theorem nlt_unit_cubic {y : ℝ} (hy : 0 ≤ y) : 0 < 79 / 20 * y ^ 3 - y ^ 2 + 1 / 105 := by
  have e : 79 / 20 * y ^ 3 - y ^ 2 + 1 / 105 =
      79 / 20 * (y - 40 / 237) ^ 2 * (y + 20 / 237) + 169 / 5897745 := by ring
  rw [e]
  have : 0 ≤ 79 / 20 * (y - 40 / 237) ^ 2 * (y + 20 / 237) := by positivity
  linarith

/-- **The initial face** `h = 1/4`: for `17/60 ≤ x ≤ 3/7`, `y ≥ 0`,
`y(1 + 4x) ≤ 1 - 2x`, the circuit at `t = 3/8` is positive. -/
theorem nlt_face_unit {x y : ℝ} (h1 : 17 / 60 ≤ x) (h2 : x ≤ 3 / 7) (hy0 : 0 ≤ y)
    (hy : y * (1 + 4 * x) ≤ 1 - 2 * x) :
    0 < nltSt0 (3 / 8) x + nltSt1 (3 / 8) x * y + nltSt2 (3 / 8) x * y ^ 2
      + nltSt3 (3 / 8) x * y ^ 3 + nltSt4 (3 / 8) x * y ^ 4 + nltSt5 (3 / 8) x * y ^ 5
      + nltSt6 (3 / 8) x * y ^ 6 := by
  have u4 := nltUf4_pos h1 h2
  have u5 := nltUf5_pos h1 h2
  have u6 := nltUf6_pos h1 h2
  have uB := nltUfB_pos h1 h2
  have uE := nltUfE_pos h1 h2
  have u0 := nltUf0_pos h1 h2
  have uR0 := nltUfR0_pos h1 h2
  have uRb := nltUfRb_pos h1 h2
  have uR := nltUfR_pos h1 h2
  unfold nltUf4 nltUf5 nltUf6 nltUfB nltUfE nltUf0 nltUfR0 nltUfRb nltUfR at *
  have e : nltCu0 x + nltCu1 x * y + nltCu2 x * y ^ 2 + nltCu3 x * y ^ 3 + nltCu4 x * y ^ 4
      + nltCu5 x * y ^ 5 + nltCu6 x * y ^ 6 = 1536 * (nltSt0 (3 / 8) x + nltSt1 (3 / 8) x * y
      + nltSt2 (3 / 8) x * y ^ 2 + nltSt3 (3 / 8) x * y ^ 3 + nltSt4 (3 / 8) x * y ^ 4
      + nltSt5 (3 / 8) x * y ^ 5 + nltSt6 (3 / 8) x * y ^ 6) := by
    rw [← nlt_Cu0_eq, ← nlt_Cu1_eq, ← nlt_Cu2_eq, ← nlt_Cu3_eq, ← nlt_Cu4_eq, ← nlt_Cu5_eq,
      ← nlt_Cu6_eq]; ring
  suffices key : 0 < nltCu0 x + nltCu1 x * y + nltCu2 x * y ^ 2 + nltCu3 x * y ^ 3
      + nltCu4 x * y ^ 4 + nltCu5 x * y ^ 5 + nltCu6 x * y ^ 6 by rw [e] at key; linarith
  set C0 := nltCu0 x
  set C1 := nltCu1 x
  set C2 := nltCu2 x
  set C3 := nltCu3 x
  set C4 := nltCu4 x
  set C5 := nltCu5 x
  set C6 := nltCu6 x
  have hx0 : 0 < x := by linarith
  -- `y ≤ b = (15/16)(1/2 - x) ≤ 13/64`
  have hb : y ≤ 15 / 16 * (1 / 2 - x) := by
    have h4 : 0 < 1 + 4 * x := by linarith
    have : 1 - 2 * x ≤ 15 / 16 * (1 / 2 - x) * (1 + 4 * x) := by nlinarith
    by_contra hc
    push Not at hc
    have := mul_lt_mul_of_pos_right hc h4
    linarith
  have hy13 : y ≤ 13 / 64 := by linarith
  -- `P ≥ C₀ + C₁y + C₂y² + B_*y³`
  have f4 : 0 ≤ C4 * y ^ 4 := mul_nonneg u4.le (pow_nonneg hy0 4)
  have f5 : -(144000000 * x) * y ^ 5 ≤ C5 * y ^ 5 :=
    mul_le_mul_of_nonneg_right (by linarith) (pow_nonneg hy0 5)
  have f6 : -(6100000 * x) * y ^ 6 ≤ C6 * y ^ 6 :=
    mul_le_mul_of_nonneg_right (by linarith) (pow_nonneg hy0 6)
  have g1 : 144000000 * y ^ 2 + 6100000 * y ^ 3 ≤ 6000000 := by
    have a2 : y ^ 2 ≤ (13 / 64) ^ 2 := pow_le_pow_left₀ hy0 hy13 2
    have a3 : y ^ 3 ≤ (13 / 64) ^ 3 := pow_le_pow_left₀ hy0 hy13 3
    norm_num at a2 a3
    linarith
  have g2 := mul_le_mul_of_nonneg_left g1 (by positivity : (0 : ℝ) ≤ x * y ^ 3)
  have hP : C0 + C1 * y + C2 * y ^ 2 + (C3 - 6000000 * x) * y ^ 3 ≤
      C0 + C1 * y + C2 * y ^ 2 + C3 * y ^ 3 + C4 * y ^ 4 + C5 * y ^ 5 + C6 * y ^ 6 := by
    nlinarith
  -- `C₂y² + B_*y³ ≥ min(0, C₂/105)`, then the bound linear in `y`
  have hbpos : 0 < 15 / 16 * (1 / 2 - x) := by linarith
  have lin : ∀ c0 c1 : ℝ, 0 < c0 → 0 < c0 + 15 / 16 * (1 / 2 - x) * c1 → 0 < c0 + c1 * y := by
    intro c0 c1 hc0 hc1
    have : 0 < 15 / 16 * (1 / 2 - x) * (c0 + c1 * y) := by
      have e2 : 15 / 16 * (1 / 2 - x) * (c0 + c1 * y) =
          (15 / 16 * (1 / 2 - x) - y) * c0 + y * (c0 + 15 / 16 * (1 / 2 - x) * c1) := by ring
      rw [e2]
      rcases eq_or_lt_of_le hy0 with hy | hy
      · rw [← hy]; nlinarith
      · nlinarith [mul_pos hy hc1, mul_nonneg (by linarith : (0 : ℝ) ≤ 15 / 16 * (1 / 2 - x) - y) hc0.le]
    exact pos_of_mul_pos_right this hbpos.le
  rcases le_total 0 C2 with hC2 | hC2
  · have h3 : 0 ≤ C2 * y ^ 2 + (C3 - 6000000 * x) * y ^ 3 := by
      have := mul_nonneg hC2 (pow_nonneg hy0 2)
      have := mul_nonneg uB.le (pow_nonneg hy0 3)
      linarith
    have := lin C0 C1 u0 uRb
    linarith
  · have hcub := nlt_unit_cubic hy0
    have h3 : C2 / 105 ≤ C2 * y ^ 2 + (C3 - 6000000 * x) * y ^ 3 := by
      have k1 : -C2 * (79 / 20) * y ^ 3 ≤ (C3 - 6000000 * x) * y ^ 3 :=
        mul_le_mul_of_nonneg_right (by linarith) (pow_nonneg hy0 3)
      have k2 : 0 ≤ -C2 * (79 / 20 * y ^ 3 - y ^ 2 + 1 / 105) :=
        mul_nonneg (by linarith) hcub.le
      nlinarith
    have := lin (C0 + C2 / 105) C1 uR0 (by linarith)
    linarith

/-- **The outer face** `j = 5h/7`: for `3/7 ≤ x ≤ 4/7`,
`0 ≤ y ≤ 2/31`, the circuit at `t = (12 - 7x)/24` is positive. -/
theorem nlt_face_outer {x y : ℝ} (h1 : 3 / 7 ≤ x) (h2 : x ≤ 4 / 7) (hy0 : 0 ≤ y)
    (hy : y ≤ 2 / 31) :
    0 < nltSt0 ((12 - 7 * x) / 24) x + nltSt1 ((12 - 7 * x) / 24) x * y
      + nltSt2 ((12 - 7 * x) / 24) x * y ^ 2 + nltSt3 ((12 - 7 * x) / 24) x * y ^ 3
      + nltSt4 ((12 - 7 * x) / 24) x * y ^ 4 + nltSt5 ((12 - 7 * x) / 24) x * y ^ 5
      + nltSt6 ((12 - 7 * x) / 24) x * y ^ 6 := by
  rw [nlt_Co0_eq, nlt_Co1_eq, nlt_Co2_eq, nlt_Co3_eq, nlt_Co4_eq, nlt_Co5_eq, nlt_Co6_eq]
  have c0 := nltOf0_pos h1 h2
  have c1 := nltOf1_pos h1 h2
  have c2 := nltOf2_pos h1 h2
  have c3 := nltOf3_pos h1 h2
  have c4 := nltOf4_pos h1 h2
  have c5 := nltOf5_pos h1 h2
  have c6 := nltOf6_pos h1 h2
  unfold nltOf0 nltOf1 nltOf2 nltOf3 nltOf4 nltOf5 nltOf6 at *
  -- `S_y > 0` on `[0, 2/31]`, hence `S ≥ S(x, 0) = C₀ > 10`
  have a2 : y ^ 2 ≤ 2 / 31 * y := by nlinarith
  have a4 : y ^ 4 ≤ (2 / 31) ^ 3 * y := by
    have := pow_le_pow_left₀ hy0 hy 3
    nlinarith [pow_nonneg hy0 3]
  have a5 : y ^ 5 ≤ (2 / 31) ^ 4 * y := by
    have := pow_le_pow_left₀ hy0 hy 4
    nlinarith [pow_nonneg hy0 4]
  have k2 : -2000 * y ^ 2 ≤ nltCo2 x * y ^ 2 := mul_le_mul_of_nonneg_right c2.le (pow_nonneg hy0 2)
  have k3 : 0 ≤ nltCo3 x * y ^ 3 := mul_nonneg c3.le (pow_nonneg hy0 3)
  have k4 : 0 ≤ nltCo4 x * y ^ 4 := mul_nonneg c4.le (pow_nonneg hy0 4)
  have k5 : -50000 * y ^ 5 ≤ nltCo5 x * y ^ 5 := mul_le_mul_of_nonneg_right c5.le (pow_nonneg hy0 5)
  have k6 : -3000 * y ^ 6 ≤ nltCo6 x * y ^ 6 := mul_le_mul_of_nonneg_right c6.le (pow_nonneg hy0 6)
  have k1 : 800 * y ≤ nltCo1 x * y := mul_le_mul_of_nonneg_right c1.le hy0
  have a6 : y ^ 6 ≤ (2 / 31) ^ 5 * y := by
    have := pow_le_pow_left₀ hy0 hy 5
    nlinarith [pow_nonneg hy0 5]
  norm_num at a4 a5 a6
  nlinarith

end SmoothedOctagon
