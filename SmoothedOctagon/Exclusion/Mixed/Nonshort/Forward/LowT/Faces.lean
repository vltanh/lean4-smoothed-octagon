module

public import SmoothedOctagon.Exclusion.Mixed.Nonshort.Forward.LowT.InitialFace

/-!
# The low-scale outer face

On `j = 5h/7`, the duration increment is at most `2/31`.
Coefficient bounds make the circuit increase with the duration, and its
initial value is positive. The initial scale face is proved in `InitialFace`.
-/

@[expose] public section

namespace SmoothedOctagon

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
