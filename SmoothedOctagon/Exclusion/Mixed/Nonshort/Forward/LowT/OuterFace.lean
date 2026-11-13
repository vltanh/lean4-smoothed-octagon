module

public import SmoothedOctagon.Exclusion.Mixed.Nonshort.Forward.LowT.InitialFace

/-!
# The low-scale outer face

On `j = 5h/7`, fix the fraction of the maximum admissible duration.
The circuit increases with the scale along this curve, so its sign follows
from the initial face at `h = 1/4`.
-/

@[expose] public section

namespace SmoothedOctagon

/-- The coefficient of `y^0` on the outer face. -/
noncomputable def nltCo0 {R : Type*} [CommRing R] [Algebra ℝ R] (x : R) : R :=
  (-146 / 3 : ℝ) • x ^ 2
    + (1703 / 18 : ℝ) • x ^ 3
    + (-11383 / 12 : ℝ) • x ^ 4
    + (8491 / 36 : ℝ) • x ^ 5
    + (273903 / 64 : ℝ) • x ^ 6
    + (92134651 / 20736 : ℝ) • x ^ 7
    + (42875 / 24 : ℝ) • x ^ 8
    + (40817 / 144 : ℝ) • x ^ 9

theorem nlt_Co0_eq (x : ℝ) : nltSt0 ((12 - 7 * x) / 24) x = nltCo0 x := by
  norm_num [nltSt0, nltCo0, smul_eq_mul]
  ring

/-- The coefficient of `y^1` on the outer face. -/
noncomputable def nltCo1 {R : Type*} [CommRing R] [Algebra ℝ R] (x : R) : R :=
  (-760 / 3 : ℝ) • x
    + (52450 / 9 : ℝ) • x ^ 2
    + (85877 / 18 : ℝ) • x ^ 3
    + (-1972985 / 144 : ℝ) • x ^ 4
    + (-18808865 / 1728 : ℝ) • x ^ 5
    + (43245665 / 3456 : ℝ) • x ^ 6
    + (240616649 / 13824 : ℝ) • x ^ 7
    + (14201327 / 1728 : ℝ) • x ^ 8
    + (3542161 / 1728 : ℝ) • x ^ 9
    + (40817 / 144 : ℝ) • x ^ 10

theorem nlt_Co1_eq (x : ℝ) : nltSt1 ((12 - 7 * x) / 24) x = nltCo1 x := by
  norm_num [nltSt1, nltCo1, smul_eq_mul]
  ring

/-- The coefficient of `y^2` on the outer face. -/
noncomputable def nltCo2 {R : Type*} [CommRing R] [Algebra ℝ R] (x : R) : R :=
  (-608 / 3 : ℝ) • 1
    + (42836 / 9 : ℝ) • x
    + (281723 / 18 : ℝ) • x ^ 2
    + (-468623 / 72 : ℝ) • x ^ 3
    + (-38213467 / 864 : ℝ) • x ^ 4
    + (-136385543 / 3456 : ℝ) • x ^ 5
    + (-16090531 / 864 : ℝ) • x ^ 6
    + (-113883629 / 10368 : ℝ) • x ^ 7
    + (-2481899 / 384 : ℝ) • x ^ 8
    + (-6680317 / 3456 : ℝ) • x ^ 9
    + (-145775 / 864 : ℝ) • x ^ 10

theorem nlt_Co2_eq (x : ℝ) : nltSt2 ((12 - 7 * x) / 24) x = nltCo2 x := by
  norm_num [nltSt2, nltCo2, smul_eq_mul]
  ring

/-- The coefficient of `y^3` on the outer face. -/
noncomputable def nltCo3 {R : Type*} [CommRing R] [Algebra ℝ R] (x : R) : R :=
  (19456 / 3 : ℝ) • 1
    + (388496 / 9 : ℝ) • x
    + (286657 / 2 : ℝ) • x ^ 2
    + (62450465 / 216 : ℝ) • x ^ 3
    + (94747547 / 288 : ℝ) • x ^ 4
    + (1262385373 / 10368 : ℝ) • x ^ 5
    + (-1352480477 / 10368 : ℝ) • x ^ 6
    + (-3407982385 / 20736 : ℝ) • x ^ 7
    + (-745859959 / 10368 : ℝ) • x ^ 8
    + (-12825239 / 864 : ℝ) • x ^ 9
    + (-425663 / 288 : ℝ) • x ^ 10

theorem nlt_Co3_eq (x : ℝ) : nltSt3 ((12 - 7 * x) / 24) x = nltCo3 x := by
  norm_num [nltSt3, nltCo3, smul_eq_mul]
  ring

/-- The coefficient of `y^4` on the outer face. -/
noncomputable def nltCo4 {R : Type*} [CommRing R] [Algebra ℝ R] (x : R) : R :=
  (-2736 : ℝ) • 1
    + (-24484 / 3 : ℝ) • x
    + (1172225 / 18 : ℝ) • x ^ 2
    + (21947915 / 72 : ℝ) • x ^ 3
    + (398494483 / 864 : ℝ) • x ^ 4
    + (260416511 / 1152 : ℝ) • x ^ 5
    + (-205809391 / 1728 : ℝ) • x ^ 6
    + (-1271989063 / 6912 : ℝ) • x ^ 7
    + (-7644493 / 96 : ℝ) • x ^ 8
    + (-8817613 / 576 : ℝ) • x ^ 9
    + (-833833 / 576 : ℝ) • x ^ 10

theorem nlt_Co4_eq (x : ℝ) : nltSt4 ((12 - 7 * x) / 24) x = nltCo4 x := by
  norm_num [nltSt4, nltCo4, smul_eq_mul]
  ring

/-- The coefficient of `y^5` on the outer face. -/
noncomputable def nltCo5 {R : Type*} [CommRing R] [Algebra ℝ R] (x : R) : R :=
  (-9728 : ℝ) • 1
    + (-143822 / 3 : ℝ) • x
    + (-642419 / 9 : ℝ) • x ^ 2
    + (4375 / 2 : ℝ) • x ^ 3
    + (14398915 / 144 : ℝ) • x ^ 4
    + (261991735 / 3456 : ℝ) • x ^ 5
    + (-13547797 / 864 : ℝ) • x ^ 6
    + (-1808944133 / 41472 : ℝ) • x ^ 7
    + (-4407155 / 216 : ℝ) • x ^ 8
    + (-13943027 / 3456 : ℝ) • x ^ 9
    + (-1358623 / 3456 : ℝ) • x ^ 10

theorem nlt_Co5_eq (x : ℝ) : nltSt5 ((12 - 7 * x) / 24) x = nltCo5 x := by
  norm_num [nltSt5, nltCo5, smul_eq_mul]
  ring

/-- The coefficient of `y^6` on the outer face. -/
noncomputable def nltCo6 {R : Type*} [CommRing R] [Algebra ℝ R] (x : R) : R :=
  (-304 : ℝ) • 1
    + (-1626 : ℝ) • x
    + (-17443 / 6 : ℝ) • x ^ 2
    + (-448201 / 216 : ℝ) • x ^ 3
    + (-86123 / 864 : ℝ) • x ^ 4
    + (1915051 / 2592 : ℝ) • x ^ 5
    + (4339501 / 10368 : ℝ) • x ^ 6
    + (628367 / 10368 : ℝ) • x ^ 7
    + (-62327 / 5184 : ℝ) • x ^ 8
    + (-595 / 216 : ℝ) • x ^ 9

theorem nlt_Co6_eq (x : ℝ) : nltSt6 ((12 - 7 * x) / 24) x = nltCo6 x := by
  norm_num [nltSt6, nltCo6, smul_eq_mul]
  ring

private noncomputable def radial (i : ℕ) (p : Polynomial ℝ) : Polynomial ℝ :=
  Polynomial.X * (6 + 5 * Polynomial.X) * p.derivative + Polynomial.C (6 * (i : ℝ)) * p

private theorem constant_nonneg {x : ℝ} (h0 : 3 / 7 ≤ x) (h1 : x ≤ 4 / 7) :
    0 ≤ (radial 0 (nltCo0 Polynomial.X)).eval x := by
  obtain ⟨u, rfl⟩ : ∃ u, x = (3 / 7) + u := ⟨x - (3 / 7), by ring⟩
  have hu : 0 ≤ u := by linarith only [h0]
  have hu1 : u ≤ 1 / 7 := by linarith only [h1]
  have lo (n : ℕ) : 0 ≤ u ^ n := pow_nonneg hu n
  have hi (n : ℕ) : u ^ n ≤ (1 / 7 : ℝ) ^ n := pow_le_pow_left₀ hu hu1 n
  norm_num [radial, nltCo0, Polynomial.derivative_mul,
    Polynomial.derivative_pow]
  nlinarith only [lo 1, lo 2, lo 3, lo 4, lo 5, lo 6, lo 7, lo 8, lo 9, lo 10, lo 11,
    hi 1, hi 2, hi 3, hi 4, hi 5, hi 6, hi 7, hi 8, hi 9, hi 10, hi 11]

private theorem quadratic_nonpos {x : ℝ} (h0 : 3 / 7 ≤ x) (h1 : x ≤ 4 / 7) :
    (radial 2 (nltCo2 Polynomial.X)).eval x ≤ 0 := by
  obtain ⟨u, rfl⟩ : ∃ u, x = (3 / 7) + u := ⟨x - (3 / 7), by ring⟩
  have hu : 0 ≤ u := by linarith only [h0]
  have hu1 : u ≤ 1 / 7 := by linarith only [h1]
  have lo (n : ℕ) : 0 ≤ u ^ n := pow_nonneg hu n
  have hi (n : ℕ) : u ^ n ≤ (1 / 7 : ℝ) ^ n := pow_le_pow_left₀ hu hu1 n
  norm_num [radial, nltCo2, Polynomial.derivative_mul,
    Polynomial.derivative_pow]
  nlinarith only [lo 1, lo 2, lo 3, lo 4, lo 5, lo 6, lo 7, lo 8, lo 9, lo 10, lo 11,
    hi 1, hi 2, hi 3, hi 4, hi 5, hi 6, hi 7, hi 8, hi 9, hi 10, hi 11]

private theorem linear_floor {x : ℝ} (h0 : 3 / 7 ≤ x) (h1 : x ≤ 4 / 7) :
    10000 ≤ (radial 1 (nltCo1 Polynomial.X)).eval x
      + (radial 2 (nltCo2 Polynomial.X)).eval x / 15 := by
  obtain ⟨u, rfl⟩ : ∃ u, x = (3 / 7) + u := ⟨x - (3 / 7), by ring⟩
  have hu : 0 ≤ u := by linarith only [h0]
  have hu1 : u ≤ 1 / 7 := by linarith only [h1]
  have lo (n : ℕ) : 0 ≤ u ^ n := pow_nonneg hu n
  have hi (n : ℕ) : u ^ n ≤ (1 / 7 : ℝ) ^ n := pow_le_pow_left₀ hu hu1 n
  norm_num [radial, nltCo1, nltCo2, Polynomial.derivative_mul,
    Polynomial.derivative_pow]
  nlinarith only [lo 1, lo 2, lo 3, lo 4, lo 5, lo 6, lo 7, lo 8, lo 9, lo 10, lo 11,
    hi 1, hi 2, hi 3, hi 4, hi 5, hi 6, hi 7, hi 8, hi 9, hi 10, hi 11]

private theorem cubic_nonneg {x : ℝ} (h0 : 3 / 7 ≤ x) (h1 : x ≤ 4 / 7) :
    0 ≤ (radial 3 (nltCo3 Polynomial.X)).eval x := by
  obtain ⟨u, rfl⟩ : ∃ u, x = (3 / 7) + u := ⟨x - (3 / 7), by ring⟩
  have hu : 0 ≤ u := by linarith only [h0]
  have hu1 : u ≤ 1 / 7 := by linarith only [h1]
  have lo (n : ℕ) : 0 ≤ u ^ n := pow_nonneg hu n
  have hi (n : ℕ) : u ^ n ≤ (1 / 7 : ℝ) ^ n := pow_le_pow_left₀ hu hu1 n
  norm_num [radial, nltCo3, Polynomial.derivative_mul,
    Polynomial.derivative_pow]
  nlinarith only [lo 1, lo 2, lo 3, lo 4, lo 5, lo 6, lo 7, lo 8, lo 9, lo 10, lo 11,
    hi 1, hi 2, hi 3, hi 4, hi 5, hi 6, hi 7, hi 8, hi 9, hi 10, hi 11]

private theorem fourth_nonneg {x : ℝ} (h0 : 3 / 7 ≤ x) (h1 : x ≤ 4 / 7) :
    0 ≤ (radial 4 (nltCo4 Polynomial.X)).eval x := by
  obtain ⟨u, rfl⟩ : ∃ u, x = (3 / 7) + u := ⟨x - (3 / 7), by ring⟩
  have hu : 0 ≤ u := by linarith only [h0]
  have hu1 : u ≤ 1 / 7 := by linarith only [h1]
  have lo (n : ℕ) : 0 ≤ u ^ n := pow_nonneg hu n
  have hi (n : ℕ) : u ^ n ≤ (1 / 7 : ℝ) ^ n := pow_le_pow_left₀ hu hu1 n
  norm_num [radial, nltCo4, Polynomial.derivative_mul,
    Polynomial.derivative_pow]
  nlinarith only [lo 1, lo 2, lo 3, lo 4, lo 5, lo 6, lo 7, lo 8, lo 9, lo 10, lo 11,
    hi 1, hi 2, hi 3, hi 4, hi 5, hi 6, hi 7, hi 8, hi 9, hi 10, hi 11]

private theorem fifth_floor {x : ℝ} (h0 : 3 / 7 ≤ x) (h1 : x ≤ 4 / 7) :
    -2000000 ≤ (radial 5 (nltCo5 Polynomial.X)).eval x := by
  obtain ⟨u, rfl⟩ : ∃ u, x = (3 / 7) + u := ⟨x - (3 / 7), by ring⟩
  have hu : 0 ≤ u := by linarith only [h0]
  have hu1 : u ≤ 1 / 7 := by linarith only [h1]
  have lo (n : ℕ) : 0 ≤ u ^ n := pow_nonneg hu n
  have hi (n : ℕ) : u ^ n ≤ (1 / 7 : ℝ) ^ n := pow_le_pow_left₀ hu hu1 n
  norm_num [radial, nltCo5, Polynomial.derivative_mul,
    Polynomial.derivative_pow]
  nlinarith only [lo 1, lo 2, lo 3, lo 4, lo 5, lo 6, lo 7, lo 8, lo 9, lo 10, lo 11,
    hi 1, hi 2, hi 3, hi 4, hi 5, hi 6, hi 7, hi 8, hi 9, hi 10, hi 11]

private theorem sixth_floor {x : ℝ} (h0 : 3 / 7 ≤ x) (h1 : x ≤ 4 / 7) :
    -200000 ≤ (radial 6 (nltCo6 Polynomial.X)).eval x := by
  obtain ⟨u, rfl⟩ : ∃ u, x = (3 / 7) + u := ⟨x - (3 / 7), by ring⟩
  have hu : 0 ≤ u := by linarith only [h0]
  have hu1 : u ≤ 1 / 7 := by linarith only [h1]
  have lo (n : ℕ) : 0 ≤ u ^ n := pow_nonneg hu n
  have hi (n : ℕ) : u ^ n ≤ (1 / 7 : ℝ) ^ n := pow_le_pow_left₀ hu hu1 n
  norm_num [radial, nltCo6, Polynomial.derivative_mul,
    Polynomial.derivative_pow]
  nlinarith only [lo 1, lo 2, lo 3, lo 4, lo 5, lo 6, lo 7, lo 8, lo 9, lo 10, lo 11,
    hi 1, hi 2, hi 3, hi 4, hi 5, hi 6, hi 7, hi 8, hi 9, hi 10, hi 11]

private noncomputable def outerCoefficient (i : Fin 7) : Polynomial ℝ :=
  ![nltCo0 Polynomial.X, nltCo1 Polynomial.X, nltCo2 Polynomial.X,
    nltCo3 Polynomial.X, nltCo4 Polynomial.X, nltCo5 Polynomial.X,
    nltCo6 Polynomial.X] i

private noncomputable def outerCircuit (x y : ℝ) : ℝ :=
  ∑ i : Fin 7, (outerCoefficient i).eval x * y ^ (i : ℕ)

private noncomputable def outerRadial (x y : ℝ) : ℝ :=
  ∑ i : Fin 7, (radial i (outerCoefficient i)).eval x * y ^ (i : ℕ)

/-- The derivative along a fixed fraction of the allowed duration is nonnegative. -/
private theorem radial_nonneg {x y : ℝ} (h0 : 3 / 7 ≤ x) (h1 : x ≤ 4 / 7)
    (hy0 : 0 ≤ y) (hy1 : y ≤ 1 / 15) : 0 ≤ outerRadial x y := by
  have r0 := constant_nonneg h0 h1
  have r2 := quadratic_nonpos h0 h1
  have r12 := linear_floor h0 h1
  have r3 := mul_nonneg (cubic_nonneg h0 h1) (pow_nonneg hy0 3)
  have r4 := mul_nonneg (fourth_nonneg h0 h1) (pow_nonneg hy0 4)
  have r5 := mul_le_mul_of_nonneg_right (fifth_floor h0 h1) (pow_nonneg hy0 5)
  have r6 := mul_le_mul_of_nonneg_right (sixth_floor h0 h1) (pow_nonneg hy0 6)
  have r2y := mul_le_mul_of_nonpos_left hy1 r2
  have pair : 10000 * y ≤ (radial 1 (nltCo1 Polynomial.X)).eval x * y
      + (radial 2 (nltCo2 Polynomial.X)).eval x * y ^ 2 := by
    have hlinear := mul_le_mul_of_nonneg_right r12 hy0
    have hquad := mul_le_mul_of_nonneg_right r2y hy0
    nlinarith only [hlinear, hquad]
  have tail (n : ℕ) : y ^ (n + 1) ≤ (1 / 15 : ℝ) ^ n * y := by
    have := mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hy0 hy1 n) hy0
    simpa only [pow_succ] using this
  unfold outerRadial
  norm_num [Fin.sum_univ_succ, outerCoefficient]
  nlinarith only [r0, pair, r3, r4, r5, r6, tail 4, tail 5]

private noncomputable def durationFraction (θ s : ℝ) : ℝ := θ * s / (6 + 5 * s)

private theorem duration_deriv (θ : ℝ) {s : ℝ} (hs : 0 < s) :
    HasDerivAt (durationFraction θ) (6 * durationFraction θ s / (s * (6 + 5 * s))) s := by
  have hd : (6 + 5 * s) ≠ 0 := by positivity
  have H : HasDerivAt (durationFraction θ)
      ((θ * (6 + 5 * s) - θ * s * 5) / (6 + 5 * s) ^ 2) s := by
    change HasDerivAt (fun u : ℝ => θ * u / (6 + 5 * u)) _ s
    simpa only [id_eq, mul_one] using
      (((hasDerivAt_id s).const_mul θ).fun_div
        (((hasDerivAt_id s).const_mul 5).const_add 6) hd)
  convert H using 1
  dsimp [durationFraction]
  field_simp [ne_of_gt hs, hd]
  ring

private theorem term_deriv (p : Polynomial ℝ) (n : ℕ) (θ : ℝ) {s : ℝ} (hs : 0 < s) :
    HasDerivAt (fun s => p.eval s * durationFraction θ s ^ n)
      ((radial n p).eval s * durationFraction θ s ^ n / (s * (6 + 5 * s))) s := by
  have hd : (6 + 5 * s) ≠ 0 := by positivity
  convert (p.hasDerivAt s).mul ((duration_deriv θ hs).pow n) using 1
  simp only [radial, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_X,
    Polynomial.eval_ofNat, Polynomial.eval_C]
  rcases n with _ | n
  · norm_num
    field_simp
  · simp only [Nat.cast_add, Nat.cast_one, Nat.add_sub_cancel, pow_succ, Pi.pow_apply]
    field_simp [ne_of_gt hs, hd]

private theorem circuit_deriv (θ : ℝ) {s : ℝ} (hs : 0 < s) :
    HasDerivAt (fun s => outerCircuit s (durationFraction θ s))
      (outerRadial s (durationFraction θ s) / (s * (6 + 5 * s))) s := by
  have H := HasDerivAt.fun_sum (u := Finset.univ)
    (fun (i : Fin 7) _ => term_deriv (outerCoefficient i) i θ hs)
  simpa only [outerCircuit, outerRadial, Finset.sum_div] using H

private theorem duration_bounds {θ s : ℝ} (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1)
    (hs0 : 3 / 7 ≤ s) (hs1 : s ≤ 4 / 7) :
    0 ≤ durationFraction θ s ∧ durationFraction θ s ≤ 1 / 15 := by
  have hs : 0 < s := by linarith only [hs0]
  constructor
  · exact div_nonneg (mul_nonneg hθ0 hs.le) (by positivity)
  · apply (div_le_iff₀ (by positivity : 0 < 6 + 5 * s)).mpr
    have := mul_le_mul_of_nonneg_right hθ1 hs.le
    nlinarith only [this, hs1]

private theorem circuit_mono {θ : ℝ} (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1) :
    MonotoneOn (fun s => outerCircuit s (durationFraction θ s)) (Set.Icc (3 / 7) (4 / 7)) := by
  apply monotoneOn_of_deriv_nonneg (convex_Icc _ _)
  · intro s hs
    exact (circuit_deriv θ (by linarith only [hs.1])).continuousAt.continuousWithinAt
  · intro s hs
    rw [interior_Icc] at hs
    exact (circuit_deriv θ (by linarith only [hs.1])).differentiableAt.differentiableWithinAt
  · intro s hs
    rw [interior_Icc] at hs
    rw [(circuit_deriv θ (by linarith only [hs.1])).deriv]
    have hb := duration_bounds hθ0 hθ1 hs.1.le hs.2.le
    have hspos : 0 < s := by linarith only [hs.1]
    exact div_nonneg (radial_nonneg hs.1.le hs.2.le hb.1 hb.2) (by positivity)

/-- On the outer face `j = 5h/7`, the circuit is positive throughout
its exact duration interval `0 ≤ y`, `y(6 + 5x) ≤ x`. -/
theorem nlt_face_outer {x y : ℝ} (h1 : 3 / 7 ≤ x) (h2 : x ≤ 4 / 7) (hy0 : 0 ≤ y)
    (hy : y * (6 + 5 * x) ≤ x) :
    0 < nltSt0 ((12 - 7 * x) / 24) x + nltSt1 ((12 - 7 * x) / 24) x * y
      + nltSt2 ((12 - 7 * x) / 24) x * y ^ 2 + nltSt3 ((12 - 7 * x) / 24) x * y ^ 3
      + nltSt4 ((12 - 7 * x) / 24) x * y ^ 4 + nltSt5 ((12 - 7 * x) / 24) x * y ^ 5
      + nltSt6 ((12 - 7 * x) / 24) x * y ^ 6 := by
  have hx : 0 < x := by linarith only [h1]
  let θ := y * (6 + 5 * x) / x
  have hθ0 : 0 ≤ θ := by positivity
  have hθ1 : θ ≤ 1 := (div_le_one hx).mpr hy
  have m := circuit_mono hθ0 hθ1 (a := 3 / 7) (b := x)
    ⟨le_rfl, by norm_num⟩ ⟨h1, h2⟩ h1
  have ey : durationFraction θ x = y := by
    dsimp [durationFraction, θ]
    field_simp
  have eb : durationFraction θ (3 / 7) = θ / 19 := by
    dsimp [durationFraction]
    ring
  change outerCircuit (3 / 7) (durationFraction θ (3 / 7)) ≤
    outerCircuit x (durationFraction θ x) at m
  rw [ey, eb] at m
  have base := nlt_face_unit (x := 3 / 7) (y := θ / 19)
    (by norm_num) le_rfl (by positivity) (by nlinarith only [hθ1])
  have e : (3 / 8 : ℝ) = (12 - 7 * (3 / 7)) / 24 := by norm_num
  rw [e, nlt_Co0_eq, nlt_Co1_eq, nlt_Co2_eq, nlt_Co3_eq, nlt_Co4_eq,
    nlt_Co5_eq, nlt_Co6_eq] at base
  have initial : 0 < outerCircuit (3 / 7) (θ / 19) := by
    simpa [outerCircuit, outerCoefficient, Fin.sum_univ_succ,
      nltCo0, nltCo1, nltCo2, nltCo3, nltCo4, nltCo5, nltCo6, add_assoc] using base
  have final := lt_of_lt_of_le initial m
  rw [nlt_Co0_eq, nlt_Co1_eq, nlt_Co2_eq, nlt_Co3_eq, nlt_Co4_eq, nlt_Co5_eq, nlt_Co6_eq]
  simpa [outerCircuit, outerCoefficient, Fin.sum_univ_succ,
    nltCo0, nltCo1, nltCo2, nltCo3, nltCo4, nltCo5, nltCo6, add_assoc] using final

end SmoothedOctagon
