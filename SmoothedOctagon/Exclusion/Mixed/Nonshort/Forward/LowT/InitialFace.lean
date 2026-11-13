module

public import SmoothedOctagon.Exclusion.Mixed.Nonshort.Forward.LowT.Circuit
public import SmoothedOctagon.Exclusion.Mixed.Nonshort.UnitShape.Boundary

/-!
# The initial face: a cubic square and quadratic Taylor bounds

At the one-quarter scale, the negative quadratic term is absorbed by
`(1 - 6y)²(1 + 12y)`. The exact duration endpoint controls the linear term.
Quadratic Taylor bounds control the two remaining one-variable minima.
-/

@[expose] public section

namespace SmoothedOctagon

/-- `C_0 = 1536 nltSt0 (3/8) x` on the initial face. -/
def nltCu0 {R : Type*} [CommRing R] (x : R) : R :=
  3793920 * x - 15602560 * x ^ 2 + 9611930 * x ^ 3 + 20231160 * x ^ 4 - 11579400 * x ^ 5 - 2570400 * x ^ 6

theorem nlt_Cu0_eq (x : ℝ) : 1536 * nltSt0 (3 / 8) x = nltCu0 x := by
  unfold nltSt0 nltCu0; ring

/-- `C_1 = 1536 nltSt1 (3/8) x` on the initial face. -/
def nltCu1 {R : Type*} [CommRing R] (x : R) : R :=
  2276352 - 11965152 * x - 19510992 * x ^ 2 + 95366541 * x ^ 3 + 51084660 * x ^ 4 - 86017524 * x ^ 5 - 38064240 * x ^ 6 - 2640960 * x ^ 7

theorem nlt_Cu1_eq (x : ℝ) : 1536 * nltSt1 (3 / 8) x = nltCu1 x := by
  unfold nltSt1 nltCu1; ring

/-- `C_2 = 1536 nltSt2 (3/8) x` on the initial face. -/
def nltCu2 {R : Type*} [CommRing R] (x : R) : R :=
  -6400416 - 38051816 * x + 58530680 * x ^ 2 + 206949420 * x ^ 3 + 54511676 * x ^ 4 - 155046960 * x ^ 5 - 125578224 * x ^ 6 - 37931040 * x ^ 7 - 3290112 * x ^ 8

theorem nlt_Cu2_eq (x : ℝ) : 1536 * nltSt2 (3 / 8) x = nltCu2 x := by
  unfold nltSt2 nltCu2; ring

/-- `C_3 = 1536 nltSt3 (3/8) x` on the initial face. -/
def nltCu3 {R : Type*} [CommRing R] (x : R) : R :=
  -6671280 - 3710852 * x + 207692872 * x ^ 2 + 673286150 * x ^ 3 + 1041675896 * x ^ 4 + 815901492 * x ^ 5 + 259700688 * x ^ 6 + 15220800 * x ^ 7 - 78336 * x ^ 8

theorem nlt_Cu3_eq (x : ℝ) : 1536 * nltSt3 (3 / 8) x = nltCu3 x := by
  unfold nltSt3 nltCu3; ring

/-- `C_4 = 1536 nltSt4 (3/8) x` on the initial face. -/
def nltCu4 {R : Type*} [CommRing R] (x : R) : R :=
  -7778448 - 49152972 * x + 9044160 * x ^ 2 + 516188634 * x ^ 3 + 1199150640 * x ^ 4 + 1101130752 * x ^ 5 + 416220768 * x ^ 6 + 50047200 * x ^ 7 + 2271744 * x ^ 8

theorem nlt_Cu4_eq (x : ℝ) : 1536 * nltSt4 (3 / 8) x = nltCu4 x := by
  unfold nltSt4 nltCu4; ring

/-- `C_5 = 1536 nltSt5 (3/8) x` on the initial face. -/
def nltCu5 {R : Type*} [CommRing R] (x : R) : R :=
  -10104048 - 69924132 * x - 140397660 * x ^ 2 - 40976151 * x ^ 3 + 176006160 * x ^ 4 + 199922532 * x ^ 5 + 62655048 * x ^ 6 - 2232000 * x ^ 7 - 1253376 * x ^ 8

theorem nlt_Cu5_eq (x : ℝ) : 1536 * nltSt5 (3 / 8) x = nltCu5 x := by
  unfold nltSt5 nltCu5; ring

/-- `C_6 = 1536 nltSt6 (3/8) x` on the initial face. -/
def nltCu6 {R : Type*} [CommRing R] (x : R) : R :=
  -295488 - 2093472 * x - 4182660 * x ^ 2 - 5293836 * x ^ 3 - 4773240 * x ^ 4 - 2945808 * x ^ 5 - 1608192 * x ^ 6 - 604800 * x ^ 7 - 78336 * x ^ 8

theorem nlt_Cu6_eq (x : ℝ) : 1536 * nltSt6 (3 / 8) x = nltCu6 x := by
  unfold nltSt6 nltCu6; ring

private theorem power_tail {u r : ℝ} (hu : |u| ≤ r) (n : ℕ) :
    -(r ^ n * u ^ 2) ≤ u ^ (n + 2) ∧ u ^ (n + 2) ≤ r ^ n * u ^ 2 := by
  have hp := mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (abs_nonneg u) hu n) (sq_nonneg u)
  have he : |u ^ (n + 2)| = |u| ^ n * u ^ 2 := by
    rw [abs_pow, pow_add, sq_abs]
  rw [← he] at hp
  exact abs_le.mp hp

private theorem quadratic_floor {a b c m u v : ℝ} (hc : 0 < c)
    (ht : c * u ^ 2 ≤ v - a - b * u) (hd : b ^ 2 < 4 * c * (a - m)) : m < v := by
  have h := mul_le_mul_of_nonneg_left ht (show 0 ≤ 4 * c by positivity)
  have hp : 0 < 4 * c * (v - m) := by nlinarith only [h, hd, sq_nonneg (2 * c * u + b)]
  have hvm := pos_of_mul_pos_right hp (show 0 ≤ 4 * c by positivity)
  linarith only [hvm]

private noncomputable def constPoly : Polynomial ℝ := nltCu0 Polynomial.X
private noncomputable def r0Poly : Polynomial ℝ :=
  nltCu0 Polynomial.X + Polynomial.C (1 / 108) * nltCu2 Polynomial.X
private noncomputable def leftPoly : Polynomial ℝ :=
  (1 + 4 * Polynomial.X) * r0Poly + (1 - 2 * Polynomial.X) * nltCu1 Polynomial.X

private theorem constant_pos {x : ℝ} (h0 : 17 / 60 ≤ x) (h1 : x ≤ 3 / 7) :
    0 < nltCu0 x := by
  let u := x - (2 / 5)
  have hu : |u| ≤ 1 / 8 := by
    apply abs_le.mpr
    dsimp [u]
    constructor <;> linarith only [h0, h1]
  have tails (n : ℕ) := power_tail hu n
  have ht : 4000000 * u ^ 2 ≤ constPoly.eval ((2 / 5) + u) - constPoly.eval (2 / 5)
      - constPoly.derivative.eval (2 / 5) * u := by
    norm_num [constPoly, nltCu0, Polynomial.derivative_mul, Polynomial.derivative_pow]
    nlinarith only [(tails 1).1, (tails 1).2, (tails 2).1, (tails 2).2,
      (tails 3).1, (tails 3).2, (tails 4).1, (tails 4).2,
      (tails 5).1, (tails 5).2, (tails 6).1, (tails 6).2,
      (tails 7).1, (tails 7).2, sq_nonneg u]
  have hd : constPoly.derivative.eval (2 / 5) ^ 2 <
      4 * (4000000 : ℝ) * (constPoly.eval (2 / 5) - (0)) := by
    norm_num [constPoly, nltCu0, Polynomial.derivative_mul, Polynomial.derivative_pow]
  have floor := quadratic_floor (by norm_num : (0 : ℝ) < 4000000) ht hd
  have he : (2 / 5) + u = x := by dsimp [u]; ring
  rw [he] at floor
  simpa [constPoly, nltCu0] using floor

private theorem r0_floor {x : ℝ} (h0 : 17 / 60 ≤ x) (h1 : x ≤ 3 / 7) :
    23000 ≤ nltCu0 x + nltCu2 x / 108 := by
  let u := x - (3 / 8)
  have hu : |u| ≤ 1 / 10 := by
    apply abs_le.mpr
    dsimp [u]
    constructor <;> linarith only [h0, h1]
  have tails (n : ℕ) := power_tail hu n
  have ht : 5000000 * u ^ 2 ≤ r0Poly.eval ((3 / 8) + u) - r0Poly.eval (3 / 8)
      - r0Poly.derivative.eval (3 / 8) * u := by
    norm_num [r0Poly, nltCu0, nltCu2, Polynomial.derivative_mul, Polynomial.derivative_pow]
    nlinarith only [(tails 1).1, (tails 1).2, (tails 2).1, (tails 2).2,
      (tails 3).1, (tails 3).2, (tails 4).1, (tails 4).2,
      (tails 5).1, (tails 5).2, (tails 6).1, (tails 6).2,
      (tails 7).1, (tails 7).2, sq_nonneg u]
  have hd : r0Poly.derivative.eval (3 / 8) ^ 2 <
      4 * (5000000 : ℝ) * (r0Poly.eval (3 / 8) - (23000)) := by
    norm_num [r0Poly, nltCu0, nltCu2, Polynomial.derivative_mul, Polynomial.derivative_pow]
  have floor := quadratic_floor (by norm_num : (0 : ℝ) < 5000000) ht hd
  have he : (3 / 8) + u = x := by dsimp [u]; ring
  rw [he] at floor
  simpa [r0Poly, nltCu0, nltCu2, div_eq_mul_inv, mul_comm] using floor.le

private theorem left_floor {x : ℝ} (h0 : 17 / 60 ≤ x) (h1 : x ≤ 1 / 3) :
    7500 ≤ (1 + 4 * x) * (nltCu0 x + nltCu2 x / 108) + (1 - 2 * x) * nltCu1 x := by
  let u := x - (7 / 24)
  have hu : |u| ≤ 1 / 24 := by
    apply abs_le.mpr
    dsimp [u]
    constructor <;> linarith only [h0, h1]
  have tails (n : ℕ) := power_tail hu n
  have ht : 20000000 * u ^ 2 ≤ leftPoly.eval ((7 / 24) + u) - leftPoly.eval (7 / 24)
      - leftPoly.derivative.eval (7 / 24) * u := by
    norm_num [leftPoly, r0Poly, nltCu0, nltCu1, nltCu2, Polynomial.derivative_mul, Polynomial.derivative_pow]
    nlinarith only [(tails 1).1, (tails 1).2, (tails 2).1, (tails 2).2,
      (tails 3).1, (tails 3).2, (tails 4).1, (tails 4).2,
      (tails 5).1, (tails 5).2, (tails 6).1, (tails 6).2,
      (tails 7).1, (tails 7).2, sq_nonneg u]
  have hd : leftPoly.derivative.eval (7 / 24) ^ 2 <
      4 * (20000000 : ℝ) * (leftPoly.eval (7 / 24) - (7500)) := by
    norm_num [leftPoly, r0Poly, nltCu0, nltCu1, nltCu2, Polynomial.derivative_mul, Polynomial.derivative_pow]
  have floor := quadratic_floor (by norm_num : (0 : ℝ) < 20000000) ht hd
  have he : (7 / 24) + u = x := by dsimp [u]; ring
  rw [he] at floor
  simpa [leftPoly, r0Poly, nltCu0, nltCu1, nltCu2, div_eq_mul_inv, mul_comm] using floor.le

private theorem fourth_nonneg {x : ℝ} (h0 : 17 / 60 ≤ x) (h1 : x ≤ 3 / 7) :
    0 ≤ nltCu4 x := by
  obtain ⟨u, rfl⟩ : ∃ u, x = (17 / 60) + u := ⟨x - (17 / 60), by ring⟩
  have hu : 0 ≤ u := by linarith only [h0]
  have hu1 : u ≤ 3 / 20 := by linarith only [h1]
  have steps (n : ℕ) := nlt_pw hu hu1 n
  norm_num [nltCu4]
  nlinarith only [steps 1, steps 2, steps 3, steps 4, steps 5, steps 6, steps 7,
    hu, hu1, sq_nonneg u, pow_nonneg hu 3, pow_nonneg hu 4,
    pow_nonneg hu 5, pow_nonneg hu 6, pow_nonneg hu 7, pow_nonneg hu 8]

private theorem fifth_lower {x : ℝ} (h0 : 17 / 60 ≤ x) (h1 : x ≤ 3 / 7) :
    -144000000 * x ≤ nltCu5 x := by
  obtain ⟨u, rfl⟩ : ∃ u, x = (17 / 60) + u := ⟨x - (17 / 60), by ring⟩
  have hu : 0 ≤ u := by linarith only [h0]
  have hu1 : u ≤ 3 / 20 := by linarith only [h1]
  have steps (n : ℕ) := nlt_pw hu hu1 n
  norm_num [nltCu5]
  nlinarith only [steps 1, steps 2, steps 3, steps 4, steps 5, steps 6, steps 7,
    hu, hu1, sq_nonneg u, pow_nonneg hu 3, pow_nonneg hu 4,
    pow_nonneg hu 5, pow_nonneg hu 6, pow_nonneg hu 7, pow_nonneg hu 8]

private theorem cubic_nonneg {x : ℝ} (h0 : 17 / 60 ≤ x) (h1 : x ≤ 3 / 7) :
    0 ≤ nltCu3 x - 6000000 * x := by
  obtain ⟨u, rfl⟩ : ∃ u, x = (17 / 60) + u := ⟨x - (17 / 60), by ring⟩
  have hu : 0 ≤ u := by linarith only [h0]
  have hu1 : u ≤ 3 / 20 := by linarith only [h1]
  have steps (n : ℕ) := nlt_pw hu hu1 n
  norm_num [nltCu3]
  nlinarith only [steps 1, steps 2, steps 3, steps 4, steps 5, steps 6, steps 7,
    hu, hu1, sq_nonneg u, pow_nonneg hu 3, pow_nonneg hu 4,
    pow_nonneg hu 5, pow_nonneg hu 6, pow_nonneg hu 7, pow_nonneg hu 8]

private theorem cubic_link {x : ℝ} (h0 : 17 / 60 ≤ x) (h1 : x ≤ 3 / 7) :
    -250000 ≤ nltCu3 x - 6000000 * x + 4 * nltCu2 x := by
  obtain ⟨u, rfl⟩ : ∃ u, x = (17 / 60) + u := ⟨x - (17 / 60), by ring⟩
  have hu : 0 ≤ u := by linarith only [h0]
  have hu1 : u ≤ 3 / 20 := by linarith only [h1]
  have steps (n : ℕ) := nlt_pw hu hu1 n
  norm_num [nltCu3, nltCu2]
  nlinarith only [steps 1, steps 2, steps 3, steps 4, steps 5, steps 6, steps 7,
    hu, hu1, sq_nonneg u, pow_nonneg hu 3, pow_nonneg hu 4,
    pow_nonneg hu 5, pow_nonneg hu 6, pow_nonneg hu 7, pow_nonneg hu 8]

private theorem linear_link {x : ℝ} (h0 : 17 / 60 ≤ x) (h1 : x ≤ 3 / 7) :
    0 ≤ nltCu1 x - nltCu2 x / 4 := by
  obtain ⟨u, rfl⟩ : ∃ u, x = (17 / 60) + u := ⟨x - (17 / 60), by ring⟩
  have hu : 0 ≤ u := by linarith only [h0]
  have hu1 : u ≤ 3 / 20 := by linarith only [h1]
  have steps (n : ℕ) := nlt_pw hu hu1 n
  norm_num [nltCu1, nltCu2]
  nlinarith only [steps 1, steps 2, steps 3, steps 4, steps 5, steps 6, steps 7,
    hu, hu1, sq_nonneg u, pow_nonneg hu 3, pow_nonneg hu 4,
    pow_nonneg hu 5, pow_nonneg hu 6, pow_nonneg hu 7, pow_nonneg hu 8]

private theorem linear_lower {x : ℝ} (h0 : 1 / 3 ≤ x) (h1 : x ≤ 3 / 7) :
    -125000 ≤ nltCu1 x := by
  obtain ⟨u, rfl⟩ : ∃ u, x = (1 / 3) + u := ⟨x - (1 / 3), by ring⟩
  have hu : 0 ≤ u := by linarith only [h0]
  have hu1 : u ≤ 1 / 10 := by linarith only [h1]
  have steps (n : ℕ) := nlt_pw hu hu1 n
  norm_num [nltCu1]
  nlinarith only [steps 1, steps 2, steps 3, steps 4, steps 5, steps 6, steps 7,
    hu, hu1, sq_nonneg u, pow_nonneg hu 3, pow_nonneg hu 4,
    pow_nonneg hu 5, pow_nonneg hu 6, pow_nonneg hu 7, pow_nonneg hu 8]

private theorem sixth_lower {x : ℝ} (h0 : 17 / 60 ≤ x) (h1 : x ≤ 3 / 7) :
    -6100000 * x ≤ nltCu6 x := by
  let p : Polynomial ℝ := nltCu6 Polynomial.X + 6100000 * Polynomial.X
  have hconc : ∀ s, 17 / 60 ≤ s → s ≤ 3 / 7 → p.derivative.derivative.eval s ≤ 0 := by
    intro s hs _
    have hs0 : 0 ≤ s := by linarith only [hs]
    norm_num [p, nltCu6, Polynomial.derivative_mul, Polynomial.derivative_pow]
    exact le_trans (by norm_num : (-8365320 : ℝ) ≤ 0) (by positivity)
  have floor := UnitShape.polynomial_floor (p := p) (m := 0) h0 h1 hconc
    (by norm_num [p, nltCu6]) (by norm_num [p, nltCu6])
  have he : p.eval x = nltCu6 x + 6100000 * x := by simp [p, nltCu6]
  rw [he] at floor
  linarith only [floor]

/-- Positivity at the one-quarter scale, using the exact duration bound. -/
theorem nlt_face_unit {x y : ℝ} (h1 : 17 / 60 ≤ x) (h2 : x ≤ 3 / 7) (hy0 : 0 ≤ y)
    (hy : y * (1 + 4 * x) ≤ 1 - 2 * x) :
    0 < nltSt0 (3 / 8) x + nltSt1 (3 / 8) x * y + nltSt2 (3 / 8) x * y ^ 2
      + nltSt3 (3 / 8) x * y ^ 3 + nltSt4 (3 / 8) x * y ^ 4 + nltSt5 (3 / 8) x * y ^ 5
      + nltSt6 (3 / 8) x * y ^ 6 := by
  have u0 := constant_pos h1 h2
  have u4 := fourth_nonneg h1 h2
  have u5 := fifth_lower h1 h2
  have u6 := sixth_lower h1 h2
  have uB := cubic_nonneg h1 h2
  have uE := cubic_link h1 h2
  have uL := linear_link h1 h2
  have uR := r0_floor h1 h2
  let b := (1 - 2 * x) / (1 + 4 * x)
  have hx0 : 0 < x := by linarith only [h1]
  have hW : 0 < 1 + 4 * x := by linarith only [h1]
  have hbpos : 0 < b := by
    apply div_pos _ hW
    linarith only [h2]
  have hyb : y ≤ b := (le_div_iff₀ hW).mpr hy
  have hb13 : b ≤ 13 / 64 := by
    apply (div_le_iff₀ hW).mpr
    linarith only [h1]
  have hy13 := hyb.trans hb13
  have e : nltCu0 x + nltCu1 x * y + nltCu2 x * y ^ 2 + nltCu3 x * y ^ 3 + nltCu4 x * y ^ 4
      + nltCu5 x * y ^ 5 + nltCu6 x * y ^ 6 = 1536 * (nltSt0 (3 / 8) x + nltSt1 (3 / 8) x * y
      + nltSt2 (3 / 8) x * y ^ 2 + nltSt3 (3 / 8) x * y ^ 3 + nltSt4 (3 / 8) x * y ^ 4
      + nltSt5 (3 / 8) x * y ^ 5 + nltSt6 (3 / 8) x * y ^ 6) := by
    rw [← nlt_Cu0_eq, ← nlt_Cu1_eq, ← nlt_Cu2_eq, ← nlt_Cu3_eq, ← nlt_Cu4_eq, ← nlt_Cu5_eq,
      ← nlt_Cu6_eq]
    ring
  suffices key : 0 < nltCu0 x + nltCu1 x * y + nltCu2 x * y ^ 2 + nltCu3 x * y ^ 3
      + nltCu4 x * y ^ 4 + nltCu5 x * y ^ 5 + nltCu6 x * y ^ 6 by rw [e] at key; linarith only [key]
  have f4 := mul_nonneg u4 (pow_nonneg hy0 4)
  have f5 := mul_le_mul_of_nonneg_right u5 (pow_nonneg hy0 5)
  have f6 := mul_le_mul_of_nonneg_right u6 (pow_nonneg hy0 6)
  have g1 : 144000000 * y ^ 2 + 6100000 * y ^ 3 ≤ 6000000 := by
    have a2 := pow_le_pow_left₀ hy0 hy13 2
    have a3 := pow_le_pow_left₀ hy0 hy13 3
    norm_num at a2 a3
    linarith only [a2, a3]
  have g2 := mul_le_mul_of_nonneg_left g1 (show 0 ≤ x * y ^ 3 by positivity)
  have hP : nltCu0 x + nltCu1 x * y + nltCu2 x * y ^ 2 + (nltCu3 x - 6000000 * x) * y ^ 3 ≤
      nltCu0 x + nltCu1 x * y + nltCu2 x * y ^ 2 + nltCu3 x * y ^ 3 + nltCu4 x * y ^ 4
        + nltCu5 x * y ^ 5 + nltCu6 x * y ^ 6 := by
    nlinarith only [f4, f5, f6, g2]
  by_cases hc : 0 ≤ nltCu2 x
  · have hlin : 0 ≤ nltCu1 x := by linarith only [uL, hc]
    have p1 := mul_nonneg hlin hy0
    have p2 := mul_nonneg hc (sq_nonneg y)
    have p3 := mul_nonneg uB (pow_nonneg hy0 3)
    linarith only [hP, u0, p1, p2, p3]
  have hsq : 0 ≤ (1 - 6 * y) ^ 2 * (1 + 12 * y) := by positivity
  have p2 := mul_nonneg (show 0 ≤ -nltCu2 x by linarith only [hc]) hsq
  have p3 := mul_le_mul_of_nonneg_right uE (pow_nonneg hy0 3)
  have cubic : nltCu2 x / 108 - 250000 * y ^ 3 ≤
      nltCu2 x * y ^ 2 + (nltCu3 x - 6000000 * x) * y ^ 3 := by
    nlinarith only [p2, p3]
  have hend : 3000 ≤ nltCu0 x + nltCu2 x / 108 + b * nltCu1 x := by
    by_cases hx : x ≤ 1 / 3
    · have hleft := left_floor h1 hx
      have he : (1 + 4 * x) * (nltCu0 x + nltCu2 x / 108 + b * nltCu1 x) =
          (1 + 4 * x) * (nltCu0 x + nltCu2 x / 108) + (1 - 2 * x) * nltCu1 x := by
        dsimp [b]
        field_simp
      have hp : 0 < (1 + 4 * x) * (nltCu0 x + nltCu2 x / 108 + b * nltCu1 x - 3000) := by
        nlinarith only [hleft, he, hx]
      have hpos := pos_of_mul_pos_right hp hW.le
      linarith only [hpos]
    · have hlin := linear_lower (le_of_not_ge hx) h2
      have hb7 : b ≤ 1 / 7 := by
        apply (div_le_iff₀ hW).mpr
        linarith only [hx]
      have hp := mul_le_mul_of_nonneg_right hlin hbpos.le
      linarith only [hp, hb7, uR]
  have left : 0 ≤ (b - y) * (nltCu0 x + nltCu2 x / 108 - 3000) := by
    exact mul_nonneg (sub_nonneg.mpr hyb) (by linarith only [uR])
  have right := mul_nonneg hy0 (show 0 ≤ nltCu0 x + nltCu2 x / 108 + b * nltCu1 x - 3000 by
    linarith only [hend])
  have hline : 3000 ≤ nltCu0 x + nltCu2 x / 108 + nltCu1 x * y := by
    by_contra hneg
    have hp := mul_neg_of_pos_of_neg hbpos (show nltCu0 x + nltCu2 x / 108 + nltCu1 x * y - 3000 < 0 by
      linarith only [hneg])
    nlinarith only [left, right, hp]
  have hsmall : 250000 * y ^ 3 < 2500 := by
    have hy3 := pow_le_pow_left₀ hy0 hy13 3
    norm_num at hy3
    linarith only [hy3]
  linarith only [hP, cubic, hline, hsmall]

end SmoothedOctagon
