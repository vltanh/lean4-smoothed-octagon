module

public import SmoothedOctagon.Exclusion.Mixed.Horner
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Ring

/-!
# Smaller-short window, large ratio: elementary sign tools

The chord bound reduces each rational beta test to its endpoint values.
The coefficient-list operations represent the cleared polynomial numerators
and their cubic control values: addition, scaling, multiplication,
translation, differentiation and restriction to a line.
-/

@[expose] public section

namespace SmoothedOctagon

/-! ### Beta convexity -/

/-- **The chord bound** for `f(y) = k y² + l y + m + r/(y - p) + s/(y - q)` on `[b₀, b₁]`, with
both poles left of `b₀`, `k ≥ 0`, `s ≥ 0` and `k(b₀ - p)³ + r ≥ 0` (the residue at `p` may be
negative): `f(y) ≤ max (f b₀) (f b₁)`. -/
theorem lgr_chord {k l m r s p q b₀ b₁ y : ℝ} (hp : p < b₀) (hq : q < b₀) (h0 : b₀ ≤ y)
    (h1 : y ≤ b₁) (hk : 0 ≤ k) (hr : 0 ≤ k * (b₀ - p) ^ 3 + r) (hs : 0 ≤ s) :
    k * y ^ 2 + l * y + m + r / (y - p) + s / (y - q) ≤
      max (k * b₀ ^ 2 + l * b₀ + m + r / (b₀ - p) + s / (b₀ - q))
        (k * b₁ ^ 2 + l * b₁ + m + r / (b₁ - p) + s / (b₁ - q)) := by
  rcases eq_or_lt_of_le (h0.trans h1) with he | hlt
  · have hy0 : y = b₀ := le_antisymm (he ▸ h1) h0
    subst hy0; exact le_max_left _ _
  have hp0 : 0 < b₀ - p := by linarith
  have hpy : 0 < y - p := by linarith
  have hp1 : 0 < b₁ - p := by linarith
  have hq0 : 0 < b₀ - q := by linarith
  have hqy : 0 < y - q := by linarith
  have hq1 : 0 < b₁ - q := by linarith
  have hw : 0 < b₁ - b₀ := by linarith
  -- the divided difference
  have hdd : 0 ≤ k + r / ((b₀ - p) * (y - p) * (b₁ - p)) + s / ((b₀ - q) * (y - q) * (b₁ - q)) := by
    have hs' : 0 ≤ s / ((b₀ - q) * (y - q) * (b₁ - q)) := by positivity
    have hprod : (b₀ - p) ^ 3 ≤ (b₀ - p) * (y - p) * (b₁ - p) := by
      have h1' : (b₀ - p) * (b₀ - p) ≤ (b₀ - p) * (y - p) :=
        mul_le_mul_of_nonneg_left (by linarith) hp0.le
      have h2' : (b₀ - p) * (y - p) * (b₀ - p) ≤ (b₀ - p) * (y - p) * (b₁ - p) :=
        mul_le_mul_of_nonneg_left (by linarith) (by positivity)
      nlinarith
    rcases le_or_gt 0 r with hr0 | hr0
    · have : 0 ≤ r / ((b₀ - p) * (y - p) * (b₁ - p)) := by positivity
      linarith
    · have hpos : 0 < (b₀ - p) * (y - p) * (b₁ - p) := by positivity
      have key : r / (b₀ - p) ^ 3 ≤ r / ((b₀ - p) * (y - p) * (b₁ - p)) := by
        rw [div_le_div_iff₀ (by positivity) hpos]
        nlinarith
      have hk' : 0 ≤ k + r / (b₀ - p) ^ 3 := by
        have : k + r / (b₀ - p) ^ 3 = (k * (b₀ - p) ^ 3 + r) / (b₀ - p) ^ 3 := by
          field_simp
        rw [this]; positivity
      linarith
  have key : (b₁ - y) * (k * b₀ ^ 2 + l * b₀ + m + r / (b₀ - p) + s / (b₀ - q)) +
      (y - b₀) * (k * b₁ ^ 2 + l * b₁ + m + r / (b₁ - p) + s / (b₁ - q)) -
      (b₁ - b₀) * (k * y ^ 2 + l * y + m + r / (y - p) + s / (y - q)) =
      (b₁ - y) * (y - b₀) * (b₁ - b₀) *
        (k + r / ((b₀ - p) * (y - p) * (b₁ - p)) + s / ((b₀ - q) * (y - q) * (b₁ - q))) := by
    field_simp
    ring
  have hnn : 0 ≤ (b₁ - y) * (y - b₀) * (b₁ - b₀) *
      (k + r / ((b₀ - p) * (y - p) * (b₁ - p)) + s / ((b₀ - q) * (y - q) * (b₁ - q))) :=
    mul_nonneg (mul_nonneg (mul_nonneg (by linarith) (by linarith)) hw.le) hdd
  set F0 := k * b₀ ^ 2 + l * b₀ + m + r / (b₀ - p) + s / (b₀ - q)
  set F1 := k * b₁ ^ 2 + l * b₁ + m + r / (b₁ - p) + s / (b₁ - q)
  set Fy := k * y ^ 2 + l * y + m + r / (y - p) + s / (y - q)
  have hM0 : F0 ≤ max F0 F1 := le_max_left _ _
  have hM1 : F1 ≤ max F0 F1 := le_max_right _ _
  have h2 : (b₁ - b₀) * Fy ≤ (b₁ - b₀) * max F0 F1 := by
    have e1 : (b₁ - y) * F0 ≤ (b₁ - y) * max F0 F1 := mul_le_mul_of_nonneg_left hM0 (by linarith)
    have e2 : (y - b₀) * F1 ≤ (y - b₀) * max F0 F1 := mul_le_mul_of_nonneg_left hM1 (by linarith)
    nlinarith
  exact le_of_mul_le_mul_left h2 hw

/-! ### Coefficient lists -/

/-- Coefficientwise sum of two coefficient lists. -/
noncomputable abbrev lgrAdd := Horner.add

theorem lgr_horner_add (p q : List ℝ) (s : ℝ) :
    polyHorner (lgrAdd p q) s = polyHorner p s + polyHorner q s := Horner.eval_add p q s

/-- Scalar multiple of a coefficient list. -/
noncomputable abbrev lgrSmul := Horner.smul

theorem lgr_horner_smul (m : ℝ) (p : List ℝ) (s : ℝ) :
    polyHorner (lgrSmul m p) s = m * polyHorner p s := Horner.eval_smul m p s

/-- Translation of a coefficient list. -/
noncomputable abbrev lgrShift := Horner.shift

theorem lgr_horner_shift (m : ℝ) (p : List ℝ) (t : ℝ) :
    polyHorner (lgrShift m p) t = polyHorner p (m + t) := Horner.eval_shift m p t

/-! ### Bivariate coefficient lists -/

/-- An outer polynomial in `X` whose coefficients are polynomials in `A`. -/
noncomputable def lgrH2 (LL : List (List ℝ)) (X A : ℝ) : ℝ :=
  polyHorner (LL.map (fun l => polyHorner l A)) X

/-- Coefficientwise sum of two bivariate lists. -/
noncomputable def lgrAdd2 : List (List ℝ) → List (List ℝ) → List (List ℝ)
  | [], Q => Q
  | c :: P, [] => c :: P
  | c :: P, d :: Q => lgrAdd c d :: lgrAdd2 P Q

theorem lgr_map_add2 (P Q : List (List ℝ)) (A : ℝ) :
    ∀ X, polyHorner ((lgrAdd2 P Q).map (fun l => polyHorner l A)) X =
      polyHorner (P.map (fun l => polyHorner l A)) X + polyHorner (Q.map (fun l => polyHorner l A)) X := by
  induction P generalizing Q with
  | nil => intro X; simp [lgrAdd2, polyHorner]
  | cons c P ih =>
    intro X
    cases Q with
    | nil => simp [lgrAdd2, polyHorner]
    | cons d Q => simp only [lgrAdd2, List.map, polyHorner, ih, lgr_horner_add]; ring

/-- The `X`-derivative of a bivariate list. -/
noncomputable def lgrD2 : List (List ℝ) → List (List ℝ)
  | [] => []
  | _ :: P => lgrAdd2 P ([] :: lgrD2 P)

theorem lgr_H2_D (P : List (List ℝ)) (X A : ℝ) :
    lgrH2 (lgrD2 P) X A = polyHornerD (P.map (fun l => polyHorner l A)) X := by
  unfold lgrH2
  induction P generalizing X with
  | nil => simp [lgrD2, polyHorner, polyHornerD]
  | cons c P ih =>
    simp only [lgrD2, lgr_map_add2, List.map, polyHorner, polyHornerD, ih]; ring

/-- The restriction of a bivariate list to the line `X = αA + β`, as a polynomial in `A`. -/
noncomputable def lgrSlant (α β : ℝ) : List (List ℝ) → List ℝ
  | [] => []
  | l :: P => lgrAdd l (lgrAdd (lgrSmul β (lgrSlant α β P)) (0 :: lgrSmul α (lgrSlant α β P)))

theorem lgr_horner_slant (α β : ℝ) (P : List (List ℝ)) (A : ℝ) :
    polyHorner (lgrSlant α β P) A = lgrH2 P (α * A + β) A := by
  unfold lgrH2
  induction P with
  | nil => simp [lgrSlant, polyHorner]
  | cons l P ih =>
    simp only [lgrSlant, lgr_horner_add, lgr_horner_smul, List.map, polyHorner, ih]; ring

theorem lgr_H2_map {P : List (List ℝ)} {f : List ℝ → List ℝ} {c A : ℝ}
    (hf : ∀ q, polyHorner (f q) A = c * polyHorner q A) (X : ℝ) :
    lgrH2 (P.map f) X A = c * lgrH2 P X A := by
  unfold lgrH2
  induction P with
  | nil => simp [polyHorner]
  | cons l P ih => simp only [List.map, polyHorner, hf, ih]; ring

theorem lgr_H2_add2 (P Q : List (List ℝ)) (X A : ℝ) :
    lgrH2 (lgrAdd2 P Q) X A = lgrH2 P X A + lgrH2 Q X A := lgr_map_add2 P Q A X

theorem lgr_H2_cons_nil (P : List (List ℝ)) (X A : ℝ) : lgrH2 ([] :: P) X A = X * lgrH2 P X A := by
  simp [lgrH2, polyHorner]

theorem lgr_H2_single (l : List ℝ) (X A : ℝ) : lgrH2 [l] X A = polyHorner l A := by
  simp [lgrH2, polyHorner]

/-! ### Products of coefficient lists -/

/-- Product of coefficient lists. -/
noncomputable abbrev lgrMul := Horner.mul

theorem lgr_horner_mul (p q : List ℝ) (s : ℝ) :
    polyHorner (lgrMul p q) s = polyHorner p s * polyHorner q s := Horner.eval_mul p q s

/-- Scalar multiple of a bivariate list. -/
noncomputable def lgrSmul2 (m : ℝ) (P : List (List ℝ)) : List (List ℝ) := P.map (lgrSmul m)

theorem lgr_H2_smul2 (m : ℝ) (P : List (List ℝ)) (X A : ℝ) :
    lgrH2 (lgrSmul2 m P) X A = m * lgrH2 P X A :=
  lgr_H2_map (fun q => lgr_horner_smul m q A) X

/-- Product of bivariate lists. -/
noncomputable def lgrMul2 : List (List ℝ) → List (List ℝ) → List (List ℝ)
  | [], _ => []
  | l :: P, Q => lgrAdd2 (Q.map (lgrMul l)) ([] :: lgrMul2 P Q)

theorem lgr_H2_mul2 (P Q : List (List ℝ)) (X A : ℝ) :
    lgrH2 (lgrMul2 P Q) X A = lgrH2 P X A * lgrH2 Q X A := by
  induction P with
  | nil => simp [lgrMul2, lgrH2, polyHorner]
  | cons l P ih =>
    simp only [lgrMul2, lgr_H2_add2, lgr_H2_cons_nil, ih,
      lgr_H2_map (fun q => lgr_horner_mul l q A)]
    simp only [lgrH2, List.map, polyHorner]; ring

end SmoothedOctagon
