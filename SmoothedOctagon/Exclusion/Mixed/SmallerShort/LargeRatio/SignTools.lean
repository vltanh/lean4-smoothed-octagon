module

public import SmoothedOctagon.Exclusion.Mixed.PolyDeriv
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Ring

/-!
# Smaller-short window, large ratio: elementary sign tools

Tools for the sign arguments of the large-ratio bound: the central-face tests at `τ = 2`, `τ = T` and
`τ = 8T/9`, the lower face `β = x`, and the outer large-ratio tests.

* **Beta convexity** (`lgr_chord`): a function `k y² + l y + m + r/(y - p) + s/(y - q)` with
  `k ≥ 0`, `s ≥ 0` and `k(b₀ - p)³ + r ≥ 0` lies below its chord on `[b₀, b₁]` (both poles to the
  left); this is a residue argument, and the convexity reduces `β` to its two ends.
* **Coefficient lists** (polynomials written in Horner form, `polyHorner`): sum `lgrAdd`, scalar
  multiple `lgrSmul`, Taylor shift `lgrShift` (`polyHorner (lgrShift m p) t = polyHorner p (m + t)`),
  derivative `lgrD` (`= polyHornerD`), and their bivariate versions (`lgrH2`: an outer polynomial in
  `X` whose coefficients are polynomials in `A`; `lgrAdd2`, `lgrD2`, the restriction `lgrEval` to a
  fixed `X`, and the restriction `lgrSlant` to a line `X = αA + β`).
* **The elementary coefficient bound**: on `0 ≤ A ≤ H`, a polynomial is at least
  its constant term plus its negative terms evaluated at `H` (`lgrLow`, `lgr_low_le`); the bivariate
  version bounds every coefficient of `X` first (`lgrLow2`, `lgr_low2_le`). With the Taylor shift it
  gives the sign of a one-variable polynomial on any interval (`lgr_pos_of_shift`) and on a fixed
  cover of an interval (`lgrCov`, `lgr_cov_pos`); for an unbounded outer variable, a positive
  constant and nonnegative higher bounded coefficients suffice (`lgrPosL`, `lgr_pos_unb`).
* **Products** (`lgrMul`, `lgrMul2`, `lgrSmul2`): the expanded numerators are computed inside Lean
  from their factored formulas, never printed.
* **Coordinate changes** of bivariate lists: outer Taylor shift `lgrShift2`, inner shift
  (`lgr_H2_shift_inner`), the shear `X = Y + αA` (`lgrShear`), and the inner derivative
  (`lgr_hasDerivAt2_inner`); monotonicity in either variable (`lgr_mono_X`, `lgr_mono_A`).
* **Convexity in `x`** (`lgr_conv_pos`): a positive second `X`-derivative on a rectangle, with a
  positive value and a nonnegative first derivative on its left edge, gives positivity on the whole
  rectangle.
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
noncomputable def lgrAdd : List ℝ → List ℝ → List ℝ
  | [], q => q
  | c :: p, [] => c :: p
  | c :: p, d :: q => (c + d) :: lgrAdd p q

theorem lgr_horner_add (p q : List ℝ) (s : ℝ) :
    polyHorner (lgrAdd p q) s = polyHorner p s + polyHorner q s := by
  induction p generalizing q with
  | nil => simp [lgrAdd, polyHorner]
  | cons c p ih =>
    cases q with
    | nil => simp [lgrAdd, polyHorner]
    | cons d q => simp only [lgrAdd, polyHorner, ih]; ring

/-- Scalar multiple of a coefficient list. -/
noncomputable def lgrSmul (m : ℝ) : List ℝ → List ℝ
  | [] => []
  | c :: p => (m * c) :: lgrSmul m p

theorem lgr_horner_smul (m : ℝ) (p : List ℝ) (s : ℝ) :
    polyHorner (lgrSmul m p) s = m * polyHorner p s := by
  induction p with
  | nil => simp [lgrSmul, polyHorner]
  | cons c p ih => simp only [lgrSmul, polyHorner, ih]; ring

/-- **Taylor shift**: `polyHorner (lgrShift m p) t = polyHorner p (m + t)`. -/
noncomputable def lgrShift (m : ℝ) : List ℝ → List ℝ
  | [] => []
  | c :: p => lgrAdd [c] (lgrAdd (lgrSmul m (lgrShift m p)) (0 :: lgrShift m p))

theorem lgr_horner_shift (m : ℝ) (p : List ℝ) (t : ℝ) :
    polyHorner (lgrShift m p) t = polyHorner p (m + t) := by
  induction p with
  | nil => simp [lgrShift, polyHorner]
  | cons c p ih =>
    simp only [lgrShift, lgr_horner_add, lgr_horner_smul, polyHorner, ih]; ring

/-- The derivative coefficient list: `polyHorner (lgrD p) = polyHornerD p`. -/
noncomputable def lgrD : List ℝ → List ℝ
  | [] => []
  | _ :: p => lgrAdd p (0 :: lgrD p)

theorem lgr_horner_D (p : List ℝ) (s : ℝ) : polyHorner (lgrD p) s = polyHornerD p s := by
  induction p with
  | nil => simp [lgrD, polyHorner, polyHornerD]
  | cons c p ih => simp only [lgrD, lgr_horner_add, polyHorner, polyHornerD, ih]; ring

theorem lgr_hasDerivAt (p : List ℝ) (s : ℝ) :
    HasDerivAt (polyHorner p) (polyHorner (lgrD p) s) s := by
  rw [lgr_horner_D]; exact poly_hasDerivAt_horner p s

/-! ### The elementary coefficient bound -/

/-- The negative part of a coefficient list evaluated at `H`: `∑ min(cₖ, 0) Hᵏ`. -/
noncomputable def lgrNeg (H : ℝ) : List ℝ → ℝ
  | [] => 0
  | c :: p => min c 0 + H * lgrNeg H p

/-- **The coefficient bound** `c₀ + ∑_{k ≥ 1} min(cₖ, 0) Hᵏ`. -/
noncomputable def lgrLow (H : ℝ) : List ℝ → ℝ
  | [] => 0
  | c :: p => c + H * lgrNeg H p

theorem lgr_neg_nonpos {H : ℝ} (hH : 0 ≤ H) (p : List ℝ) : lgrNeg H p ≤ 0 := by
  induction p with
  | nil => simp [lgrNeg]
  | cons c p ih =>
    simp only [lgrNeg]
    have : H * lgrNeg H p ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hH ih
    have : min c 0 ≤ 0 := min_le_right _ _
    linarith

/-- Coefficientwise domination: `e ≤ d` term by term (`d` may be longer). -/
def lgrDom : List ℝ → List ℝ → Prop
  | [], _ => True
  | _ :: _, [] => False
  | c :: e, d :: q => c ≤ d ∧ lgrDom e q

theorem lgr_neg_le_dom {H A : ℝ} (hA : 0 ≤ A) (hAH : A ≤ H) :
    ∀ (e d : List ℝ), lgrDom e d → (∀ x ∈ d.drop e.length, 0 ≤ x) →
      lgrNeg H e ≤ polyHorner d A := by
  have hH : 0 ≤ H := hA.trans hAH
  intro e
  induction e with
  | nil =>
    intro d _ hd
    simp only [lgrNeg, List.length_nil, List.drop_zero] at hd ⊢
    clear hAH
    induction d with
    | nil => simp [polyHorner]
    | cons c d ih =>
      simp only [polyHorner]
      have hc : 0 ≤ c := hd c (by simp)
      have hd' : ∀ x ∈ d, 0 ≤ x := fun x hx => hd x (List.mem_cons_of_mem c hx)
      have := ih trivial hd'
      positivity
  | cons c e ih =>
    intro d hdom hd
    cases d with
    | nil => exact absurd hdom (by simp [lgrDom])
    | cons d0 d =>
      obtain ⟨hc, hdom'⟩ := hdom
      have ih' := ih d hdom' (by simpa using hd)
      simp only [lgrNeg, polyHorner]
      have hn := lgr_neg_nonpos hH e
      have h1 : min c 0 ≤ d0 := (min_le_left _ _).trans hc
      have h2 : H * lgrNeg H e ≤ A * lgrNeg H e := mul_le_mul_of_nonpos_right hAH hn
      have h3 : A * lgrNeg H e ≤ A * polyHorner d A := mul_le_mul_of_nonneg_left ih' hA
      linarith

theorem lgr_low_le_dom {H A : ℝ} (hA : 0 ≤ A) (hAH : A ≤ H) (e d : List ℝ) (hdom : lgrDom e d)
    (hd : ∀ x ∈ d.drop e.length, 0 ≤ x) : lgrLow H e ≤ polyHorner d A := by
  have hH : 0 ≤ H := hA.trans hAH
  cases e with
  | nil =>
    simp only [lgrLow, List.length_nil, List.drop_zero] at hd ⊢
    have := lgr_neg_le_dom hA hAH [] d trivial (by simpa using hd)
    simpa [lgrNeg] using this
  | cons c e =>
    cases d with
    | nil => exact absurd hdom (by simp [lgrDom])
    | cons d0 d =>
      obtain ⟨hc, hdom'⟩ := hdom
      have ih' := lgr_neg_le_dom hA hAH e d hdom' (by simpa using hd)
      simp only [lgrLow, polyHorner]
      have hn := lgr_neg_nonpos hH e
      have h2 : H * lgrNeg H e ≤ A * lgrNeg H e := mul_le_mul_of_nonpos_right hAH hn
      have h3 : A * lgrNeg H e ≤ A * polyHorner d A := mul_le_mul_of_nonneg_left ih' hA
      linarith

theorem lgr_dom_refl : ∀ p : List ℝ, lgrDom p p
  | [] => trivial
  | _ :: p => ⟨le_rfl, lgr_dom_refl p⟩

/-- **The coefficient bound** on `0 ≤ A ≤ H`. -/
theorem lgr_low_le {H A : ℝ} (hA : 0 ≤ A) (hAH : A ≤ H) (p : List ℝ) :
    lgrLow H p ≤ polyHorner p A :=
  lgr_low_le_dom hA hAH p p (lgr_dom_refl p) (by simp)

/-- **Sign on an interval** from the coefficient bound after a Taylor shift to its left end. -/
theorem lgr_pos_of_shift {p q A : ℝ} (cs : List ℝ) (h : 0 < lgrLow (q - p) (lgrShift p cs))
    (hpA : p ≤ A) (hAq : A ≤ q) : 0 < polyHorner cs A := by
  have e : polyHorner cs A = polyHorner (lgrShift p cs) (A - p) := by
    rw [lgr_horner_shift]; ring_nf
  rw [e]
  exact h.trans_le (lgr_low_le (by linarith) (by linarith) _)


/-- **Sign on an interval from a cover**: `lgrCov cs e [p₀, p₁, …, pₙ]` asks the coefficient bound
after the Taylor shift on each piece `[pᵢ, pᵢ₊₁]` (with `pₙ₊₁ = e`). -/
def lgrCov (cs : List ℝ) (e : ℝ) : List ℝ → Prop
  | [] => True
  | [p] => 0 < lgrLow (e - p) (lgrShift p cs)
  | p :: q :: r => 0 < lgrLow (q - p) (lgrShift p cs) ∧ lgrCov cs e (q :: r)

theorem lgr_cov_pos (cs : List ℝ) (e : ℝ) :
    ∀ (p : ℝ) (r : List ℝ), lgrCov cs e (p :: r) → ∀ A, p ≤ A → A ≤ e → 0 < polyHorner cs A := by
  intro p r
  induction r generalizing p with
  | nil => intro h A h1 h2; exact lgr_pos_of_shift cs h h1 h2
  | cons q r ih =>
    intro h A h1 h2
    obtain ⟨hq, hr⟩ := h
    rcases le_total A q with hAq | hAq
    · exact lgr_pos_of_shift cs hq h1 hAq
    · exact ih q hr A hAq h2

/-- Positive constant term and nonnegative other coefficients. -/
def lgrPosL : List ℝ → Prop
  | [] => False
  | c :: p => 0 < c ∧ ∀ d ∈ p, 0 ≤ d

theorem lgr_nn_horner {X : ℝ} (hX : 0 ≤ X) : ∀ p : List ℝ, (∀ d ∈ p, 0 ≤ d) → 0 ≤ polyHorner p X
  | [], _ => by simp [polyHorner]
  | c :: p, h => by
    simp only [polyHorner]
    have hc : 0 ≤ c := h c (by simp)
    have := lgr_nn_horner hX p (fun d hd => h d (List.mem_cons_of_mem c hd))
    positivity

theorem lgr_posL_horner {X : ℝ} (hX : 0 ≤ X) (p : List ℝ) (h : lgrPosL p) : 0 < polyHorner p X := by
  cases p with
  | nil => exact absurd h (by simp [lgrPosL])
  | cons c p =>
    obtain ⟨hc, hp⟩ := h
    simp only [polyHorner]
    have := lgr_nn_horner hX p hp
    positivity

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

theorem lgr_hasDerivAt2 (P : List (List ℝ)) (A X : ℝ) :
    HasDerivAt (fun X => lgrH2 P X A) (lgrH2 (lgrD2 P) X A) X := by
  rw [lgr_H2_D]; exact poly_hasDerivAt_horner _ X

/-- The restriction of a bivariate list to `X = X₀`, as a polynomial in `A`. -/
noncomputable def lgrEval (X₀ : ℝ) : List (List ℝ) → List ℝ
  | [] => []
  | l :: P => lgrAdd l (lgrSmul X₀ (lgrEval X₀ P))

theorem lgr_horner_eval (X₀ : ℝ) (P : List (List ℝ)) (A : ℝ) :
    polyHorner (lgrEval X₀ P) A = lgrH2 P X₀ A := by
  unfold lgrH2
  induction P with
  | nil => simp [lgrEval, polyHorner]
  | cons l P ih => simp only [lgrEval, lgr_horner_add, lgr_horner_smul, List.map, polyHorner, ih]

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

/-- **The bivariate coefficient bound**: every coefficient of `X` is bounded on `0 ≤ A ≤ H_A` by
`lgrLow`, then the resulting polynomial in `X` on `0 ≤ X ≤ H_X`. -/
noncomputable def lgrLow2 (HA HX : ℝ) (P : List (List ℝ)) : ℝ :=
  lgrLow HX (P.map (lgrLow HA))

theorem lgr_dom_map {HA A : ℝ} (hA : 0 ≤ A) (hAH : A ≤ HA) (P : List (List ℝ)) :
    lgrDom (P.map (lgrLow HA)) (P.map (fun l => polyHorner l A)) := by
  induction P with
  | nil => trivial
  | cons l P ih => exact ⟨lgr_low_le hA hAH l, ih⟩

theorem lgr_low2_le {HA HX A X : ℝ} (hA : 0 ≤ A) (hAH : A ≤ HA) (hX : 0 ≤ X) (hXH : X ≤ HX)
    (P : List (List ℝ)) : lgrLow2 HA HX P ≤ lgrH2 P X A :=
  lgr_low_le_dom hX hXH _ _ (lgr_dom_map hA hAH P) (by
    rw [List.drop_eq_nil_of_le (by simp)]; simp)


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

/-- Outer Taylor shift of a bivariate list: `lgrH2 (lgrShift2 m P) X A = lgrH2 P (m + X) A`. -/
noncomputable def lgrShift2 (m : ℝ) : List (List ℝ) → List (List ℝ)
  | [] => []
  | l :: P => lgrAdd2 [l] (lgrAdd2 ((lgrShift2 m P).map (lgrSmul m)) ([] :: lgrShift2 m P))

theorem lgr_H2_shift2 (m : ℝ) (P : List (List ℝ)) (X A : ℝ) :
    lgrH2 (lgrShift2 m P) X A = lgrH2 P (m + X) A := by
  induction P with
  | nil => simp [lgrShift2, lgrH2, polyHorner]
  | cons l P ih =>
    simp only [lgrShift2, lgr_H2_add2, lgr_H2_single, lgr_H2_cons_nil,
      lgr_H2_map (fun q => lgr_horner_smul m q A), ih]
    simp only [lgrH2, List.map, polyHorner]; ring

/-- The shear `X = Y + αA` of a bivariate list: `lgrH2 (lgrShear α P) Y A = lgrH2 P (Y + αA) A`. -/
noncomputable def lgrShear (α : ℝ) : List (List ℝ) → List (List ℝ)
  | [] => []
  | l :: P => lgrAdd2 [l] (lgrAdd2 ([] :: lgrShear α P) ((lgrShear α P).map (fun q => 0 :: lgrSmul α q)))

theorem lgr_H2_shear (α : ℝ) (P : List (List ℝ)) (Y A : ℝ) :
    lgrH2 (lgrShear α P) Y A = lgrH2 P (Y + α * A) A := by
  induction P with
  | nil => simp [lgrShear, lgrH2, polyHorner]
  | cons l P ih =>
    have hf : ∀ q, polyHorner (0 :: lgrSmul α q) A = (α * A) * polyHorner q A := by
      intro q; simp only [polyHorner, lgr_horner_smul]; ring
    simp only [lgrShear, lgr_H2_add2, lgr_H2_single, lgr_H2_cons_nil, lgr_H2_map hf, ih]
    simp only [lgrH2, List.map, polyHorner]; ring

/-- Inner Taylor shift: `lgrH2 (P.map (lgrShift m)) X A = lgrH2 P X (m + A)`. -/
theorem lgr_H2_shift_inner (m : ℝ) (P : List (List ℝ)) (X A : ℝ) :
    lgrH2 (P.map (lgrShift m)) X A = lgrH2 P X (m + A) := by
  unfold lgrH2
  induction P with
  | nil => simp [polyHorner]
  | cons l P ih => simp only [List.map, polyHorner, lgr_horner_shift, ih]

/-- The inner derivative: `∂_A lgrH2 P X A = lgrH2 (P.map lgrD) X A`. -/
theorem lgr_hasDerivAt2_inner (P : List (List ℝ)) (X A : ℝ) :
    HasDerivAt (fun A => lgrH2 P X A) (lgrH2 (P.map lgrD) X A) A := by
  unfold lgrH2
  induction P with
  | nil => simpa [polyHorner] using hasDerivAt_const A (0 : ℝ)
  | cons l P ih =>
    simp only [List.map, polyHorner]
    exact (lgr_hasDerivAt l A).add (ih.const_mul X)

/-- **The unbounded bivariate rule**: coefficients of `X` bounded on `0 ≤ A ≤ H_A`, then a positive
constant and nonnegative higher coefficients give positivity for every `X ≥ 0`. -/
theorem lgr_pos_unb {HA A X : ℝ} (hA : 0 ≤ A) (hAH : A ≤ HA) (hX : 0 ≤ X) (P : List (List ℝ))
    (h : lgrPosL (P.map (lgrLow HA))) : 0 < lgrH2 P X A := by
  unfold lgrH2
  induction P generalizing X with
  | nil => exact absurd h (by simp [lgrPosL])
  | cons l P _ =>
    obtain ⟨hc, hp⟩ := h
    simp only [List.map, polyHorner]
    have h0 := (lgr_low_le hA hAH l)
    have hnn : 0 ≤ polyHorner (P.map (fun l => polyHorner l A)) X := by
      have := lgr_low_le_dom hX le_rfl (P.map (lgrLow HA)) (P.map (fun l => polyHorner l A))
        (lgr_dom_map hA hAH P) (by rw [List.drop_eq_nil_of_le (by simp)]; simp)
      have h2 : 0 ≤ lgrLow X (P.map (lgrLow HA)) := by
        cases hP : P.map (lgrLow HA) with
        | nil => simp [lgrLow]
        | cons d q =>
          rw [hP] at hp
          simp only [lgrLow]
          have hd : 0 ≤ d := hp d (by simp)
          have : lgrNeg X q = 0 := by
            have hq : ∀ e ∈ q, 0 ≤ e := fun e he => hp e (List.mem_cons_of_mem d he)
            clear hP hp hd this
            induction q with
            | nil => simp [lgrNeg]
            | cons e q ih =>
              simp only [lgrNeg]
              rw [min_eq_right (hq e (by simp)), ih (fun f hf => hq f (List.mem_cons_of_mem e hf))]
              ring
          rw [this]; simpa using hd
      linarith
    have := mul_nonneg hX hnn
    linarith

/-- Monotonicity in `X` from a nonnegative `X`-derivative. -/
theorem lgr_mono_X {P : List (List ℝ)} {A X₁ X₂ : ℝ}
    (hd : ∀ X, X₁ ≤ X → X ≤ X₂ → 0 ≤ lgrH2 (lgrD2 P) X A) (h12 : X₁ ≤ X₂) :
    lgrH2 P X₁ A ≤ lgrH2 P X₂ A :=
  poly_mono (f := fun X => lgrH2 P X A) (fun s => lgr_hasDerivAt2 _ A s)
    (fun s h1 h2 => hd s h1 h2) le_rfl h12 le_rfl

/-- Monotonicity in `A` from a nonnegative `A`-derivative. -/
theorem lgr_mono_A {P : List (List ℝ)} {X A₁ A₂ : ℝ}
    (hd : ∀ A, A₁ ≤ A → A ≤ A₂ → 0 ≤ lgrH2 (P.map lgrD) X A) (h12 : A₁ ≤ A₂) :
    lgrH2 P X A₁ ≤ lgrH2 P X A₂ :=
  poly_mono (f := fun A => lgrH2 P X A) (fun s => lgr_hasDerivAt2_inner _ X s)
    (fun s h1 h2 => hd s h1 h2) le_rfl h12 le_rfl

/-! ### Products of coefficient lists -/

/-- Product of coefficient lists. -/
noncomputable def lgrMul : List ℝ → List ℝ → List ℝ
  | [], _ => []
  | c :: p, q => lgrAdd (lgrSmul c q) (0 :: lgrMul p q)

theorem lgr_horner_mul (p q : List ℝ) (s : ℝ) :
    polyHorner (lgrMul p q) s = polyHorner p s * polyHorner q s := by
  induction p with
  | nil => simp [lgrMul, polyHorner]
  | cons c p ih => simp only [lgrMul, lgr_horner_add, lgr_horner_smul, polyHorner, ih]; ring

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

/-! ### Convexity in `x` on a rectangle -/

/-- **Rectangle convexity**: if on `0 ≤ X ≤ W` the second `X`-derivative is nonnegative, the first
derivative is nonnegative at `X = 0` and the value is positive at `X = 0`, then the value is
positive on `0 ≤ X ≤ W` (at the fixed `A`). -/
theorem lgr_conv_pos {P : List (List ℝ)} {A W X : ℝ}
    (h2 : ∀ X, 0 ≤ X → X ≤ W → 0 ≤ lgrH2 (lgrD2 (lgrD2 P)) X A)
    (h1 : 0 ≤ lgrH2 (lgrD2 P) 0 A) (h0 : 0 < lgrH2 P 0 A) (hX : 0 ≤ X) (hXW : X ≤ W) :
    0 < lgrH2 P X A := by
  have hd1 : ∀ X, 0 ≤ X → X ≤ W → 0 ≤ lgrH2 (lgrD2 P) X A := by
    intro X hX hXW
    have := poly_mono (f := fun X => lgrH2 (lgrD2 P) X A) (fun s => lgr_hasDerivAt2 _ A s)
      (fun s h1 h2' => h2 s h1 h2') le_rfl hX hXW
    linarith
  have := poly_mono (f := fun X => lgrH2 P X A) (fun s => lgr_hasDerivAt2 _ A s)
    (fun s h1 h2' => hd1 s h1 h2') le_rfl hX hXW
  linarith

end SmoothedOctagon
