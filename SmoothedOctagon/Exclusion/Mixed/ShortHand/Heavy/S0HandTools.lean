module

public import SmoothedOctagon.Exclusion.Mixed.FwdHand.PolyDeriv
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Ring

/-!
# Hand proof of the smaller-short case, gate S0: elementary sign tools

Tools for the sign arguments of gate S0: the central-face tests at `τ = 2`, `τ = T` and
`τ = 8T/9`, the lower face `β = x`, and the outer large-ratio tests.

* **Beta convexity** (`hl0_chord`): a function `k y² + l y + m + r/(y - p) + s/(y - q)` with
  `k ≥ 0`, `s ≥ 0` and `k(b₀ - p)³ + r ≥ 0` lies below its chord on `[b₀, b₁]` (both poles to the
  left); this is a residue argument, and the convexity reduces `β` to its two ends.
* **Coefficient lists** (polynomials written in Horner form, `lrhHorner`): sum `hl0Add`, scalar
  multiple `hl0Smul`, Taylor shift `hl0Shift` (`lrhHorner (hl0Shift m p) t = lrhHorner p (m + t)`),
  derivative `hl0D` (`= lrhHornerD`), and their bivariate versions (`hl0H2`: an outer polynomial in
  `X` whose coefficients are polynomials in `A`; `hl0Add2`, `hl0D2`, the restriction `hl0Eval` to a
  fixed `X`, and the restriction `hl0Slant` to a line `X = αA + β`).
* **The elementary coefficient bound**: on `0 ≤ A ≤ H`, a polynomial is at least
  its constant term plus its negative terms evaluated at `H` (`hl0Low`, `hl0_low_le`); the bivariate
  version bounds every coefficient of `X` first (`hl0Low2`, `hl0_low2_le`). With the Taylor shift it
  gives the sign of a one-variable polynomial on any interval (`hl0_pos_of_shift`) and on a fixed
  cover of an interval (`hl0Cov`, `hl0_cov_pos`); for an unbounded outer variable, a positive
  constant and nonnegative higher bounded coefficients suffice (`hl0PosL`, `hl0_pos_unb`).
* **Products** (`hl0Mul`, `hl0Mul2`, `hl0Smul2`): the expanded numerators are computed inside Lean
  from their factored formulas, never printed.
* **Coordinate changes** of bivariate lists: outer Taylor shift `hl0Shift2`, inner shift
  (`hl0_H2_shift_inner`), the shear `X = Y + αA` (`hl0Shear`), and the inner derivative
  (`hl0_hasDerivAt2_inner`); monotonicity in either variable (`hl0_mono_X`, `hl0_mono_A`).
* **Convexity in `x`** (`hl0_conv_pos`): a positive second `X`-derivative on a rectangle, with a
  positive value and a nonnegative first derivative on its left edge, gives positivity on the whole
  rectangle.
-/

@[expose] public section

namespace SmoothedOctagon

/-! ### Beta convexity -/

/-- **The chord bound** for `f(y) = k y² + l y + m + r/(y - p) + s/(y - q)` on `[b₀, b₁]`, with
both poles left of `b₀`, `k ≥ 0`, `s ≥ 0` and `k(b₀ - p)³ + r ≥ 0` (the residue at `p` may be
negative): `f(y) ≤ max (f b₀) (f b₁)`. -/
theorem hl0_chord {k l m r s p q b₀ b₁ y : ℝ} (hp : p < b₀) (hq : q < b₀) (h0 : b₀ ≤ y)
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
noncomputable def hl0Add : List ℝ → List ℝ → List ℝ
  | [], q => q
  | c :: p, [] => c :: p
  | c :: p, d :: q => (c + d) :: hl0Add p q

theorem hl0_horner_add (p q : List ℝ) (s : ℝ) :
    lrhHorner (hl0Add p q) s = lrhHorner p s + lrhHorner q s := by
  induction p generalizing q with
  | nil => simp [hl0Add, lrhHorner]
  | cons c p ih =>
    cases q with
    | nil => simp [hl0Add, lrhHorner]
    | cons d q => simp only [hl0Add, lrhHorner, ih]; ring

/-- Scalar multiple of a coefficient list. -/
noncomputable def hl0Smul (m : ℝ) : List ℝ → List ℝ
  | [] => []
  | c :: p => (m * c) :: hl0Smul m p

theorem hl0_horner_smul (m : ℝ) (p : List ℝ) (s : ℝ) :
    lrhHorner (hl0Smul m p) s = m * lrhHorner p s := by
  induction p with
  | nil => simp [hl0Smul, lrhHorner]
  | cons c p ih => simp only [hl0Smul, lrhHorner, ih]; ring

/-- **Taylor shift**: `lrhHorner (hl0Shift m p) t = lrhHorner p (m + t)`. -/
noncomputable def hl0Shift (m : ℝ) : List ℝ → List ℝ
  | [] => []
  | c :: p => hl0Add [c] (hl0Add (hl0Smul m (hl0Shift m p)) (0 :: hl0Shift m p))

theorem hl0_horner_shift (m : ℝ) (p : List ℝ) (t : ℝ) :
    lrhHorner (hl0Shift m p) t = lrhHorner p (m + t) := by
  induction p with
  | nil => simp [hl0Shift, lrhHorner]
  | cons c p ih =>
    simp only [hl0Shift, hl0_horner_add, hl0_horner_smul, lrhHorner, ih]; ring

/-- The derivative coefficient list: `lrhHorner (hl0D p) = lrhHornerD p`. -/
noncomputable def hl0D : List ℝ → List ℝ
  | [] => []
  | _ :: p => hl0Add p (0 :: hl0D p)

theorem hl0_horner_D (p : List ℝ) (s : ℝ) : lrhHorner (hl0D p) s = lrhHornerD p s := by
  induction p with
  | nil => simp [hl0D, lrhHorner, lrhHornerD]
  | cons c p ih => simp only [hl0D, hl0_horner_add, lrhHorner, lrhHornerD, ih]; ring

theorem hl0_hasDerivAt (p : List ℝ) (s : ℝ) :
    HasDerivAt (lrhHorner p) (lrhHorner (hl0D p) s) s := by
  rw [hl0_horner_D]; exact lrh_hasDerivAt_horner p s

/-! ### The elementary coefficient bound -/

/-- The negative part of a coefficient list evaluated at `H`: `∑ min(cₖ, 0) Hᵏ`. -/
noncomputable def hl0Neg (H : ℝ) : List ℝ → ℝ
  | [] => 0
  | c :: p => min c 0 + H * hl0Neg H p

/-- **The coefficient bound** `c₀ + ∑_{k ≥ 1} min(cₖ, 0) Hᵏ`. -/
noncomputable def hl0Low (H : ℝ) : List ℝ → ℝ
  | [] => 0
  | c :: p => c + H * hl0Neg H p

theorem hl0_neg_nonpos {H : ℝ} (hH : 0 ≤ H) (p : List ℝ) : hl0Neg H p ≤ 0 := by
  induction p with
  | nil => simp [hl0Neg]
  | cons c p ih =>
    simp only [hl0Neg]
    have : H * hl0Neg H p ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hH ih
    have : min c 0 ≤ 0 := min_le_right _ _
    linarith

/-- Coefficientwise domination: `e ≤ d` term by term (`d` may be longer). -/
def hl0Dom : List ℝ → List ℝ → Prop
  | [], _ => True
  | _ :: _, [] => False
  | c :: e, d :: q => c ≤ d ∧ hl0Dom e q

theorem hl0_neg_le_dom {H A : ℝ} (hA : 0 ≤ A) (hAH : A ≤ H) :
    ∀ (e d : List ℝ), hl0Dom e d → (∀ x ∈ d.drop e.length, 0 ≤ x) →
      hl0Neg H e ≤ lrhHorner d A := by
  have hH : 0 ≤ H := hA.trans hAH
  intro e
  induction e with
  | nil =>
    intro d _ hd
    simp only [hl0Neg, List.length_nil, List.drop_zero] at hd ⊢
    clear hAH
    induction d with
    | nil => simp [lrhHorner]
    | cons c d ih =>
      simp only [lrhHorner]
      have hc : 0 ≤ c := hd c (by simp)
      have hd' : ∀ x ∈ d, 0 ≤ x := fun x hx => hd x (List.mem_cons_of_mem c hx)
      have := ih trivial hd'
      positivity
  | cons c e ih =>
    intro d hdom hd
    cases d with
    | nil => exact absurd hdom (by simp [hl0Dom])
    | cons d0 d =>
      obtain ⟨hc, hdom'⟩ := hdom
      have ih' := ih d hdom' (by simpa using hd)
      simp only [hl0Neg, lrhHorner]
      have hn := hl0_neg_nonpos hH e
      have h1 : min c 0 ≤ d0 := (min_le_left _ _).trans hc
      have h2 : H * hl0Neg H e ≤ A * hl0Neg H e := mul_le_mul_of_nonpos_right hAH hn
      have h3 : A * hl0Neg H e ≤ A * lrhHorner d A := mul_le_mul_of_nonneg_left ih' hA
      linarith

theorem hl0_low_le_dom {H A : ℝ} (hA : 0 ≤ A) (hAH : A ≤ H) (e d : List ℝ) (hdom : hl0Dom e d)
    (hd : ∀ x ∈ d.drop e.length, 0 ≤ x) : hl0Low H e ≤ lrhHorner d A := by
  have hH : 0 ≤ H := hA.trans hAH
  cases e with
  | nil =>
    simp only [hl0Low, List.length_nil, List.drop_zero] at hd ⊢
    have := hl0_neg_le_dom hA hAH [] d trivial (by simpa using hd)
    simpa [hl0Neg] using this
  | cons c e =>
    cases d with
    | nil => exact absurd hdom (by simp [hl0Dom])
    | cons d0 d =>
      obtain ⟨hc, hdom'⟩ := hdom
      have ih' := hl0_neg_le_dom hA hAH e d hdom' (by simpa using hd)
      simp only [hl0Low, lrhHorner]
      have hn := hl0_neg_nonpos hH e
      have h2 : H * hl0Neg H e ≤ A * hl0Neg H e := mul_le_mul_of_nonpos_right hAH hn
      have h3 : A * hl0Neg H e ≤ A * lrhHorner d A := mul_le_mul_of_nonneg_left ih' hA
      linarith

theorem hl0_dom_refl : ∀ p : List ℝ, hl0Dom p p
  | [] => trivial
  | _ :: p => ⟨le_rfl, hl0_dom_refl p⟩

/-- **The coefficient bound** on `0 ≤ A ≤ H`. -/
theorem hl0_low_le {H A : ℝ} (hA : 0 ≤ A) (hAH : A ≤ H) (p : List ℝ) :
    hl0Low H p ≤ lrhHorner p A :=
  hl0_low_le_dom hA hAH p p (hl0_dom_refl p) (by simp)

/-- **Sign on an interval** from the coefficient bound after a Taylor shift to its left end. -/
theorem hl0_pos_of_shift {p q A : ℝ} (cs : List ℝ) (h : 0 < hl0Low (q - p) (hl0Shift p cs))
    (hpA : p ≤ A) (hAq : A ≤ q) : 0 < lrhHorner cs A := by
  have e : lrhHorner cs A = lrhHorner (hl0Shift p cs) (A - p) := by
    rw [hl0_horner_shift]; ring_nf
  rw [e]
  exact h.trans_le (hl0_low_le (by linarith) (by linarith) _)


/-- **Sign on an interval from a cover**: `hl0Cov cs e [p₀, p₁, …, pₙ]` asks the coefficient bound
after the Taylor shift on each piece `[pᵢ, pᵢ₊₁]` (with `pₙ₊₁ = e`). -/
def hl0Cov (cs : List ℝ) (e : ℝ) : List ℝ → Prop
  | [] => True
  | [p] => 0 < hl0Low (e - p) (hl0Shift p cs)
  | p :: q :: r => 0 < hl0Low (q - p) (hl0Shift p cs) ∧ hl0Cov cs e (q :: r)

theorem hl0_cov_pos (cs : List ℝ) (e : ℝ) :
    ∀ (p : ℝ) (r : List ℝ), hl0Cov cs e (p :: r) → ∀ A, p ≤ A → A ≤ e → 0 < lrhHorner cs A := by
  intro p r
  induction r generalizing p with
  | nil => intro h A h1 h2; exact hl0_pos_of_shift cs h h1 h2
  | cons q r ih =>
    intro h A h1 h2
    obtain ⟨hq, hr⟩ := h
    rcases le_total A q with hAq | hAq
    · exact hl0_pos_of_shift cs hq h1 hAq
    · exact ih q hr A hAq h2

/-- Positive constant term and nonnegative other coefficients. -/
def hl0PosL : List ℝ → Prop
  | [] => False
  | c :: p => 0 < c ∧ ∀ d ∈ p, 0 ≤ d

theorem hl0_nn_horner {X : ℝ} (hX : 0 ≤ X) : ∀ p : List ℝ, (∀ d ∈ p, 0 ≤ d) → 0 ≤ lrhHorner p X
  | [], _ => by simp [lrhHorner]
  | c :: p, h => by
    simp only [lrhHorner]
    have hc : 0 ≤ c := h c (by simp)
    have := hl0_nn_horner hX p (fun d hd => h d (List.mem_cons_of_mem c hd))
    positivity

theorem hl0_posL_horner {X : ℝ} (hX : 0 ≤ X) (p : List ℝ) (h : hl0PosL p) : 0 < lrhHorner p X := by
  cases p with
  | nil => exact absurd h (by simp [hl0PosL])
  | cons c p =>
    obtain ⟨hc, hp⟩ := h
    simp only [lrhHorner]
    have := hl0_nn_horner hX p hp
    positivity

/-! ### Bivariate coefficient lists -/

/-- An outer polynomial in `X` whose coefficients are polynomials in `A`. -/
noncomputable def hl0H2 (LL : List (List ℝ)) (X A : ℝ) : ℝ :=
  lrhHorner (LL.map (fun l => lrhHorner l A)) X

/-- Coefficientwise sum of two bivariate lists. -/
noncomputable def hl0Add2 : List (List ℝ) → List (List ℝ) → List (List ℝ)
  | [], Q => Q
  | c :: P, [] => c :: P
  | c :: P, d :: Q => hl0Add c d :: hl0Add2 P Q

theorem hl0_map_add2 (P Q : List (List ℝ)) (A : ℝ) :
    ∀ X, lrhHorner ((hl0Add2 P Q).map (fun l => lrhHorner l A)) X =
      lrhHorner (P.map (fun l => lrhHorner l A)) X + lrhHorner (Q.map (fun l => lrhHorner l A)) X := by
  induction P generalizing Q with
  | nil => intro X; simp [hl0Add2, lrhHorner]
  | cons c P ih =>
    intro X
    cases Q with
    | nil => simp [hl0Add2, lrhHorner]
    | cons d Q => simp only [hl0Add2, List.map, lrhHorner, ih, hl0_horner_add]; ring

/-- The `X`-derivative of a bivariate list. -/
noncomputable def hl0D2 : List (List ℝ) → List (List ℝ)
  | [] => []
  | _ :: P => hl0Add2 P ([] :: hl0D2 P)

theorem hl0_H2_D (P : List (List ℝ)) (X A : ℝ) :
    hl0H2 (hl0D2 P) X A = lrhHornerD (P.map (fun l => lrhHorner l A)) X := by
  unfold hl0H2
  induction P generalizing X with
  | nil => simp [hl0D2, lrhHorner, lrhHornerD]
  | cons c P ih =>
    simp only [hl0D2, hl0_map_add2, List.map, lrhHorner, lrhHornerD, ih]; ring

theorem hl0_hasDerivAt2 (P : List (List ℝ)) (A X : ℝ) :
    HasDerivAt (fun X => hl0H2 P X A) (hl0H2 (hl0D2 P) X A) X := by
  rw [hl0_H2_D]; exact lrh_hasDerivAt_horner _ X

/-- The restriction of a bivariate list to `X = X₀`, as a polynomial in `A`. -/
noncomputable def hl0Eval (X₀ : ℝ) : List (List ℝ) → List ℝ
  | [] => []
  | l :: P => hl0Add l (hl0Smul X₀ (hl0Eval X₀ P))

theorem hl0_horner_eval (X₀ : ℝ) (P : List (List ℝ)) (A : ℝ) :
    lrhHorner (hl0Eval X₀ P) A = hl0H2 P X₀ A := by
  unfold hl0H2
  induction P with
  | nil => simp [hl0Eval, lrhHorner]
  | cons l P ih => simp only [hl0Eval, hl0_horner_add, hl0_horner_smul, List.map, lrhHorner, ih]

/-- The restriction of a bivariate list to the line `X = αA + β`, as a polynomial in `A`. -/
noncomputable def hl0Slant (α β : ℝ) : List (List ℝ) → List ℝ
  | [] => []
  | l :: P => hl0Add l (hl0Add (hl0Smul β (hl0Slant α β P)) (0 :: hl0Smul α (hl0Slant α β P)))

theorem hl0_horner_slant (α β : ℝ) (P : List (List ℝ)) (A : ℝ) :
    lrhHorner (hl0Slant α β P) A = hl0H2 P (α * A + β) A := by
  unfold hl0H2
  induction P with
  | nil => simp [hl0Slant, lrhHorner]
  | cons l P ih =>
    simp only [hl0Slant, hl0_horner_add, hl0_horner_smul, List.map, lrhHorner, ih]; ring

/-- **The bivariate coefficient bound**: every coefficient of `X` is bounded on `0 ≤ A ≤ H_A` by
`hl0Low`, then the resulting polynomial in `X` on `0 ≤ X ≤ H_X`. -/
noncomputable def hl0Low2 (HA HX : ℝ) (P : List (List ℝ)) : ℝ :=
  hl0Low HX (P.map (hl0Low HA))

theorem hl0_dom_map {HA A : ℝ} (hA : 0 ≤ A) (hAH : A ≤ HA) (P : List (List ℝ)) :
    hl0Dom (P.map (hl0Low HA)) (P.map (fun l => lrhHorner l A)) := by
  induction P with
  | nil => trivial
  | cons l P ih => exact ⟨hl0_low_le hA hAH l, ih⟩

theorem hl0_low2_le {HA HX A X : ℝ} (hA : 0 ≤ A) (hAH : A ≤ HA) (hX : 0 ≤ X) (hXH : X ≤ HX)
    (P : List (List ℝ)) : hl0Low2 HA HX P ≤ hl0H2 P X A :=
  hl0_low_le_dom hX hXH _ _ (hl0_dom_map hA hAH P) (by
    rw [List.drop_eq_nil_of_le (by simp)]; simp)


theorem hl0_H2_map {P : List (List ℝ)} {f : List ℝ → List ℝ} {c A : ℝ}
    (hf : ∀ q, lrhHorner (f q) A = c * lrhHorner q A) (X : ℝ) :
    hl0H2 (P.map f) X A = c * hl0H2 P X A := by
  unfold hl0H2
  induction P with
  | nil => simp [lrhHorner]
  | cons l P ih => simp only [List.map, lrhHorner, hf, ih]; ring

theorem hl0_H2_add2 (P Q : List (List ℝ)) (X A : ℝ) :
    hl0H2 (hl0Add2 P Q) X A = hl0H2 P X A + hl0H2 Q X A := hl0_map_add2 P Q A X

theorem hl0_H2_cons_nil (P : List (List ℝ)) (X A : ℝ) : hl0H2 ([] :: P) X A = X * hl0H2 P X A := by
  simp [hl0H2, lrhHorner]

theorem hl0_H2_single (l : List ℝ) (X A : ℝ) : hl0H2 [l] X A = lrhHorner l A := by
  simp [hl0H2, lrhHorner]

/-- Outer Taylor shift of a bivariate list: `hl0H2 (hl0Shift2 m P) X A = hl0H2 P (m + X) A`. -/
noncomputable def hl0Shift2 (m : ℝ) : List (List ℝ) → List (List ℝ)
  | [] => []
  | l :: P => hl0Add2 [l] (hl0Add2 ((hl0Shift2 m P).map (hl0Smul m)) ([] :: hl0Shift2 m P))

theorem hl0_H2_shift2 (m : ℝ) (P : List (List ℝ)) (X A : ℝ) :
    hl0H2 (hl0Shift2 m P) X A = hl0H2 P (m + X) A := by
  induction P with
  | nil => simp [hl0Shift2, hl0H2, lrhHorner]
  | cons l P ih =>
    simp only [hl0Shift2, hl0_H2_add2, hl0_H2_single, hl0_H2_cons_nil,
      hl0_H2_map (fun q => hl0_horner_smul m q A), ih]
    simp only [hl0H2, List.map, lrhHorner]; ring

/-- The shear `X = Y + αA` of a bivariate list: `hl0H2 (hl0Shear α P) Y A = hl0H2 P (Y + αA) A`. -/
noncomputable def hl0Shear (α : ℝ) : List (List ℝ) → List (List ℝ)
  | [] => []
  | l :: P => hl0Add2 [l] (hl0Add2 ([] :: hl0Shear α P) ((hl0Shear α P).map (fun q => 0 :: hl0Smul α q)))

theorem hl0_H2_shear (α : ℝ) (P : List (List ℝ)) (Y A : ℝ) :
    hl0H2 (hl0Shear α P) Y A = hl0H2 P (Y + α * A) A := by
  induction P with
  | nil => simp [hl0Shear, hl0H2, lrhHorner]
  | cons l P ih =>
    have hf : ∀ q, lrhHorner (0 :: hl0Smul α q) A = (α * A) * lrhHorner q A := by
      intro q; simp only [lrhHorner, hl0_horner_smul]; ring
    simp only [hl0Shear, hl0_H2_add2, hl0_H2_single, hl0_H2_cons_nil, hl0_H2_map hf, ih]
    simp only [hl0H2, List.map, lrhHorner]; ring

/-- Inner Taylor shift: `hl0H2 (P.map (hl0Shift m)) X A = hl0H2 P X (m + A)`. -/
theorem hl0_H2_shift_inner (m : ℝ) (P : List (List ℝ)) (X A : ℝ) :
    hl0H2 (P.map (hl0Shift m)) X A = hl0H2 P X (m + A) := by
  unfold hl0H2
  induction P with
  | nil => simp [lrhHorner]
  | cons l P ih => simp only [List.map, lrhHorner, hl0_horner_shift, ih]

/-- The inner derivative: `∂_A hl0H2 P X A = hl0H2 (P.map hl0D) X A`. -/
theorem hl0_hasDerivAt2_inner (P : List (List ℝ)) (X A : ℝ) :
    HasDerivAt (fun A => hl0H2 P X A) (hl0H2 (P.map hl0D) X A) A := by
  unfold hl0H2
  induction P with
  | nil => simpa [lrhHorner] using hasDerivAt_const A (0 : ℝ)
  | cons l P ih =>
    simp only [List.map, lrhHorner]
    exact (hl0_hasDerivAt l A).add (ih.const_mul X)

/-- **The unbounded bivariate rule**: coefficients of `X` bounded on `0 ≤ A ≤ H_A`, then a positive
constant and nonnegative higher coefficients give positivity for every `X ≥ 0`. -/
theorem hl0_pos_unb {HA A X : ℝ} (hA : 0 ≤ A) (hAH : A ≤ HA) (hX : 0 ≤ X) (P : List (List ℝ))
    (h : hl0PosL (P.map (hl0Low HA))) : 0 < hl0H2 P X A := by
  unfold hl0H2
  induction P generalizing X with
  | nil => exact absurd h (by simp [hl0PosL])
  | cons l P _ =>
    obtain ⟨hc, hp⟩ := h
    simp only [List.map, lrhHorner]
    have h0 := (hl0_low_le hA hAH l)
    have hnn : 0 ≤ lrhHorner (P.map (fun l => lrhHorner l A)) X := by
      have := hl0_low_le_dom hX le_rfl (P.map (hl0Low HA)) (P.map (fun l => lrhHorner l A))
        (hl0_dom_map hA hAH P) (by rw [List.drop_eq_nil_of_le (by simp)]; simp)
      have h2 : 0 ≤ hl0Low X (P.map (hl0Low HA)) := by
        cases hP : P.map (hl0Low HA) with
        | nil => simp [hl0Low]
        | cons d q =>
          rw [hP] at hp
          simp only [hl0Low]
          have hd : 0 ≤ d := hp d (by simp)
          have : hl0Neg X q = 0 := by
            have hq : ∀ e ∈ q, 0 ≤ e := fun e he => hp e (List.mem_cons_of_mem d he)
            clear hP hp hd this
            induction q with
            | nil => simp [hl0Neg]
            | cons e q ih =>
              simp only [hl0Neg]
              rw [min_eq_right (hq e (by simp)), ih (fun f hf => hq f (List.mem_cons_of_mem e hf))]
              ring
          rw [this]; simpa using hd
      linarith
    have := mul_nonneg hX hnn
    linarith

/-- Monotonicity in `X` from a nonnegative `X`-derivative. -/
theorem hl0_mono_X {P : List (List ℝ)} {A X₁ X₂ : ℝ}
    (hd : ∀ X, X₁ ≤ X → X ≤ X₂ → 0 ≤ hl0H2 (hl0D2 P) X A) (h12 : X₁ ≤ X₂) :
    hl0H2 P X₁ A ≤ hl0H2 P X₂ A :=
  hrl_mono (f := fun X => hl0H2 P X A) (fun s => hl0_hasDerivAt2 _ A s)
    (fun s h1 h2 => hd s h1 h2) le_rfl h12 le_rfl

/-- Monotonicity in `A` from a nonnegative `A`-derivative. -/
theorem hl0_mono_A {P : List (List ℝ)} {X A₁ A₂ : ℝ}
    (hd : ∀ A, A₁ ≤ A → A ≤ A₂ → 0 ≤ hl0H2 (P.map hl0D) X A) (h12 : A₁ ≤ A₂) :
    hl0H2 P X A₁ ≤ hl0H2 P X A₂ :=
  hrl_mono (f := fun A => hl0H2 P X A) (fun s => hl0_hasDerivAt2_inner _ X s)
    (fun s h1 h2 => hd s h1 h2) le_rfl h12 le_rfl

/-! ### Products of coefficient lists -/

/-- Product of coefficient lists. -/
noncomputable def hl0Mul : List ℝ → List ℝ → List ℝ
  | [], _ => []
  | c :: p, q => hl0Add (hl0Smul c q) (0 :: hl0Mul p q)

theorem hl0_horner_mul (p q : List ℝ) (s : ℝ) :
    lrhHorner (hl0Mul p q) s = lrhHorner p s * lrhHorner q s := by
  induction p with
  | nil => simp [hl0Mul, lrhHorner]
  | cons c p ih => simp only [hl0Mul, hl0_horner_add, hl0_horner_smul, lrhHorner, ih]; ring

/-- Scalar multiple of a bivariate list. -/
noncomputable def hl0Smul2 (m : ℝ) (P : List (List ℝ)) : List (List ℝ) := P.map (hl0Smul m)

theorem hl0_H2_smul2 (m : ℝ) (P : List (List ℝ)) (X A : ℝ) :
    hl0H2 (hl0Smul2 m P) X A = m * hl0H2 P X A :=
  hl0_H2_map (fun q => hl0_horner_smul m q A) X

/-- Product of bivariate lists. -/
noncomputable def hl0Mul2 : List (List ℝ) → List (List ℝ) → List (List ℝ)
  | [], _ => []
  | l :: P, Q => hl0Add2 (Q.map (hl0Mul l)) ([] :: hl0Mul2 P Q)

theorem hl0_H2_mul2 (P Q : List (List ℝ)) (X A : ℝ) :
    hl0H2 (hl0Mul2 P Q) X A = hl0H2 P X A * hl0H2 Q X A := by
  induction P with
  | nil => simp [hl0Mul2, hl0H2, lrhHorner]
  | cons l P ih =>
    simp only [hl0Mul2, hl0_H2_add2, hl0_H2_cons_nil, ih,
      hl0_H2_map (fun q => hl0_horner_mul l q A)]
    simp only [hl0H2, List.map, lrhHorner]; ring

/-! ### Convexity in `x` on a rectangle -/

/-- **Rectangle convexity**: if on `0 ≤ X ≤ W` the second `X`-derivative is nonnegative, the first
derivative is nonnegative at `X = 0` and the value is positive at `X = 0`, then the value is
positive on `0 ≤ X ≤ W` (at the fixed `A`). -/
theorem hl0_conv_pos {P : List (List ℝ)} {A W X : ℝ}
    (h2 : ∀ X, 0 ≤ X → X ≤ W → 0 ≤ hl0H2 (hl0D2 (hl0D2 P)) X A)
    (h1 : 0 ≤ hl0H2 (hl0D2 P) 0 A) (h0 : 0 < hl0H2 P 0 A) (hX : 0 ≤ X) (hXW : X ≤ W) :
    0 < hl0H2 P X A := by
  have hd1 : ∀ X, 0 ≤ X → X ≤ W → 0 ≤ hl0H2 (hl0D2 P) X A := by
    intro X hX hXW
    have := hrl_mono (f := fun X => hl0H2 (hl0D2 P) X A) (fun s => hl0_hasDerivAt2 _ A s)
      (fun s h1 h2' => h2 s h1 h2') le_rfl hX hXW
    linarith
  have := hrl_mono (f := fun X => hl0H2 P X A) (fun s => hl0_hasDerivAt2 _ A s)
    (fun s h1 h2' => hd1 s h1 h2') le_rfl hX hXW
  linarith

end SmoothedOctagon
