module

public import SmoothedOctagon.Exclusion.Forward.Budget.Concavity
public import SmoothedOctagon.Exclusion.Forward.Cap
public import Mathlib.Analysis.Convex.Deriv

/-!
# Case F: the exterior-factor budget

Four exterior ratios in `[1, U]` with sum at least `(5U + 1)/3` push the cost above `A_oct`. Since
`G(a, ·)` is concave on `[a, 4/a]`, the excess over three ratios equal to `1` may be concentrated on
one ratio. Joint concavity bounds the resulting exterior cost by the chord between its two
endpoint values on `[11/5, 3]`.

## Main API

* `ff_Gbb`, `ff_hasDerivAt_Gb_right`: `∂²G/∂b²`.
* `ff_Gbb_neg`: `G_bb(a, b) < 0` for `a² ≥ 4/3`, `a ≤ b`, `ab ≤ 4`, through
  `G_abb = 2a(b - a)/(a + b)³ ≥ 0` and the two boundary values `G_bb(b, b)`, `G_bb(4/b, b)`.
* `ff_G_concaveOn`: `G(a, ·)` is concave on `[a, 4/a]`.
* `ff_four_concave`: four ratios in `[1, M]` with sum at least `σ`, `σ - 3 ∈ (1, M]`, for an
  increasing concave function: the sum is at least `3φ(1) + φ(σ - 3)`.
* `ff_budgetCost_strictConcaveOn`: joint strict concavity of the concentrated exterior cost.
* `ff_budget_linear`: its endpoint chord lies above `(29/16) U`.
* `ff_budget_g`: the one-variable budget contradiction.
-/

@[expose] public section

namespace SmoothedOctagon

open Real Set

/-! ### The second derivative of `G` -/

/-- `∂²G/∂b²`. -/
noncomputable def ff_Gbb (a b : ℝ) : ℝ :=
  Real.log (b ^ 2 + 4) - 2 * Real.log (a + b) + (a ^ 2 + b ^ 2) / (a + b) ^ 2 - 4 * b / (a + b) +
    5 * b ^ 2 / (b ^ 2 + 4) - 2 * b ^ 4 / (b ^ 2 + 4) ^ 2

theorem ff_hasDerivAt_Gb_right {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    HasDerivAt (fun y ↦ ff_Gb a y) (ff_Gbb a b) b := by
  have hab : 0 < a + b := by linarith
  have hK : 0 < b ^ 2 + 4 := by positivity
  have h1 : HasDerivAt (fun y : ℝ ↦ Real.log (a + y)) (1 / (a + b)) b := by
    simpa using ((hasDerivAt_id' b).const_add a).log hab.ne'
  have h2 : HasDerivAt (fun y : ℝ ↦ Real.log (y ^ 2 + 4)) (2 * b / (b ^ 2 + 4)) b := by
    simpa using ((hasDerivAt_pow 2 b).add_const 4).log hK.ne'
  have h : HasDerivAt (fun y ↦ ff_Gb a y) _ b :=
    ((((hasDerivAt_const b (3 * a)).sub (((hasDerivAt_id' b).const_mul 2).mul h1)).sub
      (((hasDerivAt_pow 2 b).const_add (a ^ 2)).div ((hasDerivAt_id' b).const_add a) hab.ne')).add
      ((hasDerivAt_id' b).mul h2)).add ((hasDerivAt_pow 3 b).div ((hasDerivAt_pow 2 b).add_const 4)
        hK.ne')
  refine h.congr_deriv ?_
  unfold ff_Gbb
  field_simp
  ring

/-- `∂³G/∂a∂b² = 2a(b - a)/(a + b)³`. -/
theorem ff_hasDerivAt_Gbb_left {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    HasDerivAt (fun x ↦ ff_Gbb x b) (2 * a * (b - a) / (a + b) ^ 3) a := by
  have hab : 0 < a + b := by linarith
  have h1 : HasDerivAt (fun x : ℝ ↦ Real.log (x + b)) (1 / (a + b)) a := by
    simpa using ((hasDerivAt_id' a).add_const b).log hab.ne'
  have hs : HasDerivAt (fun x : ℝ ↦ x + b) 1 a := (hasDerivAt_id' a).add_const b
  have h : HasDerivAt (fun x ↦ ff_Gbb x b) _ a :=
    (((((hasDerivAt_const a (Real.log (b ^ 2 + 4))).sub (h1.const_mul 2)).add
      (((hasDerivAt_pow 2 a).add_const (b ^ 2)).div (hs.fun_pow 2) (pow_pos hab 2).ne')).sub
      ((hasDerivAt_const a (4 * b)).div hs hab.ne')).add_const (5 * b ^ 2 / (b ^ 2 + 4))).sub_const
      (2 * b ^ 4 / (b ^ 2 + 4) ^ 2)
  refine h.congr_deriv ?_
  field_simp
  ring

/-- `G_bb(b, b) < 0` for `4/3 ≤ b² ≤ 4`. -/
theorem ff_Gbb_diag_neg {b : ℝ} (hb : 0 < b) (h1 : 4 / 3 ≤ b ^ 2) (h2 : b ^ 2 ≤ 4) :
    ff_Gbb b b < 0 := by
  have hK : 0 < b ^ 2 + 4 := by positivity
  set s := 4 * b ^ 2 / (b ^ 2 + 4) with hs
  have hs1 : 1 ≤ s := by rw [hs, le_div_iff₀ hK]; linarith
  have hs2 : s ≤ 2 := by rw [hs, div_le_iff₀ hK]; linarith
  have hlog := ff_log_ge_two hs1
  have hl1 : Real.log s = 2 * Real.log 2 + 2 * Real.log b - Real.log (b ^ 2 + 4) := by
    rw [hs, Real.log_div (by positivity) hK.ne', Real.log_mul (by norm_num) (by positivity),
      Real.log_pow, show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
    push_cast; ring
  have hl2 : Real.log (b + b) = Real.log 2 + Real.log b := by
    rw [show b + b = 2 * b by ring, Real.log_mul (by norm_num) hb.ne']
  have e : ff_Gbb b b = -Real.log s - 3 / 2 + 5 * s / 4 - s ^ 2 / 8 := by
    unfold ff_Gbb
    rw [hl2, hl1, hs]
    generalize Real.log 2 = l2
    generalize Real.log b = lb
    generalize Real.log (b ^ 2 + 4) = lk
    field_simp
    ring
  rw [e]
  have hs0 : 0 < s + 1 := by linarith
  have hq : s ^ 2 - 7 * s + 4 ≤ 0 := by nlinarith
  have hp : -s ^ 3 + 9 * s ^ 2 - 18 * s + 4 < 0 := by
    nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ 2 - s) (neg_nonneg.2 hq)]
  have key : -(2 * ((s - 1) / (s + 1))) - 3 / 2 + 5 * s / 4 - s ^ 2 / 8 < 0 := by
    rw [show -(2 * ((s - 1) / (s + 1))) - 3 / 2 + 5 * s / 4 - s ^ 2 / 8 =
      (-s ^ 3 + 9 * s ^ 2 - 18 * s + 4) / (8 * (s + 1)) by field_simp; ring]
    exact div_neg_of_neg_of_pos hp (by positivity)
  linarith

/-- `G_bb(4/b, b) = log ρ + 1 - ρ < 0`, `ρ = b²/(b² + 4)`. -/
theorem ff_Gbb_edge_neg {b : ℝ} (hb : 0 < b) : ff_Gbb (4 / b) b < 0 := by
  have hK : 0 < b ^ 2 + 4 := by positivity
  set ρ := b ^ 2 / (b ^ 2 + 4) with hρ
  have hρ0 : 0 < ρ := by positivity
  have hρ1 : ρ ≠ 1 := by
    rw [hρ]; intro h; rw [div_eq_one_iff_eq hK.ne'] at h; linarith
  have e : ff_Gbb (4 / b) b = Real.log ρ + 1 - ρ := by
    unfold ff_Gbb
    have e1 : 4 / b + b = (b ^ 2 + 4) / b := by field_simp; ring
    rw [e1, hρ, Real.log_div (by positivity) hK.ne', Real.log_div hK.ne' hb.ne', Real.log_pow]
    push_cast
    field_simp
    ring
  rw [e]
  have := Real.log_lt_sub_one_of_pos hρ0 hρ1
  linarith

/-- **`G_bb < 0`** for `a² ≥ 4/3`, `a ≤ b` and `ab ≤ 4`: `G_bb(·, b)` increases (`G_abb ≥ 0`), and
it is negative at `b` when `b ≤ 2` and at `4/b` when `b ≥ 2`. -/
theorem ff_Gbb_neg {a b : ℝ} (ha : 0 < a) (ha2 : 4 / 3 ≤ a ^ 2) (hab : a ≤ b) (hab4 : a * b ≤ 4) :
    ff_Gbb a b < 0 := by
  have hb : 0 < b := by linarith
  have mono : ∀ c, a ≤ c → c ≤ b → ff_Gbb a b ≤ ff_Gbb c b := fun c hac hcb ↦
    ff_le_of_deriv (f := fun x ↦ ff_Gbb x b) hac
      (fun x hx ↦ ff_hasDerivAt_Gbb_left (by linarith [hx.1]) hb)
      (fun x hx ↦ by
        have hx0 : 0 < x := by linarith [hx.1]
        apply div_nonneg _ (by positivity)
        apply mul_nonneg (by linarith) (by linarith [hx.2]))
  rcases le_total b 2 with hb2 | hb2
  · exact lt_of_le_of_lt (mono b hab le_rfl) (ff_Gbb_diag_neg hb (by nlinarith) (by nlinarith))
  · have h4 : a ≤ 4 / b := by rw [le_div_iff₀ hb]; linarith
    have h4' : 4 / b ≤ b := by rw [div_le_iff₀ hb]; nlinarith
    exact lt_of_le_of_lt (mono (4 / b) h4 h4') (ff_Gbb_edge_neg hb)

/-- **`G(a, ·)` is concave on `[a, 4/a]`** for `4/3 ≤ a² ≤ 4`. -/
theorem ff_G_concaveOn {a : ℝ} (ha : 0 < a) (ha2 : 4 / 3 ≤ a ^ 2) :
    ConcaveOn ℝ (Icc a (4 / a)) (fun y ↦ ff_G a y) := by
  refine concaveOn_of_hasDerivWithinAt2_nonpos (convex_Icc _ _)
    (fun y hy ↦ (ff_hasDerivAt_G_right ha (by linarith [hy.1])).continuousAt.continuousWithinAt)
    (fun y hy ↦ (ff_hasDerivAt_G_right ha ?_).hasDerivWithinAt)
    (fun y hy ↦ (ff_hasDerivAt_Gb_right ha ?_).hasDerivWithinAt) (fun y hy ↦ ?_)
  · rw [interior_Icc] at hy; linarith [hy.1]
  · rw [interior_Icc] at hy; linarith [hy.1]
  · rw [interior_Icc] at hy
    refine (ff_Gbb_neg ha ha2 hy.1.le ?_).le
    have := hy.2; rw [lt_div_iff₀ ha] at this; linarith

/-! ### Four ratios with a fixed sum -/

/-- **Concentration of the excess**: for `φ` increasing and concave on `[1, M]`, four points of
`[1, M]` with sum at least `σ`, where `x* = σ - 3 ∈ (1, M]`, have
`φ(x₁) + φ(x₂) + φ(x₃) + φ(x₄) ≥ 3φ(1) + φ(x*)`. -/
theorem ff_four_concave {φ : ℝ → ℝ} {M σ x₁ x₂ x₃ x₄ : ℝ} (hmono : MonotoneOn φ (Icc 1 M))
    (hconc : ConcaveOn ℝ (Icc 1 M) φ) (hs1 : 1 < σ - 3) (hsM : σ - 3 ≤ M)
    (h1 : x₁ ∈ Icc 1 M) (h2 : x₂ ∈ Icc 1 M) (h3 : x₃ ∈ Icc 1 M) (h4 : x₄ ∈ Icc 1 M)
    (hsum : σ ≤ x₁ + x₂ + x₃ + x₄) : 3 * φ 1 + φ (σ - 3) ≤ φ x₁ + φ x₂ + φ x₃ + φ x₄ := by
  set xs := σ - 3 with hxs
  have hM1 : (1 : ℝ) ∈ Icc 1 M := ⟨le_rfl, by linarith⟩
  have hxsM : xs ∈ Icc 1 M := ⟨hs1.le, hsM⟩
  have hd : xs - 1 ≠ 0 := (by linarith : (0 : ℝ) < xs - 1).ne'
  set sl := (φ xs - φ 1) / (xs - 1) with hsl
  have hsl0 : 0 ≤ sl := div_nonneg (sub_nonneg.2 (hmono hM1 hxsM hs1.le)) (by linarith)
  -- `φ(x) ≥ φ(1) + sl (min(x, x*) - 1)`
  have key : ∀ x ∈ Icc 1 M, φ 1 + sl * (min x xs - 1) ≤ φ x := by
    intro x hx
    rcases le_total x xs with hle | hle
    · rw [min_eq_left hle]
      -- the chord of the concave function
      have hθ : 0 ≤ (x - 1) / (xs - 1) := div_nonneg (by linarith [hx.1]) (by linarith)
      have hθ' : 0 ≤ 1 - (x - 1) / (xs - 1) := by
        rw [sub_nonneg, div_le_one (by linarith)]; linarith
      have hc := hconc.2 hM1 hxsM hθ' hθ (by ring)
      have ex : (1 - (x - 1) / (xs - 1)) • (1 : ℝ) + ((x - 1) / (xs - 1)) • xs = x := by
        simp only [smul_eq_mul]; field_simp; ring
      rw [ex] at hc
      simp only [smul_eq_mul] at hc
      have : (1 - (x - 1) / (xs - 1)) * φ 1 + (x - 1) / (xs - 1) * φ xs = φ 1 + sl * (x - 1) := by
        rw [hsl]; field_simp; ring
      linarith
    · rw [min_eq_right hle]
      have := hmono hxsM hx hle
      have e : φ 1 + sl * (xs - 1) = φ xs := by rw [hsl]; field_simp; ring
      linarith
  have k1 := key x₁ h1
  have k2 := key x₂ h2
  have k3 := key x₃ h3
  have k4 := key x₄ h4
  -- `∑ (min(xᵢ, x*) - 1) ≥ x* - 1`
  have hmin : xs - 1 ≤ (min x₁ xs - 1) + (min x₂ xs - 1) + (min x₃ xs - 1) + (min x₄ xs - 1) := by
    have m1 := h1.1; have m2 := h2.1; have m3 := h3.1; have m4 := h4.1
    rcases le_total x₁ xs with a1 | a1 <;> rcases le_total x₂ xs with a2 | a2 <;>
      rcases le_total x₃ xs with a3 | a3 <;> rcases le_total x₄ xs with a4 | a4 <;>
      simp only [min_eq_left, min_eq_right, a1, a2, a3, a4] <;> linarith
  have := mul_le_mul_of_nonneg_left hmin hsl0
  have e : 3 * φ 1 + φ xs = 4 * φ 1 + sl * (xs - 1) := by rw [hsl]; field_simp; ring
  linarith

/-! ### The endpoint chord -/

private theorem ff_budgetCost_left : 29 / 16 * (11 / 5) < ff_budgetCost (11 / 5) 1 := by
  have hl : Real.log (16 / 5) + Real.log (5 / 4) = 2 * Real.log 2 := by
    rw [← Real.log_mul (by norm_num) (by norm_num),
      show (16 / 5 : ℝ) * (5 / 4) = 2 ^ 2 by norm_num, Real.log_pow]
    norm_num
  have he : ff_budgetCost (11 / 5) 1 = 7 * (4 / 5 - Real.log (5 / 4)) := by
    unfold ff_budgetCost ff_g2
    norm_num
    linarith only [hl]
  rw [he]
  linarith only [ff_log_five_fourths_lt]

private theorem ff_budgetCost_right : 29 / 16 * 3 < ff_budgetCost 3 (7 / 3) := by
  have h15 : 0 < √15 := by positivity
  have h19 : 0 < √19 := by positivity
  have hl1 : Real.log (5 / 3) < 2 / √15 := by
    have h := ff_log_lt_sqrt_quotient (v := 5 / 3) (by norm_num)
    have he : (5 / 3 - 1) / √(5 / 3) = 2 / √15 := by
      have hs : √(5 / 3) = √15 / 3 := by
        rw [show (5 / 3 : ℝ) = 15 / 3 ^ 2 by norm_num, Real.sqrt_div (by norm_num),
          Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 3)]
      rw [hs]
      ring
    rwa [he] at h
  have hl2 : 49 / 18 * Real.log (25 / 19) < 49 / (15 * √19) := by
    have h := ff_log_lt_sqrt_quotient (v := 25 / 19) (by norm_num)
    have he : 49 / 18 * ((25 / 19 - 1) / √(25 / 19)) = 49 / (15 * √19) := by
      have hs : √(25 / 19) = 5 / √19 := by
        rw [Real.sqrt_div (by norm_num), show (25 : ℝ) = 5 ^ 2 by norm_num,
          Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 5)]
      rw [hs]
      field_simp
      nlinarith only [Real.sq_sqrt (show (0 : ℝ) ≤ 19 by norm_num)]
    have := mul_lt_mul_of_pos_left h (by norm_num : (0 : ℝ) < 49 / 18)
    rwa [he] at this
  have h17 : 2 / √15 < 17 / 32 := by
    rw [div_lt_iff₀ h15]
    nlinarith only [Real.sq_sqrt (show (0 : ℝ) ≤ 15 by norm_num), Real.sqrt_nonneg 15]
  have h34 : 49 / (15 * √19) < 3 / 4 := by
    rw [div_lt_iff₀ (by positivity : 0 < 15 * √19)]
    nlinarith only [Real.sq_sqrt (show (0 : ℝ) ≤ 19 by norm_num), Real.sqrt_nonneg 19]
  have he : ff_budgetCost 3 (7 / 3) =
      2 * (4 - Real.log (5 / 3) - 49 / 18 * Real.log (25 / 19)) := by
    have hl3 : Real.log (10 / 3) = Real.log 2 + Real.log (5 / 3) := by
      rw [← Real.log_mul (by norm_num) (by norm_num)]
      norm_num
    have hl4 : Real.log (25 / 19) = 2 * Real.log (10 / 3) - Real.log (76 / 9) := by
      calc Real.log (25 / 19) = Real.log (((10 / 3 : ℝ) ^ 2) / (76 / 9)) := by norm_num
        _ = 2 * Real.log (10 / 3) - Real.log (76 / 9) := by
          rw [Real.log_div (by norm_num) (by norm_num), Real.log_pow]
          norm_num
    have hl5 : Real.log 4 = 2 * Real.log 2 := by
      rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
      norm_num
    unfold ff_budgetCost ff_g2
    norm_num
    linarith only [hl3, hl4, hl5]
  rw [he]
  linarith only [hl1, hl2, h17, h34]

/-- The chord between the two endpoint costs lies above the linear exterior budget. -/
theorem ff_budget_linear {U : ℝ} (hU : 11 / 5 ≤ U) (hU3 : U ≤ 3) :
    29 / 16 * U < ff_budgetCost U ((5 * U - 8) / 3) := by
  by_cases he : U = 11 / 5
  · subst U
    convert ff_budgetCost_left using 1; norm_num
  have hU' : 11 / 5 < U := lt_of_le_of_ne hU (Ne.symm he)
  let a := (15 - 5 * U) / 4
  let b := (5 * U - 11) / 4
  have ha : 0 ≤ a := by dsimp [a]; linarith only [hU3]
  have hb : 0 < b := by dsimp [b]; linarith only [hU']
  have hab : a + b = 1 := by dsimp [a, b]; ring
  have hc := ff_budgetCost_strictConcaveOn.concaveOn.2
    (x := ((11 / 5 : ℝ), (1 : ℝ))) (by norm_num)
    (y := ((3 : ℝ), (7 / 3 : ℝ))) (by norm_num) ha hb.le hab
  have heq : a • ((11 / 5 : ℝ), (1 : ℝ)) + b • ((3 : ℝ), (7 / 3 : ℝ)) =
      (U, (5 * U - 8) / 3) := by
    ext <;> simp only [Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd,
      smul_eq_mul, a, b] <;> ring
  rw [heq] at hc
  simp only [smul_eq_mul] at hc
  have hl := mul_le_mul_of_nonneg_left ff_budgetCost_left.le ha
  have hr := mul_lt_mul_of_pos_left ff_budgetCost_right hb
  have hlinear : 29 / 16 * U = a * (29 / 16 * (11 / 5)) + b * (29 / 16 * 3) := by
    dsimp [a, b]
    ring
  rw [hlinear]
  linarith only [hc, hl, hr]

/-- **The one-variable budget contradiction**: on `11/5 < U < 3`, four ratios in `[1, U]` with sum
at least `(5U + 1)/3` give `(√3/U){2g(P) + 2g(z) + 2g(w) + 2g(D) - g(1)} > A_oct`, where
`g(x) = g2(U, 1, x)`. -/
theorem ff_budget_g {U P z w D : ℝ} (hU : 11 / 5 < U) (hU3 : U < 3) (hP : 1 ≤ P) (hP' : P ≤ U)
    (hz : 1 ≤ z) (hz' : z ≤ U) (hw : 1 ≤ w) (hw' : w ≤ U) (hD : 1 ≤ D) (hD' : D ≤ U)
    (hsum : (5 * U + 1) / 3 ≤ P + z + w + D) :
    octagonCost < √3 / U * (2 * ff_g2 U 1 P + 2 * ff_g2 U 1 z + 2 * ff_g2 U 1 w + 2 * ff_g2 U 1 D -
      ff_g2 U 1 1) := by
  have hU0 : 0 < U := by linarith
  -- the physical scale `a = 2/√U`
  set a := 2 / √U with ha
  have hsU : 0 < √U := Real.sqrt_pos.2 hU0
  have ha0 : 0 < a := by positivity
  have ha2 : a ^ 2 = 4 / U := by rw [ha, div_pow, Real.sq_sqrt hU0.le]; norm_num
  have hUa : U = 4 / a ^ 2 := by rw [ha2]; field_simp
  have ha43 : 4 / 3 ≤ a ^ 2 := by rw [ha2, le_div_iff₀ hU0]; linarith
  have hgx : ∀ x : ℝ, 0 < x → ff_G a (a * x) = a ^ 2 * ff_g2 U 1 x := fun x hx ↦ by
    have := ff_G_mul ha0 one_pos hx
    rw [mul_one] at this; rw [this, ← hUa]
  set φ : ℝ → ℝ := fun x ↦ ff_G a (a * x) with hφ
  have hmap : ∀ x ∈ Icc (1 : ℝ) U, a * x ∈ Icc a (4 / a) := by
    intro x hx
    refine ⟨by nlinarith [hx.1], ?_⟩
    rw [le_div_iff₀ ha0]
    have : a * x * a = a ^ 2 * x := by ring
    rw [this, ha2]
    have := hx.2
    rw [div_mul_eq_mul_div, div_le_iff₀ hU0]; nlinarith
  have hmono : MonotoneOn φ (Icc 1 U) := by
    intro x hx y hy hxy
    refine ff_G_mono_right ha0 (by nlinarith [hx.1]) (by nlinarith) ?_
    have := (hmap y hy).2
    rw [le_div_iff₀ ha0] at this
    nlinarith
  have hconc : ConcaveOn ℝ (Icc 1 U) φ := by
    refine ⟨convex_Icc _ _, fun x hx y hy θ η hθ hη hθη ↦ ?_⟩
    have hc := (ff_G_concaveOn ha0 ha43).2 (hmap x hx) (hmap y hy) hθ hη hθη
    simp only [smul_eq_mul, hφ] at hc ⊢
    have e : a * (θ * x + η * y) = θ * (a * x) + η * (a * y) := by ring
    rw [e]; exact hc
  have hxs1 : 1 < (5 * U + 1) / 3 - 3 := by linarith
  have hxsU : (5 * U + 1) / 3 - 3 ≤ U := by linarith
  have h4 := ff_four_concave hmono hconc hxs1 hxsU ⟨hP, hP'⟩ ⟨hz, hz'⟩ ⟨hw, hw'⟩ ⟨hD, hD'⟩ hsum
  simp only [hφ] at h4
  have hxs : (5 * U + 1) / 3 - 3 = (5 * U - 8) / 3 := by ring
  rw [hxs, hgx 1 one_pos, hgx _ (by linarith), hgx P (by linarith), hgx z (by linarith),
    hgx w (by linarith), hgx D (by linarith)] at h4
  -- divide by `a²`
  have h4' : 3 * ff_g2 U 1 1 + ff_g2 U 1 ((5 * U - 8) / 3) ≤
      ff_g2 U 1 P + ff_g2 U 1 z + ff_g2 U 1 w + ff_g2 U 1 D := by
    have ha2p : 0 < a ^ 2 := by positivity
    nlinarith
  have hlb := ff_budget_linear hU.le hU3.le
  unfold ff_budgetCost at hlb
  have hbig : 29 / 16 * U < 2 * ff_g2 U 1 P + 2 * ff_g2 U 1 z + 2 * ff_g2 U 1 w +
      2 * ff_g2 U 1 D - ff_g2 U 1 1 := by linarith only [hlb, h4']
  calc octagonCost < 29 * √3 / 16 := ff_octagonCost_lt_sqrt
    _ = √3 / U * (29 / 16 * U) := by field_simp
    _ < _ := mul_lt_mul_of_pos_left hbig (div_pos (by positivity) hU0)

end SmoothedOctagon
