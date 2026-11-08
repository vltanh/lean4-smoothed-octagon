module

public import SmoothedOctagon.Exclusion.Mixed.ShortHand.Heavy.S3HandOLowY
public import SmoothedOctagon.Exclusion.Mixed.ShortHand.Heavy.S3HandOMid
public import SmoothedOctagon.Exclusion.Mixed.ShortHand.Heavy.S3HandOUp

/-!
# Gate S3, the outer face by hand: the assembly

Proof of the leaf `hs3_outer_face`. On the actual outer terminal shapes
`1 ≤ α ≤ x`, `x(x + 2) ≤ 6α²` (so `α ≥ a_* = 5(x + 1)/13`), `β = x + C(α - 1)` with
`8x/(9x + 8) ≤ C = xg ≤ 115x/304` (the retained lower short-order bound), at `q = 1/7` and
`u = ū(x, β)`:

* the logarithm is replaced by its rational majorant (`hs3_log_maj`, `β < 2α`), and the test is
  `G(x, C, n, 1/α)` (`hl3o_G_eq`);
* the duration multipliers satisfy `n₀, n₁ ∈ [25/8, 7/2]` for `α ≤ 5/4` and `∈ [5/2, 7/2]` for
  `α ≥ 5/4` (`hl3o_n_bds`);
* `G` is affine in `n` and convex in `r = 1/α` (`hl3o_neg_between`); it is negative at `α = x`
  (`hl3o_up`), at `α = 5/4` for `n = 5/2` (`hl3o_mid`) and at `α = a_*` for `n = 25/8, 7/2`
  (`hl3o_low`).

## Main API

* `hs3_outer_face_proof`: `F₀, F₁ < 0` on the actual outer terminal shapes.
-/

@[expose] public section

namespace SmoothedOctagon

open Real Set

/-- `G` is affine in the duration weight. -/
theorem hl3o_G_affine (x C r n n₁ n₂ : ℝ) :
    (n₂ - n₁) * hl3oG x C n r = (n₂ - n) * hl3oG x C n₁ r + (n - n₁) * hl3oG x C n₂ r := by
  unfold hl3oG hl3oP hl3oA hl3oPc0 hl3oPc1 hl3oPc2 hl3oPc3 hl3oPc4 hl3oAc0 hl3oAc1 hl3oAc2 hl3oAc3
    hl3oAc4
  ring

/-- Negative at two weights, negative in between. -/
theorem hl3o_G_interp {x C r n n₁ n₂ : ℝ} (h12 : n₁ < n₂) (hn₁ : n₁ ≤ n) (hn₂ : n ≤ n₂)
    (h₁ : hl3oG x C n₁ r < 0) (h₂ : hl3oG x C n₂ r < 0) : hl3oG x C n r < 0 := by
  have e := hl3o_G_affine x C r n n₁ n₂
  have hs : (n₂ - n) * hl3oG x C n₁ r + (n - n₁) * hl3oG x C n₂ r < 0 := by
    rcases eq_or_lt_of_le hn₂ with h | h
    · rw [h, sub_self, zero_mul, zero_add]
      exact mul_neg_of_pos_of_neg (by linarith) h₂
    · have h1 : (n₂ - n) * hl3oG x C n₁ r < 0 := mul_neg_of_pos_of_neg (by linarith) h₁
      have h2 : (n - n₁) * hl3oG x C n₂ r ≤ 0 := mul_nonpos_of_nonneg_of_nonpos (by linarith) h₂.le
      linarith
  rw [← e] at hs
  exact neg_of_mul_neg_right hs (by linarith)

/-! ### The duration multipliers -/

section Mult

variable {x a b : ℝ}

theorem hl3o_n0_eq (ha : 1 < a) (hb : 0 < a + b) :
    2 + 4 * (4 - 3 * (2 * (1 / 7) / hsRA a b)) / (5 * a - 1) =
      2 + (88 * a - 24 * b) / (7 * a * (5 * a - 1)) := by
  unfold hsRA
  have ha0 : a ≠ 0 := by linarith
  have hk : 5 * a - 1 ≠ 0 := by linarith
  have hb' : a + b ≠ 0 := hb.ne'
  generalize 5 * a - 1 = k at hk ⊢
  field_simp
  ring

theorem hl3o_n1_eq (ha : 1 < a) : hsRA a b / (1 / 7) = 7 * a / (a + b) := by
  unfold hsRA; field_simp

/-- **The multiplier enclosure**: `n₀, n₁ ∈ [5/2, 7/2]`, and `n₀, n₁ ≥ 25/8` for `α ≤ 5/4`, from
the cleared numerators and the lower beta order. -/
theorem hl3o_n_bds {C : ℝ} (hx : 2 ≤ x) (hx2 : x ≤ 13 / 6) (ha : 1 < a) (hax : a ≤ x)
    (hC : 8 * x / (9 * x + 8) ≤ C) (hC' : C ≤ 19 * x / 50) (hb : b = x + C * (a - 1))
    (hb2 : b < 2 * a) :
    let n₀ := 2 + 4 * (4 - 3 * (2 * (1 / 7) / hsRA a b)) / (5 * a - 1)
    let n₁ := hsRA a b / (1 / 7) + 4 / (5 * a - 1)
    5 / 2 ≤ n₀ ∧ n₀ ≤ 7 / 2 ∧ 5 / 2 ≤ n₁ ∧ n₁ ≤ 7 / 2 ∧ (a ≤ 5 / 4 → 25 / 8 ≤ n₀ ∧ 25 / 8 ≤ n₁) := by
  intro n₀ n₁
  have hx0 : 0 < x := by linarith
  have hC0 : 0 ≤ C := le_trans (by positivity) hC
  have hbx : x ≤ b := by rw [hb]; nlinarith
  have hab : 0 < a + b := by linarith
  have hk : 0 < 5 * a - 1 := by linarith
  have hn₀ : n₀ = 2 + (88 * a - 24 * b) / (7 * a * (5 * a - 1)) := hl3o_n0_eq ha hab
  have hn₁ : n₁ = 7 * a / (a + b) + 4 / (5 * a - 1) := by
    show hsRA a b / (1 / 7) + 4 / (5 * a - 1) = _
    rw [hl3o_n1_eq ha]
  have hD : 0 < 7 * a * (5 * a - 1) := by positivity
  -- the cleared numerators
  have e1 : ∀ c, 7 * a / (a + b) + 4 / (5 * a - 1) - c =
      (7 * a * (5 * a - 1) + 4 * (a + b) - c * (a + b) * (5 * a - 1)) / ((a + b) * (5 * a - 1)) := by
    intro c
    have hk' : 5 * a - 1 ≠ 0 := hk.ne'
    have hab' : a + b ≠ 0 := hab.ne'
    generalize 5 * a - 1 = k at hk' ⊢
    field_simp
  have hb13 : b ≤ (247 * a + 403) / 300 := by
    rw [hb]
    have : C * (a - 1) ≤ 19 * x / 50 * (a - 1) := mul_le_mul_of_nonneg_right hC' (by linarith)
    nlinarith
  -- the lower beta order at `x`
  have hbl : x + 8 * x / (9 * x + 8) * (a - 1) ≤ b := by
    rw [hb]; nlinarith [mul_le_mul_of_nonneg_right hC (by linarith : (0 : ℝ) ≤ a - 1)]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · -- `183a - 35a² - 48b > a(87 - 35a) > 0`
    rw [hn₀]
    have : 1 / 2 * (7 * a * (5 * a - 1)) ≤ 88 * a - 24 * b := by nlinarith
    have := (le_div_iff₀ hD).2 this
    linarith
  · rw [hn₀]
    have : 88 * a - 24 * b ≤ 3 / 2 * (7 * a * (5 * a - 1)) := by nlinarith
    have := (div_le_iff₀ hD).2 this
    linarith
  · rw [hn₁]
    have h := e1 (5 / 2)
    have : 0 ≤ 7 * a * (5 * a - 1) + 4 * (a + b) - 5 / 2 * (a + b) * (5 * a - 1) := by nlinarith
    have := div_nonneg this (by positivity : (0 : ℝ) ≤ (a + b) * (5 * a - 1))
    linarith
  · -- `(35a - 15)b - 35a² - a > 0`, by the lower beta order
    rw [hn₁]
    have h := e1 (7 / 2)
    have hnum : 0 < (35 * a - 15) * b - 35 * a ^ 2 - a := by
      have hl : (35 * a - 15) * (x + 8 * x / (9 * x + 8) * (a - 1)) ≤ (35 * a - 15) * b :=
        mul_le_mul_of_nonneg_left hbl (by linarith)
      have e9 : x + 8 * x / (9 * x + 8) * (a - 1) = x * (9 * x + 8 * a) / (9 * x + 8) := by
        field_simp; ring
      rw [e9] at hl
      rcases le_or_gt a 2 with ha2 | ha2
      · -- replace `x` by `2`
        have hm : (18 + 8 * a) / 13 ≤ x * (9 * x + 8 * a) / (9 * x + 8) := by
          rw [div_le_div_iff₀ (by norm_num) (by positivity)]
          nlinarith [mul_nonneg (sub_nonneg.2 hx) (sub_nonneg.2 (le_of_lt ha))]
        have := mul_le_mul_of_nonneg_left hm (by linarith : (0 : ℝ) ≤ 35 * a - 15)
        nlinarith
      · -- replace `x` by `a`
        have hm : a * (9 * a + 8 * a) / (9 * a + 8) ≤ x * (9 * x + 8 * a) / (9 * x + 8) := by
          rw [div_le_div_iff₀ (by positivity) (by positivity)]
          nlinarith [mul_nonneg (sub_nonneg.2 hax) (by positivity : (0 : ℝ) ≤ a)]
        have := mul_le_mul_of_nonneg_left hm (by linarith : (0 : ℝ) ≤ 35 * a - 15)
        have e17 : (35 * a - 15) * (a * (9 * a + 8 * a) / (9 * a + 8)) - 35 * a ^ 2 - a =
            a * (280 * a ^ 2 - 544 * a - 8) / (9 * a + 8) := by
          field_simp; ring
        have : 0 < a * (280 * a ^ 2 - 544 * a - 8) / (9 * a + 8) := by
          apply div_pos _ (by positivity)
          apply mul_pos (by linarith); nlinarith
        linarith
    have : 0 ≤ (7 / 2 - (7 * a / (a + b) + 4 / (5 * a - 1))) := by
      have e2 : 7 / 2 - (7 * a / (a + b) + 4 / (5 * a - 1)) =
          ((35 * a - 15) * b - 35 * a ^ 2 - a) / (2 * (a + b) * (5 * a - 1)) := by
        rw [← neg_sub, h]
        have hk' : 5 * a - 1 ≠ 0 := hk.ne'
        have hab' : a + b ≠ 0 := hab.ne'
        generalize hkd : 5 * a - 1 = k at hk' ⊢
        field_simp
        rw [← hkd]
        ring
      rw [e2]; positivity
    linarith
  · intro ha54
    constructor
    · -- `767a - 315a² - 192b ≥ (-7875a² + 15223a - 6448)/25 > 0`
      rw [hn₀]
      have : 9 / 8 * (7 * a * (5 * a - 1)) ≤ 88 * a - 24 * b := by nlinarith
      have := (le_div_iff₀ hD).2 this
      linarith
    · -- `155a² + a + 57b - 125ab ≥ (15625a² - 35996a + 22971)/300 > 0`
      rw [hn₁]
      have h := e1 (25 / 8)
      have hb' : b * (125 * a - 57) ≤ (247 * a + 403) / 300 * (125 * a - 57) :=
        mul_le_mul_of_nonneg_right hb13 (by linarith)
      have : 0 ≤ 7 * a * (5 * a - 1) + 4 * (a + b) - 25 / 8 * (a + b) * (5 * a - 1) := by
        nlinarith [sq_nonneg (a - 35996 / 31250)]
      have := div_nonneg this (by positivity : (0 : ℝ) ≤ (a + b) * (5 * a - 1))
      linarith

end Mult

/-- The rational logarithm majorant at `q = 1/7`: `ℓ* = 319847/180000 - 56α/(19α + 5β)`. -/
theorem hl3o_logmaj {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    -40153 / 180000 + 2 * (5 * (2 * (1 / 7) / hsRA a b) - 4) / (5 * (2 * (1 / 7) / hsRA a b) + 4) =
      319847 / 180000 - 56 * a / (19 * a + 5 * b) := by
  have e : 2 * (1 / 7) / hsRA a b = 2 * (a + b) / (7 * a) := by
    unfold hsRA
    have : a + b ≠ 0 := by linarith
    field_simp
  rw [e]
  have h1 : 2 * (5 * (2 * (a + b) / (7 * a)) - 4) / (5 * (2 * (a + b) / (7 * a)) + 4) =
      (10 * b - 18 * a) / (19 * a + 5 * b) := by
    rw [div_eq_div_iff (by positivity) (by positivity)]
    field_simp
    ring
  rw [h1]
  have : 19 * a + 5 * b ≠ 0 := by positivity
  field_simp
  ring

/-! ### The leaf -/

/-- **`hs3_outer_face`**: on the actual outer terminal shapes, with the retained lower
short-order slope `g ≥ 8/(9x + 8)`, both outer tests are negative at `q = 1/7`, `u = ū(x, β)`. -/
theorem hs3_outer_face_proof {x al g : ℝ} (hx : 2 ≤ x) (hx2 : x ≤ 13 / 6) (hal : 1 ≤ al)
    (hax : al ≤ x) (h6 : x * (x + 2) ≤ 6 * al ^ 2) (hg : 8 / (9 * x + 8) ≤ g) (hg' : g ≤ 115 / 304) :
    hs3F0 x (x * (1 + g * (al - 1))) al (hsUO x (x * (1 + g * (al - 1)))) (1 / 7) < 0 ∧
      hs3F1 x (x * (1 + g * (al - 1))) al (hsUO x (x * (1 + g * (al - 1)))) (1 / 7) < 0 := by
  have hx0 : 0 < x := by linarith
  set C := x * g with hCd
  have hbe : x * (1 + g * (al - 1)) = x + C * (al - 1) := by rw [hCd]; ring
  rw [hbe]
  set b := x + C * (al - 1) with hbd
  -- the shape domain
  have has : 5 * (x + 1) / 13 ≤ al := by
    have h2 : (5 * (x + 1) / 13) ^ 2 ≤ al ^ 2 := by nlinarith
    exact (abs_le_of_sq_le_sq' h2 (by linarith)).2
  have ha1 : 1 < al := by linarith
  have hC1 : 8 * x / (9 * x + 8) ≤ C := by
    rw [hCd, div_le_iff₀ (by positivity)]
    rw [div_le_iff₀ (by positivity)] at hg
    nlinarith
  have hC2 : C ≤ 19 * x / 50 := by rw [hCd]; nlinarith
  have hC35 : 3 / 5 ≤ C := by
    have : 3 / 5 ≤ 8 * x / (9 * x + 8) := by rw [le_div_iff₀ (by positivity)]; linarith
    linarith
  have hC56 : C ≤ 5 / 6 := by linarith
  have hb2 : b < 2 * al := by
    rw [hbd]
    have h1 : C * (al - 1) ≤ 115 * x / 304 * (al - 1) :=
      mul_le_mul_of_nonneg_right (by rw [hCd]; nlinarith) (by linarith)
    nlinarith [mul_nonneg (sub_nonneg.2 has) (by linarith : (0 : ℝ) ≤ 2 - 115 * x / 304),
      mul_nonneg (sub_nonneg.2 hx) (sub_nonneg.2 hx2)]
  have hbx : x ≤ b := by rw [hbd]; nlinarith
  -- the rational logarithm majorant (`y = 2q/r_A ≤ 6/7`)
  have hRA : 0 < hsRA al b := by unfold hsRA; apply div_pos <;> linarith
  have hy0 : 0 < 2 * (1 / 7) / hsRA al b := by positivity
  have ey : 2 * (1 / 7) / hsRA al b = 2 * (al + b) / (7 * al) := by
    unfold hsRA
    have : al ≠ 0 := by linarith
    have : al + b ≠ 0 := by linarith
    field_simp
  have hy7 : 2 * (1 / 7) / hsRA al b ≤ 6 / 7 := by
    rw [ey, div_le_div_iff₀ (by linarith) (by norm_num)]
    linarith
  have hlog := hs3_log_maj hy0 hy7
  have hmaj := hl3o_logmaj (a := al) (b := b) (by linarith) (by linarith)
  rw [hmaj] at hlog
  have hF : ∀ n, hs3Fn x b al (hsUO x b) (1 / 7) n (log (2 * (1 / 7) / hsRA al b)) ≤
      hl3oG x C n (1 / al) := by
    intro n
    rw [← hl3o_G_eq (by linarith) ha1 (by linarith) (by linarith)]
    unfold hs3Fn
    linarith
  -- the multipliers
  obtain ⟨hn0a, hn0b, hn1a, hn1b, hn54⟩ := hl3o_n_bds hx hx2 ha1 hax hC1 hC2 rfl hb2
  -- the reciprocal shape and the three faces
  have hr1 : 1 / x ≤ 1 / al := one_div_le_one_div_of_le (by linarith) hax
  have hr2 : 1 / al ≤ 13 / (5 * (x + 1)) := by
    rw [div_le_div_iff₀ (by linarith) (by positivity)]; linarith
  have hrs : 13 / (5 * (x + 1)) ≤ 7 / 8 := by
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]; linarith
  have hx1 : 1 / x ≤ 1 / 2 := by rw [div_le_div_iff₀ hx0 (by norm_num)]; linarith
  have hlow : ∀ n, (n = 25 / 8 ∨ n = 7 / 2) → hl3oG x C n (1 / al) < 0 := by
    intro n hn
    have hn1 : 5 / 2 ≤ n := by rcases hn with h | h <;> norm_num [h]
    have hn2 : n ≤ 7 / 2 := by rcases hn with h | h <;> norm_num [h]
    exact hl3o_neg_between hx hx2 hC35 hC56 hn1 hn2 le_rfl hrs ⟨hr1, hr2⟩
      (hl3o_up hx hx2 hC1 hC56 hn1 hn2) (hl3o_low hn hx hx2 hC35 hC2)
  have hG : ∀ n, 5 / 2 ≤ n → n ≤ 7 / 2 → (al ≤ 5 / 4 → 25 / 8 ≤ n) → hl3oG x C n (1 / al) < 0 := by
    intro n hn1 hn2 hn3
    have h72 := hlow (7 / 2) (Or.inr rfl)
    rcases le_or_gt al (5 / 4) with ha54 | ha54
    · exact hl3o_G_interp (n₁ := 25 / 8) (n₂ := 7 / 2) (by norm_num) (hn3 ha54) hn2
        (hlow (25 / 8) (Or.inl rfl)) h72
    · have hr45 : 1 / al ≤ 4 / 5 := by
        rw [div_le_div_iff₀ (by linarith) (by norm_num)]; linarith
      have h52 : hl3oG x C (5 / 2) (1 / al) < 0 :=
        hl3o_neg_between hx hx2 hC35 hC56 (by norm_num) (by norm_num) le_rfl (by norm_num)
          ⟨hr1, hr45⟩ (hl3o_up hx hx2 hC1 hC56 (by norm_num) (by norm_num)) (hl3o_mid hx hx2 hC35 hC56)
      exact hl3o_G_interp (n₁ := 5 / 2) (n₂ := 7 / 2) (by norm_num) hn1 hn2 h52 h72
  constructor
  · exact (hF _).trans_lt (hG _ hn0a hn0b fun h => (hn54 h).1)
  · exact (hF _).trans_lt (hG _ hn1a hn1b fun h => (hn54 h).2)

end SmoothedOctagon
