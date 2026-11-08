module

public import SmoothedOctagon.Exclusion.Mixed.ShortHand.Heavy.S4HandW6a

/-!
# Gate S4, hand proof of W6: terminal concavity

`archive/lighter-proofs/SHORT_CASIMIR_TERMINAL_CONCAVITY.md` §§3-5. On `x = 13/6`, `e = 13/5`,
`r = 13d ∈ [0, 13/19]`, the terminal source `hl46W6F` (`S4HandW6a`) has a positive third
derivative (note (14), from the six elementary terms (15)-(21) and the exact logarithm), so its
second derivative increases; at `r = 13/19` it is negative (exact rational value), hence `Ψ` is
concave in `d` on the whole line.

Route: the terminal value of `Ψ_rr` at `r = 13/19` is evaluated exactly (`norm_num`) instead of
through the six rounded contributions of note (23).

## Main API

`hl46_W6`.
-/

@[expose] public section

namespace SmoothedOctagon

open Set Real

/-! ### Bounds on `[0, 13/19]` (note (12), (13), (19), (20)) -/

theorem hl46_w6_U_bounds {r : ℝ} (hr : 0 ≤ r) (hr' : r ≤ 13 / 19) :
    379 / 500 ≤ hl46W6U r ∧ hl46W6U r ≤ 19 / 25 ∧ -7 / 5000 ≤ hl46W6U1 r ∧
      hl46W6U1 r ≤ -11 / 10000 ∧ 7 / 20000 ≤ hl46W6U2 r ∧ hl46W6U2 r ≤ 1 / 2500 ∧
      -1 / 15000 ≤ hl46W6U3 r ∧ hl46W6U3 r ≤ -1 / 24000 := by
  have h7 : (7 : ℝ) ≤ r + 7 := by linarith
  have h77 : r + 7 ≤ 77 / 10 := by linarith
  have p2 : (49 : ℝ) ≤ (r + 7) ^ 2 := by nlinarith
  have p2' : (r + 7) ^ 2 ≤ (77 / 10) ^ 2 := pow_le_pow_left₀ (by linarith) h77 2
  have p3 : (7 : ℝ) ^ 3 ≤ (r + 7) ^ 3 := pow_le_pow_left₀ (by norm_num) h7 3
  have p3' : (r + 7) ^ 3 ≤ (77 / 10) ^ 3 := pow_le_pow_left₀ (by linarith) h77 3
  have p4 : (7 : ℝ) ^ 4 ≤ (r + 7) ^ 4 := pow_le_pow_left₀ (by norm_num) h7 4
  have p4' : (r + 7) ^ 4 ≤ (77 / 10) ^ 4 := pow_le_pow_left₀ (by linarith) h77 4
  have hU1 : ∀ y ∈ Icc (0 : ℝ) (13 / 19), hl46W6U1 y ≤ 0 := by
    intro y hy
    unfold hl46W6U1
    have : 0 ≤ 160867 / 6319248 / (y + 7) ^ 2 := by have := hy.1; positivity
    have : (2 * y - 7) / 8112 ≤ 0 := by
      apply div_nonpos_of_nonpos_of_nonneg _ (by norm_num); linarith [hy.2]
    linarith
  have m1 : hl46W6U r ≤ hl46W6U 0 :=
    hl46_anti_of (fun y hy => (hl46_j3_U hy.1).1) hU1 le_rfl hr hr'
  have m2 : hl46W6U (13 / 19) ≤ hl46W6U r :=
    hl46_anti_of (fun y hy => (hl46_j3_U hy.1).1) hU1 hr hr' le_rfl
  refine ⟨le_trans (by norm_num [hl46W6U]) m2, m1.trans (by norm_num [hl46W6U]), ?_, ?_, ?_, ?_,
    ?_, ?_⟩
  · unfold hl46W6U1
    have : 160867 / 6319248 / (r + 7) ^ 2 ≤ 160867 / 6319248 / 49 :=
      div_le_div_of_nonneg_left (by norm_num) (by norm_num) p2
    have : (2 * 0 - 7) / 8112 ≤ (2 * r - 7) / 8112 := by linarith
    norm_num at *
    linarith
  · unfold hl46W6U1
    have : 160867 / 6319248 / (77 / 10) ^ 2 ≤ 160867 / 6319248 / (r + 7) ^ 2 :=
      div_le_div_of_nonneg_left (by norm_num) (by positivity) p2'
    have : (2 * r - 7) / 8112 ≤ (2 * (13 / 19) - 7) / 8112 := by linarith
    norm_num at *
    linarith
  · unfold hl46W6U2
    have : 2 * (160867 / 6319248) / (77 / 10) ^ 3 ≤ 2 * (160867 / 6319248) / (r + 7) ^ 3 :=
      div_le_div_of_nonneg_left (by norm_num) (by positivity) p3'
    norm_num at *
    linarith
  · unfold hl46W6U2
    have : 2 * (160867 / 6319248) / (r + 7) ^ 3 ≤ 2 * (160867 / 6319248) / 7 ^ 3 :=
      div_le_div_of_nonneg_left (by norm_num) (by norm_num) p3
    norm_num at *
    linarith
  · unfold hl46W6U3
    have h : 6 * (160867 / 6319248) / (r + 7) ^ 4 ≤ 6 * (160867 / 6319248) / 7 ^ 4 :=
      div_le_div_of_nonneg_left (by norm_num) (by norm_num) p4
    have c : (6 * (160867 / 6319248) : ℝ) / 7 ^ 4 ≤ 1 / 15000 := by norm_num
    rw [neg_div ((r + 7) ^ 4)]
    linarith
  · unfold hl46W6U3
    have : 6 * (160867 / 6319248) / (77 / 10) ^ 4 ≤ 6 * (160867 / 6319248) / (r + 7) ^ 4 :=
      div_le_div_of_nonneg_left (by norm_num) (by positivity) p4'
    rw [neg_div]
    norm_num at *
    linarith

/-! ### The six terms of the third derivative (note (15)-(21)) -/

theorem hl46_w6_grpG {U U1 U2 U3 : ℝ} (hU : 379 / 500 ≤ U) (hU' : U ≤ 19 / 25) (h1 : U1 ≤ 0)
    (h2 : 0 ≤ U2) (h3 : -1 / 15000 ≤ U3) (h3' : U3 ≤ 0) :
    -1 / 60000 ≤ -47045881 / 60840000 * (U3 * U + 3 * (U2 * U1) + 3 * (U1 * U2) + U * U3) +
      83616986 / 60840000 * U3 := by
  have e : -47045881 / 60840000 * (U3 * U + 3 * (U2 * U1) + 3 * (U1 * U2) + U * U3) +
      83616986 / 60840000 * U3 =
      (-47045881 / 30420000 * U + 83616986 / 60840000) * U3 +
        6 * (47045881 / 60840000) * (-(U1 * U2)) := by ring
  rw [e]
  have c0 : 0 ≤ -47045881 / 30420000 * U + 83616986 / 60840000 := by linarith
  have c1 : -47045881 / 30420000 * U + 83616986 / 60840000 ≤ 1 / 4 := by linarith
  have a : (1 / 4) * (-1 / 15000) ≤ (-47045881 / 30420000 * U + 83616986 / 60840000) * U3 := by
    nlinarith
  have b : 0 ≤ -(U1 * U2) := by nlinarith
  nlinarith

theorem hl46_w6_grpA {U U1 U2 U3 A : ℝ} (hU : 379 / 500 ≤ U) (h1 : U1 ≤ 0) (h2 : 0 ≤ U2)
    (h3 : U3 ≤ 0) (hA : 5 ≤ A) (hA' : A ≤ 57 / 10) :
    (227 / 18 * U3 + 0) * (1 / A) + 3 * ((227 / 18 * U2 + 0) * (-1 / A ^ 2)) +
        3 * ((227 / 18 * U1 + 0) * (2 * 1 ^ 2 / A ^ 3)) +
        (227 / 18 * U + -2077 / 576) * (-(6 * 1 ^ 3) / A ^ 4) ≤ -(21 / 625) := by
  have hA0 : 0 < A := by linarith
  have t1 : (227 / 18 * U3 + 0) * (1 / A) ≤ 0 :=
    mul_nonpos_of_nonpos_of_nonneg (by linarith) (by positivity)
  have t2 : (227 / 18 * U2 + 0) * (-1 / A ^ 2) ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos (by linarith) (div_nonpos_of_nonpos_of_nonneg (by norm_num)
      (by positivity))
  have t3 : (227 / 18 * U1 + 0) * (2 * 1 ^ 2 / A ^ 3) ≤ 0 :=
    mul_nonpos_of_nonpos_of_nonneg (by linarith) (by positivity)
  have hP : 119 / 20 ≤ 227 / 18 * U + -2077 / 576 := by linarith
  have hA4 : A ^ 4 ≤ (57 / 10) ^ 4 := pow_le_pow_left₀ hA0.le hA' 4
  have q : 6 / (57 / 10) ^ 4 ≤ 6 / A ^ 4 := div_le_div_of_nonneg_left (by norm_num) (by positivity) hA4
  have e : (227 / 18 * U + -2077 / 576) * (-(6 * 1 ^ 3) / A ^ 4) =
      -((227 / 18 * U + -2077 / 576) * (6 / A ^ 4)) := by ring
  have t4 := mul_le_mul hP q (by norm_num) (by linarith)
  norm_num at t4
  rw [e]
  linarith

theorem hl46_w6_grpB {U U1 U2 U3 B : ℝ} (hU : 379 / 500 ≤ U) (hU' : U ≤ 19 / 25) (h1 : U1 ≤ 0)
    (h2 : 0 ≤ U2) (h3 : U3 ≤ 0) (hB : 95 ≤ B) :
    (98342375 / 457919 * U3 + 0) * (1 / B) + 3 * ((98342375 / 457919 * U2 + 0) * (-11 / B ^ 2)) +
        3 * ((98342375 / 457919 * U1 + 0) * (2 * 11 ^ 2 / B ^ 3)) +
        (98342375 / 457919 * U + -20425821365 / 87920448) * (-(6 * 11 ^ 3) / B ^ 4) ≤ 7 / 1000 := by
  have hB0 : 0 < B := by linarith
  have t1 : (98342375 / 457919 * U3 + 0) * (1 / B) ≤ 0 :=
    mul_nonpos_of_nonpos_of_nonneg (by linarith) (by positivity)
  have t2 : (98342375 / 457919 * U2 + 0) * (-11 / B ^ 2) ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos (by linarith) (div_nonpos_of_nonpos_of_nonneg (by norm_num)
      (by positivity))
  have t3 : (98342375 / 457919 * U1 + 0) * (2 * 11 ^ 2 / B ^ 3) ≤ 0 :=
    mul_nonpos_of_nonpos_of_nonneg (by linarith) (by positivity)
  have hQ : -70 ≤ 98342375 / 457919 * U + -20425821365 / 87920448 := by linarith
  have hQ' : 98342375 / 457919 * U + -20425821365 / 87920448 ≤ 0 := by linarith
  have hB4 : (95 : ℝ) ^ 4 ≤ B ^ 4 := pow_le_pow_left₀ (by norm_num) hB 4
  have q : 6 * 11 ^ 3 / B ^ 4 ≤ (6 * 11 ^ 3 : ℝ) / 95 ^ 4 :=
    div_le_div_of_nonneg_left (by norm_num) (by norm_num) hB4
  have q0 : 0 ≤ 6 * 11 ^ 3 / B ^ 4 := by positivity
  have e : (98342375 / 457919 * U + -20425821365 / 87920448) * (-(6 * 11 ^ 3) / B ^ 4) =
      (-(98342375 / 457919 * U + -20425821365 / 87920448)) * (6 * 11 ^ 3 / B ^ 4) := by ring
  have t4 := mul_le_mul (by linarith : -(98342375 / 457919 * U + -20425821365 / 87920448) ≤ 70) q
    q0 (by norm_num)
  have c : (70 : ℝ) * (6 * 11 ^ 3 / 95 ^ 4) ≤ 7 / 1000 := by norm_num
  rw [e]
  linarith

theorem hl46_w6_grpC {f f1 f2 f3 h h1 h2 h3 : ℝ} (hf' : f ≤ 14000) (hf1 : -600 ≤ f1)
    (hf2 : 0 ≤ f2) (hf3 : f3 ≤ 0) (hh : 0 ≤ h) (hh1 : h1 ≤ 0)
    (hh2 : -(6 / 10 ^ 7) ≤ h2) (hh2' : h2 ≤ 0) (hh3 : 0 ≤ h3) (hh3' : h3 ≤ 21 / 10 ^ 8) :
    f3 * h + 3 * (f2 * h1) + 3 * (f1 * h2) + f * h3 ≤ 21 / 5000 := by
  have t1 : f3 * h ≤ 0 := mul_nonpos_of_nonpos_of_nonneg hf3 hh
  have t2 : f2 * h1 ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hf2 hh1
  have t3 : f1 * h2 ≤ 600 * (6 / 10 ^ 7) := by nlinarith
  have t4 : f * h3 ≤ 14000 * (21 / 10 ^ 8) := mul_le_mul hf' hh3' hh3 (by norm_num)
  norm_num at t3 t4 ⊢
  linarith

theorem hl46_w6_grpL {A B K K' : ℝ} (hA : 5 ≤ A) (hB : 95 ≤ B) (hK : 9025 ≤ K) (hK0 : 0 ≤ K')
    (hK' : K' ≤ 410) :
    2 * 1 ^ 3 / A ^ 3 + 2 * 11 ^ 3 / B ^ 3 - (-(216 * K') / K ^ 2 + 2 * K' ^ 3 / K ^ 3) ≤
      21 / 1000 := by
  have a : 2 * 1 ^ 3 / A ^ 3 ≤ (2 : ℝ) / 5 ^ 3 :=
    div_le_div₀ (by norm_num) (by norm_num) (by norm_num) (pow_le_pow_left₀ (by norm_num) hA 3)
  have b : 2 * 11 ^ 3 / B ^ 3 ≤ (2 * 11 ^ 3 : ℝ) / 95 ^ 3 :=
    div_le_div₀ (by norm_num) le_rfl (by norm_num) (pow_le_pow_left₀ (by norm_num) hB 3)
  have c : 216 * K' / K ^ 2 ≤ (216 * 410 : ℝ) / 9025 ^ 2 :=
    div_le_div₀ (by norm_num) (by linarith) (by norm_num) (pow_le_pow_left₀ (by norm_num) hK 2)
  have d : 0 ≤ 2 * K' ^ 3 / K ^ 3 := by
    have : 0 < K := by linarith
    positivity
  rw [neg_div]
  norm_num at a b c ⊢
  linarith

/-- The building blocks of `1/K` and of `n - mu` on `[0, 13/19]` (note (19), (20)). -/
theorem hl46_w6_C_bounds {r : ℝ} (hr : 0 ≤ r) (hr' : r ≤ 13 / 19) :
    let U := hl46W6U r; let U1 := hl46W6U1 r; let U2 := hl46W6U2 r; let U3 := hl46W6U3 r
    let n := 3690640915 / 249774 + 157928748 / 249774 * r
    let m := 697700705 / 249774 + 394433796 / 249774 * r
    0 ≤ n - m * U ∧ n - m * U ≤ 14000 ∧
      -600 ≤ 157928748 / 249774 - (394433796 / 249774 * U + m * U1) ∧
      157928748 / 249774 - (394433796 / 249774 * U + m * U1) ≤ 0 ∧
      0 ≤ 0 - (0 * U + 2 * (394433796 / 249774 * U1) + m * U2) ∧
      0 - (0 * U + 3 * (0 * U1) + 3 * (394433796 / 249774 * U2) + m * U3) ≤ 0 ∧
      0 ≤ 1 / hl46W6K r ∧ -(72 * r + 360) / hl46W6K r ^ 2 ≤ 0 ∧
      -(6 / 10 ^ 7) ≤ (2 * (72 * r + 360) ^ 2 - 72 * hl46W6K r) / hl46W6K r ^ 3 ∧
      (2 * (72 * r + 360) ^ 2 - 72 * hl46W6K r) / hl46W6K r ^ 3 ≤ 0 ∧
      0 ≤ (432 * (72 * r + 360) * hl46W6K r - 6 * (72 * r + 360) ^ 3) / hl46W6K r ^ 4 ∧
      (432 * (72 * r + 360) * hl46W6K r - 6 * (72 * r + 360) ^ 3) / hl46W6K r ^ 4 ≤
        21 / 10 ^ 8 := by
  intro U U1 U2 U3 n m
  obtain ⟨u0, u0', u1, u1', u2, u2', u3, u3'⟩ := hl46_w6_U_bounds hr hr'
  have hn : 14700 ≤ n ∧ n ≤ 15300 := by constructor <;> (simp only [n]; linarith)
  have hm : 2700 ≤ m ∧ m ≤ 3900 := by constructor <;> (simp only [m]; linarith)
  have hK : 9025 ≤ hl46W6K r := hl46_W6K_pos hr
  have hK' : hl46W6K r ≤ 9289 := by unfold hl46W6K; nlinarith
  have hD : 360 ≤ 72 * r + 360 ∧ 72 * r + 360 ≤ 410 := by constructor <;> linarith
  have hK0 : 0 < hl46W6K r := by linarith
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, by positivity, ?_, ?_, ?_, ?_, ?_⟩
  · nlinarith
  · nlinarith
  · nlinarith
  · nlinarith
  · nlinarith
  · nlinarith
  · exact div_nonpos_of_nonpos_of_nonneg (by linarith) (by positivity)
  · rw [le_div_iff₀ (by positivity)]
    have : (9025 : ℝ) ^ 3 ≤ hl46W6K r ^ 3 := pow_le_pow_left₀ (by norm_num) hK 3
    nlinarith
  · apply div_nonpos_of_nonpos_of_nonneg _ (by positivity)
    nlinarith
  · apply div_nonneg _ (by positivity)
    have e : 432 * (72 * r + 360) * hl46W6K r - 6 * (72 * r + 360) ^ 3 =
        6 * (72 * r + 360) * (72 * hl46W6K r - (72 * r + 360) ^ 2) := by ring
    rw [e]
    have a : 0 ≤ 72 * hl46W6K r - (72 * r + 360) ^ 2 := by nlinarith
    have b : 0 ≤ 6 * (72 * r + 360) := by linarith
    exact mul_nonneg b a
  · rw [div_le_iff₀ (by positivity)]
    have : (9025 : ℝ) ^ 4 ≤ hl46W6K r ^ 4 := pow_le_pow_left₀ (by norm_num) hK 4
    have e : 432 * (72 * r + 360) * hl46W6K r - 6 * (72 * r + 360) ^ 3 =
        6 * (72 * r + 360) * (72 * hl46W6K r - (72 * r + 360) ^ 2) := by ring
    rw [e]
    have a : 72 * hl46W6K r - (72 * r + 360) ^ 2 ≤ 72 * 9289 - 360 ^ 2 := by nlinarith
    have b := mul_le_mul hD.2 a (by nlinarith) (by norm_num)
    nlinarith

/-! ### Concavity on the terminal line -/

/-- A third derivative `≥ 0` on `[a, b]` and `f'' ≤ 0` at `b` make `f` concave there, so `f`
exceeds any `c` below both ends. -/
theorem hl46_concave_of_J3 {f f₁ f₂ f₃ : ℝ → ℝ} {a b c : ℝ}
    (hJ : ∀ x ∈ Icc a b, HL46J3 f f₁ f₂ f₃ x) (h3 : ∀ x ∈ Icc a b, 0 ≤ f₃ x) (hb2 : f₂ b ≤ 0)
    (ha : c < f a) (hb : c < f b) {x : ℝ} (hx : x ∈ Icc a b) : c < f x :=
  hl46_concave_lt (fun _ hy => (hJ _ hy).toJ)
    (fun _ hy => (hl46_mono_of (fun z hz => (hJ z hz).2.2) h3 hy.1 hy.2 le_rfl).trans hb2) ha hb hx

/-- **W6** (`SHORT_CASIMIR_TERMINAL_CONCAVITY`): at `x = 13/6`, `e = 13/5`, `Ψ` is concave in
`d`, so it exceeds any `c` below both ends. -/
theorem hl46_W6 {c d : ℝ} (hd : 0 ≤ d) (hd' : d ≤ 1 / 19) (h0 : c < hl46PsiC (13 / 6) 0 (13 / 5))
    (h1 : c < hl46PsiC (13 / 6) (1 / 19) (13 / 5)) : c < hl46PsiC (13 / 6) d (13 / 5) := by
  have hJ := fun x (hx : x ∈ Icc (0 : ℝ) (13 / 19)) =>
    HL46J3.add (HL46J3.sub
      (HL46J3.add (HL46J3.const_mul (-47045881 / 60840000)
        (HL46J3.mul (hl46_j3_U hx.1) (hl46_j3_U hx.1)))
        (HL46J3.const_mul (83616986 / 60840000) (hl46_j3_U hx.1)))
      (HL46J3.const_mul (1 / 7) (HL46J3.add (HL46J3.add (HL46J3.add (HL46J3.add
        (HL46J3.const_mul (25 / 66) (hl46_j3_U hx.1))
        (HL46J3.mul (HL46J3.add (HL46J3.const_mul (227 / 18) (hl46_j3_U hx.1))
          (hl46_j3_const (-2077 / 576) x)) (hl46_j3_inv 1 5 (by linarith [hx.1]))))
        (HL46J3.mul (HL46J3.add (HL46J3.const_mul (98342375 / 457919) (hl46_j3_U hx.1))
          (hl46_j3_const (-20425821365 / 87920448) x)) (hl46_j3_inv 11 95 (by linarith [hx.1]))))
        (HL46J3.mul (HL46J3.sub (hl46_j3_aff (3690640915 / 249774) (157928748 / 249774) x)
          (HL46J3.mul (hl46_j3_aff (697700705 / 249774) (394433796 / 249774) x) (hl46_j3_U hx.1)))
          (hl46_j3_invK hx.1)))
        (HL46J3.sub (HL46J3.add (hl46_j3_log 1 5 (by linarith [hx.1]))
          (hl46_j3_log 11 95 (by linarith [hx.1]))) (hl46_j3_logK hx.1)))))
      (hl46_j3_const (-25230529 / 60840000 - 1 / 7 * (-56 / 33 + log 12)) x)
  have e0 := hl46_w6_eq (r := 0) le_rfl
  have e1 := hl46_w6_eq (r := 13 / 19) (by norm_num)
  have ed := hl46_w6_eq (r := 13 * d) (by linarith)
  rw [show (0 : ℝ) / 13 = 0 by norm_num] at e0
  rw [show (13 / 19 : ℝ) / 13 = 1 / 19 by norm_num] at e1
  rw [show 13 * d / 13 = d by ring] at ed
  rw [e0] at h0
  rw [e1] at h1
  rw [ed]
  refine hl46_concave_of_J3 (f := hl46W6F) hJ (fun x hx => ?_) ?_ h0 h1
    ⟨by linarith, by linarith⟩
  · obtain ⟨hx0, hx1⟩ := hx
    obtain ⟨u0, u0', u1, u1', u2, u2', u3, u3'⟩ := hl46_w6_U_bounds hx0 hx1
    obtain ⟨-, f0', f1, f1', f2, f3, k0, k1, k2, k2', k3, k3'⟩ := hl46_w6_C_bounds hx0 hx1
    have G := hl46_w6_grpG (U1 := hl46W6U1 x) (U2 := hl46W6U2 x) u0 u0' (by linarith) (by linarith) u3
      (by linarith)
    have A := hl46_w6_grpA (A := 1 * x + 5) (U1 := hl46W6U1 x) (U2 := hl46W6U2 x)
      (U3 := hl46W6U3 x) u0 (by linarith) (by linarith) (by linarith)
      (by linarith) (by linarith)
    have B := hl46_w6_grpB (B := 11 * x + 95) (U1 := hl46W6U1 x) (U2 := hl46W6U2 x)
      (U3 := hl46W6U3 x) u0 u0' (by linarith) (by linarith) (by linarith)
      (by linarith)
    have C := hl46_w6_grpC f0' f1 f2 f3 k0 k1 k2 k2' k3 k3'
    have L := hl46_w6_grpL (A := 1 * x + 5) (B := 11 * x + 95) (K := hl46W6K x)
      (K' := 72 * x + 360) (by linarith) (by linarith) (hl46_W6K_pos hx0) (by linarith)
      (by linarith)
    have V : 25 / 66 * hl46W6U3 x ≤ 0 := by linarith
    linarith only [G, A, B, C, L, V]
  · norm_num [hl46W6U, hl46W6U1, hl46W6U2, hl46W6K]

end SmoothedOctagon
