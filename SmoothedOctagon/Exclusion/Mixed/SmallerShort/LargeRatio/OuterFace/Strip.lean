module

public import SmoothedOctagon.Exclusion.Mixed.SmallerShort.LargeRatio.OuterFace
public import SmoothedOctagon.Exclusion.Mixed.SmallerShort.LargeRatio.OuterFace.Strip.Residues

/-!
# Smaller-short window, large ratio: the outer face, beta convexity on the strip

On the strip
`(22x + 20)/55 ≤ α ≤ (2x + 3)/5` with `u = û = u_∞ + J/(β - 1)`, each outer test is
`kη² + lη + m + r/η + s/(η + α + 1)` in `η = β - 1` (`lgr_pfo_g`, `lgr_pfo_2`): `k = q₀, q₀, 5q₀`,
`r = J·U_i` (`U_i` the coefficient of `u` at `β = 1`) and `s = R_i` (`R_T = α(7w₋ - 6)`,
`R₈ = (8/9)R_T + α/9`, `R₂ = α`). The residue signs `U_T > -5/2`, `U₂ > 0`, `R_T > x²/3`
(`lgr_strip_rT`, `lgr_strip_r2`, `lgr_strip_sT`) give the convexity margin
`k + min(r, 0)/(β₀ - 1)³ + s/B₁³ ≥ 0` (`lgr_strip_hk`) of `lgr_chord2`, with
`β - 1 ≥ x - 1` and `B ≤ 2x` on the strip (`lgr_strip_chord_T`, `_8`, `_2`).

The residue signs use the normalized strip coordinate `e = (55α-22x-20)/13`.
Two polynomials have nonnegative coefficients in `X = x - 12/5`.
The duration residue is bounded below by `300 + X³(17-X-X²/5)`,
which is positive for `0 ≤ X ≤ 7` (`Strip/Residues`).

## Main API

* `lgr_strip_chord_T`, `lgr_strip_chord_8`, `lgr_strip_chord_2`.
-/

@[expose] public section

namespace SmoothedOctagon

theorem lgr_J_nonneg {x : ℝ} (hx : 1 ≤ x) : 0 ≤ lgrJ x := by
  unfold lgrJ
  have : 0 ≤ x - 1 := by linarith
  positivity

/-! ### Partial fractions of the outer tests -/

/-- `Q₀ = M₀S`. -/
noncomputable def lgroQ0 (S a : ℝ) : ℝ := (6 * a ^ 2 + 1) * S
/-- `P₀ = M₀(1/S - S) + 2S - 1`. -/
noncomputable def lgroP0 (S a : ℝ) : ℝ := (6 * a ^ 2 + 1) * (1 / S - S) + 2 * S - 1
/-- `C₀ = M₀² - M₀S + S²`. -/
noncomputable def lgroC0 (S a : ℝ) : ℝ := (6 * a ^ 2 + 1) ^ 2 - (6 * a ^ 2 + 1) * S + S ^ 2
/-- Coefficient of `η` in `W`. -/
noncomputable def lgroWl (S a ui J D1 δ : ℝ) : ℝ :=
  ui * δ * (2 * D1 - lgroQ0 S a) + J * δ ^ 2 - δ * lgroP0 S a
/-- Constant term of `W`. -/
noncomputable def lgroWm (S a ui J D1 δ : ℝ) : ℝ :=
  lgroC0 S a - D1 * lgroP0 S a + ui * D1 * (D1 - lgroQ0 S a) + J * δ * (2 * D1 - lgroQ0 S a)
/-- Residue of `W` at `η = 0`. -/
noncomputable def lgroWr (S a J D1 : ℝ) : ℝ := J * D1 * (D1 - lgroQ0 S a)
/-- Constant term of `L`. -/
noncomputable def lgroLm (S a ui J D1 δ : ℝ) : ℝ := ui * (2 * D1 - lgroQ0 S a) + 2 * J * δ - lgroP0 S a
/-- Residue of `L` at `η = 0`. -/
noncomputable def lgroLr (S a J D1 : ℝ) : ℝ := J * (2 * D1 - lgroQ0 S a)

theorem lgr_Wo_pf {S a ui J D1 δ η : ℝ} (hS : S ≠ 0) (hη : η ≠ 0) :
    lgrWo S a (ui + J / η) (D1 + δ * η) = lgrWk ui δ * η ^ 2 + lgroWl S a ui J D1 δ * η +
      lgroWm S a ui J D1 δ + lgroWr S a J D1 / η := by
  unfold lgrWo lgrWk lgroWl lgroWm lgroWr lgroQ0 lgroP0 lgroC0
  field_simp
  ring

theorem lgr_Lo_pf {S a ui J D1 δ η : ℝ} (hS : S ≠ 0) (hη : η ≠ 0) :
    lgrLo S a (ui + J / η) (D1 + δ * η) = lgrLl ui δ * η + lgroLm S a ui J D1 δ +
      lgroLr S a J D1 / η := by
  unfold lgrLo lgrLl lgroLm lgroLr lgroQ0 lgroP0
  field_simp
  ring

/-- `Q = W_k c² - W_l c + W_m - 49α⁴ - W_r/c`: `Q/(49α⁴) = w₋ - 1`. -/
noncomputable def lgroQd (S a ui J D1 δ c : ℝ) : ℝ :=
  lgrWk ui δ * c ^ 2 - lgroWl S a ui J D1 δ * c + lgroWm S a ui J D1 δ - 49 * a ^ 4 -
    lgroWr S a J D1 / c

/-- **The tests `τ = gα/B` in partial fractions** (`g = 7`: `τ = T`; `g = 56/9`: `τ = 8T/9`). -/
theorem lgr_pfo_g {S a c ui J D1 δ η g ℓ : ℝ} (hS : S ≠ 0) (ha : a ≠ 0) (hc : c ≠ 0)
    (hg : g ≠ 0) (hη : η ≠ 0) (hB : c + η ≠ 0) :
    lgrGo S a (c + η) (ui + J / η) (D1 + δ * η) (g * (a / (c + η))) ℓ =
      (lgrWk ui δ / (2 * (49 * a ^ 4))) * η ^ 2 +
      (g * a * lgrWk ui δ / (49 * a ^ 4) + 1 / (g * a) + (ui - 1) / a - lgrLl ui δ / (7 * a ^ 2) +
        lgroWl S a ui J D1 δ / (2 * (49 * a ^ 4))) * η +
      (g * a * (lgroWl S a ui J D1 δ - lgrWk ui δ * c) / (49 * a ^ 4) + c / (g * a) +
        ((ui - 1) * c + J) / a + 6 / 7 - lgroLm S a ui J D1 δ / (7 * a ^ 2) + ℓ +
        lgroWm S a ui J D1 δ / (2 * (49 * a ^ 4)) - 3 / 8) +
      (g * a * lgroWr S a J D1 / (c * (49 * a ^ 4)) + J * c / a - lgroLr S a J D1 / (7 * a ^ 2) +
        lgroWr S a J D1 / (2 * (49 * a ^ 4))) / (η - 0) +
      (g * a * lgroQd S a ui J D1 δ c / (49 * a ^ 4) + a) / (η - -c) := by
  unfold lgrGo lgroQd
  rw [lgr_Wo_pf hS hη, lgr_Lo_pf hS hη]
  have hB' : η - -c ≠ 0 := by rw [sub_neg_eq_add, add_comm]; exact hB
  rw [sub_zero]
  field_simp
  ring

/-- **The test `τ = 2` in partial fractions**. -/
theorem lgr_pfo_2 {S a c ui J D1 δ η : ℝ} (hS : S ≠ 0) (ha : a ≠ 0) (hη : η ≠ 0)
    (hB : c + η ≠ 0) :
    lgrGo S a (c + η) (ui + J / η) (D1 + δ * η) 2 (5 / (2 * (7 * (a / (c + η)))) - 11 / 9) =
      (5 / 2 * lgrWk ui δ / (49 * a ^ 4)) * η ^ 2 +
      (5 / 2 * lgroWl S a ui J D1 δ / (49 * a ^ 4) + (ui - 1) / a - lgrLl ui δ / (7 * a ^ 2) +
        5 / (14 * a)) * η +
      (5 / 2 * lgroWm S a ui J D1 δ / (49 * a ^ 4) + ((ui - 1) * c + J) / a -
        lgroLm S a ui J D1 δ / (7 * a ^ 2) + 5 * c / (14 * a) + 6 / 7 - 2 + 1 / 2 - 11 / 9 - 3 / 8) +
      (5 / 2 * lgroWr S a J D1 / (49 * a ^ 4) + J * c / a - lgroLr S a J D1 / (7 * a ^ 2)) / (η - 0) +
      a / (η - -c) := by
  unfold lgrGo
  rw [lgr_Wo_pf hS hη, lgr_Lo_pf hS hη]
  have hB' : η - -c ≠ 0 := by rw [sub_neg_eq_add, add_comm]; exact hB
  rw [sub_zero]
  field_simp
  ring

/-! ### The coefficients at the actual shape -/

/-- `k = δ²u_∞/(98α⁴) = q₀`. -/
noncomputable def lgrokd (x a : ℝ) : ℝ := lgrWk (lgrui x) (2 * (a - x)) / (2 * (49 * a ^ 4))
/-- `l` for `τ = gα/B`. -/
noncomputable def lgrold (x a g : ℝ) : ℝ :=
  g * a * lgrWk (lgrui x) (2 * (a - x)) / (49 * a ^ 4) + 1 / (g * a) + (lgrui x - 1) / a -
    lgrLl (lgrui x) (2 * (a - x)) / (7 * a ^ 2) +
    lgroWl (x + 1) a (lgrui x) (lgrJ x) ((a + 1) ^ 2) (2 * (a - x)) / (2 * (49 * a ^ 4))
/-- `m` for `τ = gα/B`. -/
noncomputable def lgromd (x a g ℓ : ℝ) : ℝ :=
  g * a * (lgroWl (x + 1) a (lgrui x) (lgrJ x) ((a + 1) ^ 2) (2 * (a - x)) -
      lgrWk (lgrui x) (2 * (a - x)) * (a + 1)) / (49 * a ^ 4) + (a + 1) / (g * a) +
    ((lgrui x - 1) * (a + 1) + lgrJ x) / a + 6 / 7 -
    lgroLm (x + 1) a (lgrui x) (lgrJ x) ((a + 1) ^ 2) (2 * (a - x)) / (7 * a ^ 2) + ℓ +
    lgroWm (x + 1) a (lgrui x) (lgrJ x) ((a + 1) ^ 2) (2 * (a - x)) / (2 * (49 * a ^ 4)) - 3 / 8
/-- The residue `r = J·U` at `β = 1` for `τ = gα/B`. -/
noncomputable def lgrord (x a g : ℝ) : ℝ :=
  g * a * lgroWr (x + 1) a (lgrJ x) ((a + 1) ^ 2) / ((a + 1) * (49 * a ^ 4)) +
    lgrJ x * (a + 1) / a - lgroLr (x + 1) a (lgrJ x) ((a + 1) ^ 2) / (7 * a ^ 2) +
    lgroWr (x + 1) a (lgrJ x) ((a + 1) ^ 2) / (2 * (49 * a ^ 4))
/-- The residue `s = (gα)(w₋ - 1) + α` at `β = -α`. -/
noncomputable def lgrosd (x a g : ℝ) : ℝ :=
  g * a * lgroQd (x + 1) a (lgrui x) (lgrJ x) ((a + 1) ^ 2) (2 * (a - x)) (a + 1) / (49 * a ^ 4) + a
/-- `k` for `τ = 2`. -/
noncomputable def lgrok2 (x a : ℝ) : ℝ := 5 / 2 * lgrWk (lgrui x) (2 * (a - x)) / (49 * a ^ 4)
/-- `l` for `τ = 2`. -/
noncomputable def lgrol2 (x a : ℝ) : ℝ :=
  5 / 2 * lgroWl (x + 1) a (lgrui x) (lgrJ x) ((a + 1) ^ 2) (2 * (a - x)) / (49 * a ^ 4) +
    (lgrui x - 1) / a - lgrLl (lgrui x) (2 * (a - x)) / (7 * a ^ 2) + 5 / (14 * a)
/-- `m` for `τ = 2`. -/
noncomputable def lgrom2 (x a : ℝ) : ℝ :=
  5 / 2 * lgroWm (x + 1) a (lgrui x) (lgrJ x) ((a + 1) ^ 2) (2 * (a - x)) / (49 * a ^ 4) +
    ((lgrui x - 1) * (a + 1) + lgrJ x) / a -
    lgroLm (x + 1) a (lgrui x) (lgrJ x) ((a + 1) ^ 2) (2 * (a - x)) / (7 * a ^ 2) +
    5 * (a + 1) / (14 * a) + 6 / 7 - 2 + 1 / 2 - 11 / 9 - 3 / 8
/-- The residue `r = J·U₂` at `β = 1` for `τ = 2`. -/
noncomputable def lgror2 (x a : ℝ) : ℝ :=
  5 / 2 * lgroWr (x + 1) a (lgrJ x) ((a + 1) ^ 2) / (49 * a ^ 4) + lgrJ x * (a + 1) / a -
    lgroLr (x + 1) a (lgrJ x) ((a + 1) ^ 2) / (7 * a ^ 2)

/-- The outer tests with `u = û` as functions of `β`, `τ = gα/B`. -/
theorem lgr_Og_pf {x a b g ℓ : ℝ} (hx : 1 < x) (ha : 0 < a) (hb : 1 < b) (hg : g ≠ 0) :
    ssF x b a (ssUhat x b) (1 / 7) (g * ssRA a b) ℓ (1 / 2) =
      lgrokd x a * (b - 1) ^ 2 + lgrold x a g * (b - 1) + lgromd x a g ℓ +
      lgrord x a g / ((b - 1) - 0) + lgrosd x a g / ((b - 1) - -(a + 1)) := by
  have hx0 : 0 < x := by linarith
  have hB : 0 < a + b := by linarith
  have e : ssF x b a (ssUhat x b) (1 / 7) (g * ssRA a b) ℓ (1 / 2) =
      lgrGo (x + 1) a ((a + 1) + (b - 1)) (lgrui x + lgrJ x / (b - 1))
        ((a + 1) ^ 2 + 2 * (a - x) * (b - 1)) (g * (a / ((a + 1) + (b - 1)))) ℓ := by
    rw [lgr_out_F hx0 ha hB, lgr_uhat_pole hx hb, lgr_Dg_pole]
    have e1 : (a + 1) + (b - 1) = a + b := by ring
    rw [e1]; rfl
  rw [e, lgr_pfo_g (by linarith) ha.ne' (by linarith) hg (by linarith : b - 1 ≠ 0) (by linarith)]
  unfold lgrokd lgrold lgromd lgrord lgrosd
  ring

theorem lgr_OTs_pf {x a b : ℝ} (hx : 1 < x) (ha : 0 < a) (hb : 1 < b) :
    lgrOT x a b (ssUhat x b) = lgrokd x a * (b - 1) ^ 2 + lgrold x a 7 * (b - 1) + lgromd x a 7 0 +
      lgrord x a 7 / ((b - 1) - 0) + lgrosd x a 7 / ((b - 1) - -(a + 1)) :=
  lgr_Og_pf hx ha hb (by norm_num)

theorem lgr_O8s_pf {x a b : ℝ} (hx : 1 < x) (ha : 0 < a) (hb : 1 < b) :
    lgrO8 x a b (ssUhat x b) = lgrokd x a * (b - 1) ^ 2 + lgrold x a (56 / 9) * (b - 1) +
      lgromd x a (56 / 9) (-1 / 9) + lgrord x a (56 / 9) / ((b - 1) - 0) +
      lgrosd x a (56 / 9) / ((b - 1) - -(a + 1)) := by
  rw [← lgr_Og_pf hx ha hb (by norm_num)]
  unfold lgrO8
  congr 1
  ring

theorem lgr_O2s_pf {x a b : ℝ} (hx : 1 < x) (ha : 0 < a) (hb : 1 < b) :
    lgrO2 x a b (ssUhat x b) = lgrok2 x a * (b - 1) ^ 2 + lgrol2 x a * (b - 1) + lgrom2 x a +
      lgror2 x a / ((b - 1) - 0) + a / ((b - 1) - -(a + 1)) := by
  have hx0 : 0 < x := by linarith
  have hB : 0 < a + b := by linarith
  have e : lgrO2 x a b (ssUhat x b) =
      lgrGo (x + 1) a ((a + 1) + (b - 1)) (lgrui x + lgrJ x / (b - 1))
        ((a + 1) ^ 2 + 2 * (a - x) * (b - 1)) 2
        (5 / (2 * (7 * (a / ((a + 1) + (b - 1))))) - 11 / 9) := by
    unfold lgrO2 ssRA
    rw [lgr_out_F hx0 ha hB, lgr_uhat_pole hx hb, lgr_Dg_pole]
    have e1 : (a + 1) + (b - 1) = a + b := by ring
    rw [e1]
  rw [e, lgr_pfo_2 (by linarith) ha.ne' (by linarith : b - 1 ≠ 0) (by linarith)]
  unfold lgrok2 lgrol2 lgrom2 lgror2
  ring

/-! ### The residue signs on the strip -/

theorem lgr_strip_rT {x a : ℝ} (hx : 12 / 5 ≤ x) (hx9 : x ≤ 9) (ha : (22 * x + 20) / 55 ≤ a)
    (ham : a ≤ (2 * x + 3) / 5) : -(5 / 2) * lgrJ x ≤ lgrord x a 7 := by
  have hx1 : 0 < x - 1 := by linarith
  have ha0 : 0 < a := by linarith
  have hM : 0 < (x + 1) * (35 * x + 13) := by nlinarith
  have e : lgrord x a 7 + 5 / 2 * lgrJ x = lgrJ x * lgrQTf x a / (98 * a ^ 4) := by
    unfold lgrord lgroWr lgroLr lgroQ0 lgrJ lgrQTf
    field_simp
    ring
  have hP := S0Outer.Residues.QT_pos hx hx9 ha ham
  have hJ : 0 ≤ lgrJ x := lgr_J_nonneg (by linarith)
  have : 0 ≤ lgrJ x * lgrQTf x a / (98 * a ^ 4) := by positivity
  linarith

theorem lgr_strip_r2 {x a : ℝ} (hx : 12 / 5 ≤ x) (_hx9 : x ≤ 9) (ha : (22 * x + 20) / 55 ≤ a)
    (ham : a ≤ (2 * x + 3) / 5) : 0 ≤ lgror2 x a := by
  have hx1 : 0 < x - 1 := by linarith
  have ha0 : 0 < a := by linarith
  have e : lgror2 x a = lgrJ x * lgrQ2f x a / (98 * a ^ 4) := by
    unfold lgror2 lgroWr lgroLr lgroQ0 lgrJ lgrQ2f
    field_simp
    ring
  have hP := S0Outer.Residues.Q2_pos hx ha ham
  have hJ : 0 ≤ lgrJ x := lgr_J_nonneg (by linarith)
  rw [e]; positivity

theorem lgr_strip_sT {x a : ℝ} (hx : 12 / 5 ≤ x) (_hx9 : x ≤ 9) (ha : (22 * x + 20) / 55 ≤ a)
    (ham : a ≤ (2 * x + 3) / 5) : x ^ 2 / 3 ≤ lgrosd x a 7 := by
  have hx1 : 0 < x - 1 := by linarith
  have ha0 : 0 < a := by linarith
  have hM : 0 < (x + 1) * (35 * x + 13) := by nlinarith
  have e : lgrosd x a 7 - x ^ 2 / 3 = lgrSRf x a / (84 * a ^ 3 * (x + 1) * (35 * x + 13)) := by
    unfold lgrosd lgroQd lgrWk lgroWl lgroWm lgroWr lgroQ0 lgroP0 lgroC0 lgrui lgrJ lgrSRf
    field_simp
    ring
  have hP := S0Outer.Residues.SR_pos hx ha ham
  have : 0 ≤ lgrSRf x a / (84 * a ^ 3 * (x + 1) * (35 * x + 13)) := by positivity
  linarith

theorem lgr_strip_r8 {x a : ℝ} (hx : 12 / 5 ≤ x) (ha : 1 ≤ a) : lgrord x a 7 ≤ lgrord x a (56 / 9) := by
  have ha0 : 0 < a := by linarith
  have hJ : 0 ≤ lgrJ x := lgr_J_nonneg (by linarith)
  have hD : (a + 1) ^ 2 - (6 * a ^ 2 + 1) * (x + 1) ≤ 0 := by nlinarith
  have e : lgrord x a (56 / 9) - lgrord x a 7 =
      7 / 9 * a * lgrJ x * (a + 1) ^ 2 * ((6 * a ^ 2 + 1) * (x + 1) - (a + 1) ^ 2) /
        ((a + 1) * (49 * a ^ 4)) := by
    unfold lgrord lgroWr lgroQ0
    field_simp
    ring
  have : 0 ≤ 7 / 9 * a * lgrJ x * (a + 1) ^ 2 * ((6 * a ^ 2 + 1) * (x + 1) - (a + 1) ^ 2) /
      ((a + 1) * (49 * a ^ 4)) := by
    apply div_nonneg _ (by positivity)
    apply mul_nonneg (by positivity) (by linarith)
  linarith

theorem lgr_osd8 (x a : ℝ) (ha : a ≠ 0) : lgrosd x a (56 / 9) = 8 / 9 * lgrosd x a 7 + a / 9 := by
  unfold lgrosd; field_simp; ring

/-! ### The chord bounds on the strip -/

/-- The convexity margin: `k + min(r, 0)/(β₀ - 1)³ + s/B₁³ ≥ 0` once `r ≥ -(5/2)J`,
`s ≥ σ ≥ 0`, `β₀ - 1 ≥ x - 1`, `B₁ ≤ 2x` and `σ/(2x)³ ≥ (5/2)J/(x - 1)³`. -/
theorem lgr_strip_hk {k r s J σ x b₀ B₁ : ℝ} (hk : 0 ≤ k) (hJ : 0 ≤ J) (hx1 : 0 < x - 1)
    (hb₀ : x - 1 ≤ b₀) (hB₁ : 0 < B₁) (hB₁x : B₁ ≤ 2 * x) (hr : -(5 / 2) * J ≤ r) (hs : σ ≤ s)
    (hσ : 0 ≤ σ) (key : 0 ≤ -(5 / 2) * J / (x - 1) ^ 3 + σ / (2 * x) ^ 3) :
    0 ≤ k + min r 0 / b₀ ^ 3 + s / B₁ ^ 3 := by
  have hx0 : 0 < x := by linarith
  have hb0 : 0 < b₀ := by linarith
  have h1 : -(5 / 2) * J / (x - 1) ^ 3 ≤ min r 0 / b₀ ^ 3 := by
    have hm : -(5 / 2) * J ≤ min r 0 := le_min hr (by linarith)
    have hm0 : min r 0 ≤ 0 := min_le_right _ _
    have hp : (x - 1) ^ 3 ≤ b₀ ^ 3 := pow_le_pow_left₀ hx1.le hb₀ 3
    have s1 : min r 0 / (x - 1) ^ 3 ≤ min r 0 / b₀ ^ 3 := by
      rw [div_le_div_iff₀ (by positivity) (by positivity)]
      nlinarith
    have s2 : -(5 / 2) * J / (x - 1) ^ 3 ≤ min r 0 / (x - 1) ^ 3 :=
      div_le_div_of_nonneg_right hm (by positivity)
    linarith
  have h2 : σ / (2 * x) ^ 3 ≤ s / B₁ ^ 3 := by
    have hp : B₁ ^ 3 ≤ (2 * x) ^ 3 := pow_le_pow_left₀ hB₁.le hB₁x 3
    have s1 : σ / (2 * x) ^ 3 ≤ σ / B₁ ^ 3 := div_le_div_of_nonneg_left hσ (by positivity) hp
    have s2 : σ / B₁ ^ 3 ≤ s / B₁ ^ 3 := div_le_div_of_nonneg_right hs (by positivity)
    linarith
  linarith

theorem lgr_J_ratio {x : ℝ} (hx : 1 < x) :
    lgrJ x / (x - 1) ^ 3 = 7 / (4 * (x + 1) * (35 * x + 13)) := by
  have : x - 1 ≠ 0 := by linarith
  have : (x + 1) * (35 * x + 13) ≠ 0 := by nlinarith
  unfold lgrJ; field_simp

/-- **Beta convexity on the strip, `τ = T`**: the test is at most the larger of its values at
`β = x + (3/5)(α - 1)` and at `β₁` (`lgr_chord2`). -/
theorem lgr_strip_chord_T {x a b b₁ : ℝ} (hx : 12 / 5 ≤ x) (hx9 : x ≤ 9)
    (ha : (22 * x + 20) / 55 ≤ a) (ham : a ≤ (2 * x + 3) / 5) (hb : x + 3 / 5 * (a - 1) ≤ b)
    (hbb : b ≤ b₁) (hb₁ : b₁ + a ≤ 2 * x) :
    lgrOT x a b (ssUhat x b) ≤ max (lgrOT x a (x + 3 / 5 * (a - 1)) (ssUhat x (x + 3 / 5 * (a - 1))))
      (lgrOT x a b₁ (ssUhat x b₁)) := by
  have hx1 : 1 < x := by linarith
  have ha1 : 1 ≤ a := by linarith
  have ha0 : 0 < a := by linarith
  have hb0 : 1 < x + 3 / 5 * (a - 1) := by linarith
  rw [lgr_OTs_pf hx1 ha0 (by linarith), lgr_OTs_pf hx1 ha0 hb0, lgr_OTs_pf hx1 ha0 (by linarith)]
  have hsT := lgr_strip_sT hx hx9 ha ham
  apply lgr_chord2 (by linarith) (by linarith) (by linarith) (by linarith)
    (by nlinarith)
  have e : b₁ - 1 - -(a + 1) = b₁ + a := by ring
  rw [e]
  have hJ : 0 ≤ lgrJ x := lgr_J_nonneg (by linarith)
  apply lgr_strip_hk (J := lgrJ x) (σ := x ^ 2 / 3) (by unfold lgrokd lgrWk lgrui; positivity) hJ
    (by linarith) (by linarith) (by linarith) hb₁ (lgr_strip_rT hx hx9 ha ham) hsT (by positivity)
  have e2 : -(5 / 2) * lgrJ x / (x - 1) ^ 3 = -(5 / 2) * (lgrJ x / (x - 1) ^ 3) := by ring
  rw [e2, lgr_J_ratio hx1]
  have hM : 0 < (x + 1) * (35 * x + 13) := by nlinarith
  rw [show x ^ 2 / 3 / (2 * x) ^ 3 = 1 / (24 * x) by field_simp; ring]
  have : 35 / (8 * ((x + 1) * (35 * x + 13))) ≤ 1 / (24 * x) := by
    rw [div_le_div_iff₀ (by positivity) (by positivity)]; nlinarith
  have e3 : -(5 / 2) * (7 / (4 * (x + 1) * (35 * x + 13))) = -(35 / (8 * ((x + 1) * (35 * x + 13)))) := by
    field_simp; ring
  linarith

/-- **Beta convexity on the strip, `τ = 8T/9`**: the test is at most the larger of its values at
`β = x + (3/5)(α - 1)` and at `β₁` (`lgr_chord2`). -/
theorem lgr_strip_chord_8 {x a b b₁ : ℝ} (hx : 12 / 5 ≤ x) (hx9 : x ≤ 9)
    (ha : (22 * x + 20) / 55 ≤ a) (ham : a ≤ (2 * x + 3) / 5) (hb : x + 3 / 5 * (a - 1) ≤ b)
    (hbb : b ≤ b₁) (hb₁ : b₁ + a ≤ 2 * x) :
    lgrO8 x a b (ssUhat x b) ≤ max (lgrO8 x a (x + 3 / 5 * (a - 1)) (ssUhat x (x + 3 / 5 * (a - 1))))
      (lgrO8 x a b₁ (ssUhat x b₁)) := by
  have hx1 : 1 < x := by linarith
  have ha1 : 1 ≤ a := by linarith
  have ha0 : 0 < a := by linarith
  have hb0 : 1 < x + 3 / 5 * (a - 1) := by linarith
  rw [lgr_O8s_pf hx1 ha0 (by linarith), lgr_O8s_pf hx1 ha0 hb0, lgr_O8s_pf hx1 ha0 (by linarith)]
  have hsT := lgr_strip_sT hx hx9 ha ham
  have hs8 : 8 * x ^ 2 / 27 ≤ lgrosd x a (56 / 9) := by rw [lgr_osd8 x a ha0.ne']; linarith
  apply lgr_chord2 (by linarith) (by linarith) (by linarith) (by linarith) (by nlinarith)
  have e : b₁ - 1 - -(a + 1) = b₁ + a := by ring
  rw [e]
  have hJ : 0 ≤ lgrJ x := lgr_J_nonneg (by linarith)
  apply lgr_strip_hk (J := lgrJ x) (σ := 8 * x ^ 2 / 27) (by unfold lgrokd lgrWk lgrui; positivity)
    hJ (by linarith) (by linarith) (by linarith) hb₁
    ((lgr_strip_rT hx hx9 ha ham).trans (lgr_strip_r8 hx ha1)) hs8 (by positivity)
  have e2 : -(5 / 2) * lgrJ x / (x - 1) ^ 3 = -(5 / 2) * (lgrJ x / (x - 1) ^ 3) := by ring
  rw [e2, lgr_J_ratio hx1]
  have hM : 0 < (x + 1) * (35 * x + 13) := by nlinarith
  rw [show 8 * x ^ 2 / 27 / (2 * x) ^ 3 = 1 / (27 * x) by field_simp; ring]
  have : 35 / (8 * ((x + 1) * (35 * x + 13))) ≤ 1 / (27 * x) := by
    rw [div_le_div_iff₀ (by positivity) (by positivity)]; nlinarith
  have e3 : -(5 / 2) * (7 / (4 * (x + 1) * (35 * x + 13))) = -(35 / (8 * ((x + 1) * (35 * x + 13)))) := by
    field_simp; ring
  linarith

/-- **Beta convexity on the strip, `τ = 2`**: the test is at most the larger of its values at
`β = x + (3/5)(α - 1)` and at `β₁` (`lgr_chord2`). -/
theorem lgr_strip_chord_2 {x a b b₁ : ℝ} (hx : 12 / 5 ≤ x) (hx9 : x ≤ 9)
    (ha : (22 * x + 20) / 55 ≤ a) (ham : a ≤ (2 * x + 3) / 5) (hb : x + 3 / 5 * (a - 1) ≤ b)
    (hbb : b ≤ b₁) :
    lgrO2 x a b (ssUhat x b) ≤ max (lgrO2 x a (x + 3 / 5 * (a - 1)) (ssUhat x (x + 3 / 5 * (a - 1))))
      (lgrO2 x a b₁ (ssUhat x b₁)) := by
  have hx1 : 1 < x := by linarith
  have ha0 : 0 < a := by linarith
  have hb0 : 1 < x + 3 / 5 * (a - 1) := by linarith
  rw [lgr_O2s_pf hx1 ha0 (by linarith), lgr_O2s_pf hx1 ha0 hb0, lgr_O2s_pf hx1 ha0 (by linarith)]
  apply lgr_chord2 (by linarith) (by linarith) (by linarith) (by linarith) ha0.le
  have hr := lgr_strip_r2 hx hx9 ha ham
  rw [min_eq_right hr, zero_div, add_zero]
  have hk : 0 ≤ lgrok2 x a := by unfold lgrok2 lgrWk lgrui; positivity
  have : 0 < b₁ - 1 - -(a + 1) := by linarith
  positivity

end SmoothedOctagon
