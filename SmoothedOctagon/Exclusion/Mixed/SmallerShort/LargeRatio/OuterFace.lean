module

public import SmoothedOctagon.Exclusion.Mixed.SmallerShort.LargeRatio.CentralFace

/-!
# Smaller-short window, large ratio: the outer face, forms and reductions

At the outer scale `q = 1/7` the floor-weighted face value is
`lgrGo S α B u D τ ℓ = (w - 1)τ + 1/τ + (u - 1)B/α + α/B + 6/7 - E_L + ℓ + (w - 3/4)/2` with
`w = W/(49α⁴)`, `E_L = L/(7α²)`, `W = C₀ - DP₀ + uD(D - Q₀)`, `L = u(2D - Q₀) - P₀`,
`M₀ = 6α² + 1`, `Q₀ = M₀S`, `P₀ = M₀(1/S - S) + 2S - 1`, `C₀ = M₀² - M₀S + S²`
(`lgr_out_F`). The three tests are `τ = T = 7r_A`, `8T/9` and `2` (`lgrOT`, `lgrO8`, `lgrO2`).

* **Incoming monotonicity**: the coefficient of `u` is
  `(τ + 1/2)d(d - λS) + 1/r_A - 2d + λS > 0` (`lgr_Cu_pos`, with `d ≤ 51/175`, `λS ≤ 10`,
  `1/r_A ≥ 7/3`, `τ ≤ 3`), so `ū` may be raised (`lgr_OT_mono`, …).
* **Two majorants**: `ū ≤ u_b = (x + 74)/100` (`lgr_ubar_le_ub`) and, on the strip
  `α ≤ m = (2x + 3)/5`, `ū ≤ û` (`lgro_ubar_le_uhat`), both from the common step `lgr_ubar_step`.
* **Beta convexity on the strip**: with `u = û` each test is
  `kη² + lη + m + r/η + s/(η + α + 1)` (`lgr_pfo_g`, `lgr_pfo_2`); the generalised chord bound
  `lgr_chord2` lets the pole at `β = -α` absorb the negative residue at `β = 1`, from
  `U_T > -5/2`, `U₂ > 0` and `R_T > x²/3` (`lgr_strip_chord_T`, …).

The residue signs `U_T > -5/2`, `U₂ > 0` are proved by the uniform coefficient bound (`lgrCov2`) on
the strip
coordinates `X = x - 12/5`, `A = α - α_f(x)`, and `R_T > x²/3` directly at `u = û(-α)`.

## Main API

* `lgrGo`, `lgr_out_F`, `lgrOT`, `lgrO8`, `lgrO2`.
* `lgr_OT_mono`, `lgr_O8_mono`, `lgr_O2_mono`; `lgr_ubar_le_ub`, `lgro_ubar_le_uhat`.
* `lgr_chord2`, `lgrCov2`, `lgr_cov2_pos`.
-/

@[expose] public section

namespace SmoothedOctagon

/-! ### Tools: a chord bound with two compensating poles, and the bivariate cover -/

/-- **The chord bound, second form**: for `f(y) = k y² + l y + m + r/(y - p) + s/(y - q)` on
`[b₀, b₁]` with both poles left of `b₀`, `s ≥ 0` and `k + min(r, 0)/(b₀ - p)³ + s/(b₁ - q)³ ≥ 0`,
`f(y) ≤ max (f b₀) (f b₁)`. -/
theorem lgr_chord2 {k l m r s p q b₀ b₁ y : ℝ} (hp : p < b₀) (hq : q < b₀) (h0 : b₀ ≤ y)
    (h1 : y ≤ b₁) (hs : 0 ≤ s) (hk : 0 ≤ k + min r 0 / (b₀ - p) ^ 3 + s / (b₁ - q) ^ 3) :
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
  have hdd : 0 ≤ k + r / ((b₀ - p) * (y - p) * (b₁ - p)) + s / ((b₀ - q) * (y - q) * (b₁ - q)) := by
    have hprod : (b₀ - p) ^ 3 ≤ (b₀ - p) * (y - p) * (b₁ - p) := by
      have h1' : (b₀ - p) * (b₀ - p) ≤ (b₀ - p) * (y - p) :=
        mul_le_mul_of_nonneg_left (by linarith) hp0.le
      have h2' : (b₀ - p) * (y - p) * (b₀ - p) ≤ (b₀ - p) * (y - p) * (b₁ - p) :=
        mul_le_mul_of_nonneg_left (by linarith) (by positivity)
      nlinarith
    have hprod' : (b₀ - q) * (y - q) * (b₁ - q) ≤ (b₁ - q) ^ 3 := by
      have h1' : (b₀ - q) * (y - q) ≤ (b₁ - q) * (b₁ - q) :=
        mul_le_mul (by linarith) (by linarith) hqy.le hq1.le
      have h2' : (b₀ - q) * (y - q) * (b₁ - q) ≤ (b₁ - q) * (b₁ - q) * (b₁ - q) :=
        mul_le_mul_of_nonneg_right h1' hq1.le
      nlinarith
    have hpos : 0 < (b₀ - p) * (y - p) * (b₁ - p) := by positivity
    have hpos' : 0 < (b₀ - q) * (y - q) * (b₁ - q) := by positivity
    have hs' : s / (b₁ - q) ^ 3 ≤ s / ((b₀ - q) * (y - q) * (b₁ - q)) :=
      div_le_div_of_nonneg_left hs hpos' hprod'
    have hr' : min r 0 / (b₀ - p) ^ 3 ≤ r / ((b₀ - p) * (y - p) * (b₁ - p)) := by
      rcases le_total 0 r with hr0 | hr0
      · rw [min_eq_right hr0, zero_div]; positivity
      · rw [min_eq_left hr0, div_le_div_iff₀ (by positivity) hpos]
        nlinarith
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

/-- **The bivariate cover**: `lgrCov2 P H_A e [p₀, …, pₙ]` asks the bivariate coefficient bound on
each outer piece `[pᵢ, pᵢ₊₁]` (`pₙ₊₁ = e`) after an outer Taylor shift, inner `0 ≤ A ≤ H_A`. -/
def lgrCov2 (P : List (List ℝ)) (HA e : ℝ) : List ℝ → Prop
  | [] => True
  | [p] => 0 < lgrLow2 HA (e - p) (lgrShift2 p P)
  | p :: q :: r => 0 < lgrLow2 HA (q - p) (lgrShift2 p P) ∧ lgrCov2 P HA e (q :: r)

theorem lgr_cov2_pos (P : List (List ℝ)) (HA e : ℝ) :
    ∀ (p : ℝ) (r : List ℝ), lgrCov2 P HA e (p :: r) →
      ∀ X A, p ≤ X → X ≤ e → 0 ≤ A → A ≤ HA → 0 < lgrH2 P X A := by
  have one : ∀ p q X A, 0 < lgrLow2 HA (q - p) (lgrShift2 p P) → p ≤ X → X ≤ q → 0 ≤ A →
      A ≤ HA → 0 < lgrH2 P X A := by
    intro p q X A h h1 h2 h3 h4
    have e : lgrH2 P X A = lgrH2 (lgrShift2 p P) (X - p) A := by
      rw [lgr_H2_shift2]; congr 1; ring
    rw [e]
    exact h.trans_le (lgr_low2_le h3 h4 (by linarith) (by linarith) _)
  intro p r
  induction r generalizing p with
  | nil => intro h X A h1 h2 h3 h4; exact one p e X A h h1 h2 h3 h4
  | cons q r ih =>
    intro h X A h1 h2 h3 h4
    obtain ⟨hq, hr⟩ := h
    rcases le_total X q with hXq | hXq
    · exact one p q X A hq h1 hXq h3 h4
    · exact ih q hr X A hXq h2 h3 h4

/-! ### The outer face value -/

/-- `W = C₀ - DP₀ + uD(D - Q₀)`, so that `w = W/(49α⁴)`. -/
noncomputable def lgrWo (S a u D : ℝ) : ℝ :=
  (6 * a ^ 2 + 1) ^ 2 - (6 * a ^ 2 + 1) * S + S ^ 2 + D ^ 2 * u -
    D * ((6 * a ^ 2 + 1) * (S * (u - 1) + 1 / S) + 2 * S - 1)

/-- `L = 2Du - N₀`, so that `E_L = L/(7α²)`. -/
noncomputable def lgrLo (S a u D : ℝ) : ℝ :=
  2 * D * u - ((6 * a ^ 2 + 1) * (S * (u - 1) + 1 / S) + 2 * S - 1)

/-- **The outer face value** at `q = 1/7`, floor weight `1/2`. -/
noncomputable def lgrGo (S a B u D τ ℓ : ℝ) : ℝ :=
  (lgrWo S a u D / (49 * a ^ 4) - 1) * τ + 1 / τ + (u - 1) * B / a + a / B + 6 / 7 -
    lgrLo S a u D / (7 * a ^ 2) + ℓ + (lgrWo S a u D / (49 * a ^ 4) - 3 / 4) / 2

theorem lgr_Ws_o {x a b u : ℝ} (hx : 0 < x) (ha : 0 < a) :
    ssWs x b a u (1 / 7) = lgrWo (x + 1) a u (ssDg x b a) / (49 * a ^ 4) := by
  unfold ssWs ssA1 ssA2 ssE0 lgrWo
  field_simp
  ring

theorem lgr_ELs_o {x a b u : ℝ} (hx : 0 < x) (ha : 0 < a) :
    ssELs x b a u (1 / 7) = lgrLo (x + 1) a u (ssDg x b a) / (7 * a ^ 2) := by
  unfold ssELs ssA3 ssE0 lgrLo
  field_simp
  ring

/-- **The outer face value** of `ssF` at `q = 1/7`. -/
theorem lgr_out_F {x a b u τ ℓ : ℝ} (hx : 0 < x) (ha : 0 < a) (hB : 0 < a + b) :
    ssF x b a u (1 / 7) τ ℓ (1 / 2) = lgrGo (x + 1) a (a + b) u (ssDg x b a) τ ℓ := by
  unfold ssF
  rw [lgr_Ws_o hx ha, lgr_ELs_o hx ha]
  unfold lgrGo ssRA
  field_simp
  ring

/-- The outer `τ = T = 7r_A` test at `q = 1/7`, with incoming norm `u`. -/
noncomputable def lgrOT (x a b u : ℝ) : ℝ := ssF x b a u (1 / 7) (7 * ssRA a b) 0 (1 / 2)
/-- The outer `τ = 8T/9` test. -/
noncomputable def lgrO8 (x a b u : ℝ) : ℝ :=
  ssF x b a u (1 / 7) (8 * (7 * ssRA a b) / 9) (-1 / 9) (1 / 2)
/-- The outer `τ = 2` test. -/
noncomputable def lgrO2 (x a b u : ℝ) : ℝ :=
  ssF x b a u (1 / 7) 2 (5 / (2 * (7 * ssRA a b)) - 11 / 9) (1 / 2)

/-! ### Incoming monotonicity -/

/-- The coefficient of `u`: `(τ + 1/2)d(d - λS) + B/α - 2d + λS`, `d = D/(7α²)`,
`λS = M₀S/(7α²)`. -/
noncomputable def lgrCu (S a B D τ : ℝ) : ℝ :=
  (τ + 1 / 2) * (D / (7 * a ^ 2)) * (D / (7 * a ^ 2) - (6 * a ^ 2 + 1) * S / (7 * a ^ 2)) + B / a -
    2 * (D / (7 * a ^ 2)) + (6 * a ^ 2 + 1) * S / (7 * a ^ 2)

theorem lgr_Go_affine {S a B u u' D τ ℓ : ℝ} (hS : S ≠ 0) (ha : a ≠ 0) (hτ : τ ≠ 0) :
    lgrGo S a B u' D τ ℓ = lgrGo S a B u D τ ℓ + (u' - u) * lgrCu S a B D τ := by
  unfold lgrGo lgrWo lgrLo lgrCu
  field_simp
  ring

/-- The scalar core of the positivity of `lgrCu`. -/
theorem lgr_Cu_core {d L τ ρ : ℝ} (hτ : 0 < τ) (hτ3 : τ ≤ 3) (hρ : 7 / 3 ≤ ρ) (hL : 0 ≤ L)
    (hL10 : L ≤ 10) (hd : d ≤ 51 / 175) : 0 < (τ + 1 / 2) * d * (d - L) + ρ - 2 * d + L := by
  rcases le_or_gt d 0 with h0 | h0
  · have : 0 ≤ (τ + 1 / 2) * d * (d - L) := by
      have : d - L ≤ 0 := by linarith
      have : 0 ≤ (τ + 1 / 2) * (-d) * (L - d) := by
        apply mul_nonneg (mul_nonneg (by linarith) (by linarith)) (by linarith)
      nlinarith
    linarith
  · have hτd : τ * d ≤ 153 / 175 := by nlinarith
    have h1 : 0 ≤ L * (1 - τ * d) := mul_nonneg hL (by linarith)
    have h2 : L * d ≤ 10 * d := by nlinarith
    have h3 : 0 ≤ (τ + 1 / 2) * d * d := by positivity
    nlinarith

/-- **The coefficient of `u` is positive** on the outer domain (`β ≥ 4α/3`, `β ≥ x ≥ α ≥ 1`,
`x ≥ 12/5`, `x ≤ 9`, `0 < τ ≤ 3`). -/
theorem lgr_Cu_pos {x a b τ : ℝ} (hx : 12 / 5 ≤ x) (hx9 : x ≤ 9) (ha : 1 ≤ a) (hax : a ≤ x)
    (hxb : x ≤ b) (hb43 : 4 * a ≤ 3 * b) (hτ : 0 < τ) (hτ3 : τ ≤ 3) :
    0 < lgrCu (x + 1) a (a + b) (ssDg x b a) τ := by
  have ha0 : 0 < a := by linarith
  have ha2 : 0 < 7 * a ^ 2 := by positivity
  have hD : ssDg x b a ≤ 51 / 25 * a ^ 2 := by
    unfold ssDg
    have : 2 * b * (x - a) ≥ 2 * x * (x - a) := by nlinarith
    nlinarith
  have hd : ssDg x b a / (7 * a ^ 2) ≤ 51 / 175 := by
    rw [div_le_iff₀ ha2]; linarith
  have hL : (6 * a ^ 2 + 1) * (x + 1) / (7 * a ^ 2) ≤ 10 := by
    rw [div_le_iff₀ ha2]; nlinarith
  have hρ : 7 / 3 ≤ (a + b) / a := by rw [le_div_iff₀ ha0]; linarith
  unfold lgrCu
  exact lgr_Cu_core hτ hτ3 hρ (by positivity) hL hd

/-- `T = 7r_A ≤ 3` from `β ≥ 4α/3`. -/
theorem lgr_T_le {a b : ℝ} (ha : 0 < a) (hb43 : 4 * a ≤ 3 * b) : 7 * ssRA a b ≤ 3 := by
  unfold ssRA
  have : 0 < a + b := by linarith
  rw [mul_div_assoc', div_le_iff₀ this]; linarith

theorem lgr_T_pos {a b : ℝ} (ha : 0 < a) (hb : 0 < b) : 0 < 7 * ssRA a b := by
  unfold ssRA; positivity

/-- **Raising the incoming norm**: each outer test increases with `u`. -/
theorem lgr_O_mono {x a b u u' τ ℓ : ℝ} (hx : 12 / 5 ≤ x) (hx9 : x ≤ 9) (ha : 1 ≤ a)
    (hax : a ≤ x) (hxb : x ≤ b) (hb43 : 4 * a ≤ 3 * b) (hτ : 0 < τ) (hτ3 : τ ≤ 3) (hu : u ≤ u') :
    ssF x b a u (1 / 7) τ ℓ (1 / 2) ≤ ssF x b a u' (1 / 7) τ ℓ (1 / 2) := by
  have hx0 : 0 < x := by linarith
  have ha0 : 0 < a := by linarith
  have hB : 0 < a + b := by linarith
  rw [lgr_out_F hx0 ha0 hB, lgr_out_F hx0 ha0 hB,
    lgr_Go_affine (u := u) (u' := u') (by linarith : x + 1 ≠ 0) ha0.ne' hτ.ne']
  have := lgr_Cu_pos hx hx9 ha hax hxb hb43 hτ hτ3
  nlinarith

theorem lgr_OT_mono {x a b u u' : ℝ} (hx : 12 / 5 ≤ x) (hx9 : x ≤ 9) (ha : 1 ≤ a)
    (hax : a ≤ x) (hxb : x ≤ b) (hb43 : 4 * a ≤ 3 * b) (hu : u ≤ u') :
    lgrOT x a b u ≤ lgrOT x a b u' :=
  lgr_O_mono hx hx9 ha hax hxb hb43 (lgr_T_pos (by linarith) (by linarith))
    (lgr_T_le (by linarith) hb43) hu

theorem lgr_O8_mono {x a b u u' : ℝ} (hx : 12 / 5 ≤ x) (hx9 : x ≤ 9) (ha : 1 ≤ a)
    (hax : a ≤ x) (hxb : x ≤ b) (hb43 : 4 * a ≤ 3 * b) (hu : u ≤ u') :
    lgrO8 x a b u ≤ lgrO8 x a b u' := by
  have h1 := lgr_T_pos (a := a) (b := b) (by linarith) (by linarith)
  have h2 := lgr_T_le (a := a) (b := b) (by linarith) hb43
  exact lgr_O_mono hx hx9 ha hax hxb hb43 (by positivity) (by linarith) hu

theorem lgr_O2_mono {x a b u u' : ℝ} (hx : 12 / 5 ≤ x) (hx9 : x ≤ 9) (ha : 1 ≤ a)
    (hax : a ≤ x) (hxb : x ≤ b) (hb43 : 4 * a ≤ 3 * b) (hu : u ≤ u') :
    lgrO2 x a b u ≤ lgrO2 x a b u' :=
  lgr_O_mono hx hx9 ha hax hxb hb43 (by norm_num) (by norm_num) hu

/-! ### Two incoming majorants -/

/-- The common step: `ū ≤ 3/4 + v(x - 1 + κδ)/(β - 1)` once `δ²SM ≤ 96κ x²(x - 1)²`
(`v = 2(x - 1)²/(SM)`, `δ = β - x`). -/
theorem lgr_ubar_step {x b κ : ℝ} (hx : 1 < x) (hxb : x ≤ b)
    (h : (b - x) ^ 2 * ((x + 1) * (35 * x + 13)) ≤ 96 * κ * x ^ 2 * (x - 1) ^ 2) :
    ssUbar x b ≤ 3 / 4 + 2 * (x - 1) ^ 2 / ((x + 1) * (35 * x + 13)) * (x - 1 + κ * (b - x)) /
      (b - 1) := by
  have hSM : 0 < (x + 1) * (35 * x + 13) := by nlinarith
  have hb1 : 0 < b - 1 := by linarith
  have hδ : 0 ≤ b - x := by linarith
  have hx0 : 0 < x := by linarith
  unfold ssUbar
  have key : 2 * (x - 1) ^ 3 / ((x + 1) * (35 * x + 13)) + (b - x) ^ 3 / (48 * x ^ 2) ≤
      2 * (x - 1) ^ 2 / ((x + 1) * (35 * x + 13)) * (x - 1 + κ * (b - x)) := by
    have e : 2 * (x - 1) ^ 2 / ((x + 1) * (35 * x + 13)) * (x - 1 + κ * (b - x)) -
        (2 * (x - 1) ^ 3 / ((x + 1) * (35 * x + 13)) + (b - x) ^ 3 / (48 * x ^ 2)) =
        (b - x) * (96 * κ * x ^ 2 * (x - 1) ^ 2 - (b - x) ^ 2 * ((x + 1) * (35 * x + 13))) /
          (48 * x ^ 2 * ((x + 1) * (35 * x + 13))) := by
      field_simp; ring
    have : 0 ≤ (b - x) * (96 * κ * x ^ 2 * (x - 1) ^ 2 - (b - x) ^ 2 * ((x + 1) * (35 * x + 13))) /
        (48 * x ^ 2 * ((x + 1) * (35 * x + 13))) := by
      apply div_nonneg (mul_nonneg hδ (by linarith)) (by positivity)
    linarith
  have : (2 * (x - 1) ^ 3 / ((x + 1) * (35 * x + 13)) + (b - x) ^ 3 / (48 * x ^ 2)) / (b - 1) ≤
      2 * (x - 1) ^ 2 / ((x + 1) * (35 * x + 13)) * (x - 1 + κ * (b - x)) / (b - 1) :=
    div_le_div_of_nonneg_right key hb1.le
  linarith

/-- `δ R ≤ x(7x + 1)(α - 1)` bounds `δ² R²`. -/
theorem lgr_delta_sq {x a b t : ℝ} (hx : 0 < x) (hxb : x ≤ b) (hat : a - 1 ≤ t)
    (hb : b ≤ x + x * (7 * x + 1) * (a - 1) / (4 * x ^ 2 + 11 * x + 1)) :
    (b - x) ^ 2 * (4 * x ^ 2 + 11 * x + 1) ^ 2 ≤ x ^ 2 * (7 * x + 1) ^ 2 * t ^ 2 := by
  have hR : 0 < 4 * x ^ 2 + 11 * x + 1 := by positivity
  have h1 : (b - x) * (4 * x ^ 2 + 11 * x + 1) ≤ x * (7 * x + 1) * (a - 1) := by
    have := hb; rw [← sub_le_iff_le_add', le_div_iff₀ hR] at this; linarith
  have h2 : (b - x) * (4 * x ^ 2 + 11 * x + 1) ≤ x * (7 * x + 1) * t :=
    h1.trans (mul_le_mul_of_nonneg_left hat (by positivity))
  have h0 : 0 ≤ (b - x) * (4 * x ^ 2 + 11 * x + 1) := mul_nonneg (by linarith) hR.le
  have := mul_le_mul h2 h2 h0 (h0.trans h2)
  nlinarith

/-- **`ū ≤ u_b = (x + 74)/100`** on the whole outer domain. -/
theorem lgr_ubar_le_ub {x a b : ℝ} (hx : 12 / 5 ≤ x) (hx9 : x ≤ 9) (hax : a ≤ x)
    (hxb : x ≤ b) (hb : b ≤ x + x * (7 * x + 1) * (a - 1) / (4 * x ^ 2 + 11 * x + 1)) :
    ssUbar x b ≤ (x + 74) / 100 := by
  have hx0 : 0 < x := by linarith
  have hx1 : 1 < x := by linarith
  have hR : 0 < 4 * x ^ 2 + 11 * x + 1 := by positivity
  have hd := lgr_delta_sq hx0 hxb (by linarith : a - 1 ≤ x - 1) hb
  have h7 : (7 * x + 1) ^ 2 * ((x + 1) * (35 * x + 13)) ≤ 96 * (4 * x ^ 2 + 11 * x + 1) ^ 2 := by
    nlinarith [mul_nonneg (pow_nonneg hx0.le 3) (by linarith : (0 : ℝ) ≤ 5606 - 179 * x)]
  have hstep : (b - x) ^ 2 * ((x + 1) * (35 * x + 13)) ≤ 96 * 1 * x ^ 2 * (x - 1) ^ 2 := by
    have hSM : 0 ≤ (x + 1) * (35 * x + 13) := by nlinarith
    have e1 := mul_le_mul_of_nonneg_right hd hSM
    have e2 := mul_le_mul_of_nonneg_left h7 (by positivity : (0 : ℝ) ≤ x ^ 2 * (x - 1) ^ 2)
    have : (b - x) ^ 2 * ((x + 1) * (35 * x + 13)) * (4 * x ^ 2 + 11 * x + 1) ^ 2 ≤
        96 * x ^ 2 * (x - 1) ^ 2 * (4 * x ^ 2 + 11 * x + 1) ^ 2 := by nlinarith
    have := le_of_mul_le_mul_right this (by positivity)
    linarith
  have h := lgr_ubar_step hx1 hxb hstep
  have e : 2 * (x - 1) ^ 2 / ((x + 1) * (35 * x + 13)) * (x - 1 + 1 * (b - x)) / (b - 1) =
      2 * (x - 1) ^ 2 / ((x + 1) * (35 * x + 13)) := by
    have : b - 1 ≠ 0 := by linarith
    field_simp; ring
  rw [e] at h
  have hv : 2 * (x - 1) ^ 2 / ((x + 1) * (35 * x + 13)) ≤ (x - 1) / 100 := by
    rw [div_le_div_iff₀ (by nlinarith) (by norm_num)]
    nlinarith [sq_nonneg (35 * x - 76)]
  linarith

/-- **`ū ≤ û`** on the strip `α ≤ (2x + 3)/5`. -/
theorem lgro_ubar_le_uhat {x a b : ℝ} (hx : 12 / 5 ≤ x) (hx9 : x ≤ 9)
    (ham : a ≤ (2 * x + 3) / 5) (hxb : x ≤ b)
    (hb : b ≤ x + x * (7 * x + 1) * (a - 1) / (4 * x ^ 2 + 11 * x + 1)) :
    ssUbar x b ≤ ssUhat x b := by
  have hx0 : 0 < x := by linarith
  have hx1 : 1 < x := by linarith
  have hR : 0 < 4 * x ^ 2 + 11 * x + 1 := by positivity
  have hd := lgr_delta_sq hx0 hxb (by linarith : a - 1 ≤ 2 / 5 * (x - 1)) hb
  have h9 : (7 * x + 1) ^ 2 * ((x + 1) * (35 * x + 13)) ≤ 75 * (4 * x ^ 2 + 11 * x + 1) ^ 2 := by
    nlinarith [mul_nonneg (pow_nonneg hx0.le 3) (by linarith : (0 : ℝ) ≤ 9 - x),
      mul_nonneg (sq_nonneg x) (by linarith : (0 : ℝ) ≤ 8331 - 877 * x)]
  have hstep : (b - x) ^ 2 * ((x + 1) * (35 * x + 13)) ≤ 96 * (1 / 8) * x ^ 2 * (x - 1) ^ 2 := by
    have hSM : 0 ≤ (x + 1) * (35 * x + 13) := by nlinarith
    have e1 := mul_le_mul_of_nonneg_right hd hSM
    have e2 := mul_le_mul_of_nonneg_left h9 (by positivity : (0 : ℝ) ≤ 4 / 25 * x ^ 2 * (x - 1) ^ 2)
    have : (b - x) ^ 2 * ((x + 1) * (35 * x + 13)) * (4 * x ^ 2 + 11 * x + 1) ^ 2 ≤
        12 * x ^ 2 * (x - 1) ^ 2 * (4 * x ^ 2 + 11 * x + 1) ^ 2 := by nlinarith
    have := le_of_mul_le_mul_right this (by positivity)
    linarith
  have h := lgr_ubar_step hx1 hxb hstep
  have e : ssUhat x b = 3 / 4 + 2 * (x - 1) ^ 2 / ((x + 1) * (35 * x + 13)) *
      (x - 1 + 1 / 8 * (b - x)) / (b - 1) := by
    unfold ssUhat; ring
  rw [e]; exact h

/-! ### The cleared outer numerators -/

/-- `S V W` for `u = U/V`. -/
noncomputable def lgrWoN (S a U V D : ℝ) : ℝ :=
  S * ((6 * a ^ 2 + 1) ^ 2 - (6 * a ^ 2 + 1) * S + S ^ 2) * V + S * D ^ 2 * U -
    D * ((6 * a ^ 2 + 1) * (S ^ 2 * (U - V) + V) + (2 * S - 1) * S * V)

/-- `S V L` for `u = U/V`. -/
noncomputable def lgrLoN (S a U V D : ℝ) : ℝ :=
  2 * S * D * U - ((6 * a ^ 2 + 1) * (S ^ 2 * (U - V) + V) + (2 * S - 1) * S * V)

/-- The cleared `τ = T` numerator: `F_T = -N_T/(392α⁴SVB)`. -/
noncomputable def lgrNoT (S a B U V D : ℝ) : ℝ :=
  56 * a ^ 2 * B * lgrLoN S a U V D - (4 * B + 56 * a) * lgrWoN S a U V D -
    392 * a ^ 3 * B ^ 2 * S * U + V * (336 * a ^ 3 * B ^ 2 * S - 189 * a ^ 4 * B * S + 2352 * a ^ 5 * S)

/-- The cleared `τ = 8T/9` numerator: `F₈ = -N₈/(7056α⁴SVB)`. -/
noncomputable def lgrNo8 (S a B U V D : ℝ) : ℝ :=
  1008 * a ^ 2 * B * lgrLoN S a U V D - (72 * B + 896 * a) * lgrWoN S a U V D -
    7056 * a ^ 3 * B ^ 2 * S * U +
    V * (5922 * a ^ 3 * B ^ 2 * S - 2618 * a ^ 4 * B * S + 36848 * a ^ 5 * S)

/-- The cleared `τ = 2` numerator: `F₂ = -N₂/(3528α⁴SVB)`. -/
noncomputable def lgrNo2 (S a B U V D : ℝ) : ℝ :=
  504 * a ^ 2 * B * lgrLoN S a U V D - 180 * B * lgrWoN S a U V D - 3528 * a ^ 3 * B ^ 2 * S * U +
    V * (2268 * a ^ 3 * B ^ 2 * S + 7903 * a ^ 4 * B * S - 3528 * a ^ 5 * S)

theorem lgr_Go_UV {S a B U V D τ ℓ : ℝ} (hS : S ≠ 0) (hV : V ≠ 0) :
    lgrGo S a B (U / V) D τ ℓ = (lgrWoN S a U V D / (S * V) / (49 * a ^ 4) - 1) * τ + 1 / τ +
      (U / V - 1) * B / a + a / B + 6 / 7 - lgrLoN S a U V D / (S * V) / (7 * a ^ 2) + ℓ +
      (lgrWoN S a U V D / (S * V) / (49 * a ^ 4) - 3 / 4) / 2 := by
  have hW : lgrWo S a (U / V) D = lgrWoN S a U V D / (S * V) := by
    unfold lgrWo lgrWoN; field_simp; ring
  have hL : lgrLo S a (U / V) D = lgrLoN S a U V D / (S * V) := by
    unfold lgrLo lgrLoN; field_simp; ring
  unfold lgrGo; rw [hW, hL]

theorem lgr_NoT_eq {S a B U V D : ℝ} (hS : S ≠ 0) (ha : a ≠ 0) (hB : B ≠ 0) (hV : V ≠ 0) :
    lgrGo S a B (U / V) D (7 * (a / B)) 0 = -lgrNoT S a B U V D / (392 * a ^ 4 * S * V * B) := by
  rw [lgr_Go_UV hS hV]
  unfold lgrNoT
  generalize lgrWoN S a U V D = W
  generalize lgrLoN S a U V D = L
  field_simp
  ring

theorem lgr_No8_eq {S a B U V D : ℝ} (hS : S ≠ 0) (ha : a ≠ 0) (hB : B ≠ 0) (hV : V ≠ 0) :
    lgrGo S a B (U / V) D (8 * (7 * (a / B)) / 9) (-1 / 9) =
      -lgrNo8 S a B U V D / (7056 * a ^ 4 * S * V * B) := by
  rw [lgr_Go_UV hS hV]
  unfold lgrNo8
  generalize lgrWoN S a U V D = W
  generalize lgrLoN S a U V D = L
  field_simp
  ring

theorem lgr_No2_eq {S a B U V D : ℝ} (hS : S ≠ 0) (ha : a ≠ 0) (hB : B ≠ 0) (hV : V ≠ 0) :
    lgrGo S a B (U / V) D 2 (5 / (2 * (7 * (a / B))) - 11 / 9) =
      -lgrNo2 S a B U V D / (3528 * a ^ 4 * S * V * B) := by
  rw [lgr_Go_UV hS hV]
  unfold lgrNo2
  generalize lgrWoN S a U V D = W
  generalize lgrLoN S a U V D = L
  field_simp
  ring

/-- The outer tests are negative when their cleared numerators are positive (`u = U/V`, `V > 0`). -/
theorem lgr_OT_neg {x a b U V : ℝ} (hx : 0 < x) (ha : 0 < a) (hb : 0 < b) (hV : 0 < V)
    (hN : 0 < lgrNoT (x + 1) a (a + b) U V (ssDg x b a)) : lgrOT x a b (U / V) < 0 := by
  have hB : 0 < a + b := by linarith
  unfold lgrOT
  rw [lgr_out_F hx ha hB]
  unfold ssRA
  rw [lgr_NoT_eq (by linarith) ha.ne' hB.ne' hV.ne']
  apply div_neg_of_neg_of_pos (by linarith)
  positivity

theorem lgr_O8_neg {x a b U V : ℝ} (hx : 0 < x) (ha : 0 < a) (hb : 0 < b) (hV : 0 < V)
    (hN : 0 < lgrNo8 (x + 1) a (a + b) U V (ssDg x b a)) : lgrO8 x a b (U / V) < 0 := by
  have hB : 0 < a + b := by linarith
  unfold lgrO8
  rw [lgr_out_F hx ha hB]
  unfold ssRA
  rw [lgr_No8_eq (by linarith) ha.ne' hB.ne' hV.ne']
  apply div_neg_of_neg_of_pos (by linarith)
  positivity

theorem lgr_O2_neg {x a b U V : ℝ} (hx : 0 < x) (ha : 0 < a) (hb : 0 < b) (hV : 0 < V)
    (hN : 0 < lgrNo2 (x + 1) a (a + b) U V (ssDg x b a)) : lgrO2 x a b (U / V) < 0 := by
  have hB : 0 < a + b := by linarith
  unfold lgrO2
  rw [lgr_out_F hx ha hB]
  unfold ssRA
  rw [lgr_No2_eq (by linarith) ha.ne' hB.ne' hV.ne']
  apply div_neg_of_neg_of_pos (by linarith)
  positivity

/-! ### The cleared outer numerators on coefficient lists -/

/-- `lgrWoN` on lists (`M₀ = 6α² + 1`). -/
noncomputable def lgrWoNL (S a U V D : List (List ℝ)) : List (List ℝ) :=
  let M0 := lgrAdd2 (lgrSmul2 6 (lgrMul2 a a)) [[1]]
  let S2 := lgrMul2 S S
  lgrAdd2 (lgrMul2 (lgrMul2 S (lgrAdd2 (lgrMul2 M0 M0) (lgrAdd2 (lgrSmul2 (-1) (lgrMul2 M0 S)) S2))) V)
    (lgrAdd2 (lgrMul2 (lgrMul2 S (lgrMul2 D D)) U)
      (lgrSmul2 (-1) (lgrMul2 D (lgrAdd2 (lgrMul2 M0 (lgrAdd2 (lgrMul2 S2 (lgrAdd2 U (lgrSmul2 (-1) V))) V))
        (lgrMul2 (lgrMul2 (lgrAdd2 (lgrSmul2 2 S) [[-1]]) S) V)))))

/-- `lgrLoN` on lists. -/
noncomputable def lgrLoNL (S a U V D : List (List ℝ)) : List (List ℝ) :=
  let M0 := lgrAdd2 (lgrSmul2 6 (lgrMul2 a a)) [[1]]
  lgrAdd2 (lgrSmul2 2 (lgrMul2 (lgrMul2 S D) U))
    (lgrSmul2 (-1) (lgrAdd2 (lgrMul2 M0 (lgrAdd2 (lgrMul2 (lgrMul2 S S) (lgrAdd2 U (lgrSmul2 (-1) V))) V))
      (lgrMul2 (lgrMul2 (lgrAdd2 (lgrSmul2 2 S) [[-1]]) S) V)))

theorem lgr_H2_WoNL (S a U V D : List (List ℝ)) (X A : ℝ) :
    lgrH2 (lgrWoNL S a U V D) X A =
      lgrWoN (lgrH2 S X A) (lgrH2 a X A) (lgrH2 U X A) (lgrH2 V X A) (lgrH2 D X A) := by
  unfold lgrWoNL lgrWoN
  simp only [lgr_H2_add2, lgr_H2_mul2, lgr_H2_smul2, lgr_H2_single, polyHorner]
  ring

theorem lgr_H2_LoNL (S a U V D : List (List ℝ)) (X A : ℝ) :
    lgrH2 (lgrLoNL S a U V D) X A =
      lgrLoN (lgrH2 S X A) (lgrH2 a X A) (lgrH2 U X A) (lgrH2 V X A) (lgrH2 D X A) := by
  unfold lgrLoNL lgrLoN
  simp only [lgr_H2_add2, lgr_H2_mul2, lgr_H2_smul2, lgr_H2_single, polyHorner]
  ring

/-- A cleared outer numerator on lists:
`e₁α²B·L - (e₂B + e₃α)W - e₄α³B²SU + V(c₁α³B²S + c₂α⁴BS + c₃α⁵S)` (`lgrNoT`, `lgrNo8`, `lgrNo2`). -/
noncomputable def lgrNoL (e₁ e₂ e₃ e₄ c₁ c₂ c₃ : ℝ) (S a B U V D : List (List ℝ)) : List (List ℝ) :=
  let a2 := lgrMul2 a a
  let a3 := lgrMul2 a2 a
  let B2 := lgrMul2 B B
  lgrAdd2 (lgrSmul2 e₁ (lgrMul2 (lgrMul2 a2 B) (lgrLoNL S a U V D)))
    (lgrAdd2 (lgrSmul2 (-1) (lgrMul2 (lgrAdd2 (lgrSmul2 e₂ B) (lgrSmul2 e₃ a)) (lgrWoNL S a U V D)))
      (lgrAdd2 (lgrSmul2 (-e₄) (lgrMul2 (lgrMul2 (lgrMul2 a3 B2) S) U))
        (lgrMul2 V (lgrAdd2 (lgrSmul2 c₁ (lgrMul2 (lgrMul2 a3 B2) S))
          (lgrAdd2 (lgrSmul2 c₂ (lgrMul2 (lgrMul2 (lgrMul2 a3 a) B) S))
            (lgrSmul2 c₃ (lgrMul2 (lgrMul2 (lgrMul2 a3 a2) [[1]]) S)))))))

theorem lgr_H2_NoL (e₁ e₂ e₃ e₄ c₁ c₂ c₃ : ℝ) (S a B U V D : List (List ℝ)) (X A : ℝ) :
    lgrH2 (lgrNoL e₁ e₂ e₃ e₄ c₁ c₂ c₃ S a B U V D) X A =
      e₁ * lgrH2 a X A ^ 2 * lgrH2 B X A *
          lgrLoN (lgrH2 S X A) (lgrH2 a X A) (lgrH2 U X A) (lgrH2 V X A) (lgrH2 D X A) -
        (e₂ * lgrH2 B X A + e₃ * lgrH2 a X A) *
          lgrWoN (lgrH2 S X A) (lgrH2 a X A) (lgrH2 U X A) (lgrH2 V X A) (lgrH2 D X A) -
        e₄ * lgrH2 a X A ^ 3 * lgrH2 B X A ^ 2 * lgrH2 S X A * lgrH2 U X A +
        lgrH2 V X A * (c₁ * lgrH2 a X A ^ 3 * lgrH2 B X A ^ 2 * lgrH2 S X A +
          c₂ * lgrH2 a X A ^ 4 * lgrH2 B X A * lgrH2 S X A + c₃ * lgrH2 a X A ^ 5 * lgrH2 S X A) := by
  unfold lgrNoL
  simp only [lgr_H2_add2, lgr_H2_mul2, lgr_H2_smul2, lgr_H2_WoNL, lgr_H2_LoNL, lgr_H2_single,
    polyHorner]
  generalize lgrWoN _ _ _ _ _ = W
  generalize lgrLoN _ _ _ _ _ = L
  ring

theorem lgr_NoT_NoL (S a B U V D : ℝ) :
    lgrNoT S a B U V D = 56 * a ^ 2 * B * lgrLoN S a U V D - (4 * B + 56 * a) * lgrWoN S a U V D -
      392 * a ^ 3 * B ^ 2 * S * U + V * (336 * a ^ 3 * B ^ 2 * S + -189 * a ^ 4 * B * S + 2352 * a ^ 5 * S) := by
  unfold lgrNoT; ring

theorem lgr_No8_NoL (S a B U V D : ℝ) :
    lgrNo8 S a B U V D = 1008 * a ^ 2 * B * lgrLoN S a U V D - (72 * B + 896 * a) * lgrWoN S a U V D -
      7056 * a ^ 3 * B ^ 2 * S * U +
      V * (5922 * a ^ 3 * B ^ 2 * S + -2618 * a ^ 4 * B * S + 36848 * a ^ 5 * S) := by
  unfold lgrNo8; ring

theorem lgr_No2_NoL (S a B U V D : ℝ) :
    lgrNo2 S a B U V D = 504 * a ^ 2 * B * lgrLoN S a U V D - (180 * B + 0 * a) * lgrWoN S a U V D -
      3528 * a ^ 3 * B ^ 2 * S * U + V * (2268 * a ^ 3 * B ^ 2 * S + 7903 * a ^ 4 * B * S + -3528 * a ^ 5 * S) := by
  unfold lgrNo2; ring

/-- The outer `τ = T`, `8T/9`, `2` coefficients of `lgrNoL`. -/
theorem lgr_H2_NoTL (S a B U V D : List (List ℝ)) (X A : ℝ) :
    lgrH2 (lgrNoL 56 4 56 392 336 (-189) 2352 S a B U V D) X A =
      lgrNoT (lgrH2 S X A) (lgrH2 a X A) (lgrH2 B X A) (lgrH2 U X A) (lgrH2 V X A) (lgrH2 D X A) := by
  rw [lgr_H2_NoL, lgr_NoT_NoL]

theorem lgr_H2_No8L (S a B U V D : List (List ℝ)) (X A : ℝ) :
    lgrH2 (lgrNoL 1008 72 896 7056 5922 (-2618) 36848 S a B U V D) X A =
      lgrNo8 (lgrH2 S X A) (lgrH2 a X A) (lgrH2 B X A) (lgrH2 U X A) (lgrH2 V X A) (lgrH2 D X A) := by
  rw [lgr_H2_NoL, lgr_No8_NoL]

theorem lgr_H2_No2L (S a B U V D : List (List ℝ)) (X A : ℝ) :
    lgrH2 (lgrNoL 504 180 0 3528 2268 7903 (-3528) S a B U V D) X A =
      lgrNo2 (lgrH2 S X A) (lgrH2 a X A) (lgrH2 B X A) (lgrH2 U X A) (lgrH2 V X A) (lgrH2 D X A) := by
  rw [lgr_H2_NoL, lgr_No2_NoL]

end SmoothedOctagon
