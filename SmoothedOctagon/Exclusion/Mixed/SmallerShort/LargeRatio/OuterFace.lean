module

public import SmoothedOctagon.Exclusion.Mixed.ShortHand.Heavy.S0HandCen

/-!
# Hand proof of the smaller-short case, gate S0: the outer face, forms and reductions

At the outer scale `q = 1/7` the floor-weighted face value is
`hl0Go S α B u D τ ℓ = (w - 1)τ + 1/τ + (u - 1)B/α + α/B + 6/7 - E_L + ℓ + (w - 3/4)/2` with
`w = W/(49α⁴)`, `E_L = L/(7α²)`, `W = C₀ - DP₀ + uD(D - Q₀)`, `L = u(2D - Q₀) - P₀`,
`M₀ = 6α² + 1`, `Q₀ = M₀S`, `P₀ = M₀(1/S - S) + 2S - 1`, `C₀ = M₀² - M₀S + S²`
(`hl0_out_F`). The three tests are `τ = T = 7r_A`, `8T/9` and `2` (`hl0OT`, `hl0O8`, `hl0O2`).

* **Incoming monotonicity**: the coefficient of `u` is
  `(τ + 1/2)d(d - λS) + 1/r_A - 2d + λS > 0` (`hl0_Cu_pos`, with `d ≤ 51/175`, `λS ≤ 10`,
  `1/r_A ≥ 7/3`, `τ ≤ 3`), so `ū` may be raised (`hl0_OT_mono`, …).
* **Two majorants**: `ū ≤ u_b = (x + 74)/100` (`hl0_ubar_le_ub`) and, on the strip
  `α ≤ m = (2x + 3)/5`, `ū ≤ û` (`hl0_ubar_le_uhat`), both from the common step `hl0_ubar_step`.
* **Beta convexity on the strip**: with `u = û` each test is
  `kη² + lη + m + r/η + s/(η + α + 1)` (`hl0_pfo_T`, `hl0_pfo_2`); the generalised chord bound
  `hl0_chord2` lets the pole at `β = -α` absorb the negative residue at `β = 1`, from
  `U_T > -5/2`, `U₂ > 0` and `R_T > x²/3` (`hl0_strip_chord_T`, …).

The residue signs `U_T > -5/2`, `U₂ > 0` are proved by the uniform coefficient bound (`hl0Cov2`) on
the strip
coordinates `X = x - 12/5`, `A = α - α_f(x)`, and `R_T > x²/3` directly at `u = û(-α)`.

## Main API

* `hl0Go`, `hl0_out_F`, `hl0OT`, `hl0O8`, `hl0O2`.
* `hl0_OT_mono`, `hl0_O8_mono`, `hl0_O2_mono`; `hl0_ubar_le_ub`, `hl0_ubar_le_uhat`.
* `hl0_chord2`, `hl0Cov2`, `hl0_cov2_pos`.
-/

@[expose] public section

namespace SmoothedOctagon

/-! ### Tools: a chord bound with two compensating poles, and the bivariate cover -/

/-- **The chord bound, second form**: for `f(y) = k y² + l y + m + r/(y - p) + s/(y - q)` on
`[b₀, b₁]` with both poles left of `b₀`, `s ≥ 0` and `k + min(r, 0)/(b₀ - p)³ + s/(b₁ - q)³ ≥ 0`,
`f(y) ≤ max (f b₀) (f b₁)`. -/
theorem hl0_chord2 {k l m r s p q b₀ b₁ y : ℝ} (hp : p < b₀) (hq : q < b₀) (h0 : b₀ ≤ y)
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

/-- **The bivariate cover**: `hl0Cov2 P H_A e [p₀, …, pₙ]` asks the bivariate coefficient bound on
each outer piece `[pᵢ, pᵢ₊₁]` (`pₙ₊₁ = e`) after an outer Taylor shift, inner `0 ≤ A ≤ H_A`. -/
def hl0Cov2 (P : List (List ℝ)) (HA e : ℝ) : List ℝ → Prop
  | [] => True
  | [p] => 0 < hl0Low2 HA (e - p) (hl0Shift2 p P)
  | p :: q :: r => 0 < hl0Low2 HA (q - p) (hl0Shift2 p P) ∧ hl0Cov2 P HA e (q :: r)

theorem hl0_cov2_pos (P : List (List ℝ)) (HA e : ℝ) :
    ∀ (p : ℝ) (r : List ℝ), hl0Cov2 P HA e (p :: r) →
      ∀ X A, p ≤ X → X ≤ e → 0 ≤ A → A ≤ HA → 0 < hl0H2 P X A := by
  have one : ∀ p q X A, 0 < hl0Low2 HA (q - p) (hl0Shift2 p P) → p ≤ X → X ≤ q → 0 ≤ A →
      A ≤ HA → 0 < hl0H2 P X A := by
    intro p q X A h h1 h2 h3 h4
    have e : hl0H2 P X A = hl0H2 (hl0Shift2 p P) (X - p) A := by
      rw [hl0_H2_shift2]; congr 1; ring
    rw [e]
    exact h.trans_le (hl0_low2_le h3 h4 (by linarith) (by linarith) _)
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
noncomputable def hl0Wo (S a u D : ℝ) : ℝ :=
  (6 * a ^ 2 + 1) ^ 2 - (6 * a ^ 2 + 1) * S + S ^ 2 + D ^ 2 * u -
    D * ((6 * a ^ 2 + 1) * (S * (u - 1) + 1 / S) + 2 * S - 1)

/-- `L = 2Du - N₀`, so that `E_L = L/(7α²)`. -/
noncomputable def hl0Lo (S a u D : ℝ) : ℝ :=
  2 * D * u - ((6 * a ^ 2 + 1) * (S * (u - 1) + 1 / S) + 2 * S - 1)

/-- **The outer face value** at `q = 1/7`, floor weight `1/2`. -/
noncomputable def hl0Go (S a B u D τ ℓ : ℝ) : ℝ :=
  (hl0Wo S a u D / (49 * a ^ 4) - 1) * τ + 1 / τ + (u - 1) * B / a + a / B + 6 / 7 -
    hl0Lo S a u D / (7 * a ^ 2) + ℓ + (hl0Wo S a u D / (49 * a ^ 4) - 3 / 4) / 2

theorem hl0_Ws_o {x a b u : ℝ} (hx : 0 < x) (ha : 0 < a) :
    hsWs x b a u (1 / 7) = hl0Wo (x + 1) a u (hsDg x b a) / (49 * a ^ 4) := by
  unfold hsWs hsA1 hsA2 hsE0 hl0Wo
  field_simp
  ring

theorem hl0_ELs_o {x a b u : ℝ} (hx : 0 < x) (ha : 0 < a) :
    hsELs x b a u (1 / 7) = hl0Lo (x + 1) a u (hsDg x b a) / (7 * a ^ 2) := by
  unfold hsELs hsA3 hsE0 hl0Lo
  field_simp
  ring

/-- **The outer face value** of `hsF` at `q = 1/7`. -/
theorem hl0_out_F {x a b u τ ℓ : ℝ} (hx : 0 < x) (ha : 0 < a) (hB : 0 < a + b) :
    hsF x b a u (1 / 7) τ ℓ (1 / 2) = hl0Go (x + 1) a (a + b) u (hsDg x b a) τ ℓ := by
  unfold hsF
  rw [hl0_Ws_o hx ha, hl0_ELs_o hx ha]
  unfold hl0Go hsRA
  field_simp
  ring

/-- The outer `τ = T = 7r_A` test at `q = 1/7`, with incoming norm `u`. -/
noncomputable def hl0OT (x a b u : ℝ) : ℝ := hsF x b a u (1 / 7) (7 * hsRA a b) 0 (1 / 2)
/-- The outer `τ = 8T/9` test. -/
noncomputable def hl0O8 (x a b u : ℝ) : ℝ :=
  hsF x b a u (1 / 7) (8 * (7 * hsRA a b) / 9) (-1 / 9) (1 / 2)
/-- The outer `τ = 2` test. -/
noncomputable def hl0O2 (x a b u : ℝ) : ℝ :=
  hsF x b a u (1 / 7) 2 (5 / (2 * (7 * hsRA a b)) - 11 / 9) (1 / 2)

/-! ### Incoming monotonicity -/

/-- The coefficient of `u`: `(τ + 1/2)d(d - λS) + B/α - 2d + λS`, `d = D/(7α²)`,
`λS = M₀S/(7α²)`. -/
noncomputable def hl0Cu (S a B D τ : ℝ) : ℝ :=
  (τ + 1 / 2) * (D / (7 * a ^ 2)) * (D / (7 * a ^ 2) - (6 * a ^ 2 + 1) * S / (7 * a ^ 2)) + B / a -
    2 * (D / (7 * a ^ 2)) + (6 * a ^ 2 + 1) * S / (7 * a ^ 2)

theorem hl0_Go_affine {S a B u u' D τ ℓ : ℝ} (hS : S ≠ 0) (ha : a ≠ 0) (hτ : τ ≠ 0) :
    hl0Go S a B u' D τ ℓ = hl0Go S a B u D τ ℓ + (u' - u) * hl0Cu S a B D τ := by
  unfold hl0Go hl0Wo hl0Lo hl0Cu
  field_simp
  ring

/-- The scalar core of the positivity of `hl0Cu`. -/
theorem hl0_Cu_core {d L τ ρ : ℝ} (hτ : 0 < τ) (hτ3 : τ ≤ 3) (hρ : 7 / 3 ≤ ρ) (hL : 0 ≤ L)
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
theorem hl0_Cu_pos {x a b τ : ℝ} (hx : 12 / 5 ≤ x) (hx9 : x ≤ 9) (ha : 1 ≤ a) (hax : a ≤ x)
    (hxb : x ≤ b) (hb43 : 4 * a ≤ 3 * b) (hτ : 0 < τ) (hτ3 : τ ≤ 3) :
    0 < hl0Cu (x + 1) a (a + b) (hsDg x b a) τ := by
  have ha0 : 0 < a := by linarith
  have ha2 : 0 < 7 * a ^ 2 := by positivity
  have hD : hsDg x b a ≤ 51 / 25 * a ^ 2 := by
    unfold hsDg
    have : 2 * b * (x - a) ≥ 2 * x * (x - a) := by nlinarith
    nlinarith
  have hd : hsDg x b a / (7 * a ^ 2) ≤ 51 / 175 := by
    rw [div_le_iff₀ ha2]; linarith
  have hL : (6 * a ^ 2 + 1) * (x + 1) / (7 * a ^ 2) ≤ 10 := by
    rw [div_le_iff₀ ha2]; nlinarith
  have hρ : 7 / 3 ≤ (a + b) / a := by rw [le_div_iff₀ ha0]; linarith
  unfold hl0Cu
  exact hl0_Cu_core hτ hτ3 hρ (by positivity) hL hd

/-- `T = 7r_A ≤ 3` from `β ≥ 4α/3`. -/
theorem hl0_T_le {a b : ℝ} (ha : 0 < a) (hb43 : 4 * a ≤ 3 * b) : 7 * hsRA a b ≤ 3 := by
  unfold hsRA
  have : 0 < a + b := by linarith
  rw [mul_div_assoc', div_le_iff₀ this]; linarith

theorem hl0_T_pos {a b : ℝ} (ha : 0 < a) (hb : 0 < b) : 0 < 7 * hsRA a b := by
  unfold hsRA; positivity

/-- **Raising the incoming norm**: each outer test increases with `u`. -/
theorem hl0_O_mono {x a b u u' τ ℓ : ℝ} (hx : 12 / 5 ≤ x) (hx9 : x ≤ 9) (ha : 1 ≤ a)
    (hax : a ≤ x) (hxb : x ≤ b) (hb43 : 4 * a ≤ 3 * b) (hτ : 0 < τ) (hτ3 : τ ≤ 3) (hu : u ≤ u') :
    hsF x b a u (1 / 7) τ ℓ (1 / 2) ≤ hsF x b a u' (1 / 7) τ ℓ (1 / 2) := by
  have hx0 : 0 < x := by linarith
  have ha0 : 0 < a := by linarith
  have hB : 0 < a + b := by linarith
  rw [hl0_out_F hx0 ha0 hB, hl0_out_F hx0 ha0 hB,
    hl0_Go_affine (u := u) (u' := u') (by linarith : x + 1 ≠ 0) ha0.ne' hτ.ne']
  have := hl0_Cu_pos hx hx9 ha hax hxb hb43 hτ hτ3
  nlinarith

theorem hl0_OT_mono {x a b u u' : ℝ} (hx : 12 / 5 ≤ x) (hx9 : x ≤ 9) (ha : 1 ≤ a)
    (hax : a ≤ x) (hxb : x ≤ b) (hb43 : 4 * a ≤ 3 * b) (hu : u ≤ u') :
    hl0OT x a b u ≤ hl0OT x a b u' :=
  hl0_O_mono hx hx9 ha hax hxb hb43 (hl0_T_pos (by linarith) (by linarith))
    (hl0_T_le (by linarith) hb43) hu

theorem hl0_O8_mono {x a b u u' : ℝ} (hx : 12 / 5 ≤ x) (hx9 : x ≤ 9) (ha : 1 ≤ a)
    (hax : a ≤ x) (hxb : x ≤ b) (hb43 : 4 * a ≤ 3 * b) (hu : u ≤ u') :
    hl0O8 x a b u ≤ hl0O8 x a b u' := by
  have h1 := hl0_T_pos (a := a) (b := b) (by linarith) (by linarith)
  have h2 := hl0_T_le (a := a) (b := b) (by linarith) hb43
  exact hl0_O_mono hx hx9 ha hax hxb hb43 (by positivity) (by linarith) hu

theorem hl0_O2_mono {x a b u u' : ℝ} (hx : 12 / 5 ≤ x) (hx9 : x ≤ 9) (ha : 1 ≤ a)
    (hax : a ≤ x) (hxb : x ≤ b) (hb43 : 4 * a ≤ 3 * b) (hu : u ≤ u') :
    hl0O2 x a b u ≤ hl0O2 x a b u' :=
  hl0_O_mono hx hx9 ha hax hxb hb43 (by norm_num) (by norm_num) hu

/-! ### Two incoming majorants -/

/-- The common step: `ū ≤ 3/4 + v(x - 1 + κδ)/(β - 1)` once `δ²SM ≤ 96κ x²(x - 1)²`
(`v = 2(x - 1)²/(SM)`, `δ = β - x`). -/
theorem hl0_ubar_step {x b κ : ℝ} (hx : 1 < x) (hxb : x ≤ b)
    (h : (b - x) ^ 2 * ((x + 1) * (35 * x + 13)) ≤ 96 * κ * x ^ 2 * (x - 1) ^ 2) :
    hsUbar x b ≤ 3 / 4 + 2 * (x - 1) ^ 2 / ((x + 1) * (35 * x + 13)) * (x - 1 + κ * (b - x)) /
      (b - 1) := by
  have hSM : 0 < (x + 1) * (35 * x + 13) := by nlinarith
  have hb1 : 0 < b - 1 := by linarith
  have hδ : 0 ≤ b - x := by linarith
  have hx0 : 0 < x := by linarith
  unfold hsUbar
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
theorem hl0_delta_sq {x a b t : ℝ} (hx : 0 < x) (hxb : x ≤ b) (hat : a - 1 ≤ t)
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
theorem hl0_ubar_le_ub {x a b : ℝ} (hx : 12 / 5 ≤ x) (hx9 : x ≤ 9) (hax : a ≤ x)
    (hxb : x ≤ b) (hb : b ≤ x + x * (7 * x + 1) * (a - 1) / (4 * x ^ 2 + 11 * x + 1)) :
    hsUbar x b ≤ (x + 74) / 100 := by
  have hx0 : 0 < x := by linarith
  have hx1 : 1 < x := by linarith
  have hR : 0 < 4 * x ^ 2 + 11 * x + 1 := by positivity
  have hd := hl0_delta_sq hx0 hxb (by linarith : a - 1 ≤ x - 1) hb
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
  have h := hl0_ubar_step hx1 hxb hstep
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
theorem hl0_ubar_le_uhat {x a b : ℝ} (hx : 12 / 5 ≤ x) (hx9 : x ≤ 9)
    (ham : a ≤ (2 * x + 3) / 5) (hxb : x ≤ b)
    (hb : b ≤ x + x * (7 * x + 1) * (a - 1) / (4 * x ^ 2 + 11 * x + 1)) :
    hsUbar x b ≤ hsUhat x b := by
  have hx0 : 0 < x := by linarith
  have hx1 : 1 < x := by linarith
  have hR : 0 < 4 * x ^ 2 + 11 * x + 1 := by positivity
  have hd := hl0_delta_sq hx0 hxb (by linarith : a - 1 ≤ 2 / 5 * (x - 1)) hb
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
  have h := hl0_ubar_step hx1 hxb hstep
  have e : hsUhat x b = 3 / 4 + 2 * (x - 1) ^ 2 / ((x + 1) * (35 * x + 13)) *
      (x - 1 + 1 / 8 * (b - x)) / (b - 1) := by
    unfold hsUhat; ring
  rw [e]; exact h

/-! ### The cleared outer numerators -/

/-- `S V W` for `u = U/V`. -/
noncomputable def hl0WoN (S a U V D : ℝ) : ℝ :=
  S * ((6 * a ^ 2 + 1) ^ 2 - (6 * a ^ 2 + 1) * S + S ^ 2) * V + S * D ^ 2 * U -
    D * ((6 * a ^ 2 + 1) * (S ^ 2 * (U - V) + V) + (2 * S - 1) * S * V)

/-- `S V L` for `u = U/V`. -/
noncomputable def hl0LoN (S a U V D : ℝ) : ℝ :=
  2 * S * D * U - ((6 * a ^ 2 + 1) * (S ^ 2 * (U - V) + V) + (2 * S - 1) * S * V)

/-- The cleared `τ = T` numerator: `F_T = -N_T/(392α⁴SVB)`. -/
noncomputable def hl0NoT (S a B U V D : ℝ) : ℝ :=
  56 * a ^ 2 * B * hl0LoN S a U V D - (4 * B + 56 * a) * hl0WoN S a U V D -
    392 * a ^ 3 * B ^ 2 * S * U + V * (336 * a ^ 3 * B ^ 2 * S - 189 * a ^ 4 * B * S + 2352 * a ^ 5 * S)

/-- The cleared `τ = 8T/9` numerator: `F₈ = -N₈/(7056α⁴SVB)`. -/
noncomputable def hl0No8 (S a B U V D : ℝ) : ℝ :=
  1008 * a ^ 2 * B * hl0LoN S a U V D - (72 * B + 896 * a) * hl0WoN S a U V D -
    7056 * a ^ 3 * B ^ 2 * S * U +
    V * (5922 * a ^ 3 * B ^ 2 * S - 2618 * a ^ 4 * B * S + 36848 * a ^ 5 * S)

/-- The cleared `τ = 2` numerator: `F₂ = -N₂/(3528α⁴SVB)`. -/
noncomputable def hl0No2 (S a B U V D : ℝ) : ℝ :=
  504 * a ^ 2 * B * hl0LoN S a U V D - 180 * B * hl0WoN S a U V D - 3528 * a ^ 3 * B ^ 2 * S * U +
    V * (2268 * a ^ 3 * B ^ 2 * S + 7903 * a ^ 4 * B * S - 3528 * a ^ 5 * S)

theorem hl0_Go_UV {S a B U V D τ ℓ : ℝ} (hS : S ≠ 0) (hV : V ≠ 0) :
    hl0Go S a B (U / V) D τ ℓ = (hl0WoN S a U V D / (S * V) / (49 * a ^ 4) - 1) * τ + 1 / τ +
      (U / V - 1) * B / a + a / B + 6 / 7 - hl0LoN S a U V D / (S * V) / (7 * a ^ 2) + ℓ +
      (hl0WoN S a U V D / (S * V) / (49 * a ^ 4) - 3 / 4) / 2 := by
  have hW : hl0Wo S a (U / V) D = hl0WoN S a U V D / (S * V) := by
    unfold hl0Wo hl0WoN; field_simp; ring
  have hL : hl0Lo S a (U / V) D = hl0LoN S a U V D / (S * V) := by
    unfold hl0Lo hl0LoN; field_simp; ring
  unfold hl0Go; rw [hW, hL]

theorem hl0_NoT_eq {S a B U V D : ℝ} (hS : S ≠ 0) (ha : a ≠ 0) (hB : B ≠ 0) (hV : V ≠ 0) :
    hl0Go S a B (U / V) D (7 * (a / B)) 0 = -hl0NoT S a B U V D / (392 * a ^ 4 * S * V * B) := by
  rw [hl0_Go_UV hS hV]
  unfold hl0NoT
  generalize hl0WoN S a U V D = W
  generalize hl0LoN S a U V D = L
  field_simp
  ring

theorem hl0_No8_eq {S a B U V D : ℝ} (hS : S ≠ 0) (ha : a ≠ 0) (hB : B ≠ 0) (hV : V ≠ 0) :
    hl0Go S a B (U / V) D (8 * (7 * (a / B)) / 9) (-1 / 9) =
      -hl0No8 S a B U V D / (7056 * a ^ 4 * S * V * B) := by
  rw [hl0_Go_UV hS hV]
  unfold hl0No8
  generalize hl0WoN S a U V D = W
  generalize hl0LoN S a U V D = L
  field_simp
  ring

theorem hl0_No2_eq {S a B U V D : ℝ} (hS : S ≠ 0) (ha : a ≠ 0) (hB : B ≠ 0) (hV : V ≠ 0) :
    hl0Go S a B (U / V) D 2 (5 / (2 * (7 * (a / B))) - 11 / 9) =
      -hl0No2 S a B U V D / (3528 * a ^ 4 * S * V * B) := by
  rw [hl0_Go_UV hS hV]
  unfold hl0No2
  generalize hl0WoN S a U V D = W
  generalize hl0LoN S a U V D = L
  field_simp
  ring

/-- The outer tests are negative when their cleared numerators are positive (`u = U/V`, `V > 0`). -/
theorem hl0_OT_neg {x a b U V : ℝ} (hx : 0 < x) (ha : 0 < a) (hb : 0 < b) (hV : 0 < V)
    (hN : 0 < hl0NoT (x + 1) a (a + b) U V (hsDg x b a)) : hl0OT x a b (U / V) < 0 := by
  have hB : 0 < a + b := by linarith
  unfold hl0OT
  rw [hl0_out_F hx ha hB]
  unfold hsRA
  rw [hl0_NoT_eq (by linarith) ha.ne' hB.ne' hV.ne']
  apply div_neg_of_neg_of_pos (by linarith)
  positivity

theorem hl0_O8_neg {x a b U V : ℝ} (hx : 0 < x) (ha : 0 < a) (hb : 0 < b) (hV : 0 < V)
    (hN : 0 < hl0No8 (x + 1) a (a + b) U V (hsDg x b a)) : hl0O8 x a b (U / V) < 0 := by
  have hB : 0 < a + b := by linarith
  unfold hl0O8
  rw [hl0_out_F hx ha hB]
  unfold hsRA
  rw [hl0_No8_eq (by linarith) ha.ne' hB.ne' hV.ne']
  apply div_neg_of_neg_of_pos (by linarith)
  positivity

theorem hl0_O2_neg {x a b U V : ℝ} (hx : 0 < x) (ha : 0 < a) (hb : 0 < b) (hV : 0 < V)
    (hN : 0 < hl0No2 (x + 1) a (a + b) U V (hsDg x b a)) : hl0O2 x a b (U / V) < 0 := by
  have hB : 0 < a + b := by linarith
  unfold hl0O2
  rw [hl0_out_F hx ha hB]
  unfold hsRA
  rw [hl0_No2_eq (by linarith) ha.ne' hB.ne' hV.ne']
  apply div_neg_of_neg_of_pos (by linarith)
  positivity

/-! ### The cleared outer numerators on coefficient lists -/

/-- `hl0WoN` on lists (`M₀ = 6α² + 1`). -/
noncomputable def hl0WoNL (S a U V D : List (List ℝ)) : List (List ℝ) :=
  let M0 := hl0Add2 (hl0Smul2 6 (hl0Mul2 a a)) [[1]]
  let S2 := hl0Mul2 S S
  hl0Add2 (hl0Mul2 (hl0Mul2 S (hl0Add2 (hl0Mul2 M0 M0) (hl0Add2 (hl0Smul2 (-1) (hl0Mul2 M0 S)) S2))) V)
    (hl0Add2 (hl0Mul2 (hl0Mul2 S (hl0Mul2 D D)) U)
      (hl0Smul2 (-1) (hl0Mul2 D (hl0Add2 (hl0Mul2 M0 (hl0Add2 (hl0Mul2 S2 (hl0Add2 U (hl0Smul2 (-1) V))) V))
        (hl0Mul2 (hl0Mul2 (hl0Add2 (hl0Smul2 2 S) [[-1]]) S) V)))))

/-- `hl0LoN` on lists. -/
noncomputable def hl0LoNL (S a U V D : List (List ℝ)) : List (List ℝ) :=
  let M0 := hl0Add2 (hl0Smul2 6 (hl0Mul2 a a)) [[1]]
  hl0Add2 (hl0Smul2 2 (hl0Mul2 (hl0Mul2 S D) U))
    (hl0Smul2 (-1) (hl0Add2 (hl0Mul2 M0 (hl0Add2 (hl0Mul2 (hl0Mul2 S S) (hl0Add2 U (hl0Smul2 (-1) V))) V))
      (hl0Mul2 (hl0Mul2 (hl0Add2 (hl0Smul2 2 S) [[-1]]) S) V)))

theorem hl0_H2_WoNL (S a U V D : List (List ℝ)) (X A : ℝ) :
    hl0H2 (hl0WoNL S a U V D) X A =
      hl0WoN (hl0H2 S X A) (hl0H2 a X A) (hl0H2 U X A) (hl0H2 V X A) (hl0H2 D X A) := by
  unfold hl0WoNL hl0WoN
  simp only [hl0_H2_add2, hl0_H2_mul2, hl0_H2_smul2, hl0_H2_single, lrhHorner]
  ring

theorem hl0_H2_LoNL (S a U V D : List (List ℝ)) (X A : ℝ) :
    hl0H2 (hl0LoNL S a U V D) X A =
      hl0LoN (hl0H2 S X A) (hl0H2 a X A) (hl0H2 U X A) (hl0H2 V X A) (hl0H2 D X A) := by
  unfold hl0LoNL hl0LoN
  simp only [hl0_H2_add2, hl0_H2_mul2, hl0_H2_smul2, hl0_H2_single, lrhHorner]
  ring

/-- A cleared outer numerator on lists:
`e₁α²B·L - (e₂B + e₃α)W - e₄α³B²SU + V(c₁α³B²S + c₂α⁴BS + c₃α⁵S)` (`hl0NoT`, `hl0No8`, `hl0No2`). -/
noncomputable def hl0NoL (e₁ e₂ e₃ e₄ c₁ c₂ c₃ : ℝ) (S a B U V D : List (List ℝ)) : List (List ℝ) :=
  let a2 := hl0Mul2 a a
  let a3 := hl0Mul2 a2 a
  let B2 := hl0Mul2 B B
  hl0Add2 (hl0Smul2 e₁ (hl0Mul2 (hl0Mul2 a2 B) (hl0LoNL S a U V D)))
    (hl0Add2 (hl0Smul2 (-1) (hl0Mul2 (hl0Add2 (hl0Smul2 e₂ B) (hl0Smul2 e₃ a)) (hl0WoNL S a U V D)))
      (hl0Add2 (hl0Smul2 (-e₄) (hl0Mul2 (hl0Mul2 (hl0Mul2 a3 B2) S) U))
        (hl0Mul2 V (hl0Add2 (hl0Smul2 c₁ (hl0Mul2 (hl0Mul2 a3 B2) S))
          (hl0Add2 (hl0Smul2 c₂ (hl0Mul2 (hl0Mul2 (hl0Mul2 a3 a) B) S))
            (hl0Smul2 c₃ (hl0Mul2 (hl0Mul2 (hl0Mul2 a3 a2) [[1]]) S)))))))

theorem hl0_H2_NoL (e₁ e₂ e₃ e₄ c₁ c₂ c₃ : ℝ) (S a B U V D : List (List ℝ)) (X A : ℝ) :
    hl0H2 (hl0NoL e₁ e₂ e₃ e₄ c₁ c₂ c₃ S a B U V D) X A =
      e₁ * hl0H2 a X A ^ 2 * hl0H2 B X A *
          hl0LoN (hl0H2 S X A) (hl0H2 a X A) (hl0H2 U X A) (hl0H2 V X A) (hl0H2 D X A) -
        (e₂ * hl0H2 B X A + e₃ * hl0H2 a X A) *
          hl0WoN (hl0H2 S X A) (hl0H2 a X A) (hl0H2 U X A) (hl0H2 V X A) (hl0H2 D X A) -
        e₄ * hl0H2 a X A ^ 3 * hl0H2 B X A ^ 2 * hl0H2 S X A * hl0H2 U X A +
        hl0H2 V X A * (c₁ * hl0H2 a X A ^ 3 * hl0H2 B X A ^ 2 * hl0H2 S X A +
          c₂ * hl0H2 a X A ^ 4 * hl0H2 B X A * hl0H2 S X A + c₃ * hl0H2 a X A ^ 5 * hl0H2 S X A) := by
  unfold hl0NoL
  simp only [hl0_H2_add2, hl0_H2_mul2, hl0_H2_smul2, hl0_H2_WoNL, hl0_H2_LoNL, hl0_H2_single,
    lrhHorner]
  generalize hl0WoN _ _ _ _ _ = W
  generalize hl0LoN _ _ _ _ _ = L
  ring

theorem hl0_NoT_NoL (S a B U V D : ℝ) :
    hl0NoT S a B U V D = 56 * a ^ 2 * B * hl0LoN S a U V D - (4 * B + 56 * a) * hl0WoN S a U V D -
      392 * a ^ 3 * B ^ 2 * S * U + V * (336 * a ^ 3 * B ^ 2 * S + -189 * a ^ 4 * B * S + 2352 * a ^ 5 * S) := by
  unfold hl0NoT; ring

theorem hl0_No8_NoL (S a B U V D : ℝ) :
    hl0No8 S a B U V D = 1008 * a ^ 2 * B * hl0LoN S a U V D - (72 * B + 896 * a) * hl0WoN S a U V D -
      7056 * a ^ 3 * B ^ 2 * S * U +
      V * (5922 * a ^ 3 * B ^ 2 * S + -2618 * a ^ 4 * B * S + 36848 * a ^ 5 * S) := by
  unfold hl0No8; ring

theorem hl0_No2_NoL (S a B U V D : ℝ) :
    hl0No2 S a B U V D = 504 * a ^ 2 * B * hl0LoN S a U V D - (180 * B + 0 * a) * hl0WoN S a U V D -
      3528 * a ^ 3 * B ^ 2 * S * U + V * (2268 * a ^ 3 * B ^ 2 * S + 7903 * a ^ 4 * B * S + -3528 * a ^ 5 * S) := by
  unfold hl0No2; ring

/-- The outer `τ = T`, `8T/9`, `2` coefficients of `hl0NoL`. -/
theorem hl0_H2_NoTL (S a B U V D : List (List ℝ)) (X A : ℝ) :
    hl0H2 (hl0NoL 56 4 56 392 336 (-189) 2352 S a B U V D) X A =
      hl0NoT (hl0H2 S X A) (hl0H2 a X A) (hl0H2 B X A) (hl0H2 U X A) (hl0H2 V X A) (hl0H2 D X A) := by
  rw [hl0_H2_NoL, hl0_NoT_NoL]

theorem hl0_H2_No8L (S a B U V D : List (List ℝ)) (X A : ℝ) :
    hl0H2 (hl0NoL 1008 72 896 7056 5922 (-2618) 36848 S a B U V D) X A =
      hl0No8 (hl0H2 S X A) (hl0H2 a X A) (hl0H2 B X A) (hl0H2 U X A) (hl0H2 V X A) (hl0H2 D X A) := by
  rw [hl0_H2_NoL, hl0_No8_NoL]

theorem hl0_H2_No2L (S a B U V D : List (List ℝ)) (X A : ℝ) :
    hl0H2 (hl0NoL 504 180 0 3528 2268 7903 (-3528) S a B U V D) X A =
      hl0No2 (hl0H2 S X A) (hl0H2 a X A) (hl0H2 B X A) (hl0H2 U X A) (hl0H2 V X A) (hl0H2 D X A) := by
  rw [hl0_H2_NoL, hl0_No2_NoL]

end SmoothedOctagon
