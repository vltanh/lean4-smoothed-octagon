module

public import SmoothedOctagon.Exclusion.Mixed.ShortHand.Heavy.S1CAux
public import SmoothedOctagon.Exclusion.Mixed.ShortHand.Heavy.S1CClaimU
public import SmoothedOctagon.Exclusion.Mixed.ShortHand.Heavy.S1CClaimB
public import SmoothedOctagon.Exclusion.Mixed.ShortHand.Heavy.S1CClaimA
public import SmoothedOctagon.Exclusion.Mixed.ShortHand.Heavy.S1CClaimX

/-!
# Gate S1, central face: the four monotonicity steps

On the box `8/5 ≤ x ≤ 2`, `1 ≤ α ≤ 7/6`, `x + (α - 1)/2 ≤ β ≤ x + 4(α - 1)/5`
(`LOW_RATIO_CENTRAL_HAND_SIGN` (11)), from the generated derivative claims:

* `hh1c_stepU0`, `hh1c_stepU1`: `F₀`, `F₁` decrease in `u ≥ 3/4` (concave quadratics with
  `∂_uF(3/4) ≤ 0`; D-R11);
* `hh1c_stepB0`: `β ↦ F₀(x, α, β, u_ℓ(x, β))` decreases (D-R12);
* `hh1c_stepB1`: `β ↦ F₁(x, α, β, u)` decreases at fixed `u`;
* `hh1c_stepA0`: `α ↦ F₀(x, α, β*(α), u_ℓ(x, β*(α)))`, `β* = x + (10/13)(α - 1)`, decreases for
  `α ≤ a_U(x)` (D-R13);
* `hh1c_stepX1`: `x ↦ F₁(x, α, x + (10/13)(α - 1), V̄(x))` decreases (route: the duration test
  `F₁` is reduced in `x` at fixed `α` instead of the notes' concavity in `α`).
-/

@[expose] public section

namespace SmoothedOctagon

/-- The `u`-quadratic structure of `F₀`. -/
theorem hh1c_F0_u_diff (x a b u u' : ℝ) (hx : 0 < x) (ha : 0 < a) (hb : 0 < b) :
    hh1cF0 x a b u - hh1cF0 x a b u' = (u' - u) * ((7 / 96 * hh1cR2u x a b - hh1cGu x (3 / 4)) +
      (1 + x) ^ 6 / (16 * (x * (x + 2)) ^ 2) * (u + u' - 3 / 2)) := by
  simp only [hh1cF0, hh1cR2, hh1cG, hh1cw, hh1cEL, hh1cR2u, hh1cwu, hh1cGu, hh1cE]
  have hS : 1 + x ≠ 0 := by positivity
  have hX : x * (x + 2) ≠ 0 := by positivity
  have hab : a + b ≠ 0 := by positivity
  have ha0 : a ≠ 0 := ha.ne'
  field_simp
  ring

/-- The `u`-quadratic structure of `F₁`. -/
theorem hh1c_F1_u_diff (x a b u u' : ℝ) (hx : 0 < x) (ha : 0 < a) (hb : 0 < b) :
    hh1cF1 x a b u - hh1cF1 x a b u' = (u' - u) * ((7 / 96 * (hh1cR2u x a b +
      (hh1cT x a b - 2) * hh1cwu x a b) - hh1cGu x (3 / 4)) +
      (1 + x) ^ 6 / (16 * (x * (x + 2)) ^ 2) * (u + u' - 3 / 2)) := by
  have h0 := hh1c_F0_u_diff x a b u u' hx ha hb
  simp only [hh1cF1, hh1cw, hh1cwu, hh1cE] at h0 ⊢
  linear_combination h0

theorem hh1c_stepU0 {x a b u u' : ℝ} (hx0 : 8 / 5 ≤ x) (hx1 : x ≤ 2) (ha0 : 1 ≤ a) (ha1 : a ≤ 7 / 6)
    (hb0 : x + 1 / 2 * (a - 1) ≤ b) (hb1 : b ≤ x + 4 / 5 * (a - 1)) (hu : 3 / 4 ≤ u)
    (huu : u ≤ u') : hh1cF0 x a b u' ≤ hh1cF0 x a b u := by
  have hc := hh1c_claim_U0 (u := u) hx0 hx1 ha0 (by linarith) hb0 hb1
  have hd := hh1c_F0_u_diff x a b u u' (by linarith) (by linarith) (by nlinarith)
  have h2 : 0 ≤ (1 + x) ^ 6 / (16 * (x * (x + 2)) ^ 2) * (u + u' - 3 / 2) :=
    mul_nonneg (by positivity) (by linarith)
  nlinarith [mul_nonneg (sub_nonneg.2 huu) (add_nonneg hc h2)]

theorem hh1c_stepU1 {x a b u u' : ℝ} (hx0 : 8 / 5 ≤ x) (hx1 : x ≤ 2) (ha0 : 1 ≤ a) (ha1 : a ≤ 7 / 6)
    (hb0 : x + 1 / 2 * (a - 1) ≤ b) (hb1 : b ≤ x + 4 / 5 * (a - 1)) (hu : 3 / 4 ≤ u)
    (huu : u ≤ u') : hh1cF1 x a b u' ≤ hh1cF1 x a b u := by
  have hc := hh1c_claim_U1 (u := u) hx0 hx1 ha0 (by linarith) hb0 hb1
  have hd := hh1c_F1_u_diff x a b u u' (by linarith) (by linarith) (by nlinarith)
  have h2 : 0 ≤ (1 + x) ^ 6 / (16 * (x * (x + 2)) ^ 2) * (u + u' - 3 / 2) :=
    mul_nonneg (by positivity) (by linarith)
  nlinarith [mul_nonneg (sub_nonneg.2 huu) (add_nonneg hc h2)]

/-- `∂_uF₁(u) ≤ ∂_uF₁(3/4) ≤ 0` for `u ≥ 3/4` (`Γ_u` decreases in `u`). -/
theorem hh1c_F1u_nonpos {x a b u : ℝ} (hx0 : 8 / 5 ≤ x) (hx1 : x ≤ 2) (ha0 : 1 ≤ a)
    (ha1 : a ≤ 7 / 6) (hb0 : x + 1 / 2 * (a - 1) ≤ b) (hb1 : b ≤ x + 4 / 5 * (a - 1))
    (hu : 3 / 4 ≤ u) :
    hh1cGu x u - 7 / 96 * (hh1cR2u x a b + (hh1cT x a b - 2) * hh1cwu x a b) ≤ 0 := by
  have hc := hh1c_claim_U1 (u := u) hx0 hx1 ha0 (by linarith) hb0 hb1
  have hG : hh1cGu x u - hh1cGu x (3 / 4) = -(2 * (1 + x) ^ 2 * (u - 3 / 4)) * (1 + x) ^ 4 /
      (16 * (x * (x + 2)) ^ 2) := by
    simp only [hh1cGu, hh1cE]
    have hS : 1 + x ≠ 0 := by positivity
    field_simp
    ring
  have h3 : 0 ≤ 2 * (1 + x) ^ 2 * (u - 3 / 4) * (1 + x) ^ 4 / (16 * (x * (x + 2)) ^ 2) := by
    apply div_nonneg _ (by positivity)
    apply mul_nonneg (mul_nonneg (by positivity) (by linarith)) (by positivity)
  rw [neg_mul, neg_div] at hG
  linarith

/-- **Step B for `F₀`** along the ceiling `u = u_ℓ(x, β)` (`LOW_RATIO_CENTRAL_HAND_SIGN` (20)). -/
theorem hh1c_stepB0 {x a b b' : ℝ} (hx0 : 8 / 5 ≤ x) (hx1 : x ≤ 2) (ha0 : 1 ≤ a) (ha1 : a ≤ 7 / 6)
    (hb0 : x + 1 / 2 * (a - 1) ≤ b) (hbb : b ≤ b') (hb1 : b' ≤ x + 4 / 5 * (a - 1)) :
    hh1cF0 x a b' (hsUl x b') ≤ hh1cF0 x a b (hsUl x b) := by
  have hx : 0 < x := by linarith
  have ha : 0 < a := by linarith
  set D : ℝ → ℝ := fun z =>
    0 * (hh1cGx x (hsUl x z) - 7 / 96 * hh1cR2x x a z (hsUl x z)) +
      0 * (-(7 / 96) * hh1cR2a x a z (hsUl x z)) + 1 * (-(7 / 96) * hh1cR2b x a z (hsUl x z)) +
      -(15 * (x - 1) ^ 3 / (8 * (1 + x) * (35 * x + 13) * (z - 1) ^ 2)) *
        (hh1cGu x (hsUl x z) - 7 / 96 * hh1cR2u x a z) +
      7 / 96 * hh1eps (hh1cy x a z) *
        (-(2 * (1 + x) / hh1cK x a) * 0 + (1 / a + 1 / (a + z) - 2 * a / hh1cK x a) * 0 +
          1 / (a + z) * 1) with hD
  have key := ss_le_of_deriv (f := fun z => -hh1cF0 x a z (hsUl x z)) (f' := fun z => -D z) hbb
    (fun z hz => by
      have hz1 : x ≤ z := by nlinarith [hz.1]
      exact (hh1c_F0_hasDerivAt (hasDerivAt_const z x) (hasDerivAt_const z a) (hasDerivAt_id' z)
        (hh1_Ul_hasDerivAt (by linarith) (by linarith)) hx ha (by linarith)).neg)
    (fun z hz => by
      have hz0 : x + 1 / 2 * (a - 1) ≤ z := by linarith [hz.1]
      have hz1 : z ≤ x + 4 / 5 * (a - 1) := by linarith [hz.2]
      have hxz : x ≤ z := by nlinarith
      obtain ⟨hU0, hU1⟩ := hh1_Ul_bounds (by linarith) hx1 hxz
      obtain ⟨hL0, hL1⟩ := hh1_Ul_deriv_bounds (by linarith) hx1 hxz
      have hB := hh1c_claim_B0 hx0 hx1 ha0 (by linarith) hz0 hz1 hU0 hU1
      have hM := hh1c_claim_M0 hx0 hx1 ha0 (by linarith) hz0 hz1 hU0 hU1
      obtain ⟨hy0, hy1⟩ := hh1c_y_bounds hx0 hx1 ha0 ha1 hz0 hz1
      have he := hh1_eps_le hy0 hy1
      have he0 := hh1_eps_nonneg (hh1cy x a z)
      have hinv : 1 / (a + z) ≤ 1 / 2 := by
        rw [div_le_div_iff₀ (by linarith) (by norm_num)]; linarith
      have hinv0 : 0 ≤ 1 / (a + z) := div_nonneg zero_le_one (by linarith)
      simp only [hD]
      set L := -(15 * (x - 1) ^ 3 / (8 * (1 + x) * (35 * x + 13) * (z - 1) ^ 2)) with hLdef
      set M := hh1cGu x (hsUl x z) - 7 / 96 * hh1cR2u x a z with hMdef
      have hM' : -(1 / 5) ≤ M := by rw [hMdef]; linarith
      have hLM : L * M ≤ 15 / 1992 * (1 / 5) := by
        have := mul_le_mul_of_nonpos_left hM' hL1
        linarith
      have hEp : hh1eps (hh1cy x a z) * (1 / (a + z)) ≤ 1 / 625 * (1 / 2) := by
        exact mul_le_mul he hinv hinv0 (by norm_num)
      nlinarith)
  linarith

/-- **Step B for `F₁`** at a fixed norm. -/
theorem hh1c_stepB1 {x a b b' u : ℝ} (hx0 : 8 / 5 ≤ x) (hx1 : x ≤ 2) (ha0 : 1 ≤ a)
    (ha1 : a ≤ 7 / 6) (hb0 : x + 1 / 2 * (a - 1) ≤ b) (hbb : b ≤ b') (hb1 : b' ≤ x + 4 / 5 * (a - 1))
    (hu0 : 3 / 4 ≤ u) (hu1 : u ≤ 3 / 4 + 2 / 249) :
    hh1cF1 x a b' u ≤ hh1cF1 x a b u := by
  have hx : 0 < x := by linarith
  have ha : 0 < a := by linarith
  set D : ℝ → ℝ := fun z =>
    0 * (hh1cGx x u - 7 / 96 * hh1cR1x x a z u) + 1 * (-(7 / 96) * hh1cR1b x a z u) +
      0 * (hh1cGu x u - 7 / 96 * (hh1cR2u x a z + (hh1cT x a z - 2) * hh1cwu x a z)) +
      7 / 96 * hh1eps (hh1cy x a z) * (-(2 * (1 + x) / hh1cK x a) * 0 + 1 / (a + z) * 1) with hD
  have key := ss_le_of_deriv (f := fun z => -hh1cF1 x a z u) (f' := fun z => -D z) hbb
    (fun z hz => by
      have hz1 : 0 < z := by nlinarith [hz.1]
      exact (hh1c_F1_hasDerivAt (hasDerivAt_const z x) (hasDerivAt_id' z) (hasDerivAt_const z u)
        hx ha hz1).neg)
    (fun z hz => by
      have hz0 : x + 1 / 2 * (a - 1) ≤ z := by linarith [hz.1]
      have hz1 : z ≤ x + 4 / 5 * (a - 1) := by linarith [hz.2]
      have hB := hh1c_claim_B1 hx0 hx1 ha0 (by linarith) hz0 hz1 hu0 hu1
      obtain ⟨hy0, hy1⟩ := hh1c_y_bounds hx0 hx1 ha0 ha1 hz0 hz1
      have he := hh1_eps_le hy0 hy1
      have hinv : 1 / (a + z) ≤ 1 / 2 := by
        rw [div_le_div_iff₀ (by nlinarith) (by norm_num)]; nlinarith
      have hinv0 : 0 ≤ 1 / (a + z) := by
        have : 0 < a + z := by nlinarith
        positivity
      have hEp : hh1eps (hh1cy x a z) * (1 / (a + z)) ≤ 1 / 625 * (1 / 2) :=
        mul_le_mul he hinv hinv0 (by norm_num)
      simp only [hD]
      nlinarith)
  linarith

/-- **Step A for `F₀`** along `β* = x + (10/13)(α - 1)`, `u = u_ℓ(x, β*)`, up to `α ≤ a_U(x)`
(`LOW_RATIO_CENTRAL_HAND_SIGN` (22)). -/
theorem hh1c_stepA0 {x a a' : ℝ} (hx0 : 329 / 200 ≤ x) (hx1 : x ≤ 2) (ha0 : 1 ≤ a) (haa : a ≤ a')
    (ha1 : a' ≤ (1013 * x + 676) / 2340) :
    hh1cF0 x a' (x + 10 / 13 * (a' - 1)) (hsUl x (x + 10 / 13 * (a' - 1))) ≤
      hh1cF0 x a (x + 10 / 13 * (a - 1)) (hsUl x (x + 10 / 13 * (a - 1))) := by
  have hx : 0 < x := by linarith
  obtain ⟨Bf, hBf⟩ : ∃ Bf : ℝ → ℝ, Bf = fun s => x + 10 / 13 * (s - 1) := ⟨_, rfl⟩
  have hBv : ∀ s, Bf s = x + 10 / 13 * (s - 1) := fun s => by rw [hBf]
  have hBd : ∀ s, HasDerivAt Bf (10 / 13) s := fun s => by
    have := ((hasDerivAt_id' s).sub_const 1).const_mul (10 / 13) |>.const_add x
    rw [hBf]; simpa using this
  set D : ℝ → ℝ := fun z =>
    0 * (hh1cGx x (hsUl x (Bf z)) - 7 / 96 * hh1cR2x x z (Bf z) (hsUl x (Bf z))) +
      1 * (-(7 / 96) * hh1cR2a x z (Bf z) (hsUl x (Bf z))) +
      10 / 13 * (-(7 / 96) * hh1cR2b x z (Bf z) (hsUl x (Bf z))) +
      -(15 * (x - 1) ^ 3 / (8 * (1 + x) * (35 * x + 13) * (Bf z - 1) ^ 2)) * (10 / 13) *
        (hh1cGu x (hsUl x (Bf z)) - 7 / 96 * hh1cR2u x z (Bf z)) +
      7 / 96 * hh1eps (hh1cy x z (Bf z)) *
        (-(2 * (1 + x) / hh1cK x z) * 0 + (1 / z + 1 / (z + Bf z) - 2 * z / hh1cK x z) * 1 +
          1 / (z + Bf z) * (10 / 13)) with hD
  have key := ss_le_of_deriv (f := fun z => -hh1cF0 x z (Bf z) (hsUl x (Bf z))) (f' := fun z => -D z)
    haa
    (fun z hz => by
      have hz0 : 1 ≤ z := le_trans ha0 hz.1
      have hBz : x ≤ Bf z := by rw [hBv]; nlinarith
      have hU := (hh1_Ul_hasDerivAt (x := x) (b := Bf z) (by linarith) (by linarith)).comp z (hBd z)
      exact (hh1c_F0_hasDerivAt (hasDerivAt_const z x) (hasDerivAt_id' z) (hBd z) hU hx
        (by linarith) (by linarith)).neg)
    (fun z hz => by
      have hz0 : 1 ≤ z := by linarith [hz.1]
      have hz1 : z ≤ (1013 * x + 676) / 2340 := by linarith [hz.2]
      have hz2 : z ≤ 7 / 6 := by linarith
      have hBz0 : x + 1 / 2 * (z - 1) ≤ Bf z := by rw [hBv]; nlinarith
      have hBz1 : Bf z ≤ x + 4 / 5 * (z - 1) := by rw [hBv]; nlinarith
      have hxB : x ≤ Bf z := by nlinarith
      obtain ⟨hU0, hU1⟩ := hh1_Ul_bounds (by linarith) hx1 hxB
      obtain ⟨hL0, hL1⟩ := hh1_Ul_deriv_bounds (by linarith) hx1 hxB
      have hA := hh1c_claim_A0 (b := Bf z) hx0 hx1 hz0 (by linarith) hU0 hU1
      rw [← hBv z] at hA
      have hM := hh1c_claim_M0 (by linarith) hx1 hz0 (by linarith) hBz0 hBz1 hU0 hU1
      obtain ⟨hy0, hy1⟩ := hh1c_y_bounds (by linarith) hx1 hz0 hz2 hBz0 hBz1
      have he := hh1_eps_le hy0 hy1
      have he0 := hh1_eps_nonneg (hh1cy x z (Bf z))
      have hK : 0 < hh1cK x z := by unfold hh1cK; positivity
      have hzB : 0 < z + Bf z := by linarith
      have hW : 1 / z + 1 / (z + Bf z) - 2 * z / hh1cK x z + 1 / (z + Bf z) * (10 / 13) ≤ 49 / 26 := by
        have h1 : 1 / z ≤ 1 := by rw [div_le_one (by linarith)]; exact hz0
        have h2 : 1 / (z + Bf z) ≤ 1 / 2 := by
          rw [div_le_div_iff₀ hzB (by norm_num)]; linarith
        have h3 : 0 ≤ 2 * z / hh1cK x z := by positivity
        nlinarith
      simp only [hD]
      set L := -(15 * (x - 1) ^ 3 / (8 * (1 + x) * (35 * x + 13) * (Bf z - 1) ^ 2)) with hLdef
      set M := hh1cGu x (hsUl x (Bf z)) - 7 / 96 * hh1cR2u x z (Bf z) with hMdef
      have hM' : -(1 / 5) ≤ M := by rw [hMdef]; linarith
      have hLM : L * M ≤ 15 / 1992 * (1 / 5) := by
        have := mul_le_mul_of_nonpos_left hM' hL1
        linarith
      set W := 1 / z + 1 / (z + Bf z) - 2 * z / hh1cK x z with hWdef
      have hEp : hh1eps (hh1cy x z (Bf z)) * (W * 1 + 1 / (z + Bf z) * (10 / 13)) ≤
          1 / 625 * (49 / 26) := by
        rcases le_total 0 (W * 1 + 1 / (z + Bf z) * (10 / 13)) with h | h
        · calc _ ≤ 1 / 625 * (W * 1 + 1 / (z + Bf z) * (10 / 13)) :=
                mul_le_mul_of_nonneg_right he h
            _ ≤ _ := by nlinarith
        · nlinarith [mul_nonpos_of_nonneg_of_nonpos he0 h]
      nlinarith)
  simp only [hBv] at key
  linarith

/-- **Step X for `F₁`** along `β = x + (10/13)(α - 1)`, `u = V̄(x)` at fixed `α`. -/
theorem hh1c_stepX1 {x x' a : ℝ} (hx0 : 8 / 5 ≤ x) (hxx : x ≤ x') (hx1 : x' ≤ 2) (ha0 : 1 ≤ a)
    (ha1 : a ≤ 7 / 6) :
    hh1cF1 x' a (x' + 10 / 13 * (a - 1)) (hsVbar x') ≤
      hh1cF1 x a (x + 10 / 13 * (a - 1)) (hsVbar x) := by
  have ha : 0 < a := by linarith
  obtain ⟨Bf, hBf⟩ : ∃ Bf : ℝ → ℝ, Bf = fun s => s + 10 / 13 * (a - 1) := ⟨_, rfl⟩
  have hBv : ∀ s, Bf s = s + 10 / 13 * (a - 1) := fun s => by rw [hBf]
  have hBd : ∀ s, HasDerivAt Bf 1 s := fun s => by
    rw [hBf]; simpa using (hasDerivAt_id' s).add_const (10 / 13 * (a - 1))
  set D : ℝ → ℝ := fun z =>
    1 * (hh1cGx z (hsVbar z) - 7 / 96 * hh1cR1x z a (Bf z) (hsVbar z)) +
      1 * (-(7 / 96) * hh1cR1b z a (Bf z) (hsVbar z)) +
      2 * (2 * (z - 1) * ((z + 1) * (35 * z + 13)) - (z - 1) ^ 2 * (70 * z + 48)) /
          ((z + 1) * (35 * z + 13)) ^ 2 *
        (hh1cGu z (hsVbar z) - 7 / 96 * (hh1cR2u z a (Bf z) + (hh1cT z a (Bf z) - 2) * hh1cwu z a (Bf z))) +
      7 / 96 * hh1eps (hh1cy z a (Bf z)) * (-(2 * (1 + z) / hh1cK z a) * 1 + 1 / (a + Bf z) * 1) with hD
  have key := ss_le_of_deriv (f := fun z => -hh1cF1 z a (Bf z) (hsVbar z)) (f' := fun z => -D z) hxx
    (fun z hz => by
      have hz0 : 8 / 5 ≤ z := le_trans hx0 hz.1
      have hBp : 0 < Bf z := by rw [hBv]; nlinarith
      exact (hh1c_F1_hasDerivAt (hasDerivAt_id' z) (hBd z) (hh1_Vbar_hasDerivAt (by linarith))
        (by linarith) ha hBp).neg)
    (fun z hz => by
      have hz0 : 8 / 5 ≤ z := by linarith [hz.1]
      have hz1 : z ≤ 2 := by linarith [hz.2]
      have hBz0 : z + 1 / 2 * (a - 1) ≤ Bf z := by rw [hBv]; nlinarith
      have hBz1 : Bf z ≤ z + 4 / 5 * (a - 1) := by rw [hBv]; nlinarith
      obtain ⟨hV0, hV1⟩ := hh1_Vbar_bounds (by linarith) hz1
      have hVd := hh1_Vbar_deriv_nonneg (x := z) (by linarith) hz1
      have hXa := hh1c_claim_X1a (b := Bf z) hz0 hz1 ha0 (by linarith) hV0 hV1
      rw [← hBv z] at hXa
      have hXb := hh1c_claim_X1b (a := a) (b := Bf z) hz0 hz1 ha0 (by linarith) hV0 hV1
      have hFu := hh1c_F1u_nonpos hz0 hz1 ha0 ha1 hBz0 hBz1 hV0
      have he0 := hh1_eps_nonneg (hh1cy z a (Bf z))
      have hK : 0 < hh1cK z a := by unfold hh1cK; positivity
      have hB : 0 < a + Bf z := by rw [hBv]; nlinarith
      have hneg : -(2 * (1 + z) / hh1cK z a) * 1 + 1 / (a + Bf z) * 1 ≤ 0 := by
        rw [mul_one, mul_one, neg_add_le_iff_le_add, add_zero, div_le_div_iff₀ hB hK]
        unfold hh1cK; rw [hBv]; nlinarith
      simp only [hD]
      nlinarith [mul_nonpos_of_nonneg_of_nonpos hVd hFu, mul_nonpos_of_nonneg_of_nonpos he0 hneg])
  simp only [hBv] at key
  linarith

end SmoothedOctagon
