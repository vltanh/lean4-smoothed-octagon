module

public import SmoothedOctagon.Exclusion.Mixed.ShortHand.Heavy.S1ODeriv
public import SmoothedOctagon.Exclusion.Mixed.ShortHand.Heavy.S1CAux
public import SmoothedOctagon.Exclusion.Mixed.ShortHand.Heavy.S1OClaimS
public import SmoothedOctagon.Exclusion.Mixed.ShortHand.Heavy.S1OClaimF
public import SmoothedOctagon.Exclusion.Mixed.ShortHand.Heavy.S1OClaimB1
public import SmoothedOctagon.Exclusion.Mixed.ShortHand.Heavy.S1OClaimB2

/-!
# Gate S1, outer face: the norm concavity and the monotonicity steps

* `hh1_conc3`, `hh1o_F0_u3`, `hh1o_F1_u3`: both outer tests are concave quadratics in `u` (leading
  coefficient `-(1 + x)²K²/(576α⁴)`), so on `[u₁, u₂]` they are at least the smaller endpoint value;
* `hh1o_stepDS`, `hh1o_stepDg`, `hh1o_stepLo`: `β ↦ F₁` increases on `1 ≤ α ≤ x ≤ 6/5` and on the
  diagonal `α = x`, and decreases on the lower shape `α = (6x + 3)/13`;
* `hh1o_stepB0`, `hh1o_stepBU`: `β ↦ F₀` decreases on the outer `B` box at a fixed norm and along
  the ceiling `u = u_ℓ(x, β)`;
* `hh1o_stepA0`, `hh1o_stepAU`: `α ↦ F₀` increases along `β = x + (10/13)(α - 1)` at a fixed norm
  and along the ceiling.

All derivative signs are the generated claims `S1OClaim*`; the cubic-ceiling defect `ε(y)` is
bounded by `1/400` for `9/14 ≤ y ≤ 1` (`hh1_eps_le'`).
-/

@[expose] public section

namespace SmoothedOctagon

open Set

/-- A concave quadratic is at least the smaller of its endpoint values. -/
theorem hh1_conc3 {f : ℝ → ℝ} {u1 u u2 κ : ℝ} (h1 : u1 ≤ u) (h2 : u ≤ u2) (hκ : 0 ≤ κ)
    (hid : ∀ s, (u2 - u1) * f s - (u2 - s) * f u1 - (s - u1) * f u2 =
      κ * (s - u1) * (u2 - s) * (u2 - u1)) : min (f u1) (f u2) ≤ f u := by
  rcases eq_or_lt_of_le h1 with h | h
  · rw [← h]; exact min_le_left _ _
  have h12 : 0 < u2 - u1 := by linarith
  have hm1 := min_le_left (f u1) (f u2)
  have hm2 := min_le_right (f u1) (f u2)
  have p1 := mul_nonneg (sub_nonneg.2 h2) (sub_nonneg.2 hm1)
  have p2 := mul_nonneg (sub_nonneg.2 h1) (sub_nonneg.2 hm2)
  have p3 := mul_nonneg (mul_nonneg (mul_nonneg hκ (sub_nonneg.2 h1)) (sub_nonneg.2 h2)) h12.le
  have e : (u2 - u1) * (f u - min (f u1) (f u2)) = (u2 - u) * (f u1 - min (f u1) (f u2)) +
      (u - u1) * (f u2 - min (f u1) (f u2)) + κ * (u - u1) * (u2 - u) * (u2 - u1) := by
    linear_combination hid u
  have key : 0 ≤ (u2 - u1) * (f u - min (f u1) (f u2)) := by rw [e]; linarith
  by_contra hc
  have := mul_neg_of_pos_of_neg h12 (sub_neg.2 (not_le.mp hc))
  linarith

theorem hh1o_F0_u3 (x a b u1 u2 : ℝ) : ∀ s, (u2 - u1) * hh1oF0 x a b s -
    (u2 - s) * hh1oF0 x a b u1 - (s - u1) * hh1oF0 x a b u2 =
      (1 + x) ^ 2 * hh1oK a ^ 2 / (576 * a ^ 4) * (s - u1) * (u2 - s) * (u2 - u1) := by
  intro s
  simp only [hh1oF0, hh1oR2, hh1ow, hh1oEL, hh1oG, hh1oE]
  ring

theorem hh1o_F1_u3 (x a b u1 u2 : ℝ) : ∀ s, (u2 - u1) * hh1oF1 x a b s -
    (u2 - s) * hh1oF1 x a b u1 - (s - u1) * hh1oF1 x a b u2 =
      (1 + x) ^ 2 * hh1oK a ^ 2 / (576 * a ^ 4) * (s - u1) * (u2 - s) * (u2 - u1) := by
  intro s
  simp only [hh1oF1, hh1oF0, hh1oR2, hh1ow, hh1oEL, hh1oG, hh1oE]
  ring

theorem hh1o_Cm_mono {x0 x : ℝ} (h0 : 0 < x0) (h : x0 ≤ x) :
    8 * x0 / (9 * x0 + 8) ≤ 8 * x / (9 * x + 8) := by
  rw [div_le_div_iff₀ (by positivity) (by linarith)]; nlinarith

theorem hh1o_Cp_mono {x x1 : ℝ} (h0 : 0 < x) (h : x ≤ x1) :
    x * (7 * x + 1) / (4 * x ^ 2 + 11 * x + 1) ≤ x1 * (7 * x1 + 1) /
        (4 * x1 ^ 2 + 11 * x1 + 1) := by
  have h1 : 0 < x1 := by linarith
  rw [div_le_div_iff₀ (by positivity) (by positivity)]
  nlinarith [mul_nonneg (sub_nonneg.2 h) (by positivity :
      (0 : ℝ) ≤ 73 * x * x1 + 7 * x + 7 * x1 + 1)]

theorem hh1o_Vbar_mono {x y : ℝ} (hx : 1 < x) (hxy : x ≤ y) (hy : y ≤ 2) : hsVbar x ≤ hsVbar y :=
  ss_le_of_deriv (f := hsVbar) (f' := fun z => 2 * (2 * (z - 1) * ((z + 1) * (35 * z + 13)) -
      (z - 1) ^ 2 * (70 * z + 48)) / ((z + 1) * (35 * z + 13)) ^ 2) hxy
    (fun z hz => hh1_Vbar_hasDerivAt (by linarith [hz.1]))
    (fun z hz => hh1_Vbar_deriv_nonneg (by linarith [hz.1]) (by linarith [hz.2]))

/-- The lower chord `L(x) = 8/17 + (32/221)(x - 1) ≤ C₋(x) = 8x/(9x + 8)` on `[1, 2]`. -/
theorem hh1o_chord {x : ℝ} (hx : 1 ≤ x) (hx2 : x ≤ 2) :
    8 / 17 + 32 / 221 * (x - 1) ≤ 8 * x / (9 * x + 8) := by
  rw [le_div_iff₀ (by linarith)]
  nlinarith [mul_nonneg (sub_nonneg.2 hx) (sub_nonneg.2 hx2)]

theorem hh1_eps_le' {y : ℝ} (h0 : 9 / 14 ≤ y) (h1 : y ≤ 1) : hh1eps y ≤ 1 / 400 := by
  have hy : 0 < y + 1 := by linarith
  have e : hh1eps y = ((1 - y) / (y + 1)) ^ 4 := by unfold hh1eps; ring
  have t0 : 0 ≤ (1 - y) / (y + 1) := div_nonneg (by linarith) hy.le
  have t1 : (1 - y) / (y + 1) ≤ 5 / 23 := by rw [div_le_iff₀ hy]; linarith
  rw [e]
  calc ((1 - y) / (y + 1)) ^ 4 ≤ (5 / 23) ^ 4 := pow_le_pow_left₀ t0 t1 4
    _ ≤ 1 / 400 := by norm_num

theorem hh1o_eps_le {a b : ℝ} (ha : 0 < a) (h1 : 5 * a ≤ 4 * b) (h2 : 2 * b ≤ 5 * a) :
    hh1eps (hh1oy a b) ≤ 1 / 400 := by
  apply hh1_eps_le'
  · unfold hh1oy; rw [le_div_iff₀ (by positivity)]; linarith
  · unfold hh1oy; rw [div_le_one (by positivity)]; linarith

/-- **Step S**: on `1 ≤ α ≤ x ≤ 6/5`, `β ↦ F₁(x, α, β, u)` increases. -/
theorem hh1o_stepDS {x a b b' u : ℝ} (hx0 : 1 < x) (hx1 : x ≤ 6 / 5) (ha0 : 1 ≤ a) (ha1 : a ≤ x)
    (hb0 : x ≤ b) (hbb : b ≤ b') (hb1 : b' ≤ x + 10 / 13 * (x - 1)) (hu0 : 3 / 4 ≤ u)
    (hu1 : u ≤ 9083 / 12100) :
    hh1oF1 x a b u ≤ hh1oF1 x a b' u := by
  set D : ℝ → ℝ := fun z =>
    0 * (hh1oGa x a u - 7 / 96 * hh1oR1a x a z u) + 1 * (-(7 / 96) * hh1oR1b x a z u) +
      0 * (hh1oGu x a u - 7 / 96 * hh1oR1u x a z) +
      7 / 96 * hh1eps (hh1oy a z) * ((1 / (a + z) - 1 / a) * 0 + 1 / (a + z) * 1) with hD
  exact ss_le_of_deriv (f := fun z => hh1oF1 x a z u) (f' := D) hbb
    (fun z hz => hh1o_F1_hasDerivAt (x := x) (hasDerivAt_const z a) (hasDerivAt_id' z)
      (hasDerivAt_const z u) (by linarith) (by linarith [hz.1]))
    (fun z hz => by
      have hc := hh1o_claim_dS (x := x) (a := a) (t := z - x) (u := u) hx0.le hx1 ha0 (by linarith)
        (by linarith [hz.1]) (by linarith [hz.2]) hu0 hu1
      rw [show x + (z - x) = z by ring] at hc
      have he0 := hh1_eps_nonneg (hh1oy a z)
      have haz : 0 < a + z := by linarith [hz.1]
      have hi : 0 ≤ 1 / (a + z) := by positivity
      have hP := mul_nonneg he0 hi
      simp only [hD]
      linarith)

/-- **Step Dg**: on the diagonal `α = x`, `β ↦ F₁(x, x, β, u)` increases. -/
theorem hh1o_stepDg {x b b' u : ℝ} (hx0 : 1 < x) (hx1 : x ≤ 2) (hb0 : x ≤ b) (hbb : b ≤ b')
    (hb1 : b' ≤ x + 10 / 13 * (x - 1)) (hu0 : 3 / 4 ≤ u) (hu1 : u ≤ 755 / 996) :
    hh1oF1 x x b u ≤ hh1oF1 x x b' u := by
  set D : ℝ → ℝ := fun z =>
    0 * (hh1oGa x x u - 7 / 96 * hh1oR1a x x z u) + 1 * (-(7 / 96) * hh1oR1b x x z u) +
      0 * (hh1oGu x x u - 7 / 96 * hh1oR1u x x z) +
      7 / 96 * hh1eps (hh1oy x z) * ((1 / (x + z) - 1 / x) * 0 + 1 / (x + z) * 1) with hD
  exact ss_le_of_deriv (f := fun z => hh1oF1 x x z u) (f' := D) hbb
    (fun z hz => hh1o_F1_hasDerivAt (x := x) (hasDerivAt_const z x) (hasDerivAt_id' z)
      (hasDerivAt_const z u) (by linarith) (by linarith [hz.1]))
    (fun z hz => by
      have hc := hh1o_claim_dg (x := x) (t := z - x) (u := u) hx0.le hx1 (by linarith [hz.1])
        (by linarith [hz.2]) hu0 hu1
      rw [show x + (z - x) = z by ring] at hc
      have he0 := hh1_eps_nonneg (hh1oy x z)
      have hxz : 0 < x + z := by linarith [hz.1]
      have hi : 0 ≤ 1 / (x + z) := by positivity
      have hP := mul_nonneg he0 hi
      simp only [hD]
      linarith)

/-- **Step Lo**: on the lower shape `α = (6x + 3)/13`, `β ↦ F₁` decreases. -/
theorem hh1o_stepLo {x b b' u : ℝ} (hx0 : 5 / 3 ≤ x) (hx1 : x ≤ 2) (hb0 : x ≤ b) (hbb : b ≤ b')
    (hb1 : b' ≤ x + 10 / 13 * ((6 * x + 3) / 13 - 1)) (hu0 : 3 / 4 ≤ u) (hu1 : u ≤ 755 / 996) :
    hh1oF1 x ((6 * x + 3) / 13) b' u ≤ hh1oF1 x ((6 * x + 3) / 13) b u := by
  have hA1 : 1 ≤ (6 * x + 3) / 13 := by linarith
  have hA2 : (6 * x + 3) / 13 ≤ 15 / 13 := by linarith
  set D : ℝ → ℝ := fun z =>
    0 * (hh1oGa x ((6 * x + 3) / 13) u - 7 / 96 * hh1oR1a x ((6 * x + 3) / 13) z u) +
      1 * (-(7 / 96) * hh1oR1b x ((6 * x + 3) / 13) z u) +
      0 * (hh1oGu x ((6 * x + 3) / 13) u - 7 / 96 * hh1oR1u x ((6 * x + 3) / 13) z) +
      7 / 96 * hh1eps (hh1oy ((6 * x + 3) / 13) z) *
        ((1 / ((6 * x + 3) / 13 + z) - 1 / ((6 * x + 3) / 13)) * 0 + 1 / ((6 * x + 3) / 13 + z) * 1)
    with hD
  have key := ss_le_of_deriv (f := fun z => -hh1oF1 x ((6 * x + 3) / 13) z u) (f' := fun z => -D z)
    hbb
    (fun z hz => (hh1o_F1_hasDerivAt (x := x) (hasDerivAt_const z ((6 * x + 3) / 13))
      (hasDerivAt_id' z) (hasDerivAt_const z u) (by linarith) (by linarith [hz.1])).neg)
    (fun z hz => by
      have hc := hh1o_claim_lo (x := x) (t := z - x) (u := u) hx0 hx1 (by linarith [hz.1])
        (by linarith [hz.2]) hu0 hu1
      rw [show x + (z - x) = z by ring] at hc
      have he := hh1o_eps_le (a := (6 * x + 3) / 13) (b := z) (by linarith) (by linarith [hz.1])
        (by linarith [hz.2])
      have he0 := hh1_eps_nonneg (hh1oy ((6 * x + 3) / 13) z)
      have hAz : 1 ≤ (6 * x + 3) / 13 + z := by linarith [hz.1]
      have hi0 : 0 ≤ 1 / ((6 * x + 3) / 13 + z) := by positivity
      have hi1 : 1 / ((6 * x + 3) / 13 + z) ≤ 1 := by rw [div_le_one (by linarith)]; exact hAz
      have hP := mul_le_mul he hi1 hi0 (by norm_num)
      simp only [hD]
      linarith)
  linarith

/-- **Step B₀**: on the outer `B` box `β ↦ F₀(x, α, β, u)` decreases at a fixed norm. -/
theorem hh1o_stepB0 {x a b b' u : ℝ} (hx0 : 3 / 2 ≤ x) (hx1 : x ≤ 2) (ha0 : 1 ≤ a) (ha1 : a ≤ 6 / 5)
    (hb0 : x + 5 / 9 * (a - 1) ≤ b) (hbb : b ≤ b') (hb1 : b' ≤ x + 10 / 13 * (a - 1))
    (hu0 : 3 / 4 ≤ u) (hu1 : u ≤ 3 / 4 + 2 / 249) :
    hh1oF0 x a b' u ≤ hh1oF0 x a b u := by
  set D : ℝ → ℝ := fun z =>
    0 * (hh1oGa x a u - 7 / 96 * hh1oR2a x a z u) + 1 * (-(7 / 96) * hh1oR2b x a z u) +
      0 * (hh1oGu x a u - 7 / 96 * hh1oR2u x a z) +
      7 / 96 * hh1eps (hh1oy a z) * ((1 / (a + z) - 1 / a) * 0 + 1 / (a + z) * 1) with hD
  have hA : 0 ≤ a - 1 := by linarith
  have key := ss_le_of_deriv (f := fun z => -hh1oF0 x a z u) (f' := fun z => -D z) hbb
    (fun z hz => (hh1o_F0_hasDerivAt (x := x) (hasDerivAt_const z a) (hasDerivAt_id' z)
      (hasDerivAt_const z u) (by linarith) (by nlinarith [hz.1])).neg)
    (fun z hz => by
      have hz0 : x + 5 / 9 * (a - 1) ≤ z := by linarith [hz.1]
      have hz1 : z ≤ x + 10 / 13 * (a - 1) := by linarith [hz.2]
      have hc := hh1o_claim_OB0 hx0 hx1 ha0 (by linarith) hz0 hz1 hu0 hu1
      have he := hh1o_eps_le (a := a) (b := z) (by linarith) (by nlinarith) (by nlinarith)
      have hAz : 1 ≤ a + z := by nlinarith
      have hi0 : 0 ≤ 1 / (a + z) := by positivity
      have hi1 : 1 / (a + z) ≤ 1 := by rw [div_le_one (by linarith)]; exact hAz
      have hP := mul_le_mul he hi1 hi0 (by norm_num)
      simp only [hD]
      linarith)
  linarith

/-- `|∂_βu_ℓ| = 15(x - 1)³/(8S(35x + 13)(β - 1)²) ≤ 15(x - 1)/(8S(35x + 13))` for `β ≥ x > 1`. -/
theorem hh1o_Ulp_le {x z : ℝ} (hx : 1 < x) (hz : x ≤ z) :
    15 * (x - 1) ^ 3 / (8 * (1 + x) * (35 * x + 13) * (z - 1) ^ 2) ≤
      15 * (x - 1) / (8 * (1 + x) * (35 * x + 13)) := by
  have h1 : 0 < x - 1 := by linarith
  have h2 : 0 < z - 1 := by linarith
  rw [div_le_div_iff₀ (by positivity) (by positivity)]
  have h3 : (x - 1) ^ 2 ≤ (z - 1) ^ 2 := by nlinarith
  have h4 : 0 ≤ 15 * (x - 1) * (8 * (1 + x) * (35 * x + 13)) := by positivity
  nlinarith [mul_le_mul_of_nonneg_right h3 h4]

/-- **Step B along the ceiling**: `β ↦ F₀(x, α, β, u_ℓ(x, β))` decreases on the outer `B` box. -/
theorem hh1o_stepBU {x a b b' : ℝ} (hx0 : 3 / 2 ≤ x) (hx1 : x ≤ 2) (ha0 : 1 ≤ a) (ha1 : a ≤ 6 / 5)
    (hb0 : x + 5 / 9 * (a - 1) ≤ b) (hbb : b ≤ b') (hb1 : b' ≤ x + 10 / 13 * (a - 1)) :
    hh1oF0 x a b' (hsUl x b') ≤ hh1oF0 x a b (hsUl x b) := by
  have hA : 0 ≤ a - 1 := by linarith
  set D : ℝ → ℝ := fun z =>
    0 * (hh1oGa x a (hsUl x z) - 7 / 96 * hh1oR2a x a z (hsUl x z)) +
      1 * (-(7 / 96) * hh1oR2b x a z (hsUl x z)) +
      -(15 * (x - 1) ^ 3 / (8 * (1 + x) * (35 * x + 13) * (z - 1) ^ 2)) *
        (hh1oGu x a (hsUl x z) - 7 / 96 * hh1oR2u x a z) +
      7 / 96 * hh1eps (hh1oy a z) * ((1 / (a + z) - 1 / a) * 0 + 1 / (a + z) * 1) with hD
  have key := ss_le_of_deriv (f := fun z => -hh1oF0 x a z (hsUl x z)) (f' := fun z => -D z) hbb
    (fun z hz => (hh1o_F0_hasDerivAt (x := x) (hasDerivAt_const z a) (hasDerivAt_id' z)
      (hh1_Ul_hasDerivAt (by linarith) (by nlinarith [hz.1])) (by linarith)
      (by nlinarith [hz.1])).neg)
    (fun z hz => by
      have hz0 : x + 5 / 9 * (a - 1) ≤ z := by linarith [hz.1]
      have hz1 : z ≤ x + 10 / 13 * (a - 1) := by linarith [hz.2]
      have hxz : x ≤ z := by nlinarith
      obtain ⟨hU0, hU1⟩ := hh1_Ul_bounds (by linarith) hx1 hxz
      have hc := hh1o_claim_OBV hx0 hx1 ha0 (by linarith) hz0 hz1 hU0 hU1
      have hc0 := hh1o_claim_OB0 hx0 hx1 ha0 (by linarith) hz0 hz1 hU0 hU1
      obtain ⟨hL0, hL1⟩ := hh1_Ul_deriv_bounds (by linarith) hx1 hxz
      have hUV := hh1o_Ulp_le (x := x) (z := z) (by linarith) hxz
      have he := hh1o_eps_le (a := a) (b := z) (by linarith) (by nlinarith) (by nlinarith)
      have hAz : 5 / 2 ≤ a + z := by nlinarith
      have hi0 : 0 ≤ 1 / (a + z) := by positivity
      have hi1 : 1 / (a + z) ≤ 2 / 5 := by
        rw [div_le_div_iff₀ (by linarith) (by norm_num)]; linarith
      have hP := mul_le_mul he hi1 hi0 (by norm_num)
      simp only [hD]
      set U' := 15 * (x - 1) ^ 3 / (8 * (1 + x) * (35 * x + 13) * (z - 1) ^ 2) with hU'
      set M := hh1oGu x a (hsUl x z) - 7 / 96 * hh1oR2u x a z with hM
      rcases le_total 0 M with hm | hm
      · have := mul_nonneg (by linarith : (0 : ℝ) ≤ U') hm
        linarith
      · have := mul_le_mul_of_nonpos_right hUV hm
        linarith)
  linarith

/-- **Step A₀**: `α ↦ F₀(x, α, x + (10/13)(α - 1), u)` increases on the outer `B` box. -/
theorem hh1o_stepA0 {x a a' u : ℝ} (hx0 : 3 / 2 ≤ x) (hx1 : x ≤ 2) (ha0 : 1 ≤ a) (haa : a ≤ a')
    (ha1 : a' ≤ 6 / 5) (hu0 : 3 / 4 ≤ u) (hu1 : u ≤ 3 / 4 + 2 / 249) :
    hh1oF0 x a (x + 10 / 13 * (a - 1)) u ≤ hh1oF0 x a' (x + 10 / 13 * (a' - 1)) u := by
  obtain ⟨Bf, hBf⟩ : ∃ Bf : ℝ → ℝ, Bf = fun s => x + 10 / 13 * (s - 1) := ⟨_, rfl⟩
  have hBv : ∀ s, Bf s = x + 10 / 13 * (s - 1) := fun s => by rw [hBf]
  have hBd : ∀ s, HasDerivAt Bf (10 / 13) s := fun s => by
    have := ((hasDerivAt_id' s).sub_const 1).const_mul (10 / 13) |>.const_add x
    rw [hBf]; simpa using this
  set D : ℝ → ℝ := fun z =>
    1 * (hh1oGa x z u - 7 / 96 * hh1oR2a x z (Bf z) u) + 10 / 13 * (-(7 / 96) * hh1oR2b x z
        (Bf z) u) +
      0 * (hh1oGu x z u - 7 / 96 * hh1oR2u x z (Bf z)) +
      7 / 96 * hh1eps (hh1oy z (Bf z)) * ((1 / (z + Bf z) - 1 / z) * 1 + 1 / (z + Bf z) * (10 / 13))
    with hD
  have key := ss_le_of_deriv (f := fun z => hh1oF0 x z (Bf z) u) (f' := D) haa
    (fun z hz => by
      have hz0 : 0 < z := by linarith [hz.1]
      have hBz : 0 < Bf z := by rw [hBv]; nlinarith [hz.1]
      exact hh1o_F0_hasDerivAt (x := x) (hasDerivAt_id' z) (hBd z) (hasDerivAt_const z u) hz0 hBz)
    (fun z hz => by
      have hz0 : 1 ≤ z := by linarith [hz.1]
      have hz1 : z ≤ 6 / 5 := by linarith [hz.2]
      have hc := hh1o_claim_OA0 (b := 0) hx0 hx1 hz0 (by linarith) hu0 hu1
      rw [← hBv z] at hc
      have he := hh1o_eps_le (a := z) (b := Bf z) (by linarith) (by rw [hBv]; nlinarith)
        (by rw [hBv]; nlinarith)
      have he0 := hh1_eps_nonneg (hh1oy z (Bf z))
      have hzB : 0 < z + Bf z := by rw [hBv]; nlinarith
      have hi0 : 0 ≤ 1 / (z + Bf z) := by positivity
      have hi1 : 1 / z ≤ 1 := by rw [div_le_one (by linarith)]; exact hz0
      have hW : -1 ≤ (1 / (z + Bf z) - 1 / z) * 1 + 1 / (z + Bf z) * (10 / 13) := by nlinarith
      have hP := mul_le_mul_of_nonneg_left hW he0
      simp only [hD]
      linarith)
  simp only [hBv] at key
  exact key

/-- **Step A along the ceiling**: `α ↦ F₀(x, α, β*(α), u_ℓ(x, β*(α)))`, `β* = x + (10/13)(α - 1)`,
increases on the outer `B` box. -/
theorem hh1o_stepAU {x a a' : ℝ} (hx0 : 3 / 2 ≤ x) (hx1 : x ≤ 2) (ha0 : 1 ≤ a) (haa : a ≤ a')
    (ha1 : a' ≤ 6 / 5) :
    hh1oF0 x a (x + 10 / 13 * (a - 1)) (hsUl x (x + 10 / 13 * (a - 1))) ≤
      hh1oF0 x a' (x + 10 / 13 * (a' - 1)) (hsUl x (x + 10 / 13 * (a' - 1))) := by
  obtain ⟨Bf, hBf⟩ : ∃ Bf : ℝ → ℝ, Bf = fun s => x + 10 / 13 * (s - 1) := ⟨_, rfl⟩
  have hBv : ∀ s, Bf s = x + 10 / 13 * (s - 1) := fun s => by rw [hBf]
  have hBd : ∀ s, HasDerivAt Bf (10 / 13) s := fun s => by
    have := ((hasDerivAt_id' s).sub_const 1).const_mul (10 / 13) |>.const_add x
    rw [hBf]; simpa using this
  set D : ℝ → ℝ := fun z =>
    1 * (hh1oGa x z (hsUl x (Bf z)) - 7 / 96 * hh1oR2a x z (Bf z) (hsUl x (Bf z))) +
      10 / 13 * (-(7 / 96) * hh1oR2b x z (Bf z) (hsUl x (Bf z))) +
      -(15 * (x - 1) ^ 3 / (8 * (1 + x) * (35 * x + 13) * (Bf z - 1) ^ 2)) * (10 / 13) *
        (hh1oGu x z (hsUl x (Bf z)) - 7 / 96 * hh1oR2u x z (Bf z)) +
      7 / 96 * hh1eps (hh1oy z (Bf z)) * ((1 / (z + Bf z) - 1 / z) * 1 + 1 / (z + Bf z) * (10 / 13))
    with hD
  have key := ss_le_of_deriv (f := fun z => hh1oF0 x z (Bf z) (hsUl x (Bf z))) (f' := D) haa
    (fun z hz => by
      have hz0 : 1 ≤ z := le_trans ha0 hz.1
      have hBz : x ≤ Bf z := by rw [hBv]; nlinarith
      have hU := (hh1_Ul_hasDerivAt (x := x) (b := Bf z) (by linarith) (by linarith)).comp z (hBd z)
      exact hh1o_F0_hasDerivAt (x := x) (hasDerivAt_id' z) (hBd z) hU (by linarith) (by linarith))
    (fun z hz => by
      have hz0 : 1 ≤ z := by linarith [hz.1]
      have hz1 : z ≤ 6 / 5 := by linarith [hz.2]
      have hBz0 : x + 1 / 2 * (z - 1) ≤ Bf z := by rw [hBv]; nlinarith
      have hBz1 : Bf z ≤ x + 4 / 5 * (z - 1) := by rw [hBv]; nlinarith
      have hxB : x ≤ Bf z := by nlinarith
      obtain ⟨hU0, hU1⟩ := hh1_Ul_bounds (by linarith) hx1 hxB
      obtain ⟨hL0, hL1⟩ := hh1_Ul_deriv_bounds (by linarith) hx1 hxB
      have hc := hh1o_claim_OA0 (b := 0) hx0 hx1 hz0 (by linarith) hU0 hU1
      rw [← hBv z] at hc
      have hM := hh1o_claim_OM1 hx0 hx1 hz0 (by linarith) hBz0 hBz1 hU0 hU1
      have he := hh1o_eps_le (a := z) (b := Bf z) (by linarith) (by rw [hBv]; nlinarith)
        (by rw [hBv]; nlinarith)
      have he0 := hh1_eps_nonneg (hh1oy z (Bf z))
      have hzB : 0 < z + Bf z := by rw [hBv]; nlinarith
      have hi0 : 0 ≤ 1 / (z + Bf z) := by positivity
      have hi1 : 1 / z ≤ 1 := by rw [div_le_one (by linarith)]; exact hz0
      have hW : -1 ≤ (1 / (z + Bf z) - 1 / z) * 1 + 1 / (z + Bf z) * (10 / 13) := by nlinarith
      have hP := mul_le_mul_of_nonneg_left hW he0
      simp only [hD]
      set L := -(15 * (x - 1) ^ 3 / (8 * (1 + x) * (35 * x + 13) * (Bf z - 1) ^ 2)) with hLdef
      set M := hh1oGu x z (hsUl x (Bf z)) - 7 / 96 * hh1oR2u x z (Bf z) with hMdef
      have hM' : M ≤ 1 / 20 := by rw [hMdef]; linarith
      have hLM : -(15 / 1992) * (1 / 20) ≤ L * M := by
        have h1 := mul_le_mul_of_nonpos_left hM' hL1
        linarith
      linarith)
  simp only [hBv] at key
  exact key

end SmoothedOctagon
