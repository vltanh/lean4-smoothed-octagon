module

public import SmoothedOctagon.Exclusion.Mixed.ShortHand.Heavy.S1HandOB4

/-!
# Gate S1 by hand, outer face, branch B: the test `F₀`

`SHORT_OUTER_BETA_LOW_SHAPE`, `SHORT_OUTER_ALPHA_LOW_SHAPE`, `SHORT_OUTER_LOW_SHAPE_TERMINAL`.
On `3/2 ≤ x ≤ 2`, `1 ≤ α ≤ 6/5`, `6α² ≥ x(x + 2)`, `x ≤ β ≤ x + (10/13)(α - 1)`,
`u_f ≤ u ≤ u_ℓ(x, β)`:

* norm concavity at the actual point reduces `u` to the two curves `u_f(x)`, `u_ℓ(x, β)`;
* `β ↦ F₀` decreases with slope `≤ -7/5120` at a fixed norm (`hl1o_F0_bmono`), and along the ceiling
  `u_ℓ(x, β)` as well: `(F₀)_u ≥ -1/6` on the capped strip (`(8)-(15)`; `(F₀)_u` is affine
  decreasing in `u` and concave in `β`) and `0 ≤ -(u_ℓ)_β ≤ 15/1992` (`(16)-(17)`); so `C = 10/13`;
* at `C = 10/13`, `α ↦ F₀` increases at a fixed norm: in the reciprocal shape
  `g′(r) ≤ P′(r) + ce/Z² - (399/400)ce/Z ≤ -1/400` (`ℓ′(y) ≥ (1 - (5/23)⁴)/y`, and
  `P′ = Σ i pᵢ r^{i-1}` decreases in `u ≥ 3/4`); along the ceiling the norm motion costs at most
  `(1/4)(15/1992)(10/13)` per unit of `α` since `(F₀)_u ≤ Γ_u ≤ 1/4` (`(17)`, `(23)`); so
  `α = α_*(x)`, `1` on `x ≤ 5/3`, `(45x + 22)/97` on `x ≥ 5/3` (`(3)`, `(26)`);
* the four terminal curves are positive.

Route: the shape derivative is bounded through the reciprocal-shape form at the single slope
`C = 10/13` (two-variable signs in `(x, r)`), instead of the `C`-concavity and the quadratic
`H` of `SHORT_OUTER_ALPHA_LOW_SHAPE` §1; the terminal curves are cleared and bounded termwise, instead
of the `x`-monotonicity and the grid evaluation at `x = 2` of `SHORT_OUTER_LOW_SHAPE_TERMINAL`.

## Main API

* `hl1o_F0_uquad`, `hl1o_B_F0u_ge`, `hl1o_B_F0u_le`, `hl1o_F0_bmono_ul`, `hl1o_B_amono`,
  `hl1o_B_amono_ul`, `hl1o_B_F0`.
-/

@[expose] public section

namespace SmoothedOctagon

open Set Real



/-! ### The beta motion along the ceiling -/

/-- **`β ↦ F₀(x, α, β, u_ℓ(x, β))` decreases** (`SHORT_OUTER_BETA_LOW_SHAPE` (17)). -/
theorem hl1o_F0_bmono_ul {x a b1 b2 : ℝ} (hx : 3 / 2 ≤ x) (hx2 : x ≤ 2) (ha1 : 1 ≤ a)
    (ha2 : a ≤ 6 / 5) (hcap : x * (x + 2) ≤ 6 * a ^ 2) (hb1 : x ≤ b1) (hb12 : b1 ≤ b2)
    (hb2 : b2 ≤ a * x) : hh1oF0 x a b2 (hsUl x b2) ≤ hh1oF0 x a b1 (hsUl x b1) := by
  have hx1 : 1 < x := by linarith
  have key := ss_le_of_deriv (f := fun t => -hh1oF0 x a t (hsUl x t))
    (f' := fun t => -(0 * (hh1oGa x a (hsUl x t) - 7 / 96 * hh1oR2a x a t (hsUl x t)) +
      1 * (-(7 / 96) * hh1oR2b x a t (hsUl x t)) +
      -(15 * (x - 1) ^ 3 / (8 * (1 + x) * (35 * x + 13) * (t - 1) ^ 2)) *
        (hh1oGu x a (hsUl x t) - 7 / 96 * hh1oR2u x a t) +
      7 / 96 * hh1eps (hh1oy a t) * ((1 / (a + t) - 1 / a) * 0 + 1 / (a + t) * 1)))
    (x := b1) (y := b2) hb12
    (fun t ht => (hh1o_F0_hasDerivAt (x := x) (hasDerivAt_const t a) (hasDerivAt_id' t)
      (hh1_Ul_hasDerivAt hx1 (by linarith [ht.1])) (by linarith)
      (by linarith [ht.1])).neg)
    (fun t ht => by
      have ht1 : x ≤ t := by linarith [ht.1]
      have ht2 : t ≤ a * x := by linarith [ht.2]
      obtain ⟨hU0, hU1⟩ := hh1_Ul_bounds hx1 hx2 ht1
      obtain ⟨hd0, hd1⟩ := hh1_Ul_deriv_bounds hx1 hx2 ht1
      have hb := hl1o_F0_bderiv hx hx2 ha1 ha2 ht1 ht2 hU0
      have hu := hl1o_B_F0u_ge (u := hsUl x t) hx hx2 ha1 ha2 hcap ht1 ht2 (by linarith)
      have hprod : -(15 * (x - 1) ^ 3 / (8 * (1 + x) * (35 * x + 13) * (t - 1) ^ 2)) *
          (hh1oGu x a (hsUl x t) - 7 / 96 * hh1oR2u x a t) ≤ 15 / 1992 * (1 / 6) := by
        generalize -(15 * (x - 1) ^ 3 / (8 * (1 + x) * (35 * x + 13) * (t - 1) ^ 2)) = U' at hd0 hd1 ⊢
        generalize hh1oGu x a (hsUl x t) - 7 / 96 * hh1oR2u x a t = G at hu ⊢
        rcases le_total 0 G with hG | hG
        · nlinarith
        · have := mul_le_mul (show -U' ≤ 15 / 1992 by linarith) (show -G ≤ 1 / 6 by linarith)
            (by linarith) (by norm_num)
          nlinarith
      simp only [zero_mul, one_mul, mul_zero, zero_add, mul_one]
      linarith)
  linarith

/-- **`α ↦ F₀(x, α, x + (10/13)(α - 1), u)` increases** at a fixed norm `u ≥ 3/4`. -/
theorem hl1o_B_amono {x a1 a2 u : ℝ} (hx : 3 / 2 ≤ x) (hx2 : x ≤ 2) (h1 : 1 ≤ a1) (h12 : a1 ≤ a2)
    (h2 : a2 ≤ 6 / 5) (hu : 3 / 4 ≤ u) :
    hh1oF0 x a1 (x + 10 / 13 * (a1 - 1)) u + 1 / 400 * (1 / a1 - 1 / a2) ≤
      hh1oF0 x a2 (x + 10 / 13 * (a2 - 1)) u := by
  have hx0 : 0 < x := by linarith
  have hZ : ∀ a' : ℝ, 1 ≤ a' → 0 < 1 + 10 / 13 + (x - 10 / 13) * (1 / a') := by
    intro a' h
    have : 0 < (x - 10 / 13) * (1 / a') := mul_pos (by linarith) (by positivity)
    linarith
  rw [hl1o_F0_rG hx0 (by linarith) rfl (hZ a1 h1), hl1o_F0_rG hx0 (by linarith) rfl
    (hZ a2 (by linarith))]
  have hr : 1 / a2 ≤ 1 / a1 := one_div_le_one_div_of_le (by linarith) h12
  have key := ss_le_of_deriv (f := fun r => -(hl1G (hl1p0 x (10 / 13) u) (hl1p1 x (10 / 13) u)
      (hl1p2 x (10 / 13) u) (hl1p3 x (10 / 13) u) (hl1p4 x (10 / 13) u) (-(7 / 96)) (1 + 10 / 13)
      (x - 10 / 13) r + r / 400))
    (f' := fun r => -(hl1G1 (hl1p1 x (10 / 13) u) (hl1p2 x (10 / 13) u) (hl1p3 x (10 / 13) u)
      (hl1p4 x (10 / 13) u) (-(7 / 96)) (1 + 10 / 13) (x - 10 / 13) r + 1 / 400)) hr
    (fun r hr' => by
      have hr0 : 5 / 6 ≤ r := by
        have := hr'.1; have : 5 / 6 ≤ 1 / a2 := by
          rw [le_div_iff₀ (by linarith)]; linarith
        linarith
      have hZr : 0 < 1 + 10 / 13 + (x - 10 / 13) * r := by nlinarith
      exact ((hl1G_hasDerivAt hZr).add ((hasDerivAt_id' r).div_const 400)).neg)
    (fun r hr' => by
      have hr0 : 5 / 6 ≤ r := by
        have := hr'.1; have : 5 / 6 ≤ 1 / a2 := by
          rw [le_div_iff₀ (by linarith)]; linarith
        linarith
      have hr1 : r ≤ 1 := by
        have := hr'.2; have : 1 / a1 ≤ 1 := by rw [div_le_one (by linarith)]; exact h1
        linarith
      have := hl1o_B_G1 hx hx2 hr0 hr1 hu
      linarith)
  linarith

/-- `u_ℓ` decreases with slope at most `15/1992` (mean value form). -/
theorem hl1_Ul_mv {x b1 b2 : ℝ} (hx : 1 < x) (hx2 : x ≤ 2) (hb1 : x ≤ b1) (hb12 : b1 ≤ b2) :
    hsUl x b1 - hsUl x b2 ≤ 15 / 1992 * (b2 - b1) ∧ hsUl x b2 ≤ hsUl x b1 := by
  have key := ss_le_of_deriv (f := fun t => hsUl x t + 15 / 1992 * t)
    (f' := fun t => -(15 * (x - 1) ^ 3 / (8 * (1 + x) * (35 * x + 13) * (t - 1) ^ 2)) + 15 / 1992)
    hb12 (fun t ht => (hh1_Ul_hasDerivAt hx (by linarith [ht.1])).add
      ((hasDerivAt_id' t).const_mul _) |>.congr_deriv (by ring))
    (fun t ht => by have := (hh1_Ul_deriv_bounds hx hx2 (by linarith [ht.1] : x ≤ t)).1; linarith)
  have key2 := ss_le_of_deriv (f := fun t => -hsUl x t)
    (f' := fun t => 15 * (x - 1) ^ 3 / (8 * (1 + x) * (35 * x + 13) * (t - 1) ^ 2))
    hb12 (fun t ht => (hh1_Ul_hasDerivAt hx (by linarith [ht.1])).neg |>.congr_deriv (by ring))
    (fun t ht => by have := (hh1_Ul_deriv_bounds hx hx2 (by linarith [ht.1] : x ≤ t)).2; linarith)
  constructor <;> linarith

/-- **`α ↦ F₀` along the ceiling** `u_ℓ(x, x + (10/13)(α - 1))` increases
(`SHORT_OUTER_ALPHA_LOW_SHAPE` (23)). -/
theorem hl1o_B_amono_ul {x a1 a2 : ℝ} (hx : 3 / 2 ≤ x) (hx2 : x ≤ 2) (h1 : 1 ≤ a1) (h12 : a1 ≤ a2)
    (h2 : a2 ≤ 6 / 5) :
    hh1oF0 x a1 (x + 10 / 13 * (a1 - 1)) (hsUl x (x + 10 / 13 * (a1 - 1))) ≤
      hh1oF0 x a2 (x + 10 / 13 * (a2 - 1)) (hsUl x (x + 10 / 13 * (a2 - 1))) := by
  have hx0 : 0 < x := by linarith
  have hx1 : 1 < x := by linarith
  have hb1 : x ≤ x + 10 / 13 * (a1 - 1) := by nlinarith
  have hb12 : x + 10 / 13 * (a1 - 1) ≤ x + 10 / 13 * (a2 - 1) := by nlinarith
  obtain ⟨hmv, hU21⟩ := hl1_Ul_mv hx1 hx2 hb1 hb12
  obtain ⟨hU20, _⟩ := hh1_Ul_bounds hx1 hx2 (hb1.trans hb12)
  obtain ⟨hU10, _⟩ := hh1_Ul_bounds hx1 hx2 hb1
  have hA := hl1o_B_amono hx hx2 h1 h12 h2 hU10
  have hq := hl1o_F0_uquad (b := x + 10 / 13 * (a2 - 1)) (u1 := hsUl x (x + 10 / 13 * (a1 - 1)))
    (u2 := hsUl x (x + 10 / 13 * (a2 - 1))) hx0 (by linarith : (0 : ℝ) < a2)
  have hle := hl1o_B_F0u_le (u := hsUl x (x + 10 / 13 * (a2 - 1))) hx hx2 (by linarith) h2
    (hb1.trans hb12) hU20
  generalize hU1 : hsUl x (x + 10 / 13 * (a1 - 1)) = U1 at *
  generalize hU2 : hsUl x (x + 10 / 13 * (a2 - 1)) = U2 at *
  have hK : 0 ≤ (U1 - U2) ^ 2 * (1 + x) ^ 2 * hh1oK a2 ^ 2 / (576 * a2 ^ 4) := by positivity
  have hstep : hh1oF0 x a2 (x + 10 / 13 * (a2 - 1)) U1 - hh1oF0 x a2 (x + 10 / 13 * (a2 - 1)) U2 ≤
      (U1 - U2) * (1 / 4) := by
    have := mul_le_mul_of_nonneg_left hle (by linarith : (0 : ℝ) ≤ U1 - U2)
    linarith
  have hr : (a2 - a1) * (25 / 36) ≤ 1 / a1 - 1 / a2 := by
    have h36 : a1 * a2 ≤ 36 / 25 := by nlinarith
    rw [div_sub_div _ _ (by linarith) (by linarith), le_div_iff₀ (by nlinarith)]
    nlinarith [mul_le_mul_of_nonneg_left h36 (sub_nonneg.2 h12)]
  have hmv' : U1 - U2 ≤ 15 / 1992 * (10 / 13 * (a2 - a1)) := by
    have : x + 10 / 13 * (a2 - 1) - (x + 10 / 13 * (a1 - 1)) = 10 / 13 * (a2 - a1) := by ring
    rw [← this]; exact hmv
  have hfin : (U1 - U2) * (1 / 4) ≤ 1 / 400 * (1 / a1 - 1 / a2) := by
    have : 15 / 1992 * (10 / 13 * (a2 - a1)) * (1 / 4) ≤ 1 / 400 * ((a2 - a1) * (25 / 36)) := by
      nlinarith
    nlinarith
  linarith

/-! ### Assembly -/

/-- **Branch B, `F₀ > 0`** (`SHORT_OUTER_LOW_SHAPE_TERMINAL` (1)). -/
theorem hl1o_B_F0 {x a b u : ℝ} (hx : 3 / 2 ≤ x) (hx2 : x ≤ 2) (ha1 : 1 ≤ a) (ha2 : a ≤ 6 / 5)
    (hcap : x * (x + 2) ≤ 6 * a ^ 2) (hxb : x ≤ b) (hb : b ≤ x + 10 / 13 * (a - 1))
    (hu : hsUf x ≤ u) (hul : u ≤ hsUl x b) : 0 < hh1oF0 x a b u := by
  have hx0 : 0 < x := by linarith
  have hx1 : 1 < x := by linarith
  have ha0 : 0 < a := by linarith
  have hA : 0 ≤ a - 1 := by linarith
  set bS := x + 10 / 13 * (a - 1) with hbS
  have hbS1 : bS ≤ a * x := by simp only [hbS]; nlinarith
  have hUf0 : 3 / 4 ≤ hsUf x := by
    unfold hsUf
    have : 0 ≤ (x - 1) ^ 2 / (28 * (x + 1) ^ 2) := by positivity
    linarith
  -- the lower shape, below the cap
  obtain ⟨aS, haS1, haS, hT⟩ : ∃ aS, 1 ≤ aS ∧ aS ≤ a ∧
      0 < hh1oF0 x aS (x + 10 / 13 * (aS - 1)) (hsUf x) ∧
      0 < hh1oF0 x aS (x + 10 / 13 * (aS - 1)) (hsUl x (x + 10 / 13 * (aS - 1))) := by
    rcases le_total x (5 / 3) with h53 | h53
    · refine ⟨1, le_rfl, ha1, ?_, ?_⟩
      · rw [show x + 10 / 13 * (1 - 1) = x by ring]; exact hl1o_B_U1f hx h53
      · rw [show x + 10 / 13 * (1 - 1) = x by ring]; exact hl1o_B_U1l hx h53
    · refine ⟨(45 * x + 22) / 97, by linarith, ?_, hl1o_B_U97f h53 hx2, hl1o_B_U97l h53 hx2⟩
      have h1 : ((45 * x + 22) / 97) ^ 2 ≤ a ^ 2 := by
        nlinarith [mul_nonneg (sub_nonneg.2 h53) (sub_nonneg.2 hx2)]
      nlinarith [sq_nonneg (a - (45 * x + 22) / 97)]
  have hm := hl1o_F0_umin (x := x) (a := a) (b := b) hu hul ha0.ne'
  refine lt_of_lt_of_le (lt_min ?_ ?_) hm
  · -- the floor norm: beta, then shape, at the fixed norm `u_f(x)`
    have h1 := hl1o_F0_bmono (u := hsUf x) hx hx2 ha1 ha2 hxb hb hbS1 hUf0
    have h2 := hl1o_B_amono hx hx2 haS1 haS ha2 hUf0
    have h3 : 0 ≤ 1 / 400 * (1 / aS - 1 / a) := by
      have : 1 / a ≤ 1 / aS := one_div_le_one_div_of_le (by linarith) haS
      linarith
    have h4 : 0 ≤ 7 / 5120 * (bS - b) := by linarith
    linarith [hT.1]
  · -- the ceiling: beta, then shape, along `u_ℓ`
    have h1 := hl1o_F0_bmono_ul hx hx2 ha1 ha2 hcap hxb hb hbS1
    have h2 := hl1o_B_amono_ul hx hx2 haS1 haS ha2
    linarith [hT.2]

end SmoothedOctagon
