module

public import SmoothedOctagon.Exclusion.Mixed.ShortHand.Heavy.S1OSteps
public import SmoothedOctagon.Exclusion.Mixed.ShortHand.Heavy.S1OConc
public import SmoothedOctagon.Exclusion.Mixed.ShortHand.Heavy.S1OCurv0
public import SmoothedOctagon.Exclusion.Mixed.ShortHand.Heavy.S1OCurv1
public import SmoothedOctagon.Exclusion.Mixed.ShortHand.Heavy.S1OCurv2
public import SmoothedOctagon.Exclusion.Mixed.ShortHand.Heavy.S1OCurv3
public import SmoothedOctagon.Exclusion.Mixed.ShortHand.Heavy.S1OUni
public import SmoothedOctagon.Exclusion.Mixed.ShortHand.Heavy.S1OClaimW1
public import SmoothedOctagon.Exclusion.Mixed.ShortHand.Heavy.S1OClaimW2

/-!
# Gate S1: the outer low-ratio face

`hs1_outer_face_proof` proves the heavy leaf `hs1_outer_face`
(`LOW_RATIO_OUTER_HAND_SIGN` §6; inventory HS-S01 D-R20–D-R22): on the outer face `q = 1/7`
(`6α² ≥ x(x + 2)`) the corrected envelope exceeds `9193/50000` for every duration `τ ∈ [2, T]`.

Proof. The duration reduction `hh1o_face_red` leaves the two tests `F₀`, `F₁`. Write
`β = x + C(α - 1)` with `C₋(x) ≤ C ≤ C₊(x)`.

* `F₁` (`hh1o_F1_pos`): concave in `u`, so `u ∈ {u_f(x), V̄(x)}`. For `x ≤ 6/5`, `F₁` increases
  in `β` (`hh1o_stepDS`) down to the chord slope `L(x) = 8/17 + 32(x - 1)/221 ≤ C₋(x)`, and the
  two-variable signs `S2` conclude. For `x ≥ 6/5`, `F₁(x, 1/r, ·)` is concave in the reciprocal
  shape `r` (`hh1og_min` with the curvature signs `S1OCurv*`), so `α` is an endpoint: the diagonal
  `α = x`, or `α = 1` (`x ≤ 5/3`), `α = (6x + 3)/13` (`x ≥ 5/3`), or the shared face `α = 6/5`
  (when `x ≥ 3/2`, `α ≥ 6/5`). On the diagonal `F₁` increases in `β`, down to `L(x)`; on
  `α = (6x + 3)/13` it decreases in `β`, up to `10/13`. The one-variable terminal signs `S1OUni`
  and the two-variable face signs `A65` conclude, with `F₁ ≥ 1/2500` when `x ≥ 3/2`, `α ≥ 6/5`.
* `F₀` on the `B` corner `x ≥ 3/2`, `α ≤ 6/5` (`hh1o_F0_B`): concave in `u` on `[u_f, u_ℓ]`; at
  `u = u_f` and along the ceiling `u = u_ℓ(x, β)`, `F₀` decreases in `β` up to `x + (10/13)(α - 1)`
  and increases in `α` down to `α = 1` or the chord `a_L(x) = (4375x + 2797)/10000` of
  `√(x(x + 2)/6)`; the terminal signs `T4`, `T5` conclude.
* `F₀` elsewhere: `F₀ = F₁ + c(T - 2)(w - 3/4)` with `0 ≤ T - 2 ≤ 3/2`, `w ≥ 3/4` for `x ≤ 3/2`
  and `w ≥ 3/4 - 1/300` for `x ≥ 3/2`, `α ≥ 6/5` (`S1OClaimW*`), where `F₁ ≥ 1/2500`.

Route: the notes reduce `F₁` by the three branches S/A/B with large coefficient tables; here the
reduction is by norm concavity, reciprocal-shape concavity and one-variable terminal signs, with
all signs generated termwise/Bernstein certificates.
-/

@[expose] public section

namespace SmoothedOctagon

theorem hh1o_piece {x x0 x1 C u : ℝ} (h0 : 1 < x0) (hx0 : x0 ≤ x) (hx1 : x ≤ x1) (hx2 : x1 ≤ 2)
    (hC0 : 8 * x / (9 * x + 8) ≤ C) (hC1 : C ≤ x * (7 * x + 1) / (4 * x ^ 2 + 11 * x + 1))
    (hu1 : u ≤ hsVbar x) :
    8 * x0 / (9 * x0 + 8) ≤ C ∧ C ≤ x1 * (7 * x1 + 1) / (4 * x1 ^ 2 + 11 * x1 + 1) ∧
      u ≤ hsVbar x1 :=
  ⟨(hh1o_Cm_mono (by linarith) hx0).trans hC0, hC1.trans (hh1o_Cp_mono (by linarith) hx1),
    hu1.trans (hh1o_Vbar_mono (by linarith) hx1 hx2)⟩

theorem hh1o_curv {x C u : ℝ} (hx0 : 6 / 5 ≤ x) (hx1 : x ≤ 2) (hC0 : 8 * x / (9 * x + 8) ≤ C)
    (hC1 : C ≤ x * (7 * x + 1) / (4 * x ^ 2 + 11 * x + 1)) (hu0 : 3 / 4 ≤ u) (hu1 : u ≤ hsVbar x) :
    0 ≤ -(4 * hh1oP4 x C u / x + hh1oP3 x C u) ∧ 0 ≤ -hh1oQ x C u ∧
      0 ≤ -(12 * hh1oP4 x C u / x ^ 2 + 6 * hh1oP3 x C u / x + 2 * hh1oP2 x C u +
        7 / 96 * ((x - C) * x / ((1 + C) * x + (x - C))) ^ 2) := by
  rcases le_total x (13 / 10) with h1 | h1
  · obtain ⟨p1, p2, p3⟩ := hh1o_piece (x0 := 6 / 5) (x1 := 13 / 10) (by norm_num) hx0 h1
      (by norm_num) hC0 hC1 hu1
    norm_num [hsVbar] at p1 p2 p3
    exact ⟨hh1o_claim_cc2_0 hx0 h1 (by linarith) (by linarith) hu0 (by linarith),
      hh1o_claim_cc3_0 hx0 h1 (by linarith) (by linarith) hu0 (by linarith),
      hh1o_claim_cc4_0 hx0 h1 (by linarith) (by linarith) hu0 (by linarith)⟩
  rcases le_total x (3 / 2) with h2 | h2
  · obtain ⟨p1, p2, p3⟩ := hh1o_piece (x0 := 13 / 10) (x1 := 3 / 2) (by norm_num) h1 h2
      (by norm_num) hC0 hC1 hu1
    norm_num [hsVbar] at p1 p2 p3
    exact ⟨hh1o_claim_cc2_1 h1 h2 (by linarith) (by linarith) hu0 (by linarith),
      hh1o_claim_cc3_1 h1 h2 (by linarith) (by linarith) hu0 (by linarith),
      hh1o_claim_cc4_1 h1 h2 (by linarith) (by linarith) hu0 (by linarith)⟩
  rcases le_total x (7 / 4) with h3 | h3
  · obtain ⟨p1, p2, p3⟩ := hh1o_piece (x0 := 3 / 2) (x1 := 7 / 4) (by norm_num) h2 h3
      (by norm_num) hC0 hC1 hu1
    norm_num [hsVbar] at p1 p2 p3
    exact ⟨hh1o_claim_cc2_2 h2 h3 (by linarith) (by linarith) hu0 (by linarith),
      hh1o_claim_cc3_2 h2 h3 (by linarith) (by linarith) hu0 (by linarith),
      hh1o_claim_cc4_2 h2 h3 (by linarith) (by linarith) hu0 (by linarith)⟩
  · obtain ⟨p1, p2, p3⟩ := hh1o_piece (x0 := 7 / 4) (x1 := 2) (by norm_num) h3 hx1
      le_rfl hC0 hC1 hu1
    norm_num [hsVbar] at p1 p2 p3
    exact ⟨hh1o_claim_cc2_3 h3 hx1 (by linarith) (by linarith) hu0 (by linarith),
      hh1o_claim_cc3_3 h3 hx1 (by linarith) (by linarith) hu0 (by linarith),
      hh1o_claim_cc4_3 h3 hx1 (by linarith) (by linarith) hu0 (by linarith)⟩

theorem hh1o_Uf_le_Vbar {x : ℝ} (hx : 1 < x) : hsUf x ≤ hsVbar x := by
  unfold hsUf hsVbar
  have h : (x - 1) ^ 2 / (28 * (x + 1) ^ 2) ≤ 2 * (x - 1) ^ 2 / ((x + 1) * (35 * x + 13)) := by
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith [mul_nonneg (mul_nonneg (sq_nonneg (x - 1)) (by linarith : (0 : ℝ) ≤ x + 1))
      (by linarith : (0 : ℝ) ≤ 21 * x + 43)]
  linarith

theorem hh1o_Uf_ge (x : ℝ) : 3 / 4 ≤ hsUf x := by
  unfold hsUf
  have : 0 ≤ (x - 1) ^ 2 / (28 * (x + 1) ^ 2) := by positivity
  linarith

/-- **`F₁` at a terminal norm** `u ∈ {u_f(x), V̄(x)}`, slope `C` fixed. -/
theorem hh1o_F1_core {x a C u : ℝ} (hx : 1 < x) (hx2 : x ≤ 2) (hal : 1 ≤ a) (hax : a ≤ x)
    (hqc : x * (x + 2) ≤ 6 * a ^ 2) (hC0 : 8 * x / (9 * x + 8) ≤ C)
    (hC1 : C ≤ x * (7 * x + 1) / (4 * x ^ 2 + 11 * x + 1)) (hu : u = hsUf x ∨ u = hsVbar x) :
    0 < hh1oF1 x a (x + C * (a - 1)) u ∧
      (3 / 2 ≤ x → 6 / 5 ≤ a → 1 / 2500 ≤ hh1oF1 x a (x + C * (a - 1)) u) := by
  have hV := hh1_Vbar_bounds hx hx2
  have hu0 : 3 / 4 ≤ u := by
    rcases hu with h | h <;> rw [h]
    · exact hh1o_Uf_ge x
    · exact hV.1
  have hu1 : u ≤ hsVbar x := by
    rcases hu with h | h <;> rw [h]
    · exact hh1o_Uf_le_Vbar hx
  have hu2 : u ≤ 755 / 996 := by linarith [hV.2]
  have hCp2 : C ≤ 10 / 13 := by
    have := hh1o_Cp_mono (x1 := 2) (by linarith) hx2
    norm_num at this
    linarith
  have hCm1 : 8 / 17 ≤ C := by
    have := hh1o_Cm_mono (x0 := 1) one_pos hx.le
    norm_num at this
    linarith
  have hC0' : 0 ≤ C := by linarith
  have hCx : C < x := by linarith
  have hx1 : 0 ≤ x - 1 := by linarith
  -- the diagonal `α = x`
  have hdiag : 1 / 2500 < hh1oF1 x x (x + C * (x - 1)) u := by
    have hL := hh1o_chord hx.le hx2
    have m1 := mul_le_mul_of_nonneg_right (hL.trans hC0) hx1
    have m2 := mul_le_mul_of_nonneg_right hCp2 hx1
    have m0 : 0 ≤ (8 / 17 + 32 / 221 * (x - 1)) * (x - 1) := mul_nonneg (by linarith) hx1
    have h1 := hh1o_stepDg (b := x + (8 / 17 + 32 / 221 * (x - 1)) * (x - 1))
      (b' := x + C * (x - 1)) (u := u) hx hx2 (by linarith) (by linarith) (by linarith) hu0 hu2
    have h2 : 0 < hh1oF1 x x (x + (8 / 17 + 32 / 221 * (x - 1)) * (x - 1)) u - 1 / 2500 := by
      rcases hu with h | h
      · exact hh1o_uni_T1uf (by linarith) (by linarith) rfl rfl h
      · exact hh1o_uni_T1vb (by linarith) (by linarith) rfl rfl h
    linarith
  rcases le_total x (6 / 5) with hx65 | hx65
  · -- region S: `F₁` increases in `β`, down to the chord slope; the two-variable sign `S2`
    have hus : u ≤ 9083 / 12100 := by
      have := hu1.trans (hh1o_Vbar_mono hx hx65 (by norm_num))
      norm_num [hsVbar] at this
      linarith
    have hA1 : 0 ≤ a - 1 := by linarith
    have hL := hh1o_chord hx.le hx2
    have m1 := mul_le_mul_of_nonneg_right (hL.trans hC0) hA1
    have m2 := mul_le_mul_of_nonneg_right hCp2 hA1
    have m0 : 0 ≤ (8 / 17 + 32 / 221 * (x - 1)) * (a - 1) := mul_nonneg (by linarith) hA1
    have hs := hh1o_stepDS (b := x + (8 / 17 + 32 / 221 * (x - 1)) * (a - 1))
      (b' := x + C * (a - 1)) (u := u) hx hx65 hal hax (by linarith) (by linarith) (by linarith)
      hu0 hus
    have hT : 0 ≤ hh1oF1 x a (x + (8 / 17 + 32 / 221 * (x - 1)) * (a - 1)) u - 1 / 8000 := by
      rcases hu with h | h
      · exact hh1o_claim_S2uf hx.le hx65 hal (by linarith) rfl h
      · exact hh1o_claim_S2vb hx.le hx65 hal (by linarith) rfl h
    exact ⟨by linarith, fun h _ => absurd h (by linarith)⟩
  -- reciprocal-shape concavity
  obtain ⟨c2, c3, c4⟩ := hh1o_curv hx65 hx2 hC0 hC1 hu0 hu1
  have hEq : ∀ a', 0 < a' → hh1oF1 x a' (x + C * (a' - 1)) u = hh1og x C u (1 / a') :=
    fun a' ha' => hh1o_F1_eq_g hx ha' hC0' hCx rfl
  have hEx := hEq x (by linarith)
  have hEa := hEq a (by linarith)
  have hxa : 1 / x ≤ 1 / a := one_div_le_one_div_of_le (by linarith) hax
  by_cases hA : 3 / 2 ≤ x ∧ 6 / 5 ≤ a
  · -- the shared face `α = 6/5`
    have hE6 := hEq (6 / 5) (by norm_num)
    have hmin := hh1og_min (u := u) (r0 := 1 / x) (r := 1 / a) (r1 := 1 / (6 / 5)) hx hx2 hC0' hCx
      le_rfl hxa (one_div_le_one_div_of_le (by norm_num) hA.2) (by norm_num) c2 c3 c4
    have h65 : 1 / 2500 ≤ hh1oF1 x (6 / 5) (x + C * (6 / 5 - 1)) u := by
      have hb : x + C * (6 / 5 - 1) = x + C / 5 := by ring
      rw [hb]
      have hCl : 24 / 43 ≤ C := by
        have := hh1o_Cm_mono (x0 := 3 / 2) (by norm_num) hA.1
        norm_num at this
        linarith
      rcases hu with h | h
      · have := hh1o_claim_A65uf (a := 6 / 5) (b := x + C / 5) (u := u) hA.1 hx2 hCl hCp2 rfl rfl h
        linarith
      · have := hh1o_claim_A65vb (a := 6 / 5) (b := x + C / 5) (u := u) hA.1 hx2 hCl hCp2 rfl rfl h
        linarith
    rw [← hEx, ← hEa, ← hE6] at hmin
    have := le_min hdiag.le h65
    exact ⟨by linarith, fun _ _ => by linarith⟩
  rcases le_total x (5 / 3) with h53 | h53
  · -- the lower shape `α = 1`
    have hE1 := hEq 1 one_pos
    have hmin := hh1og_min (u := u) (r0 := 1 / x) (r := 1 / a) (r1 := 1 / 1) hx hx2 hC0' hCx
      le_rfl hxa (one_div_le_one_div_of_le one_pos hal) (by norm_num) c2 c3 c4
    have hT2 : 0 < hh1oF1 x 1 (x + C * (1 - 1)) u := by
      have hb : x + C * (1 - 1) = x := by ring
      rw [hb]
      rcases hu with h | h
      · have := hh1o_uni_T2uf (a := 1) (b := x) hx65 h53 rfl rfl h
        linarith
      · have := hh1o_uni_T2vb (a := 1) (b := x) hx65 h53 rfl rfl h
        linarith
    rw [← hEx, ← hEa, ← hE1] at hmin
    exact ⟨lt_of_lt_of_le (lt_min (by linarith) hT2) hmin, fun h1 h2 => absurd ⟨h1, h2⟩ hA⟩
  · -- the lower shape `α = (6x + 3)/13`
    have hlo : (6 * x + 3) / 13 ≤ a := by
      have h1 : ((6 * x + 3) / 13) ^ 2 ≤ a ^ 2 := by
        nlinarith [mul_nonneg (sub_nonneg.2 h53) (sub_nonneg.2 hx2)]
      nlinarith [sq_nonneg (a - (6 * x + 3) / 13)]
    have hlo1 : 1 ≤ (6 * x + 3) / 13 := by linarith
    have hE3 := hEq ((6 * x + 3) / 13) (by linarith)
    have hmin := hh1og_min (u := u) (r0 := 1 / x) (r := 1 / a) (r1 := 1 / ((6 * x + 3) / 13)) hx
      hx2 hC0' hCx le_rfl hxa (one_div_le_one_div_of_le (by linarith) hlo)
      (by rw [div_le_one (by linarith)]; exact hlo1) c2 c3 c4
    have hT3 : 0 < hh1oF1 x ((6 * x + 3) / 13) (x + C * ((6 * x + 3) / 13 - 1)) u := by
      have hk : 0 ≤ (6 * x + 3) / 13 - 1 := by linarith
      have m1 := mul_le_mul_of_nonneg_right hCp2 hk
      have m0 := mul_nonneg hC0' hk
      have hs := hh1o_stepLo (b := x + C * ((6 * x + 3) / 13 - 1))
        (b' := x + 10 / 13 * ((6 * x + 3) / 13 - 1)) (u := u) h53 hx2 (by linarith) (by linarith)
        le_rfl hu0 hu2
      rcases hu with h | h
      · have := hh1o_uni_T3uf (a := (6 * x + 3) / 13) (b := x + 10 / 13 * ((6 * x + 3) / 13 - 1))
          h53 (by linarith) rfl rfl h
        linarith
      · have := hh1o_uni_T3vb (a := (6 * x + 3) / 13) (b := x + 10 / 13 * ((6 * x + 3) / 13 - 1))
          h53 (by linarith) rfl rfl h
        linarith
    rw [← hEx, ← hEa, ← hE3] at hmin
    exact ⟨lt_of_lt_of_le (lt_min (by linarith) hT3) hmin, fun h1 h2 => absurd ⟨h1, h2⟩ hA⟩

/-- **The outer `F₁`**: positive on the whole outer face, and at least `1/2500` when `x ≥ 3/2`,
`α ≥ 6/5`. -/
theorem hh1o_F1_pos {x a b u C : ℝ} (hx : 1 < x) (hx2 : x ≤ 2) (hal : 1 ≤ a) (hax : a ≤ x)
    (hqc : x * (x + 2) ≤ 6 * a ^ 2) (hC0 : 8 * x / (9 * x + 8) ≤ C)
    (hC1 : C ≤ x * (7 * x + 1) / (4 * x ^ 2 + 11 * x + 1)) (hb : b = x + C * (a - 1))
    (hu : hsUf x ≤ u) (huv : u ≤ hsVbar x) :
    0 < hh1oF1 x a b u ∧ (3 / 2 ≤ x → 6 / 5 ≤ a → 1 / 2500 ≤ hh1oF1 x a b u) := by
  subst hb
  have ha0 : 0 < a := by linarith
  have hm := hh1_conc3 (f := fun s => hh1oF1 x a (x + C * (a - 1)) s) hu huv (by positivity)
    (hh1o_F1_u3 x a _ _ _)
  obtain ⟨p1, q1⟩ := hh1o_F1_core hx hx2 hal hax hqc hC0 hC1 (Or.inl rfl)
  obtain ⟨p2, q2⟩ := hh1o_F1_core hx hx2 hal hax hqc hC0 hC1 (Or.inr rfl)
  exact ⟨lt_of_lt_of_le (lt_min p1 p2) hm, fun h1 h2 => le_trans (le_min (q1 h1 h2) (q2 h1 h2)) hm⟩

/-- **The outer `F₀` on the `B` corner** `x ≥ 3/2`, `α ≤ 6/5`, `u ≤ u_ℓ(x, β)`. -/
theorem hh1o_F0_B {x a b u : ℝ} (hx0 : 3 / 2 ≤ x) (hx1 : x ≤ 2) (ha0 : 1 ≤ a) (ha1 : a ≤ 6 / 5)
    (hqc : x * (x + 2) ≤ 6 * a ^ 2) (hb0 : x + 5 / 9 * (a - 1) ≤ b)
    (hb1 : b ≤ x + 10 / 13 * (a - 1)) (hu : hsUf x ≤ u) (hul : u ≤ hsUl x b) :
    0 < hh1oF0 x a b u := by
  have hap : 0 < a := by linarith
  have hm := hh1_conc3 (f := fun s => hh1oF0 x a b s) hu hul (by positivity) (hh1o_F0_u3 x a b _ _)
  have hV := hh1_Vbar_bounds (by linarith) hx1
  have hUf0 := hh1o_Uf_ge x
  have hUf1 : hsUf x ≤ 3 / 4 + 2 / 249 := (hh1o_Uf_le_Vbar (by linarith)).trans hV.2
  have haL : 1029 / 625 ≤ x → (4375 * x + 2797) / 10000 ≤ a := fun hxl => by
    have h1 : ((4375 * x + 2797) / 10000) ^ 2 ≤ a ^ 2 := by
      nlinarith [mul_nonneg (sub_nonneg.2 hxl) (sub_nonneg.2 hx1)]
    nlinarith [sq_nonneg (a - (4375 * x + 2797) / 10000)]
  refine lt_of_lt_of_le (lt_min ?_ ?_) hm
  · -- the norm `u_f(x)`
    have h1 := hh1o_stepB0 (b' := x + 10 / 13 * (a - 1)) hx0 hx1 ha0 ha1 hb0 hb1 le_rfl hUf0 hUf1
    rcases le_total x (1029 / 625) with hxl | hxl
    · have h2 := hh1o_stepA0 (a := 1) (a' := a) (u := hsUf x) hx0 hx1 le_rfl ha0 ha1 hUf0 hUf1
      have h3 := hh1o_uni_T4uf (a := 1) (b := x + 10 / 13 * (1 - 1)) (u := hsUf x) hx0 hxl rfl
        (by ring) rfl
      linarith
    · have hl := haL hxl
      have h2 := hh1o_stepA0 (a := (4375 * x + 2797) / 10000) (a' := a) (u := hsUf x) hx0 hx1
        (by linarith) hl ha1 hUf0 hUf1
      have h3 := hh1o_uni_T5uf (a := (4375 * x + 2797) / 10000)
        (b := x + 10 / 13 * ((4375 * x + 2797) / 10000 - 1)) (u := hsUf x) hxl
            (by linarith) rfl rfl rfl
      linarith
  · -- along the ceiling `u_ℓ(x, β)`
    have h1 := hh1o_stepBU (b' := x + 10 / 13 * (a - 1)) hx0 hx1 ha0 ha1 hb0 hb1 le_rfl
    rcases le_total x (1029 / 625) with hxl | hxl
    · have h2 := hh1o_stepAU (a := 1) (a' := a) hx0 hx1 le_rfl ha0 ha1
      have h3 := hh1o_uni_T4ul (a := 1) (b := x + 10 / 13 * (1 - 1))
        (u := hsUl x (x + 10 / 13 * (1 - 1))) hx0 hxl rfl (by ring) rfl
      linarith
    · have hl := haL hxl
      have h2 := hh1o_stepAU (a := (4375 * x + 2797) / 10000) (a' := a) hx0 hx1 (by linarith) hl
        ha1
      have h3 := hh1o_uni_T5ul (a := (4375 * x + 2797) / 10000)
        (b := x + 10 / 13 * ((4375 * x + 2797) / 10000 - 1))
        (u := hsUl x (x + 10 / 13 * ((4375 * x + 2797) / 10000 - 1))) hxl (by linarith) rfl rfl
        rfl
      linarith

/-- **The outer low-ratio face** (`LOW_RATIO_OUTER_HAND_SIGN` §6; inventory HS-S01 D-R20–D-R22):
for `1 < x ≤ 2`, `1 ≤ α ≤ x`, `6α² ≥ x(x + 2)` (`q = 1/7 ≤ q_c`), the strip
`x + 8x(α - 1)/(9x + 8) ≤ β ≤ x + x(7x + 1)(α - 1)/(4x² + 11x + 1)`, `u_f(x) ≤ u ≤ V̄(x)` (and
`u ≤ u_ℓ(x, β)` when `x ≥ 3/2`, `α ≤ 6/5`) and every `τ ∈ [2, 7r_A]`:
`Γ_*(1/7) - (7/96)R*_τ(1/7) > 9193/50000`. -/
theorem hs1_outer_face_proof {x al be u τ : ℝ} (hx : 1 < x) (hx2 : x ≤ 2) (hal : 1 ≤ al)
    (hax : al ≤ x) (hxb : x ≤ be) (hbx : be ≤ al * x) (hqc : x * (x + 2) ≤ 6 * al ^ 2)
    (hb : x + 8 * x * (al - 1) / (9 * x + 8) ≤ be)
    (hb' : be ≤ x + x * (7 * x + 1) * (al - 1) / (4 * x ^ 2 + 11 * x + 1)) (hu : hsUf x ≤ u)
    (huv : u ≤ hsVbar x) (hul : 3 / 2 ≤ x → al ≤ 6 / 5 → u ≤ hsUl x be) (hτ : 2 ≤ τ)
    (hτT : τ ≤ 7 * hsRA al be) :
    9193 / 50000 < hsGs x al u (1 / 7) - 7 / 96 * hsRs x be al u (1 / 7) τ := by
  have hred := hh1o_face_red (x := x) (u := u) (by linarith) hal (by linarith) hτ hτT
  have hd0 : 0 < 9 * x + 8 := by linarith
  have hd1 : 0 < 4 * x ^ 2 + 11 * x + 1 := by positivity
  obtain ⟨C, hC0, hC1, hbC⟩ : ∃ C, 8 * x / (9 * x + 8) ≤ C ∧
      C ≤ x * (7 * x + 1) / (4 * x ^ 2 + 11 * x + 1) ∧ be = x + C * (al - 1) := by
    rcases eq_or_lt_of_le hal with h | h
    · refine ⟨8 * x / (9 * x + 8), le_rfl, ?_, ?_⟩
      · rw [div_le_div_iff₀ hd0 hd1]; nlinarith
      · rw [← h] at hb' ⊢
        have : be ≤ x := by simpa using hb'
        have : be = x := le_antisymm this hxb
        rw [this]; ring
    · have hA : 0 < al - 1 := by linarith
      refine ⟨(be - x) / (al - 1), ?_, ?_, ?_⟩
      · rw [le_div_iff₀ hA]
        have : 8 * x / (9 * x + 8) * (al - 1) = 8 * x * (al - 1) / (9 * x + 8) := by ring
        linarith
      · rw [div_le_iff₀ hA]
        have : x * (7 * x + 1) / (4 * x ^ 2 + 11 * x + 1) * (al - 1) =
            x * (7 * x + 1) * (al - 1) / (4 * x ^ 2 + 11 * x + 1) := by ring
        linarith
      · field_simp
        ring
  obtain ⟨hF1, hF1A⟩ := hh1o_F1_pos hx hx2 hal hax hqc hC0 hC1 hbC hu huv
  suffices h0 : 0 < hh1oF0 x al be u by
    have := lt_min h0 hF1
    linarith
  have hCp2 : C ≤ 10 / 13 := by
    have := hh1o_Cp_mono (x1 := 2) (by linarith) hx2
    norm_num at this
    linarith
  have hA1 : 0 ≤ al - 1 := by linarith
  have hu0 : 3 / 4 ≤ u := (hh1o_Uf_ge x).trans hu
  by_cases hB : 3 / 2 ≤ x ∧ al ≤ 6 / 5
  · have hCm : 5 / 9 ≤ C := by
      have := hh1o_Cm_mono (x0 := 3 / 2) (by norm_num) hB.1
      norm_num at this
      linarith
    have m0 := mul_le_mul_of_nonneg_right hCm hA1
    have m1 := mul_le_mul_of_nonneg_right hCp2 hA1
    exact hh1o_F0_B hB.1 hx2 hal hB.2 hqc (by linarith) (by linarith) hu (hul hB.1 hB.2)
  -- `F₀ = F₁ + c(T - 2)(w - 3/4)` with `0 ≤ T - 2 ≤ 3/2`
  have hT : hh1oF0 x al be u =
      hh1oF1 x al be u + 7 / 96 * (hh1oT al be - 2) * (hh1ow x al be u - 3 / 4) := by
    unfold hh1oF1; ring
  have hab : 0 < al + be := by linarith
  have hT0 : 0 ≤ hh1oT al be - 2 := by
    unfold hh1oT
    rw [sub_nonneg, le_div_iff₀ hab]
    nlinarith
  have hT1 : hh1oT al be - 2 ≤ 3 / 2 := by
    unfold hh1oT
    rw [sub_le_iff_le_add, div_le_iff₀ hab]
    linarith
  rcases lt_or_ge x (3 / 2) with hS | hS
  · -- `x ≤ 3/2`: `w ≥ 3/4`
    have hw : 0 ≤ hh1ow x al be u - 3 / 4 := by
      rcases le_total x (5 / 4) with h | h
      · have hCl : 8 / 17 ≤ C := by
          have := hh1o_Cm_mono (x0 := 1) one_pos hx.le
          norm_num at this
          linarith
        have hCu : C ≤ 65 / 112 := by
          have := hh1o_Cp_mono (x1 := 5 / 4) (by linarith) h
          norm_num at this
          linarith
        have hU : u ≤ 3 / 4 + 2 / 2043 := by
          have := huv.trans (hh1o_Vbar_mono hx h (by norm_num))
          norm_num [hsVbar] at this
          linarith
        have m0 := mul_le_mul_of_nonneg_right hCl hA1
        have m1 := mul_le_mul_of_nonneg_right hCu hA1
        exact hh1o_claim_wS1 hx.le h hal (by linarith) (by linarith) (by linarith) hu0 hU
      · have hCl : 40 / 77 ≤ C := by
          have := hh1o_Cm_mono (x0 := 5 / 4) (by norm_num) h
          norm_num at this
          linarith
        have hCu : C ≤ 69 / 106 := by
          have := hh1o_Cp_mono (x1 := 3 / 2) (by linarith) hS.le
          norm_num at this
          linarith
        have hU : u ≤ 3 / 4 + 2 / 655 := by
          have := huv.trans (hh1o_Vbar_mono hx hS.le (by norm_num))
          norm_num [hsVbar] at this
          linarith
        have m0 := mul_le_mul_of_nonneg_right hCl hA1
        have m1 := mul_le_mul_of_nonneg_right hCu hA1
        exact hh1o_claim_wS2 h hS.le hal (by linarith) (by linarith) (by linarith) hu0 hU
    have := mul_nonneg hT0 hw
    rw [hT]
    linarith
  · -- `x ≥ 3/2`, `α ≥ 6/5`: `w ≥ 3/4 - 1/300`, `F₁ ≥ 1/2500`
    have ha65 : 6 / 5 ≤ al := by
      by_contra h
      exact hB ⟨hS, (not_le.mp h).le⟩
    have hF := hF1A hS ha65
    have hw : -(1 / 300) ≤ hh1ow x al be u - 3 / 4 := by
      rw [hbC]
      rcases le_total x (7 / 4) with h1 | h1
      · obtain ⟨p1, p2, p3⟩ := hh1o_piece (x0 := 3 / 2) (x1 := 7 / 4) (by norm_num) hS h1
          (by norm_num) hC0 hC1 huv
        norm_num [hsVbar] at p1 p2 p3
        have := hh1o_claim_wA1 (C := C) (u := u) hS h1 ha65 (by linarith) (by linarith)
            (by linarith) hu0
          (by linarith)
        linarith
      rcases le_total x (15 / 8) with h2 | h2
      · obtain ⟨p1, p2, p3⟩ := hh1o_piece (x0 := 7 / 4) (x1 := 15 / 8) (by norm_num) h1 h2
          (by norm_num) hC0 hC1 huv
        norm_num [hsVbar] at p1 p2 p3
        rcases le_total al (13 / 10) with h3 | h3
        · have := hh1o_claim_wA2 (C := C) (u := u) h1 h2 ha65 h3 (by linarith) (by linarith) hu0
              (by linarith)
          linarith
        · have := hh1o_claim_wA3 (C := C) (u := u) h1 h2 h3 (by linarith) (by linarith)
              (by linarith) hu0
            (by linarith)
          linarith
      · obtain ⟨p1, p2, p3⟩ := hh1o_piece (x0 := 15 / 8) (x1 := 2) (by norm_num) h2 hx2
          le_rfl hC0 hC1 huv
        norm_num [hsVbar] at p1 p2 p3
        rcases le_total al (5 / 4) with h3 | h3
        · have := hh1o_claim_wA4 (C := C) (u := u) h2 hx2 ha65 h3 (by linarith) (by linarith) hu0
              (by linarith)
          linarith
        rcases le_total al (13 / 10) with h4 | h4
        · have := hh1o_claim_wA5 (C := C) (u := u) h2 hx2 h3 h4 (by linarith) (by linarith) hu0
              (by linarith)
          linarith
        · have := hh1o_claim_wA6 (C := C) (u := u) h2 hx2 h4 (by linarith) (by linarith)
              (by linarith) hu0
            (by linarith)
          linarith
    have h1 := mul_le_mul_of_nonneg_left hw hT0
    have h2 : (hh1oT al be - 2) * -(1 / 300) ≥ 3 / 2 * -(1 / 300) := by nlinarith
    rw [hT]
    linarith

end SmoothedOctagon
