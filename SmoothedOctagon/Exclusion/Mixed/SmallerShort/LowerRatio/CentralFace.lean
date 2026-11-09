module

public import SmoothedOctagon.Exclusion.Mixed.ShortHand.Heavy.S1HandC5

/-!
# Gate S1 by hand: the central face, assembly

At the cap `x(x + 2) = 6α²` the central transport (`K = 7α²`) and
the outer transport (`K = 6α² + 1 = S²`) coincide (`hl1c_cap`); the ceiling `u_ℓ(x, β)` is above
the floor `u_f(x)` there (`hl1_uf_le_ul`). `hs1_central_face_proof` chains the norm,
beta and shape steps and closes at `α = 1` and at the cap with the outer branch-B signs.

## Main API

* `hl1c_cap`, `hl1_uf_le_ul`, `hs1_central_face_proof`.
-/

@[expose] public section

namespace SmoothedOctagon

open Set Real

/-- **At the cap the central and outer tests coincide.** -/
theorem hl1c_cap {x a b u : ℝ} (hx : 0 < x) (ha : 0 < a) (hcap : x * (x + 2) = 6 * a ^ 2) :
    hh1cF0 x a b u = hh1oF0 x a b u ∧ hh1cF1 x a b u = hh1oF1 x a b u := by
  have hKc : hh1cK x a = 7 * a ^ 2 := by unfold hh1cK; rw [hcap]; ring
  have hKo : hh1oK a = (1 + x) ^ 2 := by unfold hh1oK; linear_combination -hcap
  have hS : (1 + x) ≠ 0 := by linarith
  have ha0 : a ≠ 0 := ha.ne'
  have hL : hh1cL x a = hh1oL a := by unfold hh1cL hh1oL; rw [hKc, hKo]
  have hd : hh1cd x a b = hh1od x a b := by unfold hh1cd hh1od; rw [hKc]
  have hv : hh1cv x = hh1ov x a := by
    unfold hh1cv hh1ov; rw [hKo]; field_simp
  have hE : hh1cE x u = hh1oE x a u := by unfold hh1cE hh1oE; rw [hKo]
  have hw : hh1cw x a b u = hh1ow x a b u := by unfold hh1cw hh1ow; rw [hL, hd, hv, hE]
  have hEL : hh1cEL x a b u = hh1oEL x a b u := by unfold hh1cEL hh1oEL; rw [hL, hd, hE]
  have hG : hh1cG x u = hh1oG x a u := by
    unfold hh1cG hh1oG; rw [hv, hE, hKo, hcap]; field_simp; ring
  have hq : hh1cq x a = 1 / 7 := by unfold hh1cq; rw [hKc]; field_simp
  have hy : hh1cy x a b = hh1oy a b := by unfold hh1cy hh1oy; rw [hKc]; field_simp
  have hT : hh1cT x a b = hh1oT a b := by unfold hh1cT hh1oT; rw [hKc]; field_simp
  have h0 : hh1cF0 x a b u = hh1oF0 x a b u := by
    unfold hh1cF0 hh1oF0 hh1cR2 hh1oR2; rw [hG, hw, hEL, hq, hy]
  refine ⟨h0, ?_⟩
  unfold hh1cF1 hh1oF1; rw [h0, hT, hw]

/-- `u_f(x) ≤ u_ℓ(x, β)` for `3/2 ≤ x ≤ 2`, `x ≤ β ≤ 7x/6`. -/
theorem hl1_uf_le_ul {x b : ℝ} (hx : 3 / 2 ≤ x) (hx2 : x ≤ 2) (hxb : x ≤ b) (hb : b ≤ 7 * x / 6) :
    hsUf x ≤ hsUl x b := by
  unfold hsUf hsUl
  have hb1 : 0 < b - 1 := by linarith
  have hS : 0 < 1 + x := by linarith
  rw [add_le_add_iff_left, div_le_div_iff₀ (by positivity) (by positivity)]
  have hq : 0 ≤ (x - 1) ^ 2 := sq_nonneg _
  have key : 2 * (35 * x + 13) * (b - 1) ≤ 7 * (1 + x) * (b + 15 * x - 16) := by nlinarith
  have : (x - 1) ^ 2 * (8 * (1 + x) * (35 * x + 13) * (b - 1)) ≤
      (x - 1) ^ 2 * (b + 15 * x - 16) * (28 * (x + 1) ^ 2) := by
    have := mul_le_mul_of_nonneg_left key (mul_nonneg hq (by positivity : (0 : ℝ) ≤ 4 * (1 + x)))
    nlinarith
  linarith

/-- **The central low-ratio face**: on the central face `q = q_c` with the order strip in `β`,
`3/4 ≤ u ≤ u_ℓ(x, β)` and `2 ≤ τ ≤ r_A/q_c`: `Γ_*(q_c) - (7/96)R*_τ(q_c) > 9193/50000`. -/
theorem hs1_central_face_proof {x al be u τ : ℝ} (hx : 1 < x) (hx2 : x ≤ 2) (hal : 1 ≤ al)
    (hqc : 6 * al ^ 2 ≤ x * (x + 2)) (hb : x + 8 * x * (al - 1) / (9 * x + 8) ≤ be)
    (hb' : be ≤ x + x * (7 * x + 1) * (al - 1) / (4 * x ^ 2 + 11 * x + 1)) (hu : 3 / 4 ≤ u)
    (hul : u ≤ hsUl x be) (hτ : 2 ≤ τ) (hτT : τ * hsQc x al ≤ hsRA al be) :
    9193 / 50000 < hsGs x al u (hsQc x al) - 7 / 96 * hsRs x be al u (hsQc x al) τ := by
  have hx0 : 0 < x := by linarith
  have hx41 : 41 / 25 ≤ x := by nlinarith
  have ha76 : al ≤ 7 / 6 := by nlinarith
  have haU : al ≤ (1013 * x + 676) / 2340 := hl1c_aU hx.le (by linarith) hqc
  have hA : 0 ≤ al - 1 := by linarith
  have hblo : x + (al - 1) / 2 ≤ be := by
    have : (al - 1) / 2 ≤ 8 * x * (al - 1) / (9 * x + 8) := by
      rw [le_div_iff₀ (by linarith)]; nlinarith
    linarith
  have hbhi : be ≤ x + 10 / 13 * (al - 1) := by
    have : x * (7 * x + 1) * (al - 1) / (4 * x ^ 2 + 11 * x + 1) ≤ 10 / 13 * (al - 1) := by
      rw [div_le_iff₀ (by positivity)]
      nlinarith [mul_nonneg hA (mul_nonneg (by linarith : (0 : ℝ) ≤ 2 - x)
        (by linarith : (0 : ℝ) ≤ 51 * x + 5))]
    linarith
  have hxb : x ≤ be := by linarith
  have hred := hh1c_face_red (u := u) hx0 hal (by linarith) hτ hτT
  -- the cap
  set ac := Real.sqrt (x * (x + 2) / 6) with hacdef
  have hac2 : ac ^ 2 = x * (x + 2) / 6 := Real.sq_sqrt (by positivity)
  have hac0 : 0 ≤ ac := Real.sqrt_nonneg _
  have hacal : al ≤ ac := Real.le_sqrt_of_sq_le (by linarith)
  have hcap : x * (x + 2) = 6 * ac ^ 2 := by rw [hac2]; ring
  have hacU : ac ≤ (1013 * x + 676) / 2340 := hl1c_aU hx.le (by linarith) (by linarith)
  have hac76 : ac ≤ 7 / 6 := by nlinarith
  have hac65 : ac ≤ 6 / 5 := by linarith
  have hac1 : 1 ≤ ac := by linarith
  obtain ⟨hcap0, hcap1⟩ := hl1c_cap (b := x + 10 / 13 * (ac - 1)) (u := hsUl x (x + 10 / 13 * (ac - 1)))
    hx0 (by linarith) hcap
  obtain ⟨-, hcap1'⟩ := hl1c_cap (b := x + 10 / 13 * (ac - 1)) (u := 19 / 25) hx0 (by linarith) hcap
  have hUlb : hsUl x be ≤ 19 / 25 := by
    have := (hh1_Ul_bounds hx hx2 hxb).2; linarith
  -- the second test
  have hF1 : 0 < hh1cF1 x al be u := by
    have h1 := hl1c_F1_ustep hx41 hx2 hal ha76 hblo hbhi hu (hul.trans hUlb)
    have h2 := hl1c_F1_bstep hx41 hx2 hal ha76 hblo hbhi le_rfl
    have h3 := hl1c_F1_conc hx41 hx2 hal hacal hacU hac76
    have t1 : 0 < hh1cF1 x 1 (x + 10 / 13 * (1 - 1)) (19 / 25) := by
      rw [show x + 10 / 13 * ((1 : ℝ) - 1) = x by ring]; exact hl1cT1 hx41 hx2
    have t2 : 0 < hh1cF1 x ac (x + 10 / 13 * (ac - 1)) (19 / 25) := by
      rw [hcap1']
      exact hl1o_B_F1 (by linarith) hx2 hac1 hac65 hcap.le (by norm_num) (by norm_num) rfl
        (by norm_num) (by norm_num)
    have := lt_of_lt_of_le (lt_min t1 t2) h3
    linarith
  -- the first test
  have hF0 : 0 < hh1cF0 x al be u := by
    have h1 := hl1c_F0_ustep hx41 hx2 hal ha76 hblo hbhi hu hul
    have h2 := hl1c_F0_bstep hx41 hx2 hal ha76 haU hblo hbhi le_rfl
    have h3 := hl1c_F0_astep_ul hx41 hx2 hal hacal hacU hac76
    have t : 0 < hh1cF0 x ac (x + 10 / 13 * (ac - 1)) (hsUl x (x + 10 / 13 * (ac - 1))) := by
      rw [hcap0]
      have hbx : x ≤ x + 10 / 13 * (ac - 1) := by nlinarith
      exact hl1o_B_F0 (by linarith) hx2 hac1 hac65 hcap.le hbx le_rfl
        (hl1_uf_le_ul (by linarith) hx2 hbx (by nlinarith)) le_rfl
    linarith
  have := lt_min hF0 hF1
  linarith

end SmoothedOctagon
