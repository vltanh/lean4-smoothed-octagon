module

public import SmoothedOctagon.Exclusion.Mixed.SmallerShort.LowerRatio.CentralFace.LowRatio

/-!
# Smaller-short window, lower ratio: the central face, assembly

At the cap `x(x + 2) = 6α²` the central transport (`K = 7α²`) and
the outer transport (`K = 6α² + 1 = S²`) coincide (`lrc_cap`); the ceiling `u_ℓ(x, β)` is above
the floor `u_f(x)` there (`lr_uf_le_ul`). `lr_central_face_proof` chains the norm,
beta and shape steps and closes at `α = 1` and at the cap with the outer branch-B signs.

## Main API

* `lrc_cap`, `lr_uf_le_ul`, `lr_central_face_proof`.
-/

@[expose] public section

namespace SmoothedOctagon

open Set Real

/-- **At the cap the central and outer tests coincide.** -/
theorem lrc_cap {x a b u : ℝ} (hx : 0 < x) (ha : 0 < a) (hcap : x * (x + 2) = 6 * a ^ 2) :
    lrcF0 x a b u = lroF0 x a b u ∧ lrcF1 x a b u = lroF1 x a b u := by
  have hKc : lrcK x a = 7 * a ^ 2 := by unfold lrcK; rw [hcap]; ring
  have hKo : lroK a = (1 + x) ^ 2 := by unfold lroK; linear_combination -hcap
  have hS : (1 + x) ≠ 0 := by linarith
  have ha0 : a ≠ 0 := ha.ne'
  have hL : lrcL x a = lroL a := by unfold lrcL lroL; rw [hKc, hKo]
  have hd : lrcd x a b = lrod x a b := by unfold lrcd lrod; rw [hKc]
  have hv : lrcv x = lrov x a := by
    unfold lrcv lrov; rw [hKo]; field_simp
  have hE : lrcE x u = lroE x a u := by unfold lrcE lroE; rw [hKo]
  have hw : lrcw x a b u = lrow x a b u := by unfold lrcw lrow; rw [hL, hd, hv, hE]
  have hEL : lrcEL x a b u = lroEL x a b u := by unfold lrcEL lroEL; rw [hL, hd, hE]
  have hG : lrcG x u = lroG x a u := by
    unfold lrcG lroG; rw [hv, hE, hKo, hcap]; field_simp; ring
  have hq : lrcq x a = 1 / 7 := by unfold lrcq; rw [hKc]; field_simp
  have hy : lrcy x a b = lroy a b := by unfold lrcy lroy; rw [hKc]; field_simp
  have hT : lrcT x a b = lroT a b := by unfold lrcT lroT; rw [hKc]; field_simp
  have h0 : lrcF0 x a b u = lroF0 x a b u := by
    unfold lrcF0 lroF0 lrcR2 lroR2; rw [hG, hw, hEL, hq, hy]
  refine ⟨h0, ?_⟩
  unfold lrcF1 lroF1; rw [h0, hT, hw]

/-- `u_f(x) ≤ u_ℓ(x, β)` for `3/2 ≤ x ≤ 2`, `x ≤ β ≤ 7x/6`. -/
theorem lr_uf_le_ul {x b : ℝ} (hx : 3 / 2 ≤ x) (_hx2 : x ≤ 2) (hxb : x ≤ b) (hb : b ≤ 7 * x / 6) :
    ssUf x ≤ ssUl x b := by
  unfold ssUf ssUl
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
theorem lr_central_face_proof {x al be u τ : ℝ} (hx : 1 < x) (hx2 : x ≤ 2) (hal : 1 ≤ al)
    (hqc : 6 * al ^ 2 ≤ x * (x + 2)) (hb : x + 8 * x * (al - 1) / (9 * x + 8) ≤ be)
    (hb' : be ≤ x + x * (7 * x + 1) * (al - 1) / (4 * x ^ 2 + 11 * x + 1)) (hu : 3 / 4 ≤ u)
    (hul : u ≤ ssUl x be) (hτ : 2 ≤ τ) (hτT : τ * ssQc x al ≤ ssRA al be) :
    9193 / 50000 < ssGs x al u (ssQc x al) - 7 / 96 * ssRs x be al u (ssQc x al) τ := by
  have hx0 : 0 < x := by linarith
  have hx41 : 41 / 25 ≤ x := by nlinarith
  have ha76 : al ≤ 7 / 6 := by nlinarith
  have haU : al ≤ (1013 * x + 676) / 2340 := lrc_aU hx.le (by linarith) hqc
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
  have hred := lrc_face_red (u := u) hx0 hal (by linarith) hτ hτT
  -- the cap
  set ac := Real.sqrt (x * (x + 2) / 6) with hacdef
  have hac2 : ac ^ 2 = x * (x + 2) / 6 := Real.sq_sqrt (by positivity)
  have hac0 : 0 ≤ ac := Real.sqrt_nonneg _
  have hacal : al ≤ ac := Real.le_sqrt_of_sq_le (by linarith)
  have hcap : x * (x + 2) = 6 * ac ^ 2 := by rw [hac2]; ring
  have hacU : ac ≤ (1013 * x + 676) / 2340 := lrc_aU hx.le (by linarith) (by linarith)
  have hac76 : ac ≤ 7 / 6 := by nlinarith
  have hac65 : ac ≤ 6 / 5 := by linarith
  have hac1 : 1 ≤ ac := by linarith
  obtain ⟨hcap0, hcap1⟩ := lrc_cap (b := x + 10 / 13 * (ac - 1)) (u := ssUl x (x + 10 / 13 * (ac - 1)))
    hx0 (by linarith) hcap
  obtain ⟨-, hcap1'⟩ := lrc_cap (b := x + 10 / 13 * (ac - 1)) (u := 19 / 25) hx0 (by linarith) hcap
  have hUlb : ssUl x be ≤ 19 / 25 := by
    have := (lr_Ul_bounds hx hx2 hxb).2; linarith
  -- the second test
  have hF1 : 0 < lrcF1 x al be u := by
    have h1 := lrc_F1_ustep hx41 hx2 hal ha76 hblo hbhi hu (hul.trans hUlb)
    have h2 := lrc_F1_bstep hx41 hx2 hal ha76 hblo hbhi le_rfl
    have h3 := lrc_F1_conc hx41 hx2 hal hacal hacU hac76
    have t1 : 0 < lrcF1 x 1 (x + 10 / 13 * (1 - 1)) (19 / 25) := by
      rw [show x + 10 / 13 * ((1 : ℝ) - 1) = x by ring]; exact lrcT1 hx41 hx2
    have t2 : 0 < lrcF1 x ac (x + 10 / 13 * (ac - 1)) (19 / 25) := by
      rw [hcap1']
      exact lro_B_F1 (by linarith) hx2 hac1 hac65 hcap.le (by norm_num) (by norm_num) rfl
        (by norm_num) (by norm_num)
    have := lt_of_lt_of_le (lt_min t1 t2) h3
    linarith
  -- the first test
  have hF0 : 0 < lrcF0 x al be u := by
    have h1 := lrc_F0_ustep hx41 hx2 hal ha76 hblo hbhi hu hul
    have h2 := lrc_F0_bstep hx41 hx2 hal ha76 haU hblo hbhi le_rfl
    have h3 := lrc_F0_astep_ul hx41 hx2 hal hacal hacU hac76
    have t : 0 < lrcF0 x ac (x + 10 / 13 * (ac - 1)) (ssUl x (x + 10 / 13 * (ac - 1))) := by
      rw [hcap0]
      have hbx : x ≤ x + 10 / 13 * (ac - 1) := by nlinarith
      exact lro_B_F0 (by linarith) hx2 hac1 hac65 hcap.le hbx le_rfl
        (lr_uf_le_ul (by linarith) hx2 hbx (by nlinarith)) le_rfl
    linarith
  have := lt_min hF0 hF1
  linarith

end SmoothedOctagon
