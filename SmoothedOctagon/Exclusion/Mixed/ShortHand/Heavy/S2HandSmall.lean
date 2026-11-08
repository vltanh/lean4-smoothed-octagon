module

public import SmoothedOctagon.Exclusion.Mixed.ShortHand.Heavy.S2HandSmallLink

/-!
# S2 hand signs: the outer face for small `α`

`hs2_outer_sign_small_proof` proves the statement of `hs2_outer_sign_small` following
`archive/lighter-proofs/SHORT_RATIO_OUTER_COMPLETE.md` §3: the actual shape has
`a_f(x) = (36x + 25)/84 ≤ α ≤ 3/2` and `5/8 ≤ c ≤ c_+(x) = (24x + 51)/128` (§2 (7)-(8)); the
incoming norm `u_s` is raised to `ū = u_s(x, x + c(a_f - 1))`; the fixed-norm reciprocal convexity
(`S2HandRecip`) bounds each test by its values at `α = 3/2` (the middle terminal of
`S2HandLarge`, since `ū ≤ u_v`) and at `α = a_f`; there the beta comparison (`S2HandSmallNorm`)
reaches `c = c_+`, the terminal curve of `S2HandSmallLink`.

Route: the notes' moving-norm reciprocal convexity (`SHORT_RATIO_OUTER_RECIPROCAL` §4) is replaced
by the fixed norm `ū` (see `S2HandSmallNorm`).

## Main API

* `hl2_af_lt`, `hl2_c_le_cplus`, `hl2_term_x`, `hl2_small_H0`, `hl2_small_H1`.
* `hs2_outer_sign_small_proof`.
-/

@[expose] public section

namespace SmoothedOctagon

open Real Set

/-- `a_f(x) < α` from `x(x + 2) ≤ 6α²` (`SHORT_RATIO_OUTER_COMPLETE` (7)). -/
theorem hl2_af_lt {x al : ℝ} (hx : 13 / 6 ≤ x) (hx2 : x ≤ 12 / 5) (hal : 1 ≤ al)
    (hqc : x * (x + 2) ≤ 6 * al ^ 2) : (36 * x + 25) / 84 < al := by
  by_contra h
  push Not at h
  have h1 : al ^ 2 ≤ ((36 * x + 25) / 84) ^ 2 := pow_le_pow_left₀ (by linarith) h 2
  nlinarith

/-- `c ≤ c_+(x) = (24x + 51)/128` (`SHORT_RATIO_OUTER_COMPLETE` (8)). -/
theorem hl2_c_le_cplus {x al be c : ℝ} (hx : 13 / 6 ≤ x) (hx2 : x ≤ 12 / 5) (hal : 1 < al)
    (hb' : be ≤ x + x * (7 * x + 1) * (al - 1) / (4 * x ^ 2 + 11 * x + 1))
    (hbe : be = x + c * (al - 1)) : c ≤ (24 * x + 51) / 128 := by
  have ha : 0 < al - 1 := by linarith
  have hR : 0 < 4 * x ^ 2 + 11 * x + 1 := by positivity
  have h1 : c * (al - 1) ≤ x * (7 * x + 1) * (al - 1) / (4 * x ^ 2 + 11 * x + 1) := by linarith
  have h2 : c ≤ x * (7 * x + 1) / (4 * x ^ 2 + 11 * x + 1) := by
    rw [le_div_iff₀ hR]
    rw [le_div_iff₀ hR] at h1
    nlinarith
  have h3 : x * (7 * x + 1) / (4 * x ^ 2 + 11 * x + 1) ≤ (24 * x + 51) / 128 := by
    rw [div_le_div_iff₀ hR (by norm_num)]
    nlinarith [mul_nonneg (sub_nonneg.2 hx) (sub_nonneg.2 hx2), sq_nonneg (x - 9 / 4),
      mul_nonneg (mul_nonneg (sub_nonneg.2 hx) (sub_nonneg.2 hx)) (sub_nonneg.2 hx)]
  linarith

/-- The terminal curve in the leaf's coordinates. -/
theorem hl2_term_x {x : ℝ} (hx : 13 / 6 ≤ x) (hx2 : x ≤ 12 / 5) :
    hl2H0 x ((24 * x + 51) / 128) (hsUs x (x + (24 * x + 51) / 128 * ((36 * x + 25) / 84 - 1)))
        (84 / (36 * x + 25)) < 0 ∧
      hl2H1 x ((24 * x + 51) / 128) (hsUs x (x + (24 * x + 51) / 128 * ((36 * x + 25) / 84 - 1)))
        (84 / (36 * x + 25)) < 0 := by
  obtain ⟨hr1, hr2, -⟩ := hl2_rf hx hx2
  have key := hl2_term_r hr1 hr2
  have hA : 0 < 36 * x + 25 := by linarith
  rw [show 7 / (3 * (84 / (36 * x + 25))) - 25 / 36 = x by field_simp; ring,
    show 1 / (84 / (36 * x + 25)) - 1 = (36 * x + 25) / 84 - 1 by field_simp] at key
  exact key

/-- `5/2 < Z < 19/6` on the smaller rectangle. -/
theorem hl2_Z_small {x c r : ℝ} (hx : 13 / 6 ≤ x) (hx2 : x ≤ 12 / 5) (hc : 5 / 8 ≤ c)
    (hc2 : c ≤ 7 / 8) (hr : 2 / 3 ≤ r) (hr2 : r ≤ 5 / 6) :
    5 / 2 < hl2Zr x c r ∧ hl2Zr x c r < 19 / 6 := by
  unfold hl2Zr; constructor <;> nlinarith

/-- The small-shape sign for `H₀` (`SHORT_RATIO_OUTER_COMPLETE` §3). -/
theorem hl2_small_H0 {x al c : ℝ} (hx : 13 / 6 ≤ x) (hx2 : x ≤ 12 / 5)
    (haf : (36 * x + 25) / 84 ≤ al) (hal' : al ≤ 3 / 2) (hc : 5 / 8 ≤ c)
    (hcp : c ≤ (24 * x + 51) / 128) : hl2H0 x c (hsUs x (x + c * (al - 1))) (1 / al) < 0 := by
  have hc2 : c ≤ 7 / 8 := by linarith
  have hcp2 : (24 * x + 51) / 128 ≤ 7 / 8 := by linarith
  obtain ⟨hr1, hr2, -⟩ := hl2_rf hx hx2
  have hal0 : 0 < al := by linarith
  have hA : 0 < 36 * x + 25 := by linarith
  have hr : 2 / 3 ≤ 1 / al := by rw [le_div_iff₀ hal0]; linarith
  have hrf : 1 / al ≤ 84 / (36 * x + 25) := by
    rw [div_le_div_iff₀ hal0 hA]; linarith
  have hx3 : 1 / x ≤ 2 / 3 := by rw [div_le_iff₀ (by linarith)]; linarith
  set ub := hsUs x (x + c * ((36 * x + 25) / 84 - 1)) with hub
  -- the fixed norm `ū`
  have hb0 : x ≤ x + c * ((36 * x + 25) / 84 - 1) := by nlinarith
  have hbb : x + c * ((36 * x + 25) / 84 - 1) ≤ x + c * (al - 1) := by nlinarith
  obtain ⟨hule, -⟩ := hl2_Us_lip hx hx2 hb0 hbb
  have hub1 : ub ≤ hsVbar x := hl2_ubar_le hx hx2 hc
  have hub2 := (hl2_Vbar_le hx hx2).2
  have hub0 : 3 / 4 ≤ ub := by
    have hb1 : 0 < x + c * ((36 * x + 25) / 84 - 1) - 1 := by linarith
    rw [hub, hl2_Us_eq hb1.ne']
    have := (hl2_kx_bounds hx hx2).1
    have : 0 ≤ hl2kx x / (x + c * ((36 * x + 25) / 84 - 1) - 1) := by positivity
    linarith
  -- step A: raise the norm to `ū`
  have hZ := hl2_Z_small hx hx2 hc hc2 hr (by linarith)
  obtain ⟨hHu, -⟩ := hl2_Hu_pos (m := 4 - hl2Zr x c (1 / al) / 2) hx hx2 hc hc2 hr
    (by linarith) (by linarith) (by linarith)
  have sA := hl2_Ht_u (4 - hl2Zr x c (1 / al) / 2) x c (hsUs x (x + c * (al - 1))) ub (1 / al)
  have hA' : hl2H0 x c (hsUs x (x + c * (al - 1))) (1 / al) ≤ hl2H0 x c ub (1 / al) := by
    unfold hl2H0
    nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ ub - hsUs x (x + c * (al - 1))) hHu.le]
  -- step B: convexity at fixed `ū`
  have sB := hl2_H0_le_max hx hx2 hc hc2 hub0 (by linarith) hx3 hr hrf (by linarith)
  -- step C: the middle shape
  have hZm := hl2_Z_small hx hx2 hc hc2 (le_refl (2 / 3 : ℝ)) (by norm_num)
  obtain ⟨hHum, -⟩ := hl2_Hu_pos (m := 4 - hl2Zr x c (2 / 3) / 2) hx hx2 hc hc2
    (le_refl (2 / 3 : ℝ)) (by norm_num) (by linarith) (by linarith)
  have sC := hl2_Ht_u (4 - hl2Zr x c (2 / 3) / 2) x c ub (hsVbar x) (2 / 3)
  have hmid : hl2H0 x c ub (2 / 3) < 0 := by
    have := hl2_mid_H0 hx hx2 hc hc2
    unfold hl2H0 at this ⊢
    nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ hsVbar x - ub) hHum.le]
  -- step D: the beta comparison and the terminal
  have sD := hl2_beta_H0 hx hx2 hc hcp hcp2
  have sE := (hl2_term_x hx hx2).1
  rw [← hub] at sD
  exact lt_of_le_of_lt hA' (lt_of_le_of_lt sB (max_lt hmid (lt_of_le_of_lt sD sE)))

/-- The small-shape sign for `H₁` (`SHORT_RATIO_OUTER_COMPLETE` §3). -/
theorem hl2_small_H1 {x al c : ℝ} (hx : 13 / 6 ≤ x) (hx2 : x ≤ 12 / 5)
    (haf : (36 * x + 25) / 84 ≤ al) (hal' : al ≤ 3 / 2) (hc : 5 / 8 ≤ c)
    (hcp : c ≤ (24 * x + 51) / 128) : hl2H1 x c (hsUs x (x + c * (al - 1))) (1 / al) < 0 := by
  have hc2 : c ≤ 7 / 8 := by linarith
  have hcp2 : (24 * x + 51) / 128 ≤ 7 / 8 := by linarith
  obtain ⟨hr1, hr2, -⟩ := hl2_rf hx hx2
  have hal0 : 0 < al := by linarith
  have hA : 0 < 36 * x + 25 := by linarith
  have hr : 2 / 3 ≤ 1 / al := by rw [le_div_iff₀ hal0]; linarith
  have hrf : 1 / al ≤ 84 / (36 * x + 25) := by
    rw [div_le_div_iff₀ hal0 hA]; linarith
  have hx3 : 1 / x ≤ 2 / 3 := by rw [div_le_iff₀ (by linarith)]; linarith
  set ub := hsUs x (x + c * ((36 * x + 25) / 84 - 1)) with hub
  have hb0 : x ≤ x + c * ((36 * x + 25) / 84 - 1) := by nlinarith
  have hbb : x + c * ((36 * x + 25) / 84 - 1) ≤ x + c * (al - 1) := by nlinarith
  obtain ⟨hule, -⟩ := hl2_Us_lip hx hx2 hb0 hbb
  have hub1 : ub ≤ hsVbar x := hl2_ubar_le hx hx2 hc
  have hub2 := (hl2_Vbar_le hx hx2).2
  have hub0 : 3 / 4 ≤ ub := by
    have hb1 : 0 < x + c * ((36 * x + 25) / 84 - 1) - 1 := by linarith
    rw [hub, hl2_Us_eq hb1.ne']
    have := (hl2_kx_bounds hx hx2).1
    have : 0 ≤ hl2kx x / (x + c * ((36 * x + 25) / 84 - 1) - 1) := by positivity
    linarith
  have hZ := hl2_Z_small hx hx2 hc hc2 hr (by linarith)
  have hm1 : 7 / hl2Zr x c (1 / al) + 1 / 4 ≤ 13 / 4 := by
    have : 7 / hl2Zr x c (1 / al) ≤ 3 := by rw [div_le_iff₀ (by linarith)]; linarith
    linarith
  obtain ⟨hHu, -⟩ := hl2_Hu_pos (m := 7 / hl2Zr x c (1 / al) + 1 / 4) hx hx2 hc hc2 hr
    (by linarith) (by have : 0 < 7 / hl2Zr x c (1 / al) := div_pos (by norm_num) (by linarith)
                      linarith) hm1
  have sA := hl2_Ht_u (7 / hl2Zr x c (1 / al) + 1 / 4) x c (hsUs x (x + c * (al - 1))) ub (1 / al)
  have hA' : hl2H1 x c (hsUs x (x + c * (al - 1))) (1 / al) ≤ hl2H1 x c ub (1 / al) := by
    unfold hl2H1
    nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ ub - hsUs x (x + c * (al - 1))) hHu.le]
  have sB := hl2_H1_le_max hx hx2 hc hc2 hub0 (by linarith) hx3 hr hrf (by linarith)
  have hZm := hl2_Z_small hx hx2 hc hc2 (le_refl (2 / 3 : ℝ)) (by norm_num)
  have hm1' : 7 / hl2Zr x c (2 / 3) + 1 / 4 ≤ 13 / 4 := by
    have : 7 / hl2Zr x c (2 / 3) ≤ 3 := by rw [div_le_iff₀ (by linarith)]; linarith
    linarith
  obtain ⟨hHum, -⟩ := hl2_Hu_pos (m := 7 / hl2Zr x c (2 / 3) + 1 / 4) hx hx2 hc hc2
    (le_refl (2 / 3 : ℝ)) (by norm_num)
    (by have : 0 < 7 / hl2Zr x c (2 / 3) := div_pos (by norm_num) (by linarith)
        linarith) hm1'
  have sC := hl2_Ht_u (7 / hl2Zr x c (2 / 3) + 1 / 4) x c ub (hsVbar x) (2 / 3)
  have hmid : hl2H1 x c ub (2 / 3) < 0 := by
    have := hl2_mid_H1 hx hx2 hc hc2
    unfold hl2H1 at this ⊢
    nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ hsVbar x - ub) hHum.le]
  have sD := hl2_beta_H1 hx hx2 hc hcp hcp2
  have sE := (hl2_term_x hx hx2).2
  rw [← hub] at sD
  exact lt_of_le_of_lt hA' (lt_of_le_of_lt sB (max_lt hmid (lt_of_le_of_lt sD sE)))

/-- **The outer sharp-ratio face, small `α`** (`hs2_outer_sign_small`;
`SHORT_RATIO_OUTER_COMPLETE` §3). -/
theorem hs2_outer_sign_small_proof {x al be τ : ℝ} (hx : 13 / 6 ≤ x) (hx2 : x ≤ 12 / 5)
    (hal : 1 ≤ al) (hal' : al ≤ 3 / 2) (_hax : al ≤ x) (hqc : x * (x + 2) ≤ 6 * al ^ 2)
    (hb : x + 8 * x * (al - 1) / (9 * x + 8) ≤ be)
    (hb' : be ≤ x + x * (7 * x + 1) * (al - 1) / (4 * x ^ 2 + 11 * x + 1)) (hτ : 2 ≤ τ)
    (hτT : τ ≤ 7 * hsRA al be) :
    hsF x be al (hsUs x be) (1 / 7) τ (log (τ * (1 / 7) / hsRA al be))
      (2 - 7 * τ * (1 / 7) / (4 * hsRA al be)) < 0 := by
  have haf := hl2_af_lt hx hx2 hal hqc
  have hal1 : 1 < al := by linarith
  obtain ⟨c, hc1, hc2, hbe⟩ := hl2_strip_c hx hx2 hal1 hb hb'
  have hcp := hl2_c_le_cplus hx hx2 hal1 hb' hbe
  have hal0 : 0 < al := by linarith
  have hB : 0 < al + be := by rw [hbe]; nlinarith
  have hrA : 0 < hsRA al be := by unfold hsRA; positivity
  have hk : 0 < 1 / 7 / hsRA al be := by positivity
  have hτk : τ * (1 / 7 / hsRA al be) ≤ 1 := by
    rw [mul_div_assoc', div_le_one hrA]
    linarith
  rw [hl2_hsF_face]
  refine lt_of_le_of_lt (hl2_tau_outer hk hτ hτk) (max_lt ?_ ?_)
  · rw [hl2_face_H0 hal0 hbe hB, hbe]
    exact hl2_small_H0 hx hx2 haf.le hal' hc1 hcp
  · rw [hl2_face_H1 hal0 hbe hB, hbe]
    exact hl2_small_H1 hx hx2 haf.le hal' hc1 hcp

end SmoothedOctagon
