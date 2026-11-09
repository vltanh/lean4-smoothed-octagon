module

public import SmoothedOctagon.Exclusion.Mixed.SmallerShort.Displacement.OuterFace.LowerCurves

/-!
# Smaller-short window, displacement, outer face: the two lower-shape curves (signs)

The outer face sign `dsp_outer_face_proof`, fifth part: the polynomial identities for the derivative bounds
along the lower-shape curves (`dspo_N0_id`, `dspo_N1_id`, `dspo_M0_id`, `dspo_M1_id`, `dspo_Y0_id`,
`dspo_Z0_id`), each a polynomial in `h = x - 2` with signs checked on `0 ≤ h ≤ 1/6`, and the sign of
the two lower-shape curves.

## Main API

* `dspo_low_curve`: `G(x, 19x/50, n, r_*) < 0` for `n ∈ {25/8, 7/2}`, `2 ≤ x ≤ 13/6`.
* `dspo_low`: `G(x, C, n, r_*) < 0` for `3/5 ≤ C ≤ 19x/50` and `n ∈ {25/8, 7/2}`.
-/

@[expose] public section

namespace SmoothedOctagon

open Real Set

section Curve

variable {n x : ℝ}

set_option linter.unusedSimpArgs false in
theorem dspo_N0_id (hx : 0 < x) :
    (19 / 4 - dspoLdD (25 / 8) x) * (3062500 * (x + 1) ^ 5) =
      -3427600 * (x - 2) ^ 6 - 53594215 * (x - 2) ^ 5 - 341187225 * (x - 2) ^ 4 -
        1128855722 * (x - 2) ^ 3 - 1824003552 * (x - 2) ^ 2 - 990072519 * (x - 2) + 257335889 := by
  unfold dspoLdD dspoAc0 dspoAc1 dspoAc2 dspoAc3 dspoAc4 dspoα0 dspoα1 dspoα2 dspoα3 dspoα4 dspoβ0
    dspoβ1 dspoβ2
  have hx1 : x + 1 ≠ 0 := by linarith
  dsp_deriv
  field_simp
  ring

set_option linter.unusedSimpArgs false in
theorem dspo_N1_id (hx : 0 < x) :
    (26 / 5 - dspoLdD (7 / 2) x) * (5468750 * (x + 1) ^ 5) =
      -6855200 * (x - 2) ^ 6 - 106804805 * (x - 2) ^ 5 - 676620075 * (x - 2) ^ 4 -
        2218057669 * (x - 2) ^ 3 - 3503959029 * (x - 2) ^ 2 - 1720404138 * (x - 2) + 695230228 := by
  unfold dspoLdD dspoAc0 dspoAc1 dspoAc2 dspoAc3 dspoAc4 dspoα0 dspoα1 dspoα2 dspoα3 dspoα4 dspoβ0
    dspoβ1 dspoβ2
  have hx1 : x + 1 ≠ 0 := by linarith
  dsp_deriv
  field_simp
  ring

theorem dspo_M0_id (hx : 0 < x) :
    (18 / 5 - dspoA x (19 * x / 50) (25 / 8) (13 / (5 * (x + 1)))) * (3062500 * (x + 1) ^ 4) =
      -1713800 * (x - 2) ^ 6 - 37292690 * (x - 2) ^ 5 - 285159828 * (x - 2) ^ 4 -
        983843464 * (x - 2) ^ 3 - 1551465687 * (x - 2) ^ 2 - 809079076 * (x - 2) + 212579377 := by
  unfold dspoA dspoAc0 dspoAc1 dspoAc2 dspoAc3 dspoAc4 dspoα0 dspoα1 dspoα2 dspoα3 dspoα4 dspoβ0
    dspoβ1 dspoβ2
  have hx1 : x + 1 ≠ 0 := by linarith
  field_simp
  ring

theorem dspo_M1_id (hx : 0 < x) :
    (18 / 5 - dspoA x (19 * x / 50) (7 / 2) (13 / (5 * (x + 1)))) * (5468750 * (x + 1) ^ 4) =
      -3427600 * (x - 2) ^ 6 - 73545505 * (x - 2) ^ 5 - 555438081 * (x - 2) ^ 4 -
        1887824303 * (x - 2) ^ 3 - 2904167349 * (x - 2) ^ 2 - 1395804152 * (x - 2) + 506917454 := by
  unfold dspoA dspoAc0 dspoAc1 dspoAc2 dspoAc3 dspoAc4 dspoα0 dspoα1 dspoα2 dspoα3 dspoα4 dspoβ0
    dspoβ1 dspoβ2
  have hx1 : x + 1 ≠ 0 := by linarith
  field_simp
  ring

/-- The closed form `V = (x - 1)²(95x² + 1148x - 1300)/(S(35x + 13)(95x² + 498x - 650))` of
`V = ū - 3/4` at `r_*`, `C = 19x/50`. -/
noncomputable def dspoVcl (x : ℝ) : ℝ :=
  (x - 1) ^ 2 * (95 * x ^ 2 + 1148 * x - 1300) / ((x + 1) * (35 * x + 13) * (95 * x ^ 2 + 498 * x - 650))

theorem dspo_Vcl_eq (hx : 3 / 2 ≤ x) : dspoV x (19 * x / 50) (13 / (5 * (x + 1))) = dspoVcl x := by
  have hQ : 0 < 95 * x ^ 2 + 498 * x - 650 := by nlinarith
  have hH : 19 * x / 50 + (x - 19 * x / 50 - 1) * (13 / (5 * (x + 1))) =
      (95 * x ^ 2 + 498 * x - 650) / (250 * (x + 1)) := by
    have : x + 1 ≠ 0 := by linarith
    field_simp; ring
  unfold dspoV dspoVcl dspoc
  rw [hH]
  have : x + 1 ≠ 0 := by linarith
  have : 35 * x + 13 ≠ 0 := by linarith
  generalize hQd : 95 * x ^ 2 + 498 * x - 650 = Q at hQ ⊢
  have : Q ≠ 0 := hQ.ne'
  field_simp
  rw [← hQd]
  ring

theorem dspo_Y0_id (hx : 3 / 2 ≤ x) :
    (1 / 110 - dspoVcl x) * (110 * (x + 1) * (35 * x + 13) * (95 * x ^ 2 + 498 * x - 650)) =
      -7125 * (x - 2) ^ 4 - 140390 * (x - 2) ^ 3 - 283841 * (x - 2) ^ 2 - 115690 * (x - 2) + 29414 := by
  have hQ : 0 < 95 * x ^ 2 + 498 * x - 650 := by nlinarith
  unfold dspoVcl
  have : x + 1 ≠ 0 := by linarith
  have : 35 * x + 13 ≠ 0 := by linarith
  generalize hQd : 95 * x ^ 2 + 498 * x - 650 = Q at hQ ⊢
  have : Q ≠ 0 := hQ.ne'
  field_simp
  rw [← hQd]
  ring

set_option linter.unusedSimpArgs false in
theorem dspo_Z0_id (hx : 3 / 2 ≤ x) :
    (7 / 800 - deriv dspoVcl x) *
      (800 * (x + 1) ^ 2 * (35 * x + 13) ^ 2 * (95 * x ^ 2 + 498 * x - 650) ^ 2) =
      77389375 * (x - 2) ^ 8 + 2261864500 * (x - 2) ^ 7 + 27371661650 * (x - 2) ^ 6 +
        153729796040 * (x - 2) ^ 5 + 405804725187 * (x - 2) ^ 4 + 503827505900 * (x - 2) ^ 3 +
        286854745744 * (x - 2) ^ 2 + 60769341560 * (x - 2) + 689585532 := by
  have hQ : 0 < 95 * x ^ 2 + 498 * x - 650 := by nlinarith
  have hD : (x + 1) * (35 * x + 13) * (95 * x ^ 2 + 498 * x - 650) ≠ 0 := by positivity
  unfold dspoVcl
  dsp_deriv
  have : x + 1 ≠ 0 := by linarith
  have : 35 * x + 13 ≠ 0 := by linarith
  generalize hQd : 95 * x ^ 2 + 498 * x - 650 = Q at hQ hD ⊢
  have : Q ≠ 0 := hQ.ne'
  field_simp
  rw [← hQd]
  ring

/-! ### The sign of the two curves -/

set_option hygiene false in
/-- The sign of a printed polynomial in `0 ≤ h ≤ 1/6` (hypotheses `hh`, `hh6`). -/
macro "dsp_hbox" : tactic => `(tactic| linarith
    [(dsp_mono1 hh hh6 1).1, (dsp_mono1 hh hh6 1).2, (dsp_mono1 hh hh6 2).1,
      (dsp_mono1 hh hh6 2).2, (dsp_mono1 hh hh6 3).1, (dsp_mono1 hh hh6 3).2,
      (dsp_mono1 hh hh6 4).1, (dsp_mono1 hh hh6 4).2, (dsp_mono1 hh hh6 5).1,
      (dsp_mono1 hh hh6 5).2, (dsp_mono1 hh hh6 6).1, (dsp_mono1 hh hh6 6).2,
      (dsp_mono1 hh hh6 7).1, (dsp_mono1 hh hh6 7).2, (dsp_mono1 hh hh6 8).1,
      (dsp_mono1 hh hh6 8).2])

/-- `z = Z(r_*)` along the curve. -/
noncomputable def dspoLz (x : ℝ) : ℝ := 1 + 19 * x / 50 + (x - 19 * x / 50) * (13 / (5 * (x + 1)))

theorem dspo_hd_Lz {t : ℝ} (ht : 0 < t) :
    HasDerivAt dspoLz (19 / 50 + 403 / (250 * (t + 1) ^ 2)) t := by
  have := ((((hasDerivAt_id t).const_mul 19).div_const 50).const_add 1).add
    (((hasDerivAt_id t).sub (((hasDerivAt_id t).const_mul 19).div_const 50)).mul (dsp_hd_rs ht))
  unfold dspoLz
  refine this.congr_deriv ?_
  simp only [Pi.sub_apply, id]
  have : t + 1 ≠ 0 := by linarith
  field_simp
  ring

theorem dspo_Lz_bds {x : ℝ} (hx : 2 ≤ x) (hx2 : x ≤ 13 / 6) : 17 / 6 ≤ dspoLz x ∧ dspoLz x ≤ 3 := by
  have e : dspoLz x = (95 * x ^ 2 + 748 * x + 250) / (250 * (x + 1)) := by
    unfold dspoLz
    have : x + 1 ≠ 0 := by linarith
    field_simp; ring
  rw [e]
  constructor
  · rw [le_div_iff₀ (by positivity)]; nlinarith
  · rw [div_le_iff₀ (by positivity)]; nlinarith

/-- The curve `x ↦ G(x, 19x/50, n, r_*)` has derivative `p' + V'd + Vd' + z'f(z)`. -/
theorem dspo_hd_curve {n t : ℝ} (ht : 2 ≤ t) :
    HasDerivAt (fun s => dspoG s (19 * s / 50) n (13 / (5 * (s + 1))))
      (dspoLpD n t + deriv dspoVcl t * dspoA t (19 * t / 50) n (13 / (5 * (t + 1))) +
        dspoVcl t * dspoLdD n t + (19 / 50 + 403 / (250 * (t + 1) ^ 2)) * dspof (dspoLz t)) t := by
  have ht0 : 0 < t := by linarith
  -- `V` in closed form near `t`
  have hQ : 0 < 95 * t ^ 2 + 498 * t - 650 := by nlinarith
  have hVd : DifferentiableAt ℝ dspoVcl t := by
    unfold dspoVcl
    have : (t + 1) * (35 * t + 13) * (95 * t ^ 2 + 498 * t - 650) ≠ 0 := by positivity
    fun_prop (disch := assumption)
  have hV : HasDerivAt (fun s => dspoV s (19 * s / 50) (13 / (5 * (s + 1)))) (deriv dspoVcl t) t := by
    refine hVd.hasDerivAt.congr_of_eventuallyEq ?_
    filter_upwards [Ioi_mem_nhds (by linarith : (3 / 2 : ℝ) < t)] with s hs
    exact dspo_Vcl_eq hs.le
  -- `Φ = 1/z - 56/(5z + 14)`
  have hZ := dspo_hd_Lz ht0
  have hz0 : 0 < dspoLz t := by
    unfold dspoLz
    have e : t - 19 * t / 50 = 31 * t / 50 := by ring
    rw [e]; positivity
  have hK : 5 * dspoLz t + 14 ≠ 0 := by positivity
  have hPhi := ((hasDerivAt_const t (1 : ℝ)).fun_div hZ hz0.ne').sub
    ((hasDerivAt_const t (56 : ℝ)).fun_div ((hZ.const_mul 5).add_const 14) hK)
  have := ((dspo_hd_Lp (n := n) ht0).add (hV.mul (dspo_hd_Ld (n := n) ht0))).add hPhi
  unfold dspoG dspoPhi
  refine this.congr_deriv ?_
  rw [dspo_Vcl_eq (by linarith)]
  unfold dspof
  have : dspoLz t ≠ 0 := hz0.ne'
  field_simp
  ring

/-- The common part of the two curve slopes: with `p' ≤ -a`, `d' ≤ b`, `0 < d ≤ 18/5`,
`R' < -a + (7/800)(18/5) + b/110 + (14/25)(8/35)`. -/
theorem dspo_curve_slope {n t a b : ℝ} (hn1 : 5 / 2 ≤ n) (hn2 : n ≤ 7 / 2) (ht : 2 ≤ t)
    (ht2 : t ≤ 13 / 6) (hp : dspoLpD n t ≤ -a) (hd : dspoLdD n t ≤ b) (hb : 0 ≤ b)
    (hdd : dspoA t (19 * t / 50) n (13 / (5 * (t + 1))) ≤ 18 / 5) :
    dspoLpD n t + deriv dspoVcl t * dspoA t (19 * t / 50) n (13 / (5 * (t + 1))) +
      dspoVcl t * dspoLdD n t + (19 / 50 + 403 / (250 * (t + 1) ^ 2)) * dspof (dspoLz t) ≤
      -a + 7 / 800 * (18 / 5) + 1 / 110 * b + 14 / 25 * (8 / 35) := by
  have ht0 : 0 < t := by linarith
  have hh : 0 ≤ t - 2 := by linarith
  have hh6 : t - 2 ≤ 1 / 6 := by linarith
  have hC1 : 3 / 5 ≤ 19 * t / 50 := by linarith
  have hC2 : 19 * t / 50 ≤ 5 / 6 := by linarith
  have hr1 : 1 / t ≤ 13 / (5 * (t + 1)) := by
    rw [div_le_div_iff₀ ht0 (by positivity)]; linarith
  have hr2 : 13 / (5 * (t + 1)) ≤ 7 / 8 := by
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]; linarith
  obtain ⟨hA1, -, -⟩ := dspo_A_bds ht ht2 hC1 hC2 hn1 hn2 hr1 hr2
  obtain ⟨hV0, -, -, -⟩ := dspo_V_bds ht ht2 hC1 hC2 hr1 hr2
  rw [dspo_Vcl_eq (by linarith)] at hV0
  have hQ : 0 < 95 * t ^ 2 + 498 * t - 650 := by nlinarith
  have hY : dspoVcl t ≤ 1 / 110 := by
    have h1 : 0 ≤ -7125 * (t - 2) ^ 4 - 140390 * (t - 2) ^ 3 - 283841 * (t - 2) ^ 2 -
        115690 * (t - 2) + 29414 := by dsp_hbox
    rw [← dspo_Y0_id (by linarith)] at h1
    have := nonneg_of_mul_nonneg_left h1 (by positivity)
    linarith
  have hZ : deriv dspoVcl t ≤ 7 / 800 := by
    have h1 : 0 ≤ 77389375 * (t - 2) ^ 8 + 2261864500 * (t - 2) ^ 7 + 27371661650 * (t - 2) ^ 6 +
        153729796040 * (t - 2) ^ 5 + 405804725187 * (t - 2) ^ 4 + 503827505900 * (t - 2) ^ 3 +
        286854745744 * (t - 2) ^ 2 + 60769341560 * (t - 2) + 689585532 := by positivity
    rw [← dspo_Z0_id (by linarith)] at h1
    have := nonneg_of_mul_nonneg_left h1 (by positivity)
    linarith
  obtain ⟨hz1, hz2⟩ := dspo_Lz_bds ht ht2
  have hf1 := dspof_lt' hz1
  have hf0 : 0 ≤ dspof (dspoLz t) := le_trans (by norm_num) (dspof_ge (by linarith) hz2)
  have hzd0 : 0 ≤ 19 / 50 + 403 / (250 * (t + 1) ^ 2) := by positivity
  have hzd : 19 / 50 + 403 / (250 * (t + 1) ^ 2) ≤ 14 / 25 := by
    have : 403 / (250 * (t + 1) ^ 2) ≤ 403 / (250 * 9) := by
      apply div_le_div_of_nonneg_left (by norm_num) (by norm_num)
      nlinarith
    linarith
  have e1 : deriv dspoVcl t * dspoA t (19 * t / 50) n (13 / (5 * (t + 1))) ≤
      7 / 800 * dspoA t (19 * t / 50) n (13 / (5 * (t + 1))) :=
    mul_le_mul_of_nonneg_right hZ (by linarith)
  have e2 : dspoVcl t * dspoLdD n t ≤ dspoVcl t * b := mul_le_mul_of_nonneg_left hd hV0
  have e3 : dspoVcl t * b ≤ 1 / 110 * b := mul_le_mul_of_nonneg_right hY hb
  have e4 : (19 / 50 + 403 / (250 * (t + 1) ^ 2)) * dspof (dspoLz t) ≤ 14 / 25 * (8 / 35) :=
    mul_le_mul hzd hf1.le hf0 (by norm_num)
  linarith

/-- **The two lower-shape curves are negative**: the curve decreases (its slope is negative on
`[2, 13/6]`) and is negative at `x = 2`. -/
theorem dspo_low_curve {n x : ℝ} (hn : n = 25 / 8 ∨ n = 7 / 2) (hx : 2 ≤ x) (hx2 : x ≤ 13 / 6) :
    dspoG x (19 * x / 50) n (13 / (5 * (x + 1))) < 0 := by
  have hn1 : 5 / 2 ≤ n := by rcases hn with h | h <;> norm_num [h]
  have hn2 : n ≤ 7 / 2 := by rcases hn with h | h <;> norm_num [h]
  -- the slope is negative on `[2, 13/6]`
  have hneg : ∀ t, 2 ≤ t → t ≤ 13 / 6 →
      dspoLpD n t + deriv dspoVcl t * dspoA t (19 * t / 50) n (13 / (5 * (t + 1))) +
        dspoVcl t * dspoLdD n t + (19 / 50 + 403 / (250 * (t + 1) ^ 2)) * dspof (dspoLz t) ≤ 0 := by
    intro t ht ht2
    have ht0 : 0 < t := by linarith
    have hh : 0 ≤ t - 2 := by linarith
    have hh6 : t - 2 ≤ 1 / 6 := by linarith
    rcases hn with rfl | rfl
    · have hp : dspoLpD (25 / 8) t ≤ -(41 / 200) := by
        have h1 : 0 ≤ 558600 * (t - 2) ^ 7 + 10651040 * (t - 2) ^ 6 + 86143320 * (t - 2) ^ 5 +
            342670492 * (t - 2) ^ 4 + 691815823 * (t - 2) ^ 3 + 709620600 * (t - 2) ^ 2 +
            292950023 * (t - 2) + 4785838 := by positivity
        rw [← dspo_O0_id ht0] at h1
        have := nonneg_of_mul_nonneg_left h1 (by positivity)
        linarith
      have hd : dspoLdD (25 / 8) t ≤ 19 / 4 := by
        have h1 : 0 ≤ -3427600 * (t - 2) ^ 6 - 53594215 * (t - 2) ^ 5 - 341187225 * (t - 2) ^ 4 -
            1128855722 * (t - 2) ^ 3 - 1824003552 * (t - 2) ^ 2 - 990072519 * (t - 2) + 257335889 := by
          dsp_hbox
        rw [← dspo_N0_id ht0] at h1
        have := nonneg_of_mul_nonneg_left h1 (by positivity)
        linarith
      have hdd : dspoA t (19 * t / 50) (25 / 8) (13 / (5 * (t + 1))) ≤ 18 / 5 := by
        have h1 : 0 ≤ -1713800 * (t - 2) ^ 6 - 37292690 * (t - 2) ^ 5 - 285159828 * (t - 2) ^ 4 -
            983843464 * (t - 2) ^ 3 - 1551465687 * (t - 2) ^ 2 - 809079076 * (t - 2) + 212579377 := by
          dsp_hbox
        rw [← dspo_M0_id ht0] at h1
        have := nonneg_of_mul_nonneg_left h1 (by positivity)
        linarith
      have := dspo_curve_slope hn1 hn2 ht ht2 hp hd (by norm_num) hdd
      linarith
    · have hp : dspoLpD (7 / 2) t ≤ -(23 / 100) := by
        have h1 : 0 ≤ 2234400 * (t - 2) ^ 7 + 42467535 * (t - 2) ^ 6 + 342114030 * (t - 2) ^ 5 +
            1358603668 * (t - 2) ^ 4 + 2757913492 * (t - 2) ^ 3 + 2900959275 * (t - 2) ^ 2 +
            1291446542 * (t - 2) + 43690402 := by positivity
        rw [← dspo_O1_id ht0] at h1
        have := nonneg_of_mul_nonneg_left h1 (by positivity)
        linarith
      have hd : dspoLdD (7 / 2) t ≤ 26 / 5 := by
        have h1 : 0 ≤ -6855200 * (t - 2) ^ 6 - 106804805 * (t - 2) ^ 5 - 676620075 * (t - 2) ^ 4 -
            2218057669 * (t - 2) ^ 3 - 3503959029 * (t - 2) ^ 2 - 1720404138 * (t - 2) + 695230228 := by
          dsp_hbox
        rw [← dspo_N1_id ht0] at h1
        have := nonneg_of_mul_nonneg_left h1 (by positivity)
        linarith
      have hdd : dspoA t (19 * t / 50) (7 / 2) (13 / (5 * (t + 1))) ≤ 18 / 5 := by
        have h1 : 0 ≤ -3427600 * (t - 2) ^ 6 - 73545505 * (t - 2) ^ 5 - 555438081 * (t - 2) ^ 4 -
            1887824303 * (t - 2) ^ 3 - 2904167349 * (t - 2) ^ 2 - 1395804152 * (t - 2) + 506917454 := by
          dsp_hbox
        rw [← dspo_M1_id ht0] at h1
        have := nonneg_of_mul_nonneg_left h1 (by positivity)
        linarith
      have := dspo_curve_slope hn1 hn2 ht ht2 hp hd (by norm_num) hdd
      linarith
  have hmono : dspoG x (19 * x / 50) n (13 / (5 * (x + 1))) ≤
      dspoG 2 (19 * 2 / 50) n (13 / (5 * (2 + 1))) := by
    have := ss_le_of_deriv (f := fun s => -dspoG s (19 * s / 50) n (13 / (5 * (s + 1))))
      (f' := fun t => -(dspoLpD n t + deriv dspoVcl t * dspoA t (19 * t / 50) n (13 / (5 * (t + 1))) +
        dspoVcl t * dspoLdD n t + (19 / 50 + 403 / (250 * (t + 1) ^ 2)) * dspof (dspoLz t))) hx
      (fun t ht => (dspo_hd_curve ht.1).neg)
      (fun t ht => by linarith [hneg t ht.1.le (ht.2.le.trans hx2)])
    linarith
  -- the rational values at `x = 2`
  have h2 : dspoG 2 (19 * 2 / 50) n (13 / (5 * (2 + 1))) < 0 := by
    rcases hn with rfl | rfl <;>
    · unfold dspoG dspoP dspoA dspoV dspoPhi dspoc dspoPc0 dspoPc1 dspoPc2 dspoPc3 dspoPc4 dspoAc0
        dspoAc1 dspoAc2 dspoAc3 dspoAc4 dspoα0 dspoα1 dspoα2 dspoα3 dspoα4 dspoβ0 dspoβ1 dspoβ2
        dspoγ0 dspoγ1 dspoγ2 dspoγ3 dspoγ4 dspoδ0 dspoδ1 dspoδ2
      norm_num
  linarith

/-- **The lower-shape tests**: for every slope
`3/5 ≤ C ≤ 19x/50` and `n ∈ {25/8, 7/2}`, `R_n(x, a_*, C) < 0`. -/
theorem dspo_low {n x C : ℝ} (hn : n = 25 / 8 ∨ n = 7 / 2) (hx : 2 ≤ x) (hx2 : x ≤ 13 / 6)
    (hC : 3 / 5 ≤ C) (hC' : C ≤ 19 * x / 50) : dspoG x C n (13 / (5 * (x + 1))) < 0 := by
  have hn1 : 5 / 2 ≤ n := by rcases hn with h | h <;> norm_num [h]
  have hn2 : n ≤ 7 / 2 := by rcases hn with h | h <;> norm_num [h]
  exact (dspo_low_mono hx hx2 hC hC' (by linarith) hn1 hn2).trans_lt (dspo_low_curve hn hx hx2)

end Curve

end SmoothedOctagon
