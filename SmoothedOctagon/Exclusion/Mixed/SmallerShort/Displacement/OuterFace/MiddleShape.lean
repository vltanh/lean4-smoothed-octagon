module

public import SmoothedOctagon.Exclusion.Mixed.SmallerShort.Displacement.OuterFace.LowerShape

/-!
# Smaller-short window, displacement, outer face: the middle shape `α = 5/4`

The outer face sign `dsp_outer_face_proof`, sixth part. At `r = 4/5`, `n = 5/2`: since `A_n > 1`, the norm
is raised to `19/25` (`V ≤ 1/100`) and the logarithm constant to `16/9`; the resulting bound
`M(x, C)` has `153125S(C + 4x + 5)²(C + 4x + 19)²M_C = Q(h, C)` with positive coefficients, so
`M(x, C) ≤ M(x, 5/6) = N(h)/(11025000S(24x + 35)(24x + 119)) < 0`.

## Main API

* `dspo_mid`: `G(x, C, 5/2, 4/5) < 0` for `3/5 ≤ C ≤ 5/6`.
-/

@[expose] public section

namespace SmoothedOctagon

open Real Set

/-- The polynomial `Q(h, C) = 153125S(C + 4x + 5)²(C + 4x + 19)²M_C`, `h = x - 2`, with positive
coefficients. -/
noncomputable def dspoQ (h C : ℝ) : ℝ :=
  h ^ 8 * (1245184) +
    h ^ 7 * (1556480 * C + 31551488) +
    h ^ 6 * (778240 * C ^ 2 + 32952320 * C + 321821696) +
    h ^ 5 * (194560 * C ^ 3 + 13232640 * C ^ 2 + 273387520 * C + 1701993984) +
    h ^ 4 * (24320 * C ^ 4 + 2497280 * C ^ 3 + 84751488 * C ^ 2 + 1135620352 * C + 5008527744) +
    h ^ 3 * (1216 * C ^ 5 + 210800 * C ^ 4 + 11327936 * C ^ 3 + 257136288 * C ^ 2 + 2499943040 * C +
      8222843104) +
    h ^ 2 * (5472 * C ^ 5 + 574204 * C ^ 4 + 22046784 * C ^ 3 + 379369096 * C ^ 2 + 2869398104 * C +
      7418853236) +
    h * (6156 * C ^ 5 + 544540 * C ^ 4 + 17454536 * C ^ 3 + 249238183 * C ^ 2 + 1639188350 * C +
      3861571483) +
    (2052 * C ^ 5 + 150114 * C ^ 4 + 3600024 * C ^ 3 + 48714393 * C ^ 2 + 403215522 * C + 942621879)

/-- The middle-face bound `M(x, C)`: norm `19/25`, logarithm constant `16/9`. -/
noncomputable def dspoM (x C : ℝ) : ℝ :=
  dspoP x C (5 / 2) (4 / 5) + 1 / 100 * dspoA x C (5 / 2) (4 / 5) + dspoPhi x C (4 / 5) + 153 / 180000

section Mid

variable {x C : ℝ}

theorem dspo_Q_id (hx : 0 < x) (hC : 0 ≤ C) :
    (dspoPC x C (5 / 2) (4 / 5) + 1 / 100 * dspoAC x C (5 / 2) (4 / 5) +
      (1 - 4 / 5) * dspof (1 + C + (x - C) * (4 / 5))) *
      (153125 * (x + 1) * (C + 4 * x + 5) ^ 2 * (C + 4 * x + 19) ^ 2) = dspoQ (x - 2) C := by
  have hZ : 1 + C + (x - C) * (4 / 5) = (C + 4 * x + 5) / 5 := by ring
  rw [hZ]
  unfold dspoPC dspoAC dspof dspoQ
  have : x + 1 ≠ 0 := by linarith
  have : C + 4 * x + 5 ≠ 0 := by linarith
  have : 5 * ((C + 4 * x + 5) / 5) + 14 = C + 4 * x + 19 := by ring
  rw [this]
  have : C + 4 * x + 19 ≠ 0 := by linarith
  field_simp
  ring

theorem dspo_M56_id (hx : 0 < x) :
    dspoM x (5 / 6) * (11025000 * (x + 1) * (24 * x + 35) * (24 * x + 119)) =
      403439616 * (x - 2) ^ 7 + 6862897152 * (x - 2) ^ 6 + 42994741248 * (x - 2) ^ 5 +
        126236766720 * (x - 2) ^ 4 + 185797060288 * (x - 2) ^ 3 + 137194124304 * (x - 2) ^ 2 +
        28358242681 * (x - 2) - 12914813589 := by
  unfold dspoM dspoP dspoA dspoPhi dspoPc0 dspoPc1 dspoPc2 dspoPc3 dspoPc4 dspoAc0 dspoAc1 dspoAc2
    dspoAc3 dspoAc4 dspoα0 dspoα1 dspoα2 dspoα3 dspoα4 dspoβ0 dspoβ1 dspoβ2 dspoγ0 dspoγ1 dspoγ2
    dspoγ3 dspoγ4 dspoδ0 dspoδ1 dspoδ2
  have hZ : 1 + 5 / 6 + (x - 5 / 6) * (4 / 5) = (24 * x + 35) / 30 := by ring
  rw [hZ]
  have : 5 * ((24 * x + 35) / 30) + 14 = (24 * x + 119) / 6 := by ring
  rw [this]
  have : x + 1 ≠ 0 := by linarith
  have : 24 * x + 35 ≠ 0 := by linarith
  have : 24 * x + 119 ≠ 0 := by linarith
  field_simp
  ring

/-- **The middle shape**: `R_{5/2}(x, 5/4, C) < 0`. -/
theorem dspo_mid (hx : 2 ≤ x) (hx2 : x ≤ 13 / 6) (hC : 3 / 5 ≤ C) (hC' : C ≤ 5 / 6) :
    dspoG x C (5 / 2) (4 / 5) < 0 := by
  have hx0 : 0 < x := by linarith
  have hr1 : 1 / x ≤ 4 / 5 := by rw [div_le_div_iff₀ hx0 (by norm_num)]; linarith
  -- raise the norm (`A > 1`, `V ≤ 1/100`)
  obtain ⟨hA1, -, -⟩ := dspo_A_bds (n := 5 / 2) hx hx2 hC hC' (by norm_num) (by norm_num) hr1 (by norm_num)
  obtain ⟨-, hV, -, -⟩ := dspo_V_bds hx hx2 hC hC' hr1 (by norm_num)
  have h1 : dspoG x C (5 / 2) (4 / 5) < dspoM x C := by
    unfold dspoG dspoM
    have := mul_le_mul_of_nonneg_right hV (by linarith : (0 : ℝ) ≤ dspoA x C (5 / 2) (4 / 5))
    linarith
  -- `M` increases in `C`
  have h2 : dspoM x C ≤ dspoM x (5 / 6) := by
    apply ss_le_of_deriv hC'
    · intro t ht
      obtain ⟨hH, hZ, -⟩ := dspo_HZ hx hx2 (hC.trans ht.1) ht.2 hr1 (by norm_num)
      have := (((dspo_hdC_P (x := x) (n := 5 / 2) (r := 4 / 5) (t := t)).add
        ((dspo_hdC_A (x := x) (n := 5 / 2) (r := 4 / 5) (t := t)).const_mul (1 / 100))).add
        (dspo_hdC_Phi (x := x) (r := 4 / 5) (t := t) (by linarith))).add_const (153 / 180000)
      unfold dspoM
      exact this
    · intro t ht
      have ht0 : 0 ≤ t := by linarith [ht.1]
      have hQ := dspo_Q_id (C := t) hx0 ht0
      have hh : 0 ≤ x - 2 := by linarith
      have hQ0 : 0 ≤ dspoQ (x - 2) t := by unfold dspoQ; positivity
      rw [← hQ] at hQ0
      exact nonneg_of_mul_nonneg_left hQ0 (by positivity)
  -- `M(x, 5/6) < 0`
  have h3 : dspoM x (5 / 6) < 0 := by
    have hh : 0 ≤ x - 2 := by linarith
    have hh6 : x - 2 ≤ 1 / 6 := by linarith
    have hN : 403439616 * (x - 2) ^ 7 + 6862897152 * (x - 2) ^ 6 + 42994741248 * (x - 2) ^ 5 +
        126236766720 * (x - 2) ^ 4 + 185797060288 * (x - 2) ^ 3 + 137194124304 * (x - 2) ^ 2 +
        28358242681 * (x - 2) - 12914813589 < 0 := by
      linarith [(dsp_mono1 hh hh6 2).2, (dsp_mono1 hh hh6 3).2, (dsp_mono1 hh hh6 4).2,
        (dsp_mono1 hh hh6 5).2, (dsp_mono1 hh hh6 6).2, (dsp_mono1 hh hh6 7).2]
    rw [← dspo_M56_id hx0] at hN
    exact neg_of_mul_neg_left hN (by positivity)
  linarith

end Mid

end SmoothedOctagon
