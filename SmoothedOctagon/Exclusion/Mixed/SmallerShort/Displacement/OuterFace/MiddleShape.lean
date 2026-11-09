module

public import SmoothedOctagon.Exclusion.Mixed.ShortHand.Heavy.S3HandOLowC

/-!
# Gate S3, the outer face by hand: the middle shape `α = 5/4`

Proof of the leaf `hs3_outer_face`, sixth part. At `r = 4/5`, `n = 5/2`: since `A_n > 1`, the norm
is raised to `19/25` (`V ≤ 1/100`) and the logarithm constant to `16/9`; the resulting bound
`M(x, C)` has `153125S(C + 4x + 5)²(C + 4x + 19)²M_C = Q(h, C)` with positive coefficients, so
`M(x, C) ≤ M(x, 5/6) = N(h)/(11025000S(24x + 35)(24x + 119)) < 0`.

## Main API

* `hl3o_mid`: `G(x, C, 5/2, 4/5) < 0` for `3/5 ≤ C ≤ 5/6`.
-/

@[expose] public section

namespace SmoothedOctagon

open Real Set

/-- The polynomial `Q(h, C) = 153125S(C + 4x + 5)²(C + 4x + 19)²M_C`, `h = x - 2`, with positive
coefficients. -/
noncomputable def hl3oQ (h C : ℝ) : ℝ :=
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
noncomputable def hl3oM (x C : ℝ) : ℝ :=
  hl3oP x C (5 / 2) (4 / 5) + 1 / 100 * hl3oA x C (5 / 2) (4 / 5) + hl3oPhi x C (4 / 5) + 153 / 180000

section Mid

variable {x C : ℝ}

theorem hl3o_Q_id (hx : 0 < x) (hC : 0 ≤ C) :
    (hl3oPC x C (5 / 2) (4 / 5) + 1 / 100 * hl3oAC x C (5 / 2) (4 / 5) +
      (1 - 4 / 5) * hl3of (1 + C + (x - C) * (4 / 5))) *
      (153125 * (x + 1) * (C + 4 * x + 5) ^ 2 * (C + 4 * x + 19) ^ 2) = hl3oQ (x - 2) C := by
  have hZ : 1 + C + (x - C) * (4 / 5) = (C + 4 * x + 5) / 5 := by ring
  rw [hZ]
  unfold hl3oPC hl3oAC hl3of hl3oQ
  have : x + 1 ≠ 0 := by linarith
  have : C + 4 * x + 5 ≠ 0 := by linarith
  have : 5 * ((C + 4 * x + 5) / 5) + 14 = C + 4 * x + 19 := by ring
  rw [this]
  have : C + 4 * x + 19 ≠ 0 := by linarith
  field_simp
  ring

theorem hl3o_M56_id (hx : 0 < x) :
    hl3oM x (5 / 6) * (11025000 * (x + 1) * (24 * x + 35) * (24 * x + 119)) =
      403439616 * (x - 2) ^ 7 + 6862897152 * (x - 2) ^ 6 + 42994741248 * (x - 2) ^ 5 +
        126236766720 * (x - 2) ^ 4 + 185797060288 * (x - 2) ^ 3 + 137194124304 * (x - 2) ^ 2 +
        28358242681 * (x - 2) - 12914813589 := by
  unfold hl3oM hl3oP hl3oA hl3oPhi hl3oPc0 hl3oPc1 hl3oPc2 hl3oPc3 hl3oPc4 hl3oAc0 hl3oAc1 hl3oAc2
    hl3oAc3 hl3oAc4 hl3oα0 hl3oα1 hl3oα2 hl3oα3 hl3oα4 hl3oβ0 hl3oβ1 hl3oβ2 hl3oγ0 hl3oγ1 hl3oγ2
    hl3oγ3 hl3oγ4 hl3oδ0 hl3oδ1 hl3oδ2
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
theorem hl3o_mid (hx : 2 ≤ x) (hx2 : x ≤ 13 / 6) (hC : 3 / 5 ≤ C) (hC' : C ≤ 5 / 6) :
    hl3oG x C (5 / 2) (4 / 5) < 0 := by
  have hx0 : 0 < x := by linarith
  have hr1 : 1 / x ≤ 4 / 5 := by rw [div_le_div_iff₀ hx0 (by norm_num)]; linarith
  -- raise the norm (`A > 1`, `V ≤ 1/100`)
  obtain ⟨hA1, -, -⟩ := hl3o_A_bds (n := 5 / 2) hx hx2 hC hC' (by norm_num) (by norm_num) hr1 (by norm_num)
  obtain ⟨-, hV, -, -⟩ := hl3o_V_bds hx hx2 hC hC' hr1 (by norm_num)
  have h1 : hl3oG x C (5 / 2) (4 / 5) < hl3oM x C := by
    unfold hl3oG hl3oM
    have := mul_le_mul_of_nonneg_right hV (by linarith : (0 : ℝ) ≤ hl3oA x C (5 / 2) (4 / 5))
    linarith
  -- `M` increases in `C`
  have h2 : hl3oM x C ≤ hl3oM x (5 / 6) := by
    apply ss_le_of_deriv hC'
    · intro t ht
      obtain ⟨hH, hZ, -⟩ := hl3o_HZ hx hx2 (hC.trans ht.1) ht.2 hr1 (by norm_num)
      have := (((hl3o_hdC_P (x := x) (n := 5 / 2) (r := 4 / 5) (t := t)).add
        ((hl3o_hdC_A (x := x) (n := 5 / 2) (r := 4 / 5) (t := t)).const_mul (1 / 100))).add
        (hl3o_hdC_Phi (x := x) (r := 4 / 5) (t := t) (by linarith))).add_const (153 / 180000)
      unfold hl3oM
      exact this
    · intro t ht
      have ht0 : 0 ≤ t := by linarith [ht.1]
      have hQ := hl3o_Q_id (C := t) hx0 ht0
      have hh : 0 ≤ x - 2 := by linarith
      have hQ0 : 0 ≤ hl3oQ (x - 2) t := by unfold hl3oQ; positivity
      rw [← hQ] at hQ0
      exact nonneg_of_mul_nonneg_left hQ0 (by positivity)
  -- `M(x, 5/6) < 0`
  have h3 : hl3oM x (5 / 6) < 0 := by
    have hh : 0 ≤ x - 2 := by linarith
    have hh6 : x - 2 ≤ 1 / 6 := by linarith
    have hN : 403439616 * (x - 2) ^ 7 + 6862897152 * (x - 2) ^ 6 + 42994741248 * (x - 2) ^ 5 +
        126236766720 * (x - 2) ^ 4 + 185797060288 * (x - 2) ^ 3 + 137194124304 * (x - 2) ^ 2 +
        28358242681 * (x - 2) - 12914813589 < 0 := by
      linarith [(hl3_mono1 hh hh6 2).2, (hl3_mono1 hh hh6 3).2, (hl3_mono1 hh hh6 4).2,
        (hl3_mono1 hh hh6 5).2, (hl3_mono1 hh hh6 6).2, (hl3_mono1 hh hh6 7).2]
    rw [← hl3o_M56_id hx0] at hN
    exact neg_of_mul_neg_left hN (by positivity)
  linarith

end Mid

end SmoothedOctagon
