module

public import SmoothedOctagon.Exclusion.Mixed.ShortHand.Heavy.S4HandW1b

/-!
# W1, part c: the shape derivative `Φ_a < 3/500`

On the containing rectangle `2 ≤ x ≤ 13/6`, `1 ≤ a ≤ 22/19`, `x ≤ b ≤ 20x/19`,
`3/4 ≤ u ≤ 19/25`:

* the bounds `9 ≤ K ≤ 21/2`, `1 ≤ D ≤ 3`, `3 ≤ B ≤ 7/2`, `x - a ≥ 16/19`, `E ≥ 1/2`
  (`hl46_w1_box`, `hl46_w1_E_ge`);
* `Φ_a` is affine in `u` with slope `-(R₀)_{au}/7`, and `(R₀)_{au} < 0`, written as
  `-b/a² - 2aS³(K - 2D)/K³ - 4S³(BK - aD)/K³ - 4(BK - aD)(K - 2D)/K³` (`hl46_w1_Pa_u`,
  `hl46_w1_Rau_neg`);
* `(R₀)_{ab} < 0`, by `1/4 - 32/343 - 1920/8379 < 0` (`hl46_w1_Pab_nonneg`);
* hence `Φ_a ≤ Φ_a(x, a, 20x/19, 19/25) = N/(3325a²(19a + 20x)²K³)` (`hl46_w1_Pa_face`,
  `hl46_w1_Pa_N`), and with `N ≤ V(a)`, `V(11/10) < 0`, `V(22/19) < 65000000`:
  `Φ_a < 3/500` (`hl46_w1_Pa_le`).

For W5 the same source at `x = 13/6` gives
`Φ_a < 0` (`hl46_w1_Pa_end_neg`), from `V(a) ≤ V(22/19) < 64431000`, `W(a) ≤ -172000000`
(`hl46_w1_W_neg`) and
`Q(c, 1/6) ≥ 1100000000 + 1770000000/6`, so that
`N(13/6, a) = V + W/6 - Q/36 < 64431000 - 28666666 - 38750000 < 0`.

## Main API

`hl46_w1_box`, `hl46_w1_E_ge`, `hl46W1Rau`, `hl46_w1_Pa_u`, `hl46_w1_Rau_neg`,
`hl46_w1_Pab_nonneg`, `hl46_w1_Pa_be_mono`, `hl46_w1_Pa_face`, `hl46_w1_Pa_N`, `hl46_w1_N_le`,
`hl46_w1_Pa_le`, `hl46_w1_Pa_end_neg`.
-/

@[expose] public section

namespace SmoothedOctagon

open Real

/-- The bounds `9 ≤ K ≤ 21/2`, `1 ≤ D ≤ 3`, `3 ≤ B ≤ 7/2`, `x - a ≥ 16/19` on the containing
rectangle. -/
theorem hl46_w1_box {x be al : ℝ} (hx : 2 ≤ x) (hx' : x ≤ 13 / 6) (ha : 1 ≤ al) (ha' : al ≤ 22 / 19)
    (hb : x ≤ be) (hb' : be ≤ 20 * x / 19) :
    9 ≤ x * (x + 2) + al ^ 2 ∧ x * (x + 2) + al ^ 2 ≤ 21 / 2 ∧ 1 ≤ hsDg x be al ∧
      hsDg x be al ≤ 3 ∧ 3 ≤ al + be ∧ al + be ≤ 7 / 2 ∧ 16 / 19 ≤ x - al := by
  have hxa : 0 ≤ x - al := by linarith
  refine ⟨by nlinarith, by nlinarith, ?_, ?_, by linarith, by linarith, by linarith⟩
  · have h1 : 2 * be * (x - al) ≤ 2 * (20 * x / 19) * (x - al) :=
      mul_le_mul_of_nonneg_right (by linarith) hxa
    have h2 : 0 ≤ (al - 1) * (al + 1 + 40 * x / 19) := mul_nonneg (by linarith) (by linarith)
    have h3 : 0 ≤ (x - 2) * (13 / 6 - x) := mul_nonneg (by linarith) (by linarith)
    unfold hsDg
    nlinarith
  · have h1 : 2 * x * (x - al) ≤ 2 * be * (x - al) := mul_le_mul_of_nonneg_right (by linarith) hxa
    have h2 : 0 ≤ (x - 2) * (4 * x - 2 * al - 2) := mul_nonneg (by linarith) (by linarith)
    have h3 : 0 ≤ (22 / 19 - al) * (al + 22 / 19 + 4) := mul_nonneg (by linarith) (by linarith)
    unfold hsDg
    nlinarith

/-- `E ≥ 1/2` for `u ≥ 3/4` (the minimum is `485/864`). -/
theorem hl46_w1_E_ge {x u : ℝ} (hx : 2 ≤ x) (hx' : x ≤ 13 / 6) (hu : 3 / 4 ≤ u) :
    1 / 2 ≤ hh46S4P x u := by
  have h3 : 0 ≤ (1 + x) ^ 3 := by positivity
  have h1 : (1 + x) ^ 3 * (-1 / 4) ≤ (1 + x) ^ 3 * (u - 1) :=
    mul_le_mul_of_nonneg_left (by linarith) h3
  have h2 : 0 ≤ (x - 2) * (13 / 6 - x) := mul_nonneg (by linarith) (by linarith)
  have h4 : 0 ≤ (x - 2) * (13 / 6 - x) * x := mul_nonneg h2 (by linarith)
  unfold hh46S4P
  nlinarith

/-- `(R₀)_{au}`, in the form `-b/a² + C_a(1 - 2z) - 2Cz_a - 2z_a(1 - 2z)`. -/
noncomputable def hl46W1Rau (x be al : ℝ) : ℝ :=
  -be / al ^ 2 - 2 * al * (1 + x) ^ 3 * (x * (x + 2) + al ^ 2 - 2 * hsDg x be al) /
      (x * (x + 2) + al ^ 2) ^ 3 -
    4 * (1 + x) ^ 3 * ((al + be) * (x * (x + 2) + al ^ 2) - al * hsDg x be al) /
      (x * (x + 2) + al ^ 2) ^ 3 -
    4 * ((al + be) * (x * (x + 2) + al ^ 2) - al * hsDg x be al) *
      (x * (x + 2) + al ^ 2 - 2 * hsDg x be al) / (x * (x + 2) + al ^ 2) ^ 3

/-- `Φ_a` is affine in `u` with slope `-(R₀)_{au}/7`. -/
theorem hl46_w1_Pa_u (x be al u v : ℝ) (hx : 0 < x) (hal : 0 < al) (hbe : 0 < be) :
    hl46W1Pa x be al u - hl46W1Pa x be al v = -(u - v) * hl46W1Rau x be al / 7 := by
  have hK : 0 < x * (x + 2) + al ^ 2 := by positivity
  have hB : 0 < al + be := by positivity
  unfold hl46W1Pa hl46W1Wa hl46W1Ra hl46W1La hl46W1Rau hh46S4P
  field_simp
  ring

/-- `(R₀)_{au} < 0`. -/
theorem hl46_w1_Rau_neg {x be al : ℝ} (hx : 2 ≤ x) (hx' : x ≤ 13 / 6) (ha : 1 ≤ al)
    (ha' : al ≤ 22 / 19) (hb : x ≤ be) (hb' : be ≤ 20 * x / 19) : hl46W1Rau x be al < 0 := by
  obtain ⟨hK1, hK2, hD1, hD2, hB1, hB2, hη⟩ := hl46_w1_box hx hx' ha ha' hb hb'
  have hKD : 0 ≤ x * (x + 2) + al ^ 2 - 2 * hsDg x be al := by linarith
  have hBK : 0 ≤ (al + be) * (x * (x + 2) + al ^ 2) - al * hsDg x be al := by nlinarith
  have hS : 0 ≤ (1 + x) ^ 3 := by positivity
  have hK3 : 0 < (x * (x + 2) + al ^ 2) ^ 3 := by positivity
  have t1 : -be / al ^ 2 < 0 := div_neg_of_neg_of_pos (by linarith) (by positivity)
  have t2 : 0 ≤ 2 * al * (1 + x) ^ 3 * (x * (x + 2) + al ^ 2 - 2 * hsDg x be al) /
      (x * (x + 2) + al ^ 2) ^ 3 :=
    div_nonneg (mul_nonneg (by positivity) hKD) hK3.le
  have t3 : 0 ≤ 4 * (1 + x) ^ 3 * ((al + be) * (x * (x + 2) + al ^ 2) - al * hsDg x be al) /
      (x * (x + 2) + al ^ 2) ^ 3 :=
    div_nonneg (mul_nonneg (by positivity) hBK) hK3.le
  have t4 : 0 ≤ 4 * ((al + be) * (x * (x + 2) + al ^ 2) - al * hsDg x be al) *
      (x * (x + 2) + al ^ 2 - 2 * hsDg x be al) / (x * (x + 2) + al ^ 2) ^ 3 :=
    div_nonneg (mul_nonneg (mul_nonneg (by norm_num) hBK) hKD) hK3.le
  unfold hl46W1Rau
  linarith

/-- `(R₀)_{ab} < 0`: `1/4 - 32/343 - 1920/8379 < 0`. -/
theorem hl46_w1_Pab_nonneg {x be al u : ℝ} (hx : 2 ≤ x) (hx' : x ≤ 13 / 6) (ha : 1 ≤ al)
    (ha' : al ≤ 22 / 19) (hb : x ≤ be) (hb' : be ≤ 20 * x / 19) (hu : 3 / 4 ≤ u) :
    0 ≤ hl46W1Pab x be al u := by
  obtain ⟨hK1, hK2, hD1, hD2, hB1, hB2, hη⟩ := hl46_w1_box hx hx' ha ha' hb hb'
  have hE := hl46_w1_E_ge hx hx' hu
  have hF : 0 ≤ hh46S4P x u + u * (x * (x + 2) + al ^ 2 - 2 * hsDg x be al) := by
    have : 0 ≤ u * (x * (x + 2) + al ^ 2 - 2 * hsDg x be al) :=
      mul_nonneg (by linarith) (by linarith)
    linarith
  have hK0 : 0 < x * (x + 2) + al ^ 2 := by linarith
  have t1 : (1 - u) / al ^ 2 ≤ 1 / 4 := by
    rw [div_le_iff₀ (by positivity)]
    nlinarith
  have t2 : 32 / 343 ≤ 2 * be / (al + be) ^ 3 := by
    rw [le_div_iff₀ (by positivity)]
    have : (al + be) ^ 3 ≤ (7 / 2) ^ 3 := pow_le_pow_left₀ (by linarith) hB2 3
    nlinarith
  have t3 : 0 ≤ 4 * (hh46S4P x u + u * (x * (x + 2) + al ^ 2 - 2 * hsDg x be al)) /
      (x * (x + 2) + al ^ 2) ^ 2 := by positivity
  have t4 : 1920 / 8379 ≤ 8 * u * (x - al) * (al + 2 * be) / (x * (x + 2) + al ^ 2) ^ 2 := by
    rw [le_div_iff₀ (by positivity)]
    have k : (x * (x + 2) + al ^ 2) ^ 2 ≤ (21 / 2) ^ 2 := pow_le_pow_left₀ hK0.le hK2 2
    have n1 : 3 / 4 * (16 / 19) ≤ u * (x - al) := mul_le_mul hu hη (by norm_num) (by linarith)
    have n2 : 3 / 4 * (16 / 19) * 5 ≤ u * (x - al) * (al + 2 * be) :=
      mul_le_mul n1 (by linarith) (by norm_num) (by positivity)
    nlinarith
  have t5 : 0 ≤ 16 * al * (x - al) * (hh46S4P x u + u * (x * (x + 2) + al ^ 2 - 2 * hsDg x be al)) /
      (x * (x + 2) + al ^ 2) ^ 3 :=
    div_nonneg (mul_nonneg (mul_nonneg (by positivity) (by linarith)) hF) (by positivity)
  unfold hl46W1Pab
  linarith

/-- `Φ_a` increases in `b` on `[x, 20x/19]`. -/
theorem hl46_w1_Pa_be_mono {x al u b₁ b₂ : ℝ} (hx : 2 ≤ x) (hx' : x ≤ 13 / 6) (ha : 1 ≤ al)
    (ha' : al ≤ 22 / 19) (hu : 3 / 4 ≤ u) (h1 : x ≤ b₁) (h12 : b₁ ≤ b₂)
    (h2 : b₂ ≤ 20 * x / 19) : hl46W1Pa x b₁ al u ≤ hl46W1Pa x b₂ al u :=
  hl46_mono_of (a := x) (b := 20 * x / 19)
    (fun z hz => hl46_w1_hasDerivAt_Pa_be (by linarith) (by linarith) (by linarith [hz.1]))
    (fun _ hz => hl46_w1_Pab_nonneg hx hx' ha ha' hz.1 hz.2 hu) h1 h12 h2

/-- The beta and norm reductions: `Φ_a ≤ Φ_a(x, a, 20x/19, 19/25)`. -/
theorem hl46_w1_Pa_face {x be al u : ℝ} (hx : 2 ≤ x) (hx' : x ≤ 13 / 6) (ha : 1 ≤ al)
    (ha' : al ≤ 22 / 19) (hb : x ≤ be) (hb' : be ≤ 20 * x / 19) (hu' : u ≤ 19 / 25) :
    hl46W1Pa x be al u ≤ hl46W1Pa x (20 * x / 19) al (19 / 25) := by
  have e := hl46_w1_Pa_u x be al u (19 / 25) (by linarith) (by linarith) (by linarith)
  have r := hl46_w1_Rau_neg hx hx' ha ha' hb hb'
  have h1 : hl46W1Pa x be al u ≤ hl46W1Pa x be al (19 / 25) := by
    rw [← sub_nonpos, e]
    apply div_nonpos_of_nonpos_of_nonneg _ (by norm_num)
    rw [neg_mul, neg_nonpos]
    exact mul_nonneg_of_nonpos_of_nonpos (by linarith) r.le
  exact h1.trans (hl46_w1_Pa_be_mono hx hx' ha ha' (u := 19 / 25) (by norm_num) hb hb' le_rfl)

/-- `Φ_a(x, a, 20x/19, 19/25) = N/(3325a²(19a + 20x)²K³)`, `N = V + Wh - h²Q`. -/
theorem hl46_w1_Pa_N {x al : ℝ} (hx : 0 < x) (hal : 0 < al) :
    hl46W1Pa x (20 * x / 19) al (19 / 25) =
      (hl46W1V al + hl46W1W al * (x - 2) - (x - 2) ^ 2 * hl46W1Q (al - 1) (x - 2)) /
        (3325 * al ^ 2 * (19 * al + 20 * x) ^ 2 * (x * (x + 2) + al ^ 2) ^ 3) := by
  have hK : 0 < x * (x + 2) + al ^ 2 := by positivity
  rw [hl46_w1_Pa_src hx hal (by positivity), ← hl46_w1_N_taylor]
  field_simp
  ring

/-- `N ≤ V(a)`: the concavity in `x` with `W < 0`. -/
theorem hl46_w1_N_le {x al : ℝ} (hx : 2 ≤ x) (ha : 1 ≤ al)
    (ha' : al ≤ 22 / 19) :
    hl46W1V al + hl46W1W al * (x - 2) - (x - 2) ^ 2 * hl46W1Q (al - 1) (x - 2) ≤ hl46W1V al := by
  have hW := hl46_w1_W_neg ha ha'
  have hQ := hl46_w1_Q_ge (c := al - 1) (h := x - 2) (by linarith) (by linarith) (by linarith)
  have t1 : hl46W1W al * (x - 2) ≤ 0 := mul_nonpos_of_nonpos_of_nonneg (by linarith) (by linarith)
  have t2 : 0 ≤ (x - 2) ^ 2 * hl46W1Q (al - 1) (x - 2) :=
    mul_nonneg (by positivity) (by nlinarith)
  linarith

/-- `Φ_a < 3/500` on the containing rectangle. -/
theorem hl46_w1_Pa_le {x be al u : ℝ} (hx : 2 ≤ x) (hx' : x ≤ 13 / 6) (ha : 1 ≤ al)
    (ha' : al ≤ 22 / 19) (hb : x ≤ be) (hb' : be ≤ 20 * x / 19) (hu' : u ≤ 19 / 25) :
    hl46W1Pa x be al u ≤ 3 / 500 := by
  refine (hl46_w1_Pa_face hx hx' ha ha' hb hb' hu').trans ?_
  rw [hl46_w1_Pa_N (by linarith) (by linarith)]
  have hN := hl46_w1_N_le hx ha ha'
  have hden : 0 < 3325 * al ^ 2 * (19 * al + 20 * x) ^ 2 * (x * (x + 2) + al ^ 2) ^ 3 := by
    have : 0 < al := by linarith
    positivity
  rw [div_le_iff₀ hden]
  rcases le_or_gt al (11 / 10) with h | h
  · have := hl46_w1_V_neg ha h
    nlinarith
  · have hV := hl46_w1_V_le ha ha'
    have k1 : (11 / 10) ^ 2 ≤ al ^ 2 := pow_le_pow_left₀ (by norm_num) h.le 2
    have k2 : (19 * (11 / 10) + 40) ^ 2 ≤ (19 * al + 20 * x) ^ 2 :=
      pow_le_pow_left₀ (by norm_num) (by linarith) 2
    have k3 : (8 + (11 / 10) ^ 2) ^ 3 ≤ (x * (x + 2) + al ^ 2) ^ 3 :=
      pow_le_pow_left₀ (by norm_num) (by nlinarith) 3
    have k : 3325 * (11 / 10) ^ 2 * (19 * (11 / 10) + 40) ^ 2 * (8 + (11 / 10) ^ 2) ^ 3 ≤
        3325 * al ^ 2 * (19 * al + 20 * x) ^ 2 * (x * (x + 2) + al ^ 2) ^ 3 := by
      gcongr
    norm_num at k
    linarith

/-- W5's sign: `Φ_a < 0` at `x = 13/6`, `b = 20x/19`. -/
theorem hl46_w1_Pa_end_neg {al u : ℝ} (ha : 1 ≤ al) (ha' : al ≤ 22 / 19) (hu' : u ≤ 19 / 25) :
    hl46W1Pa (13 / 6) (20 * (13 / 6) / 19) al u < 0 := by
  refine lt_of_le_of_lt (hl46_w1_Pa_face (by norm_num) le_rfl ha ha' (by norm_num) le_rfl hu') ?_
  rw [hl46_w1_Pa_N (by norm_num) (by linarith)]
  have hden : 0 < 3325 * al ^ 2 * (19 * al + 20 * (13 / 6)) ^ 2 *
      ((13 / 6) * ((13 / 6) + 2) + al ^ 2) ^ 3 := by
    have : 0 < al := by linarith
    positivity
  apply div_neg_of_neg_of_pos _ hden
  have hV := hl46_w1_V_le ha ha'
  have hW := hl46_w1_W_neg ha ha'
  have hQ := hl46_w1_Q_ge (c := al - 1) (h := 13 / 6 - 2) (by linarith) (by linarith) (by norm_num)
  norm_num at hQ ⊢
  linarith

end SmoothedOctagon
