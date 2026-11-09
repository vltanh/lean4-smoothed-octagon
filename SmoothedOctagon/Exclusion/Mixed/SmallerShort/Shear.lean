module

public import SmoothedOctagon.Exclusion.Mixed.SmallerShort.Interface
public import SmoothedOctagon.Exclusion.Mixed.SmallerShort.Shear.Residual
public import SmoothedOctagon.Exclusion.Mixed.SmallerShort.Shear.Sign

/-!
# The root forces a negative physical shear

The actual outer root and the opposite-turn envelope give a nonnegative residual.
Its positive norm slope and the natural ceiling raise the norm to `19/25`.
The exact duration tangent and its two shape signs then force `q > (15/16)q_c`.
The physical shear satisfies `√3hR + 7A/2 < 0`, hence `h < 0` and `-hR > 2A`.
-/

@[expose] public section

namespace SmoothedOctagon

open Set Real

/-- The residual's factored norm slope is positive while the duration stays below the
incoming switching factor. -/
private theorem shr_factored_slope_pos {S ε r g p q : ℝ} (hS : 0 < S) (hε1 : ε ≤ 1)
    (hr : 0 < r) (hgr : g * r < 1) (hp : 0 ≤ p) (hpr : p ≤ r) (hq : 0 ≤ q) (hq2 : q < 1 / 2) :
    0 < S * (1 - ε * q) * (1 - p * g) + 1 / r - q * g * (2 - p * g) := by
  have hεq := mul_le_mul_of_nonneg_right hε1 hq
  have hfirst : 0 < 1 - ε * q := by linarith
  rcases le_or_gt g 0 with hg | hg
  · have hpg := mul_nonpos_of_nonneg_of_nonpos hp hg
    have hpg1 : 0 < 1 - p * g := by linarith
    have hleft : 0 < S * (1 - ε * q) * (1 - p * g) := by positivity
    have hright : q * g * (2 - p * g) ≤ 0 :=
      mul_nonpos_of_nonpos_of_nonneg (mul_nonpos_of_nonneg_of_nonpos hq hg) (by linarith)
    have : 0 < 1 / r := by positivity
    linarith
  · have hpg0 : 0 ≤ p * g := mul_nonneg hp hg.le
    have hpg : p * g < 1 := lt_of_le_of_lt (mul_le_mul_of_nonneg_right hpr hg.le) (by nlinarith)
    have hleft : 0 < S * (1 - ε * q) * (1 - p * g) := by positivity
    have hright : (1 - 2 * q) / r ≤ 1 / r - q * g * (2 - p * g) := by
      have hg_bound : g ≤ 1 / r := by rw [le_div_iff₀ hr]; exact hgr.le
      have h1 : g * (2 - p * g) ≤ 2 / r := by
        have h2 := mul_le_mul_of_nonneg_left (show 2 - p * g ≤ 2 by linarith) hg.le
        calc _ ≤ 2 * g := by nlinarith only [h2]
             _ ≤ 2 * (1 / r) := mul_le_mul_of_nonneg_left hg_bound (by norm_num)
             _ = 2 / r := by ring
      have := mul_le_mul_of_nonneg_left h1 hq
      have he : (1 - 2 * q) / r = 1 / r - q * (2 / r) := by ring
      rw [he]
      nlinarith only [this]
    have : 0 < (1 - 2 * q) / r := div_pos (by linarith) hr
    linarith

/-- The small-shape geometry gives `gr_A < 1`, directly from
`β(2x - α) > 1 + 2x`. -/
theorem shr_small_shape_factor {x be al : ℝ} (hx : 2 ≤ x) (hal : 1 ≤ al) (hal2 : al < 3 / 2)
    (hxb : x ≤ be) : ssDg x be al / al ^ 2 * ssRA al be < 1 := by
  have hx0 : 0 < x := by linarith
  have hal0 : 0 < al := by linarith
  have hbe0 : 0 < be := by linarith
  have hshape : 1 + 2 * x < be * (2 * x - al) := by
    have h1 := mul_le_mul_of_nonneg_right hxb (show 0 ≤ 2 * x - al by linarith)
    have h2 := mul_lt_mul_of_pos_left hal2 hx0
    have h3 := mul_nonneg (show 0 ≤ x - 2 by linarith) (show 0 ≤ 2 * x + 1 / 2 by linarith)
    nlinarith
  have e : ssDg x be al / al ^ 2 * ssRA al be =
      1 - (be * (2 * x - al) - 1 - 2 * x) / (al * (al + be)) := by
    unfold ssDg ssRA
    field_simp
    ring
  rw [e]
  have : 0 < (be * (2 * x - al) - 1 - 2 * x) / (al * (al + be)) :=
    div_pos (by linarith) (by positivity)
  linarith

/-- **Monotonicity in the bridge norm**: the affine norm slope factors into a positive
term and a remainder bounded below by `(1 - 2q)/r_A`. -/
theorem shr_norm_mono {x be al p q u u' : ℝ} (hx : 1 < x) (hal : 1 ≤ al)
    (hbe : 0 < be) (hgr : ssDg x be al / al ^ 2 * ssRA al be < 1)
    (hq : 0 ≤ q) (hq2 : q < 1 / 2) (hp : 0 < p) (hpr : p ≤ ssRA al be)
    (huu : u ≤ u') : ssPhi x be al u p 0 q ≤ ssPhi x be al u' p 0 q := by
  have hal0 : 0 < al := by linarith
  have hr : 0 < ssRA al be := by unfold ssRA; positivity
  have hε1 : 1 - 1 / al ^ 2 ≤ 1 := by
    have : 0 ≤ 1 / al ^ 2 := by positivity
    linarith
  have hslope := shr_factored_slope_pos (show 0 < 1 + x by linarith) hε1 hr hgr hp.le hpr hq hq2
  have e : ssPhi x be al u' p 0 q - ssPhi x be al u p 0 q =
      (u' - u) * ((1 + x) * (1 - (1 - 1 / al ^ 2) * q) *
        (1 - p * (ssDg x be al / al ^ 2)) + 1 / ssRA al be -
          q * (ssDg x be al / al ^ 2) * (2 - p * (ssDg x be al / al ^ 2))) := by
    unfold ssPhi ssCp ssLp ssA1 ssA2 ssA3 ssE0 ssRA
    field_simp
    ring
  have := mul_nonneg (sub_nonneg.mpr huu) hslope.le
  linarith


namespace SmallerShortData
variable (H : SmallerShortData)

/-- The small-shape root forces the lower scale bound, negative physical shear,
and the continuation bound `-hR > 2A`. -/
theorem shear_neg (hS : H.SmallShape) :
    15 / 16 * ssQc H.x H.al < H.q ∧
      √3 * ssShear H.x H.be H.al H.rho * ssRr H.x + 7 / 2 * ssAn H.x H.be H.al < 0 ∧
      ssShear H.x H.be H.al H.rho < 0 ∧
      2 * ssAn H.x H.be H.al < -ssShear H.x H.be H.al H.rho * ssRr H.x := by
  obtain ⟨hx, hx2, hδ0, hδ1, hal1, hal2⟩ := hS
  have hx1 : 1 < H.x := H.one_lt_x
  have hx0 : 0 < H.x := by linarith
  have hbe : H.be = H.x * (1 + H.δ) := by unfold SmallerShortData.δ; field_simp; ring
  have hal : 1 ≤ H.al := H.one_le_al
  have hax : H.al ≤ H.x := H.al_lt_x.le
  have hxb : H.x ≤ H.be := H.x_le_be
  have hρ := H.rho_pos
  have hρ1 : H.rho < 1 := by linarith [H.rho_le]
  -- the scale lower bound `q > q_b`
  have hq : 15 / 16 * ssQc H.x H.al < ssQ H.al H.rho := by
    by_contra hcon
    have hqb := not_lt.mp hcon
    have hq0 : 0 < ssQ H.al H.rho := by
      unfold ssQ ssLam
      have : 0 < 1 + H.rho * (H.al ^ 2 - 1) := by
        have := mul_nonneg hρ.le (show 0 ≤ H.al ^ 2 - 1 by linarith [one_le_pow₀ (n := 2) hal])
        linarith
      positivity
    have hq7 : ssQ H.al H.rho < 1 / 7 := H.q_lt_seventh
    have hτ2 := H.two_lt_τ
    have hτT := H.τ_lt
    have hτ0 : 0 < H.τ := by linarith
    -- the root and the opposite-turn envelope (`m = 0`)
    have ht0 : H.rho * (1 + H.x) ≤ H.t := by
      have h := H.rho_lt_rt
      rw [div_mul_eq_mul_div, one_mul, lt_div_iff₀ (by linarith)] at h
      linarith
    have henv := ss_env_weighted (be := H.be) (u := H.u) (τ := H.τ) (m := 0) hx1 hal hρ ht0
      H.t_le_r H.v_le (fun s hs => by
        rw [add_zero]
        exact ss_B_factor_pos hx1 hal hax hxb hρ hs.1 hτ0.le hτT.le)
    rw [H.root_zero] at henv
    simp only [zero_mul, add_zero] at henv
    obtain ⟨-, -, hR, -⟩ := ss_env_scale (be := H.be) (u := H.u) (τ := H.τ) hx0 hal hq0
      (by linarith : ssQ H.al H.rho < 1)
    rw [(ss_scale_coords (x := H.x) (be := H.be) hal hρ).1] at hR
    rw [hR] at henv
    have hphi := ss_phi_eq (x := H.x) (be := H.be) (al := H.al) (u := H.u) (m := 0)
      (show 0 < H.τ * ssQ H.al H.rho by positivity) hq0
    rw [show H.τ * ssQ H.al H.rho / ssQ H.al H.rho = H.τ by field_simp] at hphi
    have h0 : 0 ≤ ssPhi H.x H.be H.al H.u (H.τ * ssQ H.al H.rho) 0 (ssQ H.al H.rho) := by
      rw [← hphi]
      exact henv
    -- raise the norm to the natural constant ceiling
    have hu : H.u ≤ 19/25 :=
      H.u_le_V.trans (ss_V_lt_small_shape_ceiling hx hx2).le
    have hgr := shr_small_shape_factor hx hal (by linarith : H.al < 3/2) hxb
    have h1 := shr_norm_mono hx1 hal (by linarith : 0 < H.be) hgr hq0.le
      (by linarith : ssQ H.al H.rho < 1/2) (by positivity) hτT.le hu
    have hbmax : H.be ≤ 20*H.x/19 := by
      rw [hbe]
      nlinarith only [hx0,hδ1]
    have h2τ : 2 * ssQ H.al H.rho ≤ H.τ * ssQ H.al H.rho :=
      mul_le_mul_of_nonneg_right hτ2.le hq0.le
    have h2 := shr_residual_neg hx hx2 hal (by linarith) hxb hbmax
      hq0.le hqb (by positivity) h2τ hτT.le
    linarith
  -- the shear sign
  have hsh : √3 * ssShear H.x H.be H.al H.rho * ssRr H.x + 7 / 2 * ssAn H.x H.be H.al < 0 := by
    rw [hbe]
    exact shr_shear_sign hx hx2 hδ0 hδ1 (by linarith) (by linarith) hρ hρ1 hq
  -- `h < 0` and `-hR > 2A`
  have hA : 0 ≤ ssAn H.x H.be H.al := by
    unfold ssAn
    have h1 : 0 ≤ H.be * H.x - H.al := by
      have := mul_le_mul_of_nonneg_right hxb hx0.le
      have := mul_le_mul_of_nonneg_left hx1.le hx0.le
      linarith
    have h2 : 0 ≤ H.al * H.x - H.be := by linarith [H.be_le_al_x]
    have hbe0 : 0 < H.be := by linarith
    have hal0 : 0 < H.al := by linarith
    positivity
  have hRr : 0 < ssRr H.x := by
    unfold ssRr
    exact div_pos (by linarith) (by linarith)
  have hs3 : 0 < √3 := by positivity
  have hs3' : √3 < 7 / 4 := by rw [Real.sqrt_lt' (by norm_num)]; norm_num
  refine ⟨hq, hsh, ?_, ?_⟩
  · by_contra hcon
    have h1 := mul_nonneg (mul_nonneg hs3.le (not_lt.mp hcon)) hRr.le
    linarith
  · by_contra hcon
    have hX := not_lt.mp hcon
    have h1 := mul_le_mul_of_nonneg_left hX hs3.le
    have h2 := mul_le_mul_of_nonneg_right hs3'.le
      (show 0 ≤ 2 * ssAn H.x H.be H.al by positivity)
    have e : √3 * (-ssShear H.x H.be H.al H.rho * ssRr H.x) =
        -(√3 * ssShear H.x H.be H.al H.rho * ssRr H.x) := by ring
    linarith

end SmallerShortData

/-- **The shear bound for the actual window**: on the small-shape domain,
`q > (15/16)q_c`, `√3hR + 7A/2 < 0`, `h < 0`, `-hR > 2A`, with the physical shear
`h = ssShear (C/a) (B/a) (A/a) ρ`. -/
theorem M2Short.shear_neg (D : M2Short) (h1 : 2 ≤ D.C / D.a) (h2 : D.C / D.a ≤ 13 / 6)
    (h3 : 0 ≤ D.B / D.C - 1) (h4 : D.B / D.C - 1 ≤ 1 / 19)
    (h5 : 1 + 13 / 5 * (D.B / D.C - 1) ≤ D.A / D.a) (h6 : D.A / D.a ≤ 1 + 3 * (D.B / D.C - 1)) :
    15 / 16 * ssQc (D.C / D.a) (D.A / D.a) < ssQ (D.A / D.a) (D.a ^ 2 / (D.a ^ 2 + 4)) ∧
      √3 * ssShear (D.C / D.a) (D.B / D.a) (D.A / D.a) (D.a ^ 2 / (D.a ^ 2 + 4)) *
          ssRr (D.C / D.a) + 7 / 2 * ssAn (D.C / D.a) (D.B / D.a) (D.A / D.a) < 0 ∧
      ssShear (D.C / D.a) (D.B / D.a) (D.A / D.a) (D.a ^ 2 / (D.a ^ 2 + 4)) < 0 ∧
      2 * ssAn (D.C / D.a) (D.B / D.a) (D.A / D.a) <
        -ssShear (D.C / D.a) (D.B / D.a) (D.A / D.a) (D.a ^ 2 / (D.a ^ 2 + 4)) *
          ssRr (D.C / D.a) := by
  have h := D.toData.shear_neg (D.ss_smallShape h1 h2 h3 h4 h5 h6)
  rw [SmallerShortData.q, D.toData_x, D.toData_be, D.toData_al, D.toData_rho] at h
  exact h

end SmoothedOctagon
