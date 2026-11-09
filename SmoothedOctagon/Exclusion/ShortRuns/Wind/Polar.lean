module

public import SmoothedOctagon.Exclusion.ShortRuns.Wind.Angle
public import SmoothedOctagon.Foundations.LowCostWinding
public import SmoothedOctagon.Foundations.CyclicExtension
public import SmoothedOctagon.Period.Elliptic

/-!
# The polar angle of a competitive frame turns by exactly `π/3`

For a frame `g ∈ SL₂(ℝ)` write `z(g) = (g₀₀ + g₁₁)/2 + i (g₁₀ - g₀₁)/2` (`Reduction.clr_zc`,
`|z| ≥ 1`). For every vector `u ≠ 0`, `Re(g u · conj(z(g) u)) = (|g u|² + |u|²)/2 > 0`
(`wind_re_frame`), so `g u / (z(g) u)` lies in the right half plane: an angle of `z(g)` plus a
principal argument is a canonical angle from `u` to `g u`.

For a competitive normal period (`cost ≤ A_oct < π`) the polar angle `Φ` of `z(g(t))` has a
continuous choice on `[0, T]` with `Φ(T) - Φ(0) = π/3` exactly (`wind_polar`). The low-cost winding
theorem (`lowCost_reflectedFirstRow_angle`, on the cyclic extension of the frame) fixes the
continuous angle of the reflected first row `r = (g₀₀, -g₀₁)` at `π/3`; since
`Re(r · conj z) = (g₀₀² + g₀₁² + 1)/2 > 0`, the angles of `r` and `z` stay within `π/2` of each
other, and both `r` and `z` equal `e^{iπ/3}` at `t = T`.

## Main API

* `wind_isAng_exp_log`, `wind_IsAng.inv`.
* `wind_re_frame`: `Re(g u · conj(z(g) u)) = (|g u|² + det g |u|²)/2`.
* `wind_polar`: the continuous polar angle of a competitive frame.
-/

@[expose] public section

namespace SmoothedOctagon

open Complex Set PlaneCurve SmoothedPolygons
open scoped Matrix

theorem wind_isAng_exp_log (L : ℂ) : wind_IsAng L.im (exp L) := by
  refine ⟨Real.exp L.re, Real.exp_pos _, ?_⟩
  conv_lhs => rw [← re_add_im L]
  rw [exp_add, ofReal_exp]

theorem wind_IsAng.inv {a : ℝ} {z : ℂ} (h : wind_IsAng a z) : wind_IsAng (-a) z⁻¹ := by
  obtain ⟨r, hr, rfl⟩ := h
  refine ⟨r⁻¹, inv_pos.2 hr, ?_⟩
  rw [mul_inv, ← exp_neg]; push_cast; ring_nf

/-- `Re(g u · conj(z(g) u)) = (|g u|² + det g · |u|²)/2`. -/
theorem wind_re_frame (g : Matrix (Fin 2) (Fin 2) ℝ) (u : Fin 2 → ℝ) :
    (sc_toC (g *ᵥ u) * (starRingEnd ℂ) (Reduction.clr_zc g * sc_toC u)).re =
      ((g 0 0 * u 0 + g 0 1 * u 1) ^ 2 + (g 1 0 * u 0 + g 1 1 * u 1) ^ 2 +
        g.det * (u 0 ^ 2 + u 1 ^ 2)) / 2 := by
  rw [Matrix.det_fin_two]
  simp only [Complex.mul_re, Complex.mul_im, Complex.conj_re, Complex.conj_im,
    Reduction.clr_zc_re, Reduction.clr_zc_im, sc_toC_re, sc_toC_im, Matrix.mulVec, dotProduct,
    Fin.sum_univ_two]
  ring

/-- For `det g = 1` and `u ≠ 0`, `g u / (z(g) u)` lies in the right half plane. -/
theorem wind_frame_slit {g : Matrix (Fin 2) (Fin 2) ℝ} (hg : g.det = 1) {u : Fin 2 → ℝ}
    (hu : u ≠ 0) : sc_toC (g *ᵥ u) / (Reduction.clr_zc g * sc_toC u) ∈ slitPlane := by
  have hz : Reduction.clr_zc g ≠ 0 := by
    intro h; have := Reduction.clr_zc_normSq_ge hg; rw [h, map_zero] at this; linarith
  refine wind_div_mem_slit (mul_ne_zero hz (wind_toC_ne hu)) ?_
  rw [mem_slitPlane_iff]; left
  rw [wind_re_frame, hg]
  have : 0 < u 0 ^ 2 + u 1 ^ 2 := by
    by_contra h
    push Not at h
    apply hu; ext i; fin_cases i <;> simp <;> nlinarith [sq_nonneg (u 0), sq_nonneg (u 1)]
  positivity

/-- **The polar angle of a competitive frame** turns by exactly `π/3` over the period. -/
theorem wind_polar (P : NormalPeriod) (hc : P.IsCompetitive) :
    ∃ Φ : ℝ → ℝ, ContinuousOn Φ (Icc 0 P.T) ∧ Φ P.T - Φ 0 = Real.pi / 3 ∧
      ∀ t ∈ Icc 0 P.T, wind_IsAng (Φ t) (Reduction.clr_zc (P.g t)) := by
  have hadm : IsReinhardtAdmissible P.T P.u P.g P.X := ⟨P.extremal.1, P.g_zero, P.g_T, P.X_T⟩
  obtain ⟨G, Y, hagree, hGC, hYC, -, hdet, hstar, hD, hG0, -, -, -, -, hcosteq⟩ :=
    exists_cyclic_extension_of_isReinhardtAdmissible hadm
  have hT := P.T_pos
  have hGT : G P.T = R := (hagree P.T ⟨hT.le, le_rfl⟩).1.trans P.g_T
  have hlow : reinhardtCost P.T Y < Real.pi := by
    rw [hcosteq]
    have h1 : reinhardtCost P.T P.X ≤ octagonCost := hc
    exact lt_of_le_of_lt h1 Reduction.octagonCost_lt_pi
  have hα := lowCost_reflectedFirstRow_angle hT hGC hdet hYC hD hstar hG0 hGT hlow
  -- the polar curve
  set zc : ℝ → Fin 2 → ℝ := fun t ↦ ![(G t 0 0 + G t 1 1) / 2, (G t 1 0 - G t 0 1) / 2]
    with hzc_def
  have hzC : ContDiff ℝ 1 zc := by
    apply contDiff_pi.mpr
    intro i; fin_cases i
    · simpa [hzc_def] using ((hGC 0 0).add (hGC 1 1)).div_const 2
    · simpa [hzc_def] using ((hGC 1 0).sub (hGC 0 1)).div_const 2
  have hztoC : ∀ t, sc_toC (zc t) = Reduction.clr_zc (G t) := fun t ↦ by
    apply Complex.ext <;> simp [hzc_def, Reduction.clr_zc]
  have hzne : ∀ t, zc t ≠ 0 := by
    intro t h
    have h1 := Reduction.clr_zc_normSq_ge (hdet t)
    rw [← hztoC, h] at h1
    simp [sc_toC] at h1
    linarith
  have hz0 : sc_toC (zc 0) = 1 := by
    rw [hztoC, hG0]; apply Complex.ext <;> simp [Reduction.clr_zc]
  have hzexp : ∀ t, Reduction.clr_zc (G t) = exp (sc_log zc t) := fun t ↦ by
    rw [← hztoC, toComplex_eq_exp_log_of_contDiff hzC hzne t, hz0, one_mul]
  have hΦang : ∀ t, wind_IsAng (sc_angle zc t) (Reduction.clr_zc (G t)) := fun t ↦ by
    rw [hzexp]; exact wind_isAng_exp_log _
  have hΦc : Continuous (sc_angle zc) :=
    continuous_iff_continuousAt.2 fun t ↦ (hasDerivAt_angle_of_contDiff hzC hzne t).continuousAt
  -- the reflected first row
  set rr := reflectedFirstRow G with hrr
  have hrC := reflectedFirstRow_contDiff hGC
  have hrne := reflectedFirstRow_ne_zero hdet
  have hr0 : sc_toC (rr 0) = 1 := by
    simp [hrr, reflectedFirstRow, hG0, sc_toC]
  have hrang : ∀ t, wind_IsAng (sc_angle rr t) (sc_toC (rr t)) := fun t ↦ by
    rw [toComplex_eq_exp_log_of_contDiff hrC hrne t, hr0, one_mul]; exact wind_isAng_exp_log _
  have hαc : Continuous (sc_angle rr) :=
    continuous_iff_continuousAt.2 fun t ↦ (hasDerivAt_angle_of_contDiff hrC hrne t).continuousAt
  -- their quotient stays in the right half plane
  set w : ℝ → ℂ := fun t ↦ sc_toC (rr t) / Reduction.clr_zc (G t) with hw
  have hzne' : ∀ t, Reduction.clr_zc (G t) ≠ 0 := fun t ↦ by
    rw [← hztoC]; exact wind_toC_ne (hzne t)
  have hwslit : ∀ t, w t ∈ slitPlane := by
    intro t
    refine wind_div_mem_slit (hzne' t) ?_
    rw [mem_slitPlane_iff]; left
    have hd := hdet t
    rw [Matrix.det_fin_two] at hd
    simp only [Complex.mul_re, Complex.conj_re, Complex.conj_im, Reduction.clr_zc_re,
      Reduction.clr_zc_im, sc_toC_re, sc_toC_im, hrr, reflectedFirstRow, Matrix.cons_val_zero,
      Matrix.cons_val_one]
    nlinarith [sq_nonneg (G t 0 0), sq_nonneg (G t 0 1)]
  have hwc : Continuous w :=
    (sc_continuous_toC.comp hrC.continuous).div
      (Reduction.clr_continuous_zc.comp (continuous_pi fun i ↦ continuous_pi fun j ↦
        (hGC i j).continuous)) hzne'
  set f : ℝ → ℝ := fun t ↦ sc_angle rr t - sc_angle zc t - arg (w t) with hf
  have hf0 : f 0 = 0 := by
    simp only [hf, sc_angle_zero, hw, hr0, hG0]
    rw [show Reduction.clr_zc 1 = 1 by apply Complex.ext <;> simp [Reduction.clr_zc]]
    simp
  have hfc : ContinuousOn f (Icc 0 P.T) :=
    ((hαc.sub hΦc).continuousOn).sub
      (wind_continuousOn_arg hwc.continuousOn fun t _ ↦ hwslit t)
  have hfT : f P.T = f 0 := by
    refine wind_eq_of_int hT.le hfc fun t _ ↦ ?_
    have h1 : wind_IsAng (sc_angle rr t + -sc_angle zc t) (w t) :=
      (hrang t).mul (hΦang t).inv
    obtain ⟨n, hn⟩ := (wind_isAng_arg (slitPlane_ne_zero (hwslit t))).unique h1
    exact ⟨n, by rw [hf0]; simp only [hf]; linarith⟩
  have hwT : w P.T = 1 := by
    have hR : Reduction.clr_zc R ≠ 0 := by rw [← hGT]; exact hzne' _
    simp only [hw, hGT]
    rw [div_eq_one_iff_eq hR]
    apply Complex.ext <;> simp [hrr, reflectedFirstRow, hGT, sc_toC, Reduction.clr_zc, R]
  refine ⟨sc_angle zc, hΦc.continuousOn, ?_, fun t ht ↦ ?_⟩
  · rw [hf0] at hfT
    simp only [hf, hwT, arg_one, sub_zero] at hfT
    rw [sc_angle_zero, sub_zero]
    linarith
  · rw [← (hagree t ht).1]; exact hΦang t

end SmoothedOctagon
