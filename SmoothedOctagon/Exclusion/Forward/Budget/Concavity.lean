module

public import SmoothedOctagon.Exclusion.Forward.Log
public import Mathlib.Analysis.Convex.Deriv

/-!
# Joint concavity of the exterior cost

The curvature remainder increases from a positive diagonal value after pairing the
reciprocal kernel about its zero. A Schur-complement bound then makes the Hessian
negative definite throughout `1 ≤ x ≤ U ≤ 3`.
-/

@[expose] public section

namespace SmoothedOctagon

open Real Set

private noncomputable def ff_curvPrimitive (t : ℝ) : ℝ :=
  -Real.log (1 + t) - 4 / (1 + t) + 3 / (2 * (1 + t) ^ 2)

private theorem ff_curvPrimitive_deriv {t : ℝ} (ht : 0 < 1 + t) :
    HasDerivAt ff_curvPrimitive (t * (2 - t) / (1 + t) ^ 3) t := by
  have hlin : HasDerivAt (fun t : ℝ => 1 + t) 1 t := by
    simpa using (hasDerivAt_id t).const_add 1
  have hd := (((hlin.log ht.ne').neg).sub
    ((hasDerivAt_const t (4 : ℝ)).div hlin ht.ne')).add
      ((hasDerivAt_const t (3 : ℝ)).div ((hlin.pow 2).const_mul 2) (by simp only [Pi.pow_apply]; positivity))
  refine hd.congr_deriv ?_
  norm_num only [Pi.pow_apply, Nat.cast_ofNat, Nat.reduceSub, pow_one]
  field_simp
  ring

/-- Pairing about the zero of the kernel leaves a positive primitive increment. -/
private theorem ff_curvPrimitive_pair : ff_curvPrimitive 1 < ff_curvPrimitive 3 := by
  have hderiv : ∀ t ∈ Icc (0 : ℝ) 1,
      HasDerivAt (fun t => ff_curvPrimitive (2 + t) - ff_curvPrimitive (2 - t))
        (2 * t ^ 2 * (27 - 7 * t ^ 2) / ((3 - t) ^ 3 * (3 + t) ^ 3)) t := by
    intro t ht
    have hl : 0 < 3 - t := by linarith [ht.2]
    have hr : 0 < 3 + t := by linarith [ht.1]
    have h1 := (ff_curvPrimitive_deriv (t := 2 + t) (by linarith)).comp t
      (hasDerivAt_id t |>.const_add 2)
    have h2 := (ff_curvPrimitive_deriv (t := 2 - t) (by linarith)).comp t
      (hasDerivAt_id t |>.const_sub 2)
    have h := h1.sub h2
    refine h.congr_deriv ?_
    rw [show 1 + (2 + t) = 3 + t by ring, show 1 + (2 - t) = 3 - t by ring]
    field_simp
    ring
  have hmono : StrictMonoOn (fun t => ff_curvPrimitive (2 + t) - ff_curvPrimitive (2 - t))
      (Icc 0 1) := by
    apply strictMonoOn_of_deriv_pos (convex_Icc (0 : ℝ) 1)
    · intro t ht
      exact (hderiv t ht).continuousAt.continuousWithinAt
    · intro t ht
      rw [interior_Icc] at ht
      rw [(hderiv t ⟨ht.1.le, ht.2.le⟩).deriv]
      have hpos : 0 < t ^ 2 := sq_pos_of_pos ht.1
      have hnum : 0 < 27 - 7 * t ^ 2 := by nlinarith [ht.1, ht.2]
      have hl : 0 < 3 - t := by linarith [ht.2]
      have hr : 0 < 3 + t := by linarith [ht.1]
      exact div_pos (by positivity) (by positivity)
  have h := hmono (by norm_num) (by norm_num) (by norm_num : (0 : ℝ) < 1)
  norm_num at h
  linarith

private theorem ff_curvPrimitive_mono {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) (hb : b ≤ 2) :
    ff_curvPrimitive a ≤ ff_curvPrimitive b := by
  apply ff_le_of_deriv hab
    (fun t ht => ff_curvPrimitive_deriv (by linarith [ht.1]))
  intro t ht
  have ht0 : 0 ≤ t := ha.trans ht.1
  have ht2 : t ≤ 2 := ht.2.trans hb
  exact div_nonneg (mul_nonneg ht0 (by linarith)) (by positivity)

private theorem ff_curvPrimitive_anti {a b : ℝ} (ha : 2 ≤ a) (hab : a ≤ b) :
    ff_curvPrimitive b ≤ ff_curvPrimitive a := by
  have h := ff_le_of_deriv (f := fun t => -ff_curvPrimitive t) hab
    (fun t ht => (ff_curvPrimitive_deriv (by linarith [ht.1])).neg) (fun t ht => ?_)
  · linarith only [h]
  · have ht2 : 2 ≤ t := ha.trans ht.1
    rw [neg_nonneg]
    exact div_nonpos_of_nonpos_of_nonneg
      (mul_nonpos_of_nonneg_of_nonpos (by linarith) (by linarith)) (by positivity)

/-- The paired integral controls all larger endpoint ratios in the shape triangle. -/
private theorem ff_curvPrimitive_shape {x U : ℝ} (hx : 1 ≤ x) (hxU : x ≤ U) (hU : U ≤ 3) :
    ff_curvPrimitive (1 / x) ≤ ff_curvPrimitive (U / x ^ 2) := by
  have hx0 : 0 < x := by linarith
  have hx2 : 1 ≤ x ^ 2 := by nlinarith only [hx]
  have ha0 : 0 ≤ 1 / x := by positivity
  have ha1 : 1 / x ≤ 1 := by rw [div_le_one hx0]; exact hx
  have hab : 1 / x ≤ U / x ^ 2 := by
    rw [div_le_div_iff₀ hx0 (sq_pos_of_pos hx0)]
    nlinarith only [mul_nonneg (sub_nonneg.mpr hxU) hx0.le]
  have hb3 : U / x ^ 2 ≤ 3 := by
    rw [div_le_iff₀ (sq_pos_of_pos hx0)]
    linarith only [hU, hx2]
  by_cases hb2 : U / x ^ 2 ≤ 2
  · exact ff_curvPrimitive_mono ha0 hab hb2
  · have h1 := ff_curvPrimitive_mono ha0 ha1 (by norm_num : (1 : ℝ) ≤ 2)
    have h2 := ff_curvPrimitive_anti (by linarith : 2 ≤ U / x ^ 2) hb3
    exact h1.trans (ff_curvPrimitive_pair.le.trans h2)

noncomputable def ff_budgetGxx (U x : ℝ) : ℝ :=
  Real.log (x ^ 2 + U) - 2 * Real.log (1 + x) + 2 * (x + 2) / (1 + x) ^ 2 -
    U * (x ^ 2 + 3 * U) / (x ^ 2 + U) ^ 2

private noncomputable def ff_budgetCurv (U x : ℝ) : ℝ :=
  -ff_budgetGxx U x - U ^ 2 / (2 * (x ^ 2 + U) ^ 2)

private theorem ff_log_second_remainder_pos {y : ℝ} (hy : 0 < y) (hy1 : y < 1) :
    0 < -Real.log (1 - y) - y - y ^ 2 / 2 := by
  have hd : ∀ t ∈ Icc (0 : ℝ) y,
      HasDerivAt (fun t : ℝ => -Real.log (1 - t) - t - t ^ 2 / 2) (t ^ 2 / (1 - t)) t := by
    intro t ht
    have hlt : 0 < 1 - t := by linarith [ht.2]
    have hlin : HasDerivAt (fun t : ℝ => 1 - t) (-1) t := by
      simpa using (hasDerivAt_id t).const_sub 1
    have h := (((hlin.log hlt.ne').neg).sub (hasDerivAt_id t)).sub ((hasDerivAt_pow 2 t).div_const 2)
    refine h.congr_deriv ?_
    field_simp
    ring
  have hm : StrictMonoOn (fun t : ℝ => -Real.log (1 - t) - t - t ^ 2 / 2) (Icc 0 y) := by
    apply strictMonoOn_of_deriv_pos (convex_Icc (0 : ℝ) y)
    · intro t ht
      exact (hd t ht).continuousAt.continuousWithinAt
    · intro t ht
      rw [interior_Icc] at ht
      rw [(hd t ⟨ht.1.le, ht.2.le⟩).deriv]
      exact div_pos (sq_pos_of_pos ht.1) (by linarith [ht.2])
  have h := hm ⟨le_refl _, hy.le⟩ ⟨hy.le, le_refl _⟩ hy
  simpa using h

private theorem ff_budgetCurv_diag {x : ℝ} (hx : 0 < x) : 0 < ff_budgetCurv x x := by
  have hS : 0 < 1 + x := by linarith
  have hy : 0 < 1 / (1 + x) := by positivity
  have hy1 : 1 / (1 + x) < 1 := by rw [div_lt_one hS]; linarith
  have h := ff_log_second_remainder_pos hy hy1
  have e : ff_budgetCurv x x =
      -Real.log (1 - 1 / (1 + x)) - 1 / (1 + x) - (1 / (1 + x)) ^ 2 / 2 := by
    unfold ff_budgetCurv ff_budgetGxx
    rw [show x ^ 2 + x = x * (1 + x) by ring, Real.log_mul hx.ne' hS.ne',
      show 1 - 1 / (1 + x) = x / (1 + x) by field_simp; ring,
      Real.log_div hx.ne' hS.ne']
    field_simp
    ring
  rwa [e]

private theorem ff_budgetCurv_increment {U x : ℝ} (hx : 0 < x) (hU : 0 < U) :
    ff_budgetCurv U x - ff_budgetCurv x x =
      ff_curvPrimitive (U / x ^ 2) - ff_curvPrimitive (1 / x) := by
  have hS : 0 < 1 + x := by linarith
  have hD : 0 < x ^ 2 + U := by positivity
  unfold ff_budgetCurv ff_budgetGxx ff_curvPrimitive
  rw [show 1 + U / x ^ 2 = (x ^ 2 + U) / x ^ 2 by field_simp,
    show 1 + 1 / x = (1 + x) / x by field_simp; ring,
    show x ^ 2 + x = x * (1 + x) by ring,
    Real.log_div hD.ne' (pow_ne_zero 2 hx.ne'),
    Real.log_div hS.ne' hx.ne', Real.log_mul hx.ne' hS.ne', Real.log_pow]
  field_simp
  ring

theorem ff_budgetGxx_bound {U x : ℝ} (hx : 1 ≤ x) (hxU : x ≤ U) (hU : U ≤ 3) :
    ff_budgetGxx U x < -(U ^ 2 / (2 * (x ^ 2 + U) ^ 2)) := by
  have hx0 : 0 < x := by linarith
  have hU0 : 0 < U := by linarith
  have hinc := ff_curvPrimitive_shape hx hxU hU
  have hdiag := ff_budgetCurv_diag hx0
  have heq := ff_budgetCurv_increment hx0 hU0
  unfold ff_budgetCurv at *
  linarith only [hinc, hdiag, heq]

/-- The seven-entry exterior cost after concentration of the excess. -/
noncomputable def ff_budgetCost (U x : ℝ) : ℝ := 5 * ff_g2 U 1 1 + 2 * ff_g2 U 1 x

private noncomputable def ff_budgetDu (U x : ℝ) : ℝ :=
  -7 + 6 / (1 + U) + x ^ 2 / (x ^ 2 + U)

private noncomputable def ff_budgetDx (U x : ℝ) : ℝ :=
  6 - 4 * x * Real.log (1 + x) - 2 * (1 + x ^ 2) / (1 + x) +
    2 * x * Real.log (x ^ 2 + U) + 2 * x ^ 3 / (x ^ 2 + U)

private theorem ff_budgetCost_deriv {u x : ℝ → ℝ} {s du dx : ℝ}
    (hu : HasDerivAt u du s) (hx : HasDerivAt x dx s)
    (hu0 : 0 < u s) (hx0 : 0 < x s) :
    HasDerivAt (fun t => ff_budgetCost (u t) (x t))
      (du * ff_budgetDu (u s) (x s) + dx * ff_budgetDx (u s) (x s)) s := by
  have hS : 0 < 1 + x s := by linarith
  have hU : 0 < 1 + u s := by linarith
  have hD : 0 < x s ^ 2 + u s := by positivity
  have h := ((((((hasDerivAt_const s (15 : ℝ)).add (hx.const_mul 6)).sub
    (hu.const_mul 7)).sub_const (10 * Real.log 2)).sub
    ((((hx.pow 2).const_add 1).mul ((hx.const_add 1).log hS.ne')).const_mul 2)).add
    (((hu.const_add 1).log hU.ne').const_mul 6)).add
    ((hx.pow 2).mul (((hx.pow 2).add hu).log hD.ne'))
  convert h using 1
  · ext t
    unfold ff_budgetCost ff_g2
    norm_num
    ring
  · unfold ff_budgetDu ff_budgetDx
    simp only [Pi.pow_apply, Pi.add_apply]
    field_simp
    ring

private theorem ff_budgetDu_deriv {u x : ℝ → ℝ} {s du dx : ℝ}
    (hu : HasDerivAt u du s) (hx : HasDerivAt x dx s)
    (hu0 : 0 < u s) (hx0 : 0 < x s) :
    HasDerivAt (fun t => ff_budgetDu (u t) (x t))
      (du * (-6 / (1 + u s) ^ 2 - x s ^ 2 / (x s ^ 2 + u s) ^ 2) +
       dx * (2 * u s * x s / (x s ^ 2 + u s) ^ 2)) s := by
  have hU : 0 < 1 + u s := by linarith
  have hD : 0 < x s ^ 2 + u s := by positivity
  have h := ((hasDerivAt_const s (-7 : ℝ)).add
    ((hasDerivAt_const s (6 : ℝ)).div (hu.const_add 1) hU.ne')).add
    ((hx.pow 2).div ((hx.pow 2).add hu) hD.ne')
  refine h.congr_deriv ?_
  simp only [Pi.pow_apply, Pi.add_apply]
  field_simp
  ring

private theorem ff_budgetDx_deriv {u x : ℝ → ℝ} {s du dx : ℝ}
    (hu : HasDerivAt u du s) (hx : HasDerivAt x dx s)
    (hu0 : 0 < u s) (hx0 : 0 < x s) :
    HasDerivAt (fun t => ff_budgetDx (u t) (x t))
      (du * (2 * u s * x s / (x s ^ 2 + u s) ^ 2) +
       dx * (2 * ff_budgetGxx (u s) (x s))) s := by
  have hS : 0 < 1 + x s := by linarith
  have hD : 0 < x s ^ 2 + u s := by positivity
  have h := (((((hasDerivAt_const s (6 : ℝ)).sub
    ((hx.const_mul 4).mul ((hx.const_add 1).log hS.ne'))).sub
    ((((hx.pow 2).const_add 1).const_mul 2).div (hx.const_add 1) hS.ne')).add
    ((hx.const_mul 2).mul (((hx.pow 2).add hu).log hD.ne'))).add
    (((hx.pow 3).const_mul 2).div ((hx.pow 2).add hu) hD.ne'))
  refine h.congr_deriv ?_
  unfold ff_budgetGxx
  simp only [Pi.pow_apply, Pi.add_apply]
  field_simp
  ring

/-- The Hessian is negative on every nonzero direction in the shape triangle. -/
private theorem ff_budgetHessian_neg {U x du dx : ℝ}
    (hx : 1 ≤ x) (hxU : x ≤ U) (hU : U ≤ 3) (hne : du ≠ 0 ∨ dx ≠ 0) :
    du * (du * (-6 / (1 + U) ^ 2 - x ^ 2 / (x ^ 2 + U) ^ 2) +
      dx * (2 * U * x / (x ^ 2 + U) ^ 2)) +
    dx * (du * (2 * U * x / (x ^ 2 + U) ^ 2) + dx * (2 * ff_budgetGxx U x)) < 0 := by
  have hx0 : 0 < x := by linarith
  have hU0 : 0 < U := by linarith
  have hA : 0 < 1 + U := by linarith
  have hD : 0 < x ^ 2 + U := by positivity
  set a := 6 / (1 + U) ^ 2 + x ^ 2 / (x ^ 2 + U) ^ 2 with ha
  set b := 2 * U * x / (x ^ 2 + U) ^ 2 with hb
  set c := U ^ 2 / (x ^ 2 + U) ^ 2 with hc
  have ha0 : 0 < a := by rw [ha]; positivity
  have hshape : 0 < 8 * U - (1 + U) ^ 2 := by
    have : 0 ≤ (U - 1) * (5 - U) := mul_nonneg (by linarith) (by linarith)
    nlinarith only [this]
  have hbracket : 0 < 2 / (1 + U) ^ 2 - x ^ 2 / (x ^ 2 + U) ^ 2 := by
    rw [sub_pos, div_lt_div_iff₀ (sq_pos_of_pos hD) (sq_pos_of_pos hA)]
    nlinarith only [sq_nonneg (x ^ 2 - U), mul_pos (sq_pos_of_pos hx0) hshape]
  have hdet : 0 < a * c - b ^ 2 := by
    have e : a * c - b ^ 2 = 3 * U ^ 2 / (x ^ 2 + U) ^ 2 *
        (2 / (1 + U) ^ 2 - x ^ 2 / (x ^ 2 + U) ^ 2) := by
      rw [ha, hb, hc]
      field_simp
      ring
    rw [e]
    exact mul_pos (by positivity) hbracket
  have hq : -(a * du - b * dx) ^ 2 - (a * c - b ^ 2) * dx ^ 2 < 0 := by
    by_cases hd : dx = 0
    · have hu : du ≠ 0 := hne.resolve_right (not_not.mpr hd)
      simpa only [hd, mul_zero, sub_zero, zero_pow (by norm_num : 2 ≠ 0)] using
        neg_neg_of_pos (sq_pos_of_ne_zero (mul_ne_zero ha0.ne' hu))
    · nlinarith only [mul_pos hdet (sq_pos_of_ne_zero hd), sq_nonneg (a * du - b * dx)]
  have hmajor : -a * du ^ 2 + 2 * b * du * dx - c * dx ^ 2 < 0 := by
    apply neg_of_mul_neg_left _ ha0.le
    calc (-a * du ^ 2 + 2 * b * du * dx - c * dx ^ 2) * a =
        -(a * du - b * dx) ^ 2 - (a * c - b ^ 2) * dx ^ 2 := by ring
      _ < 0 := hq
  have hxx : 2 * ff_budgetGxx U x ≤ -c := by
    have := ff_budgetGxx_bound hx hxU hU
    rw [hc]
    have e : U ^ 2 / (2 * (x ^ 2 + U) ^ 2) = (U ^ 2 / (x ^ 2 + U) ^ 2) / 2 := by field_simp
    rw [e] at this
    linarith only [this]
  have hmul := mul_le_mul_of_nonneg_right hxx (sq_nonneg dx)
  rw [ha, hb, hc] at hmajor
  rw [hc] at hmul
  dsimp only [b]
  simp only [neg_div]
  nlinarith only [hmajor, hmul]

private def ff_budgetDomain : Set (ℝ × ℝ) := {p | 1 ≤ p.2 ∧ p.2 ≤ p.1 ∧ p.1 ≤ 3}

private theorem ff_budgetDomain_convex : Convex ℝ ff_budgetDomain := by
  intro p hp q hq a b ha hb hab
  change 1 ≤ a * p.2 + b * q.2 ∧ a * p.2 + b * q.2 ≤ a * p.1 + b * q.1 ∧
    a * p.1 + b * q.1 ≤ 3
  refine ⟨?_, ?_, ?_⟩
  · have := add_le_add (mul_le_mul_of_nonneg_left hp.1 ha)
      (mul_le_mul_of_nonneg_left hq.1 hb)
    nlinarith only [this, hab]
  · exact add_le_add (mul_le_mul_of_nonneg_left hp.2.1 ha)
      (mul_le_mul_of_nonneg_left hq.2.1 hb)
  · have := add_le_add (mul_le_mul_of_nonneg_left hp.2.2 ha)
      (mul_le_mul_of_nonneg_left hq.2.2 hb)
    nlinarith only [this, hab]

/-- Joint strict concavity on `1 ≤ x ≤ U ≤ 3`. -/
theorem ff_budgetCost_strictConcaveOn :
    StrictConcaveOn ℝ {p : ℝ × ℝ | 1 ≤ p.2 ∧ p.2 ≤ p.1 ∧ p.1 ≤ 3}
      (fun p => ff_budgetCost p.1 p.2) := by
  refine ⟨ff_budgetDomain_convex, ?_⟩
  intro p hp q hq hpq a b ha hb hab
  let u : ℝ → ℝ := fun s => p.1 + s * (q.1 - p.1)
  let x : ℝ → ℝ := fun s => p.2 + s * (q.2 - p.2)
  have hseg : ∀ s ∈ Icc (0 : ℝ) 1, (u s, x s) ∈ ff_budgetDomain := by
    intro s hs
    have h := ff_budgetDomain_convex hp hq (by linarith [hs.2] : 0 ≤ 1 - s) hs.1 (by ring)
    have e : (u s, x s) = (1 - s) • p + s • q := by
      ext <;> simp only [u, x, Prod.smul_fst, Prod.smul_snd, Prod.fst_add, Prod.snd_add,
        smul_eq_mul] <;> ring
    rwa [e]
  have hu : ∀ s, HasDerivAt u (q.1 - p.1) s := by
    intro s
    simpa [u] using ((hasDerivAt_id s).mul_const (q.1 - p.1)).const_add p.1
  have hx : ∀ s, HasDerivAt x (q.2 - p.2) s := by
    intro s
    simpa [x] using ((hasDerivAt_id s).mul_const (q.2 - p.2)).const_add p.2
  have hpos : ∀ s ∈ Icc (0 : ℝ) 1, 0 < u s ∧ 0 < x s := by
    intro s hs
    have h := hseg s hs
    exact ⟨by linarith [h.1, h.2.1], by linarith [h.1]⟩
  have hfirst : ∀ s ∈ Icc (0 : ℝ) 1,
      HasDerivAt (fun t => ff_budgetCost (u t) (x t))
        ((q.1 - p.1) * ff_budgetDu (u s) (x s) + (q.2 - p.2) * ff_budgetDx (u s) (x s)) s := by
    intro s hs
    exact ff_budgetCost_deriv (hu s) (hx s) (hpos s hs).1 (hpos s hs).2
  have hsecond : ∀ s ∈ Icc (0 : ℝ) 1,
      HasDerivAt (fun t => (q.1 - p.1) * ff_budgetDu (u t) (x t) +
        (q.2 - p.2) * ff_budgetDx (u t) (x t))
        ((q.1 - p.1) * ((q.1 - p.1) * (-6 / (1 + u s) ^ 2 - x s ^ 2 / (x s ^ 2 + u s) ^ 2) +
          (q.2 - p.2) * (2 * u s * x s / (x s ^ 2 + u s) ^ 2)) +
         (q.2 - p.2) * ((q.1 - p.1) * (2 * u s * x s / (x s ^ 2 + u s) ^ 2) +
          (q.2 - p.2) * (2 * ff_budgetGxx (u s) (x s)))) s := by
    intro s hs
    exact ((ff_budgetDu_deriv (hu s) (hx s) (hpos s hs).1 (hpos s hs).2).const_mul _).add
      ((ff_budgetDx_deriv (hu s) (hx s) (hpos s hs).1 (hpos s hs).2).const_mul _)
  have hne : q.1 - p.1 ≠ 0 ∨ q.2 - p.2 ≠ 0 := by
    by_contra h
    push Not at h
    apply hpq
    exact Prod.ext (by linarith [h.1]) (by linarith [h.2])
  have hanti : StrictAntiOn (fun s => (q.1 - p.1) * ff_budgetDu (u s) (x s) +
      (q.2 - p.2) * ff_budgetDx (u s) (x s)) (Icc (0 : ℝ) 1) := by
    apply strictAntiOn_of_deriv_neg (convex_Icc _ _)
    · intro s hs
      exact (hsecond s hs).continuousAt.continuousWithinAt
    · intro s hs
      have hs' := interior_subset hs
      rw [(hsecond s hs').deriv]
      have h := hseg s hs'
      exact ff_budgetHessian_neg h.1 h.2.1 h.2.2 hne
  have hc : StrictConcaveOn ℝ (Icc (0 : ℝ) 1) (fun s => ff_budgetCost (u s) (x s)) := by
    apply StrictAntiOn.strictConcaveOn_of_deriv (convex_Icc _ _)
      (fun s hs => (hfirst s hs).continuousAt.continuousWithinAt)
    intro s hs t ht hst
    rw [(hfirst s (interior_subset hs)).deriv, (hfirst t (interior_subset ht)).deriv]
    exact hanti (interior_subset hs) (interior_subset ht) hst
  have h := hc.2 (by norm_num : (0 : ℝ) ∈ Icc 0 1) (by norm_num : (1 : ℝ) ∈ Icc 0 1)
    (by norm_num : (0 : ℝ) ≠ 1) ha hb hab
  simp [u, x, smul_eq_mul] at h
  have eu : a * p.1 + b * q.1 = p.1 + b * (q.1 - p.1) := by
    rw [show a = 1 - b by linarith only [hab]]
    ring
  have ex : a * p.2 + b * q.2 = p.2 + b * (q.2 - p.2) := by
    rw [show a = 1 - b by linarith only [hab]]
    ring
  change a * ff_budgetCost p.1 p.2 + b * ff_budgetCost q.1 q.2 <
    ff_budgetCost (a * p.1 + b * q.1) (a * p.2 + b * q.2)
  rwa [eu, ex]

end SmoothedOctagon
