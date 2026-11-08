module

public import SmoothedOctagon.Exclusion.Forward.Scalar

/-!
# Case F: the edge function

Monotonicity and the rectangle inequality of the edge function `G`.

## Main API

* `ff_monotoneOn_Icc`: monotonicity on an interval from a nonnegative derivative.
* `ff_hasDerivAt_G_right`: `∂G/∂b = 3a - 2b log(a + b) - (a² + b²)/(a + b) + b log(b² + 4) + b³/(b² + 4)`.
* `ff_G_mono_right`, `ff_G_mono`: `G` increases in each argument while the product is at most `8`.
* `ff_G_rect`: `G(x, y) + G(a, a) ≥ G(x, a) + G(a, y)` for `x, y ≥ a > 0` (positive mixed
  derivative `G_ab = 2(a² + ab + b²)/(a + b)²`).
* `ff_G_mul`: `G(ax, ay) = a² g2(4/a², x, y)`.
* `ff_g2_one_one_nonneg`: `g2(U, 1, 1) ≥ 0` for `0 < U ≤ 3` (`G(a, a) ≥ 0` for `a² ≥ 4/3`).
-/

@[expose] public section

namespace SmoothedOctagon

open Set Real

/-- Monotonicity on `[lo, hi]` from a nonnegative derivative. -/
theorem ff_monotoneOn_Icc {f f' : ℝ → ℝ} {lo hi : ℝ}
    (hd : ∀ x ∈ Icc lo hi, HasDerivAt f (f' x) x) (h0 : ∀ x ∈ Icc lo hi, 0 ≤ f' x) :
    MonotoneOn f (Icc lo hi) :=
  monotoneOn_of_hasDerivWithinAt_nonneg (convex_Icc lo hi)
    (fun x hx ↦ (hd x hx).continuousAt.continuousWithinAt)
    (fun x hx ↦ (hd x (interior_subset hx)).hasDerivWithinAt)
    (fun x hx ↦ h0 x (interior_subset hx))

/-- `f lo ≤ f hi` from a nonnegative derivative on `[lo, hi]`. -/
theorem ff_le_of_deriv {f f' : ℝ → ℝ} {lo hi : ℝ} (hlh : lo ≤ hi)
    (hd : ∀ x ∈ Icc lo hi, HasDerivAt f (f' x) x) (h0 : ∀ x ∈ Icc lo hi, 0 ≤ f' x) :
    f lo ≤ f hi :=
  ff_monotoneOn_Icc hd h0 ⟨le_rfl, hlh⟩ ⟨hlh, le_rfl⟩ hlh

/-- `∂G/∂b`. -/
noncomputable def ff_Gb (a b : ℝ) : ℝ :=
  3 * a - 2 * b * Real.log (a + b) - (a ^ 2 + b ^ 2) / (a + b) + b * Real.log (b ^ 2 + 4) +
    b ^ 3 / (b ^ 2 + 4)

theorem ff_hasDerivAt_G_right {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    HasDerivAt (fun y ↦ ff_G a y) (ff_Gb a b) b := by
  have hab : 0 < a + b := by linarith
  have hK : 0 < b ^ 2 + 4 := by positivity
  have h1 : HasDerivAt (fun y : ℝ ↦ Real.log (a + y)) (1 / (a + b)) b := by
    have := ((hasDerivAt_id b).const_add a).log hab.ne'
    simpa using this
  have h2 : HasDerivAt (fun y : ℝ ↦ Real.log (y ^ 2 + 4)) (2 * b / (b ^ 2 + 4)) b := by
    have := ((hasDerivAt_pow 2 b).add_const 4).log hK.ne'
    simpa using this
  have h := ((((hasDerivAt_id b).const_mul (3 * a)).sub_const 4).sub
    (((hasDerivAt_pow 2 b).const_add (a ^ 2)).mul h1)).add
    ((((hasDerivAt_pow 2 b).mul h2).const_add (a ^ 2 * Real.log (a ^ 2 + 4))).div_const 2)
  convert h using 1
  · ext y; simp only [ff_G, Pi.add_apply, Pi.sub_apply, Pi.mul_apply, id]
  · simp only [ff_Gb]; field_simp; ring

/-- `∂G/∂b ≥ a(a + 2b)(b² - ab + 8)/((a + b)(b² + 4))`, from `log y ≥ 1 - 1/y`. -/
theorem ff_Gb_pos {a b : ℝ} (ha : 0 < a) (hb : 0 < b) (hab8 : a * b ≤ 8) : 0 < ff_Gb a b := by
  have hab : 0 < a + b := by linarith
  have hK : 0 < b ^ 2 + 4 := by positivity
  have hy : 0 < (b ^ 2 + 4) / (a + b) ^ 2 := by positivity
  have hlog := Real.one_sub_inv_le_log_of_pos hy
  rw [Real.log_div hK.ne' (by positivity), Real.log_pow, inv_div] at hlog
  have key : a * (a + 2 * b) * (b ^ 2 - a * b + 8) / ((a + b) * (b ^ 2 + 4)) ≤ ff_Gb a b := by
    have e : ff_Gb a b = 3 * a - (a ^ 2 + b ^ 2) / (a + b) + b ^ 3 / (b ^ 2 + 4) +
        b * (Real.log (b ^ 2 + 4) - 2 * Real.log (a + b)) := by unfold ff_Gb; ring
    rw [e]
    have hb' : b * (1 - (a + b) ^ 2 / (b ^ 2 + 4)) ≤
        b * (Real.log (b ^ 2 + 4) - ((2 : ℕ) : ℝ) * Real.log (a + b)) :=
      mul_le_mul_of_nonneg_left hlog hb.le
    push_cast at hb'
    have e2 : a * (a + 2 * b) * (b ^ 2 - a * b + 8) / ((a + b) * (b ^ 2 + 4)) =
        3 * a - (a ^ 2 + b ^ 2) / (a + b) + b ^ 3 / (b ^ 2 + 4) +
          b * (1 - (a + b) ^ 2 / (b ^ 2 + 4)) := by field_simp; ring
    rw [e2]; linarith
  refine lt_of_lt_of_le ?_ key
  have : 0 < b ^ 2 - a * b + 8 := by nlinarith
  positivity

/-- `G(a, ·)` increases on `[b', b]` when `a b ≤ 8`. -/
theorem ff_G_mono_right {a b b' : ℝ} (ha : 0 < a) (hb' : 0 < b') (hbb : b' ≤ b) (hab : a * b ≤ 8) :
    ff_G a b' ≤ ff_G a b := by
  refine ff_le_of_deriv (f := fun y ↦ ff_G a y) (f' := ff_Gb a) hbb
    (fun y hy ↦ ff_hasDerivAt_G_right ha (by linarith [hy.1])) (fun y hy ↦ ?_)
  refine (ff_Gb_pos ha (by linarith [hy.1]) ?_).le
  nlinarith [hy.2]

theorem ff_G_comm' (x y : ℝ) : ff_G x y = ff_G y x := by unfold ff_G; rw [add_comm x y]; ring

/-- `G` increases in both arguments while the product is at most `8`. -/
theorem ff_G_mono {x y x' y' : ℝ} (hx' : 0 < x') (hy' : 0 < y') (hxx : x' ≤ x) (hyy : y' ≤ y)
    (hxy : x * y ≤ 8) : ff_G x' y' ≤ ff_G x y := by
  have h1 : ff_G x' y' ≤ ff_G x' y :=
    ff_G_mono_right hx' hy' hyy (by nlinarith [mul_le_mul_of_nonneg_right hxx (by linarith : (0:ℝ) ≤ y)])
  have h2 : ff_G x' y ≤ ff_G x y := by
    rw [ff_G_comm' x' y, ff_G_comm' x y]
    exact ff_G_mono_right (by linarith) hx' hxx (by linarith [mul_comm x y])
  linarith

/-- `∂G/∂b` increases in `a`: `∂²G/∂a∂b = 2(a² + ab + b²)/(a + b)² > 0`. -/
theorem ff_Gb_mono_left {a a' b : ℝ} (ha : 0 < a) (hb : 0 < b) (haa : a ≤ a') :
    ff_Gb a b ≤ ff_Gb a' b := by
  refine ff_le_of_deriv (f := fun x ↦ ff_Gb x b)
    (f' := fun x ↦ 2 * (x ^ 2 + x * b + b ^ 2) / (x + b) ^ 2) haa (fun x hx ↦ ?_) (fun x hx ↦ ?_)
  · have hx : 0 < x := by linarith [hx.1]
    have hxb : 0 < x + b := by linarith
    have h1 : HasDerivAt (fun x : ℝ ↦ Real.log (x + b)) (1 / (x + b)) x := by
      have := ((hasDerivAt_id x).add_const b).log hxb.ne'
      simpa using this
    have h := ((((hasDerivAt_id x).const_mul 3).sub (h1.const_mul (2 * b))).sub
      (((hasDerivAt_pow 2 x).add_const (b ^ 2)).div ((hasDerivAt_id x).add_const b) hxb.ne')).add_const
      (b * Real.log (b ^ 2 + 4) + b ^ 3 / (b ^ 2 + 4))
    convert h using 1
    · ext y; simp only [ff_Gb, Pi.sub_apply, Pi.div_apply, id]; ring
    · simp only [id]; field_simp; ring
  · have hx : 0 < x := by linarith [hx.1]
    positivity

/-- **The rectangle inequality**: for `x, y ≥ a > 0`, `G(x, y) ≥ G(x, a) + G(a, y) - G(a, a)`, since
the mixed derivative `G_ab = 2(a² + ab + b²)/(a + b)²` is positive. -/
theorem ff_G_rect {a x y : ℝ} (ha : 0 < a) (hx : a ≤ x) (hy : a ≤ y) :
    ff_G x a + ff_G a y - ff_G a a ≤ ff_G x y := by
  have := ff_le_of_deriv (f := fun t ↦ ff_G x t - ff_G a t) (f' := fun t ↦ ff_Gb x t - ff_Gb a t)
    hy (fun t ht ↦ (ff_hasDerivAt_G_right (by linarith) (by linarith [ht.1])).sub
      (ff_hasDerivAt_G_right ha (by linarith [ht.1])))
    (fun t ht ↦ sub_nonneg.2 (ff_Gb_mono_left ha (by linarith [ht.1]) hx))
  linarith

/-- `G(ax, ay) = a² g2(4/a², x, y)`. -/
theorem ff_G_mul {a x y : ℝ} (ha : 0 < a) (hx : 0 < x) (hy : 0 < y) :
    ff_G (a * x) (a * y) = a ^ 2 * ff_g2 (4 / a ^ 2) x y := by
  have ha2 : 0 < a ^ 2 := by positivity
  have e1 : a * x + a * y = a * (x + y) := by ring
  have e2 : (a * x) ^ 2 + 4 = a ^ 2 * (x ^ 2 + 4 / a ^ 2) := by field_simp
  have e3 : (a * y) ^ 2 + 4 = a ^ 2 * (y ^ 2 + 4 / a ^ 2) := by field_simp
  have hx2 : 0 < x ^ 2 + 4 / a ^ 2 := by positivity
  have hy2 : 0 < y ^ 2 + 4 / a ^ 2 := by positivity
  unfold ff_G ff_g2
  rw [e1, e2, e3, Real.log_mul ha.ne' (by positivity), Real.log_mul ha2.ne' hx2.ne',
    Real.log_mul ha2.ne' hy2.ne', Real.log_pow]
  field_simp
  push_cast
  ring

/-- `g2(U, 1, 1) = 3 - U - log(4/(1 + U)) ≥ 0` for `0 < U ≤ 3`; equivalently `G(a, a) ≥ 0` for
`a² ≥ 4/3`. -/
theorem ff_g2_one_one_nonneg {U : ℝ} (hU : 0 < U) (hU3 : U ≤ 3) : 0 ≤ ff_g2 U 1 1 := by
  have hK : 0 < 1 + U := by linarith
  have hl := Real.one_sub_inv_le_log_of_pos (show 0 < (1 + U) / 4 by positivity)
  rw [Real.log_div hK.ne' (by norm_num), inv_div] at hl
  have e : ff_g2 U 1 1 = 3 - U + (Real.log (1 + U) - Real.log 4) := by
    unfold ff_g2
    have : Real.log (1 + 1 : ℝ) * 2 = Real.log 4 := by
      rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; norm_num; ring
    rw [show (1 : ℝ) ^ 2 + U = 1 + U by ring, ← this]
    ring
  rw [e]
  have h2 : 1 - 4 / (1 + U) = (U - 3) / (1 + U) := by field_simp; ring
  rw [h2] at hl
  have h3 : 0 ≤ (3 - U) * U / (1 + U) := by
    apply div_nonneg _ hK.le; nlinarith
  have h4 : 3 - U + (U - 3) / (1 + U) = (3 - U) * U / (1 + U) := by field_simp; ring
  linarith

end SmoothedOctagon
