module

public import SmoothedOctagon.Exclusion.Forward.Log

/-!
# Case F scalars: functions of the exterior factor

Every residual of the case-F scalar signs is, as a function of the exterior factor `h`, of the
canonical form `c₀ + c₁h + c₂h² + c₋/h + (d₀ + d₁h) log h`. Its second derivative is
`(2c₂h³ + 2c₋ + d₁h² - d₀h)/h³`, so a second-order Taylor comparison reduces to a polynomial sign.

## Main API

* `fs_cf c0 c1 c2 cm d0 d1 h`, its derivative `fs_cf'` (`fs_hasDerivAt_cf`, `fs_hasDerivAt_cf'`).
* `fs_cf_nonneg`: `G(h₀) ≥ 0`, `G'(h₀) ≥ 0` and `G'' ≥ 0` on `[h₀, h₁]` give `G(h₁) ≥ 0`.
* `fs_cf_tangent`: the tangent bound of a concave canonical function.
* `fs_Phi_sym`: `Φ(U, z, z)` through `log(S²/Z)` and `log(K/Z)`.
* `fs_f_ge_pade`: `f(h) ≥ (h - 1)³/(3h(h + 1))` for `h ≥ 1`.
* `fs_log_one_sub_le`: `log(1 - y) ≤ -y - y²/2 - y³/3` for `0 ≤ y < 1`.
-/

@[expose] public section

namespace SmoothedOctagon

open Real Set

/-- The canonical function `c₀ + c₁h + c₂h² + c₋/h + (d₀ + d₁h) log h`. -/
noncomputable def fs_cf (c0 c1 c2 cm d0 d1 h : ℝ) : ℝ :=
  c0 + c1 * h + c2 * h ^ 2 + cm / h + (d0 + d1 * h) * Real.log h

/-- The derivative of `fs_cf`. -/
noncomputable def fs_cf' (c1 c2 cm d0 d1 h : ℝ) : ℝ :=
  c1 + 2 * c2 * h - cm / h ^ 2 + d1 * Real.log h + (d0 + d1 * h) / h

theorem fs_hasDerivAt_cf (c0 c1 c2 cm d0 d1 : ℝ) {h : ℝ} (hh : 0 < h) :
    HasDerivAt (fs_cf c0 c1 c2 cm d0 d1) (fs_cf' c1 c2 cm d0 d1 h) h := by
  have hl := Real.hasDerivAt_log hh.ne'
  have hi := (hasDerivAt_id h).inv hh.ne'
  have h1 := ((((hasDerivAt_id h).const_mul c1).const_add c0).add
    ((hasDerivAt_pow 2 h).const_mul c2)).add (hi.const_mul cm)
  have h2 := (((hasDerivAt_id h).const_mul d1).const_add d0).mul hl
  have h3 := h1.add h2
  convert h3 using 1
  · ext y; simp only [fs_cf, id, Pi.add_apply, Pi.mul_apply, Pi.inv_apply]; ring
  · simp only [fs_cf', id]; field_simp; ring

theorem fs_hasDerivAt_cf' (c1 c2 cm d0 d1 : ℝ) {h : ℝ} (hh : 0 < h) :
    HasDerivAt (fs_cf' c1 c2 cm d0 d1)
      ((2 * c2 * h ^ 3 + 2 * cm + d1 * h ^ 2 - d0 * h) / h ^ 3) h := by
  have hl := Real.hasDerivAt_log hh.ne'
  have hi := (hasDerivAt_id h).inv hh.ne'
  have hi2 := (hasDerivAt_pow 2 h).inv (pow_ne_zero 2 hh.ne')
  have h1 := ((((hasDerivAt_id h).const_mul (2 * c2)).const_add c1).sub (hi2.const_mul cm)).add
    (hl.const_mul d1)
  have h2 := (((hasDerivAt_id h).const_mul d1).const_add d0).mul hi
  have h3 := h1.add h2
  convert h3 using 1
  · ext y; simp only [fs_cf', id, Pi.add_apply, Pi.sub_apply, Pi.mul_apply, Pi.inv_apply]
    field_simp
  · simp only [id, Pi.inv_apply]; field_simp; ring

/-- **Second-order comparison for the canonical function.** -/
theorem fs_cf_nonneg {c0 c1 c2 cm d0 d1 h0 h1 : ℝ} (h0pos : 0 < h0) (h01 : h0 ≤ h1)
    (hG : 0 ≤ fs_cf c0 c1 c2 cm d0 d1 h0) (hG' : 0 ≤ fs_cf' c1 c2 cm d0 d1 h0)
    (hG'' : ∀ h ∈ Icc h0 h1, 0 ≤ 2 * c2 * h ^ 3 + 2 * cm + d1 * h ^ 2 - d0 * h) :
    0 ≤ fs_cf c0 c1 c2 cm d0 d1 h1 := by
  have hd' : ∀ s ∈ Icc h0 h1, 0 ≤ fs_cf' c1 c2 cm d0 d1 s := by
    intro s hs
    have := ff_le_of_deriv (f := fs_cf' c1 c2 cm d0 d1)
      (f' := fun x ↦ (2 * c2 * x ^ 3 + 2 * cm + d1 * x ^ 2 - d0 * x) / x ^ 3) hs.1
      (fun x hx ↦ fs_hasDerivAt_cf' c1 c2 cm d0 d1 (by linarith [hx.1]))
      (fun x hx ↦ div_nonneg (hG'' x ⟨hx.1, le_trans hx.2 hs.2⟩)
        (pow_nonneg (by linarith [hx.1]) 3))
    linarith
  have := ff_le_of_deriv (f := fs_cf c0 c1 c2 cm d0 d1) (f' := fs_cf' c1 c2 cm d0 d1) h01
    (fun x hx ↦ fs_hasDerivAt_cf c0 c1 c2 cm d0 d1 (by linarith [hx.1])) hd'
  linarith

/-- **Tangent comparison for a concave canonical function**: if `G'' ≤ 0` on `[h₀, h]`, then
`G(h) ≤ G(h₀) + (h - h₀) G'(h₀)`. -/
theorem fs_cf_tangent {c0 c1 c2 cm d0 d1 h0 h : ℝ} (h0pos : 0 < h0) (hh : h0 ≤ h)
    (hconc : ∀ s ∈ Icc h0 h, 2 * c2 * s ^ 3 + 2 * cm + d1 * s ^ 2 - d0 * s ≤ 0) :
    fs_cf c0 c1 c2 cm d0 d1 h ≤
      fs_cf c0 c1 c2 cm d0 d1 h0 + (h - h0) * fs_cf' c1 c2 cm d0 d1 h0 := by
  set E := fs_cf c0 c1 c2 cm d0 d1 h0
  set D := fs_cf' c1 c2 cm d0 d1 h0
  have key := fs_cf_nonneg (c0 := E - h0 * D - c0) (c1 := D - c1) (c2 := -c2) (cm := -cm) (d0 := -d0)
    (d1 := -d1) h0pos hh (le_of_eq ?_) (le_of_eq ?_) (fun s hs ↦ by linarith [hconc s hs])
  · have e : fs_cf (E - h0 * D - c0) (D - c1) (-c2) (-cm) (-d0) (-d1) h =
        E + (h - h0) * D - fs_cf c0 c1 c2 cm d0 d1 h := by unfold fs_cf; ring
    linarith
  · simp only [E, fs_cf]; ring
  · simp only [D, fs_cf']; ring

/-- `Φ` with equal neighbours: `Φ = S/2 - 2/S + 2/K - K/8 - log(S²/Z) + log(K/Z)`. -/
theorem fs_Phi_sym {U z : ℝ} (hU : 0 < U) (hz : 0 < z) :
    ff_Phi U z z = (1 + z) / 2 - 2 / (1 + z) + 2 / (1 + U) - (1 + U) / 8 -
      Real.log ((1 + z) ^ 2 / (z ^ 2 + U)) + Real.log ((1 + U) / (z ^ 2 + U)) := by
  have hS : 0 < 1 + z := by linarith
  have hK : 0 < 1 + U := by linarith
  have hZ : 0 < z ^ 2 + U := by positivity
  have h4 : Real.log 4 = 2 * Real.log 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; push_cast; ring
  unfold ff_Phi ff_f
  rw [Real.log_div hS.ne' two_ne_zero, Real.log_div four_ne_zero hK.ne',
    Real.log_div (by positivity) hZ.ne', Real.log_div hK.ne' hZ.ne', Real.log_pow, h4]
  field_simp
  ring

/-- The factor curvature has the required sign by comparison with the geometric
boundary `U = z + 1`, followed by monotonicity in the factor. -/
theorem fs_factor_curvature_nonneg {U z s : ℝ} (hz : 1 ≤ z) (hz2 : z ^ 2 < 3)
    (hU : z + 1 ≤ U) (hU3 : U ≤ 3) (hs : (1 + z) ^ 2 / (z ^ 2 + U) ≤ s) :
    0 ≤ (U - z) * s ^ 2 * (2 * z * s - (1 + z)) + (z ^ 2 + U) * s - 2 * z * (1 + z) := by
  have hz0 : 0 < z := by linarith
  have hU0 : 0 < U := by linarith
  have hZ : 0 < z ^ 2 + U := by positivity
  have hI1 : 1 ≤ (1 + z) ^ 2 / (z ^ 2 + U) := by rw [le_div_iff₀ hZ]; nlinarith
  have hQ : (1 - z) * U ^ 2 - z * (z ^ 3 + 7 * z ^ 2 + 5 * z + 3) * U +
      z ^ 2 * (z ^ 4 + 2 * z ^ 3 + 6 * z ^ 2 + 5 * z + 2) ≤ 0 := by
    have hinner : z ^ 2 * (z + 1) - 2 * z - 8 < 0 := by
      have h := mul_lt_mul_of_pos_right hz2 (by linarith : 0 < z + 1)
      nlinarith only [h, hz2]
    have hbase : z ^ 3 * (z ^ 2 * (z + 1) - 2 * z - 8) - 7 * z ^ 2 - 2 * z + 1 < 0 := by
      have h := mul_neg_of_pos_of_neg (pow_pos hz0 3) hinner
      nlinarith only [h, hz, sq_nonneg z]
    have hdrop : 0 ≤ (U - (z + 1)) *
        ((z - 1) * (U + (z + 1)) + z * (z ^ 3 + 7 * z ^ 2 + 5 * z + 3)) := by
      apply mul_nonneg (by linarith only [hU])
      exact add_nonneg (mul_nonneg (by linarith only [hz]) (by linarith only [hz, hU]))
        (by positivity)
    have he : (1 - z) * U ^ 2 - z * (z ^ 3 + 7 * z ^ 2 + 5 * z + 3) * U +
        z ^ 2 * (z ^ 4 + 2 * z ^ 3 + 6 * z ^ 2 + 5 * z + 2) =
        z ^ 3 * (z ^ 2 * (z + 1) - 2 * z - 8) - 7 * z ^ 2 - 2 * z + 1 -
        (U - (z + 1)) * ((z - 1) * (U + (z + 1)) + z * (z ^ 3 + 7 * z ^ 2 + 5 * z + 3)) := by ring
    rw [he]
    linarith only [hbase, hdrop]
  set I := (1 + z) ^ 2 / (z ^ 2 + U) with hIdef
  have hPI : 0 ≤ (U - z) * I ^ 2 * (2 * z * I - (1 + z)) + (z ^ 2 + U) * I - 2 * z * (1 + z) := by
    have e : (U - z) * I ^ 2 * (2 * z * I - (1 + z)) + (z ^ 2 + U) * I - 2 * z * (1 + z) =
        -((1 + z) * (2 * z + 1 - U) * ((1 - z) * U ^ 2 - z * (z ^ 3 + 7 * z ^ 2 + 5 * z + 3) * U +
          z ^ 2 * (z ^ 4 + 2 * z ^ 3 + 6 * z ^ 2 + 5 * z + 2))) / (z ^ 2 + U) ^ 3 := by
      rw [hIdef]; field_simp; ring
    rw [e]
    apply div_nonneg _ (by positivity)
    have : 0 ≤ (1 + z) * (2 * z + 1 - U) := mul_nonneg (by linarith) (by linarith)
    nlinarith
  have hM : 0 ≤ (U - z) * (2 * z * (s ^ 2 + s * I + I ^ 2) - (1 + z) * (s + I)) + (z ^ 2 + U) := by
    have hs1 : 1 ≤ s := le_trans hI1 hs
    have h1 : (1 + z) * (s + I) ≤ 2 * z * (s ^ 2 + s * I + I ^ 2) := by
      have : s + I ≤ s ^ 2 + s * I + I ^ 2 := by nlinarith
      have : 0 ≤ s + I := by linarith
      nlinarith
    have : 0 ≤ U - z := by linarith
    nlinarith
  have e : (U - z) * s ^ 2 * (2 * z * s - (1 + z)) + (z ^ 2 + U) * s - 2 * z * (1 + z) =
      ((U - z) * I ^ 2 * (2 * z * I - (1 + z)) + (z ^ 2 + U) * I - 2 * z * (1 + z)) +
      (s - I) * ((U - z) * (2 * z * (s ^ 2 + s * I + I ^ 2) - (1 + z) * (s + I)) + (z ^ 2 + U)) := by
    ring
  rw [e]
  have : 0 ≤ (s - I) * ((U - z) * (2 * z * (s ^ 2 + s * I + I ^ 2) - (1 + z) * (s + I)) + (z ^ 2 + U)) :=
    mul_nonneg (by linarith) hM
  linarith

/-- **The Padé lower bound** `f(h) ≥ (h - 1)³/(3h(h + 1))` for `h ≥ 1` (derivative
`(h - 1)⁴/(6h²(h + 1)²)` of the difference). -/
theorem fs_f_ge_pade {h : ℝ} (hh : 1 ≤ h) : (h - 1) ^ 3 / (3 * h * (h + 1)) ≤ ff_f h := by
  have key := ff_le_of_deriv (f := fun s ↦ ff_f s - (s - 1) ^ 3 / (3 * s * (s + 1)))
    (f' := fun s ↦ (s - 1) ^ 4 / (6 * s ^ 2 * (s + 1) ^ 2)) hh (fun s hs ↦ ?_) (fun s hs ↦ ?_)
  · have : ff_f 1 = 0 := by simp [ff_f]
    simp only [this] at key
    norm_num at key
    linarith
  · have hs0 : 0 < s := by linarith [hs.1]
    have hl := Real.hasDerivAt_log hs0.ne'
    have hi := (hasDerivAt_id s).inv hs0.ne'
    have hf : HasDerivAt ff_f ((1 - -(s ^ 2)⁻¹) / 2 - s⁻¹) s := by
      have := (((hasDerivAt_id s).sub hi).div_const 2).sub hl
      convert this using 1
      · ext y; simp [ff_f]
      · simp only [id]; ring
    have hn : HasDerivAt (fun s : ℝ ↦ (s - 1) ^ 3) (3 * (s - 1) ^ 2) s := by
      convert ((hasDerivAt_id' s).sub_const 1).fun_pow 3 using 1; norm_num
    have hd : HasDerivAt (fun s : ℝ ↦ 3 * s * (s + 1)) (3 * (2 * s + 1)) s := by
      have := ((hasDerivAt_id' s).const_mul 3).mul ((hasDerivAt_id' s).add_const 1)
      convert this using 1; ring
    have h := hf.sub (hn.div hd (by positivity))
    convert h using 1
    field_simp
    ring
  · have hs0 : 0 < s := by linarith [hs.1]
    positivity

/-- `log(1 - y) ≤ -y - y²/2 - y³/3` for `0 ≤ y < 1`. -/
theorem fs_log_one_sub_le {y : ℝ} (h0 : 0 ≤ y) (h1 : y < 1) :
    Real.log (1 - y) ≤ -y - y ^ 2 / 2 - y ^ 3 / 3 := by
  have key := ff_le_of_deriv (f := fun s ↦ -s - s ^ 2 / 2 - s ^ 3 / 3 - Real.log (1 - s))
    (f' := fun s ↦ s ^ 3 / (1 - s)) h0 (fun s hs ↦ ?_) (fun s hs ↦ ?_)
  · simp at key; linarith
  · have hs1 : 0 < 1 - s := by linarith [hs.2]
    have hl' : HasDerivAt (fun s : ℝ ↦ Real.log (1 - s)) (-1 / (1 - s)) s := by
      have := ((hasDerivAt_id' s).const_sub 1).log hs1.ne'
      convert this using 1
    have h := (((((hasDerivAt_id' s).neg).sub ((hasDerivAt_pow 2 s).div_const 2)).sub
      ((hasDerivAt_pow 3 s).div_const 3))).sub hl'
    convert h using 1
    field_simp
    ring
  · have hs1 : 0 < 1 - s := by linarith [hs.2]
    have : 0 ≤ s := hs.1
    positivity

end SmoothedOctagon
