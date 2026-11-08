module

public import SmoothedOctagon.Exclusion.Forward.Edge
public import SmoothedOctagon.Exclusion.Forward.Cap
public import SmoothedOctagon.Exclusion.Forward.Casimir
public import SmoothedOctagon.Exclusion.Forward.Reduce
public import SmoothedOctagon.Exclusion.Forward.Budget
public import SmoothedOctagon.Exclusion.Forward.Scalars.SumSym
public import SmoothedOctagon.Exclusion.Forward.Scalars.LargerNorm
public import SmoothedOctagon.Exclusion.Forward.Scalars.Neighbor
public import SmoothedOctagon.Exclusion.Forward.Scalars.SmallMin

/-!
# Case F: the scalar exclusion

No window `ff_Dim` of an all-forward competitive normal period with `N ≥ 7` exists (`ff_Dim.elim`,
`ff_Win.elim`).

## The chain

1. `ff_Dim.U_lt_three`: `a² > 4/3` (the small forward minimum, `Forward/Scalars/SmallMin.lean`).
2. `ff_Dim.cost_seven`: `G(a, a) ≥ 0`, so the seven-entry bound holds without extra copies.
3. `ff_Dim.eleven_fifths_lt`: `a² < 20/11`.
4. `ff_Dim.budget`: `P + z + w + D < (5U + 1)/3`, from the rectangle inequality `ff_G_rect` and
   `ff_budget_g` (`Forward/Budget.lean`).
5. `ff_Dim.neighbor`: `w < 4/3` when `z ≤ w`, from the left row, the floors and the neighbour sign
   `ff_resN_neg` (`Forward/Scalars/Neighbor.lean`).
6. `ff_Dim.norms`: `δu + δv < 1/35` and `δv < 1/64` when `z ≤ w`, from the centered row
   (`ff_r_eq`), the floors (`ff_F_eq_L`, `ff_F_mono`), `m > n` (`ff_m_sub_n_pos`), the reductions
   `ff_resS_le_sym`, `ff_resV_le_sym` (`Forward/Reduce.lean`) and the symmetric signs
   `ff_resS_neg`, `ff_resV_neg` (`Forward/Scalars/SumSym.lean`, `LargerNorm.lean`).
7. `ff_casimir_lower` (`Forward/Casimir.lean`): the two norm bounds give `γ² > 23/125`,
   contradicting the cap `γ² ≤ 23/125`.

`ff_Win.toDim` converts the physical window to its dimensionless form.
-/

@[expose] public section

namespace SmoothedOctagon

open Real

/-! ### Exact identities -/

/-- `L` is the floor minus `3/4`: `F_{z/S}(h) = 3/4 + L(z, h)` for `h ≠ 1`. -/
theorem ff_F_eq_L {z h : ℝ} (hz : 0 < z) (hh : h ≠ 1) (hh0 : 0 < h) :
    ff_F (z / (1 + z)) h = 3 / 4 + ff_L z h := by
  have hh1 : h - 1 ≠ 0 := sub_ne_zero.2 hh
  have hS : 1 + z ≠ 0 := by positivity
  unfold ff_F ff_L ff_f
  field_simp
  ring

/-- The centered left row: `αA - B = (3/4)(n + m) + r`. -/
theorem ff_r_eq {U z w h : ℝ} (hU : 0 < U) (hz : 0 < z) (hw : 0 < w) (hh : 0 < h) :
    ff_alpha U z h * ff_A U z w - ff_B U z h =
      3 / 4 * (ff_n U z h + ff_m U z w h) + ff_r U z w h := by
  have hS : 0 < 1 + z := by linarith
  have hT : 0 < 1 + w := by linarith
  have hK : 0 < 1 + U := by linarith
  have hZ : 0 < z ^ 2 + U := by positivity
  have h4 : Real.log 4 = 2 * Real.log 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; push_cast; ring
  unfold ff_alpha ff_A ff_B ff_n ff_m ff_r ff_Phi ff_f ff_q
  rw [Real.log_div (by positivity) hK.ne', Real.log_mul hS.ne' hT.ne',
    Real.log_div hS.ne' two_ne_zero, Real.log_div hT.ne' two_ne_zero,
    Real.log_div four_ne_zero hK.ne', h4]
  generalize Real.log (1 + z) = l1
  generalize Real.log (1 + w) = l2
  generalize Real.log (1 + U) = l3
  generalize Real.log 2 = l4
  generalize Real.log h = l5
  field_simp
  ring

/-- The centered central row: `(3/4)(S + T) - A = e₀ - Φ`. -/
theorem ff_A_eq {U z w : ℝ} (hU : 0 < U) (hz : 0 < z) (hw : 0 < w) :
    3 / 4 * ((1 + z) + (1 + w)) - ff_A U z w = ff_e0 U - ff_Phi U z w := by
  have hS : 0 < 1 + z := by linarith
  have hT : 0 < 1 + w := by linarith
  have hK : 0 < 1 + U := by linarith
  have h4 : Real.log 4 = 2 * Real.log 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; push_cast; ring
  unfold ff_A ff_e0 ff_Phi ff_f ff_q
  rw [Real.log_div (by positivity) hK.ne', Real.log_mul hS.ne' hT.ne',
    Real.log_div hS.ne' two_ne_zero, Real.log_div hT.ne' two_ne_zero,
    Real.log_div four_ne_zero hK.ne', h4]
  generalize Real.log (1 + z) = l1
  generalize Real.log (1 + w) = l2
  generalize Real.log (1 + U) = l3
  generalize Real.log 2 = l4
  field_simp
  ring

/-- The positive coefficient difference: `m - n > 0` on `U < 3`, `1 ≤ z ≤ w`, `h ≥ 1`, since
`S Z (m - n)` is `K(ST - K) > 0` plus `(h - 1)` times a nonnegative quantity. -/
theorem ff_m_sub_n_pos {U z w h : ℝ} (hU : 0 < U) (hU3 : U < 3) (hz : 1 ≤ z) (hzw : z ≤ w)
    (hh : 1 ≤ h) : 0 < ff_m U z w h - ff_n U z h := by
  have hS : 2 ≤ 1 + z := by linarith
  have hT : 1 + z ≤ 1 + w := by linarith
  have hK : 0 < 1 + U := by linarith
  have hZ : 0 < z ^ 2 + U := by positivity
  have hSZ : 0 < (1 + z) * (z ^ 2 + U) := by positivity
  have key : (1 + z) * (z ^ 2 + U) * (ff_m U z w h - ff_n U z h) =
      (1 + U) * ((1 + z) * (1 + w) - (1 + U)) +
        (h - 1) * ((1 + z) ^ 4 - (1 + U) ^ 2 + (1 + U) * (1 + z) ^ 2 * ((1 + w) - (1 + z))) := by
    unfold ff_m ff_n ff_q
    field_simp
    ring
  have h1 : 0 < (1 + z) * (1 + w) - (1 + U) := by nlinarith
  have h2 : 0 ≤ (1 + z) ^ 4 - (1 + U) ^ 2 := by
    have : (1 + U) ^ 2 ≤ 16 := by nlinarith
    have : 16 ≤ (1 + z) ^ 4 := by
      have : (4 : ℝ) ≤ (1 + z) ^ 2 := by nlinarith
      nlinarith
    linarith
  have h3 : 0 ≤ (1 + U) * (1 + z) ^ 2 * ((1 + w) - (1 + z)) := by
    apply mul_nonneg (by positivity); linarith
  have hpos : 0 < (1 + z) * (z ^ 2 + U) * (ff_m U z w h - ff_n U z h) := by
    rw [key]
    have : 0 ≤ (h - 1) * ((1 + z) ^ 4 - (1 + U) ^ 2 + (1 + U) * (1 + z) ^ 2 * ((1 + w) - (1 + z))) :=
      mul_nonneg (by linarith) (by linarith)
    nlinarith
  exact pos_of_mul_pos_right hpos hSZ.le

/-- The floor increases in the factor: `F_x(r) ≤ F_x(r')` for `1/2 ≤ x`, `1 < r ≤ r'`. -/
theorem ff_F_mono {x r r' : ℝ} (hx : 1 / 2 ≤ x) (hr : 1 < r) (hrr : r ≤ r') :
    ff_F x r ≤ ff_F x r' := by
  refine ff_le_of_deriv (f := ff_F x)
    (f' := fun s ↦ x ^ 2 - x * ((s - 1 - Real.log s) / (s - 1) ^ 2)) hrr (fun s hs ↦ ?_)
    (fun s hs ↦ ?_)
  · have hs1 : 1 < s := lt_of_lt_of_le hr hs.1
    have hl := Real.hasDerivAt_log (by linarith : s ≠ 0)
    have h := (((hasDerivAt_id s).const_mul (x ^ 2)).const_add 1).sub
      ((((hasDerivAt_id s).mul hl).const_mul x).div ((hasDerivAt_id s).sub_const 1)
        (by simp; linarith))
    convert h using 1
    · ext y; simp only [ff_F, id, Pi.sub_apply, Pi.div_apply, Pi.mul_apply]; ring
    · have : s - 1 ≠ 0 := by linarith
      simp only [id, Pi.mul_apply]
      field_simp
      ring
  · have hs1 : 1 < s := lt_of_lt_of_le hr hs.1
    have hlog := ff_log_ge_two hs1.le
    have hs0 : 0 < s + 1 := by linarith
    have e : 2 * ((s - 1) / (s + 1)) = 2 * (s - 1) / (s + 1) := by ring
    rw [e, div_le_iff₀ hs0] at hlog
    have hb : s - 1 - Real.log s ≤ (s - 1) ^ 2 / 2 := by nlinarith
    have hq : (s - 1 - Real.log s) / (s - 1) ^ 2 ≤ 1 / 2 := by
      rw [div_le_iff₀ (by positivity)]; linarith
    have hx0 : 0 ≤ x := by linarith
    nlinarith

/-! ### The scalar signs -/

/-- **The neighbour sign**: on `11/5 ≤ U < 3`, `1 ≤ z ≤ w`, `w ≥ 4/3`, `z + w ≤ 5(U - 1)/3` and
`S²/Z ≤ h ≤ min(S/z, h_c)`, `h_c = S(5U - 2 - 3w)/(3Z)`, the neighbour residual is negative. Proof
(`fs_resN_neg`): after lowering `w`, the residual is concave in `h` and is bounded by its tangent at
`S²/Z`; the tangent values are signed by Padé/two-term logarithm bounds and Bernstein expansions. -/
theorem ff_resN_neg {U z w h : ℝ} (hU : 11 / 5 ≤ U) (hU3 : U < 3) (hz : 1 ≤ z) (hzw : z ≤ w)
    (hw : 4 / 3 ≤ w) (hzw' : z + w ≤ 5 * (U - 1) / 3) (hh1 : 1 < h)
    (hhl : (1 + z) ^ 2 / (z ^ 2 + U) ≤ h) (hhu : h ≤ (1 + z) / z)
    (hhc : h ≤ (1 + z) * (5 * U - 2 - 3 * w) / (3 * (z ^ 2 + U))) : ff_resN U z w h < 0 :=
  fs_resN_neg hU hU3 hz hzw hw hzw' hh1 hhl hhu hhc

/-- **Reduction of the sum residual to equal neighbours**: `𝓔_Σ` does not increase with the larger
neighbour `w`. -/
theorem ff_resS_le_sym {U z w h : ℝ} (hU : 11 / 5 ≤ U) (hU3 : U < 3) (hz : 1 ≤ z) (hzw : z ≤ w)
    (hw : w ≤ 4 / 3) (hh : 1 < h) : ff_resS U z w h ≤ ff_resS U z z h := by
  have hU0 : 0 < U := by linarith
  exact ff_resS_le_sym' hU hU3 hz hzw hw hh
    (ff_m_sub_n_pos hU0 hU3 hz le_rfl hh.le).le
    (fun w' hw' ↦ ff_r_eq hU0 (by linarith) hw' (by linarith))

/-- **Reduction of the larger-norm residual to equal neighbours**: `𝓔_v` does not increase with the
larger neighbour `w`. -/
theorem ff_resV_le_sym {U z w h : ℝ} (hU : 11 / 5 ≤ U) (hU3 : U < 3) (hz : 1 ≤ z) (hzw : z ≤ w)
    (hw : w ≤ 4 / 3) (hh : 1 < h) : ff_resV U z w h ≤ ff_resV U z z h := by
  have hU0 : 0 < U := by linarith
  exact ff_resV_le_sym' hU0 hz hzw hw hh (fun w' hw' ↦ ff_r_eq hU0 (by linarith) hw' (by linarith))

/-- **The symmetric sum sign**: `𝓔_Σ < 0` on the symmetric domain `1 ≤ z ≤ 4/3`, `1 + 6z/5 ≤ U < 3`,
`S²/Z ≤ h ≤ S(5U - 2 - 3z)/(3Z)`. Proof (`fs_resS_neg`): the Padé envelope `Ψ(τ)`, `τ = H/h`, is
concave (`A₀ ≤ 0`); its tangent at the cost endpoint gives two values signed by logarithm bounds and
Bernstein expansions. -/
theorem ff_resS_neg {U z h : ℝ} (hz : 1 ≤ z) (hz' : z ≤ 4 / 3) (hU : 1 + 6 * z / 5 ≤ U) (hU3 : U < 3)
    (hhl : (1 + z) ^ 2 / (z ^ 2 + U) ≤ h)
    (hhu : h ≤ (1 + z) * (5 * U - 2 - 3 * z) / (3 * (z ^ 2 + U))) : ff_resS U z z h < 0 :=
  fs_resS_neg hz hz' hU hU3 hhl hhu

/-- **The symmetric larger-norm sign**: `𝓔_v < 0` on the symmetric domain `1 ≤ z ≤ 4/3`,
`1 + 6z/5 ≤ U < 3`, `S²/Z ≤ h ≤ S(5U - 2 - 3z)/(3Z)`. Proof (`fs_resV_neg`): concavity in `h` and
the two tangent values, signed by logarithm bounds and Bernstein expansions. -/
theorem ff_resV_neg {U z h : ℝ} (hz : 1 ≤ z) (hz' : z ≤ 4 / 3) (hU : 1 + 6 * z / 5 ≤ U) (hU3 : U < 3)
    (hhl : (1 + z) ^ 2 / (z ^ 2 + U) ≤ h)
    (hhu : h ≤ (1 + z) * (5 * U - 2 - 3 * z) / (3 * (z ^ 2 + U))) : ff_resV U z z h < 0 :=
  fs_resV_neg hz hz' hU hU3 hhl hhu

/-! ### The window -/

namespace ff_Dim

variable (W : ff_Dim)

/-- **The small forward minimum**: at a forward window whose centre is a minimum of the five
margins, `a² > 4/3`, i.e. `U < 3`. Proof (`fs_U_lt_three`): the three comparison faces, with the
rational envelope of the integral bound on the hard face, a difference comparison for lowering the
larger neighbour and Bernstein signs for `R₀, …, R₃`. -/
theorem U_lt_three : W.U < 3 := fs_U_lt_three W

theorem U_pos : 0 < W.U := by rw [W.U_eq]; have := W.a_pos; positivity

theorem z_pos : 0 < W.z := by linarith [W.one_le_z]
theorem w_pos : 0 < W.w := by linarith [W.one_le_w]
theorem P_pos : 0 < W.P := by linarith [W.one_le_P]
theorem D_pos : 0 < W.D := by linarith [W.one_le_D]

/-- `a² U = 4`. -/
theorem a_sq_U : W.a ^ 2 * W.U = 4 := by
  rw [W.U_eq]; have := W.a_pos; field_simp

/-- `G(a, a x) = a² g(x)`. -/
theorem G_a_mul {x : ℝ} (hx : 0 < x) : ff_G W.a (W.a * x) = W.a ^ 2 * ff_g2 W.U 1 x := by
  have h := ff_G_mul W.a_pos one_pos hx
  rw [mul_one] at h; rw [h, W.U_eq]

/-- **The seven-entry cost bound** without extra copies: `G(a, a) ≥ 0` since `a² > 4/3`. -/
theorem cost_seven : √3 / 4 * (ff_G W.a (W.a * W.P) + ff_G (W.a * W.P) (W.a * W.z) +
    ff_G (W.a * W.z) W.a + ff_G W.a (W.a * W.w) + ff_G (W.a * W.w) (W.a * W.D) +
    ff_G (W.a * W.D) W.a + ff_G W.a W.a) ≤ octagonCost := by
  obtain ⟨n, hn⟩ := W.cost
  have hGa : 0 ≤ ff_G W.a W.a := by
    have := W.G_a_mul one_pos
    rw [mul_one] at this
    rw [this]
    exact mul_nonneg (sq_nonneg _) (ff_g2_one_one_nonneg W.U_pos W.U_lt_three.le)
  refine le_trans ?_ hn
  have h3 : (0 : ℝ) ≤ √3 / 4 := by positivity
  have : (n : ℝ) * ff_G W.a W.a ≥ 0 := mul_nonneg (Nat.cast_nonneg n) hGa
  nlinarith

/-- `L(z, h) ≥ 0` for `z ≥ 1`, `h > 1`. -/
theorem _root_.SmoothedOctagon.ff_L_nonneg {z h : ℝ} (hz : 1 ≤ z) (hh : 1 < h) : 0 ≤ ff_L z h := by
  unfold ff_L
  have h1 : 0 ≤ (z - 1) * ((z - 1) + 2 * z * (h - 1)) / (4 * (1 + z) ^ 2) := by
    apply div_nonneg _ (by positivity)
    apply mul_nonneg (by linarith); nlinarith
  have h2 : 0 ≤ z * h / (1 + z) * (ff_f h / (h - 1)) := by
    apply mul_nonneg (div_nonneg (by nlinarith) (by linarith))
    exact div_nonneg (ff_f_nonneg hh.le) (by linarith)
  linarith

theorem Z_pos : 0 < W.z ^ 2 + W.U := by have := W.U_pos; positivity
theorem W_pos : 0 < W.w ^ 2 + W.U := by have := W.U_pos; positivity

theorem P_lt_U : W.P < W.U := by nlinarith [W.Pz_lt, W.one_le_z, W.P_pos]
theorem D_lt_U : W.D < W.U := by nlinarith [W.wD_lt, W.one_le_w, W.D_pos]

/-- `h Z/S = P + z`. -/
theorem h_mul : ff_hd W.U W.z W.P * (W.z ^ 2 + W.U) / (1 + W.z) = W.P + W.z := by
  have := W.Z_pos; have := W.z_pos; unfold ff_hd; field_simp

/-- `k W/T = w + D`. -/
theorem k_mul : ff_hd W.U W.w W.D * (W.w ^ 2 + W.U) / (1 + W.w) = W.D + W.w := by
  have := W.W_pos; have := W.w_pos; unfold ff_hd; field_simp

/-- `h ≥ S²/Z` (global minimality, `p ≥ a`). -/
theorem h_ge : (1 + W.z) ^ 2 / (W.z ^ 2 + W.U) ≤ ff_hd W.U W.z W.P := by
  unfold ff_hd
  apply div_le_div_of_nonneg_right _ W.Z_pos.le
  nlinarith [W.one_le_P, W.z_pos]

/-- `k ≥ T²/W` (global minimality, `d ≥ a`). -/
theorem k_ge : (1 + W.w) ^ 2 / (W.w ^ 2 + W.U) ≤ ff_hd W.U W.w W.D := by
  unfold ff_hd
  apply div_le_div_of_nonneg_right _ W.W_pos.le
  nlinarith [W.one_le_D, W.w_pos]

/-- `h < S/z` (strict star, `pb < 4`). -/
theorem h_le : ff_hd W.U W.z W.P ≤ (1 + W.z) / W.z := by
  unfold ff_hd
  rw [div_le_div_iff₀ W.Z_pos W.z_pos]
  nlinarith [W.Pz_lt, W.z_pos]

/-- `n ≥ 0`. -/
theorem n_nonneg : 0 ≤ ff_n W.U W.z (ff_hd W.U W.z W.P) := by
  unfold ff_n
  apply div_nonneg _ W.Z_pos.le
  apply mul_nonneg (mul_nonneg (by positivity) (by linarith [W.z_lt])); linarith [W.one_lt_h]

/-- The cost restriction on the left factor: `h ≤ S(5U - 2 - 3w)/(3Z)`, from the budget and
`k ≥ T²/W`. -/
theorem h_le_c (hbud : W.P + W.z + W.w + W.D < (5 * W.U + 1) / 3) :
    ff_hd W.U W.z W.P ≤ (1 + W.z) * (5 * W.U - 2 - 3 * W.w) / (3 * (W.z ^ 2 + W.U)) := by
  have hm := W.h_mul
  have hZ := W.Z_pos
  have hS : 0 < 1 + W.z := by linarith [W.z_pos]
  rw [le_div_iff₀ (by positivity)]
  have : ff_hd W.U W.z W.P * (W.z ^ 2 + W.U) = (W.P + W.z) * (1 + W.z) := by
    rw [← hm]; field_simp
  nlinarith [W.one_le_D]

/-- **The upper threshold** `a² < 20/11`, i.e. `U > 11/5`: otherwise each of the seven edges is at
least `G(a₀, a₀)`, `a₀² = 20/11`, and `(7√3/4) G(a₀, a₀) > A_oct`. -/
theorem eleven_fifths_lt : 11 / 5 < W.U := by
  by_contra hcon
  push Not at hcon
  have h7 := W.cost_seven
  have ha := W.a_pos
  have haU := W.a_sq_U
  have hU := W.U_pos
  set a₀ := √(20 / 11) with ha₀
  have ha0 : a₀ ^ 2 = 20 / 11 := Real.sq_sqrt (by norm_num)
  have ha0p : 0 < a₀ := Real.sqrt_pos.2 (by norm_num)
  have haa : a₀ ≤ W.a := by
    by_contra hc; push Not at hc
    have : W.a ^ 2 < a₀ ^ 2 := by nlinarith
    nlinarith
  have hG0 : ff_G a₀ a₀ = 20 / 11 * (4 / 5 - Real.log (5 / 4)) := by
    have := ff_G_mul ha0p one_pos one_pos
    rw [mul_one] at this
    rw [this, ha0]
    unfold ff_g2
    have e1 : (4 : ℝ) / (20 / 11) = 11 / 5 := by norm_num
    rw [e1]
    have e2 : Real.log ((1 : ℝ) ^ 2 + 11 / 5) = Real.log 4 - Real.log (5 / 4) := by
      rw [← Real.log_div (by norm_num) (by norm_num)]; norm_num
    have e3 : Real.log ((1 : ℝ) + 1) = Real.log 2 := by norm_num
    have e4 : Real.log 4 = 2 * Real.log 2 := by
      rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; push_cast; ring
    rw [e2, e3, e4]
    ring
  have hP := W.P_lt_U
  have hD := W.D_lt_U
  have m1 : ∀ x : ℝ, 1 ≤ x → a₀ ≤ W.a * x := fun x hx ↦ by nlinarith
  have hgt := fun x y (hx : 1 ≤ x) (hy : 1 ≤ y) (hxy : x * y < W.U) ↦
    ff_G_mono ha0p ha0p (m1 x hx) (m1 y hy) (by nlinarith : W.a * x * (W.a * y) ≤ 8)
  have t1 := hgt 1 W.P le_rfl W.one_le_P (by linarith)
  have t2 := hgt W.P W.z W.one_le_P W.one_le_z W.Pz_lt
  have t3 := hgt W.z 1 W.one_le_z le_rfl (by linarith [W.z_lt])
  have t4 := hgt 1 W.w le_rfl W.one_le_w (by linarith [W.w_lt])
  have t5 := hgt W.w W.D W.one_le_w W.one_le_D W.wD_lt
  have t6 := hgt W.D 1 W.one_le_D le_rfl (by linarith)
  have t7 := hgt 1 1 le_rfl le_rfl (by linarith [W.z_lt, W.one_le_z])
  simp only [mul_one] at t1 t3 t4 t6 t7
  have hlog := ff_log_five_fourths_lt
  have hA := ff_octagonCost_lt
  have hs3 : (1.732 : ℝ) < √3 := by rw [Real.lt_sqrt (by norm_num)]; norm_num
  have hsum : 7 * ff_G a₀ a₀ ≤ ff_G W.a (W.a * W.P) + ff_G (W.a * W.P) (W.a * W.z) +
      ff_G (W.a * W.z) W.a + ff_G W.a (W.a * W.w) + ff_G (W.a * W.w) (W.a * W.D) +
      ff_G (W.a * W.D) W.a + ff_G W.a W.a := by linarith
  have hG0' : 23 / 22 ≤ ff_G a₀ a₀ := by rw [hG0]; linarith
  have : √3 / 4 * (7 * ff_G a₀ a₀) ≤ octagonCost :=
    le_trans (mul_le_mul_of_nonneg_left hsum (by positivity)) h7
  nlinarith

/-- **The exterior-factor budget**: `P + z + w + D < (5U + 1)/3`. Otherwise the seven-entry cost
bound, the rectangle inequality and `ff_budget_g` give a cost above `A_oct`. -/
theorem budget : W.P + W.z + W.w + W.D < (5 * W.U + 1) / 3 := by
  by_contra hcon
  push Not at hcon
  have hU3 := W.U_lt_three
  have hU1 := W.eleven_fifths_lt
  have h7 := W.cost_seven
  have ha := W.a_pos
  have le1 : ∀ x : ℝ, 1 ≤ x → W.a ≤ W.a * x := fun x hx ↦ by nlinarith
  have r1 := ff_G_rect ha (le1 _ W.one_le_P) (le1 _ W.one_le_z)
  have r2 := ff_G_rect ha (le1 _ W.one_le_w) (le1 _ W.one_le_D)
  rw [ff_G_comm' (W.a * W.P) W.a] at r1
  rw [ff_G_comm' (W.a * W.w) W.a] at r2
  rw [ff_G_comm' (W.a * W.z) W.a, ff_G_comm' (W.a * W.D) W.a] at h7
  have hb := ff_budget_g hU1 hU3 W.one_le_P W.P_lt_U.le W.one_le_z W.z_lt.le W.one_le_w W.w_lt.le
    W.one_le_D W.D_lt_U.le hcon
  have g1 := W.G_a_mul one_pos
  rw [mul_one] at g1
  rw [W.G_a_mul W.P_pos, W.G_a_mul W.z_pos, W.G_a_mul W.w_pos, W.G_a_mul W.D_pos, g1] at h7
  rw [W.G_a_mul W.P_pos, W.G_a_mul W.z_pos, g1] at r1
  rw [W.G_a_mul W.w_pos, W.G_a_mul W.D_pos, g1] at r2
  have e : √3 / W.U = √3 / 4 * W.a ^ 2 := by
    have := W.a_sq_U; have := W.U_pos
    field_simp; linarith
  rw [e] at hb
  have h3 : (0 : ℝ) ≤ √3 / 4 := by positivity
  have key : √3 / 4 * (W.a ^ 2 * (2 * ff_g2 W.U 1 W.P + 2 * ff_g2 W.U 1 W.z + 2 * ff_g2 W.U 1 W.w +
      2 * ff_g2 W.U 1 W.D - ff_g2 W.U 1 1)) ≤ octagonCost := by
    refine le_trans (mul_le_mul_of_nonneg_left ?_ h3) h7
    nlinarith
  nlinarith

/-- **The neighbour bound**: with `z ≤ w`, `w < 4/3`. Otherwise the left row and the floors give a
nonnegative neighbour residual, against `ff_resN_neg`. -/
theorem neighbor (hzw : W.z ≤ W.w) : W.w < 4 / 3 := by
  by_contra hcon
  push Not at hcon
  have hU3 := W.U_lt_three
  have hU1 := W.eleven_fifths_lt
  have hbud := W.budget
  have hU := W.U_pos
  have hW := W.W_pos
  have hI1 : 1 < (1 + W.w) ^ 2 / (W.w ^ 2 + W.U) := by
    rw [lt_div_iff₀ hW]; nlinarith
  have hx : 1 / 2 ≤ W.w / (1 + W.w) := by
    rw [le_div_iff₀ (by linarith [W.w_pos])]; linarith [W.one_le_w]
  have hfr := le_trans (ff_F_mono hx hI1 W.k_ge) W.floorR
  have hfl := W.floorL
  have hn := W.n_nonneg
  have hm : 0 ≤ ff_m W.U W.z W.w (ff_hd W.U W.z W.P) := by
    have := ff_m_sub_n_pos hU hU3 W.one_le_z hzw W.one_lt_h.le; linarith
  have hrow := W.rowL
  have hres : 0 ≤ ff_resN W.U W.z W.w (ff_hd W.U W.z W.P) := by
    unfold ff_resN
    have := mul_le_mul_of_nonneg_left hfl hn
    have := mul_le_mul_of_nonneg_left hfr hm
    linarith
  have hzw' : W.z + W.w ≤ 5 * (W.U - 1) / 3 := by linarith [W.one_le_P, W.one_le_D]
  have := ff_resN_neg hU1.le hU3 W.one_le_z hzw hcon hzw' W.one_lt_h W.h_ge W.h_le (W.h_le_c hbud)
  linarith

/-- **The two norm bounds**: with `z ≤ w`, `δu + δv < 1/35` and `δv < 1/64`. Otherwise the centered
row and the floors make the sum or the larger-norm residual nonnegative, against `ff_resS_neg` and
`ff_resV_neg` after the reductions to equal neighbours. -/
theorem norms (hzw : W.z ≤ W.w) : (W.u - 3 / 4) + (W.v - 3 / 4) < 1 / 35 ∧ W.v - 3 / 4 < 1 / 64 := by
  have hU3 := W.U_lt_three
  have hU1 := W.eleven_fifths_lt
  have hbud := W.budget
  have hw := W.neighbor hzw
  have hU := W.U_pos
  have hW := W.W_pos
  set h := ff_hd W.U W.z W.P with hh
  set I := (1 + W.w) ^ 2 / (W.w ^ 2 + W.U) with hI
  have hI1 : 1 < I := by
    rw [hI, lt_div_iff₀ hW]; nlinarith [W.one_le_w]
  have hx : 1 / 2 ≤ W.w / (1 + W.w) := by
    rw [le_div_iff₀ (by linarith [W.w_pos])]; linarith [W.one_le_w]
  have hrow : ff_n W.U W.z h * (W.u - 3 / 4) + ff_m W.U W.z W.w h * (W.v - 3 / 4) =
      ff_r W.U W.z W.w h := by
    have h1 := W.rowL
    have h2 := ff_r_eq hU W.z_pos W.w_pos (by linarith [W.one_lt_h] : 0 < h)
    linarith
  have hu : ff_L W.z h ≤ W.u - 3 / 4 := by
    have := W.floorL
    rw [ff_F_eq_L W.z_pos W.one_lt_h.ne' (by linarith [W.one_lt_h])] at this
    linarith
  have hv : ff_L W.w I ≤ W.v - 3 / 4 := by
    have := le_trans (ff_F_mono hx hI1 W.k_ge) W.floorR
    rw [ff_F_eq_L W.w_pos hI1.ne' (by linarith)] at this
    linarith
  have hn := W.n_nonneg
  have hmn := ff_m_sub_n_pos hU hU3 W.one_le_z hzw W.one_lt_h.le
  have hhl := W.h_ge
  have hhc : h ≤ (1 + W.z) * (5 * W.U - 2 - 3 * W.z) / (3 * (W.z ^ 2 + W.U)) := by
    refine le_trans (W.h_le_c hbud) ?_
    apply div_le_div_of_nonneg_right _ (by positivity)
    apply mul_le_mul_of_nonneg_left _ (by linarith [W.z_pos])
    linarith
  have hU6 : 1 + 6 * W.z / 5 ≤ W.U := by
    have hZ := W.Z_pos
    have := le_trans hhl hhc
    rw [div_le_div_iff₀ hZ (by positivity)] at this
    have hS : 0 < 1 + W.z := by linarith [W.z_pos]
    have hprod : 0 < (1 + W.z) * (W.z ^ 2 + W.U) := by positivity
    have key : (1 + W.z) * (W.z ^ 2 + W.U) * (3 * (1 + W.z)) ≤
        (1 + W.z) * (W.z ^ 2 + W.U) * (5 * W.U - 2 - 3 * W.z) := by
      calc _ = (1 + W.z) ^ 2 * (3 * (W.z ^ 2 + W.U)) := by ring
        _ ≤ _ := this
        _ = _ := by ring
    have := le_of_mul_le_mul_left key hprod
    linarith
  have hz43 : W.z ≤ 4 / 3 := by linarith
  constructor
  · by_contra hc
    push Not at hc
    have hres : 0 ≤ ff_resS W.U W.z W.w h := by
      unfold ff_resS
      rw [← hI]
      have e : ff_r W.U W.z W.w h = ff_n W.U W.z h * ((W.u - 3 / 4) + (W.v - 3 / 4)) +
          (ff_m W.U W.z W.w h - ff_n W.U W.z h) * (W.v - 3 / 4) := by rw [← hrow]; ring
      rw [e]
      have := mul_le_mul_of_nonneg_left hc hn
      have := mul_le_mul_of_nonneg_left hv hmn.le
      linarith
    have h1 := ff_resS_le_sym hU1.le hU3 W.one_le_z hzw hw.le W.one_lt_h
    have h2 := ff_resS_neg W.one_le_z hz43 hU6 hU3 hhl hhc
    linarith
  · by_contra hc
    push Not at hc
    have hm : 0 ≤ ff_m W.U W.z W.w h := by linarith
    have hres : 0 ≤ ff_resV W.U W.z W.w h := by
      unfold ff_resV
      rw [← hrow]
      have := mul_le_mul_of_nonneg_left hu hn
      have := mul_le_mul_of_nonneg_left hc hm
      linarith
    have h1 := ff_resV_le_sym hU1.le hU3 W.one_le_z hzw hw.le W.one_lt_h
    have h2 := ff_resV_neg W.one_le_z hz43 hU6 hU3 hhl hhc
    linarith

/-- The norm increments are nonnegative: `u, v ≥ 3/4`. -/
theorem norms_nonneg : 0 ≤ W.u - 3 / 4 ∧ 0 ≤ W.v - 3 / 4 := by
  have hl := ff_L_nonneg W.one_le_z W.one_lt_h
  have hl' := ff_L_nonneg W.one_le_w W.one_lt_k
  have hu := W.floorL
  have hv := W.floorR
  rw [ff_F_eq_L W.z_pos W.one_lt_h.ne' (by linarith [W.one_lt_h])] at hu
  rw [ff_F_eq_L W.w_pos W.one_lt_k.ne' (by linarith [W.one_lt_k])] at hv
  constructor <;> linarith

theorem false_of_le (hzw : W.z ≤ W.w) : False := by
  have hU3 := W.U_lt_three
  have hU1 := W.eleven_fifths_lt
  have hbud := W.budget
  have hw := W.neighbor hzw
  obtain ⟨hS, hV⟩ := W.norms hzw
  obtain ⟨hu0, hv0⟩ := W.norms_nonneg
  have hzw' : W.z + W.w ≤ 5 * (W.U - 1) / 3 := by linarith [W.one_le_P, W.one_le_D]
  have hE : W.E = ff_e0 W.U - ff_Phi W.U W.z W.w + (1 + W.z) * (W.u - 3 / 4) +
      (1 + W.w) * (W.v - 3 / 4) := by
    have h0 := W.row0
    have hA := ff_A_eq W.U_pos W.z_pos W.w_pos
    linarith
  have hcas := ff_casimir_lower hU1.le hU3 W.one_le_z hzw hw.le hzw' hu0 hv0 hS.le hV.le hE
  have hcap := W.cap
  rw [show (3 / 4 : ℝ) + (W.u - 3 / 4) = W.u by ring,
    show (3 / 4 : ℝ) + (W.v - 3 / 4) = W.v by ring] at hcas
  linarith

/-- **The scalar exclusion**: no window exists. -/
theorem elim (W : ff_Dim) : False := by
  rcases le_total W.z W.w with h | h
  · exact W.false_of_le h
  · exact W.swap.false_of_le h

end ff_Dim

/-! ### From the physical window -/

theorem ff_fac_comm (x y z : ℝ) : ff_fac x y z = ff_fac z y x := by unfold ff_fac; ring

theorem ff_Cph_comm (x y z : ℝ) : ff_Cph x y z = ff_Cph z y x := by
  unfold ff_Cph; rw [ff_fac_comm]; ring

theorem ff_hd_eq {a b p : ℝ} (ha : 0 < a) : ff_hd (4 / a ^ 2) (b / a) (p / a) = ff_fac p b a := by
  have hK : 0 < b ^ 2 + 4 := by positivity
  unfold ff_hd ff_fac; field_simp; ring

theorem ff_q_eq_fac {a b c : ℝ} (ha : 0 < a) : ff_q (4 / a ^ 2) (b / a) (c / a) = ff_fac b a c := by
  have hK : 0 < a ^ 2 + 4 := by positivity
  unfold ff_q ff_fac; field_simp; ring

theorem ff_A_phys {a b c : ℝ} (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    a * ff_A (4 / a ^ 2) (b / a) (c / a) = ff_Cph b a c := by
  unfold ff_A ff_Cph
  rw [ff_q_eq_fac ha]
  generalize Real.log (ff_fac b a c) = L
  have hab : 0 < a + b := by linarith
  have hac : 0 < a + c := by linarith
  have hK : 0 < a ^ 2 + 4 := by positivity
  field_simp; ring

theorem ff_B_phys {a p b : ℝ} (ha : 0 < a) (hp : 0 < p) (hb : 0 < b) :
    a * ff_B (4 / a ^ 2) (b / a) (ff_fac p b a) = ff_Cph p b a := by
  unfold ff_B ff_Cph
  generalize hL : Real.log (ff_fac p b a) = L
  unfold ff_fac
  have hab : 0 < a + b := by linarith
  have hpb : 0 < p + b := by linarith
  have hK : 0 < b ^ 2 + 4 := by positivity
  field_simp; ring

theorem ff_n_phys {a b h : ℝ} (ha : 0 < a) (hb : 0 < b) :
    a * ff_n (4 / a ^ 2) (b / a) h = ff_Mn a b h := by
  have hK : 0 < b ^ 2 + 4 := by positivity
  unfold ff_n ff_Mn; field_simp

theorem ff_m_phys {a b c h : ℝ} (ha : 0 < a) (hb : 0 < b) :
    a * ff_m (4 / a ^ 2) (b / a) (c / a) h = ff_Mm a b (ff_fac b a c) h := by
  have hK : 0 < b ^ 2 + 4 := by positivity
  have hab : 0 < a + b := by linarith
  unfold ff_m ff_Mm
  rw [ff_q_eq_fac ha]
  generalize ff_fac b a c = q
  field_simp

theorem ff_alpha_phys {a b h : ℝ} (ha : 0 < a) (hb : 0 < b) :
    ff_alpha (4 / a ^ 2) (b / a) h = ff_Mal a b h := by
  have hK : 0 < b ^ 2 + 4 := by positivity
  unfold ff_alpha ff_Mal; field_simp

namespace ff_Win

variable (W : ff_Win)

theorem b_pos : 0 < W.b := lt_of_lt_of_le W.a_pos W.a_le_b
theorem c_pos : 0 < W.c := lt_of_lt_of_le W.a_pos W.a_le_c
theorem p_pos : 0 < W.p := lt_of_lt_of_le W.a_pos W.a_le_p
theorem d_pos : 0 < W.d := lt_of_lt_of_le W.a_pos W.a_le_d

/-- The dimensionless form of the window. -/
noncomputable def toDim : ff_Dim where
  a := W.a
  U := 4 / W.a ^ 2
  z := W.b / W.a
  w := W.c / W.a
  P := W.p / W.a
  D := W.d / W.a
  u := W.u
  v := W.v
  E := W.E
  a_pos := W.a_pos
  U_eq := rfl
  one_le_z := (one_le_div W.a_pos).2 W.a_le_b
  one_le_w := (one_le_div W.a_pos).2 W.a_le_c
  one_le_P := (one_le_div W.a_pos).2 W.a_le_p
  one_le_D := (one_le_div W.a_pos).2 W.a_le_d
  Pz_lt := by
    have := W.a_pos
    rw [div_mul_div_comm, ← sq]; exact div_lt_div_of_pos_right W.pb_lt (by positivity)
  z_lt := by
    have := W.a_pos; have := W.ab_lt
    rw [div_lt_div_iff₀ W.a_pos (by positivity)]; nlinarith
  w_lt := by
    have := W.a_pos; have := W.ac_lt
    rw [div_lt_div_iff₀ W.a_pos (by positivity)]; nlinarith
  wD_lt := by
    have := W.a_pos
    rw [div_mul_div_comm, ← sq]; exact div_lt_div_of_pos_right W.cd_lt (by positivity)
  one_lt_h := by rw [ff_hd_eq W.a_pos]; exact W.one_lt_h
  one_lt_q := by rw [ff_q_eq_fac W.a_pos]; exact W.one_lt_q
  one_lt_k := by rw [ff_hd_eq W.a_pos, ff_fac_comm]; exact W.one_lt_k
  row0 := by
    have h := W.row0
    rw [← ff_A_phys W.a_pos W.b_pos W.c_pos] at h
    have ha := W.a_pos
    refine mul_left_cancel₀ ha.ne' ?_
    have e1 : W.a + W.b = W.a * (1 + W.b / W.a) := by field_simp
    have e2 : W.a + W.c = W.a * (1 + W.c / W.a) := by field_simp
    rw [e1, e2] at h
    linear_combination h
  rowL := by
    have h := W.rowL
    rw [ff_hd_eq W.a_pos, ff_alpha_phys W.a_pos W.b_pos]
    rw [← ff_n_phys W.a_pos W.b_pos, ← ff_m_phys W.a_pos W.b_pos,
      ← ff_A_phys W.a_pos W.b_pos W.c_pos, ← ff_B_phys W.a_pos W.p_pos W.b_pos] at h
    refine mul_left_cancel₀ W.a_pos.ne' ?_
    linear_combination h
  rowR := by
    have h := W.rowR
    rw [ff_hd_eq W.a_pos, ff_alpha_phys W.a_pos W.c_pos]
    rw [ff_Cph_comm W.a W.c W.d, ff_fac_comm W.a W.c W.d, ff_fac_comm W.b W.a W.c,
      ← ff_n_phys W.a_pos W.c_pos, ← ff_m_phys W.a_pos W.c_pos,
      ← ff_A_phys W.a_pos W.b_pos W.c_pos, ← ff_B_phys W.a_pos W.d_pos W.c_pos] at h
    refine mul_left_cancel₀ W.a_pos.ne' ?_
    linear_combination h
  floorL := by
    have h := W.floorL
    rw [ff_hd_eq W.a_pos]
    have e : W.b / W.a / (1 + W.b / W.a) = W.b / (W.a + W.b) := by
      have := W.a_pos; have := W.b_pos; field_simp
    rw [e]; exact h
  floorR := by
    have h := W.floorR
    rw [ff_hd_eq W.a_pos, ff_fac_comm]
    have e : W.c / W.a / (1 + W.c / W.a) = W.c / (W.a + W.c) := by
      have := W.a_pos; have := W.c_pos; field_simp
    rw [e]; exact h
  cost := by
    have ha := W.a_pos.ne'
    simp only [mul_div_cancel₀ _ ha]
    exact W.cost
  cap := by
    have h := W.cap
    have ha := W.a_pos
    unfold ff_cas
    have e : (1 + 4 / W.a ^ 2) ^ 2 * (4 * W.u * W.v - W.E ^ 2) / (16 * (4 / W.a ^ 2) ^ 2) =
        (W.a ^ 2 + 4) ^ 2 * (4 * W.u * W.v - W.E ^ 2) / 256 := by
      field_simp; ring
    rw [e]; exact h

theorem elim (W : ff_Win) : False := W.toDim.elim

end ff_Win

end SmoothedOctagon
