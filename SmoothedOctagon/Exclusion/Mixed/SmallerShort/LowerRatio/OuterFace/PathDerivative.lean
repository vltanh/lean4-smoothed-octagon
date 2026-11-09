module

public import SmoothedOctagon.Exclusion.Mixed.SmallerShort.LowerRatio.OuterFace.Functions
public import SmoothedOctagon.Exclusion.Mixed.SmallerShort.LowerRatio.CentralFace.PathDerivative

/-!
# Smaller-short window, lower ratio, outer face: partial derivatives and the derivative along a path

At fixed `x`, for a path `t ↦ (α(t), β(t), u(t))`, the outer tests have the derivative
`F' = α'(Γ_α - cR_α) + β'(-cR_β) + u'(Γ_u - cR_u) + cε(y)(log y)'` with the transport-form partials
below (logarithm form) and the cubic correction `ε` (`lreps`).

## Main API

* partials `lroLa`, `lroda`, `lrodb`, `lrova`, `lroEa`, `lrowa`, `lrowb`, `lrowu`, `lroELa`,
  `lroR2a`, `lroR2b`, `lroR2u`, `lroTa`, `lroTb`, `lroR1a`, `lroR1b`, `lroR1u`, `lroGa`, `lroGu`;
* `lro_F0_hasDerivAt`, `lro_F1_hasDerivAt`.
-/

@[expose] public section

namespace SmoothedOctagon

noncomputable def lroLa (a : ℝ) : ℝ := -2 / (7 * a ^ 3)
noncomputable def lroda (x a b : ℝ) : ℝ := 2 * (a + b) / (7 * a ^ 2) - 2 * lrod x a b / a
noncomputable def lrodb (x a : ℝ) : ℝ := 2 * (a - x) / (7 * a ^ 2)
noncomputable def lrova (x a : ℝ) : ℝ :=
  (1 + x) * (12 * a) / lroK a ^ 2 - 2 * (1 + x) ^ 2 * (12 * a) / lroK a ^ 3
noncomputable def lroEa (x a : ℝ) : ℝ := -(2 * (1 + x) - 1) * (12 * a) / lroK a ^ 2
noncomputable def lrowa (x a b u : ℝ) : ℝ :=
  2 * lroL a * lroLa a * lrov x a + lroL a ^ 2 * lrova x a + 2 * lrod x a b * lroda x a b * u -
    (lroda x a b * lroL a + lrod x a b * lroLa a) * lroE x a u - lrod x a b * lroL a * lroEa x a
noncomputable def lrowb (x a b u : ℝ) : ℝ :=
  2 * lrod x a b * lrodb x a * u - lrodb x a * lroL a * lroE x a u
noncomputable def lrowu (x a b : ℝ) : ℝ := lrod x a b ^ 2 - lrod x a b * lroL a * (1 + x)
noncomputable def lroELa (x a b u : ℝ) : ℝ :=
  2 * lroda x a b * u - lroLa a * lroE x a u - lroL a * lroEa x a
noncomputable def lroR2a (x a b u : ℝ) : ℝ :=
  2 * lrowa x a b u - lroELa x a b u - (u - 1) * b / a ^ 2 + b / (a + b) ^ 2 +
    (1 / (a + b) - 1 / a)
noncomputable def lroR2b (x a b u : ℝ) : ℝ :=
  2 * lrowb x a b u - 2 * lrodb x a * u + (u - 1) / a - a / (a + b) ^ 2 + 1 / (a + b)
noncomputable def lroR2u (x a b : ℝ) : ℝ :=
  2 * lrowu x a b + (a + b) / a - (2 * lrod x a b - lroL a * (1 + x))
noncomputable def lroTa (a b : ℝ) : ℝ := 7 * b / (a + b) ^ 2
noncomputable def lroTb (a b : ℝ) : ℝ := -(7 * a) / (a + b) ^ 2
noncomputable def lroR1a (x a b u : ℝ) : ℝ :=
  lroR2a x a b u + lroTa a b * (lrow x a b u - 3 / 4) + (lroT a b - 2) * lrowa x a b u
noncomputable def lroR1b (x a b u : ℝ) : ℝ :=
  lroR2b x a b u + lroTb a b * (lrow x a b u - 3 / 4) + (lroT a b - 2) * lrowb x a b u
noncomputable def lroR1u (x a b : ℝ) : ℝ := lroR2u x a b + (lroT a b - 2) * lrowu x a b
noncomputable def lroGa (x a u : ℝ) : ℝ :=
  (4 * u * lrova x a - 2 * lroE x a u * lroEa x a) * lroK a ^ 2 / (576 * a ^ 4) +
    (4 * u * lrov x a - lroE x a u ^ 2) *
      (24 * a * lroK a / (576 * a ^ 4) - 4 * lroK a ^ 2 / (576 * a ^ 5))
noncomputable def lroGu (x a u : ℝ) : ℝ :=
  (4 * lrov x a - 2 * (1 + x) * lroE x a u) * lroK a ^ 2 / (576 * a ^ 4)

theorem lro_K_hasDerivAt {A : ℝ → ℝ} {a' t : ℝ} (hA : HasDerivAt A a' t) :
    HasDerivAt (fun s => lroK (A s)) (12 * A t * a') t := by
  unfold lroK
  have := ((hA.fun_pow 2).const_mul 6).add_const 1
  convert this using 1; push_cast; ring

theorem lro_L_hasDerivAt {A : ℝ → ℝ} {a' t : ℝ} (hA : HasDerivAt A a' t) (ha : 0 < A t) :
    HasDerivAt (fun s => lroL (A s)) (lroLa (A t) * a') t := by
  have h0 : 7 * A t ^ 2 ≠ 0 := by positivity
  have := (lro_K_hasDerivAt hA).fun_div ((hA.fun_pow 2).const_mul 7) h0
  unfold lroL
  convert this using 1
  simp only [lroLa, lroK]
  have ha0 : A t ≠ 0 := ha.ne'
  push_cast
  field_simp
  ring

theorem lro_d_hasDerivAt {A B : ℝ → ℝ} {x a' b' t : ℝ} (hA : HasDerivAt A a' t)
    (hB : HasDerivAt B b' t) (ha : 0 < A t) :
    HasDerivAt (fun s => lrod x (A s) (B s)) (lroda x (A t) (B t) * a' + lrodb x (A t) * b') t := by
  have h0 : 7 * A t ^ 2 ≠ 0 := by positivity
  have hD : HasDerivAt (fun s => ssDg x (B s) (A s))
      (2 * A t * a' + 2 * (a' * B t + A t * b') - 2 * (b' * x)) t := by
    have := ((((hA.fun_pow 2).add ((hA.fun_mul hB).const_mul 2)).add_const 1).add_const (2 * x)).sub
      (hB.const_mul (2 * x))
    unfold ssDg
    convert this using 1
    · funext s; simp only [Pi.add_apply, Pi.sub_apply]; ring
    · push_cast; ring
  have := hD.fun_div ((hA.fun_pow 2).const_mul 7) h0
  unfold lrod
  convert this using 1
  simp only [lroda, lrodb, lrod]
  have ha0 : A t ≠ 0 := ha.ne'
  push_cast
  field_simp
  ring

theorem lro_v_hasDerivAt {A : ℝ → ℝ} {x a' t : ℝ} (hA : HasDerivAt A a' t) :
    HasDerivAt (fun s => lrov x (A s)) (lrova x (A t) * a') t := by
  have hK := lro_K_hasDerivAt hA
  have hK0 : lroK (A t) ≠ 0 := by unfold lroK; positivity
  have h1 := (hasDerivAt_const t (1 + x)).fun_div hK hK0
  have := ((h1.const_sub 1).add (h1.fun_pow 2))
  unfold lrov
  convert this using 1
  simp only [lrova]
  push_cast
  field_simp
  ring

theorem lro_E_hasDerivAt {A U : ℝ → ℝ} {x a' u' t : ℝ} (hA : HasDerivAt A a' t)
    (hU : HasDerivAt U u' t) :
    HasDerivAt (fun s => lroE x (A s) (U s)) (lroEa x (A t) * a' + (1 + x) * u') t := by
  have hK := lro_K_hasDerivAt hA
  have hK0 : lroK (A t) ≠ 0 := by unfold lroK; positivity
  have h1 := (hasDerivAt_const t (2 * (1 + x) - 1)).fun_div hK hK0
  have := (((hU.sub_const 1).const_mul (1 + x)).add_const (1 / (1 + x))).add h1
  unfold lroE
  convert this using 1
  simp only [lroEa]
  field_simp
  ring

theorem lro_y_hasDerivAt {A B : ℝ → ℝ} {a' b' t : ℝ} (hA : HasDerivAt A a' t)
    (hB : HasDerivAt B b' t) (ha : 0 < A t) (hb : 0 < B t) :
    HasDerivAt (fun s => lroy (A s) (B s))
      (lroy (A t) (B t) * ((1 / (A t + B t) - 1 / A t) * a' + 1 / (A t + B t) * b')) t := by
  have h0 : 7 * A t ≠ 0 := by positivity
  have := ((hA.add hB).const_mul 2).fun_div (hA.const_mul 7) h0
  unfold lroy
  convert this using 1
  simp only [Pi.add_apply]
  have hab : A t + B t ≠ 0 := by positivity
  have ha0 : A t ≠ 0 := ha.ne'
  field_simp
  ring

theorem lro_G_hasDerivAt {A U : ℝ → ℝ} {x a' u' t : ℝ} (hA : HasDerivAt A a' t)
    (hU : HasDerivAt U u' t) (ha : 0 < A t) :
    HasDerivAt (fun s => lroG x (A s) (U s)) (lroGa x (A t) (U t) * a' + lroGu x (A t) (U t) * u') t := by
  have hv := lro_v_hasDerivAt (x := x) hA
  have hE := lro_E_hasDerivAt (x := x) hA hU
  have hK := lro_K_hasDerivAt hA
  have h0 : 576 * A t ^ 4 ≠ 0 := by positivity
  have := ((((hU.const_mul 4).fun_mul hv).sub (hE.fun_pow 2)).fun_mul (hK.fun_pow 2)).fun_div
    ((hA.fun_pow 4).const_mul 576) h0
  unfold lroG
  convert this using 1
  simp only [lroGa, lroGu, Pi.sub_apply]
  have ha0 : A t ≠ 0 := ha.ne'
  norm_num
  field_simp
  ring

/-- **The derivative of the outer `F₀` along a path at fixed `x`**. -/
theorem lro_F0_hasDerivAt {A B U : ℝ → ℝ} {x a' b' u' t : ℝ} (hA : HasDerivAt A a' t)
    (hB : HasDerivAt B b' t) (hU : HasDerivAt U u' t) (ha : 0 < A t) (hb : 0 < B t) :
    HasDerivAt (fun s => lroF0 x (A s) (B s) (U s))
      (a' * (lroGa x (A t) (U t) - 7 / 96 * lroR2a x (A t) (B t) (U t)) +
        b' * (-(7 / 96) * lroR2b x (A t) (B t) (U t)) +
        u' * (lroGu x (A t) (U t) - 7 / 96 * lroR2u x (A t) (B t)) +
        7 / 96 * lreps (lroy (A t) (B t)) *
          ((1 / (A t + B t) - 1 / A t) * a' + 1 / (A t + B t) * b')) t := by
  have hL := lro_L_hasDerivAt hA ha
  have hd := lro_d_hasDerivAt (x := x) hA hB ha
  have hv := lro_v_hasDerivAt (x := x) hA
  have hE := lro_E_hasDerivAt (x := x) hA hU
  have hy := lro_y_hasDerivAt hA hB ha hb
  have hG := lro_G_hasDerivAt (x := x) hA hU ha
  have hy0 : 0 < lroy (A t) (B t) := by unfold lroy; positivity
  have hl := (lr_ell_hasDerivAt hy0).comp t hy
  have hw := (((hL.fun_pow 2).fun_mul hv).add ((hd.fun_pow 2).fun_mul hU)).sub
    ((hd.fun_mul hL).fun_mul hE)
  have hEL := ((hd.const_mul 2).fun_mul hU).sub (hL.fun_mul hE)
  have hab : HasDerivAt (fun s => A s + B s) (a' + b') t := hA.add hB
  have hab0 : A t + B t ≠ 0 := by positivity
  have h1 := ((hU.sub_const 1).fun_mul hab).fun_div hA ha.ne'
  have h2 := hA.fun_div hab hab0
  have hR := ((((((hw.const_mul 2).sub_const (1 / 2)).add h1).add h2).sub_const (1 / 7)).sub hEL).add hl
  have hF := (hG.sub (hR.const_mul (7 / 96))).sub_const (9193 / 50000)
  unfold lroF0 lroR2 lrow lroEL
  convert hF using 1
  · funext s; simp only [Pi.add_apply, Pi.sub_apply, Function.comp_apply]
  simp only [lroR2a, lrowa, lroELa, lroR2b, lrowb, lroR2u, lrowu]
  norm_num
  have ha0 : A t ≠ 0 := ha.ne'
  have hy1 : lroy (A t) (B t) ≠ 0 := hy0.ne'
  field_simp
  ring

/-- **The derivative of the outer `F₁` along a path at fixed `x`**. -/
theorem lro_F1_hasDerivAt {A B U : ℝ → ℝ} {x a' b' u' t : ℝ} (hA : HasDerivAt A a' t)
    (hB : HasDerivAt B b' t) (hU : HasDerivAt U u' t) (ha : 0 < A t) (hb : 0 < B t) :
    HasDerivAt (fun s => lroF1 x (A s) (B s) (U s))
      (a' * (lroGa x (A t) (U t) - 7 / 96 * lroR1a x (A t) (B t) (U t)) +
        b' * (-(7 / 96) * lroR1b x (A t) (B t) (U t)) +
        u' * (lroGu x (A t) (U t) - 7 / 96 * lroR1u x (A t) (B t)) +
        7 / 96 * lreps (lroy (A t) (B t)) *
          ((1 / (A t + B t) - 1 / A t) * a' + 1 / (A t + B t) * b')) t := by
  have hF0 := lro_F0_hasDerivAt (x := x) hA hB hU ha hb
  have hL := lro_L_hasDerivAt hA ha
  have hd := lro_d_hasDerivAt (x := x) hA hB ha
  have hv := lro_v_hasDerivAt (x := x) hA
  have hE := lro_E_hasDerivAt (x := x) hA hU
  have hw := (((hL.fun_pow 2).fun_mul hv).add ((hd.fun_pow 2).fun_mul hU)).sub
    ((hd.fun_mul hL).fun_mul hE)
  have hab0 : A t + B t ≠ 0 := by positivity
  have hT := (hA.const_mul 7).fun_div (hA.add hB) hab0
  have hF := hF0.sub (((hT.sub_const 2).fun_mul (hw.sub_const (3 / 4))).const_mul (7 / 96))
  unfold lroF1 lroT lrow
  convert hF using 1
  · funext s; simp only [Pi.add_apply, Pi.sub_apply]; ring
  simp only [lroR1a, lroR1b, lroR1u, lrowa, lrowb, lrowu, lroTa, lroTb, lroT, lrow,
    Pi.add_apply, Pi.sub_apply]
  norm_num
  have ha0 : A t ≠ 0 := ha.ne'
  field_simp
  ring

end SmoothedOctagon
