module

public import SmoothedOctagon.Exclusion.Mixed.ShortHand.Heavy.S1ODefs
public import SmoothedOctagon.Exclusion.Mixed.ShortHand.Heavy.S1CDeriv

/-!
# Gate S1, outer face: partial derivatives and the derivative along a path

At fixed `x`, for a path `t ↦ (α(t), β(t), u(t))`, the outer tests have the derivative
`F' = α'(Γ_α - cR_α) + β'(-cR_β) + u'(Γ_u - cR_u) + cε(y)(log y)'` with the transport-form partials
below (logarithm form) and the cubic correction `ε` (`hh1eps`).

## Main API

* partials `hh1oLa`, `hh1oda`, `hh1odb`, `hh1ova`, `hh1oEa`, `hh1owa`, `hh1owb`, `hh1owu`, `hh1oELa`,
  `hh1oR2a`, `hh1oR2b`, `hh1oR2u`, `hh1oTa`, `hh1oTb`, `hh1oR1a`, `hh1oR1b`, `hh1oR1u`, `hh1oGa`, `hh1oGu`;
* `hh1o_F0_hasDerivAt`, `hh1o_F1_hasDerivAt`.
-/

@[expose] public section

namespace SmoothedOctagon

noncomputable def hh1oLa (a : ℝ) : ℝ := -2 / (7 * a ^ 3)
noncomputable def hh1oda (x a b : ℝ) : ℝ := 2 * (a + b) / (7 * a ^ 2) - 2 * hh1od x a b / a
noncomputable def hh1odb (x a : ℝ) : ℝ := 2 * (a - x) / (7 * a ^ 2)
noncomputable def hh1ova (x a : ℝ) : ℝ :=
  (1 + x) * (12 * a) / hh1oK a ^ 2 - 2 * (1 + x) ^ 2 * (12 * a) / hh1oK a ^ 3
noncomputable def hh1oEa (x a : ℝ) : ℝ := -(2 * (1 + x) - 1) * (12 * a) / hh1oK a ^ 2
noncomputable def hh1owa (x a b u : ℝ) : ℝ :=
  2 * hh1oL a * hh1oLa a * hh1ov x a + hh1oL a ^ 2 * hh1ova x a + 2 * hh1od x a b * hh1oda x a b * u -
    (hh1oda x a b * hh1oL a + hh1od x a b * hh1oLa a) * hh1oE x a u - hh1od x a b * hh1oL a * hh1oEa x a
noncomputable def hh1owb (x a b u : ℝ) : ℝ :=
  2 * hh1od x a b * hh1odb x a * u - hh1odb x a * hh1oL a * hh1oE x a u
noncomputable def hh1owu (x a b : ℝ) : ℝ := hh1od x a b ^ 2 - hh1od x a b * hh1oL a * (1 + x)
noncomputable def hh1oELa (x a b u : ℝ) : ℝ :=
  2 * hh1oda x a b * u - hh1oLa a * hh1oE x a u - hh1oL a * hh1oEa x a
noncomputable def hh1oR2a (x a b u : ℝ) : ℝ :=
  2 * hh1owa x a b u - hh1oELa x a b u - (u - 1) * b / a ^ 2 + b / (a + b) ^ 2 +
    (1 / (a + b) - 1 / a)
noncomputable def hh1oR2b (x a b u : ℝ) : ℝ :=
  2 * hh1owb x a b u - 2 * hh1odb x a * u + (u - 1) / a - a / (a + b) ^ 2 + 1 / (a + b)
noncomputable def hh1oR2u (x a b : ℝ) : ℝ :=
  2 * hh1owu x a b + (a + b) / a - (2 * hh1od x a b - hh1oL a * (1 + x))
noncomputable def hh1oTa (a b : ℝ) : ℝ := 7 * b / (a + b) ^ 2
noncomputable def hh1oTb (a b : ℝ) : ℝ := -(7 * a) / (a + b) ^ 2
noncomputable def hh1oR1a (x a b u : ℝ) : ℝ :=
  hh1oR2a x a b u + hh1oTa a b * (hh1ow x a b u - 3 / 4) + (hh1oT a b - 2) * hh1owa x a b u
noncomputable def hh1oR1b (x a b u : ℝ) : ℝ :=
  hh1oR2b x a b u + hh1oTb a b * (hh1ow x a b u - 3 / 4) + (hh1oT a b - 2) * hh1owb x a b u
noncomputable def hh1oR1u (x a b : ℝ) : ℝ := hh1oR2u x a b + (hh1oT a b - 2) * hh1owu x a b
noncomputable def hh1oGa (x a u : ℝ) : ℝ :=
  (4 * u * hh1ova x a - 2 * hh1oE x a u * hh1oEa x a) * hh1oK a ^ 2 / (576 * a ^ 4) +
    (4 * u * hh1ov x a - hh1oE x a u ^ 2) *
      (24 * a * hh1oK a / (576 * a ^ 4) - 4 * hh1oK a ^ 2 / (576 * a ^ 5))
noncomputable def hh1oGu (x a u : ℝ) : ℝ :=
  (4 * hh1ov x a - 2 * (1 + x) * hh1oE x a u) * hh1oK a ^ 2 / (576 * a ^ 4)

theorem hh1o_K_hasDerivAt {A : ℝ → ℝ} {a' t : ℝ} (hA : HasDerivAt A a' t) :
    HasDerivAt (fun s => hh1oK (A s)) (12 * A t * a') t := by
  unfold hh1oK
  have := ((hA.fun_pow 2).const_mul 6).add_const 1
  convert this using 1; push_cast; ring

theorem hh1o_L_hasDerivAt {A : ℝ → ℝ} {a' t : ℝ} (hA : HasDerivAt A a' t) (ha : 0 < A t) :
    HasDerivAt (fun s => hh1oL (A s)) (hh1oLa (A t) * a') t := by
  have h0 : 7 * A t ^ 2 ≠ 0 := by positivity
  have := (hh1o_K_hasDerivAt hA).fun_div ((hA.fun_pow 2).const_mul 7) h0
  unfold hh1oL
  convert this using 1
  simp only [hh1oLa, hh1oK]
  have ha0 : A t ≠ 0 := ha.ne'
  push_cast
  field_simp
  ring

theorem hh1o_d_hasDerivAt {A B : ℝ → ℝ} {x a' b' t : ℝ} (hA : HasDerivAt A a' t)
    (hB : HasDerivAt B b' t) (ha : 0 < A t) :
    HasDerivAt (fun s => hh1od x (A s) (B s)) (hh1oda x (A t) (B t) * a' + hh1odb x (A t) * b') t := by
  have h0 : 7 * A t ^ 2 ≠ 0 := by positivity
  have hD : HasDerivAt (fun s => hsDg x (B s) (A s))
      (2 * A t * a' + 2 * (a' * B t + A t * b') - 2 * (b' * x)) t := by
    have := ((((hA.fun_pow 2).add ((hA.fun_mul hB).const_mul 2)).add_const 1).add_const (2 * x)).sub
      (hB.const_mul (2 * x))
    unfold hsDg
    convert this using 1
    · funext s; simp only [Pi.add_apply, Pi.sub_apply]; ring
    · push_cast; ring
  have := hD.fun_div ((hA.fun_pow 2).const_mul 7) h0
  unfold hh1od
  convert this using 1
  simp only [hh1oda, hh1odb, hh1od]
  have ha0 : A t ≠ 0 := ha.ne'
  push_cast
  field_simp
  ring

theorem hh1o_v_hasDerivAt {A : ℝ → ℝ} {x a' t : ℝ} (hA : HasDerivAt A a' t) :
    HasDerivAt (fun s => hh1ov x (A s)) (hh1ova x (A t) * a') t := by
  have hK := hh1o_K_hasDerivAt hA
  have hK0 : hh1oK (A t) ≠ 0 := by unfold hh1oK; positivity
  have h1 := (hasDerivAt_const t (1 + x)).fun_div hK hK0
  have := ((h1.const_sub 1).add (h1.fun_pow 2))
  unfold hh1ov
  convert this using 1
  simp only [hh1ova]
  push_cast
  field_simp
  ring

theorem hh1o_E_hasDerivAt {A U : ℝ → ℝ} {x a' u' t : ℝ} (hA : HasDerivAt A a' t)
    (hU : HasDerivAt U u' t) :
    HasDerivAt (fun s => hh1oE x (A s) (U s)) (hh1oEa x (A t) * a' + (1 + x) * u') t := by
  have hK := hh1o_K_hasDerivAt hA
  have hK0 : hh1oK (A t) ≠ 0 := by unfold hh1oK; positivity
  have h1 := (hasDerivAt_const t (2 * (1 + x) - 1)).fun_div hK hK0
  have := (((hU.sub_const 1).const_mul (1 + x)).add_const (1 / (1 + x))).add h1
  unfold hh1oE
  convert this using 1
  simp only [hh1oEa]
  field_simp
  ring

theorem hh1o_y_hasDerivAt {A B : ℝ → ℝ} {a' b' t : ℝ} (hA : HasDerivAt A a' t)
    (hB : HasDerivAt B b' t) (ha : 0 < A t) (hb : 0 < B t) :
    HasDerivAt (fun s => hh1oy (A s) (B s))
      (hh1oy (A t) (B t) * ((1 / (A t + B t) - 1 / A t) * a' + 1 / (A t + B t) * b')) t := by
  have h0 : 7 * A t ≠ 0 := by positivity
  have := ((hA.add hB).const_mul 2).fun_div (hA.const_mul 7) h0
  unfold hh1oy
  convert this using 1
  simp only [Pi.add_apply]
  have hab : A t + B t ≠ 0 := by positivity
  have ha0 : A t ≠ 0 := ha.ne'
  field_simp
  ring

theorem hh1o_G_hasDerivAt {A U : ℝ → ℝ} {x a' u' t : ℝ} (hA : HasDerivAt A a' t)
    (hU : HasDerivAt U u' t) (ha : 0 < A t) :
    HasDerivAt (fun s => hh1oG x (A s) (U s)) (hh1oGa x (A t) (U t) * a' + hh1oGu x (A t) (U t) * u') t := by
  have hv := hh1o_v_hasDerivAt (x := x) hA
  have hE := hh1o_E_hasDerivAt (x := x) hA hU
  have hK := hh1o_K_hasDerivAt hA
  have h0 : 576 * A t ^ 4 ≠ 0 := by positivity
  have := ((((hU.const_mul 4).fun_mul hv).sub (hE.fun_pow 2)).fun_mul (hK.fun_pow 2)).fun_div
    ((hA.fun_pow 4).const_mul 576) h0
  unfold hh1oG
  convert this using 1
  simp only [hh1oGa, hh1oGu, Pi.sub_apply]
  have ha0 : A t ≠ 0 := ha.ne'
  norm_num
  field_simp
  ring

/-- **The derivative of the outer `F₀` along a path at fixed `x`**. -/
theorem hh1o_F0_hasDerivAt {A B U : ℝ → ℝ} {x a' b' u' t : ℝ} (hA : HasDerivAt A a' t)
    (hB : HasDerivAt B b' t) (hU : HasDerivAt U u' t) (ha : 0 < A t) (hb : 0 < B t) :
    HasDerivAt (fun s => hh1oF0 x (A s) (B s) (U s))
      (a' * (hh1oGa x (A t) (U t) - 7 / 96 * hh1oR2a x (A t) (B t) (U t)) +
        b' * (-(7 / 96) * hh1oR2b x (A t) (B t) (U t)) +
        u' * (hh1oGu x (A t) (U t) - 7 / 96 * hh1oR2u x (A t) (B t)) +
        7 / 96 * hh1eps (hh1oy (A t) (B t)) *
          ((1 / (A t + B t) - 1 / A t) * a' + 1 / (A t + B t) * b')) t := by
  have hL := hh1o_L_hasDerivAt hA ha
  have hd := hh1o_d_hasDerivAt (x := x) hA hB ha
  have hv := hh1o_v_hasDerivAt (x := x) hA
  have hE := hh1o_E_hasDerivAt (x := x) hA hU
  have hy := hh1o_y_hasDerivAt hA hB ha hb
  have hG := hh1o_G_hasDerivAt (x := x) hA hU ha
  have hy0 : 0 < hh1oy (A t) (B t) := by unfold hh1oy; positivity
  have hl := (hh1_ell_hasDerivAt hy0).comp t hy
  have hw := (((hL.fun_pow 2).fun_mul hv).add ((hd.fun_pow 2).fun_mul hU)).sub
    ((hd.fun_mul hL).fun_mul hE)
  have hEL := ((hd.const_mul 2).fun_mul hU).sub (hL.fun_mul hE)
  have hab : HasDerivAt (fun s => A s + B s) (a' + b') t := hA.add hB
  have hab0 : A t + B t ≠ 0 := by positivity
  have h1 := ((hU.sub_const 1).fun_mul hab).fun_div hA ha.ne'
  have h2 := hA.fun_div hab hab0
  have hR := ((((((hw.const_mul 2).sub_const (1 / 2)).add h1).add h2).sub_const (1 / 7)).sub hEL).add hl
  have hF := (hG.sub (hR.const_mul (7 / 96))).sub_const (9193 / 50000)
  unfold hh1oF0 hh1oR2 hh1ow hh1oEL
  convert hF using 1
  · funext s; simp only [Pi.add_apply, Pi.sub_apply, Function.comp_apply]
  simp only [hh1oR2a, hh1owa, hh1oELa, hh1oR2b, hh1owb, hh1oR2u, hh1owu, Pi.sub_apply]
  norm_num
  have ha0 : A t ≠ 0 := ha.ne'
  have hy1 : hh1oy (A t) (B t) ≠ 0 := hy0.ne'
  field_simp
  ring

/-- **The derivative of the outer `F₁` along a path at fixed `x`**. -/
theorem hh1o_F1_hasDerivAt {A B U : ℝ → ℝ} {x a' b' u' t : ℝ} (hA : HasDerivAt A a' t)
    (hB : HasDerivAt B b' t) (hU : HasDerivAt U u' t) (ha : 0 < A t) (hb : 0 < B t) :
    HasDerivAt (fun s => hh1oF1 x (A s) (B s) (U s))
      (a' * (hh1oGa x (A t) (U t) - 7 / 96 * hh1oR1a x (A t) (B t) (U t)) +
        b' * (-(7 / 96) * hh1oR1b x (A t) (B t) (U t)) +
        u' * (hh1oGu x (A t) (U t) - 7 / 96 * hh1oR1u x (A t) (B t)) +
        7 / 96 * hh1eps (hh1oy (A t) (B t)) *
          ((1 / (A t + B t) - 1 / A t) * a' + 1 / (A t + B t) * b')) t := by
  have hF0 := hh1o_F0_hasDerivAt (x := x) hA hB hU ha hb
  have hL := hh1o_L_hasDerivAt hA ha
  have hd := hh1o_d_hasDerivAt (x := x) hA hB ha
  have hv := hh1o_v_hasDerivAt (x := x) hA
  have hE := hh1o_E_hasDerivAt (x := x) hA hU
  have hw := (((hL.fun_pow 2).fun_mul hv).add ((hd.fun_pow 2).fun_mul hU)).sub
    ((hd.fun_mul hL).fun_mul hE)
  have hab0 : A t + B t ≠ 0 := by positivity
  have hT := (hA.const_mul 7).fun_div (hA.add hB) hab0
  have hF := hF0.sub (((hT.sub_const 2).fun_mul (hw.sub_const (3 / 4))).const_mul (7 / 96))
  unfold hh1oF1 hh1oT hh1ow
  convert hF using 1
  · funext s; simp only [Pi.add_apply, Pi.sub_apply]; ring
  simp only [hh1oR1a, hh1oR1b, hh1oR1u, hh1owa, hh1owb, hh1owu, hh1oTa, hh1oTb, hh1oT, hh1ow,
    Pi.add_apply, Pi.sub_apply]
  norm_num
  have ha0 : A t ≠ 0 := ha.ne'
  field_simp
  ring

end SmoothedOctagon
