module

public import SmoothedOctagon.Exclusion.Mixed.ShortHand.Heavy.S1CDefs

/-!
# Gate S1, central face: the derivative of the tests along a path

For a differentiable path `t ↦ (x(t), α(t), β(t), u(t))` the central tests have the derivative
`F₀' = x'(Γ_x - cR̄₂_x) + α'(-cR̄₂_α) + β'(-cR̄₂_β) + u'(Γ_u - cR̄₂_u) + cε(y)(log y)'`,
with the partial derivatives of `S1CDefs` (logarithm form) and the cubic-ceiling correction
`ε(y) = ((y - 1)/(y + 1))⁴` (`ℓ'(y) = (1 - ε(y))/y`). The same for `F₁` with
`R̄₁ = R̄₂ + (T - 2)(w - 3/4)` along paths with `α' = 0`.

## Main API

* `hh1_ell_hasDerivAt`: `ℓ'(y) = 1/y - ε(y)/y`.
* `hh1c_F0_hasDerivAt`, `hh1c_F1_hasDerivAt`.
-/

@[expose] public section

namespace SmoothedOctagon

open Real

/-- `ε(y) = ((y - 1)/(y + 1))⁴`, the defect of the cubic ceiling: `ℓ'(y) = (1 - ε(y))/y`. -/
noncomputable def hh1eps (y : ℝ) : ℝ := ((y - 1) / (y + 1)) ^ 4

theorem hh1_ell_hasDerivAt {y : ℝ} (hy : 0 < y) :
    HasDerivAt hh1ell (1 / y - hh1eps y / y) y := by
  have h1 : y + 1 ≠ 0 := by linarith
  have hz : HasDerivAt (fun s => (s - 1) / (s + 1)) (((1 : ℝ) * (y + 1) - (y - 1) * 1) / (y + 1) ^ 2) y :=
    ((hasDerivAt_id' y).sub_const 1).fun_div ((hasDerivAt_id' y).add_const 1) h1
  have h := (hz.const_mul 2).add ((hz.fun_pow 3).const_mul (2 / 3))
  unfold hh1ell hh1eps
  convert h using 1
  have h2 : 1 + y ≠ 0 := by linarith
  have hy0 : y ≠ 0 := hy.ne'
  norm_num
  field_simp
  ring

theorem hh1c_K_hasDerivAt {X Aa : ℝ → ℝ} {x' a' t : ℝ} (hX : HasDerivAt X x' t)
    (hA : HasDerivAt Aa a' t) :
    HasDerivAt (fun s => hh1cK (X s) (Aa s)) (2 * (1 + X t) * x' + 2 * Aa t * a') t := by
  unfold hh1cK
  have := (hX.fun_mul (hX.add_const 2)).add (hA.fun_pow 2)
  convert this using 1; push_cast; ring

theorem hh1c_L_hasDerivAt {X Aa : ℝ → ℝ} {x' a' t : ℝ} (hX : HasDerivAt X x' t)
    (hA : HasDerivAt Aa a' t) (hx : 0 < X t) :
    HasDerivAt (fun s => hh1cL (X s) (Aa s)) (hh1cLx (X t) (Aa t) * x' + hh1cLa (X t) (Aa t) * a') t := by
  have hK0 : hh1cK (X t) (Aa t) ≠ 0 := by unfold hh1cK; positivity
  have hS : HasDerivAt (fun s => 1 + X s) x' t := by simpa using hX.const_add 1
  have := (hS.fun_pow 2).fun_div (hh1c_K_hasDerivAt hX hA) hK0
  unfold hh1cL
  convert this using 1
  simp only [hh1cLx, hh1cLa, hh1cL]
  push_cast
  field_simp
  ring

theorem hh1c_d_hasDerivAt {X Aa Bb : ℝ → ℝ} {x' a' b' t : ℝ} (hX : HasDerivAt X x' t)
    (hA : HasDerivAt Aa a' t) (hB : HasDerivAt Bb b' t) (hx : 0 < X t) :
    HasDerivAt (fun s => hh1cd (X s) (Aa s) (Bb s))
      (hh1cdx (X t) (Aa t) (Bb t) * x' + hh1cda (X t) (Aa t) (Bb t) * a' + hh1cdb (X t) (Aa t) * b') t := by
  have hK0 : hh1cK (X t) (Aa t) ≠ 0 := by unfold hh1cK; positivity
  have hD : HasDerivAt (fun s => hsDg (X s) (Bb s) (Aa s))
      (2 * Aa t * a' + 2 * (a' * Bb t + Aa t * b') + 2 * x' - 2 * (b' * X t + Bb t * x')) t := by
    have := ((((hA.fun_pow 2).add ((hA.fun_mul hB).const_mul 2)).add_const 1).add
      (hX.const_mul 2)).sub ((hB.fun_mul hX).const_mul 2)
    unfold hsDg
    convert this using 1
    · funext s; simp only [Pi.add_apply, Pi.sub_apply]; ring
    · push_cast; ring
  have := hD.fun_div (hh1c_K_hasDerivAt hX hA) hK0
  unfold hh1cd
  convert this using 1
  simp only [hh1cdx, hh1cda, hh1cdb, hh1cd]
  field_simp
  ring

theorem hh1c_v_hasDerivAt {X : ℝ → ℝ} {x' t : ℝ} (hX : HasDerivAt X x' t) (hx : 0 < X t) :
    HasDerivAt (fun s => hh1cv (X s)) (hh1cvx (X t) * x') t := by
  have hS0 : 1 + X t ≠ 0 := by linarith
  have hS : HasDerivAt (fun s => 1 + X s) x' t := by simpa using hX.const_add 1
  have := ((hS.inv hS0).neg.const_add 1).add ((hS.fun_pow 2).inv (by positivity))
  have he : (fun s => hh1cv (X s)) = fun s => 1 + -(fun s => 1 + X s)⁻¹ s + (fun s => (1 + X s) ^ 2)⁻¹ s := by
    funext s; simp only [hh1cv, Pi.inv_apply, one_div]; ring
  rw [he]
  convert this using 1
  unfold hh1cvx
  push_cast
  field_simp
  ring

theorem hh1c_E_hasDerivAt {X U : ℝ → ℝ} {x' u' t : ℝ} (hX : HasDerivAt X x' t) (hU : HasDerivAt U u' t)
    (hx : 0 < X t) :
    HasDerivAt (fun s => hh1cE (X s) (U s)) (hh1cEx (X t) (U t) * x' + (1 + X t) * u') t := by
  have hS0 : 1 + X t ≠ 0 := by linarith
  have hS : HasDerivAt (fun s => 1 + X s) x' t := by simpa using hX.const_add 1
  have := ((hS.fun_mul (hU.sub_const 1)).add (hS.inv hS0)).add
    ((((hS.const_mul 2).sub_const 1)).fun_div (hS.fun_pow 2) (by positivity))
  have he : (fun s => hh1cE (X s) (U s)) = fun s => (1 + X s) * (U s - 1) + (fun s => 1 + X s)⁻¹ s +
      (2 * (1 + X s) - 1) / (1 + X s) ^ 2 := by
    funext s; simp only [hh1cE, Pi.inv_apply, one_div]
  rw [he]
  convert this using 1
  unfold hh1cEx
  push_cast
  field_simp
  ring

theorem hh1c_q_hasDerivAt {X Aa : ℝ → ℝ} {x' a' t : ℝ} (hX : HasDerivAt X x' t)
    (hA : HasDerivAt Aa a' t) (hx : 0 < X t) :
    HasDerivAt (fun s => hh1cq (X s) (Aa s))
      (-(2 * (1 + X t) * hh1cq (X t) (Aa t) / hh1cK (X t) (Aa t)) * x' + hh1cqa (X t) (Aa t) * a') t := by
  have hK0 : hh1cK (X t) (Aa t) ≠ 0 := by unfold hh1cK; positivity
  have := (hA.fun_pow 2).fun_div (hh1c_K_hasDerivAt hX hA) hK0
  unfold hh1cq
  convert this using 1
  simp only [hh1cqa, hh1cq]
  push_cast
  field_simp
  ring

theorem hh1c_y_hasDerivAt {X Aa Bb : ℝ → ℝ} {x' a' b' t : ℝ} (hX : HasDerivAt X x' t)
    (hA : HasDerivAt Aa a' t) (hB : HasDerivAt Bb b' t) (hx : 0 < X t) (ha : 0 < Aa t)
    (hb : 0 < Bb t) :
    HasDerivAt (fun s => hh1cy (X s) (Aa s) (Bb s))
      (hh1cy (X t) (Aa t) (Bb t) * (-(2 * (1 + X t) / hh1cK (X t) (Aa t)) * x' +
        (1 / Aa t + 1 / (Aa t + Bb t) - 2 * Aa t / hh1cK (X t) (Aa t)) * a' +
        1 / (Aa t + Bb t) * b')) t := by
  have hK0 : hh1cK (X t) (Aa t) ≠ 0 := by unfold hh1cK; positivity
  have hy := ((hA.const_mul 2).fun_mul (hA.add hB)).fun_div (hh1c_K_hasDerivAt hX hA) hK0
  unfold hh1cy
  convert hy using 1
  simp only [Pi.add_apply]
  have hab : Aa t + Bb t ≠ 0 := by positivity
  have ha0 : Aa t ≠ 0 := ha.ne'
  field_simp
  ring

/-- The path atoms (`S1CDefs`): `λ`, `d`, `v`, `E`, `q`, `y` along a path. -/
theorem hh1c_atoms_hasDerivAt {X Aa Bb U : ℝ → ℝ} {x' a' b' u' t : ℝ}
    (hX : HasDerivAt X x' t) (hA : HasDerivAt Aa a' t) (hB : HasDerivAt Bb b' t)
    (hU : HasDerivAt U u' t) (hx : 0 < X t) (ha : 0 < Aa t) (hb : 0 < Bb t) :
    HasDerivAt (fun s => hh1cL (X s) (Aa s))
        (hh1cLx (X t) (Aa t) * x' + hh1cLa (X t) (Aa t) * a') t ∧
      HasDerivAt (fun s => hh1cd (X s) (Aa s) (Bb s))
        (hh1cdx (X t) (Aa t) (Bb t) * x' + hh1cda (X t) (Aa t) (Bb t) * a' +
          hh1cdb (X t) (Aa t) * b') t ∧
      HasDerivAt (fun s => hh1cv (X s)) (hh1cvx (X t) * x') t ∧
      HasDerivAt (fun s => hh1cE (X s) (U s)) (hh1cEx (X t) (U t) * x' + (1 + X t) * u') t ∧
      HasDerivAt (fun s => hh1cq (X s) (Aa s))
        (-(2 * (1 + X t) * hh1cq (X t) (Aa t) / hh1cK (X t) (Aa t)) * x' + hh1cqa (X t) (Aa t) * a') t ∧
      HasDerivAt (fun s => hh1cy (X s) (Aa s) (Bb s))
        (hh1cy (X t) (Aa t) (Bb t) * (-(2 * (1 + X t) / hh1cK (X t) (Aa t)) * x' +
          (1 / Aa t + 1 / (Aa t + Bb t) - 2 * Aa t / hh1cK (X t) (Aa t)) * a' +
          1 / (Aa t + Bb t) * b')) t :=
  ⟨hh1c_L_hasDerivAt hX hA hx, hh1c_d_hasDerivAt hX hA hB hx, hh1c_v_hasDerivAt hX hx,
    hh1c_E_hasDerivAt hX hU hx, hh1c_q_hasDerivAt hX hA hx, hh1c_y_hasDerivAt hX hA hB hx ha hb⟩

/-- The envelope Casimir along a path: `Γ' = Γ_x x' + Γ_u u'`. -/
theorem hh1c_G_hasDerivAt {X U : ℝ → ℝ} {x' u' t : ℝ} (hX : HasDerivAt X x' t)
    (hU : HasDerivAt U u' t) (hx : 0 < X t) :
    HasDerivAt (fun s => hh1cG (X s) (U s)) (hh1cGx (X t) (U t) * x' + hh1cGu (X t) (U t) * u') t := by
  obtain ⟨-, -, hv, hE, -, -⟩ := hh1c_atoms_hasDerivAt hX hX hX hU hx hx hx
  have hS : HasDerivAt (fun s => 1 + X s) x' t := by simpa using hX.const_add 1
  have hXX : HasDerivAt (fun s => 16 * (X s * (X s + 2)) ^ 2)
      (16 * (2 * (X t * (X t + 2)) * (x' * (X t + 2) + X t * x'))) t := by
    have := ((hX.fun_mul (hX.add_const 2)).fun_pow 2).const_mul 16
    convert this using 1; push_cast; ring
  have h0 : 16 * (X t * (X t + 2)) ^ 2 ≠ 0 := by positivity
  have := ((((hU.const_mul 4).fun_mul hv).sub (hE.fun_pow 2)).fun_mul (hS.fun_pow 4)).fun_div hXX h0
  unfold hh1cG hh1cGx hh1cGu
  convert this using 1
  have hS0 : 1 + X t ≠ 0 := by linarith
  have hX0 : X t ≠ 0 := hx.ne'
  have hX2 : X t + 2 ≠ 0 := by linarith
  simp only [Pi.sub_apply]
  norm_num
  field_simp
  ring

/-- **The derivative of `F₀` along a path** (log-form partials of `S1CDefs` plus the cubic
correction `cε(y)(log y)'`). -/
theorem hh1c_F0_hasDerivAt {X Aa Bb U : ℝ → ℝ} {x' a' b' u' t : ℝ}
    (hX : HasDerivAt X x' t) (hA : HasDerivAt Aa a' t) (hB : HasDerivAt Bb b' t)
    (hU : HasDerivAt U u' t) (hx : 0 < X t) (ha : 0 < Aa t) (hb : 0 < Bb t) :
    HasDerivAt (fun s => hh1cF0 (X s) (Aa s) (Bb s) (U s))
      (x' * (hh1cGx (X t) (U t) - 7 / 96 * hh1cR2x (X t) (Aa t) (Bb t) (U t)) +
        a' * (-(7 / 96) * hh1cR2a (X t) (Aa t) (Bb t) (U t)) +
        b' * (-(7 / 96) * hh1cR2b (X t) (Aa t) (Bb t) (U t)) +
        u' * (hh1cGu (X t) (U t) - 7 / 96 * hh1cR2u (X t) (Aa t) (Bb t)) +
        7 / 96 * hh1eps (hh1cy (X t) (Aa t) (Bb t)) *
          (-(2 * (1 + X t) / hh1cK (X t) (Aa t)) * x' +
            (1 / Aa t + 1 / (Aa t + Bb t) - 2 * Aa t / hh1cK (X t) (Aa t)) * a' +
            1 / (Aa t + Bb t) * b')) t := by
  obtain ⟨hL, hd, hv, hE, hq, hy⟩ := hh1c_atoms_hasDerivAt hX hA hB hU hx ha hb
  have hG := hh1c_G_hasDerivAt hX hU hx
  have hy0 : 0 < hh1cy (X t) (Aa t) (Bb t) := by unfold hh1cy hh1cK; positivity
  have hl := (hh1_ell_hasDerivAt hy0).comp t hy
  have hw := (((hL.fun_pow 2).fun_mul hv).add ((hd.fun_pow 2).fun_mul hU)).sub
    ((hd.fun_mul hL).fun_mul hE)
  have hEL := ((hd.const_mul 2).fun_mul hU).sub (hL.fun_mul hE)
  have hab : HasDerivAt (fun s => Aa s + Bb s) (a' + b') t := hA.add hB
  have hab0 : Aa t + Bb t ≠ 0 := by positivity
  have h1 := ((hU.sub_const 1).fun_mul hab).fun_div hA ha.ne'
  have h2 := hA.fun_div hab hab0
  have hR := ((((((hw.const_mul 2).sub_const (1 / 2)).add h1).add h2).sub hq).sub hEL).add hl
  have hF := (hG.sub (hR.const_mul (7 / 96))).sub_const (9193 / 50000)
  unfold hh1cF0 hh1cR2 hh1cw hh1cEL
  convert hF using 1
  · funext s; simp only [Pi.add_apply, Pi.sub_apply, Function.comp_apply]
  simp only [hh1cR2x, hh1cwx, hh1cELx, hh1cR2a, hh1cwa, hh1cELa, hh1cR2b, hh1cwb, hh1cR2u, hh1cwu,
    Pi.sub_apply]
  norm_num
  have ha0 : Aa t ≠ 0 := ha.ne'
  have hK0 : hh1cK (X t) (Aa t) ≠ 0 := by unfold hh1cK; positivity
  have hy1 : hh1cy (X t) (Aa t) (Bb t) ≠ 0 := hy0.ne'
  field_simp
  ring

/-- **The derivative of `F₁` along a path with fixed `α`**. -/
theorem hh1c_F1_hasDerivAt {X Bb U : ℝ → ℝ} {a x' b' u' t : ℝ}
    (hX : HasDerivAt X x' t) (hB : HasDerivAt Bb b' t) (hU : HasDerivAt U u' t)
    (hx : 0 < X t) (ha : 0 < a) (hb : 0 < Bb t) :
    HasDerivAt (fun s => hh1cF1 (X s) a (Bb s) (U s))
      (x' * (hh1cGx (X t) (U t) - 7 / 96 * hh1cR1x (X t) a (Bb t) (U t)) +
        b' * (-(7 / 96) * hh1cR1b (X t) a (Bb t) (U t)) +
        u' * (hh1cGu (X t) (U t) - 7 / 96 * (hh1cR2u (X t) a (Bb t) +
          (hh1cT (X t) a (Bb t) - 2) * hh1cwu (X t) a (Bb t))) +
        7 / 96 * hh1eps (hh1cy (X t) a (Bb t)) *
          (-(2 * (1 + X t) / hh1cK (X t) a) * x' + 1 / (a + Bb t) * b')) t := by
  have hA : HasDerivAt (fun _ : ℝ => a) 0 t := hasDerivAt_const t a
  have hF0 := hh1c_F0_hasDerivAt hX hA hB hU hx ha hb
  obtain ⟨hL, hd, hv, hE, -, -⟩ := hh1c_atoms_hasDerivAt hX hA hB hU hx ha hb
  have hw := (((hL.fun_pow 2).fun_mul hv).add ((hd.fun_pow 2).fun_mul hU)).sub
    ((hd.fun_mul hL).fun_mul hE)
  have hK : HasDerivAt (fun s => hh1cK (X s) a) (2 * (1 + X t) * x') t := by
    unfold hh1cK
    have := (hX.fun_mul (hX.add_const 2)).add_const (a ^ 2)
    convert this using 1; ring
  have hab0 : a * (a + Bb t) ≠ 0 := by positivity
  have hT := hK.fun_div ((hB.const_add a).const_mul a) hab0
  have hF := hF0.sub (((hT.sub_const 2).fun_mul (hw.sub_const (3 / 4))).const_mul (7 / 96))
  unfold hh1cF1 hh1cT hh1cw
  convert hF using 1
  · funext s; simp only [Pi.add_apply, Pi.sub_apply]; ring
  simp only [hh1cR1x, hh1cR1b, hh1cwx, hh1cwb, hh1cwu, hh1cTb, hh1cT, hh1cw, hh1cR2a, hh1cwa, hh1cELa,
    Pi.add_apply, Pi.sub_apply]
  norm_num
  have ha0 : a ≠ 0 := ha.ne'
  have hab : a + Bb t ≠ 0 := by positivity
  have hK0 : hh1cK (X t) a ≠ 0 := by unfold hh1cK; positivity
  field_simp
  ring

end SmoothedOctagon
