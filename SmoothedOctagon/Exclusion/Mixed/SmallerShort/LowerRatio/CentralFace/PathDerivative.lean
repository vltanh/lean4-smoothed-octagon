module

public import SmoothedOctagon.Exclusion.Mixed.SmallerShort.LowerRatio.CentralFace.Partials

/-!
# Smaller-short window, lower ratio, central face: the derivative of the tests along a path

For a differentiable path `t ↦ (x(t), α(t), β(t), u(t))` the central tests have the derivative
`F₀' = x'(Γ_x - cR̄₂_x) + α'(-cR̄₂_α) + β'(-cR̄₂_β) + u'(Γ_u - cR̄₂_u) + cε(y)(log y)'`,
with the partial derivatives of `CentralFace/Partials` (logarithm form) and the cubic-ceiling correction
`ε(y) = ((y - 1)/(y + 1))⁴` (`ℓ'(y) = (1 - ε(y))/y`). The same for `F₁` with
`R̄₁ = R̄₂ + (T - 2)(w - 3/4)` along paths with `α' = 0`.

## Main API

* `lr_ell_hasDerivAt`: `ℓ'(y) = 1/y - ε(y)/y`.
* `lrc_F0_hasDerivAt`, `lrc_F1_hasDerivAt`.
-/

@[expose] public section

namespace SmoothedOctagon

open Real

/-- `ε(y) = ((y - 1)/(y + 1))⁴`, the defect of the cubic ceiling: `ℓ'(y) = (1 - ε(y))/y`. -/
noncomputable def lreps (y : ℝ) : ℝ := ((y - 1) / (y + 1)) ^ 4

theorem lr_ell_hasDerivAt {y : ℝ} (hy : 0 < y) :
    HasDerivAt lrell (1 / y - lreps y / y) y := by
  have h1 : y + 1 ≠ 0 := by linarith
  have hz : HasDerivAt (fun s => (s - 1) / (s + 1)) (((1 : ℝ) * (y + 1) - (y - 1) * 1) / (y + 1) ^ 2) y :=
    ((hasDerivAt_id' y).sub_const 1).fun_div ((hasDerivAt_id' y).add_const 1) h1
  have h := (hz.const_mul 2).add ((hz.fun_pow 3).const_mul (2 / 3))
  unfold lrell lreps
  convert h using 1
  have h2 : 1 + y ≠ 0 := by linarith
  have hy0 : y ≠ 0 := hy.ne'
  norm_num
  field_simp
  ring

theorem lrc_K_hasDerivAt {X Aa : ℝ → ℝ} {x' a' t : ℝ} (hX : HasDerivAt X x' t)
    (hA : HasDerivAt Aa a' t) :
    HasDerivAt (fun s => lrcK (X s) (Aa s)) (2 * (1 + X t) * x' + 2 * Aa t * a') t := by
  unfold lrcK
  have := (hX.fun_mul (hX.add_const 2)).add (hA.fun_pow 2)
  convert this using 1; push_cast; ring

theorem lrc_L_hasDerivAt {X Aa : ℝ → ℝ} {x' a' t : ℝ} (hX : HasDerivAt X x' t)
    (hA : HasDerivAt Aa a' t) (hx : 0 < X t) :
    HasDerivAt (fun s => lrcL (X s) (Aa s)) (lrcLx (X t) (Aa t) * x' + lrcLa (X t) (Aa t) * a') t := by
  have hK0 : lrcK (X t) (Aa t) ≠ 0 := by unfold lrcK; positivity
  have hS : HasDerivAt (fun s => 1 + X s) x' t := by simpa using hX.const_add 1
  have := (hS.fun_pow 2).fun_div (lrc_K_hasDerivAt hX hA) hK0
  unfold lrcL
  convert this using 1
  simp only [lrcLx, lrcLa, lrcL]
  push_cast
  field_simp
  ring

theorem lrc_d_hasDerivAt {X Aa Bb : ℝ → ℝ} {x' a' b' t : ℝ} (hX : HasDerivAt X x' t)
    (hA : HasDerivAt Aa a' t) (hB : HasDerivAt Bb b' t) (hx : 0 < X t) :
    HasDerivAt (fun s => lrcd (X s) (Aa s) (Bb s))
      (lrcdx (X t) (Aa t) (Bb t) * x' + lrcda (X t) (Aa t) (Bb t) * a' + lrcdb (X t) (Aa t) * b') t := by
  have hK0 : lrcK (X t) (Aa t) ≠ 0 := by unfold lrcK; positivity
  have hD : HasDerivAt (fun s => ssDg (X s) (Bb s) (Aa s))
      (2 * Aa t * a' + 2 * (a' * Bb t + Aa t * b') + 2 * x' - 2 * (b' * X t + Bb t * x')) t := by
    have := ((((hA.fun_pow 2).add ((hA.fun_mul hB).const_mul 2)).add_const 1).add
      (hX.const_mul 2)).sub ((hB.fun_mul hX).const_mul 2)
    unfold ssDg
    convert this using 1
    · funext s; simp only [Pi.add_apply, Pi.sub_apply]; ring
    · push_cast; ring
  have := hD.fun_div (lrc_K_hasDerivAt hX hA) hK0
  unfold lrcd
  convert this using 1
  simp only [lrcdx, lrcda, lrcdb, lrcd]
  field_simp
  ring

theorem lrc_v_hasDerivAt {X : ℝ → ℝ} {x' t : ℝ} (hX : HasDerivAt X x' t) (hx : 0 < X t) :
    HasDerivAt (fun s => lrcv (X s)) (lrcvx (X t) * x') t := by
  have hS0 : 1 + X t ≠ 0 := by linarith
  have hS : HasDerivAt (fun s => 1 + X s) x' t := by simpa using hX.const_add 1
  have := ((hS.inv hS0).neg.const_add 1).add ((hS.fun_pow 2).inv (by positivity))
  have he : (fun s => lrcv (X s)) = fun s => 1 + -(fun s => 1 + X s)⁻¹ s + (fun s => (1 + X s) ^ 2)⁻¹ s := by
    funext s; simp only [lrcv, Pi.inv_apply, one_div]; ring
  rw [he]
  convert this using 1
  unfold lrcvx
  push_cast
  field_simp
  ring

theorem lrc_E_hasDerivAt {X U : ℝ → ℝ} {x' u' t : ℝ} (hX : HasDerivAt X x' t) (hU : HasDerivAt U u' t)
    (hx : 0 < X t) :
    HasDerivAt (fun s => lrcE (X s) (U s)) (lrcEx (X t) (U t) * x' + (1 + X t) * u') t := by
  have hS0 : 1 + X t ≠ 0 := by linarith
  have hS : HasDerivAt (fun s => 1 + X s) x' t := by simpa using hX.const_add 1
  have := ((hS.fun_mul (hU.sub_const 1)).add (hS.inv hS0)).add
    ((((hS.const_mul 2).sub_const 1)).fun_div (hS.fun_pow 2) (by positivity))
  have he : (fun s => lrcE (X s) (U s)) = fun s => (1 + X s) * (U s - 1) + (fun s => 1 + X s)⁻¹ s +
      (2 * (1 + X s) - 1) / (1 + X s) ^ 2 := by
    funext s; simp only [lrcE, Pi.inv_apply, one_div]
  rw [he]
  convert this using 1
  unfold lrcEx
  push_cast
  field_simp
  ring

theorem lrc_q_hasDerivAt {X Aa : ℝ → ℝ} {x' a' t : ℝ} (hX : HasDerivAt X x' t)
    (hA : HasDerivAt Aa a' t) (hx : 0 < X t) :
    HasDerivAt (fun s => lrcq (X s) (Aa s))
      (-(2 * (1 + X t) * lrcq (X t) (Aa t) / lrcK (X t) (Aa t)) * x' + lrcqa (X t) (Aa t) * a') t := by
  have hK0 : lrcK (X t) (Aa t) ≠ 0 := by unfold lrcK; positivity
  have := (hA.fun_pow 2).fun_div (lrc_K_hasDerivAt hX hA) hK0
  unfold lrcq
  convert this using 1
  simp only [lrcqa, lrcq]
  push_cast
  field_simp
  ring

theorem lrc_y_hasDerivAt {X Aa Bb : ℝ → ℝ} {x' a' b' t : ℝ} (hX : HasDerivAt X x' t)
    (hA : HasDerivAt Aa a' t) (hB : HasDerivAt Bb b' t) (hx : 0 < X t) (ha : 0 < Aa t)
    (hb : 0 < Bb t) :
    HasDerivAt (fun s => lrcy (X s) (Aa s) (Bb s))
      (lrcy (X t) (Aa t) (Bb t) * (-(2 * (1 + X t) / lrcK (X t) (Aa t)) * x' +
        (1 / Aa t + 1 / (Aa t + Bb t) - 2 * Aa t / lrcK (X t) (Aa t)) * a' +
        1 / (Aa t + Bb t) * b')) t := by
  have hK0 : lrcK (X t) (Aa t) ≠ 0 := by unfold lrcK; positivity
  have hy := ((hA.const_mul 2).fun_mul (hA.add hB)).fun_div (lrc_K_hasDerivAt hX hA) hK0
  unfold lrcy
  convert hy using 1
  simp only [Pi.add_apply]
  have hab : Aa t + Bb t ≠ 0 := by positivity
  have ha0 : Aa t ≠ 0 := ha.ne'
  field_simp
  ring

/-- The path atoms (`CentralFace/Partials`): `λ`, `d`, `v`, `E`, `q`, `y` along a path. -/
theorem lrc_atoms_hasDerivAt {X Aa Bb U : ℝ → ℝ} {x' a' b' u' t : ℝ}
    (hX : HasDerivAt X x' t) (hA : HasDerivAt Aa a' t) (hB : HasDerivAt Bb b' t)
    (hU : HasDerivAt U u' t) (hx : 0 < X t) (ha : 0 < Aa t) (hb : 0 < Bb t) :
    HasDerivAt (fun s => lrcL (X s) (Aa s))
        (lrcLx (X t) (Aa t) * x' + lrcLa (X t) (Aa t) * a') t ∧
      HasDerivAt (fun s => lrcd (X s) (Aa s) (Bb s))
        (lrcdx (X t) (Aa t) (Bb t) * x' + lrcda (X t) (Aa t) (Bb t) * a' +
          lrcdb (X t) (Aa t) * b') t ∧
      HasDerivAt (fun s => lrcv (X s)) (lrcvx (X t) * x') t ∧
      HasDerivAt (fun s => lrcE (X s) (U s)) (lrcEx (X t) (U t) * x' + (1 + X t) * u') t ∧
      HasDerivAt (fun s => lrcq (X s) (Aa s))
        (-(2 * (1 + X t) * lrcq (X t) (Aa t) / lrcK (X t) (Aa t)) * x' + lrcqa (X t) (Aa t) * a') t ∧
      HasDerivAt (fun s => lrcy (X s) (Aa s) (Bb s))
        (lrcy (X t) (Aa t) (Bb t) * (-(2 * (1 + X t) / lrcK (X t) (Aa t)) * x' +
          (1 / Aa t + 1 / (Aa t + Bb t) - 2 * Aa t / lrcK (X t) (Aa t)) * a' +
          1 / (Aa t + Bb t) * b')) t :=
  ⟨lrc_L_hasDerivAt hX hA hx, lrc_d_hasDerivAt hX hA hB hx, lrc_v_hasDerivAt hX hx,
    lrc_E_hasDerivAt hX hU hx, lrc_q_hasDerivAt hX hA hx, lrc_y_hasDerivAt hX hA hB hx ha hb⟩

/-- The envelope Casimir along a path: `Γ' = Γ_x x' + Γ_u u'`. -/
theorem lrc_G_hasDerivAt {X U : ℝ → ℝ} {x' u' t : ℝ} (hX : HasDerivAt X x' t)
    (hU : HasDerivAt U u' t) (hx : 0 < X t) :
    HasDerivAt (fun s => lrcG (X s) (U s)) (lrcGx (X t) (U t) * x' + lrcGu (X t) (U t) * u') t := by
  obtain ⟨-, -, hv, hE, -, -⟩ := lrc_atoms_hasDerivAt hX hX hX hU hx hx hx
  have hS : HasDerivAt (fun s => 1 + X s) x' t := by simpa using hX.const_add 1
  have hXX : HasDerivAt (fun s => 16 * (X s * (X s + 2)) ^ 2)
      (16 * (2 * (X t * (X t + 2)) * (x' * (X t + 2) + X t * x'))) t := by
    have := ((hX.fun_mul (hX.add_const 2)).fun_pow 2).const_mul 16
    convert this using 1; push_cast; ring
  have h0 : 16 * (X t * (X t + 2)) ^ 2 ≠ 0 := by positivity
  have := ((((hU.const_mul 4).fun_mul hv).sub (hE.fun_pow 2)).fun_mul (hS.fun_pow 4)).fun_div hXX h0
  unfold lrcG lrcGx lrcGu
  convert this using 1
  have hS0 : 1 + X t ≠ 0 := by linarith
  have hX0 : X t ≠ 0 := hx.ne'
  have hX2 : X t + 2 ≠ 0 := by linarith
  simp only [Pi.sub_apply]
  norm_num
  field_simp
  ring

/-- **The derivative of `F₀` along a path** (log-form partials of `CentralFace/Partials` plus the cubic
correction `cε(y)(log y)'`). -/
theorem lrc_F0_hasDerivAt {X Aa Bb U : ℝ → ℝ} {x' a' b' u' t : ℝ}
    (hX : HasDerivAt X x' t) (hA : HasDerivAt Aa a' t) (hB : HasDerivAt Bb b' t)
    (hU : HasDerivAt U u' t) (hx : 0 < X t) (ha : 0 < Aa t) (hb : 0 < Bb t) :
    HasDerivAt (fun s => lrcF0 (X s) (Aa s) (Bb s) (U s))
      (x' * (lrcGx (X t) (U t) - 7 / 96 * lrcR2x (X t) (Aa t) (Bb t) (U t)) +
        a' * (-(7 / 96) * lrcR2a (X t) (Aa t) (Bb t) (U t)) +
        b' * (-(7 / 96) * lrcR2b (X t) (Aa t) (Bb t) (U t)) +
        u' * (lrcGu (X t) (U t) - 7 / 96 * lrcR2u (X t) (Aa t) (Bb t)) +
        7 / 96 * lreps (lrcy (X t) (Aa t) (Bb t)) *
          (-(2 * (1 + X t) / lrcK (X t) (Aa t)) * x' +
            (1 / Aa t + 1 / (Aa t + Bb t) - 2 * Aa t / lrcK (X t) (Aa t)) * a' +
            1 / (Aa t + Bb t) * b')) t := by
  obtain ⟨hL, hd, hv, hE, hq, hy⟩ := lrc_atoms_hasDerivAt hX hA hB hU hx ha hb
  have hG := lrc_G_hasDerivAt hX hU hx
  have hy0 : 0 < lrcy (X t) (Aa t) (Bb t) := by unfold lrcy lrcK; positivity
  have hl := (lr_ell_hasDerivAt hy0).comp t hy
  have hw := (((hL.fun_pow 2).fun_mul hv).add ((hd.fun_pow 2).fun_mul hU)).sub
    ((hd.fun_mul hL).fun_mul hE)
  have hEL := ((hd.const_mul 2).fun_mul hU).sub (hL.fun_mul hE)
  have hab : HasDerivAt (fun s => Aa s + Bb s) (a' + b') t := hA.add hB
  have hab0 : Aa t + Bb t ≠ 0 := by positivity
  have h1 := ((hU.sub_const 1).fun_mul hab).fun_div hA ha.ne'
  have h2 := hA.fun_div hab hab0
  have hR := ((((((hw.const_mul 2).sub_const (1 / 2)).add h1).add h2).sub hq).sub hEL).add hl
  have hF := (hG.sub (hR.const_mul (7 / 96))).sub_const (9193 / 50000)
  unfold lrcF0 lrcR2 lrcw lrcEL
  convert hF using 1
  · funext s; simp only [Pi.add_apply, Pi.sub_apply, Function.comp_apply]
  simp only [lrcR2x, lrcwx, lrcELx, lrcR2a, lrcwa, lrcELa, lrcR2b, lrcwb, lrcR2u, lrcwu]
  norm_num
  have ha0 : Aa t ≠ 0 := ha.ne'
  have hK0 : lrcK (X t) (Aa t) ≠ 0 := by unfold lrcK; positivity
  have hy1 : lrcy (X t) (Aa t) (Bb t) ≠ 0 := hy0.ne'
  field_simp
  ring

/-- **The derivative of `F₁` along a path with fixed `α`**. -/
theorem lrc_F1_hasDerivAt {X Bb U : ℝ → ℝ} {a x' b' u' t : ℝ}
    (hX : HasDerivAt X x' t) (hB : HasDerivAt Bb b' t) (hU : HasDerivAt U u' t)
    (hx : 0 < X t) (ha : 0 < a) (hb : 0 < Bb t) :
    HasDerivAt (fun s => lrcF1 (X s) a (Bb s) (U s))
      (x' * (lrcGx (X t) (U t) - 7 / 96 * lrcR1x (X t) a (Bb t) (U t)) +
        b' * (-(7 / 96) * lrcR1b (X t) a (Bb t) (U t)) +
        u' * (lrcGu (X t) (U t) - 7 / 96 * (lrcR2u (X t) a (Bb t) +
          (lrcT (X t) a (Bb t) - 2) * lrcwu (X t) a (Bb t))) +
        7 / 96 * lreps (lrcy (X t) a (Bb t)) *
          (-(2 * (1 + X t) / lrcK (X t) a) * x' + 1 / (a + Bb t) * b')) t := by
  have hA : HasDerivAt (fun _ : ℝ => a) 0 t := hasDerivAt_const t a
  have hF0 := lrc_F0_hasDerivAt hX hA hB hU hx ha hb
  obtain ⟨hL, hd, hv, hE, -, -⟩ := lrc_atoms_hasDerivAt hX hA hB hU hx ha hb
  have hw := (((hL.fun_pow 2).fun_mul hv).add ((hd.fun_pow 2).fun_mul hU)).sub
    ((hd.fun_mul hL).fun_mul hE)
  have hK : HasDerivAt (fun s => lrcK (X s) a) (2 * (1 + X t) * x') t := by
    unfold lrcK
    have := (hX.fun_mul (hX.add_const 2)).add_const (a ^ 2)
    convert this using 1; ring
  have hab0 : a * (a + Bb t) ≠ 0 := by positivity
  have hT := hK.fun_div ((hB.const_add a).const_mul a) hab0
  have hF := hF0.sub (((hT.sub_const 2).fun_mul (hw.sub_const (3 / 4))).const_mul (7 / 96))
  unfold lrcF1 lrcT lrcw
  convert hF using 1
  · funext s; simp only [Pi.add_apply, Pi.sub_apply]; ring
  simp only [lrcR1x, lrcR1b, lrcwx, lrcwb, lrcwu, lrcTb, lrcT, lrcw, lrcR2a, lrcwa, lrcELa,
    Pi.add_apply, Pi.sub_apply]
  norm_num
  have ha0 : a ≠ 0 := ha.ne'
  have hab : a + Bb t ≠ 0 := by positivity
  have hK0 : lrcK (X t) a ≠ 0 := by unfold lrcK; positivity
  field_simp
  ring

end SmoothedOctagon
