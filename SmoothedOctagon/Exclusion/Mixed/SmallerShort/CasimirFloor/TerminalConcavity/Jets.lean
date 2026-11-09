module

public import SmoothedOctagon.Exclusion.Mixed.SmallerShort.CasimirFloor.ShapeCurve

/-!
# Smaller-short window, Casimir floor: third-order jets and the terminal source

On the terminal line `x = 13/6`, `e = 13/5`, put `r = 13d` (`0 ≤ r ≤ 13/19`). Then
`Ψ = G(u) - (r₁ + log y)/7` with the incoming value `u(r) = (r² - 7r + 6133)/8112 + v/(r + 7)`,
`v = 160867/6319248`, the Casimir quadratic `G` in `u` and the partial-fraction form

`r₁ = -56/33 + 25u/66 + (α_A u + β_A)/A + (α_B u + β_B)/B + (n - mu)/K`,
`y = 12AB/K`, `A = r + 5`, `B = 11r + 95`, `K = 36r² + 360r + 9025`.

This module proves these source identities (`cas_w6_eq`) and provides a small calculus of
third-order jets.

## Main API

* `ThirdJet` with `.add`, `.sub`, `.const_mul`, `.mul`; primitive jets `cas_j3_const`,
  `cas_j3_aff`, `cas_j3_inv`, `cas_j3_log`, `cas_j3_invK`, `cas_j3_logK`, `cas_j3_U`.
* `casW6U` (and `…1`, `…2`, `…3`), `casW6K`, `casW6F`, `cas_w6_eq`.
-/

@[expose] public section

namespace SmoothedOctagon

open Real

/-! ### Third-order jets -/

/-- A third-order jet at `x`: `f' = f₁`, `f₁' = f₂`, `f₂' = f₃` at `x`. -/
def ThirdJet (f f₁ f₂ f₃ : ℝ → ℝ) (x : ℝ) : Prop :=
  HasDerivAt f (f₁ x) x ∧ HasDerivAt f₁ (f₂ x) x ∧ HasDerivAt f₂ (f₃ x) x

namespace ThirdJet

variable {f f₁ f₂ f₃ g g₁ g₂ g₃ : ℝ → ℝ} {x : ℝ}

theorem toJ (hf : ThirdJet f f₁ f₂ f₃ x) : SecondJet f f₁ f₂ x := ⟨hf.1, hf.2.1⟩

theorem add (hf : ThirdJet f f₁ f₂ f₃ x) (hg : ThirdJet g g₁ g₂ g₃ x) :
    ThirdJet (fun y => f y + g y) (fun y => f₁ y + g₁ y) (fun y => f₂ y + g₂ y)
      (fun y => f₃ y + g₃ y) x :=
  ⟨hf.1.fun_add hg.1, hf.2.1.fun_add hg.2.1, hf.2.2.fun_add hg.2.2⟩

theorem sub (hf : ThirdJet f f₁ f₂ f₃ x) (hg : ThirdJet g g₁ g₂ g₃ x) :
    ThirdJet (fun y => f y - g y) (fun y => f₁ y - g₁ y) (fun y => f₂ y - g₂ y)
      (fun y => f₃ y - g₃ y) x :=
  ⟨hf.1.fun_sub hg.1, hf.2.1.fun_sub hg.2.1, hf.2.2.fun_sub hg.2.2⟩

theorem const_mul (c : ℝ) (hf : ThirdJet f f₁ f₂ f₃ x) :
    ThirdJet (fun y => c * f y) (fun y => c * f₁ y) (fun y => c * f₂ y) (fun y => c * f₃ y) x :=
  ⟨hf.1.const_mul c, hf.2.1.const_mul c, hf.2.2.const_mul c⟩

theorem mul (hf : ThirdJet f f₁ f₂ f₃ x) (hg : ThirdJet g g₁ g₂ g₃ x) :
    ThirdJet (fun y => f y * g y) (fun y => f₁ y * g y + f y * g₁ y)
      (fun y => f₂ y * g y + 2 * (f₁ y * g₁ y) + f y * g₂ y)
      (fun y => f₃ y * g y + 3 * (f₂ y * g₁ y) + 3 * (f₁ y * g₂ y) + f y * g₃ y) x := by
  refine ⟨hf.1.fun_mul hg.1, ?_, ?_⟩
  · refine ((hf.2.1.fun_mul hg.1).fun_add (hf.1.fun_mul hg.2.1)).congr_deriv ?_
    ring
  · refine ((((hf.2.2.fun_mul hg.1).fun_add ((hf.2.1.fun_mul hg.2.1).const_mul 2)).fun_add
      (hf.1.fun_mul hg.2.2))).congr_deriv ?_
    ring

end ThirdJet

theorem cas_j3_const (c x : ℝ) :
    ThirdJet (fun _ => c) (fun _ => 0) (fun _ => 0) (fun _ => 0) x :=
  ⟨hasDerivAt_const x c, hasDerivAt_const x (0 : ℝ), hasDerivAt_const x (0 : ℝ)⟩

theorem cas_j3_aff (c₀ c₁ x : ℝ) :
    ThirdJet (fun y => c₀ + c₁ * y) (fun _ => c₁) (fun _ => 0) (fun _ => 0) x := by
  refine ⟨?_, hasDerivAt_const x c₁, hasDerivAt_const x (0 : ℝ)⟩
  simpa using ((hasDerivAt_id' x).const_mul c₁).const_add c₀

/-- `1/(py + q)`. -/
theorem cas_j3_inv (p q : ℝ) {x : ℝ} (hx : p * x + q ≠ 0) :
    ThirdJet (fun y => 1 / (p * y + q)) (fun y => -p / (p * y + q) ^ 2)
      (fun y => 2 * p ^ 2 / (p * y + q) ^ 3) (fun y => -(6 * p ^ 3) / (p * y + q) ^ 4) x := by
  have hL : HasDerivAt (fun y : ℝ => p * y + q) p x := by
    simpa using ((hasDerivAt_id' x).const_mul p).add_const q
  refine ⟨?_, ?_, ?_⟩
  · refine ((hasDerivAt_const x (1 : ℝ)).fun_div hL hx).congr_deriv ?_
    field_simp
    ring
  · refine ((hasDerivAt_const x (-p)).fun_div (hL.fun_pow 2) (pow_ne_zero 2 hx)).congr_deriv ?_
    push_cast
    field_simp
    ring
  · refine ((hasDerivAt_const x (2 * p ^ 2)).fun_div (hL.fun_pow 3)
      (pow_ne_zero 3 hx)).congr_deriv ?_
    push_cast
    field_simp
    ring

/-- `log(py + q)`. -/
theorem cas_j3_log (p q : ℝ) {x : ℝ} (hx : 0 < p * x + q) :
    ThirdJet (fun y => log (p * y + q)) (fun y => p / (p * y + q))
      (fun y => -p ^ 2 / (p * y + q) ^ 2) (fun y => 2 * p ^ 3 / (p * y + q) ^ 3) x := by
  have hL : HasDerivAt (fun y : ℝ => p * y + q) p x := by
    simpa using ((hasDerivAt_id' x).const_mul p).add_const q
  refine ⟨?_, ?_, ?_⟩
  · refine (hL.log hx.ne').congr_deriv ?_
    ring
  · refine ((hasDerivAt_const x p).fun_div hL hx.ne').congr_deriv ?_
    field_simp
    ring
  · refine ((hasDerivAt_const x (-p ^ 2)).fun_div (hL.fun_pow 2)
      (pow_ne_zero 2 hx.ne')).congr_deriv ?_
    push_cast
    field_simp
    ring

/-- `K = 36r² + 360r + 9025`. -/
noncomputable def casW6K (r : ℝ) : ℝ := 36 * r ^ 2 + 360 * r + 9025

theorem cas_W6K_pos {r : ℝ} (hr : 0 ≤ r) : 9025 ≤ casW6K r := by
  unfold casW6K; nlinarith

private theorem cas_dK (x : ℝ) : HasDerivAt casW6K (72 * x + 360) x := by
  have := (((hasDerivAt_pow 2 x).const_mul 36).fun_add ((hasDerivAt_id' x).const_mul 360)).add_const
    9025
  refine this.congr_deriv ?_
  push_cast
  ring

/-- `1/K`. -/
theorem cas_j3_invK {x : ℝ} (hx : 0 ≤ x) :
    ThirdJet (fun y => 1 / casW6K y) (fun y => -(72 * y + 360) / casW6K y ^ 2)
      (fun y => (2 * (72 * y + 360) ^ 2 - 72 * casW6K y) / casW6K y ^ 3)
      (fun y => (432 * (72 * y + 360) * casW6K y - 6 * (72 * y + 360) ^ 3) / casW6K y ^ 4) x := by
  have hK : casW6K x ≠ 0 := by have := cas_W6K_pos hx; positivity
  have hK' : HasDerivAt (fun y : ℝ => 72 * y + 360) 72 x := by
    simpa using ((hasDerivAt_id' x).const_mul (72 : ℝ)).add_const 360
  refine ⟨?_, ?_, ?_⟩
  · refine ((hasDerivAt_const x (1 : ℝ)).fun_div (cas_dK x) hK).congr_deriv ?_
    field_simp
    ring
  · refine (hK'.fun_neg.fun_div ((cas_dK x).fun_pow 2) (pow_ne_zero 2 hK)).congr_deriv ?_
    unfold casW6K
    push_cast
    field_simp
    ring
  · refine ((((hK'.fun_pow 2).const_mul 2).fun_sub ((cas_dK x).const_mul 72)).fun_div
      ((cas_dK x).fun_pow 3) (pow_ne_zero 3 hK)).congr_deriv ?_
    unfold casW6K
    push_cast
    field_simp
    ring

/-- `log K`. -/
theorem cas_j3_logK {x : ℝ} (hx : 0 ≤ x) :
    ThirdJet (fun y => log (casW6K y)) (fun y => (72 * y + 360) / casW6K y)
      (fun y => (72 * casW6K y - (72 * y + 360) ^ 2) / casW6K y ^ 2)
      (fun y => -(216 * (72 * y + 360)) / casW6K y ^ 2 + 2 * (72 * y + 360) ^ 3 / casW6K y ^ 3)
      x := by
  have hK0 : 0 < casW6K x := by have := cas_W6K_pos hx; linarith
  have hK := hK0.ne'
  have hK' : HasDerivAt (fun y : ℝ => 72 * y + 360) 72 x := by
    simpa using ((hasDerivAt_id' x).const_mul (72 : ℝ)).add_const 360
  refine ⟨?_, ?_, ?_⟩
  · refine ((cas_dK x).log hK).congr_deriv ?_
    ring
  · refine (hK'.fun_div (cas_dK x) hK).congr_deriv ?_
    unfold casW6K
    field_simp
  · refine ((((cas_dK x).const_mul 72).fun_sub (hK'.fun_pow 2)).fun_div
      ((cas_dK x).fun_pow 2) (pow_ne_zero 2 hK)).congr_deriv ?_
    unfold casW6K
    push_cast
    field_simp
    ring

/-! ### The incoming value and the source -/

/-- `u(r) = (r² - 7r + 6133)/8112 + v/(r + 7)`, `v = 160867/6319248`. -/
noncomputable def casW6U (r : ℝ) : ℝ := (r ^ 2 - 7 * r + 6133) / 8112 + 160867 / 6319248 / (r + 7)

noncomputable def casW6U1 (r : ℝ) : ℝ := (2 * r - 7) / 8112 - 160867 / 6319248 / (r + 7) ^ 2

noncomputable def casW6U2 (r : ℝ) : ℝ := 2 / 8112 + 2 * (160867 / 6319248) / (r + 7) ^ 3

noncomputable def casW6U3 (r : ℝ) : ℝ := -(6 * (160867 / 6319248)) / (r + 7) ^ 4

theorem cas_j3_U {x : ℝ} (hx : 0 ≤ x) : ThirdJet casW6U casW6U1 casW6U2 casW6U3 x := by
  have h7 : x + 7 ≠ 0 := by positivity
  have hL : HasDerivAt (fun y : ℝ => y + 7) 1 x := by simpa using (hasDerivAt_id' x).add_const 7
  refine ⟨?_, ?_, ?_⟩
  · have := (((hasDerivAt_pow 2 x).fun_sub ((hasDerivAt_id' x).const_mul 7)).add_const 6133
      |>.div_const 8112).fun_add ((hasDerivAt_const x (160867 / 6319248 : ℝ)).fun_div hL h7)
    refine this.congr_deriv ?_
    unfold casW6U1
    push_cast
    field_simp
    ring
  · have := ((((hasDerivAt_id' x).const_mul 2).sub_const 7).div_const 8112).fun_sub
      ((hasDerivAt_const x (160867 / 6319248 : ℝ)).fun_div (hL.fun_pow 2) (pow_ne_zero 2 h7))
    refine this.congr_deriv ?_
    unfold casW6U2
    push_cast
    field_simp
    ring
  · have := ((hasDerivAt_const x (2 * (160867 / 6319248) : ℝ)).fun_div (hL.fun_pow 3)
      (pow_ne_zero 3 h7)).const_add (2 / 8112)
    refine this.congr_deriv ?_
    unfold casW6U3
    push_cast
    field_simp
    ring

/-- **The terminal source**: `Ψ` on `x = 13/6`, `e = 13/5` as a function of `r = 13d`. -/
noncomputable def casW6F (r : ℝ) : ℝ :=
  -47045881 / 60840000 * (casW6U r * casW6U r) + 83616986 / 60840000 * casW6U r -
    1 / 7 * (25 / 66 * casW6U r +
      (227 / 18 * casW6U r + -2077 / 576) * (1 / (1 * r + 5)) +
      (98342375 / 457919 * casW6U r + -20425821365 / 87920448) * (1 / (11 * r + 95)) +
      ((3690640915 / 249774 + 157928748 / 249774 * r) -
        (697700705 / 249774 + 394433796 / 249774 * r) * casW6U r) * (1 / casW6K r) +
      (log (1 * r + 5) + log (11 * r + 95) - log (casW6K r))) +
    (-25230529 / 60840000 - 1 / 7 * (-56 / 33 + log 12))

/-- **The source identities**: on `0 ≤ r`, `Ψ(13/6, r/13, 13/5)` is
`casW6F r`. -/
theorem cas_w6_eq {r : ℝ} (hr : 0 ≤ r) : casPsiC (13 / 6) (r / 13) (13 / 5) = casW6F r := by
  have hu : ssUbar (13 / 6) (13 / 6 * (1 + r / 13)) = casW6U r := by
    unfold ssUbar casW6U
    have : (r + 7) ≠ 0 := by positivity
    have hb : 13 / 6 * (1 + r / 13) - 1 = (r + 7) / 6 := by ring
    have hb' : 13 / 6 * (1 + r / 13) - 13 / 6 = r / 6 := by ring
    rw [hb, hb']
    field_simp
    ring
  have hK0 : 0 < casW6K r := by have := cas_W6K_pos hr; linarith
  have hlog : log (2 * (1 + 13 / 5 * (r / 13)) * (1 + 13 / 5 * (r / 13) + 13 / 6 * (1 + r / 13)) /
      (13 / 6 * (13 / 6 + 2) + (1 + 13 / 5 * (r / 13)) ^ 2)) =
      log 12 + (log (1 * r + 5) + log (11 * r + 95) - log (casW6K r)) := by
    have e1 : 2 * (1 + 13 / 5 * (r / 13)) * (1 + 13 / 5 * (r / 13) + 13 / 6 * (1 + r / 13)) /
        (13 / 6 * (13 / 6 + 2) + (1 + 13 / 5 * (r / 13)) ^ 2) =
        12 * (1 * r + 5) * (11 * r + 95) / casW6K r := by
      unfold casW6K
      field_simp
      ring
    rw [e1, log_div (by positivity) hK0.ne', log_mul (by positivity) (by positivity),
      log_mul (by norm_num) (by positivity)]
    ring
  unfold casPsiC casClosedPsiC
  rw [hu, hlog]
  unfold casW6F casClosedG casClosedWc casClosedRest casClosedEL casClosedP ssDg
  generalize casW6U r = U
  have hA : (1 * r + 5) ≠ 0 := by positivity
  have hB : (11 * r + 95) ≠ 0 := by positivity
  have hK := hK0.ne'
  unfold casW6K at hK ⊢
  field_simp
  ring

end SmoothedOctagon
