module

public import SmoothedOctagon.Exclusion.Mixed.SmallerShort.UpperRatio.CentralFace.Defs

/-!
# Smaller-short window, upper ratio: the central beta monotonicity, partial fractions

With the incoming pole kept visible,
`u = u_f + J/(b - 1)` (`u_f = 2401/3200`, `J = (x - 1)(680(x - 1)² - 3S²)/(9600S²)`) and
`D = C² + δ(b - 1)` (`C = a + 1`, `δ = 2(a - x)`, `D₀ = C² - δC`), so with `B = a + b`
(with `c_w = C c_v`)
`w = c₂B² + c₁B + c₀ + C c_v/(b - 1)`, `E_L = e₁B + e₀ + c_e/(b - 1)`,
`R = l₁B + l₀ + a/B + c_b/(b - 1)`.
Hence, with `ℓ = 7a/(2K)`,
`F₀ = p₃B³ + p₂B² + p₁B + a/B + p_c/(b - 1) + log B + const` and
`F₁ = (c₂/4)B² + q₁B + (A₁ + Kφ/a)/B + P_c/(b - 1) + log B + const`, `φ = (t - 1)/t² - 1/4`,
the constants being independent of `b`.

## Main API

* The coefficients `urcbJ`, `urcbd`, `urcbD0`, `urcbEf`, `urcbM`, `urcbc2`, `urcbc1`,
  `urcbc0`, `urcbcv`, `urcbe1`, `urcbe0`, `urcbce`, `urcbl1`, `urcbl0`, `urcbcb`,
  `urcbl`, `urcbp3`, `urcbp2`, `urcbp1`, `urcbp0`, `urcbpc`, `urcbq1`, `urcbq0`,
  `urcbA1`, `urcbPc` (functions of `x, a` only).
* `urcb_F0_pf`, `urcb_F1_pf`: the two partial-fraction forms.
* `urcb_hd`, `urcb_hd2`: first and second derivatives of the common template
  `α₃B³ + α₂B² + α₁B + β/B + γ/(s - 1) + log B`, `B = a + s`.
-/

@[expose] public section

namespace SmoothedOctagon

open Real Set

/-- `J = (x - 1)(680(x - 1)² - 3S²)/(9600S²)`. -/
noncomputable def urcbJ (x : ℝ) : ℝ :=
  (x - 1) * (680 * (x - 1) ^ 2 - 3 * (1 + x) ^ 2) / (9600 * (1 + x) ^ 2)

/-- `δ = 2(a - x)`. -/
noncomputable def urcbd (x a : ℝ) : ℝ := 2 * (a - x)

/-- `D₀ = C² - δC = (a + 1)(2x + 1 - a)`. -/
noncomputable def urcbD0 (x a : ℝ) : ℝ := (a + 1) ^ 2 - urcbd x a * (a + 1)

/-- `E_f = S³(u_f - 1) + 3S - 1`. -/
noncomputable def urcbEf (x : ℝ) : ℝ := (1 + x) ^ 3 * (2401 / 3200 - 1) + 3 * (1 + x) - 1

/-- `M = S²(S² - S + 1)`. -/
noncomputable def urcbM (x : ℝ) : ℝ := (1 + x) ^ 2 * ((1 + x) ^ 2 - (1 + x) + 1)

/-- `c₂ = u_f δ²/K²`. -/
noncomputable def urcbc2 (x a : ℝ) : ℝ := 2401 / 3200 * urcbd x a ^ 2 / urcK x a ^ 2

/-- `c₁ = (δ(2u_f D₀ - E_f) + Jδ²)/K²`. -/
noncomputable def urcbc1 (x a : ℝ) : ℝ :=
  (urcbd x a * (2 * (2401 / 3200) * urcbD0 x a - urcbEf x) + urcbJ x * urcbd x a ^ 2) /
    urcK x a ^ 2

/-- `c₀ = (M + u_f D₀² - D₀E_f + Jδ(2D₀ - S³ + δC))/K²`. -/
noncomputable def urcbc0 (x a : ℝ) : ℝ :=
  (urcbM x + 2401 / 3200 * urcbD0 x a ^ 2 - urcbD0 x a * urcbEf x +
    urcbJ x * urcbd x a * (2 * urcbD0 x a - (1 + x) ^ 3 + urcbd x a * (a + 1))) /
      urcK x a ^ 2

/-- `c_v = c_w/C = JC(C² - S³)/K²`. -/
noncomputable def urcbcv (x a : ℝ) : ℝ :=
  urcbJ x * (a + 1) * ((a + 1) ^ 2 - (1 + x) ^ 3) / urcK x a ^ 2

/-- `e₁ = 2u_f δ/K`. -/
noncomputable def urcbe1 (x a : ℝ) : ℝ := 2 * (2401 / 3200) * urcbd x a / urcK x a

/-- `e₀ = (2u_f D₀ - E_f + 2Jδ)/K`. -/
noncomputable def urcbe0 (x a : ℝ) : ℝ :=
  (2 * (2401 / 3200) * urcbD0 x a - urcbEf x + 2 * urcbJ x * urcbd x a) / urcK x a

/-- `c_e = J(2C² - S³)/K`. -/
noncomputable def urcbce (x a : ℝ) : ℝ := urcbJ x * (2 * (a + 1) ^ 2 - (1 + x) ^ 3) / urcK x a

/-- `l₁ = (u_f - 1)/a - e₁`. -/
noncomputable def urcbl1 (x a : ℝ) : ℝ := (2401 / 3200 - 1) / a - urcbe1 x a

/-- `l₀ = J/a + 1 - a²/K - e₀`. -/
noncomputable def urcbl0 (x a : ℝ) : ℝ := urcbJ x / a + 1 - a ^ 2 / urcK x a - urcbe0 x a

/-- `c_b = JC/a - c_e`. -/
noncomputable def urcbcb (x a : ℝ) : ℝ := urcbJ x * (a + 1) / a - urcbce x a

/-- `ℓ = 7a/(2K)`, so that `7k/2 = ℓB`. -/
noncomputable def urcbl (x a : ℝ) : ℝ := 7 * a / (2 * urcK x a)

/-- `p₃ = -ℓc₂`. -/
noncomputable def urcbp3 (x a : ℝ) : ℝ := -(urcbl x a * urcbc2 x a)

/-- `p₂ = 4c₂ - ℓc₁`. -/
noncomputable def urcbp2 (x a : ℝ) : ℝ := 4 * urcbc2 x a - urcbl x a * urcbc1 x a

/-- `p₁ = l₁ + 4c₁ - ℓ(c₀ - 3/4)`. -/
noncomputable def urcbp1 (x a : ℝ) : ℝ :=
  urcbl1 x a + 4 * urcbc1 x a - urcbl x a * (urcbc0 x a - 3 / 4)

/-- `p₀ = l₀ + 4(c₀ - 3/4) - ℓc_w`. -/
noncomputable def urcbp0 (x a : ℝ) : ℝ :=
  urcbl0 x a + 4 * (urcbc0 x a - 3 / 4) - urcbl x a * ((a + 1) * urcbcv x a)

/-- `p_c = c_b + (4 - ℓC)c_w`. -/
noncomputable def urcbpc (x a : ℝ) : ℝ :=
  urcbcb x a + (4 - urcbl x a * (a + 1)) * ((a + 1) * urcbcv x a)

/-- `q₁ = l₁ + Kc₂/a + c₁/4`. -/
noncomputable def urcbq1 (x a : ℝ) : ℝ :=
  urcbl1 x a + urcK x a * urcbc2 x a / a + urcbc1 x a / 4

/-- `q₀ = l₀ + Kc₁/a + (c₀ - 3/4)/4`. -/
noncomputable def urcbq0 (x a : ℝ) : ℝ :=
  urcbl0 x a + urcK x a * urcbc1 x a / a + (urcbc0 x a - 3 / 4) / 4

/-- `A₁ = a + K(c₀ - 3/4)/a - Kc_w/(aC)`. -/
noncomputable def urcbA1 (x a : ℝ) : ℝ :=
  a + urcK x a * (urcbc0 x a - 3 / 4) / a - urcK x a * urcbcv x a / a

/-- `P_c = c_b + Kc_w/(aC) + c_w/4`. -/
noncomputable def urcbPc (x a : ℝ) : ℝ :=
  urcbcb x a + urcK x a * urcbcv x a / a + (a + 1) * urcbcv x a / 4

theorem urcb_K_pos {x a : ℝ} (hx : 0 < x) : 0 < urcK x a := by unfold urcK; positivity

/-- The incoming ceiling with its pole visible: `u = u_f + J/(b - 1)`. -/
theorem urcb_u {x b : ℝ} (hb : b - 1 ≠ 0) (hS : 1 + x ≠ 0) :
    ssUC x b = 2401 / 3200 + urcbJ x / (b - 1) := by
  unfold ssUC urcbJ
  field_simp
  ring

/-- `D = C² + δ(b - 1)`. -/
theorem urcb_D (x a b : ℝ) : ssDg x b a = (a + 1) ^ 2 + urcbd x a * (b - 1) := by
  unfold ssDg urcbd
  ring

/-- Partial fractions of `w` in atoms. -/
theorem urcb_w_alg {y C δ J K S M D0 Ef B : ℝ} (hy : y ≠ 0) (hK : K ≠ 0) (hB : B = C + y)
    (hD0 : D0 = C ^ 2 - δ * C) (hEf : Ef = S ^ 3 * (2401 / 3200 - 1) + 3 * S - 1) :
    (M + (C ^ 2 + δ * y) ^ 2 * (2401 / 3200 + J / y) -
        (C ^ 2 + δ * y) * (S ^ 3 * (2401 / 3200 + J / y - 1) + 3 * S - 1)) / K ^ 2 =
      2401 / 3200 * δ ^ 2 / K ^ 2 * B ^ 2 +
        (δ * (2 * (2401 / 3200) * D0 - Ef) + J * δ ^ 2) / K ^ 2 * B +
        (M + 2401 / 3200 * D0 ^ 2 - D0 * Ef + J * δ * (2 * D0 - S ^ 3 + δ * C)) / K ^ 2 +
        C * (J * C * (C ^ 2 - S ^ 3) / K ^ 2) / y := by
  subst hB hD0 hEf
  field_simp
  ring

/-- Partial fractions of `w`: `w = c₂B² + c₁B + c₀ + Cc_v/(b - 1)`. -/
theorem urcb_w {x a b : ℝ} (hb : b - 1 ≠ 0) (hS : 1 + x ≠ 0) (hK : urcK x a ≠ 0) :
    urcw x a b (ssUC x b) = urcbc2 x a * (a + b) ^ 2 + urcbc1 x a * (a + b) + urcbc0 x a +
      (a + 1) * urcbcv x a / (b - 1) := by
  rw [urcb_u hb hS]
  unfold urcw
  rw [urcb_D]
  exact urcb_w_alg hb hK (by ring) rfl rfl

/-- Partial fractions of `E_L` in atoms. -/
theorem urcb_EL_alg {y C δ J K S D0 Ef B : ℝ} (hy : y ≠ 0) (hK : K ≠ 0) (hB : B = C + y)
    (hD0 : D0 = C ^ 2 - δ * C) (hEf : Ef = S ^ 3 * (2401 / 3200 - 1) + 3 * S - 1) :
    (2 * (C ^ 2 + δ * y) * (2401 / 3200 + J / y) -
        (S ^ 3 * (2401 / 3200 + J / y - 1) + 3 * S - 1)) / K =
      2 * (2401 / 3200) * δ / K * B + (2 * (2401 / 3200) * D0 - Ef + 2 * J * δ) / K +
        J * (2 * C ^ 2 - S ^ 3) / K / y := by
  subst hB hD0 hEf
  field_simp
  ring

/-- Partial fractions of `E_L`: `E_L = e₁B + e₀ + c_e/(b - 1)`. -/
theorem urcb_EL {x a b : ℝ} (hb : b - 1 ≠ 0) (hS : 1 + x ≠ 0) (hK : urcK x a ≠ 0) :
    urcEL x a b (ssUC x b) = urcbe1 x a * (a + b) + urcbe0 x a + urcbce x a / (b - 1) := by
  rw [urcb_u hb hS]
  unfold urcEL
  rw [urcb_D]
  exact urcb_EL_alg hb hK (by ring) rfl rfl

/-- Partial fractions of `R` in atoms. -/
theorem urcb_R_alg {y C J K a B e1 e0 ce : ℝ} (hy : y ≠ 0) (hK : K ≠ 0) (ha : a ≠ 0)
    (hB0 : B ≠ 0) (hB : B = C + y) (hC : C = a + 1) :
    (2401 / 3200 + J / y - 1) * B / a + a / B + 1 - a ^ 2 / K - (e1 * B + e0 + ce / y) =
      ((2401 / 3200 - 1) / a - e1) * B + (J / a + 1 - a ^ 2 / K - e0) + a / B +
        (J * C / a - ce) / y := by
  subst hB hC
  field_simp
  ring

/-- Partial fractions of `R`: `R = l₁B + l₀ + a/B + c_b/(b - 1)`. -/
theorem urcb_R {x a b : ℝ} (hb : b - 1 ≠ 0) (hS : 1 + x ≠ 0) (hK : urcK x a ≠ 0) (ha : a ≠ 0)
    (hB : a + b ≠ 0) :
    urcR x a b (ssUC x b) =
      urcbl1 x a * (a + b) + urcbl0 x a + a / (a + b) + urcbcb x a / (b - 1) := by
  unfold urcR
  rw [urcb_EL hb hS hK, urcb_u hb hS]
  exact urcb_R_alg hb hK ha hB (by ring) rfl

/-- The first test in atoms. -/
theorem urcb_G_alg {y C K a B c2 c1 c0 cv l1 l0 cb l : ℝ} (hy : y ≠ 0) (hB0 : B ≠ 0)
    (hB : B = C + y) (hl : 7 * (a * B / K) / 2 = l * B) :
    (l1 * B + l0 + a / B + cb / y) + (4 - 7 * (a * B / K) / 2) *
        (c2 * B ^ 2 + c1 * B + c0 + C * cv / y - 3 / 4) =
      -(l * c2) * B ^ 3 + (4 * c2 - l * c1) * B ^ 2 + (l1 + 4 * c1 - l * (c0 - 3 / 4)) * B +
        (l0 + 4 * (c0 - 3 / 4) - l * (C * cv)) + a / B + (cb + (4 - l * C) * (C * cv)) / y := by
  rw [hl]
  subst hB
  field_simp
  ring

/-- **Partial fractions of `F₀`**: for `b > 1`,
`F₀ = p₃B³ + p₂B² + p₁B + a/B + p_c/(b - 1) + log B + κ₀`, `κ₀` independent of `b`. -/
theorem urcb_F0_pf {t x a b : ℝ} (ht : 0 < t) (hx : 0 < x) (ha : 0 < a) (hb : 1 < b) :
    urcF0 t x a b (ssUC x b) =
      urcbp3 x a * (a + b) ^ 3 + urcbp2 x a * (a + b) ^ 2 + urcbp1 x a * (a + b) +
        a / (a + b) + urcbpc x a / (b - 1) + log (a + b) +
        (urcbp0 x a + 4 / t - 2 / t ^ 2 - 3 / 2 + log (t * a / urcK x a)) := by
  have hK : 0 < urcK x a := by unfold urcK; positivity
  have hb1 : b - 1 ≠ 0 := by linarith
  have hS : 1 + x ≠ 0 := by linarith
  have hB : 0 < a + b := by linarith
  have hlog : log (t * urck x a b) = log (t * a / urcK x a) + log (a + b) := by
    rw [← log_mul (by positivity) hB.ne']
    unfold urck
    congr 1
    field_simp
  unfold urcF0
  rw [hlog, urcb_R hb1 hS hK.ne' ha.ne' hB.ne', urcb_w hb1 hS hK.ne']
  have hl : 7 * urck x a b / 2 = urcbl x a * (a + b) := by
    unfold urck urcbl
    field_simp
  have e := urcb_G_alg (y := b - 1) (C := a + 1) (K := urcK x a) (a := a) (B := a + b)
    (c2 := urcbc2 x a) (c1 := urcbc1 x a) (c0 := urcbc0 x a) (cv := urcbcv x a)
    (l1 := urcbl1 x a) (l0 := urcbl0 x a) (cb := urcbcb x a) (l := urcbl x a) hb1 hB.ne'
    (by ring) (by rw [← hl]; unfold urck; ring)
  have e2 : (4 - 7 * urck x a b / 2) = (4 - 7 * (a * (a + b) / urcK x a) / 2) := by
    unfold urck; ring
  rw [e2]
  unfold urcbp3 urcbp2 urcbp1 urcbp0 urcbpc
  linear_combination e

/-- The second test in atoms (`T = K/(aB)`). -/
theorem urcb_H_alg {y C K a B c2 c1 c0 cv l1 l0 cb φ : ℝ} (hy : y ≠ 0) (hB0 : B ≠ 0)
    (ha : a ≠ 0) (hB : B = C + y) :
    (l1 * B + l0 + a / B + cb / y) + (K / (a * B) + 1 / 4) *
        (c2 * B ^ 2 + c1 * B + c0 + C * cv / y - 3 / 4) + K / (a * B) * φ =
      c2 / 4 * B ^ 2 + (l1 + K * c2 / a + c1 / 4) * B + (l0 + K * c1 / a + (c0 - 3 / 4) / 4) +
        (a + K * (c0 - 3 / 4) / a - K * cv / a + K * φ / a) / B +
        (cb + K * cv / a + C * cv / 4) / y := by
  subst hB
  field_simp
  ring

/-- **Partial fractions of `F₁`**: for `b > 1`,
`F₁ = (c₂/4)B² + q₁B + (A₁ + Kφ/a)/B + P_c/(b - 1) + log B + κ₁`, `φ = (t - 1)/t² - 1/4`. -/
theorem urcb_F1_pf {t x a b : ℝ} (ht : 0 < t) (hx : 0 < x) (ha : 0 < a) (hb : 1 < b) :
    urcF1 t x a b (ssUC x b) =
      urcbc2 x a / 4 * (a + b) ^ 2 + urcbq1 x a * (a + b) +
        (urcbA1 x a + urcK x a * ((t - 1) / t ^ 2 - 1 / 4) / a) / (a + b) +
        urcbPc x a / (b - 1) + log (a + b) +
        (urcbq0 x a + 2 / t - 1 + log (t * a / urcK x a)) := by
  have hK : 0 < urcK x a := by unfold urcK; positivity
  have hb1 : b - 1 ≠ 0 := by linarith
  have hS : 1 + x ≠ 0 := by linarith
  have hB : 0 < a + b := by linarith
  have hlog : log (t * urck x a b) = log (t * a / urcK x a) + log (a + b) := by
    rw [← log_mul (by positivity) hB.ne']
    unfold urck
    congr 1
    field_simp
  have hT : 1 / urck x a b = urcK x a / (a * (a + b)) := by
    unfold urck
    field_simp
  unfold urcF1
  rw [hlog, hT, urcb_R hb1 hS hK.ne' ha.ne' hB.ne', urcb_w hb1 hS hK.ne']
  have e := urcb_H_alg (y := b - 1) (C := a + 1) (K := urcK x a) (a := a) (B := a + b)
    (c2 := urcbc2 x a) (c1 := urcbc1 x a) (c0 := urcbc0 x a) (cv := urcbcv x a)
    (l1 := urcbl1 x a) (l0 := urcbl0 x a) (cb := urcbcb x a) (φ := (t - 1) / t ^ 2 - 1 / 4)
    hb1 hB.ne' ha.ne' (by ring)
  unfold urcbq1 urcbq0 urcbA1 urcbPc
  linear_combination e

/-- The common template `α₃B³ + α₂B² + α₁B + β/B + γ/(s - 1) + log B`, `B = a + s`, and its
derivative. -/
theorem urcb_hd {a α3 α2 α1 β γ s : ℝ} (hs : 0 < a + s) (hs1 : s - 1 ≠ 0) :
    HasDerivAt (fun s => α3 * (a + s) ^ 3 + α2 * (a + s) ^ 2 + α1 * (a + s) + β / (a + s) +
        γ / (s - 1) + log (a + s))
      (3 * α3 * (a + s) ^ 2 + 2 * α2 * (a + s) + α1 - β / (a + s) ^ 2 - γ / (s - 1) ^ 2 +
        1 / (a + s)) s := by
  have hB : HasDerivAt (fun s => a + s) 1 s := (hasDerivAt_id s).const_add a
  have hy : HasDerivAt (fun s => s - 1) 1 s := (hasDerivAt_id s).sub_const 1
  have h3 := (hB.pow 3).const_mul α3
  have h2 := (hB.pow 2).const_mul α2
  have h1 := hB.const_mul α1
  have hi := (hB.inv hs.ne').const_mul β
  have hj := (hy.inv hs1).const_mul γ
  have hl := hB.log hs.ne'
  convert ((((h3.add h2).add h1).add hi).add hj).add hl using 1
  · funext z; simp only [Pi.add_apply, Pi.pow_apply, Pi.inv_apply, div_eq_mul_inv]
  · simp only [Nat.cast_ofNat]
    field_simp
    ring

/-- The second derivative of the template. -/
theorem urcb_hd2 {a α3 α2 α1 β γ s : ℝ} (hs : 0 < a + s) (hs1 : s - 1 ≠ 0) :
    HasDerivAt (fun s => 3 * α3 * (a + s) ^ 2 + 2 * α2 * (a + s) + α1 - β / (a + s) ^ 2 -
        γ / (s - 1) ^ 2 + 1 / (a + s))
      (6 * α3 * (a + s) + 2 * α2 + 2 * β / (a + s) ^ 3 + 2 * γ / (s - 1) ^ 3 -
        1 / (a + s) ^ 2) s := by
  have hB : HasDerivAt (fun s => a + s) 1 s := (hasDerivAt_id s).const_add a
  have hy : HasDerivAt (fun s => s - 1) 1 s := (hasDerivAt_id s).sub_const 1
  have h2 := (hB.pow 2).const_mul (3 * α3)
  have h1 := hB.const_mul (2 * α2)
  have hi := ((hB.pow 2).inv (pow_ne_zero 2 hs.ne')).const_mul β
  have hj := ((hy.pow 2).inv (pow_ne_zero 2 hs1)).const_mul γ
  have hk := hB.inv hs.ne'
  convert ((((h2.add h1).add_const α1).sub hi).sub hj).add hk using 1
  · funext z; simp only [Pi.add_apply, Pi.sub_apply, Pi.pow_apply, Pi.inv_apply, div_eq_mul_inv,
      one_mul]
  · simp only [Nat.cast_ofNat, Pi.pow_apply]
    field_simp
    ring

end SmoothedOctagon
