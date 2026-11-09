module

public import SmoothedOctagon.Exclusion.Mixed.ShortHand.Heavy.S4HandW3c

/-!
# Gate S4, hand proof W3 (d): the cost along the lower norm and its normalized numerator

With `E = S³(u - 1) + 3S - 1`, `M = S²(S² - S + 1)`, `W = M + uD² - DE`, the cost bracket of `Ψ` is
`r₁ = T/(aBK) + log(2aB/K)`,

`T = (u - 1)B²K + a²K + aBK - a³B - aB(2uD - E) + W - 3K²/4`

(an identity in the atoms `a, B, K, D, E, M, u`, `hl46_w3_r1_atoms`). As `E` is affine in `u`
with slope `S³`, `r₁(u) = r₁(v) + (u - v)ρ`, `ρ = T_u/(aBK)` (`hl46_w3_psi_split`), which is the
form in which the norm curve `U` is compared with the lower norm `v`.

Along `b = x(1 + d)`, `u = v(x, d)` (`a` fixed), the cost `F = r₁(x, v)` has derivative
`f = n/(aB²K²) - 1/25` (`hl46_w3_F_deriv`), where

`n = T_x BK - T(B_x K + BK_x) + aBK(KB_x - BK_x) + aB²K²/25`

and `T_x` is the chain rule in the atoms (`v_x = 9/1000`). The normalized numerator is
`N = (10/3)AC²H²(f + 1/25) = (781250/3)n` (`A = 5a`, `C = 5B`, `H = 25K`).

## Main API

* `hl46W3T`, `hl46W3Tx` (atom level), `hl46W3E`, `hl46W3Ex`, `hl46W3TC`, `hl46W3TxC`,
  `hl46W3F`, `hl46W3n`, `hl46W3N`.
* `hl46_w3_r1_atoms`, `hl46_w3_psi_split`, `hl46_w3_psi_eq`, `hl46_w3_T_deriv`,
  `hl46_w3_TC_deriv`, `hl46_w3_F_deriv`.
-/

@[expose] public section

namespace SmoothedOctagon

open Real

/-- `T = (u - 1)B²K + a²K + aBK - a³B - aB(2uD - E) + (M + uD² - DE) - 3K²/4`, in atoms. -/
noncomputable def hl46W3T (a B K D E M u : ℝ) : ℝ :=
  (u - 1) * B ^ 2 * K + a ^ 2 * K + a * B * K - a ^ 3 * B - a * B * (2 * u * D - E) +
    (M + u * D ^ 2 - D * E) - 3 / 4 * K ^ 2

/-- The chain-rule derivative of `T` (`a` constant). -/
noncomputable def hl46W3Tx (a B K D E _M u B1 K1 D1 E1 M1 u1 : ℝ) : ℝ :=
  (2 * (u - 1) * B * K + a * K - a ^ 3 - a * (2 * u * D - E)) * B1 +
    ((u - 1) * B ^ 2 + a ^ 2 + a * B - 3 / 2 * K) * K1 + (-(2 * a * u * B) + 2 * u * D - E) * D1 +
    (a * B - D) * E1 + M1 + (B ^ 2 * K - 2 * a * B * D + D ^ 2) * u1

/-- **The cost bracket in atoms**: `r₁ = T/(aBK) + (log)`, and `r₁(u) - r₁(v) = (u - v)T_u/(aBK)`
(`E(u) = E(v) + S³(u - v)`). -/
theorem hl46_w3_r1_atoms {al B K D Ev S3 M u v : ℝ} (ha : al ≠ 0) (hB : B ≠ 0) (hK : K ≠ 0) :
    K / (al * B) * ((M + D ^ 2 * u - D * (Ev + S3 * (u - v))) / K ^ 2 - 3 / 4) + 1 +
        ((u - 1) * B / al + al / B - al ^ 2 / K - (2 * D * u - (Ev + S3 * (u - v))) / K) =
      hl46W3T al B K D Ev M v / (al * B * K) + (u - v) * hl46W3Tu al B K D S3 / (al * B * K) := by
  unfold hl46W3T hl46W3Tu
  field_simp
  ring

/-- `Ψ = Γ - (T(v)/(aBK) + log(2aB/K) + (u - v)T_u/(aBK))/7`. -/
theorem hl46_w3_psi_split {x be al u v : ℝ} (ha : al ≠ 0) (hB : al + be ≠ 0)
    (hK : x * (x + 2) + al ^ 2 ≠ 0) :
    hh46S4PsiC x be al u = hh46S4G x u -
      (hl46W3T al (al + be) (x * (x + 2) + al ^ 2) (hsDg x be al) (hh46S4P x v)
            ((1 + x) ^ 2 * ((1 + x) ^ 2 - (1 + x) + 1)) v / (al * (al + be) * (x * (x + 2) + al ^ 2)) +
          log (2 * al * (al + be) / (x * (x + 2) + al ^ 2)) +
        (u - v) * hl46W3Tu al (al + be) (x * (x + 2) + al ^ 2) (hsDg x be al) ((1 + x) ^ 3) /
          (al * (al + be) * (x * (x + 2) + al ^ 2))) / 7 := by
  have hE : hh46S4P x u = hh46S4P x v + (1 + x) ^ 3 * (u - v) := by unfold hh46S4P; ring
  have key := hl46_w3_r1_atoms (D := hsDg x be al) (Ev := hh46S4P x v) (S3 := (1 + x) ^ 3)
    (M := (1 + x) ^ 2 * ((1 + x) ^ 2 - (1 + x) + 1)) (u := u) (v := v) ha hB hK
  unfold hh46S4PsiC hh46S4Wc hh46S4Rest hh46S4EL
  rw [hE, key]
  ring

/-! ### The cost along the lower norm -/

/-- `E(x, v)` on the lower norm. -/
noncomputable def hl46W3E (x d : ℝ) : ℝ := hh46S4P x (hl46W3v x d)

/-- `E_x = 3S²(v - 1) + S³v_x + 3`, `v_x = 9/1000`. -/
noncomputable def hl46W3Ex (x d : ℝ) : ℝ :=
  3 * (1 + x) ^ 2 * (hl46W3v x d - 1) + (1 + x) ^ 3 * (9 / 1000) + 3

/-- `T` on the curve with `u = v`. -/
noncomputable def hl46W3TC (x d : ℝ) : ℝ :=
  hl46W3T (1 + 13 / 5 * d) (hl46W3B x d) (hl46W3K x d) (hl46W3D x d) (hl46W3E x d)
    ((1 + x) ^ 2 * ((1 + x) ^ 2 - (1 + x) + 1)) (hl46W3v x d)

/-- `T_x` on the curve with `u = v`. -/
noncomputable def hl46W3TxC (x d : ℝ) : ℝ :=
  hl46W3Tx (1 + 13 / 5 * d) (hl46W3B x d) (hl46W3K x d) (hl46W3D x d) (hl46W3E x d)
    ((1 + x) ^ 2 * ((1 + x) ^ 2 - (1 + x) + 1)) (hl46W3v x d) (1 + d) (2 * x + 2) (hl46W3Dx x d)
    (hl46W3Ex x d) (4 * (1 + x) ^ 3 - 3 * (1 + x) ^ 2 + 2 * (1 + x)) (9 / 1000)

/-- The cost `F = r₁(x, v) = T/(aBK) + log(2aB/K)` along the lower norm. -/
noncomputable def hl46W3F (x d : ℝ) : ℝ :=
  hl46W3TC x d / ((1 + 13 / 5 * d) * hl46W3B x d * hl46W3K x d) +
    log (2 * (1 + 13 / 5 * d) * hl46W3B x d / hl46W3K x d)

/-- `n = T_x BK - T(B_x K + BK_x) + aBK(KB_x - BK_x) + aB²K²/25`, so `f + 1/25 = n/(aB²K²)`. -/
noncomputable def hl46W3n (x d : ℝ) : ℝ :=
  hl46W3TxC x d * hl46W3B x d * hl46W3K x d -
      hl46W3TC x d * ((1 + d) * hl46W3K x d + hl46W3B x d * (2 * x + 2)) +
    (1 + 13 / 5 * d) * hl46W3B x d * hl46W3K x d *
      (hl46W3K x d * (1 + d) - hl46W3B x d * (2 * x + 2)) +
    (1 + 13 / 5 * d) * hl46W3B x d ^ 2 * hl46W3K x d ^ 2 / 25

/-- The normalized numerator `N = (10/3)AC²H²(f + 1/25) = (781250/3)n`. -/
noncomputable def hl46W3N (x d : ℝ) : ℝ := 781250 / 3 * hl46W3n x d

/-- `Ψ` on the shape curve, split at the lower norm. -/
theorem hl46_w3_psi_eq {x d : ℝ} (hx : 2 ≤ x) (hx' : x ≤ 13 / 6) (hd : 0 ≤ d) (hd' : d ≤ 1 / 19)
    (u : ℝ) :
    hh46S4PsiC x (x * (1 + d)) (1 + 13 / 5 * d) u =
      hh46S4G x u - (hl46W3F x d + (u - hl46W3v x d) * hl46W3rho x d) / 7 := by
  obtain ⟨ha, haB, hK, -, -⟩ := hl46_w3_curve hx hx' hd hd'
  have := hl46_w3_psi_split (x := x) (be := x * (1 + d)) (al := 1 + 13 / 5 * d) (u := u)
    (v := hl46W3v x d) (ne_of_gt (by linarith)) (ne_of_gt (by unfold hl46W3B at haB; linarith))
    (ne_of_gt (by unfold hl46W3K at hK; linarith))
  rw [this]
  unfold hl46W3F hl46W3rho hl46W3TC hl46W3TuC hl46W3B hl46W3K hl46W3D hl46W3E
  ring

/-- The chain rule for `T` in the atoms (`a` constant). -/
theorem hl46_w3_T_deriv {fB fK fD fE fM fu : ℝ → ℝ} {a B1 K1 D1 E1 M1 u1 x : ℝ}
    (hB : HasDerivAt fB B1 x) (hK : HasDerivAt fK K1 x) (hD : HasDerivAt fD D1 x)
    (hE : HasDerivAt fE E1 x) (hM : HasDerivAt fM M1 x) (hu : HasDerivAt fu u1 x) :
    HasDerivAt (fun x => hl46W3T a (fB x) (fK x) (fD x) (fE x) (fM x) (fu x))
      (hl46W3Tx a (fB x) (fK x) (fD x) (fE x) (fM x) (fu x) B1 K1 D1 E1 M1 u1) x := by
  have t1 := ((hu.sub_const 1).fun_mul (hB.fun_pow 2)).fun_mul hK
  have t2 := hK.const_mul (a ^ 2)
  have t3 := (hB.const_mul a).fun_mul hK
  have t4 := hB.const_mul (a ^ 3)
  have t5 := (hB.const_mul a).fun_mul (((hu.const_mul 2).fun_mul hD).fun_sub hE)
  have t6 := (hM.fun_add (hu.fun_mul (hD.fun_pow 2))).fun_sub (hD.fun_mul hE)
  have t7 := (hK.fun_pow 2).const_mul (3 / 4)
  have := (((((t1.fun_add t2).fun_add t3).fun_sub t4).fun_sub t5).fun_add t6).fun_sub t7
  refine this.congr_deriv ?_
  unfold hl46W3Tx
  push_cast
  ring

theorem hl46_w3_E_dx (x d : ℝ) : HasDerivAt (fun x => hl46W3E x d) (hl46W3Ex x d) x := by
  have := ((((hl46_w3_S3_dx x).fun_mul ((hl46_w3_v_deriv x d).sub_const 1)).fun_add
    (((hasDerivAt_id' x).const_add 1).const_mul 3)).sub_const 1)
  refine this.congr_deriv ?_
  unfold hl46W3Ex
  ring

theorem hl46_w3_M_dx (x : ℝ) :
    HasDerivAt (fun x : ℝ => (1 + x) ^ 2 * ((1 + x) ^ 2 - (1 + x) + 1))
      (4 * (1 + x) ^ 3 - 3 * (1 + x) ^ 2 + 2 * (1 + x)) x := by
  have hS : HasDerivAt (fun x : ℝ => 1 + x) 1 x := (hasDerivAt_id' x).const_add 1
  have := (hS.fun_pow 2).fun_mul (((hS.fun_pow 2).fun_sub hS).add_const 1)
  refine this.congr_deriv ?_
  push_cast
  ring

theorem hl46_w3_TC_deriv (x d : ℝ) : HasDerivAt (fun x => hl46W3TC x d) (hl46W3TxC x d) x :=
  hl46_w3_T_deriv (hl46_w3_B_dx x d) (hl46_w3_K_dx x d) (hl46_w3_D_dx x d) (hl46_w3_E_dx x d)
    (hl46_w3_M_dx x) (hl46_w3_v_deriv x d)

/-- The `x`-derivative of the cost along the lower norm: `f = n/(aB²K²) - 1/25`. -/
theorem hl46_w3_F_deriv {x d : ℝ} (hx : 2 ≤ x) (hx' : x ≤ 13 / 6) (hd : 0 ≤ d) (hd' : d ≤ 1 / 19) :
    HasDerivAt (fun x => hl46W3F x d)
      (hl46W3n x d / ((1 + 13 / 5 * d) * hl46W3B x d ^ 2 * hl46W3K x d ^ 2) - 1 / 25) x := by
  obtain ⟨ha, haB, hK, -, -⟩ := hl46_w3_curve hx hx' hd hd'
  have ha0 : (1 + 13 / 5 * d) ≠ 0 := by linarith
  have hB0 : hl46W3B x d ≠ 0 := by linarith
  have hK0 : hl46W3K x d ≠ 0 := hK.ne'
  have hB := hl46_w3_B_dx x d
  have hKd := hl46_w3_K_dx x d
  have h1 := (hl46_w3_TC_deriv x d).fun_div (((hasDerivAt_const x (1 + 13 / 5 * d)).fun_mul
    hB).fun_mul hKd) (by positivity)
  have h2 := ((hB.const_mul (2 * (1 + 13 / 5 * d))).fun_div hKd hK0).log (by positivity)
  have := h1.fun_add h2
  refine this.congr_deriv ?_
  unfold hl46W3n
  field_simp
  ring

end SmoothedOctagon
