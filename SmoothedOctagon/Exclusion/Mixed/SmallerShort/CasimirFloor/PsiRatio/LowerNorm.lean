module

public import SmoothedOctagon.Exclusion.Mixed.SmallerShort.CasimirFloor.PsiRatio.NormCoefficient

/-!
# Smaller-short window, Casimir floor: the cost along the lower norm and its normalized numerator

With `E = S³(u - 1) + 3S - 1`, `M = S²(S² - S + 1)`, `W = M + uD² - DE`, the cost bracket of `Ψ` is
`r₁ = T/(aBK) + log(2aB/K)`,

`T = (u - 1)B²K + a²K + aBK - a³B - aB(2uD - E) + W - 3K²/4`

(an identity in the atoms `a, B, K, D, E, M, u`, `cas_w3_r1_atoms`). As `E` is affine in `u`
with slope `S³`, `r₁(u) = r₁(v) + (u - v)ρ`, `ρ = T_u/(aBK)` (`cas_w3_psi_split`), which is the
form in which the norm curve `U` is compared with the lower norm `v`.

Along `b = x(1 + d)`, `u = v(x, d)` (`a` fixed), the cost `F = r₁(x, v)` has derivative
`f = n/(aB²K²) - 1/25` (`cas_w3_F_deriv`), where

`n = T_x BK - T(B_x K + BK_x) + aBK(KB_x - BK_x) + aB²K²/25`

and `T_x` is the chain rule in the atoms (`v_x = 9/1000`). The normalized numerator is
`N = (10/3)AC²H²(f + 1/25) = (781250/3)n` (`A = 5a`, `C = 5B`, `H = 25K`).

## Main API

* `casW3T`, `casW3Tx` (atom level), `casW3E`, `casW3Ex`, `casW3TC`, `casW3TxC`,
  `casW3F`, `casW3n`, `casW3N`.
* `cas_w3_r1_atoms`, `cas_w3_psi_split`, `cas_w3_psi_eq`, `cas_w3_T_deriv`,
  `cas_w3_TC_deriv`, `cas_w3_F_deriv`.
-/

@[expose] public section

namespace SmoothedOctagon

open Real

/-- `T = (u - 1)B²K + a²K + aBK - a³B - aB(2uD - E) + (M + uD² - DE) - 3K²/4`, in atoms. -/
noncomputable def casW3T (a B K D E M u : ℝ) : ℝ :=
  (u - 1) * B ^ 2 * K + a ^ 2 * K + a * B * K - a ^ 3 * B - a * B * (2 * u * D - E) +
    (M + u * D ^ 2 - D * E) - 3 / 4 * K ^ 2

/-- The chain-rule derivative of `T` (`a` constant). -/
noncomputable def casW3Tx (a B K D E _M u B1 K1 D1 E1 M1 u1 : ℝ) : ℝ :=
  (2 * (u - 1) * B * K + a * K - a ^ 3 - a * (2 * u * D - E)) * B1 +
    ((u - 1) * B ^ 2 + a ^ 2 + a * B - 3 / 2 * K) * K1 + (-(2 * a * u * B) + 2 * u * D - E) * D1 +
    (a * B - D) * E1 + M1 + (B ^ 2 * K - 2 * a * B * D + D ^ 2) * u1

/-- **The cost bracket in atoms**: `r₁ = T/(aBK) + (log)`, and `r₁(u) - r₁(v) = (u - v)T_u/(aBK)`
(`E(u) = E(v) + S³(u - v)`). -/
theorem cas_w3_r1_atoms {al B K D Ev S3 M u v : ℝ} (ha : al ≠ 0) (hB : B ≠ 0) (hK : K ≠ 0) :
    K / (al * B) * ((M + D ^ 2 * u - D * (Ev + S3 * (u - v))) / K ^ 2 - 3 / 4) + 1 +
        ((u - 1) * B / al + al / B - al ^ 2 / K - (2 * D * u - (Ev + S3 * (u - v))) / K) =
      casW3T al B K D Ev M v / (al * B * K) + (u - v) * casW3Tu al B K D S3 / (al * B * K) := by
  unfold casW3T casW3Tu
  field_simp
  ring

/-- `Ψ = Γ - (T(v)/(aBK) + log(2aB/K) + (u - v)T_u/(aBK))/7`. -/
theorem cas_w3_psi_split {x be al u v : ℝ} (ha : al ≠ 0) (hB : al + be ≠ 0)
    (hK : x * (x + 2) + al ^ 2 ≠ 0) :
    casClosedPsiC x be al u = casClosedG x u -
      (casW3T al (al + be) (x * (x + 2) + al ^ 2) (ssDg x be al) (casClosedP x v)
            ((1 + x) ^ 2 * ((1 + x) ^ 2 - (1 + x) + 1)) v / (al * (al + be) * (x * (x + 2) + al ^ 2)) +
          log (2 * al * (al + be) / (x * (x + 2) + al ^ 2)) +
        (u - v) * casW3Tu al (al + be) (x * (x + 2) + al ^ 2) (ssDg x be al) ((1 + x) ^ 3) /
          (al * (al + be) * (x * (x + 2) + al ^ 2))) / 7 := by
  have hE : casClosedP x u = casClosedP x v + (1 + x) ^ 3 * (u - v) := by unfold casClosedP; ring
  have key := cas_w3_r1_atoms (D := ssDg x be al) (Ev := casClosedP x v) (S3 := (1 + x) ^ 3)
    (M := (1 + x) ^ 2 * ((1 + x) ^ 2 - (1 + x) + 1)) (u := u) (v := v) ha hB hK
  unfold casClosedPsiC casClosedWc casClosedRest casClosedEL
  rw [hE, key]
  ring

/-! ### The cost along the lower norm -/

/-- `E(x, v)` on the lower norm. -/
noncomputable def casW3E (x d : ℝ) : ℝ := casClosedP x (casW3v x d)

/-- `E_x = 3S²(v - 1) + S³v_x + 3`, `v_x = 9/1000`. -/
noncomputable def casW3Ex (x d : ℝ) : ℝ :=
  3 * (1 + x) ^ 2 * (casW3v x d - 1) + (1 + x) ^ 3 * (9 / 1000) + 3

/-- `T` on the curve with `u = v`. -/
noncomputable def casW3TC (x d : ℝ) : ℝ :=
  casW3T (1 + 13 / 5 * d) (casW3B x d) (casW3K x d) (casW3D x d) (casW3E x d)
    ((1 + x) ^ 2 * ((1 + x) ^ 2 - (1 + x) + 1)) (casW3v x d)

/-- `T_x` on the curve with `u = v`. -/
noncomputable def casW3TxC (x d : ℝ) : ℝ :=
  casW3Tx (1 + 13 / 5 * d) (casW3B x d) (casW3K x d) (casW3D x d) (casW3E x d)
    ((1 + x) ^ 2 * ((1 + x) ^ 2 - (1 + x) + 1)) (casW3v x d) (1 + d) (2 * x + 2) (casW3Dx x d)
    (casW3Ex x d) (4 * (1 + x) ^ 3 - 3 * (1 + x) ^ 2 + 2 * (1 + x)) (9 / 1000)

/-- The cost `F = r₁(x, v) = T/(aBK) + log(2aB/K)` along the lower norm. -/
noncomputable def casW3F (x d : ℝ) : ℝ :=
  casW3TC x d / ((1 + 13 / 5 * d) * casW3B x d * casW3K x d) +
    log (2 * (1 + 13 / 5 * d) * casW3B x d / casW3K x d)

/-- `n = T_x BK - T(B_x K + BK_x) + aBK(KB_x - BK_x) + aB²K²/25`, so `f + 1/25 = n/(aB²K²)`. -/
noncomputable def casW3n (x d : ℝ) : ℝ :=
  casW3TxC x d * casW3B x d * casW3K x d -
      casW3TC x d * ((1 + d) * casW3K x d + casW3B x d * (2 * x + 2)) +
    (1 + 13 / 5 * d) * casW3B x d * casW3K x d *
      (casW3K x d * (1 + d) - casW3B x d * (2 * x + 2)) +
    (1 + 13 / 5 * d) * casW3B x d ^ 2 * casW3K x d ^ 2 / 25

/-- The normalized numerator `N = (10/3)AC²H²(f + 1/25) = (781250/3)n`. -/
noncomputable def casW3N (x d : ℝ) : ℝ := 781250 / 3 * casW3n x d

/-- `Ψ` on the shape curve, split at the lower norm. -/
theorem cas_w3_psi_eq {x d : ℝ} (hx : 2 ≤ x) (hx' : x ≤ 13 / 6) (hd : 0 ≤ d) (hd' : d ≤ 1 / 19)
    (u : ℝ) :
    casClosedPsiC x (x * (1 + d)) (1 + 13 / 5 * d) u =
      casClosedG x u - (casW3F x d + (u - casW3v x d) * casW3rho x d) / 7 := by
  obtain ⟨ha, haB, hK, -, -⟩ := cas_w3_curve hx hx' hd hd'
  have := cas_w3_psi_split (x := x) (be := x * (1 + d)) (al := 1 + 13 / 5 * d) (u := u)
    (v := casW3v x d) (ne_of_gt (by linarith)) (ne_of_gt (by unfold casW3B at haB; linarith))
    (ne_of_gt (by unfold casW3K at hK; linarith))
  rw [this]
  unfold casW3F casW3rho casW3TC casW3TuC casW3B casW3K casW3D casW3E
  ring

/-- The chain rule for `T` in the atoms (`a` constant). -/
theorem cas_w3_T_deriv {fB fK fD fE fM fu : ℝ → ℝ} {a B1 K1 D1 E1 M1 u1 x : ℝ}
    (hB : HasDerivAt fB B1 x) (hK : HasDerivAt fK K1 x) (hD : HasDerivAt fD D1 x)
    (hE : HasDerivAt fE E1 x) (hM : HasDerivAt fM M1 x) (hu : HasDerivAt fu u1 x) :
    HasDerivAt (fun x => casW3T a (fB x) (fK x) (fD x) (fE x) (fM x) (fu x))
      (casW3Tx a (fB x) (fK x) (fD x) (fE x) (fM x) (fu x) B1 K1 D1 E1 M1 u1) x := by
  have t1 := ((hu.sub_const 1).fun_mul (hB.fun_pow 2)).fun_mul hK
  have t2 := hK.const_mul (a ^ 2)
  have t3 := (hB.const_mul a).fun_mul hK
  have t4 := hB.const_mul (a ^ 3)
  have t5 := (hB.const_mul a).fun_mul (((hu.const_mul 2).fun_mul hD).fun_sub hE)
  have t6 := (hM.fun_add (hu.fun_mul (hD.fun_pow 2))).fun_sub (hD.fun_mul hE)
  have t7 := (hK.fun_pow 2).const_mul (3 / 4)
  have := (((((t1.fun_add t2).fun_add t3).fun_sub t4).fun_sub t5).fun_add t6).fun_sub t7
  refine this.congr_deriv ?_
  unfold casW3Tx
  push_cast
  ring

theorem cas_w3_E_dx (x d : ℝ) : HasDerivAt (fun x => casW3E x d) (casW3Ex x d) x := by
  have := ((((cas_w3_S3_dx x).fun_mul ((cas_w3_v_deriv x d).sub_const 1)).fun_add
    (((hasDerivAt_id' x).const_add 1).const_mul 3)).sub_const 1)
  refine this.congr_deriv ?_
  unfold casW3Ex
  ring

theorem cas_w3_M_dx (x : ℝ) :
    HasDerivAt (fun x : ℝ => (1 + x) ^ 2 * ((1 + x) ^ 2 - (1 + x) + 1))
      (4 * (1 + x) ^ 3 - 3 * (1 + x) ^ 2 + 2 * (1 + x)) x := by
  have hS : HasDerivAt (fun x : ℝ => 1 + x) 1 x := (hasDerivAt_id' x).const_add 1
  have := (hS.fun_pow 2).fun_mul (((hS.fun_pow 2).fun_sub hS).add_const 1)
  refine this.congr_deriv ?_
  push_cast
  ring

theorem cas_w3_TC_deriv (x d : ℝ) : HasDerivAt (fun x => casW3TC x d) (casW3TxC x d) x :=
  cas_w3_T_deriv (cas_w3_B_dx x d) (cas_w3_K_dx x d) (cas_w3_D_dx x d) (cas_w3_E_dx x d)
    (cas_w3_M_dx x) (cas_w3_v_deriv x d)

/-- The `x`-derivative of the cost along the lower norm: `f = n/(aB²K²) - 1/25`. -/
theorem cas_w3_F_deriv {x d : ℝ} (hx : 2 ≤ x) (hx' : x ≤ 13 / 6) (hd : 0 ≤ d) (hd' : d ≤ 1 / 19) :
    HasDerivAt (fun x => casW3F x d)
      (casW3n x d / ((1 + 13 / 5 * d) * casW3B x d ^ 2 * casW3K x d ^ 2) - 1 / 25) x := by
  obtain ⟨ha, haB, hK, -, -⟩ := cas_w3_curve hx hx' hd hd'
  have ha0 : (1 + 13 / 5 * d) ≠ 0 := by linarith
  have hB0 : casW3B x d ≠ 0 := by linarith
  have hK0 : casW3K x d ≠ 0 := hK.ne'
  have hB := cas_w3_B_dx x d
  have hKd := cas_w3_K_dx x d
  have h1 := (cas_w3_TC_deriv x d).fun_div (((hasDerivAt_const x (1 + 13 / 5 * d)).fun_mul
    hB).fun_mul hKd) (by positivity)
  have h2 := ((hB.const_mul (2 * (1 + 13 / 5 * d))).fun_div hKd hK0).log (by positivity)
  have := h1.fun_add h2
  refine this.congr_deriv ?_
  unfold casW3n
  field_simp
  ring

end SmoothedOctagon
