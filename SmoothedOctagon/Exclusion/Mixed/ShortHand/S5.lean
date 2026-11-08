module

public import SmoothedOctagon.Exclusion.Mixed.ShortHand.Interface

/-!
# Hand proof of the smaller-short case, gate S5: the root forces a negative physical shear

`MIXED_SMALLER_SHORT_SMALL_SHAPE_ROOT_SHEAR` (2)-(34), with `OUTER_ENVELOPE`,
`ENVELOPE_SCALE_MONOTONICITY` §1, `ROOT_INCOMING_MONOTONICITY`, `INCOMING_NORM_BOUND`; inventory
HS-S567 Part II (E.1-E.6, S5.1-S5.10). On the small-shape domain: the actual outer root
(`HsData.root_zero`) and the envelope (`hs_env_weighted`, `m = 0`) give `𝓡(u; p, q) ≥ 0` at
`p = τq`; the incoming monotonicity (`hs5_u_mono`) and the rational majorant `û`
(`hs5_Vbar_le_uhat`) give `𝓡(û; p, q) ≥ 0`; this contradicts `hs5_residual_neg` unless
`q > q_b = (29/30)q_c`; and `q > q_b` forces `√3hR + 13A/3 < 0` (`hs5_shear_sign`).

## Main API

* `hsUhat5` (`û = 755/996 + (x - 2)/100`), `hs5J2`, `hs5Jt` (the face values of S5.6).
* Stable: `hs5_Vbar_le_uhat`, `hs5_u_mono`, `hs5_log_tangent`, `hs5_J_neg`, `hs5_residual_neg`,
  `hs5_shear_sign`.
* Gate: `HsData.s5`, `M2Short.hs_S5`.
-/

@[expose] public section

namespace SmoothedOctagon

open Set Real

/-- The rational majorant `û = 755/996 + (x - 2)/100` (`SMALL_SHAPE_ROOT_SHEAR` (5)). -/
noncomputable def hsUhat5 (x : ℝ) : ℝ := 755 / 996 + (x - 2) / 100

/-- The face value at `p = 2q_b` with the second log tangent (`SMALL_SHAPE_ROOT_SHEAR` (15)):
`J₂ = E₀ + (û - 1)/r_A + r_A + 277/1000 + q_b(5/(2r_A) - 2A₁ - 1 - A₃) + 2q_b²A₂` at `u = û`,
`q_b = (29/30)q_c`. -/
noncomputable def hs5J2 (x be al : ℝ) : ℝ :=
  hsE0 x (hsUhat5 x) + (hsUhat5 x - 1) / hsRA al be + hsRA al be + 277 / 1000 +
    29 / 30 * hsQc x al * (5 / (2 * hsRA al be) - 2 * hsA1 x be al (hsUhat5 x) - 1 -
      hsA3 x be al (hsUhat5 x)) +
    2 * (29 / 30 * hsQc x al) ^ 2 * hsA2 x be al (hsUhat5 x)

/-- The face value at `p = τ r_A` with `log τ ≤ τ - 1` (`SMALL_SHAPE_ROOT_SHEAR` (16)):
`J_τ = E₀ + (û - 1)/r_A + r_A + τ - τr_A A₁ + q_b(τr_A A₂ + 1/(τr_A) - 1 - A₃)`. -/
noncomputable def hs5Jt (x be al τ : ℝ) : ℝ :=
  hsE0 x (hsUhat5 x) + (hsUhat5 x - 1) / hsRA al be + hsRA al be + τ -
    τ * hsRA al be * hsA1 x be al (hsUhat5 x) +
    29 / 30 * hsQc x al * (τ * hsRA al be * hsA2 x be al (hsUhat5 x) + 1 / (τ * hsRA al be) - 1 -
      hsA3 x be al (hsUhat5 x))

/-- **`V̄ ≤ û`** (`SMALL_SHAPE_ROOT_SHEAR` (5)-(6); inventory HS-S567 S5.1): for `2 ≤ x ≤ 13/6`,
`V̄(x) ≤ 755/996 + (x - 2)/100` (difference `t(8715t² + 4012t + 1)/(24900(3 + t)(35t + 83))`,
`t = x - 2`). Status: stable. -/
theorem hs5_Vbar_le_uhat {x : ℝ} (hx : 2 ≤ x) (hx2 : x ≤ 13 / 6) : hsVbar x ≤ hsUhat5 x := by
  sorry

/-- **The residual is monotone in the incoming norm** (`ROOT_INCOMING_MONOTONICITY` (2)-(8);
inventory HS-S567 E.5): for `x > 1`, `1 ≤ α ≤ x ≤ β`, `0 < q ≤ 1/7`, `0 < p ≤ r_A`,
`𝓡(u; p, q) = C(p) + qL(p)` is nondecreasing in `u` (bilinear corner check of the slope).
Status: stable. -/
theorem hs5_u_mono {x be al p q u u' : ℝ} (hx : 1 < x) (hal : 1 ≤ al) (hax : al ≤ x)
    (hxb : x ≤ be) (hq : 0 < q) (hq7 : q ≤ 1 / 7) (hp : 0 < p) (hpr : p ≤ hsRA al be)
    (huu : u ≤ u') : hsPhi x be al u p 0 q ≤ hsPhi x be al u' p 0 q := by
  sorry

/-- **The second log tangent** (`SMALL_SHAPE_ROOT_SHEAR` (11); inventory HS-S567 S5.4): for `y > 0`,
`log y < 5y/4 - 1223/1000` (`log(5/4) > 488/2187`). Status: stable. -/
theorem hs5_log_tangent {y : ℝ} (hy : 0 < y) : log y < 5 * y / 4 - 1223 / 1000 := by
  sorry

/-- **The three face values are negative** (`SMALL_SHAPE_ROOT_SHEAR` (15)-(27); inventory HS-S567
S5.6-S5.8): on the enlarged domain (9) `2 ≤ x ≤ 13/6`, `1 ≤ α ≤ 22/19`,
`x(1 + (α - 1)/3) ≤ β ≤ x(1 + 5(α - 1)/13)`: `J₂ < 0`, `J_θ < 0` (`θ = 223/250`), `J₁ < 0`
(convexity in `β`, then six polynomial signs). Status: stable. -/
theorem hs5_J_neg {x al be : ℝ} (hx : 2 ≤ x) (hx2 : x ≤ 13 / 6) (hal : 1 ≤ al) (hal' : al ≤ 22 / 19)
    (hb : x * (1 + (al - 1) / 3) ≤ be) (hb' : be ≤ x * (1 + 5 * (al - 1) / 13)) :
    hs5J2 x be al < 0 ∧ hs5Jt x be al (223 / 250) < 0 ∧ hs5Jt x be al 1 < 0 := by
  sorry

/-- **The residual at `û` is negative below `q_b`** (`SMALL_SHAPE_ROOT_SHEAR` (9)-(27); inventory
HS-S567 S5.3-S5.8): on domain (9), for `0 ≤ q ≤ q_b = (29/30)q_c`, `0 < p`, `2q ≤ p ≤ r_A`:
`𝓡(û; p, q) < 0` (`hs_A2_pos`; the `q = 0` face; affine in `q`; faces `q = q_b`, `p = 2q` through
`hs5_log_tangent` and `hs5_J_neg`). Status: stable. -/
theorem hs5_residual_neg {x al be p q : ℝ} (hx : 2 ≤ x) (hx2 : x ≤ 13 / 6) (hal : 1 ≤ al)
    (hal' : al ≤ 22 / 19) (hb : x * (1 + (al - 1) / 3) ≤ be) (hb' : be ≤ x * (1 + 5 * (al - 1) / 13))
    (hq : 0 ≤ q) (hqb : q ≤ 29 / 30 * hsQc x al) (hp : 0 < p) (hpq : 2 * q ≤ p)
    (hpr : p ≤ hsRA al be) : hsPhi x be al (hsUhat5 x) p 0 q < 0 := by
  sorry

/-- **The shear sign above `q_b`** (`SMALL_SHAPE_ROOT_SHEAR` (28)-(34), (2)-(3); inventory HS-S567
S5.10, including the missing `m > 0`): on `2 ≤ x ≤ 13/6`, `0 ≤ δ ≤ 1/19`, `13δ/5 ≤ α - 1 ≤ 3δ`,
`β = x(1 + δ)`, for `0 < ρ < 1` with `q = α²λρ > (29/30)q_c`: `√3·h·R + 13A/3 < 0`
(`(1 - q)(√3hR + 13A/3) = F - Gq`, `Π = 29V - 30WC > 0`). Status: stable. -/
theorem hs5_shear_sign {x δ al rho : ℝ} (hx : 2 ≤ x) (hx2 : x ≤ 13 / 6) (hδ : 0 ≤ δ)
    (hδ2 : δ ≤ 1 / 19) (hal : 13 / 5 * δ ≤ al - 1) (hal' : al - 1 ≤ 3 * δ) (hρ : 0 < rho)
    (hρ1 : rho < 1) (hq : 29 / 30 * hsQc x al < hsQ al rho) :
    √3 * hsShear x (x * (1 + δ)) al rho * hsRr x + 13 / 3 * hsAn x (x * (1 + δ)) al < 0 := by
  sorry

/-! ### Gate S5 -/

namespace HsData

variable (H : HsData)

/-- **Gate S5** (`SMALL_SHAPE_ROOT_SHEAR` (2)-(3), `HAND_PERIOD_EXCLUSION` (6)-(7); inventory HS-S567
S5.9, S5.10, S7.3): on the small-shape domain, `q > (29/30)q_c`, `√3hR + 13A/3 < 0`, hence `h < 0`
and `-hR > 5A/2` (`13/(3√3) > 5/2`, `A ≥ 0`, `R > 0`).
Proof plan: if `q ≤ q_b`: `root_zero`, `hs_env_weighted` (`m = 0`, `hs_B_pos`), `hs_env_scale`,
`hs_phi_eq` give `0 ≤ 𝓡(u; τq, q)`; `hs5_u_mono` with `u_le_V`, `hs_V_le_Vbar`,
`hs5_Vbar_le_uhat`; contradiction with `hs5_residual_neg` (`2q < p = τq < r_A`). Then
`hs5_shear_sign`.
Status: assembly (to be proved from the leaves above). -/
theorem s5 (hS : H.SmallShape) :
    29 / 30 * hsQc H.x H.al < H.q ∧
      √3 * hsShear H.x H.be H.al H.rho * hsRr H.x + 13 / 3 * hsAn H.x H.be H.al < 0 ∧
      hsShear H.x H.be H.al H.rho < 0 ∧
      5 / 2 * hsAn H.x H.be H.al < -hsShear H.x H.be H.al H.rho * hsRr H.x := by
  sorry

end HsData

/-- **Gate S5 for the actual window** (`HAND_PERIOD_EXCLUSION` (6)-(7)): on the small-shape domain,
`q > (29/30)q_c`, `√3hR + 13A/3 < 0`, `h < 0`, `-hR > 5A/2`, with the physical shear
`h = hsShear (C/a) (B/a) (A/a) ρ` (inventory HS-S567 §0.1, in the margins). -/
theorem M2Short.hs_S5 (D : M2Short) (h1 : 2 ≤ D.C / D.a) (h2 : D.C / D.a ≤ 13 / 6)
    (h3 : 0 ≤ D.B / D.C - 1) (h4 : D.B / D.C - 1 ≤ 1 / 19)
    (h5 : 1 + 13 / 5 * (D.B / D.C - 1) ≤ D.A / D.a) (h6 : D.A / D.a ≤ 1 + 3 * (D.B / D.C - 1)) :
    29 / 30 * hsQc (D.C / D.a) (D.A / D.a) < hsQ (D.A / D.a) (D.a ^ 2 / (D.a ^ 2 + 4)) ∧
      √3 * hsShear (D.C / D.a) (D.B / D.a) (D.A / D.a) (D.a ^ 2 / (D.a ^ 2 + 4)) *
          hsRr (D.C / D.a) + 13 / 3 * hsAn (D.C / D.a) (D.B / D.a) (D.A / D.a) < 0 ∧
      hsShear (D.C / D.a) (D.B / D.a) (D.A / D.a) (D.a ^ 2 / (D.a ^ 2 + 4)) < 0 ∧
      5 / 2 * hsAn (D.C / D.a) (D.B / D.a) (D.A / D.a) <
        -hsShear (D.C / D.a) (D.B / D.a) (D.A / D.a) (D.a ^ 2 / (D.a ^ 2 + 4)) *
          hsRr (D.C / D.a) := by
  have h := D.toHs.s5 (D.hs_smallShape h1 h2 h3 h4 h5 h6)
  rw [HsData.q, D.toHs_x, D.toHs_be, D.toHs_al, D.toHs_rho] at h
  exact h

end SmoothedOctagon
