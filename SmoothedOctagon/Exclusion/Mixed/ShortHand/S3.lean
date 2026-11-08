module

public import SmoothedOctagon.Exclusion.Mixed.ShortHand.Interface
public import SmoothedOctagon.Exclusion.Mixed.ShortHand.Hs35.Zero
public import SmoothedOctagon.Exclusion.Mixed.ShortHand.Hs35.Cont
public import SmoothedOctagon.Exclusion.Mixed.ShortHand.Hs35.Central

/-!
# Hand proof of the smaller-short case, gate S3: `δ < 1/19`

`MIXED_SMALLER_SHORT_DISPLACEMENT_HAND_EXCLUSION` with `DISPLACEMENT_{WEIGHT_REDUCTION, ZERO_SCALE,
SCALE_CONTINUATION, CENTRAL_BETA, CENTRAL_FACE, OUTER_FACE}`; inventory HS-S3 (R1-R45). Assuming
`2 ≤ x ≤ 13/6` (S1, S2) and `δ ≥ 1/19`: the displacement weight `m(y) = 4(4 - 3y)/(5α - 1)` gives
`G_τ = R_τ + m(w - 3/4) ≥ 0` at the actual root (`hs_env_weighted`, `hs3_B_pos`); the convex scale
polynomial (`hs_A2_pos`, `hs_phi_convex_max`), the zero-scale face (`hs3_zero_neg`) and the
`τ = 2` continuation (`hs3_tau2_cont`) reach `q* = min{q_c, 1/7}`; the duration tests (`hs3_dur`)
and the incoming slope (`hs3_uslope`) reduce to `F₀, F₁ < 0` on the central face (`hs3_central_*`)
or the outer face (`hs3_outer_*`).

## Main API

* `hs3Fn` (the test `J + n(w_* - 3/4)`), `hs3F0`, `hs3F1`, the ceilings `hsUCB`, `hsUO`, the central
  boundary `hs3b`, `hs3amin`.
* Stable: `hs3_shape`, `hs3_B_pos`, `hs3_uslope`, `hs3_dur`, `hs3_zero_neg`, `hs3_tau2_cont`,
  `hs3_central_straight`, `hs3_central_ceiling`, `hs3_beta_mono`, `hs3_log_maj`,
  `hs3_central_endpoint`, `hs3_outer_enclose`, `hs3_outer_ceiling`.
* Heavy: `hs3_central_alpha` (`DISPLACEMENT_CENTRAL_FACE` §2), `hs3_outer_face`
  (`DISPLACEMENT_OUTER_FACE` (7)-(21)).
* Gate: `HsData.s3`, `M2Short.hs_S3`.

The zero-scale face, the `τ = 2` continuation and the central-face leaves are proved in the helper
modules `Hs35/Zero.lean`, `Hs35/Cont.lean`, `Hs35/Central.lean`. The gate uses only the weak actual
root `R_τ = 0` and `w ≥ 3/4`, and `D > 0` is derived locally from `β < 2α` (inventory HS-S3 R9(e)).
-/

@[expose] public section

namespace SmoothedOctagon

open Set Real

/-- The duration test `J + n(w_* - 3/4)`, `J = (u - 1)/r_A + r_A + 1 - q - E_{L,*} + ℓ`
(`DISPLACEMENT_HAND_EXCLUSION` l.66-75). -/
noncomputable def hs3Fn (x be al u q n ℓ : ℝ) : ℝ :=
  (u - 1) / hsRA al be + hsRA al be + 1 - q - hsELs x be al u q + ℓ +
    n * (hsWs x be al u q - 3 / 4)

/-- `F₀ = J + n₀(w_* - 3/4)`, `n₀ = 2 + 4(4 - 3y)/k`, `y = 2q/r_A`, `k = 5α - 1`, with
`ℓ = log(2q/r_A)`; `F₀ = G*_2`. -/
noncomputable def hs3F0 (x be al u q : ℝ) : ℝ :=
  hs3Fn x be al u q (2 + 4 * (4 - 3 * (2 * q / hsRA al be)) / (5 * al - 1))
    (log (2 * q / hsRA al be))

/-- `F₁ = J + n₁(w_* - 3/4)`, `n₁ = T + 4/k`, `T = r_A/q`. -/
noncomputable def hs3F1 (x be al u q : ℝ) : ℝ :=
  hs3Fn x be al u q (hsRA al be / q + 4 / (5 * al - 1)) (log (2 * q / hsRA al be))

/-- The central ceiling `ū(x, β) = 3/4 + ((x - 1)g(x) + (β - x)/5808)/(β - 1)`,
`g(x) = V_G(x) - 3/4` (`DISPLACEMENT_CENTRAL_BETA` (2)). -/
noncomputable def hsUCB (x be : ℝ) : ℝ := 3 / 4 + ((x - 1) * (hsVG x - 3 / 4) + (be - x) / 5808) / (be - 1)

/-- The outer ceiling `ū = 3/4 + (x - 1)²(x + β - 2)/((β - 1)(x + 1)(35x + 13))`
(`DISPLACEMENT_OUTER_FACE` (3)). -/
noncomputable def hsUO (x be : ℝ) : ℝ :=
  3 / 4 + (x - 1) ^ 2 * (x + be - 2) / ((be - 1) * (x + 1) * (35 * x + 13))

/-- The central boundary `b(x, α) = x + (25x/(15x + 36))(α - 1)` (`DISPLACEMENT_CENTRAL_FACE` (1)). -/
noncomputable def hs3b (x al : ℝ) : ℝ := x + 25 * x / (15 * x + 36) * (al - 1)

/-- `a_min(x) = (15x + 511)/475` (`DISPLACEMENT_CENTRAL_FACE` (2)). -/
noncomputable def hs3amin (x : ℝ) : ℝ := (15 * x + 511) / 475

/-! ### The weighted reduction -/

/-- `α ≤ (5x + 4)/12` from `6α² ≤ x(x + 2)` (`((5x + 4)/12)² - x(x + 2)/6 = (x - 4)²/144`;
`DISPLACEMENT_CENTRAL_BETA` (5)). -/
private lemma hs3_al_le {x al : ℝ} (hx : 0 ≤ x) (h6 : 6 * al ^ 2 ≤ x * (x + 2)) :
    al ≤ (5 * x + 4) / 12 := by
  have e : ((5 * x + 4) / 12) ^ 2 = x * (x + 2) / 6 + (x - 4) ^ 2 / 144 := by ring
  have h : al ^ 2 ≤ ((5 * x + 4) / 12) ^ 2 := by
    rw [e]; have := sq_nonneg (x - 4); linarith
  exact abs_le_of_sq_le_sq' h (by positivity) |>.2

/-- **Shape bounds on the displacement domain** (`DISPLACEMENT_WEIGHT_REDUCTION` §1 (2)-(4);
inventory HS-S3 R9): for `2 ≤ x ≤ 13/6`, `1 ≤ α ≤ x ≤ β`, `δ = β/x - 1 ≥ 1/19`,
`α ≥ 1 + c(x)δ` and `β ≥ x(9x + 8α)/(9x + 8)`: `α ≥ 108/95`, `β < 2α`, `1/3 < r_A ≤ 13/30`.
Status: stable. -/
theorem hs3_shape {x al be : ℝ} (hx : 2 ≤ x) (hx2 : x ≤ 13 / 6) (hal : 1 ≤ al) (hax : al ≤ x)
    (hxb : x ≤ be) (hδ : 1 / 19 ≤ be / x - 1)
    (hL : 1 + (4 * x ^ 2 + 11 * x + 1) / (7 * x + 1) * (be / x - 1) ≤ al)
    (hU : x * (9 * x + 8 * al) / (9 * x + 8) ≤ be) :
    108 / 95 ≤ al ∧ be < 2 * al ∧ 1 / 3 < hsRA al be ∧ hsRA al be ≤ 13 / 30 := by
  have hx0 : 0 < x := by linarith
  have h71 : 0 < 7 * x + 1 := by linarith
  have hal0 : 0 < al := by linarith
  set δ := be / x - 1 with hδdef
  have hbe : be = x * (1 + δ) := by rw [hδdef]; field_simp; ring
  set c := (4 * x ^ 2 + 11 * x + 1) / (7 * x + 1) with hc
  have hce : c * (7 * x + 1) = 4 * x ^ 2 + 11 * x + 1 := by rw [hc]; field_simp
  have hc135 : 13 / 5 ≤ c := by nlinarith
  have hcδ : 13 / 5 * (1 / 19) ≤ c * δ := mul_le_mul hc135 hδ (by norm_num) (by linarith)
  have h108 : 108 / 95 ≤ al := by linarith
  -- `al (7x + 1) ≥ 7x + 1 + (4x² + 11x + 1)δ`
  have hkey : (7 * x + 1) + (4 * x ^ 2 + 11 * x + 1) * δ ≤ al * (7 * x + 1) := by
    have := mul_le_mul_of_nonneg_right hL h71.le
    nlinarith
  have hb2 : be < 2 * al := by
    have hq : 0 < (x ^ 2 + 21 * x + 2) * δ - (x - 2) * (7 * x + 1) := by
      have : (x ^ 2 + 21 * x + 2) * (1 / 19) ≤ (x ^ 2 + 21 * x + 2) * δ :=
        mul_le_mul_of_nonneg_left hδ (by positivity)
      nlinarith
    have : be * (7 * x + 1) < 2 * al * (7 * x + 1) := by rw [hbe]; nlinarith
    exact lt_of_mul_lt_mul_right this h71.le
  have hbe0 : 0 < be := by linarith
  have hU' : x * (9 * x + 8 * al) ≤ be * (9 * x + 8) := by
    rwa [div_le_iff₀ (by positivity)] at hU
  refine ⟨h108, hb2, ?_, ?_⟩
  · rw [hsRA, lt_div_iff₀ (by positivity)]; linarith
  · rw [hsRA, div_le_iff₀ (by positivity)]
    have : 17 * al * (9 * x + 8) ≤ 13 * be * (9 * x + 8) := by
      nlinarith [mul_nonneg hal0.le (sub_nonneg.2 hax), mul_nonneg hx0.le (sub_nonneg.2 hx)]
    have := le_of_mul_le_mul_right this (by positivity : (0 : ℝ) < 9 * x + 8)
    linarith

/-- `c(α) = -5α² + 10αx - 3α + 2x ≥ 0` on `1 ≤ α ≤ x` (concave in `α`, endpoint values
`12x - 8`, `5x² - x`). -/
private lemma hs3_cα {x al : ℝ} (hx : 2 ≤ x) (hal : 1 ≤ al) (hax : al ≤ x) :
    0 ≤ -5 * al ^ 2 + 10 * al * x - 3 * al + 2 * x := by
  have h : (x - 1) * (-5 * al ^ 2 + 10 * al * x - 3 * al + 2 * x) =
      (x - al) * (12 * x - 8) + (al - 1) * (5 * x ^ 2 - x) + 5 * ((al - 1) * (x - al)) * (x - 1) := by
    ring
  have h1 : 0 ≤ (x - al) * (12 * x - 8) := mul_nonneg (by linarith) (by linarith)
  have h2 : 0 ≤ (al - 1) * (5 * x ^ 2 - x) := mul_nonneg (by linarith) (by nlinarith)
  have h3 : 0 ≤ 5 * ((al - 1) * (x - al)) * (x - 1) :=
    mul_nonneg (mul_nonneg (by norm_num) (mul_nonneg (by linarith) (by linarith))) (by linarith)
  have : 0 ≤ (x - 1) * (-5 * al ^ 2 + 10 * al * x - 3 * al + 2 * x) := by rw [h]; linarith
  by_contra hneg
  replace hneg := not_le.mp hneg
  have := mul_neg_of_pos_of_neg (by linarith : (0 : ℝ) < x - 1) hneg
  linarith

/-- `kα(α + β) - (k + 2)(D - S) > 0` (`DISPLACEMENT_WEIGHT_REDUCTION` (11)), `k = 5α - 1`. -/
private lemma hs3_kQ {x be al : ℝ} (hx : 2 ≤ x) (hal : 1 ≤ al) (hax : al ≤ x) (hxb : x ≤ be) :
    0 < (5 * al - 1) * (al * (al + be)) -
      (5 * al - 1 + 2) * (al ^ 2 + 2 * al * be + 1 + 2 * x - 2 * be * x - (1 + x)) := by
  have e : (5 * al - 1) * (al * (al + be)) -
      (5 * al - 1 + 2) * (al ^ 2 + 2 * al * be + 1 + 2 * x - 2 * be * x - (1 + x)) =
      be * (-5 * al ^ 2 + 10 * al * x - 3 * al + 2 * x) - 2 * al ^ 2 - 5 * al * x - x := by ring
  have hc := hs3_cα hx hal hax
  have hg : (x - 1) * (x * (-5 * al ^ 2 + 10 * al * x - 3 * al + 2 * x) - 2 * al ^ 2 - 5 * al * x - x)
      = (x - al) * (12 * x ^ 2 - 14 * x - 2) + (al - 1) * (5 * x ^ 3 - 8 * x ^ 2 - x) +
        (5 * x + 2) * ((al - 1) * (x - al)) * (x - 1) := by ring
  have h1 : 0 ≤ (x - al) * (12 * x ^ 2 - 14 * x - 2) := mul_nonneg (by linarith) (by nlinarith)
  have h2 : 0 ≤ (al - 1) * (5 * x ^ 3 - 8 * x ^ 2 - x) := mul_nonneg (by linarith) (by nlinarith)
  have h3 : 0 ≤ (5 * x + 2) * ((al - 1) * (x - al)) * (x - 1) :=
    mul_nonneg (mul_nonneg (by linarith) (mul_nonneg (by linarith) (by linarith))) (by linarith)
  have h4 : 0 < (x - al) * (12 * x ^ 2 - 14 * x - 2) + (al - 1) * (5 * x ^ 3 - 8 * x ^ 2 - x) := by
    rcases eq_or_lt_of_le hal with h | h
    · subst h
      have : 0 < (x - 1) * (12 * x ^ 2 - 14 * x - 2) := mul_pos (by linarith) (by nlinarith)
      norm_num
      linarith
    · have : 0 < (al - 1) * (5 * x ^ 3 - 8 * x ^ 2 - x) := mul_pos (by linarith) (by nlinarith)
      linarith
  have hgpos : 0 < x * (-5 * al ^ 2 + 10 * al * x - 3 * al + 2 * x) - 2 * al ^ 2 - 5 * al * x - x := by
    have : 0 < (x - 1) * (x * (-5 * al ^ 2 + 10 * al * x - 3 * al + 2 * x) - 2 * al ^ 2 -
        5 * al * x - x) := by rw [hg]; linarith
    by_contra hneg
    replace hneg := not_lt.mp hneg
    have := mul_nonpos_of_nonneg_of_nonpos (by linarith : (0 : ℝ) ≤ x - 1) hneg
    linarith
  rw [e]
  nlinarith [mul_le_mul_of_nonneg_right hxb hc]

/-- The core of `hs3_B_pos` in plain variables (`DISPLACEMENT_WEIGHT_REDUCTION` (8)-(11)). -/
private lemma hs3_B_core {x be al L rho q rA s τ D : ℝ} (hx : 2 ≤ x) (hal : 1 ≤ al) (hax : al ≤ x)
    (hxb : x ≤ be) (hL0 : 0 < L) (hρ : 0 < rho) (hs : rho * (1 + x) ≤ s) (hτ : 2 ≤ τ)
    (hτT : τ * q ≤ rA) (hLq : L * rho * al ^ 2 = q) (hrAe : rA * (al + be) = al) (hrA0 : 0 < rA)
    (hD : D = al ^ 2 + 2 * al * be + 1 + 2 * x - 2 * be * x) :
    0 < 1 + (τ + 4 * (4 - 3 * (τ * q / rA)) / (5 * al - 1)) * (L * s - L * rho * D) := by
  have hal0 : 0 < al := by linarith
  have hq0 : 0 < q := by rw [← hLq]; positivity
  have hk4 : 4 ≤ 5 * al - 1 := by linarith
  have hk0 : 0 < 5 * al - 1 := by linarith
  have hz0 : 0 < τ * q := by positivity
  have hqz : 2 * q ≤ τ * q := by nlinarith
  have hzr : τ * q / rA ≤ 1 := by rw [div_le_one hrA0]; exact hτT
  have hzr0 : 0 ≤ τ * q / rA := by positivity
  set z := τ * q with hz
  set y := z / rA with hy
  set k := 5 * al - 1 with hk
  set m := 4 * (4 - 3 * y) / k with hm
  have hm0 : 0 < m := by rw [hm]; apply div_pos <;> linarith
  have hmk : m * k = 4 * (4 - 3 * y) := by rw [hm]; field_simp
  have hτm : 0 < τ + m := by linarith
  have hX : L * rho * (1 + x - D) ≤ L * s - L * rho * D := by
    have := mul_le_mul_of_nonneg_left hs hL0.le
    linarith
  suffices h : 0 < 1 + (τ + m) * (L * rho * (1 + x - D)) by
    have := mul_le_mul_of_nonneg_left hX hτm.le
    linarith
  rcases le_or_gt 0 (1 + x - D) with hDS | hDS
  · have : 0 ≤ (τ + m) * (L * rho * (1 + x - D)) := by positivity
    linarith
  have hyr : y * rA = z := by rw [hy]; field_simp
  -- `(τ + m) q k ≤ r_A (k + 2)`
  have hP : (τ + m) * q * k ≤ rA * (k + 2) := by
    have e1 : (τ + m) * q * k = z * k + 4 * (4 - 3 * y) * q := by
      rw [hz]; linear_combination q * hmk
    have e2 : 4 * (4 - 3 * y) * q ≤ 2 * (4 - 3 * y) * z :=
      by nlinarith [mul_le_mul_of_nonneg_left hqz (by linarith : (0 : ℝ) ≤ 4 - 3 * y)]
    have e4 : z * k + 2 * (4 - 3 * y) * z = rA * (y * k + 2 * (4 - 3 * y) * y) := by
      rw [← hyr]; ring
    have e5 : y * k + 2 * (4 - 3 * y) * y ≤ k + 2 := by
      nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ 1 - y) (by linarith : (0 : ℝ) ≤ k + 2 - 6 * y)]
    have := mul_le_mul_of_nonneg_left e5 hrA0.le
    linarith
  have hpoly : 0 < k * (al * (al + be)) - (k + 2) * (D - (1 + x)) := by
    rw [hk, hD]; exact hs3_kQ hx hal hax hxb
  have hDS' : 0 < D - (1 + x) := by linarith
  have hfin : (τ + m) * q * k * (D - (1 + x)) < k * al ^ 2 := by
    have h1 : (τ + m) * q * k * (D - (1 + x)) ≤ rA * (k + 2) * (D - (1 + x)) :=
      mul_le_mul_of_nonneg_right hP hDS'.le
    have h2 : rA * ((k + 2) * (D - (1 + x))) < rA * (k * (al * (al + be))) :=
      mul_lt_mul_of_pos_left (by linarith) hrA0
    have h3 : rA * (k * (al * (al + be))) = k * al ^ 2 := by
      linear_combination k * al * hrAe
    linarith
  have e : (τ + m) * (L * rho * (1 + x - D)) * (k * al ^ 2) =
      -((τ + m) * q * k * (D - (1 + x))) := by rw [← hLq]; ring
  have hka : 0 < k * al ^ 2 := by positivity
  have : 0 < (1 + (τ + m) * (L * rho * (1 + x - D))) * (k * al ^ 2) := by
    rw [add_mul, e]; linarith
  exact lt_of_mul_lt_mul_right (by rwa [zero_mul]) hka.le

/-- **The displacement-weighted positive factor** (`DISPLACEMENT_WEIGHT_REDUCTION` (8)-(11);
inventory HS-S3 R11): for `x ≥ 2`, `1 ≤ α ≤ x ≤ β`, `ρ > 0`, `s ≥ ρ(1 + x)`, `2 ≤ τ`, `τq ≤ r_A`,
with `m = 4(4 - 3τq/r_A)/(5α - 1)`: `B_{τ+m}(s) > 0`. Status: stable. -/
theorem hs3_B_pos {x be al rho s τ : ℝ} (hx : 2 ≤ x) (hal : 1 ≤ al) (hax : al ≤ x) (hxb : x ≤ be)
    (hρ : 0 < rho) (hs : rho * (1 + x) ≤ s) (hτ : 2 ≤ τ) (hτT : τ * hsQ al rho ≤ hsRA al be) :
    0 < 1 + (τ + 4 * (4 - 3 * (τ * hsQ al rho / hsRA al be)) / (5 * al - 1)) *
      (hsLam al rho * s - hsLam al rho * rho * hsDg x be al) := by
  have hal0 : 0 < al := by linarith
  have hbe0 : 0 < be := by linarith
  have hden : 0 < 1 + rho * (al ^ 2 - 1) := by
    have : 0 ≤ al ^ 2 - 1 := by nlinarith
    positivity
  have hL0 : 0 < hsLam al rho := by rw [hsLam]; positivity
  have hrA0 : 0 < hsRA al be := by rw [hsRA]; positivity
  exact hs3_B_core hx hal hax hxb hL0 hρ hs hτ hτT (by rw [hsQ]; ring)
    (by rw [hsRA]; field_simp) hrA0 rfl

/-- The incoming slope `c_u(n) = 1/r_A + λS - 2d + nd(d - λS) > 17/182`
(`DISPLACEMENT_WEIGHT_REDUCTION` (15); `λ = 1 - εq`, `d = qΔ`), in plain variables. -/
private lemma hs3_cu_pos {S R q ε Δ n : ℝ} (hS : 3 ≤ S) (hS' : S ≤ 19 / 6) (hR : 30 / 13 ≤ R)
    (hq : 0 < q) (hq7 : q ≤ 1 / 7) (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1) (hΔ0 : 0 < Δ) (hΔ3 : Δ < 3)
    (hn : 0 ≤ n) (hnd : n * (q * Δ) ≤ 1 + q * Δ) :
    17 / 182 < R + S - q * (2 * Δ + ε * S) + n * (-(q * Δ * S) + q ^ 2 * (Δ ^ 2 + Δ * ε * S)) := by
  set d := q * Δ with hd
  set lam := 1 - ε * q with hlam
  have hd0 : 0 < d := by positivity
  have hd3 : d < 3 / 7 := by rw [hd]; nlinarith
  have hlam0 : 0 ≤ lam := by rw [hlam]; nlinarith
  have hlam1 : lam ≤ 1 := by rw [hlam]; nlinarith
  have e : R + S - q * (2 * Δ + ε * S) + n * (-(q * Δ * S) + q ^ 2 * (Δ ^ 2 + Δ * ε * S)) =
      R + lam * S - 2 * d + n * d ^ 2 - n * d * (lam * S) := by rw [hd, hlam]; ring
  rw [e]
  have h1 : n * d * (lam * S) ≤ (1 + d) * (lam * S) :=
    mul_le_mul_of_nonneg_right hnd (by positivity)
  have h2 : 0 ≤ n * d ^ 2 := by positivity
  have h3 : d * (lam * S) ≤ d * (19 / 6) := by
    apply mul_le_mul_of_nonneg_left _ hd0.le
    nlinarith
  nlinarith

/-- **The positive incoming coefficient** (`DISPLACEMENT_WEIGHT_REDUCTION` (13)-(15); inventory
HS-S3 R12): for `2 ≤ x ≤ 13/6`, `11/10 ≤ α ≤ x ≤ β`, `0 < D < α(α + β)`, `D < 3α²`, `0 < q ≤ 1/7`,
`r_A ≤ 13/30` and `0 ≤ n ≤ r_A/q + 1`, the test `J + n(w_* - 3/4)` is nondecreasing in `u`
(slope `c_u(n) > 17/182`). Status: stable. -/
theorem hs3_uslope {x be al q n ℓ u u' : ℝ} (hx : 2 ≤ x) (hx2 : x ≤ 13 / 6) (hal : 11 / 10 ≤ al)
    (hax : al ≤ x) (hxb : x ≤ be) (hD : 0 < hsDg x be al) (hDQ : hsDg x be al < al * (al + be))
    (hD3 : hsDg x be al < 3 * al ^ 2) (hq : 0 < q) (hq7 : q ≤ 1 / 7) (hrA : hsRA al be ≤ 13 / 30)
    (hn : 0 ≤ n) (hnT : n ≤ hsRA al be / q + 1) (huu : u ≤ u') :
    hs3Fn x be al u q n ℓ ≤ hs3Fn x be al u' q n ℓ := by
  have _ := hax
  have hal0 : 0 < al := by linarith
  have hbe0 : 0 < be := by linarith
  have hrA0 : 0 < hsRA al be := by rw [hsRA]; positivity
  set Δ := hsDg x be al / al ^ 2 with hΔ
  set ε := 1 - 1 / al ^ 2 with hε
  have e : hs3Fn x be al u' q n ℓ - hs3Fn x be al u q n ℓ = (u' - u) *
      (1 / hsRA al be + (1 + x) - q * (2 * Δ + ε * (1 + x)) +
        n * (-(q * Δ * (1 + x)) + q ^ 2 * (Δ ^ 2 + Δ * ε * (1 + x)))) := by
    unfold hs3Fn hsELs hsWs hsA1 hsA2 hsA3 hsE0
    rw [← hΔ, ← hε]
    ring
  have hR : 30 / 13 ≤ 1 / hsRA al be := by
    rw [le_div_iff₀ hrA0]; linarith
  have hal2 : 1 ≤ al ^ 2 := by nlinarith
  have hε0 : 0 ≤ ε := by rw [hε, sub_nonneg, div_le_one (by positivity)]; exact hal2
  have hε1 : ε ≤ 1 := by rw [hε]; have : 0 < 1 / al ^ 2 := by positivity
                         linarith
  have hΔ0 : 0 < Δ := by rw [hΔ]; positivity
  have hΔ3 : Δ < 3 := by rw [hΔ, div_lt_iff₀ (by positivity)]; exact hD3
  have hrAΔ : hsRA al be * Δ < 1 := by
    have : hsRA al be * Δ = hsDg x be al / (al * (al + be)) := by
      rw [hsRA, hΔ]; field_simp
    rw [this, div_lt_one (by positivity)]; exact hDQ
  have hnd : n * (q * Δ) ≤ 1 + q * Δ := by
    have h1 : n * (q * Δ) ≤ (hsRA al be / q + 1) * (q * Δ) :=
      mul_le_mul_of_nonneg_right hnT (by positivity)
    have h2 : (hsRA al be / q + 1) * (q * Δ) = hsRA al be * Δ + q * Δ := by field_simp
    linarith
  have hc := hs3_cu_pos (by linarith : (3 : ℝ) ≤ 1 + x) (by linarith : 1 + x ≤ (19 : ℝ) / 6) hR hq hq7
    hε0 hε1 hΔ0 hΔ3 hn hnd
  have : 0 ≤ (u' - u) * (1 / hsRA al be + (1 + x) - q * (2 * Δ + ε * (1 + x)) +
        n * (-(q * Δ * (1 + x)) + q ^ 2 * (Δ ^ 2 + Δ * ε * (1 + x)))) :=
    mul_nonneg (by linarith) (by linarith)
  linarith

/-- **The two duration tests** (`DISPLACEMENT_WEIGHT_REDUCTION` (19)-(21); inventory HS-S3 R14):
for `α ≥ 1`, `β > 0`, `q > 0`, `2 ≤ τ`, `τq ≤ r_A`, the weighted envelope
`G*_τ = R*_τ + m(τq/r_A)(w_* - 3/4)` satisfies `G*_τ ≤ max{F₀, F₁}` (exact remainder
`τ/4 - 1/τ - log(τ/2) ≥ 0`). Status: stable. -/
theorem hs3_dur {x be al u q τ : ℝ} (hal : 1 ≤ al) (hbe : 0 < be) (hq : 0 < q) (hτ : 2 ≤ τ)
    (hτT : τ * q ≤ hsRA al be) :
    hsF x be al u q τ (log (τ * q / hsRA al be)) (4 * (4 - 3 * (τ * q / hsRA al be)) / (5 * al - 1)) ≤
      max (hs3F0 x be al u q) (hs3F1 x be al u q) := by
  have hrA0 : 0 < hsRA al be := by rw [hsRA]; apply div_pos <;> linarith
  have hk0 : 0 < 5 * al - 1 := by linarith
  have hτ0 : 0 < τ := by linarith
  have hlog : log (τ * q / hsRA al be) = log (2 * q / hsRA al be) + log (τ / 2) := by
    rw [← Real.log_mul (by positivity) (by positivity)]; congr 1; field_simp
  have hrem : log (τ / 2) ≤ τ / 4 - 1 / τ := by
    have := ss_log_le_half (z := τ / 2) (by linarith)
    have e : (τ / 2 - (τ / 2)⁻¹) / 2 = τ / 4 - 1 / τ := by field_simp; ring
    linarith
  have hτT' : τ ≤ hsRA al be / q := by rw [le_div_iff₀ hq]; exact hτT
  unfold hsF hs3F0 hs3F1 hs3Fn
  rw [hlog]
  generalize hsWs x be al u q = w
  generalize hsELs x be al u q = EL
  generalize hsRA al be = rA at hrA0 hτT'
  generalize log (2 * q / rA) = ℓ
  set B := 1 - 12 * q / (rA * (5 * al - 1)) with hB
  have e0 : (w - 1) * τ + 1 / τ + (u - 1) / rA + rA + 1 - q - EL + (ℓ + log (τ / 2)) +
      4 * (4 - 3 * (τ * q / rA)) / (5 * al - 1) * (w - 3 / 4) =
      ((u - 1) / rA + rA + 1 - q - EL + ℓ +
        (2 + 4 * (4 - 3 * (2 * q / rA)) / (5 * al - 1)) * (w - 3 / 4)) +
      (τ - 2) * (B * (w - 3 / 4)) - (τ / 4 - 1 / τ - log (τ / 2)) := by
    rw [hB]; field_simp; ring
  have e1 : (u - 1) / rA + rA + 1 - q - EL + ℓ + (rA / q + 4 / (5 * al - 1)) * (w - 3 / 4) =
      ((u - 1) / rA + rA + 1 - q - EL + ℓ +
        (2 + 4 * (4 - 3 * (2 * q / rA)) / (5 * al - 1)) * (w - 3 / 4)) +
      (rA / q - 2) * (B * (w - 3 / 4)) := by
    rw [hB]; field_simp; ring
  rw [e0, e1]
  rcases le_or_gt 0 (B * (w - 3 / 4)) with hBF | hBF
  · have : (τ - 2) * (B * (w - 3 / 4)) ≤ (rA / q - 2) * (B * (w - 3 / 4)) :=
      mul_le_mul_of_nonneg_right (by linarith) hBF
    exact le_max_of_le_right (by linarith)
  · have : (τ - 2) * (B * (w - 3 / 4)) ≤ 0 := mul_nonpos_of_nonneg_of_nonpos (by linarith) hBF.le
    exact le_max_of_le_left (by linarith)

/-- **The zero-scale face** (`DISPLACEMENT_ZERO_SCALE` (2)-(23); inventory HS-S3 R16-R22): for
`2 ≤ x ≤ 13/6`, `1 < α ≤ x ≤ β`, `β ≥ x(9x + 8α)/(9x + 8)`, `1/3 < r_A ≤ 13/30`,
`3/4 ≤ u ≤ U(r_A)`, `D < α(α + β)` and `0 < p ≤ r_A`: `Φ(0) = C(p) + m/4 < 0`,
`m = 4(4 - 3p/r_A)/(5α - 1)`. Status: stable.
Route: `hs35_zero_neg` (`Hs35/Zero.lean`): the notes' edges `x = 2`, `x = α`, with the `x`-lowering
and `r`-raising done algebraically (exact divided differences) instead of by the chain rule. -/
theorem hs3_zero_neg {x be al u p : ℝ} (hx : 2 ≤ x) (hx2 : x ≤ 13 / 6) (hal : 1 < al) (hax : al ≤ x)
    (hxb : x ≤ be) (hU : x * (9 * x + 8 * al) / (9 * x + 8) ≤ be) (hrA : 1 / 3 < hsRA al be)
    (hrA' : hsRA al be ≤ 13 / 30) (hu : 3 / 4 ≤ u) (hurA : u ≤ m2U (hsRA al be))
    (hDQ : hsDg x be al < al * (al + be)) (hp : 0 < p) (hpr : p ≤ hsRA al be) :
    hsPhi x be al u p (4 * (4 - 3 * (p / hsRA al be)) / (5 * al - 1)) 0 < 0 :=
  hs35_zero_neg hx hx2 hal hax hxb hU hrA hrA' hu hurA hDQ hp hpr

/-- **The `τ = 2` continuation** (`DISPLACEMENT_SCALE_CONTINUATION` (1)-(19); inventory HS-S3
R23-R28): for `2 ≤ x ≤ 13/6`, `11/10 ≤ α ≤ x ≤ β`, `1/3 ≤ r_A`, `3/4 ≤ u ≤ 19/25`,
`0 < D < 3α²`, `G*_2(q) = R*_2(q) + m(2q/r_A)(w_*(q) - 3/4)` is strictly increasing on `(0, 1/7]`.
Status: stable.
Route: `hs35_tau2_cont` (`Hs35/Cont.lean`): `B₂, B₃` are affine in `u` and in `1/r_A`, so four
corners with a negative discriminant in `Δ` replace the concavity in `1/p` and the `u`-monotonicity. -/
theorem hs3_tau2_cont {x be al u q₁ q₂ : ℝ} (hx : 2 ≤ x) (hx2 : x ≤ 13 / 6) (hal : 11 / 10 ≤ al)
    (hax : al ≤ x) (hxb : x ≤ be) (hrA : 1 / 3 ≤ hsRA al be) (hu : 3 / 4 ≤ u) (hu' : u ≤ 19 / 25)
    (hD : 0 < hsDg x be al) (hD3 : hsDg x be al < 3 * al ^ 2) (hq₁ : 0 < q₁) (hq : q₁ < q₂)
    (hq₂ : q₂ ≤ 1 / 7) :
    hsF x be al u q₁ 2 (log (2 * q₁ / hsRA al be))
        (4 * (4 - 3 * (2 * q₁ / hsRA al be)) / (5 * al - 1)) <
      hsF x be al u q₂ 2 (log (2 * q₂ / hsRA al be))
        (4 * (4 - 3 * (2 * q₂ / hsRA al be)) / (5 * al - 1)) :=
  hs35_tau2_cont hx hx2 hal hax hxb hrA hu hu' hD hD3 hq₁ hq hq₂

/-! ### The central face `q* = q_c ≤ 1/7` -/

/-- **The straight order bound** (`DISPLACEMENT_CENTRAL_FACE` §1 (1)-(3); inventory HS-S3 R33): for
`2 ≤ x ≤ 13/6`, `δ = β/x - 1 ≥ 1/19` and the quadratic order `α ≥ 1 + (c(x) + 1/23)δ`
(`hs_quad_order`, `δ/(1 + 4δ) ≥ 1/23`):
`a_min(x) < α` and `β < b(x, α)`. Status: stable. -/
theorem hs3_central_straight {x al be : ℝ} (hx : 2 ≤ x) (hx2 : x ≤ 13 / 6)
    (hδ : 1 / 19 ≤ be / x - 1)
    (hQ : 1 + ((4 * x ^ 2 + 11 * x + 1) / (7 * x + 1) + 1 / 23) * (be / x - 1) ≤ al) :
    hs3amin x < al ∧ be < hs3b x al := by
  have hx0 : 0 < x := by linarith
  have h71 : 0 < 7 * x + 1 := by linarith
  have h36 : 0 < 15 * x + 36 := by linarith
  set δ := be / x - 1 with hδdef
  have hbe : be = x * (1 + δ) := by rw [hδdef]; field_simp; ring
  have hδ0 : 0 < δ := by linarith
  have hcC : (15 * x + 36) / 25 < (4 * x ^ 2 + 11 * x + 1) / (7 * x + 1) + 1 / 23 := by
    rw [div_add_div _ _ h71.ne' (by norm_num), div_lt_div_iff₀ (by norm_num) (by positivity)]
    nlinarith
  have hα : 1 + (15 * x + 36) / 25 * δ < al := by
    have := mul_lt_mul_of_pos_right hcC hδ0
    linarith
  constructor
  · have : (15 * x + 36) / 25 * (1 / 19) ≤ (15 * x + 36) / 25 * δ :=
      mul_le_mul_of_nonneg_left hδ (by positivity)
    rw [hs3amin]; linarith
  · rw [hs3b, hbe]
    have hB : 0 < 25 * x / (15 * x + 36) := by positivity
    have := mul_lt_mul_of_pos_left (by linarith : (15 * x + 36) / 25 * δ < al - 1) hB
    have e : 25 * x / (15 * x + 36) * ((15 * x + 36) / 25 * δ) = x * δ := by field_simp
    nlinarith

/-- **The central incoming ceiling** (`DISPLACEMENT_CENTRAL_BETA` §2 (2), (5); inventory HS-S3 R29):
on `2 ≤ x ≤ 13/6`, `α ≥ 108/95`, `6α² ≤ x(x + 2)`, `20x/19 ≤ β ≤ x + 5x(α - 1)/13`:
`Sec(1, x, β) ≤ ū(x, β)`. Status: stable. -/
theorem hs3_central_ceiling {x al be : ℝ} (hx : 2 ≤ x) (hx2 : x ≤ 13 / 6) (hal : 108 / 95 ≤ al)
    (hqc : 6 * al ^ 2 ≤ x * (x + 2)) (hb : 20 * x / 19 ≤ be)
    (hb' : be ≤ x + 5 * x * (al - 1) / 13) : m2Sec 1 x be ≤ hsUCB x be := by
  have _ := hal
  have hx0 : 0 < x := by linarith
  have hxb : x ≤ be := by
    have : x ≤ 20 * x / 19 := by rw [le_div_iff₀ (by norm_num)]; linarith
    linarith
  -- `α ≤ (5x + 4)/12`, so `(β - x)/x ≤ 85/936 < 1/11`
  have hα : al ≤ (5 * x + 4) / 12 := hs3_al_le hx0.le hqc
  have hbx : (be - x) * 11 ≤ x := by
    have : 5 * x * (al - 1) / 13 * 11 ≤ x := by
      rw [div_mul_eq_mul_div, div_le_iff₀ (by norm_num)]; nlinarith
    nlinarith
  have hadd := ss_sec_add (A := 1) (B := x) (M := x) (P := be) one_pos hx0 hx0 (by linarith)
  have hV := hs_V_lt_VG (by linarith : 1 < x)
  have htail := hs_sec_tail_le hx0 hxb
  have ht2 : (be - x) ^ 2 / (48 * x ^ 2) ≤ 1 / 5808 := by
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]
    nlinarith [mul_le_mul hbx hbx (by linarith) hx0.le]
  have h1 : (be - x) * m2Sec x x be ≤ (be - x) * (3 / 4 + 1 / 5808) :=
    mul_le_mul_of_nonneg_left (by linarith) (by linarith)
  have h2 : (x - 1) * m2Sec 1 x x ≤ (x - 1) * hsVG x :=
    mul_le_mul_of_nonneg_left hV.le (by linarith)
  rw [hsUCB, ← sub_nonneg]
  have hb1 : 0 < be - 1 := by linarith
  have e : 3 / 4 + ((x - 1) * (hsVG x - 3 / 4) + (be - x) / 5808) / (be - 1) - m2Sec 1 x be =
      ((x - 1) * hsVG x + (be - x) * (3 / 4 + 1 / 5808) - (be - 1) * m2Sec 1 x be) / (be - 1) := by
    field_simp; ring
  rw [e]
  apply div_nonneg _ hb1.le
  linarith

/-- **β-monotonicity on the central face** (`DISPLACEMENT_CENTRAL_BETA` (4), (18)-(21); inventory
HS-S3 R30-R32): on `2 ≤ x ≤ 13/6`, `α ≥ 108/95`, `6α² ≤ x(x + 2)`, for
`20x/19 ≤ β₁ ≤ β₂ ≤ min{2α, x + 5x(α - 1)/13}`, `F_i(x, α, β₁; ū) ≤ F_i(x, α, β₂; ū)` at `q = q_c`
(`(F₀)_β > 7/1500`, `(F₁)_β > 1/1200`). Status: stable.
Route: `hs35_beta_mono` (`Hs35/Central.lean`): exact differences between `β₁` and `β₂` (secant form
of the β-derivative bound) instead of the derivative and the mean value theorem. -/
theorem hs3_beta_mono {x al be₁ be₂ : ℝ} (hx : 2 ≤ x) (hx2 : x ≤ 13 / 6) (hal : 108 / 95 ≤ al)
    (hqc : 6 * al ^ 2 ≤ x * (x + 2)) (hb : 20 * x / 19 ≤ be₁) (hbb : be₁ ≤ be₂)
    (hb2 : be₂ ≤ 2 * al) (hb2' : be₂ ≤ x + 5 * x * (al - 1) / 13) :
    hs3F0 x be₁ al (hsUCB x be₁) (hsQc x al) ≤ hs3F0 x be₂ al (hsUCB x be₂) (hsQc x al) ∧
      hs3F1 x be₁ al (hsUCB x be₁) (hsQc x al) ≤ hs3F1 x be₂ al (hsUCB x be₂) (hsQc x al) :=
  hs35_beta_mono hx hx2 hal hqc hb hbb hb2 hb2'

/-- **The rational log majorant** (`DISPLACEMENT_CENTRAL_FACE` (11); inventory HS-S3 R35): for
`0 < y ≤ 6/7`, `log y ≤ -40153/180000 + 2(5y - 4)/(5y + 4)`. Status: stable.
Route: `hs35_log_maj` (`Hs35/Central.lean`): the difference is monotone up to `y = 6/7`. -/
theorem hs3_log_maj {y : ℝ} (hy : 0 < y) (hy7 : y ≤ 6 / 7) :
    log y ≤ -40153 / 180000 + 2 * (5 * y - 4) / (5 * y + 4) :=
  hs35_log_maj hy hy7

/-- **The central endpoint signs** (`DISPLACEMENT_CENTRAL_FACE` (12)-(13); inventory HS-S3 R36):
for `2 ≤ x ≤ 13/6`, at `α = a_min(x)`, `β = 20x/19`, `q = q_c`, `u = ū`: `F₀ < 0`, `F₁ < 0`.
Status: stable. Proof: `hs35_central_endpoint` (`Hs35/Central.lean`, the notes' identities). -/
theorem hs3_central_endpoint {x : ℝ} (hx : 2 ≤ x) (hx2 : x ≤ 13 / 6) :
    hs3F0 x (20 * x / 19) (hs3amin x) (hsUCB x (20 * x / 19)) (hsQc x (hs3amin x)) < 0 ∧
      hs3F1 x (20 * x / 19) (hs3amin x) (hsUCB x (20 * x / 19)) (hsQc x (hs3amin x)) < 0 :=
  hs35_central_endpoint hx hx2

/-- **The central face along the boundary** (`DISPLACEMENT_CENTRAL_FACE` §2 (4)-(10) with
(11)-(13); inventory HS-S3 R34, R37): for `2 ≤ x ≤ 13/6` and `a_min(x) ≤ α ≤ 89/72`, at
`β = b(x, α)`, `q = q_c`, `u = ū(x, β)`: `F₀ < 0` and `F₁ < 0` (the notes: `d/dα F_i(x, α, b(x, α)) <
0` on `[108/95, 89/72]`, then `hs3_central_endpoint`). Status: heavy. -/
theorem hs3_central_alpha {x al : ℝ} (hx : 2 ≤ x) (hx2 : x ≤ 13 / 6) (hal : hs3amin x ≤ al)
    (hal' : al ≤ 89 / 72) :
    hs3F0 x (hs3b x al) al (hsUCB x (hs3b x al)) (hsQc x al) < 0 ∧
      hs3F1 x (hs3b x al) al (hsUCB x (hs3b x al)) (hsQc x al) < 0 := by
  sorry

/-! ### The outer face `q* = 1/7 ≤ q_c` -/

/-- **The enclosing outer domain** (`DISPLACEMENT_OUTER_FACE` §1 (1)-(2); inventory HS-S3 R38): for
`2 ≤ x ≤ 13/6`, `α ≤ x`, `x(x + 2) ≤ 6α²`, `β ≥ x(9x + 8α)/(9x + 8)`, `δ = β/x - 1 ≥ 1/19` and
`α ≥ 1 + (c(x) + 1/23)δ`: `a₀(x) = (100x + 77)/240 ≤ α` and `1/4 ≤ δ/(α - 1) ≤ 115/304`.
Status: stable. -/
theorem hs3_outer_enclose {x al be : ℝ} (hx : 2 ≤ x) (hx2 : x ≤ 13 / 6) (hax : al ≤ x)
    (hqc : x * (x + 2) ≤ 6 * al ^ 2) (hU : x * (9 * x + 8 * al) / (9 * x + 8) ≤ be)
    (hδ : 1 / 19 ≤ be / x - 1)
    (hQ : 1 + ((4 * x ^ 2 + 11 * x + 1) / (7 * x + 1) + 1 / 23) * (be / x - 1) ≤ al) :
    (100 * x + 77) / 240 ≤ al ∧ 1 / 4 ≤ (be / x - 1) / (al - 1) ∧
      (be / x - 1) / (al - 1) ≤ 115 / 304 := by
  have hx0 : 0 < x := by linarith
  have h71 : 0 < 7 * x + 1 := by linarith
  set δ := be / x - 1 with hδdef
  have hbe : be = x * (1 + δ) := by rw [hδdef]; field_simp; ring
  have hδ0 : 0 < δ := by linarith
  set c := (4 * x ^ 2 + 11 * x + 1) / (7 * x + 1) with hc
  have hce : c * (7 * x + 1) = 4 * x ^ 2 + 11 * x + 1 := by rw [hc]; field_simp
  have hc135 : 13 / 5 ≤ c := by nlinarith
  have hcd : (13 / 5 + 1 / 23) * δ ≤ (c + 1 / 23) * δ :=
    mul_le_mul_of_nonneg_right (by linarith) hδ0.le
  have ha1 : 0 < al - 1 := by nlinarith
  refine ⟨?_, ?_, ?_⟩
  · -- `x(x + 2)/6 ≥ a₀²`
    have : ((100 * x + 77) / 240) ^ 2 ≤ al ^ 2 := by nlinarith
    exact (abs_le_of_sq_le_sq' this (by linarith)).2
  · rw [le_div_iff₀ ha1]
    have hU' : x * (9 * x + 8 * al) ≤ be * (9 * x + 8) := by
      rwa [div_le_iff₀ (by positivity)] at hU
    rw [hbe, mul_assoc] at hU'
    have h1 : 9 * x + 8 * al ≤ (1 + δ) * (9 * x + 8) := le_of_mul_le_mul_left hU' hx0
    nlinarith [mul_le_mul_of_nonneg_left hx2 hδ0.le]
  · rw [div_le_iff₀ ha1]
    linarith

/-- **The outer incoming ceiling** (`DISPLACEMENT_OUTER_FACE` (3); inventory HS-S3 R39): for
`2 ≤ x ≤ 13/6`, `x ≤ β ≤ x + 5x(x - 1)/13`: `Sec(1, x, β) ≤ ū(x, β)`. Status: stable. -/
theorem hs3_outer_ceiling {x be : ℝ} (hx : 2 ≤ x) (hx2 : x ≤ 13 / 6) (hxb : x ≤ be)
    (hb : be ≤ x + 5 * x * (x - 1) / 13) : m2Sec 1 x be ≤ hsUO x be := by
  have hx0 : 0 < x := by linarith
  have hS : 0 < (x + 1) * (35 * x + 13) := by positivity
  have hub := hs_sec_le_ubar (by linarith : 1 < x) hxb
  have hbx : (be - x) * 13 ≤ 5 * x * (x - 1) := by linarith
  have htail : (be - x) ^ 3 / (48 * x ^ 2) ≤ (x - 1) ^ 2 * (be - x) / ((x + 1) * (35 * x + 13)) := by
    rw [div_le_div_iff₀ (by positivity) hS]
    have h1 : ((be - x) * 13) ^ 2 ≤ (5 * x * (x - 1)) ^ 2 :=
      pow_le_pow_left₀ (by linarith) hbx 2
    have h2 : (x + 1) * (35 * x + 13) * 25 ≤ 48 * 169 := by nlinarith
    have h3 : (be - x) ^ 2 * ((x + 1) * (35 * x + 13)) ≤ 48 * x ^ 2 * (x - 1) ^ 2 := by
      nlinarith [mul_le_mul_of_nonneg_left h2 (by positivity : (0 : ℝ) ≤ x ^ 2 * (x - 1) ^ 2)]
    nlinarith [mul_le_mul_of_nonneg_left h3 (by linarith : (0 : ℝ) ≤ be - x)]
  refine hub.trans ?_
  rw [hsUbar, hsUO]
  have hb1 : 0 < be - 1 := by linarith
  have e : (2 * (x - 1) ^ 3 / ((x + 1) * (35 * x + 13)) + (x - 1) ^ 2 * (be - x) /
      ((x + 1) * (35 * x + 13))) / (be - 1) =
      (x - 1) ^ 2 * (x + be - 2) / ((be - 1) * (x + 1) * (35 * x + 13)) := by
    field_simp; ring
  rw [← e]
  gcongr

/-- **The outer displacement face** (`DISPLACEMENT_OUTER_FACE` (4)-(21), §6; inventory HS-S3
R40-R44): on `2 ≤ x ≤ 13/6`, `(100x + 77)/240 ≤ α ≤ x`, `β = x(1 + g(α - 1))` with
`1/4 ≤ g ≤ 115/304`, at `q = 1/7`, `u = ū(x, β)`: `F₀ < 0` and `F₁ < 0`. Status: heavy. -/
theorem hs3_outer_face {x al g : ℝ} (hx : 2 ≤ x) (hx2 : x ≤ 13 / 6) (hal : (100 * x + 77) / 240 ≤ al)
    (hax : al ≤ x) (hg : 1 / 4 ≤ g) (hg' : g ≤ 115 / 304) :
    hs3F0 x (x * (1 + g * (al - 1))) al (hsUO x (x * (1 + g * (al - 1)))) (1 / 7) < 0 ∧
      hs3F1 x (x * (1 + g * (al - 1))) al (hsUO x (x * (1 + g * (al - 1)))) (1 / 7) < 0 := by
  sorry

/-! ### Gate S3 -/

/-- `D > 0` on the S3 domain (inventory HS-S3 R9(e); replaces the S0 positive diagonal):
`D ≥ 5α² - 4αx + 1 + 2x ≥ 6 - 2x` from `β < 2α`. -/
private lemma hs3_D_pos {x be al : ℝ} (hx2 : x ≤ 13 / 6) (hal : 1 ≤ al)
    (hax : al ≤ x) (hb2 : be < 2 * al) : 0 < hsDg x be al := by
  rw [hsDg]
  have h1 : be * (x - al) ≤ 2 * al * (x - al) := mul_le_mul_of_nonneg_right hb2.le (by linarith)
  have h2 : 0 ≤ (al - 1) * (5 * al + 5 - 4 * x) := mul_nonneg (by linarith) (by linarith)
  nlinarith

/-- `V̄(x) ≤ 19/25` on `2 ≤ x ≤ 13/6` (inventory HS-S3 R9(d)). -/
private lemma hs3_Vbar_le {x : ℝ} (hx : 2 ≤ x) (hx2 : x ≤ 13 / 6) : hsVbar x ≤ 19 / 25 := by
  rw [hsVbar]
  have : 2 * (x - 1) ^ 2 / ((x + 1) * (35 * x + 13)) ≤ 1 / 100 := by
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]
    nlinarith
  linarith

/-- The duration weight at `τ = 2` stays below `T + 1` (`DISPLACEMENT_WEIGHT_REDUCTION` (13):
`kT² - (k + 16)T + 24 > 0`, discriminant `k² - 64k + 256 < 0` for `9/2 ≤ k ≤ 59/6`). -/
private lemma hs3_n0_le {k T : ℝ} (hk : 9 / 2 ≤ k) (hk' : k ≤ 59 / 6) (hT : 0 < T) :
    2 + 4 * (4 - 3 * (2 / T)) / k ≤ T + 1 := by
  have hk0 : 0 < k := by linarith
  have e : 2 + 4 * (4 - 3 * (2 / T)) / k = (2 * k * T + 16 * T - 24) / (k * T) := by
    field_simp; ring
  rw [e, div_le_iff₀ (by positivity)]
  have h4 : 0 ≤ (2 * k * T - (k + 16)) ^ 2 := sq_nonneg _
  have h5 : 0 ≤ (k - 9 / 2) * (59 / 6 - k) := mul_nonneg (by linarith) (by linarith)
  nlinarith

/-- The central boundary stays in the central-beta domain (`DISPLACEMENT_CENTRAL_FACE` §1):
for `α > a_min(x)` and `6α² ≤ x(x + 2)`: `b(x, α) ≤ 2α`, `b(x, α) ≤ x + 5x(α - 1)/13` and
`α ≤ (5x + 4)/12 ≤ 89/72`. -/
private lemma hs3_b_facts {x al : ℝ} (hx : 2 ≤ x) (hx2 : x ≤ 13 / 6) (hamin : hs3amin x < al)
    (h6 : 6 * al ^ 2 ≤ x * (x + 2)) :
    hs3b x al ≤ 2 * al ∧ hs3b x al ≤ x + 5 * x * (al - 1) / 13 ∧ al ≤ 89 / 72 := by
  rw [hs3amin] at hamin
  have h36 : 0 < 15 * x + 36 := by linarith
  have hal1 : 1 ≤ al := by
    have : 1 ≤ (15 * x + 511) / 475 := by rw [le_div_iff₀ (by norm_num)]; linarith
    linarith
  have hB : 25 * x / (15 * x + 36) ≤ 5 * x / 13 := by
    rw [div_le_div_iff₀ h36 (by norm_num)]; nlinarith
  have hb' : hs3b x al ≤ x + 5 * x * (al - 1) / 13 := by
    rw [hs3b]
    have := mul_le_mul_of_nonneg_right hB (by linarith : (0 : ℝ) ≤ al - 1)
    have e : 5 * x / 13 * (al - 1) = 5 * x * (al - 1) / 13 := by ring
    linarith
  refine ⟨?_, hb', ?_⟩
  · rw [hs3b]
    have e : (2 * al - (x + 25 * x / (15 * x + 36) * (al - 1))) * (15 * x + 36) =
        al * (5 * x + 72) - 15 * x ^ 2 - 11 * x := by field_simp; ring
    have h1 : (15 * x + 511) * (5 * x + 72) ≤ 475 * al * (5 * x + 72) := by
      have : 15 * x + 511 ≤ 475 * al := by
        rw [div_lt_iff₀ (by norm_num)] at hamin; linarith
      nlinarith
    have h2 : 0 ≤ (2 * al - (x + 25 * x / (15 * x + 36) * (al - 1))) * (15 * x + 36) := by
      rw [e]; nlinarith
    have := nonneg_of_mul_nonneg_left h2 h36
    linarith
  · have := hs3_al_le (by linarith) h6
    linarith

/-- Raising the incoming norm in both duration tests (`hs3_uslope` with `n₀, n₁ ≤ T + 1`). -/
private lemma hs3_gate_us {x be al u ub qs : ℝ} (h1 : 2 ≤ x) (h2 : x ≤ 13 / 6) (h108 : 108 / 95 ≤ al)
    (hax : al ≤ x) (hxb : x ≤ be) (hD0 : 0 < hsDg x be al) (hDQ : hsDg x be al < al * (al + be))
    (hD3 : hsDg x be al < 3 * al ^ 2) (hrA3 : 1 / 3 < hsRA al be) (hrA13 : hsRA al be ≤ 13 / 30)
    (hqs0 : 0 < qs) (hqs7 : qs ≤ 1 / 7) (hub : u ≤ ub) :
    hs3F0 x be al u qs ≤ hs3F0 x be al ub qs ∧ hs3F1 x be al u qs ≤ hs3F1 x be al ub qs := by
  have hk0 : 0 < 5 * al - 1 := by linarith
  have hk4 : 4 ≤ 5 * al - 1 := by linarith
  have hrA0 : 0 < hsRA al be := by linarith
  have hT : 0 < hsRA al be / qs := by positivity
  have hn0 : 0 ≤ 2 + 4 * (4 - 3 * (2 * qs / hsRA al be)) / (5 * al - 1) := by
    have : 2 * qs / hsRA al be ≤ 1 := by rw [div_le_one hrA0]; linarith
    have : 0 ≤ 4 * (4 - 3 * (2 * qs / hsRA al be)) / (5 * al - 1) := div_nonneg (by linarith) hk0.le
    linarith
  have hn0T : 2 + 4 * (4 - 3 * (2 * qs / hsRA al be)) / (5 * al - 1) ≤ hsRA al be / qs + 1 := by
    have h := hs3_n0_le (k := 5 * al - 1) (T := hsRA al be / qs) (by linarith) (by linarith) hT
    have e : 2 / (hsRA al be / qs) = 2 * qs / hsRA al be := by field_simp
    rwa [e] at h
  have h4k : 4 / (5 * al - 1) ≤ 1 := by rw [div_le_one hk0]; exact hk4
  exact ⟨hs3_uslope h1 h2 (by linarith) hax hxb hD0 hDQ hD3 hqs0 hqs7 hrA13 hn0 hn0T hub,
    hs3_uslope h1 h2 (by linarith) hax hxb hD0 hDQ hD3 hqs0 hqs7 hrA13 (by positivity)
      (by linarith) hub⟩

/-- **The scale reduction** (`DISPLACEMENT_HAND_EXCLUSION`, `DISPLACEMENT_WEIGHT_REDUCTION` §§4-5,
`DISPLACEMENT_SCALE_CONTINUATION` §6): if the weighted envelope `Φ` at the actual normalized
duration `p = τq` is nonnegative at the actual scale `q` and negative at `0`, then at every scale
`q* ∈ [q, 1/7]` one of the duration tests is nonnegative. -/
private lemma hs3_gate_max {x be al u q τ qs : ℝ} (h1 : 2 ≤ x) (h2 : x ≤ 13 / 6) (hal1 : 1 ≤ al)
    (hax : al ≤ x) (hxb : x ≤ be) (hrA3 : 1 / 3 < hsRA al be) (hu34 : 3 / 4 ≤ u)
    (hu1925 : u ≤ 19 / 25) (hD0 : 0 < hsDg x be al) (hD3 : hsDg x be al < 3 * al ^ 2)
    (h108 : 108 / 95 ≤ al) (hq0 : 0 < q) (hτ2 : 2 ≤ τ) (hpr : τ * q ≤ hsRA al be)
    (hG : 0 ≤ hsPhi x be al u (τ * q) (4 * (4 - 3 * (τ * q / hsRA al be)) / (5 * al - 1)) q)
    (hΦ0 : hsPhi x be al u (τ * q) (4 * (4 - 3 * (τ * q / hsRA al be)) / (5 * al - 1)) 0 < 0)
    (hA2 : 0 < hsA2 x be al u) (hqs0 : 0 < qs) (hqs7 : qs ≤ 1 / 7) (hqqs : q ≤ qs) :
    0 ≤ max (hs3F0 x be al u qs) (hs3F1 x be al u qs) := by
  have hbe0 : 0 < be := by linarith
  have hk0 : 0 < 5 * al - 1 := by linarith
  have hp0 : 0 < τ * q := by positivity
  have h2qp : 2 * q ≤ τ * q := by nlinarith
  have h2qs : 2 * qs ≤ hsRA al be := by linarith
  have hm0 : 0 ≤ 4 * (4 - 3 * (τ * q / hsRA al be)) / (5 * al - 1) := by
    have : τ * q / hsRA al be ≤ 1 := by rw [div_le_one (by linarith)]; exact hpr
    exact div_nonneg (by linarith) hk0.le
  generalize τ * q = p at hp0 h2qp hpr hG hΦ0 hm0
  generalize hm : 4 * (4 - 3 * (p / hsRA al be)) / (5 * al - 1) = m at hG hΦ0 hm0
  have hconv := hs_phi_convex_max (x := x) (be := be) (al := al) (u := u) (p := p)
    (qm := min qs (p / 2)) hm0 hA2.le hq0.le (le_min hqqs (by linarith))
  have hΦm : 0 ≤ hsPhi x be al u p m (min qs (p / 2)) := by
    by_contra hneg
    have := max_lt hΦ0 (not_le.mp hneg)
    linarith
  rcases lt_or_ge (p / 2) qs with hlt | hge
  · rw [min_eq_right hlt.le] at hΦm
    have e := hs_phi_eq (x := x) (be := be) (al := al) (u := u) (m := m) hp0
      (by positivity : (0 : ℝ) < p / 2)
    have e2 : p / (p / 2) = 2 := by field_simp
    rw [e2] at e
    have hc := hs3_tau2_cont (u := u) (q₁ := p / 2) (q₂ := qs) h1 h2 (by linarith) hax hxb
      hrA3.le hu34 hu1925 hD0 hD3 (by positivity) hlt hqs7
    have e3 : 2 * (p / 2) = p := by ring
    rw [e3, hm] at hc
    have hd := hs3_dur (x := x) (u := u) (τ := 2) hal1 hbe0 hqs0 le_rfl h2qs
    linarith
  · rw [min_eq_left hge] at hΦm
    have e := hs_phi_eq (x := x) (be := be) (al := al) (u := u) (m := m) hp0 hqs0
    have hτ' : 2 ≤ p / qs := by rw [le_div_iff₀ hqs0]; linarith
    have hd := hs3_dur (x := x) (u := u) (τ := p / qs) hal1 hbe0 hqs0 hτ'
      (by rw [div_mul_cancel₀ _ hqs0.ne']; exact hpr)
    rw [div_mul_cancel₀ _ hqs0.ne', hm] at hd
    linarith

/-- **The central face** `q* = q_c ≤ 1/7` (`DISPLACEMENT_CENTRAL_FACE` §4; inventory HS-S3 R37):
`F_i(u) ≤ F_i(ū(x, β)) ≤ F_i(ū(x, b), b) < 0`. -/
private lemma hs3_gate_central {x be al u : ℝ} (h1 : 2 ≤ x) (h2 : x ≤ 13 / 6) (hal1 : 1 ≤ al)
    (hax : al ≤ x) (hxb : x ≤ be) (hδ : 1 / 19 ≤ be / x - 1)
    (hQ : 1 + ((4 * x ^ 2 + 11 * x + 1) / (7 * x + 1) + 1 / 23) * (be / x - 1) ≤ al)
    (h108 : 108 / 95 ≤ al) (hb2a : be < 2 * al) (hDQ : hsDg x be al < al * (al + be))
    (hD3 : hsDg x be al < 3 * al ^ 2) (hrA13 : hsRA al be ≤ 13 / 30) (hu : u = m2Sec 1 x be)
    (hqc7 : hsQc x al ≤ 1 / 7) (hM : 0 ≤ max (hs3F0 x be al u (hsQc x al)) (hs3F1 x be al u (hsQc x al))) :
    False := by
  have hx0 : 0 < x := by linarith
  have hqc0 : 0 < hsQc x al := by rw [hsQc]; positivity
  have h6 : 6 * al ^ 2 ≤ x * (x + 2) := (hs_qc_le_iff hx0).1 hqc7
  obtain ⟨hamin, hbb⟩ := hs3_central_straight h1 h2 hδ hQ
  obtain ⟨hb2, hb2', hα89⟩ := hs3_b_facts h1 h2 hamin h6
  have hb20 : 20 * x / 19 ≤ be := by
    rw [div_le_iff₀ (by norm_num)]
    have := mul_le_mul_of_nonneg_left hδ hx0.le
    have e : x * (be / x - 1) = be - x := by field_simp
    linarith
  have hb' : be ≤ x + 5 * x * (al - 1) / 13 := hbb.le.trans hb2'
  have hrA3 : 1 / 3 < hsRA al be := by
    rw [hsRA, lt_div_iff₀ (by linarith)]; linarith
  have huc : u ≤ hsUCB x be := by rw [hu]; exact hs3_central_ceiling h1 h2 h108 h6 hb20 hb'
  obtain ⟨hu0, hu1⟩ := hs3_gate_us h1 h2 h108 hax hxb (hs3_D_pos h2 hal1 hax hb2a) hDQ hD3
    hrA3 hrA13 hqc0 hqc7 huc
  obtain ⟨hβ0, hβ1⟩ := hs3_beta_mono h1 h2 h108 h6 hb20 hbb.le hb2 hb2'
  obtain ⟨hF0, hF1⟩ := hs3_central_alpha h1 h2 hamin.le hα89
  have := max_lt (hu0.trans_lt (hβ0.trans_lt hF0)) (hu1.trans_lt (hβ1.trans_lt hF1))
  linarith

/-- **The outer face** `q* = 1/7 < q_c` (`DISPLACEMENT_OUTER_FACE` §6; inventory HS-S3 R44). -/
private lemma hs3_gate_outer {x be al u : ℝ} (h1 : 2 ≤ x) (h2 : x ≤ 13 / 6) (hal1 : 1 ≤ al)
    (hax : al ≤ x) (hxb : x ≤ be) (hδ : 1 / 19 ≤ be / x - 1)
    (hU : x * (9 * x + 8 * al) / (9 * x + 8) ≤ be)
    (hQ : 1 + ((4 * x ^ 2 + 11 * x + 1) / (7 * x + 1) + 1 / 23) * (be / x - 1) ≤ al)
    (h108 : 108 / 95 ≤ al) (hb2a : be < 2 * al) (hDQ : hsDg x be al < al * (al + be))
    (hD3 : hsDg x be al < 3 * al ^ 2) (hrA13 : hsRA al be ≤ 13 / 30) (hu : u = m2Sec 1 x be)
    (hqc7 : 1 / 7 < hsQc x al) (hM : 0 ≤ max (hs3F0 x be al u (1 / 7)) (hs3F1 x be al u (1 / 7))) :
    False := by
  have hx0 : 0 < x := by linarith
  have h6 : x * (x + 2) ≤ 6 * al ^ 2 := by
    rw [hsQc, lt_div_iff₀ (by positivity)] at hqc7
    linarith
  obtain ⟨ha0, hg1, hg2⟩ := hs3_outer_enclose h1 h2 hax h6 hU hδ hQ
  have hα1 : 0 < al - 1 := by linarith
  have hbg : x * (1 + (be / x - 1) / (al - 1) * (al - 1)) = be := by
    rw [div_mul_cancel₀ _ hα1.ne']; field_simp; ring
  have hbo : be ≤ x + 5 * x * (x - 1) / 13 := by
    have hc : 13 / 5 ≤ (4 * x ^ 2 + 11 * x + 1) / (7 * x + 1) := by
      rw [le_div_iff₀ (by linarith)]; nlinarith
    have h13 : 13 / 5 * (be / x - 1) ≤ al - 1 := by
      have := mul_le_mul_of_nonneg_right hc (by linarith : (0 : ℝ) ≤ be / x - 1)
      have : 0 ≤ 1 / 23 * (be / x - 1) := by positivity
      nlinarith
    have e : x * (be / x - 1) = be - x := by field_simp
    nlinarith [mul_le_mul_of_nonneg_left h13 hx0.le]
  have hrA3 : 1 / 3 < hsRA al be := by
    rw [hsRA, lt_div_iff₀ (by linarith)]; linarith
  have huo : u ≤ hsUO x be := by rw [hu]; exact hs3_outer_ceiling h1 h2 hxb hbo
  obtain ⟨hu0, hu1⟩ := hs3_gate_us h1 h2 h108 hax hxb (hs3_D_pos h2 hal1 hax hb2a) hDQ hD3
    hrA3 hrA13 (by norm_num) le_rfl huo
  obtain ⟨hF0, hF1⟩ := hs3_outer_face h1 h2 ha0 hax hg1 hg2
  rw [hbg] at hF0 hF1
  have := max_lt (hu0.trans_lt hF0) (hu1.trans_lt hF1)
  linarith

namespace HsData

variable (H : HsData)

/-- The order inputs of gate S3 at the actual shape (`hs_strong_order`, `hs_upper_order_98`,
`hs_quad_order` with `δ²/(1 + 4δ) ≥ δ/23` for `δ ≥ 1/19`). -/
private lemma hs3_orders (h1 : 2 ≤ H.x) (h2 : H.x ≤ 13 / 6) (hδ : 1 / 19 ≤ H.be / H.x - 1) :
    1 + (4 * H.x ^ 2 + 11 * H.x + 1) / (7 * H.x + 1) * (H.be / H.x - 1) ≤ H.al ∧
      H.x * (9 * H.x + 8 * H.al) / (9 * H.x + 8) ≤ H.be ∧
      1 + ((4 * H.x ^ 2 + 11 * H.x + 1) / (7 * H.x + 1) + 1 / 23) * (H.be / H.x - 1) ≤ H.al := by
  have hx0 : 0 < H.x := by linarith
  refine ⟨?_, ?_, ?_⟩
  · have h := H.strong_order
    have e : H.be / H.x + hsKs H.x * (H.be - H.x) =
        1 + (4 * H.x ^ 2 + 11 * H.x + 1) / (7 * H.x + 1) * (H.be / H.x - 1) := by
      rw [hsKs]; field_simp; ring
    linarith
  · have h := mul_le_mul_of_nonneg_left (H.upper_order_98 (by linarith)) (by linarith : 0 ≤ 8 * H.x)
    have e : 8 * H.x * (H.be / H.x + 9 / 8 * (H.be - H.x)) = 8 * H.be + 9 * H.x * (H.be - H.x) := by
      field_simp
    rw [div_le_iff₀ (by linarith)]
    linarith
  · have h := hs_quad_order h1 h2 H.one_le_al H.al_lt_x H.x_le_be (H.u_eq.symm.trans H.u_eq')
    have : (H.be / H.x - 1) / 23 ≤ (H.be / H.x - 1) ^ 2 / (1 + 4 * (H.be / H.x - 1)) := by
      rw [div_le_div_iff₀ (by norm_num) (by linarith)]; nlinarith
    linarith

/-- `q = ρ_A > 0` at the actual data. -/
private lemma hs3_q_pos : 0 < hsQ H.al H.rho := by
  have hden : 0 < 1 + H.rho * (H.al ^ 2 - 1) := by
    have : 0 ≤ H.al ^ 2 - 1 := by nlinarith [H.one_le_al]
    have := H.rho_pos
    positivity
  have hLam : 0 < hsLam H.al H.rho := by rw [hsLam]; exact one_div_pos.mpr hden
  rw [hsQ]
  have := H.one_le_al
  exact mul_pos (mul_pos (by positivity) hLam) H.rho_pos

/-- **The weighted envelope at the actual root** (`DISPLACEMENT_WEIGHT_REDUCTION` §2, §4; inventory
HS-S3 R11, R13): `0 ≤ Φ(q)` at `p = τq`, `m = 4(4 - 3p/r_A)/(5α - 1)` (`root_zero`, `w ≥ 3/4`,
`hs_env_weighted` with `hs3_B_pos`, `hs_env_scale`, `hs_phi_eq`). -/
private lemma hs3_env (h1 : 2 ≤ H.x) :
    0 ≤ hsPhi H.x H.be H.al H.u (H.τ * hsQ H.al H.rho)
      (4 * (4 - 3 * (H.τ * hsQ H.al H.rho / hsRA H.al H.be)) / (5 * H.al - 1)) (hsQ H.al H.rho) := by
  have hx1 : 1 < H.x := H.one_lt_x
  have hx0 : 0 < H.x := by linarith
  have hal1 : 1 ≤ H.al := H.one_le_al
  have hq0 := H.hs3_q_pos
  have hq7 : hsQ H.al H.rho < 1 / 7 := H.q_lt_seventh
  have hτ2 : 2 < H.τ := H.two_lt_τ
  have hτT : H.τ * hsQ H.al H.rho < hsRA H.al H.be := H.τ_lt
  have hrA0 : 0 < hsRA H.al H.be := by
    rw [hsRA]; have := H.x_le_be; apply div_pos <;> linarith
  have hk0 : 0 < 5 * H.al - 1 := by linarith
  have hm0 : 0 ≤ 4 * (4 - 3 * (H.τ * hsQ H.al H.rho / hsRA H.al H.be)) / (5 * H.al - 1) := by
    have : H.τ * hsQ H.al H.rho / hsRA H.al H.be ≤ 1 := by rw [div_le_one hrA0]; exact hτT.le
    apply div_nonneg _ hk0.le
    linarith
  have ht0 : H.rho * (1 + H.x) ≤ H.t := by
    have h := H.rho_lt_rt
    rw [one_div_mul_eq_div, lt_div_iff₀ (by linarith)] at h
    exact h.le
  have henv := hs_env_weighted (u := H.u) (τ := H.τ)
    (m := 4 * (4 - 3 * (H.τ * hsQ H.al H.rho / hsRA H.al H.be)) / (5 * H.al - 1))
    hx1 hal1 H.rho_pos ht0 H.t_le_r H.v_le
    (fun s hs => hs3_B_pos h1 hal1 H.al_lt_x.le H.x_le_be H.rho_pos hs.1 hτ2.le hτT.le)
  rw [H.root_zero, ← H.w_eq] at henv
  have hρq : hsRhoOf H.al (hsQ H.al H.rho) = H.rho :=
    (hs_scale_coords (x := H.x) (be := H.be) hal1 H.rho_pos).1
  obtain ⟨e1, -, e3, -⟩ := hs_env_scale (x := H.x) (be := H.be) (al := H.al) (u := H.u)
    (q := hsQ H.al H.rho) (τ := H.τ) hx0 hal1 hq0 (by linarith)
  rw [hρq] at e1 e3
  rw [e1, e3] at henv
  have hw : 0 ≤ 4 * (4 - 3 * (H.τ * hsQ H.al H.rho / hsRA H.al H.be)) / (5 * H.al - 1) *
      (H.w - 3 / 4) := mul_nonneg hm0 (by linarith [H.w_ge])
  have e := hs_phi_eq (x := H.x) (be := H.be) (al := H.al) (u := H.u)
    (m := 4 * (4 - 3 * (H.τ * hsQ H.al H.rho / hsRA H.al H.be)) / (5 * H.al - 1))
    (by positivity : 0 < H.τ * hsQ H.al H.rho) hq0
  have e2 : H.τ * hsQ H.al H.rho / hsQ H.al H.rho = H.τ := by field_simp
  rw [e2] at e
  rw [← e]
  unfold hsRs at henv
  unfold hsF at henv ⊢
  linarith

/-- **Gate S3** (`DISPLACEMENT_HAND_EXCLUSION`; inventory HS-S3 R45): for `2 ≤ x ≤ 13/6`,
`δ < 1/19`.
Proof plan: if `δ ≥ 1/19`: `strong_order`, `upper_order_98`, `hs_quad_order`, `hs3_shape`,
`hs_D_lt_Q`, `u_le_V`, `hs_V_le_Vbar` give the shape bounds; `root_zero`, `w_ge`,
`hs_env_weighted` (`hs3_B_pos`) give `0 ≤ G*_τ`; `hs_phi_eq`, `hs_A2_pos`, `hs_phi_convex_max`,
`hs3_zero_neg`, `q_le_qc`, `q_lt_seventh`, `hs3_tau2_cont` reach `q*`; `hs3_dur`, `hs3_uslope`; then
the central face (`hs_qc_le_iff`, `hs3_central_straight`, `hs3_central_ceiling`, `hs3_beta_mono`,
`hs3_central_alpha`) or the outer face (`hs3_outer_enclose`, `hs3_outer_ceiling`, `hs3_outer_face`)
contradicts.
Status: assembly (to be proved from the leaves above). -/
theorem s3 (h1 : 2 ≤ H.x) (h2 : H.x ≤ 13 / 6) : H.δ < 1 / 19 := by
  by_contra hcon
  have hδ : 1 / 19 ≤ H.be / H.x - 1 := not_lt.mp hcon
  have hx1 : 1 < H.x := H.one_lt_x
  have hal1 : 1 ≤ H.al := H.one_le_al
  have hax : H.al < H.x := H.al_lt_x
  have hxb : H.x ≤ H.be := H.x_le_be
  obtain ⟨hL, hU, hQ⟩ := H.hs3_orders h1 h2 hδ
  obtain ⟨h108, hb2a, hrA3, hrA13⟩ := hs3_shape h1 h2 hal1 hax.le hxb hδ hL hU
  obtain ⟨hDQ, hD3⟩ := hs_D_lt_Q h1 hal1 hax.le hU
  have hu34 : 3 / 4 ≤ H.u := H.u_ge_34
  have hu1925 : H.u ≤ 19 / 25 :=
    H.u_le_V.trans ((hs_V_le_Vbar hx1).trans (hs3_Vbar_le h1 h2))
  have hq0 : 0 < hsQ H.al H.rho := H.hs3_q_pos
  have hτ2 : 2 < H.τ := H.two_lt_τ
  have hτT : H.τ * hsQ H.al H.rho < hsRA H.al H.be := H.τ_lt
  have hG := H.hs3_env h1
  have hΦ0 := hs3_zero_neg h1 h2 (by linarith) hax.le hxb hU hrA3 hrA13 hu34 H.u_le_rA hDQ
    (by positivity) hτT.le
  have hmax := fun qs hqs0 hqs7 hqqs => hs3_gate_max h1 h2 hal1 hax.le hxb hrA3 hu34 hu1925
    (hs3_D_pos h2 hal1 hax.le hb2a) hD3 h108 hq0 hτ2.le hτT.le hG hΦ0
    (hs_A2_pos h1 (by linarith) hal1 hu34 (by linarith)) (qs := qs) hqs0 hqs7 hqqs
  rcases le_or_gt (hsQc H.x H.al) (1 / 7) with hqc7 | hqc7
  · exact hs3_gate_central h1 h2 hal1 hax.le hxb hδ hQ h108 hb2a hDQ hD3 hrA13 H.u_eq hqc7
      (hmax (hsQc H.x H.al) (lt_of_lt_of_le hq0 H.q_le_qc) hqc7 H.q_le_qc)
  · exact hs3_gate_outer h1 h2 hal1 hax.le hxb hδ hU hQ h108 hb2a hDQ hD3 hrA13 H.u_eq hqc7
      (hmax (1 / 7) (by norm_num) le_rfl H.q_lt_seventh.le)

end HsData

/-- **Gate S3 for the actual window**: given `2 ≤ C/a ≤ 13/6`, `B/C - 1 < 1/19`. -/
theorem M2Short.hs_S3 (D : M2Short) (h1 : 2 ≤ D.C / D.a) (h2 : D.C / D.a ≤ 13 / 6) :
    D.B / D.C - 1 < 1 / 19 := by
  have h := D.toHs.s3 (by rwa [D.toHs_x]) (by rwa [D.toHs_x])
  rwa [D.toHs_δ] at h

end SmoothedOctagon
