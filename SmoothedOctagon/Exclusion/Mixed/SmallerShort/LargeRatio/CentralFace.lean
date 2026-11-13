module

public import SmoothedOctagon.Exclusion.Mixed.SmallerShort.Basic
public import SmoothedOctagon.Exclusion.Mixed.SmallerShort.LargeRatio.SignTools

/-!
# Smaller-short window, large ratio: the central face, forms and beta convexity

The forms of the three central-face tests of the large-ratio bound and their reduction in `β` to two faces.

At the central scale `q = q_c = α²/K`, `K = x² + 2x + α²`, the floor-weighted face value is
`lgrGc S K α B u D τ ℓ = (w - 1)τ + 1/τ + (u - 1)B/α + α/B + 1 - q - E_L + ℓ + (w - 3/4)/2` with
`w = W/K²`, `E_L = L/K`, `W = S²(S² - S + 1) + D²u - DE`, `L = 2Du - E`, `E = S³(u - 1) + 3S - 1`
(`lgr_cen_F`). The three tests are `τ = 2` (with the tangent `ℓ = 5q/(2r_A) - 11/9`), `τ = T` and
`τ = 8T/9`, `T = K/(αB)`.

**Beta convexity.** With `η = β - 1`, `u = u_∞ + J/η` and `D = (α + 1)² + 2(α - x)η`, every test
is `kη² + lη + m + r/η + s/(η + α + 1)` (`lgr_pf_two`, `lgr_pf_dur`), with `k = (5/2)δ²u_∞/K²` resp.
`δ²u_∞/(2K²)`, the residue `r = J·A` at `β = 1` and `s = α` resp. `(γK/α)(w_N - 1) + α` at
`β = -α`. The chord lemma `lgr_chord` then bounds each test by its values at `β = x` and at the
upper end (`lgr_cen_two_chord`, `lgr_cen_dur_chord`), once
* `τ = 2`: `k(x - 1)³ + r ≥ 0` (`lgr_two_res`), from the positive
  polynomial `lgrPhi2f` on the shape domain;
* `τ = T, 8T/9`: `s ≥ 0` (`lgr_dur_s`: `Q + α²K ≥ 0`, the continued norm at `β = -α`) and
  `k(x - 1)³ + r ≥ (x - 1)³h²/(64K²)`-type bound (`lgr_dur_res`, from `K ≤ (25/2)αh`,
  `S(α + 1)² ≤ (45/2)h²`, `M ≥ 28S`).

Polynomial signs on the shape domain `12/5 ≤ x ≤ 9`, `1 ≤ α ≤ (5x + 4)/12` use the coefficient
bound `lgrLow` on three pieces (`lgr_trap_pos`). The cleared numerators `lgrN2`,
`lgrNT`, `lgrN8` are also given on coefficient lists (`lgrNcL`,
`lgrFNc`), so that each face polynomial is computed inside Lean from the factored formula
(`lgr_H2_FN2`, …: `ring` on at most seven atoms), never printed.

## Main API

* `lgrWn`, `lgrLn`, `lgrGc`, `lgr_cen_F`; `lgrUc`, `lgrVc` (`û = U/V`).
* `lgr_trap_pos`: the coefficient bound on the shape domain.
* `lgr_cen_two_chord`, `lgr_cen_dur_chord`: the beta reductions.
* `lgrN2`, `lgrNT`, `lgrN8`, `lgr_G2_neg`, …; on lists `lgrFNc`, `lgr_H2_FN2`, `lgr_H2_FNT`,
  `lgr_H2_FN8`.
-/

@[expose] public section

namespace SmoothedOctagon

/-! ### The central face value -/

/-- `W = S²(S² - S + 1) + D²u - DE` with `E = S³(u - 1) + 3S - 1`: `w = W/K²`. -/
noncomputable def lgrWn (S u D : ℝ) : ℝ :=
  S ^ 2 * (S ^ 2 - S + 1) + D ^ 2 * u - D * (S ^ 3 * (u - 1) + 3 * S - 1)

/-- `L = 2Du - E`: `E_L = L/K`. -/
noncomputable def lgrLn (S u D : ℝ) : ℝ := 2 * D * u - (S ^ 3 * (u - 1) + 3 * S - 1)

/-- **The central face value** `(w - 1)τ + 1/τ + (u - 1)B/α + α/B + 1 - α²/K - E_L + ℓ + (w - 3/4)/2`. -/
noncomputable def lgrGc (S K a B u D τ ℓ : ℝ) : ℝ :=
  (lgrWn S u D / K ^ 2 - 1) * τ + 1 / τ + (u - 1) * B / a + a / B + 1 - a ^ 2 / K -
    lgrLn S u D / K + ℓ + (lgrWn S u D / K ^ 2 - 3 / 4) / 2

theorem lgr_Ws_c {x a b u : ℝ} (hx : 0 < x) (ha : 0 < a) :
    ssWs x b a u (ssQc x a) = lgrWn (x + 1) u (ssDg x b a) / (x ^ 2 + 2 * x + a ^ 2) ^ 2 := by
  have hK : 0 < x ^ 2 + 2 * x + a ^ 2 := by positivity
  unfold ssWs ssA1 ssA2 ssQc ssE0 lgrWn
  field_simp
  ring

theorem lgr_ELs_c {x a b u : ℝ} (hx : 0 < x) (ha : 0 < a) :
    ssELs x b a u (ssQc x a) = lgrLn (x + 1) u (ssDg x b a) / (x ^ 2 + 2 * x + a ^ 2) := by
  have hK : 0 < x ^ 2 + 2 * x + a ^ 2 := by positivity
  unfold ssELs ssA3 ssQc ssE0 lgrLn
  field_simp
  ring

/-- **The central face value** of `ssF` at `q = q_c`, floor weight `1/2`. -/
theorem lgr_cen_F {x a b u τ ℓ : ℝ} (hx : 0 < x) (ha : 0 < a) (hB : 0 < a + b) :
    ssF x b a u (ssQc x a) τ ℓ (1 / 2) =
      lgrGc (x + 1) (x ^ 2 + 2 * x + a ^ 2) a (a + b) u (ssDg x b a) τ ℓ := by
  have hK : 0 < x ^ 2 + 2 * x + a ^ 2 := by positivity
  unfold ssF
  rw [lgr_Ws_c hx ha, lgr_ELs_c hx ha]
  unfold lgrGc ssRA ssQc
  field_simp

/-- `T = r_A/q_c = K/(αB)`. -/
theorem lgr_T_c {x a b : ℝ} (hx : 0 < x) (ha : 0 < a) (hB : 0 < a + b) :
    ssRA a b / ssQc x a = (x ^ 2 + 2 * x + a ^ 2) / (a * (a + b)) := by
  have hK : 0 < x ^ 2 + 2 * x + a ^ 2 := by positivity
  unfold ssRA ssQc
  field_simp

/-! ### The incoming ceiling `û` -/

/-- `U = 3SM(β - 1) + (x - 1)²(β + 7x - 8)`. -/
noncomputable def lgrUc (x b : ℝ) : ℝ :=
  3 * (x + 1) * (35 * x + 13) * (b - 1) + (x - 1) ^ 2 * (b + 7 * x - 8)

/-- `V = 4SM(β - 1)`: `û = U/V`. -/
noncomputable def lgrVc (x b : ℝ) : ℝ := 4 * (x + 1) * (35 * x + 13) * (b - 1)

theorem lgr_uhat_UV {x b : ℝ} (hx : 1 < x) (hb : 1 < b) : ssUhat x b = lgrUc x b / lgrVc x b := by
  have hb1 : 0 < b - 1 := by linarith
  unfold ssUhat lgrUc lgrVc
  field_simp
  ring

/-- `u_∞ = 3/4 + (x - 1)²/(4SM)`. -/
noncomputable def lgrui (x : ℝ) : ℝ := 3 / 4 + (x - 1) ^ 2 / (4 * (x + 1) * (35 * x + 13))

/-- `J = 7(x - 1)³/(4SM)`. -/
noncomputable def lgrJ (x : ℝ) : ℝ := 7 * (x - 1) ^ 3 / (4 * (x + 1) * (35 * x + 13))

theorem lgr_uhat_pole {x b : ℝ} (hx : 1 < x) (hb : 1 < b) :
    ssUhat x b = lgrui x + lgrJ x / (b - 1) := by
  have hb1 : 0 < b - 1 := by linarith
  unfold ssUhat lgrui lgrJ
  field_simp
  ring

theorem lgr_Dg_pole (x a b : ℝ) :
    ssDg x b a = (a + 1) ^ 2 + 2 * (a - x) * (b - 1) := by
  unfold ssDg; ring

/-! ### Partial fractions in `η = β - 1` -/

/-- `e₀ = S³(u_∞ - 1) + 3S - 1`. -/
noncomputable def lgre0 (S ui : ℝ) : ℝ := S ^ 3 * (ui - 1) + 3 * S - 1
/-- Coefficient of `η²` in `W`. -/
noncomputable def lgrWk (ui δ : ℝ) : ℝ := δ ^ 2 * ui
/-- Coefficient of `η` in `W`. -/
noncomputable def lgrWl (S ui J D1 δ : ℝ) : ℝ := 2 * D1 * δ * ui + J * δ ^ 2 - δ * lgre0 S ui
/-- Constant term of `W`. -/
noncomputable def lgrWm (S ui J D1 δ : ℝ) : ℝ :=
  S ^ 2 * (S ^ 2 - S + 1) + D1 ^ 2 * ui + 2 * J * D1 * δ - D1 * lgre0 S ui - S ^ 3 * J * δ
/-- Residue of `W` at `η = 0`. -/
noncomputable def lgrWr (S J D1 : ℝ) : ℝ := J * D1 * (D1 - S ^ 3)
/-- Coefficient of `η` in `L`. -/
noncomputable def lgrLl (ui δ : ℝ) : ℝ := 2 * δ * ui
/-- Constant term of `L`. -/
noncomputable def lgrLm (S ui J D1 δ : ℝ) : ℝ := 2 * D1 * ui + 2 * J * δ - lgre0 S ui
/-- Residue of `L` at `η = 0`. -/
noncomputable def lgrLr (S J D1 : ℝ) : ℝ := J * (2 * D1 - S ^ 3)

theorem lgr_W_pf {S ui J D1 δ η : ℝ} (hη : η ≠ 0) :
    lgrWn S (ui + J / η) (D1 + δ * η) = lgrWk ui δ * η ^ 2 + lgrWl S ui J D1 δ * η +
      lgrWm S ui J D1 δ + lgrWr S J D1 / η := by
  unfold lgrWn lgrWk lgrWl lgrWm lgrWr lgre0
  field_simp
  ring

theorem lgr_L_pf {S ui J D1 δ η : ℝ} (hη : η ≠ 0) :
    lgrLn S (ui + J / η) (D1 + δ * η) = lgrLl ui δ * η + lgrLm S ui J D1 δ + lgrLr S J D1 / η := by
  unfold lgrLn lgrLl lgrLm lgrLr lgre0
  field_simp
  ring

/-- **The `τ = 2` test in partial fractions** in `η = β - 1`. -/
theorem lgr_pf_two {S K a c ui J D1 δ η : ℝ} (hK : K ≠ 0) (ha : a ≠ 0) (hη : η ≠ 0)
    (hB : c + η ≠ 0) :
    lgrGc S K a (c + η) (ui + J / η) (D1 + δ * η) 2 (5 * a * (c + η) / (2 * K) - 11 / 9) =
      (5 / 2 * lgrWk ui δ / K ^ 2) * η ^ 2 +
      (5 / 2 * lgrWl S ui J D1 δ / K ^ 2 + (ui - 1) / a - lgrLl ui δ / K + 5 * a / (2 * K)) * η +
      (5 / 2 * lgrWm S ui J D1 δ / K ^ 2 + ((ui - 1) * c + J) / a - lgrLm S ui J D1 δ / K +
        5 * a * c / (2 * K) - a ^ 2 / K - 151 / 72) +
      (5 / 2 * lgrWr S J D1 / K ^ 2 + J * c / a - lgrLr S J D1 / K) / (η - 0) +
      a / (η - -c) := by
  unfold lgrGc
  rw [lgr_W_pf hη, lgr_L_pf hη]
  have hB' : η - -c ≠ 0 := by rw [sub_neg_eq_add, add_comm]; exact hB
  rw [sub_zero]
  field_simp
  ring

/-- `Q = W_k c² - W_l c + W_m - K² - W_r/c`: `Q/K² = w - 1` continued to `β = -α`. -/
noncomputable def lgrQd (S K ui J D1 δ c : ℝ) : ℝ :=
  lgrWk ui δ * c ^ 2 - lgrWl S ui J D1 δ * c + lgrWm S ui J D1 δ - K ^ 2 - lgrWr S J D1 / c

/-- **The duration tests in partial fractions** in `η = β - 1`, `τ = γK/(αB)`. -/
theorem lgr_pf_dur {S K a c ui J D1 δ η γ ℓ : ℝ} (hK : K ≠ 0) (ha : a ≠ 0) (hc : c ≠ 0)
    (hγ : γ ≠ 0) (hη : η ≠ 0) (hB : c + η ≠ 0) :
    lgrGc S K a (c + η) (ui + J / η) (D1 + δ * η) (γ * K / (a * (c + η))) ℓ =
      (lgrWk ui δ / (2 * K ^ 2)) * η ^ 2 +
      (γ * lgrWk ui δ / (a * K) + a / (γ * K) + (ui - 1) / a - lgrLl ui δ / K +
        lgrWl S ui J D1 δ / (2 * K ^ 2)) * η +
      (γ * (lgrWl S ui J D1 δ - lgrWk ui δ * c) / (a * K) + a * c / (γ * K) + ((ui - 1) * c + J) / a +
        1 - a ^ 2 / K - lgrLm S ui J D1 δ / K + ℓ + lgrWm S ui J D1 δ / (2 * K ^ 2) - 3 / 8) +
      (γ * lgrWr S J D1 / (a * c * K) + J * c / a - lgrLr S J D1 / K +
        lgrWr S J D1 / (2 * K ^ 2)) / (η - 0) +
      (γ * lgrQd S K ui J D1 δ c / (a * K) + a) / (η - -c) := by
  unfold lgrGc lgrQd
  rw [lgr_W_pf hη, lgr_L_pf hη]
  have hB' : η - -c ≠ 0 := by rw [sub_neg_eq_add, add_comm]; exact hB
  rw [sub_zero]
  field_simp
  ring


/-! ### Polynomial signs on the shape domain -/

/-- **The coefficient bound on the shape domain** `12/5 ≤ x ≤ 9`, `1 ≤ α ≤ (5x + 4)/12`, for a
bivariate list in `X = x - 12/5`, `A = α - 1`: on `α ≤ 7/6` and on `7/6 ≤ α ≤ 4/3` (every
coefficient of `X` bounded on the `A`-interval, then positive constant and nonnegative higher
coefficients), and on `α ≥ 4/3` in the coordinates `A' = α - 4/3 ≤ 11/4`, `Y = x - (12α - 4)/5 ≥ 0`. -/
theorem lgr_trap_pos (P : List (List ℝ)) (h1 : lgrPosL (P.map (lgrLow (1 / 6))))
    (h2 : lgrPosL ((P.map (lgrShift (1 / 6))).map (lgrLow (1 / 6))))
    (h3 : lgrPosL ((lgrShear (12 / 5) (P.map (lgrShift (1 / 3)))).map (lgrLow (11 / 4))))
    {x a : ℝ} (hx : 12 / 5 ≤ x) (hx9 : x ≤ 9) (ha : 1 ≤ a) (ha' : a ≤ (5 * x + 4) / 12) :
    0 < lgrH2 P (x - 12 / 5) (a - 1) := by
  rcases le_or_gt a (7 / 6) with h76 | h76
  · exact lgr_pos_unb (by linarith) (by linarith) (by linarith) P h1
  rcases le_or_gt a (4 / 3) with h43 | h43
  · have e : lgrH2 P (x - 12 / 5) (a - 1) =
        lgrH2 (P.map (lgrShift (1 / 6))) (x - 12 / 5) (a - 7 / 6) := by
      rw [lgr_H2_shift_inner]; congr 1; ring
    rw [e]
    exact lgr_pos_unb (by linarith) (by linarith) (by linarith) _ h2
  · have e : lgrH2 P (x - 12 / 5) (a - 1) =
        lgrH2 (lgrShear (12 / 5) (P.map (lgrShift (1 / 3)))) (x - (12 * a - 4) / 5) (a - 4 / 3) := by
      rw [lgr_H2_shear, lgr_H2_shift_inner]; congr 1 <;> ring
    rw [e]
    exact lgr_pos_unb (by linarith) (by linarith) (by linarith) _ h3

/-- The `τ = 2` residue polynomial `Φ₂ = 4SMK²α(k(x - 1)³ + r)/(x - 1)³`:
`30αSMh² + 10αh²(x - 1)² + 7((5/2)αc²(c² - S³) + cK² - αK(2c² - S³))`, `h = x - α`, `c = α + 1`
(the residue factor `A*` of `lgrr2`, cleared). -/
noncomputable def lgrPhi2f (x a : ℝ) : ℝ :=
  30 * a * (x + 1) * (35 * x + 13) * (x - a) ^ 2 + 10 * a * (x - a) ^ 2 * (x - 1) ^ 2 +
    7 * (5 / 2 * a * (a + 1) ^ 2 * ((a + 1) ^ 2 - (x + 1) ^ 3) +
      (a + 1) * (x ^ 2 + 2 * x + a ^ 2) ^ 2 - a * (x ^ 2 + 2 * x + a ^ 2) * (2 * (a + 1) ^ 2 - (x + 1) ^ 3))

/-- `Φ₂` on coefficient lists (computed from the formula, never printed). -/
noncomputable def lgrPhi2L (x a : List (List ℝ)) : List (List ℝ) :=
  let S := lgrAdd2 x [[1]]
  let M := lgrAdd2 (lgrSmul2 35 x) [[13]]
  let h := lgrAdd2 x (lgrSmul2 (-1) a)
  let c := lgrAdd2 a [[1]]
  let K := lgrAdd2 (lgrMul2 x x) (lgrAdd2 (lgrSmul2 2 x) (lgrMul2 a a))
  let xm := lgrAdd2 x [[-1]]
  let c2 := lgrMul2 c c
  let S3 := lgrMul2 (lgrMul2 S S) S
  lgrAdd2 (lgrSmul2 30 (lgrMul2 (lgrMul2 (lgrMul2 a S) M) (lgrMul2 h h)))
    (lgrAdd2 (lgrSmul2 10 (lgrMul2 (lgrMul2 a (lgrMul2 h h)) (lgrMul2 xm xm)))
      (lgrSmul2 7 (lgrAdd2 (lgrSmul2 (5 / 2) (lgrMul2 (lgrMul2 a c2) (lgrAdd2 c2 (lgrSmul2 (-1) S3))))
        (lgrAdd2 (lgrMul2 c (lgrMul2 K K))
          (lgrSmul2 (-1) (lgrMul2 (lgrMul2 a K) (lgrAdd2 (lgrSmul2 2 c2) (lgrSmul2 (-1) S3))))))))

theorem lgr_H2_Phi2L (x a : List (List ℝ)) (X A : ℝ) :
    lgrH2 (lgrPhi2L x a) X A = lgrPhi2f (lgrH2 x X A) (lgrH2 a X A) := by
  unfold lgrPhi2L lgrPhi2f
  simp only [lgr_H2_add2, lgr_H2_mul2, lgr_H2_smul2, lgr_H2_single, polyHorner]
  ring

theorem lgr_H2_base (l : ℝ) (x a : ℝ) :
    lgrH2 [[l], [1]] (x - l) (a - 1) = x ∧ lgrH2 [[1, 1]] (x - l) (a - 1) = a := by
  constructor <;> simp [lgrH2, polyHorner]

theorem lgr_Phi2_pos {x a : ℝ} (hx : 12 / 5 ≤ x) (hx9 : x ≤ 9) (ha : 1 ≤ a)
    (ha' : a ≤ (5 * x + 4) / 12) : 0 < lgrPhi2f x a := by
  obtain ⟨e1, e2⟩ := lgr_H2_base (12 / 5) x a
  have e := lgr_H2_Phi2L [[12 / 5], [1]] [[1, 1]] (x - 12 / 5) (a - 1)
  rw [e1, e2] at e
  rw [← e]
  apply lgr_trap_pos _ _ _ _ hx hx9 ha ha' <;>
    norm_num [lgrPhi2L, lgrMul2, lgrMul, lgrSmul2, lgrPosL, lgrLow, lgrNeg, lgrShift, lgrShear,
      lgrAdd, lgrAdd2, lgrSmul]

/-! ### Beta convexity of the `τ = 2` test -/

/-- The `τ = 2` test at `q = q_c`, `u = û(x, β)` as a function of `(x, α, β)`. -/
noncomputable def lgrG2 (x a b : ℝ) : ℝ :=
  ssF x b a (ssUhat x b) (ssQc x a) 2 (5 / (2 * (ssRA a b / ssQc x a)) - 11 / 9) (1 / 2)

/-- `k₂ = (5/2)δ²u_∞/K²`. -/
noncomputable def lgrk2 (x a : ℝ) : ℝ :=
  5 / 2 * lgrWk (lgrui x) (2 * (a - x)) / (x ^ 2 + 2 * x + a ^ 2) ^ 2
/-- The `η`-coefficient `l₂`. -/
noncomputable def lgrl2 (x a : ℝ) : ℝ :=
  5 / 2 * lgrWl (x + 1) (lgrui x) (lgrJ x) ((a + 1) ^ 2) (2 * (a - x)) / (x ^ 2 + 2 * x + a ^ 2) ^ 2 +
    (lgrui x - 1) / a - lgrLl (lgrui x) (2 * (a - x)) / (x ^ 2 + 2 * x + a ^ 2) +
    5 * a / (2 * (x ^ 2 + 2 * x + a ^ 2))
/-- The constant term `m₂`. -/
noncomputable def lgrm2 (x a : ℝ) : ℝ :=
  5 / 2 * lgrWm (x + 1) (lgrui x) (lgrJ x) ((a + 1) ^ 2) (2 * (a - x)) / (x ^ 2 + 2 * x + a ^ 2) ^ 2 +
    ((lgrui x - 1) * (a + 1) + lgrJ x) / a -
    lgrLm (x + 1) (lgrui x) (lgrJ x) ((a + 1) ^ 2) (2 * (a - x)) / (x ^ 2 + 2 * x + a ^ 2) +
    5 * a * (a + 1) / (2 * (x ^ 2 + 2 * x + a ^ 2)) - a ^ 2 / (x ^ 2 + 2 * x + a ^ 2) - 151 / 72
/-- The residue `r₂ = J·A*` at `β = 1` (this defines the factor `A*`). -/
noncomputable def lgrr2 (x a : ℝ) : ℝ :=
  5 / 2 * lgrWr (x + 1) (lgrJ x) ((a + 1) ^ 2) / (x ^ 2 + 2 * x + a ^ 2) ^ 2 +
    lgrJ x * (a + 1) / a - lgrLr (x + 1) (lgrJ x) ((a + 1) ^ 2) / (x ^ 2 + 2 * x + a ^ 2)

theorem lgr_G2_pf {x a b : ℝ} (hx : 1 < x) (ha : 0 < a) (hb : 1 < b) :
    lgrG2 x a b = lgrk2 x a * (b - 1) ^ 2 + lgrl2 x a * (b - 1) + lgrm2 x a +
      lgrr2 x a / ((b - 1) - 0) + a / ((b - 1) - -(a + 1)) := by
  have hx0 : 0 < x := by linarith
  have hB : 0 < a + b := by linarith
  have hK : 0 < x ^ 2 + 2 * x + a ^ 2 := by positivity
  have e : lgrG2 x a b = lgrGc (x + 1) (x ^ 2 + 2 * x + a ^ 2) a ((a + 1) + (b - 1))
      (lgrui x + lgrJ x / (b - 1)) ((a + 1) ^ 2 + 2 * (a - x) * (b - 1)) 2
      (5 * a * ((a + 1) + (b - 1)) / (2 * (x ^ 2 + 2 * x + a ^ 2)) - 11 / 9) := by
    unfold lgrG2
    rw [lgr_cen_F hx0 ha hB, lgr_T_c hx0 ha hB, lgr_uhat_pole hx hb, lgr_Dg_pole]
    have e1 : (a + 1) + (b - 1) = a + b := by ring
    rw [e1]
    congr 1
    field_simp
  rw [e, lgr_pf_two hK.ne' ha.ne' (by linarith : b - 1 ≠ 0) (by linarith)]
  unfold lgrk2 lgrl2 lgrm2 lgrr2
  ring

theorem lgr_two_res {x a : ℝ} (hx : 12 / 5 ≤ x) (hx9 : x ≤ 9) (ha : 1 ≤ a)
    (ha' : a ≤ (5 * x + 4) / 12) : 0 ≤ lgrk2 x a * (x - 1 - 0) ^ 3 + lgrr2 x a := by
  have hx1 : 0 < x - 1 := by linarith
  have ha0 : 0 < a := by linarith
  have hK : 0 < x ^ 2 + 2 * x + a ^ 2 := by positivity
  have e : lgrk2 x a * (x - 1 - 0) ^ 3 + lgrr2 x a = (x - 1) ^ 3 * lgrPhi2f x a /
        (4 * (x + 1) * (35 * x + 13) * (x ^ 2 + 2 * x + a ^ 2) ^ 2 * a) := by
    unfold lgrk2 lgrr2 lgrWk lgrWr lgrLr lgrui lgrJ lgrPhi2f
    field_simp
    ring
  rw [e]
  have := lgr_Phi2_pos hx hx9 ha ha'
  positivity

/-- **Beta convexity of the `τ = 2` test**: on `x ≤ β ≤ β₁` the test is at most
the larger of its values at `β = x` and `β = β₁`. -/
theorem lgr_cen_two_chord {x a b b₁ : ℝ} (hx : 12 / 5 ≤ x) (hx9 : x ≤ 9) (ha : 1 ≤ a)
    (ha' : a ≤ (5 * x + 4) / 12) (hxb : x ≤ b) (hbb : b ≤ b₁) :
    lgrG2 x a b ≤ max (lgrG2 x a x) (lgrG2 x a b₁) := by
  have hx1 : 1 < x := by linarith
  have ha0 : 0 < a := by linarith
  rw [lgr_G2_pf hx1 ha0 (by linarith), lgr_G2_pf hx1 ha0 hx1, lgr_G2_pf hx1 ha0 (by linarith)]
  apply lgr_chord (by linarith) (by linarith) (by linarith) (by linarith)
  · unfold lgrk2 lgrWk lgrui; positivity
  · exact lgr_two_res hx hx9 ha ha'
  · exact ha0.le

/-! ### Beta convexity of the duration tests -/

/-- The duration test `τ = T` (`γ = 1`) at `q = q_c`, `u = û(x, β)`. -/
noncomputable def lgrGT (x a b : ℝ) : ℝ :=
  ssF x b a (ssUhat x b) (ssQc x a) (ssRA a b / ssQc x a) 0 (1 / 2)

/-- The duration test `τ = 8T/9` (`γ = 8/9`) at `q = q_c`, `u = û(x, β)`. -/
noncomputable def lgrG8 (x a b : ℝ) : ℝ :=
  ssF x b a (ssUhat x b) (ssQc x a) (8 * (ssRA a b / ssQc x a) / 9) (-1 / 9) (1 / 2)

/-- `k_d = δ²u_∞/(2K²)`. -/
noncomputable def lgrkd (x a : ℝ) : ℝ := lgrWk (lgrui x) (2 * (a - x)) / (2 * (x ^ 2 + 2 * x + a ^ 2) ^ 2)
/-- The `η`-coefficient `l_d`. -/
noncomputable def lgrld (x a γ : ℝ) : ℝ :=
  γ * lgrWk (lgrui x) (2 * (a - x)) / (a * (x ^ 2 + 2 * x + a ^ 2)) + a / (γ * (x ^ 2 + 2 * x + a ^ 2)) +
    (lgrui x - 1) / a - lgrLl (lgrui x) (2 * (a - x)) / (x ^ 2 + 2 * x + a ^ 2) +
    lgrWl (x + 1) (lgrui x) (lgrJ x) ((a + 1) ^ 2) (2 * (a - x)) / (2 * (x ^ 2 + 2 * x + a ^ 2) ^ 2)
/-- The constant term `m_d`. -/
noncomputable def lgrmd (x a γ ℓ : ℝ) : ℝ :=
  γ * (lgrWl (x + 1) (lgrui x) (lgrJ x) ((a + 1) ^ 2) (2 * (a - x)) -
      lgrWk (lgrui x) (2 * (a - x)) * (a + 1)) / (a * (x ^ 2 + 2 * x + a ^ 2)) +
    a * (a + 1) / (γ * (x ^ 2 + 2 * x + a ^ 2)) + ((lgrui x - 1) * (a + 1) + lgrJ x) / a + 1 -
    a ^ 2 / (x ^ 2 + 2 * x + a ^ 2) -
    lgrLm (x + 1) (lgrui x) (lgrJ x) ((a + 1) ^ 2) (2 * (a - x)) / (x ^ 2 + 2 * x + a ^ 2) + ℓ +
    lgrWm (x + 1) (lgrui x) (lgrJ x) ((a + 1) ^ 2) (2 * (a - x)) / (2 * (x ^ 2 + 2 * x + a ^ 2) ^ 2) -
    3 / 8
/-- The residue `r_d = J·A_γ` at `β = 1`. -/
noncomputable def lgrrd (x a γ : ℝ) : ℝ :=
  γ * lgrWr (x + 1) (lgrJ x) ((a + 1) ^ 2) / (a * (a + 1) * (x ^ 2 + 2 * x + a ^ 2)) +
    lgrJ x * (a + 1) / a - lgrLr (x + 1) (lgrJ x) ((a + 1) ^ 2) / (x ^ 2 + 2 * x + a ^ 2) +
    lgrWr (x + 1) (lgrJ x) ((a + 1) ^ 2) / (2 * (x ^ 2 + 2 * x + a ^ 2) ^ 2)
/-- `Q` of the duration tests at the actual coefficients. -/
noncomputable def lgrQx (x a : ℝ) : ℝ :=
  lgrQd (x + 1) (x ^ 2 + 2 * x + a ^ 2) (lgrui x) (lgrJ x) ((a + 1) ^ 2) (2 * (a - x)) (a + 1)
/-- The residue `s_d = (γK/α)(w_N - 1) + α` at `β = -α`. -/
noncomputable def lgrsd (x a γ : ℝ) : ℝ := γ * lgrQx x a / (a * (x ^ 2 + 2 * x + a ^ 2)) + a

theorem lgr_Gd_pf {x a b γ ℓ : ℝ} (hx : 1 < x) (ha : 0 < a) (hb : 1 < b) (hγ : 0 < γ) :
    ssF x b a (ssUhat x b) (ssQc x a) (γ * (ssRA a b / ssQc x a)) ℓ (1 / 2) =
      lgrkd x a * (b - 1) ^ 2 + lgrld x a γ * (b - 1) + lgrmd x a γ ℓ +
      lgrrd x a γ / ((b - 1) - 0) + lgrsd x a γ / ((b - 1) - -(a + 1)) := by
  have hx0 : 0 < x := by linarith
  have hB : 0 < a + b := by linarith
  have hK : 0 < x ^ 2 + 2 * x + a ^ 2 := by positivity
  have e : ssF x b a (ssUhat x b) (ssQc x a) (γ * (ssRA a b / ssQc x a)) ℓ (1 / 2) =
      lgrGc (x + 1) (x ^ 2 + 2 * x + a ^ 2) a ((a + 1) + (b - 1))
      (lgrui x + lgrJ x / (b - 1)) ((a + 1) ^ 2 + 2 * (a - x) * (b - 1))
      (γ * (x ^ 2 + 2 * x + a ^ 2) / (a * ((a + 1) + (b - 1)))) ℓ := by
    rw [lgr_cen_F hx0 ha hB, lgr_T_c hx0 ha hB, lgr_uhat_pole hx hb, lgr_Dg_pole]
    have e1 : (a + 1) + (b - 1) = a + b := by ring
    rw [e1, mul_div_assoc]
  rw [e, lgr_pf_dur hK.ne' ha.ne' (by linarith) hγ.ne' (by linarith : b - 1 ≠ 0) (by linarith)]
  unfold lgrkd lgrld lgrmd lgrrd lgrsd lgrQx
  ring

theorem lgr_GT_pf {x a b : ℝ} (hx : 1 < x) (ha : 0 < a) (hb : 1 < b) :
    lgrGT x a b = lgrkd x a * (b - 1) ^ 2 + lgrld x a 1 * (b - 1) + lgrmd x a 1 0 +
      lgrrd x a 1 / ((b - 1) - 0) + lgrsd x a 1 / ((b - 1) - -(a + 1)) := by
  rw [← lgr_Gd_pf hx ha hb one_pos, one_mul]; rfl

theorem lgr_G8_pf {x a b : ℝ} (hx : 1 < x) (ha : 0 < a) (hb : 1 < b) :
    lgrG8 x a b = lgrkd x a * (b - 1) ^ 2 + lgrld x a (8 / 9) * (b - 1) + lgrmd x a (8 / 9) (-1 / 9) +
      lgrrd x a (8 / 9) / ((b - 1) - 0) + lgrsd x a (8 / 9) / ((b - 1) - -(a + 1)) := by
  rw [← lgr_Gd_pf hx ha hb (by norm_num)]
  unfold lgrG8
  congr 1
  ring

/-- `4SM(Q + α²K)` cleared: with `U_I = 3SM + (x - 1)² = 4SMu_∞`,
`J_J = 7(x - 1)³ = 4SMJ`, `E₀' = S³(U_I - 4SM) + 4SM(3S - 1)`, `c = α + 1`, `δ = 2(α - x)`. -/
noncomputable def lgrQnf (x a : ℝ) : ℝ :=
  let S := x + 1
  let F4 := 4 * (x + 1) * (35 * x + 13)
  let UI := 3 * (x + 1) * (35 * x + 13) + (x - 1) ^ 2
  let JJ := 7 * (x - 1) ^ 3
  let c := a + 1
  let δ := 2 * (a - x)
  let K := x ^ 2 + 2 * x + a ^ 2
  let E0 := S ^ 3 * (UI - F4) + F4 * (3 * S - 1)
  UI * δ ^ 2 * c ^ 2 - c * (2 * c ^ 2 * δ * UI + JJ * δ ^ 2 - δ * E0) +
    (F4 * (S ^ 2 * (S ^ 2 - S + 1)) + (c ^ 2) ^ 2 * UI + 2 * JJ * c ^ 2 * δ - c ^ 2 * E0 -
      S ^ 3 * JJ * δ) - F4 * K ^ 2 - JJ * c * (c ^ 2 - S ^ 3) + F4 * a ^ 2 * K

/-- `lgrQnf` on coefficient lists. -/
noncomputable def lgrQnL (x a : List (List ℝ)) : List (List ℝ) :=
  let S := lgrAdd2 x [[1]]
  let SM := lgrMul2 S (lgrAdd2 (lgrSmul2 35 x) [[13]])
  let F4 := lgrSmul2 4 SM
  let xm := lgrAdd2 x [[-1]]
  let UI := lgrAdd2 (lgrSmul2 3 SM) (lgrMul2 xm xm)
  let JJ := lgrSmul2 7 (lgrMul2 (lgrMul2 xm xm) xm)
  let c := lgrAdd2 a [[1]]
  let c2 := lgrMul2 c c
  let δ := lgrSmul2 2 (lgrAdd2 a (lgrSmul2 (-1) x))
  let δ2 := lgrMul2 δ δ
  let K := lgrAdd2 (lgrMul2 x x) (lgrAdd2 (lgrSmul2 2 x) (lgrMul2 a a))
  let S2 := lgrMul2 S S
  let S3 := lgrMul2 S2 S
  let E0 := lgrAdd2 (lgrMul2 S3 (lgrAdd2 UI (lgrSmul2 (-1) F4)))
    (lgrMul2 F4 (lgrAdd2 (lgrSmul2 3 S) [[-1]]))
  lgrAdd2 (lgrMul2 (lgrMul2 UI δ2) c2)
    (lgrAdd2 (lgrSmul2 (-1) (lgrMul2 c (lgrAdd2 (lgrSmul2 2 (lgrMul2 (lgrMul2 c2 δ) UI))
      (lgrAdd2 (lgrMul2 JJ δ2) (lgrSmul2 (-1) (lgrMul2 δ E0))))))
    (lgrAdd2 (lgrAdd2 (lgrMul2 F4 (lgrMul2 S2 (lgrAdd2 S2 (lgrAdd2 (lgrSmul2 (-1) S) [[1]]))))
      (lgrAdd2 (lgrMul2 (lgrMul2 c2 c2) UI) (lgrAdd2 (lgrSmul2 2 (lgrMul2 (lgrMul2 JJ c2) δ))
        (lgrAdd2 (lgrSmul2 (-1) (lgrMul2 c2 E0)) (lgrSmul2 (-1) (lgrMul2 (lgrMul2 S3 JJ) δ))))))
    (lgrAdd2 (lgrSmul2 (-1) (lgrMul2 F4 (lgrMul2 K K)))
      (lgrAdd2 (lgrSmul2 (-1) (lgrMul2 (lgrMul2 JJ c) (lgrAdd2 c2 (lgrSmul2 (-1) S3))))
        (lgrMul2 (lgrMul2 F4 (lgrMul2 a a)) K)))))

theorem lgr_H2_QnL (x a : List (List ℝ)) (X A : ℝ) :
    lgrH2 (lgrQnL x a) X A = lgrQnf (lgrH2 x X A) (lgrH2 a X A) := by
  unfold lgrQnL lgrQnf
  simp only [lgr_H2_add2, lgr_H2_mul2, lgr_H2_smul2, lgr_H2_single, polyHorner]
  ring

/-- **The residue at `β = -α` is nonnegative** for `0 < γ ≤ 1`. -/
theorem lgr_dur_s {x a γ : ℝ} (hx : 12 / 5 ≤ x) (hx9 : x ≤ 9) (ha : 1 ≤ a)
    (ha' : a ≤ (5 * x + 4) / 12) (hγ : 0 < γ) (hγ1 : γ ≤ 1) : 0 ≤ lgrsd x a γ := by
  have ha0 : 0 < a := by linarith
  have hK : 0 < x ^ 2 + 2 * x + a ^ 2 := by positivity
  have hQ : lgrQx x a + a ^ 2 * (x ^ 2 + 2 * x + a ^ 2) =
      lgrQnf x a / (4 * (x + 1) * (35 * x + 13)) := by
    unfold lgrQx lgrQd lgrWk lgrWl lgrWm lgrWr lgre0 lgrui lgrJ lgrQnf
    field_simp
    ring
  have hpos : 0 < lgrQnf x a := by
    obtain ⟨e1, e2⟩ := lgr_H2_base (12 / 5) x a
    have e := lgr_H2_QnL [[12 / 5], [1]] [[1, 1]] (x - 12 / 5) (a - 1)
    rw [e1, e2] at e
    rw [← e]
    apply lgr_trap_pos _ _ _ _ hx hx9 ha ha' <;>
      norm_num [lgrQnL, lgrMul2, lgrMul, lgrSmul2, lgrPosL, lgrLow, lgrNeg, lgrShift, lgrShear,
        lgrAdd, lgrAdd2, lgrSmul]
  have hQ0 : 0 ≤ lgrQx x a + a ^ 2 * (x ^ 2 + 2 * x + a ^ 2) := by
    rw [hQ]; have : 0 < (x + 1) * (35 * x + 13) := by nlinarith
    positivity
  unfold lgrsd
  have e : γ * lgrQx x a / (a * (x ^ 2 + 2 * x + a ^ 2)) + a =
      (γ * (lgrQx x a + a ^ 2 * (x ^ 2 + 2 * x + a ^ 2)) + (1 - γ) * a ^ 2 * (x ^ 2 + 2 * x + a ^ 2)) /
        (a * (x ^ 2 + 2 * x + a ^ 2)) := by
    field_simp; ring
  rw [e]
  have : 0 ≤ 1 - γ := by linarith
  positivity

/-- **Convexity at `β = 1`**: `k_d(x - 1)³ + r_d ≥ 0` for `0 < γ ≤ 1`,
from `K ≤ (25/2)αh`, `S(α + 1)² ≤ (45/2)h²` and `M ≥ 28S` (`h = x - α`). -/
theorem lgr_dur_res {x a γ : ℝ} (hx : 12 / 5 ≤ x) (hx9 : x ≤ 9) (ha : 1 ≤ a)
    (ha' : a ≤ (5 * x + 4) / 12) (hγ1 : γ ≤ 1) :
    0 ≤ lgrkd x a * (x - 1 - 0) ^ 3 + lgrrd x a γ := by
  have hx1 : 0 < x - 1 := by linarith
  have ha0 : 0 < a := by linarith
  have hK : 0 < x ^ 2 + 2 * x + a ^ 2 := by positivity
  have ha59 : a ≤ 5 * x / 9 := by linarith
  have hh : 4 * x / 9 ≤ x - a := by linarith
  have hh0 : 0 < x - a := by linarith
  -- `2K ≤ 25αh`
  have hB1 : 2 * (x ^ 2 + 2 * x + a ^ 2) ≤ 25 * a * (x - a) := by
    nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ a - 1) (by linarith : (0 : ℝ) ≤ 5 * x / 9 - a),
      mul_nonneg (by linarith : (0 : ℝ) ≤ 2 * x - 3) (by linarith : (0 : ℝ) ≤ 9 - x),
      mul_nonneg (mul_nonneg (by linarith : (0 : ℝ) ≤ a - 1) (by linarith : (0 : ℝ) ≤ 5 * x / 9 - a))
        (by linarith : (0 : ℝ) ≤ 5 * x / 9 - 1),
      mul_nonneg (by linarith : (0 : ℝ) ≤ 5 * x / 9 - a)
        (mul_nonneg (by linarith : (0 : ℝ) ≤ 2 * x - 3) (by linarith : (0 : ℝ) ≤ 9 - x)),
      mul_nonneg (by linarith : (0 : ℝ) ≤ a - 1) (by nlinarith : (0 : ℝ) ≤ 32 / 9 * x ^ 2 - 4 * x)]
  -- `S(α + 1)² ≤ (45/2)h²`
  have hB2 : 2 * (x + 1) * (a + 1) ^ 2 ≤ 45 * (x - a) ^ 2 := by
    have h1 : (a + 1) ^ 2 ≤ (5 * x / 9 + 1) ^ 2 := by nlinarith
    have h2 : (4 * x / 9) ^ 2 ≤ (x - a) ^ 2 := by nlinarith
    have h3 : (x + 1) * (5 * x + 9) ^ 2 ≤ 360 * x ^ 2 := by
      nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ 9 - x) (by nlinarith : (0 : ℝ) ≤ 25 * x ^ 2 - 20 * x - 9)]
    have h4 : 2 * (x + 1) * (a + 1) ^ 2 ≤ 2 * (x + 1) * (5 * x / 9 + 1) ^ 2 :=
      mul_le_mul_of_nonneg_left h1 (by linarith)
    nlinarith
  -- the residue polynomial
  set S := x + 1
  set M := 35 * x + 13
  set K := x ^ 2 + 2 * x + a ^ 2
  set h := x - a
  have hM : 28 * S ≤ M := by simp only [S, M]; linarith
  have hS : 0 < S := by simp only [S]; linarith
  have hcS : (a + 1) ^ 2 ≤ S ^ 3 := by
    have : a + 1 ≤ S := by simp only [S]; linarith
    nlinarith
  have hPhi1 : 0 ≤ 6 * a * S * M * h ^ 2 - 7 * K * S ^ 2 * h - 7 / 2 * a * (a + 1) ^ 2 * S ^ 3 := by
    have e1 : 168 * a * S ^ 2 * h ^ 2 ≤ 6 * a * S * M * h ^ 2 := by
      calc 168 * a * S ^ 2 * h ^ 2 = (6 * a * S * h ^ 2) * (28 * S) := by ring
        _ ≤ (6 * a * S * h ^ 2) * M := mul_le_mul_of_nonneg_left hM (by positivity)
        _ = 6 * a * S * M * h ^ 2 := by ring
    have e2 : 7 * K * S ^ 2 * h ≤ 175 / 2 * a * S ^ 2 * h ^ 2 := by
      calc 7 * K * S ^ 2 * h = (7 / 2 * S ^ 2 * h) * (2 * K) := by ring
        _ ≤ (7 / 2 * S ^ 2 * h) * (25 * a * h) := mul_le_mul_of_nonneg_left hB1 (by positivity)
        _ = 175 / 2 * a * S ^ 2 * h ^ 2 := by ring
    have e3 : 7 / 2 * a * (a + 1) ^ 2 * S ^ 3 ≤ 315 / 4 * a * S ^ 2 * h ^ 2 := by
      calc 7 / 2 * a * (a + 1) ^ 2 * S ^ 3 = (7 / 4 * a * S ^ 2) * (2 * S * (a + 1) ^ 2) := by ring
        _ ≤ (7 / 4 * a * S ^ 2) * (45 * h ^ 2) := mul_le_mul_of_nonneg_left hB2 (by positivity)
        _ = 315 / 4 * a * S ^ 2 * h ^ 2 := by ring
    have : 0 ≤ a * S ^ 2 * h ^ 2 := by positivity
    linarith
  have hPhi : 0 ≤ 6 * a * S * M * h ^ 2 + 2 * a * h ^ 2 * (x - 1) ^ 2 + 7 * (γ * (a + 1) * K *
      ((a + 1) ^ 2 - S ^ 3) + (a + 1) * K ^ 2 - a * K * (2 * (a + 1) ^ 2 - S ^ 3) +
      a * (a + 1) ^ 2 * ((a + 1) ^ 2 - S ^ 3) / 2) := by
    have e : 6 * a * S * M * h ^ 2 + 2 * a * h ^ 2 * (x - 1) ^ 2 + 7 * (γ * (a + 1) * K *
        ((a + 1) ^ 2 - S ^ 3) + (a + 1) * K ^ 2 - a * K * (2 * (a + 1) ^ 2 - S ^ 3) +
        a * (a + 1) ^ 2 * ((a + 1) ^ 2 - S ^ 3) / 2) =
        (6 * a * S * M * h ^ 2 - 7 * K * S ^ 2 * h - 7 / 2 * a * (a + 1) ^ 2 * S ^ 3) +
        2 * a * h ^ 2 * (x - 1) ^ 2 + 7 / 2 * a * (a + 1) ^ 4 +
        7 * (1 - γ) * (a + 1) * K * (S ^ 3 - (a + 1) ^ 2) := by
      simp only [S, K, h]; ring
    rw [e]
    have : 0 ≤ 1 - γ := by linarith
    have : 0 ≤ S ^ 3 - (a + 1) ^ 2 := by linarith
    positivity
  have e : lgrkd x a * (x - 1 - 0) ^ 3 + lgrrd x a γ = (x - 1) ^ 3 *
      (6 * a * S * M * h ^ 2 + 2 * a * h ^ 2 * (x - 1) ^ 2 + 7 * (γ * (a + 1) * K *
      ((a + 1) ^ 2 - S ^ 3) + (a + 1) * K ^ 2 - a * K * (2 * (a + 1) ^ 2 - S ^ 3) +
      a * (a + 1) ^ 2 * ((a + 1) ^ 2 - S ^ 3) / 2)) / (4 * S * M * K ^ 2 * a) := by
    have hM0 : 0 < M := by linarith
    unfold lgrkd lgrrd lgrWk lgrWr lgrLr lgrui lgrJ
    simp only [S, M, K, h] at hM0 hS ⊢
    field_simp
    ring
  rw [e]
  have hM0 : 0 < M := by linarith
  positivity

/-- **Beta convexity of the duration tests**: for `0 < γ ≤ 1`, the test
`τ = γT` is at most the larger of its values at `β = x` and `β = β₁`. -/
theorem lgr_cen_dur_chord {x a b b₁ γ ℓ : ℝ} (hx : 12 / 5 ≤ x) (hx9 : x ≤ 9) (ha : 1 ≤ a)
    (ha' : a ≤ (5 * x + 4) / 12) (hxb : x ≤ b) (hbb : b ≤ b₁) (hγ : 0 < γ) (hγ1 : γ ≤ 1) :
    lgrkd x a * (b - 1) ^ 2 + lgrld x a γ * (b - 1) + lgrmd x a γ ℓ +
        lgrrd x a γ / ((b - 1) - 0) + lgrsd x a γ / ((b - 1) - -(a + 1)) ≤
      max (lgrkd x a * (x - 1) ^ 2 + lgrld x a γ * (x - 1) + lgrmd x a γ ℓ +
        lgrrd x a γ / ((x - 1) - 0) + lgrsd x a γ / ((x - 1) - -(a + 1)))
      (lgrkd x a * (b₁ - 1) ^ 2 + lgrld x a γ * (b₁ - 1) + lgrmd x a γ ℓ +
        lgrrd x a γ / ((b₁ - 1) - 0) + lgrsd x a γ / ((b₁ - 1) - -(a + 1))) := by
  have ha0 : 0 < a := by linarith
  apply lgr_chord (by linarith) (by linarith) (by linarith) (by linarith)
  · unfold lgrkd lgrWk lgrui; positivity
  · exact lgr_dur_res hx hx9 ha ha' hγ1
  · exact lgr_dur_s hx hx9 ha ha' hγ hγ1

theorem lgr_cen_T_chord {x a b b₁ : ℝ} (hx : 12 / 5 ≤ x) (hx9 : x ≤ 9) (ha : 1 ≤ a)
    (ha' : a ≤ (5 * x + 4) / 12) (hxb : x ≤ b) (hbb : b ≤ b₁) :
    lgrGT x a b ≤ max (lgrGT x a x) (lgrGT x a b₁) := by
  have hx1 : 1 < x := by linarith
  have ha0 : 0 < a := by linarith
  rw [lgr_GT_pf hx1 ha0 (by linarith), lgr_GT_pf hx1 ha0 hx1, lgr_GT_pf hx1 ha0 (by linarith)]
  exact lgr_cen_dur_chord hx hx9 ha ha' hxb hbb one_pos le_rfl

theorem lgr_cen_8_chord {x a b b₁ : ℝ} (hx : 12 / 5 ≤ x) (hx9 : x ≤ 9) (ha : 1 ≤ a)
    (ha' : a ≤ (5 * x + 4) / 12) (hxb : x ≤ b) (hbb : b ≤ b₁) :
    lgrG8 x a b ≤ max (lgrG8 x a x) (lgrG8 x a b₁) := by
  have hx1 : 1 < x := by linarith
  have ha0 : 0 < a := by linarith
  rw [lgr_G8_pf hx1 ha0 (by linarith), lgr_G8_pf hx1 ha0 hx1, lgr_G8_pf hx1 ha0 (by linarith)]
  exact lgr_cen_dur_chord hx hx9 ha ha' hxb hbb (by norm_num) (by norm_num)

/-! ### The cleared numerators -/

/-- `W·V` for `u = U/V`: `S²(S² - S + 1)V + D²U - D E_N`, `E_N = S³(U - V) + (3S - 1)V`. -/
noncomputable def lgrWN (S U V D : ℝ) : ℝ :=
  S ^ 2 * (S ^ 2 - S + 1) * V + D ^ 2 * U - D * (S ^ 3 * (U - V) + (3 * S - 1) * V)

/-- `L·V` for `u = U/V`: `2DU - E_N`. -/
noncomputable def lgrLN (S U V D : ℝ) : ℝ := 2 * D * U - (S ^ 3 * (U - V) + (3 * S - 1) * V)

/-- The cleared `τ = 2` numerator: `G₂ = -N₂/(72αBK²V)`. -/
noncomputable def lgrN2 (S K a B U V D : ℝ) : ℝ :=
  72 * a * B * K * lgrLN S U V D - 180 * a * B * lgrWN S U V D - 72 * B ^ 2 * K ^ 2 * U +
    V * (72 * B ^ 2 * K ^ 2 - 180 * a ^ 2 * B ^ 2 * K + 151 * a * B * K ^ 2 + 72 * a ^ 3 * B * K -
      72 * a ^ 2 * K ^ 2)

/-- The cleared `τ = T` numerator: `G_T = -N_T/(8αBK²V)`. -/
noncomputable def lgrNT (S K a B U V D : ℝ) : ℝ :=
  8 * a * B * K * lgrLN S U V D - (4 * a * B + 8 * K) * lgrWN S U V D - 8 * B ^ 2 * K ^ 2 * U +
    V * (8 * B ^ 2 * K ^ 2 - 8 * a ^ 2 * B ^ 2 * K - 5 * a * B * K ^ 2 + 8 * a ^ 3 * B * K +
      8 * K ^ 3 - 8 * a ^ 2 * K ^ 2)

/-- The cleared `τ = 8T/9` numerator: `G₈ = -N₈/(72αBK²V)`. -/
noncomputable def lgrN8 (S K a B U V D : ℝ) : ℝ :=
  72 * a * B * K * lgrLN S U V D - (36 * a * B + 64 * K) * lgrWN S U V D - 72 * B ^ 2 * K ^ 2 * U +
    V * (72 * B ^ 2 * K ^ 2 - 81 * a ^ 2 * B ^ 2 * K - 37 * a * B * K ^ 2 + 72 * a ^ 3 * B * K +
      64 * K ^ 3 - 72 * a ^ 2 * K ^ 2)

theorem lgr_Gc_UV {S K a B U V D τ ℓ : ℝ} (hV : V ≠ 0) :
    lgrGc S K a B (U / V) D τ ℓ = (lgrWN S U V D / V / K ^ 2 - 1) * τ + 1 / τ + (U / V - 1) * B / a +
      a / B + 1 - a ^ 2 / K - lgrLN S U V D / V / K + ℓ + (lgrWN S U V D / V / K ^ 2 - 3 / 4) / 2 := by
  have hW : lgrWn S (U / V) D = lgrWN S U V D / V := by
    unfold lgrWn lgrWN; field_simp; ring
  have hL : lgrLn S (U / V) D = lgrLN S U V D / V := by
    unfold lgrLn lgrLN; field_simp; ring
  unfold lgrGc; rw [hW, hL]

theorem lgr_N2_eq {S K a B U V D : ℝ} (hK : K ≠ 0) (ha : a ≠ 0) (hB : B ≠ 0) (hV : V ≠ 0) :
    lgrGc S K a B (U / V) D 2 (5 * a * B / (2 * K) - 11 / 9) =
      -lgrN2 S K a B U V D / (72 * a * B * K ^ 2 * V) := by
  rw [lgr_Gc_UV hV]
  unfold lgrN2
  generalize lgrWN S U V D = W
  generalize lgrLN S U V D = L
  field_simp
  ring

theorem lgr_NT_eq {S K a B U V D : ℝ} (hK : K ≠ 0) (ha : a ≠ 0) (hB : B ≠ 0) (hV : V ≠ 0) :
    lgrGc S K a B (U / V) D (K / (a * B)) 0 = -lgrNT S K a B U V D / (8 * a * B * K ^ 2 * V) := by
  rw [lgr_Gc_UV hV]
  unfold lgrNT
  generalize lgrWN S U V D = W
  generalize lgrLN S U V D = L
  field_simp
  ring

theorem lgr_N8_eq {S K a B U V D : ℝ} (hK : K ≠ 0) (ha : a ≠ 0) (hB : B ≠ 0) (hV : V ≠ 0) :
    lgrGc S K a B (U / V) D (8 * (K / (a * B)) / 9) (-1 / 9) =
      -lgrN8 S K a B U V D / (72 * a * B * K ^ 2 * V) := by
  rw [lgr_Gc_UV hV]
  unfold lgrN8
  generalize lgrWN S U V D = W
  generalize lgrLN S U V D = L
  field_simp
  ring

/-- The three central tests are negative when their cleared numerators are positive. -/
theorem lgr_G2_neg {x a b : ℝ} (hx : 1 < x) (ha : 0 < a) (hb : 1 < b)
    (hN : 0 < lgrN2 (x + 1) (x ^ 2 + 2 * x + a ^ 2) a (a + b) (lgrUc x b) (lgrVc x b) (ssDg x b a)) :
    lgrG2 x a b < 0 := by
  have hx0 : 0 < x := by linarith
  have hB : 0 < a + b := by linarith
  have hK : 0 < x ^ 2 + 2 * x + a ^ 2 := by positivity
  have hb1 : 0 < b - 1 := by linarith
  have hV : 0 < lgrVc x b := by unfold lgrVc; positivity
  unfold lgrG2
  rw [lgr_cen_F hx0 ha hB, lgr_T_c hx0 ha hB, lgr_uhat_UV hx hb]
  have e : 5 / (2 * ((x ^ 2 + 2 * x + a ^ 2) / (a * (a + b)))) - 11 / 9 =
      5 * a * (a + b) / (2 * (x ^ 2 + 2 * x + a ^ 2)) - 11 / 9 := by field_simp
  rw [e, lgr_N2_eq hK.ne' ha.ne' hB.ne' hV.ne']
  apply div_neg_of_neg_of_pos (by linarith)
  positivity

theorem lgr_GT_neg {x a b : ℝ} (hx : 1 < x) (ha : 0 < a) (hb : 1 < b)
    (hN : 0 < lgrNT (x + 1) (x ^ 2 + 2 * x + a ^ 2) a (a + b) (lgrUc x b) (lgrVc x b) (ssDg x b a)) :
    lgrGT x a b < 0 := by
  have hx0 : 0 < x := by linarith
  have hB : 0 < a + b := by linarith
  have hK : 0 < x ^ 2 + 2 * x + a ^ 2 := by positivity
  have hb1 : 0 < b - 1 := by linarith
  have hV : 0 < lgrVc x b := by unfold lgrVc; positivity
  unfold lgrGT
  rw [lgr_cen_F hx0 ha hB, lgr_T_c hx0 ha hB, lgr_uhat_UV hx hb,
    lgr_NT_eq hK.ne' ha.ne' hB.ne' hV.ne']
  apply div_neg_of_neg_of_pos (by linarith)
  positivity

theorem lgr_G8_neg {x a b : ℝ} (hx : 1 < x) (ha : 0 < a) (hb : 1 < b)
    (hN : 0 < lgrN8 (x + 1) (x ^ 2 + 2 * x + a ^ 2) a (a + b) (lgrUc x b) (lgrVc x b) (ssDg x b a)) :
    lgrG8 x a b < 0 := by
  have hx0 : 0 < x := by linarith
  have hB : 0 < a + b := by linarith
  have hK : 0 < x ^ 2 + 2 * x + a ^ 2 := by positivity
  have hb1 : 0 < b - 1 := by linarith
  have hV : 0 < lgrVc x b := by unfold lgrVc; positivity
  unfold lgrG8
  rw [lgr_cen_F hx0 ha hB, lgr_T_c hx0 ha hB, lgr_uhat_UV hx hb,
    lgr_N8_eq hK.ne' ha.ne' hB.ne' hV.ne']
  apply div_neg_of_neg_of_pos (by linarith)
  positivity

/-! ### The cleared numerators on coefficient lists -/

/-- `lgrWN` on lists. -/
noncomputable def lgrWNL (S U V D : List (List ℝ)) : List (List ℝ) :=
  lgrAdd2 (lgrMul2 (lgrMul2 (lgrMul2 S S) (lgrAdd2 (lgrMul2 S S) (lgrAdd2 (lgrSmul2 (-1) S) [[1]]))) V)
    (lgrAdd2 (lgrMul2 (lgrMul2 D D) U)
      (lgrSmul2 (-1) (lgrMul2 D (lgrAdd2 (lgrMul2 (lgrMul2 (lgrMul2 S S) S) (lgrAdd2 U (lgrSmul2 (-1) V)))
        (lgrMul2 (lgrAdd2 (lgrSmul2 3 S) [[-1]]) V)))))

/-- `lgrLN` on lists. -/
noncomputable def lgrLNL (S U V D : List (List ℝ)) : List (List ℝ) :=
  lgrAdd2 (lgrSmul2 2 (lgrMul2 D U))
    (lgrSmul2 (-1) (lgrAdd2 (lgrMul2 (lgrMul2 (lgrMul2 S S) S) (lgrAdd2 U (lgrSmul2 (-1) V)))
      (lgrMul2 (lgrAdd2 (lgrSmul2 3 S) [[-1]]) V)))

theorem lgr_H2_WNL (S U V D : List (List ℝ)) (X A : ℝ) :
    lgrH2 (lgrWNL S U V D) X A =
      lgrWN (lgrH2 S X A) (lgrH2 U X A) (lgrH2 V X A) (lgrH2 D X A) := by
  unfold lgrWNL lgrWN
  simp only [lgr_H2_add2, lgr_H2_mul2, lgr_H2_smul2, lgr_H2_single, polyHorner]
  ring

theorem lgr_H2_LNL (S U V D : List (List ℝ)) (X A : ℝ) :
    lgrH2 (lgrLNL S U V D) X A =
      lgrLN (lgrH2 S X A) (lgrH2 U X A) (lgrH2 V X A) (lgrH2 D X A) := by
  unfold lgrLNL lgrLN
  simp only [lgr_H2_add2, lgr_H2_mul2, lgr_H2_smul2, lgr_H2_single, polyHorner]
  ring

/-- The `V`-bracket of a cleared numerator, `c₁B²K² + c₂α²B²K + c₃αBK² + c₄α³BK + c₅K³ + c₆α²K²`,
on lists. -/
noncomputable def lgrBrL (c₁ c₂ c₃ c₄ c₅ c₆ : ℝ) (K a B : List (List ℝ)) : List (List ℝ) :=
  let B2 := lgrMul2 B B
  let K2 := lgrMul2 K K
  let a2 := lgrMul2 a a
  lgrAdd2 (lgrSmul2 c₁ (lgrMul2 B2 K2)) (lgrAdd2 (lgrSmul2 c₂ (lgrMul2 (lgrMul2 a2 B2) K))
    (lgrAdd2 (lgrSmul2 c₃ (lgrMul2 (lgrMul2 a B) K2)) (lgrAdd2 (lgrSmul2 c₄ (lgrMul2 (lgrMul2 (lgrMul2 a2 a) B) K))
      (lgrAdd2 (lgrSmul2 c₅ (lgrMul2 K2 K)) (lgrSmul2 c₆ (lgrMul2 a2 K2))))))

/-- A cleared central numerator on lists:
`e₁αBK·L - (e₂αB + e₃K)W - e₄B²K²U + V·bracket` (`lgrN2`, `lgrNT`, `lgrN8`). -/
noncomputable def lgrNcL (e₁ e₂ e₃ e₄ c₁ c₂ c₃ c₄ c₅ c₆ : ℝ) (S K a B U V D : List (List ℝ)) :
    List (List ℝ) :=
  lgrAdd2 (lgrSmul2 e₁ (lgrMul2 (lgrMul2 (lgrMul2 a B) K) (lgrLNL S U V D)))
    (lgrAdd2 (lgrSmul2 (-1) (lgrMul2 (lgrAdd2 (lgrSmul2 e₂ (lgrMul2 a B)) (lgrSmul2 e₃ K)) (lgrWNL S U V D)))
      (lgrAdd2 (lgrSmul2 (-e₄) (lgrMul2 (lgrMul2 (lgrMul2 B B) (lgrMul2 K K)) U))
        (lgrMul2 V (lgrBrL c₁ c₂ c₃ c₄ c₅ c₆ K a B))))

theorem lgr_H2_NcL (e₁ e₂ e₃ e₄ c₁ c₂ c₃ c₄ c₅ c₆ : ℝ) (S K a B U V D : List (List ℝ)) (X A : ℝ) :
    lgrH2 (lgrNcL e₁ e₂ e₃ e₄ c₁ c₂ c₃ c₄ c₅ c₆ S K a B U V D) X A =
      e₁ * lgrH2 a X A * lgrH2 B X A * lgrH2 K X A *
          lgrLN (lgrH2 S X A) (lgrH2 U X A) (lgrH2 V X A) (lgrH2 D X A) -
        (e₂ * lgrH2 a X A * lgrH2 B X A + e₃ * lgrH2 K X A) *
          lgrWN (lgrH2 S X A) (lgrH2 U X A) (lgrH2 V X A) (lgrH2 D X A) -
        e₄ * lgrH2 B X A ^ 2 * lgrH2 K X A ^ 2 * lgrH2 U X A +
        lgrH2 V X A * (c₁ * lgrH2 B X A ^ 2 * lgrH2 K X A ^ 2 +
          c₂ * lgrH2 a X A ^ 2 * lgrH2 B X A ^ 2 * lgrH2 K X A +
          c₃ * lgrH2 a X A * lgrH2 B X A * lgrH2 K X A ^ 2 +
          c₄ * lgrH2 a X A ^ 3 * lgrH2 B X A * lgrH2 K X A + c₅ * lgrH2 K X A ^ 3 +
          c₆ * lgrH2 a X A ^ 2 * lgrH2 K X A ^ 2) := by
  unfold lgrNcL lgrBrL
  simp only [lgr_H2_add2, lgr_H2_mul2, lgr_H2_smul2, lgr_H2_WNL, lgr_H2_LNL]
  generalize lgrWN (lgrH2 S X A) (lgrH2 U X A) (lgrH2 V X A) (lgrH2 D X A) = W
  generalize lgrLN (lgrH2 S X A) (lgrH2 U X A) (lgrH2 V X A) (lgrH2 D X A) = L
  ring

/-- The central atoms on lists, from lists for `x`, `α`, `β`: `S = x + 1`. -/
noncomputable def lgrcS (x : List (List ℝ)) : List (List ℝ) := lgrAdd2 x [[1]]
/-- `SM = (x + 1)(35x + 13)`. -/
noncomputable def lgrcSM (x : List (List ℝ)) : List (List ℝ) :=
  lgrMul2 (lgrcS x) (lgrAdd2 (lgrSmul2 35 x) [[13]])
/-- `K = x² + 2x + α²`. -/
noncomputable def lgrcK (x a : List (List ℝ)) : List (List ℝ) :=
  lgrAdd2 (lgrMul2 x x) (lgrAdd2 (lgrSmul2 2 x) (lgrMul2 a a))
/-- `U = 3SM(β - 1) + (x - 1)²(β + 7x - 8)`. -/
noncomputable def lgrcU (x b : List (List ℝ)) : List (List ℝ) :=
  lgrAdd2 (lgrSmul2 3 (lgrMul2 (lgrcSM x) (lgrAdd2 b [[-1]])))
    (lgrMul2 (lgrMul2 (lgrAdd2 x [[-1]]) (lgrAdd2 x [[-1]])) (lgrAdd2 b (lgrAdd2 (lgrSmul2 7 x) [[-8]])))
/-- `V = 4SM(β - 1)`. -/
noncomputable def lgrcV (x b : List (List ℝ)) : List (List ℝ) :=
  lgrSmul2 4 (lgrMul2 (lgrcSM x) (lgrAdd2 b [[-1]]))
/-- `D = α² + 2αβ + 1 + 2x - 2βx`. -/
noncomputable def lgrcD (x a b : List (List ℝ)) : List (List ℝ) :=
  lgrAdd2 (lgrMul2 a a) (lgrAdd2 (lgrSmul2 2 (lgrMul2 a b)) (lgrAdd2 [[1]]
    (lgrAdd2 (lgrSmul2 2 x) (lgrSmul2 (-2) (lgrMul2 b x)))))

/-- **A central face numerator on lists** with coefficients `e`, `c` (computed from the factored
formula, never printed). -/
noncomputable def lgrFNc (e₁ e₂ e₃ e₄ c₁ c₂ c₃ c₄ c₅ c₆ : ℝ) (x a b : List (List ℝ)) :
    List (List ℝ) :=
  lgrNcL e₁ e₂ e₃ e₄ c₁ c₂ c₃ c₄ c₅ c₆ (lgrcS x) (lgrcK x a) a (lgrAdd2 a b) (lgrcU x b) (lgrcV x b)
    (lgrcD x a b)

theorem lgr_H2_atoms (x a b : List (List ℝ)) (X A : ℝ) :
    lgrH2 (lgrcS x) X A = lgrH2 x X A + 1 ∧
    lgrH2 (lgrcK x a) X A = lgrH2 x X A ^ 2 + 2 * lgrH2 x X A + lgrH2 a X A ^ 2 ∧
    lgrH2 (lgrAdd2 a b) X A = lgrH2 a X A + lgrH2 b X A ∧
    lgrH2 (lgrcU x b) X A = lgrUc (lgrH2 x X A) (lgrH2 b X A) ∧
    lgrH2 (lgrcV x b) X A = lgrVc (lgrH2 x X A) (lgrH2 b X A) ∧
    lgrH2 (lgrcD x a b) X A = ssDg (lgrH2 x X A) (lgrH2 b X A) (lgrH2 a X A) := by
  unfold lgrcU lgrcV lgrcD lgrcK lgrcSM lgrcS lgrUc lgrVc ssDg
  simp only [lgr_H2_add2, lgr_H2_mul2, lgr_H2_smul2, lgr_H2_single, polyHorner]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> (try trivial) <;> ring

theorem lgr_H2_FN2 (x a b : List (List ℝ)) (X A : ℝ) :
    lgrH2 (lgrFNc 72 180 0 72 72 (-180) 151 72 0 (-72) x a b) X A =
      lgrN2 (lgrH2 x X A + 1) (lgrH2 x X A ^ 2 + 2 * lgrH2 x X A + lgrH2 a X A ^ 2) (lgrH2 a X A)
        (lgrH2 a X A + lgrH2 b X A) (lgrUc (lgrH2 x X A) (lgrH2 b X A))
        (lgrVc (lgrH2 x X A) (lgrH2 b X A)) (ssDg (lgrH2 x X A) (lgrH2 b X A) (lgrH2 a X A)) := by
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := lgr_H2_atoms x a b X A
  unfold lgrFNc
  rw [lgr_H2_NcL, h1, h2, h3, h4, h5, h6]
  unfold lgrN2
  generalize lgrWN _ _ _ _ = W
  generalize lgrLN _ _ _ _ = L
  ring

theorem lgr_H2_FNT (x a b : List (List ℝ)) (X A : ℝ) :
    lgrH2 (lgrFNc 8 4 8 8 8 (-8) (-5) 8 8 (-8) x a b) X A =
      lgrNT (lgrH2 x X A + 1) (lgrH2 x X A ^ 2 + 2 * lgrH2 x X A + lgrH2 a X A ^ 2) (lgrH2 a X A)
        (lgrH2 a X A + lgrH2 b X A) (lgrUc (lgrH2 x X A) (lgrH2 b X A))
        (lgrVc (lgrH2 x X A) (lgrH2 b X A)) (ssDg (lgrH2 x X A) (lgrH2 b X A) (lgrH2 a X A)) := by
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := lgr_H2_atoms x a b X A
  unfold lgrFNc
  rw [lgr_H2_NcL, h1, h2, h3, h4, h5, h6]
  unfold lgrNT
  generalize lgrWN _ _ _ _ = W
  generalize lgrLN _ _ _ _ = L
  ring

theorem lgr_H2_FN8 (x a b : List (List ℝ)) (X A : ℝ) :
    lgrH2 (lgrFNc 72 36 64 72 72 (-81) (-37) 72 64 (-72) x a b) X A =
      lgrN8 (lgrH2 x X A + 1) (lgrH2 x X A ^ 2 + 2 * lgrH2 x X A + lgrH2 a X A ^ 2) (lgrH2 a X A)
        (lgrH2 a X A + lgrH2 b X A) (lgrUc (lgrH2 x X A) (lgrH2 b X A))
        (lgrVc (lgrH2 x X A) (lgrH2 b X A)) (ssDg (lgrH2 x X A) (lgrH2 b X A) (lgrH2 a X A)) := by
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := lgr_H2_atoms x a b X A
  unfold lgrFNc
  rw [lgr_H2_NcL, h1, h2, h3, h4, h5, h6]
  unfold lgrN8
  generalize lgrWN _ _ _ _ = W
  generalize lgrLN _ _ _ _ = L
  ring

/-- The list for `x + c(α - 1) = l + X + cA` in `X = x - l`, `A = α - 1`. -/
theorem lgr_H2_lin (l c x a : ℝ) :
    lgrH2 [[l, c], [1]] (x - l) (a - 1) = x + c * (a - 1) := by
  simp [lgrH2, polyHorner]; ring

end SmoothedOctagon
