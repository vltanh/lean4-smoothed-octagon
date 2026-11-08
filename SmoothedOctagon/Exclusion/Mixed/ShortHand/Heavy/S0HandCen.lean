module

public import SmoothedOctagon.Exclusion.Mixed.ShortHand.Basic
public import SmoothedOctagon.Exclusion.Mixed.ShortHand.Heavy.S0HandTools

/-!
# Hand proof of the smaller-short case, gate S0: the central face, forms and beta convexity

`archive/lighter-proofs/SHORT_DURATION_CENTRAL_TAU_TWO.md` §1 and
`SHORT_DURATION_CENTRAL_UPPER_FACES.md` §1 (with the retained beta-convexity sections of
`archive/notes/MIXED_SMALLER_SHORT_CENTRAL_TAU_TWO_SIGN.md` §3 and
`MIXED_SMALLER_SHORT_CENTRAL_DURATION_FACES.md` §2).

At the central scale `q = q_c = α²/K`, `K = x² + 2x + α²`, the floor-weighted face value is
`hl0Gc S K α B u D τ ℓ = (w - 1)τ + 1/τ + (u - 1)B/α + α/B + 1 - q - E_L + ℓ + (w - 3/4)/2` with
`w = W/K²`, `E_L = L/K`, `W = S²(S² - S + 1) + D²u - DE`, `L = 2Du - E`, `E = S³(u - 1) + 3S - 1`
(`hl0_cen_F`). The three tests are `τ = 2` (with the tangent `ℓ = 5q/(2r_A) - 11/9`), `τ = T` and
`τ = 8T/9`, `T = K/(αB)`.

**Beta convexity.** With `η = β - 1`, `u = u_∞ + J/η` and `D = (α + 1)² + 2(α - x)η`, every test
is `kη² + lη + m + r/η + s/(η + α + 1)` (`hl0_pf_two`, `hl0_pf_dur`), with `k = (5/2)δ²u_∞/K²` resp.
`δ²u_∞/(2K²)`, the residue `r = J·A` at `β = 1` and `s = α` resp. `(γK/α)(w_N - 1) + α` at
`β = -α`. The chord lemma `hl0_chord` then bounds each test by its values at `β = x` and at the
enlarged upper end (`hl0_cen_two_chord`, `hl0_cen_dur_chord`), once
* `τ = 2`: `k(x - 1)³ + r ≥ 0` (`hl0_two_res`; the note proves `r ≥ 0`), from the positive
  polynomial `hl0Phi2f` on the shape domain;
* `τ = T, 8T/9`: `s ≥ 0` (`hl0_dur_s`: `Q + α²K ≥ 0`, the continued norm at `β = -α`) and
  `k(x - 1)³ + r ≥ (x - 1)³h²/(64K²)`-type bound (`hl0_dur_res`, the note's (11)-(13): `K ≤ (25/2)αh`,
  `S(α + 1)² ≤ (45/2)h²`, `M ≥ 28S`).

Polynomial signs on the shape domain `12/5 ≤ x ≤ 9`, `1 ≤ α ≤ (5x + 4)/12` use the coefficient
bound of the notes (rule (6)) on three pieces (`hl0_trap_pos`). The cleared numerators `hl0N2`,
`hl0NT`, `hl0N8` (duration source (15)-(16)) are also given on coefficient lists (`hl0NcL`,
`hl0FNc`), so that each face polynomial is computed inside Lean from the source formula
(`hl0_H2_FN2`, …: `ring` on at most seven atoms), never printed.

Route: the residue sign of the `τ = 2` test is replaced by the weaker `k(x - 1)³ + r ≥ 0`, proved
by the coefficient bound instead of the note's case split on `d₁`.

## Main API

* `hl0Wn`, `hl0Ln`, `hl0Gc`, `hl0_cen_F`; `hl0Uc`, `hl0Vc` (`û = U/V`).
* `hl0_trap_pos`: the coefficient bound on the shape domain.
* `hl0_cen_two_chord`, `hl0_cen_dur_chord`: the beta reductions.
* `hl0N2`, `hl0NT`, `hl0N8`, `hl0_G2_neg`, …; on lists `hl0FNc`, `hl0_H2_FN2`, `hl0_H2_FNT`,
  `hl0_H2_FN8`; the face lemmas `hl0_face_rect`, `hl0_face_slant`.
-/

@[expose] public section

namespace SmoothedOctagon

/-! ### The central face value -/

/-- `W = S²(S² - S + 1) + D²u - DE` with `E = S³(u - 1) + 3S - 1`: `w = W/K²`. -/
noncomputable def hl0Wn (S u D : ℝ) : ℝ :=
  S ^ 2 * (S ^ 2 - S + 1) + D ^ 2 * u - D * (S ^ 3 * (u - 1) + 3 * S - 1)

/-- `L = 2Du - E`: `E_L = L/K`. -/
noncomputable def hl0Ln (S u D : ℝ) : ℝ := 2 * D * u - (S ^ 3 * (u - 1) + 3 * S - 1)

/-- **The central face value** `(w - 1)τ + 1/τ + (u - 1)B/α + α/B + 1 - α²/K - E_L + ℓ + (w - 3/4)/2`. -/
noncomputable def hl0Gc (S K a B u D τ ℓ : ℝ) : ℝ :=
  (hl0Wn S u D / K ^ 2 - 1) * τ + 1 / τ + (u - 1) * B / a + a / B + 1 - a ^ 2 / K -
    hl0Ln S u D / K + ℓ + (hl0Wn S u D / K ^ 2 - 3 / 4) / 2

theorem hl0_Ws_c {x a b u : ℝ} (hx : 0 < x) (ha : 0 < a) :
    hsWs x b a u (hsQc x a) = hl0Wn (x + 1) u (hsDg x b a) / (x ^ 2 + 2 * x + a ^ 2) ^ 2 := by
  have hK : 0 < x ^ 2 + 2 * x + a ^ 2 := by positivity
  unfold hsWs hsA1 hsA2 hsQc hsE0 hl0Wn
  field_simp
  ring

theorem hl0_ELs_c {x a b u : ℝ} (hx : 0 < x) (ha : 0 < a) :
    hsELs x b a u (hsQc x a) = hl0Ln (x + 1) u (hsDg x b a) / (x ^ 2 + 2 * x + a ^ 2) := by
  have hK : 0 < x ^ 2 + 2 * x + a ^ 2 := by positivity
  unfold hsELs hsA3 hsQc hsE0 hl0Ln
  field_simp
  ring

/-- **The central face value** of `hsF` at `q = q_c`, floor weight `1/2`. -/
theorem hl0_cen_F {x a b u τ ℓ : ℝ} (hx : 0 < x) (ha : 0 < a) (hB : 0 < a + b) :
    hsF x b a u (hsQc x a) τ ℓ (1 / 2) =
      hl0Gc (x + 1) (x ^ 2 + 2 * x + a ^ 2) a (a + b) u (hsDg x b a) τ ℓ := by
  have hK : 0 < x ^ 2 + 2 * x + a ^ 2 := by positivity
  unfold hsF
  rw [hl0_Ws_c hx ha, hl0_ELs_c hx ha]
  unfold hl0Gc hsRA hsQc
  field_simp

/-- `T = r_A/q_c = K/(αB)`. -/
theorem hl0_T_c {x a b : ℝ} (hx : 0 < x) (ha : 0 < a) (hB : 0 < a + b) :
    hsRA a b / hsQc x a = (x ^ 2 + 2 * x + a ^ 2) / (a * (a + b)) := by
  have hK : 0 < x ^ 2 + 2 * x + a ^ 2 := by positivity
  unfold hsRA hsQc
  field_simp

/-! ### The incoming ceiling `û` -/

/-- `U = 3SM(β - 1) + (x - 1)²(β + 7x - 8)`. -/
noncomputable def hl0Uc (x b : ℝ) : ℝ :=
  3 * (x + 1) * (35 * x + 13) * (b - 1) + (x - 1) ^ 2 * (b + 7 * x - 8)

/-- `V = 4SM(β - 1)`: `û = U/V`. -/
noncomputable def hl0Vc (x b : ℝ) : ℝ := 4 * (x + 1) * (35 * x + 13) * (b - 1)

theorem hl0_uhat_UV {x b : ℝ} (hx : 1 < x) (hb : 1 < b) : hsUhat x b = hl0Uc x b / hl0Vc x b := by
  have hb1 : 0 < b - 1 := by linarith
  unfold hsUhat hl0Uc hl0Vc
  field_simp
  ring

/-- `u_∞ = 3/4 + (x - 1)²/(4SM)`. -/
noncomputable def hl0ui (x : ℝ) : ℝ := 3 / 4 + (x - 1) ^ 2 / (4 * (x + 1) * (35 * x + 13))

/-- `J = 7(x - 1)³/(4SM)`. -/
noncomputable def hl0J (x : ℝ) : ℝ := 7 * (x - 1) ^ 3 / (4 * (x + 1) * (35 * x + 13))

theorem hl0_uhat_pole {x b : ℝ} (hx : 1 < x) (hb : 1 < b) :
    hsUhat x b = hl0ui x + hl0J x / (b - 1) := by
  have hb1 : 0 < b - 1 := by linarith
  unfold hsUhat hl0ui hl0J
  field_simp
  ring

theorem hl0_Dg_pole (x a b : ℝ) :
    hsDg x b a = (a + 1) ^ 2 + 2 * (a - x) * (b - 1) := by
  unfold hsDg; ring

/-! ### Partial fractions in `η = β - 1` -/

/-- `e₀ = S³(u_∞ - 1) + 3S - 1`. -/
noncomputable def hl0e0 (S ui : ℝ) : ℝ := S ^ 3 * (ui - 1) + 3 * S - 1
/-- Coefficient of `η²` in `W`. -/
noncomputable def hl0Wk (ui δ : ℝ) : ℝ := δ ^ 2 * ui
/-- Coefficient of `η` in `W`. -/
noncomputable def hl0Wl (S ui J D1 δ : ℝ) : ℝ := 2 * D1 * δ * ui + J * δ ^ 2 - δ * hl0e0 S ui
/-- Constant term of `W`. -/
noncomputable def hl0Wm (S ui J D1 δ : ℝ) : ℝ :=
  S ^ 2 * (S ^ 2 - S + 1) + D1 ^ 2 * ui + 2 * J * D1 * δ - D1 * hl0e0 S ui - S ^ 3 * J * δ
/-- Residue of `W` at `η = 0`. -/
noncomputable def hl0Wr (S J D1 : ℝ) : ℝ := J * D1 * (D1 - S ^ 3)
/-- Coefficient of `η` in `L`. -/
noncomputable def hl0Ll (ui δ : ℝ) : ℝ := 2 * δ * ui
/-- Constant term of `L`. -/
noncomputable def hl0Lm (S ui J D1 δ : ℝ) : ℝ := 2 * D1 * ui + 2 * J * δ - hl0e0 S ui
/-- Residue of `L` at `η = 0`. -/
noncomputable def hl0Lr (S J D1 : ℝ) : ℝ := J * (2 * D1 - S ^ 3)

theorem hl0_W_pf {S ui J D1 δ η : ℝ} (hη : η ≠ 0) :
    hl0Wn S (ui + J / η) (D1 + δ * η) = hl0Wk ui δ * η ^ 2 + hl0Wl S ui J D1 δ * η +
      hl0Wm S ui J D1 δ + hl0Wr S J D1 / η := by
  unfold hl0Wn hl0Wk hl0Wl hl0Wm hl0Wr hl0e0
  field_simp
  ring

theorem hl0_L_pf {S ui J D1 δ η : ℝ} (hη : η ≠ 0) :
    hl0Ln S (ui + J / η) (D1 + δ * η) = hl0Ll ui δ * η + hl0Lm S ui J D1 δ + hl0Lr S J D1 / η := by
  unfold hl0Ln hl0Ll hl0Lm hl0Lr hl0e0
  field_simp
  ring

/-- **The `τ = 2` test in partial fractions** (tau-two source §3 (8)). -/
theorem hl0_pf_two {S K a c ui J D1 δ η : ℝ} (hK : K ≠ 0) (ha : a ≠ 0) (hη : η ≠ 0)
    (hB : c + η ≠ 0) :
    hl0Gc S K a (c + η) (ui + J / η) (D1 + δ * η) 2 (5 * a * (c + η) / (2 * K) - 11 / 9) =
      (5 / 2 * hl0Wk ui δ / K ^ 2) * η ^ 2 +
      (5 / 2 * hl0Wl S ui J D1 δ / K ^ 2 + (ui - 1) / a - hl0Ll ui δ / K + 5 * a / (2 * K)) * η +
      (5 / 2 * hl0Wm S ui J D1 δ / K ^ 2 + ((ui - 1) * c + J) / a - hl0Lm S ui J D1 δ / K +
        5 * a * c / (2 * K) - a ^ 2 / K - 151 / 72) +
      (5 / 2 * hl0Wr S J D1 / K ^ 2 + J * c / a - hl0Lr S J D1 / K) / (η - 0) +
      a / (η - -c) := by
  unfold hl0Gc
  rw [hl0_W_pf hη, hl0_L_pf hη]
  have hB' : η - -c ≠ 0 := by rw [sub_neg_eq_add, add_comm]; exact hB
  rw [sub_zero]
  field_simp
  ring

/-- `Q = W_k c² - W_l c + W_m - K² - W_r/c`: `Q/K² = w - 1` continued to `β = -α`. -/
noncomputable def hl0Qd (S K ui J D1 δ c : ℝ) : ℝ :=
  hl0Wk ui δ * c ^ 2 - hl0Wl S ui J D1 δ * c + hl0Wm S ui J D1 δ - K ^ 2 - hl0Wr S J D1 / c

/-- **The duration tests in partial fractions** (duration source §2 (7)), `τ = γK/(αB)`. -/
theorem hl0_pf_dur {S K a c ui J D1 δ η γ ℓ : ℝ} (hK : K ≠ 0) (ha : a ≠ 0) (hc : c ≠ 0)
    (hγ : γ ≠ 0) (hη : η ≠ 0) (hB : c + η ≠ 0) :
    hl0Gc S K a (c + η) (ui + J / η) (D1 + δ * η) (γ * K / (a * (c + η))) ℓ =
      (hl0Wk ui δ / (2 * K ^ 2)) * η ^ 2 +
      (γ * hl0Wk ui δ / (a * K) + a / (γ * K) + (ui - 1) / a - hl0Ll ui δ / K +
        hl0Wl S ui J D1 δ / (2 * K ^ 2)) * η +
      (γ * (hl0Wl S ui J D1 δ - hl0Wk ui δ * c) / (a * K) + a * c / (γ * K) + ((ui - 1) * c + J) / a +
        1 - a ^ 2 / K - hl0Lm S ui J D1 δ / K + ℓ + hl0Wm S ui J D1 δ / (2 * K ^ 2) - 3 / 8) +
      (γ * hl0Wr S J D1 / (a * c * K) + J * c / a - hl0Lr S J D1 / K +
        hl0Wr S J D1 / (2 * K ^ 2)) / (η - 0) +
      (γ * hl0Qd S K ui J D1 δ c / (a * K) + a) / (η - -c) := by
  unfold hl0Gc hl0Qd
  rw [hl0_W_pf hη, hl0_L_pf hη]
  have hB' : η - -c ≠ 0 := by rw [sub_neg_eq_add, add_comm]; exact hB
  rw [sub_zero]
  field_simp
  ring


/-! ### Polynomial signs on the shape domain -/

/-- **The coefficient bound on the shape domain** `12/5 ≤ x ≤ 9`, `1 ≤ α ≤ (5x + 4)/12`, for a
bivariate list in `X = x - 12/5`, `A = α - 1`: on `α ≤ 7/6` and on `7/6 ≤ α ≤ 4/3` (every
coefficient of `X` bounded on the `A`-interval, then positive constant and nonnegative higher
coefficients), and on `α ≥ 4/3` in the coordinates `A' = α - 4/3 ≤ 11/4`, `Y = x - (12α - 4)/5 ≥ 0`. -/
theorem hl0_trap_pos (P : List (List ℝ)) (h1 : hl0PosL (P.map (hl0Low (1 / 6))))
    (h2 : hl0PosL ((P.map (hl0Shift (1 / 6))).map (hl0Low (1 / 6))))
    (h3 : hl0PosL ((hl0Shear (12 / 5) (P.map (hl0Shift (1 / 3)))).map (hl0Low (11 / 4))))
    {x a : ℝ} (hx : 12 / 5 ≤ x) (hx9 : x ≤ 9) (ha : 1 ≤ a) (ha' : a ≤ (5 * x + 4) / 12) :
    0 < hl0H2 P (x - 12 / 5) (a - 1) := by
  rcases le_or_gt a (7 / 6) with h76 | h76
  · exact hl0_pos_unb (by linarith) (by linarith) (by linarith) P h1
  rcases le_or_gt a (4 / 3) with h43 | h43
  · have e : hl0H2 P (x - 12 / 5) (a - 1) =
        hl0H2 (P.map (hl0Shift (1 / 6))) (x - 12 / 5) (a - 7 / 6) := by
      rw [hl0_H2_shift_inner]; congr 1; ring
    rw [e]
    exact hl0_pos_unb (by linarith) (by linarith) (by linarith) _ h2
  · have e : hl0H2 P (x - 12 / 5) (a - 1) =
        hl0H2 (hl0Shear (12 / 5) (P.map (hl0Shift (1 / 3)))) (x - (12 * a - 4) / 5) (a - 4 / 3) := by
      rw [hl0_H2_shear, hl0_H2_shift_inner]; congr 1 <;> ring
    rw [e]
    exact hl0_pos_unb (by linarith) (by linarith) (by linarith) _ h3

/-- The `τ = 2` residue polynomial `Φ₂ = 4SMK²α(k(x - 1)³ + r)/(x - 1)³`:
`30αSMh² + 10αh²(x - 1)² + 7((5/2)αc²(c² - S³) + cK² - αK(2c² - S³))`, `h = x - α`, `c = α + 1`
(the note's `A*`, cleared). -/
noncomputable def hl0Phi2f (x a : ℝ) : ℝ :=
  30 * a * (x + 1) * (35 * x + 13) * (x - a) ^ 2 + 10 * a * (x - a) ^ 2 * (x - 1) ^ 2 +
    7 * (5 / 2 * a * (a + 1) ^ 2 * ((a + 1) ^ 2 - (x + 1) ^ 3) +
      (a + 1) * (x ^ 2 + 2 * x + a ^ 2) ^ 2 - a * (x ^ 2 + 2 * x + a ^ 2) * (2 * (a + 1) ^ 2 - (x + 1) ^ 3))

/-- `Φ₂` on coefficient lists (computed from the formula, never printed). -/
noncomputable def hl0Phi2L (x a : List (List ℝ)) : List (List ℝ) :=
  let S := hl0Add2 x [[1]]
  let M := hl0Add2 (hl0Smul2 35 x) [[13]]
  let h := hl0Add2 x (hl0Smul2 (-1) a)
  let c := hl0Add2 a [[1]]
  let K := hl0Add2 (hl0Mul2 x x) (hl0Add2 (hl0Smul2 2 x) (hl0Mul2 a a))
  let xm := hl0Add2 x [[-1]]
  let c2 := hl0Mul2 c c
  let S3 := hl0Mul2 (hl0Mul2 S S) S
  hl0Add2 (hl0Smul2 30 (hl0Mul2 (hl0Mul2 (hl0Mul2 a S) M) (hl0Mul2 h h)))
    (hl0Add2 (hl0Smul2 10 (hl0Mul2 (hl0Mul2 a (hl0Mul2 h h)) (hl0Mul2 xm xm)))
      (hl0Smul2 7 (hl0Add2 (hl0Smul2 (5 / 2) (hl0Mul2 (hl0Mul2 a c2) (hl0Add2 c2 (hl0Smul2 (-1) S3))))
        (hl0Add2 (hl0Mul2 c (hl0Mul2 K K))
          (hl0Smul2 (-1) (hl0Mul2 (hl0Mul2 a K) (hl0Add2 (hl0Smul2 2 c2) (hl0Smul2 (-1) S3))))))))

theorem hl0_H2_Phi2L (x a : List (List ℝ)) (X A : ℝ) :
    hl0H2 (hl0Phi2L x a) X A = hl0Phi2f (hl0H2 x X A) (hl0H2 a X A) := by
  unfold hl0Phi2L hl0Phi2f
  simp only [hl0_H2_add2, hl0_H2_mul2, hl0_H2_smul2, hl0_H2_single, lrhHorner]
  ring

theorem hl0_H2_base (l : ℝ) (x a : ℝ) :
    hl0H2 [[l], [1]] (x - l) (a - 1) = x ∧ hl0H2 [[1, 1]] (x - l) (a - 1) = a := by
  constructor <;> simp [hl0H2, lrhHorner]

theorem hl0_Phi2_pos {x a : ℝ} (hx : 12 / 5 ≤ x) (hx9 : x ≤ 9) (ha : 1 ≤ a)
    (ha' : a ≤ (5 * x + 4) / 12) : 0 < hl0Phi2f x a := by
  obtain ⟨e1, e2⟩ := hl0_H2_base (12 / 5) x a
  have e := hl0_H2_Phi2L [[12 / 5], [1]] [[1, 1]] (x - 12 / 5) (a - 1)
  rw [e1, e2] at e
  rw [← e]
  apply hl0_trap_pos _ _ _ _ hx hx9 ha ha' <;>
    norm_num [hl0Phi2L, hl0Mul2, hl0Mul, hl0Smul2, hl0PosL, hl0Low, hl0Neg, hl0Shift, hl0Shear,
      hl0Add, hl0Add2, hl0Smul]

/-! ### Beta convexity of the `τ = 2` test -/

/-- The `τ = 2` test (`CENTRAL_TAU_TWO_SIGN` (3)) as a function of `(x, α, β)`. -/
noncomputable def hl0G2 (x a b : ℝ) : ℝ :=
  hsF x b a (hsUhat x b) (hsQc x a) 2 (5 / (2 * (hsRA a b / hsQc x a)) - 11 / 9) (1 / 2)

/-- `k₂ = (5/2)δ²u_∞/K²`. -/
noncomputable def hl0k2 (x a : ℝ) : ℝ :=
  5 / 2 * hl0Wk (hl0ui x) (2 * (a - x)) / (x ^ 2 + 2 * x + a ^ 2) ^ 2
/-- The `η`-coefficient `l₂`. -/
noncomputable def hl0l2 (x a : ℝ) : ℝ :=
  5 / 2 * hl0Wl (x + 1) (hl0ui x) (hl0J x) ((a + 1) ^ 2) (2 * (a - x)) / (x ^ 2 + 2 * x + a ^ 2) ^ 2 +
    (hl0ui x - 1) / a - hl0Ll (hl0ui x) (2 * (a - x)) / (x ^ 2 + 2 * x + a ^ 2) +
    5 * a / (2 * (x ^ 2 + 2 * x + a ^ 2))
/-- The constant term `m₂`. -/
noncomputable def hl0m2 (x a : ℝ) : ℝ :=
  5 / 2 * hl0Wm (x + 1) (hl0ui x) (hl0J x) ((a + 1) ^ 2) (2 * (a - x)) / (x ^ 2 + 2 * x + a ^ 2) ^ 2 +
    ((hl0ui x - 1) * (a + 1) + hl0J x) / a -
    hl0Lm (x + 1) (hl0ui x) (hl0J x) ((a + 1) ^ 2) (2 * (a - x)) / (x ^ 2 + 2 * x + a ^ 2) +
    5 * a * (a + 1) / (2 * (x ^ 2 + 2 * x + a ^ 2)) - a ^ 2 / (x ^ 2 + 2 * x + a ^ 2) - 151 / 72
/-- The residue `r₂ = J·A*` at `β = 1`. -/
noncomputable def hl0r2 (x a : ℝ) : ℝ :=
  5 / 2 * hl0Wr (x + 1) (hl0J x) ((a + 1) ^ 2) / (x ^ 2 + 2 * x + a ^ 2) ^ 2 +
    hl0J x * (a + 1) / a - hl0Lr (x + 1) (hl0J x) ((a + 1) ^ 2) / (x ^ 2 + 2 * x + a ^ 2)

theorem hl0_G2_pf {x a b : ℝ} (hx : 1 < x) (ha : 0 < a) (hb : 1 < b) :
    hl0G2 x a b = hl0k2 x a * (b - 1) ^ 2 + hl0l2 x a * (b - 1) + hl0m2 x a +
      hl0r2 x a / ((b - 1) - 0) + a / ((b - 1) - -(a + 1)) := by
  have hx0 : 0 < x := by linarith
  have hB : 0 < a + b := by linarith
  have hK : 0 < x ^ 2 + 2 * x + a ^ 2 := by positivity
  have e : hl0G2 x a b = hl0Gc (x + 1) (x ^ 2 + 2 * x + a ^ 2) a ((a + 1) + (b - 1))
      (hl0ui x + hl0J x / (b - 1)) ((a + 1) ^ 2 + 2 * (a - x) * (b - 1)) 2
      (5 * a * ((a + 1) + (b - 1)) / (2 * (x ^ 2 + 2 * x + a ^ 2)) - 11 / 9) := by
    unfold hl0G2
    rw [hl0_cen_F hx0 ha hB, hl0_T_c hx0 ha hB, hl0_uhat_pole hx hb, hl0_Dg_pole]
    have e1 : (a + 1) + (b - 1) = a + b := by ring
    rw [e1]
    congr 1
    field_simp
  rw [e, hl0_pf_two hK.ne' ha.ne' (by linarith : b - 1 ≠ 0) (by linarith)]
  unfold hl0k2 hl0l2 hl0m2 hl0r2
  ring

theorem hl0_two_res {x a : ℝ} (hx : 12 / 5 ≤ x) (hx9 : x ≤ 9) (ha : 1 ≤ a)
    (ha' : a ≤ (5 * x + 4) / 12) : 0 ≤ hl0k2 x a * (x - 1 - 0) ^ 3 + hl0r2 x a := by
  have hx1 : 0 < x - 1 := by linarith
  have ha0 : 0 < a := by linarith
  have hK : 0 < x ^ 2 + 2 * x + a ^ 2 := by positivity
  have e : hl0k2 x a * (x - 1 - 0) ^ 3 + hl0r2 x a = (x - 1) ^ 3 * hl0Phi2f x a /
        (4 * (x + 1) * (35 * x + 13) * (x ^ 2 + 2 * x + a ^ 2) ^ 2 * a) := by
    unfold hl0k2 hl0r2 hl0Wk hl0Wr hl0Lr hl0ui hl0J hl0Phi2f
    field_simp
    ring
  rw [e]
  have := hl0_Phi2_pos hx hx9 ha ha'
  positivity

/-- **Beta convexity of the `τ = 2` test** (tau-two source §3): on `x ≤ β ≤ β₁` the test is at most
the larger of its values at `β = x` and `β = β₁`. -/
theorem hl0_cen_two_chord {x a b b₁ : ℝ} (hx : 12 / 5 ≤ x) (hx9 : x ≤ 9) (ha : 1 ≤ a)
    (ha' : a ≤ (5 * x + 4) / 12) (hxb : x ≤ b) (hbb : b ≤ b₁) :
    hl0G2 x a b ≤ max (hl0G2 x a x) (hl0G2 x a b₁) := by
  have hx1 : 1 < x := by linarith
  have ha0 : 0 < a := by linarith
  rw [hl0_G2_pf hx1 ha0 (by linarith), hl0_G2_pf hx1 ha0 hx1, hl0_G2_pf hx1 ha0 (by linarith)]
  apply hl0_chord (by linarith) (by linarith) (by linarith) (by linarith)
  · unfold hl0k2 hl0Wk hl0ui; positivity
  · exact hl0_two_res hx hx9 ha ha'
  · exact ha0.le

/-! ### Beta convexity of the duration tests -/

/-- The duration test `τ = T` (`CENTRAL_DURATION_FACES` (4), `c = 1`). -/
noncomputable def hl0GT (x a b : ℝ) : ℝ :=
  hsF x b a (hsUhat x b) (hsQc x a) (hsRA a b / hsQc x a) 0 (1 / 2)

/-- The duration test `τ = 8T/9` (`CENTRAL_DURATION_FACES` (4), `c = 8/9`). -/
noncomputable def hl0G8 (x a b : ℝ) : ℝ :=
  hsF x b a (hsUhat x b) (hsQc x a) (8 * (hsRA a b / hsQc x a) / 9) (-1 / 9) (1 / 2)

/-- `k_d = δ²u_∞/(2K²)`. -/
noncomputable def hl0kd (x a : ℝ) : ℝ := hl0Wk (hl0ui x) (2 * (a - x)) / (2 * (x ^ 2 + 2 * x + a ^ 2) ^ 2)
/-- The `η`-coefficient `l_d`. -/
noncomputable def hl0ld (x a γ : ℝ) : ℝ :=
  γ * hl0Wk (hl0ui x) (2 * (a - x)) / (a * (x ^ 2 + 2 * x + a ^ 2)) + a / (γ * (x ^ 2 + 2 * x + a ^ 2)) +
    (hl0ui x - 1) / a - hl0Ll (hl0ui x) (2 * (a - x)) / (x ^ 2 + 2 * x + a ^ 2) +
    hl0Wl (x + 1) (hl0ui x) (hl0J x) ((a + 1) ^ 2) (2 * (a - x)) / (2 * (x ^ 2 + 2 * x + a ^ 2) ^ 2)
/-- The constant term `m_d`. -/
noncomputable def hl0md (x a γ ℓ : ℝ) : ℝ :=
  γ * (hl0Wl (x + 1) (hl0ui x) (hl0J x) ((a + 1) ^ 2) (2 * (a - x)) -
      hl0Wk (hl0ui x) (2 * (a - x)) * (a + 1)) / (a * (x ^ 2 + 2 * x + a ^ 2)) +
    a * (a + 1) / (γ * (x ^ 2 + 2 * x + a ^ 2)) + ((hl0ui x - 1) * (a + 1) + hl0J x) / a + 1 -
    a ^ 2 / (x ^ 2 + 2 * x + a ^ 2) -
    hl0Lm (x + 1) (hl0ui x) (hl0J x) ((a + 1) ^ 2) (2 * (a - x)) / (x ^ 2 + 2 * x + a ^ 2) + ℓ +
    hl0Wm (x + 1) (hl0ui x) (hl0J x) ((a + 1) ^ 2) (2 * (a - x)) / (2 * (x ^ 2 + 2 * x + a ^ 2) ^ 2) -
    3 / 8
/-- The residue `r_d = J·A_γ` at `β = 1`. -/
noncomputable def hl0rd (x a γ : ℝ) : ℝ :=
  γ * hl0Wr (x + 1) (hl0J x) ((a + 1) ^ 2) / (a * (a + 1) * (x ^ 2 + 2 * x + a ^ 2)) +
    hl0J x * (a + 1) / a - hl0Lr (x + 1) (hl0J x) ((a + 1) ^ 2) / (x ^ 2 + 2 * x + a ^ 2) +
    hl0Wr (x + 1) (hl0J x) ((a + 1) ^ 2) / (2 * (x ^ 2 + 2 * x + a ^ 2) ^ 2)
/-- `Q` of the duration tests at the actual coefficients. -/
noncomputable def hl0Qx (x a : ℝ) : ℝ :=
  hl0Qd (x + 1) (x ^ 2 + 2 * x + a ^ 2) (hl0ui x) (hl0J x) ((a + 1) ^ 2) (2 * (a - x)) (a + 1)
/-- The residue `s_d = (γK/α)(w_N - 1) + α` at `β = -α`. -/
noncomputable def hl0sd (x a γ : ℝ) : ℝ := γ * hl0Qx x a / (a * (x ^ 2 + 2 * x + a ^ 2)) + a

theorem hl0_Gd_pf {x a b γ ℓ : ℝ} (hx : 1 < x) (ha : 0 < a) (hb : 1 < b) (hγ : 0 < γ) :
    hsF x b a (hsUhat x b) (hsQc x a) (γ * (hsRA a b / hsQc x a)) ℓ (1 / 2) =
      hl0kd x a * (b - 1) ^ 2 + hl0ld x a γ * (b - 1) + hl0md x a γ ℓ +
      hl0rd x a γ / ((b - 1) - 0) + hl0sd x a γ / ((b - 1) - -(a + 1)) := by
  have hx0 : 0 < x := by linarith
  have hB : 0 < a + b := by linarith
  have hK : 0 < x ^ 2 + 2 * x + a ^ 2 := by positivity
  have e : hsF x b a (hsUhat x b) (hsQc x a) (γ * (hsRA a b / hsQc x a)) ℓ (1 / 2) =
      hl0Gc (x + 1) (x ^ 2 + 2 * x + a ^ 2) a ((a + 1) + (b - 1))
      (hl0ui x + hl0J x / (b - 1)) ((a + 1) ^ 2 + 2 * (a - x) * (b - 1))
      (γ * (x ^ 2 + 2 * x + a ^ 2) / (a * ((a + 1) + (b - 1)))) ℓ := by
    rw [hl0_cen_F hx0 ha hB, hl0_T_c hx0 ha hB, hl0_uhat_pole hx hb, hl0_Dg_pole]
    have e1 : (a + 1) + (b - 1) = a + b := by ring
    rw [e1, mul_div_assoc]
  rw [e, hl0_pf_dur hK.ne' ha.ne' (by linarith) hγ.ne' (by linarith : b - 1 ≠ 0) (by linarith)]
  unfold hl0kd hl0ld hl0md hl0rd hl0sd hl0Qx
  ring

theorem hl0_GT_pf {x a b : ℝ} (hx : 1 < x) (ha : 0 < a) (hb : 1 < b) :
    hl0GT x a b = hl0kd x a * (b - 1) ^ 2 + hl0ld x a 1 * (b - 1) + hl0md x a 1 0 +
      hl0rd x a 1 / ((b - 1) - 0) + hl0sd x a 1 / ((b - 1) - -(a + 1)) := by
  rw [← hl0_Gd_pf hx ha hb one_pos, one_mul]; rfl

theorem hl0_G8_pf {x a b : ℝ} (hx : 1 < x) (ha : 0 < a) (hb : 1 < b) :
    hl0G8 x a b = hl0kd x a * (b - 1) ^ 2 + hl0ld x a (8 / 9) * (b - 1) + hl0md x a (8 / 9) (-1 / 9) +
      hl0rd x a (8 / 9) / ((b - 1) - 0) + hl0sd x a (8 / 9) / ((b - 1) - -(a + 1)) := by
  rw [← hl0_Gd_pf hx ha hb (by norm_num)]
  unfold hl0G8
  congr 1
  ring

/-- `4SM(Q + α²K)` cleared (duration source (8)-(9)): with `U_I = 3SM + (x - 1)² = 4SMu_∞`,
`J_J = 7(x - 1)³ = 4SMJ`, `E₀' = S³(U_I - 4SM) + 4SM(3S - 1)`, `c = α + 1`, `δ = 2(α - x)`. -/
noncomputable def hl0Qnf (x a : ℝ) : ℝ :=
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

/-- `hl0Qnf` on coefficient lists. -/
noncomputable def hl0QnL (x a : List (List ℝ)) : List (List ℝ) :=
  let S := hl0Add2 x [[1]]
  let SM := hl0Mul2 S (hl0Add2 (hl0Smul2 35 x) [[13]])
  let F4 := hl0Smul2 4 SM
  let xm := hl0Add2 x [[-1]]
  let UI := hl0Add2 (hl0Smul2 3 SM) (hl0Mul2 xm xm)
  let JJ := hl0Smul2 7 (hl0Mul2 (hl0Mul2 xm xm) xm)
  let c := hl0Add2 a [[1]]
  let c2 := hl0Mul2 c c
  let δ := hl0Smul2 2 (hl0Add2 a (hl0Smul2 (-1) x))
  let δ2 := hl0Mul2 δ δ
  let K := hl0Add2 (hl0Mul2 x x) (hl0Add2 (hl0Smul2 2 x) (hl0Mul2 a a))
  let S2 := hl0Mul2 S S
  let S3 := hl0Mul2 S2 S
  let E0 := hl0Add2 (hl0Mul2 S3 (hl0Add2 UI (hl0Smul2 (-1) F4)))
    (hl0Mul2 F4 (hl0Add2 (hl0Smul2 3 S) [[-1]]))
  hl0Add2 (hl0Mul2 (hl0Mul2 UI δ2) c2)
    (hl0Add2 (hl0Smul2 (-1) (hl0Mul2 c (hl0Add2 (hl0Smul2 2 (hl0Mul2 (hl0Mul2 c2 δ) UI))
      (hl0Add2 (hl0Mul2 JJ δ2) (hl0Smul2 (-1) (hl0Mul2 δ E0))))))
    (hl0Add2 (hl0Add2 (hl0Mul2 F4 (hl0Mul2 S2 (hl0Add2 S2 (hl0Add2 (hl0Smul2 (-1) S) [[1]]))))
      (hl0Add2 (hl0Mul2 (hl0Mul2 c2 c2) UI) (hl0Add2 (hl0Smul2 2 (hl0Mul2 (hl0Mul2 JJ c2) δ))
        (hl0Add2 (hl0Smul2 (-1) (hl0Mul2 c2 E0)) (hl0Smul2 (-1) (hl0Mul2 (hl0Mul2 S3 JJ) δ))))))
    (hl0Add2 (hl0Smul2 (-1) (hl0Mul2 F4 (hl0Mul2 K K)))
      (hl0Add2 (hl0Smul2 (-1) (hl0Mul2 (hl0Mul2 JJ c) (hl0Add2 c2 (hl0Smul2 (-1) S3))))
        (hl0Mul2 (hl0Mul2 F4 (hl0Mul2 a a)) K)))))

theorem hl0_H2_QnL (x a : List (List ℝ)) (X A : ℝ) :
    hl0H2 (hl0QnL x a) X A = hl0Qnf (hl0H2 x X A) (hl0H2 a X A) := by
  unfold hl0QnL hl0Qnf
  simp only [hl0_H2_add2, hl0_H2_mul2, hl0_H2_smul2, hl0_H2_single, lrhHorner]
  ring

/-- **The residue at `β = -α` is nonnegative** (duration source (9)), for `0 < γ ≤ 1`. -/
theorem hl0_dur_s {x a γ : ℝ} (hx : 12 / 5 ≤ x) (hx9 : x ≤ 9) (ha : 1 ≤ a)
    (ha' : a ≤ (5 * x + 4) / 12) (hγ : 0 < γ) (hγ1 : γ ≤ 1) : 0 ≤ hl0sd x a γ := by
  have ha0 : 0 < a := by linarith
  have hK : 0 < x ^ 2 + 2 * x + a ^ 2 := by positivity
  have hQ : hl0Qx x a + a ^ 2 * (x ^ 2 + 2 * x + a ^ 2) =
      hl0Qnf x a / (4 * (x + 1) * (35 * x + 13)) := by
    unfold hl0Qx hl0Qd hl0Wk hl0Wl hl0Wm hl0Wr hl0e0 hl0ui hl0J hl0Qnf
    field_simp
    ring
  have hpos : 0 < hl0Qnf x a := by
    obtain ⟨e1, e2⟩ := hl0_H2_base (12 / 5) x a
    have e := hl0_H2_QnL [[12 / 5], [1]] [[1, 1]] (x - 12 / 5) (a - 1)
    rw [e1, e2] at e
    rw [← e]
    apply hl0_trap_pos _ _ _ _ hx hx9 ha ha' <;>
      norm_num [hl0QnL, hl0Mul2, hl0Mul, hl0Smul2, hl0PosL, hl0Low, hl0Neg, hl0Shift, hl0Shear,
        hl0Add, hl0Add2, hl0Smul]
  have hQ0 : 0 ≤ hl0Qx x a + a ^ 2 * (x ^ 2 + 2 * x + a ^ 2) := by
    rw [hQ]; have : 0 < (x + 1) * (35 * x + 13) := by nlinarith
    positivity
  unfold hl0sd
  have e : γ * hl0Qx x a / (a * (x ^ 2 + 2 * x + a ^ 2)) + a =
      (γ * (hl0Qx x a + a ^ 2 * (x ^ 2 + 2 * x + a ^ 2)) + (1 - γ) * a ^ 2 * (x ^ 2 + 2 * x + a ^ 2)) /
        (a * (x ^ 2 + 2 * x + a ^ 2)) := by
    field_simp; ring
  rw [e]
  have : 0 ≤ 1 - γ := by linarith
  positivity

/-- **Convexity at `β = 1`** (duration source (11)-(13)): `k_d(x - 1)³ + r_d ≥ 0` for `0 < γ ≤ 1`,
from `K ≤ (25/2)αh`, `S(α + 1)² ≤ (45/2)h²` and `M ≥ 28S` (`h = x - α`). -/
theorem hl0_dur_res {x a γ : ℝ} (hx : 12 / 5 ≤ x) (hx9 : x ≤ 9) (ha : 1 ≤ a)
    (ha' : a ≤ (5 * x + 4) / 12) (hγ1 : γ ≤ 1) :
    0 ≤ hl0kd x a * (x - 1 - 0) ^ 3 + hl0rd x a γ := by
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
  have e : hl0kd x a * (x - 1 - 0) ^ 3 + hl0rd x a γ = (x - 1) ^ 3 *
      (6 * a * S * M * h ^ 2 + 2 * a * h ^ 2 * (x - 1) ^ 2 + 7 * (γ * (a + 1) * K *
      ((a + 1) ^ 2 - S ^ 3) + (a + 1) * K ^ 2 - a * K * (2 * (a + 1) ^ 2 - S ^ 3) +
      a * (a + 1) ^ 2 * ((a + 1) ^ 2 - S ^ 3) / 2)) / (4 * S * M * K ^ 2 * a) := by
    have hM0 : 0 < M := by linarith
    unfold hl0kd hl0rd hl0Wk hl0Wr hl0Lr hl0ui hl0J
    simp only [S, M, K, h] at hM0 hS ⊢
    field_simp
    ring
  rw [e]
  have hM0 : 0 < M := by linarith
  positivity

/-- **Beta convexity of the duration tests** (duration source §2): for `0 < γ ≤ 1`, the test
`τ = γT` is at most the larger of its values at `β = x` and `β = β₁`. -/
theorem hl0_cen_dur_chord {x a b b₁ γ ℓ : ℝ} (hx : 12 / 5 ≤ x) (hx9 : x ≤ 9) (ha : 1 ≤ a)
    (ha' : a ≤ (5 * x + 4) / 12) (hxb : x ≤ b) (hbb : b ≤ b₁) (hγ : 0 < γ) (hγ1 : γ ≤ 1) :
    hl0kd x a * (b - 1) ^ 2 + hl0ld x a γ * (b - 1) + hl0md x a γ ℓ +
        hl0rd x a γ / ((b - 1) - 0) + hl0sd x a γ / ((b - 1) - -(a + 1)) ≤
      max (hl0kd x a * (x - 1) ^ 2 + hl0ld x a γ * (x - 1) + hl0md x a γ ℓ +
        hl0rd x a γ / ((x - 1) - 0) + hl0sd x a γ / ((x - 1) - -(a + 1)))
      (hl0kd x a * (b₁ - 1) ^ 2 + hl0ld x a γ * (b₁ - 1) + hl0md x a γ ℓ +
        hl0rd x a γ / ((b₁ - 1) - 0) + hl0sd x a γ / ((b₁ - 1) - -(a + 1))) := by
  have ha0 : 0 < a := by linarith
  apply hl0_chord (by linarith) (by linarith) (by linarith) (by linarith)
  · unfold hl0kd hl0Wk hl0ui; positivity
  · exact hl0_dur_res hx hx9 ha ha' hγ1
  · exact hl0_dur_s hx hx9 ha ha' hγ hγ1

theorem hl0_cen_T_chord {x a b b₁ : ℝ} (hx : 12 / 5 ≤ x) (hx9 : x ≤ 9) (ha : 1 ≤ a)
    (ha' : a ≤ (5 * x + 4) / 12) (hxb : x ≤ b) (hbb : b ≤ b₁) :
    hl0GT x a b ≤ max (hl0GT x a x) (hl0GT x a b₁) := by
  have hx1 : 1 < x := by linarith
  have ha0 : 0 < a := by linarith
  rw [hl0_GT_pf hx1 ha0 (by linarith), hl0_GT_pf hx1 ha0 hx1, hl0_GT_pf hx1 ha0 (by linarith)]
  exact hl0_cen_dur_chord hx hx9 ha ha' hxb hbb one_pos le_rfl

theorem hl0_cen_8_chord {x a b b₁ : ℝ} (hx : 12 / 5 ≤ x) (hx9 : x ≤ 9) (ha : 1 ≤ a)
    (ha' : a ≤ (5 * x + 4) / 12) (hxb : x ≤ b) (hbb : b ≤ b₁) :
    hl0G8 x a b ≤ max (hl0G8 x a x) (hl0G8 x a b₁) := by
  have hx1 : 1 < x := by linarith
  have ha0 : 0 < a := by linarith
  rw [hl0_G8_pf hx1 ha0 (by linarith), hl0_G8_pf hx1 ha0 hx1, hl0_G8_pf hx1 ha0 (by linarith)]
  exact hl0_cen_dur_chord hx hx9 ha ha' hxb hbb (by norm_num) (by norm_num)

/-! ### The cleared numerators (duration source (15)-(16)) -/

/-- `W·V` for `u = U/V`: `S²(S² - S + 1)V + D²U - D E_N`, `E_N = S³(U - V) + (3S - 1)V`. -/
noncomputable def hl0WN (S U V D : ℝ) : ℝ :=
  S ^ 2 * (S ^ 2 - S + 1) * V + D ^ 2 * U - D * (S ^ 3 * (U - V) + (3 * S - 1) * V)

/-- `L·V` for `u = U/V`: `2DU - E_N`. -/
noncomputable def hl0LN (S U V D : ℝ) : ℝ := 2 * D * U - (S ^ 3 * (U - V) + (3 * S - 1) * V)

/-- The cleared `τ = 2` numerator: `G₂ = -N₂/(72αBK²V)`. -/
noncomputable def hl0N2 (S K a B U V D : ℝ) : ℝ :=
  72 * a * B * K * hl0LN S U V D - 180 * a * B * hl0WN S U V D - 72 * B ^ 2 * K ^ 2 * U +
    V * (72 * B ^ 2 * K ^ 2 - 180 * a ^ 2 * B ^ 2 * K + 151 * a * B * K ^ 2 + 72 * a ^ 3 * B * K -
      72 * a ^ 2 * K ^ 2)

/-- The cleared `τ = T` numerator: `G_T = -N_T/(8αBK²V)`. -/
noncomputable def hl0NT (S K a B U V D : ℝ) : ℝ :=
  8 * a * B * K * hl0LN S U V D - (4 * a * B + 8 * K) * hl0WN S U V D - 8 * B ^ 2 * K ^ 2 * U +
    V * (8 * B ^ 2 * K ^ 2 - 8 * a ^ 2 * B ^ 2 * K - 5 * a * B * K ^ 2 + 8 * a ^ 3 * B * K +
      8 * K ^ 3 - 8 * a ^ 2 * K ^ 2)

/-- The cleared `τ = 8T/9` numerator: `G₈ = -N₈/(72αBK²V)`. -/
noncomputable def hl0N8 (S K a B U V D : ℝ) : ℝ :=
  72 * a * B * K * hl0LN S U V D - (36 * a * B + 64 * K) * hl0WN S U V D - 72 * B ^ 2 * K ^ 2 * U +
    V * (72 * B ^ 2 * K ^ 2 - 81 * a ^ 2 * B ^ 2 * K - 37 * a * B * K ^ 2 + 72 * a ^ 3 * B * K +
      64 * K ^ 3 - 72 * a ^ 2 * K ^ 2)

theorem hl0_Gc_UV {S K a B U V D τ ℓ : ℝ} (hV : V ≠ 0) :
    hl0Gc S K a B (U / V) D τ ℓ = (hl0WN S U V D / V / K ^ 2 - 1) * τ + 1 / τ + (U / V - 1) * B / a +
      a / B + 1 - a ^ 2 / K - hl0LN S U V D / V / K + ℓ + (hl0WN S U V D / V / K ^ 2 - 3 / 4) / 2 := by
  have hW : hl0Wn S (U / V) D = hl0WN S U V D / V := by
    unfold hl0Wn hl0WN; field_simp; ring
  have hL : hl0Ln S (U / V) D = hl0LN S U V D / V := by
    unfold hl0Ln hl0LN; field_simp; ring
  unfold hl0Gc; rw [hW, hL]

theorem hl0_N2_eq {S K a B U V D : ℝ} (hK : K ≠ 0) (ha : a ≠ 0) (hB : B ≠ 0) (hV : V ≠ 0) :
    hl0Gc S K a B (U / V) D 2 (5 * a * B / (2 * K) - 11 / 9) =
      -hl0N2 S K a B U V D / (72 * a * B * K ^ 2 * V) := by
  rw [hl0_Gc_UV hV]
  unfold hl0N2
  generalize hl0WN S U V D = W
  generalize hl0LN S U V D = L
  field_simp
  ring

theorem hl0_NT_eq {S K a B U V D : ℝ} (hK : K ≠ 0) (ha : a ≠ 0) (hB : B ≠ 0) (hV : V ≠ 0) :
    hl0Gc S K a B (U / V) D (K / (a * B)) 0 = -hl0NT S K a B U V D / (8 * a * B * K ^ 2 * V) := by
  rw [hl0_Gc_UV hV]
  unfold hl0NT
  generalize hl0WN S U V D = W
  generalize hl0LN S U V D = L
  field_simp
  ring

theorem hl0_N8_eq {S K a B U V D : ℝ} (hK : K ≠ 0) (ha : a ≠ 0) (hB : B ≠ 0) (hV : V ≠ 0) :
    hl0Gc S K a B (U / V) D (8 * (K / (a * B)) / 9) (-1 / 9) =
      -hl0N8 S K a B U V D / (72 * a * B * K ^ 2 * V) := by
  rw [hl0_Gc_UV hV]
  unfold hl0N8
  generalize hl0WN S U V D = W
  generalize hl0LN S U V D = L
  field_simp
  ring

/-- The three central tests are negative when their cleared numerators are positive. -/
theorem hl0_G2_neg {x a b : ℝ} (hx : 1 < x) (ha : 0 < a) (hb : 1 < b)
    (hN : 0 < hl0N2 (x + 1) (x ^ 2 + 2 * x + a ^ 2) a (a + b) (hl0Uc x b) (hl0Vc x b) (hsDg x b a)) :
    hl0G2 x a b < 0 := by
  have hx0 : 0 < x := by linarith
  have hB : 0 < a + b := by linarith
  have hK : 0 < x ^ 2 + 2 * x + a ^ 2 := by positivity
  have hb1 : 0 < b - 1 := by linarith
  have hV : 0 < hl0Vc x b := by unfold hl0Vc; positivity
  unfold hl0G2
  rw [hl0_cen_F hx0 ha hB, hl0_T_c hx0 ha hB, hl0_uhat_UV hx hb]
  have e : 5 / (2 * ((x ^ 2 + 2 * x + a ^ 2) / (a * (a + b)))) - 11 / 9 =
      5 * a * (a + b) / (2 * (x ^ 2 + 2 * x + a ^ 2)) - 11 / 9 := by field_simp
  rw [e, hl0_N2_eq hK.ne' ha.ne' hB.ne' hV.ne']
  apply div_neg_of_neg_of_pos (by linarith)
  positivity

theorem hl0_GT_neg {x a b : ℝ} (hx : 1 < x) (ha : 0 < a) (hb : 1 < b)
    (hN : 0 < hl0NT (x + 1) (x ^ 2 + 2 * x + a ^ 2) a (a + b) (hl0Uc x b) (hl0Vc x b) (hsDg x b a)) :
    hl0GT x a b < 0 := by
  have hx0 : 0 < x := by linarith
  have hB : 0 < a + b := by linarith
  have hK : 0 < x ^ 2 + 2 * x + a ^ 2 := by positivity
  have hb1 : 0 < b - 1 := by linarith
  have hV : 0 < hl0Vc x b := by unfold hl0Vc; positivity
  unfold hl0GT
  rw [hl0_cen_F hx0 ha hB, hl0_T_c hx0 ha hB, hl0_uhat_UV hx hb,
    hl0_NT_eq hK.ne' ha.ne' hB.ne' hV.ne']
  apply div_neg_of_neg_of_pos (by linarith)
  positivity

theorem hl0_G8_neg {x a b : ℝ} (hx : 1 < x) (ha : 0 < a) (hb : 1 < b)
    (hN : 0 < hl0N8 (x + 1) (x ^ 2 + 2 * x + a ^ 2) a (a + b) (hl0Uc x b) (hl0Vc x b) (hsDg x b a)) :
    hl0G8 x a b < 0 := by
  have hx0 : 0 < x := by linarith
  have hB : 0 < a + b := by linarith
  have hK : 0 < x ^ 2 + 2 * x + a ^ 2 := by positivity
  have hb1 : 0 < b - 1 := by linarith
  have hV : 0 < hl0Vc x b := by unfold hl0Vc; positivity
  unfold hl0G8
  rw [hl0_cen_F hx0 ha hB, hl0_T_c hx0 ha hB, hl0_uhat_UV hx hb,
    hl0_N8_eq hK.ne' ha.ne' hB.ne' hV.ne']
  apply div_neg_of_neg_of_pos (by linarith)
  positivity

/-! ### Upper faces: convexity in `x` on a rectangle -/

/-- The `X`-derivative is nonnegative on the rectangle once the second derivative is (coefficient
bound) and the first derivative is positive on the left edge. -/
theorem hl0_face_d1 (P : List (List ℝ)) {HA W : ℝ} (hcurv : 0 ≤ hl0Low2 HA W (hl0D2 (hl0D2 P)))
    (hd1 : ∀ A, 0 ≤ A → A ≤ HA → 0 < lrhHorner (hl0Eval 0 (hl0D2 P)) A) {X A : ℝ} (hA : 0 ≤ A)
    (hAH : A ≤ HA) (hX : 0 ≤ X) (hXW : X ≤ W) : 0 ≤ hl0H2 (hl0D2 P) X A := by
  have h2 : ∀ X, 0 ≤ X → X ≤ W → 0 ≤ hl0H2 (hl0D2 (hl0D2 P)) X A :=
    fun X h1 h2 => hcurv.trans (hl0_low2_le hA hAH h1 h2 _)
  have h1 : 0 ≤ hl0H2 (hl0D2 P) 0 A := by rw [← hl0_horner_eval]; exact (hd1 A hA hAH).le
  have := hl0_mono_X (P := hl0D2 P) (A := A) (fun X' h1' h2' => h2 X' h1' (h2'.trans hXW)) hX
  linarith

/-- **A face on a rectangle** (`UPPER_FACES` §§3-4): positive second `X`-derivative, positive first
derivative and value on the left edge `X = 0`. -/
theorem hl0_face_rect (P : List (List ℝ)) {HA W : ℝ} (hcurv : 0 ≤ hl0Low2 HA W (hl0D2 (hl0D2 P)))
    (hd1 : ∀ A, 0 ≤ A → A ≤ HA → 0 < lrhHorner (hl0Eval 0 (hl0D2 P)) A)
    (hv : ∀ A, 0 ≤ A → A ≤ HA → 0 < lrhHorner (hl0Eval 0 P) A) {X A : ℝ} (hA : 0 ≤ A)
    (hAH : A ≤ HA) (hX : 0 ≤ X) (hXW : X ≤ W) : 0 < hl0H2 P X A := by
  have h0 : 0 < hl0H2 P 0 A := by rw [← hl0_horner_eval]; exact hv A hA hAH
  have := hl0_mono_X (P := P) (A := A)
    (fun X' h1' h2' => hl0_face_d1 P hcurv hd1 hA hAH h1' (h2'.trans hXW)) hX
  linarith

/-- **A face with a slanted edge** (`TAU_TWO` §§3-4): on `A ≤ T` the left edge, beyond it the line
`X = αA + β` (to the left of the actual point) carries the sign. -/
theorem hl0_face_slant (P : List (List ℝ)) {HA W T α β : ℝ}
    (hcurv : 0 ≤ hl0Low2 HA W (hl0D2 (hl0D2 P)))
    (hd1 : ∀ A, 0 ≤ A → A ≤ HA → 0 < lrhHorner (hl0Eval 0 (hl0D2 P)) A)
    (hv : ∀ A, 0 ≤ A → A ≤ T → 0 < lrhHorner (hl0Eval 0 P) A)
    (hs : ∀ A, T ≤ A → A ≤ HA → 0 < lrhHorner (hl0Slant α β P) A) {X A : ℝ} (hA : 0 ≤ A)
    (hAH : A ≤ HA) (hX : 0 ≤ X) (hXW : X ≤ W)
    (hcase : A ≤ T ∨ (0 ≤ α * A + β ∧ α * A + β ≤ X)) : 0 < hl0H2 P X A := by
  rcases le_or_gt A T with hT | hT
  · have h0 : 0 < hl0H2 P 0 A := by rw [← hl0_horner_eval]; exact hv A hA hT
    have := hl0_mono_X (P := P) (A := A)
      (fun X' h1' h2' => hl0_face_d1 P hcurv hd1 hA hAH h1' (h2'.trans hXW)) hX
    linarith
  · rcases hcase with h | ⟨h1, h2⟩
    · exact absurd h (not_le.2 hT)
    have h0 : 0 < hl0H2 P (α * A + β) A := by rw [← hl0_horner_slant]; exact hs A hT.le hAH
    have := hl0_mono_X (P := P) (A := A)
      (fun X' h1' h2' => hl0_face_d1 P hcurv hd1 hA hAH (h1.trans h1') (h2'.trans hXW)) h2
    linarith

/-! ### The cleared numerators on coefficient lists -/

/-- `hl0WN` on lists. -/
noncomputable def hl0WNL (S U V D : List (List ℝ)) : List (List ℝ) :=
  hl0Add2 (hl0Mul2 (hl0Mul2 (hl0Mul2 S S) (hl0Add2 (hl0Mul2 S S) (hl0Add2 (hl0Smul2 (-1) S) [[1]]))) V)
    (hl0Add2 (hl0Mul2 (hl0Mul2 D D) U)
      (hl0Smul2 (-1) (hl0Mul2 D (hl0Add2 (hl0Mul2 (hl0Mul2 (hl0Mul2 S S) S) (hl0Add2 U (hl0Smul2 (-1) V)))
        (hl0Mul2 (hl0Add2 (hl0Smul2 3 S) [[-1]]) V)))))

/-- `hl0LN` on lists. -/
noncomputable def hl0LNL (S U V D : List (List ℝ)) : List (List ℝ) :=
  hl0Add2 (hl0Smul2 2 (hl0Mul2 D U))
    (hl0Smul2 (-1) (hl0Add2 (hl0Mul2 (hl0Mul2 (hl0Mul2 S S) S) (hl0Add2 U (hl0Smul2 (-1) V)))
      (hl0Mul2 (hl0Add2 (hl0Smul2 3 S) [[-1]]) V)))

theorem hl0_H2_WNL (S U V D : List (List ℝ)) (X A : ℝ) :
    hl0H2 (hl0WNL S U V D) X A =
      hl0WN (hl0H2 S X A) (hl0H2 U X A) (hl0H2 V X A) (hl0H2 D X A) := by
  unfold hl0WNL hl0WN
  simp only [hl0_H2_add2, hl0_H2_mul2, hl0_H2_smul2, hl0_H2_single, lrhHorner]
  ring

theorem hl0_H2_LNL (S U V D : List (List ℝ)) (X A : ℝ) :
    hl0H2 (hl0LNL S U V D) X A =
      hl0LN (hl0H2 S X A) (hl0H2 U X A) (hl0H2 V X A) (hl0H2 D X A) := by
  unfold hl0LNL hl0LN
  simp only [hl0_H2_add2, hl0_H2_mul2, hl0_H2_smul2, hl0_H2_single, lrhHorner]
  ring

/-- The `V`-bracket of a cleared numerator, `c₁B²K² + c₂α²B²K + c₃αBK² + c₄α³BK + c₅K³ + c₆α²K²`,
on lists. -/
noncomputable def hl0BrL (c₁ c₂ c₃ c₄ c₅ c₆ : ℝ) (K a B : List (List ℝ)) : List (List ℝ) :=
  let B2 := hl0Mul2 B B
  let K2 := hl0Mul2 K K
  let a2 := hl0Mul2 a a
  hl0Add2 (hl0Smul2 c₁ (hl0Mul2 B2 K2)) (hl0Add2 (hl0Smul2 c₂ (hl0Mul2 (hl0Mul2 a2 B2) K))
    (hl0Add2 (hl0Smul2 c₃ (hl0Mul2 (hl0Mul2 a B) K2)) (hl0Add2 (hl0Smul2 c₄ (hl0Mul2 (hl0Mul2 (hl0Mul2 a2 a) B) K))
      (hl0Add2 (hl0Smul2 c₅ (hl0Mul2 K2 K)) (hl0Smul2 c₆ (hl0Mul2 a2 K2))))))

/-- A cleared central numerator on lists:
`e₁αBK·L - (e₂αB + e₃K)W - e₄B²K²U + V·bracket` (`hl0N2`, `hl0NT`, `hl0N8`). -/
noncomputable def hl0NcL (e₁ e₂ e₃ e₄ c₁ c₂ c₃ c₄ c₅ c₆ : ℝ) (S K a B U V D : List (List ℝ)) :
    List (List ℝ) :=
  hl0Add2 (hl0Smul2 e₁ (hl0Mul2 (hl0Mul2 (hl0Mul2 a B) K) (hl0LNL S U V D)))
    (hl0Add2 (hl0Smul2 (-1) (hl0Mul2 (hl0Add2 (hl0Smul2 e₂ (hl0Mul2 a B)) (hl0Smul2 e₃ K)) (hl0WNL S U V D)))
      (hl0Add2 (hl0Smul2 (-e₄) (hl0Mul2 (hl0Mul2 (hl0Mul2 B B) (hl0Mul2 K K)) U))
        (hl0Mul2 V (hl0BrL c₁ c₂ c₃ c₄ c₅ c₆ K a B))))

theorem hl0_H2_NcL (e₁ e₂ e₃ e₄ c₁ c₂ c₃ c₄ c₅ c₆ : ℝ) (S K a B U V D : List (List ℝ)) (X A : ℝ) :
    hl0H2 (hl0NcL e₁ e₂ e₃ e₄ c₁ c₂ c₃ c₄ c₅ c₆ S K a B U V D) X A =
      e₁ * hl0H2 a X A * hl0H2 B X A * hl0H2 K X A *
          hl0LN (hl0H2 S X A) (hl0H2 U X A) (hl0H2 V X A) (hl0H2 D X A) -
        (e₂ * hl0H2 a X A * hl0H2 B X A + e₃ * hl0H2 K X A) *
          hl0WN (hl0H2 S X A) (hl0H2 U X A) (hl0H2 V X A) (hl0H2 D X A) -
        e₄ * hl0H2 B X A ^ 2 * hl0H2 K X A ^ 2 * hl0H2 U X A +
        hl0H2 V X A * (c₁ * hl0H2 B X A ^ 2 * hl0H2 K X A ^ 2 +
          c₂ * hl0H2 a X A ^ 2 * hl0H2 B X A ^ 2 * hl0H2 K X A +
          c₃ * hl0H2 a X A * hl0H2 B X A * hl0H2 K X A ^ 2 +
          c₄ * hl0H2 a X A ^ 3 * hl0H2 B X A * hl0H2 K X A + c₅ * hl0H2 K X A ^ 3 +
          c₆ * hl0H2 a X A ^ 2 * hl0H2 K X A ^ 2) := by
  unfold hl0NcL hl0BrL
  simp only [hl0_H2_add2, hl0_H2_mul2, hl0_H2_smul2, hl0_H2_WNL, hl0_H2_LNL]
  generalize hl0WN (hl0H2 S X A) (hl0H2 U X A) (hl0H2 V X A) (hl0H2 D X A) = W
  generalize hl0LN (hl0H2 S X A) (hl0H2 U X A) (hl0H2 V X A) (hl0H2 D X A) = L
  ring

/-- The central atoms on lists, from lists for `x`, `α`, `β`: `S = x + 1`. -/
noncomputable def hl0cS (x : List (List ℝ)) : List (List ℝ) := hl0Add2 x [[1]]
/-- `SM = (x + 1)(35x + 13)`. -/
noncomputable def hl0cSM (x : List (List ℝ)) : List (List ℝ) :=
  hl0Mul2 (hl0cS x) (hl0Add2 (hl0Smul2 35 x) [[13]])
/-- `K = x² + 2x + α²`. -/
noncomputable def hl0cK (x a : List (List ℝ)) : List (List ℝ) :=
  hl0Add2 (hl0Mul2 x x) (hl0Add2 (hl0Smul2 2 x) (hl0Mul2 a a))
/-- `U = 3SM(β - 1) + (x - 1)²(β + 7x - 8)`. -/
noncomputable def hl0cU (x b : List (List ℝ)) : List (List ℝ) :=
  hl0Add2 (hl0Smul2 3 (hl0Mul2 (hl0cSM x) (hl0Add2 b [[-1]])))
    (hl0Mul2 (hl0Mul2 (hl0Add2 x [[-1]]) (hl0Add2 x [[-1]])) (hl0Add2 b (hl0Add2 (hl0Smul2 7 x) [[-8]])))
/-- `V = 4SM(β - 1)`. -/
noncomputable def hl0cV (x b : List (List ℝ)) : List (List ℝ) :=
  hl0Smul2 4 (hl0Mul2 (hl0cSM x) (hl0Add2 b [[-1]]))
/-- `D = α² + 2αβ + 1 + 2x - 2βx`. -/
noncomputable def hl0cD (x a b : List (List ℝ)) : List (List ℝ) :=
  hl0Add2 (hl0Mul2 a a) (hl0Add2 (hl0Smul2 2 (hl0Mul2 a b)) (hl0Add2 [[1]]
    (hl0Add2 (hl0Smul2 2 x) (hl0Smul2 (-2) (hl0Mul2 b x)))))

/-- **A central face numerator on lists** with coefficients `e`, `c` (computed from the source
formula, never printed). -/
noncomputable def hl0FNc (e₁ e₂ e₃ e₄ c₁ c₂ c₃ c₄ c₅ c₆ : ℝ) (x a b : List (List ℝ)) :
    List (List ℝ) :=
  hl0NcL e₁ e₂ e₃ e₄ c₁ c₂ c₃ c₄ c₅ c₆ (hl0cS x) (hl0cK x a) a (hl0Add2 a b) (hl0cU x b) (hl0cV x b)
    (hl0cD x a b)

theorem hl0_H2_atoms (x a b : List (List ℝ)) (X A : ℝ) :
    hl0H2 (hl0cS x) X A = hl0H2 x X A + 1 ∧
    hl0H2 (hl0cK x a) X A = hl0H2 x X A ^ 2 + 2 * hl0H2 x X A + hl0H2 a X A ^ 2 ∧
    hl0H2 (hl0Add2 a b) X A = hl0H2 a X A + hl0H2 b X A ∧
    hl0H2 (hl0cU x b) X A = hl0Uc (hl0H2 x X A) (hl0H2 b X A) ∧
    hl0H2 (hl0cV x b) X A = hl0Vc (hl0H2 x X A) (hl0H2 b X A) ∧
    hl0H2 (hl0cD x a b) X A = hsDg (hl0H2 x X A) (hl0H2 b X A) (hl0H2 a X A) := by
  unfold hl0cU hl0cV hl0cD hl0cK hl0cSM hl0cS hl0Uc hl0Vc hsDg
  simp only [hl0_H2_add2, hl0_H2_mul2, hl0_H2_smul2, hl0_H2_single, lrhHorner]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> (try trivial) <;> ring

theorem hl0_H2_FN2 (x a b : List (List ℝ)) (X A : ℝ) :
    hl0H2 (hl0FNc 72 180 0 72 72 (-180) 151 72 0 (-72) x a b) X A =
      hl0N2 (hl0H2 x X A + 1) (hl0H2 x X A ^ 2 + 2 * hl0H2 x X A + hl0H2 a X A ^ 2) (hl0H2 a X A)
        (hl0H2 a X A + hl0H2 b X A) (hl0Uc (hl0H2 x X A) (hl0H2 b X A))
        (hl0Vc (hl0H2 x X A) (hl0H2 b X A)) (hsDg (hl0H2 x X A) (hl0H2 b X A) (hl0H2 a X A)) := by
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := hl0_H2_atoms x a b X A
  unfold hl0FNc
  rw [hl0_H2_NcL, h1, h2, h3, h4, h5, h6]
  unfold hl0N2
  generalize hl0WN _ _ _ _ = W
  generalize hl0LN _ _ _ _ = L
  ring

theorem hl0_H2_FNT (x a b : List (List ℝ)) (X A : ℝ) :
    hl0H2 (hl0FNc 8 4 8 8 8 (-8) (-5) 8 8 (-8) x a b) X A =
      hl0NT (hl0H2 x X A + 1) (hl0H2 x X A ^ 2 + 2 * hl0H2 x X A + hl0H2 a X A ^ 2) (hl0H2 a X A)
        (hl0H2 a X A + hl0H2 b X A) (hl0Uc (hl0H2 x X A) (hl0H2 b X A))
        (hl0Vc (hl0H2 x X A) (hl0H2 b X A)) (hsDg (hl0H2 x X A) (hl0H2 b X A) (hl0H2 a X A)) := by
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := hl0_H2_atoms x a b X A
  unfold hl0FNc
  rw [hl0_H2_NcL, h1, h2, h3, h4, h5, h6]
  unfold hl0NT
  generalize hl0WN _ _ _ _ = W
  generalize hl0LN _ _ _ _ = L
  ring

theorem hl0_H2_FN8 (x a b : List (List ℝ)) (X A : ℝ) :
    hl0H2 (hl0FNc 72 36 64 72 72 (-81) (-37) 72 64 (-72) x a b) X A =
      hl0N8 (hl0H2 x X A + 1) (hl0H2 x X A ^ 2 + 2 * hl0H2 x X A + hl0H2 a X A ^ 2) (hl0H2 a X A)
        (hl0H2 a X A + hl0H2 b X A) (hl0Uc (hl0H2 x X A) (hl0H2 b X A))
        (hl0Vc (hl0H2 x X A) (hl0H2 b X A)) (hsDg (hl0H2 x X A) (hl0H2 b X A) (hl0H2 a X A)) := by
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := hl0_H2_atoms x a b X A
  unfold hl0FNc
  rw [hl0_H2_NcL, h1, h2, h3, h4, h5, h6]
  unfold hl0N8
  generalize hl0WN _ _ _ _ = W
  generalize hl0LN _ _ _ _ = L
  ring

/-- The list for `x + c(α - 1) = l + X + cA` in `X = x - l`, `A = α - 1`. -/
theorem hl0_H2_lin (l c x a : ℝ) :
    hl0H2 [[l, c], [1]] (x - l) (a - 1) = x + c * (a - 1) := by
  simp [hl0H2, lrhHorner]; ring

end SmoothedOctagon
