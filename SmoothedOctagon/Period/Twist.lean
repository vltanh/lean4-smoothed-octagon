module

public import SmoothedOctagon.Period.Defs

/-!
# The twisted extension, rebasing and relabeling

Basic facts about `twistedFrame`, `twistedState` and `rebaseFrame` (`Period/Defs.lean`), and about
the relabeling `(g, X) ↦ (C⁻¹ g C, C⁻¹ X C)` by `C = R^r`. Throughout `n = ⌊t / T⌋₊`.

## Main API

Powers of `R`:
* `R_inv_eq_pow_five`, `R_pow_mul_inv`, `R_pow_inv_mul`, `det_R_pow`, `commute_R_pow_inv`,
  `conj_R_pow_J`: `R⁻¹ = R⁵`, `Rⁿ (Rⁿ)⁻¹ = (Rⁿ)⁻¹ Rⁿ = 1`, `det Rⁿ = 1`, `R` commutes with `(Rⁿ)⁻¹`,
  `(Rⁿ)⁻¹ J Rⁿ = J`.

Global twist relations:
* `twist_add_nat_mul`: `F (t + T) = A F(t) B` for every `t` iterates to `F (t + nT) = Aⁿ F(t) Bⁿ`;
  `frame_add_nat_mul`, `state_add_nat_mul` are the cases `(A, B) = (1, R), (R⁻¹, R)`.
* `eq_of_eqOn_Ico_of_twist`: two curves with the same frame twist `F (t + T) = F t * R` that agree
  on `[0, T)` agree on `ℝ`.
* `twistedFrame_eq_of_twist`, `twistedState_eq_of_twist`, `rebaseFrame_eq_of_twist`: a trajectory
  already twisted on all of `ℝ` is its own twisted extension, and `ĝ(t) = g(s)⁻¹ g(s + t)`.

The twisted extension of a trajectory on `[0, T]` (no hypothesis on `ℝ`):
* values: `twistedFrame_of_mem_Ico`, `twistedFrame_period`, `twistedFrame_of_mem_Icc` and the
  `twistedState_*` analogues (`G = g`, `Y = X` on `[0, T]` under the twisted endpoint conditions);
* twist relations for `t ≥ 0`: `twistedFrame_add_period`, `twistedState_add_period`,
  `twistedFrame_add_nat_mul`, `twistedState_add_nat_mul`;
* `twistedFrame_det`, `twistedState_isStarState`: `det G = 1` and `Y` is a star state on `[0, ∞)`;
* the rebased frame: `rebaseFrame_zero`, `rebaseFrame_period`, `rebaseFrame_det`, and
  `twistedState_rebase_period` (`X̂(T) = R⁻¹ X̂(0) R` for `X̂(t) = Y(s + t)`).

Cost:
* `traceForm_J_conj_R_pow`: `⟨J, (Rⁿ)⁻¹ X Rⁿ⟩ = ⟨J, X⟩` since `RJ = JR`;
* `reinhardtCost_relabel`: relabeling by `R^r` preserves the cost;
* `reinhardtCost_rebase`: rebasing at `s ≥ 0` preserves the cost when `X(T) = R⁻¹ X(0) R`.

Controls:
* `relabelControl v = (v₂, v₀, v₁)`, so `(relabelⁿ v)_j = v_{j-n}` (`relabelControl_iterate_apply`),
  `relabel e_i = e_{i+1}` (`relabelControl_vertex`, `relabelControl_iterate_vertex`); it preserves the
  simplex and measurability, and `(Rⁿ)⁻¹ Z_v Rⁿ = Z_{relabelⁿ v}` (`conj_R_pow_controlMatrix`), so the
  state field `[P(v, S), S]` is equivariant (`conj_R_pow_stateField`).
* `twistedControl T u t = relabelⁿ (u(t - nT))`, the control on later periods:
  `measurable_twistedControl`, `twistedControl_mem`, `twistedControl_of_mem_Ico`,
  `twistedControl_add_period`.

Integral curves (`IsIntegralCurve`, Carathéodory form):
* `isIntegralCurve_mul_mul` (multiply by constant matrices on both sides), `isIntegralCurve_congr`,
  `isIntegralCurve_comp_add_left` (restart on a window `[s, s + T] ⊆ [0, L]`);
* `isIntegralCurve_poly_pw`: an integral curve on `[0, T]` with `f(T) = A f(0) B` extends by
  `Aⁿ f(t - nT) Bⁿ` (upstream `poly_pw`) to an integral curve on `[0, NT]` for every `N`;
  `twistedFrame_eq_poly_pw`, `twistedState_eq_poly_pw`, `twistedFrame_mul_twistedState`,
  `twistedState_stateField` identify the twisted frame, state and velocities with `poly_pw`.

Admissibility:
* `isReinhardtAdmissible_rebase`: rebasing an admissible `(T, u, g, X)` at any `s ≥ 0` gives the
  admissible `(T, twistedControl T u (s + ·), rebaseFrame T g s, twistedState T X (s + ·))`;
* `isReinhardtAdmissible_relabel`: relabeling by `R^r` gives the admissible
  `(T, relabelʳ ∘ u, (R^r)⁻¹ g R^r, (R^r)⁻¹ X R^r)`.
-/

@[expose] public section

namespace SmoothedOctagon

open SmoothedPolygons MeasureTheory Set

/-! ### Powers of `R` -/

/-- `R R⁵ = 1`. -/
theorem R_mul_pow_five : R * R ^ 5 = 1 := by
  rw [← pow_succ']
  exact oct_R_pow_six

/-- `R⁻¹ = R⁵`. -/
theorem R_inv_eq_pow_five : R⁻¹ = R ^ 5 :=
  Matrix.inv_eq_right_inv R_mul_pow_five

theorem R_pow_mul_inv (n : ℕ) : R ^ n * (R ^ n)⁻¹ = 1 := by
  rw [← Matrix.inv_pow']
  exact poly_Rpow_mul_Rinvpow n

theorem R_pow_inv_mul (n : ℕ) : (R ^ n)⁻¹ * R ^ n = 1 := by
  rw [← Matrix.inv_pow']
  exact poly_Rinvpow_mul_Rpow n

theorem det_R_pow (n : ℕ) : (R ^ n).det = 1 := by
  rw [Matrix.det_pow, poly_det_R, one_pow]

/-- `(Rⁿ)⁻¹ = R^{5n}`. -/
theorem R_pow_inv_eq (n : ℕ) : (R ^ n)⁻¹ = R ^ (5 * n) := by
  rw [← Matrix.inv_pow', R_inv_eq_pow_five, ← pow_mul]

theorem commute_R_pow_inv (n : ℕ) : Commute R (R ^ n)⁻¹ := by
  rw [R_pow_inv_eq]
  exact (Commute.refl R).pow_right _

theorem commute_R_pow (n : ℕ) : Commute R (R ^ n) :=
  (Commute.refl R).pow_right _

/-- `(Rⁿ)⁻¹ J Rⁿ = J`. -/
theorem conj_R_pow_J (n : ℕ) : (R ^ n)⁻¹ * J * R ^ n = J := by
  rw [← Matrix.inv_pow']
  exact poly_conj_pow_J n

/-! ### Twist relations on all of `ℝ` -/

/-- A twist relation `F (t + T) = A F(t) B` for every `t` iterates to `F (t + nT) = Aⁿ F(t) Bⁿ`. -/
theorem twist_add_nat_mul {F : ℝ → Mat2} {T : ℝ} {A B : Mat2}
    (h : ∀ t, F (t + T) = A * F t * B) (n : ℕ) (t : ℝ) :
    F (t + n * T) = A ^ n * F t * B ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [show t + ((n + 1 : ℕ) : ℝ) * T = (t + n * T) + T by push_cast; ring, h, ih,
      pow_succ' A, pow_succ B]
    simp only [Matrix.mul_assoc]

/-- The frame twist `g (t + T) = g(t) R` iterates. -/
theorem frame_add_nat_mul {g : ℝ → Mat2} {T : ℝ} (h : ∀ t, g (t + T) = g t * R) (n : ℕ)
    (t : ℝ) : g (t + n * T) = g t * R ^ n := by
  have := twist_add_nat_mul (F := g) (A := 1) (B := R) (fun t ↦ by rw [h, Matrix.one_mul]) n t
  rwa [one_pow, Matrix.one_mul] at this

/-- The state twist `X (t + T) = R⁻¹ X(t) R` iterates. -/
theorem state_add_nat_mul {X : ℝ → Mat2} {T : ℝ} (h : ∀ t, X (t + T) = R⁻¹ * X t * R) (n : ℕ)
    (t : ℝ) : X (t + n * T) = (R ^ n)⁻¹ * X t * R ^ n := by
  rw [← Matrix.inv_pow']
  exact twist_add_nat_mul h n t

/-- Two curves with the frame twist `F (t + T) = F(t) R` that agree on `[0, T)` agree on `ℝ`. -/
theorem eq_of_eqOn_Ico_of_twist {F₁ F₂ : ℝ → Mat2} {T : ℝ} (hT : 0 < T)
    (h₁ : ∀ t, F₁ (t + T) = F₁ t * R) (h₂ : ∀ t, F₂ (t + T) = F₂ t * R)
    (h : ∀ t ∈ Ico 0 T, F₁ t = F₂ t) : F₁ = F₂ := by
  have hstep : ∀ x, F₁ x = F₂ x ↔ F₁ (x + T) = F₂ (x + T) := by
    intro x
    rw [h₁, h₂]
    constructor
    · intro hx; rw [hx]
    · intro hx
      have : F₁ x * R * R ^ 5 = F₂ x * R * R ^ 5 := by rw [hx]
      rwa [Matrix.mul_assoc, Matrix.mul_assoc, R_mul_pow_five, Matrix.mul_one,
        Matrix.mul_one] at this
  have hint : ∀ n : ℤ, ∀ x ∈ Ico 0 T, F₁ (x + n * T) = F₂ (x + n * T) := by
    intro n x hx
    induction n using Int.induction_on with
    | zero => simpa using h x hx
    | succ n ih =>
      rw [show x + ((n + 1 : ℤ) : ℝ) * T = (x + n * T) + T by push_cast; ring]
      exact (hstep _).1 ih
    | pred n ih =>
      rw [hstep, show x + ((-(n : ℤ) - 1 : ℤ) : ℝ) * T + T = x + ((-(n : ℤ) : ℤ) : ℝ) * T by
        push_cast; ring]
      exact ih
  funext t
  have hmem : toIcoMod hT 0 t ∈ Ico 0 T := by
    simpa using toIcoMod_mem_Ico hT 0 t
  have := hint (toIcoDiv hT 0 t) _ hmem
  rwa [← zsmul_eq_mul, toIcoMod_add_toIcoDiv_zsmul] at this

/-- A frame already twisted on `ℝ` is its own twisted extension. -/
theorem twistedFrame_eq_of_twist {g : ℝ → Mat2} {T : ℝ} (h : ∀ t, g (t + T) = g t * R)
    (t : ℝ) : twistedFrame T g t = g t := by
  rw [twistedFrame, ← frame_add_nat_mul h, sub_add_cancel]

/-- A state already twisted on `ℝ` is its own twisted extension. -/
theorem twistedState_eq_of_twist {X : ℝ → Mat2} {T : ℝ} (h : ∀ t, X (t + T) = R⁻¹ * X t * R)
    (t : ℝ) : twistedState T X t = X t := by
  rw [twistedState, ← state_add_nat_mul h, sub_add_cancel]

/-- For a frame already twisted on `ℝ`, the rebased frame is `g(s)⁻¹ g(s + t)`. -/
theorem rebaseFrame_eq_of_twist {g : ℝ → Mat2} {T : ℝ} (h : ∀ t, g (t + T) = g t * R)
    (s t : ℝ) : rebaseFrame T g s t = (g s)⁻¹ * g (s + t) := by
  rw [rebaseFrame, twistedFrame_eq_of_twist h, twistedFrame_eq_of_twist h]

/-! ### The twisted extension of a trajectory on `[0, T]` -/

section Extension

variable {T : ℝ} {g X : ℝ → Mat2}

theorem floor_div_eq_zero_of_mem_Ico {t : ℝ} (hT : 0 < T) (ht : t ∈ Ico 0 T) :
    ⌊t / T⌋₊ = 0 :=
  Nat.floor_eq_zero.mpr ((div_lt_one hT).mpr ht.2)

theorem floor_div_add_period {t : ℝ} (hT : 0 < T) (ht : 0 ≤ t) :
    ⌊(t + T) / T⌋₊ = ⌊t / T⌋₊ + 1 := by
  rw [add_div, div_self hT.ne', Nat.floor_add_one (div_nonneg ht hT.le)]

/-- The reduced time `t - ⌊t/T⌋₊ T` lies in `[0, T)` for `t ≥ 0`. -/
theorem sub_floor_mul_mem_Ico {t : ℝ} (hT : 0 < T) (ht : 0 ≤ t) :
    t - ⌊t / T⌋₊ * T ∈ Ico 0 T := by
  obtain ⟨h1, h2⟩ := poly_floor_mem hT ht
  constructor <;> linarith

theorem twistedFrame_of_mem_Ico {t : ℝ} (hT : 0 < T) (ht : t ∈ Ico 0 T) :
    twistedFrame T g t = g t := by
  simp [twistedFrame, floor_div_eq_zero_of_mem_Ico hT ht]

theorem twistedState_of_mem_Ico {t : ℝ} (hT : 0 < T) (ht : t ∈ Ico 0 T) :
    twistedState T X t = X t := by
  simp [twistedState, floor_div_eq_zero_of_mem_Ico hT ht]

theorem twistedFrame_period (hT : 0 < T) : twistedFrame T g T = g 0 * R := by
  simp [twistedFrame, div_self hT.ne']

theorem twistedState_period (hT : 0 < T) : twistedState T X T = R⁻¹ * X 0 * R := by
  simp [twistedState, div_self hT.ne']

/-- Under `g(T) = g(0) R` (for instance `g(0) = 1`, `g(T) = R`), the twisted frame is `g` on
`[0, T]`. -/
theorem twistedFrame_of_mem_Icc {t : ℝ} (hT : 0 < T) (hg : g T = g 0 * R) (ht : t ∈ Icc 0 T) :
    twistedFrame T g t = g t := by
  rcases ht.2.lt_or_eq with h | h
  · exact twistedFrame_of_mem_Ico hT ⟨ht.1, h⟩
  · rw [h, twistedFrame_period hT, hg]

/-- Under `X(T) = R⁻¹ X(0) R`, the twisted state is `X` on `[0, T]`. -/
theorem twistedState_of_mem_Icc {t : ℝ} (hT : 0 < T) (hX : X T = R⁻¹ * X 0 * R)
    (ht : t ∈ Icc 0 T) : twistedState T X t = X t := by
  rcases ht.2.lt_or_eq with h | h
  · exact twistedState_of_mem_Ico hT ⟨ht.1, h⟩
  · rw [h, twistedState_period hT, hX]

/-- The frame twist `G(t + T) = G(t) R` for `t ≥ 0`. -/
theorem twistedFrame_add_period {t : ℝ} (hT : 0 < T) (ht : 0 ≤ t) :
    twistedFrame T g (t + T) = twistedFrame T g t * R := by
  rw [twistedFrame, twistedFrame, floor_div_add_period hT ht, pow_succ, ← Matrix.mul_assoc,
    show t + T - ((⌊t / T⌋₊ + 1 : ℕ) : ℝ) * T = t - ⌊t / T⌋₊ * T by push_cast; ring]

/-- The state twist `Y(t + T) = R⁻¹ Y(t) R` for `t ≥ 0`. -/
theorem twistedState_add_period {t : ℝ} (hT : 0 < T) (ht : 0 ≤ t) :
    twistedState T X (t + T) = R⁻¹ * twistedState T X t * R := by
  rw [twistedState, twistedState, floor_div_add_period hT ht, pow_succ, Matrix.mul_inv_rev,
    show t + T - ((⌊t / T⌋₊ + 1 : ℕ) : ℝ) * T = t - ⌊t / T⌋₊ * T by push_cast; ring]
  simp only [Matrix.mul_assoc]

theorem twistedFrame_add_nat_mul {t : ℝ} (hT : 0 < T) (ht : 0 ≤ t) (n : ℕ) :
    twistedFrame T g (t + n * T) = twistedFrame T g t * R ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [show t + ((n + 1 : ℕ) : ℝ) * T = (t + n * T) + T by push_cast; ring,
      twistedFrame_add_period hT (by positivity), ih, pow_succ, Matrix.mul_assoc]

theorem twistedState_add_nat_mul {t : ℝ} (hT : 0 < T) (ht : 0 ≤ t) (n : ℕ) :
    twistedState T X (t + n * T) = (R ^ n)⁻¹ * twistedState T X t * R ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [show t + ((n + 1 : ℕ) : ℝ) * T = (t + n * T) + T by push_cast; ring,
      twistedState_add_period hT (by positivity), ih, pow_succ, Matrix.mul_inv_rev]
    simp only [Matrix.mul_assoc]

/-- `det G = 1` on `[0, ∞)` when `det g = 1` on `[0, T]`. -/
theorem twistedFrame_det {t : ℝ} (hT : 0 < T) (hdet : ∀ t ∈ Icc 0 T, (g t).det = 1)
    (ht : 0 ≤ t) : (twistedFrame T g t).det = 1 := by
  rw [twistedFrame, Matrix.det_mul, det_R_pow, mul_one]
  exact hdet _ (Ico_subset_Icc_self (sub_floor_mul_mem_Ico hT ht))

/-- `Y` is a star state on `[0, ∞)` when `X` is one on `[0, T]`. -/
theorem twistedState_isStarState {t : ℝ} (hT : 0 < T)
    (hstar : ∀ t ∈ Icc 0 T, IsStarState (X t)) (ht : 0 ≤ t) :
    IsStarState (twistedState T X t) := by
  rw [twistedState, ← Matrix.inv_pow']
  exact poly_isStarState_conj_pow _ (hstar _ (Ico_subset_Icc_self (sub_floor_mul_mem_Ico hT ht)))

/-- The rebased frame starts at the identity. -/
theorem rebaseFrame_zero {s : ℝ} (hdet : IsUnit (twistedFrame T g s).det) :
    rebaseFrame T g s 0 = 1 := by
  rw [rebaseFrame, add_zero, Matrix.nonsing_inv_mul _ hdet]

/-- The rebased frame ends at `R`. -/
theorem rebaseFrame_period {s : ℝ} (hT : 0 < T) (hs : 0 ≤ s)
    (hdet : IsUnit (twistedFrame T g s).det) : rebaseFrame T g s T = R := by
  rw [rebaseFrame, twistedFrame_add_period hT hs, ← Matrix.mul_assoc,
    Matrix.nonsing_inv_mul _ hdet, Matrix.one_mul]

/-- The rebased frame has determinant one on `[0, ∞)`. -/
theorem rebaseFrame_det {s t : ℝ} (hT : 0 < T) (hdet : ∀ t ∈ Icc 0 T, (g t).det = 1)
    (hs : 0 ≤ s) (ht : 0 ≤ t) : (rebaseFrame T g s t).det = 1 := by
  rw [rebaseFrame, Matrix.det_mul, Matrix.det_nonsing_inv, twistedFrame_det hT hdet hs,
    twistedFrame_det hT hdet (by positivity), Ring.inverse_one, one_mul]

/-- The rebased state `X̂(t) = Y(s + t)` satisfies the twisted endpoint condition. -/
theorem twistedState_rebase_period {s : ℝ} (hT : 0 < T) (hs : 0 ≤ s) :
    twistedState T X (s + T) = R⁻¹ * twistedState T X (s + 0) * R := by
  rw [add_zero, twistedState_add_period hT hs]

end Extension

/-! ### Cost -/

/-- `⟨J, (Rⁿ)⁻¹ X Rⁿ⟩ = ⟨J, X⟩`, since `J` commutes with `R`. -/
theorem traceForm_J_conj_R_pow (n : ℕ) (X : Mat2) :
    traceForm J ((R ^ n)⁻¹ * X * R ^ n) = traceForm J X := by
  have h := poly_traceForm_conj (R_pow_mul_inv n) J X
  rwa [conj_R_pow_J] at h

/-- Relabeling by `C = R^r` preserves the cost. -/
theorem reinhardtCost_relabel (T : ℝ) (X : ℝ → Mat2) (r : ℕ) :
    reinhardtCost T (fun t ↦ (R ^ r)⁻¹ * X t * R ^ r) = reinhardtCost T X := by
  simp only [reinhardtCost, traceForm_J_conj_R_pow]

/-- The cost density of the twisted state is the periodic extension of that of `X` on `[0, ∞)`. -/
private theorem traceForm_twistedState {T : ℝ} {X : ℝ → Mat2} (hT : 0 < T) {t : ℝ}
    (ht : 0 ≤ t) : traceForm J (twistedState T X t) = traceForm J (X (toIcoMod hT 0 t)) := by
  rw [twistedState, traceForm_J_conj_R_pow]
  congr 2
  symm
  rw [toIcoMod_eq_iff]
  refine ⟨by simpa using sub_floor_mul_mem_Ico hT ht, (⌊t / T⌋₊ : ℤ), ?_⟩
  rw [zsmul_eq_mul]
  push_cast
  ring

/-- Rebasing at `s ≥ 0` preserves the cost: the cost density of the twisted state has period `T`
(`J` commutes with `R`). -/
theorem reinhardtCost_rebase {T s : ℝ} {X : ℝ → Mat2} (hT : 0 < T) (hs : 0 ≤ s)
    (hXT : X T = R⁻¹ * X 0 * R) :
    reinhardtCost T (fun t ↦ twistedState T X (s + t)) = reinhardtCost T X := by
  unfold reinhardtCost
  congr 1
  set φ : ℝ → ℝ := fun t ↦ traceForm J (X (toIcoMod hT 0 t)) with hφ
  have hper : Function.Periodic φ T := fun t ↦ by simp only [hφ, toIcoMod_add_right]
  have h1 : ∫ t in (0 : ℝ)..T, traceForm J (twistedState T X (s + t)) =
      ∫ t in s..s + T, φ t := by
    rw [intervalIntegral.integral_comp_add_left (fun x ↦ traceForm J (twistedState T X x)) s,
      add_zero]
    refine intervalIntegral.integral_congr fun t ht ↦ ?_
    rw [uIcc_of_le (by linarith)] at ht
    exact traceForm_twistedState hT (hs.trans ht.1)
  have h2 : ∫ t in (0 : ℝ)..T, φ t = ∫ t in (0 : ℝ)..T, traceForm J (X t) := by
    refine intervalIntegral.integral_congr fun t ht ↦ ?_
    rw [uIcc_of_le hT.le] at ht
    simp only [hφ]
    rcases ht.2.lt_or_eq with h | h
    · rw [(toIcoMod_eq_self hT).mpr ⟨ht.1, by simpa using h⟩]
    · subst h
      rw [show toIcoMod hT 0 t = 0 by
        rw [toIcoMod_eq_iff]; exact ⟨⟨le_rfl, by simpa using hT⟩, 1, by simp⟩, hXT,
        ← traceForm_J_conj_R_pow 1 (X 0), pow_one]
  rw [h1, hper.intervalIntegral_add_eq s 0, zero_add, h2]

/-! ### Relabeling of controls -/

/-- The relabeling of a control by the rotation `R`: `(relabel v)_j = v_{j-1}`, so that the vertex
`e_i` becomes `e_{i+1}` and `R⁻¹ Z_v R = Z_{relabel v}`. -/
def relabelControl (v : Fin 3 → ℝ) : Fin 3 → ℝ := fun j ↦ v (j + 2)

@[simp] theorem relabelControl_zero (v : Fin 3 → ℝ) : relabelControl v 0 = v 2 := rfl

@[simp] theorem relabelControl_one (v : Fin 3 → ℝ) : relabelControl v 1 = v 0 := rfl

@[simp] theorem relabelControl_two (v : Fin 3 → ℝ) : relabelControl v 2 = v 1 := rfl

theorem relabelControl_vertex (i : Fin 3) : relabelControl (vertex i) = vertex (i + 1) := by
  funext j
  fin_cases i <;> fin_cases j <;> simp [relabelControl, vertex]

/-- `relabelⁿ v` reads `v` with its labels shifted by `n`: `(relabelⁿ v)_j = v_{j - n}`. -/
theorem relabelControl_iterate_apply (n : ℕ) (v : Fin 3 → ℝ) (j : Fin 3) :
    relabelControl^[n] v j = v (j - Fin.ofNat 3 n) := by
  induction n generalizing j with
  | zero => simp
  | succ n ih =>
    rw [Function.iterate_succ_apply', relabelControl, ih]
    congr 1
    ext
    simp [Fin.val_add, Fin.sub_def]
    omega

theorem relabelControl_iterate_vertex (n : ℕ) (i : Fin 3) :
    relabelControl^[n] (vertex i) = vertex (i + Fin.ofNat 3 n) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Function.iterate_succ_apply', ih, relabelControl_vertex]
    congr 1
    ext
    simp [Fin.val_add]
    omega

theorem relabelControl_mem {v : Fin 3 → ℝ} (hv : v ∈ controlSimplex) :
    relabelControl v ∈ controlSimplex := by
  refine ⟨fun i ↦ hv.1 _, ?_⟩
  simp only [relabelControl_zero, relabelControl_one, relabelControl_two]
  linarith [hv.2]

theorem relabelControl_iterate_mem {v : Fin 3 → ℝ} (hv : v ∈ controlSimplex) (n : ℕ) :
    relabelControl^[n] v ∈ controlSimplex := by
  induction n with
  | zero => exact hv
  | succ n ih =>
    rw [Function.iterate_succ_apply']
    exact relabelControl_mem ih

theorem measurable_relabelControl : Measurable relabelControl :=
  Measurable.of_eval fun j ↦ measurable_pi_apply (j + 2)

/-- `R⁻¹ Z_v R = Z_{relabel v}`. -/
theorem conj_R_controlMatrix (v : Fin 3 → ℝ) :
    R⁻¹ * controlMatrix v * R = controlMatrix (relabelControl v) := by
  rw [poly_R_inv]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [controlMatrix, R, Matrix.mul_apply, Fin.sum_univ_two] <;>
    field_simp <;> ring_nf <;> simp <;> ring_nf

/-- `(Rⁿ)⁻¹ Z_v Rⁿ = Z_{relabelⁿ v}`. -/
theorem conj_R_pow_controlMatrix (n : ℕ) (v : Fin 3 → ℝ) :
    (R ^ n)⁻¹ * controlMatrix v * R ^ n = controlMatrix (relabelControl^[n] v) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ, Matrix.mul_inv_rev, Function.iterate_succ_apply', ← conj_R_controlMatrix, ← ih]
    simp only [Matrix.mul_assoc]

/-- The state vector field is equivariant: `(Rⁿ)⁻¹ [P(v, S), S] Rⁿ = [P(v', S'), S']` with
`v' = relabelⁿ v` and `S' = (Rⁿ)⁻¹ S Rⁿ`. -/
theorem conj_R_pow_stateField (n : ℕ) (v : Fin 3 → ℝ) (S : Mat2) :
    (R ^ n)⁻¹ * (controlP v S * S - S * controlP v S) * R ^ n =
      controlP (relabelControl^[n] v) ((R ^ n)⁻¹ * S * R ^ n) * ((R ^ n)⁻¹ * S * R ^ n) -
        ((R ^ n)⁻¹ * S * R ^ n) * controlP (relabelControl^[n] v) ((R ^ n)⁻¹ * S * R ^ n) := by
  rw [poly_conj_bracket (R_pow_mul_inv n),
    poly_controlP_conj (R_pow_mul_inv n) (conj_R_pow_controlMatrix n v)]

/-! ### Integral curves -/

/-- The entries of `A M B` are linear in the entries of `M`. -/
private theorem mul_mul_apply (A M B : Mat2) (i j : Fin 2) :
    (A * M * B) i j = A i 0 * B 0 j * M 0 0 + A i 0 * B 1 j * M 0 1 +
      A i 1 * B 0 j * M 1 0 + A i 1 * B 1 j * M 1 1 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_two]
  ring

/-- Multiplying an integral curve and its velocity on both sides by constant matrices gives an
integral curve. -/
theorem isIntegralCurve_mul_mul {f v : ℝ → Mat2} {T : ℝ} (h : IsIntegralCurve f v T)
    (A B : Mat2) : IsIntegralCurve (fun t ↦ A * f t * B) (fun t ↦ A * v t * B) T := by
  intro i j
  have hI : ∀ k l, IntervalIntegrable (fun s ↦ v s k l) volume 0 T := fun k l ↦ (h k l).1
  simp only [mul_mul_apply]
  refine ⟨((((hI 0 0).const_mul _).add ((hI 0 1).const_mul _)).add
    ((hI 1 0).const_mul _)).add ((hI 1 1).const_mul _), fun t ht ↦ ?_⟩
  have hI' : ∀ k l, IntervalIntegrable (fun s ↦ v s k l) volume 0 t := fun k l ↦
    (hI k l).mono_set (by
      rw [uIcc_of_le ht.1, uIcc_of_le (ht.1.trans ht.2)]
      exact Icc_subset_Icc_right ht.2)
  have a := (hI' 0 0).const_mul (A i 0 * B 0 j)
  have b := (hI' 0 1).const_mul (A i 0 * B 1 j)
  have c := (hI' 1 0).const_mul (A i 1 * B 0 j)
  have d := (hI' 1 1).const_mul (A i 1 * B 1 j)
  rw [intervalIntegral.integral_add ((a.add b).add c) d, intervalIntegral.integral_add (a.add b) c,
    intervalIntegral.integral_add a b, intervalIntegral.integral_const_mul,
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
    intervalIntegral.integral_const_mul, (h 0 0).2 t ht, (h 0 1).2 t ht, (h 1 0).2 t ht,
    (h 1 1).2 t ht]
  ring

/-- An integral curve with pointwise equal curve and velocity. -/
theorem isIntegralCurve_congr {f f' v v' : ℝ → Mat2} {T : ℝ} (h : IsIntegralCurve f v T)
    (hf : ∀ t, f t = f' t) (hv : ∀ t, v t = v' t) : IsIntegralCurve f' v' T := by
  obtain rfl : f = f' := funext hf
  obtain rfl : v = v' := funext hv
  exact h

/-- An integral curve on `[0, L]` restricted to the window `[s, s + T] ⊆ [0, L]` and restarted at
`s`. -/
theorem isIntegralCurve_comp_add_left {f v : ℝ → Mat2} {L s T : ℝ} (h : IsIntegralCurve f v L)
    (hs : 0 ≤ s) (hT : 0 ≤ T) (hsT : s + T ≤ L) :
    IsIntegralCurve (fun t ↦ f (s + t)) (fun t ↦ v (s + t)) T := by
  intro i j
  obtain ⟨hint, heq⟩ := h i j
  have hsub : ∀ a b, 0 ≤ a → a ≤ b → b ≤ L →
      IntervalIntegrable (fun x ↦ v x i j) volume a b := fun a b ha hab hb ↦
    hint.mono_set (by
      rw [uIcc_of_le hab, uIcc_of_le (ha.trans (hab.trans hb))]
      exact Icc_subset_Icc ha hb)
  refine ⟨?_, fun t ht ↦ ?_⟩
  · have := (hsub s (s + T) hs (by linarith) hsT).comp_add_left s
    simpa using this
  · have e := intervalIntegral.integral_comp_add_left (fun x ↦ v x i j) s (a := 0) (b := t)
    simp only [add_zero] at e
    simp only [add_zero]
    rw [heq (s + t) ⟨by linarith [ht.1], by linarith [ht.2]⟩, heq s ⟨hs, by linarith⟩, e,
      add_assoc, intervalIntegral.integral_add_adjacent_intervals
        (hsub 0 s le_rfl hs (by linarith)) (hsub s (s + t) hs (by linarith [ht.1])
          (by linarith [ht.2]))]

/-- **Control on later periods.** An integral curve on `[0, T]` with `f(T) = A f(0) B` extends by
`f(t) = Aⁿ f(t - nT) Bⁿ`, `v(t) = Aⁿ v(t - nT) Bⁿ` (`n = ⌊t/T⌋₊`, upstream `poly_pw`) to an integral
curve on `[0, NT]` for every `N`. -/
theorem isIntegralCurve_poly_pw {f v : ℝ → Mat2} {T : ℝ} {A B : Mat2} (hT : 0 < T)
    (h : IsIntegralCurve f v T) (hglue : f T = A * f 0 * B) (N : ℕ) :
    IsIntegralCurve (poly_pw A B T f) (poly_pw A B T v) (N * T) := by
  induction N with
  | zero =>
    intro i j
    simp only [Nat.cast_zero, zero_mul]
    refine ⟨IntervalIntegrable.refl, fun t ht ↦ ?_⟩
    obtain rfl : t = 0 := le_antisymm ht.2 ht.1
    simp
  | succ N ih =>
    have hc := isIntegralCurve_mul_mul h (A ^ N) (B ^ N)
    have hNT : (0 : ℝ) ≤ N * T := by positivity
    have hN1 : ((N + 1 : ℕ) : ℝ) * T = N * T + T := by push_cast; ring
    have hpiece : EqOn (fun x ↦ (A ^ N * v (x - N * T) * B ^ N))
        (poly_pw A B T v) (Ico ((N : ℝ) * T) (N * T + T)) := fun x hx ↦
      (poly_pw_of_mem_Ico hT ⟨hx.1, by linarith [hx.2]⟩).symm
    intro i j
    obtain ⟨hint, heq⟩ := ih i j
    obtain ⟨hcint, hceq⟩ := hc i j
    have hint2 : IntervalIntegrable (fun x ↦ poly_pw A B T v x i j) volume (N * T)
        (N * T + T) := by
      have := hcint.comp_sub_right (N * T)
      rw [zero_add, add_comm T] at this
      refine this.congr_uIoo fun x hx ↦ ?_
      rw [uIoo_of_le (by linarith)] at hx
      exact congrArg (· i j) (hpiece ⟨hx.1.le, hx.2⟩)
    rw [hN1]
    refine ⟨hint.trans hint2, fun t ht ↦ ?_⟩
    rcases le_or_gt t (N * T) with htN | htN
    · exact heq t ⟨ht.1, htN⟩
    · have hFt : poly_pw A B T f t = A ^ N * f (t - N * T) * B ^ N :=
        poly_pw_of_mem_Icc hT hglue ⟨htN.le, by linarith [ht.2]⟩
      have hFa : poly_pw A B T f (N * T) = A ^ N * f 0 * B ^ N := by
        rw [poly_pw_of_mem_Icc hT hglue ⟨le_rfl, by linarith⟩, sub_self]
      have e1 : (A ^ N * f (t - N * T) * B ^ N) i j = (A ^ N * f 0 * B ^ N) i j +
          ∫ x in (0 : ℝ)..t - N * T, (A ^ N * v x * B ^ N) i j :=
        hceq (t - N * T) ⟨by linarith, by linarith [ht.2]⟩
      have e2 := heq (N * T) ⟨hNT, le_rfl⟩
      have e3 : ∫ x in (0 : ℝ)..t - N * T, (A ^ N * v x * B ^ N) i j =
          ∫ x in N * T..t, poly_pw A B T v x i j := by
        have e := intervalIntegral.integral_comp_sub_right
          (fun x ↦ (A ^ N * v x * B ^ N) i j) (N * T) (a := N * T) (b := t)
        simp only [sub_self] at e
        rw [← e]
        refine intervalIntegral.integral_congr_uIoo fun x hx ↦ ?_
        rw [uIoo_of_le htN.le] at hx
        exact congrArg (· i j) (hpiece ⟨hx.1.le, by linarith [hx.2, ht.2]⟩)
      have hint_b : IntervalIntegrable (fun x ↦ poly_pw A B T v x i j) volume (N * T) t :=
        hint2.mono_set (by
          rw [uIcc_of_le htN.le, uIcc_of_le (by linarith)]
          exact Icc_subset_Icc_right ht.2)
      rw [hFt, e1, ← hFa, e2, e3, add_assoc,
        intervalIntegral.integral_add_adjacent_intervals hint hint_b]

/-! ### The twisted control and rebasing -/

/-- The twisted extension of a control on `[0, T]`: `ũ(t) = relabelⁿ (u(t - nT))`, `n = ⌊t/T⌋₊`, so
that a vertex label rises by one per period (`i(t + T) = i(t) + 1`). -/
noncomputable def twistedControl (T : ℝ) (u : ℝ → Fin 3 → ℝ) (t : ℝ) : Fin 3 → ℝ :=
  relabelControl^[⌊t / T⌋₊] (u (t - ⌊t / T⌋₊ * T))

theorem measurable_twistedControl {T : ℝ} {u : ℝ → Fin 3 → ℝ} (hu : Measurable u) :
    Measurable (twistedControl T u) := by
  have h : Measurable fun p : ℝ × ℕ ↦ relabelControl^[p.2] (u (p.1 - p.2 * T)) :=
    measurable_from_prod_countable_left fun n ↦
      (measurable_relabelControl.iterate n).comp (hu.comp (measurable_id.sub_const ((n : ℝ) * T)))
  exact h.comp (measurable_id.prodMk (measurable_id.div_const T).nat_floor)

theorem twistedControl_mem {T : ℝ} {u : ℝ → Fin 3 → ℝ} {t : ℝ} (hT : 0 < T)
    (hu : ∀ t ∈ Icc 0 T, u t ∈ controlSimplex) (ht : 0 ≤ t) :
    twistedControl T u t ∈ controlSimplex :=
  relabelControl_iterate_mem (hu _ (Ico_subset_Icc_self (sub_floor_mul_mem_Ico hT ht))) _

theorem twistedControl_of_mem_Ico {T : ℝ} {u : ℝ → Fin 3 → ℝ} {t : ℝ} (hT : 0 < T)
    (ht : t ∈ Ico 0 T) : twistedControl T u t = u t := by
  simp [twistedControl, floor_div_eq_zero_of_mem_Ico hT ht]

/-- The twisted control relabels once per period, for `t ≥ 0`. -/
theorem twistedControl_add_period {T : ℝ} {u : ℝ → Fin 3 → ℝ} {t : ℝ} (hT : 0 < T)
    (ht : 0 ≤ t) : twistedControl T u (t + T) = relabelControl (twistedControl T u t) := by
  rw [twistedControl, twistedControl, floor_div_add_period hT ht, Function.iterate_succ_apply',
    show t + T - ((⌊t / T⌋₊ + 1 : ℕ) : ℝ) * T = t - ⌊t / T⌋₊ * T by push_cast; ring]

theorem twistedFrame_eq_poly_pw (T : ℝ) (g : ℝ → Mat2) : twistedFrame T g = poly_pw 1 R T g := by
  funext t
  simp [twistedFrame, poly_pw]

theorem twistedState_eq_poly_pw (T : ℝ) (X : ℝ → Mat2) :
    twistedState T X = poly_pw R⁻¹ R T X := by
  funext t
  simp [twistedState, poly_pw]

/-- The velocity of the twisted frame. -/
theorem twistedFrame_mul_twistedState (T : ℝ) (g X : ℝ → Mat2) (t : ℝ) :
    twistedFrame T g t * twistedState T X t = poly_pw 1 R T (fun t ↦ g t * X t) t := by
  simp only [twistedFrame, twistedState, poly_pw, one_pow, Matrix.one_mul, Matrix.mul_assoc]
  rw [← Matrix.mul_assoc (R ^ _) (R ^ _)⁻¹, R_pow_mul_inv, Matrix.one_mul]

/-- The velocity of the twisted state. -/
theorem twistedState_stateField (T : ℝ) (u : ℝ → Fin 3 → ℝ) (X : ℝ → Mat2) (t : ℝ) :
    controlP (twistedControl T u t) (twistedState T X t) * twistedState T X t -
        twistedState T X t * controlP (twistedControl T u t) (twistedState T X t) =
      poly_pw R⁻¹ R T (fun t ↦ controlP (u t) (X t) * X t - X t * controlP (u t) (X t)) t := by
  simp only [twistedControl, twistedState, poly_pw, Matrix.inv_pow']
  rw [conj_R_pow_stateField]

/-- **Rebasing preserves admissibility.** If `(T, u, g, X)` is admissible and `s ≥ 0`, the rebased
trajectory `(T, ũ(s + ·), ĝ, Y(s + ·))` with `ĝ(t) = G(s)⁻¹ G(s + t)` is admissible. -/
theorem isReinhardtAdmissible_rebase {T s : ℝ} {u : ℝ → Fin 3 → ℝ} {g X : ℝ → Mat2}
    (h : IsReinhardtAdmissible T u g X) (hs : 0 ≤ s) :
    IsReinhardtAdmissible T (fun t ↦ twistedControl T u (s + t)) (rebaseFrame T g s)
      (fun t ↦ twistedState T X (s + t)) := by
  obtain ⟨⟨hT, hu, hU, hdet, hg, hX⟩, hg0, hgT, hXT⟩ := h
  have hdet' : ∀ t ∈ Icc 0 T, (g t).det = 1 := fun t ht ↦ (hdet t ht).1
  have hstar : ∀ t ∈ Icc 0 T, IsStarState (X t) := fun t ht ↦ (hdet t ht).2
  have hunit : IsUnit (twistedFrame T g s).det := by
    rw [twistedFrame_det hT hdet' hs]
    exact isUnit_one
  have hglueg : g T = 1 * g 0 * R := by rw [hgT, hg0, Matrix.one_mul, Matrix.one_mul]
  obtain ⟨N, hN⟩ : ∃ N : ℕ, s + T ≤ N * T := by
    obtain ⟨N, hN⟩ := exists_nat_ge ((s + T) / T)
    exact ⟨N, (div_le_iff₀ hT).mp hN⟩
  have hG := isIntegralCurve_comp_add_left (isIntegralCurve_poly_pw hT hg hglueg N) hs hT.le hN
  have hY := isIntegralCurve_comp_add_left (isIntegralCurve_poly_pw hT hX hXT N) hs hT.le hN
  refine ⟨⟨hT, (measurable_twistedControl hu).comp (measurable_const_add s),
    fun t ht ↦ twistedControl_mem hT hU (by linarith [ht.1]),
    fun t ht ↦ ⟨rebaseFrame_det hT hdet' hs ht.1,
      twistedState_isStarState hT hstar (by linarith [ht.1])⟩, ?_, ?_⟩,
    rebaseFrame_zero hunit, rebaseFrame_period hT hs hunit, twistedState_rebase_period hT hs⟩
  · refine isIntegralCurve_congr (isIntegralCurve_mul_mul hG (twistedFrame T g s)⁻¹ 1)
      (fun t ↦ ?_) (fun t ↦ ?_)
    · rw [rebaseFrame, twistedFrame_eq_poly_pw, Matrix.mul_one]
    · rw [rebaseFrame, Matrix.mul_one, Matrix.mul_assoc, twistedFrame_mul_twistedState]
  · refine isIntegralCurve_congr hY (fun t ↦ ?_) (fun t ↦ ?_)
    · rw [twistedState_eq_poly_pw]
    · rw [twistedState_stateField]

/-! ### Relabeling preserves admissibility -/

theorem commute_R_inv_R_pow_inv (n : ℕ) : Commute R⁻¹ (R ^ n)⁻¹ := by
  rw [R_inv_eq_pow_five, R_pow_inv_eq]
  exact Commute.pow_pow (Commute.refl R) _ _

/-- **Relabeling preserves admissibility.** Conjugating an admissible trajectory by `C = R^r` and
relabeling its control by `relabelʳ` gives an admissible trajectory. -/
theorem isReinhardtAdmissible_relabel {T : ℝ} {u : ℝ → Fin 3 → ℝ} {g X : ℝ → Mat2}
    (h : IsReinhardtAdmissible T u g X) (r : ℕ) :
    IsReinhardtAdmissible T (fun t ↦ relabelControl^[r] (u t))
      (fun t ↦ (R ^ r)⁻¹ * g t * R ^ r) (fun t ↦ (R ^ r)⁻¹ * X t * R ^ r) := by
  obtain ⟨⟨hT, hu, hU, hdet, hg, hX⟩, hg0, hgT, hXT⟩ := h
  refine ⟨⟨hT, (measurable_relabelControl.iterate r).comp hu,
    fun t ht ↦ relabelControl_iterate_mem (hU t ht) r,
    fun t ht ↦ ⟨by rw [poly_det_conj (R_pow_mul_inv r), (hdet t ht).1], ?_⟩, ?_, ?_⟩, ?_, ?_, ?_⟩
  · rw [← Matrix.inv_pow']
    exact poly_isStarState_conj_pow r (hdet t ht).2
  · refine isIntegralCurve_congr (isIntegralCurve_mul_mul hg (R ^ r)⁻¹ (R ^ r))
      (fun t ↦ rfl) (fun t ↦ ?_)
    exact poly_conj_mul (R_pow_mul_inv r) _ _
  · refine isIntegralCurve_congr (isIntegralCurve_mul_mul hX (R ^ r)⁻¹ (R ^ r))
      (fun t ↦ rfl) (fun t ↦ ?_)
    exact conj_R_pow_stateField r _ _
  · simp only [hg0, Matrix.mul_one, R_pow_inv_mul]
  · simp only [hgT]
    rw [← (commute_R_pow_inv r).eq, Matrix.mul_assoc, R_pow_inv_mul, Matrix.mul_one]
  · simp only [hXT, Matrix.mul_assoc]
    rw [(commute_R_pow r).eq, ← Matrix.mul_assoc (R ^ r)⁻¹ R⁻¹,
      ← (commute_R_inv_R_pow_inv r).eq, Matrix.mul_assoc]

end SmoothedOctagon
