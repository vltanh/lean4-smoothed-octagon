module

public import SmoothedOctagon.Period.Defs

/-!
# Shared definitions of the reduction to a finite normal period

The objects through which the sub-results of `SmoothedOctagon/Reduction/` talk to each other
(inventory A2, §§1, 2.9). Everything lives in the namespace `SmoothedOctagon.Reduction`.

Main API:

* `twistedControl T u`, `rebaseControl T u s`, `rebaseState T X s`: the twisted extension of a
  control from `[0, T]` to `t ≥ 0` (on `[nT, (n + 1)T)` the control `u(t - nT)` with its coordinates
  shifted `n` times, so the vertex `e_i` becomes `e_{i+n}` and `Z_{v(t+T)} = R⁻¹ Z_{v(t)} R`), and
  the control and state rebased at time `s`, `û(t) = v(s + t)`, `X̂(t) = Y(s + t)`
  (VERTEX_WORD_REDUCTION, Lemma 1). The rebased frame is `rebaseFrame` of `Period/Defs.lean`.
* `IsPiecewiseVertex u a b n`: on `[a, b]` the control is a.e. a concatenation of `n` constant
  vertex pieces of positive length (neighbouring labels may coincide: nothing is merged).
* `EdgeBound T u`: property (E4) of MEASURABLE_EDGE_PMP_BOUND: on every subinterval of `[0, T]`
  on which one coordinate of the control vanishes a.e., the control is a concatenation of at most
  four vertex pieces.
* `frobSq`, `covectorNormSq`, `singularGapSq`: the squared Frobenius norm of a `2 × 2` matrix, the
  squared norm `‖𝒫‖² = λ² + ‖Λ₁‖² + ‖Λ_R‖²` of the extended covector `𝒫 = (λ, Λ₁, Λ_R)`
  (SINGULAR_COST_BUDGET (6)), and the squared distance
  `Q² = ‖A‖² + ‖W‖² = ‖Λ₁ - (3/2)λJ‖² + ‖Λ_R‖²` of the costate from the singular locus
  `Λ₁ = (3/2)λJ`, `Λ_R = 0` (SINGULAR_COST_BUDGET (34)).
-/

@[expose] public section

namespace SmoothedOctagon.Reduction

open SmoothedPolygons MeasureTheory Set

/-! ### Twisted extension and rebasing of the control -/

/-- The control extended from `[0, T]` to `t ≥ 0` by the twist: with `n = ⌊t/T⌋₊`,
`v(t)_j = u(t - nT)_{j - n}` (indices mod 3). So `v(t + T)_j = v(t)_{j-1}` for `t ≥ 0`, which is the
extension of `remark6_6_1`; the vertex `e_i` on `[0, T)` becomes `e_{i+n}` on `[nT, (n+1)T)`, and
`Z_{v(t + T)} = R⁻¹ Z_{v(t)} R`, matching `twistedFrame` and `twistedState`. -/
noncomputable def twistedControl (T : ℝ) (u : ℝ → Fin 3 → ℝ) (t : ℝ) : Fin 3 → ℝ :=
  fun j ↦ u (t - ⌊t / T⌋₊ * T) (j - Fin.ofNat 3 ⌊t / T⌋₊)

/-- The control rebased at time `s`: `û(t) = v(s + t)`, with `v` the twisted extension. -/
noncomputable def rebaseControl (T : ℝ) (u : ℝ → Fin 3 → ℝ) (s t : ℝ) : Fin 3 → ℝ :=
  twistedControl T u (s + t)

/-- The state rebased at time `s`: `X̂(t) = Y(s + t)`, with `Y` the twisted extension. -/
noncomputable def rebaseState (T : ℝ) (X : ℝ → Mat2) (s t : ℝ) : Mat2 :=
  twistedState T X (s + t)

/-! ### Finite vertex descriptions -/

/-- On `[a, b]` the control `u` is almost everywhere a concatenation of `n` constant vertex pieces:
there are times `a = τ₀ < τ₁ < ⋯ < τₙ = b` and labels `l₀, …, l_{n-1}` with `u = e_{l_k}` a.e. on
`(τ_k, τ_{k+1})`. Neighbouring labels may coincide (no merging); only the values of `τ` on
`0, …, n` and of `l` on `0, …, n - 1` matter. -/
def IsPiecewiseVertex (u : ℝ → Fin 3 → ℝ) (a b : ℝ) (n : ℕ) : Prop :=
  ∃ (τ : ℕ → ℝ) (l : ℕ → Fin 3), τ 0 = a ∧ τ n = b ∧ (∀ k < n, τ k < τ (k + 1)) ∧
    ∀ k < n, ∀ᵐ t, t ∈ Ioo (τ k) (τ (k + 1)) → u t = vertex (l k)

/-- Property (E4) of a control on `[0, T]` (MEASURABLE_EDGE_PMP_BOUND, Theorem): whenever one
coordinate `u_j` vanishes a.e. on a subinterval `(t₀, t₁)` of `[0, T]` (the trajectory runs along
the edge of the simplex opposite `e_j`), the control is a.e. a concatenation of at most four
constant vertex pieces on `[t₀, t₁]`. -/
def EdgeBound (T : ℝ) (u : ℝ → Fin 3 → ℝ) : Prop :=
  ∀ t₀ t₁ : ℝ, 0 ≤ t₀ → t₀ < t₁ → t₁ ≤ T → ∀ j : Fin 3,
    (∀ᵐ t, t ∈ Ioo t₀ t₁ → u t j = 0) → ∃ n ≤ 4, IsPiecewiseVertex u t₀ t₁ n

/-! ### Norms of the costate -/

/-- The squared Frobenius norm `‖M‖_F² = Σᵢⱼ Mᵢⱼ²` of a `2 × 2` matrix. -/
noncomputable def frobSq (M : Mat2) : ℝ := M 0 0 ^ 2 + M 0 1 ^ 2 + M 1 0 ^ 2 + M 1 1 ^ 2

/-- The squared norm `‖𝒫‖² = λ² + ‖Λ₁‖_F² + ‖Λ_R‖_F²` of the extended covector
`𝒫 = (λ, Λ₁, Λ_R)` (SINGULAR_COST_BUDGET (6), QUANTITATIVE_REGULAR_SWITCH_BOUND (6); there
`W = Λ_R`). -/
noncomputable def covectorNormSq (lam : ℝ) (Λ₁ ΛR : Mat2) : ℝ := lam ^ 2 + frobSq Λ₁ + frobSq ΛR

/-- The squared distance `Q² = ‖A‖_F² + ‖W‖_F²` of the costate from the singular locus, with
`A = Λ₁ - (3/2)λJ` and `W = Λ_R` (SINGULAR_COST_BUDGET (34); the clearance of
SINGULAR_COST_BUDGET (6) is `D² = ‖X - J‖_F² + Q² ≥ Q²`). -/
noncomputable def singularGapSq (lam : ℝ) (Λ₁ ΛR : Mat2) : ℝ :=
  frobSq (Λ₁ - (3 / 2 * lam) • J) + frobSq ΛR

end SmoothedOctagon.Reduction
