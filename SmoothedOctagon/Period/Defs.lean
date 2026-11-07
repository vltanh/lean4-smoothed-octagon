module

public import SmoothedOctagon.Foundations.Problem
public import SmoothedPolygons.Ch3.ControlProblem
public import SmoothedPolygons.Ch3.ControlSets
public import Cited.HalesVajjha.CompactDomain

/-!
# Vertex periods

The objects shared by every stage of the proof after the reduction to finitely many switches.

* `octagonCost = √12 δ_oct`, the cost of the smoothed octagon's trajectory.
* `margin i X = -√3 tr(Z_{e_i} X)`, the *margin* `p_i` of a state for the vertex `e_i` of the
  control simplex. On star states `p_i = 2 ρ_{2-i}` and `p₀p₁ + p₁p₂ + p₂p₀ = 4`; on an arc of
  constant control `e_i` the active margin `p_i` is constant.
* `twistedFrame`, `twistedState`: the extension of a trajectory on `[0, T]` to `t ≥ 0` by
  `g(t + T) = g(t) R`, `X(t + T) = R⁻¹ X(t) R`; `rebaseFrame` restarts the frame at time `s`.
* `VertexRepresentation T u`: a control that is a.e. a vertex `e_{i_k}` on finitely many pieces
  `(τ_k, τ_{k+1})` of positive length, `k = 0, …, N - 1`, indexed by `ℤ` through the twist
  `τ_{k+N} = τ_k + T`, `i_{k+N} = i_k + 1`, with distinct neighbouring labels (zero pieces deleted,
  equal neighbours merged, also across the seam).
* The switch from piece `k` to piece `k + 1` is *forward* if `i_{k+1} = i_k + 1` and *reverse* if
  `i_{k+1} = i_k - 1` (labels mod 3). The smoothed octagon has four pieces, `e₂, e₀, e₁, e₂`, and
  every switch forward.
* Maximal runs of equal signs, and the five classes R (all reverse), F (all forward), M3 (mixed,
  some reverse run of length `≠ 2`), M1 (mixed, reverse runs of length 2, forward runs of length 1)
  and M2 (mixed, reverse runs of length 2, some forward run of length `≥ 2`).
* `NormalPeriod`: a Pontryagin extremal with cost multiplier `λ = -1` together with a vertex
  representation of its control, the input of every whole-period exclusion.
-/

@[expose] public section

namespace SmoothedOctagon

open SmoothedPolygons MeasureTheory Set

/-- The cost `A_oct = √12 δ_oct` of the smoothed octagon's trajectory. -/
noncomputable def octagonCost : ℝ := √12 * octagonDensity

/-- The margin `p_i(X) = -√3 tr(Z_{e_i} X)` of a state `X` for the vertex `e_i`. -/
noncomputable def margin (i : Fin 3) (X : Mat2) : ℝ :=
  -√3 * traceForm (controlMatrix (vertex i)) X

/-! ### The twisted extension and rebasing -/

/-- The frame extended from `[0, T]` to `t ≥ 0` by `G(t + T) = G(t) R`:
`G(t) = g(t - nT) Rⁿ` with `n = ⌊t/T⌋`. -/
noncomputable def twistedFrame (T : ℝ) (g : ℝ → Mat2) (t : ℝ) : Mat2 :=
  g (t - ⌊t / T⌋₊ * T) * R ^ ⌊t / T⌋₊

/-- The state extended from `[0, T]` to `t ≥ 0` by `Y(t + T) = R⁻¹ Y(t) R`. -/
noncomputable def twistedState (T : ℝ) (X : ℝ → Mat2) (t : ℝ) : Mat2 :=
  (R ^ ⌊t / T⌋₊)⁻¹ * X (t - ⌊t / T⌋₊ * T) * R ^ ⌊t / T⌋₊

/-- The frame rebased at time `s`: `ĝ(t) = G(s)⁻¹ G(s + t)`. -/
noncomputable def rebaseFrame (T : ℝ) (g : ℝ → Mat2) (s t : ℝ) : Mat2 :=
  (twistedFrame T g s)⁻¹ * twistedFrame T g (s + t)

/-! ### Vertex representations -/

/-- A finite vertex representation of a control `u` on one period `[0, T]`: `N ≥ 1` pieces
`(τ_k, τ_{k+1})`, `0 ≤ k < N`, of positive length with `τ_0 = 0` and `τ_N = T`, on which `u` is a.e.
the vertex `e_{i_k}`. Times and labels are indexed by `ℤ` through the twist, and neighbouring labels
differ, also across the seam. -/
structure VertexRepresentation (T : ℝ) (u : ℝ → Fin 3 → ℝ) where
  /-- The number of pieces in one period. -/
  N : ℕ
  /-- The switching times; piece `k` is `(τ k, τ (k + 1))`. -/
  τ : ℤ → ℝ
  /-- The vertex label of piece `k`. -/
  label : ℤ → Fin 3
  N_pos : 0 < N
  τ_zero : τ 0 = 0
  τ_strictMono : StrictMono τ
  τ_add_period : ∀ k, τ (k + N) = τ k + T
  label_add_period : ∀ k, label (k + N) = label k + 1
  label_ne : ∀ k, label (k + 1) ≠ label k
  ae_eq_vertex : ∀ k : ℤ, 0 ≤ k → k < N →
    ∀ᵐ t, t ∈ Ioo (τ k) (τ (k + 1)) → u t = vertex (label k)

namespace VertexRepresentation

variable {T : ℝ} {u : ℝ → Fin 3 → ℝ} (ρ : VertexRepresentation T u)

/-- The switch from piece `k` to piece `k + 1` is forward: `i_{k+1} = i_k + 1`. -/
def IsForward (k : ℤ) : Prop := ρ.label (k + 1) = ρ.label k + 1

/-- The switch from piece `k` to piece `k + 1` is reverse: `i_{k+1} = i_k - 1`. -/
def IsReverse (k : ℤ) : Prop := ρ.label (k + 1) = ρ.label k - 1

/-- A maximal run of `L ≥ 1` reverse switches `k, …, k + L - 1`, preceded and followed by forward
switches. -/
def IsReverseRun (k : ℤ) (L : ℕ) : Prop :=
  1 ≤ L ∧ ρ.IsForward (k - 1) ∧ ρ.IsForward (k + L) ∧ ∀ j, k ≤ j → j < k + L → ρ.IsReverse j

/-- A maximal run of `L ≥ 1` forward switches `k, …, k + L - 1`, preceded and followed by reverse
switches. -/
def IsForwardRun (k : ℤ) (L : ℕ) : Prop :=
  1 ≤ L ∧ ρ.IsReverse (k - 1) ∧ ρ.IsReverse (k + L) ∧ ∀ j, k ≤ j → j < k + L → ρ.IsForward j

/-- Class R: every switch is reverse. -/
def AllReverse : Prop := ∀ k, ρ.IsReverse k

/-- Class F: every switch is forward. -/
def AllForward : Prop := ∀ k, ρ.IsForward k

/-- Both forward and reverse switches occur. -/
def IsMixed : Prop := (∃ k, ρ.IsForward k) ∧ ∃ k, ρ.IsReverse k

/-- Class M3: mixed, with a maximal reverse run of length other than two. -/
def ClassM3 : Prop := ρ.IsMixed ∧ ∃ k L, ρ.IsReverseRun k L ∧ L ≠ 2

/-- Class M1: mixed, every maximal reverse run of length two and every maximal forward run of
length one; the cyclic sign word is `(− − +)^m`. -/
def ClassM1 : Prop :=
  ρ.IsMixed ∧ (∀ k L, ρ.IsReverseRun k L → L = 2) ∧ ∀ k L, ρ.IsForwardRun k L → L = 1

/-- Class M2: mixed, every maximal reverse run of length two, and some maximal forward run of
length at least two. -/
def ClassM2 : Prop :=
  ρ.IsMixed ∧ (∀ k L, ρ.IsReverseRun k L → L = 2) ∧ ∃ k L, ρ.IsForwardRun k L ∧ 2 ≤ L

end VertexRepresentation

/-! ### Normal periods -/

/-- A normal vertex period: a Pontryagin extremal of the Reinhardt problem with cost multiplier
`λ = -1` (so it carries `g(0) = I`, `g(T) = R`, `X(T) = R⁻¹ X(0) R` and the twisted costate
endpoints), together with a finite vertex representation of its control. -/
structure NormalPeriod where
  /-- The terminal time. -/
  T : ℝ
  /-- The control. -/
  u : ℝ → Fin 3 → ℝ
  /-- The frame. -/
  g : ℝ → Mat2
  /-- The state. -/
  X : ℝ → Mat2
  /-- The primary costate. -/
  Λ₁ : ℝ → Mat2
  /-- The reduced state costate. -/
  ΛR : ℝ → Mat2
  extremal : IsPontryaginExtremal T u g X Λ₁ ΛR (-1)
  /-- The vertex representation of the control. -/
  rep : VertexRepresentation T u

namespace NormalPeriod

variable (P : NormalPeriod)

/-- The number of pieces of one period. -/
abbrev N : ℕ := P.rep.N

/-- The cost of the period. -/
noncomputable def cost : ℝ := reinhardtCost P.T P.X

/-- The period is competitive with the smoothed octagon: its cost is at most `A_oct`. -/
def IsCompetitive : Prop := P.cost ≤ octagonCost

/-- The state stays in the compact domain `𝔥**` of Hales–Vajjha, Definition 5.0.1. -/
def InCompactDomain : Prop := ∀ t ∈ Icc 0 P.T, Cited.HalesVajjha.InCompactDomain (P.X t)

end NormalPeriod

end SmoothedOctagon
