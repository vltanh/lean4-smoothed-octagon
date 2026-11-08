module

public import SmoothedOctagon.Period.Costate
public import SmoothedOctagon.Exclusion.Mixed.Scalar

/-!
# Case M2: the covector calculus, as an interface

**To be replaced by `Period/Elliptic.lean`.** The facts of `MIXED_GLOBAL_COSTATE_ELLIPTIC` (CE) and
`MIXED_GLOBAL_SMALL_FORWARD_MINIMUM` (SFM) §2 that case M2 uses, about the primary multiplier of a
normal vertex period, collected in the structure `NormalPeriod.M2Calculus`; its existence
`NormalPeriod.m2_calculus` is the one `sorry` of this module (being proved in `Period/Elliptic.lean`
from the boundary identity `∂J/∂a_i = tr(U V_i)` (CE (8)), the cost–Casimir bound and the angle
density bound). Everything else in case M2 is derived from it.

## Conventions (CE §§2-4, inventory E2 §1.4)

The triangular coordinates of `Terminal/Cycle.lean`: `R = Term.triR = [[0, 1], [-1, 1]]`,
`T₀(q) = diag(q, q⁻¹)` (`m2T0`). The one-arc transport after piece `i` is
`A_i = T₀(q_i) R^{-ε_i}` (`CostateCycle.m2A`: `R⁻¹ = triRinv` after a forward switch, `R` after a
reverse one), and `M i = P_i⁻¹ U P_i` is the normalized primary multiplier `U` (CE (8)) in the prefix
frame `P_i` of piece `i`, so that `M (i + 1) = A_i⁻¹ (M i) A_i`, `tr M i = 0`, `det M i = γ²`.
Eight times the norm of the switch after piece `i` (CE (11)-(12)) read in the frame of piece `i` is
(`CostateCycle.m2Norm`)

* `8 q_i² (M i)₂₁/s_i²` if the switch is forward, `-8 (M i)₁₂/(q_i² s_i²)` if it is reverse,

with `s_i = a_i + a_{i+1}`. The cross pairing at a same-sign piece is `e_i = (M i)₁₁/K_i`.

## The fields (all for the actual period, across the twisted seam)

* `stat` (CE (14), first identity, times 4): at a piece with equal incident signs,
  `s_- n_{i-1} + s_+ n_i - 16 a_i (M i)₁₁/K_i = m2Stat a_{i-1} a_i a_{i+1}`.
* `secant` (CE (15)): at a turn both incident norms equal `m2Sec a_{i-1} a_i a_{i+1}`.
* `fwd_ge`, `rev_le` (CE (17)): `n_i ≥ m2g a_i a_{i+1}` after a forward switch, `≤` after a
  reverse one.
* `floor_in`, `floor_out` (SFM (11)-(12), CONT (12)): on a piece with both incident switches
  forward, `n_{i-1} ≥ F_{a_i/s_{i-1}}(q_i)` and `n_i ≥ F_{a_i/s_i}(q_i)`. SFM (10) defines `F_x`
  only for `1/2 ≤ x < 1`; its identity (12) is algebraic in `x`, so the floor holds for every `x`
  (inventory E2, D2).
* `mc_fwd` (SFM (11a)): the missing control at every forward switch, `G_L ≥ 0`, in the frame of
  the new piece; with `stat` it gives the floors (SFM (12)).
* `cas_lt` (cost–Casimir bound, `HAND_PROOF_REFINEMENTS` 1, CE "Consequence"): a competitive
  period has `γ² < 9193/50000` (`< 23/125`).
* `cas_gt` (`MIXED_GLOBAL_REVERSE_ANGLE_DENSITY` §3): a competitive mixed period in `𝔥**` has
  `γ² > 27/256`.
-/

@[expose] public section

namespace SmoothedOctagon

open SmoothedPolygons

/-- `T₀(q) = diag(q, q⁻¹)`. -/
noncomputable def m2T0 (q : ℝ) : Mat2 := !![q, 0; 0, q⁻¹]

namespace CostateCycle

variable {N : ℕ} (C : CostateCycle N)

/-- The switch after piece `i` is forward: `i_{i+1} = i_i + 1`. -/
def m2Fwd (i : ℤ) : Prop := C.lab (i + 1) = C.lab i + 1

instance (i : ℤ) : Decidable (C.m2Fwd i) := inferInstanceAs (Decidable (_ = _))

/-- The one-arc transport `A_i = T₀(q_i) R^{-ε_i}` (CE §2). -/
noncomputable def m2A (i : ℤ) : Mat2 :=
  m2T0 (C.q i) * (if C.m2Fwd i then Term.triRinv else Term.triR)

/-- Eight times the norm of the switch after piece `i`, read in the frame `M i` of piece `i`
(CE (11)-(12)). -/
noncomputable def m2Norm (M : ℤ → Mat2) (i : ℤ) : ℝ :=
  if C.m2Fwd i then 8 * C.q i ^ 2 * M i 1 0 / (C.act i + C.act (i + 1)) ^ 2
  else -8 * M i 0 1 / (C.q i ^ 2 * (C.act i + C.act (i + 1)) ^ 2)

end CostateCycle

namespace NormalPeriod

/-- **The covector calculus of a normal vertex period** (CE §§2-4, SFM §2): the normalized primary
multiplier in the prefix frames, with the stationarity identities, the turn secants, the switching
inequalities, the missing-control floors and the Casimir bounds. See the module docstring. -/
structure M2Calculus (P : NormalPeriod) where
  /-- The multiplier `M i = P_i⁻¹ U P_i` in the prefix frame of piece `i`. -/
  M : ℤ → Mat2
  /-- The squared Casimir `γ² = det U`. -/
  Γ : ℝ
  trace_eq : ∀ i, (M i).trace = 0
  det_eq : ∀ i, (M i).det = Γ
  transport : ∀ i, M (i + 1) = (P.costateCycle.m2A i)⁻¹ * M i * P.costateCycle.m2A i
  /-- CE (14) (times 4) at a piece with equal incident signs. -/
  stat : ∀ i, (P.costateCycle.m2Fwd (i - 1) ↔ P.costateCycle.m2Fwd i) →
    (P.costateCycle.act (i - 1) + P.costateCycle.act i) * P.costateCycle.m2Norm M (i - 1) +
        (P.costateCycle.act i + P.costateCycle.act (i + 1)) * P.costateCycle.m2Norm M i -
        16 * P.costateCycle.act i * M i 0 0 / (P.costateCycle.act i ^ 2 + 4) =
      m2Stat (P.costateCycle.act (i - 1)) (P.costateCycle.act i) (P.costateCycle.act (i + 1))
  /-- CE (15): both norms at a turn are its secant. -/
  secant : ∀ i, ¬ (P.costateCycle.m2Fwd (i - 1) ↔ P.costateCycle.m2Fwd i) →
    P.costateCycle.m2Norm M (i - 1) =
        m2Sec (P.costateCycle.act (i - 1)) (P.costateCycle.act i) (P.costateCycle.act (i + 1)) ∧
      P.costateCycle.m2Norm M i =
        m2Sec (P.costateCycle.act (i - 1)) (P.costateCycle.act i) (P.costateCycle.act (i + 1))
  /-- CE (17), forward switch. -/
  fwd_ge : ∀ i, P.costateCycle.m2Fwd i →
    m2g (P.costateCycle.act i) (P.costateCycle.act (i + 1)) ≤ P.costateCycle.m2Norm M i
  /-- CE (17), reverse switch. -/
  rev_le : ∀ i, ¬ P.costateCycle.m2Fwd i →
    P.costateCycle.m2Norm M i ≤ m2g (P.costateCycle.act i) (P.costateCycle.act (i + 1))
  /-- SFM (11)-(12): the floor of the incoming norm of a doubly forward piece. -/
  floor_in : ∀ i, P.costateCycle.m2Fwd (i - 1) → P.costateCycle.m2Fwd i →
    m2F (P.costateCycle.act i / (P.costateCycle.act (i - 1) + P.costateCycle.act i))
        (P.costateCycle.q i) ≤ P.costateCycle.m2Norm M (i - 1)
  /-- SFM (11)-(12): the floor of the outgoing norm of a doubly forward piece. -/
  floor_out : ∀ i, P.costateCycle.m2Fwd (i - 1) → P.costateCycle.m2Fwd i →
    m2F (P.costateCycle.act i / (P.costateCycle.act i + P.costateCycle.act (i + 1)))
        (P.costateCycle.q i) ≤ P.costateCycle.m2Norm M i
  /-- SFM (11a)-(12): the missing control at a forward switch into piece `i`, in the frame of
  piece `i`: `G_L = 4 a_i s (M i)₁₁ + 2 K_i (M i)₁₂ - 2 s² (M i)₂₁ + a_{i-1} s + K_i ≥ 0`,
  `s = a_{i-1} + a_i` (the missing Hamiltonian is `-4√3 G_L/(s (4 - a_{i-1} a_i))`). -/
  mc_fwd : ∀ i, P.costateCycle.m2Fwd (i - 1) →
    0 ≤ 4 * P.costateCycle.act i * (P.costateCycle.act (i - 1) + P.costateCycle.act i) * M i 0 0 +
      2 * (P.costateCycle.act i ^ 2 + 4) * M i 0 1 -
      2 * (P.costateCycle.act (i - 1) + P.costateCycle.act i) ^ 2 * M i 1 0 +
      P.costateCycle.act (i - 1) * (P.costateCycle.act (i - 1) + P.costateCycle.act i) +
      (P.costateCycle.act i ^ 2 + 4)
  /-- The cost–Casimir bound of a competitive period. -/
  cas_lt : P.IsCompetitive → Γ < 9193 / 50000
  /-- The lower Casimir bound of a competitive mixed period. -/
  cas_gt : P.IsCompetitive → P.InCompactDomain → P.rep.IsMixed → 27 / 256 < Γ

/-- **The covector calculus exists** (CE Theorem and §§2-4, SFM §2, the cost–Casimir bound,
`MIXED_GLOBAL_REVERSE_ANGLE_DENSITY` §3). To be replaced by `Period/Elliptic.lean`. -/
theorem m2_calculus (P : NormalPeriod) : Nonempty P.M2Calculus := by
  sorry

end NormalPeriod

end SmoothedOctagon
