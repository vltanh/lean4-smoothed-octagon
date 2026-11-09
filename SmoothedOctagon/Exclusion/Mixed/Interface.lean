module

public import SmoothedOctagon.Period.Costate
public import SmoothedOctagon.Exclusion.Mixed.Scalar
public import SmoothedOctagon.Exclusion.Mixed.Wire

/-!
# Case M2: the covector calculus, as an interface

The facts about the primary multiplier of a normal vertex period that case M2 uses, collected in the
structure `NormalPeriod.M2Calculus`. Its existence `NormalPeriod.m2_calculus` is proved from
`Period/Elliptic.lean` (through `Exclusion/Forward/Wire` and `Exclusion/Mixed/Wire`) with
`M i = CostateCycle.Mloc i`, `Γ = gam2 0`: the boundary identity `∂J/∂a_i = tr(U V_i)`,
the turn secants, the switching inequalities, the missing-control inequality and the spectral
cost–Casimir bound. The lower Casimir bound `cas_gt` is `NormalPeriod.wire_cas_gt`, proved from the
whole-period winding of the costate-metric angles (`Exclusion/Mixed/Density/`). Everything else in
case M2 is derived from it.

## Conventions

The triangular coordinates of `Terminal/Cycle.lean`: `R = Term.triR = [[0, 1], [-1, 1]]`,
`T₀(q) = diag(q, q⁻¹)` (`m2T0`). The one-arc transport after piece `i` is
`A_i = T₀(q_i) R^{-ε_i}` (`CostateCycle.m2A`: `R⁻¹ = triRinv` after a forward switch, `R` after a
reverse one), and `M i = P_i⁻¹ U P_i` is the normalized primary multiplier `U` in the prefix
frame `P_i` of piece `i`, so that `M (i + 1) = A_i⁻¹ (M i) A_i`, `tr M i = 0`, `det M i = γ²`.
Eight times the norm of the switch after piece `i`, read in the frame of piece `i`, is
(`CostateCycle.m2Norm`)

* `8 q_i² (M i)₂₁/s_i²` if the switch is forward, `-8 (M i)₁₂/(q_i² s_i²)` if it is reverse,

with `s_i = a_i + a_{i+1}`. The cross pairing at a same-sign piece is `e_i = (M i)₁₁/K_i`.

## The fields (all for the actual period, across the twisted seam)

* `stat` (the stationarity identity, times 4): at a piece with equal incident signs,
  `s_- n_{i-1} + s_+ n_i - 16 a_i (M i)₁₁/K_i = m2Stat a_{i-1} a_i a_{i+1}`.
* `secant`: at a turn both incident norms equal `m2Sec a_{i-1} a_i a_{i+1}`.
* `fwd_ge`, `rev_le` (the switching inequalities): `n_i ≥ m2g a_i a_{i+1}` after a forward switch,
  `≤` after a reverse one.
* `floor_in`, `floor_out` (the missing-control floors): on a piece with both incident switches
  forward, `n_{i-1} ≥ F_{a_i/s_{i-1}}(q_i)` and `n_i ≥ F_{a_i/s_i}(q_i)`. The identity that gives
  the floor is algebraic in `x`, so the floor holds for every `x`.
* `mc_fwd`: the missing control at every forward switch, `G_L ≥ 0`, in the frame of the new piece;
  with `stat` it gives the floors.
* `cas_lt` (the spectral cost–Casimir bound): a competitive period has `γ² < 9193/50000`
  (`< 23/125`).
* `cas_gt` (the reverse angle density): a competitive mixed period in `𝔥**` has `γ² > 27/256`.
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

/-- The one-arc transport `A_i = T₀(q_i) R^{-ε_i}`. -/
noncomputable def m2A (i : ℤ) : Mat2 :=
  m2T0 (C.q i) * (if C.m2Fwd i then Term.triRinv else Term.triR)

/-- Eight times the norm of the switch after piece `i`, read in the frame `M i` of piece `i`. -/
noncomputable def m2Norm (M : ℤ → Mat2) (i : ℤ) : ℝ :=
  if C.m2Fwd i then 8 * C.q i ^ 2 * M i 1 0 / (C.act i + C.act (i + 1)) ^ 2
  else -8 * M i 0 1 / (C.q i ^ 2 * (C.act i + C.act (i + 1)) ^ 2)

end CostateCycle

namespace NormalPeriod

/-- **The covector calculus of a normal vertex period**: the normalized primary
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
  /-- The stationarity identity (times 4) at a piece with equal incident signs. -/
  stat : ∀ i, (P.costateCycle.m2Fwd (i - 1) ↔ P.costateCycle.m2Fwd i) →
    (P.costateCycle.act (i - 1) + P.costateCycle.act i) * P.costateCycle.m2Norm M (i - 1) +
        (P.costateCycle.act i + P.costateCycle.act (i + 1)) * P.costateCycle.m2Norm M i -
        16 * P.costateCycle.act i * M i 0 0 / (P.costateCycle.act i ^ 2 + 4) =
      m2Stat (P.costateCycle.act (i - 1)) (P.costateCycle.act i) (P.costateCycle.act (i + 1))
  /-- Both norms at a turn are its secant. -/
  secant : ∀ i, ¬ (P.costateCycle.m2Fwd (i - 1) ↔ P.costateCycle.m2Fwd i) →
    P.costateCycle.m2Norm M (i - 1) =
        m2Sec (P.costateCycle.act (i - 1)) (P.costateCycle.act i) (P.costateCycle.act (i + 1)) ∧
      P.costateCycle.m2Norm M i =
        m2Sec (P.costateCycle.act (i - 1)) (P.costateCycle.act i) (P.costateCycle.act (i + 1))
  /-- The switching inequality at a forward switch. -/
  fwd_ge : ∀ i, P.costateCycle.m2Fwd i →
    m2g (P.costateCycle.act i) (P.costateCycle.act (i + 1)) ≤ P.costateCycle.m2Norm M i
  /-- The switching inequality at a reverse switch. -/
  rev_le : ∀ i, ¬ P.costateCycle.m2Fwd i →
    P.costateCycle.m2Norm M i ≤ m2g (P.costateCycle.act i) (P.costateCycle.act (i + 1))
  /-- The floor of the incoming norm of a doubly forward piece. -/
  floor_in : ∀ i, P.costateCycle.m2Fwd (i - 1) → P.costateCycle.m2Fwd i →
    m2F (P.costateCycle.act i / (P.costateCycle.act (i - 1) + P.costateCycle.act i))
        (P.costateCycle.q i) ≤ P.costateCycle.m2Norm M (i - 1)
  /-- The floor of the outgoing norm of a doubly forward piece. -/
  floor_out : ∀ i, P.costateCycle.m2Fwd (i - 1) → P.costateCycle.m2Fwd i →
    m2F (P.costateCycle.act i / (P.costateCycle.act i + P.costateCycle.act (i + 1)))
        (P.costateCycle.q i) ≤ P.costateCycle.m2Norm M i
  /-- The missing control at a forward switch into piece `i`, in the frame of
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

/-- **The covector calculus exists**, with `M = Mloc` and `Γ = gam2 0`: the identities and
inequalities come from the elliptic costate calculus, the cost–Casimir bound and the reverse angle
density. -/
theorem m2_calculus (P : NormalPeriod) : Nonempty P.M2Calculus := by
  set C := P.costateCycle with hC
  have hA : ∀ i, C.m2A i = C.Amat i := fun i ↦ rfl
  have hnorm : ∀ i, C.m2Norm C.Mloc i = 8 * C.swd i := fun i ↦ by
    unfold CostateCycle.m2Norm
    split_ifs with h
    · exact C.wire_norm_fwd h
    · rcases C.lab_cases i with h' | h'
      · exact absurd h' h
      · exact C.wire_norm_rev h'
  have hsgn : ∀ i, (C.m2Fwd (i - 1) ↔ C.m2Fwd i) → C.sgn (i - 1) = C.sgn i := by
    intro i h
    simp only [CostateCycle.sgn]
    by_cases h1 : C.m2Fwd i
    · have h0 := h.2 h1
      simp only [CostateCycle.m2Fwd] at h0 h1
      simp only [h0, h1, ↓reduceIte]
    · have h0 : ¬ C.m2Fwd (i - 1) := fun h' ↦ h1 (h.1 h')
      simp only [CostateCycle.m2Fwd] at h0 h1
      simp only [h0, h1, ↓reduceIte]
  have hturn : ∀ i, ¬ (C.m2Fwd (i - 1) ↔ C.m2Fwd i) → C.sgn (i - 1) = -C.sgn i := by
    intro i h
    simp only [CostateCycle.sgn]
    by_cases h1 : C.m2Fwd i
    · have h0 : ¬ C.m2Fwd (i - 1) := fun h' ↦ h ⟨fun _ ↦ h1, fun _ ↦ h'⟩
      simp only [CostateCycle.m2Fwd] at h0 h1
      simp only [h0, h1, ↓reduceIte]
    · have h0 : C.m2Fwd (i - 1) := by
        by_contra h'; exact h ⟨fun h'' ↦ absurd h'' h', fun h'' ↦ absurd h'' h1⟩
      simp only [CostateCycle.m2Fwd] at h0 h1
      simp only [h0, h1, ↓reduceIte]; norm_num
  have hin : ∀ i, C.m2Fwd (i - 1) → C.lab i = C.lab (i - 1) + 1 := fun i h ↦ by
    have := h; simp only [CostateCycle.m2Fwd, sub_add_cancel] at this; exact this
  refine ⟨⟨C.Mloc, C.gam2 0, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩⟩
  · intro i
    simp [CostateCycle.Mloc, triY, Matrix.trace_fin_two]
    ring
  · intro i
    rw [C.det_Mloc, C.gam2_eq]
  · intro i
    rw [hA, Matrix.inv_eq_left_inv (C.Ainv_Amat i), C.Mloc_succ]
  · intro i h
    rw [hnorm, hnorm, wire_m2Stat_eq]
    exact C.wire_stat_M (hsgn i h)
  · intro i h
    rw [hnorm, hnorm]
    exact C.wire_turn_sec (hturn i h)
  · intro i h
    rw [hnorm, wire_m2g_eq]
    have := C.swd_fwd (k := i) h
    linarith
  · intro i h
    rw [hnorm, wire_m2g_eq]
    rcases C.lab_cases i with h' | h'
    · exact absurd h' h
    · have := C.swd_rev h'
      linarith
  · intro i h1 h2
    rw [hnorm, wire_m2F_eq (C.one_lt_q i)]
    exact C.wire_floor_in (hin i h1) h2
  · intro i h1 h2
    rw [hnorm, wire_m2F_eq (C.one_lt_q i)]
    exact C.wire_floor_out (hin i h1) h2
  · intro i h
    exact C.wire_mc (hin i h)
  · exact fun hc ↦ P.wire_cas_lt hc
  · exact fun hc hD hmix ↦ P.wire_cas_gt hc hD hmix

end NormalPeriod

end SmoothedOctagon
