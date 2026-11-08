module

public import SmoothedOctagon.Period.Elliptic
public import SmoothedOctagon.Exclusion.ShortRun.Pattern
public import SmoothedOctagon.Exclusion.ShortRun.Scalar

/-!
# Case M1: the scalar data at the centres

For a normal period with the sign pattern `(− − +)^m` (switches `k₀ + 3j`, `k₀ + 3j + 1` reverse,
`k₀ + 3j + 2` forward), the centre piece `k₀ + 3j + 1` carries the scalar data `m1_CentreData`, read
off its costate cycle `C = P.costateCycle`:

`r = a/(a + p)`, `t = a/(a + n)`, `ρ = a²/(a² + 4)`, `u = 8 d_{c-1}`, `v = 8 d_c`, `E = 16 e_c`,
`γ² = C.gam2 0` (with `a, p, n` the active margins of pieces `c, c - 1, c + 1`).

## Main API

* `m1_IsPattern P k₀`: the sign pattern.
* `m1_centre`, `m1_r`, `m1_t`, `m1_ρ`, `m1_u`, `m1_v`, `m1_E`.
* `m1_centreData`: the centre data, from `CostateCycle.centre_stat`, `gram_mm`, `swd_rev`,
  `turn_swd_ge`, `centre_factor` and the strict centre minimum
  (`reverseRun_two_and_centre_min`).
-/

@[expose] public section

namespace SmoothedOctagon

/-- The centre piece of the `j`-th reverse run. -/
def m1_centre (k₀ j : ℤ) : ℤ := k₀ + 3 * j + 1

namespace NormalPeriod

variable (P : NormalPeriod)

/-- The sign pattern `(− − +)^m` starting at the switch `k₀`. -/
def m1_IsPattern (k₀ : ℤ) : Prop :=
  ∀ j : ℤ, P.rep.IsReverse (k₀ + 3 * j) ∧ P.rep.IsReverse (k₀ + 3 * j + 1) ∧
    P.rep.IsForward (k₀ + 3 * j + 2)

/-- `r = a/(a + p)` at the centre `c`. -/
noncomputable def m1_r (c : ℤ) : ℝ :=
  P.costateCycle.act c / (P.costateCycle.act c + P.costateCycle.act (c - 1))

/-- `t = a/(a + n)` at the centre `c`. -/
noncomputable def m1_t (c : ℤ) : ℝ :=
  P.costateCycle.act c / (P.costateCycle.act c + P.costateCycle.act (c + 1))

/-- `ρ = a²/(a² + 4)` at the centre `c`. -/
noncomputable def m1_ρ (c : ℤ) : ℝ := P.costateCycle.act c ^ 2 / (P.costateCycle.act c ^ 2 + 4)

/-- `u = 8 d_{c-1}`. -/
noncomputable def m1_u (c : ℤ) : ℝ := 8 * P.costateCycle.swd (c - 1)

/-- `v = 8 d_c`. -/
noncomputable def m1_v (c : ℤ) : ℝ := 8 * P.costateCycle.swd c

/-- `E = 16 e_c`. -/
noncomputable def m1_E (c : ℤ) : ℝ := 16 * P.costateCycle.cre c

/-- **The centre data** at every centre of a period with the pattern: the bounds on `r, t, ρ, u, v`,
the stationarity identity for `E` and the Gram identity for `γ²`. -/
theorem m1_centreData {k₀ : ℤ} (hpat : P.m1_IsPattern k₀) (j : ℤ) :
    m1_CentreData (P.costateCycle.gam2 0) (P.m1_r (m1_centre k₀ j)) (P.m1_t (m1_centre k₀ j))
      (P.m1_ρ (m1_centre k₀ j)) (P.m1_u (m1_centre k₀ j)) (P.m1_v (m1_centre k₀ j))
      (P.m1_E (m1_centre k₀ j)) := by
  set C := P.costateCycle with hC
  set c := m1_centre k₀ j with hc
  have hlab : ∀ k, C.lab k = P.rep.label k := fun k ↦ rfl
  obtain ⟨r0, r1, -⟩ := hpat j
  obtain ⟨-, -, f2⟩ := hpat (j - 1)
  obtain ⟨-, -, f3⟩ := hpat j
  -- signs around the centre
  have hin : C.lab c = C.lab (c - 1) - 1 := by
    have : c - 1 = k₀ + 3 * j := by rw [hc, m1_centre]; ring
    rw [this, hc, m1_centre]; exact r0
  have hout : C.lab (c + 1) = C.lab c - 1 := by rw [hc, m1_centre]; exact r1
  have hfin : C.lab (c - 1) = C.lab (c - 1 - 1) + 1 := by
    have e1 : c - 1 - 1 = k₀ + 3 * (j - 1) + 2 := by rw [hc, m1_centre]; ring
    have e2 : c - 1 = k₀ + 3 * (j - 1) + 2 + 1 := by rw [hc, m1_centre]; ring
    rw [e1, e2]; exact f2
  have hfout : C.lab (c + 1 + 1) = C.lab (c + 1) + 1 := by
    have e1 : c + 1 = k₀ + 3 * j + 2 := by rw [hc, m1_centre]; ring
    rw [e1]; exact f3
  -- the two turns
  have ht1 : C.sgn (c - 1 - 1) = -C.sgn (c - 1) := by
    rw [C.sgn_fwd (by rw [sub_add_cancel]; exact hfin), C.sgn_rev (by rw [sub_add_cancel]; exact hin)]
    norm_num
  have ht2 : C.sgn (c + 1 - 1) = -C.sgn (c + 1) := by
    rw [add_sub_cancel_right, C.sgn_rev hout, C.sgn_fwd hfout]
  have hu0 := C.turn_swd_ge ht1
  have hv0 := C.turn_swd_ge ht2
  have hvv : C.swd c = C.swd (c + 1) := by
    have := (C.turn_secant ht2).1; rwa [add_sub_cancel_right] at this
  have hu1 := C.swd_rev (k := c - 1) (by rw [sub_add_cancel]; exact hin)
  have hv1 := C.swd_rev (k := c) hout
  rw [sub_add_cancel] at hu1
  -- the strict centre minimum
  have hrun : P.rep.IsReverseRun (c - 1) 2 := by
    refine ⟨by norm_num, ?_, ?_, fun i hi1 hi2 ↦ ?_⟩
    · have e : c - 1 - 1 = k₀ + 3 * (j - 1) + 2 := by rw [hc, m1_centre]; ring
      rw [e]; exact f2
    · have e : c - 1 + ((2 : ℕ) : ℤ) = k₀ + 3 * j + 2 := by rw [hc, m1_centre]; push_cast; ring
      rw [e]; exact f3
    · have e : c - 1 = k₀ + 3 * j := by rw [hc, m1_centre]; ring
      rw [e] at hi1 hi2
      push_cast at hi2
      rcases (show i = k₀ + 3 * j ∨ i = k₀ + 3 * j + 1 by omega) with h | h <;> rw [h]
      · exact r0
      · exact r1
  have hmin := reverseRun_two_and_centre_min P ⟨⟨_, f3⟩, ⟨_, r0⟩⟩ hrun
  rw [sub_add_cancel, show c - 1 + 2 = c + 1 by ring] at hmin
  obtain ⟨-, -, hap, han, -⟩ := hmin
  have hact : ∀ k, P.activeMargin k = C.act k := fun k ↦ (P.costateCycle_m_lab k).symm
  rw [hact, hact] at hap
  rw [hact, hact] at han
  -- positivity
  have ha := C.act_pos c
  have hp := C.act_pos (c - 1)
  have hn := C.act_pos (c + 1)
  have hK : 0 < C.act c ^ 2 + 4 := by positivity
  have hfac := C.centre_factor hin hout
  have hq := C.one_lt_q c
  have hstat := C.centre_stat hin hout
  have hgram := C.gram_mm hin hout
  rw [C.gam2_eq] at hgram
  have hJu : 8 * (elJ (C.act (c - 1)) (C.act c) / 2) =
      1 - C.act c / (C.act c + C.act (c - 1)) + (C.act c / (C.act c + C.act (c - 1))) ^ 2 := by
    simp only [elJ]; field_simp; ring
  have hJv : 8 * (elJ (C.act c) (C.act (c + 1)) / 2) =
      1 - C.act c / (C.act c + C.act (c + 1)) + (C.act c / (C.act c + C.act (c + 1))) ^ 2 := by
    simp only [elJ]; field_simp; ring
  simp only [m1_r, m1_t, m1_ρ, m1_u, m1_v, m1_E]
  refine ⟨by positivity, ?_, by positivity, ?_, by positivity, ?_, by linarith, by linarith,
    by linarith, by linarith, hstat, ?_⟩
  · rw [div_lt_iff₀ (by positivity)]; linarith
  · rw [div_lt_iff₀ (by positivity)]; linarith
  · -- `ρ < r t` from the centre factor
    rw [div_mul_div_comm, div_lt_div_iff₀ hK (by positivity)]
    have : (C.act c + C.act (c - 1)) * (C.act c + C.act (c + 1)) < C.act c ^ 2 + 4 := by
      rw [← hfac]
      have hpos : 0 < (C.act c + C.act (c - 1)) * (C.act c + C.act (c + 1)) := by positivity
      nlinarith
    have : 0 < C.act c ^ 2 := by positivity
    nlinarith
  · -- the Gram identity
    have e : 1 - C.act c ^ 2 / (C.act c ^ 2 + 4) = 4 / (C.act c ^ 2 + 4) := by field_simp; ring
    rw [e]
    have e2 : 16 * (4 / (C.act c ^ 2 + 4)) ^ 2 * C.gam2 0 =
        256 * (C.gam2 0 / (C.act c ^ 2 + 4) ^ 2) := by field_simp; ring
    rw [e2, ← hgram]
    ring

end NormalPeriod

end SmoothedOctagon
