module

public import SmoothedOctagon.Exclusion.Mixed.Extract.Reverse

/-!
# The reflected, time-reversed normal period

`MIXED_GLOBAL_MINIMUM_STRUCTURE` (MGMS) §§1-3. For a normal vertex period `P` on `[0, T]` put

* `u'(t) = σ u(T - t)` (the components `1` and `2` exchanged),
* `g'(t) = S R⁻¹ g(T - t) S`, `X'(t) = -S X(T - t) S`,
* `Λ₁'(t) = -S Λ₁(T - t) S`, `Λ_R'(t) = -S Λ_R(T - t) S`,

with `S = diag(-1, 1)`. Since `S J S = -J`, `S R S = R⁻¹`, `Z_{σv} = -S Z_v S` and `S² = 1`, this is
again a Pontryagin extremal with multiplier `λ = -1`: the integral equations hold by reversal of
time (`wx_isIntegralCurve_rev`), the brackets change sign and so do the velocities, the Hamiltonian
is unchanged (`wx_hamiltonian_refl`), and the endpoints `g'(0) = S R⁻¹ R S = 1`,
`g'(T) = S R⁻¹ S = R`, `X'(T) = R⁻¹ X'(0) R` (`wx_rev_twist`) hold. Its vertex representation runs
through the pieces backwards: piece `k` of the image is piece `N - 1 - k` of the original with the
label `-i`.

## Main API

* `VertexRepresentation.wx_refl`: the reflected representation (`N' = N`,
  `τ'_k = T - τ_{N-k}`, `i'_k = -i_{N-1-k}`).
* `NormalPeriod.wx_refl_extremal`, `NormalPeriod.wx_refl`: the reflected normal period.
* `NormalPeriod.wx_refl_N`, `wx_refl_cost`, `wx_refl_inCompactDomain`, `wx_refl_label`,
  `wx_refl_activeMargin`: same number of pieces, same cost, `𝔥**` preserved, labels
  `i'_k = -1 - i_{-1-k}`, active margins `a'_k = a_{-1-k}`.
-/

@[expose] public section

namespace SmoothedOctagon

open SmoothedPolygons MeasureTheory Set

namespace VertexRepresentation

variable {T : ℝ} {u : ℝ → Fin 3 → ℝ}

/-- **The reflected representation**: piece `k` is the original piece `N - 1 - k`, run backwards,
with the reflected label. -/
noncomputable def wx_refl (ρ : VertexRepresentation T u) :
    VertexRepresentation T (fun t ↦ wx_reflControl (u (T - t))) where
  N := ρ.N
  τ k := T - ρ.τ (ρ.N - k)
  label k := -ρ.label (ρ.N - 1 - k)
  N_pos := ρ.N_pos
  τ_zero := by simp only [sub_zero, ρ.τ_N, sub_self]
  τ_strictMono := fun k l hkl ↦ by
    have := ρ.τ_strictMono (show (ρ.N : ℤ) - l < ρ.N - k by omega)
    simp only
    linarith
  τ_add_period k := by
    have := ρ.τ_add_period (ρ.N - (k + ρ.N))
    rw [show (ρ.N : ℤ) - (k + ρ.N) + ρ.N = ρ.N - k by ring] at this
    linarith
  label_add_period k := by
    have := ρ.label_add_period (ρ.N - 1 - (k + ρ.N))
    rw [show (ρ.N : ℤ) - 1 - (k + ρ.N) + ρ.N = ρ.N - 1 - k by ring] at this
    rw [this]
    abel
  label_ne k := by
    have := ρ.label_ne (ρ.N - 1 - (k + 1))
    rw [show (ρ.N : ℤ) - 1 - (k + 1) + 1 = ρ.N - 1 - k by ring] at this
    simp only [ne_eq, neg_inj]
    exact fun e ↦ this e.symm
  ae_eq_vertex k hk0 hkN := by
    have h := wx_ae_rev T (ρ.ae_eq_vertex (ρ.N - 1 - k) (by omega) (by omega))
    filter_upwards [h] with t ht htI
    rw [show (ρ.N : ℤ) - 1 - k + 1 = ρ.N - k by ring] at ht
    rw [show (ρ.N : ℤ) - (k + 1) = ρ.N - 1 - k by ring] at htI
    rw [ht ⟨by linarith [htI.2], by linarith [htI.1]⟩, wx_reflControl_vertex]

theorem wx_refl_N (ρ : VertexRepresentation T u) : ρ.wx_refl.N = ρ.N := rfl

theorem wx_refl_τ (ρ : VertexRepresentation T u) (k : ℤ) : ρ.wx_refl.τ k = T - ρ.τ (ρ.N - k) :=
  rfl

theorem wx_refl_label (ρ : VertexRepresentation T u) (k : ℤ) :
    ρ.wx_refl.label k = -ρ.label (ρ.N - 1 - k) := rfl

end VertexRepresentation

namespace NormalPeriod

variable (P : NormalPeriod)

/-- **The reflected extremal** (MGMS §§1-3). -/
theorem wx_refl_extremal :
    IsPontryaginExtremal P.T (fun t ↦ wx_reflControl (P.u (P.T - t)))
      (fun t ↦ reflS * R⁻¹ * P.g (P.T - t) * reflS) (fun t ↦ wx_rev (P.X (P.T - t)))
      (fun t ↦ wx_rev (P.Λ₁ (P.T - t))) (fun t ↦ wx_rev (P.ΛR (P.T - t))) (-1) := by
  obtain ⟨⟨hT, hmeas, hsimp, hst, hgI, hXI⟩, hg0, hgT, hXT, hΛT, hΛRT, -, hpt, hΛI, hΛRI, hmax⟩ :=
    P.extremal
  have hT0 := hT.le
  have mem : ∀ t ∈ Icc 0 P.T, P.T - t ∈ Icc 0 P.T := fun t ht ↦
    ⟨by linarith [ht.2], by linarith [ht.1]⟩
  have hSS := wx_reflS_mul_self
  refine ⟨⟨hT, ?_, ?_, ?_, ?_, ?_⟩, ?_, ?_, ?_, ?_, ?_, by norm_num, ?_, ?_, ?_, ?_⟩
  · -- measurability
    exact measurable_wx_reflControl.comp (hmeas.comp (measurable_const.sub measurable_id))
  · -- the control simplex
    intro t ht
    exact wx_reflControl_mem (hsimp _ (mem t ht))
  · -- `det g' = 1` and star states
    intro t ht
    obtain ⟨hdet, hX⟩ := hst _ (mem t ht)
    refine ⟨?_, wx_isStarState_rev hX⟩
    rw [Matrix.det_mul, Matrix.det_mul, wx_det_reflS_Rinv, hdet]
    simp [reflS, Matrix.det_fin_two_of]
  · -- the frame equation
    refine isIntegralCurve_congr (isIntegralCurve_mul_mul (wx_isIntegralCurve_rev hT0 hgI)
      (reflS * R⁻¹) reflS) (fun t ↦ rfl) (fun t ↦ ?_)
    simp only [wx_rev, Matrix.mul_neg, Matrix.neg_mul, neg_inj, Matrix.mul_assoc]
    rw [← Matrix.mul_assoc reflS reflS, hSS, Matrix.one_mul]
  · -- the state equation
    refine isIntegralCurve_congr (wx_isIntegralCurve_wx_rev hT0 hXI) (fun t ↦ rfl) (fun t ↦ ?_)
    rw [wx_controlP_refl, wx_rev_bracket]
  · -- `g'(0) = 1`
    simp only [sub_zero, hgT]
    rw [Matrix.mul_assoc reflS, poly_inv_mul_R, Matrix.mul_one, hSS]
  · -- `g'(T) = R`
    simp only [sub_self, hg0, Matrix.mul_one]
    exact wx_reflS_Rinv_reflS
  · -- `X'(T) = R⁻¹ X'(0) R`
    simp only [sub_self, sub_zero, hXT]
    exact (wx_rev_twist _).symm
  · simp only [sub_self, sub_zero, hΛT]
    exact (wx_rev_twist _).symm
  · simp only [sub_self, sub_zero, hΛRT]
    exact (wx_rev_twist _).symm
  · -- traces, `Λ_R ⊥ X`, nontriviality
    intro t ht
    obtain ⟨h1, h2, h3, -⟩ := hpt _ (mem t ht)
    refine ⟨by rw [wx_trace_rev, h1, neg_zero], by rw [wx_trace_rev, h2, neg_zero],
      by rw [wx_traceForm_rev, h3], Or.inl (by norm_num)⟩
  · -- the equation of `Λ₁`
    refine isIntegralCurve_congr (wx_isIntegralCurve_wx_rev hT0 hΛI) (fun t ↦ rfl) (fun t ↦ ?_)
    rw [wx_rev_bracket]
  · -- the equation of `Λ_R`
    refine isIntegralCurve_congr (wx_isIntegralCurve_wx_rev hT0 hΛRI) (fun t ↦ rfl) (fun t ↦ ?_)
    have e : -wx_rev (P.Λ₁ (P.T - t)) + (3 / 2 * -1 : ℝ) • J =
        wx_rev (-P.Λ₁ (P.T - t) + (3 / 2 * -1 : ℝ) • J) := by
      rw [wx_rev_add, wx_rev_neg, wx_rev_smul, wx_rev_J]
    simp only
    rw [wx_controlP_refl, wx_rev_bracket, wx_rev_bracket, wx_traceForm_rev, e, wx_rev_bracket,
      wx_rev_combo]
  · -- the maximum condition
    filter_upwards [wx_ae_rev P.T hmax] with t ht htI
    obtain ⟨h0, hle⟩ := ht ⟨by linarith [htI.2], by linarith [htI.1]⟩
    refine ⟨by rw [wx_hamiltonian_refl]; exact h0, fun v hv ↦ ?_⟩
    rw [wx_hamiltonian_refl, ← wx_reflControl_reflControl v, wx_hamiltonian_refl]
    exact hle _ (wx_reflControl_mem hv)

/-- **The reflected, time-reversed normal period** (MGMS §§1-3). -/
noncomputable def wx_refl : NormalPeriod where
  T := P.T
  u t := wx_reflControl (P.u (P.T - t))
  g t := reflS * R⁻¹ * P.g (P.T - t) * reflS
  X t := wx_rev (P.X (P.T - t))
  Λ₁ t := wx_rev (P.Λ₁ (P.T - t))
  ΛR t := wx_rev (P.ΛR (P.T - t))
  extremal := P.wx_refl_extremal
  rep := P.rep.wx_refl

theorem wx_refl_N : P.wx_refl.N = P.N := rfl

/-- The reflection preserves the cost. -/
theorem wx_refl_cost : P.wx_refl.cost = P.cost := by
  simp only [cost, reinhardtCost, wx_refl]
  congr 1
  have e : ∀ t, traceForm J (wx_rev (P.X (P.T - t))) = traceForm J (P.X (P.T - t)) := fun t ↦ by
    rw [← wx_traceForm_rev, wx_rev_J, wx_rev_rev]
  simp only [e]
  rw [intervalIntegral.integral_comp_sub_left (fun x ↦ traceForm J (P.X x)) P.T, sub_self,
    sub_zero]

/-- The reflection preserves `𝔥**`. -/
theorem wx_refl_inCompactDomain (hK : P.InCompactDomain) : P.wx_refl.InCompactDomain :=
  fun t ht ↦ by
    have ht' : t ∈ Icc 0 P.T := ht
    exact wx_inCompactDomain_rev (hK _ ⟨by linarith [ht'.2], by linarith [ht'.1]⟩)

/-- The labels of the reflected period: `i'_k = -1 - i_{-1-k}`. -/
theorem wx_refl_label (k : ℤ) : P.wx_refl.rep.label k = -1 - P.rep.label (-1 - k) := by
  show -P.rep.label (P.N - 1 - k) = _
  have := P.rep.label_add_period (-1 - k)
  rw [show -1 - k + (P.N : ℤ) = P.N - 1 - k by ring] at this
  rw [this]
  abel

/-- The active margins of the reflected period: `a'_k = a_{-1-k}`. -/
theorem wx_refl_activeMargin (k : ℤ) : P.wx_refl.activeMargin k = P.activeMargin (-1 - k) := by
  have hN : (0 : ℤ) < P.N := by exact_mod_cast P.rep.N_pos
  have hj0 : 0 ≤ k % (P.N : ℤ) := Int.emod_nonneg k hN.ne'
  have hjN : k % (P.N : ℤ) < P.N := Int.emod_lt_of_pos k hN
  -- the original side: `a_{-1-k} = a_{N-1-j}`, `j = k mod N`
  have hper : Function.Periodic P.activeMargin (P.N : ℤ) := P.activeMargin_add_N
  have e1 : P.activeMargin (-1 - k) = P.activeMargin (P.N - 1 - k % P.N) := by
    have := hper.sub_int_mul_eq (x := (P.N : ℤ) - 1 - k % P.N) (k / P.N + 1)
    rw [← this]
    congr 1
    rw [Int.emod_def]
    push_cast
    ring
  -- the reflected side
  have e2 : P.wx_refl.activeMargin k = margin (-P.rep.label (P.N - 1 - k % P.N))
      (wx_rev (P.X (P.T - (P.T - P.rep.τ (P.N - k % P.N))))) := rfl
  generalize k % (P.N : ℤ) = j at hj0 hjN e1 e2
  rw [e1, e2, sub_sub_cancel, wx_margin_rev, P.activeMargin_eq (by omega) (by omega)]
  have := (P.piece_margin (k := P.N - 1 - j) (by omega) (by omega)).1
  rw [show (P.N : ℤ) - 1 - j + 1 = P.N - j by ring, P.activeMargin_eq (by omega) (by omega)] at this
  exact this

end NormalPeriod

end SmoothedOctagon
