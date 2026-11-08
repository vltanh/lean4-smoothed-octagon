module

public import SmoothedOctagon.Period.Defs
public import SmoothedOctagon.Exclusion.Mixed.Extract.Reflect

/-!
# Case M2: the reflection and time-reversal symmetry

`MIXED_GLOBAL_MINIMUM_STRUCTURE` §§1-3 (MGMS), `MIXED_GLOBAL_NONSHORT_PERIOD_EXCLUSION` §3,
`MIXED_GENERAL_SHORT_DEFECT_INTERFACE` §1. The reflection `S = diag(1, -1)` combined with the
reversal of time, `g ↦ S R⁻¹ g(T - t) S`, `X ↦ -S X(T - t) S`, `Λ ↦ -S Λ(T - t) S`, maps a normal
vertex period to a normal vertex period with the same cost (`S J S = -J`), the same compact-domain
property (`𝔥**` is symmetric under `x ↦ -x`), the pieces in reverse order (piece `k` of the image
is piece `-1 - k` of the original), the labels reflected, `i ↦ c - i`, and the active margins
carried along. The switch signs are read in reverse order and are not negated.

## Main API

* `m2_reflect`: the reflected period (constructed in `Mixed/Extract/Reflect` as
  `NormalPeriod.wx_refl`: `u'(t) = σ u(T - t)`, `g'(t) = S R⁻¹ g(T - t) S`, `X'(t) = -S X(T - t) S`,
  `Λ'(t) = -S Λ(T - t) S`; the image of the piece `k` is the piece `N - 1 - k`, `c = -1`).
* `m2_reflect_fwd_iff`: switch `k` of the image is forward iff switch `-2 - k` of the original is.
* `m2_reflect_classM2`: the image of an M2 period is M2.
-/

@[expose] public section

namespace SmoothedOctagon

/-- **The reflected period** (MGMS §§1-3). Every normal vertex period has a reflected,
time-reversed image: a normal vertex period with the same number of pieces and the same cost, in
`𝔥**` if the original is, whose labels are `c - i_{-1-k}` for a constant `c` and whose active
margins are `a_{-1-k}`. -/
theorem m2_reflect (P : NormalPeriod) :
    ∃ P' : NormalPeriod, P'.N = P.N ∧ P'.cost = P.cost ∧
      (P.InCompactDomain → P'.InCompactDomain) ∧
      (∃ c : Fin 3, ∀ k, P'.rep.label k = c - P.rep.label (-1 - k)) ∧
      ∀ k, P'.activeMargin k = P.activeMargin (-1 - k) :=
  ⟨P.wx_refl, P.wx_refl_N, P.wx_refl_cost, P.wx_refl_inCompactDomain, ⟨-1, P.wx_refl_label⟩,
    P.wx_refl_activeMargin⟩

section

variable {T T' : ℝ} {u u' : ℝ → Fin 3 → ℝ} {ρ : VertexRepresentation T u}
  {ρ' : VertexRepresentation T' u'} {c : Fin 3}

/-- Switch `k` of the image is forward iff switch `-2 - k` of the original is. -/
theorem m2_reflect_fwd_iff (hl : ∀ k, ρ'.label k = c - ρ.label (-1 - k)) (k : ℤ) :
    ρ'.IsForward k ↔ ρ.IsForward (-2 - k) := by
  unfold VertexRepresentation.IsForward
  rw [hl, hl, show -1 - (k + 1) = -2 - k by ring, show -1 - k = -2 - k + 1 by ring]
  constructor
  · intro h
    have : ρ.label (-2 - k) = ρ.label (-2 - k + 1) - 1 := by
      have := congrArg (fun x => c - x) h
      simp only [sub_sub_cancel] at this
      rw [this]; abel
    rw [this]; abel
  · intro h
    rw [h]; abel

/-- Switch `k` of the image is reverse iff switch `-2 - k` of the original is. -/
theorem m2_reflect_rev_iff (hl : ∀ k, ρ'.label k = c - ρ.label (-1 - k)) (k : ℤ) :
    ρ'.IsReverse k ↔ ρ.IsReverse (-2 - k) := by
  unfold VertexRepresentation.IsReverse
  rw [hl, hl, show -1 - (k + 1) = -2 - k by ring, show -1 - k = -2 - k + 1 by ring]
  constructor
  · intro h
    have : ρ.label (-2 - k) = ρ.label (-2 - k + 1) + 1 := by
      have := congrArg (fun x => c - x) h
      simp only [sub_sub_cancel] at this
      rw [this]; abel
    rw [this]; abel
  · intro h
    rw [h]; abel

/-- Maximal reverse runs correspond: `k, …, k + L - 1` in the image is `-1 - k - L, …, -2 - k`. -/
theorem m2_reflect_reverseRun_iff (hl : ∀ k, ρ'.label k = c - ρ.label (-1 - k)) (k : ℤ) (L : ℕ) :
    ρ'.IsReverseRun k L ↔ ρ.IsReverseRun (-1 - k - L) L := by
  unfold VertexRepresentation.IsReverseRun
  simp only [m2_reflect_fwd_iff hl, m2_reflect_rev_iff hl]
  constructor
  · rintro ⟨h1, hf0, hf1, hr⟩
    refine ⟨h1, ?_, ?_, fun j hj1 hj2 => ?_⟩
    · rw [show -1 - k - (L : ℤ) - 1 = -2 - (k + L) by ring]; exact hf1
    · rw [show -1 - k - (L : ℤ) + L = -2 - (k - 1) by ring]; exact hf0
    · have := hr (-2 - j) (by omega) (by omega)
      rwa [show -2 - (-2 - j) = j by ring] at this
  · rintro ⟨h1, hf0, hf1, hr⟩
    refine ⟨h1, ?_, ?_, fun j hj1 hj2 => hr (-2 - j) (by omega) (by omega)⟩
    · rw [show -2 - (k - 1) = -1 - k - (L : ℤ) + L by ring]; exact hf1
    · rw [show -2 - (k + (L : ℤ)) = -1 - k - L - 1 by ring]; exact hf0

/-- Maximal forward runs correspond. -/
theorem m2_reflect_forwardRun_iff (hl : ∀ k, ρ'.label k = c - ρ.label (-1 - k)) (k : ℤ) (L : ℕ) :
    ρ'.IsForwardRun k L ↔ ρ.IsForwardRun (-1 - k - L) L := by
  unfold VertexRepresentation.IsForwardRun
  simp only [m2_reflect_fwd_iff hl, m2_reflect_rev_iff hl]
  constructor
  · rintro ⟨h1, hf0, hf1, hr⟩
    refine ⟨h1, ?_, ?_, fun j hj1 hj2 => ?_⟩
    · rw [show -1 - k - (L : ℤ) - 1 = -2 - (k + L) by ring]; exact hf1
    · rw [show -1 - k - (L : ℤ) + L = -2 - (k - 1) by ring]; exact hf0
    · have := hr (-2 - j) (by omega) (by omega)
      rwa [show -2 - (-2 - j) = j by ring] at this
  · rintro ⟨h1, hf0, hf1, hr⟩
    refine ⟨h1, ?_, ?_, fun j hj1 hj2 => hr (-2 - j) (by omega) (by omega)⟩
    · rw [show -2 - (k - 1) = -1 - k - (L : ℤ) + L by ring]; exact hf1
    · rw [show -2 - (k + (L : ℤ)) = -1 - k - L - 1 by ring]; exact hf0

/-- The image of an M2 representation is M2. -/
theorem m2_reflect_classM2 (hl : ∀ k, ρ'.label k = c - ρ.label (-1 - k)) (h : ρ.ClassM2) :
    ρ'.ClassM2 := by
  obtain ⟨⟨⟨kf, hkf⟩, ⟨kr, hkr⟩⟩, hrev, ⟨k, L, hrun, hL⟩⟩ := h
  refine ⟨⟨⟨-2 - kf, ?_⟩, ⟨-2 - kr, ?_⟩⟩, fun k L hk => ?_, ⟨-1 - k - L, L, ?_, hL⟩⟩
  · rw [m2_reflect_fwd_iff hl, show -2 - (-2 - kf) = kf by ring]; exact hkf
  · rw [m2_reflect_rev_iff hl, show -2 - (-2 - kr) = kr by ring]; exact hkr
  · exact hrev _ _ ((m2_reflect_reverseRun_iff hl k L).1 hk)
  · rw [m2_reflect_forwardRun_iff hl, show -1 - (-1 - k - (L : ℤ)) - L = k by ring]; exact hrun

end

end SmoothedOctagon
