module

public import SmoothedOctagon.Period.Costate
public import SmoothedOctagon.Exclusion.Forward.Scalar
public import SmoothedOctagon.Exclusion.Forward.Wire

/-!
# Case F: the costate interface

The facts about the normal multiplier of a costate cycle that the all-forward exclusion consumes,
stated in the coordinates of `Period/Elliptic.lean` on a `CostateCycle`, and proved from its API
through `Exclusion/Forward/Wire.lean`. The definitions `ff_mu`, `ff_gam2`, `ff_wt` are
definitionally `CostateCycle.mu`, `gam2`, `wt`.

## Coordinates (`MIXED_GLOBAL_COSTATE_ELLIPTIC` §§2-4)

* `ff_mu k j = μ_j = p_j(𝒰)` at the switch `k`, where `𝒰 = (1/√12) X⁻¹ Λ₁ X` is the normal
  multiplier `U = (1/√12) Ad_{X₀⁻¹} Λ₁(0)` conjugated by the tangent frame:
  `μ_j = -α_j/(2√3) - (p₀ + p₁ + p₂) p_j/4 + 1/2`.
* `ff_gam2 k = γ² = det 𝒰 = (μ₀μ₁ + μ₁μ₂ + μ₂μ₀)/4`.
* `ff_wt k = w_k = -μ_{i_k}` (`= tr(U Z_k) = 2 (M_k)₁₁`); the switch norm after piece `k` is
  `d_k = (w_k + w_{k+1})/(2 s_k²)` and the cross pairing on piece `k` is `e_k = w_k/(2 K_k)`.
* The window coordinates of MIXED_GLOBAL_SMALL_FORWARD_MINIMUM (5) at the piece `m`:
  `ff_u m = u = 8 d_{m-1}`, `ff_v m = v = 8 d_m`, `ff_E m = E = 16 e_m`.

## The interface

For a costate cycle with every switch forward (`i_{k+1} = i_k + 1`), active margins
`(p, b, a, c, d) = (a_{m-2}, …, a_{m+2})`:
* `ff_rows`: the three stationarity rows MIXED (6)-(8) (from `CostateCycle.stationarity`,
  MGCE (8)/(14), at the pieces `m - 1`, `m`, `m + 1` and the transport of the weights across the
  pieces `m` and `m + 1`, `ifc_w_rel`; MIXED (9)).
* `ff_floors`: the exterior floors MIXED (11) (from the missing-control inequality `σ ≤ 0` at the
  switches `m - 1` and `m + 2`, `ifc_mc`; MIXED (11a)-(12)).
* `ff_gram`: `γ² = (a² + 4)²(4uv - E²)/256` (MGCE (14), `gram_pp`).
* `NormalPeriod.ff_gam2_eq`: `γ² = det Λ₁(0)/12` for the cycle of a normal period.
* `NormalPeriod.ff_cost_casimir`: negative ellipticity of `Λ₁` (GLOBAL_STRUCTURE_FORWARD_ELLIPTIC,
  MGCE (1)) and the spectral cost–Casimir bound `C ≥ (π/3)(κ + 3/2)`, `κ² = det Λ₁(0)`
  (GLOBAL_SPECTRAL_COST_CASIMIR (1)).
-/

@[expose] public section

namespace SmoothedOctagon

open SmoothedPolygons Real

namespace CostateCycle

variable {N : ℕ} (C : CostateCycle N)

/-- `μ_j = p_j(𝒰)` at the switch `k` (`Period/Elliptic`: `CostateCycle.mu`). -/
noncomputable def ff_mu (k : ℤ) (j : Fin 3) : ℝ :=
  -(C.α k j / (2 * √3)) - (C.m k 0 + C.m k 1 + C.m k 2) * C.m k j / 4 + 1 / 2

/-- `γ² = det 𝒰 = (μ₀μ₁ + μ₁μ₂ + μ₂μ₀)/4` at the switch `k` (`CostateCycle.gam2`). -/
noncomputable def ff_gam2 (k : ℤ) : ℝ :=
  (C.ff_mu k 0 * C.ff_mu k 1 + C.ff_mu k 1 * C.ff_mu k 2 + C.ff_mu k 2 * C.ff_mu k 0) / 4

/-- `w_k = -μ_{i_k}` on piece `k` (`CostateCycle.wt`). -/
noncomputable def ff_wt (k : ℤ) : ℝ := -C.ff_mu k (C.lab k)

/-- `ff_wt` is `Period/Elliptic`'s `CostateCycle.wt`. -/
private theorem ff_wt_eq (k : ℤ) : C.ff_wt k = C.wt k := rfl

/-- `u = 8 d_{m-1} = 4 (w_{m-1} + w_m)/(a_{m-1} + a_m)²`. -/
noncomputable def ff_u (m : ℤ) : ℝ := 4 * (C.ff_wt (m - 1) + C.ff_wt m) / (C.act (m - 1) + C.act m) ^ 2

/-- `v = 8 d_m = 4 (w_m + w_{m+1})/(a_m + a_{m+1})²`. -/
noncomputable def ff_v (m : ℤ) : ℝ := 4 * (C.ff_wt m + C.ff_wt (m + 1)) / (C.act m + C.act (m + 1)) ^ 2

/-- `E = 16 e_m = 8 w_m/(a_m² + 4)`. -/
noncomputable def ff_E (m : ℤ) : ℝ := 8 * C.ff_wt m / (C.act m ^ 2 + 4)

/-- **The three stationarity rows at an all-forward window** (MIXED_GLOBAL_SMALL_FORWARD_MINIMUM
(6)-(8), from MGCE (8)): `CostateCycle.stationarity` at the pieces `m - 1`, `m`, `m + 1`, with the
transport of the weights across the pieces `m` and `m + 1` (MIXED (9)); `ifc_rows_alg`. -/
theorem ff_rows (hF : ∀ k, C.lab (k + 1) = C.lab k + 1) (m : ℤ) :
    let p := C.act (m - 2); let b := C.act (m - 1); let a := C.act m; let c := C.act (m + 1)
    let d := C.act (m + 2)
    (a + b) * C.ff_u m + (a + c) * C.ff_v m - a * C.ff_E m = ff_Cph b a c ∧
      ff_Mn a b (ff_fac p b a) * C.ff_u m + ff_Mm a b (ff_fac b a c) (ff_fac p b a) * C.ff_v m =
        ff_Mal a b (ff_fac p b a) * ff_Cph b a c - ff_Cph p b a ∧
      ff_Mm a c (ff_fac b a c) (ff_fac a c d) * C.ff_u m + ff_Mn a c (ff_fac a c d) * C.ff_v m =
        ff_Mal a c (ff_fac a c d) * ff_Cph b a c - ff_Cph a c d := by
  intro p b a c d
  have hf : ∀ k, C.lab k = C.lab (k - 1) + 1 := fun k ↦ by
    have := hF (k - 1); rwa [sub_add_cancel] at this
  have hs : ∀ k, C.sgn (k - 1) = C.sgn k := fun k ↦ by
    rw [C.sgn_fwd (by rw [sub_add_cancel]; exact hf k), C.sgn_fwd (hF k)]
  have sL := C.ifc_stat_w (hs (m - 1))
  have s0 := C.ifc_stat_w (hs m)
  have sR := C.ifc_stat_w (hs (m + 1))
  rw [show m - 1 - 1 = m - 2 by ring, sub_add_cancel] at sL
  rw [add_sub_cancel_right, show m + 1 + 1 = m + 2 by ring] at sR
  have rL := C.ifc_w_rel (k := m) (by rw [show m - 2 = m - 1 - 1 by ring]; exact hf (m - 1))
    (hf m) (hF m)
  have rR := C.ifc_w_rel (k := m + 1) (by
      rw [show m + 1 - 2 = m - 1 by ring, add_sub_cancel_right]; exact hf m) (hf (m + 1)) (hF (m + 1))
  rw [show m + 1 - 2 = m - 1 by ring, add_sub_cancel_right, show m + 1 + 1 = m + 2 by ring] at rR
  have fL := C.factor_pp (hf (m - 1)) (hF (m - 1))
  have f0 := C.factor_pp (hf m) (hF m)
  have fR := C.factor_pp (hf (m + 1)) (hF (m + 1))
  simp only [CostateCycle.sw, show m - 1 - 1 = m - 2 by ring, sub_add_cancel,
    add_sub_cancel_right, show m + 1 + 1 = m + 2 by ring, show m - 2 + 1 = m - 1 by ring] at fL f0 fR
  simp only [ff_u, ff_v, ff_E, ff_wt_eq]
  exact ifc_rows_alg (C.act_pos _) (C.act_pos _) (C.act_pos _) (C.act_pos _) (C.act_pos _) fL f0 fR
    rL rR sL s0 sR

/-- **The two exterior floors** (MIXED_GLOBAL_SMALL_FORWARD_MINIMUM (11)): the missing-control
inequality `σ ≤ 0` at the exterior switches `m - 1` and `m + 2` of five consecutive pieces with
forward switches gives `u ≥ F_{b/(a+b)}(h)` and `v ≥ F_{c/(a+c)}(k)` (MIXED (11a)-(12);
`CostateCycle.ifc_floor_out`, `ifc_floor_in`). -/
theorem ff_floors (hF : ∀ k, C.lab (k + 1) = C.lab k + 1) (m : ℤ) :
    let p := C.act (m - 2); let b := C.act (m - 1); let a := C.act m; let c := C.act (m + 1)
    let d := C.act (m + 2)
    ff_F (b / (a + b)) (ff_fac p b a) ≤ C.ff_u m ∧ ff_F (c / (a + c)) (ff_fac a c d) ≤ C.ff_v m := by
  intro p b a c d
  have hf : ∀ k, C.lab k = C.lab (k - 1) + 1 := fun k ↦ by
    have := hF (k - 1); rwa [sub_add_cancel] at this
  have fo := C.ifc_floor_out (hf (m - 1)) (hF (m - 1))
  have fi := C.ifc_floor_in (hf (m + 1)) (hF (m + 1))
  rw [sub_add_cancel] at fo
  rw [add_sub_cancel_right] at fi
  have fL := C.factor_pp (hf (m - 1)) (hF (m - 1))
  have fR := C.factor_pp (hf (m + 1)) (hF (m + 1))
  simp only [CostateCycle.sw, show m - 1 - 1 = m - 2 by ring, sub_add_cancel,
    add_sub_cancel_right, show m + 1 + 1 = m + 2 by ring, show m - 2 + 1 = m - 1 by ring] at fL fR
  have hK1 : 0 < C.act (m - 1) ^ 2 + 4 := by positivity
  have hK2 : 0 < C.act (m + 1) ^ 2 + 4 := by positivity
  have hq1 : C.q (m - 1) = ff_fac p b a := by
    simp only [ff_fac, p, b, a]; field_simp; linarith
  have hq2 : C.q (m + 1) = ff_fac a c d := by
    simp only [ff_fac, a, c, d]; field_simp; linarith
  have h1 := C.act_pos (m - 1)
  have h2 := C.act_pos m
  have h3 := C.act_pos (m + 1)
  have eu : C.ff_u m = 8 * C.swd (m - 1) := by
    simp only [ff_u, ff_wt_eq, CostateCycle.swd, sub_add_cancel]; field_simp; ring
  have ev : C.ff_v m = 8 * C.swd m := by
    simp only [ff_v, ff_wt_eq, CostateCycle.swd]; field_simp; ring
  rw [eu, ev, ← hq1, ← hq2]
  refine ⟨?_, ?_⟩
  · rw [show a + b = b + a by ring]; exact fo
  · exact fi

/-- **The Gram identity at the central piece** (MGCE (14), `gram_pp`):
`d_{m-1} d_m - e_m² = γ²/K_m²`, i.e. `γ² = (a² + 4)²(4uv - E²)/256` (`CostateCycle.gram_pp`). -/
theorem ff_gram (hF : ∀ k, C.lab (k + 1) = C.lab k + 1) (m : ℤ) :
    C.ff_gam2 m = (C.act m ^ 2 + 4) ^ 2 * (4 * C.ff_u m * C.ff_v m - C.ff_E m ^ 2) / 256 := by
  have hin : C.lab m = C.lab (m - 1) + 1 := by have := hF (m - 1); rwa [sub_add_cancel] at this
  have hg := C.gram_pp hin (hF m)
  have h1 := C.act_pos (m - 1)
  have h2 := C.act_pos m
  have h3 := C.act_pos (m + 1)
  have hK : 0 < C.act m ^ 2 + 4 := by positivity
  have eu : C.ff_u m = 8 * C.swd (m - 1) := by
    simp only [ff_u, ff_wt_eq, CostateCycle.swd, sub_add_cancel]; field_simp; ring
  have ev : C.ff_v m = 8 * C.swd m := by
    simp only [ff_v, ff_wt_eq, CostateCycle.swd]; field_simp; ring
  have eE : C.ff_E m = 16 * C.cre m := by
    simp only [ff_E, ff_wt_eq, CostateCycle.cre]; field_simp; ring
  have eg : C.ff_gam2 m = C.gam2 m := rfl
  rw [eu, ev, eE, eg]
  field_simp at hg
  linear_combination (-1 : ℝ) * hg

end CostateCycle

namespace NormalPeriod

variable (P : NormalPeriod)

/-- **`γ² = det Λ₁(0)/12`** at every switch: `𝒰 = (1/√12) X⁻¹ Λ₁ X` and `Λ₁` is conserved up to
conjugation (`Λ₁_eq_conj`) and relabeled by the twist (`gam2_eq`, `det_Λ₁_zero`). -/
theorem ff_gam2_eq (k : ℤ) : P.costateCycle.ff_gam2 k = (P.Λ₁ 0).det / 12 := by
  rw [P.det_Λ₁_zero, show P.costateCycle.ff_gam2 k = P.costateCycle.gam2 k from rfl,
    P.costateCycle.gam2_eq]
  ring

/-- **Ellipticity and the spectral cost–Casimir bound.** For an all-forward normal period the
primary costate is negative elliptic (GLOBAL_STRUCTURE_FORWARD_ELLIPTIC, MGCE (1)); with
`κ = √(det Λ₁(0))` the cost satisfies `C ≥ (π/3)(κ + 3/2)` (GLOBAL_SPECTRAL_COST_CASIMIR (1)).
Route: `γ² > 0` by the projective argument of `gam2_pos_of_mixed` (`ifc_gam2_pos_of_allForward`),
then `Λ₁_zero_neg` and the spectral winding bound `ifc_spectral`. -/
theorem ff_cost_casimir (hF : P.rep.AllForward) :
    0 < (P.Λ₁ 0).det ∧ π / 3 * (√((P.Λ₁ 0).det) + 3 / 2) ≤ P.cost := by
  have hpos := P.ifc_gam2_pos_of_allForward hF
  have hd : 0 < P.costateCycle.swd ((0 : ℕ) : ℤ) := by
    have := P.costateCycle.swd_fwd (k := 0) (hF 0)
    have := CostateCycle.elJ_ge _ _ (P.costateCycle.act_pos 0) (P.costateCycle.act_pos (0 + 1))
    push_cast; linarith
  obtain ⟨hdet, h10⟩ := P.ifc_negEll hpos hd
  exact ⟨hdet, P.ifc_spectral hdet h10⟩

end NormalPeriod

end SmoothedOctagon
