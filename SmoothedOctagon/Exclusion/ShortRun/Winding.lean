module

public import SmoothedOctagon.Exclusion.ShortRun.Centre
public import SmoothedOctagon.Exclusion.ShortRun.Wind.Main

/-!
# Case M1: the projective winding of the centre angles

`MIXED_GLOBAL_PROJECTIVE_WINDING` (1)-(2) for the all-short word `(− − +)^m`: with the switch
vectors of `MIXED_GLOBAL_COSTATE_ELLIPTIC` collapsed at the turns, the `m` centre angles
`φ_j ∈ (0, π)` (unsigned angles in the positive definite metric `S = -J₀U`, with
`cos φ_j = e_j / √(d_- d_+) = E_j / (2 √(u_j v_j))`) sum to `(m + 1) π / 3` over one period.

Route (differs from MGPW §§1-3, which lift the frame to the universal cover of `SL₂(ℝ)`): the
proof works with continuous real angle functions only (`Exclusion/ShortRun/Wind/`). The low-cost
winding theorem fixes the continuous polar angle of the competitive frame `g` at exactly `π/3`
(`wd_polar`); the canonical continuous angle `κ` from a base vector `ω` to its image `L g X ω`
(`wd_kap`) gives each centre angle as `π/3 + κ(b_out) - κ(b_in)` (`wd_centre`), is constant along
the pieces where the tracked base vector is an eigenvector of the tangent factor
(`wd_track_range`), and gains `π/3` at the seam (`wd_seam`); the sum telescopes
(`wd_winding_aux`). The window is moved to the seam by periodicity (`wd_sum_shift`).

## Main API

* `m1_winding`.
-/

@[expose] public section

namespace SmoothedOctagon

open Real

/-- **The all-short winding identity** (MGPW (2), MGSRAE (2)). Route: continuous angle functions
instead of the universal cover of `SL₂(ℝ)` (see the module docstring). -/
theorem m1_winding (P : NormalPeriod) (hc : P.IsCompetitive) {k₀ : ℤ} {m : ℕ}
    (hpat : P.m1_IsPattern k₀) (hN : P.N = 3 * m) (hpos : 0 < P.costateCycle.gam2 0) :
    ∑ j ∈ Finset.range m, Real.arccos (P.m1_E (m1_centre k₀ j) /
      (2 * √(P.m1_u (m1_centre k₀ j) * P.m1_v (m1_centre k₀ j)))) = (m + 1) * π / 3 := by
  set C := P.costateCycle with hC
  set F : ℤ → ℝ := fun c ↦ Real.arccos (C.cre c / √(C.swd (c - 1) * C.swd c)) with hF
  have hterm : ∀ c : ℤ, Real.arccos (P.m1_E c / (2 * √(P.m1_u c * P.m1_v c))) = F c := by
    intro c
    simp only [hF, NormalPeriod.m1_E, NormalPeriod.m1_u, NormalPeriod.m1_v]
    congr 1
    rw [show 8 * C.swd (c - 1) * (8 * C.swd c) = 8 ^ 2 * (C.swd (c - 1) * C.swd c) by ring,
      Real.sqrt_mul (by norm_num), Real.sqrt_sq (by norm_num)]
    ring
  simp only [hterm]
  -- periodicity in the centre index
  have hFN : ∀ c : ℤ, F (c + P.N) = F c := by
    intro c
    simp only [hF]
    rw [C.wd_cre_add, show c + (P.N : ℤ) - 1 = c - 1 + P.N by ring, C.wd_swd_add, C.wd_swd_add]
  have hper : ∀ j : ℤ, F (m1_centre k₀ (j + m)) = F (m1_centre k₀ j) := by
    intro j
    rw [show m1_centre k₀ (j + m) = m1_centre k₀ j + P.N by
      simp only [m1_centre]; rw [hN]; push_cast; ring, hFN]
  -- move the window to the seam
  set q := (k₀ + 1) / 3 with hq
  have hpat' : P.m1_IsPattern (k₀ - 3 * q) := by
    intro j
    have := hpat (j - q)
    rw [show k₀ + 3 * (j - q) = k₀ - 3 * q + 3 * j by ring] at this
    exact this
  have hk := wd_winding_aux P hc hpat' hN hpos (by omega) (by omega)
  have hs := wd_sum_shift (f := fun j ↦ F (m1_centre k₀ j)) hper (-q)
  rw [← hs, ← hk]
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  show F _ = F _
  congr 1
  simp only [m1_centre]
  ring

end SmoothedOctagon
