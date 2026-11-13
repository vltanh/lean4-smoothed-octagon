module

public import SmoothedOctagon.Exclusion.Mixed.Nonshort.Forward.LowT.Scale.BoundaryConcavity
public import SmoothedOctagon.Exclusion.Mixed.Nonshort.Forward.LowT.Scale.BoundaryEndpoints

/-!
# Positive scale derivative at maximum duration

Concavity in the order gap reduces the value to its two gap endpoints.
Their lower bounds therefore hold throughout the physical gap interval.
-/

@[expose] public section
namespace SmoothedOctagon.LowTScale

theorem boundary_floor {h j : ℝ} (h0 : 1 / 4 ≤ h) (h1 : h ≤ 1 / 3)
    (hj0 : 1 / 30 ≤ j) (hj1 : j ≤ 5 / 7 * h) :
    1 ≤ value h j ((h - j) / (1 + 2 * j)) := by
  have hjb : 5 / 7 * h ≤ 1 / 4 := by linarith only [h1]
  have hd : 0 < 1 + 2 * j := by linarith only [hj0]
  have hf := rational_boundary_floor (p := boundaryPolynomial h) (m := 1) hj0 hj1
    (fun s hs0 _ => by linarith only [hs0])
    (by
      intro s hs0 hs1
      rw [boundaryCurvature_eq]
      have hc := boundary_curvature_ceiling h0 h1 (by linarith only [hs0]) (hs1.trans hjb)
      linarith only [hc])
    (by
      rw [boundary_eval]
      apply (le_div_iff₀ (by norm_num : 0 < (1 + 2 * (1 / 30 : ℝ)) ^ 6)).mpr
      simpa only [one_mul] using
        (show (1 + 2 * (1 / 30 : ℝ)) ^ 6 ≤ 600 by norm_num).trans
          (boundary_small_gap_floor h0 h1))
    (by
      rw [boundary_eval]
      apply (le_div_iff₀ (pow_pos (by linarith only [h0] : 0 < 1 + 2 * (5 / 7 * h)) 6)).mpr
      simpa only [one_mul] using boundary_outer_gap_floor h0)
  calc
    1 ≤ (boundaryPolynomial h).eval j / (1 + 2 * j) ^ 6 := hf
    _ = value h j ((h - j) / (1 + 2 * j)) := by
      rw [boundary_eval, ← boundary_eq h j hd.ne']
      field_simp

end SmoothedOctagon.LowTScale
