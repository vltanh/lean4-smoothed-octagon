module

public import Mathlib.Analysis.Convex.Deriv

/-!
# Endpoint comparisons on a real interval
-/

@[expose] public section

namespace SmoothedOctagon
open Set

theorem le_of_hasDerivAt_nonneg {f f' : ℝ → ℝ} {x y : ℝ} (hxy : x ≤ y)
    (hd : ∀ z ∈ Icc x y, HasDerivAt f (f' z) z)
    (hn : ∀ z ∈ Ioo x y, 0 ≤ f' z) : f x ≤ f y := by
  have hm : MonotoneOn f (Icc x y) := by
    apply monotoneOn_of_deriv_nonneg (convex_Icc x y)
    · exact fun z hz => (hd z hz).continuousAt.continuousWithinAt
    · intro z hz
      exact (hd z (interior_subset hz)).differentiableAt.differentiableWithinAt
    · intro z hz
      rw [(hd z (interior_subset hz)).deriv]
      exact hn z (by simpa only [interior_Icc] using hz)
  exact hm (left_mem_Icc.mpr hxy) (right_mem_Icc.mpr hxy) hxy


theorem concaveOn_min_endpoints_le {f : ℝ → ℝ} {lo hi x : ℝ}
    (hc : ConcaveOn ℝ (Icc lo hi) f) (hx : x ∈ Icc lo hi) :
    min (f lo) (f hi) ≤ f x := by
  have hle : lo ≤ hi := le_trans hx.1 hx.2
  apply hc.ge_on_segment ⟨le_rfl,hle⟩ ⟨hle,le_rfl⟩
  simpa only [segment_eq_Icc hle] using hx


end SmoothedOctagon
