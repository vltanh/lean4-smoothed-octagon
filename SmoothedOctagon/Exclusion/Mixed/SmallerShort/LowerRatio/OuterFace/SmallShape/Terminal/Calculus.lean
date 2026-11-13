module

public import SmoothedOctagon.Exclusion.Mixed.SmallerShort.LowerRatio.OuterFace.SmallShape.Norm
public import SmoothedOctagon.Exclusion.Mixed.Horner

/-!
# Endpoint comparison for a rational derivative

When the numerator of a rational derivative decreases and its denominator
is positive, the function has no interior minimum. At a point where the
numerator is nonnegative, compare with the left endpoint; otherwise compare
with the right endpoint.
-/

@[expose] public section
namespace SmoothedOctagon.LowerRatioTerminal
open Set

theorem endpoint_min {f P D : ℝ → ℝ} {p q t : ℝ} (hpt : p ≤ t) (htq : t ≤ q)
    (hd : ∀ s ∈ Icc p q, HasDerivAt f (P s / D s) s)
    (hD : ∀ s ∈ Icc p q, 0 < D s)
    (hP : ∀ s v, p ≤ s → s ≤ v → v ≤ q → P v ≤ P s) :
    min (f p) (f q) ≤ f t := by
  rcases le_or_gt 0 (P t) with ht | ht
  · have hf : f p ≤ f t := ss_le_of_deriv (f := f) (f' := fun s => P s / D s) hpt
      (fun s hs => hd s ⟨hs.1, hs.2.trans htq⟩)
      (fun s hs => div_nonneg (ht.trans (hP s t hs.1.le hs.2.le htq))
        (hD s ⟨hs.1.le, hs.2.le.trans htq⟩).le)
    exact (min_le_left _ _).trans hf
  · have hf : -f t ≤ -f q := ss_le_of_deriv (f := fun s => -f s) (f' := fun s => -(P s / D s)) htq
      (fun s hs => (hd s ⟨hpt.trans hs.1, hs.2⟩).neg)
      (fun s hs => neg_nonneg.mpr (div_nonpos_of_nonpos_of_nonneg
        ((hP t s hpt hs.1.le hs.2.le).trans ht.le)
        (hD s ⟨hpt.trans hs.1.le, hs.2.le⟩).le))
    exact (min_le_right _ _).trans (by linarith only [hf])

/-- The cleared numerator of the outer duration test before its constant gap. -/
def numerator {R : Type*} [CommRing R] (x a B u : R) : R :=
  let S := x + 1
  let K := 6 * a ^ 2 + 1
  let b := B - a
  let D := a ^ 2 + 2 * a * b + 1 + 2 * x - 2 * b * x
  let J := K * (S ^ 2 * (u - 1) + 1) + (2 * S - 1) * S
  let M := K ^ 2 - S * K + S ^ 2
  let W := S * (M + u * D ^ 2) - D * J
  let E := 2 * u * D * S - J
  let L := 2 * B + 7 * a
  2 * (4 * u * M * S ^ 2 - J ^ 2) * B * L ^ 3 - 12 * a * S * L ^ 3 * W +
    357 * a ^ 5 * S ^ 2 * L ^ 3 - 84 * (u - 1) * a ^ 3 * S ^ 2 * B ^ 2 * L ^ 3 +
    12 * a ^ 2 * S * B * L ^ 3 * E -
    224 * a ^ 4 * S ^ 2 * B * ((2 * B) ^ 3 - (7 * a) ^ 3) -
    72 * a ^ 4 * S ^ 2 * B * L ^ 3

theorem face_eq {x a b u : ℝ} (hx : 0 < x) (ha : 0 < a) (hB : 0 < a + b) :
    lroF1 x a b u = numerator x a (a + b) u /
      (1152 * a ^ 4 * (x + 1) ^ 2 * (a + b) * (2 * (a + b) + 7 * a) ^ 3) -
      9193 / 50000 := by
  rw [lro_F1_expl hx ha hB]
  have hS : x + 1 ≠ 0 := by linarith
  have hL : 2 * (a + b) + 7 * a ≠ 0 := by positivity
  simp only [numerator, lroM, lroJ, lroK, ssE0, ssDg]
  field_simp
  ring

end SmoothedOctagon.LowerRatioTerminal
