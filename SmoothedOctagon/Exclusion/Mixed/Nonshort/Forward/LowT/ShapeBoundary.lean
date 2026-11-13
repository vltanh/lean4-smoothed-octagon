module

public import SmoothedOctagon.Exclusion.Mixed.Nonshort.Forward.LowT.Monomials
public import SmoothedOctagon.Exclusion.Mixed.Nonshort.UnitShape.Boundary

/-!
# The exact duration boundary of the low-scale shape derivative

The order gap increases the boundary polynomial. At its smallest permitted
value, concavity in the scale reduces the sign to the two scale endpoints.
-/

@[expose] public section

namespace SmoothedOctagon

/-- The numerator on the swap boundary, after cancelling the positive square `W²`. -/
def nltShapeEdge {R : Type*} [CommRing R] (h j : R) : R :=
  h ^ 2 * (h + 1) * (20 * h ^ 5 + 672 * h ^ 4 - 157 * h ^ 3 - 1245 * h ^ 2 - 502 * h + 224)
  + h * (h + 1) * (2264 * h ^ 5 - 458 * h ^ 4 - 6715 * h ^ 3 - 1389 * h ^ 2 + 2956 * h + 128) * j
  + (h + 1) * (1880 * h ^ 6 + 448 * h ^ 5 - 13688 * h ^ 4 - 97 * h ^ 3 + 13865 * h ^ 2 + 890 * h - 16) * j ^ 2
  + (1592 * h ^ 6 - 11228 * h ^ 5 - 12604 * h ^ 4 + 31261 * h ^ 3 + 33834 * h ^ 2 + 1629 * h - 480) * j ^ 3
  - 2 * (2464 * h ^ 5 + 5084 * h ^ 4 - 14170 * h ^ 3 - 19367 * h ^ 2 + 721 * h + 1562) * j ^ 4
  - 2 * (2960 * h ^ 4 - 3894 * h ^ 3 - 9855 * h ^ 2 + 4066 * h + 3951) * j ^ 5
  - 4 * (22 * h ^ 3 - 1031 * h ^ 2 + 2148 * h + 2033) * j ^ 6
  + 8 * (149 * h ^ 2 - 315 * h - 310) * j ^ 7

private noncomputable def edgeJ (h : ℝ) : Polynomial ℝ :=
  nltShapeEdge (Polynomial.C h) Polynomial.X

private noncomputable def edgeH : Polynomial ℝ :=
  nltShapeEdge Polynomial.X (Polynomial.C (1 / 30))

private theorem edgeJ_eval (h j : ℝ) : (edgeJ h).eval j = nltShapeEdge h j := by
  simp [edgeJ, nltShapeEdge]

private theorem edgeH_eval (h : ℝ) : edgeH.eval h = nltShapeEdge h (1 / 30) := by
  simp [edgeH, nltShapeEdge]

/-- Endpoint power bounds give a positive derivative throughout the order interval. -/
private theorem edge_deriv_pos {h j : ℝ} (h0 : 1 / 4 ≤ h) (h1 : h ≤ 1 / 3)
    (hj : 0 ≤ j) (hj1 : j ≤ 1 / 4) : 0 ≤ (edgeJ h).derivative.eval j := by
  have lower : 120 + 2200 * j + 6900 * j ^ 2 - 3600 * j ^ 3 - 47000 * j ^ 4
      - 65000 * j ^ 5 - 23000 * j ^ 6 ≤ (edgeJ h).derivative.eval j := by
    have lo (i k : ℕ) := nlt_lo i k rfl (by norm_num : (0 : ℝ) ≤ 1 / 4) h0 hj
    have hi (i k : ℕ) := nlt_hi i k rfl (by linarith only [h0] : (0 : ℝ) ≤ h) h1 hj
    norm_num [edgeJ, nltShapeEdge, Polynomial.derivative_mul, Polynomial.derivative_pow]
    nlinarith only [lo 7 1, lo 7 0, lo 6 2, lo 6 1, lo 6 0, hi 5 3, hi 5 2, hi 5 1, hi 5 0, hi 4 4, hi 4 3, hi 4 2, hi 4 1, hi 4 0, hi 3 5, lo 3 4, lo 3 3, lo 3 2, lo 3 1, lo 3 0, lo 2 6, lo 2 5, lo 2 4, lo 2 3, lo 2 2, lo 2 1, lo 2 0, hi 1 6, hi 1 5, hi 1 4, hi 1 3, lo 1 2, lo 1 1, lo 1 0, pow_nonneg hj 1, pow_nonneg hj 2, pow_nonneg hj 3, pow_nonneg hj 4, pow_nonneg hj 5, pow_nonneg hj 6]
  have p3 := nlt_pw hj hj1 2
  have p4 := nlt_pw hj hj1 3
  have p5 := nlt_pw hj hj1 4
  have p6 := nlt_pw hj hj1 5
  nlinarith only [lower, p3, p4, p5, p6, hj, sq_nonneg j]

private theorem edge_concave {h : ℝ} (h0 : 1 / 4 ≤ h) (h1 : h ≤ 1 / 3) :
    edgeH.derivative.derivative.eval h ≤ 0 := by
  obtain ⟨u, rfl⟩ : ∃ u, h = u + 1 / 4 := ⟨h - 1 / 4, by ring⟩
  have hu : 0 ≤ u := by linarith only [h0]
  have hu1 : u ≤ 1 / 12 := by linarith only [h1]
  have p3 := nlt_pw hu hu1 2
  have p4 := nlt_pw hu hu1 3
  have p5 := nlt_pw hu hu1 4
  have p6 := nlt_pw hu hu1 5
  norm_num [edgeH, nltShapeEdge, Polynomial.derivative_mul, Polynomial.derivative_pow]
  nlinarith only [p3, p4, p5, p6, hu, sq_nonneg u]

/-- Positivity on the scale and order rectangle. -/
theorem nltShapeEdge_pos {h j : ℝ} (h0 : 1 / 4 ≤ h) (h1 : h ≤ 1 / 3)
    (hj : 1 / 30 ≤ j) (hj1 : j ≤ 1 / 4) : 0 < nltShapeEdge h j := by
  have floor := UnitShape.polynomial_floor (p := edgeH) (m := 1) h0 h1
    (fun s hs hs1 => edge_concave hs hs1)
    (by norm_num [edgeH, nltShapeEdge]) (by norm_num [edgeH, nltShapeEdge])
  have mono := UnitShape.polynomial_mono (p := edgeJ h) hj
    (fun s hs hs1 => edge_deriv_pos h0 h1 (by linarith only [hs]) (hs1.trans hj1))
  rw [edgeH_eval] at floor
  simp only [edgeJ_eval] at mono
  linarith only [floor, mono]

end SmoothedOctagon
