module

public import SmoothedOctagon.Exclusion.Mixed.Nonshort.Forward.LowT.Faces
public import SmoothedOctagon.Exclusion.Mixed.Nonshort.Forward.LowT.MaxDuration
public import SmoothedOctagon.Exclusion.Mixed.Nonshort.Forward.LowT.Monotone

/-!
# Case M2, forward successor: the low-`t` unit-shape sign

On the low-`t` domain `1/3 ≤ t ≤ 3/8`, `j = 2t + x - 1 ≥ 1/30`, `7x ≤ 12(1 - 2t)`, `1 ≤ q`,
`q(4t + 2x - 1) ≤ 1 + x`, at `k = 1`, the residual `G_n` with the low-`t` multipliers is positive
(`nlt_unit_pos`). Its positive multiple `S` increases in `h` at fixed `j`, `y` (`nlt_HS_pos`), so
`S(h, j, y) ≥ S(h₀, j, y)` with `h₀ = max(1/4, 7j/5, j + (1 + 2j)y)`, and the three faces are
positive (`nlt_face_unit`, `nlt_face_outer`, `nlt_face_qmax`) (`nlt_S_pos`).

## Main API

* `nlt_S_pos`, `nlt_unit_pos`.
-/

@[expose] public section

namespace SmoothedOctagon

/-- **The circuit is positive** on the low-`t` unit domain:
`1/4 ≤ h ≤ 1/3`, `1/30 ≤ j ≤ 5h/7`, `0 ≤ y`, `y(1 + 2j) ≤ h - j`. -/
theorem nlt_S_pos {h j y : ℝ} (h1 : 1 / 4 ≤ h) (h2 : h ≤ 1 / 3) (j1 : 1 / 30 ≤ j)
    (j2 : j ≤ 5 / 7 * h) (hy0 : 0 ≤ y) (hy : y * (1 + 2 * j) ≤ h - j) : 0 < polyHorner (nltL0 j) h + polyHorner (nltL1 j) h * y + polyHorner (nltL2 j) h * y ^ 2 + polyHorner (nltL3 j) h * y ^ 3 + polyHorner (nltL4 j) h * y ^ 4 + polyHorner (nltL5 j) h * y ^ 5 + polyHorner (nltL6 j) h * y ^ 6 := by
  have hd : ∀ s, HasDerivAt (fun s => polyHorner (nltL0 j) s + polyHorner (nltL1 j) s * y + polyHorner (nltL2 j) s * y ^ 2 + polyHorner (nltL3 j) s * y ^ 3 + polyHorner (nltL4 j) s * y ^ 4 + polyHorner (nltL5 j) s * y ^ 5 + polyHorner (nltL6 j) s * y ^ 6) (polyHorner (nltDer (nltL0 j)) s + polyHorner (nltDer (nltL1 j)) s * y + polyHorner (nltDer (nltL2 j)) s * y ^ 2 + polyHorner (nltDer (nltL3 j)) s * y ^ 3 + polyHorner (nltDer (nltL4 j)) s * y ^ 4 + polyHorner (nltDer (nltL5 j)) s * y ^ 5 + polyHorner (nltDer (nltL6 j)) s * y ^ 6) s := fun s => (((((((nlt_hasDerivAt_horner (nltL0 j) s).add ((nlt_hasDerivAt_horner (nltL1 j) s).mul_const y)).add ((nlt_hasDerivAt_horner (nltL2 j) s).mul_const (y ^ 2))).add ((nlt_hasDerivAt_horner (nltL3 j) s).mul_const (y ^ 3))).add ((nlt_hasDerivAt_horner (nltL4 j) s).mul_const (y ^ 4))).add ((nlt_hasDerivAt_horner (nltL5 j) s).mul_const (y ^ 5))).add ((nlt_hasDerivAt_horner (nltL6 j) s).mul_const (y ^ 6)))
  have mono : ∀ h0, 1 / 4 ≤ h0 → h0 ≤ h → 7 / 5 * j ≤ h0 → j + (1 + 2 * j) * y ≤ h0 →
      polyHorner (nltL0 j) h0 + polyHorner (nltL1 j) h0 * y + polyHorner (nltL2 j) h0 * y ^ 2 + polyHorner (nltL3 j) h0 * y ^ 3 + polyHorner (nltL4 j) h0 * y ^ 4 + polyHorner (nltL5 j) h0 * y ^ 5 + polyHorner (nltL6 j) h0 * y ^ 6 ≤ polyHorner (nltL0 j) h + polyHorner (nltL1 j) h * y + polyHorner (nltL2 j) h * y ^ 2 + polyHorner (nltL3 j) h * y ^ 3 + polyHorner (nltL4 j) h * y ^ 4 + polyHorner (nltL5 j) h * y ^ 5 + polyHorner (nltL6 j) h * y ^ 6 := fun h0 a b c d =>
    poly_mono hd (a := h0) (b := h) (fun s s1 s2 =>
      (nlt_HS_pos (by linarith) (by linarith) j1 (by linarith) hy0 (by nlinarith)).le) le_rfl b le_rfl
  rcases le_total (7 / 5 * j) (1 / 4) with cb | cb
  · rcases le_total (j + (1 + 2 * j) * y) (1 / 4) with cc | cc
    · -- the initial face `h₀ = 1/4`
      have m := mono (1 / 4) le_rfl h1 cb cc
      have face := nlt_face_unit (x := 1 / 4 + j) (y := y) (by linarith) (by linarith) hy0
        (by nlinarith)
      have e : (3 / 8 : ℝ) = (1 - 1 / 4) / 2 := by norm_num
      rw [e, nlt_St_h0, nlt_St_h1, nlt_St_h2, nlt_St_h3, nlt_St_h4, nlt_St_h5, nlt_St_h6] at face
      linarith
    · -- the maximum-duration face `h₀ = j + (1 + 2j)y`
      have m := mono (j + (1 + 2 * j) * y) cc (by nlinarith) (by linarith) le_rfl
      have face := nlt_face_qmax (h := j + (1 + 2 * j) * y) (j := j) cc (by nlinarith) j1
        (by linarith)
      have ey : (j + (1 + 2 * j) * y - j) / (1 + 2 * j) = y := by
        field_simp; ring
      rw [ey, nlt_St_h0, nlt_St_h1, nlt_St_h2, nlt_St_h3, nlt_St_h4, nlt_St_h5, nlt_St_h6] at face
      linarith
  · rcases le_total (j + (1 + 2 * j) * y) (7 / 5 * j) with cc | cc
    · -- the outer face `h₀ = 7j/5`
      have m := mono (7 / 5 * j) cb (by linarith) le_rfl cc
      have hy2 : y ≤ 2 / 31 := by
        by_contra hc; push Not at hc
        nlinarith [mul_pos (sub_pos.2 hc) (by linarith : (0 : ℝ) < 1 + 2 * j)]
      have face := nlt_face_outer (x := 7 / 5 * j + j) (y := y) (by linarith) (by linarith) hy0 hy2
      have e : (12 - 7 * (7 / 5 * j + j)) / 24 = (1 - 7 / 5 * j) / 2 := by ring
      rw [e, nlt_St_h0, nlt_St_h1, nlt_St_h2, nlt_St_h3, nlt_St_h4, nlt_St_h5, nlt_St_h6] at face
      linarith
    · -- the maximum-duration face `h₀ = j + (1 + 2j)y`
      have m := mono (j + (1 + 2 * j) * y) (by linarith) (by nlinarith) (by linarith) le_rfl
      have face := nlt_face_qmax (h := j + (1 + 2 * j) * y) (j := j) (by linarith) (by nlinarith) j1
        (by linarith)
      have ey : (j + (1 + 2 * j) * y - j) / (1 + 2 * j) = y := by
        field_simp; ring
      rw [ey, nlt_St_h0, nlt_St_h1, nlt_St_h2, nlt_St_h3, nlt_St_h4, nlt_St_h5, nlt_St_h6] at face
      linarith

/-- **The unit-shape sign** at `k = 1`: on `1/3 ≤ t ≤ 3/8`,
`j = 2t + x - 1 ≥ 1/30`, `7x ≤ 12(1 - 2t)`, `1 ≤ q`, `q(4t + 2x - 1) ≤ 1 + x`, the combined residual
with the low-`t` multipliers, `V_L`, `L₊` and `F_ℓ` is positive. -/
theorem nlt_unit_pos {t x q : ℝ} (ht0 : 1 / 3 ≤ t) (ht1 : t ≤ 3 / 8) (hj : 1 / 30 ≤ 2 * t + x - 1)
    (hjh : 7 * x ≤ 12 * (1 - 2 * t)) (hq : 1 ≤ q) (hqs : q * (4 * t + 2 * x - 1) ≤ 1 + x) :
    0 < nsfComb (nltAl q) (nltM t x q) t x 1 q (hrlVL t x) (nsrLp q) (nsrFl t x q) := by
  have hx : 0 < x := by linarith
  have hq0 : 0 < q := by linarith
  have hS := nlt_S_pos (h := 1 - 2 * t) (j := 2 * t + x - 1) (y := q - 1) (by linarith)
    (by linarith) hj (by linarith) (by linarith) (by nlinarith)
  rw [← nlt_St_h0, ← nlt_St_h1, ← nlt_St_h2, ← nlt_St_h3, ← nlt_St_h4, ← nlt_St_h5, ← nlt_St_h6] at hS
  have e1 : (1 - (1 - 2 * t)) / 2 = t := by ring
  have e2 : 1 - 2 * t + (2 * t + x - 1) = x := by ring
  rw [e1, e2] at hS
  have split := nlt_S_split t x (q - 1)
  rw [show 1 + (q - 1) = q by ring] at split
  rw [← nlt_link t x q hq0 hx] at split
  have : 0 < 24 * (q + 1) * (1 + x) * (17 * x + 76) *
      nsfComb (nltAl q) (nltM t x q) t x 1 q (hrlVL t x) (nsrLp q) (nsrFl t x q) := by linarith
  exact pos_of_mul_pos_right this (by positivity)

end SmoothedOctagon
