module

public import SmoothedOctagon.Exclusion.Mixed.Short.Window

/-!
# Case M2, smaller-short window: the algebra of the window-defect field

The window cost and the endpoint traces of the window-defect field, as identities of real
algebra at the window point `pt = (a/(a + C), B/C - 1, A/a, a²/(a² + 4), v, E)` of the cover
`Certificates.SmallerShort`.

The window is read in the rotated triangular coordinates of its first piece (label `i`, margins
`(C, a, n)` at the central switch, `(A, B, p)` at the far switch, in the label order
`i, i + 1, i - 1`): the states are `df_tri C a`, `df_tri A B`, the two tangent factors are
`triFactor 0 q₁`, `triFactor 1 q₂` (`q₁ = (C + B)/(a + C)`, `q₂ = (C + B)/(B + A)`), the relative
frame is `M = -X_s T₁ T₂ X_t`, the costate is `Λ = -√12 X_s U X_s` with `U` the multiplier in the
frame of the first piece, and `J` is `triY (2/√3, 2/√3, 2/√3)`.

The cover's `m = P F Q⁻¹` is the conjugate `D M D⁻¹`, `D = [[-1, 2], [1, 0]]`, of the
triangular frame (`df_alg_m`), the cover's `H = [[h₁₁, h₁₂], [h₂₁, -h₁₁]]` is
`-4 (1 - ρ)² R D (X_s U X_s) D⁻¹ R`, `R = diag(1, -1)` (`df_alg_h`), and the endpoint traces follow
(`df_alg_traces`). The window cost is `df_alg_cost` (both turn secants eliminate the logarithms).

## Main API

* `df_tri`, `df_triY_eq`: a state with margins `(c, d, e)`, `cd + de + ec = 4`, in triangular
  coordinates.
* `df_pt_basic`: the cover's `x, β, S, A, B, U, N, Z` at the window point.
* `df_alg_m`, `df_alg_h`: the cover's `m` and `H` at the window point.
* `df_alg_traces`: `𝒜 = T_κ (tr M + tr(JΛM)/κ)`, `√3 ℬ = T_κ (tr(ΛM)/κ - tr(JM))`.
* `df_alg_cost`: the window cost `C_br`.
-/

@[expose] public section

namespace SmoothedOctagon

open SmoothedPolygons Certificates.SmallerShort

private lemma df_s3 : √3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
private lemma df_s3pos : (0 : ℝ) < √3 := by positivity

/-- A state with margins `(c, d, (4 - cd)/(c + d))` in triangular coordinates. -/
noncomputable def df_tri (c d : ℝ) : Mat2 :=
  !![-c / 2, (c ^ 2 + 4) / (2 * (c + d)); -(c + d) / 2, c / 2]

theorem df_triY_eq {c d e : ℝ} (h : c * d + d * e + e * c = 4) (hcd : 0 < c + d) :
    triY ![c, d, e] = df_tri c d := by
  have he : e = (4 - c * d) / (c + d) := by field_simp; linarith
  subst he
  ext i j; fin_cases i <;> fin_cases j <;> simp [triY, df_tri]
  field_simp; ring

section Point

variable {a C B A v E : ℝ}

/-- The cover's derived coordinates at the window point. -/
theorem df_pt_basic (ha : 0 < a) (hC : 0 < C) (hB : 0 < B) (hA : 0 < A) :
    (⟨a / (a + C), B / C - 1, A / a, a ^ 2 / (a ^ 2 + 4), v, E⟩ : Point).x = C / a ∧
    (⟨a / (a + C), B / C - 1, A / a, a ^ 2 / (a ^ 2 + 4), v, E⟩ : Point).be = B / a ∧
    (⟨a / (a + C), B / C - 1, A / a, a ^ 2 / (a ^ 2 + 4), v, E⟩ : Point).S = (a + C) / a ∧
    (⟨a / (a + C), B / C - 1, A / a, a ^ 2 / (a ^ 2 + 4), v, E⟩ : Point).A = (A + B) / a ∧
    (⟨a / (a + C), B / C - 1, A / a, a ^ 2 / (a ^ 2 + 4), v, E⟩ : Point).B = (B + C) / a ∧
    (⟨a / (a + C), B / C - 1, A / a, a ^ 2 / (a ^ 2 + 4), v, E⟩ : Point).U = 4 / a ^ 2 ∧
    (⟨a / (a + C), B / C - 1, A / a, a ^ 2 / (a ^ 2 + 4), v, E⟩ : Point).N =
      (4 - a * C) / (a * (a + C)) ∧
    (⟨a / (a + C), B / C - 1, A / a, a ^ 2 / (a ^ 2 + 4), v, E⟩ : Point).Z =
      (4 - A * B) / (a * (A + B)) := by
  have hx := ss_point_x (δ := B / C - 1) (al := A / a) (ρ := a ^ 2 / (a ^ 2 + 4)) (v := v) (E := E)
    ha hC
  have hb := ss_point_be (al := A / a) (ρ := a ^ 2 / (a ^ 2 + 4)) (v := v) (E := E) (B := B) ha hC
  have hS : (⟨a / (a + C), B / C - 1, A / a, a ^ 2 / (a ^ 2 + 4), v, E⟩ : Point).S =
      (a + C) / a := by rw [Point.S, hx]; field_simp
  have hAA : (⟨a / (a + C), B / C - 1, A / a, a ^ 2 / (a ^ 2 + 4), v, E⟩ : Point).A =
      (A + B) / a := by rw [Point.A, hb]; field_simp
  have hU : (⟨a / (a + C), B / C - 1, A / a, a ^ 2 / (a ^ 2 + 4), v, E⟩ : Point).U =
      4 / a ^ 2 := by rw [Point.U]; field_simp; ring
  refine ⟨hx, hb, hS, hAA, ?_, hU, ?_, ?_⟩
  · rw [Point.B, hb, hx]; field_simp
  · rw [Point.N, hU, hx, hS]; field_simp
  · rw [Point.Z, hU, hb, hAA]; field_simp

/-- **The cover's relative frame is the triangular frame, conjugated** (`m D = D M`,
`D = [[-1, 2], [1, 0]]`). -/
theorem df_alg_m (ha : 0 < a) (hC : 0 < C) (hB : 0 < B) (hA : 0 < A) :
    let M := -(df_tri C a * Term.triFactor 0 ((C + B) / (a + C)) *
      Term.triFactor 1 ((C + B) / (B + A)) * df_tri A B)
    (⟨a / (a + C), B / C - 1, A / a, a ^ 2 / (a ^ 2 + 4), v, E⟩ : Point).m00 =
        (-M 0 1 + 2 * M 1 1) / 2 ∧
    (⟨a / (a + C), B / C - 1, A / a, a ^ 2 / (a ^ 2 + 4), v, E⟩ : Point).m01 =
        -M 0 0 + 2 * M 1 0 + (-M 0 1 + 2 * M 1 1) / 2 ∧
    (⟨a / (a + C), B / C - 1, A / a, a ^ 2 / (a ^ 2 + 4), v, E⟩ : Point).m10 = M 0 1 / 2 ∧
    (⟨a / (a + C), B / C - 1, A / a, a ^ 2 / (a ^ 2 + 4), v, E⟩ : Point).m11 =
        M 0 0 + M 0 1 / 2 := by
  intro M
  obtain ⟨hx, hb, hS, hAA, hBB, hU, hN, hZ⟩ :=
    df_pt_basic (v := v) (E := E) ha hC hB hA
  have hM : M = !![(A * B * C - 2 * B * C ^ 2 + C ^ 2 * a + 4 * C + 4 * a) / (4 * (C + a)),
      -(A ^ 2 * B * C - 2 * A * B * C ^ 2 + A * C ^ 2 * a + 4 * A * a - 4 * B * C) /
        (4 * (A + B) * (C + a));
      (A * B - 2 * B * C + C * a) / 4,
      -(A ^ 2 * B - 2 * A * B * C + A * C * a - 4 * A - 4 * B) / (4 * (A + B))] := by
    have : 0 < C + B := by positivity
    have : 0 < B + A := by positivity
    ext i j; fin_cases i <;> fin_cases j <;>
      simp [M, df_tri, Term.triFactor] <;>
      field_simp <;> ring
  have h1 : (0 : ℝ) < A + B := by positivity
  have h2 : (0 : ℝ) < a + C := by positivity
  simp only [hM, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.empty_val', Matrix.cons_val_fin_one]
  simp only [Point.m00, Point.m01, Point.m10, Point.m11, Point.PF00, Point.PF01, Point.PF10,
    Point.PF11, Point.P00, Point.P01, Point.P10, Point.P11, Point.Qi00, Point.Qi01, Point.Qi10,
    Point.Qi11, Point.F00, Point.F01, Point.F10, Point.F11, hx, hb, hS, hAA, hBB, hU, hN, hZ]
  refine ⟨?_, ?_, ?_, ?_⟩ <;> field_simp <;> ring

/-- **The cover's costate matrix** `H = -4 (1 - ρ)² R D (X_s U X_s) D⁻¹ R` at the window point,
for the multiplier `U` of the first piece written with the centre data `(E, u, v)`. -/
theorem df_alg_h {u : ℝ} (ha : 0 < a) (hC : 0 < C) {U : Mat2}
    (hu : (⟨a / (a + C), B / C - 1, A / a, a ^ 2 / (a ^ 2 + 4), v, E⟩ : Point).u = u)
    (hU00 : U 0 0 = -(E * (a ^ 2 + 4) / 16) + u * (a + C) ^ 2 / 8)
    (hU01 : U 0 1 = E * (a ^ 2 + 4) / 8 - v * (a ^ 2 + 4) ^ 2 / (8 * (a + C) ^ 2) -
      u * (a + C) ^ 2 / 8)
    (hU10 : U 1 0 = u * (a + C) ^ 2 / 8)
    (hU11 : U 1 1 = E * (a ^ 2 + 4) / 16 - u * (a + C) ^ 2 / 8) :
    let X := df_tri C a * U * df_tri C a
    (⟨a / (a + C), B / C - 1, A / a, a ^ 2 / (a ^ 2 + 4), v, E⟩ : Point).h21 =
        -2 * (1 - a ^ 2 / (a ^ 2 + 4)) ^ 2 * X 0 1 ∧
    (⟨a / (a + C), B / C - 1, A / a, a ^ 2 / (a ^ 2 + 4), v, E⟩ : Point).h11 =
        -4 * (1 - a ^ 2 / (a ^ 2 + 4)) ^ 2 * X 0 0 -
          2 * (1 - a ^ 2 / (a ^ 2 + 4)) ^ 2 * X 0 1 ∧
    (⟨a / (a + C), B / C - 1, A / a, a ^ 2 / (a ^ 2 + 4), v, E⟩ : Point).h12 =
        8 * (1 - a ^ 2 / (a ^ 2 + 4)) ^ 2 * X 0 0 - 8 * (1 - a ^ 2 / (a ^ 2 + 4)) ^ 2 * X 1 0 +
          2 * (1 - a ^ 2 / (a ^ 2 + 4)) ^ 2 * X 0 1 := by
  intro X
  have hx := ss_point_x (δ := B / C - 1) (al := A / a) (ρ := a ^ 2 / (a ^ 2 + 4)) (v := v) (E := E)
    ha hC
  have hS : (⟨a / (a + C), B / C - 1, A / a, a ^ 2 / (a ^ 2 + 4), v, E⟩ : Point).S =
      (a + C) / a := by rw [Point.S, hx]; field_simp
  have h2 : (0 : ℝ) < a + C := by positivity
  have hX : ∀ i j, X i j = (df_tri C a * U * df_tri C a) i j := fun _ _ ↦ rfl
  simp only [hX, df_tri, Matrix.mul_apply, Fin.sum_univ_two, Matrix.of_apply, Matrix.cons_val',
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.empty_val', Matrix.cons_val_fin_one,
    hU00, hU01, hU10, hU11]
  simp only [Point.h21, Point.h11, Point.h12, hu, hS]
  refine ⟨?_, ?_, ?_⟩ <;> field_simp <;> ring

end Point

/-- **The endpoint traces**: at the window
point, `𝒜 = T_κ (tr M + tr(J Λ M)/κ)` and `√3 ℬ = T_κ (tr(Λ M)/κ - tr(J M))`. -/
theorem df_alg_traces {a C B A v E u : ℝ} (ha : 0 < a) (hC : 0 < C) (hB : 0 < B) (hA : 0 < A)
    {U : Mat2}
    (hu : (⟨a / (a + C), B / C - 1, A / a, a ^ 2 / (a ^ 2 + 4), v, E⟩ : Point).u = u)
    (hk : 0 < (⟨a / (a + C), B / C - 1, A / a, a ^ 2 / (a ^ 2 + 4), v, E⟩ : Point).kap)
    (hU00 : U 0 0 = -(E * (a ^ 2 + 4) / 16) + u * (a + C) ^ 2 / 8)
    (hU01 : U 0 1 = E * (a ^ 2 + 4) / 8 - v * (a ^ 2 + 4) ^ 2 / (8 * (a + C) ^ 2) -
      u * (a + C) ^ 2 / 8)
    (hU10 : U 1 0 = u * (a + C) ^ 2 / 8)
    (hU11 : U 1 1 = E * (a ^ 2 + 4) / 16 - u * (a + C) ^ 2 / 8) :
    let pt : Point := ⟨a / (a + C), B / C - 1, A / a, a ^ 2 / (a ^ 2 + 4), v, E⟩
    let M := -(df_tri C a * Term.triFactor 0 ((C + B) / (a + C)) *
      Term.triFactor 1 ((C + B) / (B + A)) * df_tri A B)
    let Λ := -√12 • (df_tri C a * U * df_tri C a)
    let Jt := triY fun _ ↦ 2 / √3
    pt.AA = pt.Tk * (M.trace + (Jt * Λ * M).trace / pt.kap) ∧
      √3 * pt.BB = pt.Tk * ((Λ * M).trace / pt.kap - (Jt * M).trace) := by
  intro pt M Λ Jt
  obtain ⟨m00, m01, m10, m11⟩ := df_alg_m (v := v) (E := E) ha hC hB hA
  replace m00 : pt.m00 = (-M 0 1 + 2 * M 1 1) / 2 := m00
  replace m01 : pt.m01 = -M 0 0 + 2 * M 1 0 + (-M 0 1 + 2 * M 1 1) / 2 := m01
  replace m10 : pt.m10 = M 0 1 / 2 := m10
  replace m11 : pt.m11 = M 0 0 + M 0 1 / 2 := m11
  obtain ⟨h21, h11, h12⟩ := df_alg_h (B := B) (A := A) ha hC hu hU00 hU01 hU10 hU11
  have h12' : √12 = 2 * √3 := by
    rw [show (12 : ℝ) = 2 ^ 2 * 3 by norm_num, Real.sqrt_mul (by norm_num),
      Real.sqrt_sq (by norm_num)]
  have hs := df_s3pos
  have hs2 := df_s3
  have hJt : Jt = !![-(1 / √3), 2 / √3; -(2 / √3), 1 / √3] := by
    ext i j; fin_cases i <;> fin_cases j <;> simp [Jt, triY] <;> field_simp
  set X := df_tri C a * U * df_tri C a with hX
  have hXtr : X 1 1 = -X 0 0 := by
    simp only [hX, df_tri, Matrix.mul_apply, Fin.sum_univ_two, Matrix.of_apply, Matrix.cons_val',
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.empty_val', Matrix.cons_val_fin_one,
      hU00, hU01, hU10, hU11]
    have : (0 : ℝ) < a + C := by positivity
    field_simp
    ring
  have hΛ : Λ = -(2 * √3) • X := by
    show -√12 • X = _
    rw [h12']
  have hrho : pt.rho = a ^ 2 / (a ^ 2 + 4) := rfl
  simp only [Point.AA, Point.BB, Point.Tk]
  rw [m00, m01, m10, m11, h21, h11, h12, hΛ, hJt, hrho]
  simp only [Matrix.trace_fin_two, Matrix.mul_apply, Fin.sum_univ_two, Matrix.smul_apply,
    smul_eq_mul, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.empty_val', Matrix.cons_val_fin_one, hXtr]
  have hk0 : pt.kap ≠ 0 := hk.ne'
  generalize pt.kap = k at hk0 ⊢
  generalize M 0 0 = M00
  generalize M 0 1 = M01
  generalize M 1 0 = M10
  generalize M 1 1 = M11
  generalize X 0 0 = X00
  generalize X 0 1 = X01
  generalize X 1 0 = X10
  have hK : (0 : ℝ) < a ^ 2 + 4 := by positivity
  refine ⟨?_, ?_⟩
  · field_simp
    ring_nf
  · field_simp
    ring_nf
    simp only [hs2]
    ring

/-- **The window cost**: with both turn
secants `u = Sec(a, C, B) = Sec(C, B, A)`, the raw costs of the two turns `C`, `B` give the cover's
`C_br`. -/
theorem df_alg_cost {a C B A n v E u : ℝ} (ha : 0 < a) (hC : 0 < C) (hB : 0 < B) (hA : 0 < A)
    (hn : a * C + C * n + n * a = 4) (haB : a < B) (hAC : A < C)
    (hu : (⟨a / (a + C), B / C - 1, A / a, a ^ 2 / (a ^ 2 + 4), v, E⟩ : Point).u = u)
    (hu1 : u = m2Sec a C B) (hu2 : u = m2Sec C B A) :
    √3 / 4 * (Term.rawArc C a n ((C + B) / (a + C)) +
        Term.rawArc B ((C + n) / ((C + B) / (a + C)) - C) C ((C + B) / (B + A))) =
      (⟨a / (a + C), B / C - 1, A / a, a ^ 2 / (a ^ 2 + 4), v, E⟩ : Point).cost := by
  obtain ⟨hx, hb, hS, hAA, -, -, -, -⟩ := df_pt_basic (v := v) (E := E) ha hC hB hA
  have h2 : (0 : ℝ) < a + C := by positivity
  have hnn : n = (4 - a * C) / (a + C) := by field_simp; linarith
  -- the logarithms from the two secants
  have hL1 : C * Real.log ((C + B) / (a + C)) =
      (B - a) * (1 + C ^ 2 / ((a + C) * (B + C)) - u) := by
    rw [hu1, m2Sec_of_ne haB.ne]
    rw [show (B + C) / (a + C) = (C + B) / (a + C) by ring_nf]
    have : B - a ≠ 0 := sub_ne_zero.2 haB.ne'
    field_simp
    ring
  have hL2 : B * Real.log ((C + B) / (B + A)) =
      (A - C) * (u - 1 - B ^ 2 / ((C + B) * (A + B))) := by
    rw [hu2, m2Sec_of_ne hAC.ne']
    have hlog : Real.log ((A + B) / (C + B)) = -Real.log ((C + B) / (B + A)) := by
      rw [← Real.log_inv, inv_div, show B + A = A + B by ring]
    rw [hlog]
    have : A - C ≠ 0 := sub_ne_zero.2 hAC.ne
    field_simp
    ring
  simp only [Term.rawArc, Point.cost, hu, hx, hb, hS, hAA]
  have e1 : C * ((C + a) * ((C + B) / (a + C) - 1) + (C + n) * (1 - ((C + B) / (a + C))⁻¹) -
      C * Real.log ((C + B) / (a + C))) =
      C * ((C + a) * ((C + B) / (a + C) - 1) + (C + n) * (1 - ((C + B) / (a + C))⁻¹)) -
        C * (C * Real.log ((C + B) / (a + C))) := by ring
  have e2 : B * ((B + ((C + n) / ((C + B) / (a + C)) - C)) * ((C + B) / (B + A) - 1) +
      (B + C) * (1 - ((C + B) / (B + A))⁻¹) - B * Real.log ((C + B) / (B + A))) =
      B * ((B + ((C + n) / ((C + B) / (a + C)) - C)) * ((C + B) / (B + A) - 1) +
        (B + C) * (1 - ((C + B) / (B + A))⁻¹)) - B * (B * Real.log ((C + B) / (B + A))) := by
    ring
  rw [e1, e2, hL1, hL2, hnn]
  have hK : (0 : ℝ) < a ^ 2 + 4 := by positivity
  have : (0 : ℝ) < C + B := by positivity
  have : (0 : ℝ) < B + A := by positivity
  field_simp
  ring

end SmoothedOctagon
