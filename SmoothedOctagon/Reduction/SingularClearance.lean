module

public import SmoothedOctagon.Reduction.Defs
public import SmoothedOctagon.Reduction.Clearance.Frame

/-!
# Singular clearance and projective bounds

The exact budget coefficient `b_oct` gives the clearance coefficient
`c_oct = sqrt(b_oct² + (1+3b_oct/sqrt(2))²)`. The resulting bound is homogeneous
in the Pontryagin covector and applies to normal and abnormal lifts. On each
compact star set, conservation and the exact frame estimate also give a uniform
two-sided comparison of squared covector norms through a complete period.
-/

@[expose] public section

namespace SmoothedOctagon.Reduction

open SmoothedPolygons MeasureTheory Set Real

private theorem frob_add_J (M : Mat2) (c : ℝ) :
    frobSq (M + c • J) ≤ (√(frobSq M) + √2 * |c|) ^ 2 := by
  have hM := clr_frobSq_nonneg M
  have hs := Real.sq_sqrt hM
  have h2 : √2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hd : (M 1 0 - M 0 1) ^ 2 ≤ 2 * frobSq M := by
    unfold frobSq
    nlinarith [sq_nonneg (M 1 0 + M 0 1), sq_nonneg (M 0 0), sq_nonneg (M 1 1)]
  have hd' := Real.abs_le_sqrt hd
  rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2)] at hd'
  have hc := mul_le_mul_of_nonneg_left hd' (abs_nonneg c)
  have hcross := le_abs_self (c * (M 1 0 - M 0 1))
  rw [abs_mul] at hcross
  have he : frobSq (M + c • J) =
      frobSq M + 2 * c * (M 1 0 - M 0 1) + 2 * c ^ 2 := by
    simp [frobSq, J]
    ring
  rw [he]
  nlinarith [sq_abs c]

private theorem frob_add_J_budget {B lam : ℝ} {A : Mat2}
    (hb : |lam| ≤ B * √(frobSq A)) :
    frobSq (A + (3 / 2 * lam) • J) ≤ (1 + 3 * B / √2) ^ 2 * frobSq A := by
  have hA := clr_frobSq_nonneg A
  have hsq := Real.sq_sqrt hA
  have h2 : √2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have h2p : (0 : ℝ) < √2 := by positivity
  have h := frob_add_J A (3 / 2 * lam)
  rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 3 / 2)] at h
  have hbound : √(frobSq A) + √2 * (3 / 2 * |lam|) ≤
      (1 + 3 * B / √2) * √(frobSq A) := by
    have hmul := mul_le_mul_of_nonneg_left hb (by positivity : 0 ≤ √2 * (3 / 2))
    have he : √2 * (3 / 2) = 3 / √2 := by
      apply (eq_div_iff h2p.ne').mpr
      nlinarith
    calc √(frobSq A) + √2 * (3 / 2 * |lam|) =
          √(frobSq A) + (3 / √2) * |lam| := by rw [← he]; ring
      _ ≤ √(frobSq A) + (3 / √2) * (B * √(frobSq A)) := by
        rw [he] at hmul
        exact add_le_add_right hmul _
      _ = _ := by ring
  have hnon : 0 ≤ √(frobSq A) + √2 * (3 / 2 * |lam|) := by positivity
  calc frobSq (A + (3 / 2 * lam) • J) ≤ _ := h
    _ ≤ ((1 + 3 * B / √2) * √(frobSq A)) ^ 2 := pow_le_pow_left₀ hnon hbound 2
    _ = (1 + 3 * B / √2) ^ 2 * frobSq A := by rw [mul_pow, hsq]

private theorem projective_scalar {D F l a b w v : ℝ} (hD : 0 ≤ D) (hl : 0 ≤ l)
    (ha : 0 ≤ a) (hw : 0 ≤ w) (hb : b ≤ F ^ 2 * a) (hv : v ≤ D * (2 * b + 9 * l)) :
    l + b + v ≤ ((1 + 9 * D) + (1 + 2 * D) * F ^ 2) * (l + a + w) := by
  have hc : 0 ≤ 1 + 2 * D := by positivity
  have hbound := mul_le_mul_of_nonneg_left hb hc
  have hG : 0 ≤ (1 + 9 * D) + (1 + 2 * D) * F ^ 2 := by positivity
  nlinarith only [hv, hbound, mul_nonneg (mul_nonneg hc (sq_nonneg F)) hl,
    mul_nonneg (by positivity : 0 ≤ 1 + 9 * D) ha, mul_nonneg hG hw]

/-- The clearance coefficient `sqrt(b_oct² + (1+3b_oct/sqrt(2))²)`. -/
noncomputable def clr_clearanceOct : ℝ :=
  √(clr_budgetOct ^ 2 + (1 + 3 * clr_budgetOct / √2) ^ 2)

theorem clr_clearanceOct_sq : clr_clearanceOct ^ 2 =
    clr_budgetOct ^ 2 + (1 + 3 * clr_budgetOct / √2) ^ 2 := by
  exact Real.sq_sqrt (by positivity)

theorem clr_clearanceOct_sq_ge_one : 1 ≤ clr_clearanceOct ^ 2 := by
  have hb : 0 ≤ clr_budgetOct := le_trans (by norm_num) clr_budgetOct_ge_two_thirds
  have hr : 0 ≤ 3 * clr_budgetOct / √2 := by positivity
  rw [clr_clearanceOct_sq]
  nlinarith only [hr, sq_nonneg clr_budgetOct, sq_nonneg (3 * clr_budgetOct / √2)]

/-- The exact budget and the Frobenius triangle inequality give the homogeneous
singular clearance `‖𝒫(t)‖² ≤ c_oct² Q(t)²`, for normal and abnormal lifts alike. -/
theorem covectorNormSq_le_singularGapSq {T : ℝ} {u : ℝ → Fin 3 → ℝ}
    {g X Λ₁ ΛR : ℝ → Mat2} {lam : ℝ}
    (hext : IsPontryaginExtremal T u g X Λ₁ ΛR lam)
    (hcost : reinhardtCost T X ≤ SmoothedOctagon.octagonCost) :
    ∀ t ∈ Icc 0 T, covectorNormSq lam (Λ₁ t) (ΛR t) ≤
      clr_clearanceOct ^ 2 * singularGapSq lam (Λ₁ t) (ΛR t) := by
  intro t ht
  have hb := clr_lam_sq_le hext hcost t ht
  have habs := clr_abs_lam_le hext hcost t ht
  set A := Λ₁ t - (3 / 2 * lam) • J with hA
  have hΛ : Λ₁ t = A + (3 / 2 * lam) • J := by rw [hA, sub_add_cancel]
  have hΛbound := frob_add_J_budget habs
  rw [← hΛ] at hΛbound
  have hW := clr_frobSq_nonneg (ΛR t)
  have hC := clr_clearanceOct_sq_ge_one
  have hCW := mul_le_mul_of_nonneg_right hC hW
  unfold covectorNormSq singularGapSq
  rw [clr_clearanceOct_sq] at *
  dsimp only [A] at hΛbound
  nlinarith only [hb, hΛbound, hCW]

private theorem frobSq_conj_adjugate_bound (g M : Mat2) :
    frobSq (g * M * g.adjugate) ≤ frobSq g ^ 2 * frobSq M := by
  have h1 := clr_frobSq_mul_le (g * M) g.adjugate
  have h2 := clr_frobSq_mul_le g M
  rw [clr_frobSq_adjugate] at h1
  have := clr_frobSq_nonneg g
  calc frobSq (g * M * g.adjugate) ≤ frobSq (g * M) * frobSq g := h1
    _ ≤ frobSq g * frobSq M * frobSq g := mul_le_mul_of_nonneg_right h2 this
    _ = frobSq g ^ 2 * frobSq M := by ring

/-- The squared covector norms are uniformly comparable throughout every competitive
period in a fixed compact set of star states. The constant depends only on that set
and the octagon cost. -/
theorem covectorNormSq_projective_bounds {K : Set Mat2} (hK : IsCompact K)
    (hstar : ∀ X ∈ K, IsStarState X) :
    ∃ G : ℝ, 0 < G ∧ ∀ {T : ℝ} {u : ℝ → Fin 3 → ℝ} {g X Λ₁ ΛR : ℝ → Mat2} {lam : ℝ},
      IsPontryaginExtremal T u g X Λ₁ ΛR lam → reinhardtCost T X ≤ SmoothedOctagon.octagonCost →
      (∀ t ∈ Icc 0 T, X t ∈ K) → ∀ t ∈ Icc 0 T,
      covectorNormSq lam (Λ₁ 0) (ΛR 0) ≤ G * covectorNormSq lam (Λ₁ t) (ΛR t) ∧
      covectorNormSq lam (Λ₁ t) (ΛR t) ≤ G * covectorNormSq lam (Λ₁ 0) (ΛR 0) := by
  obtain ⟨D, hD, hDbound⟩ := clr_compact_costate_bound hK hstar
  let F : ℝ := 2 * exp (2 * SmoothedOctagon.octagonCost / 3)
  let G : ℝ := (1 + 9 * D) + (1 + 2 * D) * F ^ 2
  refine ⟨G, by dsimp [G]; positivity, ?_⟩
  intro T u g X Λ₁ ΛR lam hext hcost hstate t ht
  have hT : 0 < T := hext.1.1
  have h0 : (0 : ℝ) ∈ Icc 0 T := left_mem_Icc.mpr hT.le
  have hg := clr_frobSq_frame_le hext.1 hext.2.1 hcost t ht
  have hg0 := clr_frobSq_nonneg (g t)
  have hg2 : frobSq (g t) ^ 2 ≤ F ^ 2 := pow_le_pow_left₀ hg0 hg 2
  have hdet : (g t).det = 1 := (hext.1.2.2.2.1 t ht).1
  have hinv : (g t)⁻¹ = (g t).adjugate := by
    rw [Matrix.inv_def, hdet, Ring.inverse_one, one_smul]
  have hunit : IsUnit (g t).det := by rw [hdet]; exact isUnit_one
  have hcons := clr_conservation hext t ht
  have hΛt : frobSq (Λ₁ t) ≤ F ^ 2 * frobSq (Λ₁ 0) := by
    have hc := clr_frobSq_conj_le hdet (Λ₁ 0)
    rw [← hcons] at hc
    exact hc.trans (mul_le_mul_of_nonneg_right hg2 (clr_frobSq_nonneg _))
  have hΛ0 : frobSq (Λ₁ 0) ≤ F ^ 2 * frobSq (Λ₁ t) := by
    have e : Λ₁ 0 = g t * Λ₁ t * (g t).adjugate := by
      rw [hcons, ← hinv]
      simp only [← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hunit, Matrix.one_mul]
      rw [Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hunit, Matrix.mul_one]
    have hc := frobSq_conj_adjugate_bound (g t) (Λ₁ t)
    rw [← e] at hc
    exact hc.trans (mul_le_mul_of_nonneg_right hg2 (clr_frobSq_nonneg _))
  have hW : ∀ s ∈ Icc 0 T, frobSq (ΛR s) ≤ D * (2 * frobSq (Λ₁ s) + 9 * lam ^ 2) := by
    intro s hs
    have hH := (IsPontryaginExtremal.vertexHamiltonian_max_eq_zero hext s hs).1
    obtain ⟨-, hWtr, hWX, -⟩ := hext.2.2.2.2.2.2.2.1 s hs
    have hc := hDbound lam (Λ₁ s) (ΛR s) (X s) (hstate s hs) hWtr hWX hH
    have hA : frobSq (Λ₁ s - (3 / 2 * lam) • J) ≤ 2 * frobSq (Λ₁ s) + 9 * lam ^ 2 := by
      have hy := clr_frobSq_add_smul_J_le (Λ₁ s) (-(3 / 2 * lam))
      rw [neg_smul, ← sub_eq_add_neg] at hy
      nlinarith only [hy]
    exact hc.trans (mul_le_mul_of_nonneg_left hA hD)
  constructor
  · exact projective_scalar hD (sq_nonneg lam) (clr_frobSq_nonneg (Λ₁ t))
      (clr_frobSq_nonneg (ΛR t)) hΛ0 (hW 0 h0)
  · exact projective_scalar hD (sq_nonneg lam) (clr_frobSq_nonneg (Λ₁ 0))
      (clr_frobSq_nonneg (ΛR 0)) hΛt (hW t ht)

end SmoothedOctagon.Reduction
