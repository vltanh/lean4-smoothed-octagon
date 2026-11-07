module

public import SmoothedPolygons.Ch2.Density
public import SmoothedPolygons.Ch2.Boundary

/-!
# Invariance of the greatest packing density

The greatest packing density `δ(K)` (Definition 2.1.1) depends only on the congruence class of `K`,
since a packing of congruent copies of `K` is a packing of congruent copies of every congruent copy
of `K`. In particular it is invariant under translations and reflections. For centrally symmetric
convex disks it is also invariant under every invertible linear map: by Fejes Tóth's theorem
(`theorem2_1_3`) `δ = δ_L`, the lattice density `δ_L` is invariant under orientation-preserving
linear maps (`bdy_greatestLatticePackingDensity_image`), and an orientation-reversing map is an
orientation-preserving one after a reflection.

## Main API

* `bridge_isCongruentCopy_symm`, `bridge_isCongruentCopy_trans`: congruence is an equivalence.
* `bridge_isCongruentCopy_translate`: a translate is a congruent copy.
* `bridge_isPackingOfCopies_congr`: congruent sets have the same packings of copies.
* `bridge_greatestPackingDensity_congr`: congruent sets have the same greatest packing density.
* `bridge_reflection`: the reflection `(x₀, x₁) ↦ (x₀, -x₁)`, an involution
  (`bridge_reflection_reflection`) reversing `det2` (`bridge_det2_reflection`) and giving
  congruent copies (`bridge_isCongruentCopy_reflection`).
* `bridge_greatestPackingDensity_translate`: `δ(K + b) = δ(K)`.
* `bridge_isCCSDisk_centre`: a convex disk symmetric about `c`, translated by `-c`, is a centrally
  symmetric convex disk centred at the origin.
* `bridge_det2_map`: `det(A x, A y) = det A · det(x, y)` for a linear map `A` of the plane.
* `bridge_greatestPackingDensity_linear_image`: `δ(A K) = δ(K)` for every centrally symmetric
  convex disk `K` and every invertible linear map `A`.
-/

@[expose] public section

namespace SmoothedOctagon

open SmoothedPolygons Set Matrix

/-! ### Congruence -/

theorem bridge_isCongruentCopy_symm {K K' : Set (Fin 2 → ℝ)} (h : IsCongruentCopy K K') :
    IsCongruentCopy K' K := by
  obtain ⟨A, hA, b, rfl⟩ := h
  refine ⟨star A, Unitary.star_mem hA, -(star A *ᵥ b), ?_⟩
  rw [image_image]
  have hid : ∀ x, star A *ᵥ (A *ᵥ x + b) + -(star A *ᵥ b) = x := by
    intro x
    rw [mulVec_add, mulVec_mulVec, Unitary.star_mul_self_of_mem hA, one_mulVec]
    abel
  simp only [hid, image_id']

theorem bridge_isCongruentCopy_trans {K₁ K₂ K₃ : Set (Fin 2 → ℝ)} (h₁ : IsCongruentCopy K₁ K₂)
    (h₂ : IsCongruentCopy K₂ K₃) : IsCongruentCopy K₁ K₃ := by
  obtain ⟨A, hA, b, rfl⟩ := h₁
  obtain ⟨B, hB, c, rfl⟩ := h₂
  refine ⟨B * A, mul_mem hB hA, B *ᵥ b + c, ?_⟩
  rw [image_image]
  congr 1
  funext x
  rw [mulVec_add, mulVec_mulVec, add_assoc]

theorem bridge_isCongruentCopy_translate (K : Set (Fin 2 → ℝ)) (b : Fin 2 → ℝ) :
    IsCongruentCopy K ((fun x ↦ x + b) '' K) :=
  ⟨1, one_mem _, b, by simp only [one_mulVec]⟩

theorem bridge_isPackingOfCopies_congr {K K' : Set (Fin 2 → ℝ)} (h : IsCongruentCopy K K')
    (P : Set (Set (Fin 2 → ℝ))) : IsPackingOfCopies K P ↔ IsPackingOfCopies K' P := by
  constructor
  · rintro ⟨hP, hc⟩
    exact ⟨hP, fun K'' hK'' ↦ bridge_isCongruentCopy_trans (bridge_isCongruentCopy_symm h)
      (hc K'' hK'')⟩
  · rintro ⟨hP, hc⟩
    exact ⟨hP, fun K'' hK'' ↦ bridge_isCongruentCopy_trans h (hc K'' hK'')⟩

/-- Congruent sets have the same greatest packing density. -/
theorem bridge_greatestPackingDensity_congr {K K' : Set (Fin 2 → ℝ)} (h : IsCongruentCopy K K') :
    greatestPackingDensity K' = greatestPackingDensity K := by
  unfold greatestPackingDensity
  simp only [bridge_isPackingOfCopies_congr h]

/-- The greatest packing density is invariant under translations. -/
theorem bridge_greatestPackingDensity_translate (K : Set (Fin 2 → ℝ)) (b : Fin 2 → ℝ) :
    greatestPackingDensity ((fun x ↦ x + b) '' K) = greatestPackingDensity K :=
  bridge_greatestPackingDensity_congr (bridge_isCongruentCopy_translate K b)

/-- A convex disk symmetric about `c`, translated by `-c`, is centrally symmetric about the
origin. -/
theorem bridge_isCCSDisk_centre {K : Set (Fin 2 → ℝ)} (hK : IsConvexDisk K) {c : Fin 2 → ℝ}
    (hc : ∀ x ∈ K, (2 : ℝ) • c - x ∈ K) : IsCCSDisk ((fun x ↦ x + -c) '' K) := by
  obtain ⟨hconv, hcomp, hint⟩ := hK
  refine ⟨?_, hcomp.image (continuous_id.add continuous_const), ?_, ?_⟩
  · have e : (fun x ↦ x + -c) = (fun x ↦ -c + x) := funext fun x ↦ add_comm _ _
    rw [e]
    exact hconv.translate (-c)
  · have h := (Homeomorph.addRight (-c)).image_interior K
    simp only [Homeomorph.coe_addRight] at h
    rw [← h]
    exact hint.image _
  · rintro _ ⟨x, hx, rfl⟩
    refine ⟨(2 : ℝ) • c - x, hc x hx, ?_⟩
    show (2 : ℝ) • c - x + -c = -(x + -c)
    rw [two_smul]
    abel

/-! ### Linear maps -/

/-- `det(A x, A y) = det A · det(x, y)` for a linear map `A` of the plane. -/
theorem bridge_det2_map (A : (Fin 2 → ℝ) →ₗ[ℝ] (Fin 2 → ℝ)) (x y : Fin 2 → ℝ) :
    det2 (A x) (A y) = LinearMap.det A * det2 x y := by
  rw [← LinearMap.det_toMatrix', det_fin_two, ← LinearMap.toMatrix'_mulVec A x,
    ← LinearMap.toMatrix'_mulVec A y]
  simp only [det2, mulVec, dotProduct, Fin.sum_univ_two]
  ring

/-- The reflection `(x₀, x₁) ↦ (x₀, -x₁)`. -/
noncomputable def bridge_reflection : (Fin 2 → ℝ) ≃ₗ[ℝ] (Fin 2 → ℝ) :=
  LinearEquiv.ofInvolutive (mulVecLin !![1, 0; 0, -1]) fun x ↦ by
    ext i
    fin_cases i <;> simp [mulVec, dotProduct, Fin.sum_univ_two]

theorem bridge_reflection_apply (x : Fin 2 → ℝ) :
    bridge_reflection x = !![1, 0; 0, -1] *ᵥ x := rfl

theorem bridge_reflection_reflection (x : Fin 2 → ℝ) :
    bridge_reflection (bridge_reflection x) = x := by
  simp only [bridge_reflection_apply]
  ext i
  fin_cases i <;> simp [mulVec, dotProduct, Fin.sum_univ_two]

theorem bridge_det2_reflection (x y : Fin 2 → ℝ) :
    det2 (bridge_reflection x) (bridge_reflection y) = -det2 x y := by
  simp only [bridge_reflection_apply, det2, mulVec, dotProduct, Fin.sum_univ_two]
  simp
  ring

theorem bridge_isCongruentCopy_reflection (K : Set (Fin 2 → ℝ)) :
    IsCongruentCopy K (bridge_reflection '' K) := by
  refine ⟨!![1, 0; 0, -1], ?_, 0, ?_⟩
  · rw [mem_orthogonalGroup_iff]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Fin.sum_univ_two, vecMul, dotProduct]
  · simp only [add_zero]
    rfl

/-- The greatest packing density of a centrally symmetric convex disk is invariant under an
invertible linear map scaling `det` by a positive factor. -/
private theorem bridge_gpd_image_pos {K : Set (Fin 2 → ℝ)} (hK : IsCCSDisk K)
    (A : (Fin 2 → ℝ) ≃ₗ[ℝ] (Fin 2 → ℝ)) {δ : ℝ} (hδ : 0 < δ)
    (hA : ∀ x y, det2 (A x) (A y) = δ * det2 x y) :
    greatestPackingDensity (A '' K) = greatestPackingDensity K := by
  have hK' : IsCCSDisk (A.toContinuousLinearEquiv '' K) :=
    bdy_isCCSDisk_image A.toContinuousLinearEquiv hK
  have e : (A.toContinuousLinearEquiv : (Fin 2 → ℝ) → (Fin 2 → ℝ)) '' K = A '' K := rfl
  rw [e] at hK'
  rw [theorem2_1_3 hK', theorem2_1_3 hK, ← e]
  exact bdy_greatestLatticePackingDensity_image A.toContinuousLinearEquiv hδ hA
    ⟨hK.1, hK.2.1, hK.2.2.1⟩

/-- **The greatest packing density of a centrally symmetric convex disk is invariant under every
invertible linear map**, orientation-preserving or not. -/
theorem bridge_greatestPackingDensity_linear_image {K : Set (Fin 2 → ℝ)} (hK : IsCCSDisk K)
    (A : (Fin 2 → ℝ) ≃ₗ[ℝ] (Fin 2 → ℝ)) :
    greatestPackingDensity (A '' K) = greatestPackingDensity K := by
  have hd : LinearMap.det (A : (Fin 2 → ℝ) →ₗ[ℝ] (Fin 2 → ℝ)) ≠ 0 :=
    (LinearEquiv.isUnit_det' A).ne_zero
  rcases hd.lt_or_gt with hneg | hpos
  · set F := bridge_reflection
    have himg : A '' K = (F.trans A) '' (F '' K) := by
      rw [image_image]
      refine image_congr fun x _ ↦ ?_
      simp only [LinearEquiv.trans_apply, F, bridge_reflection_reflection]
    have hFK : IsCCSDisk (F '' K) := bdy_isCCSDisk_image F.toContinuousLinearEquiv hK
    rw [himg, bridge_gpd_image_pos hFK (F.trans A) (neg_pos.2 hneg) fun x y ↦ ?_,
      bridge_greatestPackingDensity_congr (bridge_isCongruentCopy_reflection K)]
    rw [LinearEquiv.trans_apply, LinearEquiv.trans_apply]
    have h := bridge_det2_map (A : (Fin 2 → ℝ) →ₗ[ℝ] (Fin 2 → ℝ)) (F x) (F y)
    simp only [LinearEquiv.coe_coe] at h
    rw [h, bridge_det2_reflection]
    ring
  · exact bridge_gpd_image_pos hK A hpos fun x y ↦ bridge_det2_map _ x y

end SmoothedOctagon
