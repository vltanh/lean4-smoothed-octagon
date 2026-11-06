module

public import SmoothedPolygons.Ch2.Boundary

/-!
# Continuous normalized supporting covectors

At a boundary point `x` of a centrally symmetric convex disk, a normalized supporting
covector `n` satisfies `n · x = 1` and `n · y ≤ 1` on the disk. The normalization fixes
the covector's scale; it is not a unit-normal convention.

This module constructs these covectors from the upstream support-line theorem. A unique
support line gives a unique normalized covector. An interior neighborhood of the origin
bounds all supporting covectors in one compact coordinate box. The support conditions
are closed under limits, so the unique covector varies continuously along any continuous
boundary curve. In particular, this applies to `rein_bd` for every actual worst disk,
without assuming a differentiable boundary parametrization.

`exists_continuous_radial_support` provides the input for differentiating the radial gauge
by squeezing its slopes between supporting linear functions. The final gauge-domination
inequality is proved for every vector, including zero.

Status: source-level Lean draft; compilation and kernel validation have not been run.
-/

@[expose] public section

namespace SmoothedOctagon

open Set Filter Topology Real SmoothedPolygons

/-- The coordinate pairing of a covector and a vector in the plane. This definition does
not use an inner-product instance on the sup-normed function space `Fin 2 → ℝ`. -/
def planeDot (n x : Fin 2 → ℝ) : ℝ := n 0 * x 0 + n 1 * x 1

theorem planeDot_eq_dotProduct (n x : Fin 2 → ℝ) : planeDot n x = n ⬝ᵥ x := by
  simp [planeDot, dotProduct, Fin.sum_univ_two]

@[simp] theorem planeDot_zero_left (x : Fin 2 → ℝ) : planeDot 0 x = 0 := by
  simp [planeDot]

@[simp] theorem planeDot_zero_right (n : Fin 2 → ℝ) : planeDot n 0 = 0 := by
  simp [planeDot]

@[simp] theorem planeDot_smul_left (n x : Fin 2 → ℝ) (c : ℝ) :
    planeDot (c • n) x = c * planeDot n x := by
  simp only [planeDot, Pi.smul_apply, smul_eq_mul]
  ring

@[simp] theorem planeDot_smul_right (n x : Fin 2 → ℝ) (c : ℝ) :
    planeDot n (c • x) = c * planeDot n x := by
  simp only [planeDot, Pi.smul_apply, smul_eq_mul]
  ring

@[simp] theorem planeDot_add_right (n x y : Fin 2 → ℝ) :
    planeDot n (x + y) = planeDot n x + planeDot n y := by
  simp only [planeDot, Pi.add_apply]
  ring

@[simp] theorem planeDot_sub_right (n x y : Fin 2 → ℝ) :
    planeDot n (x - y) = planeDot n x - planeDot n y := by
  simp only [planeDot, Pi.sub_apply]
  ring

@[simp] theorem planeDot_neg_right (n x : Fin 2 → ℝ) :
    planeDot n (-x) = -planeDot n x := by
  simp only [planeDot, Pi.neg_apply]
  ring

/-- A supporting covector whose value at the contact point is exactly one. Boundary
membership is supplied separately when this predicate is used. -/
def IsNormalizedSupport (K : Set (Fin 2 → ℝ)) (x n : Fin 2 → ℝ) : Prop :=
  planeDot n x = 1 ∧ ∀ y ∈ K, planeDot n y ≤ 1

/-- Every boundary point has a normalized supporting covector. This uses the upstream
separation theorem, which includes the positivity needed to normalize at level one. -/
theorem exists_normalizedSupport {K : Set (Fin 2 → ℝ)} (hK : IsCCSDisk K)
    {x : Fin 2 → ℝ} (hx : x ∈ frontier K) :
    ∃ n : Fin 2 → ℝ, IsNormalizedSupport K x n := by
  obtain ⟨n, hnK, hnx⟩ := irr_exists_normal hK hx
  refine ⟨n, ?_, fun y hy ↦ ?_⟩
  · simpa only [planeDot_eq_dotProduct] using hnx
  · simpa only [planeDot_eq_dotProduct] using hnK y hy

theorem normalizedSupport_ne_zero {K : Set (Fin 2 → ℝ)} {x n : Fin 2 → ℝ}
    (hn : IsNormalizedSupport K x n) : n ≠ 0 := by
  intro hzero
  have hcontact := hn.1
  rw [hzero, planeDot_zero_left] at hcontact
  norm_num at hcontact

/-- Uniqueness of the support line implies uniqueness of its level-one covector. No
differentiability or regular parametrization is used. -/
theorem normalizedSupport_unique {K : Set (Fin 2 → ℝ)} (hK : IsCCSDisk K)
    (huniq : ∀ u ∈ frontier K, ∃! ℓ, IsSupportLine K ℓ ∧ u ∈ ℓ)
    {x n m : Fin 2 → ℝ} (hx : x ∈ frontier K)
    (hn : IsNormalizedSupport K x n) (hm : IsNormalizedSupport K x m) : n = m := by
  have hxK : x ∈ K := hK.2.1.isClosed.frontier_subset hx
  have hnx : n ⬝ᵥ x = 1 := by
    simpa only [planeDot_eq_dotProduct] using hn.1
  have hmx : m ⬝ᵥ x = 1 := by
    simpa only [planeDot_eq_dotProduct] using hm.1
  have hnK : ∀ y ∈ K, n ⬝ᵥ y ≤ 1 := by
    intro y hy
    simpa only [planeDot_eq_dotProduct] using hn.2 y hy
  have hmK : ∀ y ∈ K, m ⬝ᵥ y ≤ 1 := by
    intro y hy
    simpa only [planeDot_eq_dotProduct] using hm.2 y hy
  have hnline : IsSupportLine K {y | n ⬝ᵥ y = 1} :=
    rein_isSupportLine_of (normalizedSupport_ne_zero hn) hnK hxK hnx
  have hmline : IsSupportLine K {y | m ⬝ᵥ y = 1} :=
    rein_isSupportLine_of (normalizedSupport_ne_zero hm) hmK hxK hmx
  obtain ⟨ℓ, _, hℓuniq⟩ := huniq x hx
  exact irr_eq_of_line_eq
    ((hℓuniq _ ⟨hnline, hnx⟩).trans (hℓuniq _ ⟨hmline, hmx⟩).symm)

theorem existsUnique_normalizedSupport {K : Set (Fin 2 → ℝ)} (hK : IsCCSDisk K)
    (huniq : ∀ u ∈ frontier K, ∃! ℓ, IsSupportLine K ℓ ∧ u ∈ ℓ)
    {x : Fin 2 → ℝ} (hx : x ∈ frontier K) :
    ∃! n : Fin 2 → ℝ, IsNormalizedSupport K x n := by
  obtain ⟨n, hn⟩ := exists_normalizedSupport hK hx
  exact ⟨n, hn, fun m hm ↦ normalizedSupport_unique hK huniq hx hm hn⟩

/-- The polar inequalities put every supporting covector in one bounded coordinate box.
The bound depends only on an interior neighborhood of zero in `K`, not on a contact
point or a chosen parametrization. -/
theorem exists_support_coordinate_bound {K : Set (Fin 2 → ℝ)} (hK : IsCCSDisk K) :
    ∃ C : ℝ, 0 < C ∧ ∀ n : Fin 2 → ℝ,
      (∀ y ∈ K, planeDot n y ≤ 1) → ∀ i, |n i| ≤ C := by
  obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.1 (rein_nhds_zero hK)
  let a : ℝ := r / 2
  have ha : 0 < a := by dsimp [a]; positivity
  have har : a < r := by dsimp [a]; linarith
  have hsmall : ∀ z : Fin 2 → ℝ, (∀ i, |z i| ≤ a) → z ∈ K := by
    intro z hz
    apply hball
    change dist z 0 < r
    rw [dist_zero_right]
    refine lt_of_le_of_lt ((pi_norm_le_iff_of_nonneg ha.le).2 fun i ↦ ?_) har
    simpa only [Real.norm_eq_abs] using hz i
  have he : ∀ i : Fin 2, (Pi.single i a : Fin 2 → ℝ) ∈ K := by
    intro i
    apply hsmall
    intro j
    fin_cases i <;> fin_cases j <;> simp [abs_of_pos ha, ha.le]
  refine ⟨a⁻¹, inv_pos.2 ha, fun n hn i ↦ ?_⟩
  have heval : planeDot n (Pi.single i a) = n i * a := by
    fin_cases i <;> simp [planeDot]
  have hplus := hn _ (he i)
  have hminus := hn _ (hK.2.2.2 _ (he i))
  rw [heval] at hplus
  rw [planeDot_neg_right, heval] at hminus
  have hup : n i ≤ a⁻¹ := by
    rw [← one_div, le_div_iff₀ ha]
    exact hplus
  have hneg : -n i ≤ a⁻¹ := by
    rw [← one_div, le_div_iff₀ ha]
    simpa only [neg_mul] using hminus
  exact abs_le.2 ⟨by linarith, hup⟩

/-- A field of normalized supporting covectors along a continuous boundary curve is
continuous when each boundary support line is unique. Compactness supplies cluster
points; the contact equality and all supporting inequalities persist at every limit. -/
theorem continuous_normalizedSupport {K : Set (Fin 2 → ℝ)} (hK : IsCCSDisk K)
    (huniq : ∀ u ∈ frontier K, ∃! ℓ, IsSupportLine K ℓ ∧ u ∈ ℓ)
    {τ n : ℝ → Fin 2 → ℝ} (hτ : Continuous τ)
    (hτK : ∀ t, τ t ∈ frontier K)
    (hn : ∀ t, IsNormalizedSupport K (τ t) (n t)) : Continuous n := by
  obtain ⟨C, _, hC⟩ := exists_support_coordinate_bound hK
  have hcompact : IsCompact (univ.pi fun _ : Fin 2 ↦ Icc (-C) C) :=
    isCompact_univ_pi fun _ ↦ isCompact_Icc
  rw [continuous_iff_continuousAt]
  intro t₀
  refine hcompact.tendsto_nhds_of_unique_mapClusterPt
    (Filter.Eventually.of_forall fun t ↦ ?_) fun w _ hclus ↦ ?_
  · intro i _
    exact abs_le.1 (hC (n t) (hn t).2 i)
  · have hwcontact : planeDot w (τ t₀) = 1 := by
      by_contra hne
      have hcont : Continuous fun p : ℝ × (Fin 2 → ℝ) ↦ planeDot p.2 (τ p.1) := by
        unfold planeDot
        fun_prop
      have hclosed : IsClosed {p : ℝ × (Fin 2 → ℝ) | planeDot p.2 (τ p.1) = 1} :=
        isClosed_eq hcont continuous_const
      have hopen : {p : ℝ × (Fin 2 → ℝ) | planeDot p.2 (τ p.1) = 1}ᶜ ∈ 𝓝 (t₀, w) :=
        hclosed.isOpen_compl.mem_nhds hne
      obtain ⟨V, hV, W, hW, hVW⟩ := mem_nhds_prod_iff.1 hopen
      have hfreq := (mapClusterPt_iff_frequently.1 hclus) W hW
      obtain ⟨t, htW, htV⟩ := (hfreq.and_eventually hV).exists
      have hne' : planeDot (n t) (τ t) ≠ 1 :=
        hVW (show (t, n t) ∈ V ×ˢ W from ⟨htV, htW⟩)
      exact hne' (hn t).1
    have hwK : ∀ y ∈ K, planeDot w y ≤ 1 := by
      intro y hy
      by_contra hneg
      have hgt : 1 < planeDot w y := lt_of_not_ge hneg
      have hcont : Continuous fun v : Fin 2 → ℝ ↦ planeDot v y := by
        unfold planeDot
        fun_prop
      have hopen : {v : Fin 2 → ℝ | 1 < planeDot v y} ∈ 𝓝 w :=
        (isOpen_lt continuous_const hcont).mem_nhds hgt
      have hfreq := (mapClusterPt_iff_frequently.1 hclus) _ hopen
      obtain ⟨t, ht⟩ := hfreq.exists
      exact (not_lt_of_ge ((hn t).2 y hy)) ht
    exact normalizedSupport_unique hK huniq (hτK t₀) ⟨hwcontact, hwK⟩ (hn t₀)

/-- Every supporting linear function lies below the gauge on the whole plane. The
normalizing contact is not needed for this inequality, but is retained in the interface. -/
theorem normalizedSupport_le_gauge {K : Set (Fin 2 → ℝ)} (hK : IsCCSDisk K)
    {x n : Fin 2 → ℝ} (hn : IsNormalizedSupport K x n) (y : Fin 2 → ℝ) :
    planeDot n y ≤ gauge K y := by
  by_cases hy : y = 0
  · subst y
    simp
  have hg : 0 < gauge K y := rein_gauge_pos hK hy
  have hfrontier : (gauge K y)⁻¹ • y ∈ frontier K := by
    rw [← gauge_eq_one_iff_mem_frontier hK.1 (rein_nhds_zero hK),
      rein_gauge_smul (inv_pos.2 hg).le]
    exact inv_mul_cancel₀ hg.ne'
  have hbound := hn.2 _ (hK.2.1.isClosed.frontier_subset hfrontier)
  rw [planeDot_smul_right, inv_mul_le_iff₀ hg, mul_one] at hbound
  exact hbound

/-- Choose the normalized supporting covector at the radial boundary point. The choice
is unique under the no-corners hypothesis, and continuity is proved below. -/
noncomputable def radialSupport {K : Set (Fin 2 → ℝ)} (hK : IsCCSDisk K)
    (θ : ℝ) : Fin 2 → ℝ :=
  Classical.choose (exists_normalizedSupport hK (rein_bd_mem_frontier hK θ))

theorem radialSupport_spec {K : Set (Fin 2 → ℝ)} (hK : IsCCSDisk K) (θ : ℝ) :
    IsNormalizedSupport K (rein_bd K θ) (radialSupport hK θ) :=
  Classical.choose_spec (exists_normalizedSupport hK (rein_bd_mem_frontier hK θ))

theorem radialSupport_continuous {K : Set (Fin 2 → ℝ)} (hK : IsCCSDisk K)
    (huniq : ∀ u ∈ frontier K, ∃! ℓ, IsSupportLine K ℓ ∧ u ∈ ℓ) :
    Continuous (radialSupport hK) :=
  continuous_normalizedSupport hK huniq (rein_continuous_bd hK)
    (rein_bd_mem_frontier hK) (radialSupport_spec hK)

theorem radialSupport_periodic {K : Set (Fin 2 → ℝ)} (hK : IsCCSDisk K)
    (huniq : ∀ u ∈ frontier K, ∃! ℓ, IsSupportLine K ℓ ∧ u ∈ ℓ) :
    Function.Periodic (radialSupport hK) (2 * π) := by
  intro θ
  apply normalizedSupport_unique hK huniq (rein_bd_mem_frontier hK θ)
  · simpa only [rein_bd_add_two_pi] using radialSupport_spec hK (θ + 2 * π)
  · exact radialSupport_spec hK θ

/-- A continuous field of supporting covectors on the radial boundary, constructed from
the convex disk and its unique support lines. No smooth parametrization is assumed. -/
theorem exists_continuous_radial_support_of_unique_support
    {K : Set (Fin 2 → ℝ)} (hK : IsCCSDisk K)
    (huniq : ∀ u ∈ frontier K, ∃! ℓ, IsSupportLine K ℓ ∧ u ∈ ℓ) :
    ∃ n : ℝ → Fin 2 → ℝ, Continuous n ∧
      (∀ θ, IsNormalizedSupport K (rein_bd K θ) (n θ)) ∧
      (∀ θ y, planeDot (n θ) y ≤ gauge K y) := by
  refine ⟨radialSupport hK, radialSupport_continuous hK huniq, radialSupport_spec hK, ?_⟩
  intro θ y
  exact normalizedSupport_le_gauge hK (radialSupport_spec hK θ) y

/-- Every actual worst disk has the continuous normalized support field needed for the
radial differentiability argument. Upstream Lemma 2.2.5 supplies the no-corners theorem. -/
theorem exists_continuous_radial_support {K : Set (Fin 2 → ℝ)} (hK : IsWorstDisk K) :
    ∃ n : ℝ → Fin 2 → ℝ, Continuous n ∧
      (∀ θ, IsNormalizedSupport K (rein_bd K θ) (n θ)) ∧
      (∀ θ y, planeDot (n θ) y ≤ gauge K y) :=
  exists_continuous_radial_support_of_unique_support hK.1
    (lemma2_2_5.2 K (ch2_isWorstLatticeDisk_iff_isWorstDisk.mpr hK)).1

end SmoothedOctagon
