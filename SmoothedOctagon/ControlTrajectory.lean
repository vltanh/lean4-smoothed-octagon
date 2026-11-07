module

public import SmoothedOctagon.BalancedReduction
public import SmoothedOctagon.DeterminantClock
public import SmoothedPolygons.Ch3.ControlProblem
public import SmoothedPolygons.Ch3.LieAlgebraDynamics
public import Basic.Analysis.Calculus.MatrixFTC
public import Mathlib.Analysis.Matrix.MeasurableSpace
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.AbsolutelyContinuousFun

/-!
# From normalized boundary geometry to an actual measurable control

The determinant clock gives a global frame `g`, a star state `X`, the equation
`g' = g X`, and Lipschitz regularity of `X`. This module constructs the control
from curvature. A measurable repair assigns the uniform simplex point wherever
the three raw curvatures do not form a nonzero nonnegative vector. The repair
agrees almost everywhere with the raw normalization on each time interval.

Convexity gives curvature inequalities at every point where the derivative of
`X` exists; no almost-everywhere assertion is transported through a time change.
Absolute continuity then turns the almost-everywhere state equation into the
entrywise integral equations required by `IsStateTrajectory`.

This is a forward realization theorem. Control optimality additionally needs a
reverse comparison with arbitrary admissible controls. Source draft only;
compilation and kernel validation have not been run.
-/

@[expose] public section

namespace SmoothedOctagon

open MeasureTheory Real Set Filter Matrix SmoothedPolygons
open scoped Topology

/-- A curvature vector can be normalized precisely when its entries are nonnegative
and their sum is positive. The separate coordinates make the repair set manifestly Borel. -/
def UsableCurvatures (κ : Fin 3 → ℝ) : Prop :=
  0 ≤ κ 0 ∧ 0 ≤ κ 1 ∧ 0 ≤ κ 2 ∧ 0 < κ 0 + κ 1 + κ 2

open Classical in
/-- Normalize genuine curvatures and use the uniform control on the exceptional set. -/
noncomputable def repairedCurvatureControl (κ : ℝ → Fin 3 → ℝ)
    (t : ℝ) : Fin 3 → ℝ :=
  if UsableCurvatures (κ t) then controlVariables (κ t) else fun _ ↦ 1 / 3

theorem controlVariables_mem_of_usable {κ : Fin 3 → ℝ} (hκ : UsableCurvatures κ) :
    controlVariables κ ∈ controlSimplex := by
  obtain ⟨h0, h1, h2, hs⟩ := hκ
  refine ⟨?_, ?_⟩
  · intro j
    have hnonneg : 0 ≤ κ j := by fin_cases j <;> assumption
    have hle : κ j ≤ κ 0 + κ 1 + κ 2 := by
      fin_cases j <;> simp only [Fin.reduceFinMk] <;> linarith
    exact ⟨div_nonneg hnonneg hs.le, (div_le_iff₀ hs).2 (by simpa using hle)⟩
  · dsimp [controlVariables]
    field_simp [hs.ne']

/-- Simplex membership holds at every time, including exceptional derivative points. -/
theorem repairedCurvatureControl_mem (κ : ℝ → Fin 3 → ℝ) (t : ℝ) :
    repairedCurvatureControl κ t ∈ controlSimplex := by
  classical
  unfold repairedCurvatureControl
  split_ifs with h
  · exact controlVariables_mem_of_usable h
  · exact ⟨fun _ ↦ by norm_num, by norm_num⟩

theorem measurable_repairedCurvatureControl {κ : ℝ → Fin 3 → ℝ}
    (hκ : ∀ j, Measurable fun t ↦ κ t j) : Measurable (repairedCurvatureControl κ) := by
  classical
  have hs : Measurable fun t ↦ κ t 0 + κ t 1 + κ t 2 :=
    ((hκ 0).add (hκ 1)).add (hκ 2)
  have hset : MeasurableSet {t | UsableCurvatures (κ t)} :=
    (measurableSet_le measurable_const (hκ 0)).inter
      ((measurableSet_le measurable_const (hκ 1)).inter
        ((measurableSet_le measurable_const (hκ 2)).inter
          (measurableSet_lt measurable_const hs)))
  have hraw : Measurable fun t ↦ controlVariables (κ t) :=
    Measurable.of_eval fun j ↦ (hκ j).div hs
  exact Measurable.ite hset hraw measurable_const

/-- The actual control is a fixed formula in the normalized state and its measurable derivative. -/
noncomputable def boundaryControl (X : ℝ → Mat2) : ℝ → Fin 3 → ℝ :=
  repairedCurvatureControl fun t ↦ stateCurvature (X t) (derivEntrywise X t)

private lemma continuous_of_lipschitzOnEntrywise_univ {X : ℝ → Mat2}
    (hX : LipschitzOnEntrywise X univ) : Continuous X := by
  apply Matrix.continuous_iff_entrywise.mpr
  intro i j
  obtain ⟨C, hC⟩ := hX i j
  exact (lipschitzOnWith_univ.1 hC).continuous

/-- On determinant-one states the inverse is the adjugate, so the raw curvature
coordinates are measurable even where one of the entrywise derivatives is undefined. -/
theorem measurable_stateCurvature {X : ℝ → Mat2} (hX : Continuous X)
    (hdet : ∀ t, (X t).det = 1) (j : Fin 3) :
    Measurable fun t ↦ stateCurvature (X t) (derivEntrywise X t) j := by
  have hm : ∀ i k, Measurable fun t ↦ X t i k :=
    fun i k ↦ (Matrix.continuous_iff_entrywise.mp hX i k).measurable
  have hd : ∀ i k, Measurable fun t ↦ derivEntrywise X t i k :=
    fun i k ↦ measurable_deriv (fun t ↦ X t i k)
  have hinv : ∀ i k, Measurable fun t ↦ (X t)⁻¹ i k := by
    intro i k
    simp only [Matrix.inv_def, hdet, Ring.inverse_one, one_smul,
      Matrix.adjugate_fin_two]
    fin_cases i <;> fin_cases k
    · exact hm 1 1
    · exact (hm 0 1).neg
    · exact (hm 1 0).neg
    · exact hm 0 0
  have hY : ∀ i k, Measurable fun t ↦
      (X t + (X t)⁻¹ * derivEntrywise X t) i k := by
    intro i k
    simp only [Matrix.add_apply, Matrix.mul_apply, Fin.sum_univ_two]
    exact (hm i k).add (((hinv i 0).mul (hd 0 k)).add ((hinv i 1).mul (hd 1 k)))
  have hv : ∀ i, Measurable fun t ↦
      ((X t + (X t)⁻¹ * derivEntrywise X t) *ᵥ
        sixthRoot (2 * (j.val : ZMod 6))) i := by
    intro i
    simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_two]
    exact ((hY i 0).mul measurable_const).add ((hY i 1).mul measurable_const)
  exact (measurable_const.mul (hv 1)).sub (measurable_const.mul (hv 0))

theorem measurable_boundaryControl {X : ℝ → Mat2} (hX : Continuous X)
    (hdet : ∀ t, (X t).det = 1) : Measurable (boundaryControl X) :=
  measurable_repairedCurvatureControl (measurable_stateCurvature hX hdet)

theorem boundaryControl_mem (X : ℝ → Mat2) (t : ℝ) :
    boundaryControl X t ∈ controlSimplex := repairedCurvatureControl_mem _ t

/-- In particular the denominator used by `controlP` is strictly negative at every
star state, even at times where the control has been repaired. -/
theorem boundaryControl_denominator_neg {X : ℝ → Mat2} {t : ℝ}
    (hX : IsStarState (X t)) :
    traceForm (controlMatrix (boundaryControl X t)) (X t) < 0 :=
  ((lemma3_3_4 (X t) hX.1).mp hX.2.2) _ (boundaryControl_mem X t)

/-! ## Curvature from convexity, after the change of parameter -/

/-- The support-line proof of upstream Lemma 2.4.6, at an individual point where
the second derivative exists. A global Lipschitz bound is not needed for this step. -/
theorem positiveBoundary_curvature_nonneg {K : Set (Fin 2 → ℝ)}
    (hK : IsCCSDisk K) {γ : ℝ → Fin 2 → ℝ} (hγ : IsPositiveBoundaryParam K γ)
    {t₀ : ℝ} (hdd : DifferentiableAt ℝ (deriv γ) t₀) :
    0 ≤ det2 (deriv γ t₀) (deriv (deriv γ) t₀) := by
  have hdiff : Differentiable ℝ γ := hγ.1.differentiable (by norm_num)
  let u := deriv γ t₀
  let f : ℝ → ℝ := fun t ↦ det2 u (γ t - γ t₀)
  have hf_nonneg : ∀ t, 0 ≤ f t :=
    fun t ↦ bdy_det2_deriv_sub_nonneg hK hγ t₀ (bdy_mem hK hγ t)
  have hf0 : f t₀ = 0 := by simp [f, det2]
  have hdf : deriv f = fun t ↦ det2 u (deriv γ t) :=
    funext fun t ↦ (bdy_hasDerivAt_det2 u (γ t₀) (hdiff t).hasDerivAt).deriv
  have hdf0 : deriv f t₀ = 0 := by
    rw [hdf]
    simp only [u, det2]
    ring
  have hddf : deriv (deriv f) t₀ = det2 u (deriv (deriv γ) t₀) := by
    rw [hdf]
    have h := bdy_hasDerivAt_det2 u 0 hdd.hasDerivAt
    simp only [sub_zero] at h
    exact h.deriv
  by_contra hneg
  have hlt : deriv (deriv f) t₀ < 0 := by rw [hddf]; exact not_le.1 hneg
  have hmax : IsLocalMax f t₀ := isLocalMax_of_deriv_deriv_neg hlt hdf0
    (bdy_hasDerivAt_det2 u (γ t₀) (hdiff t₀).hasDerivAt).continuousAt
  have hev : f =ᶠ[𝓝 t₀] fun _ ↦ (0 : ℝ) :=
    Filter.Eventually.mono hmax fun t ht ↦ le_antisymm (hf0 ▸ ht) (hf_nonneg t)
  have hzero := hev.deriv.deriv_eq
  simp only [deriv_const'] at hzero
  linarith

/-- With both determinants normalized, matrix state curvature is exactly ordinary
signed curvature of the corresponding boundary contact. -/
lemma normalized_curvature_identity (g X X' : Mat2) (hg : g.det = 1)
    (hX : X.det = 1) (v : Fin 2 → ℝ) :
    det2 ((g * X) *ᵥ v) ((g * X * X + g * X') *ᵥ v) =
      det2 v ((X + X⁻¹ * X') *ᵥ v) := by
  have hunit : IsUnit X.det := by rw [hX]; exact isUnit_one
  have heq : (g * X) * (X + X⁻¹ * X') = g * X * X + g * X' := by
    rw [Matrix.mul_add, ← Matrix.mul_assoc (g * X) X⁻¹ X',
      Matrix.mul_assoc g X X⁻¹, Matrix.mul_nonsing_inv _ hunit, Matrix.mul_one]
  rw [← heq, ← Matrix.mulVec_mulVec v (g * X) (X + X⁻¹ * X'), oct_det2_mulVec,
    Matrix.det_mul, hg, hX, one_mul, one_mul]

private lemma ae_hasDerivAtEntrywise_of_lipschitz_univ {X : ℝ → Mat2}
    (hLip : LipschitzOnEntrywise X univ) :
    ∀ᵐ t, HasDerivAtEntrywise X (derivEntrywise X t) t := by
  have h : ∀ i j, ∀ᵐ t, DifferentiableAt ℝ (fun s ↦ X s i j) t := by
    intro i j
    obtain ⟨C, hC⟩ := hLip i j
    exact (lipschitzOnWith_univ.1 hC).ae_differentiableAt
  have hall : ∀ᵐ t, ∀ i j, DifferentiableAt ℝ (fun s ↦ X s i j) t :=
    ae_all_iff.2 fun i ↦ ae_all_iff.2 (h i)
  filter_upwards [hall] with t ht
  exact fun i j ↦ (ht i j).hasDerivAt

/-- This obtains the curvature input of Chapter 3 directly from actual normalized
convex boundary curves, rather than assuming it as an extra control hypothesis. -/
theorem stateCurvature_nonneg_of_boundary {K : Set (Fin 2 → ℝ)}
    (hK : IsCCSDisk K) {σ : ZMod 6 → ℝ → Fin 2 → ℝ}
    (hpar : ∀ j, IsPositiveBoundaryParam K (σ j)) {g X : ℝ → Mat2}
    (hframe : ∀ j t, σ j t = g t *ᵥ sixthRoot j)
    (hg : ∀ t, HasDerivAtEntrywise g (g t * X t) t)
    (hdetg : ∀ t, (g t).det = 1) (hdetX : ∀ t, (X t).det = 1)
    (hLip : LipschitzOnEntrywise X univ) :
    ∀ᵐ t, ∀ j, 0 ≤ stateCurvature (X t) (derivEntrywise X t) j := by
  filter_upwards [ae_hasDerivAtEntrywise_of_lipschitz_univ hLip] with t hXt
  intro j
  let k : ZMod 6 := 2 * (j.val : ZMod 6)
  have hfirst : deriv (σ k) = fun s ↦ (g s * X s) *ᵥ sixthRoot k := by
    apply funext
    intro s
    have heq : (fun r ↦ g r *ᵥ sixthRoot k) = σ k := (funext (hframe k)).symm
    have hd := (hg s).mulVec_const (sixthRoot k)
    rw [heq] at hd
    exact hd.deriv
  have hsecond : HasDerivAt (deriv (σ k))
      ((g t * X t * X t + g t * derivEntrywise X t) *ᵥ sixthRoot k) t := by
    rw [hfirst]
    exact ((hg t).mul hXt).mulVec_const (sixthRoot k)
  have hcurv := positiveBoundary_curvature_nonneg hK (hpar k) hsecond.differentiableAt
  calc
    0 ≤ det2 (deriv (σ k) t) (deriv (deriv (σ k)) t) := hcurv
    _ = stateCurvature (X t) (derivEntrywise X t) j := by
      rw [congrFun hfirst t, hsecond.deriv]
      exact normalized_curvature_identity (g t) (X t) (derivEntrywise X t)
        (hdetg t) (hdetX t) (sixthRoot k)

/-! ## Regularity and the integral form of the state equation -/

private lemma exists_lipschitzOn_mul_of_compact {f h : ℝ → ℝ} {s : Set ℝ}
    (hs : IsCompact s) (hf : ∃ C, LipschitzOnWith C f s)
    (hh : ∃ C, LipschitzOnWith C h s) :
    ∃ C, LipschitzOnWith C (fun t ↦ f t * h t) s := by
  obtain ⟨Cf, hf⟩ := hf
  obtain ⟨Ch, hh⟩ := hh
  obtain ⟨Mf, hMf⟩ := hs.exists_bound_of_continuousOn hf.continuousOn
  obtain ⟨Mh, hMh⟩ := hs.exists_bound_of_continuousOn hh.continuousOn
  simp only [Real.norm_eq_abs] at hMf hMh
  refine ⟨_, LipschitzOnWith.of_dist_le' (K := Mf * Ch + Mh * Cf)
    fun x hx y hy ↦ ?_⟩
  have hfxy := hf.dist_le_mul x hx y hy
  have hhxy := hh.dist_le_mul x hx y hy
  have hMf0 : 0 ≤ Mf := (abs_nonneg _).trans (hMf x hx)
  have hMh0 : 0 ≤ Mh := (abs_nonneg _).trans (hMh y hy)
  simp only [Real.dist_eq] at hfxy hhxy ⊢
  calc
    |f x * h x - f y * h y| = |f x * (h x - h y) + h y * (f x - f y)| := by
      congr 1
      ring
    _ ≤ |f x| * |h x - h y| + |h y| * |f x - f y| := by
      rw [← abs_mul, ← abs_mul]
      exact abs_add_le _ _
    _ ≤ Mf * (Ch * |x - y|) + Mh * (Cf * |x - y|) := by
      gcongr
      · exact hMf x hx
      · exact hMh y hy
    _ = (Mf * Ch + Mh * Cf) * |x - y| := by ring

/-- `g' = g X` is Lipschitz on each compact interval when `X` is Lipschitz.
The regularity of `g'` required by upstream Theorem 3.4.2 is therefore derived. -/
theorem frame_velocity_lipschitz {g X : ℝ → Mat2}
    (hg : ∀ t, HasDerivAtEntrywise g (g t * X t) t)
    (hLip : LipschitzOnEntrywise X univ) (T : ℝ) :
    LipschitzOnEntrywise (fun t ↦ g t * X t) (Icc 0 T) := by
  have hXc := continuous_of_lipschitzOnEntrywise_univ hLip
  have hgc : Continuous g := continuous_iff_continuousAt.mpr fun t ↦ (hg t).continuousAt
  have hvc : Continuous fun t ↦ g t * X t := hgc.matrix_mul hXc
  have hgC : ∀ i j, ContDiff ℝ 1 (fun t ↦ g t i j) := by
    intro i j
    refine contDiff_one_iff_deriv.mpr ⟨fun t ↦ (hg t i j).differentiableAt, ?_⟩
    have heq : deriv (fun t ↦ g t i j) = fun t ↦ (g t * X t) i j :=
      funext fun t ↦ (hg t i j).deriv
    rw [heq]
    exact Matrix.continuous_iff_entrywise.mp hvc i j
  have hgLip : LipschitzOnEntrywise g (Icc 0 T) := fun i j ↦
    (hgC i j).contDiffOn.exists_lipschitzOnWith one_ne_zero (convex_Icc 0 T) isCompact_Icc
  have hXLip : LipschitzOnEntrywise X (Icc 0 T) := fun i j ↦ by
    obtain ⟨C, hC⟩ := hLip i j
    exact ⟨C, hC.mono (subset_univ _)⟩
  intro i j
  obtain ⟨C0, h0⟩ := exists_lipschitzOn_mul_of_compact isCompact_Icc (hgLip i 0) (hXLip 0 j)
  obtain ⟨C1, h1⟩ := exists_lipschitzOn_mul_of_compact isCompact_Icc (hgLip i 1) (hXLip 1 j)
  exact ⟨C0 + C1, by simpa only [Matrix.mul_apply, Fin.sum_univ_two] using h0.add h1⟩

/-- A periodic matrix curve that is Lipschitz on two periods is globally Lipschitz.
This makes the regularity needed for a new balanced-pair witness available publicly. -/
theorem lipschitzOnEntrywise_univ_of_periodic {f : ℝ → Mat2} {P : ℝ}
    (hP : 0 < P) (hper : Function.Periodic f P)
    (hLip : LipschitzOnEntrywise f (Icc 0 (2 * P))) :
    LipschitzOnEntrywise f univ := by
  intro i j
  obtain ⟨C, hC⟩ := hLip i j
  have hp : Function.Periodic (fun t ↦ f t i j) P := fun t ↦ congrFun (congrFun (hper t) i) j
  obtain ⟨M, hM⟩ := isCompact_Icc.exists_bound_of_continuousOn hC.continuousOn
  simp only [Real.norm_eq_abs] at hM
  have hb : ∀ t, |f t i j| ≤ M := by
    intro t
    obtain ⟨s, hs, heq⟩ := hp.exists_mem_Ico₀ hP t
    rw [heq]
    exact hM s ⟨hs.1, by linarith [hs.2]⟩
  have hM0 : 0 ≤ M := (abs_nonneg _).trans (hb 0)
  have hclose : ∀ x y, x ≤ y → y - x < P →
      |f x i j - f y i j| ≤ C * |x - y| := by
    intro x y hxy hnear
    obtain ⟨n, ⟨hn0, hnP⟩, _⟩ := existsUnique_zsmul_near_of_pos' hP x
    have hx : x - n • P ∈ Icc 0 (2 * P) := ⟨hn0, by linarith⟩
    have hy : y - n • P ∈ Icc 0 (2 * P) := ⟨by linarith, by linarith⟩
    have hd := hC.dist_le_mul _ hx _ hy
    rwa [Real.dist_eq, Real.dist_eq, hp.sub_zsmul_eq, hp.sub_zsmul_eq,
      show x - n • P - (y - n • P) = x - y by ring] at hd
  refine ⟨_, LipschitzOnWith.of_dist_le' (K := max (C : ℝ) (2 * M / P))
    fun x _ y _ ↦ ?_⟩
  rw [Real.dist_eq, Real.dist_eq]
  rcases le_or_gt P |x - y| with hfar | hnear
  · calc
      |f x i j - f y i j| ≤ |f x i j| + |f y i j| := abs_sub _ _
      _ ≤ 2 * M := by linarith [hb x, hb y]
      _ = 2 * M / P * P := by field_simp [hP.ne']
      _ ≤ 2 * M / P * |x - y| := by gcongr
      _ ≤ max (C : ℝ) (2 * M / P) * |x - y| := by gcongr; exact le_max_right _ _
  · have hd : |f x i j - f y i j| ≤ C * |x - y| := by
      rcases le_total x y with hxy | hyx
      · exact hclose x y hxy (by
          rw [abs_sub_comm, abs_of_nonneg (by linarith)] at hnear
          exact hnear)
      · rw [abs_sub_comm (f x i j), abs_sub_comm x]
        exact hclose y x hyx (by
          rw [abs_of_nonneg (by linarith)] at hnear
          exact hnear)
    exact hd.trans (by gcongr; exact le_max_left _ _)

/-- A periodic frame satisfying `g' = g X` has globally Lipschitz velocity when
the normalized state is globally Lipschitz. Periodicity of the velocity is derived
by differentiating periodicity of the frame. -/
theorem frame_velocity_lipschitz_periodic {g X : ℝ → Mat2}
    (hg : ∀ t, HasDerivAtEntrywise g (g t * X t) t)
    (hLip : LipschitzOnEntrywise X univ) {P : ℝ} (hP : 0 < P)
    (hperiod : Function.Periodic g P) :
    LipschitzOnEntrywise (fun t ↦ g t * X t) univ := by
  have hvperiod : Function.Periodic (fun t ↦ g t * X t) P := by
    intro t
    have hs : HasDerivAt (fun u : ℝ ↦ u + P) 1 t := (hasDerivAt_id t).add_const P
    have hd := HasDerivAtEntrywise.scomp (h := fun u ↦ u + P) (hg (t + P)) hs
    have heq : (fun u ↦ g (u + P)) = g := funext hperiod
    rw [heq, one_smul] at hd
    exact hd.unique (hg t)
  exact lipschitzOnEntrywise_univ_of_periodic hP hvperiod
    (frame_velocity_lipschitz hg hLip (2 * P))

/-- The absolutely-continuous FTC, entry by entry. An almost-everywhere derivative
is sufficient; no countability assumption is made on the exceptional set. -/
theorem integralCurve_of_lipschitz_ae {f v : ℝ → Mat2} {T : ℝ} (hT : 0 ≤ T)
    (hLip : LipschitzOnEntrywise f (Icc 0 T))
    (hd : ∀ᵐ t, t ∈ Ioo 0 T → HasDerivAtEntrywise f (v t) t) :
    IsIntegralCurve f v T := by
  intro i j
  obtain ⟨C, hC⟩ := hLip i j
  have hac : AbsolutelyContinuousOnInterval (fun t ↦ f t i j) 0 T :=
    (hC.mono (uIcc_of_le hT).subset).absolutelyContinuousOnInterval
  have hae (b : ℝ) (hb : b ∈ Icc 0 T) :
      ∀ᵐ t, t ∈ uIoc 0 b → deriv (fun s ↦ f s i j) t = v t i j := by
    filter_upwards [hd, volume.ae_ne T] with t ht hne htb
    rw [uIoc_of_le hb.1] at htb
    exact (ht ⟨htb.1, lt_of_le_of_ne (htb.2.trans hb.2) hne⟩ i j).deriv
  refine ⟨hac.intervalIntegrable_deriv.congr_ae ?_, ?_⟩
  · exact (ae_restrict_iff' measurableSet_uIoc).2 (hae T ⟨hT, le_rfl⟩)
  · intro t ht
    have hact := hac.mono (uIcc_subset_uIcc left_mem_uIcc (Icc_subset_uIcc ht))
    calc
      f t i j = f 0 i j + ∫ s in (0 : ℝ)..t, deriv (fun r ↦ f r i j) s := by
        rw [hact.integral_deriv_eq_sub]
        ring
      _ = f 0 i j + ∫ s in (0 : ℝ)..t, v s i j := by
        rw [intervalIntegral.integral_congr_ae (hae t ht)]

/-- The raw curvature control and its repair agree almost everywhere on the interval. -/
theorem boundaryControl_eq_raw_ae {g X : ℝ → Mat2} {T : ℝ}
    (hg : ∀ t, HasDerivAtEntrywise g (g t * X t) t)
    (hdetg : ∀ t, (g t).det = 1) (hstar : ∀ t, IsStarState (X t))
    (hcurv : ∀ᵐ t, t ∈ Ioo 0 T → ∀ j, 0 ≤ stateCurvature (X t) (derivEntrywise X t) j) :
    ∀ᵐ t, t ∈ Ioo 0 T →
      boundaryControl X t = controlVariables (stateCurvature (X t) (derivEntrywise X t)) := by
  have hlog : ∀ t, X t = (g t)⁻¹ * (g t * X t) := by
    intro t
    have hu : IsUnit (g t).det := by rw [hdetg t]; exact isUnit_one
    rw [← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hu, Matrix.one_mul]
  have hp := lemma3_3_1 T g (fun t ↦ g t * X t)
    (fun t _ ↦ (hg t).hasDerivWithinAtEntrywise) (fun t _ ↦ hdetg t) X hlog
    (fun t _ ↦ (hstar t).2.2) hcurv
  filter_upwards [hcurv, hp] with t hκ hp ht
  have hn := hκ ht
  have hsum : 0 < stateCurvature (X t) (derivEntrywise X t) 0 +
      stateCurvature (X t) (derivEntrywise X t) 1 +
      stateCurvature (X t) (derivEntrywise X t) 2 := by
    obtain ⟨j, hj⟩ := hp ht
    fin_cases j <;> simp only [Fin.reduceFinMk] at hj <;> linarith [hn 0, hn 1, hn 2]
  have husable : UsableCurvatures (stateCurvature (X t) (derivEntrywise X t)) :=
    ⟨hn 0, hn 1, hn 2, hsum⟩
  simp only [boundaryControl, repairedCurvatureControl, if_pos husable]

/-- A normalized actual boundary frame produces a state trajectory, with an explicit
measurable control and with both integral equations proved. -/
theorem normalized_boundary_isStateTrajectory {K : Set (Fin 2 → ℝ)}
    (hK : IsCCSDisk K) {σ : ZMod 6 → ℝ → Fin 2 → ℝ}
    (hpar : ∀ j, IsPositiveBoundaryParam K (σ j)) {g X : ℝ → Mat2}
    (hframe : ∀ j t, σ j t = g t *ᵥ sixthRoot j)
    (hg : ∀ t, HasDerivAtEntrywise g (g t * X t) t)
    (hdetg : ∀ t, (g t).det = 1) (hstar : ∀ t, IsStarState (X t))
    (hLip : LipschitzOnEntrywise X univ) {T : ℝ} (hT : 0 < T) :
    IsStateTrajectory T (boundaryControl X) g X := by
  have hXc := continuous_of_lipschitzOnEntrywise_univ hLip
  have hgc : Continuous g := continuous_iff_continuousAt.mpr fun t ↦ (hg t).continuousAt
  have hvc : Continuous fun t ↦ g t * X t := hgc.matrix_mul hXc
  have hcurv : ∀ᵐ t, t ∈ Ioo 0 T →
      ∀ j, 0 ≤ stateCurvature (X t) (derivEntrywise X t) j := by
    filter_upwards [stateCurvature_nonneg_of_boundary hK hpar hframe hg hdetg
      (fun t ↦ (hstar t).2.1) hLip] with t ht _ using ht
  have hlog : ∀ t, X t = (g t)⁻¹ * (g t * X t) := by
    intro t
    have hu : IsUnit (g t).det := by rw [hdetg t]; exact isUnit_one
    rw [← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hu, Matrix.one_mul]
  have hraw := theorem3_4_2 T g (fun t ↦ g t * X t)
    (fun t _ ↦ (hg t).hasDerivWithinAtEntrywise) (fun t _ ↦ hdetg t)
    (frame_velocity_lipschitz hg hLip T) X hlog (fun t _ ↦ (hstar t).2.1)
    (fun t _ ↦ (hstar t).2.2) hcurv
    (fun t ↦ controlVariables (stateCurvature (X t) (derivEntrywise X t))) (fun _ ↦ rfl)
  have hXode : ∀ᵐ t, t ∈ Ioo 0 T → HasDerivAtEntrywise X
      (controlP (boundaryControl X t) (X t) * X t -
        X t * controlP (boundaryControl X t) (X t)) t := by
    filter_upwards [hraw, boundaryControl_eq_raw_ae hg hdetg hstar hcurv] with t hd hu ht
    rw [hu ht]
    simpa only [controlP, Matrix.smul_mul, Matrix.mul_smul, smul_sub] using hd ht
  have hXint : IsIntegralCurve X
      (fun t ↦ controlP (boundaryControl X t) (X t) * X t -
        X t * controlP (boundaryControl X t) (X t)) T := by
    apply integralCurve_of_lipschitz_ae hT.le (fun i j ↦ ?_) hXode
    obtain ⟨C, hC⟩ := hLip i j
    exact ⟨C, hC.mono (subset_univ _)⟩
  have hgint : IsIntegralCurve g (fun t ↦ g t * X t) T :=
    Matrix.eq_add_integral_of_hasDerivWithinAtEntrywise
      (fun t _ ↦ (hg t).hasDerivWithinAtEntrywise)
      (fun i j ↦ (Matrix.continuous_iff_entrywise.mp hvc i j).intervalIntegrable _ _)
  exact ⟨hT, measurable_boundaryControl hXc (fun t ↦ (hstar t).2.1),
    fun t _ ↦ boundaryControl_mem X t, fun t _ ↦ ⟨hdetg t, hstar t⟩, hgint, hXint⟩

/-! ## Discharging the inputs with the constructed determinant clock -/

/-- The periodicity, exhaustiveness, and orientation clauses of a balanced pair
give a positive global boundary parametrization for every contact. -/
theorem positiveBoundaryParam_of_balanced {K : Set (Fin 2 → ℝ)}
    {σ : ZMod 6 → ℝ → Fin 2 → ℝ} {tf : ℝ} (hbal : IsBalancedPair K σ tf)
    (j : ZMod 6) : IsPositiveBoundaryParam K (σ j) := by
  have hperiod : Function.Periodic (σ j) (6 * tf) := hbal.2.2.2.2.2.2.2.1 j
  have htf : 0 < tf := hbal.2.2.2.2.2.2.1
  have himage : σ j '' Ico 0 (6 * tf) = frontier K := hbal.2.2.2.2.2.2.2.2.2 j
  refine ⟨(hbal.2.1 j).1, (hbal.2.1 j).2, ?_, oct_det2_deriv_pos hbal j⟩
  apply Subset.antisymm
  · rintro _ ⟨t, rfl⟩
    obtain ⟨s, hs, heq⟩ := hperiod.exists_mem_Ico₀ (by positivity : 0 < 6 * tf) t
    rw [heq, ← himage]
    exact mem_image_of_mem (σ j) hs
  · rw [← himage]
    exact image_subset_range _ _

/-- Any explicit determinant clock with the properties constructed in
`balanced_exists_determinant_clock` realizes a balanced disk as a state trajectory.
The only control in the conclusion is the formula `boundaryControl`. -/
theorem balanced_determinantClock_isStateTrajectory {K : Set (Fin 2 → ℝ)}
    {σ : ZMod 6 → ℝ → Fin 2 → ℝ} {tf : ℝ} (hbal : IsBalancedPair K σ tf)
    (a : ℝ ≃o ℝ) (ha : ContDiff ℝ 1 (fun t ↦ a t))
    (hapos : ∀ t, 0 < deriv (fun u ↦ a u) t)
    (hstar : ∀ t, IsStarState (normalizedContactState σ a t))
    (hLip : LipschitzOnEntrywise (normalizedContactState σ a) univ)
    (hg : ∀ t, HasDerivAtEntrywise (fun u ↦ contactFrame σ (a u))
      (contactFrame σ (a t) * normalizedContactState σ a t) t)
    {T : ℝ} (hT : 0 < T) :
    IsStateTrajectory T (boundaryControl (normalizedContactState σ a))
      (fun t ↦ contactFrame σ (a t)) (normalizedContactState σ a) := by
  apply normalized_boundary_isStateTrajectory hbal.1
    (σ := fun j ↦ σ j ∘ a)
    (fun j ↦ positiveBoundaryParam_reparam (positiveBoundaryParam_of_balanced hbal j)
      a ha hapos)
    (fun j t ↦ contactFrame_action hbal.2.2.2.1 (a t) j) hg
    (fun t ↦ contactFrame_det hbal.2.2.2.1 (a t)) hstar hLip hT

/-- A balanced disk in circle representation supplies a genuine state trajectory
over one sixth of the determinant-clock period, with identity initial frame.

This theorem does not yet identify the terminal frame: that additionally uses the
cyclic successor construction, not merely full-period boundary exhaustiveness. -/
theorem balanced_exists_stateTrajectory {K : Set (Fin 2 → ℝ)}
    {σ : ZMod 6 → ℝ → Fin 2 → ℝ} {tf : ℝ} (hbal : IsBalancedPair K σ tf)
    (hcirc : IsCircleRepresentation σ) :
    ∃ P : ℝ, 0 < P ∧ ∃ a : ℝ ≃o ℝ,
      a 0 = 0 ∧
      (∀ t, a (t + P) = a t + 6 * tf) ∧
      IsStateTrajectory (P / 6) (boundaryControl (normalizedContactState σ a))
        (fun t ↦ contactFrame σ (a t)) (normalizedContactState σ a) ∧
      contactFrame σ (a 0) = 1 := by
  obtain ⟨P, hP, a, ha0, haC, haD, hapos, haper, hstar, hLip, hg⟩ :=
    balanced_exists_determinant_clock hbal
  refine ⟨P, hP, a, ha0, haper,
    balanced_determinantClock_isStateTrajectory hbal a haC hapos hstar hLip hg
      (by positivity), ?_⟩
  rw [ha0]
  exact contactFrame_initial hcirc

/-- The forward state problem is inhabited by the constructed representation of an
actual global worst disk in normal position. No state trajectory is postulated. -/
theorem normalized_worstDisk_exists_stateTrajectory {K : Set (Fin 2 → ℝ)}
    (hK : IsWorstDisk K) (hS : rein_Std K) :
    ∃ (σ : ZMod 6 → ℝ → Fin 2 → ℝ) (tf P : ℝ) (a : ℝ ≃o ℝ),
      IsBalancedPair K σ tf ∧ IsCircleRepresentation σ ∧ 0 < P ∧
      IsStateTrajectory (P / 6) (boundaryControl (normalizedContactState σ a))
        (fun t ↦ contactFrame σ (a t)) (normalizedContactState σ a) ∧
      contactFrame σ (a 0) = 1 := by
  obtain ⟨σ, tf, hbal, hcirc⟩ := normalized_worstDisk_exists_balanced_circle hK hS
  obtain ⟨P, hP, a, _, _, htraj, hg0⟩ := balanced_exists_stateTrajectory hbal hcirc
  exact ⟨σ, tf, P, a, hbal, hcirc, hP, htraj, hg0⟩

end SmoothedOctagon
