module

public import SmoothedOctagon.Foundations.BoundaryTrace
public import SmoothedPolygons.Ch3.AreaFormula
public import Mathlib.Analysis.Calculus.Deriv.Inverse
public import Mathlib.Analysis.Calculus.ContDiff.Deriv
public import Mathlib.Logic.Function.Iterate
public import Mathlib.Order.Hom.Basic
public import Mathlib.Tactic

/-!
# A smooth lift of the cyclic contact map

For a balanced circle representation of an actual worst disk, this module constructs a
positive `C¹` change of boundary parameter `φ` satisfying
`σ_j(φ(t)) = σ_{j+1}(t)` and `φ^[6](t) = t + 6 tf`.

The construction starts with the unique indexed critical hexagon at each polar angle.
Its successor angle advances by less than `π`; two steps still advance by less than `π`,
because the determinant of midpoint `0` and midpoint `2` is positive. Three steps therefore
reach the antipodal point after exactly `π`, and six steps make exactly one full turn.

The polar-angle lift of `σ₀` transports this map to the actual balanced parameter.
Regularity is then proved from `σ₀ ∘ φ = σ₁` by a scalar inverse-composition theorem at a
nonzero tangent coordinate. The derivative of `φ` is a quotient of positive determinant
densities. No regularity of a contact map is assumed.

This module supplies the geometric cyclic lift. A clock whose density transforms covariantly
under that lift can turn it into translation by one sixth of the new full period.
Compilation and kernel validation have not been run.
-/

@[expose] public section

namespace SmoothedOctagon

open Set Filter Topology Real SmoothedPolygons

variable {K : Set (Fin 2 → ℝ)}

/-- The polar angle of the next contact of the selected indexed critical hexagon. -/
noncomputable def successorAngle (hG : rein_Good K) (θ : ℝ) : ℝ :=
  rein_φ (criticalHexagonAtAngle hG) K 1 θ

lemma successorAngle_continuous (hG : rein_Good K) : Continuous (successorAngle hG) :=
  rein_continuous_φ hG (fun θ ↦ (criticalHexagonAtAngle_spec hG θ).1)
    (fun θ ↦ (criticalHexagonAtAngle_spec hG θ).2) (Or.inl rfl)

lemma successorAngle_strictMono (hG : rein_Good K) : StrictMono (successorAngle hG) :=
  rein_strictMono_φ hG (fun θ ↦ (criticalHexagonAtAngle_spec hG θ).1)
    (fun θ ↦ (criticalHexagonAtAngle_spec hG θ).2) (Or.inl rfl)

lemma successorAngle_add_two_pi (hG : rein_Good K) (θ : ℝ) :
    successorAngle hG (θ + 2 * π) = successorAngle hG θ + 2 * π := by
  simpa only [successorAngle, Int.cast_one, one_mul] using
    rein_φ_add_int hG (fun t ↦ (criticalHexagonAtAngle_spec hG t).1)
      (fun t ↦ (criticalHexagonAtAngle_spec hG t).2) (j := 1) θ 1

/-- Adjacent contacts advance strictly counterclockwise by less than a half turn. -/
lemma successorAngle_bounds (hG : rein_Good K) (θ : ℝ) :
    θ < successorAngle hG θ ∧ successorAngle hG θ < θ + π := by
  have hx : rein_bd K θ ≠ 0 := by
    intro hzero
    have hfront := rein_bd_mem_frontier hG.1 θ
    rw [hzero] at hfront
    exact hfront.2 (rein_zero_mem_interior hG.1)
  have hdet : 0 < det2 (rein_bd K θ) (criticalBoundaryTrace hG 1 θ) := by
    rw [← (criticalHexagonAtAngle_spec hG θ).2]
    exact rein_det2_hexMidpoint_pos (criticalHexagonAtAngle_spec hG θ).1.1
  have him := rein_im_div_pos hx hdet
  have harg0 : 0 ≤ Complex.arg
      (rein_toC (criticalBoundaryTrace hG 1 θ) / rein_toC (rein_bd K θ)) :=
    Complex.arg_nonneg_iff.2 him.le
  have hargne : Complex.arg
      (rein_toC (criticalBoundaryTrace hG 1 θ) / rein_toC (rein_bd K θ)) ≠ 0 := by
    intro hzero
    have hi0 := (Complex.arg_eq_zero_iff.1 hzero).2
    linarith
  have hargπ := Complex.arg_lt_pi_iff.2 (Or.inr him.ne')
  have hargpos := lt_of_le_of_ne harg0 (Ne.symm hargne)
  change θ < θ + rein_ang (rein_bd K θ) (criticalBoundaryTrace hG 1 θ) ∧
    θ + rein_ang (rein_bd K θ) (criticalBoundaryTrace hG 1 θ) < θ + π
  unfold rein_ang
  constructor <;> linarith

/-- Selecting the next first midpoint shifts the entire indexed critical hexagon. -/
lemma criticalBoundaryTrace_successor (hG : rein_Good K) (j : ZMod 6) (θ : ℝ) :
    criticalBoundaryTrace hG j (successorAngle hG θ) =
      criticalBoundaryTrace hG (j + 1) θ := by
  obtain ⟨r, hr, hpolar⟩ :=
    rein_φ_spec hG (fun t ↦ (criticalHexagonAtAngle_spec hG t).1) (j := 1) θ
  have hfirst : hexMidpoint (criticalHexagonAtAngle hG θ) 1 =
      rein_bd K (successorAngle hG θ) :=
    rein_eq_bd hG.1 (criticalBoundaryTrace_mem_frontier hG 1 θ) hr hpolar
  have hshift := rein_isLeastAreaHexagon_shift (criticalHexagonAtAngle_spec hG θ).1 1
  have hV : (fun k ↦ criticalHexagonAtAngle hG θ (k + 1)) =
      criticalHexagonAtAngle hG (successorAngle hG θ) :=
    criticalHexagonAtAngle_unique hG hshift (by
      rw [rein_hexMidpoint_shift, zero_add]
      exact hfirst)
  change hexMidpoint (criticalHexagonAtAngle hG (successorAngle hG θ)) j =
    hexMidpoint (criticalHexagonAtAngle hG θ) (j + 1)
  rw [← hV, rein_hexMidpoint_shift]

lemma criticalBoundaryTrace_successor_iterate (hG : rein_Good K) (n : ℕ)
    (j : ZMod 6) (θ : ℝ) :
    criticalBoundaryTrace hG j ((successorAngle hG)^[n] θ) =
      criticalBoundaryTrace hG (j + (n : ZMod 6)) θ := by
  induction n generalizing j with
  | zero => simp
  | succ n ih =>
    rw [Function.iterate_succ_apply', criticalBoundaryTrace_successor, ih]
    have hi : j + 1 + (n : ZMod 6) = j + ((n + 1 : ℕ) : ZMod 6) := by
      push_cast
      ring
    rw [hi]

lemma rein_bd_add_pi_of_isCCSDisk (hK : IsCCSDisk K) (θ : ℝ) :
    rein_bd K (θ + π) = -rein_bd K θ := by
  apply Eq.symm
  apply rein_eq_bd hK (bdy_neg_mem_frontier hK (rein_bd_mem_frontier hK θ))
    (inv_pos.2 (rein_gauge_pos hK (rein_dir_ne_zero θ)))
  rw [rein_dir_add_pi, rein_bd, smul_neg]

/-- The first two successor steps remain before the antipodal contact. -/
lemma successorAngle_twice_lt_add_pi (hG : rein_Good K) (θ : ℝ) :
    successorAngle hG (successorAngle hG θ) < θ + π := by
  have h1 := successorAngle_bounds hG θ
  have h2 := successorAngle_bounds hG (successorAngle hG θ)
  have htrace : criticalBoundaryTrace hG 0
      (successorAngle hG (successorAngle hG θ)) = criticalBoundaryTrace hG 2 θ := by
    simpa only [Function.iterate_succ_apply, Function.iterate_zero_apply, zero_add,
      Nat.cast_ofNat] using criticalBoundaryTrace_successor_iterate hG 2 0 θ
  have hdet : 0 < det2 (rein_bd K θ)
      (rein_bd K (successorAngle hG (successorAngle hG θ))) := by
    rw [← criticalBoundaryTrace_zero hG, htrace]
    exact rein_det2_hexMidpoint_two (criticalHexagonAtAngle_spec hG θ).1.1
  have hsin := (rein_det2_bd_pos_iff hG.1 θ
    (successorAngle hG (successorAngle hG θ))).1 hdet
  have hangle := (rein_sin_pos_iff (by linarith [h1.1, h2.1] :
      0 ≤ successorAngle hG (successorAngle hG θ) - θ)
    (by linarith [h1.2, h2.2] :
      successorAngle hG (successorAngle hG θ) - θ < 2 * π)).1 hsin
  linarith [hangle.2]

/-- Three successor contacts advance by exactly `π`, with no additional winding. -/
lemma successorAngle_iterate_three (hG : rein_Good K) (θ : ℝ) :
    (successorAngle hG)^[3] θ = θ + π := by
  have h1 := successorAngle_bounds hG θ
  have h2 := successorAngle_bounds hG (successorAngle hG θ)
  have h3 := successorAngle_bounds hG (successorAngle hG (successorAngle hG θ))
  have htwo := successorAngle_twice_lt_add_pi hG θ
  have hanti : criticalBoundaryTrace hG 0 ((successorAngle hG)^[3] θ) =
      -criticalBoundaryTrace hG 0 θ := by
    calc
      criticalBoundaryTrace hG 0 ((successorAngle hG)^[3] θ) =
          criticalBoundaryTrace hG 3 θ := by
        simpa only [zero_add, Nat.cast_ofNat] using
          criticalBoundaryTrace_successor_iterate hG 3 0 θ
      _ = -criticalBoundaryTrace hG 0 θ := by
        simpa only [criticalBoundaryTrace, zero_add] using
          rein_hexMidpoint_add_three (criticalHexagonAtAngle_spec hG θ).1.1 0
  have hπ : criticalBoundaryTrace hG 0 (θ + π) = -criticalBoundaryTrace hG 0 θ := by
    rw [criticalBoundaryTrace_zero, rein_bd_add_pi_of_isCCSDisk hG.1]
  apply criticalBoundaryTrace_injOn hG 0 θ _ _ (hanti.trans hπ.symm)
  · change θ ≤ successorAngle hG (successorAngle hG (successorAngle hG θ)) ∧
      successorAngle hG (successorAngle hG (successorAngle hG θ)) < θ + 2 * π
    exact ⟨by linarith [h1.1, h2.1, h3.1], by linarith [h3.2, htwo]⟩
  · exact ⟨by linarith [pi_pos], by linarith [pi_pos]⟩

/-- The successor lift makes exactly one full turn in six steps. -/
lemma successorAngle_iterate_six (hG : rein_Good K) (θ : ℝ) :
    (successorAngle hG)^[6] θ = θ + 2 * π := by
  calc
    (successorAngle hG)^[6] θ =
        (successorAngle hG)^[3] ((successorAngle hG)^[3] θ) :=
      Function.iterate_add_apply (successorAngle hG) 3 3 θ
    _ = (θ + π) + π := by
      rw [successorAngle_iterate_three, successorAngle_iterate_three]
    _ = θ + 2 * π := by ring

/-- A continuous change of parameter between two positive regular `C¹` plane curves is
itself `C¹` and has positive derivative. A nonzero tangent coordinate provides the local
scalar inverse; taking determinants computes the derivative independently of that coordinate. -/
theorem contDiff_pos_of_positive_curve_comp
    {γ η : ℝ → Fin 2 → ℝ} {h : ℝ → ℝ}
    (hγ : ContDiff ℝ 1 γ) (hη : ContDiff ℝ 1 η)
    (hγpos : ∀ t, 0 < det2 (γ t) (deriv γ t))
    (hηpos : ∀ t, 0 < det2 (η t) (deriv η t))
    (hh : Continuous h) (hcomp : ∀ t, γ (h t) = η t) :
    ContDiff ℝ 1 h ∧ ∀ t, 0 < deriv h t := by
  classical
  have hdγ : Differentiable ℝ γ := (contDiff_one_iff_deriv.1 hγ).1
  have hdη : Differentiable ℝ η := (contDiff_one_iff_deriv.1 hη).1
  have hreg : ∀ t, deriv γ t ≠ 0 := by
    intro t hz
    have hp := hγpos t
    rw [hz] at hp
    simpa [det2] using hp
  have hdh : Differentiable ℝ h := by
    intro t
    obtain ⟨i, hi⟩ : ∃ i : Fin 2, deriv γ (h t) i ≠ 0 := by
      by_contra hnone
      push_neg at hnone
      apply hreg (h t)
      ext i
      exact hnone i
    have hcoordγ := hasDerivAt_pi.1 (hdγ (h t)).hasDerivAt i
    have hcoordη := hasDerivAt_pi.1 (hdη t).hasDerivAt i
    have heq : (fun s ↦ γ s i) ∘ h =ᶠ[𝓝 t] fun s ↦ η s i :=
      Filter.Eventually.of_forall fun s ↦ congrFun (hcomp s) i
    exact (HasDerivAt.of_comp_left hh.continuousAt hcoordγ hcoordη hi heq).differentiableAt
  have hchain : ∀ t, deriv h t • deriv γ (h t) = deriv η t := by
    intro t
    have hc := (hdγ (h t)).hasDerivAt.scomp t (hdh t).hasDerivAt
    have heq : γ ∘ h = η := funext hcomp
    rw [heq] at hc
    exact hc.deriv.symm
  have hquot : ∀ t, deriv h t =
      det2 (η t) (deriv η t) / det2 (γ (h t)) (deriv γ (h t)) := by
    intro t
    apply (eq_div_iff (hγpos (h t)).ne').2
    rw [← rein_det2_smul_right, hchain, hcomp]
  refine ⟨contDiff_one_iff_deriv.2 ⟨hdh, ?_⟩, fun t ↦ ?_⟩
  · have hderiv : deriv h = fun t ↦
        det2 (η t) (deriv η t) / det2 (γ (h t)) (deriv γ (h t)) := funext hquot
    rw [hderiv]
    exact (bdy_continuous_det2 hη.continuous hη.continuous_deriv_one).div
      (bdy_continuous_det2 (hγ.continuous.comp hh) (hγ.continuous_deriv_one.comp hh))
      (fun t ↦ (hγpos (h t)).ne')
  · rw [hquot]
    exact div_pos (hηpos t) (hγpos (h t))

open PlaneCurve

private lemma starCurve_angle_surjective {γ : ℝ → Fin 2 → ℝ} {T : ℝ}
    (h : IsStarCurve γ T) : Function.Surjective (sc_angle γ) := by
  have hmono := h.sc_strictMono_angle
  have hcont := h.sc_continuous_angle
  have hper : ∀ t, sc_angle γ (t + T) = sc_angle γ t + 2 * π := by
    intro t
    rw [h.sc_angle_add_period, h.sc_angle_period]
  have hk : ∀ (k : ℕ) (t : ℝ),
      sc_angle γ (t + (k : ℝ) * T) = sc_angle γ t + (k : ℝ) * (2 * π) := by
    intro k
    induction k with
    | zero => intro t; simp
    | succ k ih =>
      intro t
      push_cast
      rw [show t + ((k : ℝ) + 1) * T = (t + (k : ℝ) * T) + T by ring, hper, ih]
      ring
  refine hcont.surjective
    (tendsto_atTop_atTop_of_monotone hmono.monotone fun b ↦ ?_)
    (tendsto_atBot_atBot_of_monotone hmono.monotone fun b ↦ ?_)
  · obtain ⟨k, hk'⟩ := exists_nat_ge (b / (2 * π))
    refine ⟨0 + k * T, ?_⟩
    rw [hk, sc_angle_zero]
    have := (div_le_iff₀ two_pi_pos).1 hk'
    linarith
  · obtain ⟨k, hk'⟩ := exists_nat_ge (-b / (2 * π))
    refine ⟨-(k * T), ?_⟩
    have h1 := hk k (-(k * T))
    rw [neg_add_cancel, sc_angle_zero] at h1
    have := (div_le_iff₀ two_pi_pos).1 hk'
    linarith

private lemma balancedCurve_mem_frontier {σ : ZMod 6 → ℝ → Fin 2 → ℝ} {tf : ℝ}
    (hbal : IsBalancedPair K σ tf) (j : ZMod 6) (t : ℝ) : σ j t ∈ frontier K := by
  obtain ⟨_, _, _, _, _, _, htf, hper, _, himage⟩ := hbal
  have hT : 0 < 6 * tf := by positivity
  have hp : Function.Periodic (σ j) (6 * tf) := hper j
  have hmod : σ j (toIcoMod hT 0 t) = σ j t := by
    rw [← self_sub_toIcoDiv_zsmul]
    exact hp.sub_zsmul_eq _
  rw [← hmod, ← himage j]
  exact mem_image_of_mem (σ j) (toIcoMod_mem_Ico' hT t)

/-- With initial direction `(1,0)`, the upstream global angle lift gives the actual radial
coordinate of a star curve on the boundary. -/
private lemma starCurve_eq_radial {γ : ℝ → Fin 2 → ℝ} {T : ℝ}
    (hK : IsCCSDisk K) (h : IsStarCurve γ T)
    (hmem : ∀ t, γ t ∈ frontier K) (hzero : γ 0 = sixthRoot 0) (t : ℝ) :
    γ t = rein_bd K (sc_angle γ t) := by
  have hz0 : sc_toC (γ 0) = (1 : ℂ) := by
    rw [hzero]
    simp [sc_toC, sixthRoot]
  have hz := h.sc_toC_eq t
  rw [hz0, one_mul] at hz
  apply rein_eq_bd hK (hmem t) (Real.exp_pos (sc_log γ t).re)
  ext i
  fin_cases i
  · have hre := congrArg Complex.re hz
    simpa only [sc_toC_re, Complex.exp_re, rein_dir, sc_angle, Pi.smul_apply,
      smul_eq_mul, Fin.zero_eta, Matrix.cons_val_zero] using hre
  · have him := congrArg Complex.im hz
    simpa only [sc_toC_im, Complex.exp_im, rein_dir, sc_angle, Pi.smul_apply,
      smul_eq_mul, Fin.mk_one, Matrix.cons_val_one, Matrix.cons_val_zero] using him

/-- Every balanced circle representation of an actual worst disk has a smooth positive
successor lift. It shifts all six contacts and advances by exactly one full period after
six iterations. The lift is constructed from the geometric data, not assumed. -/
theorem exists_positive_cyclic_contact_lift
    {σ : ZMod 6 → ℝ → Fin 2 → ℝ} {tf : ℝ}
    (hK : IsWorstDisk K) (hbal : IsBalancedPair K σ tf) (hcirc : IsCircleRepresentation σ) :
    ∃ φ : ℝ → ℝ, ContDiff ℝ 1 φ ∧
      (∀ t, 0 < deriv φ t) ∧
      (∀ j t, σ j (φ t) = σ (j + 1) t) ∧
      (∀ t, φ^[6] t = t + 6 * tf) ∧
      (∀ t, φ (t + 6 * tf) = φ t + 6 * tf) ∧
      (∀ t, t < φ t) := by
  classical
  let hG := rein_good_of_worst (ch2_isWorstLatticeDisk_iff_isWorstDisk.2 hK)
  have hstar : IsStarCurve (σ 0) (6 * tf) := oct_isStarCurve hbal 0
  let α : ℝ → ℝ := sc_angle (σ 0)
  have hαmono : StrictMono α := hstar.sc_strictMono_angle
  have hαsurj : Function.Surjective α := starCurve_angle_surjective hstar
  choose r hr using hαsurj
  let e : ℝ ≃o ℝ := StrictMono.orderIsoOfRightInverse α hαmono r hr
  have heperiod : ∀ t, e (t + 6 * tf) = e t + 2 * π := by
    intro t
    change sc_angle (σ 0) (t + 6 * tf) = sc_angle (σ 0) t + 2 * π
    rw [hstar.sc_angle_add_period, hstar.sc_angle_period]
  have hmem : ∀ j t, σ j t ∈ frontier K := balancedCurve_mem_frontier hbal
  have hzero : ∀ t, σ 0 t = rein_bd K (e t) :=
    starCurve_eq_radial hK.1 hstar (hmem 0) (hcirc 0)
  have htrace : ∀ j t, σ j t = criticalBoundaryTrace hG j (e t) := by
    intro j t
    exact bdy_eq_hexMidpoint hK (criticalHexagonAtAngle_spec hG (e t)).1
      (fun k ↦ criticalBoundaryTrace_mem_frontier hG k (e t))
      (hbal.2.2.2.1 t) (fun k ↦ hmem k t)
      ((hzero t).trans (criticalHexagonAtAngle_spec hG (e t)).2.symm) j
  let φ : ℝ → ℝ := fun t ↦ e.symm (successorAngle hG (e t))
  have hconj : ∀ t, e (φ t) = successorAngle hG (e t) :=
    fun t ↦ e.apply_symm_apply _
  have hφc : Continuous φ :=
    e.symm.continuous.comp ((successorAngle_continuous hG).comp e.continuous)
  have hshift : ∀ j t, σ j (φ t) = σ (j + 1) t := by
    intro j t
    calc
      σ j (φ t) = criticalBoundaryTrace hG j (e (φ t)) := htrace j (φ t)
      _ = criticalBoundaryTrace hG j (successorAngle hG (e t)) := by rw [hconj]
      _ = criticalBoundaryTrace hG (j + 1) (e t) := criticalBoundaryTrace_successor hG j (e t)
      _ = σ (j + 1) t := (htrace (j + 1) t).symm
  have hregular := contDiff_pos_of_positive_curve_comp (hbal.2.1 0).1 (hbal.2.1 1).1
    (oct_det2_deriv_pos hbal 0) (oct_det2_deriv_pos hbal 1) hφc
    (fun t ↦ by simpa only [zero_add] using hshift 0 t)
  have hiter : ∀ n : ℕ, ∀ t, e (φ^[n] t) = (successorAngle hG)^[n] (e t) := by
    intro n
    induction n with
    | zero => intro t; simp
    | succ n ih =>
      intro t
      rw [Function.iterate_succ_apply', hconj, ih, Function.iterate_succ_apply']
  refine ⟨φ, hregular.1, hregular.2, hshift, ?_, ?_, ?_⟩
  · intro t
    apply e.injective
    rw [hiter, successorAngle_iterate_six, heperiod]
  · intro t
    apply e.injective
    calc
      e (φ (t + 6 * tf)) = successorAngle hG (e t + 2 * π) := by rw [hconj, heperiod]
      _ = successorAngle hG (e t) + 2 * π := successorAngle_add_two_pi hG (e t)
      _ = e (φ t + 6 * tf) := by rw [heperiod, hconj]
  · intro t
    apply e.strictMono.lt_iff_lt.1
    rw [hconj]
    exact (successorAngle_bounds hG (e t)).1

end SmoothedOctagon
