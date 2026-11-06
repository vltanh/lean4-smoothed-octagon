module

public import SmoothedOctagon.AdmissibleRegularity
public import SmoothedPolygons.Ch7.SmoothedPolygonDisk
public import Mathlib.MeasureTheory.Group.Measure

/-!
# Extending an actual admissible segment through the cyclic seams

An admissible frame on `[0,T]` is repeated by `G(t+T)=G(t)R`; its state is repeated
by `Y(t+T)=R⁻¹Y(t)R`. Six copies close because `R⁶=I`. The upstream piecewise
matrix construction and integral gluing prove regularity across every seam.
The state is globally Lipschitz, and the almost-everywhere contact curvature
inequality extends by translation invariance of Lebesgue measure.

Only the actual integral-form `IsReinhardtAdmissible` hypotheses are used. The
extension agrees with both original states throughout the closed segment and
preserves its exact cost. No simplicity or convex boundary is assumed here.
Source draft only: compilation and kernel validation have not been run.
-/

@[expose] public section

namespace SmoothedOctagon

open Set Filter MeasureTheory Real Matrix SmoothedPolygons
open scoped Topology

/-! ## Six copies of a matrix arc -/

private lemma cyclic_pw_add {A B : Mat2} {T : ℝ} {f : ℝ → Mat2}
    (hT : 0 < T) {t : ℝ} (ht : 0 ≤ t) :
    poly_pw A B T f (t + T) = A * poly_pw A B T f t * B := by
  have hfl : ⌊(t + T) / T⌋₊ = ⌊t / T⌋₊ + 1 := by
    rw [add_div, div_self hT.ne', Nat.floor_add_one (div_nonneg ht hT.le)]
  simp only [poly_pw, hfl]
  push_cast
  rw [show t + T - ((⌊t / T⌋₊ : ℝ) + 1) * T = t - ⌊t / T⌋₊ * T by ring,
    pow_succ' A, pow_succ B]
  simp only [Matrix.mul_assoc]

private lemma cyclic_pw_add_nat {A B : Mat2} {T : ℝ} {f : ℝ → Mat2}
    (hT : 0 < T) {t : ℝ} (ht : 0 ≤ t) (n : ℕ) :
    poly_pw A B T f (t + n * T) = A ^ n * poly_pw A B T f t * B ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [show t + ((n + 1 : ℕ) : ℝ) * T = (t + n * T) + T by push_cast; ring,
      cyclic_pw_add hT (add_nonneg ht (by positivity)), ih, pow_succ' A, pow_succ B]
    simp only [Matrix.mul_assoc]

private lemma cyclic_pw_full_period {A B : Mat2} {T : ℝ} {f : ℝ → Mat2}
    (hT : 0 < T) (hA : A ^ 6 = 1) (hB : B ^ 6 = 1) {t : ℝ} (ht : 0 ≤ t) :
    poly_pw A B T f (t + 6 * T) = poly_pw A B T f t := by
  simpa only [Nat.cast_ofNat, hA, hB, Matrix.one_mul, Matrix.mul_one] using
    cyclic_pw_add_nat (A := A) (B := B) (f := f) hT ht 6

/-- Repeat a matrix arc through six twisted copies, then extend periodically to `ℝ`. -/
noncomputable def cyclicMatrixExtension (A B : Mat2) (T : ℝ) (f : ℝ → Mat2)
    (t : ℝ) : Mat2 :=
  poly_pw A B T f (oct_red (6 * T) t)

theorem cyclicMatrixExtension_periodic {A B : Mat2} {T : ℝ} {f : ℝ → Mat2}
    (hT : 0 < T) : Function.Periodic (cyclicMatrixExtension A B T f) (6 * T) :=
  fun t ↦ by simp only [cyclicMatrixExtension, oct_red_add (by positivity : 0 < 6 * T)]

private lemma cyclicMatrixExtension_of_nonneg {A B : Mat2} {T : ℝ} {f : ℝ → Mat2}
    (hT : 0 < T) (hA : A ^ 6 = 1) (hB : B ^ 6 = 1) {t : ℝ} (ht : 0 ≤ t) :
    cyclicMatrixExtension A B T f t = poly_pw A B T f t :=
  oct_ext_eq (by positivity : 0 < 6 * T)
    (fun _ hs ↦ cyclic_pw_full_period hT hA hB hs) ht

theorem cyclicMatrixExtension_eqOn {A B : Mat2} {T : ℝ} {f : ℝ → Mat2}
    (hT : 0 < T) (hA : A ^ 6 = 1) (hB : B ^ 6 = 1)
    (hglue : f T = A * f 0 * B) :
    EqOn (cyclicMatrixExtension A B T f) f (Icc 0 T) := by
  intro t ht
  rw [cyclicMatrixExtension_of_nonneg hT hA hB ht.1]
  simpa only [Nat.cast_zero, zero_mul, sub_zero, pow_zero, Matrix.one_mul,
    Matrix.mul_one, Nat.cast_one, one_mul] using
    poly_pw_of_mem_Icc hT hglue (i := 0) (t := t) (by simpa using ht)

theorem cyclicMatrixExtension_shift {A B : Mat2} {T : ℝ} {f : ℝ → Mat2}
    (hT : 0 < T) (hA : A ^ 6 = 1) (hB : B ^ 6 = 1) (t : ℝ) :
    cyclicMatrixExtension A B T f (t + T) =
      A * cyclicMatrixExtension A B T f t * B := by
  obtain ⟨n, hn⟩ := oct_exists_int_add_pos (by positivity : 0 < 6 * T) t
  have hp := (cyclicMatrixExtension_periodic (A := A) (B := B) (f := f) hT).int_mul n
  rw [← hp t, ← hp (t + T), show t + T + n * (6 * T) = (t + n * (6 * T)) + T by ring,
    cyclicMatrixExtension_of_nonneg hT hA hB (by linarith),
    cyclicMatrixExtension_of_nonneg hT hA hB hn.le, cyclic_pw_add hT hn.le]

private lemma cyclic_pw_continuousAt_pos {A B : Mat2} {T : ℝ} {f : ℝ → Mat2}
    (hT : 0 < T) (hglue : f T = A * f 0 * B) (hf : ContinuousOn f (Icc 0 T))
    {t : ℝ} (ht : 0 < t) : ContinuousAt (poly_pw A B T f) t := by
  obtain ⟨N, hN⟩ := exists_nat_gt (t / T)
  have htN : t < (N : ℝ) * T := (div_lt_iff₀ hT).1 hN
  exact (poly_pw_continuousOn hT hglue hf N).continuousAt (Icc_mem_nhds ht htN)

private lemma cyclicMatrixExtension_eventuallyEq {A B : Mat2} {T : ℝ} {f : ℝ → Mat2}
    (hT : 0 < T) (hA : A ^ 6 = 1) (hB : B ^ 6 = 1) {t : ℝ} (ht : 0 < t) :
    cyclicMatrixExtension A B T f =ᶠ[𝓝 t] poly_pw A B T f :=
  Filter.eventually_of_mem (Ioi_mem_nhds ht) fun _ hs ↦
    cyclicMatrixExtension_of_nonneg hT hA hB hs.le

theorem cyclicMatrixExtension_continuous {A B : Mat2} {T : ℝ} {f : ℝ → Mat2}
    (hT : 0 < T) (hA : A ^ 6 = 1) (hB : B ^ 6 = 1)
    (hglue : f T = A * f 0 * B) (hf : ContinuousOn f (Icc 0 T)) :
    Continuous (cyclicMatrixExtension A B T f) := by
  refine continuous_iff_continuousAt.2 fun t ↦ ?_
  obtain ⟨n, hn⟩ := oct_exists_int_add_pos (by positivity : 0 < 6 * T) t
  have hp := (cyclicMatrixExtension_periodic (A := A) (B := B) (f := f) hT).int_mul n
  have hc : ContinuousAt (cyclicMatrixExtension A B T f) (t + n * (6 * T)) :=
    (cyclic_pw_continuousAt_pos hT hglue hf hn).congr
      (cyclicMatrixExtension_eventuallyEq hT hA hB hn).symm
  have hcomp : ContinuousAt (fun x ↦ cyclicMatrixExtension A B T f (x + n * (6 * T))) t :=
    hc.comp (by fun_prop)
  rwa [show (fun x ↦ cyclicMatrixExtension A B T f (x + n * (6 * T))) =
    cyclicMatrixExtension A B T f from funext hp] at hcomp

/-- Matching values and a continuous matching derivative give a global derivative,
including the seams. The proof uses the integral equation on arbitrarily many copies. -/
theorem cyclicMatrixExtension_hasDerivAt {A B : Mat2} {T : ℝ} {f v : ℝ → Mat2}
    (hT : 0 < T) (hA : A ^ 6 = 1) (hB : B ^ 6 = 1)
    (hglue : f T = A * f 0 * B) (hvglue : v T = A * v 0 * B)
    (hf : ContinuousOn f (Icc 0 T)) (hv : ContinuousOn v (Icc 0 T))
    (hd : ∀ t ∈ Ioo 0 T, HasDerivAtEntrywise f (v t) t) (t : ℝ) :
    HasDerivAtEntrywise (cyclicMatrixExtension A B T f)
      (cyclicMatrixExtension A B T v t) t := by
  have hpositive : ∀ s, 0 < s → HasDerivAtEntrywise (cyclicMatrixExtension A B T f)
      (cyclicMatrixExtension A B T v s) s := by
    intro s hs
    obtain ⟨N, hN⟩ := exists_nat_gt (s / T)
    have hsN : s < (N : ℝ) * T := (div_lt_iff₀ hT).1 hN
    have hI : IsIntegralCurve (poly_pw A B T f) (poly_pw A B T v) (N * T) :=
      poly_pw_isIntegralCurve hT hglue hf hv hd N
        (fun i _ u hu ↦ poly_pw_of_mem_Ico hT hu)
    have hc := cyclic_pw_continuousAt_pos hT hvglue hv hs
    rw [cyclicMatrixExtension_of_nonneg hT hA hB hs.le]
    exact (Matrix.hasDerivAtEntrywise_of_eq_add_integral hI ⟨hs, hsN⟩ hc)
      .congr_of_eventuallyEq (cyclicMatrixExtension_eventuallyEq hT hA hB hs)
  obtain ⟨n, hn⟩ := oct_exists_int_add_pos (by positivity : 0 < 6 * T) t
  have hpf := (cyclicMatrixExtension_periodic (A := A) (B := B) (f := f) hT).int_mul n
  have hpv := (cyclicMatrixExtension_periodic (A := A) (B := B) (f := v) hT).int_mul n
  have hcomp := (hpositive _ hn).scomp ((hasDerivAt_id' t).add_const (n * (6 * T)))
  rw [one_smul, hpv, show (fun x ↦ cyclicMatrixExtension A B T f (x + n * (6 * T))) =
    cyclicMatrixExtension A B T f from funext hpf] at hcomp
  exact hcomp

/-! ## Lipschitz regularity through finitely many seams -/

private lemma cyclic_lipschitzOn_const_mul {f : ℝ → ℝ} {s : Set ℝ} {C : ℝ≥0}
    (hf : LipschitzOnWith C f s) (c : ℝ) :
    ∃ D, LipschitzOnWith D (fun t ↦ c * f t) s := by
  refine ⟨_, LipschitzOnWith.of_dist_le' (K := |c| * (C : ℝ)) fun x hx y hy ↦ ?_⟩
  have hxy := hf.dist_le_mul x hx y hy
  simp only [Real.dist_eq] at hxy ⊢
  calc
    |c * f x - c * f y| = |c| * |f x - f y| := by rw [← mul_sub, abs_mul]
    _ ≤ |c| * ((C : ℝ) * |x - y|) :=
      mul_le_mul_of_nonneg_left hxy (abs_nonneg c)
    _ = (|c| * (C : ℝ)) * |x - y| := by ring

private lemma cyclic_lipschitzOnEntrywise_const_mul {f : ℝ → Mat2} {s : Set ℝ}
    (hf : LipschitzOnEntrywise f s) (A : Mat2) :
    LipschitzOnEntrywise (fun t ↦ A * f t) s := by
  intro i j
  obtain ⟨C0, h0⟩ := hf 0 j
  obtain ⟨C1, h1⟩ := hf 1 j
  obtain ⟨D0, hD0⟩ := cyclic_lipschitzOn_const_mul h0 (A i 0)
  obtain ⟨D1, hD1⟩ := cyclic_lipschitzOn_const_mul h1 (A i 1)
  exact ⟨D0 + D1, by simpa only [Matrix.mul_apply, Fin.sum_univ_two] using hD0.add hD1⟩

private lemma cyclic_lipschitzOnEntrywise_mul_const {f : ℝ → Mat2} {s : Set ℝ}
    (hf : LipschitzOnEntrywise f s) (A : Mat2) :
    LipschitzOnEntrywise (fun t ↦ f t * A) s := by
  intro i j
  obtain ⟨C0, h0⟩ := hf i 0
  obtain ⟨C1, h1⟩ := hf i 1
  obtain ⟨D0, hD0⟩ := cyclic_lipschitzOn_const_mul h0 (A 0 j)
  obtain ⟨D1, hD1⟩ := cyclic_lipschitzOn_const_mul h1 (A 1 j)
  exact ⟨D0 + D1, by
    simpa only [Matrix.mul_apply, Fin.sum_univ_two, mul_comm] using hD0.add hD1⟩

private lemma cyclic_lipschitzOn_Icc_union {f : ℝ → ℝ} {a b c : ℝ}
    (hab : a ≤ b) (hbc : b ≤ c)
    (hf : ∃ C, LipschitzOnWith C f (Icc a b))
    (hh : ∃ C, LipschitzOnWith C f (Icc b c)) :
    ∃ C, LipschitzOnWith C f (Icc a c) := by
  obtain ⟨C, hC⟩ := hf
  obtain ⟨D, hD⟩ := hh
  have hCle : (C : ℝ) ≤ ((C + D : ℝ≥0) : ℝ) := by
    simp only [NNReal.coe_add]
    exact le_add_of_nonneg_right D.coe_nonneg
  have hDle : (D : ℝ) ≤ ((C + D : ℝ≥0) : ℝ) := by
    simp only [NNReal.coe_add]
    exact le_add_of_nonneg_left C.coe_nonneg
  have hleft : ∀ x ∈ Icc a b, ∀ y ∈ Icc a b,
      dist (f x) (f y) ≤ ((C + D : ℝ≥0) : ℝ) * dist x y :=
    fun x hx y hy ↦ (hC.dist_le_mul x hx y hy).trans
      (mul_le_mul_of_nonneg_right hCle dist_nonneg)
  have hright : ∀ x ∈ Icc b c, ∀ y ∈ Icc b c,
      dist (f x) (f y) ≤ ((C + D : ℝ≥0) : ℝ) * dist x y :=
    fun x hx y hy ↦ (hD.dist_le_mul x hx y hy).trans
      (mul_le_mul_of_nonneg_right hDle dist_nonneg)
  have hordered : ∀ x ∈ Icc a c, ∀ y ∈ Icc a c, x ≤ y →
      dist (f x) (f y) ≤ ((C + D : ℝ≥0) : ℝ) * dist x y := by
    intro x hx y hy hxy
    by_cases hyb : y ≤ b
    · exact hleft x ⟨hx.1, hxy.trans hyb⟩ y ⟨hy.1, hyb⟩
    by_cases hbx : b ≤ x
    · exact hright x ⟨hbx, hx.2⟩ y ⟨hbx.trans hxy, hy.2⟩
    have hxb : x ≤ b := (lt_of_not_ge hbx).le
    have hby : b ≤ y := (lt_of_not_ge hyb).le
    calc
      dist (f x) (f y) ≤ dist (f x) (f b) + dist (f b) (f y) := dist_triangle _ _ _
      _ ≤ ((C + D : ℝ≥0) : ℝ) * dist x b + ((C + D : ℝ≥0) : ℝ) * dist b y :=
        add_le_add (hleft x ⟨hx.1, hxb⟩ b ⟨hab, le_rfl⟩)
          (hright b ⟨le_rfl, hbc⟩ y ⟨hby, hy.2⟩)
      _ = ((C + D : ℝ≥0) : ℝ) * dist x y := by
        simp only [Real.dist_eq, abs_of_nonpos (sub_nonpos.mpr hxb),
          abs_of_nonpos (sub_nonpos.mpr hby), abs_of_nonpos (sub_nonpos.mpr hxy)]
        ring
  refine ⟨C + D, LipschitzOnWith.of_dist_le_mul fun x hx y hy ↦ ?_⟩
  rcases le_total x y with hxy | hyx
  · exact hordered x hx y hy hxy
  · rw [dist_comm, dist_comm x]
    exact hordered y hy x hx hyx

private lemma cyclic_pw_lipschitzOn {A B : Mat2} {T : ℝ} {f : ℝ → Mat2}
    (hT : 0 < T) (hglue : f T = A * f 0 * B)
    (hf : LipschitzOnEntrywise f (Icc 0 T)) (N : ℕ) :
    LipschitzOnEntrywise (poly_pw A B T f) (Icc 0 (N * T)) := by
  induction N with
  | zero =>
    intro i j
    refine ⟨0, LipschitzOnWith.of_dist_le_mul fun x hx y hy ↦ ?_⟩
    have hx0 : x = 0 := by
      have hx' : 0 ≤ x ∧ x ≤ 0 := by simpa only [Nat.cast_zero, zero_mul, mem_Icc] using hx
      exact le_antisymm hx'.2 hx'.1
    have hy0 : y = 0 := by
      have hy' : 0 ≤ y ∧ y ≤ 0 := by simpa only [Nat.cast_zero, zero_mul, mem_Icc] using hy
      exact le_antisymm hy'.2 hy'.1
    simp [hx0, hy0]
  | succ n ih =>
    have hbase : LipschitzOnEntrywise (fun t ↦ f (t - n * T))
        (Icc ((n : ℝ) * T) (((n : ℝ) + 1) * T)) := by
      intro i j
      obtain ⟨C, hC⟩ := hf i j
      refine ⟨C, LipschitzOnWith.of_dist_le_mul fun x hx y hy ↦ ?_⟩
      have hx0 : x - n * T ∈ Icc 0 T := ⟨by linarith [hx.1], by linarith [hx.2]⟩
      have hy0 : y - n * T ∈ Icc 0 T := ⟨by linarith [hy.1], by linarith [hy.2]⟩
      have hb := hC.dist_le_mul _ hx0 _ hy0
      simpa only [Real.dist_eq, show x - n * T - (y - n * T) = x - y by ring] using hb
    have hpiece := cyclic_lipschitzOnEntrywise_mul_const
      (cyclic_lipschitzOnEntrywise_const_mul hbase (A ^ n)) (B ^ n)
    have hpw : LipschitzOnEntrywise (poly_pw A B T f)
        (Icc ((n : ℝ) * T) (((n : ℝ) + 1) * T)) := by
      intro i j
      obtain ⟨C, hC⟩ := hpiece i j
      refine ⟨C, LipschitzOnWith.of_dist_le_mul fun x hx y hy ↦ ?_⟩
      rw [poly_pw_of_mem_Icc hT hglue (i := n)
        (by simpa only [Nat.cast_add, Nat.cast_one] using hx),
        poly_pw_of_mem_Icc hT hglue (i := n)
        (by simpa only [Nat.cast_add, Nat.cast_one] using hy)]
      exact hC.dist_le_mul x hx y hy
    intro i j
    simpa only [Nat.cast_succ, Nat.cast_add, Nat.cast_one] using
      cyclic_lipschitzOn_Icc_union (f := fun t ↦ poly_pw A B T f t i j)
        (by positivity : 0 ≤ (n : ℝ) * T) (by nlinarith : (n : ℝ) * T ≤ ((n : ℝ) + 1) * T)
        (ih i j) (hpw i j)

theorem cyclicMatrixExtension_lipschitz {A B : Mat2} {T : ℝ} {f : ℝ → Mat2}
    (hT : 0 < T) (hA : A ^ 6 = 1) (hB : B ^ 6 = 1)
    (hglue : f T = A * f 0 * B) (hf : LipschitzOnEntrywise f (Icc 0 T)) :
    LipschitzOnEntrywise (cyclicMatrixExtension A B T f) univ := by
  have hlocal := cyclic_pw_lipschitzOn hT hglue hf 12
  have hext : LipschitzOnEntrywise (cyclicMatrixExtension A B T f) (Icc 0 (2 * (6 * T))) := by
    intro i j
    obtain ⟨C, hC⟩ := hlocal i j
    refine ⟨C, LipschitzOnWith.of_dist_le_mul fun x hx y hy ↦ ?_⟩
    rw [cyclicMatrixExtension_of_nonneg hT hA hB hx.1,
      cyclicMatrixExtension_of_nonneg hT hA hB hy.1]
    exact hC.dist_le_mul x ⟨hx.1, by nlinarith [hx.2]⟩
      y ⟨hy.1, by nlinarith [hy.2]⟩
  exact lipschitzOnEntrywise_univ_of_periodic (by positivity : 0 < 6 * T)
    (cyclicMatrixExtension_periodic hT) hext

/-! ## Almost-everywhere transport through the cyclic joins -/

/-- A periodic property holding almost everywhere on one open period holds almost
everywhere on the line. Only the countable seam grid is discarded. -/
theorem ae_of_periodic_ae_on_Ioo {p : ℝ → Prop} {T : ℝ} (hT : 0 < T)
    (hp : Function.Periodic p T) (hae : ∀ᵐ t, t ∈ Ioo 0 T → p t) :
    ∀ᵐ t, p t := by
  have htrans : ∀ n : ℤ, ∀ᵐ t, t - (n : ℝ) * T ∈ Ioo 0 T → p (t - (n : ℝ) * T) := by
    intro n
    have h := (measurePreserving_add_right (volume : Measure ℝ) (-((n : ℝ) * T)))
      .quasiMeasurePreserving.ae hae
    simpa only [sub_eq_add_neg] using h
  have hgrid : ∀ᵐ t ∂volume, t ∉ range (fun n : ℤ ↦ (n : ℝ) * T) :=
    (countable_range _).ae_notMem volume
  filter_upwards [ae_all_iff.2 htrans, hgrid] with t ht hnot
  have hred := oct_red_mem hT t
  have hne : oct_red T t ≠ 0 := by
    intro hz
    apply hnot
    refine ⟨⌊t / T⌋, ?_⟩
    dsimp [oct_red] at hz
    linarith
  have hpos : 0 < oct_red T t := lt_of_le_of_ne hred.1 (Ne.symm hne)
  have hlocal : p (oct_red T t) := ht ⌊t / T⌋ ⟨hpos, hred.2⟩
  have heq : p (oct_red T t) = p t := hp.sub_int_mul_eq ⌊t / T⌋
  exact heq ▸ hlocal

/-- All six curvature inequalities form a periodic property under a cyclic contact
shift, including the totalized derivatives at exceptional points. -/
theorem contactCurvature_ae_of_cyclic_shift {σ : ZMod 6 → ℝ → Fin 2 → ℝ} {T : ℝ}
    (hT : 0 < T) (hshift : ∀ j t, σ j (t + T) = σ (j + 1) t)
    (hae : ∀ᵐ t, t ∈ Ioo 0 T → ∀ j,
      0 ≤ det2 (deriv (σ j) t) (deriv (deriv (σ j)) t)) :
    ∀ᵐ t, ∀ j, 0 ≤ det2 (deriv (σ j) t) (deriv (deriv (σ j)) t) := by
  have hfirst : ∀ j t, deriv (σ j) (t + T) = deriv (σ (j + 1)) t := by
    intro j t
    rw [← deriv_comp_add_const]
    congr 1
    funext s
    exact hshift j s
  have hsecond : ∀ j t, deriv (deriv (σ j)) (t + T) = deriv (deriv (σ (j + 1))) t := by
    intro j t
    rw [← deriv_comp_add_const]
    congr 1
    funext s
    exact hfirst j s
  let p : ℝ → Prop := fun t ↦ ∀ j,
    0 ≤ det2 (deriv (σ j) t) (deriv (deriv (σ j)) t)
  have hp : Function.Periodic p T := by
    intro t
    apply propext
    constructor
    · intro ht j
      simpa only [hfirst, hsecond, sub_add_cancel] using ht (j - 1)
    · intro ht j
      rw [hfirst, hsecond]
      exact ht (j + 1)
  exact ae_of_periodic_ae_on_Ioo hT hp hae

/-! ## The actual admissible frame and state -/

noncomputable def cyclicFrameExtension (T : ℝ) (g : ℝ → Mat2) : ℝ → Mat2 :=
  cyclicMatrixExtension 1 R T g

noncomputable def cyclicStateExtension (T : ℝ) (X : ℝ → Mat2) : ℝ → Mat2 :=
  cyclicMatrixExtension R⁻¹ R T X

private lemma cyclic_extension_velocity (T : ℝ) (g X : ℝ → Mat2) (t : ℝ) :
    cyclicMatrixExtension 1 R T (fun s ↦ g s * X s) t =
      cyclicFrameExtension T g t * cyclicStateExtension T X t := by
  let s := oct_red (6 * T) t
  let n := ⌊s / T⌋₊
  let r := s - n * T
  change 1 ^ n * (g r * X r) * R ^ n =
    (1 ^ n * g r * R ^ n) * (R⁻¹ ^ n * X r * R ^ n)
  simpa only [one_pow, Matrix.one_mul] using (poly_mul_conj (1 : Mat2) (g r) (X r) n).symm

/-- Extend every actual admissible segment to global cyclic geometry. The extension
agrees on the closed original segment, preserves cost, and constructs all analytic
regularity and curvature conditions used by the subsequent geometric reconstruction. -/
theorem exists_cyclic_extension_of_isReinhardtAdmissible
    {T : ℝ} {u : ℝ → Fin 3 → ℝ} {g X : ℝ → Mat2}
    (h : IsReinhardtAdmissible T u g X) :
    ∃ G Y : ℝ → Mat2,
      (∀ t ∈ Icc 0 T, G t = g t ∧ Y t = X t) ∧
      (∀ i j, ContDiff ℝ 1 (fun t ↦ G t i j)) ∧
      Continuous Y ∧ LipschitzOnEntrywise Y univ ∧
      (∀ t, (G t).det = 1) ∧ (∀ t, IsStarState (Y t)) ∧
      (∀ t, HasDerivAtEntrywise G (G t * Y t) t) ∧
      G 0 = 1 ∧ (∀ t, G (t + T) = G t * R) ∧
      (∀ t, Y (t + T) = R⁻¹ * Y t * R) ∧ Function.Periodic G (6 * T) ∧
      (∀ᵐ t, ∀ j : ZMod 6,
        0 ≤ det2 (deriv (fun s ↦ G s *ᵥ sixthRoot j) t)
          (deriv (deriv (fun s ↦ G s *ᵥ sixthRoot j)) t)) ∧
      reinhardtCost T Y = reinhardtCost T X := by
  have htraj := h.1
  have hT : 0 < T := htraj.1
  have hg0 : g 0 = 1 := h.2.1
  have hgT : g T = R := h.2.2.1
  have hXT : X T = R⁻¹ * X 0 * R := h.2.2.2
  obtain ⟨hgc, hXc⟩ := stateTrajectory_continuous htraj
  have hgglue : g T = (1 : Mat2) * g 0 * R := by rw [hgT, hg0]; simp
  have hvglue : g T * X T = (1 : Mat2) * (g 0 * X 0) * R := by
    rw [hgT, hXT, hg0]
    simp only [← Matrix.mul_assoc, poly_R_mul_inv, Matrix.one_mul]
  let G := cyclicFrameExtension T g
  let Y := cyclicStateExtension T X
  have hagree : ∀ t ∈ Icc 0 T, G t = g t ∧ Y t = X t := by
    intro t ht
    exact ⟨cyclicMatrixExtension_eqOn hT (by simp) oct_R_pow_six hgglue ht,
      cyclicMatrixExtension_eqOn hT oct_Rinv_pow_six oct_R_pow_six hXT ht⟩
  have hGcont : Continuous G :=
    cyclicMatrixExtension_continuous hT (by simp) oct_R_pow_six hgglue hgc
  have hYcont : Continuous Y :=
    cyclicMatrixExtension_continuous hT oct_Rinv_pow_six oct_R_pow_six hXT hXc
  have hYlip : LipschitzOnEntrywise Y univ :=
    cyclicMatrixExtension_lipschitz hT oct_Rinv_pow_six oct_R_pow_six hXT
      (stateTrajectory_state_lipschitz htraj)
  have hD : ∀ t, HasDerivAtEntrywise G (G t * Y t) t := by
    intro t
    have hd := cyclicMatrixExtension_hasDerivAt hT (by simp) oct_R_pow_six hgglue hvglue
      hgc (hgc.mul hXc) (stateTrajectory_frame_hasDerivAt htraj) t
    simpa only [cyclic_extension_velocity] using hd
  have hC1 : ∀ i j, ContDiff ℝ 1 (fun t ↦ G t i j) := by
    intro i j
    refine contDiff_one_iff_deriv.2 ⟨fun t ↦ (hD t i j).differentiableAt, ?_⟩
    have hd : deriv (fun t ↦ G t i j) = fun t ↦ (G t * Y t) i j :=
      funext fun t ↦ (hD t i j).deriv
    rw [hd]
    exact Matrix.continuous_iff_entrywise.1 (hGcont.mul hYcont) i j
  have hstate : ∀ t, (G t).det = 1 ∧ IsStarState (Y t) := by
    intro t
    let s := oct_red (6 * T) t
    let n := ⌊s / T⌋₊
    let r := s - n * T
    have hs : 0 ≤ s := (oct_red_mem (by positivity : 0 < 6 * T) t).1
    have hfl := poly_floor_mem hT hs
    have hr : r ∈ Icc 0 T := ⟨by dsimp [r, n]; linarith [hfl.1],
      by dsimp [r, n]; linarith [hfl.2]⟩
    have hbase := htraj.2.2.2.1 r hr
    constructor
    · change (1 ^ n * g r * R ^ n).det = 1
      simp only [one_pow, Matrix.one_mul, Matrix.det_mul, Matrix.det_pow,
        poly_det_R, one_pow, mul_one]
      exact hbase.1
    · change IsStarState (R⁻¹ ^ n * X r * R ^ n)
      exact poly_isStarState_conj_pow n hbase.2
  have hG0 : G 0 = 1 := (hagree 0 ⟨le_rfl, hT.le⟩).1.trans hg0
  have hGshift : ∀ t, G (t + T) = G t * R := by
    intro t
    simpa only [Matrix.one_mul] using
      cyclicMatrixExtension_shift (f := g) hT (by simp : (1 : Mat2) ^ 6 = 1) oct_R_pow_six t
  have hYshift : ∀ t, Y (t + T) = R⁻¹ * Y t * R :=
    cyclicMatrixExtension_shift hT oct_Rinv_pow_six oct_R_pow_six
  have hGperiod : Function.Periodic G (6 * T) := cyclicMatrixExtension_periodic hT
  have hcontact : ∀ j t,
      G (t + T) *ᵥ sixthRoot j = G t *ᵥ sixthRoot (j + 1) := by
    intro j t
    rw [hGshift, ← Matrix.mulVec_mulVec, oct_R_mulVec_sixthRoot]
  have hcurvlocal : ∀ᵐ t, t ∈ Ioo 0 T → ∀ j : ZMod 6,
      0 ≤ det2 (deriv (fun s ↦ G s *ᵥ sixthRoot j) t)
        (deriv (deriv (fun s ↦ G s *ᵥ sixthRoot j)) t) := by
    filter_upwards [stateTrajectory_contactCurvature_nonneg htraj] with t ht hti j
    have heq : (fun s ↦ G s *ᵥ sixthRoot j) =ᶠ[𝓝 t]
        fun s ↦ g s *ᵥ sixthRoot j :=
      Filter.eventually_of_mem (Ioo_mem_nhds hti.1 hti.2) fun s hs ↦
        congrArg (fun M : Mat2 ↦ M *ᵥ sixthRoot j) (hagree s (Ioo_subset_Icc_self hs)).1
    rw [heq.deriv_eq, heq.deriv.deriv_eq]
    exact ht hti j
  have hcurv := contactCurvature_ae_of_cyclic_shift hT hcontact hcurvlocal
  have hcost : reinhardtCost T Y = reinhardtCost T X := by
    unfold reinhardtCost
    congr 1
    apply intervalIntegral.integral_congr
    intro t ht
    rw [uIcc_of_le hT.le] at ht
    rw [(hagree t ht).2]
  exact ⟨G, Y, hagree, hC1, hYcont, hYlip, fun t ↦ (hstate t).1,
    fun t ↦ (hstate t).2, hD, hG0, hGshift, hYshift, hGperiod, hcurv, hcost⟩

end SmoothedOctagon
