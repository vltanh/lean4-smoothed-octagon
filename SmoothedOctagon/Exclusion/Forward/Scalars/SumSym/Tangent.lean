module

public import SmoothedOctagon.Exclusion.Forward.Scalars.SumSym.Integrals
public import SmoothedOctagon.Exclusion.Forward.Scalars.SumSym.Constant
public import SmoothedOctagon.Exclusion.Forward.Reduce

/-!
# The original row and the fixed forward sum tangent

The original row at norm-sum threshold `1/32` is bounded by an affine
function of the factor. The physical factor interval has two explicit ceilings.
-/

@[expose] public section

namespace SmoothedOctagon
open Set Real MeasureTheory

/-- Compact left-row quantities from the paper, retaining the threshold 1/32. -/
noncomputable def fwdSumAR (a k : ℝ) : ℝ :=
  1+2*((1+a)/(1-a))-(1-a)+(1-a)^2/(4*(1-a-k))
noncomputable def fwdSumB1 (a k : ℝ) : ℝ :=
  (2*(1-k)-(1+a)+(1+a)^2/(2*(1-k)))/(1-a)
noncomputable def fwdSumN1 (a k : ℝ) : ℝ :=
  2*(1-a-2*k)/((1-a)^2*(1-k))
noncomputable def fwdSumNd (a k : ℝ) : ℝ :=
  2*(a+k)*(2-a-k)/((1-a)*(1-k))
noncomputable def fwdSumFR (a k : ℝ) : ℝ := 1+(1+a)^2/(4*(1-k))
noncomputable def fwdSumR0 (a k : ℝ) : ℝ :=
  a*(a+k)*((1+a)^2+4*k-4)/(2*(1-a)*(1-k)^2)
noncomputable def fwdSumR1 (a k : ℝ) : ℝ :=
  2*((1-a-k)/(1-k))/(1-a)*fwdSumAR a k-fwdSumB1 a k-
    (49/32)*fwdSumN1 a k-fwdSumNd a k*fwdSumFR a k

/-- Continuously extended constant coefficient in normalized integral coordinates. -/
noncomputable def fwdSumA0Integral (a k : ℝ) : ℝ :=
  fwdSumR0 a k+a*(1-a-k)*(a+k)/((1-a)*(1-k))*
    (2*fwdSumEll k-(1-a)*fwdSumJ a k)
/-- Linear coefficient of the threshold-1/32 sum row, before pairing its two logarithms. -/
noncomputable def fwdSumA1Row (a k : ℝ) : ℝ :=
  fwdSumR1 a k+((1-a)*(a+k)^2+2*a)/((1-a)*(1-k))*fwdSumEll k+
    2*((1-a-k)/(1-k))/(1-a)*log ((1-a-k)/(1-k))

/-- The integral expression for the constant coefficient when `k > 0`. -/
theorem fwdSumA0Integral_eq_original {a k : ℝ}
    (ha : 0 ≤ a) (ha1 : a ≤ 1/7) (hk : 0 < k) (hk1 : k ≤ 1/5) :
    fwdSumA0Integral a k =
      fs_SA0 a (k/(1-k)) (log (1+k/(1-k))) (log (1-a*(1+k/(1-k)))) := by
  rw [fwdSum_log_one_add hk.le (by linarith),
    fwdSum_log_one_sub ha hk.le (by linarith)]
  unfold fwdSumA0Integral fwdSumR0 fs_SA0
  have hb : 1-a ≠ 0 := ne_of_gt (by linarith : 0 < 1-a)
  have hr : 1-k ≠ 0 := ne_of_gt (by linarith : 0 < 1-k)
  field_simp [hb,hr,ne_of_gt hk]
  ring

/-- Pairing the row's two logarithms into one reciprocal integral. -/
theorem fwdSumA1Row_pair {a k : ℝ}
    (ha : 0 ≤ a) (ha1 : a ≤ 1/7) (hk : 0 ≤ k) (hk1 : k ≤ 1/5) :
    fwdSumA1Row a k = fwdSumR1 a k+fwdSumPairedLog a k 0 := by
  have hlog : log ((1-a-k)/(1-k)) =
      -a*fwdSumEll k-a*(a+k)*fwdSumJ a k := by
    rw [show 1-a-k = 1-(a+k) by ring]
    exact fwdSum_log_ratio ha hk (by linarith)
  unfold fwdSumA1Row fwdSumPairedLog
  rw [hlog]
  have hb : 1-a ≠ 0 := ne_of_gt (by linarith : 0 < 1-a)
  have hr : 1-k ≠ 0 := ne_of_gt (by linarith : 0 < 1-k)
  field_simp [hb,hr]
  ring

/-- The compact rational upper bound U of the paper's supporting tangent. -/
noncomputable def fwdSumUpper (a k τ : ℝ) : ℝ :=
  fwdSumR1 a k+(9-25*τ)*fwdSumR0 a k+
    ((1+a)/(1-a))*(((a+k)/(2*(1-k))-19/243)*τ+2/243)+
    fwdSumPairedLogUpper a k (9-25*τ)

/-- Exact decomposition of W into its rational row and its paired integral term. -/
theorem fwdSumFixedTangent_pair {a k τ : ℝ}
    (ha : 0 ≤ a) (ha1 : a ≤ 1/7) (hk : 0 ≤ k) (hk1 : k ≤ 1/5) :
    fwdSumFixedTangent (fwdSumA0Integral a k) (fwdSumA1Row a k)
        ((a+k)/(1-k)) ((1+a)/(1-a)) τ =
      fwdSumR1 a k+(9-25*τ)*fwdSumR0 a k+
        ((1+a)/(1-a))*(((a+k)/(2*(1-k))-19/243)*τ+2/243)+
        fwdSumPairedLog a k (9-25*τ) := by
  rw [fwdSumA1Row_pair ha ha1 hk hk1]
  unfold fwdSumFixedTangent fwdSumA0Integral fwdSumPairedLog
  have hb : 1-a ≠ 0 := ne_of_gt (by linarith : 0 < 1-a)
  have hr : 1-k ≠ 0 := ne_of_gt (by linarith : 0 < 1-k)
  field_simp [hb,hr]
  ring

/-- The complete fixed supporting tangent is bounded above by U on the closed shape rectangle. -/
theorem fwdSumFixedTangent_le_upper {a k τ : ℝ}
    (ha : 0 ≤ a) (ha1 : a ≤ 1/7) (hk : 0 ≤ k) (hk1 : k ≤ 1/5) (hτ : τ ≤ 2/5) :
    fwdSumFixedTangent (fwdSumA0Integral a k) (fwdSumA1Row a k)
        ((a+k)/(1-k)) ((1+a)/(1-a)) τ ≤ fwdSumUpper a k τ := by
  rw [fwdSumFixedTangent_pair ha ha1 hk hk1]
  have hp := fwdSumPairedLog_le_tangent ha ha1 hk hk1 hτ
  unfold fwdSumUpper
  linarith only [hp]

/-- Affinity in the factor is an identity of the original unexpanded rational row. -/
theorem fwdSumUpper_affine (a k x y θ : ℝ) :
    fwdSumUpper a k ((1-θ)*x+θ*y) =
      (1-θ)*fwdSumUpper a k x+θ*fwdSumUpper a k y := by
  unfold fwdSumUpper fwdSumPairedLogUpper
  ring

/-- Exact original sum residual with the paper's strengthened norm threshold. -/
noncomputable def fwdSumResidual32 (U z h : ℝ) : ℝ :=
  ff_r U z z h-ff_n U z h/32-
    (ff_m U z z h-ff_n U z h)*ff_L z ((1+z)^2/(z^2+U))
noncomputable def fwdSumShapeZ (a : ℝ) : ℝ := (1+a)/(1-a)
noncomputable def fwdSumShapeU (a k : ℝ) : ℝ :=
  (4*(1-k)-(1+a)^2)/(1-a)^2

private theorem fs_shape_pos {a k : ℝ}
    (ha : 0 ≤ a) (ha1 : a ≤ 1/7) (hk1 : k ≤ 1/5) :
    0 < fwdSumShapeZ a ∧ 0 < fwdSumShapeU a k := by
  have hb : 0 < 1-a := by linarith
  have ha2 : (1+a)^2 ≤ (8/7:ℝ)^2 := by nlinarith only [ha,ha1]
  constructor
  · unfold fwdSumShapeZ; positivity
  · unfold fwdSumShapeU
    exact div_pos (by linarith) (sq_pos_of_pos hb)


private theorem fs_shape_dictionary {a k : ℝ}
    (_ha : 0 ≤ a) (ha1 : a ≤ 1/7) (_hk1 : k ≤ 1/5) :
    1+fwdSumShapeZ a = 2/(1-a) ∧
    (fwdSumShapeZ a)^2+fwdSumShapeU a k = 4*(1-k)/(1-a)^2 ∧
    1+fwdSumShapeU a k = 4*(1-a-k)/(1-a)^2 := by
  have hb : 1-a ≠ 0 := ne_of_gt (by linarith : 0 < 1-a)
  unfold fwdSumShapeZ fwdSumShapeU
  constructor
  · field_simp; ring
  constructor <;> field_simp <;> ring

private theorem fs_shape_alpha {a k h : ℝ}
    (ha : 0 ≤ a) (ha1 : a ≤ 1/7) (hk1 : k ≤ 1/5) :
    ff_alpha (fwdSumShapeU a k) (fwdSumShapeZ a) h =
      (1-a-k)/(1-k)+2*(1-a-k)/((1-a)*(1-k))*(h-1) := by
  obtain ⟨hS,hZ,hK⟩ := fs_shape_dictionary ha ha1 hk1
  unfold ff_alpha
  rw [hK,hZ,hS]
  unfold fwdSumShapeZ
  have hb : 1-a ≠ 0 := ne_of_gt (by linarith : 0 < 1-a)
  have hr : 1-k ≠ 0 := ne_of_gt (by linarith : 0 < 1-k)
  field_simp [hb,hr]
  ring

private theorem fs_shape_A {a k : ℝ}
    (ha : 0 ≤ a) (ha1 : a ≤ 1/7) (hk1 : k ≤ 1/5) :
    ff_A (fwdSumShapeU a k) (fwdSumShapeZ a) (fwdSumShapeZ a) =
      fwdSumAR a k+log ((1-a-k)/(1-k))-log (1+k/(1-k)) := by
  obtain ⟨hS,hZ,hK⟩ := fs_shape_dictionary ha ha1 hk1
  have hb : 1-a ≠ 0 := ne_of_gt (by linarith : 0 < 1-a)
  have hr : 1-k ≠ 0 := ne_of_gt (by linarith : 0 < 1-k)
  have hc : 1-a-k ≠ 0 := ne_of_gt (by linarith : 0 < 1-a-k)
  have hq : ff_q (fwdSumShapeU a k) (fwdSumShapeZ a) (fwdSumShapeZ a) =
      (1+k/(1-k))/((1-a-k)/(1-k)) := by
    unfold ff_q
    rw [hS,hK]
    field_simp [hb,hr,hc]
    ring
  have hIpos : 0 < 1+k/(1-k) := by
    rw [show 1+k/(1-k) = 1/(1-k) by field_simp; ring]
    exact one_div_pos.mpr (by linarith)
  unfold ff_A
  rw [hq,log_div (ne_of_gt hIpos) (div_ne_zero hc hr),hS,hK]
  unfold fwdSumAR fwdSumShapeZ
  field_simp [hb,hr,hc]
  ring

noncomputable def fwdSumB0 (a k : ℝ) : ℝ :=
  2*(1-k)/(1-a)+1-(1+a)^2/(2*(1-a)*(1-k))-
    (1+a)^2/(2*(1-a))+(1+a)^3/(4*(1-a)*(1-k))
noncomputable def fwdSumM0 (a k : ℝ) : ℝ :=
  2*(a+k)*(1-a-k)/((1-a)*(1-k))

private theorem fs_shape_B {a k h : ℝ}
    (ha : 0 ≤ a) (ha1 : a ≤ 1/7) (hk1 : k ≤ 1/5) (hh : 0 < h) :
    ff_B (fwdSumShapeU a k) (fwdSumShapeZ a) h =
      fwdSumB0 a k+fwdSumB1 a k*(h-1)+fwdSumShapeZ a*ff_f h-
        fwdSumShapeZ a*((a+k)/(1-k))*(h-1)^2/(2*h) := by
  obtain ⟨hS,hZ,hK⟩ := fs_shape_dictionary ha ha1 hk1
  unfold ff_B
  rw [hS,hZ]
  unfold fwdSumB0 fwdSumB1 fwdSumShapeZ ff_f
  have hb : 1-a ≠ 0 := ne_of_gt (by linarith : 0 < 1-a)
  have hr : 1-k ≠ 0 := ne_of_gt (by linarith : 0 < 1-k)
  field_simp [hb,hr,ne_of_gt hh]
  ring

private theorem fs_shape_n {a k h : ℝ}
    (ha : 0 ≤ a) (ha1 : a ≤ 1/7) (hk1 : k ≤ 1/5) :
    ff_n (fwdSumShapeU a k) (fwdSumShapeZ a) h = fwdSumN1 a k*(h-1) := by
  obtain ⟨hS,hZ,hK⟩ := fs_shape_dictionary ha ha1 hk1
  unfold ff_n
  rw [hS,hZ]
  unfold fwdSumShapeU fwdSumShapeZ fwdSumN1
  have hb : 1-a ≠ 0 := ne_of_gt (by linarith : 0 < 1-a)
  have hr : 1-k ≠ 0 := ne_of_gt (by linarith : 0 < 1-k)
  field_simp [hb,hr]
  ring

private theorem fs_shape_mn {a k h : ℝ}
    (ha : 0 ≤ a) (ha1 : a ≤ 1/7) (hk1 : k ≤ 1/5) :
    ff_m (fwdSumShapeU a k) (fwdSumShapeZ a) (fwdSumShapeZ a) h-
        ff_n (fwdSumShapeU a k) (fwdSumShapeZ a) h =
      fwdSumM0 a k+fwdSumNd a k*(h-1) := by
  obtain ⟨hS,hZ,hK⟩ := fs_shape_dictionary ha ha1 hk1
  rw [fs_shape_n ha ha1 hk1]
  unfold ff_m ff_q
  rw [hS,hZ,hK]
  unfold fwdSumN1 fwdSumNd fwdSumM0
  have hb : 1-a ≠ 0 := ne_of_gt (by linarith : 0 < 1-a)
  have hr : 1-k ≠ 0 := ne_of_gt (by linarith : 0 < 1-k)
  have hc : 1-a-k ≠ 0 := ne_of_gt (by linarith : 0 < 1-a-k)
  field_simp [hb,hr,hc]
  ring

private theorem fs_shape_floor {a k : ℝ}
    (ha : 0 ≤ a) (ha1 : a ≤ 1/7) (hk : 0 < k) (hk1 : k ≤ 1/5) :
    3/4+ff_L (fwdSumShapeZ a)
      ((1+fwdSumShapeZ a)^2/((fwdSumShapeZ a)^2+fwdSumShapeU a k)) =
      fwdSumFR a k-(1+a)/2*fwdSumEll k := by
  obtain ⟨hS,hZ,hK⟩ := fs_shape_dictionary ha ha1 hk1
  have hb : 1-a ≠ 0 := ne_of_gt (by linarith : 0 < 1-a)
  have hr : 1-k ≠ 0 := ne_of_gt (by linarith : 0 < 1-k)
  have hI : (1+fwdSumShapeZ a)^2/
      ((fwdSumShapeZ a)^2+fwdSumShapeU a k) = 1+k/(1-k) := by
    rw [hS,hZ]
    field_simp [hb,hr]
    ring
  rw [hI]
  unfold ff_L
  rw [hS]
  simp only [ff_f]
  rw [fwdSum_log_one_add hk.le (by linarith)]
  unfold fwdSumShapeZ fwdSumFR
  field_simp [hb,hr,ne_of_gt hk]
  ring

private theorem fs_row_constant {a k : ℝ}
    (ha : 0 ≤ a) (ha1 : a ≤ 1/7) (hk : 0 ≤ k) (hk1 : k ≤ 1/5) :
    fwdSumA0Integral a k =
      ((1-a-k)/(1-k))*(fwdSumAR a k+log ((1-a-k)/(1-k))-k*fwdSumEll k)-
        fwdSumB0 a k-fwdSumM0 a k*(fwdSumFR a k-(1+a)/2*fwdSumEll k) := by
  have hlog : log ((1-a-k)/(1-k)) =
      -a*fwdSumEll k-a*(a+k)*fwdSumJ a k := by
    rw [show 1-a-k = 1-(a+k) by ring]
    exact fwdSum_log_ratio ha hk (by linarith)
  rw [hlog]
  unfold fwdSumA0Integral fwdSumR0 fwdSumAR fwdSumB0 fwdSumM0 fwdSumFR
  have hb : 1-a ≠ 0 := ne_of_gt (by linarith : 0 < 1-a)
  have hr : 1-k ≠ 0 := ne_of_gt (by linarith : 0 < 1-k)
  have hc : 1-a-k ≠ 0 := ne_of_gt (by linarith : 0 < 1-a-k)
  field_simp [hb,hr,hc]
  ring

private theorem fs_row_linear {a k : ℝ}
    (_ha : 0 ≤ a) (ha1 : a ≤ 1/7) (hk1 : k ≤ 1/5) :
    fwdSumA1Row a k =
      2*(1-a-k)/((1-a)*(1-k))*
        (fwdSumAR a k+log ((1-a-k)/(1-k))-k*fwdSumEll k)-
      fwdSumB1 a k-(49/32)*fwdSumN1 a k-
        fwdSumNd a k*(fwdSumFR a k-(1+a)/2*fwdSumEll k) := by
  unfold fwdSumA1Row fwdSumR1 fwdSumNd
  have hb : 1-a ≠ 0 := ne_of_gt (by linarith : 0 < 1-a)
  have hr : 1-k ≠ 0 := ne_of_gt (by linarith : 0 < 1-k)
  field_simp [hb,hr]
  ring

/-- The original Gram row in the paired reciprocal coordinates. -/
theorem fwdSumResidual32_decomp {a k h : ℝ}
    (ha : 0 ≤ a) (ha1 : a ≤ 1/7) (hk : 0 < k) (hk1 : k ≤ 1/5) (hh : 0 < h) :
    fwdSumResidual32 (fwdSumShapeU a k) (fwdSumShapeZ a) h =
      fwdSumA0Integral a k+fwdSumA1Row a k*(h-1)+
        fwdSumShapeZ a*((a+k)/(1-k)*(h-1)^2/(2*h)-ff_f h) := by
  have hzU := fs_shape_pos ha ha1 hk1
  have hrow := ff_r_eq hzU.2 hzU.1 hzU.1 hh
  have hraw : fwdSumResidual32 (fwdSumShapeU a k) (fwdSumShapeZ a) h =
      ff_alpha (fwdSumShapeU a k) (fwdSumShapeZ a) h*
        ff_A (fwdSumShapeU a k) (fwdSumShapeZ a) (fwdSumShapeZ a)-
      ff_B (fwdSumShapeU a k) (fwdSumShapeZ a) h-
      (49/32)*ff_n (fwdSumShapeU a k) (fwdSumShapeZ a) h-
      (ff_m (fwdSumShapeU a k) (fwdSumShapeZ a) (fwdSumShapeZ a) h-
        ff_n (fwdSumShapeU a k) (fwdSumShapeZ a) h)*
        (3/4+ff_L (fwdSumShapeZ a)
          ((1+fwdSumShapeZ a)^2/((fwdSumShapeZ a)^2+fwdSumShapeU a k))) := by
    unfold fwdSumResidual32
    linarith only [hrow]
  rw [hraw,fs_shape_alpha ha ha1 hk1,fs_shape_A ha ha1 hk1,
    fs_shape_B ha ha1 hk1 hh,fs_shape_mn ha ha1 hk1,fs_shape_n ha ha1 hk1,
    fs_shape_floor ha ha1 hk hk1,fwdSum_log_one_add hk.le (by linarith),
    fs_row_constant ha ha1 hk.le hk1,fs_row_linear ha ha1 hk1]
  ring

/-- The original constant-coefficient proof applies throughout the physical normalized rectangle. -/
theorem fwdSumA0Integral_nonpos {a k : ℝ}
    (ha : 0 ≤ a) (ha1 : a ≤ 1/7) (hk : 0 < k) (hk1 : k ≤ 1/5) :
    fwdSumA0Integral a k ≤ 0 := by
  rw [fwdSumA0Integral_eq_original ha ha1 hk hk1]
  apply fs_SA0_bound ha ha1
  · exact div_pos hk (by linarith)
  · apply (div_le_iff₀ (by linarith : 0 < 1-k)).mpr
    linarith

/-- The reciprocal envelope follows directly from the existing analytic f remainder. -/
theorem fwdSum_residual_div_le_psi {A0 A1 D z h : ℝ}
    (hz : 0 ≤ z) (hh : 1 < h) :
    (A0+A1*(h-1)+z*(D*(h-1)^2/(2*h)-ff_f h))/(h-1) ≤
      fwdSumPsi A0 A1 D z ((h-1)/h) := by
  have hh0 : 0 < h := by linarith
  have hH : 0 < h-1 := sub_pos.mpr hh
  have hplus : 0 < h+1 := by linarith
  have hid : fwdSumPsi A0 A1 D z ((h-1)/h)-
      (A0+A1*(h-1)+z*(D*(h-1)^2/(2*h)-ff_f h))/(h-1) =
      z/(h-1)*(ff_f h-(h-1)^3/(3*h*(h+1))) := by
    unfold fwdSumPsi
    rw [show 2-(h-1)/h = (h+1)/h by field_simp; ring]
    field_simp [ne_of_gt hh0,ne_of_gt hH,ne_of_gt hplus]
    ring
  have hp : 0 ≤ z/(h-1)*(ff_f h-(h-1)^3/(3*h*(h+1))) :=
    mul_nonneg (div_nonneg hz hH.le) (sub_nonneg.mpr (fs_f_ge_pade hh.le))
  linarith only [hid,hp]

/-- Complete analytic reduction of the original 1/32 residual to the rational affine upper bound. -/
theorem fwdSumResidual32_div_le_upper {a k h : ℝ}
    (ha : 0 ≤ a) (ha1 : a ≤ 1/7) (hk : 0 < k) (hk1 : k ≤ 1/5)
    (hh : 1 < h) (hτ : (h-1)/h ≤ 2/5) :
    fwdSumResidual32 (fwdSumShapeU a k) (fwdSumShapeZ a) h/(h-1) ≤
      fwdSumUpper a k ((h-1)/h) := by
  have hz := (fs_shape_pos ha ha1 hk1).1
  have hτ0 : 0 < (h-1)/h := div_pos (sub_pos.mpr hh) (by linarith)
  calc
    _ ≤ fwdSumPsi (fwdSumA0Integral a k) (fwdSumA1Row a k)
        ((a+k)/(1-k)) (fwdSumShapeZ a) ((h-1)/h) := by
      rw [fwdSumResidual32_decomp ha ha1 hk hk1 (by linarith)]
      exact fwdSum_residual_div_le_psi hz.le hh
    _ ≤ fwdSumFixedTangent (fwdSumA0Integral a k) (fwdSumA1Row a k)
        ((a+k)/(1-k)) (fwdSumShapeZ a) ((h-1)/h) :=
      fwdSumPsi_le_fixedTangent (fwdSumA0Integral_nonpos ha ha1 hk hk1) hz.le hτ0
        (by linarith)
    _ ≤ _ := fwdSumFixedTangent_le_upper ha ha1 hk.le hk1 hτ

/-- Upper endpoint supplied by the physical norm budget. -/
noncomputable def fwdSumFactorTop (a k : ℝ) : ℝ :=
  (2-2*a^2-(7+3*a)*k)/(5-3*a-2*a^2-10*k)
noncomputable def fwdSumLinearTop (k : ℝ) : ℝ := 8/15-5*k/3

/-- The budget denominator is positive for the stated physical shape restriction. -/
theorem fwdSumFactorDen_pos {a k : ℝ}
    (ha1 : a ≤ 1/7) (hk : k ≤ (1-a^2)/5) :
    0 < 5-3*a-2*a^2-10*k := by
  have hd : 0 ≤ 1-a^2-5*k := by linarith only [hk]
  have hid : 5-3*a-2*a^2-10*k = 3*(1-a)+2*(1-a^2-5*k) := by ring
  rw [hid]
  linarith only [hd,ha1]

/-- The physical endpoint lies within the full fixed-tangent factor interval. -/
theorem fwdSumFactorTop_le_two_fifths {a k : ℝ}
    (ha : 0 ≤ a) (ha1 : a ≤ 1/7) (hk : 0 ≤ k)
    (hkbudget : k ≤ (1-a^2)/5) (hka : a*(1-a) ≤ k) :
    fwdSumFactorTop a k ≤ 2/5 := by
  unfold fwdSumFactorTop
  apply (div_le_iff₀ (fwdSumFactorDen_pos ha1 hkbudget)).mpr
  have hak := mul_nonneg ha hk
  nlinarith only [hka,hk,hak]

/-- Exact square remainder behind the linear ceiling for the physical endpoint. -/
theorem fwdSumFactorTop_square_remainder (a k : ℝ) :
    fwdSumLinearTop k*(5-3*a-2*a^2-10*k)-(2-2*a^2-(7+3*a)*k) =
      (2/15)*(5*(1-5*k-13*a/10)^2+71*a^2/20)+
        (2/15)*a*(1-5*k)*(1-5*a) := by
  unfold fwdSumLinearTop
  ring

/-- The factor's upper budget endpoint also lies below a linear ceiling in k. -/
theorem fwdSumFactorTop_le_linear {a k : ℝ}
    (ha : 0 ≤ a) (ha1 : a ≤ 1/7) (hk1 : k ≤ 1/5)
    (hkbudget : k ≤ (1-a^2)/5) :
    fwdSumFactorTop a k ≤ fwdSumLinearTop k := by
  unfold fwdSumFactorTop
  apply (div_le_iff₀ (fwdSumFactorDen_pos ha1 hkbudget)).mpr
  have hh := fwdSumFactorTop_square_remainder a k
  have hp : 0 ≤ (2/15:ℝ)*(5*(1-5*k-13*a/10)^2+71*a^2/20)+
      (2/15)*a*(1-5*k)*(1-5*a) := by
    apply add_nonneg
    · positivity
    · exact mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) ha)
        (by linarith)) (by linarith)
  linarith only [hh,hp]

/-- The affine upper bound is negative between any two negative endpoint values. -/
theorem fwdSumUpper_neg_between {a k x y τ : ℝ}
    (hx : x ≤ τ) (hy : τ ≤ y)
    (hleft : fwdSumUpper a k x < 0) (hright : fwdSumUpper a k y < 0) :
    fwdSumUpper a k τ < 0 := by
  by_cases hxy : x = y
  · have ht : τ = x := by linarith only [hx,hy,hxy]
    simpa only [ht] using hleft
  have hxypos : 0 < y-x := sub_pos.mpr (lt_of_le_of_ne (le_trans hx hy) hxy)
  have hid : (y-x)*fwdSumUpper a k τ =
      (y-τ)*fwdSumUpper a k x+(τ-x)*fwdSumUpper a k y := by
    unfold fwdSumUpper fwdSumPairedLogUpper
    ring
  have hleft0 : (y-τ)*fwdSumUpper a k x ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos (sub_nonneg.mpr hy) hleft.le
  by_cases htx : τ = x
  · simpa only [htx] using hleft
  · have hτx : 0 < τ-x := sub_pos.mpr (lt_of_le_of_ne hx (Ne.symm htx))
    have hprod := mul_neg_of_pos_of_neg hτx hright
    have htotal : (y-x)*fwdSumUpper a k τ < 0 := by linarith only [hid,hleft0,hprod]
    exact neg_of_mul_neg_right htotal hxypos.le

/-- The physical floor and budget give exactly the interval used by the affine test. -/
theorem fwdSum_factor_interval {a k h : ℝ}
    (ha : 0 ≤ a) (ha1 : a ≤ 1/7) (hk : 0 < k)
    (hkbudget : k ≤ (1-a^2)/5) (hka : a*(1-a) ≤ k)
    (hfloor : 1+k/(1-k) ≤ h)
    (hcap : h ≤ (5-3*a-2*a^2-10*k)/(3*(1-a)*(1-k))) :
    1 < h ∧ k ≤ (h-1)/h ∧
      (h-1)/h ≤ min (2/5) (fwdSumLinearTop k) := by
  have hk1 : k ≤ 1/5 := by nlinarith only [hkbudget,sq_nonneg a]
  have hb : 0 < 1-a := by linarith
  have hr : 0 < 1-k := by linarith
  have hh : 1 < h := lt_of_lt_of_le (by have := div_pos hk hr; linarith) hfloor
  have hh0 : 0 < h := by linarith
  have hlow : k ≤ (h-1)/h := by
    apply (le_div_iff₀ hh0).mpr
    have hfl : (1+k/(1-k))*(1-k) ≤ h*(1-k) := mul_le_mul_of_nonneg_right hfloor hr.le
    have hid : (1+k/(1-k))*(1-k) = 1 := by field_simp; ring
    rw [hid] at hfl
    nlinarith only [hfl]
  have hDc := fwdSumFactorDen_pos ha1 hkbudget
  have hden : 0 < 3*(1-a)*(1-k) := by positivity
  have hhi : (h-1)/h ≤ fwdSumFactorTop a k := by
    unfold fwdSumFactorTop
    apply (div_le_div_iff₀ hh0 hDc).mpr
    have hscaled : h*(3*(1-a)*(1-k)) ≤ 5-3*a-2*a^2-10*k :=
      (le_div_iff₀ hden).mp hcap
    nlinarith only [hscaled]
  exact ⟨hh,hlow,le_min
    (le_trans hhi (fwdSumFactorTop_le_two_fifths ha ha1 hk.le hkbudget hka))
    (le_trans hhi (fwdSumFactorTop_le_linear ha ha1 hk1 hkbudget))⟩

/-- Closing interface: only the two rational affine endpoint signs remain to prove. -/
theorem fwdSumResidual32_neg_of_upper_endpoints {a k h : ℝ}
    (ha : 0 ≤ a) (ha1 : a ≤ 1/7) (hk : 0 < k)
    (hkbudget : k ≤ (1-a^2)/5) (hka : a*(1-a) ≤ k)
    (hfloor : 1+k/(1-k) ≤ h)
    (hcap : h ≤ (5-3*a-2*a^2-10*k)/(3*(1-a)*(1-k)))
    (hleft : fwdSumUpper a k k < 0)
    (hright : fwdSumUpper a k (min (2/5) (fwdSumLinearTop k)) < 0) :
    fwdSumResidual32 (fwdSumShapeU a k) (fwdSumShapeZ a) h < 0 := by
  obtain ⟨hh,hτlow,hτtop⟩ := fwdSum_factor_interval ha ha1 hk hkbudget hka hfloor hcap
  have hk1 : k ≤ 1/5 := by nlinarith only [hkbudget,sq_nonneg a]
  have hupper := fwdSumResidual32_div_le_upper ha ha1 hk hk1 hh (le_trans hτtop (min_le_left _ _))
  have hneg := fwdSumUpper_neg_between hτlow hτtop hleft hright
  have hres : fwdSumResidual32 (fwdSumShapeU a k) (fwdSumShapeZ a) h/(h-1) < 0 :=
    lt_of_le_of_lt hupper hneg
  simpa only [zero_mul] using (div_lt_iff₀ (sub_pos.mpr hh)).mp hres

/-- The normalization covers the entire original symmetric shape domain. -/
theorem fwdSum_physical_coordinates {U z : ℝ}
    (hz : 1 ≤ z) (hz4 : z ≤ 4/3) (hbud : 1+6*z/5 ≤ U) (hU3 : U < 3) :
    let a := (z-1)/(z+1)
    let k := (2*z+1-U)/(1+z)^2
    0 ≤ a ∧ a ≤ 1/7 ∧ 0 < k ∧ a*(1-a) < k ∧
      k ≤ (1-a^2)/5 ∧ fwdSumShapeZ a = z ∧ fwdSumShapeU a k = U := by
  let a := (z-1)/(z+1)
  let k := (2*z+1-U)/(1+z)^2
  have hS : 0 < z+1 := by linarith
  have hS' : 0 < 1+z := by linarith
  have ha : 0 ≤ a := div_nonneg (by linarith) hS.le
  have ha1 : a ≤ 1/7 := by
    apply (div_le_iff₀ hS).mpr
    linarith only [hz4]
  have hk : 0 < k := div_pos (by linarith only [hz,hU3]) (sq_pos_of_pos hS')
  have hkgap : k-a*(1-a) = (3-U)/(1+z)^2 := by
    dsimp [a,k]
    field_simp [ne_of_gt hS,ne_of_gt hS']
    ring
  have hka : a*(1-a) < k := by
    have hp : 0 < (3-U)/(1+z)^2 := div_pos (sub_pos.mpr hU3) (sq_pos_of_pos hS')
    linarith only [hkgap,hp]
  have hkbudgap : (1-a^2)/5-k = (U-1-6*z/5)/(1+z)^2 := by
    dsimp [a,k]
    field_simp [ne_of_gt hS,ne_of_gt hS']
    ring
  have hkbudget : k ≤ (1-a^2)/5 := by
    have hp : 0 ≤ (U-1-6*z/5)/(1+z)^2 := div_nonneg (by linarith only [hbud]) (sq_nonneg _)
    linarith only [hkbudgap,hp]
  have hb : 1-a = 2/(z+1) := by
    dsimp [a]
    field_simp [ne_of_gt hS]
    ring
  refine ⟨ha,ha1,hk,hka,hkbudget,?_,?_⟩
  · unfold fwdSumShapeZ
    rw [hb]
    field_simp [ne_of_gt hS]
    ring
  · unfold fwdSumShapeU
    rw [hb]
    field_simp [ne_of_gt hS,ne_of_gt hS']
    ring

private theorem fs_shape_budget {a k : ℝ}
    (ha : 0 ≤ a) (ha1 : a ≤ 1/7) (hk1 : k ≤ 1/5) :
    (1+fwdSumShapeZ a)*(5*fwdSumShapeU a k-2-3*fwdSumShapeZ a)/
        (3*((fwdSumShapeZ a)^2+fwdSumShapeU a k)) =
      (5-3*a-2*a^2-10*k)/(3*(1-a)*(1-k)) := by
  obtain ⟨hS,hZ,hK⟩ := fs_shape_dictionary ha ha1 hk1
  rw [hS,hZ]
  unfold fwdSumShapeU fwdSumShapeZ
  have hb : 1-a ≠ 0 := ne_of_gt (by linarith : 0 < 1-a)
  have hr : 1-k ≠ 0 := ne_of_gt (by linarith : 0 < 1-k)
  field_simp [hb,hr]
  ring

/-- Original-domain closing interface; neither normalized endpoint sign is assumed implicitly. -/
theorem fwdSumResidual32_original_neg_of_upper_endpoints {U z h : ℝ}
    (hz : 1 ≤ z) (hz4 : z ≤ 4/3) (hbud : 1+6*z/5 ≤ U) (hU3 : U < 3)
    (hfloor : (1+z)^2/(z^2+U) ≤ h)
    (hcap : h ≤ (1+z)*(5*U-2-3*z)/(3*(z^2+U)))
    (hleft : fwdSumUpper ((z-1)/(z+1)) ((2*z+1-U)/(1+z)^2)
      ((2*z+1-U)/(1+z)^2) < 0)
    (hright : fwdSumUpper ((z-1)/(z+1)) ((2*z+1-U)/(1+z)^2)
      (min (2/5) (fwdSumLinearTop ((2*z+1-U)/(1+z)^2))) < 0) :
    fwdSumResidual32 U z h < 0 := by
  obtain ⟨ha,ha1,hk,hka,hkbudget,hzback,hUback⟩ := fwdSum_physical_coordinates hz hz4 hbud hU3
  let a := (z-1)/(z+1)
  let k := (2*z+1-U)/(1+z)^2
  have hk1 : k ≤ 1/5 := by nlinarith only [hkbudget,sq_nonneg a]
  have hI : 1+k/(1-k) = (1+z)^2/(z^2+U) := by
    rw [← hzback,← hUback]
    obtain ⟨hS,hZ,hK⟩ := fs_shape_dictionary ha ha1 hk1
    rw [hS,hZ]
    have hb : 1-a ≠ 0 := ne_of_gt (by linarith : 0 < 1-a)
    have hr : 1-k ≠ 0 := ne_of_gt (by linarith : 0 < 1-k)
    field_simp [hb,hr]
    ring
  have hbudget : h ≤ (5-3*a-2*a^2-10*k)/(3*(1-a)*(1-k)) := by
    rw [← fs_shape_budget ha ha1 hk1,hzback,hUback]
    exact hcap
  have hneg := fwdSumResidual32_neg_of_upper_endpoints ha ha1 hk hkbudget hka.le
    (hI ▸ hfloor) hbudget hleft hright
  rwa [hzback,hUback] at hneg
