module

public import SmoothedOctagon.Exclusion.Mixed.SmallerShort.Order.Contacts

/-!
# The strong lower bridge order

The strict Simpson bound and monotonicity of weighted means control the ratio
of the endpoint gaps. Two positive-product identities compare this ratio with
the affine contact threshold for every positive shape parameter.
-/

@[expose] public section

namespace SmoothedOctagon

open Set Real

/-- The strong affine slope in the deficit parameter `a=1-1/x`. -/
noncomputable def ordStrongK (a : ℝ) : ℝ := 4*(2-a)/(8-a)
/-- The endpoint-gap majorant from the strict Simpson bound. -/
noncomputable def ordGapMajorant (b r : ℝ) : ℝ :=
  (2-b*r)/(2-b)*(8+4*r-b*(1+5*r))/(4+8*r-b*r*(5+r))
/-- The fixed deficit-ratio comparison for the strong barrier. -/
noncomputable def ordStrongB (a r : ℝ) : ℝ :=
  1+(1-r)*(2/ordStrongK a-1)/(1+(2-a)*r)
/-- The comparison with the affine contact threshold, with `h=k-a`. -/
noncomputable def ordStrongB0 (k h r : ℝ) : ℝ :=
  1+(1-r)*(2/k-1)/(1+(1+h)*r)

theorem ord_strong_k_range {a : ℝ} (ha : 0 < a) (ha1 : a < 1) :
    0 < ordStrongK a ∧ ordStrongK a < 1 ∧ 1-a/2 < ordStrongK a := by
  have h8 : 0 < 8-a := by linarith
  have he : ordStrongK a-(1-a/2)=a*(2-a)/(2*(8-a)) := by
    unfold ordStrongK; field_simp; ring
  have hp : 0 < a*(2-a)/(2*(8-a)) := by
    have : 0 < 2-a := by linarith
    positivity
  refine ⟨?_,?_,?_⟩
  · unfold ordStrongK
    have : 0 < 2-a := by linarith
    positivity
  · unfold ordStrongK; rw [div_lt_one h8]; linarith
  · linarith only [he,hp]

private theorem strongHat_den {b r : ℝ} (_hb : 0 < b) (hb1 : b < 1)
    (hr : 0 ≤ r) (hr1 : r < 1) : 0 < 4+8*r-b*r*(5+r) := by
  have hcost : b*r*(5+r) ≤ r*(5+r) := by
    have : 0 ≤ r*(5+r) := by positivity
    nlinarith only [hb1,this]
  have hr2 : r^2 ≤ r := by nlinarith only [hr,hr1]
  linarith only [hcost,hr2,hr]

theorem ss_gap_ratio_simpson {b r : ℝ} (hb : 0 < b) (hb1 : b < 1)
    (hr : 0 ≤ r) (hr1 : r < 1) :
    (ss_gB 1 (1-b)-m2Sec (1-b) 1 (1-b*r)) /
      (m2Sec (1-b) 1 (1-b*r)-ss_gB 1 (1-b*r)) < ordGapMajorant b r := by
  have hp : 0 < 1-b := by linarith
  have hpq : 1-b < 1-b*r := by nlinarith only [hb,hr1]
  have hq : 1-b*r ≤ 1 := by nlinarith only [hb,hr]
  have hη : 0 < m2Sec (1-b) 1 (1-b*r)-ss_gB 1 (1-b*r) :=
    sub_pos.mpr (ss_sec_gt_right hp hpq hq)
  have hH := strongHat_den hb hb1 hr hr1
  have h2 : 0 < 2-b := by linarith
  have hN : 0 < (1+(1-b))*(6+(1-b)-5*(1-b)*(1-b*r)-(1-b*r)^2-(1-b*r)) := by
    have he : (1+(1-b))*(6+(1-b)-5*(1-b)*(1-b*r)-(1-b*r)^2-(1-b*r)) =
        b*(2-b)*(4+8*r-b*r*(5+r)) := by ring
    rw [he]; positivity
  have hgap := ss_gap_ratio_low hp hpq hq
  rw [div_lt_iff₀ hη]
  have he : ordGapMajorant b r =
      (6*((1-b)+(1-b*r)+2)*(1-(1-b)*(1-b*r))-
        (1+(1-b))*(6+(1-b)-5*(1-b)*(1-b*r)-(1-b*r)^2-(1-b*r))) /
      ((1+(1-b))*(6+(1-b)-5*(1-b)*(1-b*r)-(1-b*r)^2-(1-b*r))) := by
    unfold ordGapMajorant
    field_simp (disch := first | positivity | nlinarith)
    ring
  rw [he]
  have hh := mul_lt_mul_of_pos_right hgap (inv_pos.mpr hN)
  have he' : (1+(1-b))*(6+(1-b)-5*(1-b)*(1-b*r)-(1-b*r)^2-(1-b*r)) *
      (ss_gB 1 (1-b)-m2Sec (1-b) 1 (1-b*r)) *
      ((1+(1-b))*(6+(1-b)-5*(1-b)*(1-b*r)-(1-b*r)^2-(1-b*r)))⁻¹ =
      ss_gB 1 (1-b)-m2Sec (1-b) 1 (1-b*r) := by field_simp (disch := first | positivity | nlinarith)
  rw [he'] at hh
  convert hh using 1; ring

/-- The exact positive gain in the fixed deficit-ratio majorant. -/
theorem ord_strong_majorant_gain {a r : ℝ} (ha : 0 < a) (ha1 : a < 1)
    (hr : 0 ≤ r) (hr1 : r < 1) : ordStrongB a r-ordGapMajorant (a/(1+(1-a/2)*r)) r =
      a*r*(1-r)*((1+r)*(4*(1-a)*(7*r+1)+a*(9*r+11))+2*a*(1-a)*r*(5-r)) /
      (2*(2-a)*(1+r)*(1+(2-a)*r)*(4+(12-7*a)*r+(8-5*a)*r^2)) := by
  have hbase : 0 < 1+(1-a/2)*r := by
    have : 0 < 1-a/2 := by linarith
    positivity
  have hb : 0 < a/(1+(1-a/2)*r) := div_pos ha hbase
  have hb1 : a/(1+(1-a/2)*r) < 1 := by rw [div_lt_one hbase]; nlinarith only [ha1,hr]
  have hH := strongHat_den hb hb1 hr hr1
  have h2 : 0 < 2-a/(1+(1-a/2)*r) := by linarith only [hb1]
  have hstar : 0 < 4+(12-7*a)*r+(8-5*a)*r^2 := by
    have : 0 < 12-7*a := by linarith
    have : 0 < 8-5*a := by linarith
    positivity
  have hQ : 0 < (1+r)*(4*(1-a)*(7*r+1)+a*(9*r+11))+2*a*(1-a)*r*(5-r) := by
    have : 0 < 1-a := by linarith
    have : 0 < 5-r := by linarith
    positivity
  have h2a : 0 < 2-a := by linarith
  have h8a : 0 < 8-a := by linarith
  have h1 : 0 < 1+(2-a)*r := by positivity
  unfold ordStrongB ordGapMajorant ordStrongK
  field_simp (disch := first | positivity | nlinarith)
  ring

/-- The strict Simpson majorant remains valid for every smaller interval scale. -/
theorem ss_gap_ratio_majorant {a b r : ℝ} (ha : 0 < a) (ha1 : a < 1)
    (hb : 0 < b) (hbmax : b ≤ a/(1+(1-a/2)*r)) (hr : 0 ≤ r) (hr1 : r < 1) :
    (ss_gB 1 (1-b)-m2Sec (1-b) 1 (1-b*r)) /
      (m2Sec (1-b) 1 (1-b*r)-ss_gB 1 (1-b*r)) <
        ordGapMajorant (a/(1+(1-a/2)*r)) r := by
  have hbase : 0 < 1+(1-a/2)*r := by
    have : 0 < 1-a/2 := by linarith only [ha1]
    positivity
  have hbm0 : 0 < a/(1+(1-a/2)*r) := div_pos ha hbase
  have hbm1 : a/(1+(1-a/2)*r) < 1 := by
    rw [div_lt_one hbase]
    have : 0 ≤ (1-a/2)*r := mul_nonneg (by linarith only [ha1]) hr
    linarith only [ha1,this]
  exact lt_of_le_of_lt (ss_gap_ratio_scale_mono hb hbmax hbm1 hr hr1)
    (ss_gap_ratio_simpson hbm0 hbm1 hr hr1)

private theorem strongHat_bound {a r : ℝ} (ha : 0 < a) (ha1 : a < 1)
    (hr : 0 ≤ r) (hr1 : r < 1) :
    ordGapMajorant (a/(1+(1-a/2)*r)) r ≤ ordStrongB a r := by
  have hstar : 0 < 4+(12-7*a)*r+(8-5*a)*r^2 := by
    have : 0 < 12-7*a := by linarith
    have : 0 < 8-5*a := by linarith
    positivity
  have hQ : 0 < (1+r)*(4*(1-a)*(7*r+1)+a*(9*r+11))+2*a*(1-a)*r*(5-r) := by
    have : 0 < 1-a := by linarith
    have : 0 < 5-r := by linarith
    positivity
  have he := ord_strong_majorant_gain ha ha1 hr hr1
  have hn : 0 ≤ a*r*(1-r)*((1+r)*(4*(1-a)*(7*r+1)+a*(9*r+11))+2*a*(1-a)*r*(5-r)) /
      (2*(2-a)*(1+r)*(1+(2-a)*r)*(4+(12-7*a)*r+(8-5*a)*r^2)) := by
    have : 0 < 2-a := by linarith
    have : 0 < 1-r := by linarith
    positivity
  linarith only [he,hn]

/-- The contact threshold in deficit-ratio coordinates. -/
noncomputable def ordContactM (a v r : ℝ) : ℝ :=
  1+(1-r)*(1+v*r)/((1+(v-a)*r)*(1+(v+1-a)*r))

/-- The normalized contact threshold agrees with the original endpoint expression. -/
theorem ord_contact_threshold_eq {a v r : ℝ} (ha : 0 < a) (ha1 : a < 1)
    (hv : 0 ≤ v) (hr : 0 ≤ r) (hr1 : r < 1) :
    ordContactM a v r =
      1+((1-a*r/(1+v*r))-(1-a/(1+v*r))) /
        ((1-a*r/(1+v*r))*(1-(1-a)*(1-a*r/(1+v*r)))) := by
  have hv1 : 0 < 1+v-a := by linarith only [ha1,hv]
  have hvr : 0 < 1+v*r := by positivity
  have hhr : 0 < 1+(v-a)*r := by
    have he : 1+(v-a)*r = (1-r)+(1+v-a)*r := by ring
    rw [he]
    have : 0 < 1-r := by linarith only [hr1]
    positivity
  have hv1' : 0 < v+1-a := by linarith only [hv1]
  have hhr1 : 0 < 1+(v+1-a)*r := by positivity
  have hq : 1-a*r/(1+v*r) = (1+(v-a)*r)/(1+v*r) := by
    field_simp (disch := first | positivity | nlinarith)
    ring
  have hother : 1-(1-a)*(1-a*r/(1+v*r)) = a*(1+(v+1-a)*r)/(1+v*r) := by
    field_simp (disch := first | positivity | nlinarith)
    ring
  rw [hother,hq]
  unfold ordContactM
  field_simp (disch := first | positivity | nlinarith)
  ring

/-- The exact contact gain for a positive affine slope smaller than one. -/
theorem ord_strong_contact_gain {a k r : ℝ} (ha : 0 < a) (ha1 : a < 1)
    (hk0 : 0 < k) (hk1 : k < 1) (hr : 0 ≤ r) (hr1 : r < 1) :
    let h := k-a
    ordContactM a k r - k*ordStrongB0 k h r =
      r*((1-r)*(2-k*(1+h))+r*(1-k)*(1+h)*(2+h)) /
        ((1+h*r)*(1+(1+h)*r)) := by
  let h := k-a
  have hk : 0 < k ∧ k < 1 := ⟨hk0,hk1⟩
  have hh : -1 < h ∧ h < k := by dsimp [h]; constructor <;> linarith only [hk.1,ha1,ha]
  have hrm : 0 < 1-r := by linarith only [hr1]
  have h1 : 0 < 1+h := by linarith only [hh.1]
  have hden0 : 0 < 1+(1+h)*r := by positivity
  have hhr : 0 < 1+h*r := by
    have he : 1+h*r = (1-r)+(1+h)*r := by ring
    rw [he]; positivity
  have hkr : 0 < 1+k*r := by positivity
  rw [ord_contact_threshold_eq ha ha1 hk0.le hr hr1]
  change 1+((1-a*r/(1+k*r))-(1-a/(1+k*r))) /
        ((1-a*r/(1+k*r))*(1-(1-a)*(1-a*r/(1+k*r)))) - k*ordStrongB0 k h r = _
  have hq : 1-a*r/(1+k*r) = (1+h*r)/(1+k*r) := by dsimp [h]; field_simp (disch := first | positivity | nlinarith); ring
  have hother : 1-(1-a)*(1-a*r/(1+k*r)) = a*(1+(1+h)*r)/(1+k*r) := by
    dsimp [h]; field_simp (disch := first | positivity | nlinarith); ring
  rw [hother,hq]
  dsimp [ordStrongB0,h]
  field_simp (disch := first | positivity | nlinarith)
  ring

private theorem strong_threshold {a r : ℝ} (ha : 0 < a) (ha1 : a < 1)
    (hr : 0 ≤ r) (hr1 : r < 1) :
    ordStrongK a * ordStrongB a r ≤
      1+((1-a*r/(1+ordStrongK a*r))-(1-a/(1+ordStrongK a*r))) /
        ((1-a*r/(1+ordStrongK a*r))*(1-(1-a)*(1-a*r/(1+ordStrongK a*r)))) := by
  let k := ordStrongK a
  let h := k-a
  have hk : 0 < k ∧ k < 1 := (ord_strong_k_range ha ha1).imp_right (fun h => h.1)
  have hh : -1 < h ∧ h < k := by dsimp [h]; constructor <;> linarith only [hk.1,ha1,ha]
  have hrm : 0 < 1-r := by linarith
  have h1 : 0 < 1+h := by linarith only [hh.1]
  have h2 : 0 < 2+h := by linarith only [hh.1]
  have hden0 : 0 < 1+(1+h)*r := by positivity
  have hden : 0 < 1+(2-a)*r := by
    have : 0 < 2-a := by linarith
    positivity
  have hB : ordStrongB a r ≤ ordStrongB0 k h r := by
    have hfrac := div_le_div_of_nonneg_left (show 0 ≤ (1-r)*(2/k-1) by
      have : 0 < 2/k-1 := by rw [sub_pos,lt_div_iff₀ hk.1]; linarith only [hk.2]
      positivity) hden0 (show 1+(1+h)*r ≤ 1+(2-a)*r by
        dsimp [h]; nlinarith only [hk.2,hr])
    dsimp [ordStrongB,ordStrongB0,k] at *
    linarith only [hfrac]
  have hhr : 0 < 1+h*r := by
    have he : 1+h*r = (1-r)+(1+h)*r := by ring
    rw [he]; positivity
  have hkr : 0 < 1+k*r := by
    have : 0 < k := hk.1
    positivity
  have hcost : 0 < 2-k*(1+h) := by
    have hh' := mul_lt_mul_of_pos_left hh.2 hk.1
    have hp : 0 < (1-k)*(k+2) := by
      have : 0 < 1-k := by linarith only [hk.2]
      have : 0 < k+2 := by linarith only [hk.1]
      positivity
    nlinarith only [hh',hp]
  have he := ord_strong_contact_gain ha ha1 hk.1 hk.2 hr hr1
  rw [ord_contact_threshold_eq ha ha1 hk.1.le hr hr1] at he
  change 1+((1-a*r/(1+k*r))-(1-a/(1+k*r))) /
        ((1-a*r/(1+k*r))*(1-(1-a)*(1-a*r/(1+k*r)))) - k*ordStrongB0 k h r = _ at he
  have hn : 0 ≤ r*((1-r)*(2-k*(1+h))+r*(1-k)*(1+h)*(2+h)) /
      ((1+h*r)*(1+(1+h)*r)) := by
    have : 0 < 1-k := by linarith only [hk.2]
    positivity
  have hmul := mul_le_mul_of_nonneg_left hB hk.1.le
  change k * ordStrongB a r ≤ _
  linarith only [he,hn,hmul]

/-- The strong affine barrier has negative derivative at every contact. -/
theorem ss_strong_contact {x z : ℝ} (hx : 1 < x) (hz : z ≤ 1)
    (hP : 1/x+ssKs x*(1-z) < z) :
    ssKs x*(ss_gB 1 (1/x+ssKs x*(1-z))-m2Sec (1/x+ssKs x*(1-z)) 1 z)*z*(x-z) <
      (m2Sec (1/x+ssKs x*(1-z)) 1 z-ss_gB 1 z)*
        ((2*z-(1/x+ssKs x*(1-z)))*x-z^2) := by
  have hx0 : 0 < x := by linarith only [hx]
  let a := 1-1/x
  let p := 1/x+ssKs x*(1-z)
  let b := 1-p
  let r := (1-z)/b
  have hix : 0 < 1/x := by positivity
  have hix1 : 1/x < 1 := (div_lt_one hx0).mpr hx
  have ha : 0 < a := by dsimp [a]; linarith only [hix1]
  have ha1 : a < 1 := by dsimp [a]; linarith only [hix]
  have hk := ord_strong_k_range ha ha1
  have heK : ssKs x = ordStrongK a := by
    have h8 : 0 < 8-a := by linarith only [ha1]
    dsimp [a,ordStrongK,ssKs] at *
    field_simp (disch := first | positivity | nlinarith)
    ring
  have hp : 0 < p := by
    dsimp [p]
    rw [heK]
    have : 0 ≤ 1-z := by linarith only [hz]
    exact add_pos_of_pos_of_nonneg hix (mul_nonneg hk.1.le this)
  have hpz : p < z := hP
  have hb : 0 < b := by dsimp [b]; linarith only [hpz,hz]
  have hb1 : b < 1 := by dsimp [b]; linarith only [hp]
  have hr : 0 ≤ r := div_nonneg (by linarith only [hz]) hb.le
  have hr1 : r < 1 := by dsimp [r]; rw [div_lt_one hb]; dsimp [b]; linarith only [hpz]
  have hbr : b*r = 1-z := by dsimp [r]; field_simp
  have hep : p = 1-b := by dsimp [b]; ring
  have hez : z = 1-b*r := by linarith only [hbr]
  have hbk : b = a/(1+ordStrongK a*r) := by
    have hden : 0 < 1+ordStrongK a*r := by
      have : 0 < ordStrongK a := hk.1
      positivity
    apply (eq_div_iff hden.ne').mpr
    have hp' : p = 1-a+ordStrongK a*(1-z) := by dsimp [p,a]; rw [heK]; ring
    have hbrk := congrArg (fun v : ℝ => ordStrongK a*v) hbr
    nlinarith only [hp',hbrk,hep]
  have hbase : 0 < 1+(1-a/2)*r := by
    have : 0 < 1-a/2 := by linarith only [ha1]
    positivity
  have hbmax : b ≤ a/(1+(1-a/2)*r) := by
    rw [hbk]
    apply div_le_div_of_nonneg_left ha.le hbase
    have hp := mul_nonneg (sub_nonneg.mpr hk.2.2.le) hr
    linarith only [hp]
  have hR := lt_of_lt_of_le (ss_gap_ratio_majorant ha ha1 hb hbmax hr hr1)
    (strongHat_bound ha ha1 hr hr1)
  rw [← hep,← hez] at hR
  have hη : 0 < m2Sec p 1 z-ss_gB 1 z := sub_pos.mpr (ss_sec_gt_right hp hpz hz)
  have hF : 0 < z*(x-z) := mul_pos (hp.trans hpz) (by linarith only [hx,hz])
  have hthreshold := strong_threshold ha ha1 hr hr1
  have haz : 1-a*r/(1+ordStrongK a*r) = z := by
    rw [show a*r/(1+ordStrongK a*r) = (a/(1+ordStrongK a*r))*r by ring,← hbk,← hez]
  rw [haz,← hbk,← hep] at hthreshold
  have hthreshold' : ordStrongK a*ordStrongB a r ≤ ((2*z-p)*x-z^2)/(z*(x-z)) := by
    have he : 1+(z-p)/(z*(1-(1-a)*z)) = ((2*z-p)*x-z^2)/(z*(x-z)) := by
      have he1 : 1-(1-a)*z = (x-z)/x := by dsimp [a]; field_simp; ring
      have hzx : 0 < x-z := by linarith only [hx,hz]
      rw [he1]
      field_simp (disch := first | positivity | nlinarith)
      ring
    simpa only [he] using hthreshold
  have hchain := lt_of_lt_of_le (mul_lt_mul_of_pos_left hR hk.1) hthreshold'
  have hchain' : (ordStrongK a*(ss_gB 1 p-m2Sec p 1 z))/(m2Sec p 1 z-ss_gB 1 z) <
      ((2*z-p)*x-z^2)/(z*(x-z)) := by simpa only [mul_div_assoc] using hchain
  have hcon := (div_lt_div_iff₀ hη hF).mp hchain'
  rw [← heK] at hcon
  dsimp [p] at hcon
  convert hcon using 1 <;> ring

end SmoothedOctagon
