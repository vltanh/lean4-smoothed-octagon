module

public import SmoothedOctagon.Exclusion.Mixed.SmallerShort.Order.Upper

/-!
# The small-box upper bridge order

For the middle shape range, the half-tilted linear derivative weight gives a
positive contact expression. For the largest range, the maximal tilt gives a
quotient of its exact moments. Bounds on the quotient's derivatives reduce the
contact sign first to an edge and then to its lower corner.
-/

@[expose] public section

namespace SmoothedOctagon

open Set Real

private noncomputable def smallN (b s : ℝ) : ℝ := 9*b^2-10*b*s-5*s^2+8*b+4*s
private noncomputable def smallD (b s : ℝ) : ℝ := 3*b^2-2*b*s-7*s^2+4*b+8*s
private noncomputable def smallT (b s : ℝ) : ℝ := smallN b s / smallD b s

private theorem smallD_lower {b s : ℝ} (hb : 9/20 ≤ b) (hb1 : b ≤ 7/13)
    (hs : 0 ≤ s) (hs1 : s ≤ 1/20) : 12/5 < smallD b s := by
  have hp : 0 ≤ s * (8-2*b-7*s) := mul_nonneg hs (by linarith)
  have hbase : 963/400 ≤ b*(3*b+4) := by
    have hprod := mul_nonneg (sub_nonneg.mpr hb) (by linarith : 0 ≤ 3*b+107/20)
    nlinarith only [hprod]
  dsimp [smallD]
  nlinarith only [hp,hbase]

private theorem smallT_lower {b s : ℝ} (hb : 9/20 ≤ b) (hb1 : b ≤ 7/13)
    (hs : 0 ≤ s) (hs1 : s ≤ 1/20) : 17/10 < smallT b s := by
  have hb0 : 0 < b := by linarith
  have hbs : 0 < b-s := by linarith
  have hD := smallD_lower hb hb1 hs hs1
  have hden : 0 < b+2*s := by positivity
  have hlin : 19/11 ≤ (2*b+s)/(b+2*s) := by
    rw [le_div_iff₀ hden]
    linarith
  have hid : smallN b s*(b+2*s)-(2*b+s)*smallD b s =
      3*(b-s)*(b^2+4*b*s+s^2) := by dsimp [smallN,smallD]; ring
  have hgain : 0 < 3*(b-s)*(b^2+4*b*s+s^2) := by positivity
  have hstrict : (2*b+s)/(b+2*s) < smallT b s := by
    dsimp [smallT]
    rw [div_lt_div_iff₀ hden (by linarith : 0 < smallD b s)]
    nlinarith only [hid,hgain]
  linarith only [hlin,hstrict]

private theorem smallT_upper {b s : ℝ} (hb : 9/20 ≤ b) (hb1 : b ≤ 7/13)
    (hs : 0 ≤ s) (hs1 : s ≤ 1/20) : smallT b s < 5/2 := by
  have hb0 : 0 < b := by linarith
  have hD := smallD_lower hb hb1 hs hs1
  have hp : 0 < b*(4-3*b) := mul_pos hb0 (by linarith)
  have hq : 0 ≤ s*(10*b+32-25*s) := mul_nonneg hs (by linarith)
  have hid : 5*smallD b s-2*smallN b s = b*(4-3*b)+s*(10*b+32-25*s) := by
    dsimp [smallD,smallN]; ring
  dsimp [smallT]
  rw [div_lt_iff₀ (by linarith : 0 < smallD b s)]
  nlinarith only [hp,hq,hid]

private theorem smallT_hasDerivAt {b s : ℝ} (hD : smallD b s ≠ 0) :
    HasDerivAt (fun b ↦ smallT b s)
      ((18*b-10*s+8-smallT b s*(6*b-2*s+4))/smallD b s) b := by
  have hN : HasDerivAt (fun b ↦ smallN b s) (18*b-10*s+8) b := by
    convert (((((hasDerivAt_id' b).pow 2).const_mul 9).sub
      ((hasDerivAt_id' b).mul_const (10*s))).sub_const (5*s^2)).add
      (((hasDerivAt_id' b).const_mul 8).add_const (4*s)) using 1
    · funext b; dsimp [smallN]; ring
    · ring
  have hD' : HasDerivAt (fun b ↦ smallD b s) (6*b-2*s+4) b := by
    convert (((((hasDerivAt_id' b).pow 2).const_mul 3).sub
      ((hasDerivAt_id' b).mul_const (2*s))).sub_const (7*s^2)).add
      (((hasDerivAt_id' b).const_mul 4).add_const (8*s)) using 1
    · funext b; dsimp [smallD]; ring
    · ring
  convert hN.div hD' hD using 1
  · rfl
  · dsimp [smallT]
    field_simp

private theorem smallT_deriv_upper {b s : ℝ} (hb : 9/20 ≤ b) (hb1 : b ≤ 7/13)
    (hs : 0 ≤ s) (hs1 : s ≤ 1/20) :
    (18*b-10*s+8-smallT b s*(6*b-2*s+4))/smallD b s < 3 := by
  have hD := smallD_lower hb hb1 hs hs1
  have hT := smallT_lower hb hb1 hs hs1
  have hNb : 18*b-10*s+8 < 18 := by linarith
  have hDb : 13/2 < 6*b-2*s+4 := by linarith
  have hm : (17/10)*(13/2) < smallT b s*(6*b-2*s+4) :=
    mul_lt_mul (by linarith : (17/10:ℝ) < smallT b s) hDb.le (by norm_num) (by linarith)
  rw [div_lt_iff₀ (by linarith : 0 < smallD b s)]
  linarith only [hD,hNb,hm]

private noncomputable def smallTb (b s : ℝ) : ℝ :=
  (18*b-10*s+8-smallT b s*(6*b-2*s+4))/smallD b s
private noncomputable def smallM (l z : ℝ) : ℝ :=
  1+(z-l*(3-2*z))/(z*(1-l*z))
private noncomputable def smallMell (l z : ℝ) : ℝ :=
  (z-1)*(z+3)/(z*(1-l*z)^2)
private noncomputable def smallS (l z : ℝ) : ℝ :=
  2*l*smallT (1-l*(3-2*z)) (1-z)-smallM l z
private noncomputable def smallSell (l z : ℝ) : ℝ :=
  2*(smallT (1-l*(3-2*z)) (1-z)-l*(3-2*z)*smallTb (1-l*(3-2*z)) (1-z))-smallMell l z

private theorem small_box {l z : ℝ} (hl : 6/13 ≤ l) (hl1 : l ≤ 1/2)
    (hz : 19/20 ≤ z) (hz1 : z ≤ 1) :
    9/20 ≤ 1-l*(3-2*z) ∧ 1-l*(3-2*z) ≤ 7/13 ∧
    0 < l*(3-2*z) ∧ l*(3-2*z) ≤ 11/20 ∧ 0 < z ∧ 0 < 1-l*z := by
  have hl0 : 0 < l := by linarith
  have ha : 1 ≤ 3-2*z := by linarith
  have ha1 : 3-2*z ≤ 11/10 := by linarith
  have hp : 6/13 ≤ l*(3-2*z) := hl.trans (le_mul_of_one_le_right hl0.le ha)
  have hp1 : l*(3-2*z) ≤ 11/20 := by
    have h := mul_le_mul hl1 ha1 (by linarith : 0 ≤ 3-2*z) (by norm_num : (0:ℝ) ≤ 1/2)
    norm_num at h ⊢
    exact h
  have hprod : l*z ≤ 1/2 := (mul_le_of_le_one_right hl0.le hz1).trans hl1
  exact ⟨by linarith,by linarith,by linarith,hp1,by linarith,by linarith⟩

private theorem smallM_hasDerivAt {l z : ℝ} (hz : z ≠ 0) (hd : 1-l*z ≠ 0) :
    HasDerivAt (fun l ↦ smallM l z) (smallMell l z) l := by
  have hn := ((hasDerivAt_id' l).mul_const (3-2*z)).const_sub z
  have hden := (((hasDerivAt_id' l).mul_const z).const_sub 1).const_mul z
  have h := (hn.div hden (mul_ne_zero hz hd)).const_add 1
  convert h using 1
  · rfl
  · dsimp [smallMell]
    field_simp
    ring

private theorem smallS_hasDerivAt {l z : ℝ} (hl : 6/13 ≤ l) (hl1 : l ≤ 1/2)
    (hz : 19/20 ≤ z) (hz1 : z ≤ 1) :
    HasDerivAt (fun l ↦ smallS l z) (smallSell l z) l := by
  obtain ⟨hb,hb1,-,-,hz0,hd⟩ := small_box hl hl1 hz hz1
  have hD : 0 < smallD (1-l*(3-2*z)) (1-z) :=
    lt_trans (by norm_num) (smallD_lower (s := 1-z) hb hb1 (by linarith) (by linarith))
  have hinner := ((hasDerivAt_id' l).mul_const (3-2*z)).const_sub 1
  have hT := (smallT_hasDerivAt hD.ne').comp l hinner
  have h := (((hasDerivAt_id' l).const_mul 2).mul hT).sub
    (smallM_hasDerivAt hz0.ne' hd.ne')
  convert h using 1
  · rfl
  · dsimp [smallSell,smallTb]
    ring

private theorem smallSell_pos {l z : ℝ} (hl : 6/13 ≤ l) (hl1 : l ≤ 1/2)
    (hz : 19/20 ≤ z) (hz1 : z ≤ 1) : 0 < smallSell l z := by
  obtain ⟨hb,hb1,hp,hp1,hz0,hd⟩ := small_box hl hl1 hz hz1
  have hT := smallT_lower (s := 1-z) hb hb1 (by linarith) (by linarith)
  have hTb := smallT_deriv_upper (s := 1-z) hb hb1 (by linarith) (by linarith)
  change smallTb (1-l*(3-2*z)) (1-z) < 3 at hTb
  have hm := mul_lt_mul_of_pos_left hTb hp
  have hM : smallMell l z ≤ 0 := by
    unfold smallMell
    exact div_nonpos_of_nonpos_of_nonneg
      (mul_nonpos_of_nonpos_of_nonneg (by linarith) (by linarith)) (by positivity)
  dsimp only [smallSell]
  nlinarith only [hT,hm,hp1,hM]

private theorem smallS_ell_mono {l z : ℝ} (hl : 6/13 ≤ l) (hl1 : l ≤ 1/2)
    (hz : 19/20 ≤ z) (hz1 : z ≤ 1) : smallS (6/13) z ≤ smallS l z := by
  exact ss_le_of_deriv (f := fun l ↦ smallS l z) (f' := fun l ↦ smallSell l z) hl
    (fun k hk ↦ smallS_hasDerivAt hk.1 (hk.2.trans hl1) hz hz1)
    (fun k hk ↦ (smallSell_pos hk.1.le (hk.2.le.trans hl1) hz hz1).le)

private theorem smallN_edge (z : ℝ) :
    smallN (1-(6/13)*(3-2*z)) (1-z) =
      (1169-2994*(1-z)+2011*(1-z)^2)/169 := by dsimp [smallN]; ring
private theorem smallD_edge (z : ℝ) :
    smallD (1-(6/13)*(3-2*z)) (1-z) =
      (511+42*(1-z)-439*(1-z)^2)/169 := by dsimp [smallD]; ring
private noncomputable def smallTz (z : ℝ) : ℝ :=
  ((2994-4022*(1-z))/169-smallT (1-(6/13)*(3-2*z)) (1-z)*
    ((878*(1-z)-42)/169))/smallD (1-(6/13)*(3-2*z)) (1-z)
private noncomputable def smallMz (z : ℝ) : ℝ :=
  6*(25*z^2-36*z+39)/(z^2*(13-6*z)^2)

private theorem smallT_edge_hasDerivAt {z : ℝ} (hz : 19/20 ≤ z) (hz1 : z ≤ 1) :
    HasDerivAt (fun z ↦ smallT (1-(6/13)*(3-2*z)) (1-z)) (smallTz z) z := by
  obtain ⟨hb,hb1,-,-,-,-⟩ := small_box (by norm_num : (6/13:ℝ) ≤ 6/13)
    (by norm_num : (6/13:ℝ) ≤ 1/2) hz hz1
  have hD : 0 < smallD (1-(6/13)*(3-2*z)) (1-z) :=
    lt_trans (by norm_num) (smallD_lower (s := 1-z) hb hb1 (by linarith) (by linarith))
  have hs := (hasDerivAt_id' z).const_sub 1
  have hN : HasDerivAt (fun z ↦ smallN (1-(6/13)*(3-2*z)) (1-z))
      ((2994-4022*(1-z))/169) z := by
    convert (((hs.const_mul 2994).const_sub 1169).add ((hs.pow 2).const_mul 2011)).div_const 169 using 1
    · funext z; rw [smallN_edge]; rfl
    · ring
  have hD' : HasDerivAt (fun z ↦ smallD (1-(6/13)*(3-2*z)) (1-z))
      ((878*(1-z)-42)/169) z := by
    convert ((((hs.const_mul 42).add_const 511).sub ((hs.pow 2).const_mul 439))).div_const 169 using 1
    · funext z; rw [smallD_edge]
      simp only [Pi.sub_apply,Pi.pow_apply]
      ring
    · ring
  convert hN.div hD' hD.ne' using 1
  · rfl
  · dsimp only [smallTz,smallT]
    generalize smallN (1-(6/13)*(3-2*z)) (1-z) = Nv
    generalize smallD (1-(6/13)*(3-2*z)) (1-z) = Dv at hD ⊢
    field_simp

private theorem smallTz_lower {z : ℝ} (hz : 19/20 ≤ z) (hz1 : z ≤ 1) : 5 < smallTz z := by
  obtain ⟨hb,hb1,-,-,-,-⟩ := small_box (by norm_num : (6/13:ℝ) ≤ 6/13)
    (by norm_num : (6/13:ℝ) ≤ 1/2) hz hz1
  have hD := smallD_lower (s := 1-z) hb hb1 (by linarith) (by linarith)
  have hT := smallT_upper (s := 1-z) hb hb1 (by linarith) (by linarith)
  have hT0 := smallT_lower (s := 1-z) hb hb1 (by linarith) (by linarith)
  have hNz : 16 < (2994-4022*(1-z))/169 := by linarith
  have hDz : (878*(1-z)-42)/169 < 1/8 := by linarith
  have hDu : smallD (1-(6/13)*(3-2*z)) (1-z) < 31/10 := by
    rw [smallD_edge]
    nlinarith only [hz,sq_nonneg (1-z)]
  have hprod : smallT (1-(6/13)*(3-2*z)) (1-z)*((878*(1-z)-42)/169) < 5/16 := by
    by_cases hsign : 0 < (878*(1-z)-42)/169
    · have hm := mul_lt_mul_of_pos_right hT hsign
      nlinarith only [hm,hDz]
    · have hm := mul_nonpos_of_nonneg_of_nonpos
        (by linarith : 0 ≤ smallT (1-(6/13)*(3-2*z)) (1-z)) (le_of_not_gt hsign)
      linarith only [hm]
  unfold smallTz
  rw [lt_div_iff₀ (by linarith : 0 < smallD (1-(6/13)*(3-2*z)) (1-z))]
  linarith only [hNz,hprod,hDu]

private theorem smallM_edge_hasDerivAt {z : ℝ} (hz : 0 < z) (hz1 : z ≤ 1) :
    HasDerivAt (smallM (6/13)) (smallMz z) z := by
  have hd : 0 < 1-(6/13)*z := by linarith
  have hn := (hasDerivAt_id' z).sub
    ((((hasDerivAt_id' z).const_mul 2).const_sub 3).const_mul (6/13))
  have hden := (hasDerivAt_id' z).mul (((hasDerivAt_id' z).const_mul (6/13)).const_sub 1)
  convert (hn.div hden (mul_pos hz hd).ne').const_add 1 using 1
  · rfl
  · unfold smallMz
    simp only [Pi.sub_apply,Pi.mul_apply]
    field_simp
    ring

private theorem smallMz_upper {z : ℝ} (hz : 19/20 ≤ z) (hz1 : z ≤ 1) : smallMz z < 4 := by
  have hz0 : 0 < z := by linarith
  have hd : 0 < 13-6*z := by linarith
  have hp := mul_nonneg (by linarith : 0 ≤ 1-z) (by linarith : 0 ≤ 25*z-11)
  have hnum : 6*(25*z^2-36*z+39) ≤ 168 := by nlinarith only [hp]
  have hbase : 13/2 < z*(13-6*z) := by
    have hm := mul_le_mul hz (by linarith : (7:ℝ) ≤ 13-6*z)
      (by norm_num : (0:ℝ) ≤ 7) hz0.le
    nlinarith only [hm]
  have hsq : 169/4 < (z*(13-6*z))^2 := by
    nlinarith only [hbase,sq_nonneg (z*(13-6*z)-13/2)]
  unfold smallMz
  rw [div_lt_iff₀ (by positivity : 0 < z^2*(13-6*z)^2)]
  nlinarith only [hnum,hsq]

private theorem smallS_edge_mono {z : ℝ} (hz : 19/20 ≤ z) (hz1 : z ≤ 1) :
    smallS (6/13) (19/20) ≤ smallS (6/13) z := by
  exact ss_le_of_deriv (f := smallS (6/13)) (f' := fun z ↦ (12/13)*smallTz z-smallMz z) hz
    (fun w hw ↦ by
      have hd := ((smallT_edge_hasDerivAt hw.1 (hw.2.trans hz1)).const_mul (12/13)).sub
        (smallM_edge_hasDerivAt (by linarith [hw.1]) (hw.2.trans hz1))
      convert hd using 1
      funext w
      dsimp [smallS]
      ring)
    (fun w hw ↦ by
      have ht := smallTz_lower hw.1.le (hw.2.le.trans hz1)
      have hm := smallMz_upper hw.1.le (hw.2.le.trans hz1)
      linarith only [ht,hm])

private theorem smallS_corner_pos : 0 < smallS (6/13) (19/20) := by
  have ht : 2 < smallT (1-(6/13)*(3-2*(19/20))) (1-19/20) := by
    norm_num [smallT,smallN,smallD]
  have hm : smallM (6/13) (19/20) < 11/6 := by norm_num [smallM]
  dsimp only [smallS]
  linarith only [ht,hm]

private theorem smallS_pos {l z : ℝ} (hl : 6/13 ≤ l) (hl1 : l ≤ 1/2)
    (hz : 19/20 ≤ z) (hz1 : z ≤ 1) : 0 < smallS l z :=
  lt_of_lt_of_le (lt_of_lt_of_le smallS_corner_pos (smallS_edge_mono hz hz1))
    (smallS_ell_mono hl hl1 hz hz1)

private theorem smallT_ratio {l z : ℝ} (hl : 6/13 ≤ l) (hl1 : l ≤ 1/2)
    (hz : 19/20 ≤ z) (hz1 : z ≤ 1) :
    ss_gapTiltRatio (l*(3-2*z)) z (3*(z-l*(3-2*z))/(1+l*(3-2*z)+4*(z-l*(3-2*z)))) =
      smallT (1-l*(3-2*z)) (1-z) := by
  obtain ⟨hb,hb1,hp,hp1,-,-⟩ := small_box hl hl1 hz hz1
  let p := l*(3-2*z)
  let E := 1+p+4*(z-p)
  let e := 3*(z-p)/E
  have hpz : p < z := by dsimp only [p]; linarith only [hp1,hz]
  have hE : 0 < E := by dsimp [E]; have hd : 0 < z-p := sub_pos.mpr hpz; positivity
  have hD : 0 < smallD (1-p) (1-z) :=
    lt_trans (by norm_num) (smallD_lower (s := 1-z) hb hb1 (by linarith) (by linarith))
  have hF : ss_gapTiltFirst p z e = smallD (1-p) (1-z)/(12*E) := by
    dsimp only [ss_gapTiltFirst,e,smallD]
    field_simp
    dsimp [E]
    ring
  have hL : ss_gapTiltMass p z e-ss_gapTiltFirst p z e = smallN (1-p) (1-z)/(12*E) := by
    dsimp only [ss_gapTiltMass,ss_gapTiltFirst,e,smallN]
    field_simp
    dsimp [E]
    ring
  change ss_gapTiltRatio p z e = smallT (1-p) (1-z)
  unfold ss_gapTiltRatio
  rw [hL,hF]
  unfold smallT
  field_simp

private theorem smallHalf_admissible {p z : ℝ} (hp : 0 < p) (hpz : p < z) (hz : z ≤ 1) :
    (z-p)/2 ≤ 3*(z-p)/(1+p+4*(z-p)) := by
  have hd : 0 < z-p := sub_pos.mpr hpz
  have hden : 0 < 1+p+4*(z-p) := by positivity
  rw [le_div_iff₀ hden]
  have hm := mul_nonneg hd.le (show 0 ≤ 6-(1+p+4*(z-p)) by linarith only [hp,hz])
  nlinarith only [hm]

private theorem smallHalf_normalized {a t : ℝ} (ha : 0 < a) (ha1 : a < 1)
    (ht : 0 ≤ t) (ht8 : t < 1/8) :
    0 < ss_gapTiltRatio (1-a+a*t) (1-a*t) (((1-a*t)-(1-a+a*t))/2)*
      (1-a*t)*(1/(1-a)-(1-a*t))-
      ((2*(1-a*t)-(1-a+a*t))/(1-a)-(1-a*t)^2) := by
  have hD : 0 < 4*a*t^2+4*t-a+4 := by
    have hsq : 0 ≤ 4*a*t^2 := by positivity
    linarith
  have hF : ss_gapTiltFirst (1-a+a*t) (1-a*t) (((1-a*t)-(1-a+a*t))/2) =
      a*(4*a*t^2+4*t-a+4)/24 := by unfold ss_gapTiltFirst; ring
  have he : ss_gapTiltRatio (1-a+a*t) (1-a*t) (((1-a*t)-(1-a+a*t))/2)*
      (1-a*t)*(1/(1-a)-(1-a*t))-
      ((2*(1-a*t)-(1-a+a*t))/(1-a)-(1-a*t)^2) =
      a^2*(1-2*t)/((1-a)*(4*a*t^2+4*t-a+4))*
      (1-6*t-6*t^2-2*a*(1-a)*t^3) := by
    unfold ss_gapTiltRatio
    rw [hF]
    unfold ss_gapTiltMass
    generalize hpoly : 4*a*t^2+4*t-a+4 = Dv at hD ⊢
    field_simp
    subst Dv
    ring
  have hA : a*(1-a) ≤ 1/4 := by nlinarith only [sq_nonneg (a-1/2)]
  have h2 : t^2 ≤ 1/64 := by
    have h := pow_le_pow_left₀ ht ht8.le 2
    norm_num at h ⊢
    exact h
  have h3 : t^3 ≤ 1/512 := by
    have h := pow_le_pow_left₀ ht ht8.le 3
    norm_num at h ⊢
    exact h
  have hm := mul_le_mul hA h3 (by positivity : 0 ≤ t^3) (by norm_num : (0:ℝ) ≤ 1/4)
  have hbracket : 0 < 1-6*t-6*t^2-2*a*(1-a)*t^3 := by
    nlinarith only [ht8,h2,hm]
  rw [he]
  have h1 : 0 < 1-a := by linarith
  have ht1 : 0 < 1-2*t := by linarith
  positivity

private theorem smallHalf_contact {x z : ℝ} (hx : 16/9 ≤ x) (_hx2 : x ≤ 2)
    (hz : 19/20 ≤ z) (hz1 : z ≤ 1) :
    0 < ss_gapTiltRatio (1/x+1-z) z ((z-(1/x+1-z))/2)*z*(x-z)-
      ((2*z-(1/x+1-z))*x-z^2) := by
  have hx0 : 0 < x := by linarith
  have hi : 0 < 1/x := by positivity
  have hi1 : 1/x ≤ 9/16 := by
    have h := one_div_le_one_div_of_le (by norm_num : (0:ℝ) < 16/9) hx
    norm_num at h
    simpa only [one_div] using h
  let a := 1-1/x
  let t := (1-z)/a
  have ha : 0 < a := by dsimp [a]; linarith
  have ha1 : a < 1 := by dsimp [a]; linarith
  have ha0 : 7/16 ≤ a := by dsimp [a]; linarith
  have ht : 0 ≤ t := div_nonneg (by linarith) ha.le
  have het : a*t = 1-z := by dsimp [t]; field_simp
  have htbound : t ≤ 4/35 := by
    have hm := mul_le_mul_of_nonneg_right ha0 ht
    linarith only [hm,het,hz]
  have ht8 : t < 1/8 := by linarith only [htbound]
  have hxp : x = 1/(1-a) := by dsimp [a]; field_simp; ring
  have hzp : z = 1-a*t := by linarith only [het]
  have hpp : 1/x+1-z = 1-a+a*t := by dsimp [a] at het ⊢; linarith only [het]
  convert smallHalf_normalized ha ha1 ht ht8 using 1
  rw [hpp,hzp,hxp]
  ring

/-- The half-tilted linear weight gives the contact inequality for the unit-slope
barrier on the middle range of the small box. -/
theorem ss_small_contact_one {x z : ℝ} (hx : 16/9 ≤ x) (hx2 : x ≤ 2)
    (hz : 19/20 ≤ z) (hz1 : z ≤ 1) :
    (m2Sec (1/x+1-z) 1 z-ss_gB 1 z)*((2*z-(1/x+1-z))*x-z^2) <
      (ss_gB 1 (1/x+1-z)-m2Sec (1/x+1-z) 1 z)*z*(x-z) := by
  have hx0 : 0 < x := by linarith
  have hz0 : 0 < z := by linarith
  have hp : 0 < 1/x+1-z := by
    have hi : 0 < 1/x := by positivity
    linarith
  have hi1 : 1/x ≤ 9/16 := by
    have h := one_div_le_one_div_of_le (by norm_num : (0:ℝ) < 16/9) hx
    norm_num at h
    simpa only [one_div] using h
  have hpz : 1/x+1-z < z := by linarith only [hi1,hz]
  have hd : 0 < x-z := by linarith
  have hR := ss_gap_ratio_tilted hp hpz hz1 (show 0 ≤ (z-(1/x+1-z))/2 by linarith)
    (smallHalf_admissible hp hpz hz1)
  have hc := smallHalf_contact hx hx2 hz hz1
  simpa only [one_mul] using ord_upper_contact_of_ratio (k := 1) hp hpz hz1 (by positivity)
    hR (by simpa only [one_mul] using hc)

/-- The maximal tilt gives the contact inequality on the large range of the
small box. Monotonicity in both variables reduces the sign to one corner. -/
theorem ss_small_contact_max {x z : ℝ} (hx : 2 ≤ x) (hx2 : x ≤ 13/6)
    (hz : 19/20 ≤ z) (hz1 : z ≤ 1) :
    (m2Sec ((3-2*z)/x) 1 z-ss_gB 1 z)*((2*z-(3-2*z)/x)*x-z^2) <
      (2/x)*(ss_gB 1 ((3-2*z)/x)-m2Sec ((3-2*z)/x) 1 z)*z*(x-z) := by
  have hx0 : 0 < x := by linarith
  let l := 1/x
  have hl : 6/13 ≤ l := by
    have h := one_div_le_one_div_of_le hx0 hx2
    norm_num at h
    simpa only [l,one_div] using h
  have hl1 : l ≤ 1/2 := one_div_le_one_div_of_le (by norm_num) hx
  obtain ⟨hb,hb1,hp,hp1,hz0,hd⟩ := small_box hl hl1 hz hz1
  have hpz : l*(3-2*z) < z := by linarith only [hp1,hz]
  have hP : (3-2*z)/x = l*(3-2*z) := by dsimp [l]; ring
  rw [hP]
  have hE : 0 < 1+l*(3-2*z)+4*(z-l*(3-2*z)) := by
    have hgap : 0 < z-l*(3-2*z) := sub_pos.mpr hpz
    positivity
  have hR := ss_gap_ratio_tilted hp hpz hz1
    (show 0 ≤ 3*(z-l*(3-2*z))/(1+l*(3-2*z)+4*(z-l*(3-2*z))) by positivity) le_rfl
  rw [smallT_ratio hl hl1 hz hz1] at hR
  have hxz : 0 < x-z := by linarith
  have hden : 1-l*z = (x-z)/x := by dsimp [l]; field_simp
  have he : (2/x)*smallT (1-l*(3-2*z)) (1-z)*z*(x-z)-
      ((2*z-l*(3-2*z))*x-z^2) = z*(x-z)*smallS l z := by
    dsimp only [smallS]
    generalize smallT (1-l*(3-2*z)) (1-z) = Tv
    dsimp only [smallM]
    rw [hden]
    dsimp [l]
    field_simp
    ring
  have hc : 0 < (2/x)*smallT (1-l*(3-2*z)) (1-z)*z*(x-z)-
      ((2*z-l*(3-2*z))*x-z^2) := by
    rw [he]
    exact mul_pos (mul_pos hz0 hxz) (smallS_pos hl hl1 hz hz1)
  exact ord_upper_contact_of_ratio (k := 2/x) hp hpz hz1 (by positivity) hR hc

end SmoothedOctagon
