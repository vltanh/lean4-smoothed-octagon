module

public import SmoothedOctagon.Exclusion.Mixed.SmallerShort.Window.LogSecant

/-!
# A natural global ceiling for the bridge norm
-/

@[expose] public section

namespace SmoothedOctagon

open Set Real

private lemma ss_log_natural_ceiling {R : ℝ} (hR : 0 < R) (hR1 : R < 1) :
    R*(24+24*R-R^3)/(2*(1+R)*(12+6*R-R^2)) < log (1+R) := by
  have h := ss_lt_of_deriv
    (f := fun t => log (1+t)-t*(24+24*t-t^3)/(2*(1+t)*(12+6*t-t^2)))
    (f' := fun t => t^4*(8+12*t-t^2)/(2*(1+t)^2*(12+6*t-t^2)^2))
    hR (fun t ht => ?_) (fun t ht => ?_)
  · norm_num at h
    linarith only [h]
  · have ht0 : 0 ≤ t := ht.1
    have ht1 : t < 1 := ht.2.trans_lt hR1
    have hd : 0 < 12+6*t-t^2 := by nlinarith only [ht0,ht1]
    have hS : 0 < 1+t := by positivity
    have hn : HasDerivAt (fun t : ℝ => t*(24+24*t-t^3))
        ((24+24*t-t^3)+t*(24-3*t^2)) t := by
      have h := (hasDerivAt_id' t).mul
        ((((hasDerivAt_id' t).const_mul 24).const_add 24).sub (hasDerivAt_pow 3 t))
      convert h using 1; simp only [Pi.sub_apply]; push_cast; ring
    have hdd : HasDerivAt (fun t : ℝ => 2*(1+t)*(12+6*t-t^2))
        (2*(12+6*t-t^2)+2*(1+t)*(6-2*t)) t := by
      have h := (((hasDerivAt_id' t).const_add 1).const_mul 2).mul
        ((((hasDerivAt_id' t).const_mul 6).const_add 12).sub (hasDerivAt_pow 2 t))
      convert h using 1; simp only [Pi.sub_apply]; push_cast; ring
    have hl : HasDerivAt (fun t : ℝ => log (1+t)) (1/(1+t)) t := by
      convert (((hasDerivAt_id' t).const_add 1).log hS.ne') using 1
    refine (hl.sub (hn.div hdd (by positivity))).congr_deriv ?_
    have hd' : 12+t*6-t^2 ≠ 0 := by linarith only [hd]
    field_simp [hd',hd.ne',hS.ne']
    ring
  · have ht0 : 0 < t := ht.1
    have ht1 : t < 1 := ht.2.trans hR1
    have hd : 0 < 12+6*t-t^2 := by nlinarith only [ht0,ht1]
    have hn : 0 < 8+12*t-t^2 := by nlinarith only [ht0,ht1]
    positivity

/-- The global natural ceiling from the logarithm's factored derivative. -/
theorem ss_V_lt_natural_ceiling {x : ℝ} (hx : 1 < x) :
    m2Sec 1 x x < 3/4+(x-1)^2/(17*x^2+26*x+5) := by
  have hx0 : 0 < x := by linarith only [hx]
  have hS : 0 < x+1 := by positivity
  have hxm : 0 < x-1 := by linarith only [hx]
  let R := (x-1)/(x+1)
  have hR : 0 < R := div_pos hxm hS
  have hR1 : R < 1 := by dsimp [R]; rw [div_lt_one hS]; linarith only [hx]
  have hlog := ss_log_natural_ceiling hR hR1
  have harg : 1+R = (x+x)/(1+x) := by dsimp [R]; field_simp; ring
  have hlogarg : log (1+R) = log ((x+x)/(1+x)) := congrArg log harg
  rw [hlogarg] at hlog
  rw [m2Sec_of_ne hx.ne]
  have hden : 0 < 12+6*R-R^2 := by nlinarith only [hR,hR1]
  have hid : 3/4+(x-1)^2/(17*x^2+26*x+5) =
      1+x^2/((1+x)*(x+x))-x/(x-1)*(R*(24+24*R-R^3)/(2*(1+R)*(12+6*R-R^2))) := by
    have heqden : 12+6*R-R^2 = (17*x^2+26*x+5)/(x+1)^2 := by
      dsimp [R]
      field_simp
      ring
    rw [heqden]
    dsimp [R]
    have hpoly : 0 < 17*x^2+26*x+5 := by positivity
    field_simp
    ring
  rw [hid]
  have hm := mul_lt_mul_of_pos_left hlog (div_pos hx0 hxm)
  linarith only [hm]

/-- The constant ceiling on the full closed S5 shape-ratio interval. -/
theorem ss_V_lt_small_shape_ceiling {x : ℝ} (hx : 2 ≤ x) (hx1 : x ≤ 13/6) :
    m2Sec 1 x x < 19/25 := by
  have hx0 : 0 < x := by linarith only [hx]
  have hcap := ss_V_lt_natural_ceiling (show 1 < x by linarith only [hx])
  have hfrac : (x-1)^2/(17*x^2+26*x+5) < 1/100 := by
    rw [div_lt_iff₀ (by positivity)]
    have hm := mul_nonneg (show 0 ≤ x-2 by linarith only [hx])
      (show 0 ≤ 13/6-x by linarith only [hx1])
    nlinarith only [hm,hx1]
  linarith only [hcap,hfrac]

end SmoothedOctagon
