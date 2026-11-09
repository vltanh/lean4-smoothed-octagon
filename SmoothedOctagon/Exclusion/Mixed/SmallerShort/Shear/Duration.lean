module

public import SmoothedOctagon.Exclusion.Mixed.SmallerShort.Basic

/-!
# The exact duration tangent and its endpoint reduction
-/

@[expose] public section

namespace SmoothedOctagon

open Set Real

/-- The exact endpoint tangent of the concave duration term. -/
private lemma shr_log_recip_tangent {p q r : ℝ} (hq : 0 ≤ q) (hp : 0 < p)
    (hpq : 2*q ≤ p) (hpr : p ≤ r) :
    log (p/r)+q/p ≤ q/r+(1/r-q/r^2)*(p-r) := by
  have hr : 0 < r := hp.trans_le hpr
  let s := 1/r-q/r^2
  have hm := ss_le_of_deriv
    (f := fun z => log (z/r)+q/z-s*z)
    (f' := fun z => 1/z-q/z^2-s) hpr
    (fun z hz => ?_) (fun z hz => ?_)
  · have hrlog : log (r/r) = 0 := by rw [div_self hr.ne',log_one]
    rw [hrlog] at hm
    dsimp [s] at hm
    linarith only [hm]
  · have hz0 : 0 < z := hp.trans_le hz.1
    have hlog : HasDerivAt (fun z : ℝ => log (z/r)) (1/z) z := by
      have hh := ((hasDerivAt_id' z).div_const r).log (div_pos hz0 hr).ne'
      convert hh using 1
      field_simp
    have hrec : HasDerivAt (fun z : ℝ => q/z) (-q/z^2) z := by
      have hh := (hasDerivAt_const z q).div (hasDerivAt_id' z) hz0.ne'
      convert hh using 1; ring
    convert (hlog.add hrec).sub ((hasDerivAt_id' z).const_mul s) using 1; ring
  · have hz0 : 0 < z := hp.trans_le hz.1.le
    have hzr : z ≤ r := hz.2.le
    have hzq : 2*q ≤ z := hpq.trans hz.1.le
    have hpos : 0 ≤ r*z-q*(r+z) := by
      have hp1 := mul_nonneg hr.le (show 0 ≤ z-2*q by linarith only [hzq])
      have hp2 := mul_nonneg hq (show 0 ≤ r-z by linarith only [hzr])
      nlinarith only [hp1,hp2]
    have hid : 1/z-q/z^2-s = (r-z)*(r*z-q*(r+z))/(r^2*z^2) := by
      dsimp [s]
      field_simp
      ring
    rw [hid]
    exact div_nonneg (mul_nonneg (by linarith only [hzr]) hpos) (by positivity)

/-- The original residual is bounded by the two values of one affine tangent. -/
theorem shr_duration_endpoints {X A1 A2 A3 p q r : ℝ}
    (hq : 0 ≤ q) (hp : 0 < p) (hpq : 2*q ≤ p) (hpr : p ≤ r) :
    X+1-p*A1+log (p/r)+q*(p*A2+1/p-1-A3) ≤
      max (X+1-r*A1+q*(r*A2+1/r-1-A3))
        (X+q*(4/r-2*A1-1-A3)+2*q^2*(A2-1/r^2)) := by
  have hr : 0 < r := hp.trans_le hpr
  let J := X+1-r*A1+q*(r*A2+1/r-1-A3)
  let D := -A1+1/r+q*(A2-1/r^2)
  have ht : X+1-p*A1+log (p/r)+q*(p*A2+1/p-1-A3) ≤ J+D*(p-r) := by
    have hlog := shr_log_recip_tangent hq hp hpq hpr
    have hid : J+D*(p-r)-(X+1-p*A1+log (p/r)+q*(p*A2+1/p-1-A3)) =
        q/r+(1/r-q/r^2)*(p-r)-(log (p/r)+q/p) := by
      dsimp [J,D]
      field_simp
      ring
    linarith only [hlog,hid]
  have hT : J+D*(2*q-r) = X+q*(4/r-2*A1-1-A3)+2*q^2*(A2-1/r^2) := by
    dsimp [J,D]
    field_simp
    ring
  rcases le_or_gt 0 D with hD | hD
  · have hm := mul_nonpos_of_nonneg_of_nonpos hD (show p-r ≤ 0 by linarith only [hpr])
    have hJ : J+D*(p-r) ≤ J := by linarith only [hm]
    exact (ht.trans hJ).trans (le_max_left _ _)
  · have hm := mul_le_mul_of_nonpos_left hpq hD.le
    have hb : J+D*(p-r) ≤ J+D*(2*q-r) := by nlinarith only [hm]
    rw [hT] at hb
    exact (ht.trans hb).trans (le_max_right _ _)


/-- Affine scale motion and the increasing tangent endpoint reduce the whole residual. -/
theorem shr_residual_of_endpoints {X A1 A2 A3 p q qb r : ℝ}
    (hq : 0 ≤ q) (hqqb : q ≤ qb) (hqb : qb ≤ r/2)
    (hp : 0 < p) (hpq : 2*q ≤ p) (hpr : p ≤ r)
    (hA2 : 0 < A2) (hslope : 2*A1+1+A3 < 2/r)
    (hJ0 : X+1-r*A1 < 0)
    (hJ : X+1-r*A1+qb*(r*A2+1/r-1-A3) < 0)
    (hT : X+qb*(4/r-2*A1-1-A3)+2*qb^2*(A2-1/r^2) < 0) :
    X+1-p*A1+log (p/r)+q*(p*A2+1/p-1-A3) < 0 := by
  have hr : 0 < r := hp.trans_le hpr
  have hqb0 : 0 ≤ qb := hq.trans hqqb
  have hJq : X+1-r*A1+q*(r*A2+1/r-1-A3) < 0 := by
    rcases le_or_gt 0 (r*A2+1/r-1-A3) with hL | hL
    · have hm := mul_le_mul_of_nonneg_right hqqb hL
      linarith only [hm,hJ]
    · have hm := mul_nonpos_of_nonneg_of_nonpos hq hL.le
      linarith only [hm,hJ0]
  have hTq : X+q*(4/r-2*A1-1-A3)+2*q^2*(A2-1/r^2) < 0 := by
    have hsum : 0 ≤ qb+q := add_nonneg hqb0 hq
    have hsumr : qb+q ≤ r := by linarith only [hqqb,hqb]
    have hrat : 0 ≤ 2/r-2*(qb+q)/r^2 := by
      have hid : 2/r-2*(qb+q)/r^2 = 2*(r-(qb+q))/r^2 := by field_simp
      rw [hid]
      exact div_nonneg (by linarith only [hsumr]) (sq_nonneg r)
    have hpos := mul_nonneg hsum hA2.le
    have hs : 0 ≤ 4/r-2*A1-1-A3+2*(qb+q)*(A2-1/r^2) := by
      have hid : 4/r-2*A1-1-A3+2*(qb+q)*(A2-1/r^2) =
          (2/r-(2*A1+1+A3))+2*((qb+q)*A2)+(2/r-2*(qb+q)/r^2) := by ring
      rw [hid]
      linarith only [hrat,hpos,hslope]
    have hm := mul_nonneg (sub_nonneg.mpr hqqb) hs
    have hid : (X+qb*(4/r-2*A1-1-A3)+2*qb^2*(A2-1/r^2))-
        (X+q*(4/r-2*A1-1-A3)+2*q^2*(A2-1/r^2)) =
        (qb-q)*(4/r-2*A1-1-A3+2*(qb+q)*(A2-1/r^2)) := by ring
    linarith only [hm,hid,hT]
  exact (shr_duration_endpoints hq hp hpq hpr).trans_lt (max_lt hJq hTq)

end SmoothedOctagon
