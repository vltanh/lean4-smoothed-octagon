module

public import SmoothedOctagon.Exclusion.Mixed.Nonshort.HighRatio.Quadratic
public import SmoothedOctagon.Exclusion.Mixed.Nonshort.HighRatio.Secant

/-!
# The incoming switching floor on the raised boundary

Moving both secant endpoints lowers the incoming floor. Its midpoint Jensen
bound supplies the positive slack used by the transport quadratic.
-/

@[expose] public section

namespace SmoothedOctagon
open Set Real

/-- The switching integrand decreases on its positive left half. -/
theorem mhtg_left_antitone {D s t : ℝ} (hD : 0 < D) (hs : 0 ≤ s) (hst : s ≤ t) (ht : t ≤ D) :
    m2g D t ≤ m2g D s := by
  have ht0 : 0 ≤ t := le_trans hs hst
  have hsD : s ≤ D := le_trans hst ht
  have hprod : s*t ≤ D^2 := by
    calc s*t ≤ D*t := mul_le_mul_of_nonneg_right hsD ht0
      _ ≤ D*D := mul_le_mul_of_nonneg_left ht hD.le
      _ = D^2 := by ring
  have hid := nsr_m2g_sub (B := D) (s1 := s) (s2 := t)
    (by linarith only [hD,hs]) (by linarith only [hD,ht0])
  have hp : 0 ≤ D*(t-s)*(D^2-s*t)/((D+s)^2*(D+t)^2) := by
    apply div_nonneg
    · exact mul_nonneg (mul_nonneg hD.le (sub_nonneg.mpr hst)) (sub_nonneg.mpr hprod)
    · positivity
  linarith only [hid,hp]

/-- Moving both ends of a secant to the right lowers its average of the decreasing integrand. -/
theorem mhtSec_endpoints_antitone {A0 P0 A1 P1 D : ℝ}
    (hA0 : 0 < A0) (hA1 : 0 < A1) (h0 : A0 < P0) (h1 : A1 < P1)
    (hA : A0 ≤ A1) (hP : P0 ≤ P1) (hPD : P1 ≤ D) :
    m2Sec A1 D P1 ≤ m2Sec A0 D P0 := by
  have hD : 0 < D := by linarith only [hA1,h1,hPD]
  let p0 : ℝ → ℝ := fun θ => A0+θ*(P0-A0)
  let p1 : ℝ → ℝ := fun θ => A1+θ*(P1-A1)
  let F : ℝ → ℝ := fun θ =>
    (nsrG D (p1 θ)-nsrG D A1)/(P1-A1)-(nsrG D (p0 θ)-nsrG D A0)/(P0-A0)
  have hrange : ∀ θ ∈ Icc (0:ℝ) 1,
      0 < p0 θ ∧ p0 θ ≤ p1 θ ∧ p1 θ ≤ D := by
    intro θ hθ
    have h0p : 0 < p0 θ := by dsimp [p0]; nlinarith only [hA0,h0,hθ.1]
    have h1p : p1 θ ≤ P1 := by dsimp [p1]; nlinarith only [h1,hθ.2]
    have hcomp : p0 θ ≤ p1 θ := by
      have hp := add_nonneg (mul_nonneg (by linarith only [hθ.2] : 0≤1-θ) (sub_nonneg.mpr hA))
        (mul_nonneg hθ.1 (sub_nonneg.mpr hP))
      dsimp [p0,p1]
      nlinarith only [hp]
    exact ⟨h0p,hcomp,le_trans h1p hPD⟩
  have hd : ∀ θ ∈ Icc (0:ℝ) 1,
      HasDerivAt F (m2g D (p1 θ)-m2g D (p0 θ)) θ := by
    intro θ hθ
    obtain ⟨hp0,hp01,_⟩ := hrange θ hθ
    have hp1 : 0 < p1 θ := lt_of_lt_of_le hp0 hp01
    have hlin0 := ((hasDerivAt_id' θ).mul_const (P0-A0)).const_add A0
    have hlin1 := ((hasDerivAt_id' θ).mul_const (P1-A1)).const_add A1
    have h := (((nsr_hasDerivAt_G (B := D) (s := p1 θ)
      (by linarith only [hD,hp1])).comp θ hlin1).sub_const (nsrG D A1)).div_const (P1-A1)
    have h' := (((nsr_hasDerivAt_G (B := D) (s := p0 θ)
      (by linarith only [hD,hp0])).comp θ hlin0).sub_const (nsrG D A0)).div_const (P0-A0)
    refine (h.sub h').congr_deriv ?_
    have hn0 : P0-A0 ≠ 0 := by linarith only [h0]
    have hn1 : P1-A1 ≠ 0 := by linarith only [h1]
    field_simp
  have hm : AntitoneOn F (Icc (0:ℝ) 1) := by
    apply antitoneOn_of_deriv_nonpos (convex_Icc 0 1)
    · exact fun θ hθ => (hd θ hθ).continuousAt.continuousWithinAt
    · exact fun θ hθ => (hd θ (interior_subset hθ)).differentiableAt.differentiableWithinAt
    · intro θ hθ
      rw [(hd θ (interior_subset hθ)).deriv]
      obtain ⟨hp0,hp01,hp1D⟩ := hrange θ (interior_subset hθ)
      exact sub_nonpos.mpr (mhtg_left_antitone hD hp0.le hp01 hp1D)
  have hh := hm (left_mem_Icc.mpr zero_le_one) (right_mem_Icc.mpr zero_le_one) zero_le_one
  have hP0 : 0 < P0 := lt_trans hA0 h0
  have hP1 : 0 < P1 := lt_trans hA1 h1
  rw [nsr_sec_eq_G hA1.le hD hP1.le (ne_of_lt h1),nsr_sec_eq_G hA0.le hD hP0.le (ne_of_lt h0)]
  dsimp [F,p0,p1] at hh
  norm_num only [zero_mul,one_mul,add_zero,add_sub_cancel,sub_self,zero_div,sub_zero] at hh
  linarith only [hh]

/-- The original missing-control floor decreases along the raised-C path whenC≤D. -/
theorem mhtIncoming_floor_anti {C0 C D q : ℝ} (hC0 : 0 < C0) (hC : C0 ≤ C)
    (hCD : C ≤ D) (hq : 1 < q) (hqW : q < (C0+D)/D) :
    m2F (D/(D+C)) q ≤ m2F (D/(D+C0)) q := by
  have hD : 0 < D := by linarith only [hC0,hC,hCD]
  have hc : 0 < C := lt_of_lt_of_le hC0 hC
  have hq0 : 0 < q := by linarith only [hq]
  have hA0 : 0 < (D+C0)/q-D := by
    have hh : q*D < C0+D := (lt_div_iff₀ hD).mp hqW
    rw [sub_pos,lt_div_iff₀ hq0]
    nlinarith only [hh]
  have hA : (D+C0)/q-D ≤ (D+C)/q-D := by
    exact sub_le_sub_right ((div_le_div_iff_of_pos_right hq0).mpr (by linarith only [hC])) D
  have hA1 : 0 < (D+C)/q-D := lt_of_lt_of_le hA0 hA
  have h0 : (D+C0)/q-D < C0 := by
    rw [sub_lt_iff_lt_add,div_lt_iff₀ hq0]
    have hh := mul_lt_mul_of_pos_left hq (by linarith only [hD,hC0] : 0<D+C0)
    nlinarith only [hh]
  have h1 : (D+C)/q-D < C := by
    rw [sub_lt_iff_lt_add,div_lt_iff₀ hq0]
    have hh := mul_lt_mul_of_pos_left hq (by linarith only [hD,hc] : 0<D+C)
    nlinarith only [hh]
  rw [nsr_m2F_eq_sec hD hc hq,nsr_m2F_eq_sec hD hC0 hq]
  exact mhtSec_endpoints_antitone hA0 hA1 h0 h1 hA hC hCD

private theorem mhtI_convex_tangent {S : Set ℝ} {f : ℝ → ℝ} {m x d : ℝ}
    (hc : ConvexOn ℝ S f) (hm : m ∈ S) (hx : x ∈ S) (hd : HasDerivAt f d m) :
    f m+d*(x-m) ≤ f x := by
  rcases lt_trichotomy x m with hxm | hxm | hmx
  · have hs := hc.slope_le_of_hasDerivAt hx hm hxm hd
    rw [slope_def_field] at hs
    have hp := (div_le_iff₀ (sub_pos.mpr hxm)).mp hs
    linarith only [hp]
  · subst x; simp
  · have hs := hc.le_slope_of_hasDerivAt hm hx hmx hd
    rw [slope_def_field] at hs
    have hp := (le_div_iff₀ (sub_pos.mpr hmx)).mp hs
    linarith only [hp]

/-- Jensen's midpoint floor for the original switching secant. -/
theorem mhtSec_midpoint_floor {A C D : ℝ} (hA : 0 < A) (hAC : A < C) (hCD : C ≤ D) :
    m2g D ((A+C)/2) ≤ m2Sec A D C := by
  have hC : 0 < C := lt_trans hA hAC
  have hD : 0 < D := lt_of_lt_of_le hC hCD
  let m : ℝ := (A+C)/2
  have hm : m ∈ Icc A C := by dsimp [m]; constructor <;> linarith only [hAC]
  have hc : ConvexOn ℝ (Icc A C) (m2g D) := by
    apply convexOn_of_hasDerivWithinAt2_nonneg (convex_Icc A C)
      (f' := mhtg1 D) (f'' := mhtg2 D)
    · exact fun s hs => (mhtg_hasDerivAt_s (by linarith only [hD,hA,hs.1])).continuousAt.continuousWithinAt
    · exact fun s hs => (mhtg_hasDerivAt_s
        (by have := (interior_subset hs).1; linarith only [hD,hA,this])).hasDerivWithinAt
    · exact fun s hs => (mhtg1_hasDerivAt
        (by have := (interior_subset hs).1; linarith only [hD,hA,this])).hasDerivWithinAt
    · intro s hs
      have hs' := interior_subset hs
      unfold mhtg2
      apply div_nonneg
      · exact mul_nonneg (by positivity) (by linarith only [hs'.2,hCD,hD])
      · positivity
  let F : ℝ → ℝ := fun s => nsrG D s-m2g D m*s-mhtg1 D m*(s-m)^2/2
  have hd : ∀ s ∈ Icc A C,
      HasDerivAt F (m2g D s-m2g D m-mhtg1 D m*(s-m)) s := by
    intro s hs
    have hi := (hasDerivAt_id' s).sub_const m
    have h := ((nsr_hasDerivAt_G (B := D) (s := s) (by linarith only [hD,hA,hs.1])).sub
      ((hasDerivAt_id' s).const_mul (m2g D m))).sub (((hi.pow 2).const_mul (mhtg1 D m)).div_const 2)
    refine h.congr_deriv ?_
    norm_num only [Pi.pow_apply,Pi.mul_apply,id_eq]
    ring
  have hh := mhtS_le_of_deriv hAC.le hd (fun s hs => by
    have ht := mhtI_convex_tangent hc hm (Ioo_subset_Icc_self hs)
      (mhtg_hasDerivAt_s (by linarith only [hD,hA,hm.1] : 0<D+m))
    linarith only [ht])
  have hid := nsr_sec_eq_G hA.le hD hC.le (ne_of_lt hAC)
  rw [hid,le_div_iff₀ (sub_pos.mpr hAC)]
  dsimp [F,m] at hh
  nlinarith only [hh]

noncomputable def mhtIncomingJ (u z : ℝ) : ℝ :=
  ((u^2-u+1)/75)*(2-z)^2-(z+2*u/(u+6))^2

/-- The strict original incoming floor yields the positive Jensen slack used by the multiplier. -/
theorem mhtIncomingJ_pos {u q v : ℝ} (hu : u ∈ Icc (0:ℝ) (2/3)) (hq : 1 < q)
    (hqW : q < ((u+6)/2)/((u+3)/2))
    (hfloor : m2F (((u+3)/2)/((u+6)/2)) q ≤ v)
    (hv : v < 3/4+(u^2-u+1)/300) :
    0 < mhtIncomingJ u (1-1/q) := by
  let D : ℝ := (u+3)/2
  let W : ℝ := (u+6)/2
  let A : ℝ := W/q-D
  let z : ℝ := 1-1/q
  let m : ℝ := (A+3/2)/2
  have hD : 0 < D := by dsimp [D]; linarith only [hu.1]
  have hW : 0 < W := by dsimp [W]; linarith only [hu.1]
  have hq0 : 0 < q := by linarith only [hq]
  have hA : 0 < A := by
    have hh : q*D < W := (lt_div_iff₀ hD).mp hqW
    dsimp [A]
    rw [sub_pos,lt_div_iff₀ hq0]
    nlinarith only [hh]
  have hAC : A < 3/2 := by
    have hh : W/q < W := div_lt_self hW hq
    have hid : W-D=(3/2:ℝ) := by dsimp [W,D]; ring
    dsimp [A]
    linarith only [hh,hid]
  have hCD : (3/2:ℝ) ≤ D := by dsimp [D]; linarith only [hu.1]
  have hf := mhtSec_midpoint_floor hA hAC hCD
  have hF : m2F (D/W) q = m2Sec A D (3/2) := by
    have hi := nsr_m2F_eq_sec hD (by norm_num : (0:ℝ)<3/2) hq
    have hsum : D+3/2=W := by dsimp [D,W]; ring
    rw [hsum] at hi
    exact hi
  change m2F (D/W) q ≤ v at hfloor
  rw [hF] at hfloor
  have hmid : 0 < m := by dsimp [m]; linarith only [hA]
  have hz2 : 0 < 2-z := by
    dsimp [z]
    have hh : 0 < 1/q := one_div_pos.mpr hq0
    linarith only [hh]
  have hu6 : u+6 ≠ 0 := by linarith only [hu.1]
  have hdiff : D-m=W/2*(z+2*u/(u+6)) := by
    dsimp [D,m,A,W,z]
    field_simp
    ring
  have hsum : D+m=W/2*(2-z) := by dsimp [D,m,A,W,z]; ring
  have hratio : (D-m)/(D+m)=(z+2*u/(u+6))/(2-z) := by
    rw [hdiff,hsum]
    field_simp
  have hid : m2g D m=3/4+((D-m)/(D+m))^2/4 := by
    unfold m2g
    have hp : 0 < D+m := by linarith only [hD,hmid]
    field_simp
    ring
  rw [hratio] at hid
  have hvs : (z+2*u/(u+6))^2/(2-z)^2 < (u^2-u+1)/75 := by
    rw [div_pow] at hid
    have hh : m2g D m ≤ v := le_trans hf hfloor
    nlinarith only [hid,hh,hv]
  have hmul := (div_lt_iff₀ (sq_pos_of_pos hz2)).mp hvs
  change 0 < ((u^2-u+1)/75)*(2-z)^2-(z+2*u/(u+6))^2
  linarith only [hmul]

end SmoothedOctagon
