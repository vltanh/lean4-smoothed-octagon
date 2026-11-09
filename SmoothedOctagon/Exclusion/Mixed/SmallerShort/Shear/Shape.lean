module

public import SmoothedOctagon.Exclusion.Mixed.SmallerShort.Shear.Shape.J
public import SmoothedOctagon.Exclusion.Mixed.SmallerShort.Shear.Shape.TConcavity
public import SmoothedOctagon.Exclusion.Mixed.SmallerShort.Shear.Shape.TEndpoint
public import Mathlib.Analysis.Convex.Jensen

/-!
# Negativity of the duration endpoints on the full shape rectangle
-/

@[expose] public section

namespace SmoothedOctagon

open Set Real

private lemma s5_pole_quad_convex {al lo hi c0 c1 c2 : ℝ}
    (ha : 0 < al) (hlo : 0 < al+lo) (hc : 0 ≤ c2) :
    ConvexOn ℝ (Icc lo hi) (fun b => al/(al+b)+c0+c1*b+c2*b^2) := by
  let f := fun b => al/(al+b)+c0+c1*b+c2*b^2
  let f' := fun b => -al/(al+b)^2+c1+2*c2*b
  let f'' := fun b => 2*al/(al+b)^3+2*c2
  have h1 : ∀ b ∈ Icc lo hi, HasDerivAt f (f' b) b := by
    intro b hb
    have hd : 0 < al+b := by linarith only [hlo,hb.1]
    have hp := (hasDerivAt_const b al).div ((hasDerivAt_id' b).const_add al) hd.ne'
    have hh := ((hp.add_const c0).add ((hasDerivAt_id' b).const_mul c1)).add
      ((hasDerivAt_pow 2 b).const_mul c2)
    convert hh using 1; dsimp [f,f']; ring
  have h2 : ∀ b ∈ Icc lo hi, HasDerivAt f' (f'' b) b := by
    intro b hb
    have hd : 0 < al+b := by linarith only [hlo,hb.1]
    have hp := (hasDerivAt_const b (-al)).div
      (((hasDerivAt_id' b).const_add al).pow 2) (by change (al+b)^2 ≠ 0; positivity)
    have hh := (hp.add_const c1).add ((hasDerivAt_id' b).const_mul (2*c2))
    convert hh using 1; dsimp [f',f'']
    field_simp
    ring
  exact convexOn_of_hasDerivWithinAt2_nonneg (convex_Icc lo hi)
    (fun b hb => (h1 b hb).continuousAt.continuousWithinAt)
    (fun b hb => (h1 b (interior_subset hb)).hasDerivWithinAt)
    (fun b hb => (h2 b (interior_subset hb)).hasDerivWithinAt)
    (fun b hb => by
      have hbl := (interior_subset hb).1
      have hd : 0 < al+b := by linarith only [hlo,hbl]
      dsimp [f'']
      positivity)

/-- Convexity in the outer shape follows from the original quadratic transport and one pole. -/
theorem ssS5T_convexOn_beta {x al : ℝ} (hx : 2 ≤ x) (hal : 1 ≤ al) (hal1 : al ≤ 7/6) :
    ConvexOn ℝ (Icc x (20*x/19)) (fun be => ssS5T x be al) := by
  have hx0 : 0 < x := by linarith only [hx]
  have hal0 : 0 < al := by linarith only [hal]
  let q := (15/16)*ssQc x al
  let e := ssE0 x (19/25)
  let a := 1/al^2
  let eps := 1-a
  let g0 := (al^2+1+2*x)/al^2
  let g1 := 2*(x-al)/al^2
  let c0 := e+(19/25-1)+q*(4-2*ssA1 x 0 al (19/25)-1-ssA3 x 0 al (19/25))+
    2*q^2*(ssA2 x 0 al (19/25)-1)
  let c1 := (19/25-1)/al+q*(4/al+2*g1*(e+19/25))+
    2*q^2*(-2*(19/25)*g0*g1-g1*eps*e+g1*(2*(1+x)-1)*a-2/al)
  let c2 := 2*q^2/al^4*(4*(19/25)*(x-al)^2-al^2)
  have hq : 0 ≤ q := by dsimp [q,ssQc]; positivity
  have hg : 5/6 ≤ x-al := by linarith only [hx,hal1]
  have hg2 := pow_le_pow_left₀ (by norm_num : (0:ℝ) ≤ 5/6) hg 2
  have ha2 : al^2 ≤ (7/6)^2 := by nlinarith only [hal,hal1]
  have hbracket : 0 < 4*(19/25)*(x-al)^2-al^2 := by nlinarith only [hg2,ha2]
  have hc2 : 0 ≤ c2 := by dsimp [c2]; positivity
  have hconv := s5_pole_quad_convex (hi := 20*x/19) (c0 := c0) (c1 := c1) hal0
    (show 0 < al+x by positivity) hc2
  refine hconv.congr ?_
  intro be hbe
  have hb0 : 0 < be := hx0.trans_le hbe.1
  have hd : 0 < al+be := by positivity
  dsimp only [c0,c1,c2,e,a,eps,g0,g1,q]
  unfold ssS5T ssRA ssA1 ssA2 ssA3 ssDg
  field_simp
  ring

private theorem ssS5T_face_neg {x al k : ℝ}
    (hx : 2 ≤ x) (hx1 : x ≤ 13/6) (ha : 1 ≤ al) (ha1 : al ≤ 7/6)
    (hk : k = 1 ∨ k = 20/19) : ssS5T x (k*x) al < 0 := by
  have hx0 : 0 < x := by linarith only [hx]
  have hk0 : 0 < k := by rcases hk with rfl | rfl <;> norm_num
  have hb : x ≤ k*x := by
    rcases hk with rfl | rfl
    · simp
    · nlinarith only [hx]
  have hb1 : k*x ≤ 20*x/19 := by
    rcases hk with rfl | rfl
    · nlinarith only [hx]
    · ring_nf
      exact le_rfl
  have ht := ssS5T_le_tangent hx hx1 hb hb1 ha ha1
  have hd : s5First x (k*x) 1 = ssS5Ta x (k*x) :=
    (s5_T_hasDerivAt hx0 (mul_pos hk0 hx0) (by norm_num)).unique
      (te_original_alpha_deriv hx0 (mul_pos hk0 hx0))
  rw [hd] at ht
  obtain ⟨h0,h1⟩ := ssS5T_endpoint_tangents hx hx1 hk
  rcases le_total (ssS5Ta x (k*x)) 0 with hsign | hsign
  · have hm := mul_nonpos_of_nonneg_of_nonpos (sub_nonneg.mpr ha) hsign
    linarith only [ht,h0,hm]
  · have hm := mul_le_mul_of_nonneg_right
      (show al-1 ≤ 1/6 by linarith only [ha1]) hsign
    linarith only [ht,h1,hm]

/-- The original duration tangent is negative on the full enlarged shape rectangle. -/
theorem ssS5T_neg {x be al : ℝ} (hx : 2 ≤ x) (hx1 : x ≤ 13/6)
    (hb : x ≤ be) (hb1 : be ≤ 20*x/19) (ha : 1 ≤ al) (ha1 : al ≤ 7/6) :
    ssS5T x be al < 0 := by
  have hxx : x ≤ 20*x/19 := by linarith only [hx]
  have hconv := ssS5T_convexOn_beta hx ha ha1
  have hbound := hconv.le_max_of_mem_Icc ⟨le_rfl,hxx⟩ ⟨hxx,le_rfl⟩ ⟨hb,hb1⟩
  have hl : ssS5T x x al < 0 := by
    simpa only [one_mul] using ssS5T_face_neg hx hx1 ha ha1 (Or.inl rfl)
  have hu : ssS5T x (20*x/19) al < 0 := by
    simpa only [show (20/19:ℝ)*x = 20*x/19 by ring] using
      ssS5T_face_neg hx hx1 ha ha1 (Or.inr rfl)
  exact lt_of_le_of_lt hbound (max_lt hl hu)

end SmoothedOctagon
