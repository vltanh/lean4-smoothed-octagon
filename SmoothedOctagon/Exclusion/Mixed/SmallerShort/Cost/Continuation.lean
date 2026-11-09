module

public import SmoothedOctagon.Exclusion.Mixed.SmallerShort.Cost.Defs

/-!
# Explicit losses for central-scale score continuation

The tangent-curve score decreases under the physical shear inequality `2ν < -hR`.
Its three losses are controlled separately: anisotropy by displacement, squared shear
by the natural central bound, and the square-root ratio by positive elementary remainders.
The original half-angle identity converts their sum into the exact score derivative.
The shape bounds include zero displacement and use the original central shear.
-/

@[expose] public section

namespace SmoothedOctagon

open Real

private lemma cont_root_loss {a b : ℝ} (ha0 : 0 ≤ a) (ha1 : a ≤ 1)
    (hb0 : 0 ≤ b) (hb1 : b ≤ 1) :
    1 - √(1-b^2)/√(1+a^2) ≤ a^2/2+b^2 := by
  have ha2 : a^2 ≤ 1 := by nlinarith only [ha0,ha1]
  have hb2 : b^2 ≤ 1 := by nlinarith only [hb0,hb1]
  have hs : 0 < √(1+a^2) := by positivity
  have hss : (√(1+a^2))^2 = 1+a^2 := Real.sq_sqrt (by positivity)
  have hsq : (1-a^2/2)^2*(1+a^2) ≤ 1 := by
    have hp := mul_nonneg (sq_nonneg (a^2)) (show 0 ≤ 3-a^2 by linarith only [ha2])
    nlinarith only [hp]
  have htan : (1-a^2/2)*√(1+a^2) ≤ 1 := by
    have hnon : 0 ≤ (1-a^2/2)*√(1+a^2) := mul_nonneg (by linarith only [ha2]) hs.le
    nlinarith only [hsq,hss,hnon]
  have hinv : 1-a^2/2 ≤ 1/√(1+a^2) := (le_div_iff₀ hs).2 htan
  have hroot : 1-b^2 ≤ √(1-b^2) := by
    apply Real.le_sqrt_of_sq_le
    nlinarith only [mul_nonneg (sq_nonneg b) (show 0 ≤ 1-b^2 by linarith only [hb2])]
  have hprod := mul_le_mul hroot hinv (show 0 ≤ 1-a^2/2 by linarith only [ha2])
    (Real.sqrt_nonneg (1-b^2))
  have hcross := mul_nonneg (sq_nonneg a) (sq_nonneg b)
  rw [mul_one_div] at hprod
  nlinarith only [hprod,hcross]

private lemma cont_three_losses {R d A H J K : ℝ}
    (hR : 1/3 ≤ R) (hR1 : R ≤ 7/19) (hd1 : d ≤ 1/19)
    (hA : 0 ≤ A) (hAd : A ≤ 2*R*d/3) (hH : 0 < H) (hH1 : H < R^2)
    (hHR : 2*A ≤ H*R) (hJ : 0 < J)
    (hJ1 : J ≤ (9+R^2)/(2*(3+R^2)))
    (hK : K = A+2+2*(40/27)/J) :
    J*A + J*H^2/K + (161/54)*(1-√(1-(A/K)^2)/√(1+(A/H)^2)) < 3-2*J := by
  have hR0 : 0 < R := by linarith only [hR]
  have hR2 : R^2 < 1/7 := by nlinarith only [hR,hR1]
  have hJ32 : J ≤ 3/2 := by
    have ht : (9+R^2)/(2*(3+R^2)) ≤ 3/2 := by
      rw [div_le_iff₀ (by positivity)]
      nlinarith only [sq_nonneg R]
    exact hJ1.trans ht
  have hJ41 : J ≤ 41/28 := by
    have ht : (9+R^2)/(2*(3+R^2)) ≤ 41/28 := by
      rw [div_le_iff₀ (by positivity)]
      nlinarith only [hR]
    exact hJ1.trans ht
  have hK4A : 4+A < K := by
    rw [hK]
    have ht : 2 < 2*(40/27)/J := by
      rw [lt_div_iff₀ hJ]
      linarith only [hJ41]
    linarith only [ht]
  have hK4 : 4 < K := by linarith only [hK4A,hA]
  have hK0 : 0 < K := by linarith only [hK4]
  have hmargin : (7/11)*R^2 < 3-2*J := by
    have hnorm : 2*R^2/(3+R^2) ≤ 3-2*J := by
      rw [div_le_iff₀ (by positivity)]
      have := (le_div_iff₀ (by positivity : 0 < 2*(3+R^2))).1 hJ1
      nlinarith only [this]
    have hstrict : (7/11)*R^2 < 2*R^2/(3+R^2) := by
      rw [lt_div_iff₀ (by positivity)]
      have hp := mul_pos (sq_pos_of_pos hR0) (show 0 < 1/7-R^2 by linarith only [hR2])
      nlinarith only [hp]
    exact hstrict.trans_le hnorm
  have hloss1 : J*A < R^2/6 := by
    have hp := mul_le_mul hJ32 hAd hA (by norm_num : (0:ℝ) ≤ 3/2)
    have hdR : d < R/6 := by linarith only [hd1,hR]
    have hm := mul_lt_mul_of_pos_left hdR hR0
    nlinarith only [hp,hm]
  have hloss2 : J*H^2/K < R^2/16 := by
    rw [div_lt_iff₀ hK0]
    have hH2 : H^2 < (R^2)^2 := by nlinarith only [hH,hH1,sq_nonneg R]
    have hp := mul_le_mul_of_nonneg_right hJ32 (sq_nonneg H)
    have hm := mul_lt_mul_of_pos_left hK4 (show 0 < R^2/16 by positivity)
    have hpow := mul_pos (sq_pos_of_pos hR0) (show 0 < 1/7-R^2 by linarith only [hR2])
    nlinarith only [hH2,hp,hm,hpow]
  let a := A/H
  let b := A/K
  have ha0 : 0 ≤ a := div_nonneg hA hH.le
  have hb0 : 0 ≤ b := div_nonneg hA hK0.le
  have haR : a ≤ R/2 := by dsimp [a]; rw [div_le_iff₀ hH]; nlinarith only [hHR]
  have ha1 : a ≤ 1 := by linarith only [haR,hR1]
  have hHK : H/K < 1/8 := by
    rw [div_lt_iff₀ hK0]
    linarith only [hH1,hR2,hK4]
  have hb_eq : b = a*(H/K) := by dsimp [a,b]; field_simp
  have hb_a : b ≤ a/8 := by
    rw [hb_eq]
    have hp := mul_le_mul_of_nonneg_left hHK.le ha0
    linarith only [hp]
  have hb1 : b ≤ 1 := by linarith only [hb_a,ha1]
  have hb_sq : b^2 ≤ a^2/64 := by nlinarith only [hb_a,ha0,hb0]
  have ha_sq : a^2 ≤ R^2/4 := by nlinarith only [haR,ha0,hR0]
  have hroot := cont_root_loss ha0 ha1 hb0 hb1
  have hloss3 : (161/54)*(1-√(1-b^2)/√(1+a^2)) < (2/5)*R^2 := by
    have h1 : 1-√(1-b^2)/√(1+a^2) ≤ (33/64)*a^2 := by linarith only [hroot,hb_sq]
    have h2 : 1-√(1-b^2)/√(1+a^2) ≤ (33/256)*R^2 := by linarith only [h1,ha_sq]
    have hp := mul_le_mul_of_nonneg_left h2 (by norm_num : (0:ℝ) ≤ 161/54)
    nlinarith only [hp,sq_pos_of_pos hR0]
  dsimp [a,b] at hloss3
  linarith only [hloss1,hloss2,hloss3,hmargin,sq_pos_of_pos hR0]


private lemma cont_half_sine {A H K : ℝ} (hA : 0 ≤ A) (hH : 0 < H) (hK : A < K) :
    sin (2*arctan ((√(H^2+A^2)+H)/(K+√(K^2-A^2))))*(K^2+H^2) =
      K*√(H^2+A^2)+√(K^2-A^2)*H := by
  let W := √(H^2+A^2)
  let D := √(K^2-A^2)
  have hK0 : 0 < K := hA.trans_lt hK
  have hW0 : 0 ≤ W := Real.sqrt_nonneg _
  have hD0 : 0 ≤ D := Real.sqrt_nonneg _
  have hW2 : W^2 = H^2+A^2 := Real.sq_sqrt (by positivity)
  have hD2 : D^2 = K^2-A^2 := Real.sq_sqrt (by nlinarith only [hA,hK])
  have hKD : 0 < K+D := by positivity
  have hden : 0 < 1+((W+H)/(K+D))^2 := by positivity
  have htrig (y : ℝ) : sin (2*arctan y) = 2*y/(1+y^2) := by
    rw [sin_two_mul,sin_arctan,cos_arctan]
    have hs : 0 < √(1+y^2) := by positivity
    have hs2 := Real.sq_sqrt (show 0 ≤ 1+y^2 by positivity)
    field_simp
    rw [hs2]
  change sin (2*arctan ((W+H)/(K+D)))*(K^2+H^2) = K*W+D*H
  rw [htrig]
  field_simp
  linear_combination (-D*H-2*H*K-K*W)*hW2+(-D*H-2*H*K-K*W)*hD2

/-- Three explicit losses make the tangent-curve score strictly decrease. -/
theorem cost_continuation_loss {R d A H J K : ℝ}
    (hR : 1/3 ≤ R) (hR1 : R ≤ 7/19) (hd1 : d ≤ 1/19)
    (hA : 0 ≤ A) (hAd : A ≤ 2*R*d/3) (hH : 0 < H) (hH1 : H < R^2)
    (hHR : 2*A ≤ H*R) (hJ : 0 < J)
    (hJ1 : J ≤ (9+R^2)/(2*(3+R^2)))
    (hK : K = A+2+2*(40/27)/J) :
    J*√(H^2+A^2) < (161/54)*sin (2*arctan ((√(H^2+A^2)+H)/(K+√(K^2-A^2)))) := by
  have hR2 : R^2 < 1/7 := by nlinarith only [hR,hR1]
  have hJ32 : J ≤ 3/2 := by
    have ht : (9+R^2)/(2*(3+R^2)) ≤ 3/2 := by
      rw [div_le_iff₀ (by positivity)]
      nlinarith only [sq_nonneg R]
    exact hJ1.trans ht
  have hK4A : 4+A < K := by
    rw [hK]
    have ht : 2 < 2*(40/27)/J := by
      rw [lt_div_iff₀ hJ]
      have hJ41 : J ≤ 41/28 := by
        have hbound : (9+R^2)/(2*(3+R^2)) ≤ 41/28 := by
          rw [div_le_iff₀ (by positivity)]
          nlinarith only [hR]
        exact hJ1.trans hbound
      linarith only [hJ41]
    linarith only [ht]
  have hK0 : 0 < K := by linarith only [hK4A,hA]
  have hKA : A < K := by linarith only [hK4A]
  let W := √(H^2+A^2)
  let D := √(K^2-A^2)
  have hW : 0 < W := Real.sqrt_pos.2 (by nlinarith only [hH,sq_nonneg A])
  have hD : 0 ≤ D := Real.sqrt_nonneg _
  have hW2 : W^2 = H^2+A^2 := Real.sq_sqrt (by positivity)
  have hD2 : D^2 = K^2-A^2 := Real.sq_sqrt (by nlinarith only [hKA,hA])
  have hWa : √(1+(A/H)^2) = W/H := by
    apply (Real.sqrt_eq_iff_eq_sq (by positivity) (div_nonneg hW.le hH.le)).2
    simp only [div_pow,hW2]
    field_simp
  have hDb : √(1-(A/K)^2) = D/K := by
    have hAK : A/K < 1 := (div_lt_one hK0).2 hKA
    have hAK0 : 0 ≤ A/K := div_nonneg hA hK0.le
    apply (Real.sqrt_eq_iff_eq_sq (by nlinarith only [hAK,hAK0]) (div_nonneg hD hK0.le)).2
    simp only [div_pow,hD2]
    field_simp
  have hratio : √(1-(A/K)^2)/√(1+(A/H)^2) = D*H/(K*W) := by
    rw [hWa,hDb]
    field_simp
  have hloss := cont_three_losses hR hR1 hd1 hA hAd hH hH1 hHR hJ hJ1 hK
  rw [hratio] at hloss
  have hJK : J*K = 2*(40/27)+2*J+J*A := by
    rw [hK]
    field_simp
    ring
  have hclear := (mul_lt_mul_iff_of_pos_right (show 0 < K*W by positivity)).2 hloss
  have hdiv : (J*A+J*H^2/K+(161/54)*(1-D*H/(K*W)))*(K*W) =
      J*A*K*W+J*H^2*W+(161/54)*(K*W-D*H) := by
    field_simp
  rw [hdiv] at hclear
  have htarget : J*W*(K^2+H^2) < (161/54)*(K*W+D*H) := by
    have hp := congrArg (fun z : ℝ => z*K*W) hJK
    nlinarith only [hclear,hp]
  have hsin := cont_half_sine hA hH hKA
  change sin (2*arctan ((W+H)/(K+D)))*(K^2+H^2) = K*W+D*H at hsin
  rw [← hsin] at htarget
  rw [← mul_assoc] at htarget
  exact (mul_lt_mul_iff_of_pos_right (show 0 < K^2+H^2 by positivity)).1 htarget


open Real

/-- Natural shape and central-shear bounds for the score continuation. -/
theorem cost_continuation_shape {x d al : ℝ}
    (hx : 2 ≤ x) (hx1 : x ≤ 13/6) (hd : 0 ≤ d) (hd1 : d ≤ 1/19)
    (hal : (13/5)*d ≤ al-1) (hal1 : al-1 ≤ 3*d) :
    1/3 ≤ ssRr x ∧ ssRr x ≤ 7/19 ∧ 0 ≤ ssTs al (x*(1+d)) ∧
      ssTs al (x*(1+d)) ≤ ssRr x ∧ 0 ≤ ssAn x (x*(1+d)) al ∧
      ssAn x (x*(1+d)) al ≤ 2*ssRr x*d/3 ∧
      costZ x (x*(1+d)) al < √3*(ssRr x)^2 := by
  let be := x*(1+d)
  let R := ssRr x
  let T := ssTs al be
  let A := ssAn x be al
  let U := m2U (1/(1+x))
  have hx0 : 0 < x := by linarith only [hx]
  have hS : 0 < x+1 := by positivity
  have hal0 : 0 < al := by linarith only [hal,hd]
  have halge : 1 ≤ al := by linarith only [hal,hd]
  have hal22 : al ≤ 22/19 := by linarith only [hal1,hd1]
  have hbe : x ≤ be := by dsimp [be]; nlinarith only [hx,hd]
  have hbe0 : 0 < be := hx0.trans_le hbe
  have hsum : 0 < be+al := by positivity
  have hR : 1/3 ≤ R := by dsimp [R,ssRr]; rw [le_div_iff₀ hS]; linarith only [hx]
  have hR1 : R ≤ 7/19 := by dsimp [R,ssRr]; rw [div_le_iff₀ hS]; linarith only [hx1]
  have hR0 : 0 < R := by linarith only [hR]
  have hR2 : R^2 < 1/7 := by nlinarith only [hR,hR1]
  have hT : 0 ≤ T := by dsimp [T,ssTs]; exact div_nonneg (by linarith only [hbe,hx,hal22]) hsum.le
  have hTR : T ≤ R := by
    dsimp [T,R,ssTs,ssRr]
    rw [div_le_div_iff₀ hsum hS]
    dsimp [be]
    nlinarith only [hx,hal,hd]
  have hRTid : R-T = 2*(x*al-be)/((x+1)*(be+al)) := by
    dsimp [R,T,ssRr,ssTs]
    field_simp
    ring
  have hRT : R-T ≤ d := by
    rw [hRTid,div_le_iff₀ (by positivity)]
    have hden : (x+1)^2 ≤ (x+1)*(be+al) := by
      have hm := mul_nonneg (show 0 ≤ x+1 by positivity)
        (show 0 ≤ be+al-(x+1) by linarith only [hbe,halge])
      nlinarith only [hm]
    have hm := mul_le_mul_of_nonneg_left hden hd
    have hs := mul_nonneg hd (sq_nonneg (x-1))
    have hn : 2*(x*al-be) ≤ 4*x*d := by dsimp [be]; nlinarith only [hal1,hx0]
    nlinarith only [hm,hs,hn]
  have hAid : A = (R^2-T^2)/(3+T^2) := by
    dsimp [A,R,T,ssAn,ssRr,ssTs]
    have hKA : 0 < al^2+al*be+be^2 := by positivity
    field_simp
    ring
  have hA : 0 ≤ A := by
    rw [hAid]
    exact div_nonneg (by nlinarith only [hT,hTR]) (by positivity)
  have hAd : A ≤ 2*R*d/3 := by
    have hid : A*(3+T^2) = R^2-T^2 := by rw [hAid]; field_simp
    have hm := mul_le_mul hRT (show R+T ≤ 2*R by linarith only [hTR])
      (show 0 ≤ R+T by positivity) hd
    have hp := mul_nonneg hA (sq_nonneg T)
    nlinarith only [hid,hm,hp]
  have hUeq : U = (3+R^2)/4 := by dsimp [U,R,m2U,ssRr]; field_simp; ring
  have hU0 : 0 < U := by rw [hUeq]; positivity
  let Ds := 2*be*x-x-al*be
  have hAs : Ds/(x*(x+2)) ≤ 2*(x-1)/(x+2)+d/5 := by
    have hid : (2*(x-1)/(x+2)+(2*x-18/5)*d/(x+2))-Ds/(x*(x+2)) =
        ((1+d)*(al-1-(13/5)*d)+(13/5)*d^2)/(x+2) := by
      dsimp [Ds,be]
      field_simp
      ring
    have hp : 0 ≤ ((1+d)*(al-1-(13/5)*d)+(13/5)*d^2)/(x+2) := by
      have hgap : 0 ≤ al-1-(13/5)*d := by linarith only [hal]
      positivity
    have hcoeff : (2*x-18/5)/(x+2) ≤ 1/5 := by
      rw [div_le_iff₀ (by positivity)]
      linarith only [hx1]
    have hm := mul_le_mul_of_nonneg_right hcoeff hd
    have hmeq : (2*x-18/5)/(x+2)*d = (2*x-18/5)*d/(x+2) := by ring
    rw [hmeq] at hm
    linarith only [hid,hp,hm]
  have hbase : 2*U*(2*(x-1)/(x+2))-2*R = 2*R^2*(1+R)/(3-R) := by
    have hdenR : 3-R = 2*(x+2)/(x+1) := by dsimp [R,ssRr]; field_simp; ring
    rw [hdenR]
    dsimp [U,R,m2U,ssRr]
    field_simp
    ring
  have hZeq : costZ x be al = 2*U*(Ds/(x*(x+2)))-R-(1+A)*T := by
    dsimp [costZ,U,Ds,R,A,T]
    ring
  have hZ : costZ x be al ≤ 2*R^2*(1+R)/(3-R)+(1+2*U/5)*d := by
    have hm := mul_le_mul_of_nonneg_left hAs (show 0 ≤ 2*U by positivity)
    have hp := mul_nonneg hA hT
    rw [hZeq]
    nlinarith only [hm,hp,hRT,hbase]
  have hbasebound : 2*R^2*(1+R)/(3-R) ≤ (26/25)*R^2 := by
    have hratio : 2*(1+R)/(3-R) ≤ 26/25 := by
      rw [div_le_iff₀ (by linarith only [hR1])]
      linarith only [hR1]
    have hm := mul_le_mul_of_nonneg_left hratio (sq_nonneg R)
    convert hm using 1 <;> ring
  have hUbound : 2*U ≤ 8/5 := by rw [hUeq]; linarith only [hR2]
  have hcoeff : 1+2*U/5 ≤ 33/25 := by linarith only [hUbound]
  have hdR : d < R^2/2 := by nlinarith only [hd1,hR]
  have hm1 := mul_le_mul_of_nonneg_right hcoeff hd
  have hm2 := mul_lt_mul_of_pos_left hdR (by norm_num : (0:ℝ) < 33/25)
  have hZ17 : costZ x be al < (17/10)*R^2 := by linarith only [hZ,hbasebound,hm1,hm2]
  have hs3 : (17/10:ℝ) < √3 := by rw [Real.lt_sqrt (by norm_num)]; norm_num
  have hm3 := mul_lt_mul_of_pos_right hs3 (sq_pos_of_pos hR0)
  exact ⟨hR,hR1,hT,hTR,hA,hAd,hZ17.trans hm3⟩


end SmoothedOctagon
