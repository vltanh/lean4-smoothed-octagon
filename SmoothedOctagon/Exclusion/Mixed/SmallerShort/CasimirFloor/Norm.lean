module

public import SmoothedOctagon.Exclusion.Mixed.SmallerShort.CasimirFloor.Defs

/-!
# Norm monotonicity of the central floor tests

The compact central Gram bounds its norm increment uniformly. The original
transport gives the residual increment at every duration, and its slope exceeds
two on the closed shape rectangle. The duration correction in the second floor
test is independent of the norm. Both tests therefore decrease on the whole
half-line of norms above `3/4`.
-/

@[expose] public section

namespace SmoothedOctagon

open Set Real

private noncomputable def normAmp (x : ℝ) : ℝ := (1+x)^3/(x*(x+2))
private noncomputable def normRatio (x : ℝ) : ℝ := (x-1)/(1+x)
private noncomputable def normB (x u : ℝ) : ℝ := normAmp x*(m2U (1/(1+x))-u)

private theorem norm_u1 {x : ℝ} (hx : 0 < x) : m2U (1/(1+x)) = (3+(normRatio x)^2)/4 := by
  have hS : 0 < 1+x := by positivity
  unfold m2U normRatio
  field_simp
  ring

private theorem norm_geometry {x : ℝ} (hx : 2 ≤ x) (hx2 : x ≤ 13/6) :
    0 < normAmp x ∧ normAmp x ≤ 18/5 ∧ 0 ≤ normRatio x ∧
      normRatio x ≤ 3/8 ∧ (normRatio x)^2 ≤ 1/7 := by
  have hx0 : 0 < x := by linarith only [hx]
  have hS : 0 < 1+x := by positivity
  have hV : 8 ≤ x*(x+2) := by nlinarith only [hx]
  have hrec : 1/(x*(x+2)) ≤ 1/8 := one_div_le_one_div_of_le (by norm_num) hV
  have hAeq : normAmp x = (1+x)*(1+1/(x*(x+2))) := by
    unfold normAmp
    field_simp
    ring
  have hAmp : normAmp x ≤ 18/5 := by
    have hm := mul_le_mul (show 1+x ≤ 19/6 by linarith only [hx2])
      (show 1+1/(x*(x+2)) ≤ 9/8 by linarith only [hrec])
      (show 0 ≤ 1+1/(x*(x+2)) by positivity) (by norm_num : (0:ℝ) ≤ 19/6)
    rw [← hAeq] at hm
    linarith only [hm]
  have hR0 : 0 ≤ normRatio x := by unfold normRatio; exact div_nonneg (by linarith only [hx]) hS.le
  have hR7 : normRatio x ≤ 7/19 := by unfold normRatio; rw [div_le_iff₀ hS]; linarith only [hx2]
  refine ⟨by unfold normAmp; positivity,hAmp,hR0,by linarith only [hR7],?_⟩
  have hm := mul_nonneg (sub_nonneg.mpr hR7) (show 0 ≤ 7/19+normRatio x by positivity)
  nlinarith only [hm]

private theorem norm_b_upper {x u : ℝ} (hx : 2 ≤ x) (hx2 : x ≤ 13/6) (hu : 3/4 ≤ u) :
    normB x u ≤ 1/6 := by
  have hx0 : 0 < x := by linarith only [hx]
  obtain ⟨hA,hA1,hR0,hR1,hR2⟩ := norm_geometry hx hx2
  have hU : m2U (1/(1+x))-u ≤ (normRatio x)^2/4 := by rw [norm_u1 hx0]; linarith only [hu]
  have hm1 := mul_le_mul_of_nonneg_left hU hA.le
  have hm2 := mul_le_mul hA1 hR2 (sq_nonneg _) (by norm_num : (0:ℝ) ≤ 18/5)
  unfold normB
  nlinarith only [hm1,hm2]

private theorem norm_gram {x al u : ℝ} (hx : 0 < x) (hal : 1 ≤ al) :
    ssGs x al u (ssQc x al) = (3-(normB x u)^2-2*normRatio x*normB x u)/16 := by
  have hal0 : 0 < al := by linarith only [hal]
  have hV : 0 < x*(x+2) := by positivity
  have hN : 0 < x*(x+2)+al^2 := by positivity
  have hqc : ssQc x al < 1 := by unfold ssQc; rw [div_lt_one hN]; linarith only [hV]
  have hs : ssQc x al/(al^2*(1-ssQc x al)) = 1/(x*(x+2)) := by
    unfold ssQc
    field_simp (disch := first | positivity | nlinarith)
    ring
  rw [env_Gs_s hx hal hqc,hs]
  unfold normB normAmp normRatio
  have hS : 0 < 1+x := by positivity
  generalize m2U (1/(1+x))-u = w
  field_simp
  ring

private theorem norm_gram_increment {x al u u' : ℝ} (hx : 0 < x) (hal : 1 ≤ al) :
    ssGs x al u' (ssQc x al)-ssGs x al u (ssQc x al) =
      (u'-u)*normAmp x*(normB x u+normB x u'+2*normRatio x)/16 := by
  rw [norm_gram hx hal,norm_gram hx hal]
  unfold normB
  ring

private theorem norm_gram_bound {x al u u' : ℝ} (hx : 2 ≤ x) (hx2 : x ≤ 13/6)
    (hal : 1 ≤ al) (hu : 3/4 ≤ u) (huu : u ≤ u') :
    ssGs x al u' (ssQc x al)-ssGs x al u (ssQc x al) ≤ (u'-u)/4 := by
  obtain ⟨hA,hA1,hR0,hR1,hR2⟩ := norm_geometry hx hx2
  have hB := norm_b_upper hx hx2 hu
  have hB' := norm_b_upper hx hx2 (hu.trans huu)
  have hsum : normB x u+normB x u'+2*normRatio x ≤ 13/12 := by linarith only [hB,hB',hR1]
  have hm1 := mul_le_mul_of_nonneg_left hsum hA.le
  have hm2 := mul_le_mul_of_nonneg_right hA1 (by norm_num : (0:ℝ) ≤ 13/12)
  have hcoef : normAmp x*(normB x u+normB x u'+2*normRatio x) ≤ 4 := by linarith only [hm1,hm2]
  have hm := mul_le_mul_of_nonneg_left hcoef (sub_nonneg.mpr huu)
  rw [norm_gram_increment (by linarith only [hx]) hal]
  nlinarith only [hm]

private noncomputable def normD (x be al : ℝ) : ℝ := ssDg x be al/(x*(x+2)+al^2)
private noncomputable def normC (x al : ℝ) : ℝ := (1+x)^3/(x*(x+2)+al^2)
private noncomputable def normT (x be al : ℝ) : ℝ := ssRA al be/ssQc x al

private theorem norm_shape_rect {x be al : ℝ} (hx : 2 ≤ x) (hx2 : x ≤ 13/6)
    (hal : 1 ≤ al) (hal1 : al ≤ 22/19) (hxb : x ≤ be) (hb1 : be ≤ 130/57) :
    0 < ssDg x be al ∧ ssDg x be al < 1+x ∧ normD x be al ≤ 1/3 ∧
      ssDg x be al < al*(al+be) ∧ 30/11 ≤ 1/ssRA al be := by
  have hx0 : 0 < x := by linarith only [hx]
  have hal0 : 0 < al := by linarith only [hal]
  have hbe0 : 0 < be := hx0.trans_le hxb
  have hgap : 0 ≤ x-al := by linarith only [hx,hal1]
  have hasq : 1 ≤ al^2 := by nlinarith only [hal]
  have hN : 0 < x*(x+2)+al^2 := by positivity
  have hDpos : 0 < ssDg x be al := by
    have hm : be*(x-al) ≤ (130/57:ℝ)*(7/6) :=
      mul_le_mul hb1 (by linarith only [hx2,hal]) hgap (by norm_num)
    unfold ssDg
    nlinarith only [hm,hasq,hx]
  have hDS : ssDg x be al < 1+x := by
    have hm1 := mul_le_mul_of_nonneg_right hxb hgap
    have hm2 := mul_nonneg (show 0 ≤ x-2 by linarith only [hx])
      (show 0 ≤ 2*x+3-2*al by linarith only [hx,hal1])
    have hm3 := mul_nonneg (show 0 ≤ 22/19-al by linarith only [hal1])
      (show 0 ≤ 22/19+al+4 by linarith only [hal])
    unfold ssDg
    nlinarith only [hm1,hm2,hm3]
  have hd : normD x be al ≤ 1/3 := by
    unfold normD
    rw [div_le_iff₀ hN]
    have hNS : (1+x)^2 ≤ x*(x+2)+al^2 := by nlinarith only [hasq]
    have hSS := mul_nonneg (show 0 ≤ x-2 by linarith only [hx]) (show 0 ≤ 1+x by positivity)
    nlinarith only [hNS,hSS,hDS]
  have hDa : ssDg x be al < al*(al+be) := by
    have hm1 := mul_le_mul_of_nonneg_right hxb (show 0 ≤ 2*x-al by linarith only [hx,hal1])
    have hm2 := mul_pos hx0 (show 0 < 3/2-al by linarith only [hal1])
    have hm3 := mul_nonneg (show 0 ≤ x-2 by linarith only [hx])
      (show 0 ≤ 2*x+1/2 by positivity)
    unfold ssDg
    nlinarith only [hm1,hm2,hm3]
  have hrA : 30/11 ≤ 1/ssRA al be := by
    unfold ssRA
    rw [one_div_div,le_div_iff₀ hal0]
    linarith only [hal1,hxb,hx]
  exact ⟨hDpos,hDS,hd,hDa,hrA⟩

private theorem norm_transport_increment {x be al u u' τ : ℝ} (hx : 0 < x) (hal : 1 ≤ al) :
    ssRs x be al u' (ssQc x al) τ-ssRs x be al u (ssQc x al) τ =
      (u'-u)*(1/ssRA al be+normC x al*(1-τ*normD x be al)+τ*(normD x be al)^2-2*normD x be al) := by
  have hal0 : 0 < al := by linarith only [hal]
  have hN : 0 < x*(x+2)+al^2 := by positivity
  let qc := ssQc x al
  let d := qc*(ssDg x be al/al^2)
  let C := (1+x)*(1-qc*(1-1/al^2))
  have hd : d = normD x be al := by dsimp [d,qc,normD,ssQc]; field_simp
  have hC : C = normC x al := by dsimp [C,qc,normC,ssQc]; field_simp; ring
  have he : ssRs x be al u' qc τ-ssRs x be al u qc τ =
      (u'-u)*(1/ssRA al be+C*(1-τ*d)+τ*d^2-2*d) := by
    dsimp [C,d]
    unfold ssRs ssF ssWs ssELs ssA1 ssA2 ssA3 ssE0
    ring
  simpa only [hd,hC] using he

private theorem norm_slope {x be al τ : ℝ} (hx : 2 ≤ x) (hx2 : x ≤ 13/6)
    (hal : 1 ≤ al) (hal1 : al ≤ 22/19) (hxb : x ≤ be) (hb1 : be ≤ 130/57)
    (hτ : 0 ≤ τ) (hτd : τ*normD x be al ≤ 1) :
    2 < 1/ssRA al be+normC x al*(1-τ*normD x be al)+τ*(normD x be al)^2-2*normD x be al := by
  obtain ⟨hD,hDS,hd,hDa,hrA⟩ := norm_shape_rect hx hx2 hal hal1 hxb hb1
  have hx0 : 0 < x := by linarith only [hx]
  have hC : 0 < normC x al := by unfold normC; positivity
  have hterm1 := mul_nonneg hC.le (show 0 ≤ 1-τ*normD x be al by linarith only [hτd])
  have hterm2 := mul_nonneg hτ (sq_nonneg (normD x be al))
  linarith only [hrA,hd,hterm1,hterm2]

private theorem norm_last_duration {x be al : ℝ} (hx : 2 ≤ x) (hx2 : x ≤ 13/6)
    (hal : 1 ≤ al) (hal1 : al ≤ 22/19) (hxb : x ≤ be) (hb1 : be ≤ 130/57) :
    0 ≤ normT x be al ∧ normT x be al*normD x be al ≤ 1 := by
  have hx0 : 0 < x := by linarith only [hx]
  have hal0 : 0 < al := by linarith only [hal]
  have hbe0 : 0 < be := hx0.trans_le hxb
  have hN : 0 < x*(x+2)+al^2 := by positivity
  have hqc : 0 < ssQc x al := by unfold ssQc; positivity
  have hrA : 0 < ssRA al be := by unfold ssRA; positivity
  have he : normT x be al*normD x be al = ssDg x be al/(al*(al+be)) := by
    unfold normT normD ssRA ssQc
    field_simp
  refine ⟨(div_pos hrA hqc).le,?_⟩
  rw [he,div_le_one (by positivity)]
  exact (norm_shape_rect hx hx2 hal hal1 hxb hb1).2.2.2.1.le

private theorem norm_psi_increment {x be al u u' : ℝ} :
    casPsi x be al u'-casPsi x be al u =
      (ssGs x al u' (ssQc x al)-ssGs x al u (ssQc x al))-
      (ssRs x be al u' (ssQc x al) (normT x be al)-ssRs x be al u (ssQc x al) (normT x be al))/7 := by
  unfold casPsi casPhi normT ssRs ssF
  ring


/-- The two central floor tests have a uniform negative norm increment. -/
theorem cas_norm_increment_bound {x be al u u' : ℝ} (hx : 2 ≤ x) (hx2 : x ≤ 13/6)
    (hal : 1 ≤ al) (hal1 : al ≤ 22/19) (hxb : x ≤ be) (hb1 : be ≤ 130/57)
    (hu : 3/4 ≤ u) (huu : u ≤ u') :
    casPhi x be al u'-casPhi x be al u ≤ -(u'-u)/28 ∧
      casPsi x be al u'-casPsi x be al u ≤ -(u'-u)/28 := by
  have hx0 : 0 < x := by linarith only [hx]
  have hdu : 0 ≤ u'-u := sub_nonneg.mpr huu
  have hG := norm_gram_bound hx hx2 hal hu huu
  have hd := (norm_shape_rect hx hx2 hal hal1 hxb hb1).2.2.1
  have hs2 := norm_slope hx hx2 hal hal1 hxb hb1 (τ := 2) (by norm_num)
    (by linarith only [hd])
  have hR2eq := norm_transport_increment (be := be) (u := u) (u' := u') (τ := 2) hx0 hal
  have hm2 := mul_le_mul_of_nonneg_left hs2.le hdu
  have hR2 : 2*(u'-u) ≤ ssRs x be al u' (ssQc x al) 2-ssRs x be al u (ssQc x al) 2 := by
    rw [hR2eq]
    nlinarith only [hm2]
  obtain ⟨hT,hTd⟩ := norm_last_duration hx hx2 hal hal1 hxb hb1
  have hsT := norm_slope hx hx2 hal hal1 hxb hb1 hT hTd
  have hRTeq := norm_transport_increment (be := be) (u := u) (u' := u') (τ := normT x be al) hx0 hal
  have hmT := mul_le_mul_of_nonneg_left hsT.le hdu
  have hRT : 2*(u'-u) ≤ ssRs x be al u' (ssQc x al) (normT x be al)-
      ssRs x be al u (ssQc x al) (normT x be al) := by
    rw [hRTeq]
    nlinarith only [hmT]
  constructor
  · unfold casPhi
    linarith only [hG,hR2]
  · have he := norm_psi_increment (x := x) (be := be) (al := al) (u := u) (u' := u')
    linarith only [hG,hRT,he]

/-- The central floor tests decrease throughout the full half-line of norms. -/
theorem cas_norm_rect {x be al u u' : ℝ} (hx : 2 ≤ x) (hx2 : x ≤ 13/6)
    (hal : 1 ≤ al) (hal1 : al ≤ 22/19) (hxb : x ≤ be) (hb1 : be ≤ 130/57)
    (hu : 3/4 ≤ u) (huu : u ≤ u') :
    casPhi x be al u' ≤ casPhi x be al u ∧ casPsi x be al u' ≤ casPsi x be al u := by
  have h := cas_norm_increment_bound hx hx2 hal hal1 hxb hb1 hu huu
  constructor <;> linarith only [h.1,h.2,huu]

end SmoothedOctagon
