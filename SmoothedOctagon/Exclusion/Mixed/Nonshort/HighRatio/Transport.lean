module

public import SmoothedOctagon.Foundations.IntervalBounds

public meta import SmoothedOctagon.Tactic.Deriv

public import SmoothedOctagon.Exclusion.Mixed.Scalar
public import Mathlib.Analysis.Calculus.Deriv.Inv
public import Mathlib.Analysis.Calculus.Deriv.Pow
public import Mathlib.Analysis.Calculus.MeanValue
public import Mathlib.Analysis.Convex.Deriv

/-!
# Lowering scale and raising the middle margin

The exact transport comparison is affine in scale. Its total middle-margin
derivative and the small-displacement boundary have natural positive budgets.
-/

@[expose] public section

namespace SmoothedOctagon
open Set Real

noncomputable def mhtTransportW (C D : ℝ) : ℝ := C+D
noncomputable def mhtTransportQ (D K : ℝ) : ℝ := D^2+K-1
noncomputable def mhtTransportY (C D : ℝ) : ℝ := (D-1)*(D+2*C+1)
noncomputable def mhtTransportA (C K : ℝ) : ℝ := K^2-K*(1+C)+(1+C)^2
noncomputable def mhtTransportH (C K v : ℝ) : ℝ :=
  K*(1+C)*(v-1)+K/(1+C)+1+2*C
noncomputable def mhtDelta (C D K v q : ℝ) : ℝ :=
  let W := mhtTransportW C D
  let Q := mhtTransportQ D K
  let Y := mhtTransportY C D
  Q^2-D*W*Q/q+D^2*W^2/q^2-mhtTransportA C K-mhtTransportH C K v*Y-v*Y^2
noncomputable def mhtDeltaScale (C D v q : ℝ) : ℝ :=
  C*(D-1)*(C+2*D-1)/(C+1)+(C+1)*mhtTransportY C D*(m2g C 1-v)+
    D*(C+D)*(1-1/q)

/-- Exact affine scale comparison in the original norm ceiling. -/
theorem mhtDelta_scale_identity {C D K K' v q : ℝ} (hC : C+1 ≠ 0) :
    mhtDelta C D K v q-mhtDelta C D K' v q =
      (K-K')*mhtDeltaScale C D v q := by
  unfold mhtDelta mhtDeltaScale mhtTransportW mhtTransportQ mhtTransportY mhtTransportA mhtTransportH m2g
  have hCp : 1+C ≠ 0 := by simpa only [add_comm] using hC
  simp only [div_eq_mul_inv]
  generalize q⁻¹ = y
  field_simp [hC,hCp]
  ring

theorem mhtDeltaScale_pos {C D v q : ℝ} (hC : 1 ≤ C) (hD : 1 < D)
    (hq : 1 < q) (hv : v ≤ m2g C 1) : 0 < mhtDeltaScale C D v q := by
  have hCp : 0 < C+1 := by linarith only [hC]
  have hY : 0 < mhtTransportY C D := by unfold mhtTransportY; positivity
  have hfirst : 0 < C*(D-1)*(C+2*D-1)/(C+1) := by
    apply div_pos
    · apply mul_pos
      · exact mul_pos (by linarith only [hC]) (by linarith only [hD])
      · linarith only [hC,hD]
    · exact hCp
  have hmiddle : 0 ≤ (C+1)*mhtTransportY C D*(m2g C 1-v) :=
    mul_nonneg (mul_nonneg hCp.le hY.le) (sub_nonneg.mpr hv)
  have hq0 : 0 < q := by linarith only [hq]
  have hrecip : 1/q < 1 := (div_lt_one hq0).mpr hq
  have hlast : 0 < D*(C+D)*(1-1/q) := by positivity
  unfold mhtDeltaScale
  linarith only [hfirst,hmiddle,hlast]

theorem mhtDelta_lower_scale {C D K v q : ℝ} (hC : 1 ≤ C) (hD : 1 < D)
    (hq : 1 < q) (hv : v ≤ m2g C 1) (hK : 7 ≤ K) :
    mhtDelta C D 7 v q ≤ mhtDelta C D K v q := by
  have hi := mhtDelta_scale_identity (C := C) (D := D) (K := K) (K' := 7)
    (v := v) (q := q) (by linarith only [hC])
  have hp := mul_nonneg (sub_nonneg.mpr hK) (mhtDeltaScale_pos hC hD hq hv).le
  linarith only [hi,hp]

/-- The transported comparison decreases in the incident secant value. -/
theorem mhtDelta_value_identity (C D K v V q : ℝ) :
    mhtDelta C D K v q-mhtDelta C D K V q =
      (V-v)*mhtTransportY C D*(K*(C+1)+mhtTransportY C D) := by
  unfold mhtDelta mhtTransportH
  dsimp
  ring

theorem mhtT_le_of_deriv {f f' : ℝ → ℝ} {x y : ℝ} (hxy : x ≤ y)
    (hd : ∀ z ∈ Icc x y, HasDerivAt f (f' z) z)
    (hn : ∀ z ∈ Ioo x y, 0 ≤ f' z) : f x ≤ f y := by
  exact le_of_hasDerivAt_nonneg hxy hd hn


noncomputable def mhtSmallGap (D : ℝ) : ℝ :=
  (3/4)*(D^2+6)^2-151/4-(13/5)*((D-1)*(D+4))-(19/25)*((D-1)*(D+4))^2
noncomputable def mhtSmallGap1 (D : ℝ) : ℝ :=
  3*D*(D^2+6)-(13/5)*(2*D+3)-(38/25)*((D-1)*(D+4))*(2*D+3)
noncomputable def mhtSmallGap2 (D : ℝ) : ℝ :=
  (3/2)*(4*D^2+2*(D^2+6))-26/5-(38/25)*((2*D+3)^2+2*((D-1)*(D+4)))

private theorem mhtSmallGap_hasDerivAt (D : ℝ) :
    HasDerivAt mhtSmallGap (mhtSmallGap1 D) D := by
  have hd : HasDerivAt (fun x : ℝ => (x-1)*(x+4)) (2*D+3) D := by
    convert ((hasDerivAt_id D).sub_const 1).mul ((hasDerivAt_id D).add_const 4) using 1
    · rfl
    · simp only [id_eq]; ring
  have hq : HasDerivAt (fun x : ℝ => x^2+6) (2*D) D := by
    simpa using ((hasDerivAt_id D).pow 2).add_const 6
  have h := ((((hq.pow 2).const_mul (3/4)).sub_const (151/4)).sub
    (hd.const_mul (13/5))).sub ((hd.pow 2).const_mul (19/25))
  convert h using 1
  · ext x; dsimp [mhtSmallGap]
  · norm_num [mhtSmallGap1]; ring

private theorem mhtSmallGap1_hasDerivAt (D : ℝ) :
    HasDerivAt mhtSmallGap1 (mhtSmallGap2 D) D := by
  have hd : HasDerivAt (fun x : ℝ => (x-1)*(x+4)) (2*D+3) D := by
    convert ((hasDerivAt_id D).sub_const 1).mul ((hasDerivAt_id D).add_const 4) using 1
    · rfl
    · simp only [id_eq]; ring
  have hq : HasDerivAt (fun x : ℝ => x^2+6) (2*D) D := by
    simpa using ((hasDerivAt_id D).pow 2).add_const 6
  have hl : HasDerivAt (fun x : ℝ => 2*x+3) 2 D := by
    simpa using ((hasDerivAt_id D).const_mul 2).add_const 3
  have h := ((((hasDerivAt_id D).const_mul 3).mul hq).sub (hl.const_mul (13/5))).sub
    ((hd.mul hl).const_mul (38/25))
  convert h using 1
  · ext x; dsimp [mhtSmallGap1]; ring
  · norm_num [mhtSmallGap2]; ring

/-- The small-D transported ceiling lies strictly below the universal3/4 floor. -/
theorem mhtSmallGap_pos {D : ℝ} (hD : D ∈ Icc (4/3:ℝ) (3/2)) : 0 < mhtSmallGap D := by
  have hc : ConcaveOn ℝ (Icc (4/3:ℝ) (3/2)) mhtSmallGap := by
    apply concaveOn_of_hasDerivWithinAt2_nonpos (convex_Icc (4/3) (3/2))
      (f' := mhtSmallGap1) (f'' := mhtSmallGap2)
    · exact fun x _ => (mhtSmallGap_hasDerivAt x).continuousAt.continuousWithinAt
    · exact fun x _ => (mhtSmallGap_hasDerivAt x).hasDerivWithinAt
    · exact fun x _ => (mhtSmallGap1_hasDerivAt x).hasDerivWithinAt
    · intro x hx
      obtain ⟨hx0,hx1⟩ := interior_subset hx
      have hsq : x^2 ≤ (3/2:ℝ)^2 := by nlinarith only [hx0,hx1,sq_nonneg (x-3/2)]
      have hl : (17/3:ℝ)^2 ≤ (2*x+3)^2 := by nlinarith only [hx0,sq_nonneg (2*x+3-17/3)]
      have hy : 0 < (x-1)*(x+4) := mul_pos (by linarith only [hx0]) (by linarith only [hx0])
      unfold mhtSmallGap2
      nlinarith only [hsq,hl,hy]
  have he : 0 < min (mhtSmallGap (4/3)) (mhtSmallGap (3/2)) := by norm_num [mhtSmallGap]
  exact lt_of_lt_of_le he (concaveOn_min_endpoints_le hc hD)

theorem mhtDelta_smallD_pos {D v q : ℝ} (hD : D ∈ Icc (4/3:ℝ) (3/2))
    (hv : v ≤ 19/25) : 0 < mhtDelta (3/2) D 7 v q := by
  have hY : 0 < mhtTransportY (3/2) D := by
    unfold mhtTransportY
    exact mul_pos (by linarith only [hD.1]) (by linarith only [hD.1])
  have hval := mhtDelta_value_identity (3/2) D 7 v (19/25) q
  have hnonneg : 0 ≤ (19/25-v)*mhtTransportY (3/2) D*(7*(3/2+1)+mhtTransportY (3/2) D) := by
    exact mul_nonneg (mul_nonneg (sub_nonneg.mpr hv) hY.le) (by linarith only [hY])
  have hid : mhtDelta (3/2) D 7 (19/25) q =
      mhtSmallGap D+((D^2+6)/2-D*(D+3/2)/q)^2 := by
    unfold mhtDelta mhtTransportW mhtTransportQ mhtTransportY mhtTransportA mhtTransportH mhtSmallGap
    ring
  have hp := mhtSmallGap_pos hD
  rw [hid] at hval
  nlinarith only [hval,hnonneg,hp,sq_nonneg ((D^2+6)/2-D*(D+3/2)/q)]

noncomputable def mhtDeltaC (C D q v vc : ℝ) : ℝ :=
  -D*(D^2+6)/q+2*D^2*(C+D)/q^2-(2*C-5)-
    (7*(v-1)-7/(C+1)^2+2)*mhtTransportY C D-
    2*(D-1)*mhtTransportH C 7 v-4*v*mhtTransportY C D*(D-1)-
    vc*mhtTransportY C D*(7*(C+1)+mhtTransportY C D)
noncomputable def mhtHminus (C : ℝ) : ℝ := (C-3)/4+7/(C+1)
noncomputable def mhtHminus1 (C : ℝ) : ℝ := 1/4-7/(C+1)^2
noncomputable def mhtZ (C D : ℝ) : ℝ :=
  4*(C+1)^2*(3*mhtTransportY C D+2*mhtHminus C+
    mhtHminus1 C*(D+2*C+1)-D^2-(2*C+1)*D-2*C+5)
noncomputable def mhtZD (C D : ℝ) : ℝ :=
  4*(C+1)^2*(4*D+4*C-3/4-7/(C+1)^2)
noncomputable def mhtZEdge (C : ℝ) : ℝ := -(60*C^3+C^2-178*C-35)/9
noncomputable def mhtZEdge1 (C : ℝ) : ℝ := -(180*C^2+2*C-178)/9
noncomputable def mhtZEdge2 (C : ℝ) : ℝ := -40*C-2/9


/-- Total derivative along the actual incident secant; the scalar lemma does not assume its sign. -/
theorem mhtDelta_hasDerivAt_C {v : ℝ → ℝ} {C D q vc : ℝ}
    (hC : 1 ≤ C) (hq : 1 < q) (hv : HasDerivAt v vc C) :
    HasDerivAt (fun x => mhtDelta x D 7 (v x) q) (mhtDeltaC C D q (v C) vc) C := by
  have hCp : 0 < 1+C := by linarith only [hC]
  have hq0 : 0 < q := by linarith only [hq]
  have hw := (hasDerivAt_id' C).add_const D
  have hy := (hasDerivAt_const C (D-1)).mul
    (((hasDerivAt_const C D).add ((hasDerivAt_id' C).const_mul 2)).add_const 1)
  have hcp := (hasDerivAt_id' C).const_add 1
  have ha := ((hasDerivAt_const C ((7:ℝ)^2)).sub (hcp.const_mul 7)).add (hcp.pow 2)
  have hh := ((((hcp.mul (hv.sub_const 1)).const_mul 7).add
    ((hasDerivAt_const C (7:ℝ)).div hcp hCp.ne')).add_const 1).add
    ((hasDerivAt_id' C).const_mul 2)
  have hd := (((((hasDerivAt_const C ((D^2+6)^2)).sub
    (((hw.const_mul D).mul_const (D^2+6)).div_const q)).add
    (((hw.pow 2).const_mul (D^2)).div_const (q^2))).sub ha).sub (hh.mul hy)).sub (hv.mul (hy.pow 2))
  convert hd using 1
  · ext x
    dsimp [mhtDelta,mhtTransportW,mhtTransportQ,mhtTransportY,mhtTransportA,mhtTransportH]
    ring
  · unfold mhtDeltaC mhtTransportY mhtTransportH
    have hCp' : C+1 ≠ 0 := by linarith only [hC]
    norm_num only [Pi.pow_apply,Pi.mul_apply,Pi.add_apply,Pi.sub_apply,Pi.div_apply,id_eq]
    field_simp
    ring

theorem mhtDeltaC_value_identity (C D q v vc : ℝ) :
    mhtDeltaC C D q v vc = mhtDeltaC C D q (3/4) 0-
      (v-3/4)*(D-1)*(8*C*D+20*C+4*D^2+7*D+17)-
      vc*mhtTransportY C D*(7*(C+1)+mhtTransportY C D) := by
  unfold mhtDeltaC mhtTransportH mhtTransportY
  ring

theorem mhtDeltaC_boundary_identity {C D : ℝ} (hC : C+1 ≠ 0) :
    mhtDeltaC C D 1 (3/4) 0 = -(D-1)*mhtZ C D/(4*(C+1)^2) := by
  have hCp : 1+C ≠ 0 := by simpa only [add_comm] using hC
  unfold mhtDeltaC mhtZ mhtHminus mhtHminus1 mhtTransportH mhtTransportY
  field_simp [hC,hCp]
  ring

theorem mhtZ_hasDerivAt_D {C D : ℝ} :
    HasDerivAt (mhtZ C) (mhtZD C D) D := by
  have hy := ((hasDerivAt_id' D).sub_const 1).mul
    (((hasDerivAt_id' D).add_const (2*C)).add_const 1)
  have hd := (((((((hy.const_mul 3).add_const (2*mhtHminus C)).add
    ((((hasDerivAt_id' D).add_const (2*C)).add_const 1).const_mul (mhtHminus1 C))).sub
    ((hasDerivAt_id' D).pow 2)).sub ((hasDerivAt_id' D).const_mul (2*C+1))).sub_const (2*C)).add_const 5).const_mul (4*(C+1)^2)
  convert hd using 1
  · rfl
  · unfold mhtZD mhtHminus1
    norm_num only [Pi.pow_apply,Pi.mul_apply,Pi.add_apply,Pi.sub_apply,Pi.div_apply,id_eq]
    ring

theorem mhtZD_pos {C D : ℝ} (hC : 1 ≤ C) (hD : 4/3 ≤ D) : 0 < mhtZD C D := by
  have hc2 : (4:ℝ) ≤ (C+1)^2 := by nlinarith only [hC,sq_nonneg (C-1)]
  have hden : 0 < (C+1)^2 := by positivity
  have hfrac : 7/(C+1)^2 ≤ (7/4:ℝ) :=
    div_le_div_of_nonneg_left (by norm_num) (by norm_num) hc2
  unfold mhtZD
  exact mul_pos (by positivity) (by linarith only [hC,hD,hfrac])

theorem mhtZ_edge_identity {C : ℝ} (hC : C+1 ≠ 0) : mhtZ C (4/3) = mhtZEdge C := by
  unfold mhtZ mhtZEdge mhtTransportY mhtHminus mhtHminus1
  field_simp [hC]
  ring

private theorem mhtZEdge_hasDerivAt (C : ℝ) : HasDerivAt mhtZEdge (mhtZEdge1 C) C := by
  have hd := ((((((hasDerivAt_id' C).pow 3).const_mul 60).add
    ((hasDerivAt_id' C).pow 2)).sub ((hasDerivAt_id' C).const_mul 178)).sub_const 35).neg.div_const 9
  exact hd.congr_deriv (by unfold mhtZEdge1; ring)
private theorem mhtZEdge1_hasDerivAt (C : ℝ) : HasDerivAt mhtZEdge1 (mhtZEdge2 C) C := by
  have hd := (((((hasDerivAt_id' C).pow 2).const_mul 180).add
    ((hasDerivAt_id' C).const_mul 2)).sub_const 178).neg.div_const 9
  exact hd.congr_deriv (by unfold mhtZEdge2; ring)

theorem mhtZ_pos {C D : ℝ} (hC : C ∈ Icc (1:ℝ) (3/2)) (hD : 4/3 ≤ D) : 0 < mhtZ C D := by
  have hc : ConcaveOn ℝ (Icc (1:ℝ) (3/2)) mhtZEdge := by
    apply concaveOn_of_hasDerivWithinAt2_nonpos (convex_Icc 1 (3/2))
      (f' := mhtZEdge1) (f'' := mhtZEdge2)
    · exact fun x _ => (mhtZEdge_hasDerivAt x).continuousAt.continuousWithinAt
    · exact fun x _ => (mhtZEdge_hasDerivAt x).hasDerivWithinAt
    · exact fun x _ => (mhtZEdge1_hasDerivAt x).hasDerivWithinAt
    · intro x hx
      have hx0 := (interior_subset hx).1
      unfold mhtZEdge2
      linarith only [hx0]
  have hinit : 0 < mhtZEdge C := lt_of_lt_of_le
    (by norm_num [mhtZEdge] : 0 < min (mhtZEdge 1) (mhtZEdge (3/2)))
    (concaveOn_min_endpoints_le hc hC)
  have hm := mhtT_le_of_deriv hD
    (fun x _ => mhtZ_hasDerivAt_D)
    (fun x hx => (mhtZD_pos hC.1 hx.1.le).le)
  rw [mhtZ_edge_identity (by linarith only [hC.1])] at hm
  exact lt_of_lt_of_le hinit hm

/-- The q-dependent derivative term is a convex quadratic in1/q and is maximal atq1. -/
theorem mhtDeltaC_q_bound {C D q : ℝ} (hC : 1 ≤ C) (hD : 4/3 ≤ D)
    (hq : 1 < q) (hgap : 6 < D^2+2*C*D) :
    -D*(D^2+6)/q+2*D^2*(C+D)/q^2 ≤ -D*(D^2+6)+2*D^2*(C+D) := by
  have hq0 : 0 < q := by linarith only [hq]
  have hy0 : 0 < 1/q := one_div_pos.mpr hq0
  have hy1 : 1/q < 1 := (div_lt_one hq0).mpr hq
  have hd : 0 < D := by linarith only [hD]
  have ha : 0 < 2*D^2*(C+D) := by positivity
  have hb : 0 < -D*(D^2+6)+2*D^2*(C+D) := by
    have hp := mul_pos hd (sub_pos.mpr hgap)
    nlinarith only [hp]
  have h1 : 0 ≤ 2*D^2*(C+D)*(1/q)*(1-1/q) := by positivity
  have h2 : 0 ≤ (-D*(D^2+6)+2*D^2*(C+D))*(1-1/q) := by positivity
  have hid : (-D*(D^2+6)+2*D^2*(C+D))-
      (-D*(D^2+6)/q+2*D^2*(C+D)/q^2) =
      2*D^2*(C+D)*(1/q)*(1-1/q)+
      (-D*(D^2+6)+2*D^2*(C+D))*(1-1/q) := by ring
  linarith only [h1,h2,hid]

theorem mhtDeltaC_neg {C D q v vc : ℝ} (hC : C ∈ Icc (1:ℝ) (3/2))
    (hD : 4/3 ≤ D) (hq : 1 < q) (hgap : 6 < D^2+2*C*D)
    (hv : 3/4 ≤ v) (hvc : 0 ≤ vc) : mhtDeltaC C D q v vc < 0 := by
  have hqpart := mhtDeltaC_q_bound hC.1 hD hq hgap
  have hbase : mhtDeltaC C D q (3/4) 0 ≤ mhtDeltaC C D 1 (3/4) 0 := by
    unfold mhtDeltaC
    norm_num only [div_one,one_pow,mul_zero,sub_zero]
    linarith only [hqpart]
  have hC0 : C+1 ≠ 0 := by linarith only [hC.1]
  have hz := mhtZ_pos hC hD
  have hstrict : mhtDeltaC C D 1 (3/4) 0 < 0 := by
    rw [mhtDeltaC_boundary_identity hC0]
    exact div_neg_of_neg_of_pos (mul_neg_of_neg_of_pos (by linarith only [hD]) hz) (by positivity)
  have hy : 0 < mhtTransportY C D := by
    unfold mhtTransportY
    exact mul_pos (by linarith only [hD]) (by linarith only [hC.1,hD])
  have h1 : 0 ≤ (v-3/4)*(D-1)*(8*C*D+20*C+4*D^2+7*D+17) := by
    have hc0 : 0 ≤ C := by linarith only [hC.1]
    have hd0 : 0 ≤ D := by linarith only [hD]
    have hd1 : 0 ≤ D-1 := by linarith only [hD]
    positivity
  have h2 : 0 ≤ vc*mhtTransportY C D*(7*(C+1)+mhtTransportY C D) := by
    have hcp : 0 < C+1 := by linarith only [hC.1]
    positivity
  rw [mhtDeltaC_value_identity]
  linarith only [h1,h2,hbase,hstrict]

end SmoothedOctagon
