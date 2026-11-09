module

public import Mathlib.Analysis.Calculus.Deriv.Inv
public import Mathlib.Analysis.Calculus.Deriv.Pow
public import Mathlib.Analysis.Calculus.MeanValue
public import Mathlib.Analysis.Convex.Deriv

/-!
# The positive quadratic at the raised mixed boundary

Natural product derivatives and a logarithmic-slope fence control the
quadratic minimum. A midpoint tangent proves its positivity.
-/

@[expose] public section

namespace SmoothedOctagon
open Set Real

noncomputable def mhtD (u : ℝ) : ℝ := (u+3)/2
noncomputable def mhtW (u : ℝ) : ℝ := (u+6)/2
noncomputable def mhtY (u : ℝ) : ℝ := (mhtD u-1)*(mhtD u+4)
noncomputable def mhtS (u : ℝ) : ℝ := mhtD u*mhtW u
noncomputable def mhtS1 (u : ℝ) : ℝ := (mhtD u+mhtW u)/2
noncomputable def mhtQ (u : ℝ) : ℝ := mhtD u^2+6
noncomputable def mhtM (u : ℝ) : ℝ := mhtY u*(35/2+mhtY u)
noncomputable def mhtM1 (u : ℝ) : ℝ := (35/2+2*mhtY u)*mhtW u
noncomputable def mhtM2 (u : ℝ) : ℝ := 2*mhtW u^2+(35/2+2*mhtY u)/2
noncomputable def mhtM3 (u : ℝ) : ℝ := 3*mhtW u
noncomputable def mhtEps (u : ℝ) : ℝ := (u^2-u+1)/75
noncomputable def mhtEps1 (u : ℝ) : ℝ := (2*u-1)/75
noncomputable def mhtV (u : ℝ) : ℝ := 3/4+mhtEps u/4
noncomputable def mhtL (u : ℝ) : ℝ := u/(u+6)
noncomputable def mhtL1 (u : ℝ) : ℝ := 3/(2*mhtW u^2)
noncomputable def mhtL2 (u : ℝ) : ℝ := -3/(2*mhtW u^3)
noncomputable def mhtL3 (u : ℝ) : ℝ := 9/(4*mhtW u^4)
noncomputable def mhtL4 (u : ℝ) : ℝ := -9/(2*mhtW u^5)
noncomputable def mhtR0 : ℝ := 3*(5/2)^3*(7-5/2)

/-- Original quadratic products, before any differentiation. -/
noncomputable def mhtA (u : ℝ) : ℝ := mhtS u^2+mhtM u*(1-mhtEps u)/4
noncomputable def mhtA1 (u : ℝ) : ℝ :=
  2*mhtS u*mhtS1 u+(mhtM1 u*(1-mhtEps u)-mhtM u*mhtEps1 u)/4
noncomputable def mhtA2 (u : ℝ) : ℝ :=
  2*mhtS1 u^2+mhtS u+
    (mhtM2 u*(1-mhtEps u)-2*mhtM1 u*mhtEps1 u-mhtM u*(2/75))/4
noncomputable def mhtA3 (u : ℝ) : ℝ :=
  (3/2)*(mhtD u+mhtW u)+
    (mhtM3 u*(1-mhtEps u)-3*mhtM2 u*mhtEps1 u-3*mhtM1 u*(2/75))/4
noncomputable def mhtB (u : ℝ) : ℝ :=
  -mhtS u*(mhtY u-2)+mhtM u*(mhtEps u+mhtL u)
noncomputable def mhtB1 (u : ℝ) : ℝ :=
  -mhtS1 u*(mhtY u-2)-mhtS u*mhtW u+
    mhtM1 u*(mhtEps u+mhtL u)+mhtM u*(mhtEps1 u+mhtL1 u)
noncomputable def mhtB2 (u : ℝ) : ℝ :=
  -(1/2)*(mhtY u-2)-2*mhtS1 u*mhtW u-mhtS u/2+
    mhtM2 u*(mhtEps u+mhtL u)+2*mhtM1 u*(mhtEps1 u+mhtL1 u)+
    mhtM u*(2/75+mhtL2 u)
noncomputable def mhtB3 (u : ℝ) : ℝ :=
  -(3/2)*mhtW u-(3/2)*mhtS1 u+
    mhtM3 u*(mhtEps u+mhtL u)+3*mhtM2 u*(mhtEps1 u+mhtL1 u)+
    3*mhtM1 u*(2/75+mhtL2 u)+mhtM u*mhtL3 u
noncomputable def mhtB4 (u : ℝ) : ℝ :=
  -(3/2)+(3/2)*(mhtEps u+mhtL u)+4*mhtM3 u*(mhtEps1 u+mhtL1 u)+
    6*mhtM2 u*(2/75+mhtL2 u)+4*mhtM1 u*mhtL3 u+mhtM u*mhtL4 u

noncomputable def mhtG0 (u : ℝ) : ℝ :=
  mhtQ u^2-mhtS u*mhtQ u+mhtS u^2-151/4-
    ((35/2)*(mhtV u-1)+34/5)*mhtY u-mhtV u*mhtY u^2
noncomputable def mhtCPart (u : ℝ) : ℝ :=
  mhtQ u^2-mhtS u*mhtQ u+mhtS u^2-151/4+(107/10)*mhtY u+
    mhtM u/4-(5/4)*mhtM u*mhtEps u-6*mhtW u^3-30*mhtW u+45+9*mhtW u^2
noncomputable def mhtCPart1 (u : ℝ) : ℝ :=
  2*mhtQ u*mhtD u-mhtS1 u*mhtQ u-mhtS u*mhtD u+2*mhtS u*mhtS1 u+
    (107/10)*mhtW u+mhtM1 u/4-
    (5/4)*(mhtM1 u*mhtEps u+mhtM u*mhtEps1 u)-9*mhtW u^2-15+9*mhtW u
noncomputable def mhtCPart2 (u : ℝ) : ℝ :=
  2*mhtD u^2+mhtQ u-mhtQ u/2-2*mhtS1 u*mhtD u-mhtS u/2+
    2*mhtS1 u^2+mhtS u+107/20+mhtM2 u/4-
    (5/4)*(mhtM2 u*mhtEps u+2*mhtM1 u*mhtEps1 u+mhtM u*(2/75))-
    9*mhtW u+9/2
noncomputable def mhtCPart3 (u : ℝ) : ℝ :=
  3*mhtD u-(3/2)*mhtD u-(3/2)*mhtS1 u+3*mhtS1 u+mhtM3 u/4-
    (5/4)*(mhtM3 u*mhtEps u+3*mhtM2 u*mhtEps1 u+3*mhtM1 u*(2/75))-9/2
noncomputable def mhtCPart4 (u : ℝ) : ℝ :=
  15/8-(5/4)*((3/2)*mhtEps u+4*mhtM3 u*mhtEps1 u+6*mhtM2 u*(2/75))
noncomputable def mhtC (u : ℝ) : ℝ :=
  mhtCPart u+2*mhtR0/mhtW u-3*mhtR0/mhtW u^2
noncomputable def mhtC1 (u : ℝ) : ℝ :=
  mhtCPart1 u-mhtR0/mhtW u^2+3*mhtR0/mhtW u^3
noncomputable def mhtC2 (u : ℝ) : ℝ :=
  mhtCPart2 u+mhtR0/mhtW u^3-(9/2)*mhtR0/mhtW u^4
noncomputable def mhtC3 (u : ℝ) : ℝ :=
  mhtCPart3 u-(3/2)*mhtR0/mhtW u^4+9*mhtR0/mhtW u^5
noncomputable def mhtC4 (u : ℝ) : ℝ :=
  mhtCPart4 u+3*mhtR0/mhtW u^5-(45/2)*mhtR0/mhtW u^6

local syntax "mht_product_deriv" : tactic
macro_rules
| `(tactic| mht_product_deriv) => `(tactic|
  first
  | assumption
  | exact hasDerivAt_id' _
  | exact hasDerivAt_const _ _
  | apply HasDerivAt.add <;> mht_product_deriv
  | apply HasDerivAt.sub <;> mht_product_deriv
  | apply HasDerivAt.pow <;> mht_product_deriv
  | apply HasDerivAt.mul <;> mht_product_deriv
  | apply HasDerivAt.div <;> first | mht_product_deriv | positivity | assumption
  | apply HasDerivAt.neg <;> mht_product_deriv)






private theorem mhtD_hasDerivAt {u : ℝ} (_hu : u ≠ -6) :
    HasDerivAt mhtD (1/2) u := by
  have hd := (((hasDerivAt_id' u)).add ((hasDerivAt_const u (3 : ℝ)))).div_const (2 : ℝ)
  refine hd.congr_deriv ?_
  norm_num only [Pi.pow_apply,Pi.mul_apply,Pi.add_apply,Pi.sub_apply,Pi.div_apply,Pi.neg_apply,id_eq,zero_mul,mul_zero,one_mul,mul_one,sub_zero,zero_add,add_zero]

private theorem mhtW_hasDerivAt {u : ℝ} (_hu : u ≠ -6) :
    HasDerivAt mhtW (1/2) u := by
  have hd := (((hasDerivAt_id' u)).add ((hasDerivAt_const u (6 : ℝ)))).div_const (2 : ℝ)
  refine hd.congr_deriv ?_
  norm_num only [Pi.pow_apply,Pi.mul_apply,Pi.add_apply,Pi.sub_apply,Pi.div_apply,Pi.neg_apply,id_eq,zero_mul,mul_zero,one_mul,mul_one,sub_zero,zero_add,add_zero]

private theorem mhtY_hasDerivAt {u : ℝ} (_hu : u ≠ -6) :
    HasDerivAt mhtY (mhtW u) u := by
  have hD := mhtD_hasDerivAt _hu
  have hd := ((hD).sub ((hasDerivAt_const u (1 : ℝ)))).mul ((hD).add ((hasDerivAt_const u (4 : ℝ))))
  refine hd.congr_deriv ?_
  norm_num only [Pi.pow_apply,Pi.mul_apply,Pi.add_apply,Pi.sub_apply,Pi.div_apply,Pi.neg_apply,id_eq,zero_mul,mul_zero,one_mul,mul_one,sub_zero,zero_add,add_zero]
  dsimp only [mhtW,mhtD,mhtW,mhtS1,mhtEps1,mhtM1,mhtM2,mhtM3]
  ring

private theorem mhtS_hasDerivAt {u : ℝ} (_hu : u ≠ -6) :
    HasDerivAt mhtS (mhtS1 u) u := by
  have hD := mhtD_hasDerivAt _hu
  have hW := mhtW_hasDerivAt _hu
  have hd := (hD).mul (hW)
  refine hd.congr_deriv ?_
  norm_num only [Pi.pow_apply,Pi.mul_apply,Pi.add_apply,Pi.sub_apply,Pi.div_apply,Pi.neg_apply,id_eq,zero_mul,mul_zero,one_mul,mul_one,sub_zero,zero_add,add_zero]
  dsimp only [mhtS1,mhtD,mhtW,mhtS1,mhtEps1,mhtM1,mhtM2,mhtM3]
  ring

private theorem mhtS1_hasDerivAt {u : ℝ} (_hu : u ≠ -6) :
    HasDerivAt mhtS1 (1/2) u := by
  have hD := mhtD_hasDerivAt _hu
  have hW := mhtW_hasDerivAt _hu
  have hd := ((hD).add (hW)).div_const (2 : ℝ)
  refine hd.congr_deriv ?_
  norm_num only [Pi.pow_apply,Pi.mul_apply,Pi.add_apply,Pi.sub_apply,Pi.div_apply,Pi.neg_apply,id_eq,zero_mul,mul_zero,one_mul,mul_one,sub_zero,zero_add,add_zero]

private theorem mhtQ_hasDerivAt {u : ℝ} (_hu : u ≠ -6) :
    HasDerivAt mhtQ (mhtD u) u := by
  have hD := mhtD_hasDerivAt _hu
  have hd := ((hD).pow 2).add ((hasDerivAt_const u (6 : ℝ)))
  refine hd.congr_deriv ?_
  norm_num only [Pi.pow_apply,Pi.mul_apply,Pi.add_apply,Pi.sub_apply,Pi.div_apply,Pi.neg_apply,id_eq,zero_mul,mul_zero,one_mul,mul_one,sub_zero,zero_add,add_zero]
  dsimp only [mhtD,mhtD,mhtW,mhtS1,mhtEps1,mhtM1,mhtM2,mhtM3]
  ring

private theorem mhtM_hasDerivAt {u : ℝ} (_hu : u ≠ -6) :
    HasDerivAt mhtM (mhtM1 u) u := by
  have hY := mhtY_hasDerivAt _hu
  have hd := (hY).mul (((hasDerivAt_const u ((35/2) : ℝ))).add (hY))
  refine hd.congr_deriv ?_
  norm_num only [Pi.pow_apply,Pi.mul_apply,Pi.add_apply,Pi.sub_apply,Pi.div_apply,Pi.neg_apply,id_eq,zero_mul,mul_zero,one_mul,mul_one,sub_zero,zero_add,add_zero]
  dsimp only [mhtM1,mhtD,mhtW,mhtS1,mhtEps1,mhtM1,mhtM2,mhtM3]
  ring

private theorem mhtM1_hasDerivAt {u : ℝ} (_hu : u ≠ -6) :
    HasDerivAt mhtM1 (mhtM2 u) u := by
  have hY := mhtY_hasDerivAt _hu
  have hW := mhtW_hasDerivAt _hu
  have hd := (((hasDerivAt_const u ((35/2) : ℝ))).add (((hasDerivAt_const u (2 : ℝ))).mul (hY))).mul (hW)
  refine hd.congr_deriv ?_
  norm_num only [Pi.pow_apply,Pi.mul_apply,Pi.add_apply,Pi.sub_apply,Pi.div_apply,Pi.neg_apply,id_eq,zero_mul,mul_zero,one_mul,mul_one,sub_zero,zero_add,add_zero]
  dsimp only [mhtM2,mhtD,mhtW,mhtS1,mhtEps1,mhtM1,mhtM2,mhtM3]
  ring

private theorem mhtM2_hasDerivAt {u : ℝ} (_hu : u ≠ -6) :
    HasDerivAt mhtM2 (mhtM3 u) u := by
  have hY := mhtY_hasDerivAt _hu
  have hW := mhtW_hasDerivAt _hu
  have hd := (((hasDerivAt_const u (2 : ℝ))).mul ((hW).pow 2)).add ((((hasDerivAt_const u ((35/2) : ℝ))).add (((hasDerivAt_const u (2 : ℝ))).mul (hY))).div_const (2 : ℝ))
  refine hd.congr_deriv ?_
  norm_num only [Pi.pow_apply,Pi.mul_apply,Pi.add_apply,Pi.sub_apply,Pi.div_apply,Pi.neg_apply,id_eq,zero_mul,mul_zero,one_mul,mul_one,sub_zero,zero_add,add_zero]
  dsimp only [mhtM3,mhtD,mhtW,mhtS1,mhtEps1,mhtM1,mhtM2,mhtM3]
  ring

private theorem mhtM3_hasDerivAt {u : ℝ} (_hu : u ≠ -6) :
    HasDerivAt mhtM3 (3/2) u := by
  have hW := mhtW_hasDerivAt _hu
  have hd := ((hasDerivAt_const u (3 : ℝ))).mul (hW)
  refine hd.congr_deriv ?_
  norm_num only [Pi.pow_apply,Pi.mul_apply,Pi.add_apply,Pi.sub_apply,Pi.div_apply,Pi.neg_apply,id_eq,zero_mul,mul_zero,one_mul,mul_one,sub_zero,zero_add,add_zero]

private theorem mhtEps_hasDerivAt {u : ℝ} (_hu : u ≠ -6) :
    HasDerivAt mhtEps (mhtEps1 u) u := by
  have hd := (((((hasDerivAt_id' u)).pow 2).sub ((hasDerivAt_id' u))).add ((hasDerivAt_const u (1 : ℝ)))).div_const (75 : ℝ)
  refine hd.congr_deriv ?_
  norm_num only [Pi.pow_apply,Pi.mul_apply,Pi.add_apply,Pi.sub_apply,Pi.div_apply,Pi.neg_apply,id_eq,zero_mul,mul_zero,one_mul,mul_one,sub_zero,zero_add,add_zero]
  dsimp only [mhtEps1,mhtD,mhtW,mhtS1,mhtEps1,mhtM1,mhtM2,mhtM3]
  ring

private theorem mhtEps1_hasDerivAt {u : ℝ} (_hu : u ≠ -6) :
    HasDerivAt mhtEps1 (2/75) u := by
  have hd := ((((hasDerivAt_const u (2 : ℝ))).mul ((hasDerivAt_id' u))).sub ((hasDerivAt_const u (1 : ℝ)))).div_const (75 : ℝ)
  refine hd.congr_deriv ?_
  norm_num only [Pi.pow_apply,Pi.mul_apply,Pi.add_apply,Pi.sub_apply,Pi.div_apply,Pi.neg_apply,id_eq,zero_mul,mul_zero,one_mul,mul_one,sub_zero,zero_add,add_zero]

private theorem mhtL_hasDerivAt {u : ℝ} (_hu : u ≠ -6) :
    HasDerivAt mhtL (mhtL1 u) u := by
  have hden : u+6 ≠ 0 := by intro h; apply _hu; linarith
  have hw : mhtW u ≠ 0 := by unfold mhtW; exact div_ne_zero hden (by norm_num)
  have hd := ((hasDerivAt_id' u)).div (((hasDerivAt_id' u)).add ((hasDerivAt_const u (6 : ℝ)))) hden
  refine hd.congr_deriv ?_
  norm_num only [Pi.pow_apply,Pi.mul_apply,Pi.add_apply,Pi.sub_apply,Pi.div_apply,Pi.neg_apply,id_eq,zero_mul,mul_zero,one_mul,mul_one,sub_zero,zero_add,add_zero]
  dsimp only [mhtL1,mhtD,mhtW,mhtS1,mhtEps1,mhtM1,mhtM2,mhtM3]
  field_simp [hden]
  ring

private theorem mhtL1_hasDerivAt {u : ℝ} (_hu : u ≠ -6) :
    HasDerivAt mhtL1 (mhtL2 u) u := by
  have hW := mhtW_hasDerivAt _hu
  have hden : u+6 ≠ 0 := by intro h; apply _hu; linarith
  have hw : mhtW u ≠ 0 := by unfold mhtW; exact div_ne_zero hden (by norm_num)
  have hd := ((hasDerivAt_const u (3 : ℝ))).div (((hasDerivAt_const u (2 : ℝ))).mul ((hW).pow 2)) (mul_ne_zero (by norm_num) (pow_ne_zero _ hw))
  refine hd.congr_deriv ?_
  norm_num only [Pi.pow_apply,Pi.mul_apply,Pi.add_apply,Pi.sub_apply,Pi.div_apply,Pi.neg_apply,id_eq,zero_mul,mul_zero,one_mul,mul_one,sub_zero,zero_add,add_zero]
  dsimp only [mhtL2,mhtD,mhtW,mhtS1,mhtEps1,mhtM1,mhtM2,mhtM3]
  field_simp [hden]
  ring

private theorem mhtL2_hasDerivAt {u : ℝ} (_hu : u ≠ -6) :
    HasDerivAt mhtL2 (mhtL3 u) u := by
  have hW := mhtW_hasDerivAt _hu
  have hden : u+6 ≠ 0 := by intro h; apply _hu; linarith
  have hw : mhtW u ≠ 0 := by unfold mhtW; exact div_ne_zero hden (by norm_num)
  have hd := ((hasDerivAt_const u (-(3) : ℝ))).div (((hasDerivAt_const u (2 : ℝ))).mul ((hW).pow 3)) (mul_ne_zero (by norm_num) (pow_ne_zero _ hw))
  refine hd.congr_deriv ?_
  norm_num only [Pi.pow_apply,Pi.mul_apply,Pi.add_apply,Pi.sub_apply,Pi.div_apply,Pi.neg_apply,id_eq,zero_mul,mul_zero,one_mul,mul_one,sub_zero,zero_add,add_zero]
  dsimp only [mhtL3,mhtD,mhtW,mhtS1,mhtEps1,mhtM1,mhtM2,mhtM3]
  field_simp [hden]
  ring

private theorem mhtL3_hasDerivAt {u : ℝ} (_hu : u ≠ -6) :
    HasDerivAt mhtL3 (mhtL4 u) u := by
  have hW := mhtW_hasDerivAt _hu
  have hden : u+6 ≠ 0 := by intro h; apply _hu; linarith
  have hw : mhtW u ≠ 0 := by unfold mhtW; exact div_ne_zero hden (by norm_num)
  have hd := ((hasDerivAt_const u (9 : ℝ))).div (((hasDerivAt_const u (4 : ℝ))).mul ((hW).pow 4)) (mul_ne_zero (by norm_num) (pow_ne_zero _ hw))
  refine hd.congr_deriv ?_
  norm_num only [Pi.pow_apply,Pi.mul_apply,Pi.add_apply,Pi.sub_apply,Pi.div_apply,Pi.neg_apply,id_eq,zero_mul,mul_zero,one_mul,mul_one,sub_zero,zero_add,add_zero]
  dsimp only [mhtL4,mhtD,mhtW,mhtS1,mhtEps1,mhtM1,mhtM2,mhtM3]
  field_simp [hden]
  ring

private theorem mhtA_hasDerivAt {u : ℝ} (_hu : u ≠ -6) :
    HasDerivAt mhtA (mhtA1 u) u := by
  have hS := mhtS_hasDerivAt _hu
  have hM := mhtM_hasDerivAt _hu
  have hEps := mhtEps_hasDerivAt _hu
  have hd := ((hS).pow 2).add (((hM).mul (((hasDerivAt_const u (1 : ℝ))).sub (hEps))).div_const (4 : ℝ))
  refine hd.congr_deriv ?_
  norm_num only [Pi.pow_apply,Pi.mul_apply,Pi.add_apply,Pi.sub_apply,Pi.div_apply,Pi.neg_apply,id_eq,zero_mul,mul_zero,one_mul,mul_one,sub_zero,zero_add,add_zero]
  dsimp only [mhtA1,mhtD,mhtW,mhtS1,mhtEps1,mhtM1,mhtM2,mhtM3]
  ring

private theorem mhtA1_hasDerivAt {u : ℝ} (_hu : u ≠ -6) :
    HasDerivAt mhtA1 (mhtA2 u) u := by
  have hS := mhtS_hasDerivAt _hu
  have hS1 := mhtS1_hasDerivAt _hu
  have hM1 := mhtM1_hasDerivAt _hu
  have hEps := mhtEps_hasDerivAt _hu
  have hM := mhtM_hasDerivAt _hu
  have hEps1 := mhtEps1_hasDerivAt _hu
  have hd := ((((hasDerivAt_const u (2 : ℝ))).mul (hS)).mul (hS1)).add ((((hM1).mul (((hasDerivAt_const u (1 : ℝ))).sub (hEps))).sub ((hM).mul (hEps1))).div_const (4 : ℝ))
  refine hd.congr_deriv ?_
  norm_num only [Pi.pow_apply,Pi.mul_apply,Pi.add_apply,Pi.sub_apply,Pi.div_apply,Pi.neg_apply,id_eq,zero_mul,mul_zero,one_mul,mul_one,sub_zero,zero_add,add_zero]
  dsimp only [mhtA2,mhtD,mhtW,mhtS1,mhtEps1,mhtM1,mhtM2,mhtM3]
  ring

private theorem mhtA2_hasDerivAt {u : ℝ} (_hu : u ≠ -6) :
    HasDerivAt mhtA2 (mhtA3 u) u := by
  have hS1 := mhtS1_hasDerivAt _hu
  have hS := mhtS_hasDerivAt _hu
  have hM2 := mhtM2_hasDerivAt _hu
  have hEps := mhtEps_hasDerivAt _hu
  have hM1 := mhtM1_hasDerivAt _hu
  have hEps1 := mhtEps1_hasDerivAt _hu
  have hM := mhtM_hasDerivAt _hu
  have hd := ((((hasDerivAt_const u (2 : ℝ))).mul ((hS1).pow 2)).add (hS)).add (((((hM2).mul (((hasDerivAt_const u (1 : ℝ))).sub (hEps))).sub ((((hasDerivAt_const u (2 : ℝ))).mul (hM1)).mul (hEps1))).sub ((hM).mul ((hasDerivAt_const u ((2/75) : ℝ))))).div_const (4 : ℝ))
  refine hd.congr_deriv ?_
  norm_num only [Pi.pow_apply,Pi.mul_apply,Pi.add_apply,Pi.sub_apply,Pi.div_apply,Pi.neg_apply,id_eq,zero_mul,mul_zero,one_mul,mul_one,sub_zero,zero_add,add_zero]
  dsimp only [mhtA3,mhtD,mhtW,mhtS1,mhtEps1,mhtM1,mhtM2,mhtM3]
  ring

private theorem mhtB_hasDerivAt {u : ℝ} (_hu : u ≠ -6) :
    HasDerivAt mhtB (mhtB1 u) u := by
  have hS := mhtS_hasDerivAt _hu
  have hY := mhtY_hasDerivAt _hu
  have hM := mhtM_hasDerivAt _hu
  have hEps := mhtEps_hasDerivAt _hu
  have hL := mhtL_hasDerivAt _hu
  have hd := (((hS).neg).mul ((hY).sub ((hasDerivAt_const u (2 : ℝ))))).add ((hM).mul ((hEps).add (hL)))
  refine hd.congr_deriv ?_
  norm_num only [Pi.pow_apply,Pi.mul_apply,Pi.add_apply,Pi.sub_apply,Pi.div_apply,Pi.neg_apply,id_eq,zero_mul,mul_zero,one_mul,mul_one,sub_zero,zero_add,add_zero]
  dsimp only [mhtB1,mhtD,mhtW,mhtS1,mhtEps1,mhtM1,mhtM2,mhtM3]
  ring

private theorem mhtB1_hasDerivAt {u : ℝ} (_hu : u ≠ -6) :
    HasDerivAt mhtB1 (mhtB2 u) u := by
  have hS1 := mhtS1_hasDerivAt _hu
  have hY := mhtY_hasDerivAt _hu
  have hS := mhtS_hasDerivAt _hu
  have hW := mhtW_hasDerivAt _hu
  have hM1 := mhtM1_hasDerivAt _hu
  have hEps := mhtEps_hasDerivAt _hu
  have hL := mhtL_hasDerivAt _hu
  have hM := mhtM_hasDerivAt _hu
  have hEps1 := mhtEps1_hasDerivAt _hu
  have hL1 := mhtL1_hasDerivAt _hu
  have hd := (((((hS1).neg).mul ((hY).sub ((hasDerivAt_const u (2 : ℝ))))).sub ((hS).mul (hW))).add ((hM1).mul ((hEps).add (hL)))).add ((hM).mul ((hEps1).add (hL1)))
  refine hd.congr_deriv ?_
  norm_num only [Pi.pow_apply,Pi.mul_apply,Pi.add_apply,Pi.sub_apply,Pi.div_apply,Pi.neg_apply,id_eq,zero_mul,mul_zero,one_mul,mul_one,sub_zero,zero_add,add_zero]
  dsimp only [mhtB2,mhtD,mhtW,mhtS1,mhtEps1,mhtM1,mhtM2,mhtM3]
  ring

private theorem mhtB2_hasDerivAt {u : ℝ} (_hu : u ≠ -6) :
    HasDerivAt mhtB2 (mhtB3 u) u := by
  have hY := mhtY_hasDerivAt _hu
  have hS1 := mhtS1_hasDerivAt _hu
  have hW := mhtW_hasDerivAt _hu
  have hS := mhtS_hasDerivAt _hu
  have hM2 := mhtM2_hasDerivAt _hu
  have hEps := mhtEps_hasDerivAt _hu
  have hL := mhtL_hasDerivAt _hu
  have hM1 := mhtM1_hasDerivAt _hu
  have hEps1 := mhtEps1_hasDerivAt _hu
  have hL1 := mhtL1_hasDerivAt _hu
  have hM := mhtM_hasDerivAt _hu
  have hL2 := mhtL2_hasDerivAt _hu
  have hd := (((((((hasDerivAt_const u (-((1/2)) : ℝ))).mul ((hY).sub ((hasDerivAt_const u (2 : ℝ))))).sub ((((hasDerivAt_const u (2 : ℝ))).mul (hS1)).mul (hW))).sub ((hS).div_const (2 : ℝ))).add ((hM2).mul ((hEps).add (hL)))).add ((((hasDerivAt_const u (2 : ℝ))).mul (hM1)).mul ((hEps1).add (hL1)))).add ((hM).mul (((hasDerivAt_const u ((2/75) : ℝ))).add (hL2)))
  refine hd.congr_deriv ?_
  norm_num only [Pi.pow_apply,Pi.mul_apply,Pi.add_apply,Pi.sub_apply,Pi.div_apply,Pi.neg_apply,id_eq,zero_mul,mul_zero,one_mul,mul_one,sub_zero,zero_add,add_zero]
  dsimp only [mhtB3,mhtD,mhtW,mhtS1,mhtEps1,mhtM1,mhtM2,mhtM3]
  ring

private theorem mhtB3_hasDerivAt {u : ℝ} (_hu : u ≠ -6) :
    HasDerivAt mhtB3 (mhtB4 u) u := by
  have hW := mhtW_hasDerivAt _hu
  have hS1 := mhtS1_hasDerivAt _hu
  have hM3 := mhtM3_hasDerivAt _hu
  have hEps := mhtEps_hasDerivAt _hu
  have hL := mhtL_hasDerivAt _hu
  have hM2 := mhtM2_hasDerivAt _hu
  have hEps1 := mhtEps1_hasDerivAt _hu
  have hL1 := mhtL1_hasDerivAt _hu
  have hM1 := mhtM1_hasDerivAt _hu
  have hL2 := mhtL2_hasDerivAt _hu
  have hM := mhtM_hasDerivAt _hu
  have hL3 := mhtL3_hasDerivAt _hu
  have hd := (((((((hasDerivAt_const u (-((3/2)) : ℝ))).mul (hW)).sub (((hasDerivAt_const u ((3/2) : ℝ))).mul (hS1))).add ((hM3).mul ((hEps).add (hL)))).add ((((hasDerivAt_const u (3 : ℝ))).mul (hM2)).mul ((hEps1).add (hL1)))).add ((((hasDerivAt_const u (3 : ℝ))).mul (hM1)).mul (((hasDerivAt_const u ((2/75) : ℝ))).add (hL2)))).add ((hM).mul (hL3))
  refine hd.congr_deriv ?_
  norm_num only [Pi.pow_apply,Pi.mul_apply,Pi.add_apply,Pi.sub_apply,Pi.div_apply,Pi.neg_apply,id_eq,zero_mul,mul_zero,one_mul,mul_one,sub_zero,zero_add,add_zero]
  dsimp only [mhtB4,mhtD,mhtW,mhtS1,mhtEps1,mhtM1,mhtM2,mhtM3]
  ring

private theorem mhtCPart_hasDerivAt {u : ℝ} (_hu : u ≠ -6) :
    HasDerivAt mhtCPart (mhtCPart1 u) u := by
  have hQ := mhtQ_hasDerivAt _hu
  have hS := mhtS_hasDerivAt _hu
  have hY := mhtY_hasDerivAt _hu
  have hM := mhtM_hasDerivAt _hu
  have hEps := mhtEps_hasDerivAt _hu
  have hW := mhtW_hasDerivAt _hu
  have hd := (((((((((((hQ).pow 2).sub ((hS).mul (hQ))).add ((hS).pow 2)).sub ((hasDerivAt_const u ((151/4) : ℝ)))).add (((hasDerivAt_const u ((107/10) : ℝ))).mul (hY))).add ((hM).div_const (4 : ℝ))).sub ((((hasDerivAt_const u ((5/4) : ℝ))).mul (hM)).mul (hEps))).sub (((hasDerivAt_const u (6 : ℝ))).mul ((hW).pow 3))).sub (((hasDerivAt_const u (30 : ℝ))).mul (hW))).add ((hasDerivAt_const u (45 : ℝ)))).add (((hasDerivAt_const u (9 : ℝ))).mul ((hW).pow 2))
  refine hd.congr_deriv ?_
  norm_num only [Pi.pow_apply,Pi.mul_apply,Pi.add_apply,Pi.sub_apply,Pi.div_apply,Pi.neg_apply,id_eq,zero_mul,mul_zero,one_mul,mul_one,sub_zero,zero_add,add_zero]
  dsimp only [mhtCPart1,mhtD,mhtW,mhtS1,mhtEps1,mhtM1,mhtM2,mhtM3]
  ring

private theorem mhtCPart1_hasDerivAt {u : ℝ} (_hu : u ≠ -6) :
    HasDerivAt mhtCPart1 (mhtCPart2 u) u := by
  have hQ := mhtQ_hasDerivAt _hu
  have hD := mhtD_hasDerivAt _hu
  have hS1 := mhtS1_hasDerivAt _hu
  have hS := mhtS_hasDerivAt _hu
  have hW := mhtW_hasDerivAt _hu
  have hM1 := mhtM1_hasDerivAt _hu
  have hEps := mhtEps_hasDerivAt _hu
  have hM := mhtM_hasDerivAt _hu
  have hEps1 := mhtEps1_hasDerivAt _hu
  have hd := ((((((((((((hasDerivAt_const u (2 : ℝ))).mul (hQ)).mul (hD)).sub ((hS1).mul (hQ))).sub ((hS).mul (hD))).add ((((hasDerivAt_const u (2 : ℝ))).mul (hS)).mul (hS1))).add (((hasDerivAt_const u ((107/10) : ℝ))).mul (hW))).add ((hM1).div_const (4 : ℝ))).sub (((hasDerivAt_const u ((5/4) : ℝ))).mul (((hM1).mul (hEps)).add ((hM).mul (hEps1))))).sub (((hasDerivAt_const u (9 : ℝ))).mul ((hW).pow 2))).sub ((hasDerivAt_const u (15 : ℝ)))).add (((hasDerivAt_const u (9 : ℝ))).mul (hW))
  refine hd.congr_deriv ?_
  norm_num only [Pi.pow_apply,Pi.mul_apply,Pi.add_apply,Pi.sub_apply,Pi.div_apply,Pi.neg_apply,id_eq,zero_mul,mul_zero,one_mul,mul_one,sub_zero,zero_add,add_zero]
  dsimp only [mhtCPart2,mhtD,mhtW,mhtS1,mhtEps1,mhtM1,mhtM2,mhtM3]
  ring

private theorem mhtCPart2_hasDerivAt {u : ℝ} (_hu : u ≠ -6) :
    HasDerivAt mhtCPart2 (mhtCPart3 u) u := by
  have hD := mhtD_hasDerivAt _hu
  have hQ := mhtQ_hasDerivAt _hu
  have hS1 := mhtS1_hasDerivAt _hu
  have hS := mhtS_hasDerivAt _hu
  have hM2 := mhtM2_hasDerivAt _hu
  have hEps := mhtEps_hasDerivAt _hu
  have hM1 := mhtM1_hasDerivAt _hu
  have hEps1 := mhtEps1_hasDerivAt _hu
  have hM := mhtM_hasDerivAt _hu
  have hW := mhtW_hasDerivAt _hu
  have hd := (((((((((((((hasDerivAt_const u (2 : ℝ))).mul ((hD).pow 2)).add (hQ)).sub ((hQ).div_const (2 : ℝ))).sub ((((hasDerivAt_const u (2 : ℝ))).mul (hS1)).mul (hD))).sub ((hS).div_const (2 : ℝ))).add (((hasDerivAt_const u (2 : ℝ))).mul ((hS1).pow 2))).add (hS)).add ((hasDerivAt_const u ((107/20) : ℝ)))).add ((hM2).div_const (4 : ℝ))).sub (((hasDerivAt_const u ((5/4) : ℝ))).mul ((((hM2).mul (hEps)).add ((((hasDerivAt_const u (2 : ℝ))).mul (hM1)).mul (hEps1))).add ((hM).mul ((hasDerivAt_const u ((2/75) : ℝ))))))).sub (((hasDerivAt_const u (9 : ℝ))).mul (hW))).add ((hasDerivAt_const u ((9/2) : ℝ)))
  refine hd.congr_deriv ?_
  norm_num only [Pi.pow_apply,Pi.mul_apply,Pi.add_apply,Pi.sub_apply,Pi.div_apply,Pi.neg_apply,id_eq,zero_mul,mul_zero,one_mul,mul_one,sub_zero,zero_add,add_zero]
  dsimp only [mhtCPart3,mhtD,mhtW,mhtS1,mhtEps1,mhtM1,mhtM2,mhtM3]
  ring

private theorem mhtCPart3_hasDerivAt {u : ℝ} (_hu : u ≠ -6) :
    HasDerivAt mhtCPart3 (mhtCPart4 u) u := by
  have hD := mhtD_hasDerivAt _hu
  have hS1 := mhtS1_hasDerivAt _hu
  have hM3 := mhtM3_hasDerivAt _hu
  have hEps := mhtEps_hasDerivAt _hu
  have hM2 := mhtM2_hasDerivAt _hu
  have hEps1 := mhtEps1_hasDerivAt _hu
  have hM1 := mhtM1_hasDerivAt _hu
  have hd := ((((((((hasDerivAt_const u (3 : ℝ))).mul (hD)).sub (((hasDerivAt_const u ((3/2) : ℝ))).mul (hD))).sub (((hasDerivAt_const u ((3/2) : ℝ))).mul (hS1))).add (((hasDerivAt_const u (3 : ℝ))).mul (hS1))).add ((hM3).div_const (4 : ℝ))).sub (((hasDerivAt_const u ((5/4) : ℝ))).mul ((((hM3).mul (hEps)).add ((((hasDerivAt_const u (3 : ℝ))).mul (hM2)).mul (hEps1))).add ((((hasDerivAt_const u (3 : ℝ))).mul (hM1)).mul ((hasDerivAt_const u ((2/75) : ℝ))))))).sub ((hasDerivAt_const u ((9/2) : ℝ)))
  refine hd.congr_deriv ?_
  norm_num only [Pi.pow_apply,Pi.mul_apply,Pi.add_apply,Pi.sub_apply,Pi.div_apply,Pi.neg_apply,id_eq,zero_mul,mul_zero,one_mul,mul_one,sub_zero,zero_add,add_zero]
  dsimp only [mhtCPart4,mhtD,mhtW,mhtS1,mhtEps1,mhtM1,mhtM2,mhtM3]
  ring

private theorem mhtC_hasDerivAt {u : ℝ} (_hu : u ≠ -6) :
    HasDerivAt mhtC (mhtC1 u) u := by
  have hCPart := mhtCPart_hasDerivAt _hu
  have hW := mhtW_hasDerivAt _hu
  have hden : u+6 ≠ 0 := by intro h; apply _hu; linarith
  have hw : mhtW u ≠ 0 := by unfold mhtW; exact div_ne_zero hden (by norm_num)
  have hd := ((hCPart).add (((hasDerivAt_const u ((2*mhtR0) : ℝ))).div (hW) hw)).sub (((hasDerivAt_const u ((3*mhtR0) : ℝ))).div ((hW).pow 2) (pow_ne_zero _ hw))
  refine hd.congr_deriv ?_
  norm_num only [Pi.pow_apply,Pi.mul_apply,Pi.add_apply,Pi.sub_apply,Pi.div_apply,Pi.neg_apply,id_eq,zero_mul,mul_zero,one_mul,mul_one,sub_zero,zero_add,add_zero]
  dsimp only [mhtC1,mhtD,mhtW,mhtS1,mhtEps1,mhtM1,mhtM2,mhtM3]
  field_simp [hden]
  ring

private theorem mhtC1_hasDerivAt {u : ℝ} (_hu : u ≠ -6) :
    HasDerivAt mhtC1 (mhtC2 u) u := by
  have hCPart1 := mhtCPart1_hasDerivAt _hu
  have hW := mhtW_hasDerivAt _hu
  have hden : u+6 ≠ 0 := by intro h; apply _hu; linarith
  have hw : mhtW u ≠ 0 := by unfold mhtW; exact div_ne_zero hden (by norm_num)
  have hd := ((hCPart1).sub (((hasDerivAt_const u (mhtR0 : ℝ))).div ((hW).pow 2) (pow_ne_zero _ hw))).add (((hasDerivAt_const u ((3*mhtR0) : ℝ))).div ((hW).pow 3) (pow_ne_zero _ hw))
  refine hd.congr_deriv ?_
  norm_num only [Pi.pow_apply,Pi.mul_apply,Pi.add_apply,Pi.sub_apply,Pi.div_apply,Pi.neg_apply,id_eq,zero_mul,mul_zero,one_mul,mul_one,sub_zero,zero_add,add_zero]
  dsimp only [mhtC2,mhtD,mhtW,mhtS1,mhtEps1,mhtM1,mhtM2,mhtM3]
  field_simp [hden]
  ring

private theorem mhtC2_hasDerivAt {u : ℝ} (_hu : u ≠ -6) :
    HasDerivAt mhtC2 (mhtC3 u) u := by
  have hCPart2 := mhtCPart2_hasDerivAt _hu
  have hW := mhtW_hasDerivAt _hu
  have hden : u+6 ≠ 0 := by intro h; apply _hu; linarith
  have hw : mhtW u ≠ 0 := by unfold mhtW; exact div_ne_zero hden (by norm_num)
  have hd := ((hCPart2).add (((hasDerivAt_const u (mhtR0 : ℝ))).div ((hW).pow 3) (pow_ne_zero _ hw))).sub (((hasDerivAt_const u (((9/2)*mhtR0) : ℝ))).div ((hW).pow 4) (pow_ne_zero _ hw))
  refine hd.congr_deriv ?_
  norm_num only [Pi.pow_apply,Pi.mul_apply,Pi.add_apply,Pi.sub_apply,Pi.div_apply,Pi.neg_apply,id_eq,zero_mul,mul_zero,one_mul,mul_one,sub_zero,zero_add,add_zero]
  dsimp only [mhtC3,mhtD,mhtW,mhtS1,mhtEps1,mhtM1,mhtM2,mhtM3]
  field_simp [hden]
  ring

private theorem mhtC3_hasDerivAt {u : ℝ} (_hu : u ≠ -6) :
    HasDerivAt mhtC3 (mhtC4 u) u := by
  have hCPart3 := mhtCPart3_hasDerivAt _hu
  have hW := mhtW_hasDerivAt _hu
  have hden : u+6 ≠ 0 := by intro h; apply _hu; linarith
  have hw : mhtW u ≠ 0 := by unfold mhtW; exact div_ne_zero hden (by norm_num)
  have hd := ((hCPart3).sub (((hasDerivAt_const u (((3/2)*mhtR0) : ℝ))).div ((hW).pow 4) (pow_ne_zero _ hw))).add (((hasDerivAt_const u ((9*mhtR0) : ℝ))).div ((hW).pow 5) (pow_ne_zero _ hw))
  refine hd.congr_deriv ?_
  norm_num only [Pi.pow_apply,Pi.mul_apply,Pi.add_apply,Pi.sub_apply,Pi.div_apply,Pi.neg_apply,id_eq,zero_mul,mul_zero,one_mul,mul_one,sub_zero,zero_add,add_zero]
  dsimp only [mhtC4,mhtD,mhtW,mhtS1,mhtEps1,mhtM1,mhtM2,mhtM3]
  field_simp [hden]
  ring


/-- These are exactly the paper's three quadratic coefficients. -/
theorem mht_coefficients {u : ℝ} (hu : u ≠ -6) :
    mhtA u = mhtD u^2*mhtW u^2+mhtM u*(1-mhtEps u)/4 ∧
    mhtB u = -mhtD u*mhtW u*(mhtY u-2)+mhtM u*(mhtEps u+u/(u+6)) ∧
    mhtC u = mhtG0 u-mhtM u*(mhtEps u-u^2/(u+6)^2) := by
  constructor
  · unfold mhtA mhtS; ring
  constructor
  · unfold mhtB mhtS mhtL; ring
  have h6 : u+6 ≠ 0 := by intro h; apply hu; linarith
  unfold mhtC mhtCPart mhtG0 mhtS mhtQ mhtR0 mhtV mhtM mhtY mhtD mhtW mhtEps
  field_simp [h6]
  ring

theorem mhtA_third_identity {u : ℝ} (_hu : u ≠ -6) :
    mhtA3 u = (3/2)*(mhtD u+mhtW u)+
      (mhtM3 u*(1-mhtEps u)-3*mhtM2 u*mhtEps1 u-3*mhtM1 u*(2/75))/4 := rfl

theorem mhtB_fourth_identity {u : ℝ} (hu : u ≠ -6) :
    mhtB4 u = (3/2)*mhtEps u+12*mhtW u*mhtEps1 u+
      (4/25)*mhtM2 u+3*mhtR0/(2*mhtW u^5) := by
  have h6 : u+6 ≠ 0 := by intro h; apply hu; linarith
  unfold mhtB4 mhtM3 mhtM2 mhtM1 mhtM mhtL mhtL1 mhtL2 mhtL3 mhtL4 mhtEps1 mhtEps mhtR0 mhtY mhtD mhtW
  field_simp [h6]
  ring

theorem mhtC_fourth_identity {u : ℝ} (hu : u ≠ -6) :
    mhtC4 u = -(3/2)*mhtW u^2+(13/4)*mhtW u+3/10+
      3*mhtR0*(2*mhtW u-15)/(2*mhtW u^6) := by
  have h6 : u+6 ≠ 0 := by intro h; apply hu; linarith
  unfold mhtC4 mhtCPart4 mhtM3 mhtM2 mhtEps1 mhtEps mhtR0 mhtY mhtD mhtW
  field_simp [h6]
  ring

/-- Natural geometric ranges of the one-dimensional quadratic. -/
theorem mht_geometry {u : ℝ} (hu : u ∈ Icc (0:ℝ) (2/3)) :
    3/2 ≤ mhtD u ∧ mhtD u ≤ 11/6 ∧ 3 ≤ mhtW u ∧ mhtW u ≤ 10/3 ∧
    0 < mhtY u ∧ mhtY u < 5 ∧ 0 < mhtM u ∧
    0 < mhtEps u ∧ mhtEps u ≤ 1/75 ∧
    -(1/75) ≤ mhtEps1 u ∧ mhtEps1 u ≤ 1/225 := by
  have hd0 : 3/2 ≤ mhtD u := by simp [mhtD]; linarith only [hu.1]
  have hd1 : mhtD u ≤ 11/6 := by simp [mhtD]; linarith only [hu.2]
  have hw0 : 3 ≤ mhtW u := by simp [mhtW]; linarith only [hu.1]
  have hw1 : mhtW u ≤ 10/3 := by simp [mhtW]; linarith only [hu.2]
  have hyid : mhtY u = mhtW u^2-25/4 := by
    simp [mhtY,mhtD,mhtW]; ring
  have hy0 : 0 < mhtY u := by rw [hyid]; nlinarith only [sq_nonneg (mhtW u-3),hw0]
  have hw2 : mhtW u^2 ≤ (10/3:ℝ)^2 := by nlinarith only [hw0,hw1,sq_nonneg (mhtW u-10/3)]
  have hy1 : mhtY u < 5 := by rw [hyid]; linarith only [hw2]
  have hm : 0 < mhtM u := by unfold mhtM; positivity
  have he0 : 0 < mhtEps u := by
    unfold mhtEps
    nlinarith only [sq_nonneg (u-1/2)]
  have he1 : mhtEps u ≤ 1/75 := by
    have hprod : 0 ≤ u*(1-u) := mul_nonneg hu.1 (by linarith only [hu.2])
    unfold mhtEps
    nlinarith only [hprod]
  have he10 : -(1/75) ≤ mhtEps1 u := by unfold mhtEps1; linarith only [hu.1]
  have he11 : mhtEps1 u ≤ 1/225 := by unfold mhtEps1; linarith only [hu.2]
  exact ⟨hd0,hd1,hw0,hw1,hy0,hy1,hm,he0,he1,he10,he11⟩

theorem mhtM_derivative_bounds {u : ℝ} (hu : u ∈ Icc (0:ℝ) (2/3)) :
    0 < mhtM1 u ∧ mhtM1 u < 28*mhtW u ∧
    0 < mhtM2 u ∧ mhtM2 u < 12*mhtW u := by
  obtain ⟨_,_,hw0,hw1,hy0,hy1,_⟩ := mht_geometry hu
  have hw : 0 < mhtW u := by linarith only [hw0]
  have hm1 : 0 < mhtM1 u := by unfold mhtM1; positivity
  have hm1b : mhtM1 u < 28*mhtW u := by
    unfold mhtM1
    nlinarith only [mul_pos (by linarith only [hy1] : 0 < 28-(35/2+2*mhtY u)) hw]
  have hm2 : 0 < mhtM2 u := by unfold mhtM2; positivity
  have hprod : 0 ≤ mhtW u*(10/3-mhtW u) := mul_nonneg hw.le (by linarith only [hw1])
  have hm2b : mhtM2 u < 12*mhtW u := by
    unfold mhtM2
    nlinarith only [hprod,hy1,hw0]
  exact ⟨hm1,hm1b,hm2,hm2b⟩

theorem mhtA3_pos {u : ℝ} (hu : u ∈ Icc (0:ℝ) (2/3)) : 0 < mhtA3 u := by
  obtain ⟨hd0,_,hw0,_,_,_,_,_,he1,_,he11⟩ := mht_geometry hu
  obtain ⟨hm1,hm1b,hm2,hm2b⟩ := mhtM_derivative_bounds hu
  rw [mhtA_third_identity (by linarith only [hu.1])]
  have hlow : (3*mhtW u)*(74/75) ≤ mhtM3 u*(1-mhtEps u) := by
    unfold mhtM3
    exact mul_le_mul_of_nonneg_left (by linarith only [he1]) (by linarith only [hw0])
  have hc2 := mul_le_mul_of_nonneg_left he11 hm2.le
  have hc2b := mul_lt_mul_of_pos_right hm2b (by norm_num : (0:ℝ)<1/225)
  have hc1b := mul_lt_mul_of_pos_right hm1b (by norm_num : (0:ℝ)<2/75)
  nlinarith only [hlow,hc2,hc2b,hc1b,hd0,hw0]

theorem mhtB4_pos {u : ℝ} (hu : u ∈ Icc (0:ℝ) (2/3)) : 0 < mhtB4 u := by
  obtain ⟨_,_,hw0,hw1,hy0,_,_,he0,_,he10,_⟩ := mht_geometry hu
  rw [mhtB_fourth_identity (by linarith only [hu.1])]
  have hwe : -(mhtW u/75) ≤ mhtW u*mhtEps1 u := by
    nlinarith only [mul_le_mul_of_nonneg_left he10 (by linarith only [hw0] : 0≤mhtW u)]
  have hpole : 0 < 3*mhtR0/(2*mhtW u^5) := by unfold mhtR0; positivity
  unfold mhtM2
  nlinarith only [hwe,hpole,he0,hy0,hw0,sq_nonneg (mhtW u-3)]

theorem mhtC4_neg {u : ℝ} (hu : u ∈ Icc (0:ℝ) (2/3)) : mhtC4 u < 0 := by
  obtain ⟨_,_,hw0,hw1,_⟩ := mht_geometry hu
  rw [mhtC_fourth_identity (by linarith only [hu.1])]
  have hpole : 3*mhtR0*(2*mhtW u-15)/(2*mhtW u^6) < 0 := by
    apply div_neg_of_neg_of_pos
    · apply mul_neg_of_pos_of_neg
      · unfold mhtR0; norm_num
      · linarith only [hw1]
    · have : 0 < mhtW u := by linarith only [hw0]
      positivity
  have hprod : 0 ≤ (mhtW u-3)*(6*mhtW u+5) := mul_nonneg (by linarith only [hw0]) (by linarith only [hw0])
  nlinarith only [hpole,hprod]


private theorem mht_le_of_deriv {f f' : ℝ → ℝ} {x y : ℝ} (hxy : x ≤ y)
    (hd : ∀ z ∈ Icc x y, HasDerivAt f (f' z) z)
    (hn : ∀ z ∈ Ioo x y, 0 ≤ f' z) : f x ≤ f y := by
  have hm : MonotoneOn f (Icc x y) := by
    apply monotoneOn_of_deriv_nonneg (convex_Icc x y)
    · exact fun z hz => (hd z hz).continuousAt.continuousWithinAt
    · intro z hz
      exact (hd z (interior_subset hz)).differentiableAt.differentiableWithinAt
    · intro z hz
      rw [(hd z (interior_subset hz)).deriv]
      exact hn z (by simpa only [interior_Icc] using hz)
  exact hm (left_mem_Icc.mpr hxy) (right_mem_Icc.mpr hxy) hxy

private theorem mht_fence {f f' : ℝ → ℝ} {lo hi B : ℝ}
    (hd : ∀ x ∈ Icc lo hi, HasDerivAt f (f' x) x) (hinit : f lo ≤ B)
    (hcross : ∀ x ∈ Ico lo hi, f x = B → f' x < 0) :
    ∀ x ∈ Icc lo hi, f x ≤ B := by
  have hh := image_le_of_deriv_right_lt_deriv_boundary
    (f := f) (f' := f') (a := lo) (b := hi)
    (B := fun _ => B) (B' := fun _ => 0)
    (fun x hx => (hd x hx).continuousAt.continuousWithinAt)
    (fun x hx => (hd x (Ico_subset_Icc_self hx)).hasDerivWithinAt)
    hinit (fun x => hasDerivAt_const x B) hcross
  exact fun x hx => hh hx

private theorem mht_convex_tangent {S : Set ℝ} {f : ℝ → ℝ} {m x d : ℝ}
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

private theorem mht_concave_ge_min {f : ℝ → ℝ} {lo hi x : ℝ}
    (hc : ConcaveOn ℝ (Icc lo hi) f) (hx : x ∈ Icc lo hi) :
    min (f lo) (f hi) ≤ f x := by
  have hle : lo ≤ hi := le_trans hx.1 hx.2
  apply hc.ge_on_segment ⟨le_rfl,hle⟩ ⟨hle,le_rfl⟩
  simpa only [segment_eq_Icc hle] using hx

noncomputable def mhtEll : ℝ := mhtA1 0/mhtA 0
noncomputable def mhtLogDeriv (u : ℝ) : ℝ := mhtA1 u/mhtA u
noncomputable def mhtLogDeriv1 (u : ℝ) : ℝ := mhtA2 u/mhtA u-mhtLogDeriv u^2
noncomputable def mhtE (u : ℝ) : ℝ := mhtB1 u-mhtB u*mhtLogDeriv u
noncomputable def mhtE1 (u : ℝ) : ℝ :=
  mhtB2 u-mhtE u*mhtLogDeriv u-mhtB u*mhtA2 u/mhtA u
noncomputable def mhtQuot (u : ℝ) : ℝ := mhtB u^2/mhtA u
noncomputable def mhtQuot1 (u : ℝ) : ℝ :=
  2*mhtB u*mhtB1 u/mhtA u-mhtB u^2*mhtA1 u/mhtA u^2
noncomputable def mhtQuot2 (u : ℝ) : ℝ :=
  2/mhtA u*(mhtE u^2+mhtB u*mhtB2 u-mhtB u^2*mhtA2 u/(2*mhtA u))
noncomputable def mhtMin (u : ℝ) : ℝ := mhtC u-mhtQuot u/4
noncomputable def mhtMin1 (u : ℝ) : ℝ := mhtC1 u-mhtQuot1 u/4
noncomputable def mhtMin2 (u : ℝ) : ℝ := mhtC2 u-mhtQuot2 u/4

/-- All fixed checks are evaluations of the displayed row products. -/
theorem mht_A_endpoints :
    0 < mhtA1 0 ∧ 0 < mhtA2 0 ∧
    mhtA2 (2/3) < mhtA1 0 ∧ 1 < mhtEll := by
  norm_num [mhtEll,mhtLogDeriv,mhtE,mhtQuot,mhtQuot1,mhtMin,mhtMin1,mhtD,mhtW,mhtY,mhtS,mhtS1,mhtQ,mhtM,mhtM1,mhtM2,mhtM3,mhtEps,mhtEps1,mhtV,mhtL,mhtL1,mhtL2,mhtL3,mhtL4,mhtR0,mhtG0,mhtCPart,mhtCPart1,mhtCPart2,mhtCPart3,mhtCPart4,mhtA,mhtA1,mhtA2,mhtA3,mhtB,mhtB1,mhtB2,mhtB3,mhtB4,mhtC,mhtC1,mhtC2,mhtC3,mhtC4]

theorem mht_B_endpoints :
    mhtB 0 < 0 ∧ mhtB1 (2/3) < 0 ∧ 0 < mhtB2 0 ∧ 0 < mhtB3 0 ∧
    3*mhtEll < mhtB2 0 ∧ mhtB 0*mhtB2 0 < -9 := by
  norm_num [mhtEll,mhtLogDeriv,mhtE,mhtQuot,mhtQuot1,mhtMin,mhtMin1,mhtD,mhtW,mhtY,mhtS,mhtS1,mhtQ,mhtM,mhtM1,mhtM2,mhtM3,mhtEps,mhtEps1,mhtV,mhtL,mhtL1,mhtL2,mhtL3,mhtL4,mhtR0,mhtG0,mhtCPart,mhtCPart1,mhtCPart2,mhtCPart3,mhtCPart4,mhtA,mhtA1,mhtA2,mhtA3,mhtB,mhtB1,mhtB2,mhtB3,mhtB4,mhtC,mhtC1,mhtC2,mhtC3,mhtC4]

theorem mht_C_endpoints : 0 < mhtC2 0 ∧ 0 < mhtC2 (2/3) := by
  norm_num [mhtEll,mhtLogDeriv,mhtE,mhtQuot,mhtQuot1,mhtMin,mhtMin1,mhtD,mhtW,mhtY,mhtS,mhtS1,mhtQ,mhtM,mhtM1,mhtM2,mhtM3,mhtEps,mhtEps1,mhtV,mhtL,mhtL1,mhtL2,mhtL3,mhtL4,mhtR0,mhtG0,mhtCPart,mhtCPart1,mhtCPart2,mhtCPart3,mhtCPart4,mhtA,mhtA1,mhtA2,mhtA3,mhtB,mhtB1,mhtB2,mhtB3,mhtB4,mhtC,mhtC1,mhtC2,mhtC3,mhtC4]

theorem mht_E_endpoints : -3 < mhtE 0 ∧ mhtE 0 < 3 ∧ mhtE (2/3) < 3 := by
  norm_num [mhtEll,mhtLogDeriv,mhtE,mhtQuot,mhtQuot1,mhtMin,mhtMin1,mhtD,mhtW,mhtY,mhtS,mhtS1,mhtQ,mhtM,mhtM1,mhtM2,mhtM3,mhtEps,mhtEps1,mhtV,mhtL,mhtL1,mhtL2,mhtL3,mhtL4,mhtR0,mhtG0,mhtCPart,mhtCPart1,mhtCPart2,mhtCPart3,mhtCPart4,mhtA,mhtA1,mhtA2,mhtA3,mhtB,mhtB1,mhtB2,mhtB3,mhtB4,mhtC,mhtC1,mhtC2,mhtC3,mhtC4]

theorem mht_min_midpoint :
    mhtMin1 (1/3) < 0 ∧ 0 < mhtMin (1/3)+(1/3)*mhtMin1 (1/3) := by
  norm_num [mhtEll,mhtLogDeriv,mhtE,mhtQuot,mhtQuot1,mhtMin,mhtMin1,mhtD,mhtW,mhtY,mhtS,mhtS1,mhtQ,mhtM,mhtM1,mhtM2,mhtM3,mhtEps,mhtEps1,mhtV,mhtL,mhtL1,mhtL2,mhtL3,mhtL4,mhtR0,mhtG0,mhtCPart,mhtCPart1,mhtCPart2,mhtCPart3,mhtCPart4,mhtA,mhtA1,mhtA2,mhtA3,mhtB,mhtB1,mhtB2,mhtB3,mhtB4,mhtC,mhtC1,mhtC2,mhtC3,mhtC4]

/-- Coefficient geometry established from the natural third/fourth derivatives. -/
theorem mht_A_bounds {u : ℝ} (hu : u ∈ Icc (0:ℝ) (2/3)) :
    0 < mhtA u ∧ 0 < mhtA1 u ∧ 0 < mhtA2 u ∧ mhtA2 u < mhtA1 u := by
  have hne : u ≠ -6 := by linarith only [hu.1]
  obtain ⟨_,_,hw0,_,_,_,hm,_,he,_⟩ := mht_geometry hu
  have ha : 0 < mhtA u := by
    rw [(mht_coefficients hne).1]
    have : 0 < mhtD u := by have := (mht_geometry hu).1; linarith
    have : 0 < mhtW u := by linarith only [hw0]
    have : 0 < 1-mhtEps u := by linarith only [he]
    positivity
  have hm2 : mhtA2 0 ≤ mhtA2 u := mht_le_of_deriv hu.1
    (fun x hx => mhtA2_hasDerivAt (by linarith only [hx.1]))
    (fun x hx => (mhtA3_pos ⟨hx.1.le,le_trans hx.2.le hu.2⟩).le)
  have hp2 : 0 < mhtA2 u := lt_of_lt_of_le mht_A_endpoints.2.1 hm2
  have hm1 : mhtA1 0 ≤ mhtA1 u := mht_le_of_deriv hu.1
    (fun x hx => mhtA1_hasDerivAt (by linarith only [hx.1]))
    (fun x hx => by
      have hh := mht_le_of_deriv hx.1.le
        (fun z hz => mhtA2_hasDerivAt (by linarith only [hz.1]))
        (fun z hz => (mhtA3_pos ⟨hz.1.le,le_trans hz.2.le (le_trans hx.2.le hu.2)⟩).le)
      exact (lt_of_lt_of_le mht_A_endpoints.2.1 hh).le)
  have hp1 : 0 < mhtA1 u := lt_of_lt_of_le mht_A_endpoints.1 hm1
  have hm2up : mhtA2 u ≤ mhtA2 (2/3) := mht_le_of_deriv hu.2
    (fun x hx => mhtA2_hasDerivAt (by linarith only [hu.1,hx.1]))
    (fun x hx => (mhtA3_pos ⟨le_trans hu.1 hx.1.le,hx.2.le⟩).le)
  exact ⟨ha,hp1,hp2,lt_of_le_of_lt hm2up (lt_of_lt_of_le mht_A_endpoints.2.2.1 hm1)⟩

private theorem mhtB3_ge_initial {u : ℝ} (hu : u ∈ Icc (0:ℝ) (2/3)) :
    mhtB3 0 ≤ mhtB3 u := mht_le_of_deriv hu.1
  (fun x hx => mhtB3_hasDerivAt (by linarith only [hx.1]))
  (fun x hx => (mhtB4_pos ⟨hx.1.le,le_trans hx.2.le hu.2⟩).le)

private theorem mhtB2_ge_initial {u : ℝ} (hu : u ∈ Icc (0:ℝ) (2/3)) :
    mhtB2 0 ≤ mhtB2 u := mht_le_of_deriv hu.1
  (fun x hx => mhtB2_hasDerivAt (by linarith only [hx.1]))
  (fun x hx => (lt_of_lt_of_le mht_B_endpoints.2.2.2.1
    (mhtB3_ge_initial ⟨hx.1.le,le_trans hx.2.le hu.2⟩)).le)

private theorem mhtB1_neg {u : ℝ} (hu : u ∈ Icc (0:ℝ) (2/3)) : mhtB1 u < 0 := by
  have hh : mhtB1 u ≤ mhtB1 (2/3) := mht_le_of_deriv hu.2
    (fun x hx => mhtB1_hasDerivAt (by linarith only [hu.1,hx.1]))
    (fun x hx => (lt_of_lt_of_le mht_B_endpoints.2.2.1
      (mhtB2_ge_initial ⟨le_trans hu.1 hx.1.le,hx.2.le⟩)).le)
  exact lt_of_le_of_lt hh mht_B_endpoints.2.1

theorem mht_B_bounds {u : ℝ} (hu : u ∈ Icc (0:ℝ) (2/3)) :
    mhtB u ≤ mhtB 0 ∧ mhtB u < 0 ∧ mhtB2 0 ≤ mhtB2 u ∧ 0 < mhtB2 u := by
  have hh : -mhtB 0 ≤ -mhtB u := mht_le_of_deriv
    (f := fun x : ℝ => -mhtB x) (f' := fun x : ℝ => -mhtB1 x) hu.1
    (fun x hx => (mhtB_hasDerivAt (by linarith only [hx.1])).neg)
    (fun x hx => neg_nonneg.mpr (mhtB1_neg ⟨hx.1.le,le_trans hx.2.le hu.2⟩).le)
  have hbelow : mhtB u ≤ mhtB 0 := by linarith only [hh]
  have hm2 := mhtB2_ge_initial hu
  exact ⟨hbelow,lt_of_le_of_lt hbelow mht_B_endpoints.1,hm2,
    lt_of_lt_of_le mht_B_endpoints.2.2.1 hm2⟩

theorem mht_C2_pos {u : ℝ} (hu : u ∈ Icc (0:ℝ) (2/3)) : 0 < mhtC2 u := by
  have hc : ConcaveOn ℝ (Icc (0:ℝ) (2/3)) mhtC2 := by
    apply concaveOn_of_hasDerivWithinAt2_nonpos (convex_Icc 0 (2/3))
      (f' := mhtC3) (f'' := mhtC4)
    · exact fun x hx => (mhtC2_hasDerivAt
        (by linarith only [hx.1])).continuousAt.continuousWithinAt
    · exact fun x hx => (mhtC2_hasDerivAt
        (by have := (interior_subset hx).1; linarith)).hasDerivWithinAt
    · exact fun x hx => (mhtC3_hasDerivAt
        (by have := (interior_subset hx).1; linarith)).hasDerivWithinAt
    · exact fun x hx => (mhtC4_neg (interior_subset hx)).le
  exact lt_of_lt_of_le (lt_min mht_C_endpoints.1 mht_C_endpoints.2)
    (mht_concave_ge_min hc hu)

theorem mhtLogDeriv_hasDerivAt {u : ℝ} (hu : u ∈ Icc (0:ℝ) (2/3)) :
    HasDerivAt mhtLogDeriv (mhtLogDeriv1 u) u := by
  have hn : u ≠ -6 := by linarith only [hu.1]
  have ha := (mht_A_bounds hu).1
  have hd := (mhtA1_hasDerivAt hn).div
    (mhtA_hasDerivAt hn) ha.ne'
  change HasDerivAt (fun x => mhtA1 x/mhtA x) _ u
  refine hd.congr_deriv ?_
  unfold mhtLogDeriv1 mhtLogDeriv
  field_simp

theorem mhtLogDeriv_bounds {u : ℝ} (hu : u ∈ Icc (0:ℝ) (2/3)) :
    0 < mhtLogDeriv u ∧ mhtLogDeriv u ≤ mhtEll := by
  have hpos : 0 < mhtLogDeriv u := div_pos (mht_A_bounds hu).2.1 (mht_A_bounds hu).1
  have hh := mht_fence (lo := 0) (hi := 2/3) (B := mhtEll)
    (fun x hx => mhtLogDeriv_hasDerivAt hx) (le_refl _) ?_ u hu
  · exact ⟨hpos,hh⟩
  intro x hx he
  obtain ⟨ha,_,_,haa⟩ := mht_A_bounds (Ico_subset_Icc_self hx)
  have hs : mhtA2 x/mhtA x < mhtLogDeriv x :=
    (div_lt_div_iff_of_pos_right ha).mpr haa
  have hell := mht_A_endpoints.2.2.2
  unfold mhtLogDeriv1
  rw [he] at hs ⊢
  have hp := mul_pos (by linarith only [hell] : 0<mhtEll) (by linarith only [hell] : 0<mhtEll-1)
  nlinarith only [hs,hp]

theorem mhtE_hasDerivAt {u : ℝ} (hu : u ∈ Icc (0:ℝ) (2/3)) :
    HasDerivAt mhtE (mhtE1 u) u := by
  have hn : u ≠ -6 := by linarith only [hu.1]
  have ha := (mht_A_bounds hu).1
  have hd := (mhtB1_hasDerivAt hn).sub
    ((mhtB_hasDerivAt hn).mul (mhtLogDeriv_hasDerivAt hu))
  change HasDerivAt (fun x => mhtB1 x-mhtB x*mhtLogDeriv x) _ u
  refine hd.congr_deriv ?_
  unfold mhtE1 mhtE mhtLogDeriv1 mhtLogDeriv
  field_simp
  ring

theorem mhtE1_pos_at_lower {u : ℝ} (hu : u ∈ Icc (0:ℝ) (2/3))
    (he : mhtE u = -3) : 0 < mhtE1 u := by
  obtain ⟨ha,_,ha2,_⟩ := mht_A_bounds hu
  obtain ⟨_,hb,_,hb2⟩ := mht_B_bounds hu
  have hr := (mhtLogDeriv_bounds hu).1
  unfold mhtE1
  rw [he]
  have hterm : mhtB u*mhtA2 u/mhtA u < 0 := div_neg_of_neg_of_pos (mul_neg_of_neg_of_pos hb ha2) ha
  linarith only [hterm,hr,hb2]

theorem mhtE1_pos_at_upper {u : ℝ} (hu : u ∈ Icc (0:ℝ) (2/3))
    (he : mhtE u = 3) : 0 < mhtE1 u := by
  obtain ⟨ha,_,ha2,_⟩ := mht_A_bounds hu
  obtain ⟨_,hb,hm2,_⟩ := mht_B_bounds hu
  have hr := (mhtLogDeriv_bounds hu).2
  have hb2 := mht_B_endpoints.2.2.2.2.1
  unfold mhtE1
  rw [he]
  have hterm : mhtB u*mhtA2 u/mhtA u < 0 := div_neg_of_neg_of_pos (mul_neg_of_neg_of_pos hb ha2) ha
  linarith only [hterm,hr,hb2,hm2]

theorem mhtE_bounds {u : ℝ} (hu : u ∈ Icc (0:ℝ) (2/3)) : -3 ≤ mhtE u ∧ mhtE u ≤ 3 := by
  have hlo := mht_fence (lo := 0) (hi := 2/3) (B := 3)
    (f := fun x => -mhtE x) (f' := fun x => -mhtE1 x)
    (fun x hx => (mhtE_hasDerivAt hx).neg)
    (by linarith only [mht_E_endpoints.1])
    (fun x hx he => by
      have h := mhtE1_pos_at_lower (Ico_subset_Icc_self hx) (by linarith only [he])
      linarith only [h]) u hu
  have hrev : ∀ x ∈ Icc (0:ℝ) (2/3),
      HasDerivAt (fun t : ℝ => mhtE (2/3-t)) (-mhtE1 (2/3-x)) x := by
    intro x hx
    have hbox : (2/3:ℝ)-x ∈ Icc (0:ℝ) (2/3) := ⟨by linarith only [hx.2],by linarith only [hx.1]⟩
    simpa only [Function.comp_def,id_eq,mul_neg_one] using
      (mhtE_hasDerivAt hbox).comp x ((hasDerivAt_id x).const_sub (2/3))
  have hhi := mht_fence (lo := 0) (hi := 2/3) (B := 3)
    (f := fun x => mhtE (2/3-x)) (f' := fun x => -mhtE1 (2/3-x)) hrev
    (by simpa using mht_E_endpoints.2.2.le)
    (fun x hx he => by
      have hbox : (2/3:ℝ)-x ∈ Icc (0:ℝ) (2/3) := ⟨by linarith only [hx.2],by linarith only [hx.1]⟩
      have h := mhtE1_pos_at_upper hbox he
      linarith only [h]) (2/3-u) ⟨by linarith only [hu.2],by linarith only [hu.1]⟩
  have hid : (2/3:ℝ)-(2/3-u) = u := by ring
  rw [hid] at hhi
  exact ⟨by linarith only [hlo],hhi⟩

theorem mhtQuot_hasDerivAt {u : ℝ} (hu : u ∈ Icc (0:ℝ) (2/3)) :
    HasDerivAt mhtQuot (mhtQuot1 u) u := by
  have hn : u ≠ -6 := by linarith only [hu.1]
  have ha := (mht_A_bounds hu).1
  have hd := ((mhtB_hasDerivAt hn).pow 2).div
    (mhtA_hasDerivAt hn) ha.ne'
  change HasDerivAt (fun x => mhtB x^2/mhtA x) _ u
  refine hd.congr_deriv ?_
  unfold mhtQuot1
  norm_num only [Pi.pow_apply,Pi.mul_apply,id_eq]
  field_simp

theorem mhtQuot1_hasDerivAt {u : ℝ} (hu : u ∈ Icc (0:ℝ) (2/3)) :
    HasDerivAt mhtQuot1 (mhtQuot2 u) u := by
  have hn : u ≠ -6 := by linarith only [hu.1]
  have ha := (mht_A_bounds hu).1
  have hfirst := (((mhtB_hasDerivAt hn).const_mul 2).mul
    (mhtB1_hasDerivAt hn)).div (mhtA_hasDerivAt hn) ha.ne'
  have hsecond := (((mhtB_hasDerivAt hn).pow 2).mul
    (mhtA1_hasDerivAt hn)).div ((mhtA_hasDerivAt hn).pow 2) (pow_ne_zero 2 ha.ne')
  have hd := hfirst.sub hsecond
  change HasDerivAt (fun x => 2*mhtB x*mhtB1 x/mhtA x-mhtB x^2*mhtA1 x/mhtA x^2) _ u
  refine hd.congr_deriv ?_
  unfold mhtQuot2 mhtE mhtLogDeriv
  norm_num only [Pi.pow_apply,Pi.mul_apply,Pi.sub_apply,id_eq]
  field_simp
  ring

/-- The reciprocal quotient is concave by the invariant derivative strip. -/
theorem mhtQuot2_neg {u : ℝ} (hu : u ∈ Icc (0:ℝ) (2/3)) : mhtQuot2 u < 0 := by
  obtain ⟨ha,_,ha2,_⟩ := mht_A_bounds hu
  obtain ⟨hb,hbneg,hb2,hb2pos⟩ := mht_B_bounds hu
  obtain ⟨he0,he1⟩ := mhtE_bounds hu
  have he2 : mhtE u^2 ≤ 9 := by nlinarith only [he0,he1]
  have hbb : mhtB u*mhtB2 u ≤ mhtB 0*mhtB2 0 := by
    calc mhtB u*mhtB2 u ≤ mhtB u*mhtB2 0 := mul_le_mul_of_nonpos_left hb2 hbneg.le
      _ ≤ mhtB 0*mhtB2 0 := mul_le_mul_of_nonneg_right hb mht_B_endpoints.2.2.1.le
  have hstrict := mht_B_endpoints.2.2.2.2.2
  have hterm : 0 ≤ mhtB u^2*mhtA2 u/(2*mhtA u) := by positivity
  unfold mhtQuot2
  exact mul_neg_of_pos_of_neg (div_pos (by norm_num) ha)
    (by nlinarith only [he2,hbb,hstrict,hterm])

theorem mhtMin_hasDerivAt {u : ℝ} (hu : u ∈ Icc (0:ℝ) (2/3)) :
    HasDerivAt mhtMin (mhtMin1 u) u := by
  have hn : u ≠ -6 := by linarith only [hu.1]
  exact (mhtC_hasDerivAt hn).sub ((mhtQuot_hasDerivAt hu).div_const 4)

theorem mhtMin1_hasDerivAt {u : ℝ} (hu : u ∈ Icc (0:ℝ) (2/3)) :
    HasDerivAt mhtMin1 (mhtMin2 u) u := by
  have hn : u ≠ -6 := by linarith only [hu.1]
  exact (mhtC1_hasDerivAt hn).sub ((mhtQuot1_hasDerivAt hu).div_const 4)

theorem mhtMin_convexOn : ConvexOn ℝ (Icc (0:ℝ) (2/3)) mhtMin := by
  apply convexOn_of_hasDerivWithinAt2_nonneg (convex_Icc 0 (2/3))
    (f' := mhtMin1) (f'' := mhtMin2)
  · exact fun x hx => (mhtMin_hasDerivAt hx).continuousAt.continuousWithinAt
  · exact fun x hx => (mhtMin_hasDerivAt (interior_subset hx)).hasDerivWithinAt
  · exact fun x hx => (mhtMin1_hasDerivAt (interior_subset hx)).hasDerivWithinAt
  · intro x hx
    have h1 := mht_C2_pos (interior_subset hx)
    have h2 := mhtQuot2_neg (interior_subset hx)
    unfold mhtMin2
    linarith only [h1,h2]

theorem mhtMin_pos {u : ℝ} (hu : u ∈ Icc (0:ℝ) (2/3)) : 0 < mhtMin u := by
  have hmid : (1/3:ℝ) ∈ Icc (0:ℝ) (2/3) := by constructor <;> norm_num
  have ht := mht_convex_tangent mhtMin_convexOn hmid hu (mhtMin_hasDerivAt hmid)
  obtain ⟨hs,hp⟩ := mht_min_midpoint
  have hlinear : (1/3)*mhtMin1 (1/3) ≤ mhtMin1 (1/3)*(u-1/3) := by
    nlinarith only [mul_nonneg (neg_nonneg.mpr hs.le) (sub_nonneg.mpr hu.2)]
  linarith only [ht,hp,hlinear]

/-- The actual quadratic after subtracting the incoming Jensen slack. -/
theorem mht_quadratic_pos {u : ℝ} (hu : u ∈ Icc (0:ℝ) (2/3)) (z : ℝ) :
    0 < mhtA u*z^2+mhtB u*z+mhtC u := by
  have ha := (mht_A_bounds hu).1
  have hh := mhtMin_pos hu
  have hid : mhtA u*z^2+mhtB u*z+mhtC u =
      mhtA u*(z+mhtB u/(2*mhtA u))^2+mhtMin u := by
    unfold mhtMin mhtQuot
    field_simp
    ring
  rw [hid]
  have hsq := mul_nonneg ha.le (sq_nonneg (z+mhtB u/(2*mhtA u)))
  linarith only [hsq,hh]

end SmoothedOctagon
