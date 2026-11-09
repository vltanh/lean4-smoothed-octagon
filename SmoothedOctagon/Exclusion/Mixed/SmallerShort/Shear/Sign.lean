module

public import SmoothedOctagon.Exclusion.Mixed.SmallerShort.Interface

/-!
# The physical shear estimate from the lower scale bound
-/

@[expose] public section

namespace SmoothedOctagon

open Set Real

private noncomputable def shrShapeF (s y : ℝ) : ℝ :=
  ((3 + s) * y + 7 / 2 * (1 - y ^ 2)) / (3 + y ^ 2 * s)

/-- The two shape comparisons reduce the fraction to its smallest shape parameters. -/
private theorem shr_shape_fraction_bound {s y : ℝ} (hs : 1 / 9 ≤ s)
    (hy0 : 27 / 31 ≤ y) (hy1 : y ≤ 1) : shrShapeF s y < 15 / 13 := by
  have hy : 0 < y := by linarith
  have hden : 0 < 3 + y ^ 2 * s := by positivity
  have hden0 : 0 < 3 + y ^ 2 * (1 / 9 : ℝ) := by positivity
  have hdec_s : shrShapeF s y ≤ shrShapeF (1 / 9) y := by
    have e : shrShapeF (1 / 9) y - shrShapeF s y =
        (s - 1 / 9) * y * (1 - y ^ 2) * (7 / 2 * y - 3) /
          ((3 + y ^ 2 / 9) * (3 + y ^ 2 * s)) := by
      unfold shrShapeF
      field_simp
      ring
    have hnum : 0 ≤ (s - 1 / 9) * y * (1 - y ^ 2) * (7 / 2 * y - 3) :=
      mul_nonneg (mul_nonneg (mul_nonneg (by linarith) hy.le) (by nlinarith)) (by linarith)
    have h : 0 ≤ shrShapeF (1 / 9) y - shrShapeF s y := by rw [e]; positivity
    linarith
  have hdec_y : shrShapeF (1 / 9) y ≤ shrShapeF (1 / 9) (27 / 31) := by
    have e : shrShapeF (1 / 9) (27 / 31) - shrShapeF (1 / 9) y =
        (y - 27 / 31) * (3 + 1 / 9) *
          (7 / 2 * (y + 27 / 31) - 3 + (1 / 9) * y * (27 / 31)) /
            ((3 + (27 / 31) ^ 2 / 9) * (3 + y ^ 2 / 9)) := by
      unfold shrShapeF
      field_simp
      ring
    have hnum : 0 ≤ (y - 27 / 31) * (3 + 1 / 9) *
        (7 / 2 * (y + 27 / 31) - 3 + (1 / 9) * y * (27 / 31)) :=
      mul_nonneg (mul_nonneg (by linarith) (by norm_num)) (by linarith)
    have h : 0 ≤ shrShapeF (1 / 9) (27 / 31) - shrShapeF (1 / 9) y := by rw [e]; positivity
    linarith
  have hend : shrShapeF (1 / 9) (27 / 31) < 15 / 13 := by norm_num [shrShapeF]
  linarith

/-- Dividing the two shape coordinates leaves a ratio in a fixed positive interval. -/
private theorem shr_shape_ratio_bounds {x δ al : ℝ} (hx : 2 ≤ x) (hδ : 0 ≤ δ)
    (hδ2 : δ ≤ 1 / 19) (hal : 13 / 5 * δ ≤ al - 1) (hal' : al - 1 ≤ 3 * δ) :
    1 / 3 ≤ ssRr x ∧ ssRr x < 1 ∧
      27 / 31 ≤ ssTs al (x * (1 + δ)) / ssRr x ∧
      ssTs al (x * (1 + δ)) / ssRr x ≤ 1 := by
  have hx0 : 0 < x := by linarith
  have hx1 : 0 < x - 1 := by linarith
  have hxS : 0 < x + 1 := by linarith
  have hd : 0 < 1 + δ := by linarith
  have hal0 : 0 < al := by linarith
  let c := al / (1 + δ)
  have hc0 : 1 ≤ c := by dsimp [c]; rw [le_div_iff₀ hd]; linarith
  have hc1 : c ≤ 11 / 10 := by dsimp [c]; rw [div_le_iff₀ hd]; linarith
  have hxc : 0 < x + c := by linarith
  have hbe : 0 < x * (1 + δ) + al := by positivity
  have hy : ssTs al (x * (1 + δ)) / ssRr x =
      (x - c) * (x + 1) / ((x + c) * (x - 1)) := by
    unfold ssTs ssRr
    dsimp [c]
    field_simp
  refine ⟨?_, ?_, ?_, ?_⟩
  · unfold ssRr; rw [le_div_iff₀ hxS]; linarith
  · unfold ssRr; rw [div_lt_one hxS]; linarith
  · rw [hy, le_div_iff₀ (mul_pos hxc hx1)]
    have hp := mul_nonneg (show 0 ≤ 11 / 10 - c by linarith)
      (show 0 ≤ 58 * x + 4 by linarith)
    have hq := mul_nonneg (show 0 ≤ x - 2 by linarith)
      (show 0 ≤ 4 * x + 11 / 5 by linarith)
    nlinarith only [hp, hq]
  · rw [hy, div_le_one (mul_pos hxc hx1)]
    have := mul_nonneg (show 0 ≤ c - 1 by linarith) hx0.le
    nlinarith only [this]

/-- The scale floor and the separate shape losses give a lower bound for the shear loss. -/
private theorem shr_shear_loss_lower {x δ al rho : ℝ} (hx : 2 ≤ x) (hδ : 0 ≤ δ)
    (hδ2 : δ ≤ 1 / 19) (hal : 13 / 5 * δ ≤ al - 1) (hal' : al - 1 ≤ 3 * δ)
    (hρ : 0 < rho) (hρ1 : rho < 1) (hq : 15 / 16 * ssQc x al < ssQ al rho) :
    2 * ((x ^ 2 + x + 1) / (1 + x) ^ 2) *
        (2 * (x * (1 + δ)) * x - x - al * (x * (1 + δ))) * (rho / (1 - rho)) / ssRr x >
      2 * (12 / 13) * (3 + (ssRr x) ^ 2) / (3 - ssRr x) := by
  have hx0 : 0 < x := by linarith
  have hal0 : 0 < al := by linarith
  have hal1 : 1 ≤ al := by linarith
  have hal2 : al ≤ 22 / 19 := by linarith
  have hS : 0 < 1 + x := by linarith
  have hxm : 0 < x - 1 := by linarith
  have hx2 : 0 ≤ x - 2 := by linarith
  have halu : 0 ≤ 1 + 3 * δ - al := by linarith
  let R := ssRr x
  have ⟨hR0, hR1, _, _⟩ := shr_shape_ratio_bounds hx hδ hδ2 hal hal'
  have hR : 0 < R := by dsimp [R]; linarith
  have hRm : 0 < 3 - R := by dsimp [R]; linarith
  let X := x * (x + 2)
  let D := 2 * (x * (1 + δ)) * x - x - al * (x * (1 + δ))
  let U1 := (x ^ 2 + x + 1) / (1 + x) ^ 2
  let e : ℝ := 3 / (2 * 19 ^ 2)
  let f0 : ℝ := (22 / 19) ^ 2 / 8
  let lam : ℝ := 15 / 16
  let ζ := lam * (1 - e) / (1 + (1 - lam) * f0)
  let d0 := 2 * x * (x - 1) * (1 - e)
  have hX : 8 ≤ X := by dsimp [X]; nlinarith only [hx]
  have hU : 0 < U1 := by dsimp [U1]; positivity
  have hd0 : 0 < d0 := by dsimp [d0, e]; positivity
  have hδsq : δ ^ 2 ≤ (1 / 19 : ℝ) ^ 2 := by nlinarith only [hδ, hδ2]
  have hD : d0 ≤ D := by
    have h1 : 0 ≤ x * (1 + δ) * (1 + 3 * δ - al) := by positivity
    have h2 : 0 ≤ 2 * x * (x - 2) * δ := by positivity
    have h3 : 0 ≤ 3 * x * ((x - 1) / 19 ^ 2 - δ ^ 2) := by
      apply mul_nonneg (by positivity)
      nlinarith only [hx, hδsq]
    have eD : D - d0 = x * (1 + δ) * (1 + 3 * δ - al) +
        2 * x * (x - 2) * δ + 3 * x * ((x - 1) / 19 ^ 2 - δ ^ 2) := by
      dsimp [D, d0, e]
      ring
    linarith only [h1, h2, h3, eD]
  have hD0 : 0 < D := hd0.trans_le hD
  have haX : al ^ 2 ≤ f0 * X := by
    have ha2 : al ^ 2 ≤ (22 / 19 : ℝ) ^ 2 := by nlinarith only [hal0, hal2]
    dsimp [f0]
    nlinarith only [ha2, hX]
  have hdenq : 0 < 1 + rho * (al ^ 2 - 1) := by
    have : 0 ≤ rho * (al ^ 2 - 1) := mul_nonneg hρ.le (by nlinarith only [hal1])
    linarith
  have hXa : 0 < X + al ^ 2 := by positivity
  have hden : 0 < X + (1 - lam) * al ^ 2 := by dsimp [lam]; positivity
  have hq' : lam * al ^ 2 / (X + al ^ 2) < al ^ 2 * rho / (1 + rho * (al ^ 2 - 1)) := by
    simpa [lam, X, ssQc, ssQ, ssLam, div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using hq
  have hq'' := (div_lt_div_iff₀ hXa hdenq).mp hq'
  have hcoef : lam < rho * (X + (1 - lam) * al ^ 2 + lam) := by
    have h : 0 < al ^ 2 * (rho * (X + (1 - lam) * al ^ 2 + lam) - lam) := by
      nlinarith only [hq'']
    have := pos_of_mul_pos_right h (sq_nonneg al)
    linarith only [this]
  have hfloor : lam / (X + (1 - lam) * al ^ 2) < rho / (1 - rho) := by
    rw [div_lt_div_iff₀ hden (by linarith)]
    nlinarith only [hcoef]
  have hdenb : X + (1 - lam) * al ^ 2 ≤ X * (1 + (1 - lam) * f0) := by
    calc
      X + (1 - lam) * al ^ 2 ≤ X + (1 - lam) * (f0 * X) :=
        add_le_add (le_refl X)
          (mul_le_mul_of_nonneg_left haX (show 0 ≤ 1 - lam by norm_num [lam]))
      _ = X * (1 + (1 - lam) * f0) := by ring
  have hfrac : lam / (X * (1 + (1 - lam) * f0)) ≤ lam / (X + (1 - lam) * al ^ 2) :=
    div_le_div_of_nonneg_left (by norm_num [lam]) hden hdenb
  have hf : 0 < lam / (X * (1 + (1 - lam) * f0)) := by dsimp [lam, f0]; positivity
  have hLoss := mul_lt_mul_of_pos_left (hfrac.trans_lt hfloor)
    (show 0 < 2 * U1 * D by positivity)
  have hBase := mul_le_mul_of_nonneg_right hD
    (show 0 ≤ 2 * U1 * (lam / (X * (1 + (1 - lam) * f0))) by positivity)
  have hmin : 2 * U1 * d0 * (lam / (X * (1 + (1 - lam) * f0))) <
      2 * U1 * D * (rho / (1 - rho)) := by
    nlinarith only [hLoss, hBase]
  have hbase : 2 * U1 * d0 * (lam / (X * (1 + (1 - lam) * f0))) / R =
      2 * ζ * (3 + R ^ 2) / (3 - R) := by
    dsimp [U1, d0, X, ζ, R, ssRr, e, f0, lam]
    rw [show 3 - (x - 1) / (x + 1) = 2 * (x + 2) / (x + 1) by field_simp; ring]
    field_simp
    ring
  have hratio := (div_lt_div_iff_of_pos_right hR).mpr hmin
  rw [hbase] at hratio
  have hζ : (12 / 13 : ℝ) < ζ := by norm_num [ζ, lam, e, f0]
  have hshape : 0 < (3 + R ^ 2) / (3 - R) := by positivity
  have hstrict := mul_lt_mul_of_pos_right hζ hshape
  change 2 * (12 / 13) * (3 + R ^ 2) / (3 - R) <
    2 * U1 * D * (rho / (1 - rho)) / R
  calc
    2 * (12 / 13) * (3 + R ^ 2) / (3 - R) =
        2 * ((12 / 13) * ((3 + R ^ 2) / (3 - R))) := by ring
    _ < 2 * (ζ * ((3 + R ^ 2) / (3 - R))) := mul_lt_mul_of_pos_left hstrict (by norm_num)
    _ = 2 * ζ * (3 + R ^ 2) / (3 - R) := by ring
    _ < _ := hratio

/-- **The shear sign above `q_b`**: the scale floor and two monotone shape ratios give
`√3·h·R + 7A/2 < 0` throughout the small-shape domain. The first ratio bounds the
physical shear loss from below; the second controls the anisotropy contribution. -/
theorem shr_shear_sign {x δ al rho : ℝ} (hx : 2 ≤ x) (_hx2 : x ≤ 13 / 6) (hδ : 0 ≤ δ)
    (hδ2 : δ ≤ 1 / 19) (hal : 13 / 5 * δ ≤ al - 1) (hal' : al - 1 ≤ 3 * δ) (hρ : 0 < rho)
    (hρ1 : rho < 1) (hq : 15 / 16 * ssQc x al < ssQ al rho) :
    √3 * ssShear x (x * (1 + δ)) al rho * ssRr x + 7 / 2 * ssAn x (x * (1 + δ)) al < 0 := by
  obtain ⟨hR0, hR1, hy0, hy1⟩ := shr_shape_ratio_bounds hx hδ hδ2 hal hal'
  let R := ssRr x
  let T := ssTs al (x * (1 + δ))
  let y := T / R
  let A := ssAn x (x * (1 + δ)) al
  let L := 2 * ((x ^ 2 + x + 1) / (1 + x) ^ 2) *
    (2 * (x * (1 + δ)) * x - x - al * (x * (1 + δ))) * (rho / (1 - rho))
  have hx0 : 0 < x := by linarith only [hx]
  have hS : 0 < x + 1 := by linarith
  have hxm : 0 < x - 1 := by linarith
  have hal0 : 0 < al := by linarith
  have hbe0 : 0 < x * (1 + δ) := by positivity
  have hK : 0 < al ^ 2 + al * (x * (1 + δ)) + (x * (1 + δ)) ^ 2 := by positivity
  have hR : 0 < R := by dsimp [R]; linarith
  have hRm : 0 < 3 - R := by dsimp [R]; linarith
  have hA : A = R ^ 2 * (1 - y ^ 2) / (3 + y ^ 2 * R ^ 2) := by
    dsimp [A, R, y, T, ssAn, ssRr, ssTs]
    field_simp
    ring
  have hTy : T = y * R := by dsimp [y]; field_simp
  have hf : shrShapeF (R ^ 2) y = (1 + A) * y + 7 / 2 * A / R ^ 2 := by
    rw [hA]
    unfold shrShapeF
    field_simp
    ring
  have hshape : 7 / 6 ≤ (3 + R ^ 2) / (3 - R) := by
    rw [le_div_iff₀ hRm]
    have h : 0 ≤ (R - 1 / 3) * (6 * R + 9) := by
      apply mul_nonneg (by dsimp [R]; linarith) (by linarith)
    nlinarith only [h]
  have hfbound : shrShapeF (R ^ 2) y < 15 / 13 :=
    shr_shape_fraction_bound (by dsimp [R]; nlinarith only [hR0]) hy0 hy1
  have hloss : 2 * (12 / 13) * (3 + R ^ 2) / (3 - R) < L / R :=
    shr_shear_loss_lower hx hδ hδ2 hal hal' hρ hρ1 hq
  have hloss' : (24 / 13) * ((3 + R ^ 2) / (3 - R)) < L / R := by
    convert hloss using 1; ring
  have hneg : 1 + shrShapeF (R ^ 2) y - L / R < 0 := by
    linarith only [hfbound, hshape, hloss']
  have h3 : √3 * √3 = 3 := Real.mul_self_sqrt (by norm_num)
  have hshear : √3 * ssShear x (x * (1 + δ)) al rho = R + (1 + A) * T - L := by
    have hclear : √3 * ssShear x (x * (1 + δ)) al rho =
        (x * (1 + δ) * x - al) * ((x + 2) * al + (2 * x + 1) * (x * (1 + δ))) /
          ((1 + x) ^ 2 * (al ^ 2 + al * (x * (1 + δ)) + (x * (1 + δ)) ^ 2)) - L := by
      unfold ssShear
      change √3 * (√3 / 3 * (_ - L)) = _ - L
      have es : √3 * (√3 / 3) = 1 := by
        calc
          √3 * (√3 / 3) = (√3 * √3) / 3 := by ring
          _ = 1 := by rw [h3]; norm_num
      rw [← mul_assoc, es, one_mul]
    rw [hclear]
    dsimp [R, A, T, ssRr, ssAn, ssTs]
    field_simp
    ring
  have hid : √3 * ssShear x (x * (1 + δ)) al rho * R + 7 / 2 * A =
      R ^ 2 * (1 + shrShapeF (R ^ 2) y - L / R) := by
    rw [hshear, hf, hTy]
    field_simp
    ring
  change √3 * ssShear x (x * (1 + δ)) al rho * R + 7 / 2 * A < 0
  rw [hid]
  exact mul_neg_of_pos_of_neg (sq_pos_of_pos hR) hneg

end SmoothedOctagon
