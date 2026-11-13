module

public import SmoothedOctagon.Exclusion.Mixed.SmallerShort.LowerRatio.OuterFace.Residue

/-!
# Smaller-short window, lower ratio, outer face, large shapes: the test `F₁`

On `3/2 ≤ x ≤ 2`, `6/5 ≤ α ≤ x`, `24/43 ≤ C ≤ 10/13`, `u_f ≤ u ≤ u_v`:

* norm concavity reduces `u` to the affine norms `u₋ = (8x + 1303)/1750 ≤ u_f`,
  `u₊ = (6x + 443)/600 ≥ u_v`;
* beta concavity (`lro_F1_bmin`, with `w₀ > (19 + 2x)/28` at `u ≤ u₊`) reduces `C` to
  `24/43`, `10/13`;
* at each of these four pairs, the reciprocal-shape curvature is at most
  `2b₂ + 6b₃/x + 7/216 < 0` (`b₄, b₃ ≤ 0`, residue `Q < 0`, `(e/Z)² ≤ 4/9`),
  so `α ∈ {6/5, x}`;
* the eight terminal curves `α = 6/5`, `α = x` are positive.

The residue sign follows from the uniform comparison in `OuterFace/Residue`.
The curvature and terminal signs are proved at the affine norms `u₊`, `u₋`.

## Main API

* `lro_A_F1`: `F₁ > 0` on branch A.
-/

@[expose] public section

namespace SmoothedOctagon

open Set Real

theorem lro_A_M1_lm_num {z : ℝ} (hz0 : 0 ≤ z) (_hz1 : z ≤ (1 / 2 : ℝ)) :
    (0 : ℝ) < 3698 / 2296875 * z ^ 9 + 2524057 / 1531250 * z ^ 8 + 12094033489 / 73500000 * z ^ 7 + 9768831887209 / 6321000000 * z ^ 6 + 137714554609843 / 22755600000 * z ^ 5 + 111703413098381 / 9102240000 * z ^ 4 + 9927002879321 / 728179200 * z ^ 3 + 156324902873 / 19418112 * z ^ 2 + 9251829975 / 4315136 * z + 926451621 / 8630272 := by
  nlinarith [(by positivity : (0 : ℝ) ≤ z),
    (by positivity : (0 : ℝ) ≤ z ^ 2),
    (by positivity : (0 : ℝ) ≤ z ^ 3),
    (by positivity : (0 : ℝ) ≤ z ^ 4),
    (by positivity : (0 : ℝ) ≤ z ^ 5),
    (by positivity : (0 : ℝ) ≤ z ^ 6),
    (by positivity : (0 : ℝ) ≤ z ^ 7),
    (by positivity : (0 : ℝ) ≤ z ^ 8),
    (by positivity : (0 : ℝ) ≤ z ^ 9)]

theorem lro_A_M1_lm_id {x : ℝ} (h0 : (3 / 2 : ℝ) ≤ x) (_h1 : x ≤ (2 : ℝ)) :
    (-7 / 216 : ℝ) - (2 * lrb2 x (24 / 43) ((8 * x + 1303) / 1750) + 6 * lrb3 x (24 / 43) ((8 * x + 1303) / 1750) / x) = (3698 / 2296875 * (x - (3 / 2 : ℝ)) ^ 9 + 2524057 / 1531250 * (x - (3 / 2 : ℝ)) ^ 8 + 12094033489 / 73500000 * (x - (3 / 2 : ℝ)) ^ 7 + 9768831887209 / 6321000000 * (x - (3 / 2 : ℝ)) ^ 6 + 137714554609843 / 22755600000 * (x - (3 / 2 : ℝ)) ^ 5 + 111703413098381 / 9102240000 * (x - (3 / 2 : ℝ)) ^ 4 + 9927002879321 / 728179200 * (x - (3 / 2 : ℝ)) ^ 3 + 156324902873 / 19418112 * (x - (3 / 2 : ℝ)) ^ 2 + 9251829975 / 4315136 * (x - (3 / 2 : ℝ)) + 926451621 / 8630272) / ((x) * (x + 1) ^ 2 * (43 * x - 24) ^ 2) := by
  simp only [lrb2, lrb3, lrg2, lrq2, lrq3, lrW3, lrW4, lrd1, lrd2, lrJ2, ssE0]
  have hd0 : x ≠ 0 := by nlinarith
  have hd1 : x * 1 + 0 ≠ 0 := by nlinarith
  have hd2 : 0 + x * 1 ≠ 0 := by nlinarith
  have hd3 : 0 + 1 * x ≠ 0 := by nlinarith
  have hd4 : x + 0 ≠ 0 := by nlinarith
  have hd5 : x + 1 ≠ 0 := by nlinarith
  have hd6 : x * 1 + 1 ≠ 0 := by nlinarith
  have hd7 : 1 + x * 1 ≠ 0 := by nlinarith
  have hd8 : 1 + 1 * x ≠ 0 := by nlinarith
  have hd9 : x + 1 ≠ 0 := by nlinarith
  have hd10 : 43 * x - 24 ≠ 0 := by nlinarith
  have hd11 : x * 43 - 24 ≠ 0 := by nlinarith
  have hd12 : -24 + x * 43 ≠ 0 := by nlinarith
  have hd13 : -24 + 43 * x ≠ 0 := by nlinarith
  have hd14 : x - 24 / 43 ≠ 0 := by nlinarith
  field_simp
  ring

theorem lro_A_M1_lm {x : ℝ} (h0 : (3 / 2 : ℝ) ≤ x) (h1 : x ≤ (2 : ℝ)) :
    (2 * lrb2 x (24 / 43) ((8 * x + 1303) / 1750) + 6 * lrb3 x (24 / 43) ((8 * x + 1303) / 1750) / x) < (-7 / 216 : ℝ) := by
  have hid := lro_A_M1_lm_id h0 h1
  have hn := lro_A_M1_lm_num (z := x - (3 / 2 : ℝ)) (by linarith) (by linarith)
  have hP0 : 0 < x := by nlinarith
  have hP1 : 0 < x + 1 := by nlinarith
  have hP2 : 0 < 43 * x - 24 := by nlinarith
  have hD : 0 < (x) * (x + 1) ^ 2 * (43 * x - 24) ^ 2 := (mul_pos (mul_pos hP0 (pow_pos hP1 2)) (pow_pos hP2 2))
  have : 0 < (-7 / 216 : ℝ) - (2 * lrb2 x (24 / 43) ((8 * x + 1303) / 1750) + 6 * lrb3 x (24 / 43) ((8 * x + 1303) / 1750) / x) := by
    rw [hid]; exact div_pos (by linarith) hD
  linarith


theorem lro_A_T65_lm_num {z : ℝ} (hz0 : 0 ≤ z) (hz1 : z ≤ (1 / 2 : ℝ)) :
    (0 : ℝ) < -13660096318381 / 7144200000 * z ^ 10 - 53401416400383311 / 142884000000 * z ^ 9 - 22362763716674720909 / 2286144000000 * z ^ 8 - 82375512629670010049 / 762048000000 * z ^ 7 - 936457954122192686573 / 1524096000000 * z ^ 6 - 1088687835613079980727 / 582543360000 * z ^ 5 - 12709490484189158591537 / 4369075200000 * z ^ 4 - 21789835852045170343381 / 11650867200000 * z ^ 3 + 202884918828559806329 / 863027200000 * z ^ 2 + 333196159308475870653 / 345210880000 * z + 99171783211623395643 / 276168704000 := by
  nlinarith [(by positivity : (0 : ℝ) ≤ z),
    mul_le_mul_of_nonneg_left hz1 (by positivity : (0 : ℝ) ≤ z),
    mul_le_mul_of_nonneg_left hz1 (by positivity : (0 : ℝ) ≤ z ^ 2),
    mul_le_mul_of_nonneg_left hz1 (by positivity : (0 : ℝ) ≤ z ^ 3),
    mul_le_mul_of_nonneg_left hz1 (by positivity : (0 : ℝ) ≤ z ^ 4),
    mul_le_mul_of_nonneg_left hz1 (by positivity : (0 : ℝ) ≤ z ^ 5),
    mul_le_mul_of_nonneg_left hz1 (by positivity : (0 : ℝ) ≤ z ^ 6),
    mul_le_mul_of_nonneg_left hz1 (by positivity : (0 : ℝ) ≤ z ^ 7),
    mul_le_mul_of_nonneg_left hz1 (by positivity : (0 : ℝ) ≤ z ^ 8),
    mul_le_mul_of_nonneg_left hz1 (by positivity : (0 : ℝ) ≤ z ^ 9)]

theorem lro_A_T65_lm_id {x : ℝ} (h0 : (3 / 2 : ℝ) ≤ x) (_h1 : x ≤ (2 : ℝ)) :
    lroF1 x (6 / 5) (x + 24 / 43 * (6 / 5 - 1)) ((8 * x + 1303) / 1750) - (0 : ℝ) = (-13660096318381 / 7144200000 * (x - (3 / 2 : ℝ)) ^ 10 - 53401416400383311 / 142884000000 * (x - (3 / 2 : ℝ)) ^ 9 - 22362763716674720909 / 2286144000000 * (x - (3 / 2 : ℝ)) ^ 8 - 82375512629670010049 / 762048000000 * (x - (3 / 2 : ℝ)) ^ 7 - 936457954122192686573 / 1524096000000 * (x - (3 / 2 : ℝ)) ^ 6 - 1088687835613079980727 / 582543360000 * (x - (3 / 2 : ℝ)) ^ 5 - 12709490484189158591537 / 4369075200000 * (x - (3 / 2 : ℝ)) ^ 4 - 21789835852045170343381 / 11650867200000 * (x - (3 / 2 : ℝ)) ^ 3 + 202884918828559806329 / 863027200000 * (x - (3 / 2 : ℝ)) ^ 2 + 333196159308475870653 / 345210880000 * (x - (3 / 2 : ℝ)) + 99171783211623395643 / 276168704000) /
      ((215 * x + 282) * (x + 1) ^ 2 * (43 * x + 237) ^ 3) := by
  rw [lro_F1_expl (by nlinarith) (by nlinarith) (by nlinarith)]
  rw [show (6 / 5) + (x + 24 / 43 * (6 / 5 - 1)) = (215 * x + 282) / (215 : ℝ) by ring,
    show 2 * ((215 * x + 282) / (215 : ℝ)) + 7 * (6 / 5) = (43 * x + 237) / (43 / 2 : ℝ) by ring]
  simp only [lroM, lroJ, lroK, ssE0, ssDg]
  have hd0 : 215 * x + 282 ≠ 0 := by nlinarith
  have hd1 : x + 1 ≠ 0 := by nlinarith
  have hd2 : 43 * x + 237 ≠ 0 := by nlinarith
  have hp0 : 215 * x + 282 ≠ 0 := by nlinarith
  have hq0 : 43 * x + 237 ≠ 0 := by nlinarith
  have hx0' : x ≠ 0 := by nlinarith
  have hS0 : 1 + x ≠ 0 := by nlinarith
  generalize hp : 215 * x + 282 = p at hp0 ⊢
  generalize hq : 43 * x + 237 = q at hq0 ⊢
  field_simp
  subst hp hq 
  ring

theorem lro_A_T65_lm {x : ℝ} (h0 : (3 / 2 : ℝ) ≤ x) (h1 : x ≤ (2 : ℝ)) :
    (0 : ℝ) < lroF1 x (6 / 5) (x + 24 / 43 * (6 / 5 - 1)) ((8 * x + 1303) / 1750) := by
  have hid := lro_A_T65_lm_id h0 h1
  have hn := lro_A_T65_lm_num (z := x - (3 / 2 : ℝ)) (by linarith) (by linarith)
  have hP0 : 0 < 215 * x + 282 := by nlinarith
  have hP1 : 0 < x + 1 := by nlinarith
  have hP2 : 0 < 43 * x + 237 := by nlinarith
  have hD : 0 < (215 * x + 282) * (x + 1) ^ 2 * (43 * x + 237) ^ 3 := (mul_pos (mul_pos hP0 (pow_pos hP1 2)) (pow_pos hP2 3))
  have : 0 < lroF1 x (6 / 5) (x + 24 / 43 * (6 / 5 - 1)) ((8 * x + 1303) / 1750) - (0 : ℝ) := by
    rw [hid]; exact div_pos (by linarith) hD
  linarith


theorem lro_A_Tx_lm_num {z : ℝ} (hz0 : 0 ≤ z) (hz1 : z ≤ (1 / 2 : ℝ)) :
    (0 : ℝ) < -1555628371 / 153125 * z ^ 14 + 2714402671093 / 3062500 * z ^ 13 - 1436570973397949 / 147000000 * z ^ 12 - 2395728939954041507 / 6321000000 * z ^ 11 - 55275614478328740661 / 15170400000 * z ^ 10 - 796167829403948363 / 43344000 * z ^ 9 - 8664499224004405953937 / 151704000000 * z ^ 8 - 5875481989434836845501 / 50568000000 * z ^ 7 - 10512322262322782329093 / 67424000000 * z ^ 6 - 885241578192732621797 / 6742400000 * z ^ 5 - 5958093857846650118989 / 107878400000 * z ^ 4 + 845290493920320587547 / 107878400000 * z ^ 3 + 1382490138144116087721 / 61644800000 * z ^ 2 + 463947944393177373321 / 43151360000 * z + 15884750515717780929 / 8630272000 := by
  nlinarith [(by positivity : (0 : ℝ) ≤ z),
    mul_le_mul_of_nonneg_left hz1 (by positivity : (0 : ℝ) ≤ z),
    mul_le_mul_of_nonneg_left hz1 (by positivity : (0 : ℝ) ≤ z ^ 2),
    mul_le_mul_of_nonneg_left hz1 (by positivity : (0 : ℝ) ≤ z ^ 3),
    mul_le_mul_of_nonneg_left hz1 (by positivity : (0 : ℝ) ≤ z ^ 4),
    mul_le_mul_of_nonneg_left hz1 (by positivity : (0 : ℝ) ≤ z ^ 5),
    mul_le_mul_of_nonneg_left hz1 (by positivity : (0 : ℝ) ≤ z ^ 6),
    mul_le_mul_of_nonneg_left hz1 (by positivity : (0 : ℝ) ≤ z ^ 7),
    mul_le_mul_of_nonneg_left hz1 (by positivity : (0 : ℝ) ≤ z ^ 8),
    mul_le_mul_of_nonneg_left hz1 (by positivity : (0 : ℝ) ≤ z ^ 9),
    mul_le_mul_of_nonneg_left hz1 (by positivity : (0 : ℝ) ≤ z ^ 10),
    mul_le_mul_of_nonneg_left hz1 (by positivity : (0 : ℝ) ≤ z ^ 11),
    (by positivity : (0 : ℝ) ≤ z ^ 13)]

theorem lro_A_Tx_lm_id {x : ℝ} (h0 : (3 / 2 : ℝ) ≤ x) (_h1 : x ≤ (2 : ℝ)) :
    lroF1 x (x) (x + 24 / 43 * (x - 1)) ((8 * x + 1303) / 1750) - (0 : ℝ) = (-1555628371 / 153125 * (x - (3 / 2 : ℝ)) ^ 14 + 2714402671093 / 3062500 * (x - (3 / 2 : ℝ)) ^ 13 - 1436570973397949 / 147000000 * (x - (3 / 2 : ℝ)) ^ 12 - 2395728939954041507 / 6321000000 * (x - (3 / 2 : ℝ)) ^ 11 - 55275614478328740661 / 15170400000 * (x - (3 / 2 : ℝ)) ^ 10 - 796167829403948363 / 43344000 * (x - (3 / 2 : ℝ)) ^ 9 - 8664499224004405953937 / 151704000000 * (x - (3 / 2 : ℝ)) ^ 8 - 5875481989434836845501 / 50568000000 * (x - (3 / 2 : ℝ)) ^ 7 - 10512322262322782329093 / 67424000000 * (x - (3 / 2 : ℝ)) ^ 6 - 885241578192732621797 / 6742400000 * (x - (3 / 2 : ℝ)) ^ 5 - 5958093857846650118989 / 107878400000 * (x - (3 / 2 : ℝ)) ^ 4 + 845290493920320587547 / 107878400000 * (x - (3 / 2 : ℝ)) ^ 3 + 1382490138144116087721 / 61644800000 * (x - (3 / 2 : ℝ)) ^ 2 + 463947944393177373321 / 43151360000 * (x - (3 / 2 : ℝ)) + 15884750515717780929 / 8630272000) /
      ((55 * x - 12) * (x + 1) ^ 2 * (521 * x - 48) ^ 3 * (x) ^ 4) := by
  rw [lro_F1_expl (by nlinarith) (by nlinarith) (by nlinarith)]
  rw [show (x) + (x + 24 / 43 * (x - 1)) = (55 * x - 12) / (43 / 2 : ℝ) by ring,
    show 2 * ((55 * x - 12) / (43 / 2 : ℝ)) + 7 * (x) = (521 * x - 48) / (43 : ℝ) by ring]
  simp only [lroM, lroJ, lroK, ssE0, ssDg]
  have hd0 : 55 * x - 12 ≠ 0 := by nlinarith
  have hd1 : x + 1 ≠ 0 := by nlinarith
  have hd2 : 521 * x - 48 ≠ 0 := by nlinarith
  have hd3 : x ≠ 0 := by nlinarith
  have hp0 : 55 * x - 12 ≠ 0 := by nlinarith
  have hq0 : 521 * x - 48 ≠ 0 := by nlinarith
  have hx0' : x ≠ 0 := by nlinarith
  have hS0 : 1 + x ≠ 0 := by nlinarith
  generalize hp : 55 * x - 12 = p at hp0 ⊢
  generalize hq : 521 * x - 48 = q at hq0 ⊢
  field_simp
  subst hp hq 
  ring

theorem lro_A_Tx_lm {x : ℝ} (h0 : (3 / 2 : ℝ) ≤ x) (h1 : x ≤ (2 : ℝ)) :
    (0 : ℝ) < lroF1 x (x) (x + 24 / 43 * (x - 1)) ((8 * x + 1303) / 1750) := by
  have hid := lro_A_Tx_lm_id h0 h1
  have hn := lro_A_Tx_lm_num (z := x - (3 / 2 : ℝ)) (by linarith) (by linarith)
  have hP0 : 0 < 55 * x - 12 := by nlinarith
  have hP1 : 0 < x + 1 := by nlinarith
  have hP2 : 0 < 521 * x - 48 := by nlinarith
  have hP3 : 0 < x := by nlinarith
  have hD : 0 < (55 * x - 12) * (x + 1) ^ 2 * (521 * x - 48) ^ 3 * (x) ^ 4 := (mul_pos (mul_pos (mul_pos hP0 (pow_pos hP1 2)) (pow_pos hP2 3)) (pow_pos hP3 4))
  have : 0 < lroF1 x (x) (x + 24 / 43 * (x - 1)) ((8 * x + 1303) / 1750) - (0 : ℝ) := by
    rw [hid]; exact div_pos (by linarith) hD
  linarith


theorem lro_A_M1_lp_num {z : ℝ} (hz0 : 0 ≤ z) (_hz1 : z ≤ (1 / 2 : ℝ)) :
    (0 : ℝ) < 1849 / 240000 * z ^ 9 + 211087 / 57600 * z ^ 8 + 1611969733 / 8640000 * z ^ 7 + 1225172772131 / 743040000 * z ^ 6 + 9396550490321 / 1486080000 * z ^ 5 + 37770136548421 / 2972160000 * z ^ 4 + 1858992289921 / 132096000 * z ^ 3 + 1318963798451 / 158515200 * z ^ 2 + 737605973 / 330240 * z + 20987441 / 176128 := by
  nlinarith [(by positivity : (0 : ℝ) ≤ z),
    (by positivity : (0 : ℝ) ≤ z ^ 2),
    (by positivity : (0 : ℝ) ≤ z ^ 3),
    (by positivity : (0 : ℝ) ≤ z ^ 4),
    (by positivity : (0 : ℝ) ≤ z ^ 5),
    (by positivity : (0 : ℝ) ≤ z ^ 6),
    (by positivity : (0 : ℝ) ≤ z ^ 7),
    (by positivity : (0 : ℝ) ≤ z ^ 8),
    (by positivity : (0 : ℝ) ≤ z ^ 9)]

theorem lro_A_M1_lp_id {x : ℝ} (h0 : (3 / 2 : ℝ) ≤ x) (_h1 : x ≤ (2 : ℝ)) :
    (-7 / 216 : ℝ) - (2 * lrb2 x (24 / 43) ((6 * x + 443) / 600) + 6 * lrb3 x (24 / 43) ((6 * x + 443) / 600) / x) = (1849 / 240000 * (x - (3 / 2 : ℝ)) ^ 9 + 211087 / 57600 * (x - (3 / 2 : ℝ)) ^ 8 + 1611969733 / 8640000 * (x - (3 / 2 : ℝ)) ^ 7 + 1225172772131 / 743040000 * (x - (3 / 2 : ℝ)) ^ 6 + 9396550490321 / 1486080000 * (x - (3 / 2 : ℝ)) ^ 5 + 37770136548421 / 2972160000 * (x - (3 / 2 : ℝ)) ^ 4 + 1858992289921 / 132096000 * (x - (3 / 2 : ℝ)) ^ 3 + 1318963798451 / 158515200 * (x - (3 / 2 : ℝ)) ^ 2 + 737605973 / 330240 * (x - (3 / 2 : ℝ)) + 20987441 / 176128) / ((x) * (x + 1) ^ 2 * (43 * x - 24) ^ 2) := by
  simp only [lrb2, lrb3, lrg2, lrq2, lrq3, lrW3, lrW4, lrd1, lrd2, lrJ2, ssE0]
  have hd0 : x ≠ 0 := by nlinarith
  have hd1 : x * 1 + 0 ≠ 0 := by nlinarith
  have hd2 : 0 + x * 1 ≠ 0 := by nlinarith
  have hd3 : 0 + 1 * x ≠ 0 := by nlinarith
  have hd4 : x + 0 ≠ 0 := by nlinarith
  have hd5 : x + 1 ≠ 0 := by nlinarith
  have hd6 : x * 1 + 1 ≠ 0 := by nlinarith
  have hd7 : 1 + x * 1 ≠ 0 := by nlinarith
  have hd8 : 1 + 1 * x ≠ 0 := by nlinarith
  have hd9 : x + 1 ≠ 0 := by nlinarith
  have hd10 : 43 * x - 24 ≠ 0 := by nlinarith
  have hd11 : x * 43 - 24 ≠ 0 := by nlinarith
  have hd12 : -24 + x * 43 ≠ 0 := by nlinarith
  have hd13 : -24 + 43 * x ≠ 0 := by nlinarith
  have hd14 : x - 24 / 43 ≠ 0 := by nlinarith
  field_simp
  ring

theorem lro_A_M1_lp {x : ℝ} (h0 : (3 / 2 : ℝ) ≤ x) (h1 : x ≤ (2 : ℝ)) :
    (2 * lrb2 x (24 / 43) ((6 * x + 443) / 600) + 6 * lrb3 x (24 / 43) ((6 * x + 443) / 600) / x) < (-7 / 216 : ℝ) := by
  have hid := lro_A_M1_lp_id h0 h1
  have hn := lro_A_M1_lp_num (z := x - (3 / 2 : ℝ)) (by linarith) (by linarith)
  have hP0 : 0 < x := by nlinarith
  have hP1 : 0 < x + 1 := by nlinarith
  have hP2 : 0 < 43 * x - 24 := by nlinarith
  have hD : 0 < (x) * (x + 1) ^ 2 * (43 * x - 24) ^ 2 := (mul_pos (mul_pos hP0 (pow_pos hP1 2)) (pow_pos hP2 2))
  have : 0 < (-7 / 216 : ℝ) - (2 * lrb2 x (24 / 43) ((6 * x + 443) / 600) + 6 * lrb3 x (24 / 43) ((6 * x + 443) / 600) / x) := by
    rw [hid]; exact div_pos (by linarith) hD
  linarith


theorem lro_A_T65_lp_num {z : ℝ} (hz0 : 0 ≤ z) (hz1 : z ≤ (1 / 2 : ℝ)) :
    (0 : ℝ) < -6352409180881 / 1492992000 * z ^ 10 - 10145693389676737 / 22394880000 * z ^ 9 - 1467114258628130131 / 134369280000 * z ^ 8 - 31476384705322691963 / 268738560000 * z ^ 7 - 2456211088932800731 / 3732480000 * z ^ 6 - 462368348352065675369179 / 231115161600000 * z ^ 5 - 1456436608858455302843747 / 462230323200000 * z ^ 4 - 650406494740280910286549 / 308153548800000 * z ^ 3 + 7125472700945088425707 / 45652377600000 * z ^ 2 + 84969041981620656989 / 84541440000 * z + 6348518922311121121 / 16908288000 := by
  nlinarith [(by positivity : (0 : ℝ) ≤ z),
    mul_le_mul_of_nonneg_left hz1 (by positivity : (0 : ℝ) ≤ z),
    mul_le_mul_of_nonneg_left hz1 (by positivity : (0 : ℝ) ≤ z ^ 2),
    mul_le_mul_of_nonneg_left hz1 (by positivity : (0 : ℝ) ≤ z ^ 3),
    mul_le_mul_of_nonneg_left hz1 (by positivity : (0 : ℝ) ≤ z ^ 4),
    mul_le_mul_of_nonneg_left hz1 (by positivity : (0 : ℝ) ≤ z ^ 5),
    mul_le_mul_of_nonneg_left hz1 (by positivity : (0 : ℝ) ≤ z ^ 6),
    mul_le_mul_of_nonneg_left hz1 (by positivity : (0 : ℝ) ≤ z ^ 7),
    mul_le_mul_of_nonneg_left hz1 (by positivity : (0 : ℝ) ≤ z ^ 8),
    mul_le_mul_of_nonneg_left hz1 (by positivity : (0 : ℝ) ≤ z ^ 9)]

theorem lro_A_T65_lp_id {x : ℝ} (h0 : (3 / 2 : ℝ) ≤ x) (_h1 : x ≤ (2 : ℝ)) :
    lroF1 x (6 / 5) (x + 24 / 43 * (6 / 5 - 1)) ((6 * x + 443) / 600) - (0 : ℝ) = (-6352409180881 / 1492992000 * (x - (3 / 2 : ℝ)) ^ 10 - 10145693389676737 / 22394880000 * (x - (3 / 2 : ℝ)) ^ 9 - 1467114258628130131 / 134369280000 * (x - (3 / 2 : ℝ)) ^ 8 - 31476384705322691963 / 268738560000 * (x - (3 / 2 : ℝ)) ^ 7 - 2456211088932800731 / 3732480000 * (x - (3 / 2 : ℝ)) ^ 6 - 462368348352065675369179 / 231115161600000 * (x - (3 / 2 : ℝ)) ^ 5 - 1456436608858455302843747 / 462230323200000 * (x - (3 / 2 : ℝ)) ^ 4 - 650406494740280910286549 / 308153548800000 * (x - (3 / 2 : ℝ)) ^ 3 + 7125472700945088425707 / 45652377600000 * (x - (3 / 2 : ℝ)) ^ 2 + 84969041981620656989 / 84541440000 * (x - (3 / 2 : ℝ)) + 6348518922311121121 / 16908288000) /
      ((215 * x + 282) * (x + 1) ^ 2 * (43 * x + 237) ^ 3) := by
  rw [lro_F1_expl (by nlinarith) (by nlinarith) (by nlinarith)]
  rw [show (6 / 5) + (x + 24 / 43 * (6 / 5 - 1)) = (215 * x + 282) / (215 : ℝ) by ring,
    show 2 * ((215 * x + 282) / (215 : ℝ)) + 7 * (6 / 5) = (43 * x + 237) / (43 / 2 : ℝ) by ring]
  simp only [lroM, lroJ, lroK, ssE0, ssDg]
  have hd0 : 215 * x + 282 ≠ 0 := by nlinarith
  have hd1 : x + 1 ≠ 0 := by nlinarith
  have hd2 : 43 * x + 237 ≠ 0 := by nlinarith
  have hp0 : 215 * x + 282 ≠ 0 := by nlinarith
  have hq0 : 43 * x + 237 ≠ 0 := by nlinarith
  have hx0' : x ≠ 0 := by nlinarith
  have hS0 : 1 + x ≠ 0 := by nlinarith
  generalize hp : 215 * x + 282 = p at hp0 ⊢
  generalize hq : 43 * x + 237 = q at hq0 ⊢
  field_simp
  subst hp hq 
  ring

theorem lro_A_T65_lp {x : ℝ} (h0 : (3 / 2 : ℝ) ≤ x) (h1 : x ≤ (2 : ℝ)) :
    (0 : ℝ) < lroF1 x (6 / 5) (x + 24 / 43 * (6 / 5 - 1)) ((6 * x + 443) / 600) := by
  have hid := lro_A_T65_lp_id h0 h1
  have hn := lro_A_T65_lp_num (z := x - (3 / 2 : ℝ)) (by linarith) (by linarith)
  have hP0 : 0 < 215 * x + 282 := by nlinarith
  have hP1 : 0 < x + 1 := by nlinarith
  have hP2 : 0 < 43 * x + 237 := by nlinarith
  have hD : 0 < (215 * x + 282) * (x + 1) ^ 2 * (43 * x + 237) ^ 3 := (mul_pos (mul_pos hP0 (pow_pos hP1 2)) (pow_pos hP2 3))
  have : 0 < lroF1 x (6 / 5) (x + 24 / 43 * (6 / 5 - 1)) ((6 * x + 443) / 600) - (0 : ℝ) := by
    rw [hid]; exact div_pos (by linarith) hD
  linarith


theorem lro_A_Tx_lp_num {z : ℝ} (hz0 : 0 ≤ z) (hz1 : z ≤ (1 / 2 : ℝ)) :
    (0 : ℝ) < -1555628371 / 32000 * z ^ 14 + 324674108833 / 240000 * z ^ 13 + 25313254578863 / 2880000 * z ^ 12 - 2433915003218687 / 13760000 * z ^ 11 - 7192046535104048249 / 2972160000 * z ^ 10 - 8365875103892861231 / 619200000 * z ^ 9 - 1940783226185651943433 / 44582400000 * z ^ 8 - 3943347802635742811839 / 44582400000 * z ^ 7 - 27066341616685974076237 / 237772800000 * z ^ 6 - 29880571670704515332723 / 356659200000 * z ^ 5 - 22530936300360567913583 / 1426636800000 * z ^ 4 + 14816268053400678815923 / 475545600000 * z ^ 3 + 4462674099212332602023 / 140902400000 * z ^ 2 + 91077233036829269157 / 7045120000 * z + 22732782718867281 / 11008000 := by
  nlinarith [(by positivity : (0 : ℝ) ≤ z),
    (by positivity : (0 : ℝ) ≤ z ^ 2),
    mul_le_mul_of_nonneg_left hz1 (by positivity : (0 : ℝ) ≤ z ^ 2),
    mul_le_mul_of_nonneg_left hz1 (by positivity : (0 : ℝ) ≤ z ^ 3),
    mul_le_mul_of_nonneg_left hz1 (by positivity : (0 : ℝ) ≤ z ^ 4),
    mul_le_mul_of_nonneg_left hz1 (by positivity : (0 : ℝ) ≤ z ^ 5),
    mul_le_mul_of_nonneg_left hz1 (by positivity : (0 : ℝ) ≤ z ^ 6),
    mul_le_mul_of_nonneg_left hz1 (by positivity : (0 : ℝ) ≤ z ^ 7),
    mul_le_mul_of_nonneg_left hz1 (by positivity : (0 : ℝ) ≤ z ^ 8),
    mul_le_mul_of_nonneg_left hz1 (by positivity : (0 : ℝ) ≤ z ^ 9),
    mul_le_mul_of_nonneg_left hz1 (by positivity : (0 : ℝ) ≤ z ^ 10),
    (by positivity : (0 : ℝ) ≤ z ^ 12),
    (by positivity : (0 : ℝ) ≤ z ^ 13),
    mul_le_mul_of_nonneg_left hz1 (by positivity : (0 : ℝ) ≤ z ^ 13)]

theorem lro_A_Tx_lp_id {x : ℝ} (h0 : (3 / 2 : ℝ) ≤ x) (_h1 : x ≤ (2 : ℝ)) :
    lroF1 x (x) (x + 24 / 43 * (x - 1)) ((6 * x + 443) / 600) - (0 : ℝ) = (-1555628371 / 32000 * (x - (3 / 2 : ℝ)) ^ 14 + 324674108833 / 240000 * (x - (3 / 2 : ℝ)) ^ 13 + 25313254578863 / 2880000 * (x - (3 / 2 : ℝ)) ^ 12 - 2433915003218687 / 13760000 * (x - (3 / 2 : ℝ)) ^ 11 - 7192046535104048249 / 2972160000 * (x - (3 / 2 : ℝ)) ^ 10 - 8365875103892861231 / 619200000 * (x - (3 / 2 : ℝ)) ^ 9 - 1940783226185651943433 / 44582400000 * (x - (3 / 2 : ℝ)) ^ 8 - 3943347802635742811839 / 44582400000 * (x - (3 / 2 : ℝ)) ^ 7 - 27066341616685974076237 / 237772800000 * (x - (3 / 2 : ℝ)) ^ 6 - 29880571670704515332723 / 356659200000 * (x - (3 / 2 : ℝ)) ^ 5 - 22530936300360567913583 / 1426636800000 * (x - (3 / 2 : ℝ)) ^ 4 + 14816268053400678815923 / 475545600000 * (x - (3 / 2 : ℝ)) ^ 3 + 4462674099212332602023 / 140902400000 * (x - (3 / 2 : ℝ)) ^ 2 + 91077233036829269157 / 7045120000 * (x - (3 / 2 : ℝ)) + 22732782718867281 / 11008000) /
      ((55 * x - 12) * (x + 1) ^ 2 * (521 * x - 48) ^ 3 * (x) ^ 4) := by
  rw [lro_F1_expl (by nlinarith) (by nlinarith) (by nlinarith)]
  rw [show (x) + (x + 24 / 43 * (x - 1)) = (55 * x - 12) / (43 / 2 : ℝ) by ring,
    show 2 * ((55 * x - 12) / (43 / 2 : ℝ)) + 7 * (x) = (521 * x - 48) / (43 : ℝ) by ring]
  simp only [lroM, lroJ, lroK, ssE0, ssDg]
  have hd0 : 55 * x - 12 ≠ 0 := by nlinarith
  have hd1 : x + 1 ≠ 0 := by nlinarith
  have hd2 : 521 * x - 48 ≠ 0 := by nlinarith
  have hd3 : x ≠ 0 := by nlinarith
  have hp0 : 55 * x - 12 ≠ 0 := by nlinarith
  have hq0 : 521 * x - 48 ≠ 0 := by nlinarith
  have hx0' : x ≠ 0 := by nlinarith
  have hS0 : 1 + x ≠ 0 := by nlinarith
  generalize hp : 55 * x - 12 = p at hp0 ⊢
  generalize hq : 521 * x - 48 = q at hq0 ⊢
  field_simp
  subst hp hq 
  ring

theorem lro_A_Tx_lp {x : ℝ} (h0 : (3 / 2 : ℝ) ≤ x) (h1 : x ≤ (2 : ℝ)) :
    (0 : ℝ) < lroF1 x (x) (x + 24 / 43 * (x - 1)) ((6 * x + 443) / 600) := by
  have hid := lro_A_Tx_lp_id h0 h1
  have hn := lro_A_Tx_lp_num (z := x - (3 / 2 : ℝ)) (by linarith) (by linarith)
  have hP0 : 0 < 55 * x - 12 := by nlinarith
  have hP1 : 0 < x + 1 := by nlinarith
  have hP2 : 0 < 521 * x - 48 := by nlinarith
  have hP3 : 0 < x := by nlinarith
  have hD : 0 < (55 * x - 12) * (x + 1) ^ 2 * (521 * x - 48) ^ 3 * (x) ^ 4 := (mul_pos (mul_pos (mul_pos hP0 (pow_pos hP1 2)) (pow_pos hP2 3)) (pow_pos hP3 4))
  have : 0 < lroF1 x (x) (x + 24 / 43 * (x - 1)) ((6 * x + 443) / 600) - (0 : ℝ) := by
    rw [hid]; exact div_pos (by linarith) hD
  linarith


theorem lro_A_M1_hm_num {z : ℝ} (hz0 : 0 ≤ z) (_hz1 : z ≤ (1 / 2 : ℝ)) :
    (0 : ℝ) < 338 / 2296875 * z ^ 9 + 754247 / 4593750 * z ^ 8 + 1273876553 / 73500000 * z ^ 7 + 297021080399 / 1911000000 * z ^ 6 + 3932671317853 / 6879600000 * z ^ 5 + 109298365153 / 101920000 * z ^ 4 + 240551762039 / 220147200 * z ^ 3 + 3529377247 / 5870592 * z ^ 2 + 5579457635 / 35223552 * z + 144572699 / 23482368 := by
  nlinarith [(by positivity : (0 : ℝ) ≤ z),
    (by positivity : (0 : ℝ) ≤ z ^ 2),
    (by positivity : (0 : ℝ) ≤ z ^ 3),
    (by positivity : (0 : ℝ) ≤ z ^ 4),
    (by positivity : (0 : ℝ) ≤ z ^ 5),
    (by positivity : (0 : ℝ) ≤ z ^ 6),
    (by positivity : (0 : ℝ) ≤ z ^ 7),
    (by positivity : (0 : ℝ) ≤ z ^ 8),
    (by positivity : (0 : ℝ) ≤ z ^ 9)]

theorem lro_A_M1_hm_id {x : ℝ} (h0 : (3 / 2 : ℝ) ≤ x) (_h1 : x ≤ (2 : ℝ)) :
    (-7 / 216 : ℝ) - (2 * lrb2 x (10 / 13) ((8 * x + 1303) / 1750) + 6 * lrb3 x (10 / 13) ((8 * x + 1303) / 1750) / x) = (338 / 2296875 * (x - (3 / 2 : ℝ)) ^ 9 + 754247 / 4593750 * (x - (3 / 2 : ℝ)) ^ 8 + 1273876553 / 73500000 * (x - (3 / 2 : ℝ)) ^ 7 + 297021080399 / 1911000000 * (x - (3 / 2 : ℝ)) ^ 6 + 3932671317853 / 6879600000 * (x - (3 / 2 : ℝ)) ^ 5 + 109298365153 / 101920000 * (x - (3 / 2 : ℝ)) ^ 4 + 240551762039 / 220147200 * (x - (3 / 2 : ℝ)) ^ 3 + 3529377247 / 5870592 * (x - (3 / 2 : ℝ)) ^ 2 + 5579457635 / 35223552 * (x - (3 / 2 : ℝ)) + 144572699 / 23482368) / ((x) * (x + 1) ^ 2 * (13 * x - 10) ^ 2) := by
  simp only [lrb2, lrb3, lrg2, lrq2, lrq3, lrW3, lrW4, lrd1, lrd2, lrJ2, ssE0]
  have hd0 : x ≠ 0 := by nlinarith
  have hd1 : x * 1 + 0 ≠ 0 := by nlinarith
  have hd2 : 0 + x * 1 ≠ 0 := by nlinarith
  have hd3 : 0 + 1 * x ≠ 0 := by nlinarith
  have hd4 : x + 0 ≠ 0 := by nlinarith
  have hd5 : x + 1 ≠ 0 := by nlinarith
  have hd6 : x * 1 + 1 ≠ 0 := by nlinarith
  have hd7 : 1 + x * 1 ≠ 0 := by nlinarith
  have hd8 : 1 + 1 * x ≠ 0 := by nlinarith
  have hd9 : x + 1 ≠ 0 := by nlinarith
  have hd10 : 13 * x - 10 ≠ 0 := by nlinarith
  have hd11 : x * 13 - 10 ≠ 0 := by nlinarith
  have hd12 : -10 + x * 13 ≠ 0 := by nlinarith
  have hd13 : -10 + 13 * x ≠ 0 := by nlinarith
  have hd14 : x - 10 / 13 ≠ 0 := by nlinarith
  field_simp
  ring

theorem lro_A_M1_hm {x : ℝ} (h0 : (3 / 2 : ℝ) ≤ x) (h1 : x ≤ (2 : ℝ)) :
    (2 * lrb2 x (10 / 13) ((8 * x + 1303) / 1750) + 6 * lrb3 x (10 / 13) ((8 * x + 1303) / 1750) / x) < (-7 / 216 : ℝ) := by
  have hid := lro_A_M1_hm_id h0 h1
  have hn := lro_A_M1_hm_num (z := x - (3 / 2 : ℝ)) (by linarith) (by linarith)
  have hP0 : 0 < x := by nlinarith
  have hP1 : 0 < x + 1 := by nlinarith
  have hP2 : 0 < 13 * x - 10 := by nlinarith
  have hD : 0 < (x) * (x + 1) ^ 2 * (13 * x - 10) ^ 2 := (mul_pos (mul_pos hP0 (pow_pos hP1 2)) (pow_pos hP2 2))
  have : 0 < (-7 / 216 : ℝ) - (2 * lrb2 x (10 / 13) ((8 * x + 1303) / 1750) + 6 * lrb3 x (10 / 13) ((8 * x + 1303) / 1750) / x) := by
    rw [hid]; exact div_pos (by linarith) hD
  linarith


theorem lro_A_T65_hm_num {z : ℝ} (hz0 : 0 ≤ z) (hz1 : z ≤ (1 / 2 : ℝ)) :
    (0 : ℝ) < -114117788941 / 57153600 * z ^ 10 - 49622341388087 / 127008000 * z ^ 9 - 313810519628904779 / 30481920000 * z ^ 8 - 10487461314991231831 / 91445760000 * z ^ 7 - 1003458401239919818093 / 1524096000000 * z ^ 6 - 16095754024516074646057 / 7925299200000 * z ^ 5 - 1925403363740817731207 / 594397440000 * z ^ 4 - 401834109997678475321 / 181149696000 * z ^ 3 + 127298693886710280013 / 1293926400000 * z ^ 2 + 175819441748536699967 / 172523520000 * z + 56153842718805027217 / 138018816000 := by
  nlinarith [hz1,
    mul_le_mul_of_nonneg_left hz1 (by positivity : (0 : ℝ) ≤ z),
    mul_le_mul_of_nonneg_left hz1 (by positivity : (0 : ℝ) ≤ z ^ 2),
    mul_le_mul_of_nonneg_left hz1 (by positivity : (0 : ℝ) ≤ z ^ 3),
    mul_le_mul_of_nonneg_left hz1 (by positivity : (0 : ℝ) ≤ z ^ 4),
    mul_le_mul_of_nonneg_left hz1 (by positivity : (0 : ℝ) ≤ z ^ 5),
    mul_le_mul_of_nonneg_left hz1 (by positivity : (0 : ℝ) ≤ z ^ 6),
    mul_le_mul_of_nonneg_left hz1 (by positivity : (0 : ℝ) ≤ z ^ 7),
    mul_le_mul_of_nonneg_left hz1 (by positivity : (0 : ℝ) ≤ z ^ 8),
    mul_le_mul_of_nonneg_left hz1 (by positivity : (0 : ℝ) ≤ z ^ 9)]

theorem lro_A_T65_hm_id {x : ℝ} (h0 : (3 / 2 : ℝ) ≤ x) (_h1 : x ≤ (2 : ℝ)) :
    lroF1 x (6 / 5) (x + 10 / 13 * (6 / 5 - 1)) ((8 * x + 1303) / 1750) - (0 : ℝ) = (-114117788941 / 57153600 * (x - (3 / 2 : ℝ)) ^ 10 - 49622341388087 / 127008000 * (x - (3 / 2 : ℝ)) ^ 9 - 313810519628904779 / 30481920000 * (x - (3 / 2 : ℝ)) ^ 8 - 10487461314991231831 / 91445760000 * (x - (3 / 2 : ℝ)) ^ 7 - 1003458401239919818093 / 1524096000000 * (x - (3 / 2 : ℝ)) ^ 6 - 16095754024516074646057 / 7925299200000 * (x - (3 / 2 : ℝ)) ^ 5 - 1925403363740817731207 / 594397440000 * (x - (3 / 2 : ℝ)) ^ 4 - 401834109997678475321 / 181149696000 * (x - (3 / 2 : ℝ)) ^ 3 + 127298693886710280013 / 1293926400000 * (x - (3 / 2 : ℝ)) ^ 2 + 175819441748536699967 / 172523520000 * (x - (3 / 2 : ℝ)) + 56153842718805027217 / 138018816000) /
      ((65 * x + 88) * (x + 1) ^ 2 * (65 * x + 361) ^ 3) := by
  rw [lro_F1_expl (by nlinarith) (by nlinarith) (by nlinarith)]
  rw [show (6 / 5) + (x + 10 / 13 * (6 / 5 - 1)) = (65 * x + 88) / (65 : ℝ) by ring,
    show 2 * ((65 * x + 88) / (65 : ℝ)) + 7 * (6 / 5) = (65 * x + 361) / (65 / 2 : ℝ) by ring]
  simp only [lroM, lroJ, lroK, ssE0, ssDg]
  have hd0 : 65 * x + 88 ≠ 0 := by nlinarith
  have hd1 : x + 1 ≠ 0 := by nlinarith
  have hd2 : 65 * x + 361 ≠ 0 := by nlinarith
  have hp0 : 65 * x + 88 ≠ 0 := by nlinarith
  have hq0 : 65 * x + 361 ≠ 0 := by nlinarith
  have hx0' : x ≠ 0 := by nlinarith
  have hS0 : 1 + x ≠ 0 := by nlinarith
  generalize hp : 65 * x + 88 = p at hp0 ⊢
  generalize hq : 65 * x + 361 = q at hq0 ⊢
  field_simp
  subst hp hq 
  ring

theorem lro_A_T65_hm {x : ℝ} (h0 : (3 / 2 : ℝ) ≤ x) (h1 : x ≤ (2 : ℝ)) :
    (0 : ℝ) < lroF1 x (6 / 5) (x + 10 / 13 * (6 / 5 - 1)) ((8 * x + 1303) / 1750) := by
  have hid := lro_A_T65_hm_id h0 h1
  have hn := lro_A_T65_hm_num (z := x - (3 / 2 : ℝ)) (by linarith) (by linarith)
  have hP0 : 0 < 65 * x + 88 := by nlinarith
  have hP1 : 0 < x + 1 := by nlinarith
  have hP2 : 0 < 65 * x + 361 := by nlinarith
  have hD : 0 < (65 * x + 88) * (x + 1) ^ 2 * (65 * x + 361) ^ 3 := (mul_pos (mul_pos hP0 (pow_pos hP1 2)) (pow_pos hP2 3))
  have : 0 < lroF1 x (6 / 5) (x + 10 / 13 * (6 / 5 - 1)) ((8 * x + 1303) / 1750) - (0 : ℝ) := by
    rw [hid]; exact div_pos (by linarith) hD
  linarith


theorem lro_A_Tx_hm_num {z : ℝ} (hz0 : 0 ≤ z) (hz1 : z ≤ (1 / 2 : ℝ)) :
    (0 : ℝ) < -77953446 / 765625 * z ^ 14 + 13625619391 / 1531250 * z ^ 13 - 489860387187 / 4900000 * z ^ 12 - 299751308069943 / 79625000 * z ^ 11 - 90250240418491483 / 2548000000 * z ^ 10 - 265833719162204383 / 1528800000 * z ^ 9 - 47865601022419085897 / 91728000000 * z ^ 8 - 1926846354429514081 / 1911000000 * z ^ 7 - 17523309071646605083 / 14112000000 * z ^ 6 - 10580614732015813543 / 12230400000 * z ^ 5 - 4393002561345440981 / 36691200000 * z ^ 4 + 547527865416808439 / 1528800000 * z ^ 3 + 132610694555110878047 / 391372800000 * z ^ 2 + 3490875328853472019 / 26091520000 * z + 435450820715300059 / 20873216000 := by
  nlinarith [(by positivity : (0 : ℝ) ≤ z),
    (by positivity : (0 : ℝ) ≤ z ^ 2),
    mul_le_mul_of_nonneg_left hz1 (by positivity : (0 : ℝ) ≤ z ^ 2),
    mul_le_mul_of_nonneg_left hz1 (by positivity : (0 : ℝ) ≤ z ^ 3),
    mul_le_mul_of_nonneg_left hz1 (by positivity : (0 : ℝ) ≤ z ^ 4),
    mul_le_mul_of_nonneg_left hz1 (by positivity : (0 : ℝ) ≤ z ^ 5),
    mul_le_mul_of_nonneg_left hz1 (by positivity : (0 : ℝ) ≤ z ^ 6),
    mul_le_mul_of_nonneg_left hz1 (by positivity : (0 : ℝ) ≤ z ^ 7),
    mul_le_mul_of_nonneg_left hz1 (by positivity : (0 : ℝ) ≤ z ^ 8),
    mul_le_mul_of_nonneg_left hz1 (by positivity : (0 : ℝ) ≤ z ^ 9),
    mul_le_mul_of_nonneg_left hz1 (by positivity : (0 : ℝ) ≤ z ^ 10),
    mul_le_mul_of_nonneg_left hz1 (by positivity : (0 : ℝ) ≤ z ^ 11),
    (by positivity : (0 : ℝ) ≤ z ^ 13)]

theorem lro_A_Tx_hm_id {x : ℝ} (h0 : (3 / 2 : ℝ) ≤ x) (_h1 : x ≤ (2 : ℝ)) :
    lroF1 x (x) (x + 10 / 13 * (x - 1)) ((8 * x + 1303) / 1750) - (0 : ℝ) = (-77953446 / 765625 * (x - (3 / 2 : ℝ)) ^ 14 + 13625619391 / 1531250 * (x - (3 / 2 : ℝ)) ^ 13 - 489860387187 / 4900000 * (x - (3 / 2 : ℝ)) ^ 12 - 299751308069943 / 79625000 * (x - (3 / 2 : ℝ)) ^ 11 - 90250240418491483 / 2548000000 * (x - (3 / 2 : ℝ)) ^ 10 - 265833719162204383 / 1528800000 * (x - (3 / 2 : ℝ)) ^ 9 - 47865601022419085897 / 91728000000 * (x - (3 / 2 : ℝ)) ^ 8 - 1926846354429514081 / 1911000000 * (x - (3 / 2 : ℝ)) ^ 7 - 17523309071646605083 / 14112000000 * (x - (3 / 2 : ℝ)) ^ 6 - 10580614732015813543 / 12230400000 * (x - (3 / 2 : ℝ)) ^ 5 - 4393002561345440981 / 36691200000 * (x - (3 / 2 : ℝ)) ^ 4 + 547527865416808439 / 1528800000 * (x - (3 / 2 : ℝ)) ^ 3 + 132610694555110878047 / 391372800000 * (x - (3 / 2 : ℝ)) ^ 2 + 3490875328853472019 / 26091520000 * (x - (3 / 2 : ℝ)) + 435450820715300059 / 20873216000) /
      ((18 * x - 5) * (x + 1) ^ 2 * (163 * x - 20) ^ 3 * (x) ^ 4) := by
  rw [lro_F1_expl (by nlinarith) (by nlinarith) (by nlinarith)]
  rw [show (x) + (x + 10 / 13 * (x - 1)) = (18 * x - 5) / (13 / 2 : ℝ) by ring,
    show 2 * ((18 * x - 5) / (13 / 2 : ℝ)) + 7 * (x) = (163 * x - 20) / (13 : ℝ) by ring]
  simp only [lroM, lroJ, lroK, ssE0, ssDg]
  have hd0 : 18 * x - 5 ≠ 0 := by nlinarith
  have hd1 : x + 1 ≠ 0 := by nlinarith
  have hd2 : 163 * x - 20 ≠ 0 := by nlinarith
  have hd3 : x ≠ 0 := by nlinarith
  have hp0 : 18 * x - 5 ≠ 0 := by nlinarith
  have hq0 : 163 * x - 20 ≠ 0 := by nlinarith
  have hx0' : x ≠ 0 := by nlinarith
  have hS0 : 1 + x ≠ 0 := by nlinarith
  generalize hp : 18 * x - 5 = p at hp0 ⊢
  generalize hq : 163 * x - 20 = q at hq0 ⊢
  field_simp
  subst hp hq 
  ring

theorem lro_A_Tx_hm {x : ℝ} (h0 : (3 / 2 : ℝ) ≤ x) (h1 : x ≤ (2 : ℝ)) :
    (0 : ℝ) < lroF1 x (x) (x + 10 / 13 * (x - 1)) ((8 * x + 1303) / 1750) := by
  have hid := lro_A_Tx_hm_id h0 h1
  have hn := lro_A_Tx_hm_num (z := x - (3 / 2 : ℝ)) (by linarith) (by linarith)
  have hP0 : 0 < 18 * x - 5 := by nlinarith
  have hP1 : 0 < x + 1 := by nlinarith
  have hP2 : 0 < 163 * x - 20 := by nlinarith
  have hP3 : 0 < x := by nlinarith
  have hD : 0 < (18 * x - 5) * (x + 1) ^ 2 * (163 * x - 20) ^ 3 * (x) ^ 4 := (mul_pos (mul_pos (mul_pos hP0 (pow_pos hP1 2)) (pow_pos hP2 3)) (pow_pos hP3 4))
  have : 0 < lroF1 x (x) (x + 10 / 13 * (x - 1)) ((8 * x + 1303) / 1750) - (0 : ℝ) := by
    rw [hid]; exact div_pos (by linarith) hD
  linarith


theorem lro_A_M1_hp_num {z : ℝ} (hz0 : 0 ≤ z) (_hz1 : z ≤ (1 / 2 : ℝ)) :
    (0 : ℝ) < 169 / 240000 * z ^ 9 + 524719 / 1440000 * z ^ 8 + 33553553 / 1728000 * z ^ 7 + 36993056221 / 224640000 * z ^ 6 + 267048799879 / 449280000 * z ^ 5 + 994323324571 / 898560000 * z ^ 4 + 404304108239 / 359424000 * z ^ 3 + 89045594983 / 143769600 * z ^ 2 + 98077933 / 599040 * z + 360231 / 53248 := by
  nlinarith [(by positivity : (0 : ℝ) ≤ z),
    (by positivity : (0 : ℝ) ≤ z ^ 2),
    (by positivity : (0 : ℝ) ≤ z ^ 3),
    (by positivity : (0 : ℝ) ≤ z ^ 4),
    (by positivity : (0 : ℝ) ≤ z ^ 5),
    (by positivity : (0 : ℝ) ≤ z ^ 6),
    (by positivity : (0 : ℝ) ≤ z ^ 7),
    (by positivity : (0 : ℝ) ≤ z ^ 8),
    (by positivity : (0 : ℝ) ≤ z ^ 9)]

theorem lro_A_M1_hp_id {x : ℝ} (h0 : (3 / 2 : ℝ) ≤ x) (_h1 : x ≤ (2 : ℝ)) :
    (-7 / 216 : ℝ) - (2 * lrb2 x (10 / 13) ((6 * x + 443) / 600) + 6 * lrb3 x (10 / 13) ((6 * x + 443) / 600) / x) = (169 / 240000 * (x - (3 / 2 : ℝ)) ^ 9 + 524719 / 1440000 * (x - (3 / 2 : ℝ)) ^ 8 + 33553553 / 1728000 * (x - (3 / 2 : ℝ)) ^ 7 + 36993056221 / 224640000 * (x - (3 / 2 : ℝ)) ^ 6 + 267048799879 / 449280000 * (x - (3 / 2 : ℝ)) ^ 5 + 994323324571 / 898560000 * (x - (3 / 2 : ℝ)) ^ 4 + 404304108239 / 359424000 * (x - (3 / 2 : ℝ)) ^ 3 + 89045594983 / 143769600 * (x - (3 / 2 : ℝ)) ^ 2 + 98077933 / 599040 * (x - (3 / 2 : ℝ)) + 360231 / 53248) / ((x) * (x + 1) ^ 2 * (13 * x - 10) ^ 2) := by
  simp only [lrb2, lrb3, lrg2, lrq2, lrq3, lrW3, lrW4, lrd1, lrd2, lrJ2, ssE0]
  have hd0 : x ≠ 0 := by nlinarith
  have hd1 : x * 1 + 0 ≠ 0 := by nlinarith
  have hd2 : 0 + x * 1 ≠ 0 := by nlinarith
  have hd3 : 0 + 1 * x ≠ 0 := by nlinarith
  have hd4 : x + 0 ≠ 0 := by nlinarith
  have hd5 : x + 1 ≠ 0 := by nlinarith
  have hd6 : x * 1 + 1 ≠ 0 := by nlinarith
  have hd7 : 1 + x * 1 ≠ 0 := by nlinarith
  have hd8 : 1 + 1 * x ≠ 0 := by nlinarith
  have hd9 : x + 1 ≠ 0 := by nlinarith
  have hd10 : 13 * x - 10 ≠ 0 := by nlinarith
  have hd11 : x * 13 - 10 ≠ 0 := by nlinarith
  have hd12 : -10 + x * 13 ≠ 0 := by nlinarith
  have hd13 : -10 + 13 * x ≠ 0 := by nlinarith
  have hd14 : x - 10 / 13 ≠ 0 := by nlinarith
  field_simp
  ring

theorem lro_A_M1_hp {x : ℝ} (h0 : (3 / 2 : ℝ) ≤ x) (h1 : x ≤ (2 : ℝ)) :
    (2 * lrb2 x (10 / 13) ((6 * x + 443) / 600) + 6 * lrb3 x (10 / 13) ((6 * x + 443) / 600) / x) < (-7 / 216 : ℝ) := by
  have hid := lro_A_M1_hp_id h0 h1
  have hn := lro_A_M1_hp_num (z := x - (3 / 2 : ℝ)) (by linarith) (by linarith)
  have hP0 : 0 < x := by nlinarith
  have hP1 : 0 < x + 1 := by nlinarith
  have hP2 : 0 < 13 * x - 10 := by nlinarith
  have hD : 0 < (x) * (x + 1) ^ 2 * (13 * x - 10) ^ 2 := (mul_pos (mul_pos hP0 (pow_pos hP1 2)) (pow_pos hP2 2))
  have : 0 < (-7 / 216 : ℝ) - (2 * lrb2 x (10 / 13) ((6 * x + 443) / 600) + 6 * lrb3 x (10 / 13) ((6 * x + 443) / 600) / x) := by
    rw [hid]; exact div_pos (by linarith) hD
  linarith


theorem lro_A_T65_hp_num {z : ℝ} (hz0 : 0 ≤ z) (hz1 : z ≤ (1 / 2 : ℝ)) :
    (0 : ℝ) < -53068651441 / 11943936 * z ^ 10 - 84925105420441 / 179159040 * z ^ 9 - 61791373145040539 / 5374771200 * z ^ 8 - 445344564724725757 / 3583180800 * z ^ 7 - 94741796697175154149 / 134369280000 * z ^ 6 - 10121754532060615217983 / 4658135040000 * z ^ 5 - 32631167878795599204491 / 9316270080000 * z ^ 4 - 712410686364273802267 / 286654464000 * z ^ 3 + 2647827800239383555857 / 1117952409600000 * z ^ 2 + 2184605242806459945479 / 2070282240000 * z + 4730421513697269456577 / 11179524096000 := by
  nlinarith [hz1,
    mul_le_mul_of_nonneg_left hz1 (by positivity : (0 : ℝ) ≤ z),
    mul_le_mul_of_nonneg_left hz1 (by positivity : (0 : ℝ) ≤ z ^ 2),
    mul_le_mul_of_nonneg_left hz1 (by positivity : (0 : ℝ) ≤ z ^ 3),
    mul_le_mul_of_nonneg_left hz1 (by positivity : (0 : ℝ) ≤ z ^ 4),
    mul_le_mul_of_nonneg_left hz1 (by positivity : (0 : ℝ) ≤ z ^ 5),
    mul_le_mul_of_nonneg_left hz1 (by positivity : (0 : ℝ) ≤ z ^ 6),
    mul_le_mul_of_nonneg_left hz1 (by positivity : (0 : ℝ) ≤ z ^ 7),
    mul_le_mul_of_nonneg_left hz1 (by positivity : (0 : ℝ) ≤ z ^ 8),
    mul_le_mul_of_nonneg_left hz1 (by positivity : (0 : ℝ) ≤ z ^ 9)]

theorem lro_A_T65_hp_id {x : ℝ} (h0 : (3 / 2 : ℝ) ≤ x) (_h1 : x ≤ (2 : ℝ)) :
    lroF1 x (6 / 5) (x + 10 / 13 * (6 / 5 - 1)) ((6 * x + 443) / 600) - (0 : ℝ) = (-53068651441 / 11943936 * (x - (3 / 2 : ℝ)) ^ 10 - 84925105420441 / 179159040 * (x - (3 / 2 : ℝ)) ^ 9 - 61791373145040539 / 5374771200 * (x - (3 / 2 : ℝ)) ^ 8 - 445344564724725757 / 3583180800 * (x - (3 / 2 : ℝ)) ^ 7 - 94741796697175154149 / 134369280000 * (x - (3 / 2 : ℝ)) ^ 6 - 10121754532060615217983 / 4658135040000 * (x - (3 / 2 : ℝ)) ^ 5 - 32631167878795599204491 / 9316270080000 * (x - (3 / 2 : ℝ)) ^ 4 - 712410686364273802267 / 286654464000 * (x - (3 / 2 : ℝ)) ^ 3 + 2647827800239383555857 / 1117952409600000 * (x - (3 / 2 : ℝ)) ^ 2 + 2184605242806459945479 / 2070282240000 * (x - (3 / 2 : ℝ)) + 4730421513697269456577 / 11179524096000) /
      ((65 * x + 88) * (x + 1) ^ 2 * (65 * x + 361) ^ 3) := by
  rw [lro_F1_expl (by nlinarith) (by nlinarith) (by nlinarith)]
  rw [show (6 / 5) + (x + 10 / 13 * (6 / 5 - 1)) = (65 * x + 88) / (65 : ℝ) by ring,
    show 2 * ((65 * x + 88) / (65 : ℝ)) + 7 * (6 / 5) = (65 * x + 361) / (65 / 2 : ℝ) by ring]
  simp only [lroM, lroJ, lroK, ssE0, ssDg]
  have hd0 : 65 * x + 88 ≠ 0 := by nlinarith
  have hd1 : x + 1 ≠ 0 := by nlinarith
  have hd2 : 65 * x + 361 ≠ 0 := by nlinarith
  have hp0 : 65 * x + 88 ≠ 0 := by nlinarith
  have hq0 : 65 * x + 361 ≠ 0 := by nlinarith
  have hx0' : x ≠ 0 := by nlinarith
  have hS0 : 1 + x ≠ 0 := by nlinarith
  generalize hp : 65 * x + 88 = p at hp0 ⊢
  generalize hq : 65 * x + 361 = q at hq0 ⊢
  field_simp
  subst hp hq 
  ring

theorem lro_A_T65_hp {x : ℝ} (h0 : (3 / 2 : ℝ) ≤ x) (h1 : x ≤ (2 : ℝ)) :
    (0 : ℝ) < lroF1 x (6 / 5) (x + 10 / 13 * (6 / 5 - 1)) ((6 * x + 443) / 600) := by
  have hid := lro_A_T65_hp_id h0 h1
  have hn := lro_A_T65_hp_num (z := x - (3 / 2 : ℝ)) (by linarith) (by linarith)
  have hP0 : 0 < 65 * x + 88 := by nlinarith
  have hP1 : 0 < x + 1 := by nlinarith
  have hP2 : 0 < 65 * x + 361 := by nlinarith
  have hD : 0 < (65 * x + 88) * (x + 1) ^ 2 * (65 * x + 361) ^ 3 := (mul_pos (mul_pos hP0 (pow_pos hP1 2)) (pow_pos hP2 3))
  have : 0 < lroF1 x (6 / 5) (x + 10 / 13 * (6 / 5 - 1)) ((6 * x + 443) / 600) - (0 : ℝ) := by
    rw [hid]; exact div_pos (by linarith) hD
  linarith


theorem lro_A_Tx_hp_num {z : ℝ} (hz0 : 0 ≤ z) (hz1 : z ≤ (1 / 2 : ℝ)) :
    (0 : ℝ) < -38976723 / 80000 * z ^ 14 + 2181075779 / 160000 * z ^ 13 + 81101126123 / 960000 * z ^ 12 - 26784842750183 / 14976000 * z ^ 11 - 4431913819102987 / 187200000 * z ^ 10 - 288018903840508513 / 2246400000 * z ^ 9 - 66046266077838117 / 166400000 * z ^ 8 - 20456503209576554977 / 26956800000 * z ^ 7 - 18794062135557331667 / 21565440000 * z ^ 6 - 32725428830714160847 / 71884800000 * z ^ 5 + 92646529959433815721 / 431308800000 * z ^ 4 + 477402576181668438953 / 862617600000 * z ^ 3 + 119494192017223040333 / 287539200000 * z ^ 2 + 3272811932357876443 / 21565440000 * z + 783638192308267771 / 34504704000 := by
  nlinarith [(by positivity : (0 : ℝ) ≤ z),
    (by positivity : (0 : ℝ) ≤ z ^ 2),
    (by positivity : (0 : ℝ) ≤ z ^ 3),
    mul_le_mul_of_nonneg_left hz1 (by positivity : (0 : ℝ) ≤ z ^ 3),
    mul_le_mul_of_nonneg_left hz1 (by positivity : (0 : ℝ) ≤ z ^ 4),
    mul_le_mul_of_nonneg_left hz1 (by positivity : (0 : ℝ) ≤ z ^ 5),
    mul_le_mul_of_nonneg_left hz1 (by positivity : (0 : ℝ) ≤ z ^ 6),
    mul_le_mul_of_nonneg_left hz1 (by positivity : (0 : ℝ) ≤ z ^ 7),
    mul_le_mul_of_nonneg_left hz1 (by positivity : (0 : ℝ) ≤ z ^ 8),
    mul_le_mul_of_nonneg_left hz1 (by positivity : (0 : ℝ) ≤ z ^ 9),
    mul_le_mul_of_nonneg_left hz1 (by positivity : (0 : ℝ) ≤ z ^ 10),
    (by positivity : (0 : ℝ) ≤ z ^ 12),
    (by positivity : (0 : ℝ) ≤ z ^ 13),
    mul_le_mul_of_nonneg_left hz1 (by positivity : (0 : ℝ) ≤ z ^ 13)]

theorem lro_A_Tx_hp_id {x : ℝ} (h0 : (3 / 2 : ℝ) ≤ x) (_h1 : x ≤ (2 : ℝ)) :
    lroF1 x (x) (x + 10 / 13 * (x - 1)) ((6 * x + 443) / 600) - (0 : ℝ) = (-38976723 / 80000 * (x - (3 / 2 : ℝ)) ^ 14 + 2181075779 / 160000 * (x - (3 / 2 : ℝ)) ^ 13 + 81101126123 / 960000 * (x - (3 / 2 : ℝ)) ^ 12 - 26784842750183 / 14976000 * (x - (3 / 2 : ℝ)) ^ 11 - 4431913819102987 / 187200000 * (x - (3 / 2 : ℝ)) ^ 10 - 288018903840508513 / 2246400000 * (x - (3 / 2 : ℝ)) ^ 9 - 66046266077838117 / 166400000 * (x - (3 / 2 : ℝ)) ^ 8 - 20456503209576554977 / 26956800000 * (x - (3 / 2 : ℝ)) ^ 7 - 18794062135557331667 / 21565440000 * (x - (3 / 2 : ℝ)) ^ 6 - 32725428830714160847 / 71884800000 * (x - (3 / 2 : ℝ)) ^ 5 + 92646529959433815721 / 431308800000 * (x - (3 / 2 : ℝ)) ^ 4 + 477402576181668438953 / 862617600000 * (x - (3 / 2 : ℝ)) ^ 3 + 119494192017223040333 / 287539200000 * (x - (3 / 2 : ℝ)) ^ 2 + 3272811932357876443 / 21565440000 * (x - (3 / 2 : ℝ)) + 783638192308267771 / 34504704000) /
      ((18 * x - 5) * (x + 1) ^ 2 * (163 * x - 20) ^ 3 * (x) ^ 4) := by
  rw [lro_F1_expl (by nlinarith) (by nlinarith) (by nlinarith)]
  rw [show (x) + (x + 10 / 13 * (x - 1)) = (18 * x - 5) / (13 / 2 : ℝ) by ring,
    show 2 * ((18 * x - 5) / (13 / 2 : ℝ)) + 7 * (x) = (163 * x - 20) / (13 : ℝ) by ring]
  simp only [lroM, lroJ, lroK, ssE0, ssDg]
  have hd0 : 18 * x - 5 ≠ 0 := by nlinarith
  have hd1 : x + 1 ≠ 0 := by nlinarith
  have hd2 : 163 * x - 20 ≠ 0 := by nlinarith
  have hd3 : x ≠ 0 := by nlinarith
  have hp0 : 18 * x - 5 ≠ 0 := by nlinarith
  have hq0 : 163 * x - 20 ≠ 0 := by nlinarith
  have hx0' : x ≠ 0 := by nlinarith
  have hS0 : 1 + x ≠ 0 := by nlinarith
  generalize hp : 18 * x - 5 = p at hp0 ⊢
  generalize hq : 163 * x - 20 = q at hq0 ⊢
  field_simp
  subst hp hq 
  ring

theorem lro_A_Tx_hp {x : ℝ} (h0 : (3 / 2 : ℝ) ≤ x) (h1 : x ≤ (2 : ℝ)) :
    (0 : ℝ) < lroF1 x (x) (x + 10 / 13 * (x - 1)) ((6 * x + 443) / 600) := by
  have hid := lro_A_Tx_hp_id h0 h1
  have hn := lro_A_Tx_hp_num (z := x - (3 / 2 : ℝ)) (by linarith) (by linarith)
  have hP0 : 0 < 18 * x - 5 := by nlinarith
  have hP1 : 0 < x + 1 := by nlinarith
  have hP2 : 0 < 163 * x - 20 := by nlinarith
  have hP3 : 0 < x := by nlinarith
  have hD : 0 < (18 * x - 5) * (x + 1) ^ 2 * (163 * x - 20) ^ 3 * (x) ^ 4 := (mul_pos (mul_pos (mul_pos hP0 (pow_pos hP1 2)) (pow_pos hP2 3)) (pow_pos hP3 4))
  have : 0 < lroF1 x (x) (x + 10 / 13 * (x - 1)) ((6 * x + 443) / 600) - (0 : ℝ) := by
    rw [hid]; exact div_pos (by linarith) hD
  linarith

/-- **Reciprocal-shape concavity of `F₁` on the large shapes**. -/
theorem lro_A_recip {x a C u : ℝ} (hx : 3 / 2 ≤ x) (hx2 : x ≤ 2) (ha : 6 / 5 ≤ a) (hax : a ≤ x)
    (hC0 : 24 / 43 ≤ C) (hC1 : C ≤ 10 / 13) (hu0 : 3 / 4 ≤ u) (hu1 : u ≤ 19 / 25)
    (hM : 2 * lrb2 x C u + 6 * lrb3 x C u / x < -7 / 216) :
    min (lroF1 x x (x + C * (x - 1)) u) (lroF1 x (6 / 5) (x + C * (6 / 5 - 1)) u) ≤
      lroF1 x a (x + C * (a - 1)) u := by
  have hQ := lro_residue_neg (C := C) hx hx2 (by linarith) (by linarith) hu1
  have hx0 : 0 < x := by linarith
  have hb3 := lro_b3_nonpos hx hx2 hC1 (by linarith) hu1
  have hb4 := lrg4_nonpos (u := u) hx0
  have hZ : ∀ a' : ℝ, 6 / 5 ≤ a' → a' ≤ x → 0 < 1 + C + (x - C) * (1 / a') := by
    intro a' h1 h2
    have : 0 < (x - C) * (1 / a') := mul_pos (by linarith) (by positivity)
    linarith
  have hrep : ∀ a' : ℝ, 6 / 5 ≤ a' → a' ≤ x → lroF1 x a' (x + C * (a' - 1)) u =
      lrG (lrb0 x C u) (lrb1 x C u) (lrb2 x C u) (lrb3 x C u) (lrb4 x u) (lrQ1 x C u)
        (1 + C) (x - C) (1 / a') :=
    fun a' h1 h2 => lro_F1_rG hx0 (by linarith) rfl (by linarith) (hZ a' h1 h2)
  rw [hrep a ha hax, hrep x (by linarith) le_rfl, hrep (6 / 5) le_rfl (by linarith)]
  apply lrG_min (one_div_le_one_div_of_le (by linarith) hax)
    (one_div_le_one_div_of_le (by norm_num) ha)
  · intro s hs
    have h1 : 1 / x ≤ s := hs.1
    have hs1 : s ≤ 5 / 6 := by have := hs.2; norm_num at this; exact this
    have hxs : 1 ≤ x * s := by rw [div_le_iff₀ hx0] at h1; linarith
    constructor
    · nlinarith
    · nlinarith
  · intro s hs
    have h1 : 1 / x ≤ s := hs.1
    have hs1 : s ≤ 5 / 6 := by have := hs.2; norm_num at this; exact this
    have hxs : 1 ≤ x * s := by rw [div_le_iff₀ hx0] at h1; linarith
    have hs0 : 1 / 2 ≤ s := by nlinarith
    have he : 0 < x - C := by linarith
    set Z := 1 + C + (x - C) * s with hZdef
    have hZ0 : 0 < Z := by nlinarith
    have hZe : 3 / 2 * (x - C) ≤ Z := by nlinarith
    -- the four contributions
    have t1 : 12 * lrb4 x u * s ^ 2 ≤ 0 := by nlinarith [sq_nonneg s]
    have t2 : 6 * lrb3 x C u * s ≤ 6 * lrb3 x C u / x := by
      have : 6 * lrb3 x C u / x = 6 * lrb3 x C u * (1 / x) := by ring
      rw [this]; nlinarith
    have t3 : 2 * lrQ1 x C u * (x - C) ^ 2 / Z ^ 3 ≤ 0 :=
      div_nonpos_of_nonpos_of_nonneg (by nlinarith [sq_nonneg (x - C)]) (by positivity)
    have t4 : 7 / 96 * (x - C) ^ 2 / Z ^ 2 ≤ 7 / 216 := by
      rw [div_le_iff₀ (by positivity)]
      have : (x - C) ^ 2 ≤ 4 / 9 * Z ^ 2 := by nlinarith
      nlinarith
    nlinarith

/-- **Branch A, `F₁ > 0`.** -/
theorem lro_A_F1 {x a b C u : ℝ} (hx : 3 / 2 ≤ x) (hx2 : x ≤ 2) (ha : 6 / 5 ≤ a) (hax : a ≤ x)
    (hC0 : 24 / 43 ≤ C) (hC1 : C ≤ 10 / 13) (hb : b = x + C * (a - 1)) (hu : ssUf x ≤ u)
    (huv : u ≤ ssVbar x) : 0 < lroF1 x a b u := by
  have hx0 : 0 < x := by linarith
  have ha0 : 0 < a := by linarith
  have hum := lro_um_le hx hx2
  have hup := lro_up_ge hx hx2
  -- the shape signs at a fixed affine norm and slope
  have hshape : ∀ C' u', (C' = 24 / 43 ∨ C' = 10 / 13) →
      (u' = (8 * x + 1303) / 1750 ∨ u' = (6 * x + 443) / 600) →
      0 < lroF1 x a (x + C' * (a - 1)) u' := by
    intro C' u' hC' hu'
    have hu0 : 3 / 4 ≤ u' := by rcases hu' with rfl | rfl <;> linarith
    have hu1 : u' ≤ 19 / 25 := by rcases hu' with rfl | rfl <;> linarith
    have hC0' : 24 / 43 ≤ C' := by rcases hC' with rfl | rfl <;> norm_num
    have hC1' : C' ≤ 10 / 13 := by rcases hC' with rfl | rfl <;> norm_num
    have key : 2 * lrb2 x C' u' + 6 * lrb3 x C' u' / x < -7 / 216 ∧
        0 < lroF1 x x (x + C' * (x - 1)) u' ∧ 0 < lroF1 x (6 / 5) (x + C' * (6 / 5 - 1)) u' := by
      rcases hC' with rfl | rfl <;> rcases hu' with rfl | rfl
      · exact ⟨lro_A_M1_lm hx hx2, lro_A_Tx_lm hx hx2, lro_A_T65_lm hx hx2⟩
      · exact ⟨lro_A_M1_lp hx hx2, lro_A_Tx_lp hx hx2, lro_A_T65_lp hx hx2⟩
      · exact ⟨lro_A_M1_hm hx hx2, lro_A_Tx_hm hx hx2, lro_A_T65_hm hx hx2⟩
      · exact ⟨lro_A_M1_hp hx hx2, lro_A_Tx_hp hx hx2, lro_A_T65_hp hx hx2⟩
    obtain ⟨hM, t1, t2⟩ := key
    have := lro_A_recip hx hx2 ha hax hC0' hC1' hu0 hu1 hM
    exact lt_of_lt_of_le (lt_min t1 t2) this
  -- beta concavity at the two affine norms
  have hbeta : ∀ u', (u' = (8 * x + 1303) / 1750 ∨ u' = (6 * x + 443) / 600) →
      0 < lroF1 x a b u' := by
    intro u' hu'
    have hu1 : u' ≤ (6 * x + 443) / 600 := by rcases hu' with rfl | rfl <;> linarith
    have hw0 := lro_A_w0 (u := u') ha hax hx2 hu1
    have hA : 0 ≤ a - 1 := by linarith
    have hm := lro_F1_bmin (x := x) (a := a) (b1 := x + 24 / 43 * (a - 1)) (b := b)
      (b2 := x + 10 / 13 * (a - 1)) (u := u') hx0 ha0 (by nlinarith)
      (by rw [hb]; nlinarith) (by rw [hb]; nlinarith) (by nlinarith) (by nlinarith)
    exact lt_of_lt_of_le (lt_min (hshape _ _ (Or.inl rfl) hu') (hshape _ _ (Or.inr rfl) hu')) hm
  -- norm concavity
  have hm := lro_F1_umin (x := x) (a := a) (b := b) (hum.trans hu) (huv.trans hup) ha0.ne'
  exact lt_of_lt_of_le (lt_min (hbeta _ (Or.inl rfl)) (hbeta _ (Or.inr rfl))) hm

end SmoothedOctagon
