module

public import SmoothedOctagon.Exclusion.Mixed.FwdHand.LowTCircuit

/-!
# Case M2, forward successor by hand: the low-`t` circuit along `h` at fixed `j`, `y`

The directional derivative `𝓗 = ∂_x - ½∂_t` at fixed `j = x - (1 - 2t)` and `y = q - 1` is the
derivative in `h = 1 - 2t` along `t = (1 - h)/2`, `x = h + j`. Each coefficient `nltStᵢ` of the
circuit is, along this line, the polynomial `lrhHorner (nltLᵢ j)` in `h` (`nlt_St_h`); its
derivatives are given by the derivative coefficient list `nltDer` (`nlt_hasDerivAt_horner`).

## Main API

* `nltDer`, `nlt_der`, `nlt_hasDerivAt_horner`: the derivative of a coefficient list.
* `nltL0`, …, `nltL6`; `nlt_St_h0`, …, `nlt_St_h6`.
-/

@[expose] public section

namespace SmoothedOctagon

/-- The derivative coefficient list with running index `n`: `[n c₀, (n + 1) c₁, …]`. -/
noncomputable def nltDerAux : ℝ → List ℝ → List ℝ
  | _, [] => []
  | n, c :: cs => n * c :: nltDerAux (n + 1) cs

/-- The coefficient list of the derivative of `∑ cₖ sᵏ`. -/
noncomputable def nltDer : List ℝ → List ℝ
  | [] => []
  | _ :: cs => nltDerAux 1 cs

theorem nlt_derAux (n : ℝ) (cs : List ℝ) (s : ℝ) :
    lrhHorner (nltDerAux n cs) s = n * lrhHorner cs s + s * lrhHornerD cs s := by
  induction cs generalizing n with
  | nil => simp [nltDerAux, lrhHorner, lrhHornerD]
  | cons c cs ih => simp only [nltDerAux, lrhHorner, lrhHornerD, ih]; ring

theorem nlt_der (cs : List ℝ) (s : ℝ) : lrhHornerD cs s = lrhHorner (nltDer cs) s := by
  cases cs with
  | nil => simp [nltDer, lrhHorner, lrhHornerD]
  | cons c cs => simp only [nltDer, nlt_derAux, lrhHornerD]; ring

/-- The derivative of `lrhHorner cs` is `lrhHorner (nltDer cs)`. -/
theorem nlt_hasDerivAt_horner (cs : List ℝ) (s : ℝ) :
    HasDerivAt (lrhHorner cs) (lrhHorner (nltDer cs) s) s := by
  rw [← nlt_der]; exact lrh_hasDerivAt_horner cs s

/-- The coefficients in `h` of `nltSt0 ((1 - h)/2) (h + j)`. -/
noncomputable def nltL0 (j : ℝ) : List ℝ :=
  [(-(1210 / 3) * j ^ 2 + (43055 / 3) * j ^ 3 + 9853 * j ^ 4 - 6433 * j ^ 5 - 1428 * j ^ 6 : ℝ), (-(596 / 3) * j + (3707 / 3) * j ^ 2 + (31703 / 3) * j ^ 3 - 23381 * j ^ 4 - 15001 * j ^ 5 - 1428 * j ^ 6 : ℝ), ((614 / 3) - (32375 / 3) * j - 26735 * j ^ 2 - 49210 * j ^ 3 - 39484 * j ^ 4 - 2135 * j ^ 5 + 1428 * j ^ 6 : ℝ), ((6973 / 3) - 16577 * j - 29578 * j ^ 2 - 12999 * j ^ 3 + 26119 * j ^ 4 + 15001 * j ^ 5 + 1428 * j ^ 6 : ℝ), ((32618 / 3) + 27115 * j + 69317 * j ^ 2 + 97573 * j ^ 3 + 53789 * j ^ 4 + 8568 * j ^ 5 : ℝ), (24431 + 86132 * j + 136075 * j ^ 2 + 93706 * j ^ 3 + 21420 * j ^ 4 : ℝ), (29727 + 86014 * j + 86974 * j ^ 2 + 28560 * j ^ 3 : ℝ), (20686 + 41549 * j + 21420 * j ^ 2 : ℝ), (8065 + 8568 * j : ℝ), (1428 : ℝ)]

/-- The coefficients in `h` of `nltSt1 ((1 - h)/2) (h + j)`. -/
noncomputable def nltL1 (j : ℝ) : List ℝ :=
  [(-608 * j + 37166 * j ^ 2 + (176691 / 2) * j ^ 3 + (21315 / 2) * j ^ 4 - (126711 / 2) * j ^ 5 - 24455 * j ^ 6 - 1477 * j ^ 7 : ℝ), (3940 * j + (67253 / 2) * j ^ 2 - (144977 / 2) * j ^ 3 - (513793 / 2) * j ^ 4 - (279107 / 2) * j ^ 5 - 18253 * j ^ 6 - 1428 * j ^ 7 : ℝ), (-4650 - (59327 / 2) * j - (304747 / 2) * j ^ 2 - 339720 * j ^ 3 - 201161 * j ^ 4 + (18881 / 2) * j ^ 5 + 14459 * j ^ 6 + 1477 * j ^ 7 : ℝ), (-(8257 / 2) - (100535 / 2) * j - 115543 * j ^ 2 + (93415 / 2) * j ^ 3 + (477461 / 2) * j ^ 4 + (241783 / 2) * j ^ 5 + 18253 * j ^ 6 + 1428 * j ^ 7 : ℝ), (18960 + (152707 / 2) * j + (629053 / 2) * j ^ 2 + (1088139 / 2) * j ^ 3 + (673565 / 2) * j ^ 4 + 78297 * j ^ 5 + 9996 * j ^ 6 : ℝ), ((91435 / 2) + 235324 * j + (1074017 / 2) * j ^ 2 + 477375 * j ^ 3 + 169385 * j ^ 4 + 29988 * j ^ 5 : ℝ), ((107135 / 2) + 250349 * j + 373472 * j ^ 2 + 207935 * j ^ 3 + 49980 * j ^ 4 : ℝ), (44896 + (308483 / 2) * j + 147687 * j ^ 2 + 49980 * j ^ 3 : ℝ), ((52733 / 2) + 56803 * j + 29988 * j ^ 2 : ℝ), (9187 + 9996 * j : ℝ), (1428 : ℝ)]

/-- The coefficients in `h` of `nltSt2 ((1 - h)/2) (h + j)`. -/
noncomputable def nltL2 (j : ℝ) : List ℝ :=
  [(-(608 / 3) + 22552 * j + (767359 / 6) * j ^ 2 + (811829 / 6) * j ^ 3 - (466189 / 6) * j ^ 4 - (401905 / 2) * j ^ 5 - (245265 / 2) * j ^ 6 - (66449 / 2) * j ^ 7 - 2856 * j ^ 8 : ℝ), (-(23848 / 3) + 23649 * j + (221297 / 3) * j ^ 2 - (373341 / 2) * j ^ 3 - 445820 * j ^ 4 - (585179 / 2) * j ^ 5 - (121591 / 2) * j ^ 6 + 11238 * j ^ 7 + 2856 * j ^ 8 : ℝ), (-(216889 / 6) - (500395 / 6) * j - 199566 * j ^ 2 - (505495 / 2) * j ^ 3 - (30119 / 2) * j ^ 4 + 179703 * j ^ 5 + (262197 / 2) * j ^ 6 + (46625 / 2) * j ^ 7 : ℝ), (-60164 - (991927 / 6) * j - 102739 * j ^ 2 + (607629 / 2) * j ^ 3 + (1022945 / 2) * j ^ 4 + (622989 / 2) * j ^ 5 + (121591 / 2) * j ^ 6 - 1326 * j ^ 7 : ℝ), (-(147631 / 2) - 222357 * j - 81157 * j ^ 2 + (412343 / 2) * j ^ 3 + 197997 * j ^ 4 + (82281 / 2) * j ^ 5 - 8466 * j ^ 6 : ℝ), (-127498 - 406843 * j - (878145 / 2) * j ^ 2 - 254253 * j ^ 3 - (180425 / 2) * j ^ 4 - 22950 * j ^ 5 : ℝ), (-176769 - 481486 * j - (972615 / 2) * j ^ 2 - (424693 / 2) * j ^ 3 - 34170 * j ^ 4 : ℝ), (-(280881 / 2) - (580527 / 2) * j - (373395 / 2) * j ^ 2 - 30090 * j ^ 3 : ℝ), (-61716 - (156949 / 2) * j - 15606 * j ^ 2 : ℝ), (-(26219 / 2) - 4386 * j : ℝ), (-510 : ℝ)]

/-- The coefficients in `h` of `nltSt3 ((1 - h)/2) (h + j)`. -/
noncomputable def nltL3 (j : ℝ) : List ℝ :=
  [((19456 / 3) + 78160 * j + (993160 / 3) * j ^ 2 + 677166 * j ^ 3 + (4922093 / 6) * j ^ 4 + (1114149 / 2) * j ^ 5 + 163676 * j ^ 6 + 8374 * j ^ 7 - 68 * j ^ 8 : ℝ), ((54512 / 3) + (896656 / 3) * j + (3850630 / 3) * j ^ 2 + (15182959 / 6) * j ^ 3 + (4960495 / 2) * j ^ 4 + (2081001 / 2) * j ^ 5 + 126322 * j ^ 6 + 8396 * j ^ 7 + 68 * j ^ 8 : ℝ), (38816 + (2062064 / 3) * j + (4969381 / 2) * j ^ 2 + 3492855 * j ^ 3 + 1693218 * j ^ 4 - (78913 / 2) * j ^ 5 - 107780 * j ^ 6 - 8610 * j ^ 7 : ℝ), ((191860 / 3) + (4244837 / 6) * j + 1342549 * j ^ 2 - (399749 / 2) * j ^ 3 - (3606381 / 2) * j ^ 4 - (1869465 / 2) * j ^ 5 - 126322 * j ^ 6 - 8160 * j ^ 7 : ℝ), (-(202588 / 3) - (1320159 / 2) * j - (5635805 / 2) * j ^ 2 - 4583960 * j ^ 3 - (5488021 / 2) * j ^ 4 - 564986 * j ^ 5 - 55896 * j ^ 6 : ℝ), (-(865893 / 2) - 2483756 * j - 5046278 * j ^ 2 - 4081985 * j ^ 3 - 1236210 * j ^ 4 - 164016 * j ^ 5 : ℝ), (-(1364243 / 2) - (5313683 / 2) * j - 3334297 * j ^ 2 - 1516262 * j ^ 3 - 267240 * j ^ 4 : ℝ), (-(1097475 / 2) - (2862029 / 2) * j - 1069270 * j ^ 2 - 261120 * j ^ 3 : ℝ), (-(506361 / 2) - 406782 * j - 153000 * j ^ 2 : ℝ), (-64906 - 49776 * j : ℝ), (-6936 : ℝ)]

/-- The coefficients in `h` of `nltSt4 ((1 - h)/2) (h + j)`. -/
noncomputable def nltL4 (j : ℝ) : List ℝ :=
  [(-2736 + 2124 * j + 153527 * j ^ 2 + 613681 * j ^ 3 + 1030025 * j ^ 4 + 826983 * j ^ 5 + (595351 / 2) * j ^ 6 + (74733 / 2) * j ^ 7 + 1972 * j ^ 8 : ℝ), (-15508 + 133782 * j + 1234687 * j ^ 2 + 3125855 * j ^ 3 + 3354518 * j ^ 4 + 1506560 * j ^ 5 + (413121 / 2) * j ^ 6 + 806 * j ^ 7 - 1972 * j ^ 8 : ℝ), (17495 + 769205 * j + 3215356 * j ^ 2 + 4614060 * j ^ 3 + (4328319 / 2) * j ^ 4 - (361539 / 2) * j ^ 5 - (489475 / 2) * j ^ 6 - (61045 / 2) * j ^ 7 : ℝ), (132695 + 1199571 * j + 2170014 * j ^ 2 - 175409 * j ^ 3 - (5103075 / 2) * j ^ 4 - 1408639 * j ^ 5 - (413121 / 2) * j ^ 6 - 7650 * j ^ 7 : ℝ), (78677 - 224773 * j - (5853977 / 2) * j ^ 2 - (11175099 / 2) * j ^ 3 - (6959893 / 2) * j ^ 4 - (1410541 / 2) * j ^ 5 - 52938 * j ^ 6 : ℝ), (-308262 - 2417859 * j - (11149659 / 2) * j ^ 2 - 4645924 * j ^ 3 - (2716385 / 2) * j ^ 4 - 156978 * j ^ 5 : ℝ), (-(1243109 / 2) - (5423031 / 2) * j - (7023421 / 2) * j ^ 2 - (3106839 / 2) * j ^ 3 - 258570 * j ^ 4 : ℝ), (-(1045323 / 2) - 1420531 * j - (2102315 / 2) * j ^ 2 - 255510 * j ^ 3 : ℝ), (-(479731 / 2) - (779911 / 2) * j - 151470 * j ^ 2 : ℝ), (-(122571 / 2) - 49878 * j : ℝ), (-7038 : ℝ)]

/-- The coefficients in `h` of `nltSt5 ((1 - h)/2) (h + j)`. -/
noncomputable def nltL5 (j : ℝ) : List ℝ :=
  [(-9728 - 54768 * j - 91564 * j ^ 2 - 8911 * j ^ 3 + (246137 / 2) * j ^ 4 + (236917 / 2) * j ^ 5 + (59173 / 2) * j ^ 6 - 4556 * j ^ 7 - 1088 * j ^ 8 : ℝ), (-43064 - 151630 * j - 17689 * j ^ 2 + (960715 / 2) * j ^ 3 + 652619 * j ^ 4 + (585155 / 2) * j ^ 5 + (70417 / 2) * j ^ 6 + 5816 * j ^ 7 + 1088 * j ^ 8 : ℝ), (-54746 + 12457 * j + (1306615 / 2) * j ^ 2 + (2320325 / 2) * j ^ 3 + (1243679 / 2) * j ^ 4 + (63217 / 2) * j ^ 5 - (30817 / 2) * j ^ 6 + 780 * j ^ 7 : ℝ), (14395 + (722909 / 2) * j + (1627189 / 2) * j ^ 2 + (542475 / 2) * j ^ 3 - (896663 / 2) * j ^ 4 - (533059 / 2) * j ^ 5 - (70417 / 2) * j ^ 6 - 2040 * j ^ 7 : ℝ), (64980 + 163415 * j - 440669 * j ^ 2 - (2502619 / 2) * j ^ 3 - 822718 * j ^ 4 - 166247 * j ^ 5 - 14178 * j ^ 6 : ℝ), (-(48355 / 2) - 493061 * j - 1371658 * j ^ 2 - 1198235 * j ^ 3 - (703935 / 2) * j ^ 4 - 42228 * j ^ 5 : ℝ), (-140003 - 697613 * j - (1879929 / 2) * j ^ 2 - 415942 * j ^ 3 - 69870 * j ^ 4 : ℝ), (-137089 - (770631 / 2) * j - (568895 / 2) * j ^ 2 - 69360 * j ^ 3 : ℝ), (-65085 - 105711 * j - 41310 * j ^ 2 : ℝ), (-(33169 / 2) - 13668 * j : ℝ), (-1938 : ℝ)]

/-- The coefficients in `h` of `nltSt6 ((1 - h)/2) (h + j)`. -/
noncomputable def nltL6 (j : ℝ) : List ℝ :=
  [(-304 - 1892 * j - 4208 * j ^ 2 - 5714 * j ^ 3 - 5344 * j ^ 4 - 3536 * j ^ 5 - 1794 * j ^ 6 - 576 * j ^ 7 - 68 * j ^ 8 : ℝ), (-1436 - 6186 * j - 10586 * j ^ 2 - 10896 * j ^ 3 - 6976 * j ^ 4 - 3050 * j ^ 5 - 612 * j ^ 6 + 236 * j ^ 7 + 68 * j ^ 8 : ℝ), (-1978 - 4486 * j - 3158 * j ^ 2 + 1440 * j ^ 3 + 4052 * j ^ 4 + 3196 * j ^ 5 + 1794 * j ^ 6 + 340 * j ^ 7 : ℝ), (234 + 4962 * j + 11120 * j ^ 2 + 12416 * j ^ 3 + 7316 * j ^ 4 + 3050 * j ^ 5 + 612 * j ^ 6 : ℝ), (2568 + 7848 * j + 9228 * j ^ 2 + 4886 * j ^ 3 + 1292 * j ^ 4 + 340 * j ^ 5 : ℝ), (1608 + 1902 * j - 194 * j ^ 2 - 1520 * j ^ 3 - 340 * j ^ 4 : ℝ), (-218 - 1402 * j - 1862 * j ^ 2 - 612 * j ^ 3 : ℝ), (-406 - 678 * j - 340 * j ^ 2 : ℝ), (-68 - 68 * j : ℝ)]

theorem nlt_St_h0 (h j : ℝ) : nltSt0 ((1 - h) / 2) (h + j) = lrhHorner (nltL0 j) h := by
  simp only [nltL0, lrhHorner]; unfold nltSt0; ring

theorem nlt_St_h1 (h j : ℝ) : nltSt1 ((1 - h) / 2) (h + j) = lrhHorner (nltL1 j) h := by
  simp only [nltL1, lrhHorner]; unfold nltSt1; ring

theorem nlt_St_h2 (h j : ℝ) : nltSt2 ((1 - h) / 2) (h + j) = lrhHorner (nltL2 j) h := by
  simp only [nltL2, lrhHorner]; unfold nltSt2; ring

theorem nlt_St_h3 (h j : ℝ) : nltSt3 ((1 - h) / 2) (h + j) = lrhHorner (nltL3 j) h := by
  simp only [nltL3, lrhHorner]; unfold nltSt3; ring

theorem nlt_St_h4 (h j : ℝ) : nltSt4 ((1 - h) / 2) (h + j) = lrhHorner (nltL4 j) h := by
  simp only [nltL4, lrhHorner]; unfold nltSt4; ring

theorem nlt_St_h5 (h j : ℝ) : nltSt5 ((1 - h) / 2) (h + j) = lrhHorner (nltL5 j) h := by
  simp only [nltL5, lrhHorner]; unfold nltSt5; ring

theorem nlt_St_h6 (h j : ℝ) : nltSt6 ((1 - h) / 2) (h + j) = lrhHorner (nltL6 j) h := by
  simp only [nltL6, lrhHorner]; unfold nltSt6; ring

end SmoothedOctagon
