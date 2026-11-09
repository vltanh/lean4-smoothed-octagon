module

public import SmoothedOctagon.Exclusion.Mixed.Nonshort.Forward.LowT.Horner

/-!
# Case M2, forward successor: the higher `h`-derivatives of the low-`t` circuit

With `𝓗 = ∂_h` at fixed `j`, `y` (`nltDer` of the coefficient lists `nltLᵢ`):

* `𝓗⁴S = ∑ Fᵢ(t, x) yⁱ ≥ 500000` on `1/3 ≤ t ≤ 3/8`, `17/60 ≤ x ≤ 4/7`, `0 ≤ y ≤ 9/32`
  (`nlt_H4_ge`): `F₃, F₄, F₅ ≤ 0 ≤ F₆` and `F₂ + 5Y⁴F₆ ≤ 0` put the sextic in `y` above its chord, and
  both endpoint values exceed `500000`;
* at `h = 1/4` (`t = 3/8`, `x = u`): `P₂ = 𝓗³S = ∑ Rᵢ(u) yⁱ > 0` by the same chord argument
  (`nlt_P2_pos`), and `P₁ = 𝓗²S = ∑ Eᵢ(u) yⁱ > 0` by the unimodal bound `nlt_unimodal`
  (`E₄ > 120000`, `E₅ > -70000`, `E₆ > -1300` make `∂_y⁴P₁ > 0`; `E₂ < 0`; `∂_yP₁(9/32) < 0`)
  (`nlt_P1_pos`), for `17/60 ≤ u ≤ 41/84`, `0 ≤ y ≤ 9/32`.

The coefficient signs in `(t, x)` compare each monomial in `t` with its value at `t = 1/3` or
`t = 3/8` (`nlt_lo`, `nlt_hi`) and then use a termwise monomial bound in `x` after a shift; the
chord condition is `F₂ + 5Y⁴F₆ ≤ 0` (`Y = 9/32`); `P₂ > 0` is proved only at `t = 3/8`, where it is
used.

## Main API

* `nltF0`, …, `nltF6`, `nlt_F_eq0`, …; `nlt_H4_ge`.
* `nltE0`, …, `nltR6`, `nlt_E_eq0`, …, `nlt_R_eq0`, …; `nlt_P1_pos`, `nlt_P2_pos`.
-/

@[expose] public section

namespace SmoothedOctagon

/-- `F_0`: the `y^0`-coefficient of `𝓗⁴S`. -/
noncomputable def nltF0 (t x : ℝ) : ℝ :=
  4974736 + 13841976 * x - 15109728 * t + 16803528 * x ^ 2 - 40448208 * t * x + 13016832 * t ^ 2 + 10479048 * x ^ 3 - 42980352 * t * x ^ 2 + 31532736 * t ^ 2 * x - 3344256 * t ^ 3 + 2833176 * x ^ 4 - 20387232 * t * x ^ 3 + 27457344 * t ^ 2 * x ^ 2 - 6802368 * t ^ 3 * x + 78336 * t ^ 4 + 205632 * x ^ 5 - 3084480 * t * x ^ 4 + 8225280 * t ^ 2 * x ^ 3 - 4112640 * t ^ 3 * x ^ 2

theorem nlt_F_eq0 (j s : ℝ) : polyHorner (nltDer (nltDer (nltDer (nltDer (nltL0 j))))) s = nltF0 ((1 - s) / 2) (s + j) := by
  simp only [nltL0, nltDer, nltDerAux, polyHorner]; unfold nltF0; ring

/-- `F_1`: the `y^1`-coefficient of `𝓗⁴S`. -/
noncomputable def nltF1 (t x : ℝ) : ℝ :=
  1653624 + 15553116 * x + 4649952 * t + 46561452 * x ^ 2 - 28875192 * t * x - 18446112 * t ^ 2 + 51554148 * x ^ 3 - 110821632 * t * x ^ 2 + 3321696 * t ^ 2 * x + 8859264 * t ^ 3 + 22611900 * x ^ 4 - 106477200 * t * x ^ 3 + 76204800 * t ^ 2 * x ^ 2 - 711840 * t ^ 3 * x - 311040 * t ^ 4 + 4038264 * x ^ 5 - 36255360 * t * x ^ 4 + 63766560 * t ^ 2 * x ^ 3 - 21225600 * t ^ 3 * x ^ 2 - 391680 * t ^ 4 * x + 239904 * x ^ 6 - 4318272 * t * x ^ 5 + 14394240 * t ^ 2 * x ^ 4 - 9596160 * t ^ 3 * x ^ 3

theorem nlt_F_eq1 (j s : ℝ) : polyHorner (nltDer (nltDer (nltDer (nltDer (nltL1 j))))) s = nltF1 ((1 - s) / 2) (s + j) := by
  simp only [nltL1, nltDer, nltDerAux, polyHorner]; unfold nltF1; ring

/-- `F_2`: the `y^2`-coefficient of `𝓗⁴S`. -/
noncomputable def nltF2 (t x : ℝ) : ℝ :=
  -30440040 - 106874856 * x + 97971048 * t - 126533508 * x ^ 2 + 321862248 * t * x - 86395152 * t ^ 2 - 67386096 * x ^ 3 + 366738624 * t * x ^ 2 - 245814912 * t ^ 2 * x + 7613472 * t ^ 3 - 12589392 * x ^ 4 + 189394944 * t * x ^ 3 - 240882768 * t ^ 2 * x ^ 2 + 10732896 * t ^ 3 * x + 5280768 * t ^ 4 - 547524 * x ^ 5 + 37840560 * t * x ^ 4 - 87641520 * t ^ 2 * x ^ 3 + 9146880 * t ^ 3 * x ^ 2 + 11508480 * t ^ 4 * x - 203184 * x ^ 6 + 3069792 * t * x ^ 5 - 6315840 * t ^ 2 * x ^ 4 - 3623040 * t ^ 3 * x ^ 3 + 4700160 * t ^ 4 * x ^ 2

theorem nlt_F_eq2 (j s : ℝ) : polyHorner (nltDer (nltDer (nltDer (nltDer (nltL2 j))))) s = nltF2 ((1 - s) / 2) (s + j) := by
  simp only [nltL2, nltDer, nltDerAux, polyHorner]; unfold nltF2; ring

/-- `F_3`: the `y^3`-coefficient of `𝓗⁴S`. -/
noncomputable def nltF3 (t x : ℝ) : ℝ :=
  -52545968 - 260483220 * x + 130131600 * t - 483765492 * x ^ 2 + 663880872 * t * x - 52494048 * t ^ 2 - 429002712 * x ^ 3 + 1141961088 * t * x ^ 2 - 366995904 * t ^ 2 * x - 10887936 * t ^ 3 - 164322492 * x ^ 4 + 832132944 * t * x ^ 3 - 674484768 * t ^ 2 * x ^ 2 + 27603936 * t ^ 3 * x + 5503488 * t ^ 4 - 25192560 * x ^ 5 + 232771200 * t * x ^ 4 - 406332480 * t ^ 2 * x ^ 3 + 106686720 * t ^ 3 * x ^ 2 + 15989760 * t ^ 4 * x - 1341504 * x ^ 6 + 23265792 * t * x ^ 5 - 71677440 * t ^ 2 * x ^ 4 + 36034560 * t ^ 3 * x ^ 3 + 7050240 * t ^ 4 * x ^ 2

theorem nlt_F_eq3 (j s : ℝ) : polyHorner (nltDer (nltDer (nltDer (nltDer (nltL3 j))))) s = nltF3 ((1 - s) / 2) (s + j) := by
  simp only [nltL3, nltDer, nltDerAux, polyHorner]; unfold nltF3; ring

/-- `F_4`: the `y^4`-coefficient of `𝓗⁴S`. -/
noncomputable def nltF4 (t x : ℝ) : ℝ :=
  -31292952 - 198378264 * x + 64874352 * t - 443411736 * x ^ 2 + 477479136 * t * x + 12482976 * t ^ 2 - 439351704 * x ^ 3 + 986248656 * t * x ^ 2 - 190997568 * t ^ 2 * x - 19400832 * t ^ 3 - 179825436 * x ^ 4 + 784631952 * t * x ^ 3 - 532849104 * t ^ 2 * x ^ 2 + 12538368 * t ^ 3 * x + 774144 * t ^ 4 - 28140780 * x ^ 5 + 228525600 * t * x ^ 4 - 369265680 * t ^ 2 * x ^ 3 + 104253120 * t ^ 3 * x ^ 2 + 6819840 * t ^ 4 * x - 1270512 * x ^ 6 + 22428576 * t * x ^ 5 - 71824320 * t ^ 2 * x ^ 4 + 42007680 * t ^ 3 * x ^ 3 + 3525120 * t ^ 4 * x ^ 2

theorem nlt_F_eq4 (j s : ℝ) : polyHorner (nltDer (nltDer (nltDer (nltDer (nltL4 j))))) s = nltF4 ((1 - s) / 2) (s + j) := by
  simp only [nltL4, nltDer, nltDerAux, polyHorner]; unfold nltF4; ring

/-- `F_5`: the `y^5`-coefficient of `𝓗⁴S`. -/
noncomputable def nltF5 (t x : ℝ) : ℝ :=
  -5677200 - 45349824 * x + 12551712 * t - 113773884 * x ^ 2 + 119386344 * t * x + 9252624 * t ^ 2 - 117050460 * x ^ 3 + 270106800 * t * x ^ 2 - 38125920 * t ^ 2 * x - 10642080 * t ^ 3 - 46952172 * x ^ 4 + 221497104 * t * x ^ 3 - 139925088 * t ^ 2 * x ^ 2 - 7557024 * t ^ 3 * x - 352512 * t ^ 4 - 7015656 * x ^ 5 + 64254840 * t * x ^ 4 - 100989120 * t ^ 2 * x ^ 3 + 24711840 * t ^ 3 * x ^ 2 + 875520 * t ^ 4 * x - 340272 * x ^ 6 + 6051456 * t * x ^ 5 - 19681920 * t ^ 2 * x ^ 4 + 12142080 * t ^ 3 * x ^ 3 + 587520 * t ^ 4 * x ^ 2

theorem nlt_F_eq5 (j s : ℝ) : polyHorner (nltDer (nltDer (nltDer (nltDer (nltL5 j))))) s = nltF5 ((1 - s) / 2) (s + j) := by
  simp only [nltL5, nltDer, nltDerAux, polyHorner]; unfold nltF5; ring

/-- `F_6`: the `y^6`-coefficient of `𝓗⁴S`. -/
noncomputable def nltF6 (t x : ℝ) : ℝ :=
  2496 - 32832 * x + 206016 * t - 41712 * x ^ 2 + 255552 * t * x - 102528 * t ^ 2 - 164688 * x ^ 3 + 204672 * t * x ^ 2 + 773184 * t ^ 2 * x - 132864 * t ^ 3 - 50592 * x ^ 4 + 514944 * t * x ^ 3 + 839232 * t ^ 2 * x ^ 2 - 799104 * t ^ 3 * x - 26112 * t ^ 4 + 8160 * x ^ 5 + 163200 * t * x ^ 4 + 97920 * t ^ 2 * x ^ 3 - 391680 * t ^ 3 * x ^ 2

theorem nlt_F_eq6 (j s : ℝ) : polyHorner (nltDer (nltDer (nltDer (nltDer (nltL6 j))))) s = nltF6 ((1 - s) / 2) (s + j) := by
  simp only [nltL6, nltDer, nltDerAux, polyHorner]; unfold nltF6; ring

/-- `E_0`: the `y^0`-coefficient of `𝓗²S` at `h = 1/4`. -/
noncomputable def nltE0 (x : ℝ) : ℝ :=
  (129817 / 6) + (2519527 / 384) * x + (255743 / 16) * x ^ 2 - (88091 / 16) * x ^ 3 - (75561 / 4) * x ^ 4 + (34321 / 2) * x ^ 5 + 4998 * x ^ 6

theorem nlt_E_eq0 (j : ℝ) : polyHorner (nltDer (nltDer (nltL0 j))) (1 / 4) = nltE0 (j + 1 / 4) := by
  simp only [nltL0, nltDer, nltDerAux, polyHorner]; unfold nltE0; ring

/-- `E_1`: the `y^1`-coefficient of `𝓗²S` at `h = 1/4`. -/
noncomputable def nltE1 (x : ℝ) : ℝ :=
  (209393 / 16) + (7161165 / 256) * x + (1826257 / 32) * x ^ 2 - (4621567 / 32) * x ^ 3 - (89755 / 8) * x ^ 4 + 179309 * x ^ 5 + (109753 / 2) * x ^ 6 + 5096 * x ^ 7

theorem nlt_E_eq1 (j : ℝ) : polyHorner (nltDer (nltDer (nltL1 j))) (1 / 4) = nltE1 (j + 1 / 4) := by
  simp only [nltL1, nltDer, nltDerAux, polyHorner]; unfold nltE1; ring

/-- `E_2`: the `y^2`-coefficient of `𝓗²S` at `h = 1/4`. -/
noncomputable def nltE2 (x : ℝ) : ℝ :=
  -(4448395 / 32) - (78497143 / 192) * x - (19490043 / 32) * x ^ 2 - (3399997 / 8) * x ^ 3 + (731345 / 8) * x ^ 4 + (3106839 / 8) * x ^ 5 + (1075711 / 4) * x ^ 6 + 44636 * x ^ 7

theorem nlt_E_eq2 (j : ℝ) : polyHorner (nltDer (nltDer (nltL2 j))) (1 / 4) = nltE2 (j + 1 / 4) := by
  simp only [nltL2, nltDer, nltDerAux, polyHorner]; unfold nltE2; ring

/-- `E_3`: the `y^3`-coefficient of `𝓗²S` at `h = 1/4`. -/
noncomputable def nltE3 (x : ℝ) : ℝ :=
  -(16355135 / 96) - (87639991 / 384) * x + (9003923 / 8) * x ^ 2 + (79713483 / 32) * x ^ 3 + (1984789 / 8) * x ^ 4 - 1324225 * x ^ 5 - 395410 * x ^ 6 - 29460 * x ^ 7

theorem nlt_E_eq3 (j : ℝ) : polyHorner (nltDer (nltDer (nltL3 j))) (1 / 4) = nltE3 (j + 1 / 4) := by
  simp only [nltL3, nltDer, nltDerAux, polyHorner]; unfold nltE3; ring

/-- `E_4`: the `y^4`-coefficient of `𝓗²S` at `h = 1/4`. -/
noncomputable def nltE4 (x : ℝ) : ℝ :=
  -(269093 / 2) + (10046253 / 128) * x + (19296511 / 8) * x ^ 2 + (16152471 / 4) * x ^ 3 + (4040223 / 8) * x ^ 4 - (15113277 / 8) * x ^ 5 - (2848437 / 4) * x ^ 6 - 72520 * x ^ 7

theorem nlt_E_eq4 (j : ℝ) : polyHorner (nltDer (nltDer (nltL4 j))) (1 / 4) = nltE4 (j + 1 / 4) := by
  simp only [nltL4, nltDer, nltDerAux, polyHorner]; unfold nltE4; ring

/-- `E_5`: the `y^5`-coefficient of `𝓗²S` at `h = 1/4`. -/
noncomputable def nltE5 (x : ℝ) : ℝ :=
  -(6239549 / 64) - (33072663 / 256) * x + 630610 * x ^ 2 + (40301203 / 32) * x ^ 3 + (10927599 / 32) * x ^ 4 - (2680261 / 8) * x ^ 5 - (366553 / 4) * x ^ 6 - 1500 * x ^ 7

theorem nlt_E_eq5 (j : ℝ) : polyHorner (nltDer (nltDer (nltL5 j))) (1 / 4) = nltE5 (j + 1 / 4) := by
  simp only [nltL5, nltDer, nltDerAux, polyHorner]; unfold nltE5; ring

/-- `E_6`: the `y^6`-coefficient of `𝓗²S` at `h = 1/4`. -/
noncomputable def nltE6 (x : ℝ) : ℝ :=
  -(106491 / 64) - (11107 / 64) * x + (72005 / 16) * x ^ 2 + (83037 / 8) * x ^ 3 + (39063 / 4) * x ^ 4 + (10711 / 2) * x ^ 5 + 3316 * x ^ 6 + 680 * x ^ 7

theorem nlt_E_eq6 (j : ℝ) : polyHorner (nltDer (nltDer (nltL6 j))) (1 / 4) = nltE6 (j + 1 / 4) := by
  simp only [nltL6, nltDer, nltDerAux, polyHorner]; unfold nltE6; ring

/-- `R_0(3/8, x)`: the `y^0`-coefficient of `𝓗³S` at `h = 1/4`. -/
noncomputable def nltR0 (x : ℝ) : ℝ :=
  (18701901 / 128) + (2068095 / 8) * x + (6934239 / 16) * x ^ 2 + (1753299 / 4) * x ^ 3 + 391038 * x ^ 4 + 128562 * x ^ 5 + 8568 * x ^ 6

theorem nlt_R_eq0 (j : ℝ) : polyHorner (nltDer (nltDer (nltDer (nltL0 j)))) (1 / 4) = nltR0 (j + 1 / 4) := by
  simp only [nltL0, nltDer, nltDerAux, polyHorner]; unfold nltR0; ring

/-- `R_1(3/8, x)`: the `y^1`-coefficient of `𝓗³S` at `h = 1/4`. -/
noncomputable def nltR1 (x : ℝ) : ℝ :=
  (43850541 / 256) + (7673091 / 16) * x + (34827195 / 32) * x ^ 2 + (18793257 / 8) * x ^ 3 + (10806867 / 4) * x ^ 4 + (2129181 / 2) * x ^ 5 + 154500 * x ^ 6 + 8568 * x ^ 7

theorem nlt_R_eq1 (j : ℝ) : polyHorner (nltDer (nltDer (nltDer (nltL1 j)))) (1 / 4) = nltR1 (j + 1 / 4) := by
  simp only [nltL1, nltDer, nltDerAux, polyHorner]; unfold nltR1; ring

/-- `R_2(3/8, x)`: the `y^2`-coefficient of `𝓗³S` at `h = 1/4`. -/
noncomputable def nltR2 (x : ℝ) : ℝ :=
  -(47853089 / 64) - (11985385 / 4) * x - (15743559 / 4) * x ^ 2 - (8011443 / 8) * x ^ 3 + (12927771 / 8) * x ^ 4 + (6193359 / 4) * x ^ 5 + 327900 * x ^ 6 - 7956 * x ^ 7

theorem nlt_R_eq2 (j : ℝ) : polyHorner (nltDer (nltDer (nltDer (nltL2 j)))) (1 / 4) = nltR2 (j + 1 / 4) := by
  simp only [nltL2, nltDer, nltDerAux, polyHorner]; unfold nltR2; ring

/-- `R_3(3/8, x)`: the `y^3`-coefficient of `𝓗³S` at `h = 1/4`. -/
noncomputable def nltR3 (x : ℝ) : ℝ :=
  -(153734461 / 128) - (77243917 / 16) * x - (331922271 / 32) * x ^ 2 - (162567723 / 8) * x ^ 3 - 21401556 * x ^ 4 - 8037669 * x ^ 5 - 1007628 * x ^ 6 - 48960 * x ^ 7

theorem nlt_R_eq3 (j : ℝ) : polyHorner (nltDer (nltDer (nltDer (nltL3 j)))) (1 / 4) = nltR3 (j + 1 / 4) := by
  simp only [nltL3, nltDer, nltDerAux, polyHorner]; unfold nltR3; ring

/-- `R_4(3/8, x)`: the `y^4`-coefficient of `𝓗³S` at `h = 1/4`. -/
noncomputable def nltR4 (x : ℝ) : ℝ :=
  -(66090579 / 128) - (4419435 / 4) * x - (21125391 / 4) * x ^ 2 - (42340149 / 2) * x ^ 3 - (53222733 / 2) * x ^ 4 - (43987527 / 4) * x ^ 5 - 1476666 * x ^ 6 - 45900 * x ^ 7

theorem nlt_R_eq4 (j : ℝ) : polyHorner (nltDer (nltDer (nltDer (nltL4 j)))) (1 / 4) = nltR4 (j + 1 / 4) := by
  simp only [nltL4, nltDer, nltDerAux, polyHorner]; unfold nltR4; ring

/-- `R_5(3/8, x)`: the `y^5`-coefficient of `𝓗³S` at `h = 1/4`. -/
noncomputable def nltR5 (x : ℝ) : ℝ :=
  -(22449111 / 256) + (4086027 / 8) * x + (16060125 / 32) * x ^ 2 - (7528755 / 2) * x ^ 3 - (94472307 / 16) * x ^ 4 - (4653201 / 2) * x ^ 5 - 274899 * x ^ 6 - 12240 * x ^ 7

theorem nlt_R_eq5 (j : ℝ) : polyHorner (nltDer (nltDer (nltDer (nltL5 j)))) (1 / 4) = nltR5 (j + 1 / 4) := by
  simp only [nltL5, nltDer, nltDerAux, polyHorner]; unfold nltR5; ring

/-- `R_6(3/8, x)`: the `y^6`-coefficient of `𝓗³S` at `h = 1/4`. -/
noncomputable def nltR6 (x : ℝ) : ℝ :=
  (505197 / 64) + (299187 / 8) * x + (486351 / 8) * x ^ 2 + (116313 / 2) * x ^ 3 + (56781 / 2) * x ^ 4 + 14832 * x ^ 5 + 3672 * x ^ 6

theorem nlt_R_eq6 (j : ℝ) : polyHorner (nltDer (nltDer (nltDer (nltL6 j)))) (1 / 4) = nltR6 (j + 1 / 4) := by
  simp only [nltL6, nltDer, nltDerAux, polyHorner]; unfold nltR6; ring

/-- A coefficient combination of `𝓗⁴S`: `-F₃`. -/
noncomputable def nltFc3 (t x : ℝ) : ℝ := -nltF3 t x

/-- The univariate lower polynomial of `nltFc3 t x` (monomial comparison in `t`). -/
noncomputable def nltFc3_posQ (x : ℝ) : ℝ :=
  (710907355 / 72) + (2425600109 / 48) * x + (498829429 / 4) * x ^ 2 + (480601954 / 3) * x ^ 3 + 84997452 * x ^ 4 + 16467888 * x ^ 5 + 1341504 * x ^ 6

/-- The univariate bound for `nltFc3_pos`. -/
theorem nltFc3_posQ_pos {x : ℝ} (h1 : (17 / 60) ≤ x) (h2 : x ≤ (4 / 7)) : 0 < nltFc3_posQ x := by
  obtain ⟨z, rfl⟩ : ∃ z, x = (17 / 60) + z := ⟨x - (17 / 60), by ring⟩
  have z0 : 0 ≤ z := by linarith
  have z1 : z ≤ (121 / 420) := by linarith
  have p2 : z ^ 2 ≤ (121 / 420) * z ^ 1 := nlt_pw z0 z1 1
  have q2 : 0 ≤ z ^ 2 := pow_nonneg z0 2
  have p3 : z ^ 3 ≤ (121 / 420) * z ^ 2 := nlt_pw z0 z1 2
  have q3 : 0 ≤ z ^ 3 := pow_nonneg z0 3
  have p4 : z ^ 4 ≤ (121 / 420) * z ^ 3 := nlt_pw z0 z1 3
  have q4 : 0 ≤ z ^ 4 := pow_nonneg z0 4
  have p5 : z ^ 5 ≤ (121 / 420) * z ^ 4 := nlt_pw z0 z1 4
  have q5 : 0 ≤ z ^ 5 := pow_nonneg z0 5
  have p6 : z ^ 6 ≤ (121 / 420) * z ^ 5 := nlt_pw z0 z1 5
  have q6 : 0 ≤ z ^ 6 := pow_nonneg z0 6
  have e : nltFc3_posQ ((17 / 60) + z) = (1037477046460787 / 27000000) + (56720595738817 / 337500) * z + (687810853471 / 2250) * z ^ 2 + (20277105868 / 75) * z ^ 3 + (549711772 / 5) * z ^ 4 + (93742224 / 5) * z ^ 5 + 1341504 * z ^ 6 := by unfold nltFc3_posQ; ring
  rw [e]; linarith only [z0, z1, p2, q2, p3, q3, p4, q4, p5, q5, p6, q6]

/-- A coefficient sign of `𝓗⁴S` on the box `[1/3, 3/8] × [17/60, 4/7]`. -/
theorem nltFc3_pos {t x : ℝ} (ht0 : (1 / 3) ≤ t) (ht1 : t ≤ (3 / 8)) (hx0 : (17 / 60) ≤ x) (hx1 : x ≤ (4 / 7)) :
    0 < nltFc3 t x := by
  have hx : (0 : ℝ) ≤ x := by linarith
  have ht : (0 : ℝ) ≤ t := by linarith
  have hq := nltFc3_posQ_pos hx0 hx1
  have m0 := nlt_hi 4 2 (by norm_num : ((3 / 8) : ℝ) ^ 4 = (81 / 4096)) ht ht1 hx
  have m1 := nlt_hi 4 1 (by norm_num : ((3 / 8) : ℝ) ^ 4 = (81 / 4096)) ht ht1 hx
  have m2 := nlt_hi 4 0 (by norm_num : ((3 / 8) : ℝ) ^ 4 = (81 / 4096)) ht ht1 hx
  have m3 := nlt_hi 3 3 (by norm_num : ((3 / 8) : ℝ) ^ 3 = (27 / 512)) ht ht1 hx
  have m4 := nlt_hi 3 2 (by norm_num : ((3 / 8) : ℝ) ^ 3 = (27 / 512)) ht ht1 hx
  have m5 := nlt_hi 3 1 (by norm_num : ((3 / 8) : ℝ) ^ 3 = (27 / 512)) ht ht1 hx
  have m6 := nlt_lo 3 0 (by norm_num : ((1 / 3) : ℝ) ^ 3 = (1 / 27)) (by norm_num) ht0 hx
  have m7 := nlt_lo 2 4 (by norm_num : ((1 / 3) : ℝ) ^ 2 = (1 / 9)) (by norm_num) ht0 hx
  have m8 := nlt_lo 2 3 (by norm_num : ((1 / 3) : ℝ) ^ 2 = (1 / 9)) (by norm_num) ht0 hx
  have m9 := nlt_lo 2 2 (by norm_num : ((1 / 3) : ℝ) ^ 2 = (1 / 9)) (by norm_num) ht0 hx
  have m10 := nlt_lo 2 1 (by norm_num : ((1 / 3) : ℝ) ^ 2 = (1 / 9)) (by norm_num) ht0 hx
  have m11 := nlt_lo 2 0 (by norm_num : ((1 / 3) : ℝ) ^ 2 = (1 / 9)) (by norm_num) ht0 hx
  have m12 := nlt_hi 1 5 (by norm_num : ((3 / 8) : ℝ) ^ 1 = (3 / 8)) ht ht1 hx
  have m13 := nlt_hi 1 4 (by norm_num : ((3 / 8) : ℝ) ^ 1 = (3 / 8)) ht ht1 hx
  have m14 := nlt_hi 1 3 (by norm_num : ((3 / 8) : ℝ) ^ 1 = (3 / 8)) ht ht1 hx
  have m15 := nlt_hi 1 2 (by norm_num : ((3 / 8) : ℝ) ^ 1 = (3 / 8)) ht ht1 hx
  have m16 := nlt_hi 1 1 (by norm_num : ((3 / 8) : ℝ) ^ 1 = (3 / 8)) ht ht1 hx
  have m17 := nlt_hi 1 0 (by norm_num : ((3 / 8) : ℝ) ^ 1 = (3 / 8)) ht ht1 hx
  unfold nltFc3 nltF3 nltFc3_posQ at *
  linarith

/-- A coefficient combination of `𝓗⁴S`: `-F₄`. -/
noncomputable def nltFc4 (t x : ℝ) : ℝ := -nltF4 t x

/-- The univariate lower polynomial of `nltFc4 t x` (monomial comparison in `t`). -/
noncomputable def nltFc4_posQ (x : ℝ) : ℝ :=
  (35477351 / 6) + 39749472 * x + (508826049 / 4) * x ^ 2 + (735715973 / 4) * x ^ 3 + 102108816 * x ^ 4 + 19730064 * x ^ 5 + 1270512 * x ^ 6

/-- The univariate bound for `nltFc4_pos`. -/
theorem nltFc4_posQ_pos {x : ℝ} (h1 : (17 / 60) ≤ x) (h2 : x ≤ (4 / 7)) : 0 < nltFc4_posQ x := by
  obtain ⟨z, rfl⟩ : ∃ z, x = (17 / 60) + z := ⟨x - (17 / 60), by ring⟩
  have z0 : 0 ≤ z := by linarith
  have z1 : z ≤ (121 / 420) := by linarith
  have p2 : z ^ 2 ≤ (121 / 420) * z ^ 1 := nlt_pw z0 z1 1
  have q2 : 0 ≤ z ^ 2 := pow_nonneg z0 2
  have p3 : z ^ 3 ≤ (121 / 420) * z ^ 2 := nlt_pw z0 z1 2
  have q3 : 0 ≤ z ^ 3 := pow_nonneg z0 3
  have p4 : z ^ 4 ≤ (121 / 420) * z ^ 3 := nlt_pw z0 z1 3
  have q4 : 0 ≤ z ^ 4 := pow_nonneg z0 4
  have p5 : z ^ 5 ≤ (121 / 420) * z ^ 4 := nlt_pw z0 z1 4
  have q5 : 0 ≤ z ^ 5 := pow_nonneg z0 5
  have p6 : z ^ 6 ≤ (121 / 420) * z ^ 5 := nlt_pw z0 z1 5
  have q6 : 0 ≤ z ^ 6 := pow_nonneg z0 6
  have e : nltFc4_posQ ((17 / 60) + z) = (5226987877447541 / 162000000) + (896773029937591 / 5400000) * z + (3036051569827 / 9000) * z ^ 2 + (94820742091 / 300) * z ^ 3 + (657948241 / 5) * z ^ 4 + (109449672 / 5) * z ^ 5 + 1270512 * z ^ 6 := by unfold nltFc4_posQ; ring
  rw [e]; linarith only [z0, z1, p2, q2, p3, q3, p4, q4, p5, q5, p6, q6]

/-- A coefficient sign of `𝓗⁴S` on the box `[1/3, 3/8] × [17/60, 4/7]`. -/
theorem nltFc4_pos {t x : ℝ} (ht0 : (1 / 3) ≤ t) (ht1 : t ≤ (3 / 8)) (hx0 : (17 / 60) ≤ x) (hx1 : x ≤ (4 / 7)) :
    0 < nltFc4 t x := by
  have hx : (0 : ℝ) ≤ x := by linarith
  have ht : (0 : ℝ) ≤ t := by linarith
  have hq := nltFc4_posQ_pos hx0 hx1
  have m0 := nlt_hi 4 2 (by norm_num : ((3 / 8) : ℝ) ^ 4 = (81 / 4096)) ht ht1 hx
  have m1 := nlt_hi 4 1 (by norm_num : ((3 / 8) : ℝ) ^ 4 = (81 / 4096)) ht ht1 hx
  have m2 := nlt_hi 4 0 (by norm_num : ((3 / 8) : ℝ) ^ 4 = (81 / 4096)) ht ht1 hx
  have m3 := nlt_hi 3 3 (by norm_num : ((3 / 8) : ℝ) ^ 3 = (27 / 512)) ht ht1 hx
  have m4 := nlt_hi 3 2 (by norm_num : ((3 / 8) : ℝ) ^ 3 = (27 / 512)) ht ht1 hx
  have m5 := nlt_hi 3 1 (by norm_num : ((3 / 8) : ℝ) ^ 3 = (27 / 512)) ht ht1 hx
  have m6 := nlt_lo 3 0 (by norm_num : ((1 / 3) : ℝ) ^ 3 = (1 / 27)) (by norm_num) ht0 hx
  have m7 := nlt_lo 2 4 (by norm_num : ((1 / 3) : ℝ) ^ 2 = (1 / 9)) (by norm_num) ht0 hx
  have m8 := nlt_lo 2 3 (by norm_num : ((1 / 3) : ℝ) ^ 2 = (1 / 9)) (by norm_num) ht0 hx
  have m9 := nlt_lo 2 2 (by norm_num : ((1 / 3) : ℝ) ^ 2 = (1 / 9)) (by norm_num) ht0 hx
  have m10 := nlt_lo 2 1 (by norm_num : ((1 / 3) : ℝ) ^ 2 = (1 / 9)) (by norm_num) ht0 hx
  have m11 := nlt_hi 2 0 (by norm_num : ((3 / 8) : ℝ) ^ 2 = (9 / 64)) ht ht1 hx
  have m12 := nlt_hi 1 5 (by norm_num : ((3 / 8) : ℝ) ^ 1 = (3 / 8)) ht ht1 hx
  have m13 := nlt_hi 1 4 (by norm_num : ((3 / 8) : ℝ) ^ 1 = (3 / 8)) ht ht1 hx
  have m14 := nlt_hi 1 3 (by norm_num : ((3 / 8) : ℝ) ^ 1 = (3 / 8)) ht ht1 hx
  have m15 := nlt_hi 1 2 (by norm_num : ((3 / 8) : ℝ) ^ 1 = (3 / 8)) ht ht1 hx
  have m16 := nlt_hi 1 1 (by norm_num : ((3 / 8) : ℝ) ^ 1 = (3 / 8)) ht ht1 hx
  have m17 := nlt_hi 1 0 (by norm_num : ((3 / 8) : ℝ) ^ 1 = (3 / 8)) ht ht1 hx
  unfold nltFc4 nltF4 nltFc4_posQ at *
  linarith

/-- A coefficient combination of `𝓗⁴S`: `-F₅`. -/
noncomputable def nltFc5 (t x : ℝ) : ℝ := -nltF5 t x

/-- The univariate lower polynomial of `nltFc5 t x` (monomial comparison in `t`). -/
noncomputable def nltFc5_posQ (x : ℝ) : ℝ :=
  (2435791 / 36) + (182834437 / 36) * x + (213730273 / 8) * x ^ 2 + (133709263 / 3) * x ^ 3 + 25043487 * x ^ 4 + 4746360 * x ^ 5 + 340272 * x ^ 6

/-- The univariate bound for `nltFc5_pos`. -/
theorem nltFc5_posQ_pos {x : ℝ} (h1 : (17 / 60) ≤ x) (h2 : x ≤ (4 / 7)) : 0 < nltFc5_posQ x := by
  obtain ⟨z, rfl⟩ : ∃ z, x = (17 / 60) + z := ⟨x - (17 / 60), by ring⟩
  have z0 : 0 ≤ z := by linarith
  have z1 : z ≤ (121 / 420) := by linarith
  have p2 : z ^ 2 ≤ (121 / 420) * z ^ 1 := nlt_pw z0 z1 1
  have q2 : 0 ≤ z ^ 2 := pow_nonneg z0 2
  have p3 : z ^ 3 ≤ (121 / 420) * z ^ 2 := nlt_pw z0 z1 2
  have q3 : 0 ≤ z ^ 3 := pow_nonneg z0 3
  have p4 : z ^ 4 ≤ (121 / 420) * z ^ 3 := nlt_pw z0 z1 3
  have q4 : 0 ≤ z ^ 4 := pow_nonneg z0 4
  have p5 : z ^ 5 ≤ (121 / 420) * z ^ 4 := nlt_pw z0 z1 4
  have q5 : 0 ≤ z ^ 5 := pow_nonneg z0 5
  have p6 : z ^ 6 ≤ (121 / 420) * z ^ 5 := nlt_pw z0 z1 5
  have q6 : 0 ≤ z ^ 6 := pow_nonneg z0 6
  have e : nltFc5_posQ ((17 / 60) + z) = (783326866107761 / 162000000) + (11268114556681 / 337500) * z + (1399961857109 / 18000) * z ^ 2 + (1922935938 / 25) * z ^ 3 + (160886206 / 5) * z ^ 4 + (26624112 / 5) * z ^ 5 + 340272 * z ^ 6 := by unfold nltFc5_posQ; ring
  rw [e]; linarith only [z0, z1, p2, q2, p3, q3, p4, q4, p5, q5, p6, q6]

/-- A coefficient sign of `𝓗⁴S` on the box `[1/3, 3/8] × [17/60, 4/7]`. -/
theorem nltFc5_pos {t x : ℝ} (ht0 : (1 / 3) ≤ t) (ht1 : t ≤ (3 / 8)) (hx0 : (17 / 60) ≤ x) (hx1 : x ≤ (4 / 7)) :
    0 < nltFc5 t x := by
  have hx : (0 : ℝ) ≤ x := by linarith
  have ht : (0 : ℝ) ≤ t := by linarith
  have hq := nltFc5_posQ_pos hx0 hx1
  have m0 := nlt_hi 4 2 (by norm_num : ((3 / 8) : ℝ) ^ 4 = (81 / 4096)) ht ht1 hx
  have m1 := nlt_hi 4 1 (by norm_num : ((3 / 8) : ℝ) ^ 4 = (81 / 4096)) ht ht1 hx
  have m2 := nlt_lo 4 0 (by norm_num : ((1 / 3) : ℝ) ^ 4 = (1 / 81)) (by norm_num) ht0 hx
  have m3 := nlt_hi 3 3 (by norm_num : ((3 / 8) : ℝ) ^ 3 = (27 / 512)) ht ht1 hx
  have m4 := nlt_hi 3 2 (by norm_num : ((3 / 8) : ℝ) ^ 3 = (27 / 512)) ht ht1 hx
  have m5 := nlt_lo 3 1 (by norm_num : ((1 / 3) : ℝ) ^ 3 = (1 / 27)) (by norm_num) ht0 hx
  have m6 := nlt_lo 3 0 (by norm_num : ((1 / 3) : ℝ) ^ 3 = (1 / 27)) (by norm_num) ht0 hx
  have m7 := nlt_lo 2 4 (by norm_num : ((1 / 3) : ℝ) ^ 2 = (1 / 9)) (by norm_num) ht0 hx
  have m8 := nlt_lo 2 3 (by norm_num : ((1 / 3) : ℝ) ^ 2 = (1 / 9)) (by norm_num) ht0 hx
  have m9 := nlt_lo 2 2 (by norm_num : ((1 / 3) : ℝ) ^ 2 = (1 / 9)) (by norm_num) ht0 hx
  have m10 := nlt_lo 2 1 (by norm_num : ((1 / 3) : ℝ) ^ 2 = (1 / 9)) (by norm_num) ht0 hx
  have m11 := nlt_hi 2 0 (by norm_num : ((3 / 8) : ℝ) ^ 2 = (9 / 64)) ht ht1 hx
  have m12 := nlt_hi 1 5 (by norm_num : ((3 / 8) : ℝ) ^ 1 = (3 / 8)) ht ht1 hx
  have m13 := nlt_hi 1 4 (by norm_num : ((3 / 8) : ℝ) ^ 1 = (3 / 8)) ht ht1 hx
  have m14 := nlt_hi 1 3 (by norm_num : ((3 / 8) : ℝ) ^ 1 = (3 / 8)) ht ht1 hx
  have m15 := nlt_hi 1 2 (by norm_num : ((3 / 8) : ℝ) ^ 1 = (3 / 8)) ht ht1 hx
  have m16 := nlt_hi 1 1 (by norm_num : ((3 / 8) : ℝ) ^ 1 = (3 / 8)) ht ht1 hx
  have m17 := nlt_hi 1 0 (by norm_num : ((3 / 8) : ℝ) ^ 1 = (3 / 8)) ht ht1 hx
  unfold nltFc5 nltF5 nltFc5_posQ at *
  linarith

/-- A coefficient combination of `𝓗⁴S`: `F₆`. -/
noncomputable def nltFc6 (t x : ℝ) : ℝ := nltF6 t x

/-- The univariate lower polynomial of `nltFc6 t x` (monomial comparison in `t`). -/
noncomputable def nltFc6_posQ (x : ℝ) : ℝ :=
  (393817 / 8) + (1153453 / 12) * x + 99105 * x ^ 2 + 17840 * x ^ 3 + 3808 * x ^ 4 + 8160 * x ^ 5

/-- The univariate bound for `nltFc6_pos`. -/
theorem nltFc6_posQ_pos {x : ℝ} (h1 : (17 / 60) ≤ x) (h2 : x ≤ (4 / 7)) : 0 < nltFc6_posQ x := by
  obtain ⟨z, rfl⟩ : ∃ z, x = (17 / 60) + z := ⟨x - (17 / 60), by ring⟩
  have z0 : 0 ≤ z := by linarith
  have z1 : z ≤ (121 / 420) := by linarith
  have p2 : z ^ 2 ≤ (121 / 420) * z ^ 1 := nlt_pw z0 z1 1
  have q2 : 0 ≤ z ^ 2 := pow_nonneg z0 2
  have p3 : z ^ 3 ≤ (121 / 420) * z ^ 2 := nlt_pw z0 z1 2
  have q3 : 0 ≤ z ^ 3 := pow_nonneg z0 3
  have p4 : z ^ 4 ≤ (121 / 420) * z ^ 3 := nlt_pw z0 z1 3
  have q4 : 0 ≤ z ^ 4 := pow_nonneg z0 4
  have p5 : z ^ 5 ≤ (121 / 420) * z ^ 4 := nlt_pw z0 z1 4
  have q5 : 0 ≤ z ^ 5 := pow_nonneg z0 5
  have e : nltFc6_posQ ((17 / 60) + z) = (9165158531 / 108000) + (4244033987 / 27000) * z + (26540822 / 225) * z ^ 2 + (143532 / 5) * z ^ 3 + 15368 * z ^ 4 + 8160 * z ^ 5 := by unfold nltFc6_posQ; ring
  rw [e]; linarith only [z0, z1, p2, q2, p3, q3, p4, q4, p5, q5]

/-- A coefficient sign of `𝓗⁴S` on the box `[1/3, 3/8] × [17/60, 4/7]`. -/
theorem nltFc6_pos {t x : ℝ} (ht0 : (1 / 3) ≤ t) (ht1 : t ≤ (3 / 8)) (hx0 : (17 / 60) ≤ x) (hx1 : x ≤ (4 / 7)) :
    0 < nltFc6 t x := by
  have hx : (0 : ℝ) ≤ x := by linarith
  have ht : (0 : ℝ) ≤ t := by linarith
  have hq := nltFc6_posQ_pos hx0 hx1
  have m0 := nlt_hi 4 0 (by norm_num : ((3 / 8) : ℝ) ^ 4 = (81 / 4096)) ht ht1 hx
  have m1 := nlt_hi 3 2 (by norm_num : ((3 / 8) : ℝ) ^ 3 = (27 / 512)) ht ht1 hx
  have m2 := nlt_hi 3 1 (by norm_num : ((3 / 8) : ℝ) ^ 3 = (27 / 512)) ht ht1 hx
  have m3 := nlt_hi 3 0 (by norm_num : ((3 / 8) : ℝ) ^ 3 = (27 / 512)) ht ht1 hx
  have m4 := nlt_lo 2 3 (by norm_num : ((1 / 3) : ℝ) ^ 2 = (1 / 9)) (by norm_num) ht0 hx
  have m5 := nlt_lo 2 2 (by norm_num : ((1 / 3) : ℝ) ^ 2 = (1 / 9)) (by norm_num) ht0 hx
  have m6 := nlt_lo 2 1 (by norm_num : ((1 / 3) : ℝ) ^ 2 = (1 / 9)) (by norm_num) ht0 hx
  have m7 := nlt_hi 2 0 (by norm_num : ((3 / 8) : ℝ) ^ 2 = (9 / 64)) ht ht1 hx
  have m8 := nlt_lo 1 4 (by norm_num : ((1 / 3) : ℝ) ^ 1 = (1 / 3)) (by norm_num) ht0 hx
  have m9 := nlt_lo 1 3 (by norm_num : ((1 / 3) : ℝ) ^ 1 = (1 / 3)) (by norm_num) ht0 hx
  have m10 := nlt_lo 1 2 (by norm_num : ((1 / 3) : ℝ) ^ 1 = (1 / 3)) (by norm_num) ht0 hx
  have m11 := nlt_lo 1 1 (by norm_num : ((1 / 3) : ℝ) ^ 1 = (1 / 3)) (by norm_num) ht0 hx
  have m12 := nlt_lo 1 0 (by norm_num : ((1 / 3) : ℝ) ^ 1 = (1 / 3)) (by norm_num) ht0 hx
  unfold nltFc6 nltF6 nltFc6_posQ at *
  linarith

/-- A coefficient combination of `𝓗⁴S`: `-(F₂ + 5Y⁴F₆)`, `Y = 9/32`. -/
noncomputable def nltFc2 (t x : ℝ) : ℝ := -(nltF2 t x + 5 * (9 / 32) ^ 4 * nltF6 t x)

/-- The univariate lower polynomial of `nltFc2 t x` (monomial comparison in `t`). -/
noncomputable def nltFc2_posQ (x : ℝ) : ℝ :=
  (70276421397305 / 25165824) + (53235630782325 / 4194304) * x + (15930602208171 / 1048576) * x ^ 2 + (153204226787 / 24576) * x ^ 3 - (58942414803 / 65536) * x ^ 4 - (19788702939 / 32768) * x ^ 5 + 203184 * x ^ 6

/-- The univariate bound for `nltFc2_pos`. -/
theorem nltFc2_posQ_pos {x : ℝ} (h1 : (17 / 60) ≤ x) (h2 : x ≤ (4 / 7)) : 0 < nltFc2_posQ x := by
  obtain ⟨z, rfl⟩ : ∃ z, x = (17 / 60) + z := ⟨x - (17 / 60), by ring⟩
  have z0 : 0 ≤ z := by linarith
  have z1 : z ≤ (121 / 420) := by linarith
  have p2 : z ^ 2 ≤ (121 / 420) * z ^ 1 := nlt_pw z0 z1 1
  have q2 : 0 ≤ z ^ 2 := pow_nonneg z0 2
  have p3 : z ^ 3 ≤ (121 / 420) * z ^ 2 := nlt_pw z0 z1 2
  have q3 : 0 ≤ z ^ 3 := pow_nonneg z0 3
  have p4 : z ^ 4 ≤ (121 / 420) * z ^ 3 := nlt_pw z0 z1 3
  have q4 : 0 ≤ z ^ 4 := pow_nonneg z0 4
  have p5 : z ^ 5 ≤ (121 / 420) * z ^ 4 := nlt_pw z0 z1 4
  have q5 : 0 ≤ z ^ 5 := pow_nonneg z0 5
  have p6 : z ^ 6 ≤ (121 / 420) * z ^ 5 := nlt_pw z0 z1 5
  have q6 : 0 ≤ z ^ 6 := pow_nonneg z0 6
  have e : nltFc2_posQ ((17 / 60) + z) = (328838575319621847493 / 42467328000000) + (1785497576600405521 / 78643200000) * z + (122514388490629 / 6144000) * z ^ 2 + (31602882574429 / 6553600) * z ^ 3 - (989758837371 / 655360) * z ^ 4 - (42351081543 / 163840) * z ^ 5 + 203184 * z ^ 6 := by unfold nltFc2_posQ; ring
  rw [e]; linarith only [z0, z1, p2, q2, p3, q3, p4, q4, p5, q5, p6, q6]

/-- A coefficient sign of `𝓗⁴S` on the box `[1/3, 3/8] × [17/60, 4/7]`. -/
theorem nltFc2_pos {t x : ℝ} (ht0 : (1 / 3) ≤ t) (ht1 : t ≤ (3 / 8)) (hx0 : (17 / 60) ≤ x) (hx1 : x ≤ (4 / 7)) :
    0 < nltFc2 t x := by
  have hx : (0 : ℝ) ≤ x := by linarith
  have ht : (0 : ℝ) ≤ t := by linarith
  have hq := nltFc2_posQ_pos hx0 hx1
  have m0 := nlt_hi 4 2 (by norm_num : ((3 / 8) : ℝ) ^ 4 = (81 / 4096)) ht ht1 hx
  have m1 := nlt_hi 4 1 (by norm_num : ((3 / 8) : ℝ) ^ 4 = (81 / 4096)) ht ht1 hx
  have m2 := nlt_hi 4 0 (by norm_num : ((3 / 8) : ℝ) ^ 4 = (81 / 4096)) ht ht1 hx
  have m3 := nlt_lo 3 3 (by norm_num : ((1 / 3) : ℝ) ^ 3 = (1 / 27)) (by norm_num) ht0 hx
  have m4 := nlt_hi 3 2 (by norm_num : ((3 / 8) : ℝ) ^ 3 = (27 / 512)) ht ht1 hx
  have m5 := nlt_hi 3 1 (by norm_num : ((3 / 8) : ℝ) ^ 3 = (27 / 512)) ht ht1 hx
  have m6 := nlt_hi 3 0 (by norm_num : ((3 / 8) : ℝ) ^ 3 = (27 / 512)) ht ht1 hx
  have m7 := nlt_lo 2 4 (by norm_num : ((1 / 3) : ℝ) ^ 2 = (1 / 9)) (by norm_num) ht0 hx
  have m8 := nlt_lo 2 3 (by norm_num : ((1 / 3) : ℝ) ^ 2 = (1 / 9)) (by norm_num) ht0 hx
  have m9 := nlt_lo 2 2 (by norm_num : ((1 / 3) : ℝ) ^ 2 = (1 / 9)) (by norm_num) ht0 hx
  have m10 := nlt_lo 2 1 (by norm_num : ((1 / 3) : ℝ) ^ 2 = (1 / 9)) (by norm_num) ht0 hx
  have m11 := nlt_lo 2 0 (by norm_num : ((1 / 3) : ℝ) ^ 2 = (1 / 9)) (by norm_num) ht0 hx
  have m12 := nlt_hi 1 5 (by norm_num : ((3 / 8) : ℝ) ^ 1 = (3 / 8)) ht ht1 hx
  have m13 := nlt_hi 1 4 (by norm_num : ((3 / 8) : ℝ) ^ 1 = (3 / 8)) ht ht1 hx
  have m14 := nlt_hi 1 3 (by norm_num : ((3 / 8) : ℝ) ^ 1 = (3 / 8)) ht ht1 hx
  have m15 := nlt_hi 1 2 (by norm_num : ((3 / 8) : ℝ) ^ 1 = (3 / 8)) ht ht1 hx
  have m16 := nlt_hi 1 1 (by norm_num : ((3 / 8) : ℝ) ^ 1 = (3 / 8)) ht ht1 hx
  have m17 := nlt_hi 1 0 (by norm_num : ((3 / 8) : ℝ) ^ 1 = (3 / 8)) ht ht1 hx
  unfold nltFc2 nltF2 nltF6 nltFc2_posQ at *
  linarith

/-- A coefficient combination of `𝓗⁴S`: `F₀`. -/
noncomputable def nltFc0 (t x : ℝ) : ℝ := nltF0 t x

/-- The univariate lower polynomial of `nltFc0 t x` (monomial comparison in `t`). -/
noncomputable def nltFc0_posQ (x : ℝ) : ℝ :=
  (20862451 / 36) + (43651601 / 24) * x + (7039669 / 2) * x ^ 2 + 3747756 * x ^ 3 + 1676496 * x ^ 4 + 205632 * x ^ 5

/-- The univariate bound for `nltFc0_pos`. -/
theorem nltFc0_posQ_pos {x : ℝ} (h1 : (17 / 60) ≤ x) (h2 : x ≤ (4 / 7)) : 500000 < nltFc0_posQ x := by
  obtain ⟨z, rfl⟩ : ∃ z, x = (17 / 60) + z := ⟨x - (17 / 60), by ring⟩
  have z0 : 0 ≤ z := by linarith
  have z1 : z ≤ (121 / 420) := by linarith
  have p2 : z ^ 2 ≤ (121 / 420) * z ^ 1 := nlt_pw z0 z1 1
  have q2 : 0 ≤ z ^ 2 := pow_nonneg z0 2
  have p3 : z ^ 3 ≤ (121 / 420) * z ^ 2 := nlt_pw z0 z1 2
  have q3 : 0 ≤ z ^ 3 := pow_nonneg z0 3
  have p4 : z ^ 4 ≤ (121 / 420) * z ^ 3 := nlt_pw z0 z1 3
  have q4 : 0 ≤ z ^ 4 := pow_nonneg z0 4
  have p5 : z ^ 5 ≤ (121 / 420) * z ^ 4 := nlt_pw z0 z1 4
  have q5 : 0 ≤ z ^ 5 := pow_nonneg z0 5
  have e : nltFc0_posQ ((17 / 60) + z) = (994836739417 / 675000) + (43876172257 / 9000) * z + (75597111 / 10) * z ^ 2 + (29064308 / 5) * z ^ 3 + 1967808 * z ^ 4 + 205632 * z ^ 5 := by unfold nltFc0_posQ; ring
  rw [e]; linarith only [z0, z1, p2, q2, p3, q3, p4, q4, p5, q5]

/-- A coefficient sign of `𝓗⁴S` on the box `[1/3, 3/8] × [17/60, 4/7]`. -/
theorem nltFc0_pos {t x : ℝ} (ht0 : (1 / 3) ≤ t) (ht1 : t ≤ (3 / 8)) (hx0 : (17 / 60) ≤ x) (hx1 : x ≤ (4 / 7)) :
    500000 < nltFc0 t x := by
  have hx : (0 : ℝ) ≤ x := by linarith
  have ht : (0 : ℝ) ≤ t := by linarith
  have hq := nltFc0_posQ_pos hx0 hx1
  have m0 := nlt_lo 4 0 (by norm_num : ((1 / 3) : ℝ) ^ 4 = (1 / 81)) (by norm_num) ht0 hx
  have m1 := nlt_hi 3 2 (by norm_num : ((3 / 8) : ℝ) ^ 3 = (27 / 512)) ht ht1 hx
  have m2 := nlt_hi 3 1 (by norm_num : ((3 / 8) : ℝ) ^ 3 = (27 / 512)) ht ht1 hx
  have m3 := nlt_hi 3 0 (by norm_num : ((3 / 8) : ℝ) ^ 3 = (27 / 512)) ht ht1 hx
  have m4 := nlt_lo 2 3 (by norm_num : ((1 / 3) : ℝ) ^ 2 = (1 / 9)) (by norm_num) ht0 hx
  have m5 := nlt_lo 2 2 (by norm_num : ((1 / 3) : ℝ) ^ 2 = (1 / 9)) (by norm_num) ht0 hx
  have m6 := nlt_lo 2 1 (by norm_num : ((1 / 3) : ℝ) ^ 2 = (1 / 9)) (by norm_num) ht0 hx
  have m7 := nlt_lo 2 0 (by norm_num : ((1 / 3) : ℝ) ^ 2 = (1 / 9)) (by norm_num) ht0 hx
  have m8 := nlt_hi 1 4 (by norm_num : ((3 / 8) : ℝ) ^ 1 = (3 / 8)) ht ht1 hx
  have m9 := nlt_hi 1 3 (by norm_num : ((3 / 8) : ℝ) ^ 1 = (3 / 8)) ht ht1 hx
  have m10 := nlt_hi 1 2 (by norm_num : ((3 / 8) : ℝ) ^ 1 = (3 / 8)) ht ht1 hx
  have m11 := nlt_hi 1 1 (by norm_num : ((3 / 8) : ℝ) ^ 1 = (3 / 8)) ht ht1 hx
  have m12 := nlt_hi 1 0 (by norm_num : ((3 / 8) : ℝ) ^ 1 = (3 / 8)) ht ht1 hx
  unfold nltFc0 nltF0 nltFc0_posQ at *
  linarith

/-- A coefficient combination of `𝓗⁴S`: the value at `y = 9/32`. -/
noncomputable def nltFcY (t x : ℝ) : ℝ := nltF0 t x + nltF1 t x * (9 / 32) + nltF2 t x * (9 / 32) ^ 2 + nltF3 t x * (9 / 32) ^ 3 + nltF4 t x * (9 / 32) ^ 4 + nltF5 t x * (9 / 32) ^ 5 + nltF6 t x * (9 / 32) ^ 6

/-- The univariate lower polynomial of `nltFcY t x` (monomial comparison in `t`). -/
noncomputable def nltFcY_posQ (x : ℝ) : ℝ :=
  (11517990817310507 / 19327352832) + (10869204550791637 / 12884901888) * x + (2330220386321471 / 1073741824) * x ^ 2 + (120014555363415 / 33554432) * x ^ 3 + (144907519924281 / 67108864) * x ^ 4 + (14614078724055 / 33554432) * x ^ 5 + (27278685333 / 2097152) * x ^ 6

/-- The univariate bound for `nltFcY_pos`. -/
theorem nltFcY_posQ_pos {x : ℝ} (h1 : (17 / 60) ≤ x) (h2 : x ≤ (4 / 7)) : 500000 < nltFcY_posQ x := by
  obtain ⟨z, rfl⟩ : ∃ z, x = (17 / 60) + z := ⟨x - (17 / 60), by ring⟩
  have z0 : 0 ≤ z := by linarith
  have z1 : z ≤ (121 / 420) := by linarith
  have p2 : z ^ 2 ≤ (121 / 420) * z ^ 1 := nlt_pw z0 z1 1
  have q2 : 0 ≤ z ^ 2 := pow_nonneg z0 2
  have p3 : z ^ 3 ≤ (121 / 420) * z ^ 2 := nlt_pw z0 z1 2
  have q3 : 0 ≤ z ^ 3 := pow_nonneg z0 3
  have p4 : z ^ 4 ≤ (121 / 420) * z ^ 3 := nlt_pw z0 z1 3
  have q4 : 0 ≤ z ^ 4 := pow_nonneg z0 4
  have p5 : z ^ 5 ≤ (121 / 420) * z ^ 4 := nlt_pw z0 z1 4
  have q5 : 0 ≤ z ^ 5 := pow_nonneg z0 5
  have p6 : z ^ 6 ≤ (121 / 420) * z ^ 5 := nlt_pw z0 z1 5
  have q6 : 0 ≤ z ^ 6 := pow_nonneg z0 6
  have e : nltFcY_posQ ((17 / 60) + z) = (16021030381240801186829 / 14495514624000000) + (759892901763398726497 / 241591910400000) * z + (53274134512589853 / 8388608000) * z ^ 2 + (42811844542512871 / 6710886400) * z ^ 3 + (1873652149839351 / 671088640) * z ^ 4 + (76780294825563 / 167772160) * z ^ 5 + (27278685333 / 2097152) * z ^ 6 := by unfold nltFcY_posQ; ring
  rw [e]; linarith only [z0, z1, p2, q2, p3, q3, p4, q4, p5, q5, p6, q6]

/-- A coefficient sign of `𝓗⁴S` on the box `[1/3, 3/8] × [17/60, 4/7]`. -/
theorem nltFcY_pos {t x : ℝ} (ht0 : (1 / 3) ≤ t) (ht1 : t ≤ (3 / 8)) (hx0 : (17 / 60) ≤ x) (hx1 : x ≤ (4 / 7)) :
    500000 < nltFcY t x := by
  have hx : (0 : ℝ) ≤ x := by linarith
  have ht : (0 : ℝ) ≤ t := by linarith
  have hq := nltFcY_posQ_pos hx0 hx1
  have m0 := nlt_lo 4 2 (by norm_num : ((1 / 3) : ℝ) ^ 4 = (1 / 81)) (by norm_num) ht0 hx
  have m1 := nlt_lo 4 1 (by norm_num : ((1 / 3) : ℝ) ^ 4 = (1 / 81)) (by norm_num) ht0 hx
  have m2 := nlt_lo 4 0 (by norm_num : ((1 / 3) : ℝ) ^ 4 = (1 / 81)) (by norm_num) ht0 hx
  have m3 := nlt_hi 3 3 (by norm_num : ((3 / 8) : ℝ) ^ 3 = (27 / 512)) ht ht1 hx
  have m4 := nlt_hi 3 2 (by norm_num : ((3 / 8) : ℝ) ^ 3 = (27 / 512)) ht ht1 hx
  have m5 := nlt_hi 3 1 (by norm_num : ((3 / 8) : ℝ) ^ 3 = (27 / 512)) ht ht1 hx
  have m6 := nlt_hi 3 0 (by norm_num : ((3 / 8) : ℝ) ^ 3 = (27 / 512)) ht ht1 hx
  have m7 := nlt_lo 2 4 (by norm_num : ((1 / 3) : ℝ) ^ 2 = (1 / 9)) (by norm_num) ht0 hx
  have m8 := nlt_lo 2 3 (by norm_num : ((1 / 3) : ℝ) ^ 2 = (1 / 9)) (by norm_num) ht0 hx
  have m9 := nlt_lo 2 2 (by norm_num : ((1 / 3) : ℝ) ^ 2 = (1 / 9)) (by norm_num) ht0 hx
  have m10 := nlt_lo 2 1 (by norm_num : ((1 / 3) : ℝ) ^ 2 = (1 / 9)) (by norm_num) ht0 hx
  have m11 := nlt_hi 2 0 (by norm_num : ((3 / 8) : ℝ) ^ 2 = (9 / 64)) ht ht1 hx
  have m12 := nlt_hi 1 5 (by norm_num : ((3 / 8) : ℝ) ^ 1 = (3 / 8)) ht ht1 hx
  have m13 := nlt_hi 1 4 (by norm_num : ((3 / 8) : ℝ) ^ 1 = (3 / 8)) ht ht1 hx
  have m14 := nlt_hi 1 3 (by norm_num : ((3 / 8) : ℝ) ^ 1 = (3 / 8)) ht ht1 hx
  have m15 := nlt_hi 1 2 (by norm_num : ((3 / 8) : ℝ) ^ 1 = (3 / 8)) ht ht1 hx
  have m16 := nlt_hi 1 1 (by norm_num : ((3 / 8) : ℝ) ^ 1 = (3 / 8)) ht ht1 hx
  have m17 := nlt_hi 1 0 (by norm_num : ((3 / 8) : ℝ) ^ 1 = (3 / 8)) ht ht1 hx
  unfold nltFcY nltF0 nltF1 nltF2 nltF3 nltF4 nltF5 nltF6 nltFcY_posQ at *
  linarith

/-- A coefficient sign at `t = 3/8`: `E₄` (for `P₁`). -/
noncomputable def nltEb4 (x : ℝ) : ℝ := nltE4 x

/-- `nltEb4 > 120000` on `[17/60, 41/84]`. -/
theorem nltEb4_pos {x : ℝ} (h1 : (17 / 60) ≤ x) (h2 : x ≤ (41 / 84)) : 120000 < nltEb4 x := by
  obtain ⟨z, rfl⟩ : ∃ z, x = (17 / 60) + z := ⟨x - (17 / 60), by ring⟩
  have z0 : 0 ≤ z := by linarith
  have z1 : z ≤ (43 / 210) := by linarith
  have p2 : z ^ 2 ≤ (43 / 210) * z ^ 1 := nlt_pw z0 z1 1
  have q2 : 0 ≤ z ^ 2 := pow_nonneg z0 2
  have p3 : z ^ 3 ≤ (43 / 210) * z ^ 2 := nlt_pw z0 z1 2
  have q3 : 0 ≤ z ^ 3 := pow_nonneg z0 3
  have p4 : z ^ 4 ≤ (43 / 210) * z ^ 3 := nlt_pw z0 z1 3
  have q4 : 0 ≤ z ^ 4 := pow_nonneg z0 4
  have p5 : z ^ 5 ≤ (43 / 210) * z ^ 4 := nlt_pw z0 z1 4
  have q5 : 0 ≤ z ^ 5 := pow_nonneg z0 5
  have p6 : z ^ 6 ≤ (43 / 210) * z ^ 5 := nlt_pw z0 z1 5
  have q6 : 0 ≤ z ^ 6 := pow_nonneg z0 6
  have p7 : z ^ 7 ≤ (43 / 210) * z ^ 6 := nlt_pw z0 z1 6
  have q7 : 0 ≤ z ^ 7 := pow_nonneg z0 7
  have e : nltEb4 ((17 / 60) + z) = (96634481702825039 / 559872000000) + (5586697134460789 / 2332800000) * z + (289599177031649 / 51840000) * z ^ 2 + (35686734433 / 12960) * z ^ 3 - (26667464671 / 8640) * z ^ 4 - (193320119 / 60) * z ^ 5 - (10271287 / 12) * z ^ 6 - 72520 * z ^ 7 := by unfold nltEb4 nltE4; ring
  rw [e]; linarith only [z0, z1, p2, q2, p3, q3, p4, q4, p5, q5, p6, q6, p7, q7]


/-- A coefficient sign at `t = 3/8`: `E₅` (for `P₁`). -/
noncomputable def nltEb5 (x : ℝ) : ℝ := nltE5 x

/-- `nltEb5 > -70000` on `[17/60, 41/84]`. -/
theorem nltEb5_pos {x : ℝ} (h1 : (17 / 60) ≤ x) (h2 : x ≤ (41 / 84)) : (-70000) < nltEb5 x := by
  obtain ⟨z, rfl⟩ : ∃ z, x = (17 / 60) + z := ⟨x - (17 / 60), by ring⟩
  have z0 : 0 ≤ z := by linarith
  have z1 : z ≤ (43 / 210) := by linarith
  have p2 : z ^ 2 ≤ (43 / 210) * z ^ 1 := nlt_pw z0 z1 1
  have q2 : 0 ≤ z ^ 2 := pow_nonneg z0 2
  have p3 : z ^ 3 ≤ (43 / 210) * z ^ 2 := nlt_pw z0 z1 2
  have q3 : 0 ≤ z ^ 3 := pow_nonneg z0 3
  have p4 : z ^ 4 ≤ (43 / 210) * z ^ 3 := nlt_pw z0 z1 3
  have q4 : 0 ≤ z ^ 4 := pow_nonneg z0 4
  have p5 : z ^ 5 ≤ (43 / 210) * z ^ 4 := nlt_pw z0 z1 4
  have q5 : 0 ≤ z ^ 5 := pow_nonneg z0 5
  have p6 : z ^ 6 ≤ (43 / 210) * z ^ 5 := nlt_pw z0 z1 5
  have q6 : 0 ≤ z ^ 6 := pow_nonneg z0 6
  have p7 : z ^ 7 ≤ (43 / 210) * z ^ 6 := nlt_pw z0 z1 6
  have q7 : 0 ≤ z ^ 7 := pow_nonneg z0 7
  have e : nltEb5 ((17 / 60) + z) = -(3314796476046239 / 62208000000) + (1672836690401 / 3037500) * z + (683701799603 / 384000) * z ^ 2 + (6410158669 / 4800) * z ^ 3 - (704689751 / 2880) * z ^ 4 - (2466732 / 5) * z ^ 5 - (378453 / 4) * z ^ 6 - 1500 * z ^ 7 := by unfold nltEb5 nltE5; ring
  rw [e]; linarith only [z0, z1, p2, q2, p3, q3, p4, q4, p5, q5, p6, q6, p7, q7]


/-- A coefficient sign at `t = 3/8`: `E₆` (for `P₁`). -/
noncomputable def nltEb6 (x : ℝ) : ℝ := nltE6 x

/-- `nltEb6 > -1300` on `[17/60, 41/84]`. -/
theorem nltEb6_pos {x : ℝ} (h1 : (17 / 60) ≤ x) (h2 : x ≤ (41 / 84)) : (-1300) < nltEb6 x := by
  obtain ⟨z, rfl⟩ : ∃ z, x = (17 / 60) + z := ⟨x - (17 / 60), by ring⟩
  have z0 : 0 ≤ z := by linarith
  have z1 : z ≤ (43 / 210) := by linarith
  have p2 : z ^ 2 ≤ (43 / 210) * z ^ 1 := nlt_pw z0 z1 1
  have q2 : 0 ≤ z ^ 2 := pow_nonneg z0 2
  have p3 : z ^ 3 ≤ (43 / 210) * z ^ 2 := nlt_pw z0 z1 2
  have q3 : 0 ≤ z ^ 3 := pow_nonneg z0 3
  have p4 : z ^ 4 ≤ (43 / 210) * z ^ 3 := nlt_pw z0 z1 3
  have q4 : 0 ≤ z ^ 4 := pow_nonneg z0 4
  have p5 : z ^ 5 ≤ (43 / 210) * z ^ 4 := nlt_pw z0 z1 4
  have q5 : 0 ≤ z ^ 5 := pow_nonneg z0 5
  have p6 : z ^ 6 ≤ (43 / 210) * z ^ 5 := nlt_pw z0 z1 5
  have q6 : 0 ≤ z ^ 6 := pow_nonneg z0 6
  have p7 : z ^ 7 ≤ (43 / 210) * z ^ 6 := nlt_pw z0 z1 6
  have q7 : 0 ≤ z ^ 7 := pow_nonneg z0 7
  have e : nltEb6 ((17 / 60) + z) = -(9108420419761 / 8748000000) + (3485350241047 / 583200000) * z + (126953460103 / 6480000) * z ^ 2 + (1776077537 / 64800) * z ^ 3 + (2363803 / 108) * z ^ 4 + (182086 / 15) * z ^ 5 + (13994 / 3) * z ^ 6 + 680 * z ^ 7 := by unfold nltEb6 nltE6; ring
  rw [e]; linarith only [z0, z1, p2, q2, p3, q3, p4, q4, p5, q5, p6, q6, p7, q7]


/-- A coefficient sign at `t = 3/8`: `-E₂` (for `P₁`). -/
noncomputable def nltEb2 (x : ℝ) : ℝ := -nltE2 x

/-- `nltEb2 > 0` on `[17/60, 41/84]`. -/
theorem nltEb2_pos {x : ℝ} (h1 : (17 / 60) ≤ x) (h2 : x ≤ (41 / 84)) : 0 < nltEb2 x := by
  obtain ⟨z, rfl⟩ : ∃ z, x = (17 / 60) + z := ⟨x - (17 / 60), by ring⟩
  have z0 : 0 ≤ z := by linarith
  have z1 : z ≤ (43 / 210) := by linarith
  have p2 : z ^ 2 ≤ (43 / 210) * z ^ 1 := nlt_pw z0 z1 1
  have q2 : 0 ≤ z ^ 2 := pow_nonneg z0 2
  have p3 : z ^ 3 ≤ (43 / 210) * z ^ 2 := nlt_pw z0 z1 2
  have q3 : 0 ≤ z ^ 3 := pow_nonneg z0 3
  have p4 : z ^ 4 ≤ (43 / 210) * z ^ 3 := nlt_pw z0 z1 3
  have q4 : 0 ≤ z ^ 4 := pow_nonneg z0 4
  have p5 : z ^ 5 ≤ (43 / 210) * z ^ 4 := nlt_pw z0 z1 4
  have q5 : 0 ≤ z ^ 5 := pow_nonneg z0 5
  have p6 : z ^ 6 ≤ (43 / 210) * z ^ 5 := nlt_pw z0 z1 5
  have q6 : 0 ≤ z ^ 6 := pow_nonneg z0 6
  have p7 : z ^ 7 ≤ (43 / 210) * z ^ 6 := nlt_pw z0 z1 6
  have q7 : 0 ≤ z ^ 7 := pow_nonneg z0 7
  have e : nltEb2 ((17 / 60) + z) = (873308703656588237 / 2799360000000) + (2427250528201477 / 2916000000) * z + (210014074057811 / 259200000) * z ^ 2 - (79558517993 / 648000) * z ^ 3 - (43241279581 / 43200) * z ^ 4 - (69058568 / 75) * z ^ 5 - (21447349 / 60) * z ^ 6 - 44636 * z ^ 7 := by unfold nltEb2 nltE2; ring
  rw [e]; linarith only [z0, z1, p2, q2, p3, q3, p4, q4, p5, q5, p6, q6, p7, q7]


/-- A coefficient sign at `t = 3/8`: `-∂_yP₁` at `y = 9/32`. -/
noncomputable def nltEbD (x : ℝ) : ℝ := -(nltE1 x + 2 * nltE2 x * (9 / 32) + 3 * nltE3 x * (9 / 32) ^ 2 + 4 * nltE4 x * (9 / 32) ^ 3 + 5 * nltE5 x * (9 / 32) ^ 4 + 6 * nltE6 x * (9 / 32) ^ 5)

/-- `nltEbD > 0` on `[17/60, 41/84]`. -/
theorem nltEbD_pos {x : ℝ} (h1 : (17 / 60) ≤ x) (h2 : x ≤ (41 / 84)) : 0 < nltEbD x := by
  obtain ⟨z, rfl⟩ : ∃ z, x = (17 / 60) + z := ⟨x - (17 / 60), by ring⟩
  have z0 : 0 ≤ z := by linarith
  have z1 : z ≤ (43 / 210) := by linarith
  have p2 : z ^ 2 ≤ (43 / 210) * z ^ 1 := nlt_pw z0 z1 1
  have q2 : 0 ≤ z ^ 2 := pow_nonneg z0 2
  have p3 : z ^ 3 ≤ (43 / 210) * z ^ 2 := nlt_pw z0 z1 2
  have q3 : 0 ≤ z ^ 3 := pow_nonneg z0 3
  have p4 : z ^ 4 ≤ (43 / 210) * z ^ 3 := nlt_pw z0 z1 3
  have q4 : 0 ≤ z ^ 4 := pow_nonneg z0 4
  have p5 : z ^ 5 ≤ (43 / 210) * z ^ 4 := nlt_pw z0 z1 4
  have q5 : 0 ≤ z ^ 5 := pow_nonneg z0 5
  have p6 : z ^ 6 ≤ (43 / 210) * z ^ 5 := nlt_pw z0 z1 5
  have q6 : 0 ≤ z ^ 6 := pow_nonneg z0 6
  have p7 : z ^ 7 ≤ (43 / 210) * z ^ 6 := nlt_pw z0 z1 6
  have q7 : 0 ≤ z ^ 7 := pow_nonneg z0 7
  have e : nltEbD ((17 / 60) + z) = (94129212643691978916991 / 587068342272000000) - (52498337277832201961 / 1956894474240000) * z - (85838570591017415311 / 108716359680000) * z ^ 2 - (794088473124772211 / 1087163596800) * z ^ 3 - (201635850114089 / 2264924160) * z ^ 4 - (1453765355057 / 125829120) * z ^ 5 - (1994997415585 / 25165824) * z ^ 6 - (35063343295 / 2097152) * z ^ 7 := by unfold nltEbD nltE1 nltE2 nltE3 nltE4 nltE5 nltE6; ring
  rw [e]; linarith only [z0, z1, p2, q2, p3, q3, p4, q4, p5, q5, p6, q6, p7, q7]


/-- A coefficient sign at `t = 3/8`: `E₀` (for `P₁`). -/
noncomputable def nltEb0 (x : ℝ) : ℝ := nltE0 x

/-- `nltEb0 > 0` on `[17/60, 41/84]`. -/
theorem nltEb0_pos {x : ℝ} (h1 : (17 / 60) ≤ x) (h2 : x ≤ (41 / 84)) : 0 < nltEb0 x := by
  obtain ⟨z, rfl⟩ : ∃ z, x = (17 / 60) + z := ⟨x - (17 / 60), by ring⟩
  have z0 : 0 ≤ z := by linarith
  have z1 : z ≤ (43 / 210) := by linarith
  have p2 : z ^ 2 ≤ (43 / 210) * z ^ 1 := nlt_pw z0 z1 1
  have q2 : 0 ≤ z ^ 2 := pow_nonneg z0 2
  have p3 : z ^ 3 ≤ (43 / 210) * z ^ 2 := nlt_pw z0 z1 2
  have q3 : 0 ≤ z ^ 3 := pow_nonneg z0 3
  have p4 : z ^ 4 ≤ (43 / 210) * z ^ 3 := nlt_pw z0 z1 3
  have q4 : 0 ≤ z ^ 4 := pow_nonneg z0 4
  have p5 : z ^ 5 ≤ (43 / 210) * z ^ 4 := nlt_pw z0 z1 4
  have q5 : 0 ≤ z ^ 5 := pow_nonneg z0 5
  have p6 : z ^ 6 ≤ (43 / 210) * z ^ 5 := nlt_pw z0 z1 5
  have q6 : 0 ≤ z ^ 6 := pow_nonneg z0 6
  have e : nltEb0 ((17 / 60) + z) = (31836628830677 / 1296000000) + (1708378049761 / 129600000) * z + (2847599039 / 432000) * z ^ 2 - (2444612 / 225) * z ^ 3 + (686333 / 60) * z ^ 4 + (256571 / 10) * z ^ 5 + 4998 * z ^ 6 := by unfold nltEb0 nltE0; ring
  rw [e]; linarith only [z0, z1, p2, q2, p3, q3, p4, q4, p5, q5, p6, q6]


/-- A coefficient sign at `t = 3/8`: `P₁` at `y = 9/32`. -/
noncomputable def nltEbY (x : ℝ) : ℝ := nltE0 x + nltE1 x * (9 / 32) + nltE2 x * (9 / 32) ^ 2 + nltE3 x * (9 / 32) ^ 3 + nltE4 x * (9 / 32) ^ 4 + nltE5 x * (9 / 32) ^ 5 + nltE6 x * (9 / 32) ^ 6

/-- `nltEbY > 0` on `[17/60, 41/84]`. -/
theorem nltEbY_pos {x : ℝ} (h1 : (17 / 60) ≤ x) (h2 : x ≤ (41 / 84)) : 0 < nltEbY x := by
  obtain ⟨z, rfl⟩ : ∃ z, x = (17 / 60) + z := ⟨x - (17 / 60), by ring⟩
  have z0 : 0 ≤ z := by linarith
  have z1 : z ≤ (43 / 210) := by linarith
  have p2 : z ^ 2 ≤ (43 / 210) * z ^ 1 := nlt_pw z0 z1 1
  have q2 : 0 ≤ z ^ 2 := pow_nonneg z0 2
  have p3 : z ^ 3 ≤ (43 / 210) * z ^ 2 := nlt_pw z0 z1 2
  have q3 : 0 ≤ z ^ 3 := pow_nonneg z0 3
  have p4 : z ^ 4 ≤ (43 / 210) * z ^ 3 := nlt_pw z0 z1 3
  have q4 : 0 ≤ z ^ 4 := pow_nonneg z0 4
  have p5 : z ^ 5 ≤ (43 / 210) * z ^ 4 := nlt_pw z0 z1 4
  have q5 : 0 ≤ z ^ 5 := pow_nonneg z0 5
  have p6 : z ^ 6 ≤ (43 / 210) * z ^ 5 := nlt_pw z0 z1 5
  have q6 : 0 ≤ z ^ 6 := pow_nonneg z0 6
  have p7 : z ^ 7 ≤ (43 / 210) * z ^ 6 := nlt_pw z0 z1 6
  have q7 : 0 ≤ z ^ 7 := pow_nonneg z0 7
  have e : nltEbY ((17 / 60) + z) = (54764597206507822018579 / 10436770529280000000) - (2121983387499400700437 / 347892350976000000) * z + (473688490346539167869 / 11596411699200000) * z ^ 2 + (720887918942029343 / 12884901888000) * z ^ 3 + (11979435957747107 / 107374182400) * z ^ 4 + (1490281799118037 / 13421772800) * z ^ 5 + (96457938423279 / 2684354560) * z ^ 6 + (517081385493 / 134217728) * z ^ 7 := by unfold nltEbY nltE0 nltE1 nltE2 nltE3 nltE4 nltE5 nltE6; ring
  rw [e]; linarith only [z0, z1, p2, q2, p3, q3, p4, q4, p5, q5, p6, q6, p7, q7]


/-- A coefficient sign at `t = 3/8`: `-R₃` (for `P₂`). -/
noncomputable def nltRb3 (x : ℝ) : ℝ := -nltR3 x

/-- `nltRb3 > 0` on `[17/60, 41/84]`. -/
theorem nltRb3_pos {x : ℝ} (h1 : (17 / 60) ≤ x) (h2 : x ≤ (41 / 84)) : 0 < nltRb3 x := by
  obtain ⟨z, rfl⟩ : ∃ z, x = (17 / 60) + z := ⟨x - (17 / 60), by ring⟩
  have z0 : 0 ≤ z := by linarith
  have z1 : z ≤ (43 / 210) := by linarith
  have p2 : z ^ 2 ≤ (43 / 210) * z ^ 1 := nlt_pw z0 z1 1
  have q2 : 0 ≤ z ^ 2 := pow_nonneg z0 2
  have p3 : z ^ 3 ≤ (43 / 210) * z ^ 2 := nlt_pw z0 z1 2
  have q3 : 0 ≤ z ^ 3 := pow_nonneg z0 3
  have p4 : z ^ 4 ≤ (43 / 210) * z ^ 3 := nlt_pw z0 z1 3
  have q4 : 0 ≤ z ^ 4 := pow_nonneg z0 4
  have p5 : z ^ 5 ≤ (43 / 210) * z ^ 4 := nlt_pw z0 z1 4
  have q5 : 0 ≤ z ^ 5 := pow_nonneg z0 5
  have p6 : z ^ 6 ≤ (43 / 210) * z ^ 5 := nlt_pw z0 z1 5
  have q6 : 0 ≤ z ^ 6 := pow_nonneg z0 6
  have p7 : z ^ 7 ≤ (43 / 210) * z ^ 6 := nlt_pw z0 z1 6
  have q7 : 0 ≤ z ^ 7 := pow_nonneg z0 7
  have e : nltRb3 ((17 / 60) + z) = (520594642073153 / 129600000) + (1154532356149517 / 64800000) * z + (4785754540009 / 120000) * z ^ 2 + (7724691751 / 150) * z ^ 3 + (510608734 / 15) * z ^ 4 + 9833175 * z ^ 5 + 1104732 * z ^ 6 + 48960 * z ^ 7 := by unfold nltRb3 nltR3; ring
  rw [e]; linarith only [z0, z1, p2, q2, p3, q3, p4, q4, p5, q5, p6, q6, p7, q7]


/-- A coefficient sign at `t = 3/8`: `-R₄` (for `P₂`). -/
noncomputable def nltRb4 (x : ℝ) : ℝ := -nltR4 x

/-- `nltRb4 > 0` on `[17/60, 41/84]`. -/
theorem nltRb4_pos {x : ℝ} (h1 : (17 / 60) ≤ x) (h2 : x ≤ (41 / 84)) : 0 < nltRb4 x := by
  obtain ⟨z, rfl⟩ : ∃ z, x = (17 / 60) + z := ⟨x - (17 / 60), by ring⟩
  have z0 : 0 ≤ z := by linarith
  have z1 : z ≤ (43 / 210) := by linarith
  have p2 : z ^ 2 ≤ (43 / 210) * z ^ 1 := nlt_pw z0 z1 1
  have q2 : 0 ≤ z ^ 2 := pow_nonneg z0 2
  have p3 : z ^ 3 ≤ (43 / 210) * z ^ 2 := nlt_pw z0 z1 2
  have q3 : 0 ≤ z ^ 3 := pow_nonneg z0 3
  have p4 : z ^ 4 ≤ (43 / 210) * z ^ 3 := nlt_pw z0 z1 3
  have q4 : 0 ≤ z ^ 4 := pow_nonneg z0 4
  have p5 : z ^ 5 ≤ (43 / 210) * z ^ 4 := nlt_pw z0 z1 4
  have q5 : 0 ≤ z ^ 5 := pow_nonneg z0 5
  have p6 : z ^ 6 ≤ (43 / 210) * z ^ 5 := nlt_pw z0 z1 5
  have q6 : 0 ≤ z ^ 6 := pow_nonneg z0 6
  have p7 : z ^ 7 ≤ (43 / 210) * z ^ 6 := nlt_pw z0 z1 6
  have q7 : 0 ≤ z ^ 7 := pow_nonneg z0 7
  have e : nltRb4 ((17 / 60) + z) = (416279509110499 / 216000000) + (258938984682997 / 21600000) * z + (1239664220029 / 32000) * z ^ 2 + (97343639871 / 1600) * z ^ 3 + (1760198989 / 40) * z ^ 4 + (135845937 / 10) * z ^ 5 + 1567701 * z ^ 6 + 45900 * z ^ 7 := by unfold nltRb4 nltR4; ring
  rw [e]; linarith only [z0, z1, p2, q2, p3, q3, p4, q4, p5, q5, p6, q6, p7, q7]


/-- A coefficient sign at `t = 3/8`: `-R₅` (for `P₂`). -/
noncomputable def nltRb5 (x : ℝ) : ℝ := -nltR5 x

/-- `nltRb5 > 0` on `[17/60, 41/84]`. -/
theorem nltRb5_pos {x : ℝ} (h1 : (17 / 60) ≤ x) (h2 : x ≤ (41 / 84)) : 0 < nltRb5 x := by
  obtain ⟨z, rfl⟩ : ∃ z, x = (17 / 60) + z := ⟨x - (17 / 60), by ring⟩
  have z0 : 0 ≤ z := by linarith
  have z1 : z ≤ (43 / 210) := by linarith
  have p2 : z ^ 2 ≤ (43 / 210) * z ^ 1 := nlt_pw z0 z1 1
  have q2 : 0 ≤ z ^ 2 := pow_nonneg z0 2
  have p3 : z ^ 3 ≤ (43 / 210) * z ^ 2 := nlt_pw z0 z1 2
  have q3 : 0 ≤ z ^ 3 := pow_nonneg z0 3
  have p4 : z ^ 4 ≤ (43 / 210) * z ^ 3 := nlt_pw z0 z1 3
  have q4 : 0 ≤ z ^ 4 := pow_nonneg z0 4
  have p5 : z ^ 5 ≤ (43 / 210) * z ^ 4 := nlt_pw z0 z1 4
  have q5 : 0 ≤ z ^ 5 := pow_nonneg z0 5
  have p6 : z ^ 6 ≤ (43 / 210) * z ^ 5 := nlt_pw z0 z1 5
  have q6 : 0 ≤ z ^ 6 := pow_nonneg z0 6
  have p7 : z ^ 7 ≤ (43 / 210) * z ^ 6 := nlt_pw z0 z1 6
  have q7 : 0 ≤ z ^ 7 := pow_nonneg z0 7
  have e : nltRb5 ((17 / 60) + z) = (59787500199817 / 1944000000) + (4708777746377 / 6480000) * z + (8781248411447 / 1440000) * z ^ 2 + (22413102329 / 1800) * z ^ 3 + (1144956587 / 120) * z ^ 4 + (14072817 / 5) * z ^ 5 + 299175 * z ^ 6 + 12240 * z ^ 7 := by unfold nltRb5 nltR5; ring
  rw [e]; linarith only [z0, z1, p2, q2, p3, q3, p4, q4, p5, q5, p6, q6, p7, q7]


/-- A coefficient sign at `t = 3/8`: `R₆` (for `P₂`). -/
noncomputable def nltRb6 (x : ℝ) : ℝ := nltR6 x

/-- `nltRb6 > 0` on `[17/60, 41/84]`. -/
theorem nltRb6_pos {x : ℝ} (h1 : (17 / 60) ≤ x) (h2 : x ≤ (41 / 84)) : 0 < nltRb6 x := by
  obtain ⟨z, rfl⟩ : ∃ z, x = (17 / 60) + z := ⟨x - (17 / 60), by ring⟩
  have z0 : 0 ≤ z := by linarith
  have z1 : z ≤ (43 / 210) := by linarith
  have p2 : z ^ 2 ≤ (43 / 210) * z ^ 1 := nlt_pw z0 z1 1
  have q2 : 0 ≤ z ^ 2 := pow_nonneg z0 2
  have p3 : z ^ 3 ≤ (43 / 210) * z ^ 2 := nlt_pw z0 z1 2
  have q3 : 0 ≤ z ^ 3 := pow_nonneg z0 3
  have p4 : z ^ 4 ≤ (43 / 210) * z ^ 3 := nlt_pw z0 z1 3
  have q4 : 0 ≤ z ^ 4 := pow_nonneg z0 4
  have p5 : z ^ 5 ≤ (43 / 210) * z ^ 4 := nlt_pw z0 z1 4
  have q5 : 0 ≤ z ^ 5 := pow_nonneg z0 5
  have p6 : z ^ 6 ≤ (43 / 210) * z ^ 5 := nlt_pw z0 z1 5
  have q6 : 0 ≤ z ^ 6 := pow_nonneg z0 6
  have e : nltRb6 ((17 / 60) + z) = (336218081293 / 13500000) + (160119766807 / 1800000) * z + (1531562581 / 12000) * z ^ 2 + (5195481 / 50) * z ^ 3 + (269121 / 5) * z ^ 4 + (105372 / 5) * z ^ 5 + 3672 * z ^ 6 := by unfold nltRb6 nltR6; ring
  rw [e]; linarith only [z0, z1, p2, q2, p3, q3, p4, q4, p5, q5, p6, q6]


/-- A coefficient sign at `t = 3/8`: `-(R₂ + 5Y⁴R₆)`, `Y = 9/32`. -/
noncomputable def nltRb2 (x : ℝ) : ℝ := -(nltR2 x + 5 * (9 / 32) ^ 4 * nltR6 x)

/-- `nltRb2 > 0` on `[17/60, 41/84]`. -/
theorem nltRb2_pos {x : ℝ} (h1 : (17 / 60) ≤ x) (h2 : x ≤ (41 / 84)) : 0 < nltRb2 x := by
  obtain ⟨z, rfl⟩ : ∃ z, x = (17 / 60) + z := ⟨x - (17 / 60), by ring⟩
  have z0 : 0 ≤ z := by linarith
  have z1 : z ≤ (43 / 210) := by linarith
  have p2 : z ^ 2 ≤ (43 / 210) * z ^ 1 := nlt_pw z0 z1 1
  have q2 : 0 ≤ z ^ 2 := pow_nonneg z0 2
  have p3 : z ^ 3 ≤ (43 / 210) * z ^ 2 := nlt_pw z0 z1 2
  have q3 : 0 ≤ z ^ 3 := pow_nonneg z0 3
  have p4 : z ^ 4 ≤ (43 / 210) * z ^ 3 := nlt_pw z0 z1 3
  have q4 : 0 ≤ z ^ 4 := pow_nonneg z0 4
  have p5 : z ^ 5 ≤ (43 / 210) * z ^ 4 := nlt_pw z0 z1 4
  have q5 : 0 ≤ z ^ 5 := pow_nonneg z0 5
  have p6 : z ^ 6 ≤ (43 / 210) * z ^ 5 := nlt_pw z0 z1 5
  have q6 : 0 ≤ z ^ 6 := pow_nonneg z0 6
  have p7 : z ^ 7 ≤ (43 / 210) * z ^ 6 := nlt_pw z0 z1 6
  have q7 : 0 ≤ z ^ 7 := pow_nonneg z0 7
  have e : nltRb2 ((17 / 60) + z) = (1223837911490237719411 / 637009920000000) + (447146991886337485673 / 84934656000000) * z + (1139126354206223071 / 314572800000) * z ^ 2 - (5246123586341209 / 2359296000) * z ^ 3 - (330273849382379 / 78643200) * z ^ 4 - (13716793449711 / 6553600) * z ^ 5 - (204626643891 / 655360) * z ^ 6 + 7956 * z ^ 7 := by unfold nltRb2 nltR2 nltR6; ring
  rw [e]; linarith only [z0, z1, p2, q2, p3, q3, p4, q4, p5, q5, p6, q6, p7, q7]


/-- A coefficient sign at `t = 3/8`: `R₀` (for `P₂`). -/
noncomputable def nltRb0 (x : ℝ) : ℝ := nltR0 x

/-- `nltRb0 > 0` on `[17/60, 41/84]`. -/
theorem nltRb0_pos {x : ℝ} (h1 : (17 / 60) ≤ x) (h2 : x ≤ (41 / 84)) : 0 < nltRb0 x := by
  obtain ⟨z, rfl⟩ : ∃ z, x = (17 / 60) + z := ⟨x - (17 / 60), by ring⟩
  have z0 : 0 ≤ z := by linarith
  have z1 : z ≤ (43 / 210) := by linarith
  have p2 : z ^ 2 ≤ (43 / 210) * z ^ 1 := nlt_pw z0 z1 1
  have q2 : 0 ≤ z ^ 2 := pow_nonneg z0 2
  have p3 : z ^ 3 ≤ (43 / 210) * z ^ 2 := nlt_pw z0 z1 2
  have q3 : 0 ≤ z ^ 3 := pow_nonneg z0 3
  have p4 : z ^ 4 ≤ (43 / 210) * z ^ 3 := nlt_pw z0 z1 3
  have q4 : 0 ≤ z ^ 4 := pow_nonneg z0 4
  have p5 : z ^ 5 ≤ (43 / 210) * z ^ 4 := nlt_pw z0 z1 4
  have q5 : 0 ≤ z ^ 5 := pow_nonneg z0 5
  have p6 : z ^ 6 ≤ (43 / 210) * z ^ 5 := nlt_pw z0 z1 5
  have q6 : 0 ≤ z ^ 6 := pow_nonneg z0 6
  have e : nltRb0 ((17 / 60) + z) = (28822425015301 / 108000000) + (7014345170623 / 10800000) * z + (36877899527 / 36000) * z ^ 2 + (148290827 / 150) * z ^ 3 + (2917424 / 5) * z ^ 4 + (715638 / 5) * z ^ 5 + 8568 * z ^ 6 := by unfold nltRb0 nltR0; ring
  rw [e]; linarith only [z0, z1, p2, q2, p3, q3, p4, q4, p5, q5, p6, q6]


/-- A coefficient sign at `t = 3/8`: `P₂` at `y = 9/32`. -/
noncomputable def nltRbY (x : ℝ) : ℝ := nltR0 x + nltR1 x * (9 / 32) + nltR2 x * (9 / 32) ^ 2 + nltR3 x * (9 / 32) ^ 3 + nltR4 x * (9 / 32) ^ 4 + nltR5 x * (9 / 32) ^ 5 + nltR6 x * (9 / 32) ^ 6

/-- `nltRbY > 0` on `[17/60, 41/84]`. -/
theorem nltRbY_pos {x : ℝ} (h1 : (17 / 60) ≤ x) (h2 : x ≤ (41 / 84)) : 0 < nltRbY x := by
  obtain ⟨z, rfl⟩ : ∃ z, x = (17 / 60) + z := ⟨x - (17 / 60), by ring⟩
  have z0 : 0 ≤ z := by linarith
  have z1 : z ≤ (43 / 210) := by linarith
  have p2 : z ^ 2 ≤ (43 / 210) * z ^ 1 := nlt_pw z0 z1 1
  have q2 : 0 ≤ z ^ 2 := pow_nonneg z0 2
  have p3 : z ^ 3 ≤ (43 / 210) * z ^ 2 := nlt_pw z0 z1 2
  have q3 : 0 ≤ z ^ 3 := pow_nonneg z0 3
  have p4 : z ^ 4 ≤ (43 / 210) * z ^ 3 := nlt_pw z0 z1 3
  have q4 : 0 ≤ z ^ 4 := pow_nonneg z0 4
  have p5 : z ^ 5 ≤ (43 / 210) * z ^ 4 := nlt_pw z0 z1 4
  have q5 : 0 ≤ z ^ 5 := pow_nonneg z0 5
  have p6 : z ^ 6 ≤ (43 / 210) * z ^ 5 := nlt_pw z0 z1 5
  have q6 : 0 ≤ z ^ 6 := pow_nonneg z0 6
  have p7 : z ^ 7 ≤ (43 / 210) * z ^ 6 := nlt_pw z0 z1 6
  have q7 : 0 ≤ z ^ 7 := pow_nonneg z0 7
  have e : nltRbY ((17 / 60) + z) = (10497138709516629366487 / 72477573120000000) + (8897806809784442909593 / 28991029248000000) * z + (873018391735338406859 / 966367641600000) * z ^ 2 + (1126266274443654511 / 805306368000) * z ^ 3 + (29646196930080481 / 26843545600) * z ^ 4 + (2531891338149867 / 6710886400) * z ^ 5 + (31258305377307 / 671088640) * z ^ 6 + (802057059 / 2097152) * z ^ 7 := by unfold nltRbY nltR0 nltR1 nltR2 nltR3 nltR4 nltR5 nltR6; ring
  rw [e]; linarith only [z0, z1, p2, q2, p3, q3, p4, q4, p5, q5, p6, q6, p7, q7]


/-- The chord bound `nlt_poly6_chord` with a common lower bound `m` of both endpoint values. -/
theorem nlt_chord_ge {c0 c1 c2 c3 c4 c5 c6 Y y m : ℝ} (hY : 0 < Y) (hy0 : 0 ≤ y) (hyY : y ≤ Y)
    (h3 : c3 ≤ 0) (h4 : c4 ≤ 0) (h5 : c5 ≤ 0) (h6 : 0 ≤ c6) (h2 : c2 + 5 * Y ^ 4 * c6 ≤ 0)
    (hm0 : m ≤ c0)
    (hmY : m ≤ c0 + c1 * Y + c2 * Y ^ 2 + c3 * Y ^ 3 + c4 * Y ^ 4 + c5 * Y ^ 5 + c6 * Y ^ 6) :
    m ≤ c0 + c1 * y + c2 * y ^ 2 + c3 * y ^ 3 + c4 * y ^ 4 + c5 * y ^ 5 + c6 * y ^ 6 := by
  have hc := nlt_poly6_chord (c0 := c0) (c1 := c1) hy0 hyY h3 h4 h5 h6 h2
  have k1 := mul_le_mul_of_nonneg_left hm0 (by linarith : (0 : ℝ) ≤ Y - y)
  have k2 := mul_le_mul_of_nonneg_left hmY hy0
  have : Y * m ≤ Y * (c0 + c1 * y + c2 * y ^ 2 + c3 * y ^ 3 + c4 * y ^ 4 + c5 * y ^ 5
      + c6 * y ^ 6) := by linarith
  exact le_of_mul_le_mul_left this hY

/-- The strict chord bound: positive endpoint values give a positive sextic on `[0, Y]`. -/
theorem nlt_chord_pos {c0 c1 c2 c3 c4 c5 c6 Y y : ℝ} (hY : 0 < Y) (hy0 : 0 ≤ y) (hyY : y ≤ Y)
    (h3 : c3 ≤ 0) (h4 : c4 ≤ 0) (h5 : c5 ≤ 0) (h6 : 0 ≤ c6) (h2 : c2 + 5 * Y ^ 4 * c6 ≤ 0)
    (hm0 : 0 < c0)
    (hmY : 0 < c0 + c1 * Y + c2 * Y ^ 2 + c3 * Y ^ 3 + c4 * Y ^ 4 + c5 * Y ^ 5 + c6 * Y ^ 6) :
    0 < c0 + c1 * y + c2 * y ^ 2 + c3 * y ^ 3 + c4 * y ^ 4 + c5 * y ^ 5 + c6 * y ^ 6 := by
  have := nlt_chord_ge (m := min c0 (c0 + c1 * Y + c2 * Y ^ 2 + c3 * Y ^ 3 + c4 * Y ^ 4
    + c5 * Y ^ 5 + c6 * Y ^ 6)) hY hy0 hyY h3 h4 h5 h6 h2 (min_le_left _ _) (min_le_right _ _)
  have : 0 < min c0 (c0 + c1 * Y + c2 * Y ^ 2 + c3 * Y ^ 3 + c4 * Y ^ 4 + c5 * Y ^ 5
    + c6 * Y ^ 6) := lt_min hm0 hmY
  linarith

/-- **`𝓗⁴S ≥ 500000`** on `1/3 ≤ t ≤ 3/8`, `17/60 ≤ x ≤ 4/7`,
`0 ≤ y ≤ 9/32`. -/
theorem nlt_H4_box {t x y : ℝ} (ht0 : 1 / 3 ≤ t) (ht1 : t ≤ 3 / 8) (hx0 : 17 / 60 ≤ x)
    (hx1 : x ≤ 4 / 7) (hy0 : 0 ≤ y) (hy1 : y ≤ 9 / 32) :
    500000 ≤ nltF0 t x + nltF1 t x * y + nltF2 t x * y ^ 2 + nltF3 t x * y ^ 3 + nltF4 t x * y ^ 4
      + nltF5 t x * y ^ 5 + nltF6 t x * y ^ 6 := by
  have a3 := nltFc3_pos ht0 ht1 hx0 hx1
  have a4 := nltFc4_pos ht0 ht1 hx0 hx1
  have a5 := nltFc5_pos ht0 ht1 hx0 hx1
  have a6 := nltFc6_pos ht0 ht1 hx0 hx1
  have a2 := nltFc2_pos ht0 ht1 hx0 hx1
  have a0 := nltFc0_pos ht0 ht1 hx0 hx1
  have aY := nltFcY_pos ht0 ht1 hx0 hx1
  unfold nltFc3 nltFc4 nltFc5 nltFc6 nltFc2 nltFc0 nltFcY at *
  exact nlt_chord_ge (by norm_num) hy0 hy1 (by linarith) (by linarith) (by linarith) (by linarith)
    (by linarith) a0.le aY.le

/-- **`𝓗⁴S ≥ 500000` along `h`** (the Horner form): for `1/4 ≤ s ≤ 1/3`, `17/60 ≤ s + j ≤ 4/7`,
`0 ≤ y ≤ 9/32`. -/
theorem nlt_H4_ge {j s y : ℝ} (hs0 : 1 / 4 ≤ s) (hs1 : s ≤ 1 / 3) (hx0 : 17 / 60 ≤ s + j)
    (hx1 : s + j ≤ 4 / 7) (hy0 : 0 ≤ y) (hy1 : y ≤ 9 / 32) :
    500000 ≤ polyHorner (nltDer (nltDer (nltDer (nltDer (nltL0 j))))) s
      + polyHorner (nltDer (nltDer (nltDer (nltDer (nltL1 j))))) s * y
      + polyHorner (nltDer (nltDer (nltDer (nltDer (nltL2 j))))) s * y ^ 2
      + polyHorner (nltDer (nltDer (nltDer (nltDer (nltL3 j))))) s * y ^ 3
      + polyHorner (nltDer (nltDer (nltDer (nltDer (nltL4 j))))) s * y ^ 4
      + polyHorner (nltDer (nltDer (nltDer (nltDer (nltL5 j))))) s * y ^ 5
      + polyHorner (nltDer (nltDer (nltDer (nltDer (nltL6 j))))) s * y ^ 6 := by
  rw [nlt_F_eq0, nlt_F_eq1, nlt_F_eq2, nlt_F_eq3, nlt_F_eq4, nlt_F_eq5, nlt_F_eq6]
  exact nlt_H4_box (by linarith) (by linarith) hx0 hx1 hy0 hy1

/-- **`P₂ = 𝓗³S > 0` at `h = 1/4`** (`t = 3/8`), for `17/60 ≤ u ≤ 41/84`, `0 ≤ y ≤ 9/32`, by the
chord argument. -/
theorem nlt_P2_pos {u y : ℝ} (h1 : 17 / 60 ≤ u) (h2 : u ≤ 41 / 84) (hy0 : 0 ≤ y)
    (hy1 : y ≤ 9 / 32) :
    0 < nltR0 u + nltR1 u * y + nltR2 u * y ^ 2 + nltR3 u * y ^ 3 + nltR4 u * y ^ 4
      + nltR5 u * y ^ 5 + nltR6 u * y ^ 6 := by
  have a3 := nltRb3_pos h1 h2
  have a4 := nltRb4_pos h1 h2
  have a5 := nltRb5_pos h1 h2
  have a6 := nltRb6_pos h1 h2
  have a2 := nltRb2_pos h1 h2
  have a0 := nltRb0_pos h1 h2
  have aY := nltRbY_pos h1 h2
  unfold nltRb3 nltRb4 nltRb5 nltRb6 nltRb2 nltRb0 nltRbY at *
  exact nlt_chord_pos (by norm_num) hy0 hy1 (by linarith) (by linarith) (by linarith)
    (by linarith) (by linarith) a0 aY

/-- **`P₁ = 𝓗²S > 0` at `h = 1/4`** (`t = 3/8`), for `17/60 ≤ u ≤ 41/84`, `0 ≤ y ≤ 9/32`, by the
unimodal bound. -/
theorem nlt_P1_pos {u y : ℝ} (h1 : 17 / 60 ≤ u) (h2 : u ≤ 41 / 84) (hy0 : 0 ≤ y)
    (hy1 : y ≤ 9 / 32) :
    0 < nltE0 u + nltE1 u * y + nltE2 u * y ^ 2 + nltE3 u * y ^ 3 + nltE4 u * y ^ 4
      + nltE5 u * y ^ 5 + nltE6 u * y ^ 6 := by
  have b4 := nltEb4_pos h1 h2
  have b5 := nltEb5_pos h1 h2
  have b6 := nltEb6_pos h1 h2
  have b2 := nltEb2_pos h1 h2
  have bD := nltEbD_pos h1 h2
  have b0 := nltEb0_pos h1 h2
  have bY := nltEbY_pos h1 h2
  unfold nltEb4 nltEb5 nltEb6 nltEb2 nltEbD nltEb0 nltEbY at *
  set cs : List ℝ := [nltE0 u, nltE1 u, nltE2 u, nltE3 u, nltE4 u, nltE5 u, nltE6 u] with hcs
  have hf : ∀ w, polyHorner cs w = nltE0 u + nltE1 u * w + nltE2 u * w ^ 2 + nltE3 u * w ^ 3
      + nltE4 u * w ^ 4 + nltE5 u * w ^ 5 + nltE6 u * w ^ 6 := fun w => by
    rw [hcs]; simp only [polyHorner]; ring
  have hf1 : ∀ w, polyHorner (nltDer cs) w = nltE1 u + 2 * nltE2 u * w + 3 * nltE3 u * w ^ 2
      + 4 * nltE4 u * w ^ 3 + 5 * nltE5 u * w ^ 4 + 6 * nltE6 u * w ^ 5 := fun w => by
    rw [hcs]; simp only [nltDer, nltDerAux, polyHorner]; ring
  have hf2 : ∀ w, polyHorner (nltDer (nltDer cs)) w = 2 * nltE2 u + 6 * nltE3 u * w
      + 12 * nltE4 u * w ^ 2 + 20 * nltE5 u * w ^ 3 + 30 * nltE6 u * w ^ 4 := fun w => by
    rw [hcs]; simp only [nltDer, nltDerAux, polyHorner]; ring
  have hf4 : ∀ w, polyHorner (nltDer (nltDer (nltDer (nltDer cs)))) w =
      24 * nltE4 u + 120 * nltE5 u * w + 360 * nltE6 u * w ^ 2 := fun w => by
    rw [hcs]; simp only [nltDer, nltDerAux, polyHorner]; ring
  have h4 : ∀ s, 0 ≤ s → s ≤ 9 / 32 → 0 ≤ polyHorner (nltDer (nltDer (nltDer (nltDer cs)))) s := by
    intro s s0 s1
    rw [hf4]
    have k5 := mul_le_mul_of_nonneg_right b5.le s0
    have k6 := mul_le_mul_of_nonneg_right b6.le (pow_nonneg s0 2)
    have : s ^ 2 ≤ (9 / 32) ^ 2 := pow_le_pow_left₀ s0 s1 2
    nlinarith
  have key := nlt_unimodal (fun s => nlt_hasDerivAt_horner cs s)
    (fun s => nlt_hasDerivAt_horner (nltDer cs) s)
    (fun s => nlt_hasDerivAt_horner (nltDer (nltDer cs)) s)
    (fun s => nlt_hasDerivAt_horner (nltDer (nltDer (nltDer cs))) s) h4
    (by rw [hf2]; linarith) (by rw [hf1]; linarith) hy0 hy1
  rw [hf, hf, hf] at key
  have : 0 < min (nltE0 u + nltE1 u * 0 + nltE2 u * 0 ^ 2 + nltE3 u * 0 ^ 3 + nltE4 u * 0 ^ 4
      + nltE5 u * 0 ^ 5 + nltE6 u * 0 ^ 6) (nltE0 u + nltE1 u * (9 / 32) + nltE2 u * (9 / 32) ^ 2
      + nltE3 u * (9 / 32) ^ 3 + nltE4 u * (9 / 32) ^ 4 + nltE5 u * (9 / 32) ^ 5
      + nltE6 u * (9 / 32) ^ 6) := lt_min (by simp; linarith) bY
  linarith

end SmoothedOctagon
