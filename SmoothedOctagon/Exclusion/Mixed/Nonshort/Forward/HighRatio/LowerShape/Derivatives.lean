module

public import SmoothedOctagon.Exclusion.Mixed.PolyDeriv

/-!
# Case M2, forward successor: the derivative signs of the high-ratio `h`-reduction

The univariate and monomial sign arguments of the high-ratio `h`-reduction. Write `𝓗` for the
derivative in `h` along `t = (1 - h)/2`, `x = h + j`. For `3/8 ≤ t ≤ 2/5`, `7/30 ≤ x ≤ 3/7`,
`0 ≤ y ≤ 1/4`: `-𝓗²S = ∑ Rᵢ(t, x) yⁱ > 0` (`hrl_R_pos`: `Rᵢ ≥ Qᵢ ≥ 1000Uᵢ` by monomial comparison
in `t` and coefficient rounding, `Uᵢ` by monomials in `z = x - 1/5`; `R₀` increases in `x` and
`R₀(t, 1/5) ≥ 1000K₀(t) > 0`), and `-𝓗S(2/5, x, 1 + y) = ∑ Bᵢ(x) yⁱ > 0` (`hrl_B_pos`:
`Bᵢ ≥ 10Zᵢ` by coefficient rounding, `Zᵢ` by monomials).

## Main API

* `hrlR0`, …, `hrlR6`; `hrlBb0`, …, `hrlBb6`; `hrl_R_pos`, `hrl_B_pos`.
-/

@[expose] public section

namespace SmoothedOctagon

/-- `R_0(t, x)`: `-𝓗²S = ∑ Rᵢ yⁱ`. -/
noncomputable def hrlR0 (t x : ℝ) : ℝ :=
  26416 - 110144 * x + 74480 * t - 678120 * x ^ (2 : ℕ) + 2265456 * t * x - 500352 * t ^ (2 : ℕ) - 1016316 * x ^ (3 : ℕ) + 6903900 * t * x ^ (2 : ℕ) - 6466080 * t ^ (2 : ℕ) * x + 530832 * t ^ (3 : ℕ) - 604996 * x ^ (4 : ℕ) + 6643009 * t * x ^ (3 : ℕ) - 13617054 * t ^ (2 : ℕ) * x ^ (2 : ℕ) + 6335064 * t ^ (3 : ℕ) * x - 1040868 * t ^ (4 : ℕ) - 143568 * x ^ (5 : ℕ) + 2236068 * t * x ^ (4 : ℕ) - 7615380 * t ^ (2 : ℕ) * x ^ (3 : ℕ) + 7979163 * t ^ (3 : ℕ) * x ^ (2 : ℕ) - 4631772 * t ^ (4 : ℕ) * x + 1513974 * t ^ (5 : ℕ) - 13056 * x ^ (6 : ℕ) + 262020 * t * x ^ (5 : ℕ) - 356472 * t ^ (2 : ℕ) * x ^ (4 : ℕ) - 243931 * t ^ (3 : ℕ) * x ^ (3 : ℕ) - (4089471 / 2) * t ^ (4 : ℕ) * x ^ (2 : ℕ) + 2791482 * t ^ (5 : ℕ) * x - 469278 * t ^ (6 : ℕ) + 19584 * t * x ^ (6 : ℕ) + 44088 * t ^ (2 : ℕ) * x ^ (5 : ℕ) - 1468960 * t ^ (3 : ℕ) * x ^ (4 : ℕ) + (3077915 / 2) * t ^ (4 : ℕ) * x ^ (3 : ℕ) + 772038 * t ^ (5 : ℕ) * x ^ (2 : ℕ) - 257346 * t ^ (6 : ℕ) * x

/-- `R_1(t, x)`: `-𝓗²S = ∑ Rᵢ yⁱ`. -/
noncomputable def hrlR1 (t x : ℝ) : ℝ :=
  46728 - 540936 * x + 272232 * t - 3407384 * x ^ (2 : ℕ) + 8480536 * t * x + 410128 * t ^ (2 : ℕ) - 6164466 * x ^ (3 : ℕ) + 30169089 * t * x ^ (2 : ℕ) - 9944628 * t ^ (2 : ℕ) * x - 4471380 * t ^ (3 : ℕ) - 4870302 * x ^ (4 : ℕ) + (70949487 / 2) * t * x ^ (3 : ℕ) - 27384303 * t ^ (2 : ℕ) * x ^ (2 : ℕ) - 9954608 * t ^ (3 : ℕ) * x + 157136 * t ^ (4 : ℕ) - 1754828 * x ^ (5 : ℕ) + 16939528 * t * x ^ (4 : ℕ) - 13151984 * t ^ (2 : ℕ) * x ^ (3 : ℕ) - (53762697 / 2) * t ^ (3 : ℕ) * x ^ (2 : ℕ) + (1778085 / 2) * t ^ (4 : ℕ) * x + 5621853 * t ^ (5 : ℕ) - 247888 * x ^ (6 : ℕ) + 3535128 * t * x ^ (5 : ℕ) + 3793668 * t ^ (2 : ℕ) * x ^ (4 : ℕ) - (84855297 / 2) * t ^ (3 : ℕ) * x ^ (3 : ℕ) + (87542823 / 4) * t ^ (4 : ℕ) * x ^ (2 : ℕ) + 9451071 * t ^ (5 : ℕ) * x - 2025969 * t ^ (6 : ℕ) - 13168 * x ^ (7 : ℕ) + 392608 * t * x ^ (6 : ℕ) + 1438416 * t ^ (2 : ℕ) * x ^ (5 : ℕ) - 19951145 * t ^ (3 : ℕ) * x ^ (4 : ℕ) + (94567235 / 4) * t ^ (4 : ℕ) * x ^ (3 : ℕ) - 253953 * t ^ (5 : ℕ) * x ^ (2 : ℕ) - 1158057 * t ^ (6 : ℕ) * x + 19584 * t * x ^ (7 : ℕ) + 9792 * t ^ (2 : ℕ) * x ^ (6 : ℕ) - 1960032 * t ^ (3 : ℕ) * x ^ (5 : ℕ) + 4022880 * t ^ (4 : ℕ) * x ^ (4 : ℕ) - 946560 * t ^ (5 : ℕ) * x ^ (3 : ℕ)

/-- `R_2(t, x)`: `-𝓗²S = ∑ Rᵢ yⁱ`. -/
noncomputable def hrlR2 (t x : ℝ) : ℝ :=
  20280 - 864980 * x + 329336 * t - 5873554 * x ^ (2 : ℕ) + 11040752 * t * x + 2951432 * t ^ (2 : ℕ) - 12143398 * x ^ (3 : ℕ) + (90249759 / 2) * t * x ^ (2 : ℕ) + 7227438 * t ^ (2 : ℕ) * x - 10110406 * t ^ (3 : ℕ) - 11313190 * x ^ (4 : ℕ) + (122405747 / 2) * t * x ^ (3 : ℕ) + 3951216 * t ^ (2 : ℕ) * x ^ (2 : ℕ) - 45011318 * t ^ (3 : ℕ) * x - 861007 * t ^ (4 : ℕ) - 5084854 * x ^ (5 : ℕ) + 35116952 * t * x ^ (4 : ℕ) + 13905821 * t ^ (2 : ℕ) * x ^ (3 : ℕ) - 99748407 * t ^ (3 : ℕ) * x ^ (2 : ℕ) + (26076201 / 4) * t ^ (4 : ℕ) * x + 10198749 * t ^ (5 : ℕ) - 1015984 * x ^ (6 : ℕ) + 9053646 * t * x ^ (5 : ℕ) + 16973520 * t ^ (2 : ℕ) * x ^ (4 : ℕ) - (214227215 / 2) * t ^ (3 : ℕ) * x ^ (3 : ℕ) + (223032855 / 4) * t ^ (4 : ℕ) * x ^ (2 : ℕ) + 17375205 * t ^ (5 : ℕ) * x - 3368205 * t ^ (6 : ℕ) - 81824 * x ^ (7 : ℕ) + 1093184 * t * x ^ (6 : ℕ) + 4486596 * t ^ (2 : ℕ) * x ^ (5 : ℕ) - (89034865 / 2) * t ^ (3 : ℕ) * x ^ (4 : ℕ) + 52225790 * t ^ (4 : ℕ) * x ^ (3 : ℕ) - 3668094 * t ^ (5 : ℕ) * x ^ (2 : ℕ) - 2058768 * t ^ (6 : ℕ) * x + 39168 * t * x ^ (7 : ℕ) + 122400 * t ^ (2 : ℕ) * x ^ (6 : ℕ) - 4979232 * t ^ (3 : ℕ) * x ^ (5 : ℕ) + 10257120 * t ^ (4 : ℕ) * x ^ (4 : ℕ) - 2839680 * t ^ (5 : ℕ) * x ^ (3 : ℕ)

/-- `R_3(t, x)`: `-𝓗²S = ∑ Rᵢ yⁱ`. -/
noncomputable def hrlR3 (t x : ℝ) : ℝ :=
  -944 - 580720 * x + 168064 * t - 4309296 * x ^ (2 : ℕ) + 6108624 * t * x + 2946480 * t ^ (2 : ℕ) - 9944990 * x ^ (3 : ℕ) + 28763298 * t * x ^ (2 : ℕ) + 18060732 * t ^ (2 : ℕ) * x - 6179368 * t ^ (3 : ℕ) - 10566664 * x ^ (4 : ℕ) + 44892958 * t * x ^ (3 : ℕ) + 32075952 * t ^ (2 : ℕ) * x ^ (2 : ℕ) - 37053496 * t ^ (3 : ℕ) * x - 6309992 * t ^ (4 : ℕ) - 5665774 * x ^ (5 : ℕ) + (60741061 / 2) * t * x ^ (4 : ℕ) + 30402098 * t ^ (2 : ℕ) * x ^ (3 : ℕ) - 88338359 * t ^ (3 : ℕ) * x ^ (2 : ℕ) - 10805756 * t ^ (4 : ℕ) * x + 10948138 * t ^ (5 : ℕ) - 1461088 * x ^ (6 : ℕ) + (18828075 / 2) * t * x ^ (5 : ℕ) + 17018256 * t ^ (2 : ℕ) * x ^ (4 : ℕ) - 87041397 * t ^ (3 : ℕ) * x ^ (3 : ℕ) + (78523983 / 2) * t ^ (4 : ℕ) * x ^ (2 : ℕ) + 21871278 * t ^ (5 : ℕ) * x - 2598690 * t ^ (6 : ℕ) - 149224 * x ^ (7 : ℕ) + 1245820 * t * x ^ (6 : ℕ) + 3858141 * t ^ (2 : ℕ) * x ^ (5 : ℕ) - 34262300 * t ^ (3 : ℕ) * x ^ (4 : ℕ) + (84334165 / 2) * t ^ (4 : ℕ) * x ^ (3 : ℕ) - 2847510 * t ^ (5 : ℕ) * x ^ (2 : ℕ) - 1801422 * t ^ (6 : ℕ) * x + 29376 * t * x ^ (7 : ℕ) + 97920 * t ^ (2 : ℕ) * x ^ (6 : ℕ) - 4020024 * t ^ (3 : ℕ) * x ^ (5 : ℕ) + 8937240 * t ^ (4 : ℕ) * x ^ (4 : ℕ) - 3076320 * t ^ (5 : ℕ) * x ^ (3 : ℕ)

/-- `R_4(t, x)`: `-𝓗²S = ∑ Rᵢ yⁱ`. -/
noncomputable def hrlR4 (t x : ℝ) : ℝ :=
  -131328 * x + 32832 * t - 1176192 * x ^ (2 : ℕ) + 1158240 * t * x + 876288 * t ^ (2 : ℕ) - 3185916 * x ^ (3 : ℕ) + (13480419 / 2) * t * x ^ (2 : ℕ) + 8113386 * t ^ (2 : ℕ) * x - 794734 * t ^ (3 : ℕ) - 4044782 * x ^ (4 : ℕ) + (26489965 / 2) * t * x ^ (3 : ℕ) + 16720050 * t ^ (2 : ℕ) * x ^ (2 : ℕ) - 5555294 * t ^ (3 : ℕ) * x - 5957896 * t ^ (4 : ℕ) - 2701170 * x ^ (5 : ℕ) + 11350173 * t * x ^ (4 : ℕ) + 12216777 * t ^ (2 : ℕ) * x ^ (3 : ℕ) - 21231885 * t ^ (3 : ℕ) * x ^ (2 : ℕ) - (41636421 / 2) * t ^ (4 : ℕ) * x + 6278616 * t ^ (5 : ℕ) - 896646 * x ^ (6 : ℕ) + 4426569 * t * x ^ (5 : ℕ) + 4254696 * t ^ (2 : ℕ) * x ^ (4 : ℕ) - 21329022 * t ^ (3 : ℕ) * x ^ (3 : ℕ) + 2908314 * t ^ (4 : ℕ) * x ^ (2 : ℕ) + 16226892 * t ^ (5 : ℕ) * x - 807360 * t ^ (6 : ℕ) - 109250 * x ^ (7 : ℕ) + 651122 * t * x ^ (6 : ℕ) + 825846 * t ^ (2 : ℕ) * x ^ (5 : ℕ) - 8189455 * t ^ (3 : ℕ) * x ^ (4 : ℕ) + (24556505 / 2) * t ^ (4 : ℕ) * x ^ (3 : ℕ) + 690606 * t ^ (5 : ℕ) * x ^ (2 : ℕ) - 772038 * t ^ (6 : ℕ) * x + 7344 * t * x ^ (7 : ℕ) + 9792 * t ^ (2 : ℕ) * x ^ (6 : ℕ) - 1050192 * t ^ (3 : ℕ) * x ^ (5 : ℕ) + 2900880 * t ^ (4 : ℕ) * x ^ (4 : ℕ) - 1419840 * t ^ (5 : ℕ) * x ^ (3 : ℕ)

/-- `R_5(t, x)`: `-𝓗²S = ∑ Rᵢ yⁱ`. -/
noncomputable def hrlR5 (t x : ℝ) : ℝ :=
  -58368 * x ^ (2 : ℕ) - 3648 * t * x + 29184 * t ^ (2 : ℕ) - 289536 * x ^ (3 : ℕ) + 207864 * t * x ^ (2 : ℕ) + 710064 * t ^ (2 : ℕ) * x + 92784 * t ^ (3 : ℕ) - 548230 * x ^ (4 : ℕ) + (2429519 / 2) * t * x ^ (3 : ℕ) + 1807623 * t ^ (2 : ℕ) * x ^ (2 : ℕ) + 2913228 * t ^ (3 : ℕ) * x - 1817820 * t ^ (4 : ℕ) - 517890 * x ^ (5 : ℕ) + (3444465 / 2) * t * x ^ (4 : ℕ) + 189600 * t ^ (2 : ℕ) * x ^ (3 : ℕ) + (5414895 / 2) * t ^ (3 : ℕ) * x ^ (2 : ℕ) - (20900025 / 2) * t ^ (4 : ℕ) * x + 1482393 * t ^ (5 : ℕ) - 225376 * x ^ (6 : ℕ) + (1823031 / 2) * t * x ^ (5 : ℕ) - 671400 * t ^ (2 : ℕ) * x ^ (4 : ℕ) + (2714155 / 2) * t ^ (3 : ℕ) * x ^ (3 : ℕ) - (21447525 / 4) * t ^ (4 : ℕ) * x ^ (2 : ℕ) + 5834307 * t ^ (5 : ℕ) * x + 22707 * t ^ (6 : ℕ) - 31620 * x ^ (7 : ℕ) + 149472 * t * x ^ (6 : ℕ) - 142959 * t ^ (2 : ℕ) * x ^ (5 : ℕ) + 301265 * t ^ (3 : ℕ) * x ^ (4 : ℕ) + (1246075 / 4) * t ^ (4 : ℕ) * x ^ (3 : ℕ) + 1153359 * t ^ (5 : ℕ) * x ^ (2 : ℕ) - 128673 * t ^ (6 : ℕ) * x - 4896 * t ^ (2 : ℕ) * x ^ (6 : ℕ) - 19992 * t ^ (3 : ℕ) * x ^ (5 : ℕ) + 246840 * t ^ (4 : ℕ) * x ^ (4 : ℕ) - 236640 * t ^ (5 : ℕ) * x ^ (3 : ℕ)

/-- `R_6(t, x)`: `-𝓗²S = ∑ Rᵢ yⁱ`. -/
noncomputable def hrlR6 (t x : ℝ) : ℝ :=
  5472 * x ^ (3 : ℕ) - 17328 * t * x ^ (2 : ℕ) + 19152 * t ^ (2 : ℕ) * x + 19152 * t ^ (3 : ℕ) + 11800 * x ^ (4 : ℕ) - 2140 * t * x ^ (3 : ℕ) + 76980 * t ^ (2 : ℕ) * x ^ (2 : ℕ) + 625600 * t ^ (3 : ℕ) * x - 273145 * t ^ (4 : ℕ) + 3092 * x ^ (5 : ℕ) + 26006 * t * x ^ (4 : ℕ) - 123088 * t ^ (2 : ℕ) * x ^ (3 : ℕ) + 714373 * t ^ (3 : ℕ) * x ^ (2 : ℕ) - (7885895 / 4) * t ^ (4 : ℕ) * x + 61045 * t ^ (5 : ℕ) - 2500 * x ^ (6 : ℕ) + 20094 * t * x ^ (5 : ℕ) - 145740 * t ^ (2 : ℕ) * x ^ (4 : ℕ) + (681345 / 2) * t ^ (3 : ℕ) * x ^ (3 : ℕ) - (5878305 / 4) * t ^ (4 : ℕ) * x ^ (2 : ℕ) + 763077 * t ^ (5 : ℕ) * x + 42891 * t ^ (6 : ℕ) - 680 * x ^ (7 : ℕ) + 3740 * t * x ^ (6 : ℕ) - 26724 * t ^ (2 : ℕ) * x ^ (5 : ℕ) + (121975 / 2) * t ^ (3 : ℕ) * x ^ (4 : ℕ) - 231710 * t ^ (4 : ℕ) * x ^ (3 : ℕ) + 257346 * t ^ (5 : ℕ) * x ^ (2 : ℕ)

/-- `B_0(x)`: `-𝓗S(2/5, x, 1 + y) = ∑ Bᵢ yⁱ`. -/
noncomputable def hrlBb0 (x : ℝ) : ℝ :=
  (14030208 / 15625) - (112902192 / 15625) * x + (103758868 / 15625) * x ^ (2 : ℕ) + (218421756 / 3125) * x ^ (3 : ℕ) + (9172656 / 125) * x ^ (4 : ℕ) + (2993216 / 125) * x ^ (5 : ℕ) + (19584 / 25) * x ^ (6 : ℕ)

/-- `B_1(x)`: `-𝓗S(2/5, x, 1 + y) = ∑ Bᵢ yⁱ`. -/
noncomputable def hrlBb1 (x : ℝ) : ℝ :=
  -(37138368 / 15625) - (775179096 / 15625) * x + (2177570546 / 15625) * x ^ (2 : ℕ) + (2139572726 / 3125) * x ^ (3 : ℕ) + (471010564 / 625) * x ^ (4 : ℕ) + (182258676 / 625) * x ^ (5 : ℕ) + (547664 / 25) * x ^ (6 : ℕ) + (19024 / 25) * x ^ (7 : ℕ)

/-- `B_2(x)`: `-𝓗S(2/5, x, 1 + y) = ∑ Bᵢ yⁱ`. -/
noncomputable def hrlBb2 (x : ℝ) : ℝ :=
  -(129441984 / 15625) - (90408832 / 3125) * x + (10679734924 / 15625) * x ^ (2 : ℕ) + (6778275876 / 3125) * x ^ (3 : ℕ) + (1442800502 / 625) * x ^ (4 : ℕ) + (602874154 / 625) * x ^ (5 : ℕ) + (11326208 / 125) * x ^ (6 : ℕ) - (392032 / 25) * x ^ (7 : ℕ) - 3264 * x ^ (8 : ℕ)

/-- `B_3(x)`: `-𝓗S(2/5, x, 1 + y) = ∑ Bᵢ yⁱ`. -/
noncomputable def hrlBb3 (x : ℝ) : ℝ :=
  -(22056896 / 15625) + (28469784 / 625) * x + (14272317936 / 15625) * x ^ (2 : ℕ) + (7788070848 / 3125) * x ^ (3 : ℕ) + (1635516648 / 625) * x ^ (4 : ℕ) + (724420048 / 625) * x ^ (5 : ℕ) + (15276616 / 125) * x ^ (6 : ℕ) - (1025864 / 25) * x ^ (7 : ℕ) - 8704 * x ^ (8 : ℕ)

/-- `B_4(x)`: `-𝓗S(2/5, x, 1 + y) = ∑ Bᵢ yⁱ`. -/
noncomputable def hrlBb4 (x : ℝ) : ℝ :=
  (105888576 / 15625) + (112077008 / 3125) * x + (6585372394 / 15625) * x ^ (2 : ℕ) + (3455606846 / 3125) * x ^ (3 : ℕ) + (734765436 / 625) * x ^ (4 : ℕ) + (352045236 / 625) * x ^ (5 : ℕ) + (1637594 / 25) * x ^ (6 : ℕ) - (870586 / 25) * x ^ (7 : ℕ) - 7616 * x ^ (8 : ℕ)

/-- `B_5(x)`: `-𝓗S(2/5, x, 1 + y) = ∑ Bᵢ yⁱ`. -/
noncomputable def hrlBb5 (x : ℝ) : ℝ :=
  (46296192 / 15625) - (31397232 / 15625) * x + (727794204 / 15625) * x ^ (2 : ℕ) + (486304078 / 3125) * x ^ (3 : ℕ) + (111332166 / 625) * x ^ (4 : ℕ) + (61822318 / 625) * x ^ (5 : ℕ) + (1605702 / 125) * x ^ (6 : ℕ) - (54516 / 5) * x ^ (7 : ℕ) - 2448 * x ^ (8 : ℕ)

/-- `B_6(x)`: `-𝓗S(2/5, x, 1 + y) = ∑ Bᵢ yⁱ`. -/
noncomputable def hrlBb6 (x : ℝ) : ℝ :=
  -(5240672 / 15625) - (97542416 / 15625) * x - (1592424 / 125) * x ^ (2 : ℕ) - (39581476 / 3125) * x ^ (3 : ℕ) - (1266564 / 125) * x ^ (4 : ℕ) - (485464 / 125) * x ^ (5 : ℕ) - (10224 / 25) * x ^ (6 : ℕ) - (1316 / 5) * x ^ (7 : ℕ) - 68 * x ^ (8 : ℕ)

/-- The lower bound `Q_1(x)` of `R_1(t, x)` for `3/8 ≤ t ≤ 2/5`. -/
noncomputable def hrlQ1 (x : ℝ) : ℝ :=
  -43180 + 493954 * x + 2234327 * x ^ (2 : ℕ) + 2776709 * x ^ (3 : ℕ) + 818186 * x ^ (4 : ℕ) - 352320 * x ^ (5 : ℕ) - 99283 * x ^ (6 : ℕ) - 5824 * x ^ (7 : ℕ)

/-- The rounded polynomial `U_1(x)`, with `Q_1 ≥ 1000U_1`. -/
noncomputable def hrlU1 (x : ℝ) : ℝ :=
  -44 + 493 * x + 2234 * x ^ (2 : ℕ) + 2776 * x ^ (3 : ℕ) + 818 * x ^ (4 : ℕ) - 353 * x ^ (5 : ℕ) - 100 * x ^ (6 : ℕ) - 6 * x ^ (7 : ℕ)

/-- The lower bound `Q_2(x)` of `R_2(t, x)` for `3/8 ≤ t ≤ 2/5`. -/
noncomputable def hrlQ2 (x : ℝ) : ℝ :=
  -48447 + 1660270 * x + 6285096 * x ^ (2 : ℕ) + 6911621 * x ^ (3 : ℕ) + 1596291 * x ^ (4 : ℕ) - 1377481 * x ^ (5 : ℕ) - 588828 * x ^ (6 : ℕ) - 67136 * x ^ (7 : ℕ)

/-- The rounded polynomial `U_2(x)`, with `Q_2 ≥ 1000U_2`. -/
noncomputable def hrlU2 (x : ℝ) : ℝ :=
  -49 + 1660 * x + 6285 * x ^ (2 : ℕ) + 6911 * x ^ (3 : ℕ) + 1596 * x ^ (4 : ℕ) - 1378 * x ^ (5 : ℕ) - 589 * x ^ (6 : ℕ) - 68 * x ^ (7 : ℕ)

/-- The lower bound `Q_3(x)` of `R_3(t, x)` for `3/8 ≤ t ≤ 2/5`. -/
noncomputable def hrlQ3 (x : ℝ) : ℝ :=
  -10042 + 1756567 * x + 6081229 * x ^ (2 : ℕ) + 6396883 * x ^ (3 : ℕ) + 1199427 * x ^ (4 : ℕ) - 1850241 * x ^ (5 : ℕ) - 980136 * x ^ (6 : ℕ) - 138208 * x ^ (7 : ℕ)

/-- The rounded polynomial `U_3(x)`, with `Q_3 ≥ 1000U_3`. -/
noncomputable def hrlU3 (x : ℝ) : ℝ :=
  -11 + 1756 * x + 6081 * x ^ (2 : ℕ) + 6396 * x ^ (3 : ℕ) + 1199 * x ^ (4 : ℕ) - 1851 * x ^ (5 : ℕ) - 981 * x ^ (6 : ℕ) - 139 * x ^ (7 : ℕ)

/-- The lower bound `Q_4(x)` of `R_4(t, x)` for `3/8 ≤ t ≤ 2/5`. -/
noncomputable def hrlQ4 (x : ℝ) : ℝ :=
  -24592 + 672644 * x + 2406437 * x ^ (2 : ℕ) + 2362147 * x ^ (3 : ℕ) + 343090 * x ^ (4 : ℕ) - 992285 * x ^ (5 : ℕ) - 651099 * x ^ (6 : ℕ) - 106496 * x ^ (7 : ℕ)

/-- The rounded polynomial `U_4(x)`, with `Q_4 ≥ 1000U_4`. -/
noncomputable def hrlU4 (x : ℝ) : ℝ :=
  -25 + 672 * x + 2406 * x ^ (2 : ℕ) + 2362 * x ^ (3 : ℕ) + 343 * x ^ (4 : ℕ) - 993 * x ^ (5 : ℕ) - 652 * x ^ (6 : ℕ) - 107 * x ^ (7 : ℕ)

/-- The lower bound `Q_5(x)` of `R_5(t, x)` for `3/8 ≤ t ≤ 2/5`. -/
noncomputable def hrlQ5 (x : ℝ) : ℝ :=
  -26484 + 27239 * x + 287842 * x ^ (2 : ℕ) + 267963 * x ^ (3 : ℕ) + 10951 * x ^ (4 : ℕ) - 200225 * x ^ (5 : ℕ) - 170108 * x ^ (6 : ℕ) - 31620 * x ^ (7 : ℕ)

/-- The rounded polynomial `U_5(x)`, with `Q_5 ≥ 1000U_5 - 10000`. -/
noncomputable def hrlU5 (x : ℝ) : ℝ :=
  -17 + 27 * x + 287 * x ^ (2 : ℕ) + 267 * x ^ (3 : ℕ) + 10 * x ^ (4 : ℕ) - 201 * x ^ (5 : ℕ) - 171 * x ^ (6 : ℕ) - 32 * x ^ (7 : ℕ)

/-- The lower bound `Q_6(x)` of `R_6(t, x)` for `3/8 ≤ t ≤ 2/5`. -/
noncomputable def hrlQ6 (x : ℝ) : ℝ :=
  -5411 - 9128 * x + 5853 * x ^ (2 : ℕ) - 3045 * x ^ (3 : ℕ) + 1449 * x ^ (4 : ℕ) + 6351 * x ^ (5 : ℕ) - 1098 * x ^ (6 : ℕ) - 680 * x ^ (7 : ℕ)

/-- The rounded polynomial `U_6(x)`, with `Q_6 ≥ 1000U_6 - 10000`. -/
noncomputable def hrlU6 (x : ℝ) : ℝ :=
  4 - 10 * x + 5 * x ^ (2 : ℕ) - 4 * x ^ (3 : ℕ) + x ^ (4 : ℕ) + 6 * x ^ (5 : ℕ) - 2 * x ^ (6 : ℕ) - x ^ (7 : ℕ)

/-- The rounded polynomial `Z_0(x)`, with `B_0 ≥ 10Z_0`. -/
noncomputable def hrlZ0 (x : ℝ) : ℝ :=
  89 - 723 * x + 664 * x ^ (2 : ℕ) + 6989 * x ^ (3 : ℕ) + 7338 * x ^ (4 : ℕ) + 2394 * x ^ (5 : ℕ) + 78 * x ^ (6 : ℕ)

/-- The rounded polynomial `Z_1(x)`, with `B_1 ≥ 10Z_1`. -/
noncomputable def hrlZ1 (x : ℝ) : ℝ :=
  -238 - 4962 * x + 13936 * x ^ (2 : ℕ) + 68466 * x ^ (3 : ℕ) + 75361 * x ^ (4 : ℕ) + 29161 * x ^ (5 : ℕ) + 2190 * x ^ (6 : ℕ) + 76 * x ^ (7 : ℕ)

/-- The rounded polynomial `Z_2(x)`, with `B_2 ≥ 10Z_2`. -/
noncomputable def hrlZ2 (x : ℝ) : ℝ :=
  -829 - 2894 * x + 68350 * x ^ (2 : ℕ) + 216904 * x ^ (3 : ℕ) + 230848 * x ^ (4 : ℕ) + 96459 * x ^ (5 : ℕ) + 9060 * x ^ (6 : ℕ) - 1569 * x ^ (7 : ℕ) - 327 * x ^ (8 : ℕ)

/-- The rounded polynomial `Z_3(x)`, with `B_3 ≥ 10Z_3`. -/
noncomputable def hrlZ3 (x : ℝ) : ℝ :=
  -142 + 4555 * x + 91342 * x ^ (2 : ℕ) + 249218 * x ^ (3 : ℕ) + 261682 * x ^ (4 : ℕ) + 115907 * x ^ (5 : ℕ) + 12221 * x ^ (6 : ℕ) - 4104 * x ^ (7 : ℕ) - 871 * x ^ (8 : ℕ)

/-- The rounded polynomial `Z_4(x)`, with `B_4 ≥ 10Z_4`. -/
noncomputable def hrlZ4 (x : ℝ) : ℝ :=
  677 + 3586 * x + 42146 * x ^ (2 : ℕ) + 110579 * x ^ (3 : ℕ) + 117562 * x ^ (4 : ℕ) + 56327 * x ^ (5 : ℕ) + 6550 * x ^ (6 : ℕ) - 3483 * x ^ (7 : ℕ) - 762 * x ^ (8 : ℕ)

/-- The rounded polynomial `Z_5(x)`, with `B_5 ≥ 10Z_5`. -/
noncomputable def hrlZ5 (x : ℝ) : ℝ :=
  296 - 201 * x + 4657 * x ^ (2 : ℕ) + 15561 * x ^ (3 : ℕ) + 17813 * x ^ (4 : ℕ) + 9891 * x ^ (5 : ℕ) + 1284 * x ^ (6 : ℕ) - 1091 * x ^ (7 : ℕ) - 245 * x ^ (8 : ℕ)

/-- The rounded polynomial `Z_6(x)`, with `B_6 ≥ 10Z_6 - 7000`. -/
noncomputable def hrlZ6 (x : ℝ) : ℝ :=
  666 - 625 * x - 1274 * x ^ (2 : ℕ) - 1267 * x ^ (3 : ℕ) - 1014 * x ^ (4 : ℕ) - 389 * x ^ (5 : ℕ) - 41 * x ^ (6 : ℕ) - 27 * x ^ (7 : ℕ) - 7 * x ^ (8 : ℕ)

/-- The polynomial `K₀(t)` with `R₀(t, 1/5) ≥ 1000K₀(t)`. -/
noncomputable def hrlK0 (t : ℝ) : ℝ :=
  -32 + 860 * t - 2400 * t ^ (2 : ℕ) + 2112 * t ^ (3 : ℕ) - 2037 * t ^ (4 : ℕ) + 2103 * t ^ (5 : ℕ) - 521 * t ^ (6 : ℕ)

/-- The lower bound `L_x(x)` of `∂_xR₀(t, x)` for `3/8 ≤ t ≤ 2/5`. -/
noncomputable def hrlLx (x : ℝ) : ℝ :=
  -60022 + 212540 * x + 813520 * x ^ (2 : ℕ) + 329922 * x ^ (3 : ℕ) - 195554 * x ^ (4 : ℕ) - 34272 * x ^ (5 : ℕ)

/-- `∂_xR₀(t, x)`. -/
noncomputable def hrlDR0 (t x : ℝ) : ℝ :=
  -110144 - 1356240 * x + 2265456 * t - 3048948 * x ^ (2 : ℕ) + 13807800 * t * x - 6466080 * t ^ (2 : ℕ) - 2419984 * x ^ (3 : ℕ) + 19929027 * t * x ^ (2 : ℕ) - 27234108 * t ^ (2 : ℕ) * x + 6335064 * t ^ (3 : ℕ) - 717840 * x ^ (4 : ℕ) + 8944272 * t * x ^ (3 : ℕ) - 22846140 * t ^ (2 : ℕ) * x ^ (2 : ℕ) + 15958326 * t ^ (3 : ℕ) * x - 4631772 * t ^ (4 : ℕ) - 78336 * x ^ (5 : ℕ) + 1310100 * t * x ^ (4 : ℕ) - 1425888 * t ^ (2 : ℕ) * x ^ (3 : ℕ) - 731793 * t ^ (3 : ℕ) * x ^ (2 : ℕ) - 4089471 * t ^ (4 : ℕ) * x + 2791482 * t ^ (5 : ℕ) + 117504 * t * x ^ (5 : ℕ) + 220440 * t ^ (2 : ℕ) * x ^ (4 : ℕ) - 5875840 * t ^ (3 : ℕ) * x ^ (3 : ℕ) + (9233745 / 2) * t ^ (4 : ℕ) * x ^ (2 : ℕ) + 1544076 * t ^ (5 : ℕ) * x - 257346 * t ^ (6 : ℕ)

/-- The coefficients in `x` of `R₀(t, x)`. -/
noncomputable def hrlR0L (t : ℝ) : List ℝ :=
  [(26416 + 74480 * t - 500352 * t ^ (2 : ℕ) + 530832 * t ^ (3 : ℕ) - 1040868 * t ^ (4 : ℕ) + 1513974 * t ^ (5 : ℕ) - 469278 * t ^ (6 : ℕ)), (-110144 + 2265456 * t - 6466080 * t ^ (2 : ℕ) + 6335064 * t ^ (3 : ℕ) - 4631772 * t ^ (4 : ℕ) + 2791482 * t ^ (5 : ℕ) - 257346 * t ^ (6 : ℕ)), (-678120 + 6903900 * t - 13617054 * t ^ (2 : ℕ) + 7979163 * t ^ (3 : ℕ) - (4089471 / 2) * t ^ (4 : ℕ) + 772038 * t ^ (5 : ℕ)), (-1016316 + 6643009 * t - 7615380 * t ^ (2 : ℕ) - 243931 * t ^ (3 : ℕ) + (3077915 / 2) * t ^ (4 : ℕ)), (-604996 + 2236068 * t - 356472 * t ^ (2 : ℕ) - 1468960 * t ^ (3 : ℕ)), (-143568 + 262020 * t + 44088 * t ^ (2 : ℕ)), (-13056 + 19584 * t)]

theorem hrl_tb {t : ℝ} (h1 : (3 / 8) ≤ t) (h2 : t ≤ (2 / 5)) :
    ((9 / 64) : ℝ) ≤ t ^ (2 : ℕ) ∧
      t ^ (2 : ℕ) ≤ ((4 / 25) : ℝ) ∧
      ((27 / 512) : ℝ) ≤ t ^ (3 : ℕ) ∧
      t ^ (3 : ℕ) ≤ ((8 / 125) : ℝ) ∧
      ((81 / 4096) : ℝ) ≤ t ^ (4 : ℕ) ∧
      t ^ (4 : ℕ) ≤ ((16 / 625) : ℝ) ∧
      ((243 / 32768) : ℝ) ≤ t ^ (5 : ℕ) ∧
      t ^ (5 : ℕ) ≤ ((32 / 3125) : ℝ) ∧
      ((729 / 262144) : ℝ) ≤ t ^ (6 : ℕ) ∧
      t ^ (6 : ℕ) ≤ ((64 / 15625) : ℝ) := by
  have l : ∀ n : ℕ, ((3 / 8) : ℝ) ^ n ≤ t ^ n := fun n => pow_le_pow_left₀ (by norm_num) h1 n
  have u : ∀ n : ℕ, t ^ n ≤ ((2 / 5) : ℝ) ^ n := fun n => pow_le_pow_left₀ (by linarith) h2 n
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  all_goals first
    | (have := l 2; norm_num at this ⊢; linarith) | (have := u 2; norm_num at this ⊢; linarith)
    | (have := l 3; norm_num at this ⊢; linarith) | (have := u 3; norm_num at this ⊢; linarith)
    | (have := l 4; norm_num at this ⊢; linarith) | (have := u 4; norm_num at this ⊢; linarith)
    | (have := l 5; norm_num at this ⊢; linarith) | (have := u 5; norm_num at this ⊢; linarith)
    | (have := l 6; norm_num at this ⊢; linarith) | (have := u 6; norm_num at this ⊢; linarith)

theorem hrl_zb {z : ℝ} (h1 : (1 / 30) ≤ z) (h2 : z ≤ (8 / 35)) :
    ((1 / 900) : ℝ) ≤ z ^ (2 : ℕ) ∧
      z ^ (2 : ℕ) ≤ ((64 / 1225) : ℝ) ∧
      ((1 / 27000) : ℝ) ≤ z ^ (3 : ℕ) ∧
      z ^ (3 : ℕ) ≤ ((512 / 42875) : ℝ) ∧
      ((1 / 810000) : ℝ) ≤ z ^ (4 : ℕ) ∧
      z ^ (4 : ℕ) ≤ ((4096 / 1500625) : ℝ) ∧
      ((1 / 24300000) : ℝ) ≤ z ^ (5 : ℕ) ∧
      z ^ (5 : ℕ) ≤ ((32768 / 52521875) : ℝ) ∧
      ((1 / 729000000) : ℝ) ≤ z ^ (6 : ℕ) ∧
      z ^ (6 : ℕ) ≤ ((262144 / 1838265625) : ℝ) ∧
      ((1 / 21870000000) : ℝ) ≤ z ^ (7 : ℕ) ∧
      z ^ (7 : ℕ) ≤ ((2097152 / 64339296875) : ℝ) ∧
      ((1 / 656100000000) : ℝ) ≤ z ^ (8 : ℕ) ∧
      z ^ (8 : ℕ) ≤ ((16777216 / 2251875390625) : ℝ) := by
  have l : ∀ n : ℕ, ((1 / 30) : ℝ) ^ n ≤ z ^ n := fun n => pow_le_pow_left₀ (by norm_num) h1 n
  have u : ∀ n : ℕ, z ^ n ≤ ((8 / 35) : ℝ) ^ n := fun n => pow_le_pow_left₀ (by linarith) h2 n
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  all_goals first
    | (have := l 2; norm_num at this ⊢; linarith) | (have := u 2; norm_num at this ⊢; linarith)
    | (have := l 3; norm_num at this ⊢; linarith) | (have := u 3; norm_num at this ⊢; linarith)
    | (have := l 4; norm_num at this ⊢; linarith) | (have := u 4; norm_num at this ⊢; linarith)
    | (have := l 5; norm_num at this ⊢; linarith) | (have := u 5; norm_num at this ⊢; linarith)
    | (have := l 6; norm_num at this ⊢; linarith) | (have := u 6; norm_num at this ⊢; linarith)
    | (have := l 7; norm_num at this ⊢; linarith) | (have := u 7; norm_num at this ⊢; linarith)
    | (have := l 8; norm_num at this ⊢; linarith) | (have := u 8; norm_num at this ⊢; linarith)

theorem hrl_ab {a : ℝ} (h1 : 0 ≤ a) (h2 : a ≤ (1 / 40)) :
    (0 : ℝ) ≤ a ^ (2 : ℕ) ∧
      a ^ (2 : ℕ) ≤ ((1 / 1600) : ℝ) ∧
      (0 : ℝ) ≤ a ^ (3 : ℕ) ∧
      a ^ (3 : ℕ) ≤ ((1 / 64000) : ℝ) ∧
      (0 : ℝ) ≤ a ^ (4 : ℕ) ∧
      a ^ (4 : ℕ) ≤ ((1 / 2560000) : ℝ) ∧
      (0 : ℝ) ≤ a ^ (5 : ℕ) ∧
      a ^ (5 : ℕ) ≤ ((1 / 102400000) : ℝ) ∧
      (0 : ℝ) ≤ a ^ (6 : ℕ) ∧
      a ^ (6 : ℕ) ≤ ((1 / 4096000000) : ℝ) := by
  have l : ∀ n : ℕ, (0 : ℝ) ^ n ≤ a ^ n := fun n => pow_le_pow_left₀ (by norm_num) h1 n
  have u : ∀ n : ℕ, a ^ n ≤ ((1 / 40) : ℝ) ^ n := fun n => pow_le_pow_left₀ (by linarith) h2 n
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  all_goals first
    | (have := l 2; norm_num at this ⊢; linarith) | (have := u 2; norm_num at this ⊢; linarith)
    | (have := l 3; norm_num at this ⊢; linarith) | (have := u 3; norm_num at this ⊢; linarith)
    | (have := l 4; norm_num at this ⊢; linarith) | (have := u 4; norm_num at this ⊢; linarith)
    | (have := l 5; norm_num at this ⊢; linarith) | (have := u 5; norm_num at this ⊢; linarith)
    | (have := l 6; norm_num at this ⊢; linarith) | (have := u 6; norm_num at this ⊢; linarith)

/-- `R_1 ≥ Q_1` by monomial comparison in `t`. -/
theorem hrl_RQ1 {t x : ℝ} (h1 : 3 / 8 ≤ t) (h2 : t ≤ 2 / 5) (hx : 0 ≤ x) : hrlQ1 x ≤ hrlR1 t x := by
  obtain ⟨l2, u2, l3, u3, l4, u4, l5, u5, l6, u6⟩ := hrl_tb h1 h2
  have f0 : 0 ≤ ((64 / 15625) - t ^ (6 : ℕ)) * x := by simpa using mul_nonneg (sub_nonneg.2 u6) (pow_nonneg hx 1)
  have f1 : 0 ≤ ((64 / 15625) - t ^ (6 : ℕ)) := by simpa using mul_nonneg (sub_nonneg.2 u6) (pow_nonneg hx 0)
  have f2 : 0 ≤ ((32 / 3125) - t ^ (5 : ℕ)) * x ^ (3 : ℕ) := by simpa using mul_nonneg (sub_nonneg.2 u5) (pow_nonneg hx 3)
  have f3 : 0 ≤ ((32 / 3125) - t ^ (5 : ℕ)) * x ^ (2 : ℕ) := by simpa using mul_nonneg (sub_nonneg.2 u5) (pow_nonneg hx 2)
  have f4 : 0 ≤ (t ^ (5 : ℕ) - (243 / 32768)) * x := by simpa using mul_nonneg (sub_nonneg.2 l5) (pow_nonneg hx 1)
  have f5 : 0 ≤ (t ^ (5 : ℕ) - (243 / 32768)) := by simpa using mul_nonneg (sub_nonneg.2 l5) (pow_nonneg hx 0)
  have f6 : 0 ≤ (t ^ (4 : ℕ) - (81 / 4096)) * x ^ (4 : ℕ) := by simpa using mul_nonneg (sub_nonneg.2 l4) (pow_nonneg hx 4)
  have f7 : 0 ≤ (t ^ (4 : ℕ) - (81 / 4096)) * x ^ (3 : ℕ) := by simpa using mul_nonneg (sub_nonneg.2 l4) (pow_nonneg hx 3)
  have f8 : 0 ≤ (t ^ (4 : ℕ) - (81 / 4096)) * x ^ (2 : ℕ) := by simpa using mul_nonneg (sub_nonneg.2 l4) (pow_nonneg hx 2)
  have f9 : 0 ≤ (t ^ (4 : ℕ) - (81 / 4096)) * x := by simpa using mul_nonneg (sub_nonneg.2 l4) (pow_nonneg hx 1)
  have f10 : 0 ≤ (t ^ (4 : ℕ) - (81 / 4096)) := by simpa using mul_nonneg (sub_nonneg.2 l4) (pow_nonneg hx 0)
  have f11 : 0 ≤ ((8 / 125) - t ^ (3 : ℕ)) * x ^ (5 : ℕ) := by simpa using mul_nonneg (sub_nonneg.2 u3) (pow_nonneg hx 5)
  have f12 : 0 ≤ ((8 / 125) - t ^ (3 : ℕ)) * x ^ (4 : ℕ) := by simpa using mul_nonneg (sub_nonneg.2 u3) (pow_nonneg hx 4)
  have f13 : 0 ≤ ((8 / 125) - t ^ (3 : ℕ)) * x ^ (3 : ℕ) := by simpa using mul_nonneg (sub_nonneg.2 u3) (pow_nonneg hx 3)
  have f14 : 0 ≤ ((8 / 125) - t ^ (3 : ℕ)) * x ^ (2 : ℕ) := by simpa using mul_nonneg (sub_nonneg.2 u3) (pow_nonneg hx 2)
  have f15 : 0 ≤ ((8 / 125) - t ^ (3 : ℕ)) * x := by simpa using mul_nonneg (sub_nonneg.2 u3) (pow_nonneg hx 1)
  have f16 : 0 ≤ ((8 / 125) - t ^ (3 : ℕ)) := by simpa using mul_nonneg (sub_nonneg.2 u3) (pow_nonneg hx 0)
  have f17 : 0 ≤ (t ^ (2 : ℕ) - (9 / 64)) * x ^ (6 : ℕ) := by simpa using mul_nonneg (sub_nonneg.2 l2) (pow_nonneg hx 6)
  have f18 : 0 ≤ (t ^ (2 : ℕ) - (9 / 64)) * x ^ (5 : ℕ) := by simpa using mul_nonneg (sub_nonneg.2 l2) (pow_nonneg hx 5)
  have f19 : 0 ≤ (t ^ (2 : ℕ) - (9 / 64)) * x ^ (4 : ℕ) := by simpa using mul_nonneg (sub_nonneg.2 l2) (pow_nonneg hx 4)
  have f20 : 0 ≤ ((4 / 25) - t ^ (2 : ℕ)) * x ^ (3 : ℕ) := by simpa using mul_nonneg (sub_nonneg.2 u2) (pow_nonneg hx 3)
  have f21 : 0 ≤ ((4 / 25) - t ^ (2 : ℕ)) * x ^ (2 : ℕ) := by simpa using mul_nonneg (sub_nonneg.2 u2) (pow_nonneg hx 2)
  have f22 : 0 ≤ ((4 / 25) - t ^ (2 : ℕ)) * x := by simpa using mul_nonneg (sub_nonneg.2 u2) (pow_nonneg hx 1)
  have f23 : 0 ≤ (t ^ (2 : ℕ) - (9 / 64)) := by simpa using mul_nonneg (sub_nonneg.2 l2) (pow_nonneg hx 0)
  have f24 : 0 ≤ (t - (3 / 8)) * x ^ (7 : ℕ) := by simpa using mul_nonneg (sub_nonneg.2 h1) (pow_nonneg hx 7)
  have f25 : 0 ≤ (t - (3 / 8)) * x ^ (6 : ℕ) := by simpa using mul_nonneg (sub_nonneg.2 h1) (pow_nonneg hx 6)
  have f26 : 0 ≤ (t - (3 / 8)) * x ^ (5 : ℕ) := by simpa using mul_nonneg (sub_nonneg.2 h1) (pow_nonneg hx 5)
  have f27 : 0 ≤ (t - (3 / 8)) * x ^ (4 : ℕ) := by simpa using mul_nonneg (sub_nonneg.2 h1) (pow_nonneg hx 4)
  have f28 : 0 ≤ (t - (3 / 8)) * x ^ (3 : ℕ) := by simpa using mul_nonneg (sub_nonneg.2 h1) (pow_nonneg hx 3)
  have f29 : 0 ≤ (t - (3 / 8)) * x ^ (2 : ℕ) := by simpa using mul_nonneg (sub_nonneg.2 h1) (pow_nonneg hx 2)
  have f30 : 0 ≤ (t - (3 / 8)) * x := by simpa using mul_nonneg (sub_nonneg.2 h1) (pow_nonneg hx 1)
  have f31 : 0 ≤ (t - (3 / 8)) := by simpa using mul_nonneg (sub_nonneg.2 h1) (pow_nonneg hx 0)
  have f32 : 0 ≤ x ^ (5 : ℕ) := by positivity
  have f33 : 0 ≤ x ^ (4 : ℕ) := by positivity
  have f34 : 0 ≤ x ^ (3 : ℕ) := by positivity
  have f35 : 0 ≤ x ^ (2 : ℕ) := by positivity
  have f36 : 0 ≤ x := by positivity
  have f37 : 0 ≤ 1 := by positivity
  unfold hrlR1 hrlQ1
  linarith only [f0, f1, f2, f3, f4, f5, f6, f7, f8, f9, f10, f11, f12, f13, f14, f15, f16, f17, f18, f19, f20, f21, f22, f23, f24, f25, f26, f27, f28, f29, f30, f31, f32, f33, f34, f35, f36, f37]

/-- `R_2 ≥ Q_2` by monomial comparison in `t`. -/
theorem hrl_RQ2 {t x : ℝ} (h1 : 3 / 8 ≤ t) (h2 : t ≤ 2 / 5) (hx : 0 ≤ x) : hrlQ2 x ≤ hrlR2 t x := by
  obtain ⟨l2, u2, l3, u3, l4, u4, l5, u5, l6, u6⟩ := hrl_tb h1 h2
  have f0 : 0 ≤ ((64 / 15625) - t ^ (6 : ℕ)) * x := by simpa using mul_nonneg (sub_nonneg.2 u6) (pow_nonneg hx 1)
  have f1 : 0 ≤ ((64 / 15625) - t ^ (6 : ℕ)) := by simpa using mul_nonneg (sub_nonneg.2 u6) (pow_nonneg hx 0)
  have f2 : 0 ≤ ((32 / 3125) - t ^ (5 : ℕ)) * x ^ (3 : ℕ) := by simpa using mul_nonneg (sub_nonneg.2 u5) (pow_nonneg hx 3)
  have f3 : 0 ≤ ((32 / 3125) - t ^ (5 : ℕ)) * x ^ (2 : ℕ) := by simpa using mul_nonneg (sub_nonneg.2 u5) (pow_nonneg hx 2)
  have f4 : 0 ≤ (t ^ (5 : ℕ) - (243 / 32768)) * x := by simpa using mul_nonneg (sub_nonneg.2 l5) (pow_nonneg hx 1)
  have f5 : 0 ≤ (t ^ (5 : ℕ) - (243 / 32768)) := by simpa using mul_nonneg (sub_nonneg.2 l5) (pow_nonneg hx 0)
  have f6 : 0 ≤ (t ^ (4 : ℕ) - (81 / 4096)) * x ^ (4 : ℕ) := by simpa using mul_nonneg (sub_nonneg.2 l4) (pow_nonneg hx 4)
  have f7 : 0 ≤ (t ^ (4 : ℕ) - (81 / 4096)) * x ^ (3 : ℕ) := by simpa using mul_nonneg (sub_nonneg.2 l4) (pow_nonneg hx 3)
  have f8 : 0 ≤ (t ^ (4 : ℕ) - (81 / 4096)) * x ^ (2 : ℕ) := by simpa using mul_nonneg (sub_nonneg.2 l4) (pow_nonneg hx 2)
  have f9 : 0 ≤ (t ^ (4 : ℕ) - (81 / 4096)) * x := by simpa using mul_nonneg (sub_nonneg.2 l4) (pow_nonneg hx 1)
  have f10 : 0 ≤ ((16 / 625) - t ^ (4 : ℕ)) := by simpa using mul_nonneg (sub_nonneg.2 u4) (pow_nonneg hx 0)
  have f11 : 0 ≤ ((8 / 125) - t ^ (3 : ℕ)) * x ^ (5 : ℕ) := by simpa using mul_nonneg (sub_nonneg.2 u3) (pow_nonneg hx 5)
  have f12 : 0 ≤ ((8 / 125) - t ^ (3 : ℕ)) * x ^ (4 : ℕ) := by simpa using mul_nonneg (sub_nonneg.2 u3) (pow_nonneg hx 4)
  have f13 : 0 ≤ ((8 / 125) - t ^ (3 : ℕ)) * x ^ (3 : ℕ) := by simpa using mul_nonneg (sub_nonneg.2 u3) (pow_nonneg hx 3)
  have f14 : 0 ≤ ((8 / 125) - t ^ (3 : ℕ)) * x ^ (2 : ℕ) := by simpa using mul_nonneg (sub_nonneg.2 u3) (pow_nonneg hx 2)
  have f15 : 0 ≤ ((8 / 125) - t ^ (3 : ℕ)) * x := by simpa using mul_nonneg (sub_nonneg.2 u3) (pow_nonneg hx 1)
  have f16 : 0 ≤ ((8 / 125) - t ^ (3 : ℕ)) := by simpa using mul_nonneg (sub_nonneg.2 u3) (pow_nonneg hx 0)
  have f17 : 0 ≤ (t ^ (2 : ℕ) - (9 / 64)) * x ^ (6 : ℕ) := by simpa using mul_nonneg (sub_nonneg.2 l2) (pow_nonneg hx 6)
  have f18 : 0 ≤ (t ^ (2 : ℕ) - (9 / 64)) * x ^ (5 : ℕ) := by simpa using mul_nonneg (sub_nonneg.2 l2) (pow_nonneg hx 5)
  have f19 : 0 ≤ (t ^ (2 : ℕ) - (9 / 64)) * x ^ (4 : ℕ) := by simpa using mul_nonneg (sub_nonneg.2 l2) (pow_nonneg hx 4)
  have f20 : 0 ≤ (t ^ (2 : ℕ) - (9 / 64)) * x ^ (3 : ℕ) := by simpa using mul_nonneg (sub_nonneg.2 l2) (pow_nonneg hx 3)
  have f21 : 0 ≤ (t ^ (2 : ℕ) - (9 / 64)) * x ^ (2 : ℕ) := by simpa using mul_nonneg (sub_nonneg.2 l2) (pow_nonneg hx 2)
  have f22 : 0 ≤ (t ^ (2 : ℕ) - (9 / 64)) * x := by simpa using mul_nonneg (sub_nonneg.2 l2) (pow_nonneg hx 1)
  have f23 : 0 ≤ (t ^ (2 : ℕ) - (9 / 64)) := by simpa using mul_nonneg (sub_nonneg.2 l2) (pow_nonneg hx 0)
  have f24 : 0 ≤ (t - (3 / 8)) * x ^ (7 : ℕ) := by simpa using mul_nonneg (sub_nonneg.2 h1) (pow_nonneg hx 7)
  have f25 : 0 ≤ (t - (3 / 8)) * x ^ (6 : ℕ) := by simpa using mul_nonneg (sub_nonneg.2 h1) (pow_nonneg hx 6)
  have f26 : 0 ≤ (t - (3 / 8)) * x ^ (5 : ℕ) := by simpa using mul_nonneg (sub_nonneg.2 h1) (pow_nonneg hx 5)
  have f27 : 0 ≤ (t - (3 / 8)) * x ^ (4 : ℕ) := by simpa using mul_nonneg (sub_nonneg.2 h1) (pow_nonneg hx 4)
  have f28 : 0 ≤ (t - (3 / 8)) * x ^ (3 : ℕ) := by simpa using mul_nonneg (sub_nonneg.2 h1) (pow_nonneg hx 3)
  have f29 : 0 ≤ (t - (3 / 8)) * x ^ (2 : ℕ) := by simpa using mul_nonneg (sub_nonneg.2 h1) (pow_nonneg hx 2)
  have f30 : 0 ≤ (t - (3 / 8)) * x := by simpa using mul_nonneg (sub_nonneg.2 h1) (pow_nonneg hx 1)
  have f31 : 0 ≤ (t - (3 / 8)) := by simpa using mul_nonneg (sub_nonneg.2 h1) (pow_nonneg hx 0)
  have f32 : 0 ≤ x ^ (6 : ℕ) := by positivity
  have f33 : 0 ≤ x ^ (5 : ℕ) := by positivity
  have f34 : 0 ≤ x ^ (4 : ℕ) := by positivity
  have f35 : 0 ≤ x ^ (3 : ℕ) := by positivity
  have f36 : 0 ≤ x ^ (2 : ℕ) := by positivity
  have f37 : 0 ≤ x := by positivity
  have f38 : 0 ≤ 1 := by positivity
  unfold hrlR2 hrlQ2
  linarith only [f0, f1, f2, f3, f4, f5, f6, f7, f8, f9, f10, f11, f12, f13, f14, f15, f16, f17, f18, f19, f20, f21, f22, f23, f24, f25, f26, f27, f28, f29, f30, f31, f32, f33, f34, f35, f36, f37, f38]

/-- `R_3 ≥ Q_3` by monomial comparison in `t`. -/
theorem hrl_RQ3 {t x : ℝ} (h1 : 3 / 8 ≤ t) (h2 : t ≤ 2 / 5) (hx : 0 ≤ x) : hrlQ3 x ≤ hrlR3 t x := by
  obtain ⟨l2, u2, l3, u3, l4, u4, l5, u5, l6, u6⟩ := hrl_tb h1 h2
  have f0 : 0 ≤ ((64 / 15625) - t ^ (6 : ℕ)) * x := by simpa using mul_nonneg (sub_nonneg.2 u6) (pow_nonneg hx 1)
  have f1 : 0 ≤ ((64 / 15625) - t ^ (6 : ℕ)) := by simpa using mul_nonneg (sub_nonneg.2 u6) (pow_nonneg hx 0)
  have f2 : 0 ≤ ((32 / 3125) - t ^ (5 : ℕ)) * x ^ (3 : ℕ) := by simpa using mul_nonneg (sub_nonneg.2 u5) (pow_nonneg hx 3)
  have f3 : 0 ≤ ((32 / 3125) - t ^ (5 : ℕ)) * x ^ (2 : ℕ) := by simpa using mul_nonneg (sub_nonneg.2 u5) (pow_nonneg hx 2)
  have f4 : 0 ≤ (t ^ (5 : ℕ) - (243 / 32768)) * x := by simpa using mul_nonneg (sub_nonneg.2 l5) (pow_nonneg hx 1)
  have f5 : 0 ≤ (t ^ (5 : ℕ) - (243 / 32768)) := by simpa using mul_nonneg (sub_nonneg.2 l5) (pow_nonneg hx 0)
  have f6 : 0 ≤ (t ^ (4 : ℕ) - (81 / 4096)) * x ^ (4 : ℕ) := by simpa using mul_nonneg (sub_nonneg.2 l4) (pow_nonneg hx 4)
  have f7 : 0 ≤ (t ^ (4 : ℕ) - (81 / 4096)) * x ^ (3 : ℕ) := by simpa using mul_nonneg (sub_nonneg.2 l4) (pow_nonneg hx 3)
  have f8 : 0 ≤ (t ^ (4 : ℕ) - (81 / 4096)) * x ^ (2 : ℕ) := by simpa using mul_nonneg (sub_nonneg.2 l4) (pow_nonneg hx 2)
  have f9 : 0 ≤ ((16 / 625) - t ^ (4 : ℕ)) * x := by simpa using mul_nonneg (sub_nonneg.2 u4) (pow_nonneg hx 1)
  have f10 : 0 ≤ ((16 / 625) - t ^ (4 : ℕ)) := by simpa using mul_nonneg (sub_nonneg.2 u4) (pow_nonneg hx 0)
  have f11 : 0 ≤ ((8 / 125) - t ^ (3 : ℕ)) * x ^ (5 : ℕ) := by simpa using mul_nonneg (sub_nonneg.2 u3) (pow_nonneg hx 5)
  have f12 : 0 ≤ ((8 / 125) - t ^ (3 : ℕ)) * x ^ (4 : ℕ) := by simpa using mul_nonneg (sub_nonneg.2 u3) (pow_nonneg hx 4)
  have f13 : 0 ≤ ((8 / 125) - t ^ (3 : ℕ)) * x ^ (3 : ℕ) := by simpa using mul_nonneg (sub_nonneg.2 u3) (pow_nonneg hx 3)
  have f14 : 0 ≤ ((8 / 125) - t ^ (3 : ℕ)) * x ^ (2 : ℕ) := by simpa using mul_nonneg (sub_nonneg.2 u3) (pow_nonneg hx 2)
  have f15 : 0 ≤ ((8 / 125) - t ^ (3 : ℕ)) * x := by simpa using mul_nonneg (sub_nonneg.2 u3) (pow_nonneg hx 1)
  have f16 : 0 ≤ ((8 / 125) - t ^ (3 : ℕ)) := by simpa using mul_nonneg (sub_nonneg.2 u3) (pow_nonneg hx 0)
  have f17 : 0 ≤ (t ^ (2 : ℕ) - (9 / 64)) * x ^ (6 : ℕ) := by simpa using mul_nonneg (sub_nonneg.2 l2) (pow_nonneg hx 6)
  have f18 : 0 ≤ (t ^ (2 : ℕ) - (9 / 64)) * x ^ (5 : ℕ) := by simpa using mul_nonneg (sub_nonneg.2 l2) (pow_nonneg hx 5)
  have f19 : 0 ≤ (t ^ (2 : ℕ) - (9 / 64)) * x ^ (4 : ℕ) := by simpa using mul_nonneg (sub_nonneg.2 l2) (pow_nonneg hx 4)
  have f20 : 0 ≤ (t ^ (2 : ℕ) - (9 / 64)) * x ^ (3 : ℕ) := by simpa using mul_nonneg (sub_nonneg.2 l2) (pow_nonneg hx 3)
  have f21 : 0 ≤ (t ^ (2 : ℕ) - (9 / 64)) * x ^ (2 : ℕ) := by simpa using mul_nonneg (sub_nonneg.2 l2) (pow_nonneg hx 2)
  have f22 : 0 ≤ (t ^ (2 : ℕ) - (9 / 64)) * x := by simpa using mul_nonneg (sub_nonneg.2 l2) (pow_nonneg hx 1)
  have f23 : 0 ≤ (t ^ (2 : ℕ) - (9 / 64)) := by simpa using mul_nonneg (sub_nonneg.2 l2) (pow_nonneg hx 0)
  have f24 : 0 ≤ (t - (3 / 8)) * x ^ (7 : ℕ) := by simpa using mul_nonneg (sub_nonneg.2 h1) (pow_nonneg hx 7)
  have f25 : 0 ≤ (t - (3 / 8)) * x ^ (6 : ℕ) := by simpa using mul_nonneg (sub_nonneg.2 h1) (pow_nonneg hx 6)
  have f26 : 0 ≤ (t - (3 / 8)) * x ^ (5 : ℕ) := by simpa using mul_nonneg (sub_nonneg.2 h1) (pow_nonneg hx 5)
  have f27 : 0 ≤ (t - (3 / 8)) * x ^ (4 : ℕ) := by simpa using mul_nonneg (sub_nonneg.2 h1) (pow_nonneg hx 4)
  have f28 : 0 ≤ (t - (3 / 8)) * x ^ (3 : ℕ) := by simpa using mul_nonneg (sub_nonneg.2 h1) (pow_nonneg hx 3)
  have f29 : 0 ≤ (t - (3 / 8)) * x ^ (2 : ℕ) := by simpa using mul_nonneg (sub_nonneg.2 h1) (pow_nonneg hx 2)
  have f30 : 0 ≤ (t - (3 / 8)) * x := by simpa using mul_nonneg (sub_nonneg.2 h1) (pow_nonneg hx 1)
  have f31 : 0 ≤ (t - (3 / 8)) := by simpa using mul_nonneg (sub_nonneg.2 h1) (pow_nonneg hx 0)
  have f32 : 0 ≤ x ^ (6 : ℕ) := by positivity
  have f33 : 0 ≤ x ^ (5 : ℕ) := by positivity
  have f34 : 0 ≤ x ^ (4 : ℕ) := by positivity
  have f35 : 0 ≤ x ^ (3 : ℕ) := by positivity
  have f36 : 0 ≤ x ^ (2 : ℕ) := by positivity
  have f37 : 0 ≤ x := by positivity
  have f38 : 0 ≤ 1 := by positivity
  unfold hrlR3 hrlQ3
  linarith only [f0, f1, f2, f3, f4, f5, f6, f7, f8, f9, f10, f11, f12, f13, f14, f15, f16, f17, f18, f19, f20, f21, f22, f23, f24, f25, f26, f27, f28, f29, f30, f31, f32, f33, f34, f35, f36, f37, f38]

/-- `R_4 ≥ Q_4` by monomial comparison in `t`. -/
theorem hrl_RQ4 {t x : ℝ} (h1 : 3 / 8 ≤ t) (h2 : t ≤ 2 / 5) (hx : 0 ≤ x) : hrlQ4 x ≤ hrlR4 t x := by
  obtain ⟨l2, u2, l3, u3, l4, u4, l5, u5, l6, u6⟩ := hrl_tb h1 h2
  have f0 : 0 ≤ ((64 / 15625) - t ^ (6 : ℕ)) * x := by simpa using mul_nonneg (sub_nonneg.2 u6) (pow_nonneg hx 1)
  have f1 : 0 ≤ ((64 / 15625) - t ^ (6 : ℕ)) := by simpa using mul_nonneg (sub_nonneg.2 u6) (pow_nonneg hx 0)
  have f2 : 0 ≤ ((32 / 3125) - t ^ (5 : ℕ)) * x ^ (3 : ℕ) := by simpa using mul_nonneg (sub_nonneg.2 u5) (pow_nonneg hx 3)
  have f3 : 0 ≤ (t ^ (5 : ℕ) - (243 / 32768)) * x ^ (2 : ℕ) := by simpa using mul_nonneg (sub_nonneg.2 l5) (pow_nonneg hx 2)
  have f4 : 0 ≤ (t ^ (5 : ℕ) - (243 / 32768)) * x := by simpa using mul_nonneg (sub_nonneg.2 l5) (pow_nonneg hx 1)
  have f5 : 0 ≤ (t ^ (5 : ℕ) - (243 / 32768)) := by simpa using mul_nonneg (sub_nonneg.2 l5) (pow_nonneg hx 0)
  have f6 : 0 ≤ (t ^ (4 : ℕ) - (81 / 4096)) * x ^ (4 : ℕ) := by simpa using mul_nonneg (sub_nonneg.2 l4) (pow_nonneg hx 4)
  have f7 : 0 ≤ (t ^ (4 : ℕ) - (81 / 4096)) * x ^ (3 : ℕ) := by simpa using mul_nonneg (sub_nonneg.2 l4) (pow_nonneg hx 3)
  have f8 : 0 ≤ (t ^ (4 : ℕ) - (81 / 4096)) * x ^ (2 : ℕ) := by simpa using mul_nonneg (sub_nonneg.2 l4) (pow_nonneg hx 2)
  have f9 : 0 ≤ ((16 / 625) - t ^ (4 : ℕ)) * x := by simpa using mul_nonneg (sub_nonneg.2 u4) (pow_nonneg hx 1)
  have f10 : 0 ≤ ((16 / 625) - t ^ (4 : ℕ)) := by simpa using mul_nonneg (sub_nonneg.2 u4) (pow_nonneg hx 0)
  have f11 : 0 ≤ ((8 / 125) - t ^ (3 : ℕ)) * x ^ (5 : ℕ) := by simpa using mul_nonneg (sub_nonneg.2 u3) (pow_nonneg hx 5)
  have f12 : 0 ≤ ((8 / 125) - t ^ (3 : ℕ)) * x ^ (4 : ℕ) := by simpa using mul_nonneg (sub_nonneg.2 u3) (pow_nonneg hx 4)
  have f13 : 0 ≤ ((8 / 125) - t ^ (3 : ℕ)) * x ^ (3 : ℕ) := by simpa using mul_nonneg (sub_nonneg.2 u3) (pow_nonneg hx 3)
  have f14 : 0 ≤ ((8 / 125) - t ^ (3 : ℕ)) * x ^ (2 : ℕ) := by simpa using mul_nonneg (sub_nonneg.2 u3) (pow_nonneg hx 2)
  have f15 : 0 ≤ ((8 / 125) - t ^ (3 : ℕ)) * x := by simpa using mul_nonneg (sub_nonneg.2 u3) (pow_nonneg hx 1)
  have f16 : 0 ≤ ((8 / 125) - t ^ (3 : ℕ)) := by simpa using mul_nonneg (sub_nonneg.2 u3) (pow_nonneg hx 0)
  have f17 : 0 ≤ (t ^ (2 : ℕ) - (9 / 64)) * x ^ (6 : ℕ) := by simpa using mul_nonneg (sub_nonneg.2 l2) (pow_nonneg hx 6)
  have f18 : 0 ≤ (t ^ (2 : ℕ) - (9 / 64)) * x ^ (5 : ℕ) := by simpa using mul_nonneg (sub_nonneg.2 l2) (pow_nonneg hx 5)
  have f19 : 0 ≤ (t ^ (2 : ℕ) - (9 / 64)) * x ^ (4 : ℕ) := by simpa using mul_nonneg (sub_nonneg.2 l2) (pow_nonneg hx 4)
  have f20 : 0 ≤ (t ^ (2 : ℕ) - (9 / 64)) * x ^ (3 : ℕ) := by simpa using mul_nonneg (sub_nonneg.2 l2) (pow_nonneg hx 3)
  have f21 : 0 ≤ (t ^ (2 : ℕ) - (9 / 64)) * x ^ (2 : ℕ) := by simpa using mul_nonneg (sub_nonneg.2 l2) (pow_nonneg hx 2)
  have f22 : 0 ≤ (t ^ (2 : ℕ) - (9 / 64)) * x := by simpa using mul_nonneg (sub_nonneg.2 l2) (pow_nonneg hx 1)
  have f23 : 0 ≤ (t ^ (2 : ℕ) - (9 / 64)) := by simpa using mul_nonneg (sub_nonneg.2 l2) (pow_nonneg hx 0)
  have f24 : 0 ≤ (t - (3 / 8)) * x ^ (7 : ℕ) := by simpa using mul_nonneg (sub_nonneg.2 h1) (pow_nonneg hx 7)
  have f25 : 0 ≤ (t - (3 / 8)) * x ^ (6 : ℕ) := by simpa using mul_nonneg (sub_nonneg.2 h1) (pow_nonneg hx 6)
  have f26 : 0 ≤ (t - (3 / 8)) * x ^ (5 : ℕ) := by simpa using mul_nonneg (sub_nonneg.2 h1) (pow_nonneg hx 5)
  have f27 : 0 ≤ (t - (3 / 8)) * x ^ (4 : ℕ) := by simpa using mul_nonneg (sub_nonneg.2 h1) (pow_nonneg hx 4)
  have f28 : 0 ≤ (t - (3 / 8)) * x ^ (3 : ℕ) := by simpa using mul_nonneg (sub_nonneg.2 h1) (pow_nonneg hx 3)
  have f29 : 0 ≤ (t - (3 / 8)) * x ^ (2 : ℕ) := by simpa using mul_nonneg (sub_nonneg.2 h1) (pow_nonneg hx 2)
  have f30 : 0 ≤ (t - (3 / 8)) * x := by simpa using mul_nonneg (sub_nonneg.2 h1) (pow_nonneg hx 1)
  have f31 : 0 ≤ (t - (3 / 8)) := by simpa using mul_nonneg (sub_nonneg.2 h1) (pow_nonneg hx 0)
  have f32 : 0 ≤ x ^ (6 : ℕ) := by positivity
  have f33 : 0 ≤ x ^ (5 : ℕ) := by positivity
  have f34 : 0 ≤ x ^ (4 : ℕ) := by positivity
  have f35 : 0 ≤ x ^ (3 : ℕ) := by positivity
  have f36 : 0 ≤ x ^ (2 : ℕ) := by positivity
  have f37 : 0 ≤ x := by positivity
  have f38 : 0 ≤ 1 := by positivity
  unfold hrlR4 hrlQ4
  linarith only [f0, f1, f2, f3, f4, f5, f6, f7, f8, f9, f10, f11, f12, f13, f14, f15, f16, f17, f18, f19, f20, f21, f22, f23, f24, f25, f26, f27, f28, f29, f30, f31, f32, f33, f34, f35, f36, f37, f38]

/-- `R_5 ≥ Q_5` by monomial comparison in `t`. -/
theorem hrl_RQ5 {t x : ℝ} (h1 : 3 / 8 ≤ t) (h2 : t ≤ 2 / 5) (hx : 0 ≤ x) : hrlQ5 x ≤ hrlR5 t x := by
  obtain ⟨l2, u2, l3, u3, l4, u4, l5, u5, l6, u6⟩ := hrl_tb h1 h2
  have f0 : 0 ≤ ((64 / 15625) - t ^ (6 : ℕ)) * x := by simpa using mul_nonneg (sub_nonneg.2 u6) (pow_nonneg hx 1)
  have f1 : 0 ≤ (t ^ (6 : ℕ) - (729 / 262144)) := by simpa using mul_nonneg (sub_nonneg.2 l6) (pow_nonneg hx 0)
  have f2 : 0 ≤ ((32 / 3125) - t ^ (5 : ℕ)) * x ^ (3 : ℕ) := by simpa using mul_nonneg (sub_nonneg.2 u5) (pow_nonneg hx 3)
  have f3 : 0 ≤ (t ^ (5 : ℕ) - (243 / 32768)) * x ^ (2 : ℕ) := by simpa using mul_nonneg (sub_nonneg.2 l5) (pow_nonneg hx 2)
  have f4 : 0 ≤ (t ^ (5 : ℕ) - (243 / 32768)) * x := by simpa using mul_nonneg (sub_nonneg.2 l5) (pow_nonneg hx 1)
  have f5 : 0 ≤ (t ^ (5 : ℕ) - (243 / 32768)) := by simpa using mul_nonneg (sub_nonneg.2 l5) (pow_nonneg hx 0)
  have f6 : 0 ≤ (t ^ (4 : ℕ) - (81 / 4096)) * x ^ (4 : ℕ) := by simpa using mul_nonneg (sub_nonneg.2 l4) (pow_nonneg hx 4)
  have f7 : 0 ≤ (t ^ (4 : ℕ) - (81 / 4096)) * x ^ (3 : ℕ) := by simpa using mul_nonneg (sub_nonneg.2 l4) (pow_nonneg hx 3)
  have f8 : 0 ≤ ((16 / 625) - t ^ (4 : ℕ)) * x ^ (2 : ℕ) := by simpa using mul_nonneg (sub_nonneg.2 u4) (pow_nonneg hx 2)
  have f9 : 0 ≤ ((16 / 625) - t ^ (4 : ℕ)) * x := by simpa using mul_nonneg (sub_nonneg.2 u4) (pow_nonneg hx 1)
  have f10 : 0 ≤ ((16 / 625) - t ^ (4 : ℕ)) := by simpa using mul_nonneg (sub_nonneg.2 u4) (pow_nonneg hx 0)
  have f11 : 0 ≤ ((8 / 125) - t ^ (3 : ℕ)) * x ^ (5 : ℕ) := by simpa using mul_nonneg (sub_nonneg.2 u3) (pow_nonneg hx 5)
  have f12 : 0 ≤ (t ^ (3 : ℕ) - (27 / 512)) * x ^ (4 : ℕ) := by simpa using mul_nonneg (sub_nonneg.2 l3) (pow_nonneg hx 4)
  have f13 : 0 ≤ (t ^ (3 : ℕ) - (27 / 512)) * x ^ (3 : ℕ) := by simpa using mul_nonneg (sub_nonneg.2 l3) (pow_nonneg hx 3)
  have f14 : 0 ≤ (t ^ (3 : ℕ) - (27 / 512)) * x ^ (2 : ℕ) := by simpa using mul_nonneg (sub_nonneg.2 l3) (pow_nonneg hx 2)
  have f15 : 0 ≤ (t ^ (3 : ℕ) - (27 / 512)) * x := by simpa using mul_nonneg (sub_nonneg.2 l3) (pow_nonneg hx 1)
  have f16 : 0 ≤ (t ^ (3 : ℕ) - (27 / 512)) := by simpa using mul_nonneg (sub_nonneg.2 l3) (pow_nonneg hx 0)
  have f17 : 0 ≤ ((4 / 25) - t ^ (2 : ℕ)) * x ^ (6 : ℕ) := by simpa using mul_nonneg (sub_nonneg.2 u2) (pow_nonneg hx 6)
  have f18 : 0 ≤ ((4 / 25) - t ^ (2 : ℕ)) * x ^ (5 : ℕ) := by simpa using mul_nonneg (sub_nonneg.2 u2) (pow_nonneg hx 5)
  have f19 : 0 ≤ ((4 / 25) - t ^ (2 : ℕ)) * x ^ (4 : ℕ) := by simpa using mul_nonneg (sub_nonneg.2 u2) (pow_nonneg hx 4)
  have f20 : 0 ≤ (t ^ (2 : ℕ) - (9 / 64)) * x ^ (3 : ℕ) := by simpa using mul_nonneg (sub_nonneg.2 l2) (pow_nonneg hx 3)
  have f21 : 0 ≤ (t ^ (2 : ℕ) - (9 / 64)) * x ^ (2 : ℕ) := by simpa using mul_nonneg (sub_nonneg.2 l2) (pow_nonneg hx 2)
  have f22 : 0 ≤ (t ^ (2 : ℕ) - (9 / 64)) * x := by simpa using mul_nonneg (sub_nonneg.2 l2) (pow_nonneg hx 1)
  have f23 : 0 ≤ (t ^ (2 : ℕ) - (9 / 64)) := by simpa using mul_nonneg (sub_nonneg.2 l2) (pow_nonneg hx 0)
  have f24 : 0 ≤ (t - (3 / 8)) * x ^ (6 : ℕ) := by simpa using mul_nonneg (sub_nonneg.2 h1) (pow_nonneg hx 6)
  have f25 : 0 ≤ (t - (3 / 8)) * x ^ (5 : ℕ) := by simpa using mul_nonneg (sub_nonneg.2 h1) (pow_nonneg hx 5)
  have f26 : 0 ≤ (t - (3 / 8)) * x ^ (4 : ℕ) := by simpa using mul_nonneg (sub_nonneg.2 h1) (pow_nonneg hx 4)
  have f27 : 0 ≤ (t - (3 / 8)) * x ^ (3 : ℕ) := by simpa using mul_nonneg (sub_nonneg.2 h1) (pow_nonneg hx 3)
  have f28 : 0 ≤ (t - (3 / 8)) * x ^ (2 : ℕ) := by simpa using mul_nonneg (sub_nonneg.2 h1) (pow_nonneg hx 2)
  have f29 : 0 ≤ ((2 / 5) - t) * x := by simpa using mul_nonneg (sub_nonneg.2 h2) (pow_nonneg hx 1)
  have f30 : 0 ≤ x ^ (6 : ℕ) := by positivity
  have f31 : 0 ≤ x ^ (5 : ℕ) := by positivity
  have f32 : 0 ≤ x ^ (4 : ℕ) := by positivity
  have f33 : 0 ≤ x ^ (3 : ℕ) := by positivity
  have f34 : 0 ≤ x ^ (2 : ℕ) := by positivity
  have f35 : 0 ≤ x := by positivity
  have f36 : 0 ≤ 1 := by positivity
  unfold hrlR5 hrlQ5
  linarith only [f0, f1, f2, f3, f4, f5, f6, f7, f8, f9, f10, f11, f12, f13, f14, f15, f16, f17, f18, f19, f20, f21, f22, f23, f24, f25, f26, f27, f28, f29, f30, f31, f32, f33, f34, f35, f36]

/-- `R_6 ≥ Q_6` by monomial comparison in `t`. -/
theorem hrl_RQ6 {t x : ℝ} (h1 : 3 / 8 ≤ t) (h2 : t ≤ 2 / 5) (hx : 0 ≤ x) : hrlQ6 x ≤ hrlR6 t x := by
  obtain ⟨l2, u2, l3, u3, l4, u4, l5, u5, l6, u6⟩ := hrl_tb h1 h2
  have f0 : 0 ≤ (t ^ (6 : ℕ) - (729 / 262144)) := by simpa using mul_nonneg (sub_nonneg.2 l6) (pow_nonneg hx 0)
  have f1 : 0 ≤ (t ^ (5 : ℕ) - (243 / 32768)) * x ^ (2 : ℕ) := by simpa using mul_nonneg (sub_nonneg.2 l5) (pow_nonneg hx 2)
  have f2 : 0 ≤ (t ^ (5 : ℕ) - (243 / 32768)) * x := by simpa using mul_nonneg (sub_nonneg.2 l5) (pow_nonneg hx 1)
  have f3 : 0 ≤ (t ^ (5 : ℕ) - (243 / 32768)) := by simpa using mul_nonneg (sub_nonneg.2 l5) (pow_nonneg hx 0)
  have f4 : 0 ≤ ((16 / 625) - t ^ (4 : ℕ)) * x ^ (3 : ℕ) := by simpa using mul_nonneg (sub_nonneg.2 u4) (pow_nonneg hx 3)
  have f5 : 0 ≤ ((16 / 625) - t ^ (4 : ℕ)) * x ^ (2 : ℕ) := by simpa using mul_nonneg (sub_nonneg.2 u4) (pow_nonneg hx 2)
  have f6 : 0 ≤ ((16 / 625) - t ^ (4 : ℕ)) * x := by simpa using mul_nonneg (sub_nonneg.2 u4) (pow_nonneg hx 1)
  have f7 : 0 ≤ ((16 / 625) - t ^ (4 : ℕ)) := by simpa using mul_nonneg (sub_nonneg.2 u4) (pow_nonneg hx 0)
  have f8 : 0 ≤ (t ^ (3 : ℕ) - (27 / 512)) * x ^ (4 : ℕ) := by simpa using mul_nonneg (sub_nonneg.2 l3) (pow_nonneg hx 4)
  have f9 : 0 ≤ (t ^ (3 : ℕ) - (27 / 512)) * x ^ (3 : ℕ) := by simpa using mul_nonneg (sub_nonneg.2 l3) (pow_nonneg hx 3)
  have f10 : 0 ≤ (t ^ (3 : ℕ) - (27 / 512)) * x ^ (2 : ℕ) := by simpa using mul_nonneg (sub_nonneg.2 l3) (pow_nonneg hx 2)
  have f11 : 0 ≤ (t ^ (3 : ℕ) - (27 / 512)) * x := by simpa using mul_nonneg (sub_nonneg.2 l3) (pow_nonneg hx 1)
  have f12 : 0 ≤ (t ^ (3 : ℕ) - (27 / 512)) := by simpa using mul_nonneg (sub_nonneg.2 l3) (pow_nonneg hx 0)
  have f13 : 0 ≤ ((4 / 25) - t ^ (2 : ℕ)) * x ^ (5 : ℕ) := by simpa using mul_nonneg (sub_nonneg.2 u2) (pow_nonneg hx 5)
  have f14 : 0 ≤ ((4 / 25) - t ^ (2 : ℕ)) * x ^ (4 : ℕ) := by simpa using mul_nonneg (sub_nonneg.2 u2) (pow_nonneg hx 4)
  have f15 : 0 ≤ ((4 / 25) - t ^ (2 : ℕ)) * x ^ (3 : ℕ) := by simpa using mul_nonneg (sub_nonneg.2 u2) (pow_nonneg hx 3)
  have f16 : 0 ≤ (t ^ (2 : ℕ) - (9 / 64)) * x ^ (2 : ℕ) := by simpa using mul_nonneg (sub_nonneg.2 l2) (pow_nonneg hx 2)
  have f17 : 0 ≤ (t ^ (2 : ℕ) - (9 / 64)) * x := by simpa using mul_nonneg (sub_nonneg.2 l2) (pow_nonneg hx 1)
  have f18 : 0 ≤ (t - (3 / 8)) * x ^ (6 : ℕ) := by simpa using mul_nonneg (sub_nonneg.2 h1) (pow_nonneg hx 6)
  have f19 : 0 ≤ (t - (3 / 8)) * x ^ (5 : ℕ) := by simpa using mul_nonneg (sub_nonneg.2 h1) (pow_nonneg hx 5)
  have f20 : 0 ≤ (t - (3 / 8)) * x ^ (4 : ℕ) := by simpa using mul_nonneg (sub_nonneg.2 h1) (pow_nonneg hx 4)
  have f21 : 0 ≤ ((2 / 5) - t) * x ^ (3 : ℕ) := by simpa using mul_nonneg (sub_nonneg.2 h2) (pow_nonneg hx 3)
  have f22 : 0 ≤ ((2 / 5) - t) * x ^ (2 : ℕ) := by simpa using mul_nonneg (sub_nonneg.2 h2) (pow_nonneg hx 2)
  have f23 : 0 ≤ x ^ (6 : ℕ) := by positivity
  have f24 : 0 ≤ x ^ (5 : ℕ) := by positivity
  have f25 : 0 ≤ x ^ (4 : ℕ) := by positivity
  have f26 : 0 ≤ x ^ (3 : ℕ) := by positivity
  have f27 : 0 ≤ x ^ (2 : ℕ) := by positivity
  have f28 : 0 ≤ x := by positivity
  have f29 : 0 ≤ 1 := by positivity
  unfold hrlR6 hrlQ6
  linarith only [f0, f1, f2, f3, f4, f5, f6, f7, f8, f9, f10, f11, f12, f13, f14, f15, f16, f17, f18, f19, f20, f21, f22, f23, f24, f25, f26, f27, f28, f29]

/-- `∂_xR₀ ≥ L_x` by monomial comparison in `t`. -/
theorem hrl_DR0_ge {t x : ℝ} (h1 : 3 / 8 ≤ t) (h2 : t ≤ 2 / 5) (hx : 0 ≤ x) : hrlLx x ≤ hrlDR0 t x := by
  obtain ⟨l2, u2, l3, u3, l4, u4, l5, u5, l6, u6⟩ := hrl_tb h1 h2
  have f0 : 0 ≤ ((64 / 15625) - t ^ (6 : ℕ)) := by simpa using mul_nonneg (sub_nonneg.2 u6) (pow_nonneg hx 0)
  have f1 : 0 ≤ (t ^ (5 : ℕ) - (243 / 32768)) * x := by simpa using mul_nonneg (sub_nonneg.2 l5) (pow_nonneg hx 1)
  have f2 : 0 ≤ (t ^ (5 : ℕ) - (243 / 32768)) := by simpa using mul_nonneg (sub_nonneg.2 l5) (pow_nonneg hx 0)
  have f3 : 0 ≤ (t ^ (4 : ℕ) - (81 / 4096)) * x ^ (2 : ℕ) := by simpa using mul_nonneg (sub_nonneg.2 l4) (pow_nonneg hx 2)
  have f4 : 0 ≤ ((16 / 625) - t ^ (4 : ℕ)) * x := by simpa using mul_nonneg (sub_nonneg.2 u4) (pow_nonneg hx 1)
  have f5 : 0 ≤ ((16 / 625) - t ^ (4 : ℕ)) := by simpa using mul_nonneg (sub_nonneg.2 u4) (pow_nonneg hx 0)
  have f6 : 0 ≤ ((8 / 125) - t ^ (3 : ℕ)) * x ^ (3 : ℕ) := by simpa using mul_nonneg (sub_nonneg.2 u3) (pow_nonneg hx 3)
  have f7 : 0 ≤ ((8 / 125) - t ^ (3 : ℕ)) * x ^ (2 : ℕ) := by simpa using mul_nonneg (sub_nonneg.2 u3) (pow_nonneg hx 2)
  have f8 : 0 ≤ (t ^ (3 : ℕ) - (27 / 512)) * x := by simpa using mul_nonneg (sub_nonneg.2 l3) (pow_nonneg hx 1)
  have f9 : 0 ≤ (t ^ (3 : ℕ) - (27 / 512)) := by simpa using mul_nonneg (sub_nonneg.2 l3) (pow_nonneg hx 0)
  have f10 : 0 ≤ (t ^ (2 : ℕ) - (9 / 64)) * x ^ (4 : ℕ) := by simpa using mul_nonneg (sub_nonneg.2 l2) (pow_nonneg hx 4)
  have f11 : 0 ≤ ((4 / 25) - t ^ (2 : ℕ)) * x ^ (3 : ℕ) := by simpa using mul_nonneg (sub_nonneg.2 u2) (pow_nonneg hx 3)
  have f12 : 0 ≤ ((4 / 25) - t ^ (2 : ℕ)) * x ^ (2 : ℕ) := by simpa using mul_nonneg (sub_nonneg.2 u2) (pow_nonneg hx 2)
  have f13 : 0 ≤ ((4 / 25) - t ^ (2 : ℕ)) * x := by simpa using mul_nonneg (sub_nonneg.2 u2) (pow_nonneg hx 1)
  have f14 : 0 ≤ ((4 / 25) - t ^ (2 : ℕ)) := by simpa using mul_nonneg (sub_nonneg.2 u2) (pow_nonneg hx 0)
  have f15 : 0 ≤ (t - (3 / 8)) * x ^ (5 : ℕ) := by simpa using mul_nonneg (sub_nonneg.2 h1) (pow_nonneg hx 5)
  have f16 : 0 ≤ (t - (3 / 8)) * x ^ (4 : ℕ) := by simpa using mul_nonneg (sub_nonneg.2 h1) (pow_nonneg hx 4)
  have f17 : 0 ≤ (t - (3 / 8)) * x ^ (3 : ℕ) := by simpa using mul_nonneg (sub_nonneg.2 h1) (pow_nonneg hx 3)
  have f18 : 0 ≤ (t - (3 / 8)) * x ^ (2 : ℕ) := by simpa using mul_nonneg (sub_nonneg.2 h1) (pow_nonneg hx 2)
  have f19 : 0 ≤ (t - (3 / 8)) * x := by simpa using mul_nonneg (sub_nonneg.2 h1) (pow_nonneg hx 1)
  have f20 : 0 ≤ (t - (3 / 8)) := by simpa using mul_nonneg (sub_nonneg.2 h1) (pow_nonneg hx 0)
  have f21 : 0 ≤ x ^ (4 : ℕ) := by positivity
  have f22 : 0 ≤ x ^ (3 : ℕ) := by positivity
  have f23 : 0 ≤ x ^ (2 : ℕ) := by positivity
  have f24 : 0 ≤ x := by positivity
  have f25 : 0 ≤ 1 := by positivity
  unfold hrlDR0 hrlLx
  linarith only [f0, f1, f2, f3, f4, f5, f6, f7, f8, f9, f10, f11, f12, f13, f14, f15, f16, f17, f18, f19, f20, f21, f22, f23, f24, f25]

/-- `Q_1 ≥ 1000U_1` by coefficient rounding. -/
theorem hrl_QU1 {x : ℝ} (hx : 0 ≤ x) : 1000 * hrlU1 x ≤ hrlQ1 x := by
  have e : hrlQ1 x - (1000 * hrlU1 x) = 820 + 954 * x + 327 * x ^ (2 : ℕ) + 709 * x ^ (3 : ℕ) + 186 * x ^ (4 : ℕ) + 680 * x ^ (5 : ℕ) + 717 * x ^ (6 : ℕ) + 176 * x ^ (7 : ℕ) := by unfold hrlQ1 hrlU1; ring
  have : 0 ≤ 820 + 954 * x + 327 * x ^ (2 : ℕ) + 709 * x ^ (3 : ℕ) + 186 * x ^ (4 : ℕ) + 680 * x ^ (5 : ℕ) + 717 * x ^ (6 : ℕ) + 176 * x ^ (7 : ℕ) := by positivity
  linarith

/-- `Q_2 ≥ 1000U_2` by coefficient rounding. -/
theorem hrl_QU2 {x : ℝ} (hx : 0 ≤ x) : 1000 * hrlU2 x ≤ hrlQ2 x := by
  have e : hrlQ2 x - (1000 * hrlU2 x) = 553 + 270 * x + 96 * x ^ (2 : ℕ) + 621 * x ^ (3 : ℕ) + 291 * x ^ (4 : ℕ) + 519 * x ^ (5 : ℕ) + 172 * x ^ (6 : ℕ) + 864 * x ^ (7 : ℕ) := by unfold hrlQ2 hrlU2; ring
  have : 0 ≤ 553 + 270 * x + 96 * x ^ (2 : ℕ) + 621 * x ^ (3 : ℕ) + 291 * x ^ (4 : ℕ) + 519 * x ^ (5 : ℕ) + 172 * x ^ (6 : ℕ) + 864 * x ^ (7 : ℕ) := by positivity
  linarith

/-- `Q_3 ≥ 1000U_3` by coefficient rounding. -/
theorem hrl_QU3 {x : ℝ} (hx : 0 ≤ x) : 1000 * hrlU3 x ≤ hrlQ3 x := by
  have e : hrlQ3 x - (1000 * hrlU3 x) = 958 + 567 * x + 229 * x ^ (2 : ℕ) + 883 * x ^ (3 : ℕ) + 427 * x ^ (4 : ℕ) + 759 * x ^ (5 : ℕ) + 864 * x ^ (6 : ℕ) + 792 * x ^ (7 : ℕ) := by unfold hrlQ3 hrlU3; ring
  have : 0 ≤ 958 + 567 * x + 229 * x ^ (2 : ℕ) + 883 * x ^ (3 : ℕ) + 427 * x ^ (4 : ℕ) + 759 * x ^ (5 : ℕ) + 864 * x ^ (6 : ℕ) + 792 * x ^ (7 : ℕ) := by positivity
  linarith

/-- `Q_4 ≥ 1000U_4` by coefficient rounding. -/
theorem hrl_QU4 {x : ℝ} (hx : 0 ≤ x) : 1000 * hrlU4 x ≤ hrlQ4 x := by
  have e : hrlQ4 x - (1000 * hrlU4 x) = 408 + 644 * x + 437 * x ^ (2 : ℕ) + 147 * x ^ (3 : ℕ) + 90 * x ^ (4 : ℕ) + 715 * x ^ (5 : ℕ) + 901 * x ^ (6 : ℕ) + 504 * x ^ (7 : ℕ) := by unfold hrlQ4 hrlU4; ring
  have : 0 ≤ 408 + 644 * x + 437 * x ^ (2 : ℕ) + 147 * x ^ (3 : ℕ) + 90 * x ^ (4 : ℕ) + 715 * x ^ (5 : ℕ) + 901 * x ^ (6 : ℕ) + 504 * x ^ (7 : ℕ) := by positivity
  linarith

/-- `Q_5 ≥ 1000U_5 - 10000` by coefficient rounding. -/
theorem hrl_QU5 {x : ℝ} (hx : 0 ≤ x) : 1000 * hrlU5 x - 10000 ≤ hrlQ5 x := by
  have e : hrlQ5 x - (1000 * hrlU5 x - 10000) = 516 + 239 * x + 842 * x ^ (2 : ℕ) + 963 * x ^ (3 : ℕ) + 951 * x ^ (4 : ℕ) + 775 * x ^ (5 : ℕ) + 892 * x ^ (6 : ℕ) + 380 * x ^ (7 : ℕ) := by unfold hrlQ5 hrlU5; ring
  have : 0 ≤ 516 + 239 * x + 842 * x ^ (2 : ℕ) + 963 * x ^ (3 : ℕ) + 951 * x ^ (4 : ℕ) + 775 * x ^ (5 : ℕ) + 892 * x ^ (6 : ℕ) + 380 * x ^ (7 : ℕ) := by positivity
  linarith

/-- `Q_6 ≥ 1000U_6 - 10000` by coefficient rounding. -/
theorem hrl_QU6 {x : ℝ} (hx : 0 ≤ x) : 1000 * hrlU6 x - 10000 ≤ hrlQ6 x := by
  have e : hrlQ6 x - (1000 * hrlU6 x - 10000) = 589 + 872 * x + 853 * x ^ (2 : ℕ) + 955 * x ^ (3 : ℕ) + 449 * x ^ (4 : ℕ) + 351 * x ^ (5 : ℕ) + 902 * x ^ (6 : ℕ) + 320 * x ^ (7 : ℕ) := by unfold hrlQ6 hrlU6; ring
  have : 0 ≤ 589 + 872 * x + 853 * x ^ (2 : ℕ) + 955 * x ^ (3 : ℕ) + 449 * x ^ (4 : ℕ) + 351 * x ^ (5 : ℕ) + 902 * x ^ (6 : ℕ) + 320 * x ^ (7 : ℕ) := by positivity
  linarith

/-- `B_0 ≥ 10Z_0` by coefficient rounding. -/
theorem hrl_BZ0 {x : ℝ} (hx : 0 ≤ x) : 10 * hrlZ0 x ≤ hrlBb0 x := by
  have e : hrlBb0 x - (10 * hrlZ0 x) = (123958 / 15625) + (66558 / 15625) * x + (8868 / 15625) * x ^ (2 : ℕ) + (15506 / 3125) * x ^ (3 : ℕ) + (156 / 125) * x ^ (4 : ℕ) + (716 / 125) * x ^ (5 : ℕ) + (84 / 25) * x ^ (6 : ℕ) := by unfold hrlBb0 hrlZ0; ring
  have : 0 ≤ (123958 / 15625) + (66558 / 15625) * x + (8868 / 15625) * x ^ (2 : ℕ) + (15506 / 3125) * x ^ (3 : ℕ) + (156 / 125) * x ^ (4 : ℕ) + (716 / 125) * x ^ (5 : ℕ) + (84 / 25) * x ^ (6 : ℕ) := by positivity
  linarith

/-- `B_1 ≥ 10Z_1` by coefficient rounding. -/
theorem hrl_BZ1 {x : ℝ} (hx : 0 ≤ x) : 10 * hrlZ1 x ≤ hrlBb1 x := by
  have e : hrlBb1 x - (10 * hrlZ1 x) = (49132 / 15625) + (133404 / 15625) * x + (70546 / 15625) * x ^ (2 : ℕ) + (10226 / 3125) * x ^ (3 : ℕ) + (4314 / 625) * x ^ (4 : ℕ) + (2426 / 625) * x ^ (5 : ℕ) + (164 / 25) * x ^ (6 : ℕ) + (24 / 25) * x ^ (7 : ℕ) := by unfold hrlBb1 hrlZ1; ring
  have : 0 ≤ (49132 / 15625) + (133404 / 15625) * x + (70546 / 15625) * x ^ (2 : ℕ) + (10226 / 3125) * x ^ (3 : ℕ) + (4314 / 625) * x ^ (4 : ℕ) + (2426 / 625) * x ^ (5 : ℕ) + (164 / 25) * x ^ (6 : ℕ) + (24 / 25) * x ^ (7 : ℕ) := by positivity
  linarith

/-- `B_2 ≥ 10Z_2` by coefficient rounding. -/
theorem hrl_BZ2 {x : ℝ} (hx : 0 ≤ x) : 10 * hrlZ2 x ≤ hrlBb2 x := by
  have e : hrlBb2 x - (10 * hrlZ2 x) = (89266 / 15625) + (28668 / 3125) * x + (47424 / 15625) * x ^ (2 : ℕ) + (25876 / 3125) * x ^ (3 : ℕ) + (502 / 625) * x ^ (4 : ℕ) + (5404 / 625) * x ^ (5 : ℕ) + (1208 / 125) * x ^ (6 : ℕ) + (218 / 25) * x ^ (7 : ℕ) + 6 * x ^ (8 : ℕ) := by unfold hrlBb2 hrlZ2; ring
  have : 0 ≤ (89266 / 15625) + (28668 / 3125) * x + (47424 / 15625) * x ^ (2 : ℕ) + (25876 / 3125) * x ^ (3 : ℕ) + (502 / 625) * x ^ (4 : ℕ) + (5404 / 625) * x ^ (5 : ℕ) + (1208 / 125) * x ^ (6 : ℕ) + (218 / 25) * x ^ (7 : ℕ) + 6 * x ^ (8 : ℕ) := by positivity
  linarith

/-- `B_3 ≥ 10Z_3` by coefficient rounding. -/
theorem hrl_BZ3 {x : ℝ} (hx : 0 ≤ x) : 10 * hrlZ3 x ≤ hrlBb3 x := by
  have e : hrlBb3 x - (10 * hrlZ3 x) = (130604 / 15625) + (1034 / 625) * x + (130436 / 15625) * x ^ (2 : ℕ) + (8348 / 3125) * x ^ (3 : ℕ) + (4148 / 625) * x ^ (4 : ℕ) + (1298 / 625) * x ^ (5 : ℕ) + (366 / 125) * x ^ (6 : ℕ) + (136 / 25) * x ^ (7 : ℕ) + 6 * x ^ (8 : ℕ) := by unfold hrlBb3 hrlZ3; ring
  have : 0 ≤ (130604 / 15625) + (1034 / 625) * x + (130436 / 15625) * x ^ (2 : ℕ) + (8348 / 3125) * x ^ (3 : ℕ) + (4148 / 625) * x ^ (4 : ℕ) + (1298 / 625) * x ^ (5 : ℕ) + (366 / 125) * x ^ (6 : ℕ) + (136 / 25) * x ^ (7 : ℕ) + 6 * x ^ (8 : ℕ) := by positivity
  linarith

/-- `B_4 ≥ 10Z_4` by coefficient rounding. -/
theorem hrl_BZ4 {x : ℝ} (hx : 0 ≤ x) : 10 * hrlZ4 x ≤ hrlBb4 x := by
  have e : hrlBb4 x - (10 * hrlZ4 x) = (107326 / 15625) + (14508 / 3125) * x + (59894 / 15625) * x ^ (2 : ℕ) + (13096 / 3125) * x ^ (3 : ℕ) + (2936 / 625) * x ^ (4 : ℕ) + (1486 / 625) * x ^ (5 : ℕ) + (94 / 25) * x ^ (6 : ℕ) + (164 / 25) * x ^ (7 : ℕ) + 4 * x ^ (8 : ℕ) := by unfold hrlBb4 hrlZ4; ring
  have : 0 ≤ (107326 / 15625) + (14508 / 3125) * x + (59894 / 15625) * x ^ (2 : ℕ) + (13096 / 3125) * x ^ (3 : ℕ) + (2936 / 625) * x ^ (4 : ℕ) + (1486 / 625) * x ^ (5 : ℕ) + (94 / 25) * x ^ (6 : ℕ) + (164 / 25) * x ^ (7 : ℕ) + 4 * x ^ (8 : ℕ) := by positivity
  linarith

/-- `B_5 ≥ 10Z_5` by coefficient rounding. -/
theorem hrl_BZ5 {x : ℝ} (hx : 0 ≤ x) : 10 * hrlZ5 x ≤ hrlBb5 x := by
  have e : hrlBb5 x - (10 * hrlZ5 x) = (46192 / 15625) + (9018 / 15625) * x + (137954 / 15625) * x ^ (2 : ℕ) + (22828 / 3125) * x ^ (3 : ℕ) + (916 / 625) * x ^ (4 : ℕ) + (3568 / 625) * x ^ (5 : ℕ) + (702 / 125) * x ^ (6 : ℕ) + (34 / 5) * x ^ (7 : ℕ) + 2 * x ^ (8 : ℕ) := by unfold hrlBb5 hrlZ5; ring
  have : 0 ≤ (46192 / 15625) + (9018 / 15625) * x + (137954 / 15625) * x ^ (2 : ℕ) + (22828 / 3125) * x ^ (3 : ℕ) + (916 / 625) * x ^ (4 : ℕ) + (3568 / 625) * x ^ (5 : ℕ) + (702 / 125) * x ^ (6 : ℕ) + (34 / 5) * x ^ (7 : ℕ) + 2 * x ^ (8 : ℕ) := by positivity
  linarith

/-- `B_6 ≥ 10Z_6 - 7000` by coefficient rounding. -/
theorem hrl_BZ6 {x : ℝ} (hx : 0 ≤ x) : 10 * hrlZ6 x - 7000 ≤ hrlBb6 x := by
  have e : hrlBb6 x - (10 * hrlZ6 x - 7000) = (71828 / 15625) + (113834 / 15625) * x + (76 / 125) * x ^ (2 : ℕ) + (12274 / 3125) * x ^ (3 : ℕ) + (936 / 125) * x ^ (4 : ℕ) + (786 / 125) * x ^ (5 : ℕ) + (26 / 25) * x ^ (6 : ℕ) + (34 / 5) * x ^ (7 : ℕ) + 2 * x ^ (8 : ℕ) := by unfold hrlBb6 hrlZ6; ring
  have : 0 ≤ (71828 / 15625) + (113834 / 15625) * x + (76 / 125) * x ^ (2 : ℕ) + (12274 / 3125) * x ^ (3 : ℕ) + (936 / 125) * x ^ (4 : ℕ) + (786 / 125) * x ^ (5 : ℕ) + (26 / 25) * x ^ (6 : ℕ) + (34 / 5) * x ^ (7 : ℕ) + 2 * x ^ (8 : ℕ) := by positivity
  linarith

/-- `R₀(t, 1/5) ≥ 1000K₀(t)` by coefficient rounding. -/
theorem hrl_R0K {t : ℝ} (hx : 0 ≤ t) : 1000 * hrlK0 t ≤ hrlR0 t (1 / 5) := by
  have e : hrlR0 t (1 / 5) - (1000 * hrlK0 t) = (1829704 / 15625) + (8345009 / 15625) * t + (845478 / 3125) * t ^ (2 : ℕ) + (88692 / 125) * t ^ (3 : ℕ) + (7496 / 25) * t ^ (4 : ℕ) + (3798 / 25) * t ^ (5 : ℕ) + (1264 / 5) * t ^ (6 : ℕ) := by unfold hrlR0 hrlK0; ring
  have : 0 ≤ (1829704 / 15625) + (8345009 / 15625) * t + (845478 / 3125) * t ^ (2 : ℕ) + (88692 / 125) * t ^ (3 : ℕ) + (7496 / 25) * t ^ (4 : ℕ) + (3798 / 25) * t ^ (5 : ℕ) + (1264 / 5) * t ^ (6 : ℕ) := by positivity
  linarith

/-- `U_1 ≥ 0` on `[7/30, 3/7]`, by monomials in `z = x - 1/5`. -/
theorem hrl_U1_lb {x : ℝ} (h1 : 7 / 30 ≤ x) (h2 : x ≤ 3 / 7) : 0 ≤ hrlU1 x := by
  obtain ⟨z, rfl⟩ : ∃ z, x = z + 1 / 5 := ⟨x - 1 / 5, by ring⟩
  have hz0 : 1 / 30 ≤ z := by linarith
  have hz1 : z ≤ 8 / 35 := by linarith
  obtain ⟨l2, u2, l3, u3, l4, u4, l5, u5, l6, u6, l7, u7, l8, u8⟩ := hrl_zb hz0 hz1
  have e : hrlU1 (z + 1 / 5) = (13074794 / 78125) + (27232458 / 15625) * z ^ (1 : ℕ) + (12703874 / 3125) * z ^ (2 : ℕ) + (409108 / 125) * z ^ (3 : ℕ) + (10083 / 25) * z ^ (4 : ℕ) + (-(11951 / 25) : ℝ) * z ^ (5 : ℕ) + (-(542 / 5) : ℝ) * z ^ (6 : ℕ) + (-6 : ℝ) * z ^ (7 : ℕ) := by unfold hrlU1; ring
  rw [e]; linarith only [hz0, l2, l3, l4, u5, u6, u7]

/-- `U_2 ≥ 0` on `[7/30, 3/7]`, by monomials in `z = x - 1/5`. -/
theorem hrl_U2_lb {x : ℝ} (h1 : 7 / 30 ≤ x) (h2 : x ≤ 3 / 7) : 0 ≤ hrlU2 x := by
  obtain ⟨z, rfl⟩ : ∃ z, x = z + 1 / 5 := ⟨x - 1 / 5, by ring⟩
  have hz0 : 1 / 30 ≤ z := by linarith
  have hz1 : z ≤ 8 / 35 := by linarith
  obtain ⟨l2, u2, l3, u3, l4, u4, l5, u5, l6, u6, l7, u7, l8, u8⟩ := hrl_zb hz0 hz1
  have e : hrlU2 (z + 1 / 5) = (46231412 / 78125) + (78784479 / 15625) * z ^ (1 : ℕ) + (33405647 / 3125) * z ^ (2 : ℕ) + (942319 / 125) * z ^ (3 : ℕ) + (-(3861 / 25) : ℝ) * z ^ (4 : ℕ) + (-(53548 / 25) : ℝ) * z ^ (5 : ℕ) + (-(3421 / 5) : ℝ) * z ^ (6 : ℕ) + (-68 : ℝ) * z ^ (7 : ℕ) := by unfold hrlU2; ring
  rw [e]; linarith only [hz0, l2, l3, u4, u5, u6, u7]

/-- `U_3 ≥ 0` on `[7/30, 3/7]`, by monomials in `z = x - 1/5`. -/
theorem hrl_U3_lb {x : ℝ} (h1 : 7 / 30 ≤ x) (h2 : x ≤ 3 / 7) : 0 ≤ hrlU3 x := by
  obtain ⟨z, rfl⟩ : ∃ z, x = z + 1 / 5 := ⟨x - 1 / 5, by ring⟩
  have hz0 : 1 / 30 ≤ z := by linarith
  have hz1 : z ≤ 8 / 35 := by linarith
  obtain ⟨l2, u2, l3, u3, l4, u4, l5, u5, l6, u6, l7, u7, l8, u8⟩ := hrl_zb hz0 hz1
  have e : hrlU3 (z + 1 / 5) = (49677306 / 78125) + (77773972 / 15625) * z ^ (1 : ℕ) + (31355631 / 3125) * z ^ (2 : ℕ) + (806257 / 125) * z ^ (3 : ℕ) + (-(31988 / 25) : ℝ) * z ^ (4 : ℕ) + (-(78624 / 25) : ℝ) * z ^ (5 : ℕ) + (-(5878 / 5) : ℝ) * z ^ (6 : ℕ) + (-139 : ℝ) * z ^ (7 : ℕ) := by unfold hrlU3; ring
  rw [e]; linarith only [hz0, l2, l3, u4, u5, u6, u7]

/-- `U_4 ≥ 288` on `[7/30, 3/7]`, by monomials in `z = x - 1/5`. -/
theorem hrl_U4_lb {x : ℝ} (h1 : 7 / 30 ≤ x) (h2 : x ≤ 3 / 7) : 288 ≤ hrlU4 x := by
  obtain ⟨z, rfl⟩ : ∃ z, x = z + 1 / 5 := ⟨x - 1 / 5, by ring⟩
  have hz0 : 1 / 30 ≤ z := by linarith
  have hz1 : z ≤ 8 / 35 := by linarith
  obtain ⟨l2, u2, l3, u3, l4, u4, l5, u5, l6, u6, l7, u7, l8, u8⟩ := hrl_zb hz0 hz1
  have e : hrlU4 (z + 1 / 5) = (17556558 / 78125) + (29993316 / 15625) * z ^ (1 : ℕ) + (11905353 / 3125) * z ^ (2 : ℕ) + (266111 / 125) * z ^ (3 : ℕ) + (-(26779 / 25) : ℝ) * z ^ (4 : ℕ) + (-(46632 / 25) : ℝ) * z ^ (5 : ℕ) + (-(4009 / 5) : ℝ) * z ^ (6 : ℕ) + (-107 : ℝ) * z ^ (7 : ℕ) := by unfold hrlU4; ring
  rw [e]; linarith only [hz0, l2, l3, u4, u5, u6, u7]

/-- `U_5 ≥ 0` on `[7/30, 3/7]`, by monomials in `z = x - 1/5`. -/
theorem hrl_U5_lb {x : ℝ} (h1 : 7 / 30 ≤ x) (h2 : x ≤ 3 / 7) : 0 ≤ hrlU5 x := by
  obtain ⟨z, rfl⟩ : ∃ z, x = z + 1 / 5 := ⟨x - 1 / 5, by ring⟩
  have hz0 : 1 / 30 ≤ z := by linarith
  have hz1 : z ≤ 8 / 35 := by linarith
  obtain ⟨l2, u2, l3, u3, l4, u4, l5, u5, l6, u6, l7, u7, l8, u8⟩ := hrl_zb hz0 hz1
  have e : hrlU5 (z + 1 / 5) = (152838 / 78125) + (2690771 / 15625) * z ^ (1 : ℕ) + (1341253 / 3125) * z ^ (2 : ℕ) + (20681 / 125) * z ^ (3 : ℕ) + (-(7564 / 25) : ℝ) * z ^ (4 : ℕ) + (-(10827 / 25) : ℝ) * z ^ (5 : ℕ) + (-(1079 / 5) : ℝ) * z ^ (6 : ℕ) + (-32 : ℝ) * z ^ (7 : ℕ) := by unfold hrlU5; ring
  rw [e]; linarith only [hz0, l2, l3, u4, u5, u6, u7]

/-- `U_6 ≥ 0` on `[7/30, 3/7]`, by monomials in `z = x - 1/5`. -/
theorem hrl_U6_lb {x : ℝ} (h1 : 7 / 30 ≤ x) (h2 : x ≤ 3 / 7) : 0 ≤ hrlU6 x := by
  obtain ⟨z, rfl⟩ : ∃ z, x = z + 1 / 5 := ⟨x - 1 / 5, by ring⟩
  have hz0 : 1 / 30 ≤ z := by linarith
  have hz1 : z ≤ 8 / 35 := by linarith
  obtain ⟨l2, u2, l3, u3, l4, u4, l5, u5, l6, u6, l7, u7, l8, u8⟩ := hrl_zb hz0 hz1
  have e : hrlU6 (z + 1 / 5) = (169639 / 78125) + (-(131317 / 15625) : ℝ) * z ^ (1 : ℕ) + (10204 / 3125) * z ^ (2 : ℕ) + (-(147 / 125) : ℝ) * z ^ (3 : ℕ) + (138 / 25) * z ^ (4 : ℕ) + (69 / 25) * z ^ (5 : ℕ) + (-(17 / 5) : ℝ) * z ^ (6 : ℕ) + (-1 : ℝ) * z ^ (7 : ℕ) := by unfold hrlU6; ring
  rw [e]; linarith only [hz1, l2, l4, l5, u3, u6, u7]

/-- `Z_0 > 0` on `[7/30, 3/7]`, by monomials in `z = x - 1/5`. -/
theorem hrl_Z0_lb {x : ℝ} (h1 : 7 / 30 ≤ x) (h2 : x ≤ 3 / 7) : 0 < hrlZ0 x := by
  obtain ⟨z, rfl⟩ : ∃ z, x = z + 1 / 5 := ⟨x - 1 / 5, by ring⟩
  have hz0 : 1 / 30 ≤ z := by linarith
  have hz1 : z ≤ 8 / 35 := by linarith
  obtain ⟨l2, u2, l3, u3, l4, u4, l5, u5, l6, u6, l7, u7, l8, u8⟩ := hrl_zb hz0 hz1
  have e : hrlZ0 (z + 1 / 5) = (615373 / 15625) + (1985618 / 3125) * z ^ (1 : ℕ) + (851489 / 125) * z ^ (2 : ℕ) + (345737 / 25) * z ^ (3 : ℕ) + (48894 / 5) * z ^ (4 : ℕ) + (12438 / 5) * z ^ (5 : ℕ) + 78 * z ^ (6 : ℕ) := by unfold hrlZ0; ring
  rw [e]; linarith only [hz0, l2, l3, l4, l5, l6]

/-- `Z_1 ≥ 0` on `[7/30, 3/7]`, by monomials in `z = x - 1/5`. -/
theorem hrl_Z1_lb {x : ℝ} (h1 : 7 / 30 ≤ x) (h2 : x ≤ 3 / 7) : 0 ≤ hrlZ1 x := by
  obtain ⟨z, rfl⟩ : ∃ z, x = z + 1 / 5 := ⟨x - 1 / 5, by ring⟩
  have hz0 : 1 / 30 ≤ z := by linarith
  have hz1 : z ≤ 8 / 35 := by linarith
  obtain ⟨l2, u2, l3, u3, l4, u4, l5, u5, l6, u6, l7, u7, l8, u8⟩ := hrl_zb hz0 hz1
  have e : hrlZ1 (z + 1 / 5) = (376426 / 78125) + (179334357 / 15625) * z ^ (1 : ℕ) + (235900596 / 3125) * z ^ (2 : ℕ) + (17596732 / 125) * z ^ (3 : ℕ) + (2646432 / 25) * z ^ (4 : ℕ) + (796321 / 25) * z ^ (5 : ℕ) + (11482 / 5) * z ^ (6 : ℕ) + 76 * z ^ (7 : ℕ) := by unfold hrlZ1; ring
  rw [e]; linarith only [hz0, l2, l3, l4, l5, l6, l7]

/-- `Z_2 ≥ 0` on `[7/30, 3/7]`, by monomials in `z = x - 1/5`. -/
theorem hrl_Z2_lb {x : ℝ} (h1 : 7 / 30 ≤ x) (h2 : x ≤ 3 / 7) : 0 ≤ hrlZ2 x := by
  obtain ⟨z, rfl⟩ : ∃ z, x = z + 1 / 5 := ⟨x - 1 / 5, by ring⟩
  have hz0 : 1 / 30 ≤ z := by linarith
  have hz1 : z ≤ 8 / 35 := by linarith
  obtain ⟨l2, u2, l3, u3, l4, u4, l5, u5, l6, u6, l7, u7, l8, u8⟩ := hrl_zb hz0 hz1
  have e : hrlZ2 (z + 1 / 5) = (1352427578 / 390625) + (4582027094 / 78125) * z ^ (1 : ℕ) + (4090921099 / 15625) * z ^ (2 : ℕ) + (1379755863 / 3125) * z ^ (3 : ℕ) + (41533382 / 125) * z ^ (4 : ℕ) + (13233318 / 125) * z ^ (5 : ℕ) + (162429 / 25) * z ^ (6 : ℕ) + (-(10461 / 5) : ℝ) * z ^ (7 : ℕ) + (-327 : ℝ) * z ^ (8 : ℕ) := by unfold hrlZ2; ring
  rw [e]; linarith only [hz0, l2, l3, l4, l5, l6, u7, u8]

/-- `Z_3 ≥ 0` on `[7/30, 3/7]`, by monomials in `z = x - 1/5`. -/
theorem hrl_Z3_lb {x : ℝ} (h1 : 7 / 30 ≤ x) (h2 : x ≤ 3 / 7) : 0 ≤ hrlZ3 x := by
  obtain ⟨z, rfl⟩ : ∃ z, x = z + 1 / 5 := ⟨x - 1 / 5, by ring⟩
  have hz0 : 1 / 30 ≤ z := by linarith
  have hz1 : z ≤ 8 / 35 := by linarith
  obtain ⟨l2, u2, l3, u3, l4, u4, l5, u5, l6, u6, l7, u7, l8, u8⟩ := hrl_zb hz0 hz1
  have e : hrlZ3 (z + 1 / 5) = (2684739384 / 390625) + (6275045042 / 78125) * z ^ (1 : ℕ) + (4893956317 / 15625) * z ^ (2 : ℕ) + (1583238524 / 3125) * z ^ (3 : ℕ) + (47959366 / 125) * z ^ (4 : ℕ) + (15841829 / 125) * z ^ (5 : ℕ) + (137497 / 25) * z ^ (6 : ℕ) + (-(27488 / 5) : ℝ) * z ^ (7 : ℕ) + (-871 : ℝ) * z ^ (8 : ℕ) := by unfold hrlZ3; ring
  rw [e]; linarith only [hz0, l2, l3, l4, l5, l6, u7, u8]

/-- `Z_4 ≥ 0` on `[7/30, 3/7]`, by monomials in `z = x - 1/5`. -/
theorem hrl_Z4_lb {x : ℝ} (h1 : 7 / 30 ≤ x) (h2 : x ≤ 3 / 7) : 0 ≤ hrlZ4 x := by
  obtain ⟨z, rfl⟩ : ∃ z, x = z + 1 / 5 := ⟨x - 1 / 5, by ring⟩
  have hz0 : 1 / 30 ≤ z := by linarith
  have hz1 : z ≤ 8 / 35 := by linarith
  obtain ⟨l2, u2, l3, u3, l4, u4, l5, u5, l6, u6, l7, u7, l8, u8⟩ := hrl_zb hz0 hz1
  have e : hrlZ4 (z + 1 / 5) = (1629362698 / 390625) + (2963860749 / 78125) * z ^ (1 : ℕ) + (2208544824 / 15625) * z ^ (2 : ℕ) + (712495928 / 3125) * z ^ (3 : ℕ) + (22094802 / 125) * z ^ (4 : ℕ) + (7614988 / 125) * z ^ (5 : ℕ) + (20509 / 25) * z ^ (6 : ℕ) + (-(23511 / 5) : ℝ) * z ^ (7 : ℕ) + (-762 : ℝ) * z ^ (8 : ℕ) := by unfold hrlZ4; ring
  rw [e]; linarith only [hz0, l2, l3, l4, l5, l6, u7, u8]

/-- `Z_5 ≥ 760` on `[7/30, 3/7]`, by monomials in `z = x - 1/5`. -/
theorem hrl_Z5_lb {x : ℝ} (h1 : 7 / 30 ≤ x) (h2 : x ≤ 3 / 7) : 760 ≤ hrlZ5 x := by
  obtain ⟨z, rfl⟩ : ∃ z, x = z + 1 / 5 := ⟨x - 1 / 5, by ring⟩
  have hz0 : 1 / 30 ≤ z := by linarith
  have hz1 : z ≤ 8 / 35 := by linarith
  obtain ⟨l2, u2, l3, u3, l4, u4, l5, u5, l6, u6, l7, u7, l8, u8⟩ := hrl_zb hz0 hz1
  have e : hrlZ5 (z + 1 / 5) = (9348461 / 15625) + (65315866 / 15625) * z ^ (1 : ℕ) + (59634517 / 3125) * z ^ (2 : ℕ) + (21192346 / 625) * z ^ (3 : ℕ) + (703537 / 25) * z ^ (4 : ℕ) + (52028 / 5) * z ^ (5 : ℕ) + (-(2589 / 5) : ℝ) * z ^ (6 : ℕ) + (-1483 : ℝ) * z ^ (7 : ℕ) + (-245 : ℝ) * z ^ (8 : ℕ) := by unfold hrlZ5; ring
  rw [e]; linarith only [hz0, l2, l3, l4, l5, u6, u7, u8]

/-- `Z_6 ≥ 0` on `[7/30, 3/7]`, by monomials in `z = x - 1/5`. -/
theorem hrl_Z6_lb {x : ℝ} (h1 : 7 / 30 ≤ x) (h2 : x ≤ 3 / 7) : 0 ≤ hrlZ6 x := by
  obtain ⟨z, rfl⟩ : ∃ z, x = z + 1 / 5 := ⟨x - 1 / 5, by ring⟩
  have hz0 : 1 / 30 ≤ z := by linarith
  have hz1 : z ≤ 8 / 35 := by linarith
  obtain ⟨l2, u2, l3, u3, l4, u4, l5, u5, l6, u6, l7, u7, l8, u8⟩ := hrl_zb hz0 hz1
  have e : hrlZ6 (z + 1 / 5) = (186778958 / 390625) + (-(103304026 / 78125) : ℝ) * z ^ (1 : ℕ) + (-(36091531 / 15625) : ℝ) * z ^ (2 : ℕ) + (-(7006242 / 3125) : ℝ) * z ^ (3 : ℕ) + (-(179493 / 125) : ℝ) * z ^ (4 : ℕ) + (-(58002 / 125) : ℝ) * z ^ (5 : ℕ) + (-(2166 / 25) : ℝ) * z ^ (6 : ℕ) + (-(191 / 5) : ℝ) * z ^ (7 : ℕ) + (-7 : ℝ) * z ^ (8 : ℕ) := by unfold hrlZ6; ring
  rw [e]; linarith only [hz1, u2, u3, u4, u5, u6, u7, u8]

/-- `K₀ > 0` on `[3/8, 2/5]`, by monomials in `a = t - 3/8`. -/
theorem hrl_K0_pos {t : ℝ} (h1 : 3 / 8 ≤ t) (h2 : t ≤ 2 / 5) : 0 < hrlK0 t := by
  obtain ⟨a, rfl⟩ : ∃ a, t = a + 3 / 8 := ⟨t - 3 / 8, by ring⟩
  have ha0 : 0 ≤ a := by linarith
  have ha1 : a ≤ 1 / 40 := by linarith
  obtain ⟨l2, u2, l3, u3, l4, u4, l5, u5, l6, u6⟩ := hrl_ab ha0 ha1
  have e : hrlK0 (a + 3 / 8) = (10024135 / 262144) + (-(4815637 / 16384) : ℝ) * a ^ (1 : ℕ) + (-(3228711 / 4096) : ℝ) * a ^ (2 : ℕ) + (187437 / 128) * a ^ (3 : ℕ) + (51657 / 64) * a ^ (4 : ℕ) + (3723 / 4) * a ^ (5 : ℕ) + (-521 : ℝ) * a ^ (6 : ℕ) := by unfold hrlK0; ring
  rw [e]; linarith only [ha1, l3, l4, l5, u2, u6]

/-- `L_x > 0` on `[1/5, 1/2]`. -/
theorem hrl_Lx_pos {x : ℝ} (h1 : 1 / 5 ≤ x) (h2 : x ≤ 1 / 2) : 0 < hrlLx x := by
  have hx : 0 ≤ x := by linarith
  have x2 : x ^ (2 : ℕ) ≤ 1 / 4 := by nlinarith
  have x2l : 1 / 25 ≤ x ^ (2 : ℕ) := by nlinarith
  have x3 : 1 / 125 ≤ x ^ (3 : ℕ) := by nlinarith
  have x3n : 0 ≤ x ^ (3 : ℕ) := by positivity
  have x5 : x ^ (5 : ℕ) ≤ x ^ (3 : ℕ) / 4 := by
    have := mul_le_mul_of_nonneg_left x2 x3n; nlinarith
  have x4 : x ^ (4 : ℕ) ≤ x ^ (3 : ℕ) / 2 := by
    have := mul_le_mul_of_nonneg_left h2 x3n; nlinarith
  unfold hrlLx; linarith

theorem hrl_R0_dx (t s : ℝ) : HasDerivAt (polyHorner (hrlR0L t)) (hrlDR0 t s) s := by
  have H := poly_hasDerivAt_horner (hrlR0L t) s
  have e : polyHornerD (hrlR0L t) s = hrlDR0 t s := by
    simp only [hrlR0L, polyHornerD, polyHorner]; unfold hrlDR0; ring
  rw [e] at H; exact H

theorem hrl_R0_eq (t x : ℝ) : hrlR0 t x = polyHorner (hrlR0L t) x := by
  simp only [hrlR0L, polyHorner]; unfold hrlR0; ring

/-- `R₀ > 0` on the rectangle: `R₀` increases in `x`, and `R₀(t, 1/5) ≥ 1000K₀ > 0`. -/
theorem hrl_R0_pos {t x : ℝ} (h1 : 3 / 8 ≤ t) (h2 : t ≤ 2 / 5) (hx1 : 1 / 5 ≤ x) (hx2 : x ≤ 1 / 2) :
    0 < hrlR0 t x := by
  have mono := poly_mono (hrl_R0_dx t) (a := 1 / 5) (b := 1 / 2)
    (fun s s1 s2 => by
      have := hrl_DR0_ge h1 h2 (by linarith : (0 : ℝ) ≤ s); have := hrl_Lx_pos s1 s2; linarith)
    le_rfl hx1 hx2
  rw [← hrl_R0_eq, ← hrl_R0_eq] at mono
  have := hrl_R0K (by linarith : (0 : ℝ) ≤ t)
  have := hrl_K0_pos h1 h2
  linarith

/-- **`-𝓗²S > 0`** on the rectangle: `R₀ > 0`, `R₁, R₂, R₃ ≥ 0`, and
`R₄ + R₅y + R₆y² ≥ 0` from `R₄ ≥ 288000`, `R₅, R₆ ≥ -10000`. -/
theorem hrl_R_pos {t x y : ℝ} (h1 : 3 / 8 ≤ t) (h2 : t ≤ 2 / 5) (hx1 : 7 / 30 ≤ x) (hx2 : x ≤ 3 / 7)
    (hy0 : 0 ≤ y) (hy1 : y ≤ 1 / 4) :
    0 < hrlR0 t x + hrlR1 t x * y + hrlR2 t x * y ^ (2 : ℕ) + hrlR3 t x * y ^ (3 : ℕ) + hrlR4 t x * y ^ (4 : ℕ)
      + hrlR5 t x * y ^ (5 : ℕ) + hrlR6 t x * y ^ (6 : ℕ) := by
  have hx : 0 ≤ x := by linarith
  have r0 := hrl_R0_pos (x := x) h1 h2 (by linarith) (by linarith)
  have r1 : 0 ≤ hrlR1 t x := by
    have := hrl_RQ1 h1 h2 hx; have := hrl_QU1 hx; have := hrl_U1_lb hx1 hx2; linarith
  have r2 : 0 ≤ hrlR2 t x := by
    have := hrl_RQ2 h1 h2 hx; have := hrl_QU2 hx; have := hrl_U2_lb hx1 hx2; linarith
  have r3 : 0 ≤ hrlR3 t x := by
    have := hrl_RQ3 h1 h2 hx; have := hrl_QU3 hx; have := hrl_U3_lb hx1 hx2; linarith
  have r4 : 288000 ≤ hrlR4 t x := by
    have := hrl_RQ4 h1 h2 hx; have := hrl_QU4 hx; have := hrl_U4_lb hx1 hx2; linarith
  have r5 : -10000 ≤ hrlR5 t x := by
    have := hrl_RQ5 h1 h2 hx; have := hrl_QU5 hx; have := hrl_U5_lb hx1 hx2; linarith
  have r6 : -10000 ≤ hrlR6 t x := by
    have := hrl_RQ6 h1 h2 hx; have := hrl_QU6 hx; have := hrl_U6_lb hx1 hx2; linarith
  have q5 := mul_le_mul_of_nonneg_right r5 hy0
  have q6 := mul_le_mul_of_nonneg_right r6 (sq_nonneg y)
  have y2 : y ^ (2 : ℕ) ≤ 1 / 16 := by nlinarith
  have inner : 0 ≤ hrlR4 t x + hrlR5 t x * y + hrlR6 t x * y ^ (2 : ℕ) := by nlinarith
  have m4 := mul_nonneg (pow_nonneg hy0 4) inner
  have m1 := mul_nonneg r1 hy0
  have m2 := mul_nonneg r2 (pow_nonneg hy0 2)
  have m3 := mul_nonneg r3 (pow_nonneg hy0 3)
  nlinarith

/-- **`-𝓗S(2/5, x, 1 + y) > 0`**: `B₀ > 0`, `B₁, …, B₄ ≥ 0`, and `B₅ + B₆y ≥ 0` from
`B₅ ≥ 7600`, `B₆ ≥ -7000`. -/
theorem hrl_B_pos {x y : ℝ} (hx1 : 7 / 30 ≤ x) (hx2 : x ≤ 3 / 7) (hy0 : 0 ≤ y) (hy1 : y ≤ 1 / 4) :
    0 < hrlBb0 x + hrlBb1 x * y + hrlBb2 x * y ^ (2 : ℕ) + hrlBb3 x * y ^ (3 : ℕ) + hrlBb4 x * y ^ (4 : ℕ)
      + hrlBb5 x * y ^ (5 : ℕ) + hrlBb6 x * y ^ (6 : ℕ) := by
  have hx : 0 ≤ x := by linarith
  have b0 : 0 < hrlBb0 x := by have := hrl_BZ0 hx; have := hrl_Z0_lb hx1 hx2; linarith
  have b1 : 0 ≤ hrlBb1 x := by have := hrl_BZ1 hx; have := hrl_Z1_lb hx1 hx2; linarith
  have b2 : 0 ≤ hrlBb2 x := by have := hrl_BZ2 hx; have := hrl_Z2_lb hx1 hx2; linarith
  have b3 : 0 ≤ hrlBb3 x := by have := hrl_BZ3 hx; have := hrl_Z3_lb hx1 hx2; linarith
  have b4 : 0 ≤ hrlBb4 x := by have := hrl_BZ4 hx; have := hrl_Z4_lb hx1 hx2; linarith
  have b5 : 7600 ≤ hrlBb5 x := by have := hrl_BZ5 hx; have := hrl_Z5_lb hx1 hx2; linarith
  have b6 : -7000 ≤ hrlBb6 x := by have := hrl_BZ6 hx; have := hrl_Z6_lb hx1 hx2; linarith
  have q6 := mul_le_mul_of_nonneg_right b6 hy0
  have inner : 0 ≤ hrlBb5 x + hrlBb6 x * y := by nlinarith
  have m5 := mul_nonneg (pow_nonneg hy0 5) inner
  have m1 := mul_nonneg b1 hy0
  have m2 := mul_nonneg b2 (pow_nonneg hy0 2)
  have m3 := mul_nonneg b3 (pow_nonneg hy0 3)
  have m4 := mul_nonneg b4 (pow_nonneg hy0 4)
  nlinarith

end SmoothedOctagon
