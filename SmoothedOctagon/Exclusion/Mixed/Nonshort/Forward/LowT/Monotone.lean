module

public import SmoothedOctagon.Exclusion.Mixed.FwdHand.LowTCurv
public import SmoothedOctagon.Exclusion.Mixed.FwdHand.LowTInit

/-!
# Case M2, forward successor by hand: the low-`t` circuit increases in `h`

On the low-`t` unit domain `1/4 ≤ h ≤ 1/3`, `1/30 ≤ j ≤ 5h/7`, `0 ≤ y`, `y(1 + 2j) ≤ h - j`, the
circuit `S` satisfies `𝓗S = ∂_hS > 0` (`nlt_HS_pos`).

With `u = j + 1/4`, `r = h - 1/4`, the jets `Pᵢ = 𝓗^{i+1}S(3/8, u, 1 + y)` (`nltP0`, `nltP1`, `nltP2`)
and `𝓗⁴S ≥ 500000` give the cubic Taylor bound `𝓗S ≥ T(u, y, r)` (`nltT`, `nlt_taylor3`), and
`T` increases in `r` since `P₁, P₂ > 0`. Let `A`, `B` be the values of `r` on the
maximum-duration face and on the outer face (`nltAA`, `nltBB`); at `r₀ = max(0, A, B)`:

* `r₀ = 0`: `T = P₀ ≥ 68`;
* `r₀ = B`: `T_B` increases in `u`, and `T_B(3/7, y) = P₀(3/7, y)` (`nlt_TB_pos`);
* `r₀ = A`: `f = ∂_uT_A` increases in `u` and is positive at the left ends `u = 17/60, 1/3, 3/8,
  2/5` of four pieces, so `T_A` decreases to `A = 0` (where `T_A = P₀`) or to `u = 17/60`
  (`nlt_TA_pos`).

The polynomials `T_A`, `T_B` are written by their coefficient lists in `u` (`nltTAL0`, …,
`nltTBL0`, …) and differentiated by `nltDer`; the one-variable signs use termwise monomial bounds
after a shift.

## Main API

* `nltP0`, `nltP1`, `nltP2`, `nltT`, `nltAA`, `nltBB`; `nltTAL0`, …, `nlt_TA_eq`; `nltTBL0`, …,
  `nlt_TB_eq`.
* `nlt_T_mono`, `nlt_TA_pos`, `nlt_TB_pos`, `nlt_HS_pos`.
-/

@[expose] public section

namespace SmoothedOctagon

/-- `P₀(u, y) = 𝓗S(3/8, u, 1 + y)`. -/
noncomputable def nltP0 (u y : ℝ) : ℝ := nltc0 u + nltc1 u * y + nltc2 u * y ^ 2 + nltc3 u * y ^ 3 + nltc4 u * y ^ 4 + nltc5 u * y ^ 5 + nltc6 u * y ^ 6

/-- `P₁(u, y) = 𝓗²S(3/8, u, 1 + y)`. -/
noncomputable def nltP1 (u y : ℝ) : ℝ := nltE0 u + nltE1 u * y + nltE2 u * y ^ 2 + nltE3 u * y ^ 3 + nltE4 u * y ^ 4 + nltE5 u * y ^ 5 + nltE6 u * y ^ 6

/-- `P₂(u, y) = 𝓗³S(3/8, u, 1 + y)`. -/
noncomputable def nltP2 (u y : ℝ) : ℝ := nltR0 u + nltR1 u * y + nltR2 u * y ^ 2 + nltR3 u * y ^ 3 + nltR4 u * y ^ 4 + nltR5 u * y ^ 5 + nltR6 u * y ^ 6

/-- The cubic Taylor polynomial `T(u, y, r)`. -/
noncomputable def nltT (u y r : ℝ) : ℝ :=
  nltP0 u y + r * nltP1 u y + r ^ 2 / 2 * nltP2 u y + 250000 / 3 * r ^ 3

/-- `A = (2u + 1/2)y + u - 1/2`: the value of `r` on the maximum-duration face. -/
noncomputable def nltAA (u y : ℝ) : ℝ := (2 * u + 1 / 2) * y + u - 1 / 2

/-- `B = (7u - 3)/5`: the value of `r` on the outer face `j = 5h/7`. -/
noncomputable def nltBB (u : ℝ) : ℝ := (7 * u - 3) / 5

/-- The coefficients in `u` of the `y^0`-coefficient of `T_A(u, y) = T(u, y, A)`. -/
noncomputable def nltTAL0 : List ℝ :=
  [((-(513203 / 1024)) : ℝ), ((5219249 / 128) : ℝ), ((-(55016305 / 384)) : ℝ), ((2805685 / 32) : ℝ), ((2008851 / 64) : ℝ), ((3075 / 16) : ℝ), ((586097 / 4) : ℝ), (64995 : ℝ), (4284 : ℝ)]

/-- The coefficients in `u` of the `y^1`-coefficient of `T_A(u, y) = T(u, y, A)`. -/
noncomputable def nltTAL1 : List ℝ :=
  [((135432107 / 6144) : ℝ), ((-(100281901 / 768)) : ℝ), ((-(230082617 / 768)) : ℝ), ((55875079 / 64) : ℝ), ((-(8079093 / 128)) : ℝ), ((12125887 / 32) : ℝ), ((13887849 / 8) : ℝ), (770859 : ℝ), (95198 : ℝ), (4284 : ℝ)]

/-- The coefficients in `u` of the `y^2`-coefficient of `T_A(u, y) = T(u, y, A)`. -/
noncomputable def nltTAL2 : List ℝ :=
  [((-(156018019 / 1536)) : ℝ), ((-(23148577 / 128)) : ℝ), ((102303479 / 96) : ℝ), ((117093889 / 64) : ℝ), ((-(33021005 / 64)) : ℝ), (3075942 : ℝ), ((25759859 / 4) : ℝ), ((13202203 / 4) : ℝ), (547464 : ℝ), (13158 : ℝ)]

/-- The coefficients in `u` of the `y^3`-coefficient of `T_A(u, y) = T(u, y, A)`. -/
noncomputable def nltTAL3 : List ℝ :=
  [((332795617 / 6144) : ℝ), ((713876065 / 768) : ℝ), ((199096271 / 128) : ℝ), ((-(50115937 / 96)) : ℝ), ((355080977 / 128) : ℝ), ((188812861 / 32) : ℝ), ((15046251 / 8) : ℝ), ((3760497 / 2) : ℝ), (557892 : ℝ), ((-23256) : ℝ)]

/-- The coefficients in `u` of the `y^4`-coefficient of `T_A(u, y) = T(u, y, A)`. -/
noncomputable def nltTAL4 : List ℝ :=
  [((277533991 / 3072) : ℝ), ((11539491 / 128) : ℝ), ((-(1275457721 / 384)) : ℝ), ((-(268675159 / 64)) : ℝ), ((126936419 / 64) : ℝ), ((-(391564853 / 16)) : ℝ), ((-(184062709 / 4)) : ℝ), ((-(73579557 / 4)) : ℝ), ((-2191727) : ℝ), ((-136782) : ℝ)]

/-- The coefficients in `u` of the `y^5`-coefficient of `T_A(u, y) = T(u, y, A)`. -/
noncomputable def nltTAL5 : List ℝ :=
  [((-(169998181 / 2048)) : ℝ), ((-(400733545 / 256)) : ℝ), ((-(453647823 / 64)) : ℝ), ((-(648409085 / 64)) : ℝ), ((-(411615615 / 16)) : ℝ), ((-(702046851 / 8)) : ℝ), ((-(1672912637 / 16)) : ℝ), ((-(81816283 / 2)) : ℝ), ((-(10542759 / 2)) : ℝ), ((-195840) : ℝ)]

/-- The coefficients in `u` of the `y^6`-coefficient of `T_A(u, y) = T(u, y, A)`. -/
noncomputable def nltTAL6 : List ℝ :=
  [((-(46326713 / 512)) : ℝ), ((-(128275663 / 128)) : ℝ), ((-(423881663 / 128)) : ℝ), ((-(209425151 / 32)) : ℝ), ((-(55998881 / 2)) : ℝ), ((-(147565345 / 2)) : ℝ), ((-(302745407 / 4)) : ℝ), ((-28164059) : ℝ), ((-3543326) : ℝ), ((-116280) : ℝ)]

/-- The coefficients in `u` of the `y^7`-coefficient of `T_A(u, y) = T(u, y, A)`. -/
noncomputable def nltTAL7 : List ℝ :=
  [((-(28194543 / 2048)) : ℝ), ((-(10383035 / 256)) : ℝ), ((97765727 / 256) : ℝ), ((35100467 / 32) : ℝ), ((-(433616715 / 128)) : ℝ), ((-(54413921 / 4)) : ℝ), ((-(56436741 / 4)) : ℝ), ((-4894830) : ℝ), ((-553334) : ℝ), ((-24480) : ℝ)]

/-- The coefficients in `u` of the `y^8`-coefficient of `T_A(u, y) = T(u, y, A)`. -/
noncomputable def nltTAL8 : List ℝ :=
  [((505197 / 512) : ℝ), ((25137 / 2) : ℝ), ((3890241 / 64) : ℝ), ((2285763 / 16) : ℝ), ((2932689 / 16) : ℝ), ((293115 / 2) : ℝ), (72072 : ℝ), (33336 : ℝ), (7344 : ℝ)]

/-- The coefficients in `u` of the `y^0`-coefficient of `T_B(u, y) = T(u, y, B)`. -/
noncomputable def nltTBL0 : List ℝ :=
  [((-(14157771 / 6400)) : ℝ), ((61451961 / 800) : ℝ), ((-(244136781 / 800)) : ℝ), ((288955339 / 1200) : ℝ), ((178526227 / 1600) : ℝ), ((30173563 / 400) : ℝ), ((5946941 / 20) : ℝ), ((3144771 / 25) : ℝ), ((209916 / 25) : ℝ)]

/-- The coefficients in `u` of the `y^1`-coefficient of `T_B(u, y) = T(u, y, B)`. -/
noncomputable def nltTBL1 : List ℝ :=
  [((315063829 / 12800) : ℝ), ((-(110194151 / 1600)) : ℝ), ((-(25291101 / 1600)) : ℝ), ((28754163 / 160) : ℝ), ((-(2486010049 / 3200)) : ℝ), ((3431817 / 800) : ℝ), ((398620969 / 200) : ℝ), ((24710217 / 25) : ℝ), ((3783682 / 25) : ℝ), ((209916 / 25) : ℝ)]

/-- The coefficients in `u` of the `y^2`-coefficient of `T_B(u, y) = T(u, y, B)`. -/
noncomputable def nltTBL2 : List ℝ :=
  [((-(763498153 / 9600)) : ℝ), ((40983299 / 600) : ℝ), ((709057637 / 800) : ℝ), ((-(321169157 / 800)) : ℝ), ((-(88529397 / 25)) : ℝ), ((-(1842852919 / 800)) : ℝ), ((70540067 / 100) : ℝ), ((6428623 / 4) : ℝ), ((9834286 / 25) : ℝ), ((-(194922 / 25)) : ℝ)]

/-- The coefficients in `u` of the `y^3`-coefficient of `T_B(u, y) = T(u, y, B)`. -/
noncomputable def nltTBL3 : List ℝ :=
  [((-(2766782297 / 19200)) : ℝ), ((4545323 / 150) : ℝ), ((837305953 / 1600) : ℝ), ((2361568841 / 1200) : ℝ), ((26286922649 / 3200) : ℝ), ((-(1199783523 / 800)) : ℝ), ((-(3195806917 / 200)) : ℝ), ((-(75727939 / 10)) : ℝ), ((-(24688126 / 25)) : ℝ), ((-(239904 / 5)) : ℝ)]

/-- The coefficients in `u` of the `y^4`-coefficient of `T_B(u, y) = T(u, y, B)`. -/
noncomputable def nltTBL4 : List ℝ :=
  [((-(295789501 / 6400)) : ℝ), ((-(69676949 / 800)) : ℝ), ((-(568575099 / 400)) : ℝ), ((96406251 / 40) : ℝ), ((3109324163 / 200) : ℝ), ((249052181 / 100) : ℝ), ((-(1925860743 / 100)) : ℝ), ((-(42040773 / 4)) : ℝ), ((-(37801917 / 25)) : ℝ), ((-44982) : ℝ)]

/-- The coefficients in `u` of the `y^5`-coefficient of `T_B(u, y) = T(u, y, B)`. -/
noncomputable def nltTBL5 : List ℝ :=
  [((131081181 / 12800) : ℝ), ((-(53679249 / 1600)) : ℝ), ((-(1708508289 / 1600)) : ℝ), ((-(54435017 / 400)) : ℝ), ((14966563273 / 3200) : ℝ), ((1403903137 / 800) : ℝ), ((-(1713559809 / 400)) : ℝ), ((-(108755129 / 50)) : ℝ), ((-(13006571 / 50)) : ℝ), ((-(59976 / 5)) : ℝ)]

/-- The coefficients in `u` of the `y^6`-coefficient of `T_B(u, y) = T(u, y, B)`. -/
noncomputable def nltTBL6 : List ℝ :=
  [((4748103 / 3200) : ℝ), ((-(445233 / 80)) : ℝ), ((-(516999 / 25)) : ℝ), ((-(3422921 / 400)) : ℝ), ((17799707 / 800) : ℝ), ((9057747 / 200) : ℝ), ((533528 / 25) : ℝ), ((398882 / 25) : ℝ), ((115464 / 25) : ℝ)]

theorem nlt_TA_eq (u y : ℝ) : nltT u y (nltAA u y) = lrhHorner nltTAL0 u + lrhHorner nltTAL1 u * y + lrhHorner nltTAL2 u * y ^ 2 + lrhHorner nltTAL3 u * y ^ 3 + lrhHorner nltTAL4 u * y ^ 4 + lrhHorner nltTAL5 u * y ^ 5 + lrhHorner nltTAL6 u * y ^ 6 + lrhHorner nltTAL7 u * y ^ 7 + lrhHorner nltTAL8 u * y ^ 8 := by
  simp only [nltTAL0, nltTAL1, nltTAL2, nltTAL3, nltTAL4, nltTAL5, nltTAL6, nltTAL7, nltTAL8, lrhHorner]
  unfold nltAA nltT nltP0 nltP1 nltP2 nltc0 nltE0 nltR0 nltc1 nltE1 nltR1 nltc2 nltE2 nltR2 nltc3 nltE3 nltR3 nltc4 nltE4 nltR4 nltc5 nltE5 nltR5 nltc6 nltE6 nltR6
  ring

theorem nlt_TB_eq (u y : ℝ) : nltT u y (nltBB u) = lrhHorner nltTBL0 u + lrhHorner nltTBL1 u * y + lrhHorner nltTBL2 u * y ^ 2 + lrhHorner nltTBL3 u * y ^ 3 + lrhHorner nltTBL4 u * y ^ 4 + lrhHorner nltTBL5 u * y ^ 5 + lrhHorner nltTBL6 u * y ^ 6 := by
  simp only [nltTBL0, nltTBL1, nltTBL2, nltTBL3, nltTBL4, nltTBL5, nltTBL6, lrhHorner]
  unfold nltBB nltT nltP0 nltP1 nltP2 nltc0 nltE0 nltR0 nltc1 nltE1 nltR1 nltc2 nltE2 nltR2 nltc3 nltE3 nltR3 nltc4 nltE4 nltR4 nltc5 nltE5 nltR5 nltc6 nltE6 nltR6
  ring

/-- `f(17/60, y)`. -/
noncomputable def nltTf0 (y : ℝ) : ℝ := -(189067602987059 / 12960000000) - (863472482267471057 / 13996800000000) * y + (345247434030947767 / 345600000000) * y ^ 2 + (1676344178235480701 / 777600000000) * y ^ 3 - (111542218618066560623 / 27993600000000) * y ^ 4 - (1690139489775707911 / 116640000000) * y ^ 5 - (14437903334035305763 / 1399680000000) * y ^ 6 - (10486537924083811 / 21870000000) * y ^ 7 + (218819204969 / 2109375) * y ^ 8

/-- `nltTf0 > 0` on `[1/7, 9/32]`. -/
theorem nltTf0_pos {y : ℝ} (h1 : (1 / 7) ≤ y) (h2 : y ≤ (9 / 32)) : 0 < nltTf0 y := by
  obtain ⟨z, rfl⟩ : ∃ z, y = (1 / 7) + z := ⟨y - (1 / 7), by ring⟩
  have z0 : 0 ≤ z := by linarith
  have z1 : z ≤ (31 / 224) := by linarith
  have p2 : z ^ 2 ≤ (31 / 224) * z ^ 1 := nlt_pw z0 z1 1
  have q2 : 0 ≤ z ^ 2 := pow_nonneg z0 2
  have p3 : z ^ 3 ≤ (31 / 224) * z ^ 2 := nlt_pw z0 z1 2
  have q3 : 0 ≤ z ^ 3 := pow_nonneg z0 3
  have p4 : z ^ 4 ≤ (31 / 224) * z ^ 3 := nlt_pw z0 z1 3
  have q4 : 0 ≤ z ^ 4 := pow_nonneg z0 4
  have p5 : z ^ 5 ≤ (31 / 224) * z ^ 4 := nlt_pw z0 z1 4
  have q5 : 0 ≤ z ^ 5 := pow_nonneg z0 5
  have p6 : z ^ 6 ≤ (31 / 224) * z ^ 5 := nlt_pw z0 z1 5
  have q6 : 0 ≤ z ^ 6 := pow_nonneg z0 6
  have p7 : z ^ 7 ≤ (31 / 224) * z ^ 6 := nlt_pw z0 z1 6
  have q7 : 0 ≤ z ^ 7 := pow_nonneg z0 7
  have p8 : z ^ 8 ≤ (31 / 224) * z ^ 7 := nlt_pw z0 z1 7
  have q8 : 0 ≤ z ^ 8 := pow_nonneg z0 8
  have e : nltTf0 ((1 / 7) + z) = (2133434089319340329773 / 3227550665472000000) + (396768063025499291964883 / 1440870832800000000) * z + (49532641163722799831747 / 52276492800000000) * z ^ 2 - (774289178495534619137 / 210039480000000) * z ^ 3 - (56133179100354144772663 / 3200601600000000) * z ^ 4 - (268854380603133836099 / 11430720000000) * z ^ 5 - (105182500643854328117 / 9797760000000) * z ^ 6 - (55256025331637941 / 153090000000) * z ^ 7 + (218819204969 / 2109375) * z ^ 8 := by unfold nltTf0; ring
  rw [e]; linarith only [z0, z1, p2, q2, p3, q3, p4, q4, p5, q5, p6, q6, p7, q7, p8, q8]


theorem nlt_Tf0_eq (y : ℝ) : lrhHorner (nltDer nltTAL0) ((17 / 60)) + lrhHorner (nltDer nltTAL1) ((17 / 60)) * y + lrhHorner (nltDer nltTAL2) ((17 / 60)) * y ^ 2 + lrhHorner (nltDer nltTAL3) ((17 / 60)) * y ^ 3 + lrhHorner (nltDer nltTAL4) ((17 / 60)) * y ^ 4 + lrhHorner (nltDer nltTAL5) ((17 / 60)) * y ^ 5 + lrhHorner (nltDer nltTAL6) ((17 / 60)) * y ^ 6 + lrhHorner (nltDer nltTAL7) ((17 / 60)) * y ^ 7 + lrhHorner (nltDer nltTAL8) ((17 / 60)) * y ^ 8 = nltTf0 y := by
  simp only [nltTAL0, nltTAL1, nltTAL2, nltTAL3, nltTAL4, nltTAL5, nltTAL6, nltTAL7, nltTAL8, nltDer, nltDerAux, lrhHorner]; unfold nltTf0; ring

/-- `f(1/3, y)`. -/
noncomputable def nltTf1 (y : ℝ) : ℝ := -(57347207 / 3456) + (14207375041 / 559872) * y + (44964461615 / 31104) * y ^ 2 + (163866466549 / 62208) * y ^ 3 - (1696801885331 / 279936) * y ^ 4 - (4085253960133 / 186624) * y ^ 5 - (4547921528399 / 279936) * y ^ 6 - (649091264443 / 559872) * y ^ 7 + (40043437 / 288) * y ^ 8

/-- `nltTf1 > 0` on `[1/10, 9/32]`. -/
theorem nltTf1_pos {y : ℝ} (h1 : (1 / 10) ≤ y) (h2 : y ≤ (9 / 32)) : 0 < nltTf1 y := by
  obtain ⟨z, rfl⟩ : ∃ z, y = (1 / 10) + z := ⟨y - (1 / 10), by ring⟩
  have z0 : 0 ≤ z := by linarith
  have z1 : z ≤ (29 / 160) := by linarith
  have p2 : z ^ 2 ≤ (29 / 160) * z ^ 1 := nlt_pw z0 z1 1
  have q2 : 0 ≤ z ^ 2 := pow_nonneg z0 2
  have p3 : z ^ 3 ≤ (29 / 160) * z ^ 2 := nlt_pw z0 z1 2
  have q3 : 0 ≤ z ^ 3 := pow_nonneg z0 3
  have p4 : z ^ 4 ≤ (29 / 160) * z ^ 3 := nlt_pw z0 z1 3
  have q4 : 0 ≤ z ^ 4 := pow_nonneg z0 4
  have p5 : z ^ 5 ≤ (29 / 160) * z ^ 4 := nlt_pw z0 z1 4
  have q5 : 0 ≤ z ^ 5 := pow_nonneg z0 5
  have p6 : z ^ 6 ≤ (29 / 160) * z ^ 5 := nlt_pw z0 z1 5
  have q6 : 0 ≤ z ^ 6 := pow_nonneg z0 6
  have p7 : z ^ 7 ≤ (29 / 160) * z ^ 6 := nlt_pw z0 z1 6
  have q7 : 0 ≤ z ^ 7 := pow_nonneg z0 7
  have p8 : z ^ 8 ≤ (29 / 160) * z ^ 7 := nlt_pw z0 z1 7
  have q8 : 0 ≤ z ^ 8 := pow_nonneg z0 8
  have e : nltTf1 ((1 / 10) + z) = (61390664506599149 / 27993600000000) + (1000354274268383707 / 2799360000000) * z + (50658223866790153 / 31104000000) * z ^ 2 - (64618229251897741 / 27993600000) * z ^ 3 - (3636011484182003 / 186624000) * z ^ 4 - (2974202931880877 / 93312000) * z ^ 5 - (476420524914013 / 27993600) * z ^ 6 - (2934078556103 / 2799360) * z ^ 7 + (40043437 / 288) * z ^ 8 := by unfold nltTf1; ring
  rw [e]; linarith only [z0, z1, p2, q2, p3, q3, p4, q4, p5, q5, p6, q6, p7, q7, p8, q8]


theorem nlt_Tf1_eq (y : ℝ) : lrhHorner (nltDer nltTAL0) ((1 / 3)) + lrhHorner (nltDer nltTAL1) ((1 / 3)) * y + lrhHorner (nltDer nltTAL2) ((1 / 3)) * y ^ 2 + lrhHorner (nltDer nltTAL3) ((1 / 3)) * y ^ 3 + lrhHorner (nltDer nltTAL4) ((1 / 3)) * y ^ 4 + lrhHorner (nltDer nltTAL5) ((1 / 3)) * y ^ 5 + lrhHorner (nltDer nltTAL6) ((1 / 3)) * y ^ 6 + lrhHorner (nltDer nltTAL7) ((1 / 3)) * y ^ 7 + lrhHorner (nltDer nltTAL8) ((1 / 3)) * y ^ 8 = nltTf1 y := by
  simp only [nltTAL0, nltTAL1, nltTAL2, nltTAL3, nltTAL4, nltTAL5, nltTAL6, nltTAL7, nltTAL8, nltDer, nltDerAux, lrhHorner]; unfold nltTf1; ring

/-- `f(3/8, y)`. -/
noncomputable def nltTf2 (y : ℝ) : ℝ := -(3992152639 / 262144) + (1639082844005 / 12582912) * y + (16282036832083 / 8388608) * y ^ 2 + (19939497698075 / 6291456) * y ^ 3 - (72123188257463 / 8388608) * y ^ 4 - (4030800139625 / 131072) * y ^ 5 - (49061211085111 / 2097152) * y ^ 6 - (1089892292917 / 524288) * y ^ 7 + (5750717175 / 32768) * y ^ 8

/-- `nltTf2 > 0` on `[1/13, 9/32]`. -/
theorem nltTf2_pos {y : ℝ} (h1 : (1 / 13) ≤ y) (h2 : y ≤ (9 / 32)) : 0 < nltTf2 y := by
  obtain ⟨z, rfl⟩ : ∃ z, y = (1 / 13) + z := ⟨y - (1 / 13), by ring⟩
  have z0 : 0 ≤ z := by linarith
  have z1 : z ≤ (85 / 416) := by linarith
  have p2 : z ^ 2 ≤ (85 / 416) * z ^ 1 := nlt_pw z0 z1 1
  have q2 : 0 ≤ z ^ 2 := pow_nonneg z0 2
  have p3 : z ^ 3 ≤ (85 / 416) * z ^ 2 := nlt_pw z0 z1 2
  have q3 : 0 ≤ z ^ 3 := pow_nonneg z0 3
  have p4 : z ^ 4 ≤ (85 / 416) * z ^ 3 := nlt_pw z0 z1 3
  have q4 : 0 ≤ z ^ 4 := pow_nonneg z0 4
  have p5 : z ^ 5 ≤ (85 / 416) * z ^ 4 := nlt_pw z0 z1 4
  have q5 : 0 ≤ z ^ 5 := pow_nonneg z0 5
  have p6 : z ^ 6 ≤ (85 / 416) * z ^ 5 := nlt_pw z0 z1 5
  have q6 : 0 ≤ z ^ 6 := pow_nonneg z0 6
  have p7 : z ^ 7 ≤ (85 / 416) * z ^ 6 := nlt_pw z0 z1 6
  have q7 : 0 ≤ z ^ 7 := pow_nonneg z0 7
  have p8 : z ^ 8 ≤ (85 / 416) * z ^ 7 := nlt_pw z0 z1 7
  have q8 : 0 ≤ z ^ 8 := pow_nonneg z0 8
  have e : nltTf2 ((1 / 13) + z) = (25079700798904435057 / 3421422626013184) + (183065102515817833483 / 394779533770752) * z + (89674575746625055993 / 40490208591872) * z ^ 2 - (1765212738253534007 / 1167986786304) * z ^ 3 - (5399036153427046043 / 239587033088) * z ^ 4 - (96304153180955359 / 2303721472) * z ^ 5 - (8677760182827947 / 354418688) * z ^ 6 - (13432508009521 / 6815744) * z ^ 7 + (5750717175 / 32768) * z ^ 8 := by unfold nltTf2; ring
  rw [e]; linarith only [z0, z1, p2, q2, p3, q3, p4, q4, p5, q5, p6, q6, p7, q7, p8, q8]


theorem nlt_Tf2_eq (y : ℝ) : lrhHorner (nltDer nltTAL0) ((3 / 8)) + lrhHorner (nltDer nltTAL1) ((3 / 8)) * y + lrhHorner (nltDer nltTAL2) ((3 / 8)) * y ^ 2 + lrhHorner (nltDer nltTAL3) ((3 / 8)) * y ^ 3 + lrhHorner (nltDer nltTAL4) ((3 / 8)) * y ^ 4 + lrhHorner (nltDer nltTAL5) ((3 / 8)) * y ^ 5 + lrhHorner (nltDer nltTAL6) ((3 / 8)) * y ^ 6 + lrhHorner (nltDer nltTAL7) ((3 / 8)) * y ^ 7 + lrhHorner (nltDer nltTAL8) ((3 / 8)) * y ^ 8 = nltTf2 y := by
  simp only [nltTAL0, nltTAL1, nltTAL2, nltTAL3, nltTAL4, nltTAL5, nltTAL6, nltTAL7, nltTAL8, nltDer, nltDerAux, lrhHorner]; unfold nltTf2; ring

/-- `f(2/5, y)`. -/
noncomputable def nltTf3 (y : ℝ) : ℝ := -(383235073981 / 30000000) + (63359240015503 / 300000000) * y + (346361941782133 / 150000000) * y ^ 2 + (1069605737483113 / 300000000) * y ^ 3 - (1588656570673987 / 150000000) * y ^ 4 - (150339126748113 / 4000000) * y ^ 5 - (289096484049999 / 10000000) * y ^ 6 - (2265298149147 / 800000) * y ^ 7 + (251164949061 / 1250000) * y ^ 8

/-- `nltTf3 > 0` on `[1/19, 9/32]`. -/
theorem nltTf3_pos {y : ℝ} (h1 : (1 / 19) ≤ y) (h2 : y ≤ (9 / 32)) : 0 < nltTf3 y := by
  obtain ⟨z, rfl⟩ : ∃ z, y = (1 / 19) + z := ⟨y - (1 / 19), by ring⟩
  have z0 : 0 ≤ z := by linarith
  have z1 : z ≤ (139 / 608) := by linarith
  have p2 : z ^ 2 ≤ (139 / 608) * z ^ 1 := nlt_pw z0 z1 1
  have q2 : 0 ≤ z ^ 2 := pow_nonneg z0 2
  have p3 : z ^ 3 ≤ (139 / 608) * z ^ 2 := nlt_pw z0 z1 2
  have q3 : 0 ≤ z ^ 3 := pow_nonneg z0 3
  have p4 : z ^ 4 ≤ (139 / 608) * z ^ 3 := nlt_pw z0 z1 3
  have q4 : 0 ≤ z ^ 4 := pow_nonneg z0 4
  have p5 : z ^ 5 ≤ (139 / 608) * z ^ 4 := nlt_pw z0 z1 4
  have q5 : 0 ≤ z ^ 5 := pow_nonneg z0 5
  have p6 : z ^ 6 ≤ (139 / 608) * z ^ 5 := nlt_pw z0 z1 5
  have q6 : 0 ≤ z ^ 6 := pow_nonneg z0 6
  have p7 : z ^ 7 ≤ (139 / 608) * z ^ 6 := nlt_pw z0 z1 6
  have q7 : 0 ≤ z ^ 7 := pow_nonneg z0 7
  have p8 : z ^ 8 ≤ (139 / 608) * z ^ 7 := nlt_pw z0 z1 7
  have q8 : 0 ≤ z ^ 8 := pow_nonneg z0 8
  have e : nltTf3 ((1 / 19) + z) = (821617591641420286733 / 159220903509375000) + (5320755100431074780071 / 11173396737500000) * z + (9307511923393560737807 / 3528441075000000) * z ^ 2 + (38901327278380775159 / 185707425000000) * z ^ 3 - (424143032634660557827 / 19548150000000) * z ^ 4 - (803827203246814209 / 17147500000) * z ^ 5 - (8645890237313349 / 288800000) * z ^ 6 - (1043867507365017 / 380000000) * z ^ 7 + (251164949061 / 1250000) * z ^ 8 := by unfold nltTf3; ring
  rw [e]; linarith only [z0, z1, p2, q2, p3, q3, p4, q4, p5, q5, p6, q6, p7, q7, p8, q8]


theorem nlt_Tf3_eq (y : ℝ) : lrhHorner (nltDer nltTAL0) ((2 / 5)) + lrhHorner (nltDer nltTAL1) ((2 / 5)) * y + lrhHorner (nltDer nltTAL2) ((2 / 5)) * y ^ 2 + lrhHorner (nltDer nltTAL3) ((2 / 5)) * y ^ 3 + lrhHorner (nltDer nltTAL4) ((2 / 5)) * y ^ 4 + lrhHorner (nltDer nltTAL5) ((2 / 5)) * y ^ 5 + lrhHorner (nltDer nltTAL6) ((2 / 5)) * y ^ 6 + lrhHorner (nltDer nltTAL7) ((2 / 5)) * y ^ 7 + lrhHorner (nltDer nltTAL8) ((2 / 5)) * y ^ 8 = nltTf3 y := by
  simp only [nltTAL0, nltTAL1, nltTAL2, nltTAL3, nltTAL4, nltTAL5, nltTAL6, nltTAL7, nltTAL8, nltDer, nltDerAux, lrhHorner]; unfold nltTf3; ring

/-- The `z^0`-jet of `∂_u f` at `u = 1/4 + z`. -/
noncomputable def nltJ0 (y : ℝ) : ℝ :=
  -(85655269 / 768) + (3126835277 / 3072) * y + (38999517259 / 6144) * y ^ 2 + (3357334927 / 512) * y ^ 3 - (155306828053 / 6144) * y ^ 4 - (184515278499 / 2048) * y ^ 5 - (4516495117 / 64) * y ^ 6 - (399650479 / 64) * y ^ 7 + (16929375 / 32) * y ^ 8

/-- The `z^1`-jet of `∂_u f` at `u = 1/4 + z`. -/
noncomputable def nltJ1 (y : ℝ) : ℝ :=
  (133705125 / 128) + (1305556149 / 128) * y + (17602707453 / 512) * y ^ 2 + (10467260171 / 256) * y ^ 3 - (106068972927 / 512) * y ^ 4 - (198549592863 / 256) * y ^ 5 - (83218058445 / 128) * y ^ 6 - (763296675 / 8) * y ^ 7 + (42742413 / 16) * y ^ 8

/-- The `z^2`-jet of `∂_u f` at `u = 1/4 + z`. -/
noncomputable def nltJ2 (y : ℝ) : ℝ :=
  (9874107 / 4) + (477341415 / 16) * y + (4347934533 / 32) * y ^ 2 + (1256712285 / 8) * y ^ 3 - (31650491913 / 32) * y ^ 4 - (98795578155 / 32) * y ^ 5 - 2490829701 * y ^ 6 - (13996998405 / 32) * y ^ 7 + (21806217 / 4) * y ^ 8

/-- The `z^3`-jet of `∂_u f` at `u = 1/4 + z`. -/
noncomputable def nltJ3 (y : ℝ) : ℝ :=
  6180660 + (163202595 / 2) * y + (1404269535 / 4) * y ^ 2 + (933288745 / 4) * y ^ 3 - (19139951175 / 8) * y ^ 4 - (12119687955 / 2) * y ^ 5 - (9097406775 / 2) * y ^ 6 - 833758770 * y ^ 7 + 6096900 * y ^ 8

/-- The `z^4`-jet of `∂_u f` at `u = 1/4 + z`. -/
noncomputable def nltJ4 (y : ℝ) : ℝ :=
  8032875 + (390864435 / 4) * y + (3165902505 / 8) * y ^ 2 + (367020225 / 2) * y ^ 3 - (19733227695 / 8) * y ^ 4 - (44550777975 / 8) * y ^ 5 - 3939806790 * y ^ 6 - (1420536135 / 2) * y ^ 7 + 4297860 * y ^ 8

/-- The `z^5`-jet of `∂_u f` at `u = 1/4 + z`. -/
noncomputable def nltJ5 (y : ℝ) : ℝ :=
  3089646 + 40777548 * y + (371707077 / 2) * y ^ 2 + 123635673 * y ^ 3 - (1939232631 / 2) * y ^ 4 - 2179444701 * y ^ 5 - 1491518322 * y ^ 6 - 254376276 * y ^ 7 + 2017008 * y ^ 8

/-- The `z^6`-jet of `∂_u f` at `u = 1/4 + z`. -/
noncomputable def nltJ6 (y : ℝ) : ℝ :=
  239904 + 5870872 * y + 32315892 * y ^ 2 + 28311696 * y ^ 3 - 139971244 * y ^ 4 - 319873092 * y ^ 5 - 213077536 * y ^ 6 - 34071184 * y ^ 7 + 411264 * y ^ 8

/-- The `z^7`-jet of `∂_u f` at `u = 1/4 + z`. -/
noncomputable def nltJ7 (y : ℝ) : ℝ :=
  308448 * y + 947376 * y ^ 2 - 1674432 * y ^ 3 - 9848304 * y ^ 4 - 14100480 * y ^ 5 - 8372160 * y ^ 6 - 1762560 * y ^ 7

theorem nlt_g_jet (z y : ℝ) : lrhHorner (nltDer (nltDer nltTAL0)) (1 / 4 + z) + lrhHorner (nltDer (nltDer nltTAL1)) (1 / 4 + z) * y + lrhHorner (nltDer (nltDer nltTAL2)) (1 / 4 + z) * y ^ 2 + lrhHorner (nltDer (nltDer nltTAL3)) (1 / 4 + z) * y ^ 3 + lrhHorner (nltDer (nltDer nltTAL4)) (1 / 4 + z) * y ^ 4 + lrhHorner (nltDer (nltDer nltTAL5)) (1 / 4 + z) * y ^ 5 + lrhHorner (nltDer (nltDer nltTAL6)) (1 / 4 + z) * y ^ 6 + lrhHorner (nltDer (nltDer nltTAL7)) (1 / 4 + z) * y ^ 7 + lrhHorner (nltDer (nltDer nltTAL8)) (1 / 4 + z) * y ^ 8 =
    nltJ0 y * z ^ 0 + nltJ1 y * z ^ 1 + nltJ2 y * z ^ 2 + nltJ3 y * z ^ 3 + nltJ4 y * z ^ 4 + nltJ5 y * z ^ 5 + nltJ6 y * z ^ 6 + nltJ7 y * z ^ 7 := by
  simp only [nltTAL0, nltTAL1, nltTAL2, nltTAL3, nltTAL4, nltTAL5, nltTAL6, nltTAL7, nltTAL8, nltDer, nltDerAux, lrhHorner]
  unfold nltJ0 nltJ1 nltJ2 nltJ3 nltJ4 nltJ5 nltJ6 nltJ7
  ring

/-- A jet sign: `J_1`. -/
noncomputable def nltJb1 (y : ℝ) : ℝ := nltJ1 y

/-- `nltJb1 > 0` on `[1/19, 9/32]`. -/
theorem nltJb1_pos {y : ℝ} (h1 : (1 / 19) ≤ y) (h2 : y ≤ (9 / 32)) : 0 < nltJb1 y := by
  obtain ⟨z, rfl⟩ : ∃ z, y = (1 / 19) + z := ⟨y - (1 / 19), by ring⟩
  have z0 : 0 ≤ z := by linarith
  have z1 : z ≤ (139 / 608) := by linarith
  have p2 : z ^ 2 ≤ (139 / 608) * z ^ 1 := nlt_pw z0 z1 1
  have q2 : 0 ≤ z ^ 2 := pow_nonneg z0 2
  have p3 : z ^ 3 ≤ (139 / 608) * z ^ 2 := nlt_pw z0 z1 2
  have q3 : 0 ≤ z ^ 3 := pow_nonneg z0 3
  have p4 : z ^ 4 ≤ (139 / 608) * z ^ 3 := nlt_pw z0 z1 3
  have q4 : 0 ≤ z ^ 4 := pow_nonneg z0 4
  have p5 : z ^ 5 ≤ (139 / 608) * z ^ 4 := nlt_pw z0 z1 4
  have q5 : 0 ≤ z ^ 5 := pow_nonneg z0 5
  have p6 : z ^ 6 ≤ (139 / 608) * z ^ 5 := nlt_pw z0 z1 5
  have q6 : 0 ≤ z ^ 6 := pow_nonneg z0 6
  have p7 : z ^ 7 ≤ (139 / 608) * z ^ 6 := nlt_pw z0 z1 6
  have q7 : 0 ≤ z ^ 7 := pow_nonneg z0 7
  have p8 : z ^ 8 ≤ (139 / 608) * z ^ 7 := nlt_pw z0 z1 7
  have q8 : 0 ≤ z ^ 8 := pow_nonneg z0 8
  have e : nltJb1 ((1 / 19) + z) = (7307229835913540765 / 4347792138496) + (3205069256697976707 / 228831165184) * z + (871645637498095473 / 24087491072) * z ^ 2 - (16564446793947127 / 633881344) * z ^ 3 - (29276424504694317 / 66724352) * z ^ 4 - (1732059761375409 / 1755904) * z ^ 5 - (31656440122533 / 46208) * z ^ 6 - (14331667173 / 152) * z ^ 7 + (42742413 / 16) * z ^ 8 := by unfold nltJb1 nltJ1; ring
  rw [e]; linarith only [z0, z1, p2, q2, p3, q3, p4, q4, p5, q5, p6, q6, p7, q7, p8, q8]


/-- A jet sign: `J_2`. -/
noncomputable def nltJb2 (y : ℝ) : ℝ := nltJ2 y

/-- `nltJb2 > 0` on `[1/19, 9/32]`. -/
theorem nltJb2_pos {y : ℝ} (h1 : (1 / 19) ≤ y) (h2 : y ≤ (9 / 32)) : 0 < nltJb2 y := by
  obtain ⟨z, rfl⟩ : ∃ z, y = (1 / 19) + z := ⟨y - (1 / 19), by ring⟩
  have z0 : 0 ≤ z := by linarith
  have z1 : z ≤ (139 / 608) := by linarith
  have p2 : z ^ 2 ≤ (139 / 608) * z ^ 1 := nlt_pw z0 z1 1
  have q2 : 0 ≤ z ^ 2 := pow_nonneg z0 2
  have p3 : z ^ 3 ≤ (139 / 608) * z ^ 2 := nlt_pw z0 z1 2
  have q3 : 0 ≤ z ^ 3 := pow_nonneg z0 3
  have p4 : z ^ 4 ≤ (139 / 608) * z ^ 3 := nlt_pw z0 z1 3
  have q4 : 0 ≤ z ^ 4 := pow_nonneg z0 4
  have p5 : z ^ 5 ≤ (139 / 608) * z ^ 4 := nlt_pw z0 z1 4
  have q5 : 0 ≤ z ^ 5 := pow_nonneg z0 5
  have p6 : z ^ 6 ≤ (139 / 608) * z ^ 5 := nlt_pw z0 z1 5
  have q6 : 0 ≤ z ^ 6 := pow_nonneg z0 6
  have p7 : z ^ 7 ≤ (139 / 608) * z ^ 6 := nlt_pw z0 z1 6
  have q7 : 0 ≤ z ^ 7 := pow_nonneg z0 7
  have p8 : z ^ 8 ≤ (139 / 608) * z ^ 7 := nlt_pw z0 z1 7
  have q8 : 0 ≤ z ^ 8 := pow_nonneg z0 8
  have e : nltJb2 ((1 / 19) + z) = (1203556067706902385 / 271737008656) + (639874078564822695 / 14301947824) * z + (104965708443923499 / 752734096) * z ^ 2 - (11413087132196031 / 79235168) * z ^ 3 - (7953824872466883 / 4170272) * z ^ 4 - (213964572994809 / 54872) * z ^ 5 - (30630780901209 / 11552) * z ^ 6 - (264547371807 / 608) * z ^ 7 + (21806217 / 4) * z ^ 8 := by unfold nltJb2 nltJ2; ring
  rw [e]; linarith only [z0, z1, p2, q2, p3, q3, p4, q4, p5, q5, p6, q6, p7, q7, p8, q8]


/-- A jet sign: `J_3`. -/
noncomputable def nltJb3 (y : ℝ) : ℝ := nltJ3 y

/-- `nltJb3 > 0` on `[1/19, 9/32]`. -/
theorem nltJb3_pos {y : ℝ} (h1 : (1 / 19) ≤ y) (h2 : y ≤ (9 / 32)) : 0 < nltJb3 y := by
  obtain ⟨z, rfl⟩ : ∃ z, y = (1 / 19) + z := ⟨y - (1 / 19), by ring⟩
  have z0 : 0 ≤ z := by linarith
  have z1 : z ≤ (139 / 608) := by linarith
  have p2 : z ^ 2 ≤ (139 / 608) * z ^ 1 := nlt_pw z0 z1 1
  have q2 : 0 ≤ z ^ 2 := pow_nonneg z0 2
  have p3 : z ^ 3 ≤ (139 / 608) * z ^ 2 := nlt_pw z0 z1 2
  have q3 : 0 ≤ z ^ 3 := pow_nonneg z0 3
  have p4 : z ^ 4 ≤ (139 / 608) * z ^ 3 := nlt_pw z0 z1 3
  have q4 : 0 ≤ z ^ 4 := pow_nonneg z0 4
  have p5 : z ^ 5 ≤ (139 / 608) * z ^ 4 := nlt_pw z0 z1 4
  have q5 : 0 ≤ z ^ 5 := pow_nonneg z0 5
  have p6 : z ^ 6 ≤ (139 / 608) * z ^ 5 := nlt_pw z0 z1 5
  have q6 : 0 ≤ z ^ 6 := pow_nonneg z0 6
  have p7 : z ^ 7 ≤ (139 / 608) * z ^ 6 := nlt_pw z0 z1 6
  have q7 : 0 ≤ z ^ 7 := pow_nonneg z0 7
  have p8 : z ^ 8 ≤ (139 / 608) * z ^ 7 := nlt_pw z0 z1 7
  have q8 : 0 ≤ z ^ 8 := pow_nonneg z0 8
  have e : nltJb3 ((1 / 19) + z) = (1557197688421477985 / 135868504328) + (424967497777911405 / 3575486956) * z + (63752396983736805 / 188183524) * z ^ 2 - (4473921606069095 / 9904396) * z ^ 3 - (4358398383882975 / 1042568) * z ^ 4 - (103498579403655 / 13718) * z ^ 5 - (3505602252195 / 722) * z ^ 6 - (15792641430 / 19) * z ^ 7 + 6096900 * z ^ 8 := by unfold nltJb3 nltJ3; ring
  rw [e]; linarith only [z0, z1, p2, q2, p3, q3, p4, q4, p5, q5, p6, q6, p7, q7, p8, q8]


/-- A jet sign: `J_4`. -/
noncomputable def nltJb4 (y : ℝ) : ℝ := nltJ4 y

/-- `nltJb4 > 0` on `[1/19, 9/32]`. -/
theorem nltJb4_pos {y : ℝ} (h1 : (1 / 19) ≤ y) (h2 : y ≤ (9 / 32)) : 0 < nltJb4 y := by
  obtain ⟨z, rfl⟩ : ∃ z, y = (1 / 19) + z := ⟨y - (1 / 19), by ring⟩
  have z0 : 0 ≤ z := by linarith
  have z1 : z ≤ (139 / 608) := by linarith
  have p2 : z ^ 2 ≤ (139 / 608) * z ^ 1 := nlt_pw z0 z1 1
  have q2 : 0 ≤ z ^ 2 := pow_nonneg z0 2
  have p3 : z ^ 3 ≤ (139 / 608) * z ^ 2 := nlt_pw z0 z1 2
  have q3 : 0 ≤ z ^ 3 := pow_nonneg z0 3
  have p4 : z ^ 4 ≤ (139 / 608) * z ^ 3 := nlt_pw z0 z1 3
  have q4 : 0 ≤ z ^ 4 := pow_nonneg z0 4
  have p5 : z ^ 5 ≤ (139 / 608) * z ^ 4 := nlt_pw z0 z1 4
  have q5 : 0 ≤ z ^ 5 := pow_nonneg z0 5
  have p6 : z ^ 6 ≤ (139 / 608) * z ^ 5 := nlt_pw z0 z1 5
  have q6 : 0 ≤ z ^ 6 := pow_nonneg z0 6
  have p7 : z ^ 7 ≤ (139 / 608) * z ^ 6 := nlt_pw z0 z1 6
  have q7 : 0 ≤ z ^ 7 := pow_nonneg z0 7
  have p8 : z ^ 8 ≤ (139 / 608) * z ^ 7 := nlt_pw z0 z1 7
  have q8 : 0 ≤ z ^ 8 := pow_nonneg z0 8
  have e : nltJb4 ((1 / 19) + z) = (1939869128472485415 / 135868504328) + (995672521195665135 / 7150973912) * z + (141189413150019765 / 376367048) * z ^ 2 - (4969290009762375 / 9904396) * z ^ 3 - (1068492886638255 / 260642) * z ^ 4 - (376108008417825 / 54872) * z ^ 5 - (3033231128175 / 722) * z ^ 6 - (26921420805 / 38) * z ^ 7 + 4297860 * z ^ 8 := by unfold nltJb4 nltJ4; ring
  rw [e]; linarith only [z0, z1, p2, q2, p3, q3, p4, q4, p5, q5, p6, q6, p7, q7, p8, q8]


/-- A jet sign: `J_5`. -/
noncomputable def nltJb5 (y : ℝ) : ℝ := nltJ5 y

/-- `nltJb5 > 0` on `[1/19, 9/32]`. -/
theorem nltJb5_pos {y : ℝ} (h1 : (1 / 19) ≤ y) (h2 : y ≤ (9 / 32)) : 0 < nltJb5 y := by
  obtain ⟨z, rfl⟩ : ∃ z, y = (1 / 19) + z := ⟨y - (1 / 19), by ring⟩
  have z0 : 0 ≤ z := by linarith
  have z1 : z ≤ (139 / 608) := by linarith
  have p2 : z ^ 2 ≤ (139 / 608) * z ^ 1 := nlt_pw z0 z1 1
  have q2 : 0 ≤ z ^ 2 := pow_nonneg z0 2
  have p3 : z ^ 3 ≤ (139 / 608) * z ^ 2 := nlt_pw z0 z1 2
  have q3 : 0 ≤ z ^ 3 := pow_nonneg z0 3
  have p4 : z ^ 4 ≤ (139 / 608) * z ^ 3 := nlt_pw z0 z1 3
  have q4 : 0 ≤ z ^ 4 := pow_nonneg z0 4
  have p5 : z ^ 5 ≤ (139 / 608) * z ^ 4 := nlt_pw z0 z1 4
  have q5 : 0 ≤ z ^ 5 := pow_nonneg z0 5
  have p6 : z ^ 6 ≤ (139 / 608) * z ^ 5 := nlt_pw z0 z1 5
  have q6 : 0 ≤ z ^ 6 := pow_nonneg z0 6
  have p7 : z ^ 7 ≤ (139 / 608) * z ^ 6 := nlt_pw z0 z1 6
  have q7 : 0 ≤ z ^ 7 := pow_nonneg z0 7
  have p8 : z ^ 8 ≤ (139 / 608) * z ^ 7 := nlt_pw z0 z1 7
  have q8 : 0 ≤ z ^ 8 := pow_nonneg z0 8
  have e : nltJb5 ((1 / 19) + z) = (97831019531966091 / 16983563041) + (54272133181130697 / 893871739) * z + (17492423248024053 / 94091762) * z ^ 2 - (359737226726997 / 2476099) * z ^ 3 - (418702029239361 / 260642) * z ^ 4 - (18280823071287 / 6859) * z ^ 5 - (572213682726 / 361) * z ^ 6 - (4817013180 / 19) * z ^ 7 + 2017008 * z ^ 8 := by unfold nltJb5 nltJ5; ring
  rw [e]; linarith only [z0, z1, p2, q2, p3, q3, p4, q4, p5, q5, p6, q6, p7, q7, p8, q8]


/-- A jet sign: `J_6`. -/
noncomputable def nltJb6 (y : ℝ) : ℝ := nltJ6 y

/-- `nltJb6 > 0` on `[1/19, 9/32]`. -/
theorem nltJb6_pos {y : ℝ} (h1 : (1 / 19) ≤ y) (h2 : y ≤ (9 / 32)) : 0 < nltJb6 y := by
  obtain ⟨z, rfl⟩ : ∃ z, y = (1 / 19) + z := ⟨y - (1 / 19), by ring⟩
  have z0 : 0 ≤ z := by linarith
  have z1 : z ≤ (139 / 608) := by linarith
  have p2 : z ^ 2 ≤ (139 / 608) * z ^ 1 := nlt_pw z0 z1 1
  have q2 : 0 ≤ z ^ 2 := pow_nonneg z0 2
  have p3 : z ^ 3 ≤ (139 / 608) * z ^ 2 := nlt_pw z0 z1 2
  have q3 : 0 ≤ z ^ 3 := pow_nonneg z0 3
  have p4 : z ^ 4 ≤ (139 / 608) * z ^ 3 := nlt_pw z0 z1 3
  have q4 : 0 ≤ z ^ 4 := pow_nonneg z0 4
  have p5 : z ^ 5 ≤ (139 / 608) * z ^ 4 := nlt_pw z0 z1 4
  have q5 : 0 ≤ z ^ 5 := pow_nonneg z0 5
  have p6 : z ^ 6 ≤ (139 / 608) * z ^ 5 := nlt_pw z0 z1 5
  have q6 : 0 ≤ z ^ 6 := pow_nonneg z0 6
  have p7 : z ^ 7 ≤ (139 / 608) * z ^ 6 := nlt_pw z0 z1 6
  have q7 : 0 ≤ z ^ 7 := pow_nonneg z0 7
  have p8 : z ^ 8 ≤ (139 / 608) * z ^ 7 := nlt_pw z0 z1 7
  have q8 : 0 ≤ z ^ 8 := pow_nonneg z0 8
  have e : nltJb6 ((1 / 19) + z) = (10892150673510148 / 16983563041) + (8414372597662052 / 893871739) * z + (1598082647841876 / 47045881) * z ^ 2 - (26363357300168 / 2476099) * z ^ 3 - (30387683585784 / 130321) * z ^ 4 - (2669106852636 / 6859) * z ^ 5 - (81440942576 / 361) * z ^ 6 - (644062384 / 19) * z ^ 7 + 411264 * z ^ 8 := by unfold nltJb6 nltJ6; ring
  rw [e]; linarith only [z0, z1, p2, q2, p3, q3, p4, q4, p5, q5, p6, q6, p7, q7, p8, q8]


/-- A jet sign: `J_7`. -/
noncomputable def nltJb7 (y : ℝ) : ℝ := nltJ7 y

/-- `nltJb7 > 0` on `[1/19, 9/32]`. -/
theorem nltJb7_pos {y : ℝ} (h1 : (1 / 19) ≤ y) (h2 : y ≤ (9 / 32)) : 0 < nltJb7 y := by
  obtain ⟨z, rfl⟩ : ∃ z, y = (1 / 19) + z := ⟨y - (1 / 19), by ring⟩
  have z0 : 0 ≤ z := by linarith
  have z1 : z ≤ (139 / 608) := by linarith
  have p2 : z ^ 2 ≤ (139 / 608) * z ^ 1 := nlt_pw z0 z1 1
  have q2 : 0 ≤ z ^ 2 := pow_nonneg z0 2
  have p3 : z ^ 3 ≤ (139 / 608) * z ^ 2 := nlt_pw z0 z1 2
  have q3 : 0 ≤ z ^ 3 := pow_nonneg z0 3
  have p4 : z ^ 4 ≤ (139 / 608) * z ^ 3 := nlt_pw z0 z1 3
  have q4 : 0 ≤ z ^ 4 := pow_nonneg z0 4
  have p5 : z ^ 5 ≤ (139 / 608) * z ^ 4 := nlt_pw z0 z1 4
  have q5 : 0 ≤ z ^ 5 := pow_nonneg z0 5
  have p6 : z ^ 6 ≤ (139 / 608) * z ^ 5 := nlt_pw z0 z1 5
  have q6 : 0 ≤ z ^ 6 := pow_nonneg z0 6
  have p7 : z ^ 7 ≤ (139 / 608) * z ^ 6 := nlt_pw z0 z1 6
  have q7 : 0 ≤ z ^ 7 := pow_nonneg z0 7
  have e : nltJb7 ((1 / 19) + z) = (16565990392224 / 893871739) + (18251544278016 / 47045881) * z + (1232532893232 / 2476099) * z ^ 2 - (542557564416 / 130321) * z ^ 3 - (95448638736 / 6859) * z ^ 4 - (6081713280 / 361) * z ^ 5 - (171408960 / 19) * z ^ 6 - 1762560 * z ^ 7 := by unfold nltJb7 nltJ7; ring
  rw [e]; linarith only [z0, z1, p2, q2, p3, q3, p4, q4, p5, q5, p6, q6, p7, q7]


/-- The leading jet bound `J₀ + J₁/30`. -/
noncomputable def nltJb0 (y : ℝ) : ℝ := nltJ0 y + nltJ1 y / 30

/-- `nltJb0 > 0` on `[1/19, 9/32]`. -/
theorem nltJb0_pos {y : ℝ} (h1 : (1 / 19) ≤ y) (h2 : y ≤ (9 / 32)) : 0 < nltJb0 y := by
  obtain ⟨z, rfl⟩ : ∃ z, y = (1 / 19) + z := ⟨y - (1 / 19), by ring⟩
  have z0 : 0 ≤ z := by linarith
  have z1 : z ≤ (139 / 608) := by linarith
  have p2 : z ^ 2 ≤ (139 / 608) * z ^ 1 := nlt_pw z0 z1 1
  have q2 : 0 ≤ z ^ 2 := pow_nonneg z0 2
  have p3 : z ^ 3 ≤ (139 / 608) * z ^ 2 := nlt_pw z0 z1 2
  have q3 : 0 ≤ z ^ 3 := pow_nonneg z0 3
  have p4 : z ^ 4 ≤ (139 / 608) * z ^ 3 := nlt_pw z0 z1 3
  have q4 : 0 ≤ z ^ 4 := pow_nonneg z0 4
  have p5 : z ^ 5 ≤ (139 / 608) * z ^ 4 := nlt_pw z0 z1 4
  have q5 : 0 ≤ z ^ 5 := pow_nonneg z0 5
  have p6 : z ^ 6 ≤ (139 / 608) * z ^ 5 := nlt_pw z0 z1 5
  have q6 : 0 ≤ z ^ 6 := pow_nonneg z0 6
  have p7 : z ^ 7 ≤ (139 / 608) * z ^ 6 := nlt_pw z0 z1 6
  have q7 : 0 ≤ z ^ 7 := pow_nonneg z0 7
  have p8 : z ^ 8 ≤ (139 / 608) * z ^ 7 := nlt_pw z0 z1 7
  have q8 : 0 ≤ z ^ 8 := pow_nonneg z0 8
  have e : nltJb0 ((1 / 19) + z) = (569413321874500619 / 34782337107968) + (60109762042966664533 / 27459739822080) * z + (11604635234540959961 / 1445249464320) * z ^ 2 - (29647426449328423 / 12677626880) * z ^ 3 - (133268265865857487 / 2001730560) * z ^ 4 - (10227811351217297 / 70236160) * z ^ 5 - (44205350826391 / 462080) * z ^ 6 - (55721335069 / 6080) * z ^ 7 + (49447173 / 80) * z ^ 8 := by unfold nltJb0 nltJ0 nltJ1; ring
  rw [e]; linarith only [z0, z1, p2, q2, p3, q3, p4, q4, p5, q5, p6, q6, p7, q7, p8, q8]


/-- `T_A(17/60, y)`. -/
noncomputable def nltTq (y : ℝ) : ℝ := (2850256052094343 / 1555200000000) - (14986767725456749631 / 839808000000000) * y - (3643095336976133221 / 186624000000000) * y ^ 2 + (64447961101503848429 / 139968000000000) * y ^ 3 - (511850166184543236329 / 1679616000000000) * y ^ 4 - (7669519894759794287 / 4478976000000) * y ^ 5 - (3012099691707234173 / 2624400000000) * y ^ 6 - (199803439512859 / 8201250000) * y ^ 7 + (1344872325172 / 94921875) * y ^ 8

/-- `nltTq > 0` on `[13/64, 9/32]`. -/
theorem nltTq_pos {y : ℝ} (h1 : (13 / 64) ≤ y) (h2 : y ≤ (9 / 32)) : 0 < nltTq y := by
  obtain ⟨z, rfl⟩ : ∃ z, y = (13 / 64) + z := ⟨y - (13 / 64), by ring⟩
  have z0 : 0 ≤ z := by linarith
  have z1 : z ≤ (5 / 64) := by linarith
  have p2 : z ^ 2 ≤ (5 / 64) * z ^ 1 := nlt_pw z0 z1 1
  have q2 : 0 ≤ z ^ 2 := pow_nonneg z0 2
  have p3 : z ^ 3 ≤ (5 / 64) * z ^ 2 := nlt_pw z0 z1 2
  have q3 : 0 ≤ z ^ 3 := pow_nonneg z0 3
  have p4 : z ^ 4 ≤ (5 / 64) * z ^ 3 := nlt_pw z0 z1 3
  have q4 : 0 ≤ z ^ 4 := pow_nonneg z0 4
  have p5 : z ^ 5 ≤ (5 / 64) * z ^ 4 := nlt_pw z0 z1 4
  have q5 : 0 ≤ z ^ 5 := pow_nonneg z0 5
  have p6 : z ^ 6 ≤ (5 / 64) * z ^ 5 := nlt_pw z0 z1 5
  have q6 : 0 ≤ z ^ 6 := pow_nonneg z0 6
  have p7 : z ^ 7 ≤ (5 / 64) * z ^ 6 := nlt_pw z0 z1 6
  have q7 : 0 ≤ z ^ 7 := pow_nonneg z0 7
  have p8 : z ^ 8 ≤ (5 / 64) * z ^ 7 := nlt_pw z0 z1 7
  have q8 : 0 ≤ z ^ 8 := pow_nonneg z0 8
  have e : nltTq ((13 / 64) + z) = (25094595692146902147805117 / 360694789491916800000000) + (22741768048316100978288713 / 5635856085811200000000) * z + (928793756006343086874347 / 73383542784000000000) * z ^ 2 - (1181966255213205791872381 / 1719926784000000000) * z ^ 3 - (32960709781567978516309 / 11943936000000000) * z ^ 4 - (349986275533610629373 / 111974400000000) * z ^ 5 - (1530026844873633083 / 1312200000000) * z ^ 6 - (54916825293551 / 41006250000) * z ^ 7 + (1344872325172 / 94921875) * z ^ 8 := by unfold nltTq; ring
  rw [e]; linarith only [z0, z1, p2, q2, p3, q3, p4, q4, p5, q5, p6, q6, p7, q7, p8, q8]


theorem nlt_Tq_eq (y : ℝ) : lrhHorner nltTAL0 (17 / 60) + lrhHorner nltTAL1 (17 / 60) * y + lrhHorner nltTAL2 (17 / 60) * y ^ 2 + lrhHorner nltTAL3 (17 / 60) * y ^ 3 + lrhHorner nltTAL4 (17 / 60) * y ^ 4 + lrhHorner nltTAL5 (17 / 60) * y ^ 5 + lrhHorner nltTAL6 (17 / 60) * y ^ 6 + lrhHorner nltTAL7 (17 / 60) * y ^ 7 + lrhHorner nltTAL8 (17 / 60) * y ^ 8 = nltTq y := by
  simp only [nltTAL0, nltTAL1, nltTAL2, nltTAL3, nltTAL4, nltTAL5, nltTAL6, nltTAL7, nltTAL8, lrhHorner]; unfold nltTq; ring

/-- `U_0(u)`: the `u`-derivative of the `y^0`-coefficient of `T_B`. -/
noncomputable def nltU0 (u : ℝ) : ℝ :=
  (61451961 / 800) - (244136781 / 400) * u + (288955339 / 400) * u ^ 2 + (178526227 / 400) * u ^ 3 + (30173563 / 80) * u ^ 4 + (17840823 / 10) * u ^ 5 + (22013397 / 25) * u ^ 6 + (1679328 / 25) * u ^ 7

theorem nlt_U_eq0 (u : ℝ) : lrhHorner (nltDer nltTBL0) u = nltU0 u := by
  simp only [nltTBL0, nltDer, nltDerAux, lrhHorner]; unfold nltU0; ring

/-- `U_1(u)`: the `u`-derivative of the `y^1`-coefficient of `T_B`. -/
noncomputable def nltU1 (u : ℝ) : ℝ :=
  -(110194151 / 1600) - (25291101 / 800) * u + (86262489 / 160) * u ^ 2 - (2486010049 / 800) * u ^ 3 + (3431817 / 160) * u ^ 4 + (1195862907 / 100) * u ^ 5 + (172971519 / 25) * u ^ 6 + (30269456 / 25) * u ^ 7 + (1889244 / 25) * u ^ 8

theorem nlt_U_eq1 (u : ℝ) : lrhHorner (nltDer nltTBL1) u = nltU1 u := by
  simp only [nltTBL1, nltDer, nltDerAux, lrhHorner]; unfold nltU1; ring

/-- `U_2(u)`: the `u`-derivative of the `y^2`-coefficient of `T_B`. -/
noncomputable def nltU2 (u : ℝ) : ℝ :=
  (40983299 / 600) + (709057637 / 400) * u - (963507471 / 800) * u ^ 2 - (354117588 / 25) * u ^ 3 - (1842852919 / 160) * u ^ 4 + (211620201 / 50) * u ^ 5 + (45000361 / 4) * u ^ 6 + (78674288 / 25) * u ^ 7 - (1754298 / 25) * u ^ 8

theorem nlt_U_eq2 (u : ℝ) : lrhHorner (nltDer nltTBL2) u = nltU2 u := by
  simp only [nltTBL2, nltDer, nltDerAux, lrhHorner]; unfold nltU2; ring

/-- `U_3(u)`: the `u`-derivative of the `y^3`-coefficient of `T_B`. -/
noncomputable def nltU3 (u : ℝ) : ℝ :=
  (4545323 / 150) + (837305953 / 800) * u + (2361568841 / 400) * u ^ 2 + (26286922649 / 800) * u ^ 3 - (1199783523 / 160) * u ^ 4 - (9587420751 / 100) * u ^ 5 - (530095573 / 10) * u ^ 6 - (197505008 / 25) * u ^ 7 - (2159136 / 5) * u ^ 8

theorem nlt_U_eq3 (u : ℝ) : lrhHorner (nltDer nltTBL3) u = nltU3 u := by
  simp only [nltTBL3, nltDer, nltDerAux, lrhHorner]; unfold nltU3; ring

/-- `U_4(u)`: the `u`-derivative of the `y^4`-coefficient of `T_B`. -/
noncomputable def nltU4 (u : ℝ) : ℝ :=
  -(69676949 / 800) - (568575099 / 200) * u + (289218753 / 40) * u ^ 2 + (3109324163 / 50) * u ^ 3 + (249052181 / 20) * u ^ 4 - (5777582229 / 50) * u ^ 5 - (294285411 / 4) * u ^ 6 - (302415336 / 25) * u ^ 7 - 404838 * u ^ 8

theorem nlt_U_eq4 (u : ℝ) : lrhHorner (nltDer nltTBL4) u = nltU4 u := by
  simp only [nltTBL4, nltDer, nltDerAux, lrhHorner]; unfold nltU4; ring

/-- `U_5(u)`: the `u`-derivative of the `y^5`-coefficient of `T_B`. -/
noncomputable def nltU5 (u : ℝ) : ℝ :=
  -(53679249 / 1600) - (1708508289 / 800) * u - (163305051 / 400) * u ^ 2 + (14966563273 / 800) * u ^ 3 + (1403903137 / 160) * u ^ 4 - (5140679427 / 200) * u ^ 5 - (761285903 / 50) * u ^ 6 - (52026284 / 25) * u ^ 7 - (539784 / 5) * u ^ 8

theorem nlt_U_eq5 (u : ℝ) : lrhHorner (nltDer nltTBL5) u = nltU5 u := by
  simp only [nltTBL5, nltDer, nltDerAux, lrhHorner]; unfold nltU5; ring

/-- `U_6(u)`: the `u`-derivative of the `y^6`-coefficient of `T_B`. -/
noncomputable def nltU6 (u : ℝ) : ℝ :=
  -(445233 / 80) - (1033998 / 25) * u - (10268763 / 400) * u ^ 2 + (17799707 / 200) * u ^ 3 + (9057747 / 40) * u ^ 4 + (3201168 / 25) * u ^ 5 + (2792174 / 25) * u ^ 6 + (923712 / 25) * u ^ 7

theorem nlt_U_eq6 (u : ℝ) : lrhHorner (nltDer nltTBL6) u = nltU6 u := by
  simp only [nltTBL6, nltDer, nltDerAux, lrhHorner]; unfold nltU6; ring

/-- A coefficient bound for `∂_uT_B`: `U_0`. -/
noncomputable def nltUb0 (u : ℝ) : ℝ := nltU0 u

/-- `nltUb0 > 20000` on `[3/7, 41/84]`. -/
theorem nltUb0_pos {u : ℝ} (h1 : (3 / 7) ≤ u) (h2 : u ≤ (41 / 84)) : 20000 < nltUb0 u := by
  obtain ⟨z, rfl⟩ : ∃ z, u = (3 / 7) + z := ⟨u - (3 / 7), by ring⟩
  have z0 : 0 ≤ z := by linarith
  have z1 : z ≤ (5 / 84) := by linarith
  have p2 : z ^ 2 ≤ (5 / 84) * z ^ 1 := nlt_pw z0 z1 1
  have q2 : 0 ≤ z ^ 2 := pow_nonneg z0 2
  have p3 : z ^ 3 ≤ (5 / 84) * z ^ 2 := nlt_pw z0 z1 2
  have q3 : 0 ≤ z ^ 3 := pow_nonneg z0 3
  have p4 : z ^ 4 ≤ (5 / 84) * z ^ 3 := nlt_pw z0 z1 3
  have q4 : 0 ≤ z ^ 4 := pow_nonneg z0 4
  have p5 : z ^ 5 ≤ (5 / 84) * z ^ 4 := nlt_pw z0 z1 4
  have q5 : 0 ≤ z ^ 5 := pow_nonneg z0 5
  have p6 : z ^ 6 ≤ (5 / 84) * z ^ 5 := nlt_pw z0 z1 5
  have q6 : 0 ≤ z ^ 6 := pow_nonneg z0 6
  have p7 : z ^ 7 ≤ (5 / 84) * z ^ 6 := nlt_pw z0 z1 6
  have q7 : 0 ≤ z ^ 7 := pow_nonneg z0 7
  have e : nltUb0 ((3 / 7) + z) = (10452820341 / 384160) + (51708909549 / 68600) * z + (1404237881 / 392) * z ^ 2 + (16339006249 / 2800) * z ^ 3 + (544899043 / 80) * z ^ 4 + (215370687 / 50) * z ^ 5 + (27051381 / 25) * z ^ 6 + (1679328 / 25) * z ^ 7 := by unfold nltUb0 nltU0; ring
  rw [e]; linarith only [z0, z1, p2, q2, p3, q3, p4, q4, p5, q5, p6, q6, p7, q7]


/-- A coefficient bound for `∂_uT_B`: `U_1`. -/
noncomputable def nltUb1 (u : ℝ) : ℝ := nltU1 u

/-- `nltUb1 > -20000` on `[3/7, 41/84]`. -/
theorem nltUb1_pos {u : ℝ} (h1 : (3 / 7) ≤ u) (h2 : u ≤ (41 / 84)) : (-20000) < nltUb1 u := by
  obtain ⟨z, rfl⟩ : ∃ z, u = (3 / 7) + z := ⟨u - (3 / 7), by ring⟩
  have z0 : 0 ≤ z := by linarith
  have z1 : z ≤ (5 / 84) := by linarith
  have p2 : z ^ 2 ≤ (5 / 84) * z ^ 1 := nlt_pw z0 z1 1
  have q2 : 0 ≤ z ^ 2 := pow_nonneg z0 2
  have p3 : z ^ 3 ≤ (5 / 84) * z ^ 2 := nlt_pw z0 z1 2
  have q3 : 0 ≤ z ^ 3 := pow_nonneg z0 3
  have p4 : z ^ 4 ≤ (5 / 84) * z ^ 3 := nlt_pw z0 z1 3
  have q4 : 0 ≤ z ^ 4 := pow_nonneg z0 4
  have p5 : z ^ 5 ≤ (5 / 84) * z ^ 4 := nlt_pw z0 z1 4
  have q5 : 0 ≤ z ^ 5 := pow_nonneg z0 5
  have p6 : z ^ 6 ≤ (5 / 84) * z ^ 5 := nlt_pw z0 z1 5
  have q6 : 0 ≤ z ^ 6 := pow_nonneg z0 6
  have p7 : z ^ 7 ≤ (5 / 84) * z ^ 6 := nlt_pw z0 z1 6
  have q7 : 0 ≤ z ^ 7 := pow_nonneg z0 7
  have p8 : z ^ 8 ≤ (5 / 84) * z ^ 7 := nlt_pw z0 z1 7
  have q8 : 0 ≤ z ^ 8 := pow_nonneg z0 8
  have e : nltUb1 ((3 / 7) + z) = -(44161151701 / 5378240) + (1341166326987 / 960400) * z + (676591462233 / 68600) * z ^ 2 + (1226080940867 / 39200) * z ^ 3 + (54010349991 / 1120) * z ^ 4 + (3475325379 / 100) * z ^ 5 + (273495999 / 25) * z ^ 6 + (36746864 / 25) * z ^ 7 + (1889244 / 25) * z ^ 8 := by unfold nltUb1 nltU1; ring
  rw [e]; linarith only [z0, z1, p2, q2, p3, q3, p4, q4, p5, q5, p6, q6, p7, q7, p8, q8]


/-- A coefficient bound for `∂_uT_B`: `U_2`. -/
noncomputable def nltUb2 (u : ℝ) : ℝ := nltU2 u

/-- `nltUb2 > -1600000` on `[3/7, 41/84]`. -/
theorem nltUb2_pos {u : ℝ} (h1 : (3 / 7) ≤ u) (h2 : u ≤ (41 / 84)) : (-1600000) < nltUb2 u := by
  obtain ⟨z, rfl⟩ : ∃ z, u = (3 / 7) + z := ⟨u - (3 / 7), by ring⟩
  have z0 : 0 ≤ z := by linarith
  have z1 : z ≤ (5 / 84) := by linarith
  have p2 : z ^ 2 ≤ (5 / 84) * z ^ 1 := nlt_pw z0 z1 1
  have q2 : 0 ≤ z ^ 2 := pow_nonneg z0 2
  have p3 : z ^ 3 ≤ (5 / 84) * z ^ 2 := nlt_pw z0 z1 2
  have q3 : 0 ≤ z ^ 3 := pow_nonneg z0 3
  have p4 : z ^ 4 ≤ (5 / 84) * z ^ 3 := nlt_pw z0 z1 3
  have q4 : 0 ≤ z ^ 4 := pow_nonneg z0 4
  have p5 : z ^ 5 ≤ (5 / 84) * z ^ 4 := nlt_pw z0 z1 4
  have q5 : 0 ≤ z ^ 5 := pow_nonneg z0 5
  have p6 : z ^ 6 ≤ (5 / 84) * z ^ 5 := nlt_pw z0 z1 5
  have q6 : 0 ≤ z ^ 6 := pow_nonneg z0 6
  have p7 : z ^ 7 ≤ (5 / 84) * z ^ 6 := nlt_pw z0 z1 6
  have q7 : 0 ≤ z ^ 7 := pow_nonneg z0 7
  have p8 : z ^ 8 ≤ (5 / 84) * z ^ 7 := nlt_pw z0 z1 7
  have q8 : 0 ≤ z ^ 8 := pow_nonneg z0 8
  have e : nltUb2 ((3 / 7) + z) = -(1527945023411 / 2016840) - (14901862756843 / 1680700) * z - (6075580895871 / 274400) * z ^ 2 - (266853681 / 56) * z ^ 3 + (41497420823 / 1120) * z ^ 4 + (1124754924 / 25) * z ^ 5 + (406602413 / 20) * z ^ 6 + (72659552 / 25) * z ^ 7 - (1754298 / 25) * z ^ 8 := by unfold nltUb2 nltU2; ring
  rw [e]; linarith only [z0, z1, p2, q2, p3, q3, p4, q4, p5, q5, p6, q6, p7, q7, p8, q8]


/-- A coefficient bound for `∂_uT_B`: `U_3`. -/
noncomputable def nltUb3 (u : ℝ) : ℝ := nltU3 u

/-- `nltUb3 > 0` on `[3/7, 41/84]`. -/
theorem nltUb3_pos {u : ℝ} (h1 : (3 / 7) ≤ u) (h2 : u ≤ (41 / 84)) : 0 < nltUb3 u := by
  obtain ⟨z, rfl⟩ : ∃ z, u = (3 / 7) + z := ⟨u - (3 / 7), by ring⟩
  have z0 : 0 ≤ z := by linarith
  have z1 : z ≤ (5 / 84) := by linarith
  have p2 : z ^ 2 ≤ (5 / 84) * z ^ 1 := nlt_pw z0 z1 1
  have q2 : 0 ≤ z ^ 2 := pow_nonneg z0 2
  have p3 : z ^ 3 ≤ (5 / 84) * z ^ 2 := nlt_pw z0 z1 2
  have q3 : 0 ≤ z ^ 3 := pow_nonneg z0 3
  have p4 : z ^ 4 ≤ (5 / 84) * z ^ 3 := nlt_pw z0 z1 3
  have q4 : 0 ≤ z ^ 4 := pow_nonneg z0 4
  have p5 : z ^ 5 ≤ (5 / 84) * z ^ 4 := nlt_pw z0 z1 4
  have q5 : 0 ≤ z ^ 5 := pow_nonneg z0 5
  have p6 : z ^ 6 ≤ (5 / 84) * z ^ 5 := nlt_pw z0 z1 5
  have q6 : 0 ≤ z ^ 6 := pow_nonneg z0 6
  have p7 : z ^ 7 ≤ (5 / 84) * z ^ 6 := nlt_pw z0 z1 6
  have q7 : 0 ≤ z ^ 7 := pow_nonneg z0 7
  have p8 : z ^ 8 ≤ (5 / 84) * z ^ 7 := nlt_pw z0 z1 7
  have q8 : 0 ≤ z ^ 8 := pow_nonneg z0 8
  have e : nltUb3 ((3 / 7) + z) = (854128531340389 / 395300640) + (350258683561 / 480200) * z - (124623549993569 / 1920800) * z ^ 2 - (68387282997253 / 274400) * z ^ 3 - (2993121815547 / 7840) * z ^ 4 - (185192184621 / 700) * z ^ 5 - (3946549193 / 50) * z ^ 6 - (234518768 / 25) * z ^ 7 - (2159136 / 5) * z ^ 8 := by unfold nltUb3 nltU3; ring
  rw [e]; linarith only [z0, z1, p2, q2, p3, q3, p4, q4, p5, q5, p6, q6, p7, q7, p8, q8]


/-- A coefficient bound for `∂_uT_B`: `U_4`. -/
noncomputable def nltUb4 (u : ℝ) : ℝ := nltU4 u

/-- `nltUb4 > 0` on `[3/7, 41/84]`. -/
theorem nltUb4_pos {u : ℝ} (h1 : (3 / 7) ≤ u) (h2 : u ≤ (41 / 84)) : 0 < nltUb4 u := by
  obtain ⟨z, rfl⟩ : ∃ z, u = (3 / 7) + z := ⟨u - (3 / 7), by ring⟩
  have z0 : 0 ≤ z := by linarith
  have z1 : z ≤ (5 / 84) := by linarith
  have p2 : z ^ 2 ≤ (5 / 84) * z ^ 1 := nlt_pw z0 z1 1
  have q2 : 0 ≤ z ^ 2 := pow_nonneg z0 2
  have p3 : z ^ 3 ≤ (5 / 84) * z ^ 2 := nlt_pw z0 z1 2
  have q3 : 0 ≤ z ^ 3 := pow_nonneg z0 3
  have p4 : z ^ 4 ≤ (5 / 84) * z ^ 3 := nlt_pw z0 z1 3
  have q4 : 0 ≤ z ^ 4 := pow_nonneg z0 4
  have p5 : z ^ 5 ≤ (5 / 84) * z ^ 4 := nlt_pw z0 z1 4
  have q5 : 0 ≤ z ^ 5 := pow_nonneg z0 5
  have p6 : z ^ 6 ≤ (5 / 84) * z ^ 5 := nlt_pw z0 z1 5
  have q6 : 0 ≤ z ^ 6 := pow_nonneg z0 6
  have p7 : z ^ 7 ≤ (5 / 84) * z ^ 6 := nlt_pw z0 z1 6
  have q7 : 0 ≤ z ^ 7 := pow_nonneg z0 7
  have p8 : z ^ 8 ≤ (5 / 84) * z ^ 7 := nlt_pw z0 z1 7
  have q8 : 0 ≤ z ^ 8 := pow_nonneg z0 8
  have e : nltUb4 ((3 / 7) + z) = (83769016767901 / 26353376) + (50874245233677 / 3361400) * z - (14897848794093 / 480200) * z ^ 2 - (4444276321501 / 17150) * z ^ 3 - (231347658131 / 490) * z ^ 4 - (61806164211 / 175) * z ^ 5 - (11194321707 / 100) * z ^ 6 - (337115736 / 25) * z ^ 7 - 404838 * z ^ 8 := by unfold nltUb4 nltU4; ring
  rw [e]; linarith only [z0, z1, p2, q2, p3, q3, p4, q4, p5, q5, p6, q6, p7, q7, p8, q8]


/-- A coefficient bound for `∂_uT_B`: `U_5`. -/
noncomputable def nltUb5 (u : ℝ) : ℝ := nltU5 u

/-- `nltUb5 > 0` on `[3/7, 41/84]`. -/
theorem nltUb5_pos {u : ℝ} (h1 : (3 / 7) ≤ u) (h2 : u ≤ (41 / 84)) : 0 < nltUb5 u := by
  obtain ⟨z, rfl⟩ : ∃ z, u = (3 / 7) + z := ⟨u - (3 / 7), by ring⟩
  have z0 : 0 ≤ z := by linarith
  have z1 : z ≤ (5 / 84) := by linarith
  have p2 : z ^ 2 ≤ (5 / 84) * z ^ 1 := nlt_pw z0 z1 1
  have q2 : 0 ≤ z ^ 2 := pow_nonneg z0 2
  have p3 : z ^ 3 ≤ (5 / 84) * z ^ 2 := nlt_pw z0 z1 2
  have q3 : 0 ≤ z ^ 3 := pow_nonneg z0 3
  have p4 : z ^ 4 ≤ (5 / 84) * z ^ 3 := nlt_pw z0 z1 3
  have q4 : 0 ≤ z ^ 4 := pow_nonneg z0 4
  have p5 : z ^ 5 ≤ (5 / 84) * z ^ 4 := nlt_pw z0 z1 4
  have q5 : 0 ≤ z ^ 5 := pow_nonneg z0 5
  have p6 : z ^ 6 ≤ (5 / 84) * z ^ 5 := nlt_pw z0 z1 5
  have q6 : 0 ≤ z ^ 6 := pow_nonneg z0 6
  have p7 : z ^ 7 ≤ (5 / 84) * z ^ 6 := nlt_pw z0 z1 6
  have q7 : 0 ≤ z ^ 7 := pow_nonneg z0 7
  have p8 : z ^ 8 ≤ (5 / 84) * z ^ 7 := nlt_pw z0 z1 7
  have q8 : 0 ≤ z ^ 8 := pow_nonneg z0 8
  have e : nltUb5 ((3 / 7) + z) = (14401632803931 / 52706752) + (4645249027383 / 960400) * z + (9078647521047 / 1920800) * z ^ 2 - (10969261489661 / 274400) * z ^ 3 - (738850780667 / 7840) * z ^ 4 - (102701266029 / 1400) * z ^ 5 - (1101203927 / 50) * z ^ 6 - (61279724 / 25) * z ^ 7 - (539784 / 5) * z ^ 8 := by unfold nltUb5 nltU5; ring
  rw [e]; linarith only [z0, z1, p2, q2, p3, q3, p4, q4, p5, q5, p6, q6, p7, q7, p8, q8]


/-- A coefficient bound for `∂_uT_B`: `U_6`. -/
noncomputable def nltUb6 (u : ℝ) : ℝ := nltU6 u

/-- `nltUb6 > -20000` on `[3/7, 41/84]`. -/
theorem nltUb6_pos {u : ℝ} (h1 : (3 / 7) ≤ u) (h2 : u ≤ (41 / 84)) : (-20000) < nltUb6 u := by
  obtain ⟨z, rfl⟩ : ∃ z, u = (3 / 7) + z := ⟨u - (3 / 7), by ring⟩
  have z0 : 0 ≤ z := by linarith
  have z1 : z ≤ (5 / 84) := by linarith
  have p2 : z ^ 2 ≤ (5 / 84) * z ^ 1 := nlt_pw z0 z1 1
  have q2 : 0 ≤ z ^ 2 := pow_nonneg z0 2
  have p3 : z ^ 3 ≤ (5 / 84) * z ^ 2 := nlt_pw z0 z1 2
  have q3 : 0 ≤ z ^ 3 := pow_nonneg z0 3
  have p4 : z ^ 4 ≤ (5 / 84) * z ^ 3 := nlt_pw z0 z1 3
  have q4 : 0 ≤ z ^ 4 := pow_nonneg z0 4
  have p5 : z ^ 5 ≤ (5 / 84) * z ^ 4 := nlt_pw z0 z1 4
  have q5 : 0 ≤ z ^ 5 := pow_nonneg z0 5
  have p6 : z ^ 6 ≤ (5 / 84) * z ^ 5 := nlt_pw z0 z1 5
  have q6 : 0 ≤ z ^ 6 := pow_nonneg z0 6
  have p7 : z ^ 7 ≤ (5 / 84) * z ^ 6 := nlt_pw z0 z1 6
  have q7 : 0 ≤ z ^ 7 := pow_nonneg z0 7
  have e : nltUb6 ((3 / 7) + z) = -(35312944425 / 3294172) + (30207543333 / 336140) * z + (486765436323 / 960400) * z ^ 2 + (63923980961 / 68600) * z ^ 3 + (1784257203 / 1960) * z ^ 4 + (97607532 / 175) * z ^ 5 + (1112662 / 5) * z ^ 6 + (923712 / 25) * z ^ 7 := by unfold nltUb6 nltU6; ring
  rw [e]; linarith only [z0, z1, p2, q2, p3, q3, p4, q4, p5, q5, p6, q6, p7, q7]


/-- `T` increases in `r ≥ 0` when `P₁, P₂ > 0`. -/
theorem nlt_T_mono {u y r r0 : ℝ} (h1 : 0 < nltP1 u y) (h2 : 0 < nltP2 u y) (hr0 : 0 ≤ r0)
    (hr : r0 ≤ r) : nltT u y r0 ≤ nltT u y r := by
  have e : nltT u y r - nltT u y r0 = (r - r0) * (nltP1 u y + (r + r0) / 2 * nltP2 u y
      + 250000 / 3 * (r ^ 2 + r * r0 + r0 ^ 2)) := by unfold nltT; ring
  have k1 : 0 ≤ (r + r0) / 2 * nltP2 u y := mul_nonneg (by linarith) h2.le
  have k2 : 0 ≤ r ^ 2 + r * r0 + r0 ^ 2 := by nlinarith
  have : 0 ≤ (r - r0) * (nltP1 u y + (r + r0) / 2 * nltP2 u y
      + 250000 / 3 * (r ^ 2 + r * r0 + r0 ^ 2)) := mul_nonneg (by linarith) (by linarith)
  linarith

/-- The enlargement of the domain of `nlt_P0_pos`: `y(1 + 4u) ≤ 1 - 2u` implies
`y ≤ 3931/8640 - 8u/9` for `17/60 ≤ u ≤ 3/7`. -/
theorem nlt_b_ge {u y : ℝ} (h1 : 17 / 60 ≤ u) (h2 : u ≤ 3 / 7) (hy : y * (1 + 4 * u) ≤ 1 - 2 * u) :
    y ≤ 3931 / 8640 - 8 / 9 * u := by
  have h4 : 0 < 1 + 4 * u := by linarith
  have e : (3931 / 8640 - 8 / 9 * u) * (1 + 4 * u) - (1 - 2 * u) =
      (60 * u - 17) * (277 - 512 * u) / 8640 := by ring
  have : 0 ≤ (60 * u - 17) * (277 - 512 * u) := mul_nonneg (by linarith) (by linarith)
  by_contra hc
  push Not at hc
  have := mul_lt_mul_of_pos_right hc h4
  nlinarith

/-- `∂_u f ≥ 0` on `[17/60, 41/84] × [1/19, 9/32]`. -/
theorem nlt_g_pos {u y : ℝ} (h1 : 17 / 60 ≤ u) (h2 : u ≤ 41 / 84) (hy1 : 1 / 19 ≤ y)
    (hy2 : y ≤ 9 / 32) : 0 ≤ lrhHorner (nltDer (nltDer nltTAL0)) u + lrhHorner (nltDer (nltDer nltTAL1)) u * y + lrhHorner (nltDer (nltDer nltTAL2)) u * y ^ 2 + lrhHorner (nltDer (nltDer nltTAL3)) u * y ^ 3 + lrhHorner (nltDer (nltDer nltTAL4)) u * y ^ 4 + lrhHorner (nltDer (nltDer nltTAL5)) u * y ^ 5 + lrhHorner (nltDer (nltDer nltTAL6)) u * y ^ 6 + lrhHorner (nltDer (nltDer nltTAL7)) u * y ^ 7 + lrhHorner (nltDer (nltDer nltTAL8)) u * y ^ 8 := by
  obtain ⟨z, rfl⟩ : ∃ z, u = 1 / 4 + z := ⟨u - 1 / 4, by ring⟩
  rw [nlt_g_jet]
  have z0 : 1 / 30 ≤ z := by linarith
  have zz : 0 ≤ z := by linarith
  have j0 := nltJb0_pos hy1 hy2
  have j1 := nltJb1_pos hy1 hy2
  have j2 := nltJb2_pos hy1 hy2
  have j3 := nltJb3_pos hy1 hy2
  have j4 := nltJb4_pos hy1 hy2
  have j5 := nltJb5_pos hy1 hy2
  have j6 := nltJb6_pos hy1 hy2
  have j7 := nltJb7_pos hy1 hy2
  unfold nltJb0 nltJb1 nltJb2 nltJb3 nltJb4 nltJb5 nltJb6 nltJb7 at *
  have k1 : nltJ1 y / 30 ≤ nltJ1 y * z := by nlinarith
  have k2 := mul_nonneg j2.le (pow_nonneg zz 2)
  have k3 := mul_nonneg j3.le (pow_nonneg zz 3)
  have k4 := mul_nonneg j4.le (pow_nonneg zz 4)
  have k5 := mul_nonneg j5.le (pow_nonneg zz 5)
  have k6 := mul_nonneg j6.le (pow_nonneg zz 6)
  have k7 := mul_nonneg j7.le (pow_nonneg zz 7)
  linarith

/-- `f = ∂_uT_A > 0` where `A ≥ 0`. -/
theorem nlt_f_pos {u y : ℝ} (h1 : 17 / 60 ≤ u) (h2 : u ≤ 41 / 84) (hy1 : 1 / 19 ≤ y)
    (hy2 : y ≤ 9 / 32) (hA : 1 - 2 * u ≤ y * (1 + 4 * u)) : 0 < lrhHorner (nltDer nltTAL0) u + lrhHorner (nltDer nltTAL1) u * y + lrhHorner (nltDer nltTAL2) u * y ^ 2 + lrhHorner (nltDer nltTAL3) u * y ^ 3 + lrhHorner (nltDer nltTAL4) u * y ^ 4 + lrhHorner (nltDer nltTAL5) u * y ^ 5 + lrhHorner (nltDer nltTAL6) u * y ^ 6 + lrhHorner (nltDer nltTAL7) u * y ^ 7 + lrhHorner (nltDer nltTAL8) u * y ^ 8 := by
  have hd : ∀ w, HasDerivAt (fun w => lrhHorner (nltDer nltTAL0) w + lrhHorner (nltDer nltTAL1) w * y + lrhHorner (nltDer nltTAL2) w * y ^ 2 + lrhHorner (nltDer nltTAL3) w * y ^ 3 + lrhHorner (nltDer nltTAL4) w * y ^ 4 + lrhHorner (nltDer nltTAL5) w * y ^ 5 + lrhHorner (nltDer nltTAL6) w * y ^ 6 + lrhHorner (nltDer nltTAL7) w * y ^ 7 + lrhHorner (nltDer nltTAL8) w * y ^ 8) (lrhHorner (nltDer (nltDer nltTAL0)) w + lrhHorner (nltDer (nltDer nltTAL1)) w * y + lrhHorner (nltDer (nltDer nltTAL2)) w * y ^ 2 + lrhHorner (nltDer (nltDer nltTAL3)) w * y ^ 3 + lrhHorner (nltDer (nltDer nltTAL4)) w * y ^ 4 + lrhHorner (nltDer (nltDer nltTAL5)) w * y ^ 5 + lrhHorner (nltDer (nltDer nltTAL6)) w * y ^ 6 + lrhHorner (nltDer (nltDer nltTAL7)) w * y ^ 7 + lrhHorner (nltDer (nltDer nltTAL8)) w * y ^ 8) w := fun w => (((((((((nlt_hasDerivAt_horner (nltDer nltTAL0) w).add ((nlt_hasDerivAt_horner (nltDer nltTAL1) w).mul_const y)).add ((nlt_hasDerivAt_horner (nltDer nltTAL2) w).mul_const (y ^ 2))).add ((nlt_hasDerivAt_horner (nltDer nltTAL3) w).mul_const (y ^ 3))).add ((nlt_hasDerivAt_horner (nltDer nltTAL4) w).mul_const (y ^ 4))).add ((nlt_hasDerivAt_horner (nltDer nltTAL5) w).mul_const (y ^ 5))).add ((nlt_hasDerivAt_horner (nltDer nltTAL6) w).mul_const (y ^ 6))).add ((nlt_hasDerivAt_horner (nltDer nltTAL7) w).mul_const (y ^ 7))).add ((nlt_hasDerivAt_horner (nltDer nltTAL8) w).mul_const (y ^ 8)))
  have mono : ∀ a, 17 / 60 ≤ a → a ≤ u → lrhHorner (nltDer nltTAL0) a + lrhHorner (nltDer nltTAL1) a * y + lrhHorner (nltDer nltTAL2) a * y ^ 2 + lrhHorner (nltDer nltTAL3) a * y ^ 3 + lrhHorner (nltDer nltTAL4) a * y ^ 4 + lrhHorner (nltDer nltTAL5) a * y ^ 5 + lrhHorner (nltDer nltTAL6) a * y ^ 6 + lrhHorner (nltDer nltTAL7) a * y ^ 7 + lrhHorner (nltDer nltTAL8) a * y ^ 8 ≤ lrhHorner (nltDer nltTAL0) u + lrhHorner (nltDer nltTAL1) u * y + lrhHorner (nltDer nltTAL2) u * y ^ 2 + lrhHorner (nltDer nltTAL3) u * y ^ 3 + lrhHorner (nltDer nltTAL4) u * y ^ 4 + lrhHorner (nltDer nltTAL5) u * y ^ 5 + lrhHorner (nltDer nltTAL6) u * y ^ 6 + lrhHorner (nltDer nltTAL7) u * y ^ 7 + lrhHorner (nltDer nltTAL8) u * y ^ 8 := fun a ha hau =>
    hrl_mono hd (a := 17 / 60) (b := 41 / 84) (fun w w1 w2 => nlt_g_pos w1 w2 hy1 hy2) ha hau h2
  rcases le_total u (1 / 3) with c1 | c1
  · have hy : 1 / 7 ≤ y := by
      by_contra hc; push Not at hc
      nlinarith [mul_pos (sub_pos.2 hc) (by linarith : (0 : ℝ) < 1 + 4 * u)]
    have p := nltTf0_pos hy hy2
    rw [← nlt_Tf0_eq] at p
    have := mono (17 / 60) le_rfl h1
    linarith
  rcases le_total u (3 / 8) with c2 | c2
  · have hy : 1 / 10 ≤ y := by
      by_contra hc; push Not at hc
      nlinarith [mul_pos (sub_pos.2 hc) (by linarith : (0 : ℝ) < 1 + 4 * u)]
    have p := nltTf1_pos hy hy2
    rw [← nlt_Tf1_eq] at p
    have := mono (1 / 3) (by norm_num) c1
    linarith
  rcases le_total u (2 / 5) with c3 | c3
  · have hy : 1 / 13 ≤ y := by
      by_contra hc; push Not at hc
      nlinarith [mul_pos (sub_pos.2 hc) (by linarith : (0 : ℝ) < 1 + 4 * u)]
    have p := nltTf2_pos hy hy2
    rw [← nlt_Tf2_eq] at p
    have := mono (3 / 8) (by norm_num) c2
    linarith
  · have p := nltTf3_pos hy1 hy2
    rw [← nlt_Tf3_eq] at p
    have := mono (2 / 5) (by norm_num) c3
    linarith

/-- **The maximum-duration branch**: `T_A > 0` where `A ≥ 0`,
`17/60 ≤ u ≤ 41/84`, `1/19 ≤ y ≤ 9/32`. -/
theorem nlt_TA_pos {u y : ℝ} (h1 : 17 / 60 ≤ u) (h2 : u ≤ 41 / 84) (hy1 : 1 / 19 ≤ y)
    (hy2 : y ≤ 9 / 32) (hA : 0 ≤ nltAA u y) : 0 < nltT u y (nltAA u y) := by
  rw [nlt_TA_eq]
  have hd : ∀ w, HasDerivAt (fun w => lrhHorner (nltTAL0) w + lrhHorner (nltTAL1) w * y + lrhHorner (nltTAL2) w * y ^ 2 + lrhHorner (nltTAL3) w * y ^ 3 + lrhHorner (nltTAL4) w * y ^ 4 + lrhHorner (nltTAL5) w * y ^ 5 + lrhHorner (nltTAL6) w * y ^ 6 + lrhHorner (nltTAL7) w * y ^ 7 + lrhHorner (nltTAL8) w * y ^ 8) (lrhHorner (nltDer nltTAL0) w + lrhHorner (nltDer nltTAL1) w * y + lrhHorner (nltDer nltTAL2) w * y ^ 2 + lrhHorner (nltDer nltTAL3) w * y ^ 3 + lrhHorner (nltDer nltTAL4) w * y ^ 4 + lrhHorner (nltDer nltTAL5) w * y ^ 5 + lrhHorner (nltDer nltTAL6) w * y ^ 6 + lrhHorner (nltDer nltTAL7) w * y ^ 7 + lrhHorner (nltDer nltTAL8) w * y ^ 8) w := fun w => (((((((((nlt_hasDerivAt_horner (nltTAL0) w).add ((nlt_hasDerivAt_horner (nltTAL1) w).mul_const y)).add ((nlt_hasDerivAt_horner (nltTAL2) w).mul_const (y ^ 2))).add ((nlt_hasDerivAt_horner (nltTAL3) w).mul_const (y ^ 3))).add ((nlt_hasDerivAt_horner (nltTAL4) w).mul_const (y ^ 4))).add ((nlt_hasDerivAt_horner (nltTAL5) w).mul_const (y ^ 5))).add ((nlt_hasDerivAt_horner (nltTAL6) w).mul_const (y ^ 6))).add ((nlt_hasDerivAt_horner (nltTAL7) w).mul_const (y ^ 7))).add ((nlt_hasDerivAt_horner (nltTAL8) w).mul_const (y ^ 8)))
  have hAw : ∀ w, nltAA w y = ((1 + 4 * w) * y - (1 - 2 * w)) / 2 := fun w => by unfold nltAA; ring
  rw [hAw] at hA
  rcases le_total y (13 / 64) with cy | cy
  · have hpos : 0 < 2 + 4 * y := by linarith
    obtain ⟨u0, hu0⟩ : ∃ u0, u0 = (1 - y) / (2 + 4 * y) := ⟨_, rfl⟩
    have e0 : (1 + 4 * u0) * y - (1 - 2 * u0) = 0 := by rw [hu0]; field_simp; ring
    have u0lo : 17 / 60 ≤ u0 := by rw [hu0, le_div_iff₀ hpos]; linarith
    have u0hi : u0 ≤ 3 / 7 := by rw [hu0, div_le_iff₀ hpos]; linarith
    have u0u : u0 ≤ u := by nlinarith
    have mono := hrl_mono hd (a := u0) (b := u) (fun w w1 w2 =>
      (nlt_f_pos (by linarith) (by linarith) hy1 hy2
        (by nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ 4 * y + 2) (by linarith : (0 : ℝ) ≤ w - u0)])).le)
      le_rfl u0u le_rfl
    have base : 0 < nltT u0 y (nltAA u0 y) := by
      have hA0 : nltAA u0 y = 0 := by rw [hAw, e0]; ring
      rw [hA0]
      have hb := nlt_b_ge u0lo u0hi (by nlinarith : y * (1 + 4 * u0) ≤ 1 - 2 * u0)
      have p0 := nlt_P0_pos u0lo u0hi (by linarith) hb
      have e : nltT u0 y 0 = nltP0 u0 y := by unfold nltT; ring
      rw [e]; unfold nltP0; linarith
    rw [nlt_TA_eq] at base
    linarith
  · have mono := hrl_mono hd (a := 17 / 60) (b := u) (fun w w1 w2 =>
      (nlt_f_pos w1 (by linarith) hy1 hy2
        (by nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ 4 * y + 2) (by linarith : (0 : ℝ) ≤ w - 17 / 60)])).le)
      le_rfl h1 le_rfl
    have p := nltTq_pos cy hy2
    rw [← nlt_Tq_eq] at p
    linarith

/-- **The outer branch**: `T_B > 0` for `3/7 ≤ u ≤ 41/84`,
`0 ≤ y ≤ 2/31`. -/
theorem nlt_TB_pos {u y : ℝ} (h1 : 3 / 7 ≤ u) (h2 : u ≤ 41 / 84) (hy0 : 0 ≤ y) (hy1 : y ≤ 2 / 31) :
    0 < nltT u y (nltBB u) := by
  rw [nlt_TB_eq]
  have hd : ∀ w, HasDerivAt (fun w => lrhHorner (nltTBL0) w + lrhHorner (nltTBL1) w * y + lrhHorner (nltTBL2) w * y ^ 2 + lrhHorner (nltTBL3) w * y ^ 3 + lrhHorner (nltTBL4) w * y ^ 4 + lrhHorner (nltTBL5) w * y ^ 5 + lrhHorner (nltTBL6) w * y ^ 6) (lrhHorner (nltDer nltTBL0) w + lrhHorner (nltDer nltTBL1) w * y + lrhHorner (nltDer nltTBL2) w * y ^ 2 + lrhHorner (nltDer nltTBL3) w * y ^ 3 + lrhHorner (nltDer nltTBL4) w * y ^ 4 + lrhHorner (nltDer nltTBL5) w * y ^ 5 + lrhHorner (nltDer nltTBL6) w * y ^ 6) w := fun w => (((((((nlt_hasDerivAt_horner (nltTBL0) w).add ((nlt_hasDerivAt_horner (nltTBL1) w).mul_const y)).add ((nlt_hasDerivAt_horner (nltTBL2) w).mul_const (y ^ 2))).add ((nlt_hasDerivAt_horner (nltTBL3) w).mul_const (y ^ 3))).add ((nlt_hasDerivAt_horner (nltTBL4) w).mul_const (y ^ 4))).add ((nlt_hasDerivAt_horner (nltTBL5) w).mul_const (y ^ 5))).add ((nlt_hasDerivAt_horner (nltTBL6) w).mul_const (y ^ 6)))
  have pos : ∀ w, 3 / 7 ≤ w → w ≤ 41 / 84 → 0 ≤ lrhHorner (nltDer nltTBL0) w + lrhHorner (nltDer nltTBL1) w * y + lrhHorner (nltDer nltTBL2) w * y ^ 2 + lrhHorner (nltDer nltTBL3) w * y ^ 3 + lrhHorner (nltDer nltTBL4) w * y ^ 4 + lrhHorner (nltDer nltTBL5) w * y ^ 5 + lrhHorner (nltDer nltTBL6) w * y ^ 6 := by
    intro w w1 w2
    rw [nlt_U_eq0, nlt_U_eq1, nlt_U_eq2, nlt_U_eq3, nlt_U_eq4, nlt_U_eq5, nlt_U_eq6]
    have b0 := nltUb0_pos w1 w2
    have b1 := nltUb1_pos w1 w2
    have b2 := nltUb2_pos w1 w2
    have b3 := nltUb3_pos w1 w2
    have b4 := nltUb4_pos w1 w2
    have b5 := nltUb5_pos w1 w2
    have b6 := nltUb6_pos w1 w2
    unfold nltUb0 nltUb1 nltUb2 nltUb3 nltUb4 nltUb5 nltUb6 at *
    have k1 := mul_le_mul_of_nonneg_right b1.le hy0
    have k2 := mul_le_mul_of_nonneg_right b2.le (pow_nonneg hy0 2)
    have k3 := mul_nonneg b3.le (pow_nonneg hy0 3)
    have k4 := mul_nonneg b4.le (pow_nonneg hy0 4)
    have k5 := mul_nonneg b5.le (pow_nonneg hy0 5)
    have k6 := mul_le_mul_of_nonneg_right b6.le (pow_nonneg hy0 6)
    have y2 : y ^ 2 ≤ (2 / 31) ^ 2 := pow_le_pow_left₀ hy0 hy1 2
    have y6 : y ^ 6 ≤ (2 / 31) ^ 6 := pow_le_pow_left₀ hy0 hy1 6
    norm_num at y2 y6
    linarith
  have mono := hrl_mono hd pos le_rfl h1 h2
  have base : 0 < lrhHorner (nltTBL0) (3 / 7) + lrhHorner (nltTBL1) (3 / 7) * y + lrhHorner (nltTBL2) (3 / 7) * y ^ 2 + lrhHorner (nltTBL3) (3 / 7) * y ^ 3 + lrhHorner (nltTBL4) (3 / 7) * y ^ 4 + lrhHorner (nltTBL5) (3 / 7) * y ^ 5 + lrhHorner (nltTBL6) (3 / 7) * y ^ 6 := by
    rw [← nlt_TB_eq]
    have hB : nltBB (3 / 7) = 0 := by unfold nltBB; norm_num
    rw [hB]
    have p0 := nlt_P0_pos (x := 3 / 7) (y := y) (by norm_num) le_rfl hy0 (by linarith)
    have e : nltT (3 / 7) y 0 = nltP0 (3 / 7) y := by unfold nltT; ring
    rw [e]; unfold nltP0; linarith
  linarith

/-- Case bounds for `y` in the three branches `r₀ = 0`, `r₀ = A`, `r₀ = B`. -/
theorem nlt_case_y19 {u y : ℝ} (u1 : 17 / 60 ≤ u) (cA : 0 ≤ ((1 + 4 * u) * y - (1 - 2 * u)) / 2)
    (cAB : (7 * u - 3) / 5 ≤ ((1 + 4 * u) * y - (1 - 2 * u)) / 2) : 1 / 19 ≤ y := by
  by_contra hc; push Not at hc
  have hp := mul_pos (sub_pos.2 hc) (by linarith : (0 : ℝ) < 1 + 4 * u)
  rcases le_total u (3 / 7) with cu | cu
  · nlinarith
  · nlinarith

theorem nlt_case_y231a {u y : ℝ} (u1 : 3 / 7 ≤ u) (cA : ((1 + 4 * u) * y - (1 - 2 * u)) / 2 ≤ 0) :
    y ≤ 2 / 31 := by
  by_contra hc; push Not at hc
  nlinarith [mul_pos (sub_pos.2 hc) (by linarith : (0 : ℝ) < 1 + 4 * u)]

theorem nlt_case_y231b {u y : ℝ} (u1 : 17 / 60 ≤ u) (u2 : u ≤ 41 / 84)
    (cAB : ((1 + 4 * u) * y - (1 - 2 * u)) / 2 ≤ (7 * u - 3) / 5) : y ≤ 2 / 31 := by
  by_contra hc; push Not at hc
  nlinarith [mul_pos (sub_pos.2 hc) (by linarith : (0 : ℝ) < 1 + 4 * u)]

/-- **`𝓗S > 0`** on the low-`t` unit domain:
`1/4 ≤ h ≤ 1/3`, `1/30 ≤ j ≤ 5h/7`, `0 ≤ y`, `y(1 + 2j) ≤ h - j`. -/
theorem nlt_HS_pos {h j y : ℝ} (h1 : 1 / 4 ≤ h) (h2 : h ≤ 1 / 3) (j1 : 1 / 30 ≤ j)
    (j2 : j ≤ 5 / 7 * h) (hy0 : 0 ≤ y) (hy : y * (1 + 2 * j) ≤ h - j) : 0 < lrhHorner (nltDer (nltL0 j)) h + lrhHorner (nltDer (nltL1 j)) h * y + lrhHorner (nltDer (nltL2 j)) h * y ^ 2 + lrhHorner (nltDer (nltL3 j)) h * y ^ 3 + lrhHorner (nltDer (nltL4 j)) h * y ^ 4 + lrhHorner (nltDer (nltL5 j)) h * y ^ 5 + lrhHorner (nltDer (nltL6 j)) h * y ^ 6 := by
  have hy9 : y ≤ 9 / 32 := by nlinarith
  have u1 : 17 / 60 ≤ j + 1 / 4 := by linarith
  have u2 : j + 1 / 4 ≤ 41 / 84 := by linarith
  have P1 : 0 < nltP1 (j + 1 / 4) y := by unfold nltP1; exact nlt_P1_pos u1 u2 hy0 hy9
  have P2 : 0 < nltP2 (j + 1 / 4) y := by unfold nltP2; exact nlt_P2_pos u1 u2 hy0 hy9
  have hrA : nltAA (j + 1 / 4) y ≤ h - 1 / 4 := by unfold nltAA; nlinarith
  have hrB : nltBB (j + 1 / 4) ≤ h - 1 / 4 := by unfold nltBB; linarith
  have hAw : nltAA (j + 1 / 4) y = ((1 + 4 * (j + 1 / 4)) * y - (1 - 2 * (j + 1 / 4))) / 2 := by
    unfold nltAA; ring
  have hBw : nltBB (j + 1 / 4) = (7 * (j + 1 / 4) - 3) / 5 := rfl
  -- the cubic Taylor bound
  have hT : nltT (j + 1 / 4) y (h - 1 / 4) ≤ lrhHorner (nltDer (nltL0 j)) h + lrhHorner (nltDer (nltL1 j)) h * y + lrhHorner (nltDer (nltL2 j)) h * y ^ 2 + lrhHorner (nltDer (nltL3 j)) h * y ^ 3 + lrhHorner (nltDer (nltL4 j)) h * y ^ 4 + lrhHorner (nltDer (nltL5 j)) h * y ^ 5 + lrhHorner (nltDer (nltL6 j)) h * y ^ 6 := by
    have hd0 : ∀ s, HasDerivAt (fun s => lrhHorner (nltDer (nltL0 j)) s + lrhHorner (nltDer (nltL1 j)) s * y + lrhHorner (nltDer (nltL2 j)) s * y ^ 2 + lrhHorner (nltDer (nltL3 j)) s * y ^ 3 + lrhHorner (nltDer (nltL4 j)) s * y ^ 4 + lrhHorner (nltDer (nltL5 j)) s * y ^ 5 + lrhHorner (nltDer (nltL6 j)) s * y ^ 6) (lrhHorner (nltDer (nltDer (nltL0 j))) s + lrhHorner (nltDer (nltDer (nltL1 j))) s * y + lrhHorner (nltDer (nltDer (nltL2 j))) s * y ^ 2 + lrhHorner (nltDer (nltDer (nltL3 j))) s * y ^ 3 + lrhHorner (nltDer (nltDer (nltL4 j))) s * y ^ 4 + lrhHorner (nltDer (nltDer (nltL5 j))) s * y ^ 5 + lrhHorner (nltDer (nltDer (nltL6 j))) s * y ^ 6) s := fun s => (((((((nlt_hasDerivAt_horner (nltDer (nltL0 j)) s).add ((nlt_hasDerivAt_horner (nltDer (nltL1 j)) s).mul_const y)).add ((nlt_hasDerivAt_horner (nltDer (nltL2 j)) s).mul_const (y ^ 2))).add ((nlt_hasDerivAt_horner (nltDer (nltL3 j)) s).mul_const (y ^ 3))).add ((nlt_hasDerivAt_horner (nltDer (nltL4 j)) s).mul_const (y ^ 4))).add ((nlt_hasDerivAt_horner (nltDer (nltL5 j)) s).mul_const (y ^ 5))).add ((nlt_hasDerivAt_horner (nltDer (nltL6 j)) s).mul_const (y ^ 6)))
    have hd1 : ∀ s, HasDerivAt (fun s => lrhHorner (nltDer (nltDer (nltL0 j))) s + lrhHorner (nltDer (nltDer (nltL1 j))) s * y + lrhHorner (nltDer (nltDer (nltL2 j))) s * y ^ 2 + lrhHorner (nltDer (nltDer (nltL3 j))) s * y ^ 3 + lrhHorner (nltDer (nltDer (nltL4 j))) s * y ^ 4 + lrhHorner (nltDer (nltDer (nltL5 j))) s * y ^ 5 + lrhHorner (nltDer (nltDer (nltL6 j))) s * y ^ 6) (lrhHorner (nltDer (nltDer (nltDer (nltL0 j)))) s + lrhHorner (nltDer (nltDer (nltDer (nltL1 j)))) s * y + lrhHorner (nltDer (nltDer (nltDer (nltL2 j)))) s * y ^ 2 + lrhHorner (nltDer (nltDer (nltDer (nltL3 j)))) s * y ^ 3 + lrhHorner (nltDer (nltDer (nltDer (nltL4 j)))) s * y ^ 4 + lrhHorner (nltDer (nltDer (nltDer (nltL5 j)))) s * y ^ 5 + lrhHorner (nltDer (nltDer (nltDer (nltL6 j)))) s * y ^ 6) s := fun s => (((((((nlt_hasDerivAt_horner (nltDer (nltDer (nltL0 j))) s).add ((nlt_hasDerivAt_horner (nltDer (nltDer (nltL1 j))) s).mul_const y)).add ((nlt_hasDerivAt_horner (nltDer (nltDer (nltL2 j))) s).mul_const (y ^ 2))).add ((nlt_hasDerivAt_horner (nltDer (nltDer (nltL3 j))) s).mul_const (y ^ 3))).add ((nlt_hasDerivAt_horner (nltDer (nltDer (nltL4 j))) s).mul_const (y ^ 4))).add ((nlt_hasDerivAt_horner (nltDer (nltDer (nltL5 j))) s).mul_const (y ^ 5))).add ((nlt_hasDerivAt_horner (nltDer (nltDer (nltL6 j))) s).mul_const (y ^ 6)))
    have hd2 : ∀ s, HasDerivAt (fun s => lrhHorner (nltDer (nltDer (nltDer (nltL0 j)))) s + lrhHorner (nltDer (nltDer (nltDer (nltL1 j)))) s * y + lrhHorner (nltDer (nltDer (nltDer (nltL2 j)))) s * y ^ 2 + lrhHorner (nltDer (nltDer (nltDer (nltL3 j)))) s * y ^ 3 + lrhHorner (nltDer (nltDer (nltDer (nltL4 j)))) s * y ^ 4 + lrhHorner (nltDer (nltDer (nltDer (nltL5 j)))) s * y ^ 5 + lrhHorner (nltDer (nltDer (nltDer (nltL6 j)))) s * y ^ 6) (lrhHorner (nltDer (nltDer (nltDer (nltDer (nltL0 j))))) s + lrhHorner (nltDer (nltDer (nltDer (nltDer (nltL1 j))))) s * y + lrhHorner (nltDer (nltDer (nltDer (nltDer (nltL2 j))))) s * y ^ 2 + lrhHorner (nltDer (nltDer (nltDer (nltDer (nltL3 j))))) s * y ^ 3 + lrhHorner (nltDer (nltDer (nltDer (nltDer (nltL4 j))))) s * y ^ 4 + lrhHorner (nltDer (nltDer (nltDer (nltDer (nltL5 j))))) s * y ^ 5 + lrhHorner (nltDer (nltDer (nltDer (nltDer (nltL6 j))))) s * y ^ 6) s := fun s => (((((((nlt_hasDerivAt_horner (nltDer (nltDer (nltDer (nltL0 j)))) s).add ((nlt_hasDerivAt_horner (nltDer (nltDer (nltDer (nltL1 j)))) s).mul_const y)).add ((nlt_hasDerivAt_horner (nltDer (nltDer (nltDer (nltL2 j)))) s).mul_const (y ^ 2))).add ((nlt_hasDerivAt_horner (nltDer (nltDer (nltDer (nltL3 j)))) s).mul_const (y ^ 3))).add ((nlt_hasDerivAt_horner (nltDer (nltDer (nltDer (nltL4 j)))) s).mul_const (y ^ 4))).add ((nlt_hasDerivAt_horner (nltDer (nltDer (nltDer (nltL5 j)))) s).mul_const (y ^ 5))).add ((nlt_hasDerivAt_horner (nltDer (nltDer (nltDer (nltL6 j)))) s).mul_const (y ^ 6)))
    have h3 : ∀ s, 1 / 4 ≤ s → s ≤ h → 500000 ≤ lrhHorner (nltDer (nltDer (nltDer (nltDer (nltL0 j))))) s + lrhHorner (nltDer (nltDer (nltDer (nltDer (nltL1 j))))) s * y + lrhHorner (nltDer (nltDer (nltDer (nltDer (nltL2 j))))) s * y ^ 2 + lrhHorner (nltDer (nltDer (nltDer (nltDer (nltL3 j))))) s * y ^ 3 + lrhHorner (nltDer (nltDer (nltDer (nltDer (nltL4 j))))) s * y ^ 4 + lrhHorner (nltDer (nltDer (nltDer (nltDer (nltL5 j))))) s * y ^ 5 + lrhHorner (nltDer (nltDer (nltDer (nltDer (nltL6 j))))) s * y ^ 6 := fun s s1 s2 =>
      nlt_H4_ge s1 (by linarith) (by linarith) (by linarith) hy0 hy9
    have tay := nlt_taylor3 hd0 hd1 hd2 h3 h1 le_rfl
    rw [nlt_c_eq0, nlt_c_eq1, nlt_c_eq2, nlt_c_eq3, nlt_c_eq4, nlt_c_eq5, nlt_c_eq6, nlt_E_eq0, nlt_E_eq1, nlt_E_eq2, nlt_E_eq3, nlt_E_eq4, nlt_E_eq5, nlt_E_eq6, nlt_R_eq0, nlt_R_eq1, nlt_R_eq2, nlt_R_eq3, nlt_R_eq4, nlt_R_eq5, nlt_R_eq6] at tay
    unfold nltT nltP0 nltP1 nltP2; linarith
  rcases le_total (nltAA (j + 1 / 4) y) 0 with cA | cA
  · rcases le_total (nltBB (j + 1 / 4)) 0 with cB | cB
    · -- `r₀ = 0`
      have mono := nlt_T_mono P1 P2 le_rfl (by linarith : (0 : ℝ) ≤ h - 1 / 4)
      have hu37 : j + 1 / 4 ≤ 3 / 7 := by rw [hBw] at cB; linarith
      have hb := nlt_b_ge (y := y) u1 hu37 (by rw [hAw] at cA; linarith)
      have p0 := nlt_P0_pos u1 hu37 hy0 hb
      have e : nltT (j + 1 / 4) y 0 = nltP0 (j + 1 / 4) y := by unfold nltT; ring
      unfold nltP0 at e
      linarith
    · -- `r₀ = B ≥ 0 ≥ A`
      have mono := nlt_T_mono P1 P2 cB hrB
      have hu37 : 3 / 7 ≤ j + 1 / 4 := by rw [hBw] at cB; linarith
      have hy2 := nlt_case_y231a hu37 (by rw [hAw] at cA; exact cA)
      have := nlt_TB_pos hu37 u2 hy0 hy2
      linarith
  · rcases le_total (nltBB (j + 1 / 4)) (nltAA (j + 1 / 4) y) with cAB | cAB
    · -- `r₀ = A ≥ B`, `A ≥ 0`
      have mono := nlt_T_mono P1 P2 cA hrA
      have hy19 := nlt_case_y19 u1 (by rw [hAw] at cA; exact cA) (by rw [hAw, hBw] at cAB; exact cAB)
      have := nlt_TA_pos u1 u2 hy19 hy9 cA
      linarith
    · -- `r₀ = B > A ≥ 0`
      have hB0 : 0 ≤ nltBB (j + 1 / 4) := le_trans cA cAB
      have mono := nlt_T_mono P1 P2 hB0 hrB
      have hu37 : 3 / 7 ≤ j + 1 / 4 := by rw [hBw] at hB0; linarith
      have hy2 := nlt_case_y231b u1 u2 (by rw [hAw, hBw] at cAB; exact cAB)
      have := nlt_TB_pos hu37 u2 hy0 hy2
      linarith

end SmoothedOctagon
