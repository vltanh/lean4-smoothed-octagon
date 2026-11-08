module

public import SmoothedOctagon.Exclusion.Mixed.FwdHand.PolyDeriv

/-!
# Case M2, forward successor by hand: the high-ratio lower shape, terminal face `h = 1/4`

`docs/lighter-proofs/NONSHORT_HIGH_RATIO_LOWER_FACE.md` (PR #2, branch `proof/lighter-signs`): at
`t = 3/8`, `k₀ = 29t²/4`, the normalized residual `P(x, y) = ∑ Cᵢ(x) yⁱ`
(`96q(q + 1)W³D G_{4,L}`, `q = 1 + y`) satisfies `P ≥ 13/4` for `17/60 ≤ x ≤ 3/7`,
`0 ≤ y ≤ (1 - 2x)/(1 + 4x)` (`hrl_face`). As in the note: `C₂, …, C₆ < 0` gives concavity in `y`
and the upper face `b(x) = 467/960 - x` (F3); `C₀ > 20` by convexity of `R` (F4); and along the line
`F(x) = P(x, b(x))`, `F⁽⁹⁾ < 0` is integrated with the endpoint jets (F8) (`hrl_F_ge`).

Route: `F` is expanded as a univariate polynomial of degree `14` (`hrlFL0`, its derivatives
`hrlFL1`, …, `hrlFL9`) and the jets (F8) are exact rational evaluations, in place of the note's
ninth-derivative formula (F5)-(F7) and its rounded Horner chains; `F⁽⁹⁾ < 0` and `C₂ < 0` use
Taylor coefficients at `x = 17/60` in place of (F6) and (F2).

## Main API

* `hrlCF0`, …, `hrlCF6`, `hrlP`; `hrl_F_ge`; `hrl_face`.
-/

@[expose] public section

namespace SmoothedOctagon

/-! ### The face coefficients (`NONSHORT_HIGH_RATIO_LOWER_FACE` §1) -/

/-- `C_0(x)` of `NONSHORT_HIGH_RATIO_LOWER_FACE` §1 (`t = 3/8`, `k₀ = 261/256`). -/
noncomputable def hrlCF0 (x : ℝ) : ℝ :=
  -(74732415 / 65536) * x + (1238140495 / 262144) * x ^ (2 : ℕ) + (635549755 / 262144) * x ^ (3 : ℕ) - (2542125 / 256) * x ^ (4 : ℕ) - (4381125 / 512) * x ^ (5 : ℕ) - (3825 / 2) * x ^ (6 : ℕ)

/-- `C_1(x)` of `NONSHORT_HIGH_RATIO_LOWER_FACE` §1 (`t = 3/8`, `k₀ = 261/256`). -/
noncomputable def hrlCF1 (x : ℝ) : ℝ :=
  -(44839449 / 65536) + (591967515 / 262144) * x + (16856367297 / 524288) * x ^ (2 : ℕ) - (2481472989 / 524288) * x ^ (3 : ℕ) - (3434657649 / 32768) * x ^ (4 : ℕ) - (105946215 / 1024) * x ^ (5 : ℕ) - (2167215 / 64) * x ^ (6 : ℕ) - 1965 * x ^ (7 : ℕ)

/-- `C_2(x)` of `NONSHORT_HIGH_RATIO_LOWER_FACE` §1 (`t = 3/8`, `k₀ = 261/256`). -/
noncomputable def hrlCF2 (x : ℝ) : ℝ :=
  (145359519 / 131072) + (6313406737 / 524288) * x + (10322714837 / 524288) * x ^ (2 : ℕ) - (11554797201 / 65536) * x ^ (3 : ℕ) - (31332968633 / 65536) * x ^ (4 : ℕ) - (116601189 / 256) * x ^ (5 : ℕ) - (24615003 / 128) * x ^ (6 : ℕ) - 33540 * x ^ (7 : ℕ) - 2448 * x ^ (8 : ℕ)

/-- `C_3(x)` of `NONSHORT_HIGH_RATIO_LOWER_FACE` §1 (`t = 3/8`, `k₀ = 261/256`). -/
noncomputable def hrlCF3 (x : ℝ) : ℝ :=
  (10753107 / 8192) - (264165151 / 65536) * x - (19730788975 / 262144) * x ^ (2 : ℕ) - (100902544067 / 262144) * x ^ (3 : ℕ) - (3063148985 / 4096) * x ^ (4 : ℕ) - (1418453067 / 2048) * x ^ (5 : ℕ) - (20825019 / 64) * x ^ (6 : ℕ) - (146475 / 2) * x ^ (7 : ℕ) - 6528 * x ^ (8 : ℕ)

/-- `C_4(x)` of `NONSHORT_HIGH_RATIO_LOWER_FACE` §1 (`t = 3/8`, `k₀ = 261/256`). -/
noncomputable def hrlCF4 (x : ℝ) : ℝ :=
  -(144402831 / 65536) - (7396491861 / 262144) * x - (3879209205 / 32768) * x ^ (2 : ℕ) - (84147940983 / 262144) * x ^ (3 : ℕ) - (16553778615 / 32768) * x ^ (4 : ℕ) - (460321809 / 1024) * x ^ (5 : ℕ) - (14389761 / 64) * x ^ (6 : ℕ) - (464265 / 8) * x ^ (7 : ℕ) - 5712 * x ^ (8 : ℕ)

/-- `C_5(x)` of `NONSHORT_HIGH_RATIO_LOWER_FACE` §1 (`t = 3/8`, `k₀ = 261/256`). -/
noncomputable def hrlCF5 (x : ℝ) : ℝ :=
  -(127147563 / 65536) - (4463664003 / 262144) * x - (28149980355 / 524288) * x ^ (2 : ℕ) - (56966436693 / 524288) * x ^ (3 : ℕ) - (4717837395 / 32768) * x ^ (4 : ℕ) - (246960519 / 2048) * x ^ (5 : ℕ) - (7970421 / 128) * x ^ (6 : ℕ) - (140175 / 8) * x ^ (7 : ℕ) - 1836 * x ^ (8 : ℕ)

/-- `C_6(x)` of `NONSHORT_HIGH_RATIO_LOWER_FACE` §1 (`t = 3/8`, `k₀ = 261/256`). -/
noncomputable def hrlCF6 (x : ℝ) : ℝ :=
  -(26376921 / 131072) - (746579511 / 524288) * x - (1484996355 / 524288) * x ^ (2 : ℕ) - (233133111 / 65536) * x ^ (3 : ℕ) - (208980465 / 65536) * x ^ (4 : ℕ) - (1996137 / 1024) * x ^ (5 : ℕ) - (67263 / 64) * x ^ (6 : ℕ) - (1575 / 4) * x ^ (7 : ℕ) - 51 * x ^ (8 : ℕ)

/-- `P(x, y) = ∑ Cᵢ(x) yⁱ`, the normalized face residual. -/
noncomputable def hrlP (x y : ℝ) : ℝ :=
  hrlCF0 x * y ^ (0 : ℕ) + hrlCF1 x * y ^ (1 : ℕ) + hrlCF2 x * y ^ (2 : ℕ) + hrlCF3 x * y ^ (3 : ℕ) + hrlCF4 x * y ^ (4 : ℕ) + hrlCF5 x * y ^ (5 : ℕ) + hrlCF6 x * y ^ (6 : ℕ)

/-- `R(x)` with `C₀ = -5xR/262144` (face note §3). -/
noncomputable def hrlRf (x : ℝ) : ℝ :=
  59785932 - 247628099 * x - 127109951 * x ^ (2 : ℕ) + 520627200 * x ^ (3 : ℕ) + 448627200 * x ^ (4 : ℕ) + 100270080 * x ^ (5 : ℕ)

/-- The coefficients of `F^(0)`, `F(x) = P(x, 467/960 - x)`. -/
noncomputable def hrlFL0 : List ℝ :=
  [(-(124381006976111273408449 / 1266637395197952000000) : ℝ), (8284997248539681546716563 / 15199648742375424000000), (2554025849324823897894797 / 202661983231672320000), (-(464131461147123182473645631 / 5699868278390784000000) : ℝ), (370657644614459544768940409 / 3419920967034470400000), (12878960058407612553384773 / 89060441849856000000), (-(4252741355099432296044089 / 16698832846848000000) : ℝ), (-(10534338393260464550387 / 69578470195200000) : ℝ), (42864379399959215886487 / 260919263232000000), (3600675150319852219 / 45298483200000), (-(955989907685537 / 18874368000) : ℝ), (-(244146114089 / 14745600) : ℝ), (148714087 / 20480), (254577 / 160), (-51 : ℝ)]

/-- The coefficients of `F^(1)`, `F(x) = P(x, 467/960 - x)`. -/
noncomputable def hrlFL1 : List ℝ :=
  [(8284997248539681546716563 / 15199648742375424000000), (2554025849324823897894797 / 101330991615836160000), (-(464131461147123182473645631 / 1899956092796928000000) : ℝ), (370657644614459544768940409 / 854980241758617600000), (12878960058407612553384773 / 17812088369971200000), (-(4252741355099432296044089 / 2783138807808000000) : ℝ), (-(73740368752823251852709 / 69578470195200000) : ℝ), (42864379399959215886487 / 32614907904000000), (3600675150319852219 / 5033164800000), (-(955989907685537 / 1887436800) : ℝ), (-(2685607254979 / 14745600) : ℝ), (446142261 / 5120), (3309501 / 160), (-714 : ℝ)]

/-- The coefficients of `F^(2)`, `F(x) = P(x, 467/960 - x)`. -/
noncomputable def hrlFL2 : List ℝ :=
  [(2554025849324823897894797 / 101330991615836160000), (-(464131461147123182473645631 / 949978046398464000000) : ℝ), (370657644614459544768940409 / 284993413919539200000), (12878960058407612553384773 / 4453022092492800000), (-(4252741355099432296044089 / 556627761561600000) : ℝ), (-(73740368752823251852709 / 11596411699200000) : ℝ), (300050655799714511205409 / 32614907904000000), (3600675150319852219 / 629145600000), (-(955989907685537 / 209715200) : ℝ), (-(2685607254979 / 1474560) : ℝ), (4907564871 / 5120), (9928503 / 40), (-9282 : ℝ)]

/-- The coefficients of `F^(3)`, `F(x) = P(x, 467/960 - x)`. -/
noncomputable def hrlFL3 : List ℝ :=
  [(-(464131461147123182473645631 / 949978046398464000000) : ℝ), (370657644614459544768940409 / 142496706959769600000), (12878960058407612553384773 / 1484340697497600000), (-(4252741355099432296044089 / 139156940390400000) : ℝ), (-(73740368752823251852709 / 2319282339840000) : ℝ), (300050655799714511205409 / 5435817984000000), (25204726052238965533 / 629145600000), (-(955989907685537 / 26214400) : ℝ), (-(2685607254979 / 163840) : ℝ), (4907564871 / 512), (109213533 / 40), (-111384 : ℝ)]

/-- The coefficients of `F^(4)`, `F(x) = P(x, 467/960 - x)`. -/
noncomputable def hrlFL4 : List ℝ :=
  [(370657644614459544768940409 / 142496706959769600000), (12878960058407612553384773 / 742170348748800000), (-(4252741355099432296044089 / 46385646796800000) : ℝ), (-(73740368752823251852709 / 579820584960000) : ℝ), (300050655799714511205409 / 1087163596800000), (25204726052238965533 / 104857600000), (-(6691929353798759 / 26214400) : ℝ), (-(2685607254979 / 20480) : ℝ), (44168083839 / 512), (109213533 / 4), (-1225224 : ℝ)]

/-- The coefficients of `F^(5)`, `F(x) = P(x, 467/960 - x)`. -/
noncomputable def hrlFL5 : List ℝ :=
  [(12878960058407612553384773 / 742170348748800000), (-(4252741355099432296044089 / 23192823398400000) : ℝ), (-(73740368752823251852709 / 193273528320000) : ℝ), (300050655799714511205409 / 271790899200000), (25204726052238965533 / 20971520000), (-(20075788061396277 / 13107200) : ℝ), (-(18799250784853 / 20480) : ℝ), (44168083839 / 64), (982921797 / 4), (-12252240 : ℝ)]

/-- The coefficients of `F^(6)`, `F(x) = P(x, 467/960 - x)`. -/
noncomputable def hrlFL6 : List ℝ :=
  [(-(4252741355099432296044089 / 23192823398400000) : ℝ), (-(73740368752823251852709 / 96636764160000) : ℝ), (300050655799714511205409 / 90596966400000), (25204726052238965533 / 5242880000), (-(20075788061396277 / 2621440) : ℝ), (-(56397752354559 / 10240) : ℝ), (309176586873 / 64), 1965843594, (-110270160 : ℝ)]

/-- The coefficients of `F^(7)`, `F(x) = P(x, 467/960 - x)`. -/
noncomputable def hrlFL7 : List ℝ :=
  [(-(73740368752823251852709 / 96636764160000) : ℝ), (300050655799714511205409 / 45298483200000), (75614178156716896599 / 5242880000), (-(20075788061396277 / 655360) : ℝ), (-(56397752354559 / 2048) : ℝ), (927529760619 / 32), 13760905158, (-882161280 : ℝ)]

/-- The coefficients of `F^(8)`, `F(x) = P(x, 467/960 - x)`. -/
noncomputable def hrlFL8 : List ℝ :=
  [(300050655799714511205409 / 45298483200000), (75614178156716896599 / 2621440000), (-(60227364184188831 / 655360) : ℝ), (-(56397752354559 / 512) : ℝ), (4637648803095 / 32), 82565430948, (-6175128960 : ℝ)]

/-- The coefficients of `F^(9)`, `F(x) = P(x, 467/960 - x)`. -/
noncomputable def hrlFL9 : List ℝ :=
  [(75614178156716896599 / 2621440000), (-(60227364184188831 / 327680) : ℝ), (-(169193257063677 / 512) : ℝ), (4637648803095 / 8), 412827154740, (-37050773760 : ℝ)]

/-- The coefficients of `R^(0)`. -/
noncomputable def hrlRL0 : List ℝ :=
  [59785932, (-247628099 : ℝ), (-127109951 : ℝ), 520627200, 448627200, 100270080]

/-- The coefficients of `R^(1)`. -/
noncomputable def hrlRL1 : List ℝ :=
  [(-247628099 : ℝ), (-254219902 : ℝ), 1561881600, 1794508800, 501350400]

/-- The coefficients of `R^(2)`. -/
noncomputable def hrlRL2 : List ℝ :=
  [(-254219902 : ℝ), 3123763200, 5383526400, 2005401600]

theorem hrl_FL_d0 (s : ℝ) : HasDerivAt (lrhHorner hrlFL0) (lrhHorner hrlFL1 s) s := by
  have H := lrh_hasDerivAt_horner hrlFL0 s
  have e : lrhHornerD hrlFL0 s = lrhHorner hrlFL1 s := by
    simp only [hrlFL0, hrlFL1, lrhHornerD, lrhHorner]; ring
  rw [e] at H; exact H

theorem hrl_FL_d1 (s : ℝ) : HasDerivAt (lrhHorner hrlFL1) (lrhHorner hrlFL2 s) s := by
  have H := lrh_hasDerivAt_horner hrlFL1 s
  have e : lrhHornerD hrlFL1 s = lrhHorner hrlFL2 s := by
    simp only [hrlFL1, hrlFL2, lrhHornerD, lrhHorner]; ring
  rw [e] at H; exact H

theorem hrl_FL_d2 (s : ℝ) : HasDerivAt (lrhHorner hrlFL2) (lrhHorner hrlFL3 s) s := by
  have H := lrh_hasDerivAt_horner hrlFL2 s
  have e : lrhHornerD hrlFL2 s = lrhHorner hrlFL3 s := by
    simp only [hrlFL2, hrlFL3, lrhHornerD, lrhHorner]; ring
  rw [e] at H; exact H

theorem hrl_FL_d3 (s : ℝ) : HasDerivAt (lrhHorner hrlFL3) (lrhHorner hrlFL4 s) s := by
  have H := lrh_hasDerivAt_horner hrlFL3 s
  have e : lrhHornerD hrlFL3 s = lrhHorner hrlFL4 s := by
    simp only [hrlFL3, hrlFL4, lrhHornerD, lrhHorner]; ring
  rw [e] at H; exact H

theorem hrl_FL_d4 (s : ℝ) : HasDerivAt (lrhHorner hrlFL4) (lrhHorner hrlFL5 s) s := by
  have H := lrh_hasDerivAt_horner hrlFL4 s
  have e : lrhHornerD hrlFL4 s = lrhHorner hrlFL5 s := by
    simp only [hrlFL4, hrlFL5, lrhHornerD, lrhHorner]; ring
  rw [e] at H; exact H

theorem hrl_FL_d5 (s : ℝ) : HasDerivAt (lrhHorner hrlFL5) (lrhHorner hrlFL6 s) s := by
  have H := lrh_hasDerivAt_horner hrlFL5 s
  have e : lrhHornerD hrlFL5 s = lrhHorner hrlFL6 s := by
    simp only [hrlFL5, hrlFL6, lrhHornerD, lrhHorner]; ring
  rw [e] at H; exact H

theorem hrl_FL_d6 (s : ℝ) : HasDerivAt (lrhHorner hrlFL6) (lrhHorner hrlFL7 s) s := by
  have H := lrh_hasDerivAt_horner hrlFL6 s
  have e : lrhHornerD hrlFL6 s = lrhHorner hrlFL7 s := by
    simp only [hrlFL6, hrlFL7, lrhHornerD, lrhHorner]; ring
  rw [e] at H; exact H

theorem hrl_FL_d7 (s : ℝ) : HasDerivAt (lrhHorner hrlFL7) (lrhHorner hrlFL8 s) s := by
  have H := lrh_hasDerivAt_horner hrlFL7 s
  have e : lrhHornerD hrlFL7 s = lrhHorner hrlFL8 s := by
    simp only [hrlFL7, hrlFL8, lrhHornerD, lrhHorner]; ring
  rw [e] at H; exact H

theorem hrl_FL_d8 (s : ℝ) : HasDerivAt (lrhHorner hrlFL8) (lrhHorner hrlFL9 s) s := by
  have H := lrh_hasDerivAt_horner hrlFL8 s
  have e : lrhHornerD hrlFL8 s = lrhHorner hrlFL9 s := by
    simp only [hrlFL8, hrlFL9, lrhHornerD, lrhHorner]; ring
  rw [e] at H; exact H

theorem hrl_RL_d0 (s : ℝ) : HasDerivAt (lrhHorner hrlRL0) (lrhHorner hrlRL1 s) s := by
  have H := lrh_hasDerivAt_horner hrlRL0 s
  have e : lrhHornerD hrlRL0 s = lrhHorner hrlRL1 s := by
    simp only [hrlRL0, hrlRL1, lrhHornerD, lrhHorner]; ring
  rw [e] at H; exact H

theorem hrl_RL_d1 (s : ℝ) : HasDerivAt (lrhHorner hrlRL1) (lrhHorner hrlRL2 s) s := by
  have H := lrh_hasDerivAt_horner hrlRL1 s
  have e : lrhHornerD hrlRL1 s = lrhHorner hrlRL2 s := by
    simp only [hrlRL1, hrlRL2, lrhHornerD, lrhHorner]; ring
  rw [e] at H; exact H

theorem hrl_F_eq (x : ℝ) : hrlP x (467 / 960 - x) = lrhHorner hrlFL0 x := by
  simp only [hrlFL0, lrhHorner]
  unfold hrlP hrlCF0 hrlCF1 hrlCF2 hrlCF3 hrlCF4 hrlCF5 hrlCF6
  ring

theorem hrl_R_eq (x : ℝ) : hrlRf x = lrhHorner hrlRL0 x := by
  simp only [hrlRL0, lrhHorner]; unfold hrlRf; ring

theorem hrl_xb {x : ℝ} (h1 : (17 / 60) ≤ x) (h2 : x ≤ (3 / 7)) :
    ((289 / 3600) : ℝ) ≤ x ^ (2 : ℕ) ∧
      x ^ (2 : ℕ) ≤ ((9 / 49) : ℝ) ∧
      ((4913 / 216000) : ℝ) ≤ x ^ (3 : ℕ) ∧
      x ^ (3 : ℕ) ≤ ((27 / 343) : ℝ) ∧
      ((83521 / 12960000) : ℝ) ≤ x ^ (4 : ℕ) ∧
      x ^ (4 : ℕ) ≤ ((81 / 2401) : ℝ) ∧
      ((1419857 / 777600000) : ℝ) ≤ x ^ (5 : ℕ) ∧
      x ^ (5 : ℕ) ≤ ((243 / 16807) : ℝ) ∧
      ((24137569 / 46656000000) : ℝ) ≤ x ^ (6 : ℕ) ∧
      x ^ (6 : ℕ) ≤ ((729 / 117649) : ℝ) ∧
      ((410338673 / 2799360000000) : ℝ) ≤ x ^ (7 : ℕ) ∧
      x ^ (7 : ℕ) ≤ ((2187 / 823543) : ℝ) ∧
      ((6975757441 / 167961600000000) : ℝ) ≤ x ^ (8 : ℕ) ∧
      x ^ (8 : ℕ) ≤ ((6561 / 5764801) : ℝ) := by
  have l : ∀ n : ℕ, ((17 / 60) : ℝ) ^ n ≤ x ^ n := fun n => pow_le_pow_left₀ (by norm_num) h1 n
  have u : ∀ n : ℕ, x ^ n ≤ ((3 / 7) : ℝ) ^ n := fun n => pow_le_pow_left₀ (by linarith) h2 n
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  all_goals first
    | (have := l 2; norm_num at this ⊢; linarith) | (have := u 2; norm_num at this ⊢; linarith)
    | (have := l 3; norm_num at this ⊢; linarith) | (have := u 3; norm_num at this ⊢; linarith)
    | (have := l 4; norm_num at this ⊢; linarith) | (have := u 4; norm_num at this ⊢; linarith)
    | (have := l 5; norm_num at this ⊢; linarith) | (have := u 5; norm_num at this ⊢; linarith)
    | (have := l 6; norm_num at this ⊢; linarith) | (have := u 6; norm_num at this ⊢; linarith)
    | (have := l 7; norm_num at this ⊢; linarith) | (have := u 7; norm_num at this ⊢; linarith)
    | (have := l 8; norm_num at this ⊢; linarith) | (have := u 8; norm_num at this ⊢; linarith)

theorem hrl_sb {s : ℝ} (h1 : 0 ≤ s) (h2 : s ≤ (61 / 420)) :
    (0 : ℝ) ≤ s ^ (2 : ℕ) ∧
      s ^ (2 : ℕ) ≤ ((3721 / 176400) : ℝ) ∧
      (0 : ℝ) ≤ s ^ (3 : ℕ) ∧
      s ^ (3 : ℕ) ≤ ((226981 / 74088000) : ℝ) ∧
      (0 : ℝ) ≤ s ^ (4 : ℕ) ∧
      s ^ (4 : ℕ) ≤ ((13845841 / 31116960000) : ℝ) ∧
      (0 : ℝ) ≤ s ^ (5 : ℕ) ∧
      s ^ (5 : ℕ) ≤ ((844596301 / 13069123200000) : ℝ) ∧
      (0 : ℝ) ≤ s ^ (6 : ℕ) ∧
      s ^ (6 : ℕ) ≤ ((51520374361 / 5489031744000000) : ℝ) ∧
      (0 : ℝ) ≤ s ^ (7 : ℕ) ∧
      s ^ (7 : ℕ) ≤ ((3142742836021 / 2305393332480000000) : ℝ) ∧
      (0 : ℝ) ≤ s ^ (8 : ℕ) ∧
      s ^ (8 : ℕ) ≤ ((191707312997281 / 968265199641600000000) : ℝ) := by
  have l : ∀ n : ℕ, (0 : ℝ) ^ n ≤ s ^ n := fun n => pow_le_pow_left₀ (by norm_num) h1 n
  have u : ∀ n : ℕ, s ^ n ≤ ((61 / 420) : ℝ) ^ n := fun n => pow_le_pow_left₀ (by linarith) h2 n
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  all_goals first
    | (have := l 2; norm_num at this ⊢; linarith) | (have := u 2; norm_num at this ⊢; linarith)
    | (have := l 3; norm_num at this ⊢; linarith) | (have := u 3; norm_num at this ⊢; linarith)
    | (have := l 4; norm_num at this ⊢; linarith) | (have := u 4; norm_num at this ⊢; linarith)
    | (have := l 5; norm_num at this ⊢; linarith) | (have := u 5; norm_num at this ⊢; linarith)
    | (have := l 6; norm_num at this ⊢; linarith) | (have := u 6; norm_num at this ⊢; linarith)
    | (have := l 7; norm_num at this ⊢; linarith) | (have := u 7; norm_num at this ⊢; linarith)
    | (have := l 8; norm_num at this ⊢; linarith) | (have := u 8; norm_num at this ⊢; linarith)

/-- `F⁽⁹⁾ < 0` on `[17/60, 3/7]` (face note (F6)). -/
theorem hrl_F9_neg {x : ℝ} (h1 : 17 / 60 ≤ x) (h2 : x ≤ 3 / 7) : lrhHorner hrlFL9 x < 0 := by
  obtain ⟨s, rfl⟩ : ∃ s, x = s + 17 / 60 := ⟨x - 17 / 60, by ring⟩
  have hs0 : 0 ≤ s := by linarith
  have hs1 : s ≤ 61 / 420 := by linarith
  obtain ⟨l2, u2, l3, u3, l4, u4, l5, u5, l6, u6, l7, u7, l8, u8⟩ := hrl_sb hs0 hs1
  have e : lrhHorner hrlFL9 (s + 17 / 60) = (-(89081107364515043449 / 2621440000) : ℝ) + (-(63923547408347487 / 327680) : ℝ) * s ^ (1 : ℕ) + (902943613293183 / 2560) * s ^ (2 : ℕ) + (8142666703479 / 8) * s ^ (3 : ℕ) + 360338558580 * s ^ (4 : ℕ) + (-37050773760 : ℝ) * s ^ (5 : ℕ) := by
    simp only [hrlFL9, lrhHorner]; ring
  rw [e]; linarith only [hs0, l5, u2, u3, u4]

theorem hrl_jet0 : 0 < lrhHorner hrlFL7 (17 / 60) := by
  simp only [hrlFL7, lrhHorner]; norm_num

theorem hrl_jet1 : 0 < lrhHorner hrlFL7 (3 / 7) := by
  simp only [hrlFL7, lrhHorner]; norm_num

theorem hrl_jet2 : lrhHorner hrlFL5 (17 / 60) < 0 := by
  simp only [hrlFL5, lrhHorner]; norm_num

theorem hrl_jet3 : lrhHorner hrlFL5 (3 / 7) < 0 := by
  simp only [hrlFL5, lrhHorner]; norm_num

theorem hrl_jet4 : lrhHorner hrlFL4 (17 / 60) < 0 := by
  simp only [hrlFL4, lrhHorner]; norm_num

theorem hrl_jet5 : 0 < lrhHorner hrlFL2 (17 / 60) := by
  simp only [hrlFL2, lrhHorner]; norm_num

theorem hrl_jet6 : 0 < lrhHorner hrlFL2 (2 / 5) := by
  simp only [hrlFL2, lrhHorner]; norm_num

theorem hrl_jet7 : 0 < lrhHorner hrlFL1 (2 / 5) := by
  simp only [hrlFL1, lrhHorner]; norm_num

theorem hrl_jet8 : 0 < lrhHorner hrlFL1 (3 / 7) := by
  simp only [hrlFL1, lrhHorner]; norm_num

theorem hrl_jet9 : 5 ≤ lrhHorner hrlFL0 (11 / 30) := by
  simp only [hrlFL0, lrhHorner]; norm_num

theorem hrl_jet10 : 19 ≤ lrhHorner hrlFL1 (11 / 30) := by
  simp only [hrlFL1, lrhHorner]; norm_num

theorem hrl_jet11 : lrhHorner hrlFL1 (11 / 30) ≤ 21 := by
  simp only [hrlFL1, lrhHorner]; norm_num

/-- **The line face** (face note §6): `F(x) = P(x, 467/960 - x) ≥ 13/4` on `[17/60, 3/7]`. -/
theorem hrl_F_ge {x : ℝ} (h1 : 17 / 60 ≤ x) (h2 : x ≤ 3 / 7) : 13 / 4 ≤ lrhHorner hrlFL0 x := by
  -- `F⁽⁸⁾` decreases, so `F⁽⁷⁾` (concave) is positive
  have a8 : ∀ u v, 17 / 60 ≤ u → u ≤ v → v ≤ 3 / 7 → lrhHorner hrlFL8 v ≤ lrhHorner hrlFL8 u :=
    fun u v hu huv hv => hrl_anti hrl_FL_d8 (fun s h1 h2 => (hrl_F9_neg h1 h2).le) hu huv hv
  have p7 : ∀ s, 17 / 60 ≤ s → s ≤ 3 / 7 → 0 < lrhHorner hrlFL7 s :=
    fun s h1 h2 => hrl_concave_pos hrl_FL_d7 a8 hrl_jet0 hrl_jet1 h1 h2
  -- `F⁽⁶⁾` increases, so `F⁽⁵⁾` (convex) is negative
  have a6 : ∀ u v, 17 / 60 ≤ u → u ≤ v → v ≤ 3 / 7 →
      -lrhHorner hrlFL6 v ≤ -lrhHorner hrlFL6 u := fun u v hu huv hv => by
    have := hrl_mono hrl_FL_d6 (fun s h1 h2 => (p7 s h1 h2).le) hu huv hv; linarith
  have n5 : ∀ s, 17 / 60 ≤ s → s ≤ 3 / 7 → lrhHorner hrlFL5 s < 0 := fun s h1 h2 => by
    have := hrl_concave_pos (f := fun s => -lrhHorner hrlFL5 s) (f' := fun s => -lrhHorner hrlFL6 s)
      (fun s => (hrl_FL_d5 s).neg) a6 (show 0 < -lrhHorner hrlFL5 (17 / 60) by linarith [hrl_jet2])
      (show 0 < -lrhHorner hrlFL5 (3 / 7) by linarith [hrl_jet3]) h1 h2
    have : 0 < -lrhHorner hrlFL5 s := this
    linarith
  -- `F⁽⁴⁾` decreases from a negative value; `F⁽³⁾` decreases
  have n4 : ∀ s, 17 / 60 ≤ s → s ≤ 3 / 7 → lrhHorner hrlFL4 s < 0 := fun s h1 h2 => by
    have := hrl_anti hrl_FL_d4 (fun s h1 h2 => (n5 s h1 h2).le) le_rfl h1 h2
    have := hrl_jet4; linarith
  have a3 : ∀ u v, 17 / 60 ≤ u → u ≤ v → v ≤ 3 / 7 → lrhHorner hrlFL3 v ≤ lrhHorner hrlFL3 u :=
    fun u v hu huv hv => hrl_anti hrl_FL_d3 (fun s h1 h2 => (n4 s h1 h2).le) hu huv hv
  -- on `[17/60, 2/5]`: `F'' > 0`, so `F` lies above its tangent at `11/30`
  have p2 : ∀ s, 17 / 60 ≤ s → s ≤ 2 / 5 → 0 < lrhHorner hrlFL2 s := fun s h1 h2 =>
    hrl_concave_pos hrl_FL_d2 (fun u v hu huv hv => a3 u v hu huv (by linarith)) hrl_jet5 hrl_jet6 h1 h2
  have tangent : ∀ s, 17 / 60 ≤ s → s ≤ 2 / 5 →
      lrhHorner hrlFL0 (11 / 30) + lrhHorner hrlFL1 (11 / 30) * (s - 11 / 30) ≤ lrhHorner hrlFL0 s := by
    intro s h1 h2
    have hd : ∀ u, HasDerivAt (fun u => lrhHorner hrlFL0 u - lrhHorner hrlFL1 (11 / 30) * u)
        (lrhHorner hrlFL1 u - lrhHorner hrlFL1 (11 / 30)) u := fun u =>
      ((hrl_FL_d0 u).sub ((hasDerivAt_id' u).const_mul (lrhHorner hrlFL1 (11 / 30)))).congr_deriv
        (by ring)
    rcases le_total s (11 / 30) with hs | hs
    · have := hrl_anti hd (a := 17 / 60) (b := 11 / 30) (fun u hu1 hu2 => by
        have := hrl_mono hrl_FL_d1 (a := 17 / 60) (b := 2 / 5) (fun w w1 w2 => (p2 w w1 w2).le)
          hu1 hu2 (by norm_num)
        linarith) h1 hs le_rfl
      linarith
    · have := hrl_mono hd (a := 11 / 30) (b := 2 / 5) (fun u hu1 hu2 => by
        have := hrl_mono hrl_FL_d1 (a := 17 / 60) (b := 2 / 5) (fun w w1 w2 => (p2 w w1 w2).le)
          (by norm_num) hu1 hu2
        linarith) le_rfl hs h2
      linarith
  have left : ∀ s, 17 / 60 ≤ s → s ≤ 2 / 5 → 13 / 4 ≤ lrhHorner hrlFL0 s := fun s h1 h2 => by
    have := tangent s h1 h2
    have j0 := hrl_jet9; have j1 := hrl_jet10; have j2 := hrl_jet11
    rcases le_total s (11 / 30) with hs | hs
    · have : 0 ≤ (21 - lrhHorner hrlFL1 (11 / 30)) * (11 / 30 - s) :=
        mul_nonneg (by linarith) (by linarith)
      linarith
    · have : 0 ≤ lrhHorner hrlFL1 (11 / 30) * (s - 11 / 30) := mul_nonneg (by linarith) (by linarith)
      linarith
  -- on `[2/5, 3/7]`: `F'` is concave and positive at both ends, so `F` increases
  have p1 : ∀ s, 2 / 5 ≤ s → s ≤ 3 / 7 → 0 < lrhHorner hrlFL1 s := fun s h1 h2 => by
    rcases le_or_gt 0 (lrhHorner hrlFL2 s) with hs | hs
    · have nn : ∀ w, 2 / 5 ≤ w → w ≤ s → 0 ≤ lrhHorner hrlFL2 w := fun w w1 w2 => by
        rcases le_or_gt 0 (lrhHorner hrlFL3 w) with h3 | h3
        · have := hrl_mono hrl_FL_d2 (a := 2 / 5) (b := w)
            (fun u u1 u2 => le_trans h3 (a3 u w (by linarith) u2 (by linarith))) le_rfl w1 le_rfl
          linarith [hrl_jet6]
        · have := hrl_anti hrl_FL_d2 (a := w) (b := s)
            (fun u u1 u2 => le_trans (a3 w u (by linarith) u1 (by linarith)) h3.le) le_rfl w2 le_rfl
          linarith
      have := hrl_mono hrl_FL_d1 (a := 2 / 5) (b := s) nn le_rfl h1 le_rfl
      linarith [hrl_jet7]
    · have h3 : lrhHorner hrlFL3 s ≤ 0 := by
        by_contra hc
        push Not at hc
        have := hrl_mono hrl_FL_d2 (a := 2 / 5) (b := s)
          (fun u u1 u2 => le_trans hc.le (a3 u s (by linarith) u2 h2)) le_rfl h1 le_rfl
        linarith [hrl_jet6]
      have h2' : ∀ u, s ≤ u → u ≤ 3 / 7 → lrhHorner hrlFL2 u ≤ 0 := fun u u1 u2 => by
        have := hrl_anti hrl_FL_d2 (a := s) (b := 3 / 7)
          (fun w w1 w2 => le_trans (a3 s w (by linarith) w1 w2) h3) le_rfl u1 u2
        linarith
      have := hrl_anti hrl_FL_d1 (a := s) (b := 3 / 7) h2' le_rfl h2 le_rfl
      linarith [hrl_jet8]
  rcases le_total x (2 / 5) with hx | hx
  · exact left x h1 hx
  · have := hrl_mono hrl_FL_d0 (fun s h1 h2 => (p1 s h1 h2).le) le_rfl hx h2
    have := left (2 / 5) (by norm_num) le_rfl
    linarith

/-- `C₀ > 20` on `[17/60, 3/7]` (face note (F4)): `R` is convex with `R < -5·10⁶` at both ends. -/
theorem hrl_CF0_gt {x : ℝ} (h1 : 17 / 60 ≤ x) (h2 : x ≤ 3 / 7) : 20 < hrlCF0 x := by
  have hR2 : ∀ s, 17 / 60 ≤ s → s ≤ 3 / 7 → 0 ≤ lrhHorner hrlRL2 s := fun s h1 h2 => by
    simp only [hrlRL2, lrhHorner]; nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ s) (by linarith : (0 : ℝ) ≤ s)]
  have a1 : ∀ u v, 17 / 60 ≤ u → u ≤ v → v ≤ 3 / 7 →
      -lrhHorner hrlRL1 v ≤ -lrhHorner hrlRL1 u := fun u v hu huv hv => by
    have := hrl_mono hrl_RL_d1 hR2 hu huv hv; linarith
  have key := hrl_concave_pos (f := fun s => -lrhHorner hrlRL0 s - 5000000)
    (f' := fun s => -lrhHorner hrlRL1 s) (fun s => ((hrl_RL_d0 s).neg.sub_const 5000000)) a1
    (show 0 < -lrhHorner hrlRL0 (17 / 60) - 5000000 by simp only [hrlRL0, lrhHorner]; norm_num)
    (show 0 < -lrhHorner hrlRL0 (3 / 7) - 5000000 by simp only [hrlRL0, lrhHorner]; norm_num) h1 h2
  have k2 : 0 < -lrhHorner hrlRL0 x - 5000000 := key
  have e : hrlCF0 x = -5 * x * lrhHorner hrlRL0 x / 262144 := by
    rw [← hrl_R_eq]; unfold hrlCF0 hrlRf; ring
  rw [e]
  have : 5 * x * 5000000 ≤ 5 * x * (-lrhHorner hrlRL0 x) :=
    mul_le_mul_of_nonneg_left (by linarith) (by linarith)
  have : (20 : ℝ) * 262144 < 5 * x * 5000000 := by nlinarith
  rw [lt_div_iff₀ (by norm_num)]; nlinarith

/-- `C₂ < 0` on `x ≥ 17/60` (face note §2): `-524288C₂` has positive Taylor coefficients at `17/60`. -/
theorem hrl_CF2_neg {x : ℝ} (h1 : 17 / 60 ≤ x) : hrlCF2 x < 0 := by
  obtain ⟨s, rfl⟩ : ∃ s, x = s + 17 / 60 := ⟨x - 17 / 60, by ring⟩
  have hs : 0 ≤ s := by linarith
  have e : -524288 * hrlCF2 (s + 17 / 60) = (9202337071503112987 / 9112500000) + (528646041153630649 / 12656250) * s ^ (1 : ℕ) + (321141290596410112 / 1265625) * s ^ (2 : ℕ) + (52159732819853888 / 84375) * s ^ (3 : ℕ) + (90618539600296 / 125) * s ^ (4 : ℕ) + (165554232451072 / 375) * s ^ (5 : ℕ) + (3464603512832 / 25) * s ^ (6 : ℕ) + (102468943872 / 5) * s ^ (7 : ℕ) + 1283457024 * s ^ (8 : ℕ) := by unfold hrlCF2; ring
  have : 0 < (9202337071503112987 / 9112500000) + (528646041153630649 / 12656250) * s ^ (1 : ℕ) + (321141290596410112 / 1265625) * s ^ (2 : ℕ) + (52159732819853888 / 84375) * s ^ (3 : ℕ) + (90618539600296 / 125) * s ^ (4 : ℕ) + (165554232451072 / 375) * s ^ (5 : ℕ) + (3464603512832 / 25) * s ^ (6 : ℕ) + (102468943872 / 5) * s ^ (7 : ℕ) + 1283457024 * s ^ (8 : ℕ) := by positivity
  linarith

theorem hrl_CF3_neg {x : ℝ} (h1 : 17 / 60 ≤ x) (h2 : x ≤ 3 / 7) : hrlCF3 x < 0 := by
  obtain ⟨l2, u2, l3, u3, l4, u4, l5, u5, l6, u6, l7, u7, l8, u8⟩ := hrl_xb h1 h2
  unfold hrlCF3; linarith only [h1, l2, l3, l4, l5, l6, l7, l8]

theorem hrl_CF4_neg {x : ℝ} (h1 : 17 / 60 ≤ x) (h2 : x ≤ 3 / 7) : hrlCF4 x < 0 := by
  obtain ⟨l2, u2, l3, u3, l4, u4, l5, u5, l6, u6, l7, u7, l8, u8⟩ := hrl_xb h1 h2
  unfold hrlCF4; linarith only [h1, l2, l3, l4, l5, l6, l7, l8]

theorem hrl_CF5_neg {x : ℝ} (h1 : 17 / 60 ≤ x) (h2 : x ≤ 3 / 7) : hrlCF5 x < 0 := by
  obtain ⟨l2, u2, l3, u3, l4, u4, l5, u5, l6, u6, l7, u7, l8, u8⟩ := hrl_xb h1 h2
  unfold hrlCF5; linarith only [h1, l2, l3, l4, l5, l6, l7, l8]

theorem hrl_CF6_neg {x : ℝ} (h1 : 17 / 60 ≤ x) (h2 : x ≤ 3 / 7) : hrlCF6 x < 0 := by
  obtain ⟨l2, u2, l3, u3, l4, u4, l5, u5, l6, u6, l7, u7, l8, u8⟩ := hrl_xb h1 h2
  unfold hrlCF6; linarith only [h1, l2, l3, l4, l5, l6, l7, l8]

/-- **The terminal face** (`NONSHORT_HIGH_RATIO_LOWER_FACE` (F1)): `P(x, y) ≥ 13/4` for
`17/60 ≤ x ≤ 3/7`, `0 ≤ y`, `y(1 + 4x) ≤ 1 - 2x`. -/
theorem hrl_face {x y : ℝ} (h1 : 17 / 60 ≤ x) (h2 : x ≤ 3 / 7) (hy0 : 0 ≤ y)
    (hy : y * (1 + 4 * x) ≤ 1 - 2 * x) : 13 / 4 ≤ hrlP x y := by
  have c0 := hrl_CF0_gt h1 h2
  have c2 := hrl_CF2_neg h1
  have c3 := hrl_CF3_neg h1 h2
  have c4 := hrl_CF4_neg h1 h2
  have c5 := hrl_CF5_neg h1 h2
  have c6 := hrl_CF6_neg h1 h2
  have hF := hrl_F_ge h1 h2
  rw [← hrl_F_eq] at hF
  obtain ⟨b, hb⟩ : ∃ b, b = 467 / 960 - x := ⟨_, rfl⟩
  rw [← hb] at hF
  have hb0 : 0 < b := by rw [hb]; linarith
  -- `y ≤ b` (face note (F3))
  have hyb : y ≤ b := by
    have : (1 - 2 * x) ≤ b * (1 + 4 * x) := by rw [hb]; nlinarith
    have h4 : 0 < 1 + 4 * x := by linarith
    nlinarith
  -- concavity in `y`: `Cᵢ yⁱ b ≥ Cᵢ y bⁱ` for `i ≥ 2`
  have yb : ∀ n : ℕ, y ^ n ≤ b ^ n := fun n => pow_le_pow_left₀ hy0 hyb n
  have f2 : hrlCF2 x * (y * b ^ (2 : ℕ)) ≤ hrlCF2 x * (y ^ (2 : ℕ) * b) := by
    apply mul_le_mul_of_nonpos_left _ c2.le
    have := mul_le_mul_of_nonneg_left (yb 1) (mul_nonneg hy0 hb0.le); nlinarith
  have f3 : hrlCF3 x * (y * b ^ (3 : ℕ)) ≤ hrlCF3 x * (y ^ (3 : ℕ) * b) := by
    apply mul_le_mul_of_nonpos_left _ c3.le
    have := mul_le_mul_of_nonneg_left (yb 2) (mul_nonneg hy0 hb0.le); nlinarith
  have f4 : hrlCF4 x * (y * b ^ (4 : ℕ)) ≤ hrlCF4 x * (y ^ (4 : ℕ) * b) := by
    apply mul_le_mul_of_nonpos_left _ c4.le
    have := mul_le_mul_of_nonneg_left (yb 3) (mul_nonneg hy0 hb0.le); nlinarith
  have f5 : hrlCF5 x * (y * b ^ (5 : ℕ)) ≤ hrlCF5 x * (y ^ (5 : ℕ) * b) := by
    apply mul_le_mul_of_nonpos_left _ c5.le
    have := mul_le_mul_of_nonneg_left (yb 4) (mul_nonneg hy0 hb0.le); nlinarith
  have f6 : hrlCF6 x * (y * b ^ (6 : ℕ)) ≤ hrlCF6 x * (y ^ (6 : ℕ) * b) := by
    apply mul_le_mul_of_nonpos_left _ c6.le
    have := mul_le_mul_of_nonneg_left (yb 5) (mul_nonneg hy0 hb0.le); nlinarith
  have g1 : 13 / 4 * y ≤ y * hrlP x b := by
    have := mul_le_mul_of_nonneg_left hF hy0; linarith
  have g0 : 13 / 4 * (b - y) ≤ (b - y) * hrlCF0 x := by
    have := mul_le_mul_of_nonneg_left c0.le (sub_nonneg.2 hyb); linarith
  have key : 13 / 4 * b ≤ hrlP x y * b := by
    unfold hrlP at g1 ⊢
    linarith
  exact le_of_mul_le_mul_right key hb0

end SmoothedOctagon
