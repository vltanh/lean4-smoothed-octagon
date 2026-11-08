module

public import SmoothedOctagon.Exclusion.Mixed.FwdHand.LowTHorner

/-!
# Case M2, forward successor by hand: the low-`t` unit sign on the maximum-duration face

`docs/lighter-proofs/NONSHORT_LOW_T_QMAX.md` and `NONSHORT_LOW_T_QMAX_AUXILIARIES.md` (PR #2, branch
`proof/lighter-signs`). On the face `q = (1 + h + j)/(1 + 2j)` (`y = (h - j)/d`, `d = 1 + 2j`) the
cleared circuit `6 d⁶ S = W² P` (`W = 1 + h + j`) defines the bivariate polynomial `P(h, j)` of the
note (10) (`nltPqL`, `nlt_Pq_eq`). Its `j`-derivative is the factored polynomial `𝓡` of (13)
(`nlt_Pq_dj`), which is at least `500𝓜` on `[1/4, 1/3] × [0, 1/4]` (15) (`nlt_Rq_ge`); `𝓜 > 0` on
`1/30 ≤ j ≤ 3h/4` (auxiliary note (1), via `∂_h𝓜 > 0` (4) and the two endpoint faces) (`nlt_Mq_pos`).
Hence `P` increases in `j` and `P(h, j) ≥ P(h, 1/30) > 39` (`nlt_face_qmax`).

Route: `P(h, 1/30) > 39` is proved directly as a one-variable sign (termwise monomial bound after a
shift) in place of the zero-gap value (19) and the integral bound (21)-(25); the identities (10),
(14) are checked by direct expansion (at most 136 monomials) instead of sixth derivatives and zero
jets; the one-variable signs use termwise monomial bounds after a shift.

## Main API

* `nltPqL`, `nlt_Pq_eq`; `nltMq`, `nltEq`, `nltUq1`, …, `nltVq5`, `nltDq9`, …, `nltRq`, `nlt_Pq_dj`.
* `nlt_Rq_ge`, `nlt_Mq_pos`, `nlt_face_qmax`.
-/

@[expose] public section

namespace SmoothedOctagon

/-- The coefficients in `j` of the cleared maximum-duration numerator `P(h, j)` (note (10)). -/
noncomputable def nltPqL (h : ℝ) : List ℝ :=
  [(12 * h ^ 2 - 22762 * h ^ 3 - 38304 * h ^ 4 + 80212 * h ^ 5 + 116136 * h ^ 6 - 578049 * h ^ 7 - 1754001 * h ^ 8 - 2140842 * h ^ 9 - 1430898 * h ^ 10 - 552873 * h ^ 11 - 118887 * h ^ 12 - 11628 * h ^ 13 : ℝ), (-2408 * h + 110558 * h ^ 2 + 97600 * h ^ 3 + 945162 * h ^ 4 + 3769971 * h ^ 5 + 4134198 * h ^ 6 - 2453427 * h ^ 7 - 10074486 * h ^ 8 - 10564929 * h ^ 9 - 5810568 * h ^ 10 - 1841121 * h ^ 11 - 322434 * h ^ 12 - 23256 * h ^ 13 : ℝ), (12 - 21350 * h + 62196 * h ^ 2 - 2055456 * h ^ 3 + 2684664 * h ^ 4 + 20680851 * h ^ 5 + 26170965 * h ^ 6 + 4415583 * h ^ 7 - 16639725 * h ^ 8 - 16544076 * h ^ 9 - 7261710 * h ^ 10 - 1675542 * h ^ 11 - 170136 * h ^ 12 : ℝ), (-42798 + 570408 * h - 1856220 * h ^ 2 - 18016574 * h ^ 3 - 5750376 * h ^ 4 + 53365412 * h ^ 5 + 77418402 * h ^ 6 + 36992574 * h ^ 7 - 1386072 * h ^ 8 - 7462464 * h ^ 9 - 2762316 * h ^ 10 - 399024 * h ^ 11 : ℝ), (-479468 + 5559084 * h - 2262932 * h ^ 2 - 52062067 * h ^ 3 - 31873443 * h ^ 4 + 80610387 * h ^ 5 + 123127329 * h ^ 6 + 67169508 * h ^ 7 + 16571034 * h ^ 8 + 1631064 * h ^ 9 - 93024 * h ^ 10 : ℝ), (-2643022 + 20052419 * h + 12903858 * h ^ 2 - 74774025 * h ^ 3 - 59330232 * h ^ 4 + 65560812 * h ^ 5 + 100739844 * h ^ 6 + 48612174 * h ^ 7 + 11265012 * h ^ 8 + 1153008 * h ^ 9 : ℝ), (-8786580 + 36875433 * h + 41708145 * h ^ 2 - 62851071 * h ^ 3 - 70519173 * h ^ 4 + 14474358 * h ^ 5 + 35225268 * h ^ 6 + 13355964 * h ^ 7 + 2044080 * h ^ 8 : ℝ), (-18285880 + 37322168 * h + 53759262 * h ^ 2 - 36739830 * h ^ 3 - 57636612 * h ^ 4 - 14090832 * h ^ 5 + 1718016 * h ^ 6 + 1008576 * h ^ 7 : ℝ), (-23855858 + 21566391 * h + 39183213 * h ^ 2 - 15939723 * h ^ 3 - 27429555 * h ^ 4 - 8688660 * h ^ 5 - 935136 * h ^ 6 : ℝ), (-19296978 + 8913549 * h + 19369812 * h ^ 2 - 3696549 * h ^ 3 - 6431010 * h ^ 4 - 1570392 * h ^ 5 : ℝ), (-9383466 + 4241574 * h + 6422994 * h ^ 2 - 435318 * h ^ 3 - 845784 * h ^ 4 : ℝ), (-2427636 + 1677000 * h + 919548 * h ^ 2 - 168912 * h ^ 3 : ℝ), (-210936 + 210936 * h : ℝ)]

/-- **The cleared face numerator** (note (10)): `6 d⁶ S = W² P` on `q = W/d`. -/
theorem nlt_Pq_eq (h j : ℝ) :
    6 * nltSt0 ((1 - h) / 2) (h + j) * (h - j) ^ 0 * (1 + 2 * j) ^ 6 + 6 * nltSt1 ((1 - h) / 2) (h + j) * (h - j) ^ 1 * (1 + 2 * j) ^ 5 + 6 * nltSt2 ((1 - h) / 2) (h + j) * (h - j) ^ 2 * (1 + 2 * j) ^ 4 + 6 * nltSt3 ((1 - h) / 2) (h + j) * (h - j) ^ 3 * (1 + 2 * j) ^ 3 + 6 * nltSt4 ((1 - h) / 2) (h + j) * (h - j) ^ 4 * (1 + 2 * j) ^ 2 + 6 * nltSt5 ((1 - h) / 2) (h + j) * (h - j) ^ 5 * (1 + 2 * j) ^ 1 + 6 * nltSt6 ((1 - h) / 2) (h + j) * (h - j) ^ 6 * (1 + 2 * j) ^ 0 = (1 + h + j) ^ 2 * lrhHorner (nltPqL h) j := by
  rw [nlt_St_h0, nlt_St_h1, nlt_St_h2, nlt_St_h3, nlt_St_h4, nlt_St_h5, nlt_St_h6]
  simp only [nltL0, nltL1, nltL2, nltL3, nltL4, nltL5, nltL6, nltPqL, lrhHorner]
  ring

/-- The auxiliary polynomial `𝓜` (auxiliary note (3)). -/
noncomputable def nltMq (h j : ℝ) : ℝ :=
  -5 * h - 257 * j ^ 2 - 86 * h * j + 221 * h ^ 2 - 3836 * j ^ 3 + 3422 * h * j ^ 2 + 248 * h ^ 2 * j + 195 * h ^ 3 - 26431 * j ^ 4 + 44472 * h * j ^ 3 - 11138 * h ^ 2 * j ^ 2 - 8222 * h ^ 3 * j + 1890 * h ^ 4 - 105439 * j ^ 5 + 200524 * h * j ^ 4 - 18104 * h ^ 2 * j ^ 3 - 108100 * h ^ 3 * j ^ 2 + 10738 * h ^ 4 * j + 7539 * h ^ 5 - 256003 * j ^ 6 + 442505 * h * j ^ 5 + 129038 * h ^ 2 * j ^ 4 - 416497 * h ^ 3 * j ^ 3 - 34503 * h ^ 4 * j ^ 2 + 82723 * h ^ 5 * j + 8268 * h ^ 6 - 381694 * j ^ 7 + 522510 * h * j ^ 6 + 500497 * h ^ 2 * j ^ 5 - 747741 * h ^ 3 * j ^ 4 - 254988 * h ^ 4 * j ^ 3 + 320192 * h ^ 5 * j ^ 2 + 104683 * h ^ 6 * j - 4907 * h ^ 7 - 336381 * j ^ 8 + 455425 * h * j ^ 7 + 484321 * h ^ 2 * j ^ 6 - 1018180 * h ^ 3 * j ^ 5 - 358391 * h ^ 4 * j ^ 4 + 926841 * h ^ 5 * j ^ 3 + 517202 * h ^ 6 * j ^ 2 - 13039 * h ^ 7 * j - 28629 * h ^ 8

/-- The positive error polynomial `𝓔` (note §2). -/
noncomputable def nltEq (h j : ℝ) : ℝ :=
  24 * j + 92 * h + 106 * j ^ 2 + 300 * h * j + 58 * h ^ 2 + 128 * j ^ 3 + 224 * h * j ^ 2 + 392 * h ^ 2 * j + 100 * h ^ 3 + 390 * j ^ 4 + 336 * h * j ^ 3 + 340 * h ^ 2 * j ^ 2 + 88 * h ^ 3 * j + 162 * h ^ 4 + 20 * j ^ 5 + 95 * h * j ^ 4 + 272 * h ^ 2 * j ^ 3 + 278 * h ^ 3 * j ^ 2 + 328 * h ^ 4 * j + 471 * h ^ 5 + 340 * j ^ 6 + 98 * h * j ^ 5 + 290 * h ^ 2 * j ^ 4 + 232 * h ^ 3 * j ^ 3 + 372 * h ^ 4 * j ^ 2 + 202 * h ^ 5 * j + 198 * h ^ 6 + 136 * j ^ 7 + 176 * h * j ^ 6 + 370 * h ^ 2 * j ^ 5 + 375 * h ^ 3 * j ^ 4 + 228 * h ^ 4 * j ^ 3 + 236 * h ^ 5 * j ^ 2 + 430 * h ^ 6 * j + 73 * h ^ 7 + (106467959 / 48) * j ^ 8 + (5674 / 27) * h * j ^ 7 + (13483 / 48) * h ^ 2 * j ^ 6 + (7817 / 16) * h ^ 3 * j ^ 5 + (1025 / 32) * h ^ 4 * j ^ 4 + (10739 / 27) * h ^ 5 * j ^ 3 + (3881 / 18) * h ^ 6 * j ^ 2 + (10220 / 27) * h ^ 7 * j + (13130 / 27) * h ^ 8

/-- The homogeneous factor `U_1` (note §2). -/
noncomputable def nltUq1 (h j : ℝ) : ℝ :=
  80221941 * j ^ 8 + 313465704 * h * j ^ 7 + 327804060 * h ^ 4 * j ^ 4 + 492509316 * h ^ 5 * j ^ 3 + 110977722 * h ^ 6 * j ^ 2

/-- The homogeneous factor `V_1` (note §2). -/
noncomputable def nltVq1 (h j : ℝ) : ℝ :=
  257178810 * h ^ 2 * j ^ 6 + 423115038 * h ^ 3 * j ^ 5 + 33279450 * h ^ 7 * j + 10564929 * h ^ 8

/-- The homogeneous factor `U_2` (note §2). -/
noncomputable def nltUq2 (h j : ℝ) : ℝ :=
  174328308 * j ^ 8 + 86846148 * h ^ 3 * j ^ 5 + 503699220 * h ^ 4 * j ^ 4 + 268678032 * h ^ 5 * j ^ 3

/-- The homogeneous factor `V_2` (note §2). -/
noncomputable def nltVq2 (h j : ℝ) : ℝ :=
  127517784 * h * j ^ 7 + 403456284 * h ^ 2 * j ^ 6 + 4158216 * h ^ 6 * j ^ 2 + 33088152 * h ^ 7 * j + 5810568 * h ^ 8

/-- The homogeneous factor `U_3` (note §2). -/
noncomputable def nltUq3 (h j : ℝ) : ℝ :=
  211351608 * h ^ 3 * j ^ 5 + 243060870 * h ^ 4 * j ^ 4 + 66284136 * h ^ 5 * j ^ 3

/-- The homogeneous factor `V_3` (note §2). -/
noncomputable def nltVq3 (h j : ℝ) : ℝ :=
  33268941 * j ^ 8 + 219436440 * h * j ^ 7 + 98635824 * h ^ 2 * j ^ 6 + 22387392 * h ^ 6 * j ^ 2 + 14523420 * h ^ 7 * j + 1841121 * h ^ 8

/-- The homogeneous factor `U_4` (note §2). -/
noncomputable def nltUq4 (h j : ℝ) : ℝ :=
  12026112 * h ^ 2 * j ^ 6 + 80135784 * h ^ 3 * j ^ 5 + 56325060 * h ^ 4 * j ^ 4 + 6524256 * h ^ 5 * j ^ 3

/-- The homogeneous factor `V_4` (note §2). -/
noncomputable def nltVq4 (h j : ℝ) : ℝ :=
  57879090 * j ^ 8 + 69509280 * h * j ^ 7 + 8286948 * h ^ 6 * j ^ 2 + 3351084 * h ^ 7 * j + 322434 * h ^ 8

/-- The homogeneous factor `U_5` (note §2). -/
noncomputable def nltUq5 (h j : ℝ) : ℝ :=
  7060032 * h ^ 2 * j ^ 6 + 12264480 * h ^ 3 * j ^ 5 + 5765040 * h ^ 4 * j ^ 4

/-- The homogeneous factor `V_5` (note §2). -/
noncomputable def nltVq5 (h j : ℝ) : ℝ :=
  14133528 * j ^ 8 + 7481088 * h * j ^ 7 + 372096 * h ^ 5 * j ^ 3 + 1197072 * h ^ 6 * j ^ 2 + 340272 * h ^ 7 * j + 23256 * h ^ 8

/-- The factor `D_9` (note (11)). -/
noncomputable def nltDq9 (h : ℝ) : ℝ :=
  -93834660 + 42415740 * h + 64229940 * h ^ 2 - 4353180 * h ^ 3 - 8457840 * h ^ 4

/-- The factor `D_10` (note (11)). -/
noncomputable def nltDq10 (h : ℝ) : ℝ :=
  -26703996 + 18447000 * h + 10115028 * h ^ 2 - 1858032 * h ^ 3

/-- The factor `D_11` (note (11)). -/
noncomputable def nltDq11 (h : ℝ) : ℝ :=
  -2531232 + 2531232 * h

/-- The factored polynomial `𝓡` (note (13)). -/
noncomputable def nltRq (h j : ℝ) : ℝ :=
  500 * nltMq h j
    + nltEq h j
    + (h ^ 1 - (1 / 4) ^ 1) * nltUq1 h j
    + ((1 / 3) ^ 1 - h ^ 1) * nltVq1 h j
    + (h ^ 2 - (1 / 4) ^ 2) * nltUq2 h j
    + ((1 / 3) ^ 2 - h ^ 2) * nltVq2 h j
    + (h ^ 3 - (1 / 4) ^ 3) * nltUq3 h j
    + ((1 / 3) ^ 3 - h ^ 3) * nltVq3 h j
    + (h ^ 4 - (1 / 4) ^ 4) * nltUq4 h j
    + ((1 / 3) ^ 4 - h ^ 4) * nltVq4 h j
    + (h ^ 5 - (1 / 4) ^ 5) * nltUq5 h j
    + ((1 / 3) ^ 5 - h ^ 5) * nltVq5 h j
    + j ^ 9 * (nltDq9 h - (-79482001))
    + 79482001 * j ^ 8 * ((1 / 4) ^ 1 - j ^ 1)
    + j ^ 10 * (nltDq10 h - (-21528873))
    + 21528873 * j ^ 8 * ((1 / 4) ^ 2 - j ^ 2)
    + j ^ 11 * (nltDq11 h - (-1898424))
    + 1898424 * j ^ 8 * ((1 / 4) ^ 3 - j ^ 3)

/-- **The gap derivative** (note (14)): `∂_j P = 𝓡`. -/
theorem nlt_Pq_dj (h j : ℝ) : lrhHorner (nltDer (nltPqL h)) j = nltRq h j := by
  simp only [nltPqL, nltDer, nltDerAux, lrhHorner]
  unfold nltRq nltMq nltEq nltUq1 nltUq2 nltUq3 nltUq4 nltUq5 nltVq1 nltVq2 nltVq3 nltVq4 nltVq5 nltDq9 nltDq10 nltDq11
  ring

/-- `D_9 - ℓ_9` (note (12)). -/
noncomputable def nltDqb9 (h : ℝ) : ℝ := nltDq9 h - (-79482001)

/-- `nltDqb9 > 0` on `[1/4, 1/3]`. -/
theorem nltDqb9_pos {h : ℝ} (h1 : (1 / 4) ≤ h) (h2 : h ≤ (1 / 3)) : 0 < nltDqb9 h := by
  obtain ⟨z, rfl⟩ : ∃ z, h = (1 / 4) + z := ⟨h - (1 / 4), by ring⟩
  have z0 : 0 ≤ z := by linarith
  have z1 : z ≤ (1 / 12) := by linarith
  have p2 : z ^ 2 ≤ (1 / 12) * z ^ 1 := nlt_pw z0 z1 1
  have q2 : 0 ≤ z ^ 2 := pow_nonneg z0 2
  have p3 : z ^ 3 ≤ (1 / 12) * z ^ 2 := nlt_pw z0 z1 2
  have q3 : 0 ≤ z ^ 3 := pow_nonneg z0 3
  have p4 : z ^ 4 ≤ (1 / 12) * z ^ 3 := nlt_pw z0 z1 3
  have q4 : 0 ≤ z ^ 4 := pow_nonneg z0 4
  have e : nltDqb9 ((1 / 4) + z) = (1316723 / 8) + (292743495 / 4) * z + 57793365 * z ^ 2 - 12811020 * z ^ 3 - 8457840 * z ^ 4 := by unfold nltDqb9 nltDq9; ring
  rw [e]; linarith only [z0, z1, p2, q2, p3, q3, p4, q4]


/-- `D_10 - ℓ_10` (note (12)). -/
noncomputable def nltDqb10 (h : ℝ) : ℝ := nltDq10 h - (-21528873)

/-- `nltDqb10 > 0` on `[1/4, 1/3]`. -/
theorem nltDqb10_pos {h : ℝ} (h1 : (1 / 4) ≤ h) (h2 : h ≤ (1 / 3)) : 0 < nltDqb10 h := by
  obtain ⟨z, rfl⟩ : ∃ z, h = (1 / 4) + z := ⟨h - (1 / 4), by ring⟩
  have z0 : 0 ≤ z := by linarith
  have z1 : z ≤ (1 / 12) := by linarith
  have p2 : z ^ 2 ≤ (1 / 12) * z ^ 1 := nlt_pw z0 z1 1
  have q2 : 0 ≤ z ^ 2 := pow_nonneg z0 2
  have p3 : z ^ 3 ≤ (1 / 12) * z ^ 2 := nlt_pw z0 z1 2
  have q3 : 0 ≤ z ^ 3 := pow_nonneg z0 3
  have e : nltDqb10 ((1 / 4) + z) = (79569 / 2) + 23156133 * z + 8721504 * z ^ 2 - 1858032 * z ^ 3 := by unfold nltDqb10 nltDq10; ring
  rw [e]; linarith only [z0, z1, p2, q2, p3, q3]


/-- **The gap derivative bound** (note (15)): `𝓡 ≥ 500𝓜` on `[1/4, 1/3] × [0, 1/4]`; every other
summand of (13) is a product of factors of known sign. -/
theorem nlt_Rq_ge {h j : ℝ} (h1 : 1 / 4 ≤ h) (h2 : h ≤ 1 / 3) (j0 : 0 ≤ j) (j1 : j ≤ 1 / 4) :
    500 * nltMq h j ≤ nltRq h j := by
  have h0 : 0 ≤ h := by linarith
  have hE : 0 ≤ nltEq h j := by unfold nltEq; positivity
  have hU1 : 0 ≤ nltUq1 h j := by unfold nltUq1; positivity
  have hU2 : 0 ≤ nltUq2 h j := by unfold nltUq2; positivity
  have hU3 : 0 ≤ nltUq3 h j := by unfold nltUq3; positivity
  have hU4 : 0 ≤ nltUq4 h j := by unfold nltUq4; positivity
  have hU5 : 0 ≤ nltUq5 h j := by unfold nltUq5; positivity
  have hV1 : 0 ≤ nltVq1 h j := by unfold nltVq1; positivity
  have hV2 : 0 ≤ nltVq2 h j := by unfold nltVq2; positivity
  have hV3 : 0 ≤ nltVq3 h j := by unfold nltVq3; positivity
  have hV4 : 0 ≤ nltVq4 h j := by unfold nltVq4; positivity
  have hV5 : 0 ≤ nltVq5 h j := by unfold nltVq5; positivity
  have p : ∀ r : ℕ, (1 / 4 : ℝ) ^ r ≤ h ^ r := fun r => pow_le_pow_left₀ (by norm_num) h1 r
  have p' : ∀ r : ℕ, h ^ r ≤ (1 / 3 : ℝ) ^ r := fun r => pow_le_pow_left₀ h0 h2 r
  have q' : ∀ r : ℕ, j ^ r ≤ (1 / 4 : ℝ) ^ r := fun r => pow_le_pow_left₀ j0 j1 r
  have a1 := mul_nonneg (sub_nonneg.2 (p 1)) hU1
  have a2 := mul_nonneg (sub_nonneg.2 (p 2)) hU2
  have a3 := mul_nonneg (sub_nonneg.2 (p 3)) hU3
  have a4 := mul_nonneg (sub_nonneg.2 (p 4)) hU4
  have a5 := mul_nonneg (sub_nonneg.2 (p 5)) hU5
  have b1 := mul_nonneg (sub_nonneg.2 (p' 1)) hV1
  have b2 := mul_nonneg (sub_nonneg.2 (p' 2)) hV2
  have b3 := mul_nonneg (sub_nonneg.2 (p' 3)) hV3
  have b4 := mul_nonneg (sub_nonneg.2 (p' 4)) hV4
  have b5 := mul_nonneg (sub_nonneg.2 (p' 5)) hV5
  have d9 := (nltDqb9_pos h1 h2).le
  have d10 := (nltDqb10_pos h1 h2).le
  have d11 : 0 ≤ nltDq11 h - (-1898424) := by unfold nltDq11; linarith
  unfold nltDqb9 at d9
  unfold nltDqb10 at d10
  have e9 := mul_nonneg (pow_nonneg j0 9) d9
  have e10 := mul_nonneg (pow_nonneg j0 10) d10
  have e11 := mul_nonneg (pow_nonneg j0 11) d11
  have f9 := mul_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ 79482001) (pow_nonneg j0 8))
    (sub_nonneg.2 (q' 1))
  have f10 := mul_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ 21528873) (pow_nonneg j0 8))
    (sub_nonneg.2 (q' 2))
  have f11 := mul_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ 1898424) (pow_nonneg j0 8))
    (sub_nonneg.2 (q' 3))
  unfold nltRq
  linarith

/-- The coefficients in `h` of `𝓜`. -/
noncomputable def nltMqL (j : ℝ) : List ℝ :=
  [(-257 * j ^ 2 - 3836 * j ^ 3 - 26431 * j ^ 4 - 105439 * j ^ 5 - 256003 * j ^ 6 - 381694 * j ^ 7 - 336381 * j ^ 8 : ℝ), (-5 - 86 * j + 3422 * j ^ 2 + 44472 * j ^ 3 + 200524 * j ^ 4 + 442505 * j ^ 5 + 522510 * j ^ 6 + 455425 * j ^ 7 : ℝ), (221 + 248 * j - 11138 * j ^ 2 - 18104 * j ^ 3 + 129038 * j ^ 4 + 500497 * j ^ 5 + 484321 * j ^ 6 : ℝ), (195 - 8222 * j - 108100 * j ^ 2 - 416497 * j ^ 3 - 747741 * j ^ 4 - 1018180 * j ^ 5 : ℝ), (1890 + 10738 * j - 34503 * j ^ 2 - 254988 * j ^ 3 - 358391 * j ^ 4 : ℝ), (7539 + 82723 * j + 320192 * j ^ 2 + 926841 * j ^ 3 : ℝ), (8268 + 104683 * j + 517202 * j ^ 2 : ℝ), (-4907 - 13039 * j : ℝ), (-28629 : ℝ)]

theorem nlt_Mq_h (h j : ℝ) : nltMq h j = lrhHorner (nltMqL j) h := by
  simp only [nltMqL, lrhHorner]; unfold nltMq; ring

/-- `A_0(v)` of the auxiliary note (5). -/
noncomputable def nltAq0 (v : ℝ) : ℝ :=
  (1775673 / 4096) + (5629039 / 16384) * v - (3913717 / 4096) * v ^ 2 - (10369939 / 16384) * v ^ 3 + (819537 / 2048) * v ^ 4 + (2007379 / 4096) * v ^ 5 + (1529341 / 8192) * v ^ 6 + (455425 / 16384) * v ^ 7

/-- `A_1(v)` of the auxiliary note (5). -/
noncomputable def nltAq1 (v : ℝ) : ℝ :=
  (1250347 / 1024) + (17305689 / 8192) * v - (3176553 / 4096) * v ^ 2 - (9000907 / 4096) * v ^ 3 - (4529315 / 4096) * v ^ 4 - (131569 / 1024) * v ^ 5 + (484321 / 8192) * v ^ 6

/-- `A_2(v)` of the auxiliary note (5). -/
noncomputable def nltAq2 (v : ℝ) : ℝ :=
  (5486667 / 4096) + (65394153 / 16384) * v + (5259423 / 2048) * v ^ 2 - (2213025 / 8192) * v ^ 3 - (829599 / 1024) * v ^ 4 - (763635 / 4096) * v ^ 5

/-- `A_3(v)` of the auxiliary note (5). -/
noncomputable def nltAq3 (v : ℝ) : ℝ :=
  (1094815 / 2048) + (13129687 / 4096) * v + (6804911 / 2048) * v ^ 2 + (3614253 / 4096) * v ^ 3 - (358391 / 4096) * v ^ 4

/-- `A_4(v)` of the auxiliary note (5). -/
noncomputable def nltAq4 (v : ℝ) : ℝ :=
  -(923985 / 4096) + (17810705 / 16384) * v + (5479975 / 4096) * v ^ 2 + (4634205 / 16384) * v ^ 3

/-- `A_5(v)` of the auxiliary note (5). -/
noncomputable def nltAq5 (v : ℝ) : ℝ :=
  -(37815 / 128) + (982377 / 8192) * v + (775803 / 4096) * v ^ 2

/-- `A_6(v)` of the auxiliary note (5). -/
noncomputable def nltAq6 (v : ℝ) : ℝ :=
  -(435155 / 4096) - (91273 / 16384) * v

/-- `A_7(v)` of the auxiliary note (5). -/
noncomputable def nltAq7 (_v : ℝ) : ℝ :=
  -(28629 / 2048)

/-- The auxiliary derivative identity (5): `∂_h𝓜 = ∑ Aᵢ(4j)(4h - 1)ⁱ`. -/
theorem nlt_Mq_dh (h j : ℝ) : lrhHorner (nltDer (nltMqL j)) h =
    nltAq0 (4 * j) * (4 * h - 1) ^ 0 + nltAq1 (4 * j) * (4 * h - 1) ^ 1 + nltAq2 (4 * j) * (4 * h - 1) ^ 2 + nltAq3 (4 * j) * (4 * h - 1) ^ 3 + nltAq4 (4 * j) * (4 * h - 1) ^ 4 + nltAq5 (4 * j) * (4 * h - 1) ^ 5 + nltAq6 (4 * j) * (4 * h - 1) ^ 6 + nltAq7 (4 * j) * (4 * h - 1) ^ 7 := by
  simp only [nltMqL, nltDer, nltDerAux, lrhHorner]
  unfold nltAq0 nltAq1 nltAq2 nltAq3 nltAq4 nltAq5 nltAq6 nltAq7
  ring

/-- A bound of the auxiliary note §1. -/
noncomputable def nltAqb0 (v : ℝ) : ℝ := nltAq0 v

/-- `nltAqb0 > 140` on `[0, 1]`. -/
theorem nltAqb0_pos {v : ℝ} (h1 : 0 ≤ v) (h2 : v ≤ 1) : 140 < nltAqb0 v := by
  rcases le_total v (1 / 2) with hm | hm
  · obtain ⟨z, rfl⟩ : ∃ z, v = 0 + z := ⟨v - 0, by ring⟩
    have z0 : 0 ≤ z := by linarith
    have z1 : z ≤ (1 / 2) := by linarith
    have p2 : z ^ 2 ≤ (1 / 2) * z ^ 1 := nlt_pw z0 z1 1
    have q2 : 0 ≤ z ^ 2 := pow_nonneg z0 2
    have p3 : z ^ 3 ≤ (1 / 2) * z ^ 2 := nlt_pw z0 z1 2
    have q3 : 0 ≤ z ^ 3 := pow_nonneg z0 3
    have p4 : z ^ 4 ≤ (1 / 2) * z ^ 3 := nlt_pw z0 z1 3
    have q4 : 0 ≤ z ^ 4 := pow_nonneg z0 4
    have p5 : z ^ 5 ≤ (1 / 2) * z ^ 4 := nlt_pw z0 z1 4
    have q5 : 0 ≤ z ^ 5 := pow_nonneg z0 5
    have p6 : z ^ 6 ≤ (1 / 2) * z ^ 5 := nlt_pw z0 z1 5
    have q6 : 0 ≤ z ^ 6 := pow_nonneg z0 6
    have p7 : z ^ 7 ≤ (1 / 2) * z ^ 6 := nlt_pw z0 z1 6
    have q7 : 0 ≤ z ^ 7 := pow_nonneg z0 7
    have e : nltAqb0 (0 + z) = (1775673 / 4096) + (5629039 / 16384) * z - (3913717 / 4096) * z ^ 2 - (10369939 / 16384) * z ^ 3 + (819537 / 2048) * z ^ 4 + (2007379 / 4096) * z ^ 5 + (1529341 / 8192) * z ^ 6 + (455425 / 16384) * z ^ 7 := by unfold nltAqb0 nltAq0; ring
    rw [e]; linarith only [z0, z1, p2, q2, p3, q3, p4, q4, p5, q5, p6, q6, p7, q7]
  · rcases le_total v (3 / 4) with hm | hm
    · obtain ⟨z, rfl⟩ : ∃ z, v = (3 / 4) - z := ⟨(3 / 4) - v, by ring⟩
      have z0 : 0 ≤ z := by linarith
      have z1 : z ≤ (1 / 4) := by linarith
      have p2 : z ^ 2 ≤ (1 / 4) * z ^ 1 := nlt_pw z0 z1 1
      have q2 : 0 ≤ z ^ 2 := pow_nonneg z0 2
      have p3 : z ^ 3 ≤ (1 / 4) * z ^ 2 := nlt_pw z0 z1 2
      have q3 : 0 ≤ z ^ 3 := pow_nonneg z0 3
      have p4 : z ^ 4 ≤ (1 / 4) * z ^ 3 := nlt_pw z0 z1 3
      have q4 : 0 ≤ z ^ 4 := pow_nonneg z0 4
      have p5 : z ^ 5 ≤ (1 / 4) * z ^ 4 := nlt_pw z0 z1 4
      have q5 : 0 ≤ z ^ 5 := pow_nonneg z0 5
      have p6 : z ^ 6 ≤ (1 / 4) * z ^ 5 := nlt_pw z0 z1 5
      have q6 : 0 ≤ z ^ 6 := pow_nonneg z0 6
      have p7 : z ^ 7 ≤ (1 / 4) * z ^ 6 := nlt_pw z0 z1 6
      have q7 : 0 ≤ z ^ 7 := pow_nonneg z0 7
      have e : nltAqb0 ((3 / 4) - z) = (44709582963 / 268435456) + (27293334785 / 67108864) * z + (34612372103 / 16777216) * z ^ 2 - (21840916979 / 4194304) * z ^ 3 + (4428751689 / 1048576) * z ^ 4 - (434772685 / 262144) * z ^ 5 + (21798653 / 65536) * z ^ 6 - (455425 / 16384) * z ^ 7 := by unfold nltAqb0 nltAq0; ring
      rw [e]; linarith only [z0, z1, p2, q2, p3, q3, p4, q4, p5, q5, p6, q6, p7, q7]
    · rcases le_total v (7 / 8) with hm | hm
      · rcases le_total v (13 / 16) with hm | hm
        · obtain ⟨z, rfl⟩ : ∃ z, v = (3 / 4) + z := ⟨v - (3 / 4), by ring⟩
          have z0 : 0 ≤ z := by linarith
          have z1 : z ≤ (1 / 16) := by linarith
          have p2 : z ^ 2 ≤ (1 / 16) * z ^ 1 := nlt_pw z0 z1 1
          have q2 : 0 ≤ z ^ 2 := pow_nonneg z0 2
          have p3 : z ^ 3 ≤ (1 / 16) * z ^ 2 := nlt_pw z0 z1 2
          have q3 : 0 ≤ z ^ 3 := pow_nonneg z0 3
          have p4 : z ^ 4 ≤ (1 / 16) * z ^ 3 := nlt_pw z0 z1 3
          have q4 : 0 ≤ z ^ 4 := pow_nonneg z0 4
          have p5 : z ^ 5 ≤ (1 / 16) * z ^ 4 := nlt_pw z0 z1 4
          have q5 : 0 ≤ z ^ 5 := pow_nonneg z0 5
          have p6 : z ^ 6 ≤ (1 / 16) * z ^ 5 := nlt_pw z0 z1 5
          have q6 : 0 ≤ z ^ 6 := pow_nonneg z0 6
          have p7 : z ^ 7 ≤ (1 / 16) * z ^ 6 := nlt_pw z0 z1 6
          have q7 : 0 ≤ z ^ 7 := pow_nonneg z0 7
          have e : nltAqb0 ((3 / 4) + z) = (44709582963 / 268435456) - (27293334785 / 67108864) * z + (34612372103 / 16777216) * z ^ 2 + (21840916979 / 4194304) * z ^ 3 + (4428751689 / 1048576) * z ^ 4 + (434772685 / 262144) * z ^ 5 + (21798653 / 65536) * z ^ 6 + (455425 / 16384) * z ^ 7 := by unfold nltAqb0 nltAq0; ring
          rw [e]; linarith only [z0, z1, p2, q2, p3, q3, p4, q4, p5, q5, p6, q6, p7, q7]
        · obtain ⟨z, rfl⟩ : ∃ z, v = (13 / 16) + z := ⟨v - (13 / 16), by ring⟩
          have z0 : 0 ≤ z := by linarith
          have z1 : z ≤ (1 / 16) := by linarith
          have p2 : z ^ 2 ≤ (1 / 16) * z ^ 1 := nlt_pw z0 z1 1
          have q2 : 0 ≤ z ^ 2 := pow_nonneg z0 2
          have p3 : z ^ 3 ≤ (1 / 16) * z ^ 2 := nlt_pw z0 z1 2
          have q3 : 0 ≤ z ^ 3 := pow_nonneg z0 3
          have p4 : z ^ 4 ≤ (1 / 16) * z ^ 3 := nlt_pw z0 z1 3
          have q4 : 0 ≤ z ^ 4 := pow_nonneg z0 4
          have p5 : z ^ 5 ≤ (1 / 16) * z ^ 4 := nlt_pw z0 z1 4
          have q5 : 0 ≤ z ^ 5 := pow_nonneg z0 5
          have p6 : z ^ 6 ≤ (1 / 16) * z ^ 5 := nlt_pw z0 z1 5
          have q6 : 0 ≤ z ^ 6 := pow_nonneg z0 6
          have p7 : z ^ 7 ≤ (1 / 16) * z ^ 6 := nlt_pw z0 z1 6
          have q7 : 0 ≤ z ^ 7 := pow_nonneg z0 7
          have e : nltAqb0 ((13 / 16) + z) = (662053135887621 / 4398046511104) - (22964468369713 / 274877906944) * z + (53988415034625 / 17179869184) * z ^ 2 + (6796358640723 / 1073741824) * z ^ 3 + (319545781951 / 67108864) * z ^ 4 + (7489094557 / 4194304) * z ^ 5 + (90382587 / 262144) * z ^ 6 + (455425 / 16384) * z ^ 7 := by unfold nltAqb0 nltAq0; ring
          rw [e]; linarith only [z0, z1, p2, q2, p3, q3, p4, q4, p5, q5, p6, q6, p7, q7]
      · obtain ⟨z, rfl⟩ : ∃ z, v = (7 / 8) + z := ⟨v - (7 / 8), by ring⟩
        have z0 : 0 ≤ z := by linarith
        have z1 : z ≤ (1 / 8) := by linarith
        have p2 : z ^ 2 ≤ (1 / 8) * z ^ 1 := nlt_pw z0 z1 1
        have q2 : 0 ≤ z ^ 2 := pow_nonneg z0 2
        have p3 : z ^ 3 ≤ (1 / 8) * z ^ 2 := nlt_pw z0 z1 2
        have q3 : 0 ≤ z ^ 3 := pow_nonneg z0 3
        have p4 : z ^ 4 ≤ (1 / 8) * z ^ 3 := nlt_pw z0 z1 3
        have q4 : 0 ≤ z ^ 4 := pow_nonneg z0 4
        have p5 : z ^ 5 ≤ (1 / 8) * z ^ 4 := nlt_pw z0 z1 4
        have q5 : 0 ≤ z ^ 5 := pow_nonneg z0 5
        have p6 : z ^ 6 ≤ (1 / 8) * z ^ 5 := nlt_pw z0 z1 5
        have q6 : 0 ≤ z ^ 6 := pow_nonneg z0 6
        have p7 : z ^ 7 ≤ (1 / 8) * z ^ 6 := nlt_pw z0 z1 6
        have q7 : 0 ≤ z ^ 7 := pow_nonneg z0 7
        have e : nltAqb0 ((7 / 8) + z) = (5470316928967 / 34359738368) + (1667462682903 / 4294967296) * z + (2386594434275 / 536870912) * z ^ 2 + (509453519107 / 67108864) * z ^ 3 + (44795366677 / 8388608) * z ^ 4 + (2010238501 / 1048576) * z ^ 5 + (46785281 / 131072) * z ^ 6 + (455425 / 16384) * z ^ 7 := by unfold nltAqb0 nltAq0; ring
        rw [e]; linarith only [z0, z1, p2, q2, p3, q3, p4, q4, p5, q5, p6, q6, p7, q7]


/-- A bound of the auxiliary note §1. -/
noncomputable def nltAqb1 (v : ℝ) : ℝ := nltAq1 v

/-- `nltAqb1 > -816` on `[0, 1]`. -/
theorem nltAqb1_pos {v : ℝ} (h1 : 0 ≤ v) (h2 : v ≤ 1) : (-816) < nltAqb1 v := by
  rcases le_total v (1 / 2) with hm | hm
  · obtain ⟨z, rfl⟩ : ∃ z, v = 0 + z := ⟨v - 0, by ring⟩
    have z0 : 0 ≤ z := by linarith
    have z1 : z ≤ (1 / 2) := by linarith
    have p2 : z ^ 2 ≤ (1 / 2) * z ^ 1 := nlt_pw z0 z1 1
    have q2 : 0 ≤ z ^ 2 := pow_nonneg z0 2
    have p3 : z ^ 3 ≤ (1 / 2) * z ^ 2 := nlt_pw z0 z1 2
    have q3 : 0 ≤ z ^ 3 := pow_nonneg z0 3
    have p4 : z ^ 4 ≤ (1 / 2) * z ^ 3 := nlt_pw z0 z1 3
    have q4 : 0 ≤ z ^ 4 := pow_nonneg z0 4
    have p5 : z ^ 5 ≤ (1 / 2) * z ^ 4 := nlt_pw z0 z1 4
    have q5 : 0 ≤ z ^ 5 := pow_nonneg z0 5
    have p6 : z ^ 6 ≤ (1 / 2) * z ^ 5 := nlt_pw z0 z1 5
    have q6 : 0 ≤ z ^ 6 := pow_nonneg z0 6
    have e : nltAqb1 (0 + z) = (1250347 / 1024) + (17305689 / 8192) * z - (3176553 / 4096) * z ^ 2 - (9000907 / 4096) * z ^ 3 - (4529315 / 4096) * z ^ 4 - (131569 / 1024) * z ^ 5 + (484321 / 8192) * z ^ 6 := by unfold nltAqb1 nltAq1; ring
    rw [e]; linarith only [z0, z1, p2, q2, p3, q3, p4, q4, p5, q5, p6, q6]
  · obtain ⟨z, rfl⟩ : ∃ z, v = 1 - z := ⟨1 - v, by ring⟩
    have z0 : 0 ≤ z := by linarith
    have z1 : z ≤ (1 / 2) := by linarith
    have p2 : z ^ 2 ≤ (1 / 2) * z ^ 1 := nlt_pw z0 z1 1
    have q2 : 0 ≤ z ^ 2 := pow_nonneg z0 2
    have p3 : z ^ 3 ≤ (1 / 2) * z ^ 2 := nlt_pw z0 z1 2
    have q3 : 0 ≤ z ^ 3 := pow_nonneg z0 3
    have p4 : z ^ 4 ≤ (1 / 2) * z ^ 3 := nlt_pw z0 z1 3
    have q4 : 0 ≤ z ^ 4 := pow_nonneg z0 4
    have p5 : z ^ 5 ≤ (1 / 2) * z ^ 4 := nlt_pw z0 z1 4
    have q5 : 0 ≤ z ^ 5 := pow_nonneg z0 5
    have p6 : z ^ 6 ≤ (1 / 2) * z ^ 5 := nlt_pw z0 z1 5
    have q6 : 0 ≤ z ^ 6 := pow_nonneg z0 6
    have e : nltAqb1 (1 - z) = -(1668329 / 2048) + (87997319 / 8192) * z - (117971033 / 8192) * z ^ 2 + (27537717 / 4096) * z ^ 3 - (7056575 / 8192) * z ^ 4 - (926687 / 4096) * z ^ 5 + (484321 / 8192) * z ^ 6 := by unfold nltAqb1 nltAq1; ring
    rw [e]; linarith only [z0, z1, p2, q2, p3, q3, p4, q4, p5, q5, p6, q6]


/-- A bound of the auxiliary note §1. -/
noncomputable def nltAqb2 (v : ℝ) : ℝ := nltAq2 v

/-- `nltAqb2 > 1338` on `[0, 1]`. -/
theorem nltAqb2_pos {v : ℝ} (h1 : 0 ≤ v) (h2 : v ≤ 1) : 1338 < nltAqb2 v := by
  obtain ⟨z, rfl⟩ : ∃ z, v = 0 + z := ⟨v - 0, by ring⟩
  have z0 : 0 ≤ z := by linarith
  have z1 : z ≤ 1 := by linarith
  have p2 : z ^ 2 ≤ 1 * z ^ 1 := nlt_pw z0 z1 1
  have q2 : 0 ≤ z ^ 2 := pow_nonneg z0 2
  have p3 : z ^ 3 ≤ 1 * z ^ 2 := nlt_pw z0 z1 2
  have q3 : 0 ≤ z ^ 3 := pow_nonneg z0 3
  have p4 : z ^ 4 ≤ 1 * z ^ 3 := nlt_pw z0 z1 3
  have q4 : 0 ≤ z ^ 4 := pow_nonneg z0 4
  have p5 : z ^ 5 ≤ 1 * z ^ 4 := nlt_pw z0 z1 4
  have q5 : 0 ≤ z ^ 5 := pow_nonneg z0 5
  have e : nltAqb2 (0 + z) = (5486667 / 4096) + (65394153 / 16384) * z + (5259423 / 2048) * z ^ 2 - (2213025 / 8192) * z ^ 3 - (829599 / 1024) * z ^ 4 - (763635 / 4096) * z ^ 5 := by unfold nltAqb2 nltAq2; ring
  rw [e]; linarith only [z0, z1, p2, q2, p3, q3, p4, q4, p5, q5]


/-- A bound of the auxiliary note §1. -/
noncomputable def nltAqb3 (v : ℝ) : ℝ := nltAq3 v

/-- `nltAqb3 > 0` on `[0, 1]`. -/
theorem nltAqb3_pos {v : ℝ} (h1 : 0 ≤ v) (h2 : v ≤ 1) : 0 < nltAqb3 v := by
  obtain ⟨z, rfl⟩ : ∃ z, v = 0 + z := ⟨v - 0, by ring⟩
  have z0 : 0 ≤ z := by linarith
  have z1 : z ≤ 1 := by linarith
  have p2 : z ^ 2 ≤ 1 * z ^ 1 := nlt_pw z0 z1 1
  have q2 : 0 ≤ z ^ 2 := pow_nonneg z0 2
  have p3 : z ^ 3 ≤ 1 * z ^ 2 := nlt_pw z0 z1 2
  have q3 : 0 ≤ z ^ 3 := pow_nonneg z0 3
  have p4 : z ^ 4 ≤ 1 * z ^ 3 := nlt_pw z0 z1 3
  have q4 : 0 ≤ z ^ 4 := pow_nonneg z0 4
  have e : nltAqb3 (0 + z) = (1094815 / 2048) + (13129687 / 4096) * z + (6804911 / 2048) * z ^ 2 + (3614253 / 4096) * z ^ 3 - (358391 / 4096) * z ^ 4 := by unfold nltAqb3 nltAq3; ring
  rw [e]; linarith only [z0, z1, p2, q2, p3, q3, p4, q4]


/-- A bound of the auxiliary note §1. -/
noncomputable def nltAqb4 (v : ℝ) : ℝ := nltAq4 v

/-- `nltAqb4 > -226` on `[0, 1]`. -/
theorem nltAqb4_pos {v : ℝ} (h1 : 0 ≤ v) (h2 : v ≤ 1) : (-226) < nltAqb4 v := by
  obtain ⟨z, rfl⟩ : ∃ z, v = 0 + z := ⟨v - 0, by ring⟩
  have z0 : 0 ≤ z := by linarith
  have z1 : z ≤ 1 := by linarith
  have p2 : z ^ 2 ≤ 1 * z ^ 1 := nlt_pw z0 z1 1
  have q2 : 0 ≤ z ^ 2 := pow_nonneg z0 2
  have p3 : z ^ 3 ≤ 1 * z ^ 2 := nlt_pw z0 z1 2
  have q3 : 0 ≤ z ^ 3 := pow_nonneg z0 3
  have e : nltAqb4 (0 + z) = -(923985 / 4096) + (17810705 / 16384) * z + (5479975 / 4096) * z ^ 2 + (4634205 / 16384) * z ^ 3 := by unfold nltAqb4 nltAq4; ring
  rw [e]; linarith only [z0, z1, p2, q2, p3, q3]


/-- A bound of the auxiliary note §1. -/
noncomputable def nltAqb5 (v : ℝ) : ℝ := nltAq5 v

/-- `nltAqb5 > -296` on `[0, 1]`. -/
theorem nltAqb5_pos {v : ℝ} (h1 : 0 ≤ v) (h2 : v ≤ 1) : (-296) < nltAqb5 v := by
  obtain ⟨z, rfl⟩ : ∃ z, v = 0 + z := ⟨v - 0, by ring⟩
  have z0 : 0 ≤ z := by linarith
  have z1 : z ≤ 1 := by linarith
  have p2 : z ^ 2 ≤ 1 * z ^ 1 := nlt_pw z0 z1 1
  have q2 : 0 ≤ z ^ 2 := pow_nonneg z0 2
  have e : nltAqb5 (0 + z) = -(37815 / 128) + (982377 / 8192) * z + (775803 / 4096) * z ^ 2 := by unfold nltAqb5 nltAq5; ring
  rw [e]; linarith only [z0, z1, p2, q2]


/-- A bound of the auxiliary note §1. -/
noncomputable def nltAqb6 (v : ℝ) : ℝ := nltAq6 v

/-- `nltAqb6 > -112` on `[0, 1]`. -/
theorem nltAqb6_pos {v : ℝ} (h1 : 0 ≤ v) (h2 : v ≤ 1) : (-112) < nltAqb6 v := by
  obtain ⟨z, rfl⟩ : ∃ z, v = 0 + z := ⟨v - 0, by ring⟩
  have z0 : 0 ≤ z := by linarith
  have z1 : z ≤ 1 := by linarith
  have e : nltAqb6 (0 + z) = -(435155 / 4096) - (91273 / 16384) * z := by unfold nltAqb6 nltAq6; ring
  rw [e]; linarith only [z0, z1]


/-- A bound of the auxiliary note §1. -/
noncomputable def nltAqb7 (v : ℝ) : ℝ := nltAq7 v

/-- `nltAqb7 > -14` on `[0, 1]`. -/
theorem nltAqb7_pos {v : ℝ} (h1 : 0 ≤ v) (h2 : v ≤ 1) : (-14) < nltAqb7 v := by
  obtain ⟨z, rfl⟩ : ∃ z, v = 0 + z := ⟨v - 0, by ring⟩
  have z0 : 0 ≤ z := by linarith
  have z1 : z ≤ 1 := by linarith
  have e : nltAqb7 (0 + z) = -(28629 / 2048) := by unfold nltAqb7 nltAq7; ring
  rw [e]; linarith only [z0, z1]


/-- The combined lower polynomial of the auxiliary note (11). -/
noncomputable def nltMqK (u : ℝ) : ℝ := 140 - 816 * u + 1338 * u ^ 2 - 226 * u ^ 4 - 296 * u ^ 5 - 112 * u ^ 6 - 14 * u ^ 7

/-- `nltMqK > 0` on `[0, 1/3]`. -/
theorem nltMqK_pos {u : ℝ} (h1 : 0 ≤ u) (h2 : u ≤ (1 / 3)) : 0 < nltMqK u := by
  obtain ⟨z, rfl⟩ : ∃ z, u = (1 / 3) - z := ⟨(1 / 3) - u, by ring⟩
  have z0 : 0 ≤ z := by linarith
  have z1 : z ≤ (1 / 3) := by linarith
  have p2 : z ^ 2 ≤ (1 / 3) * z ^ 1 := nlt_pw z0 z1 1
  have q2 : 0 ≤ z ^ 2 := pow_nonneg z0 2
  have p3 : z ^ 3 ≤ (1 / 3) * z ^ 2 := nlt_pw z0 z1 2
  have q3 : 0 ≤ z ^ 3 := pow_nonneg z0 3
  have p4 : z ^ 4 ≤ (1 / 3) * z ^ 3 := nlt_pw z0 z1 3
  have q4 : 0 ≤ z ^ 4 := pow_nonneg z0 4
  have p5 : z ^ 5 ≤ (1 / 3) * z ^ 4 := nlt_pw z0 z1 4
  have q5 : 0 ≤ z ^ 5 := pow_nonneg z0 5
  have p6 : z ^ 6 ≤ (1 / 3) * z ^ 5 := nlt_pw z0 z1 5
  have q6 : 0 ≤ z ^ 6 := pow_nonneg z0 6
  have p7 : z ^ 7 ≤ (1 / 3) * z ^ 6 := nlt_pw z0 z1 6
  have q7 : 0 ≤ z ^ 7 := pow_nonneg z0 7
  have e : nltMqK ((1 / 3) - z) = (27334 / 2187) - (15562 / 729) * z + (85516 / 81) * z ^ 2 + (58258 / 81) * z ^ 3 - (24952 / 27) * z ^ 4 + (1658 / 3) * z ^ 5 - (434 / 3) * z ^ 6 + 14 * z ^ 7 := by unfold nltMqK; ring
  rw [e]; linarith only [z0, z1, p2, q2, p3, q3, p4, q4, p5, q5, p6, q6, p7, q7]


/-- `F(v) = 65536𝓜(1/4, v/4)` (auxiliary note (12)-(13)). -/
noncomputable def nltMqF (v : ℝ) : ℝ := 2073343 + 213357 * v - 6072350 * v ^ 2 - 458951 * v ^ 3 + 4782453 * v ^ 4 + 1315792 * v ^ 5 - 1521687 * v ^ 6 - 1071351 * v ^ 7 - 336381 * v ^ 8

/-- `nltMqF > 0` on `[2/15, 3/4]`. -/
theorem nltMqF_pos {v : ℝ} (h1 : (2 / 15) ≤ v) (h2 : v ≤ (3 / 4)) : 0 < nltMqF v := by
  obtain ⟨z, rfl⟩ : ∃ z, v = (3 / 4) - z := ⟨(3 / 4) - v, by ring⟩
  have z0 : 0 ≤ z := by linarith
  have z1 : z ≤ (37 / 60) := by linarith
  have p2 : z ^ 2 ≤ (37 / 60) * z ^ 1 := nlt_pw z0 z1 1
  have q2 : 0 ≤ z ^ 2 := pow_nonneg z0 2
  have p3 : z ^ 3 ≤ (37 / 60) * z ^ 2 := nlt_pw z0 z1 2
  have q3 : 0 ≤ z ^ 3 := pow_nonneg z0 3
  have p4 : z ^ 4 ≤ (37 / 60) * z ^ 3 := nlt_pw z0 z1 3
  have q4 : 0 ≤ z ^ 4 := pow_nonneg z0 4
  have p5 : z ^ 5 ≤ (37 / 60) * z ^ 4 := nlt_pw z0 z1 4
  have q5 : 0 ≤ z ^ 5 := pow_nonneg z0 5
  have p6 : z ^ 6 ≤ (37 / 60) * z ^ 5 := nlt_pw z0 z1 5
  have q6 : 0 ≤ z ^ 6 := pow_nonneg z0 6
  have p7 : z ^ 7 ≤ (37 / 60) * z ^ 6 := nlt_pw z0 z1 6
  have q7 : 0 ≤ z ^ 7 := pow_nonneg z0 7
  have p8 : z ^ 8 ≤ (37 / 60) * z ^ 7 := nlt_pw z0 z1 7
  have q8 : 0 ≤ z ^ 8 := pow_nonneg z0 8
  have e : nltMqF ((3 / 4) - z) = (129353599 / 65536) + (13837143375 / 4096) * z + (22363393 / 64) * z ^ 2 + (2018319239 / 256) * z ^ 3 - (3378181341 / 128) * z ^ 4 + (418146149 / 16) * z ^ 5 - (24888561 / 2) * z ^ 6 + 3089637 * z ^ 7 - 336381 * z ^ 8 := by unfold nltMqF; ring
  rw [e]; linarith only [z0, z1, p2, q2, p3, q3, p4, q4, p5, q5, p6, q6, p7, q7, p8, q8]


/-- `T(h)` with `65536𝓜(h, 3h/4) = hT(h)` (auxiliary note (17)-(18)). -/
noncomputable def nltMqT (h : ℝ) : ℝ := -327680 + 782336 * h + 45060096 * h ^ 2 - 9367296 * h ^ 3 - 945389376 * h ^ 4 - 1607824368 * h ^ 5 + 4611512824 * h ^ 6 + 26334162591 * h ^ 7

/-- `nltMqT > 0` on `[1/4, 1/3]`. -/
theorem nltMqT_pos {h : ℝ} (h1 : (1 / 4) ≤ h) (h2 : h ≤ (1 / 3)) : 0 < nltMqT h := by
  obtain ⟨z, rfl⟩ : ∃ z, h = (1 / 4) + z := ⟨h - (1 / 4), by ring⟩
  have z0 : 0 ≤ z := by linarith
  have z1 : z ≤ (1 / 12) := by linarith
  have p2 : z ^ 2 ≤ (1 / 12) * z ^ 1 := nlt_pw z0 z1 1
  have q2 : 0 ≤ z ^ 2 := pow_nonneg z0 2
  have p3 : z ^ 3 ≤ (1 / 12) * z ^ 2 := nlt_pw z0 z1 2
  have q3 : 0 ≤ z ^ 3 := pow_nonneg z0 3
  have p4 : z ^ 4 ≤ (1 / 12) * z ^ 3 := nlt_pw z0 z1 3
  have q4 : 0 ≤ z ^ 4 := pow_nonneg z0 4
  have p5 : z ^ 5 ≤ (1 / 12) * z ^ 4 := nlt_pw z0 z1 4
  have q5 : 0 ≤ z ^ 5 := pow_nonneg z0 5
  have p6 : z ^ 6 ≤ (1 / 12) * z ^ 5 := nlt_pw z0 z1 5
  have q6 : 0 ≤ z ^ 6 := pow_nonneg z0 6
  have p7 : z ^ 7 ≤ (1 / 12) * z ^ 6 := nlt_pw z0 z1 6
  have q7 : 0 ≤ z ^ 7 := pow_nonneg z0 7
  have e : nltMqT ((1 / 4) + z) = (129353599 / 16384) + (12663257753 / 4096) * z + (248374219563 / 1024) * z ^ 2 + (788947109693 / 256) * z ^ 3 + (1009255590621 / 64) * z ^ 4 + (637968532299 / 16) * z ^ 5 + (202785189433 / 4) * z ^ 6 + 26334162591 * z ^ 7 := by unfold nltMqT; ring
  rw [e]; linarith only [z0, z1, p2, q2, p3, q3, p4, q4, p5, q5, p6, q6, p7, q7]


/-- `P(h, 1/30)`. -/
noncomputable def nltPq30 (h : ℝ) : ℝ :=
  -(50606609017731059 / 22143375000000000) - (1663456257809172061 / 22143375000000000) * h + (113651532055800193 / 30754687500000) * h ^ 2 - (1385635615253177929 / 61509375000000) * h ^ 3 - (5563875353943587 / 1366875000000) * h ^ 4 + (7891487292263033 / 34171875000) * h ^ 5 + (24135046988069 / 84375000) * h ^ 6 - (49622776152083 / 75937500) * h ^ 7 - (1067345198659 / 506250) * h ^ 8 - (423843119963 / 168750) * h ^ 9 - (9184244566 / 5625) * h ^ 10 - (77015024 / 125) * h ^ 11 - (3245596 / 25) * h ^ 12 - (62016 / 5) * h ^ 13

theorem nlt_Pq30_eq (h : ℝ) : lrhHorner (nltPqL h) (1 / 30) = nltPq30 h := by
  simp only [nltPqL, lrhHorner]; unfold nltPq30; ring

/-- `P(h, 1/30) > 39` (auxiliary note (2)). -/
theorem nlt_Pq30_gt {h : ℝ} (h1 : (1 / 4) ≤ h) (h2 : h ≤ (1 / 3)) : 39 < nltPq30 h := by
  obtain ⟨z, rfl⟩ : ∃ z, h = (1 / 4) + z := ⟨h - (1 / 4), by ring⟩
  have z0 : 0 ≤ z := by linarith
  have z1 : z ≤ (1 / 12) := by linarith
  have p2 : z ^ 2 ≤ (1 / 12) * z ^ 1 := nlt_pw z0 z1 1
  have q2 : 0 ≤ z ^ 2 := pow_nonneg z0 2
  have p3 : z ^ 3 ≤ (1 / 12) * z ^ 2 := nlt_pw z0 z1 2
  have q3 : 0 ≤ z ^ 3 := pow_nonneg z0 3
  have p4 : z ^ 4 ≤ (1 / 12) * z ^ 3 := nlt_pw z0 z1 3
  have q4 : 0 ≤ z ^ 4 := pow_nonneg z0 4
  have p5 : z ^ 5 ≤ (1 / 12) * z ^ 4 := nlt_pw z0 z1 4
  have q5 : 0 ≤ z ^ 5 := pow_nonneg z0 5
  have p6 : z ^ 6 ≤ (1 / 12) * z ^ 5 := nlt_pw z0 z1 5
  have q6 : 0 ≤ z ^ 6 := pow_nonneg z0 6
  have p7 : z ^ 7 ≤ (1 / 12) * z ^ 6 := nlt_pw z0 z1 6
  have q7 : 0 ≤ z ^ 7 := pow_nonneg z0 7
  have p8 : z ^ 8 ≤ (1 / 12) * z ^ 7 := nlt_pw z0 z1 7
  have q8 : 0 ≤ z ^ 8 := pow_nonneg z0 8
  have p9 : z ^ 9 ≤ (1 / 12) * z ^ 8 := nlt_pw z0 z1 8
  have q9 : 0 ≤ z ^ 9 := pow_nonneg z0 9
  have p10 : z ^ 10 ≤ (1 / 12) * z ^ 9 := nlt_pw z0 z1 9
  have q10 : 0 ≤ z ^ 10 := pow_nonneg z0 10
  have p11 : z ^ 11 ≤ (1 / 12) * z ^ 10 := nlt_pw z0 z1 10
  have q11 : 0 ≤ z ^ 11 := pow_nonneg z0 11
  have p12 : z ^ 12 ≤ (1 / 12) * z ^ 11 := nlt_pw z0 z1 11
  have q12 : 0 ≤ z ^ 12 := pow_nonneg z0 12
  have p13 : z ^ 13 ≤ (1 / 12) * z ^ 12 := nlt_pw z0 z1 12
  have q13 : 0 ≤ z ^ 13 := pow_nonneg z0 13
  have e : nltPq30 ((1 / 4) + z) = (3266323305507477321173 / 60466176000000000000) + (1304569966743913949561 / 1417176000000000000) * z + (444222076574050877239 / 125971200000000000) * z ^ 2 - (986451461217987841189 / 15746400000000000) * z ^ 3 - (275486806079335308247 / 349920000000000) * z ^ 4 - (16430940574403920511 / 4374000000000) * z ^ 5 - (230645921046637483 / 24300000000) * z ^ 6 - (8798192758991689 / 607500000) * z ^ 7 - (230149354868321 / 16200000) * z ^ 8 - (1551213073163 / 168750) * z ^ 9 - (44077896647 / 11250) * z ^ 10 - (133257164 / 125) * z ^ 11 - (4253356 / 25) * z ^ 12 - (62016 / 5) * z ^ 13 := by unfold nltPq30; ring
  rw [e]; linarith only [z0, z1, p2, q2, p3, q3, p4, q4, p5, q5, p6, q6, p7, q7, p8, q8, p9, q9, p10, q10, p11, q11, p12, q12, p13, q13]

/-- **`𝓜` increases in `h`** (auxiliary note (4), (11)) on `[1/4, 1/3] × [0, 1/4]`. -/
theorem nlt_Mq_dh_pos {h j : ℝ} (h1 : 1 / 4 ≤ h) (h2 : h ≤ 1 / 3) (j0 : 0 ≤ j) (j1 : j ≤ 1 / 4) :
    0 < lrhHorner (nltDer (nltMqL j)) h := by
  rw [nlt_Mq_dh]
  have v0 : 0 ≤ 4 * j := by linarith
  have v1 : 4 * j ≤ 1 := by linarith
  have a0 := nltAqb0_pos v0 v1
  have a1 := nltAqb1_pos v0 v1
  have a2 := nltAqb2_pos v0 v1
  have a3 := nltAqb3_pos v0 v1
  have a4 := nltAqb4_pos v0 v1
  have a5 := nltAqb5_pos v0 v1
  have a6 := nltAqb6_pos v0 v1
  have a7 := nltAqb7_pos v0 v1
  unfold nltAqb0 nltAqb1 nltAqb2 nltAqb3 nltAqb4 nltAqb5 nltAqb6 nltAqb7 at *
  have u0 : 0 ≤ 4 * h - 1 := by linarith
  have u1 : 4 * h - 1 ≤ 1 / 3 := by linarith
  have k := nltMqK_pos u0 u1
  unfold nltMqK at k
  have t1 := mul_le_mul_of_nonneg_right a1.le u0
  have t2 := mul_le_mul_of_nonneg_right a2.le (pow_nonneg u0 2)
  have t3 := mul_nonneg a3.le (pow_nonneg u0 3)
  have t4 := mul_le_mul_of_nonneg_right a4.le (pow_nonneg u0 4)
  have t5 := mul_le_mul_of_nonneg_right a5.le (pow_nonneg u0 5)
  have t6 := mul_le_mul_of_nonneg_right a6.le (pow_nonneg u0 6)
  have t7 := mul_le_mul_of_nonneg_right a7.le (pow_nonneg u0 7)
  linarith

/-- **`𝓜 > 0`** (auxiliary note (1)) for `1/4 ≤ h ≤ 1/3`, `1/30 ≤ j ≤ 3h/4`: lower `h` to `1/4`
if `j ≤ 3/16`, otherwise to `4j/3`, and use the endpoint signs (12)-(13), (17)-(18). -/
theorem nlt_Mq_pos {h j : ℝ} (h1 : 1 / 4 ≤ h) (h2 : h ≤ 1 / 3) (j0 : 1 / 30 ≤ j)
    (j1 : j ≤ 3 / 4 * h) : 0 < nltMq h j := by
  have hd : ∀ s, HasDerivAt (lrhHorner (nltMqL j)) (lrhHorner (nltDer (nltMqL j)) s) s :=
    fun s => nlt_hasDerivAt_horner _ s
  have jle : j ≤ 1 / 4 := by linarith
  have dpos : ∀ s, 1 / 4 ≤ s → s ≤ 1 / 3 → 0 ≤ lrhHorner (nltDer (nltMqL j)) s :=
    fun s s1 s2 => (nlt_Mq_dh_pos s1 s2 (by linarith) jle).le
  rw [nlt_Mq_h]
  rcases le_total j (3 / 16) with hj | hj
  · have mono := hrl_mono hd dpos le_rfl h1 h2
    have base : 0 < nltMq (1 / 4) j := by
      have := nltMqF_pos (v := 4 * j) (by linarith) (by linarith)
      have e : 65536 * nltMq (1 / 4) j = nltMqF (4 * j) := by unfold nltMq nltMqF; ring
      linarith
    rw [nlt_Mq_h] at base
    linarith
  · have h0 : 1 / 4 ≤ 4 / 3 * j := by linarith
    have h0' : 4 / 3 * j ≤ h := by linarith
    have mono := hrl_mono hd dpos h0 h0' h2
    have base : 0 < nltMq (4 / 3 * j) j := by
      have hT := nltMqT_pos (h := 4 / 3 * j) h0 (by linarith)
      have e : 65536 * nltMq (4 / 3 * j) j = 4 / 3 * j * nltMqT (4 / 3 * j) := by
        unfold nltMq nltMqT; ring
      have : 0 < 4 / 3 * j * nltMqT (4 / 3 * j) := mul_pos (by linarith) hT
      linarith
    rw [nlt_Mq_h] at base
    linarith

/-- **The maximum-duration face** (`NONSHORT_LOW_T_QMAX` (2)): for `1/4 ≤ h ≤ 1/3`,
`1/30 ≤ j ≤ 5h/7`, the circuit at `y = (h - j)/(1 + 2j)` is positive. -/
theorem nlt_face_qmax {h j : ℝ} (h1 : 1 / 4 ≤ h) (h2 : h ≤ 1 / 3) (j0 : 1 / 30 ≤ j)
    (j1 : j ≤ 5 / 7 * h) :
    0 < nltSt0 ((1 - h) / 2) (h + j) + nltSt1 ((1 - h) / 2) (h + j) * ((h - j) / (1 + 2 * j))
      + nltSt2 ((1 - h) / 2) (h + j) * ((h - j) / (1 + 2 * j)) ^ 2
      + nltSt3 ((1 - h) / 2) (h + j) * ((h - j) / (1 + 2 * j)) ^ 3
      + nltSt4 ((1 - h) / 2) (h + j) * ((h - j) / (1 + 2 * j)) ^ 4
      + nltSt5 ((1 - h) / 2) (h + j) * ((h - j) / (1 + 2 * j)) ^ 5
      + nltSt6 ((1 - h) / 2) (h + j) * ((h - j) / (1 + 2 * j)) ^ 6 := by
  have hd : ∀ s, HasDerivAt (lrhHorner (nltPqL h)) (lrhHorner (nltDer (nltPqL h)) s) s :=
    fun s => nlt_hasDerivAt_horner _ s
  have pos : ∀ s, 1 / 30 ≤ s → s ≤ j → 0 ≤ lrhHorner (nltDer (nltPqL h)) s := fun s s1 s2 => by
    rw [nlt_Pq_dj]
    have := nlt_Rq_ge h1 h2 (by linarith) (by linarith : s ≤ 1 / 4)
    have := nlt_Mq_pos h1 h2 s1 (by linarith : s ≤ 3 / 4 * h)
    linarith
  have mono := hrl_mono hd pos le_rfl j0 le_rfl
  have p30 := nlt_Pq30_gt h1 h2
  rw [← nlt_Pq30_eq] at p30
  have hP : 0 < lrhHorner (nltPqL h) j := by linarith
  have e := nlt_Pq_eq h j
  have hd1 : 0 < 1 + 2 * j := by linarith
  set P := lrhHorner (nltPqL h) j
  have key : nltSt0 ((1 - h) / 2) (h + j) + nltSt1 ((1 - h) / 2) (h + j) * ((h - j) / (1 + 2 * j))
      + nltSt2 ((1 - h) / 2) (h + j) * ((h - j) / (1 + 2 * j)) ^ 2
      + nltSt3 ((1 - h) / 2) (h + j) * ((h - j) / (1 + 2 * j)) ^ 3
      + nltSt4 ((1 - h) / 2) (h + j) * ((h - j) / (1 + 2 * j)) ^ 4
      + nltSt5 ((1 - h) / 2) (h + j) * ((h - j) / (1 + 2 * j)) ^ 5
      + nltSt6 ((1 - h) / 2) (h + j) * ((h - j) / (1 + 2 * j)) ^ 6 =
      (1 + h + j) ^ 2 * P / (6 * (1 + 2 * j) ^ 6) := by
    rw [← e]; field_simp
  rw [key]
  have : 0 < 1 + h + j := by linarith
  positivity

end SmoothedOctagon
