module

public import SmoothedOctagon.Exclusion.Mixed.SmallerShort.LargeRatio.OuterFace
public import SmoothedOctagon.Exclusion.Mixed.SmallerShort.LargeRatio.SignChange

/-!
# Smaller-short window, large ratio: the outer face, large shapes

For `(2x + 3)/5 ≤ α ≤ x` the incoming norm is raised to `u_b = (x + 74)/100`; then each cleared
numerator (`lgrNoT`, `lgrNo8`, `lgrNo2` at `U = x + 74`, `V = 100`) is a cubic in `β`, computed in
Lean from its factored formula (`lgrFLT`, …). On
`β ∈ [x + (3/5)(α - 1), x + (3/2)(α - 1)]` the four-term cubic identity (`lgr_cubic_pos`,
`lgr_cubic_list`) reduces its sign to four coefficients
`C_j = κ s_j P_j(α - (2x + 3)/5, x - 2)` (`lgrPT0_eq`, …, the twelve printed `P_{ij}`, verified
against the Lean definitions), and each `P_{ij}` is positive by one sign change in `A`
(`lgr_sc2`, `lgr_sc3`, `lgr_sc4`), its coefficient signs and its value at `A = 3(X + 1)/5`
on `2/5 ≤ X ≤ 7` by a second sign-change comparison in `Y = X - 2/5`.
Every required univariate polynomial has nonnegative lower coefficients,
nonpositive higher coefficients, and positive values at `Y = 0, 33/5`.

## Main API

* `lgr_largeT`, `lgr_large8`, `lgr_large2`.
-/

@[expose] public section

namespace SmoothedOctagon

/-- **The four-term cubic identity**: a cubic positive at both ends, with positive
inner control values `f(p) + (q - p)f'(p)/3`, `f(q) - (q - p)f'(q)/3`, is positive on `[p, q]`. -/
theorem lgr_cubic_pos {m0 m1 m2 m3 p q y : ℝ} (hpq : p < q) (hpy : p ≤ y) (hyq : y ≤ q)
    (h0 : 0 < m0 + m1 * p + m2 * p ^ 2 + m3 * p ^ 3)
    (h1 : 0 < m0 + m1 * p + m2 * p ^ 2 + m3 * p ^ 3 +
      (q - p) / 3 * (m1 + 2 * m2 * p + 3 * m3 * p ^ 2))
    (h2 : 0 < m0 + m1 * q + m2 * q ^ 2 + m3 * q ^ 3 -
      (q - p) / 3 * (m1 + 2 * m2 * q + 3 * m3 * q ^ 2))
    (h3 : 0 < m0 + m1 * q + m2 * q ^ 2 + m3 * q ^ 3) :
    0 < m0 + m1 * y + m2 * y ^ 2 + m3 * y ^ 3 := by
  have e : (q - p) ^ 3 * (m0 + m1 * y + m2 * y ^ 2 + m3 * y ^ 3) =
      (q - y) ^ 3 * (m0 + m1 * p + m2 * p ^ 2 + m3 * p ^ 3) +
      3 * (y - p) * (q - y) ^ 2 * (m0 + m1 * p + m2 * p ^ 2 + m3 * p ^ 3 +
        (q - p) / 3 * (m1 + 2 * m2 * p + 3 * m3 * p ^ 2)) +
      3 * (y - p) ^ 2 * (q - y) * (m0 + m1 * q + m2 * q ^ 2 + m3 * q ^ 3 -
        (q - p) / 3 * (m1 + 2 * m2 * q + 3 * m3 * q ^ 2)) +
      (y - p) ^ 3 * (m0 + m1 * q + m2 * q ^ 2 + m3 * q ^ 3) := by ring
  have hqp' : 0 < q - p := by linarith
  have hqp : 0 < (q - p) ^ 3 := by positivity
  have hpos : 0 < (q - p) ^ 3 * (m0 + m1 * y + m2 * y ^ 2 + m3 * y ^ 3) := by
    rw [e]
    have t1 : 0 ≤ 3 * (y - p) * (q - y) ^ 2 * (m0 + m1 * p + m2 * p ^ 2 + m3 * p ^ 3 +
        (q - p) / 3 * (m1 + 2 * m2 * p + 3 * m3 * p ^ 2)) :=
      mul_nonneg (mul_nonneg (by linarith) (by positivity)) h1.le
    have t2 : 0 ≤ 3 * (y - p) ^ 2 * (q - y) * (m0 + m1 * q + m2 * q ^ 2 + m3 * q ^ 3 -
        (q - p) / 3 * (m1 + 2 * m2 * q + 3 * m3 * q ^ 2)) :=
      mul_nonneg (mul_nonneg (by positivity) (by linarith)) h2.le
    rcases eq_or_lt_of_le hyq with hy | hy
    · subst hy
      have : 0 < (y - p) ^ 3 * (m0 + m1 * y + m2 * y ^ 2 + m3 * y ^ 3) := by
        have : 0 < y - p := by linarith
        positivity
      have : 0 ≤ (y - y) ^ 3 * (m0 + m1 * p + m2 * p ^ 2 + m3 * p ^ 3) := by simp
      linarith
    · have : 0 < (q - y) ^ 3 * (m0 + m1 * p + m2 * p ^ 2 + m3 * p ^ 3) := by
        have : 0 < q - y := by linarith
        positivity
      have : 0 ≤ (y - p) ^ 3 * (m0 + m1 * q + m2 * q ^ 2 + m3 * q ^ 3) :=
        mul_nonneg (pow_nonneg (by linarith) 3) h3.le
      linarith
  exact pos_of_mul_pos_right hpos hqp.le


/-- **The cubic identity on lists**: a list of at most four coefficients (a cubic in the outer
variable) satisfying the four control conditions is positive on `[p, q]`. -/
theorem lgr_cubic_list (F : List (List ℝ)) (hF : F.length ≤ 4) {A p q y : ℝ} (hpq : p < q)
    (hpy : p ≤ y) (hyq : y ≤ q) (h0 : 0 < lgrH2 F p A)
    (h1 : 0 < lgrH2 F p A + (q - p) / 3 * lgrH2 (lgrD2 F) p A)
    (h2 : 0 < lgrH2 F q A - (q - p) / 3 * lgrH2 (lgrD2 F) q A) (h3 : 0 < lgrH2 F q A) :
    0 < lgrH2 F y A := by
  simp only [lgr_H2_D] at h1 h2
  unfold lgrH2 at h0 h1 h2 h3 ⊢
  have hlen : (F.map (fun l => polyHorner l A)).length ≤ 4 := by simpa using hF
  generalize F.map (fun l => polyHorner l A) = cs at hlen h0 h1 h2 h3 ⊢
  have key : ∀ cs : List ℝ, cs.length ≤ 4 → ∃ m0 m1 m2 m3 : ℝ, ∀ s,
      polyHorner cs s = m0 + m1 * s + m2 * s ^ 2 + m3 * s ^ 3 ∧
        polyHornerD cs s = m1 + 2 * m2 * s + 3 * m3 * s ^ 2 := by
    intro cs hcs
    rcases cs with _ | ⟨c0, _ | ⟨c1, _ | ⟨c2, _ | ⟨c3, _ | ⟨c4, cs⟩⟩⟩⟩⟩
    · exact ⟨0, 0, 0, 0, fun s => by simp [polyHorner, polyHornerD]⟩
    · exact ⟨c0, 0, 0, 0, fun s => by simp [polyHorner, polyHornerD]⟩
    · exact ⟨c0, c1, 0, 0, fun s => ⟨by simp [polyHorner]; ring, by simp [polyHorner, polyHornerD]⟩⟩
    · exact ⟨c0, c1, c2, 0, fun s => by constructor <;> simp [polyHorner, polyHornerD] <;> ring⟩
    · exact ⟨c0, c1, c2, c3, fun s => by constructor <;> simp [polyHorner, polyHornerD] <;> ring⟩
    · simp only [List.length_cons] at hcs; omega
  obtain ⟨m0, m1, m2, m3, hm⟩ := key cs hlen
  rw [(hm y).1]
  rw [(hm p).1, (hm p).2] at h1
  rw [(hm p).1] at h0
  rw [(hm q).1, (hm q).2] at h2
  rw [(hm q).1] at h3
  exact lgr_cubic_pos hpq hpy hyq h0 h1 h2 h3

/-- The sign-change comparison: `p(A)A_m^{r+1} ≥ p(A_m)A^{r+1}` gives `p(A) > 0`. -/
theorem lgr_sc_core {A Am pA pAm : ℝ} {n : ℕ} (hA : 0 ≤ A) (hAm : A ≤ Am) (h0 : A = 0 → 0 < pA)
    (hend : 0 < pAm) (hkey : pAm * A ^ n ≤ pA * Am ^ n) : 0 < pA := by
  rcases eq_or_lt_of_le hA with h | h
  · exact h0 h.symm
  · have hAm0 : 0 < Am := h.trans_le hAm
    have : 0 < pAm * A ^ n := by positivity
    have : 0 < pA * Am ^ n := by linarith
    exact pos_of_mul_pos_left this (by positivity)

theorem lgr_pow_mono {A Am : ℝ} (hA : 0 ≤ A) (hAm : A ≤ Am) (n : ℕ) : A ^ n ≤ Am ^ n :=
  pow_le_pow_left₀ hA hAm n

/-- **One sign change, `r = 2`**: `c₀ > 0`, `c₁, c₂ ≥ 0`, `c₄, c₅ ≤ 0`. -/
theorem lgr_sc2 {l0 l1 l2 l3 l4 l5 : List ℝ} {X A : ℝ} (hX : 2 / 5 ≤ X) (hX7 : X ≤ 7) (hA : 0 ≤ A)
    (hAm : A ≤ 3 / 5 * X + 3 / 5)
    (h0 : ∀ X, 2 / 5 ≤ X → X ≤ 7 → 0 < polyHorner l0 X)
    (h1 : ∀ X, 2 / 5 ≤ X → X ≤ 7 → 0 < polyHorner l1 X)
    (h2 : ∀ X, 2 / 5 ≤ X → X ≤ 7 → 0 < polyHorner l2 X)
    (h4 : ∀ X, 2 / 5 ≤ X → X ≤ 7 → polyHorner l4 X < 0)
    (h5 : ∀ X, 2 / 5 ≤ X → X ≤ 7 → polyHorner l5 X < 0)
    (hend : ∀ X, 2 / 5 ≤ X → X ≤ 7 → 0 < polyHorner (lgrSlant (3 / 5) (3 / 5) [l0, l1, l2, l3, l4, l5]) X) :
    0 < lgrH2 [l0, l1, l2, l3, l4, l5] A X := by
  have he := hend X hX hX7
  rw [lgr_horner_slant] at he
  simp only [lgrH2, List.map, polyHorner] at he ⊢
  set Am := 3 / 5 * X + 3 / 5
  set c0 := polyHorner l0 X; set c1 := polyHorner l1 X; set c2 := polyHorner l2 X
  set c3 := polyHorner l3 X; set c4 := polyHorner l4 X; set c5 := polyHorner l5 X
  have p0 := h0 X hX hX7; have p1 := h1 X hX hX7; have p2 := h2 X hX hX7
  have p4 := h4 X hX hX7; have p5 := h5 X hX hX7
  have hAm0 : 0 ≤ Am := hA.trans hAm
  apply lgr_sc_core (n := 3) hA hAm (fun h => by subst h; simpa using p0) he
  have k0 : 0 ≤ c0 * (Am ^ 3 - A ^ 3) := mul_nonneg p0.le (by linarith [lgr_pow_mono hA hAm 3])
  have k1 : 0 ≤ c1 * (A * Am * (Am ^ 2 - A ^ 2)) :=
    mul_nonneg p1.le (mul_nonneg (mul_nonneg hA hAm0) (by linarith [lgr_pow_mono hA hAm 2]))
  have k2 : 0 ≤ c2 * (A ^ 2 * Am ^ 2 * (Am - A)) :=
    mul_nonneg p2.le (mul_nonneg (by positivity) (by linarith))
  have k4 : 0 ≤ c4 * (A ^ 3 * Am ^ 3 * (A - Am)) :=
    mul_nonneg_of_nonpos_of_nonpos p4.le (mul_nonpos_of_nonneg_of_nonpos (by positivity) (by linarith))
  have k5 : 0 ≤ c5 * (A ^ 3 * Am ^ 3 * (A ^ 2 - Am ^ 2)) :=
    mul_nonneg_of_nonpos_of_nonpos p5.le
      (mul_nonpos_of_nonneg_of_nonpos (by positivity) (by linarith [lgr_pow_mono hA hAm 2]))
  nlinarith [k0, k1, k2, k4, k5]

/-- **One sign change, `r = 3`**: `c₀ > 0`, `c₁, c₂, c₃ ≥ 0`, `c₅ ≤ 0`. -/
theorem lgr_sc3 {l0 l1 l2 l3 l4 l5 : List ℝ} {X A : ℝ} (hX : 2 / 5 ≤ X) (hX7 : X ≤ 7) (hA : 0 ≤ A)
    (hAm : A ≤ 3 / 5 * X + 3 / 5)
    (h0 : ∀ X, 2 / 5 ≤ X → X ≤ 7 → 0 < polyHorner l0 X)
    (h1 : ∀ X, 2 / 5 ≤ X → X ≤ 7 → 0 < polyHorner l1 X)
    (h2 : ∀ X, 2 / 5 ≤ X → X ≤ 7 → 0 < polyHorner l2 X)
    (h3 : ∀ X, 2 / 5 ≤ X → X ≤ 7 → 0 < polyHorner l3 X)
    (h5 : ∀ X, 2 / 5 ≤ X → X ≤ 7 → polyHorner l5 X < 0)
    (hend : ∀ X, 2 / 5 ≤ X → X ≤ 7 → 0 < polyHorner (lgrSlant (3 / 5) (3 / 5) [l0, l1, l2, l3, l4, l5]) X) :
    0 < lgrH2 [l0, l1, l2, l3, l4, l5] A X := by
  have he := hend X hX hX7
  rw [lgr_horner_slant] at he
  simp only [lgrH2, List.map, polyHorner] at he ⊢
  set Am := 3 / 5 * X + 3 / 5
  set c0 := polyHorner l0 X; set c1 := polyHorner l1 X; set c2 := polyHorner l2 X
  set c3 := polyHorner l3 X; set c4 := polyHorner l4 X; set c5 := polyHorner l5 X
  have p0 := h0 X hX hX7; have p1 := h1 X hX hX7; have p2 := h2 X hX hX7
  have p3 := h3 X hX hX7; have p5 := h5 X hX hX7
  have hAm0 : 0 ≤ Am := hA.trans hAm
  apply lgr_sc_core (n := 4) hA hAm (fun h => by subst h; simpa using p0) he
  have k0 : 0 ≤ c0 * (Am ^ 4 - A ^ 4) := mul_nonneg p0.le (by linarith [lgr_pow_mono hA hAm 4])
  have k1 : 0 ≤ c1 * (A * Am * (Am ^ 3 - A ^ 3)) :=
    mul_nonneg p1.le (mul_nonneg (mul_nonneg hA hAm0) (by linarith [lgr_pow_mono hA hAm 3]))
  have k2 : 0 ≤ c2 * (A ^ 2 * Am ^ 2 * (Am ^ 2 - A ^ 2)) :=
    mul_nonneg p2.le (mul_nonneg (by positivity) (by linarith [lgr_pow_mono hA hAm 2]))
  have k3 : 0 ≤ c3 * (A ^ 3 * Am ^ 3 * (Am - A)) :=
    mul_nonneg p3.le (mul_nonneg (by positivity) (by linarith))
  have k5 : 0 ≤ c5 * (A ^ 4 * Am ^ 4 * (A - Am)) :=
    mul_nonneg_of_nonpos_of_nonpos p5.le (mul_nonpos_of_nonneg_of_nonpos (by positivity) (by linarith))
  nlinarith [k0, k1, k2, k3, k5]

/-- **No sign change, `r = 4`**: `c₀ > 0`, `c₁, …, c₄ ≥ 0` (`c₅` arbitrary). -/
theorem lgr_sc4 {l0 l1 l2 l3 l4 l5 : List ℝ} {X A : ℝ} (hX : 2 / 5 ≤ X) (hX7 : X ≤ 7) (hA : 0 ≤ A)
    (hAm : A ≤ 3 / 5 * X + 3 / 5)
    (h0 : ∀ X, 2 / 5 ≤ X → X ≤ 7 → 0 < polyHorner l0 X)
    (h1 : ∀ X, 2 / 5 ≤ X → X ≤ 7 → 0 < polyHorner l1 X)
    (h2 : ∀ X, 2 / 5 ≤ X → X ≤ 7 → 0 < polyHorner l2 X)
    (h3 : ∀ X, 2 / 5 ≤ X → X ≤ 7 → 0 < polyHorner l3 X)
    (h4 : ∀ X, 2 / 5 ≤ X → X ≤ 7 → 0 < polyHorner l4 X)
    (hend : ∀ X, 2 / 5 ≤ X → X ≤ 7 → 0 < polyHorner (lgrSlant (3 / 5) (3 / 5) [l0, l1, l2, l3, l4, l5]) X) :
    0 < lgrH2 [l0, l1, l2, l3, l4, l5] A X := by
  have he := hend X hX hX7
  rw [lgr_horner_slant] at he
  simp only [lgrH2, List.map, polyHorner] at he ⊢
  set Am := 3 / 5 * X + 3 / 5
  set c0 := polyHorner l0 X; set c1 := polyHorner l1 X; set c2 := polyHorner l2 X
  set c3 := polyHorner l3 X; set c4 := polyHorner l4 X; set c5 := polyHorner l5 X
  have p0 := h0 X hX hX7; have p1 := h1 X hX hX7; have p2 := h2 X hX hX7
  have p3 := h3 X hX hX7; have p4 := h4 X hX hX7
  have hAm0 : 0 ≤ Am := hA.trans hAm
  apply lgr_sc_core (n := 5) hA hAm (fun h => by subst h; simpa using p0) he
  have k0 : 0 ≤ c0 * (Am ^ 5 - A ^ 5) := mul_nonneg p0.le (by linarith [lgr_pow_mono hA hAm 5])
  have k1 : 0 ≤ c1 * (A * Am * (Am ^ 4 - A ^ 4)) :=
    mul_nonneg p1.le (mul_nonneg (mul_nonneg hA hAm0) (by linarith [lgr_pow_mono hA hAm 4]))
  have k2 : 0 ≤ c2 * (A ^ 2 * Am ^ 2 * (Am ^ 3 - A ^ 3)) :=
    mul_nonneg p2.le (mul_nonneg (by positivity) (by linarith [lgr_pow_mono hA hAm 3]))
  have k3 : 0 ≤ c3 * (A ^ 3 * Am ^ 3 * (Am ^ 2 - A ^ 2)) :=
    mul_nonneg p3.le (mul_nonneg (by positivity) (by linarith [lgr_pow_mono hA hAm 2]))
  have k4 : 0 ≤ c4 * (A ^ 4 * Am ^ 4 * (Am - A)) :=
    mul_nonneg p4.le (mul_nonneg (by positivity) (by linarith))
  nlinarith [k0, k1, k2, k3, k4]

/-- The large-shape numerator of the `T` test (`u = u_b`) as a polynomial in `β` (outer variable;
the inner lists are constants in `x`, `α`), computed from the factored formula. -/
noncomputable def lgrFLT (x a : ℝ) : List (List ℝ) :=
  lgrNoL 56 4 56 392 336 (-189) 2352 [[x + 1]] [[a]] (lgrAdd2 [[a]] [[0], [1]]) [[x + 74]] [[100]]
    (lgrcD [[x]] [[a]] [[0], [1]])

theorem lgrFLT_link (x a b : ℝ) :
    lgrNoT (x + 1) a (a + b) (x + 74) 100 (ssDg x b a) = lgrH2 (lgrFLT x a) b 0 := by
  have h6 := lgr_H2_cD [[x]] [[a]] [[0], [1]] b 0
  unfold lgrFLT
  rw [lgr_H2_NoTL, h6]
  simp [lgrH2, polyHorner, lgrAdd2, lgrAdd, Horner.add]

/-- The large-shape numerator of the `T` test is a cubic in `β`. -/
theorem lgrFLT_len (x a : ℝ) : (lgrFLT x a).length ≤ 4 := by
  simp [lgrFLT, lgrNoL, lgrWoNL, lgrLoNL, lgrcD, lgrMul2, lgrMul, Horner.mul, lgrSmul2, lgrAdd2, lgrAdd, Horner.add, lgrSmul]

/-- `P_{T0}(A, X)`, grouped by powers of `A = α - (2x + 3)/5`, with
coefficients polynomials in `X = x - 2`. -/
noncomputable def lgrPT0 : List (List ℝ) :=
  [[(8272169647 / 3125), (34792853996 / 3125), (51652903569 / 3125), (7576318836 / 625), (3193514912 / 625), (4135166942 / 3125), (582672406 / 3125), (12284444 / 3125), (-996624 / 625)],
    [(1376480412 / 125), (6172280874 / 125), (1809766266 / 25), (1197572466 / 25), (389217186 / 25), (289754652 / 125), (9641544 / 125), (-271728 / 25)],
    [(-95134102 / 25), (343748133 / 25), (823940917 / 25), (523041663 / 25), (118949397 / 25), (5975196 / 25), (-113244 / 5)],
    [(-86477828 / 5), (-24619948), (-43802682 / 5), (-1852656 / 5), (339714 / 5), (-7680)],
    [(-9061125), (-12629215), (-4474575), (-367595), 18390],
    [(-1311024), (-1383662), (-189398), 8940]]

theorem lgrPT0_eq (x a : ℝ) :
    lgrH2 (lgrFLT x a) (x + (3 / 5) * (a - 1)) 0 =
      (4 / 125) * lgrH2 lgrPT0 (a - (2 * x + 3) / 5) (x - 2) := by
  simp only [lgrFLT, lgrNoL, lgrWoNL, lgrLoNL, lgrcD, lgrMul2, lgrMul, Horner.mul, lgrSmul2, lgrAdd2, lgrAdd, Horner.add, lgrSmul, Horner.smul, lgrH2, List.map, polyHorner, lgrPT0]
  ring

/-- **`P_{T0} > 0`** on `2/5 ≤ X ≤ 7`, `0 ≤ A ≤ 3(X + 1)/5` (one sign change in `A`). -/
theorem lgrPT0_pos {X A : ℝ} (hX : 2 / 5 ≤ X) (hX7 : X ≤ 7) (hA : 0 ≤ A)
    (hAm : A ≤ 3 / 5 * X + 3 / 5) : 0 < lgrH2 lgrPT0 A X := by
  simp only [lgrPT0]
  apply lgr_sc2 hX hX7 hA hAm
    (OneSignChange.positive_after_shift _ 6
      (by norm_num [OneSignChange.Conditions, lgrShift, Horner.shift, lgrAdd, Horner.add, lgrSmul, Horner.smul, Nat.forall_lt_succ_right,
        Nat.le_one_iff_eq_zero_or_eq_one, List.getD, polyHorner]))
    (OneSignChange.positive_after_shift _ 6
      (by norm_num [OneSignChange.Conditions, lgrShift, Horner.shift, lgrAdd, Horner.add, lgrSmul, Horner.smul, Nat.forall_lt_succ_right,
        Nat.le_one_iff_eq_zero_or_eq_one, List.getD, polyHorner]))
    (OneSignChange.positive_after_shift _ 5
      (by norm_num [OneSignChange.Conditions, lgrShift, Horner.shift, lgrAdd, Horner.add, lgrSmul, Horner.smul, Nat.forall_lt_succ_right,
        Nat.le_one_iff_eq_zero_or_eq_one, List.getD, polyHorner]))
    (OneSignChange.negative_after_shift _ 3
      (by norm_num [OneSignChange.Conditions, lgrShift, Horner.shift, lgrAdd, Horner.add, lgrSmul, Horner.smul, Nat.forall_lt_succ_right,
        Nat.le_one_iff_eq_zero_or_eq_one, List.getD, polyHorner]))
    (OneSignChange.negative_after_shift _ 2
      (by norm_num [OneSignChange.Conditions, lgrShift, Horner.shift, lgrAdd, Horner.add, lgrSmul, Horner.smul, Nat.forall_lt_succ_right,
        Nat.le_one_iff_eq_zero_or_eq_one, List.getD, polyHorner]))
    (OneSignChange.positive_after_shift _ 7
      (by norm_num [OneSignChange.Conditions, lgrShift, Horner.shift, lgrAdd, Horner.add, lgrSmul, Horner.smul, Nat.forall_lt_succ_right,
        Nat.le_one_iff_eq_zero_or_eq_one, List.getD, polyHorner, lgrSlant]))

/-- `P_{T1}(A, X)`, grouped by powers of `A = α - (2x + 3)/5`, with
coefficients polynomials in `X = x - 2`. -/
noncomputable def lgrPT1 : List (List ℝ) :=
  [[(3505517212 / 3125), (14204427068 / 3125), (4069023192 / 625), (14347640244 / 3125), (1175319692 / 625), (1536480092 / 3125), (227936548 / 3125), (1006384 / 625), (-2213856 / 3125)],
    [(676494447 / 125), (2837077347 / 125), (4034334972 / 125), (2628721866 / 125), (848893644 / 125), (126626988 / 125), (4240476 / 125), (-618912 / 125)],
    [(21766508 / 25), (293745018 / 25), (471994414 / 25), (266988978 / 25), 2303106, (553776 / 5), (-270696 / 25)],
    [(-33347318 / 5), (-41623169 / 5), (-10704978 / 5), (1072449 / 5), (215436 / 5), (-4728)],
    [(-4841520), (-6258832), (-2107860), (-169856), 8292],
    [(-933429), (-871706), (-111755), 5322]]

theorem lgrPT1_eq (x a : ℝ) :
    lgrH2 (lgrFLT x a) (x + (3 / 5) * (a - 1)) 0 + ((x + (3 / 2) * (a - 1)) - (x + (3 / 5) * (a - 1))) / 3 * lgrH2 (lgrD2 (lgrFLT x a)) (x + (3 / 5) * (a - 1)) 0 =
      (2 / 25) * lgrH2 lgrPT1 (a - (2 * x + 3) / 5) (x - 2) := by
  simp only [lgrFLT, lgrNoL, lgrWoNL, lgrLoNL, lgrcD, lgrMul2, lgrMul, Horner.mul, lgrSmul2, lgrAdd2, lgrAdd, Horner.add, lgrSmul, Horner.smul, lgrD2, lgrH2, List.map, polyHorner, lgrPT1]
  ring

/-- **`P_{T1} > 0`** on `2/5 ≤ X ≤ 7`, `0 ≤ A ≤ 3(X + 1)/5` (one sign change in `A`). -/
theorem lgrPT1_pos {X A : ℝ} (hX : 2 / 5 ≤ X) (hX7 : X ≤ 7) (hA : 0 ≤ A)
    (hAm : A ≤ 3 / 5 * X + 3 / 5) : 0 < lgrH2 lgrPT1 A X := by
  simp only [lgrPT1]
  apply lgr_sc2 hX hX7 hA hAm
    (OneSignChange.positive_after_shift _ 6
      (by norm_num [OneSignChange.Conditions, lgrShift, Horner.shift, lgrAdd, Horner.add, lgrSmul, Horner.smul, Nat.forall_lt_succ_right,
        Nat.le_one_iff_eq_zero_or_eq_one, List.getD, polyHorner]))
    (OneSignChange.positive_after_shift _ 6
      (by norm_num [OneSignChange.Conditions, lgrShift, Horner.shift, lgrAdd, Horner.add, lgrSmul, Horner.smul, Nat.forall_lt_succ_right,
        Nat.le_one_iff_eq_zero_or_eq_one, List.getD, polyHorner]))
    (OneSignChange.positive_after_shift _ 5
      (by norm_num [OneSignChange.Conditions, lgrShift, Horner.shift, lgrAdd, Horner.add, lgrSmul, Horner.smul, Nat.forall_lt_succ_right,
        Nat.le_one_iff_eq_zero_or_eq_one, List.getD, polyHorner]))
    (OneSignChange.negative_after_shift _ 3
      (by norm_num [OneSignChange.Conditions, lgrShift, Horner.shift, lgrAdd, Horner.add, lgrSmul, Horner.smul, Nat.forall_lt_succ_right,
        Nat.le_one_iff_eq_zero_or_eq_one, List.getD, polyHorner]))
    (OneSignChange.negative_after_shift _ 2
      (by norm_num [OneSignChange.Conditions, lgrShift, Horner.shift, lgrAdd, Horner.add, lgrSmul, Horner.smul, Nat.forall_lt_succ_right,
        Nat.le_one_iff_eq_zero_or_eq_one, List.getD, polyHorner]))
    (OneSignChange.positive_after_shift _ 7
      (by norm_num [OneSignChange.Conditions, lgrShift, Horner.shift, lgrAdd, Horner.add, lgrSmul, Horner.smul, Nat.forall_lt_succ_right,
        Nat.le_one_iff_eq_zero_or_eq_one, List.getD, polyHorner, lgrSlant]))

/-- `P_{T2}(A, X)`, grouped by powers of `A = α - (2x + 3)/5`, with
coefficients polynomials in `X = x - 2`. -/
noncomputable def lgrPT2 : List (List ℝ) :=
  [[(723565562 / 3125), (2815564672 / 3125), (3848846622 / 3125), (2561003652 / 3125), (200103892 / 625), (265719712 / 3125), (42728192 / 3125), (1008352 / 3125), (-488448 / 3125)],
    [(159414414 / 125), (634662498 / 125), (878948664 / 125), (564746184 / 125), (181425096 / 125), (27177648 / 125), (921264 / 125), (-139392 / 125)],
    [(18086272 / 25), (92866494 / 25), (124422758 / 25), 2610831, (13533627 / 25), (628398 / 25), (-12648 / 5)],
    [(-1108832), (-5740588 / 5), (-359079 / 5), (628167 / 5), (57684 / 5), (-6384 / 5)],
    [(-1140114), (-1445789), (-480345), (-39442), 1878],
    [(-273894), (-243829), (-30439), 1446]]

theorem lgrPT2_eq (x a : ℝ) :
    lgrH2 (lgrFLT x a) (x + (3 / 2) * (a - 1)) 0 - ((x + (3 / 2) * (a - 1)) - (x + (3 / 5) * (a - 1))) / 3 * lgrH2 (lgrD2 (lgrFLT x a)) (x + (3 / 2) * (a - 1)) 0 =
      (2 / 5) * lgrH2 lgrPT2 (a - (2 * x + 3) / 5) (x - 2) := by
  simp only [lgrFLT, lgrNoL, lgrWoNL, lgrLoNL, lgrcD, lgrMul2, lgrMul, Horner.mul, lgrSmul2, lgrAdd2, lgrAdd, Horner.add, lgrSmul, Horner.smul, lgrD2, lgrH2, List.map, polyHorner, lgrPT2]
  ring

/-- **`P_{T2} > 0`** on `2/5 ≤ X ≤ 7`, `0 ≤ A ≤ 3(X + 1)/5` (one sign change in `A`). -/
theorem lgrPT2_pos {X A : ℝ} (hX : 2 / 5 ≤ X) (hX7 : X ≤ 7) (hA : 0 ≤ A)
    (hAm : A ≤ 3 / 5 * X + 3 / 5) : 0 < lgrH2 lgrPT2 A X := by
  simp only [lgrPT2]
  apply lgr_sc2 hX hX7 hA hAm
    (OneSignChange.positive_after_shift _ 6
      (by norm_num [OneSignChange.Conditions, lgrShift, Horner.shift, lgrAdd, Horner.add, lgrSmul, Horner.smul, Nat.forall_lt_succ_right,
        Nat.le_one_iff_eq_zero_or_eq_one, List.getD, polyHorner]))
    (OneSignChange.positive_after_shift _ 6
      (by norm_num [OneSignChange.Conditions, lgrShift, Horner.shift, lgrAdd, Horner.add, lgrSmul, Horner.smul, Nat.forall_lt_succ_right,
        Nat.le_one_iff_eq_zero_or_eq_one, List.getD, polyHorner]))
    (OneSignChange.positive_after_shift _ 5
      (by norm_num [OneSignChange.Conditions, lgrShift, Horner.shift, lgrAdd, Horner.add, lgrSmul, Horner.smul, Nat.forall_lt_succ_right,
        Nat.le_one_iff_eq_zero_or_eq_one, List.getD, polyHorner]))
    (OneSignChange.negative_after_shift _ 3
      (by norm_num [OneSignChange.Conditions, lgrShift, Horner.shift, lgrAdd, Horner.add, lgrSmul, Horner.smul, Nat.forall_lt_succ_right,
        Nat.le_one_iff_eq_zero_or_eq_one, List.getD, polyHorner]))
    (OneSignChange.negative_after_shift _ 2
      (by norm_num [OneSignChange.Conditions, lgrShift, Horner.shift, lgrAdd, Horner.add, lgrSmul, Horner.smul, Nat.forall_lt_succ_right,
        Nat.le_one_iff_eq_zero_or_eq_one, List.getD, polyHorner]))
    (OneSignChange.positive_after_shift _ 7
      (by norm_num [OneSignChange.Conditions, lgrShift, Horner.shift, lgrAdd, Horner.add, lgrSmul, Horner.smul, Nat.forall_lt_succ_right,
        Nat.le_one_iff_eq_zero_or_eq_one, List.getD, polyHorner, lgrSlant]))

/-- `P_{T3}(A, X)`, grouped by powers of `A = α - (2x + 3)/5`, with
coefficients polynomials in `X = x - 2`. -/
noncomputable def lgrPT3 : List (List ℝ) :=
  [[(145736248 / 3125), (540981356 / 3125), (693216852 / 3125), (419699664 / 3125), (29957288 / 625), (40951088 / 3125), (7572016 / 3125), (197312 / 3125), (-107136 / 3125)],
    [(7295409 / 25), (139035357 / 125), (37582476 / 25), (119109606 / 125), (38086704 / 125), (5741616 / 125), (198096 / 125), (-31104 / 125)],
    [(6720296 / 25), (25979364 / 25), (31208134 / 25), (15497913 / 25), (623001 / 5), (140388 / 25), (-2904 / 5)],
    [(-704474 / 5), (-409808 / 5), (375078 / 5), (219981 / 5), (14211 / 5), (-1608 / 5)],
    [(-248064), (-318481), (-106857), (-9164), 426],
    [(-74631), (-64292), (-7889), 372]]

theorem lgrPT3_eq (x a : ℝ) :
    lgrH2 (lgrFLT x a) (x + (3 / 2) * (a - 1)) 0 =
      2 * lgrH2 lgrPT3 (a - (2 * x + 3) / 5) (x - 2) := by
  simp only [lgrFLT, lgrNoL, lgrWoNL, lgrLoNL, lgrcD, lgrMul2, lgrMul, Horner.mul, lgrSmul2, lgrAdd2, lgrAdd, Horner.add, lgrSmul, Horner.smul, lgrH2, List.map, polyHorner, lgrPT3]
  ring

/-- **`P_{T3} > 0`** on `2/5 ≤ X ≤ 7`, `0 ≤ A ≤ 3(X + 1)/5` (one sign change in `A`). -/
theorem lgrPT3_pos {X A : ℝ} (hX : 2 / 5 ≤ X) (hX7 : X ≤ 7) (hA : 0 ≤ A)
    (hAm : A ≤ 3 / 5 * X + 3 / 5) : 0 < lgrH2 lgrPT3 A X := by
  simp only [lgrPT3]
  apply lgr_sc2 hX hX7 hA hAm
    (OneSignChange.positive_after_shift _ 6
      (by norm_num [OneSignChange.Conditions, lgrShift, Horner.shift, lgrAdd, Horner.add, lgrSmul, Horner.smul, Nat.forall_lt_succ_right,
        Nat.le_one_iff_eq_zero_or_eq_one, List.getD, polyHorner]))
    (OneSignChange.positive_after_shift _ 6
      (by norm_num [OneSignChange.Conditions, lgrShift, Horner.shift, lgrAdd, Horner.add, lgrSmul, Horner.smul, Nat.forall_lt_succ_right,
        Nat.le_one_iff_eq_zero_or_eq_one, List.getD, polyHorner]))
    (OneSignChange.positive_after_shift _ 5
      (by norm_num [OneSignChange.Conditions, lgrShift, Horner.shift, lgrAdd, Horner.add, lgrSmul, Horner.smul, Nat.forall_lt_succ_right,
        Nat.le_one_iff_eq_zero_or_eq_one, List.getD, polyHorner]))
    (OneSignChange.negative_after_shift _ 3
      (by norm_num [OneSignChange.Conditions, lgrShift, Horner.shift, lgrAdd, Horner.add, lgrSmul, Horner.smul, Nat.forall_lt_succ_right,
        Nat.le_one_iff_eq_zero_or_eq_one, List.getD, polyHorner]))
    (OneSignChange.negative_after_shift _ 2
      (by norm_num [OneSignChange.Conditions, lgrShift, Horner.shift, lgrAdd, Horner.add, lgrSmul, Horner.smul, Nat.forall_lt_succ_right,
        Nat.le_one_iff_eq_zero_or_eq_one, List.getD, polyHorner]))
    (OneSignChange.positive_after_shift _ 7
      (by norm_num [OneSignChange.Conditions, lgrShift, Horner.shift, lgrAdd, Horner.add, lgrSmul, Horner.smul, Nat.forall_lt_succ_right,
        Nat.le_one_iff_eq_zero_or_eq_one, List.getD, polyHorner, lgrSlant]))

/-- **The large shapes, `T` test**: the cleared numerator at `u = u_b` is positive for
`(2x + 3)/5 ≤ α ≤ x` and `x + (3/5)(α - 1) ≤ β ≤ x + (3/2)(α - 1)`. -/
theorem lgr_largeT {x a b : ℝ} (hx : 12 / 5 ≤ x) (hx9 : x ≤ 9) (ham : (2 * x + 3) / 5 ≤ a)
    (hax : a ≤ x) (hb : x + 3 / 5 * (a - 1) ≤ b) (hb' : b ≤ x + 3 / 2 * (a - 1)) :
    0 < lgrNoT (x + 1) a (a + b) (x + 74) 100 (ssDg x b a) := by
  rw [lgrFLT_link]
  have hA : 0 ≤ a - (2 * x + 3) / 5 := by linarith
  have hAm : a - (2 * x + 3) / 5 ≤ 3 / 5 * (x - 2) + 3 / 5 := by linarith
  apply lgr_cubic_list _ (lgrFLT_len x a) (p := (x + (3 / 5) * (a - 1))) (q := (x + (3 / 2) * (a - 1))) (by nlinarith) (by linarith) (by linarith)
  · rw [lgrPT0_eq]; have := lgrPT0_pos (by linarith) (by linarith) hA hAm; positivity
  · rw [lgrPT1_eq]; have := lgrPT1_pos (by linarith) (by linarith) hA hAm; positivity
  · rw [lgrPT2_eq]; have := lgrPT2_pos (by linarith) (by linarith) hA hAm; positivity
  · rw [lgrPT3_eq]; have := lgrPT3_pos (by linarith) (by linarith) hA hAm; positivity

/-- The large-shape numerator of the `8` test (`u = u_b`) as a polynomial in `β` (outer variable;
the inner lists are constants in `x`, `α`), computed from the factored formula. -/
noncomputable def lgrFL8 (x a : ℝ) : List (List ℝ) :=
  lgrNoL 1008 72 896 7056 5922 (-2618) 36848 [[x + 1]] [[a]] (lgrAdd2 [[a]] [[0], [1]]) [[x + 74]] [[100]]
    (lgrcD [[x]] [[a]] [[0], [1]])

theorem lgrFL8_link (x a b : ℝ) :
    lgrNo8 (x + 1) a (a + b) (x + 74) 100 (ssDg x b a) = lgrH2 (lgrFL8 x a) b 0 := by
  have h6 := lgr_H2_cD [[x]] [[a]] [[0], [1]] b 0
  unfold lgrFL8
  rw [lgr_H2_No8L, h6]
  simp [lgrH2, polyHorner, lgrAdd2, lgrAdd, Horner.add]

/-- The large-shape numerator of the `8` test is a cubic in `β`. -/
theorem lgrFL8_len (x a : ℝ) : (lgrFL8 x a).length ≤ 4 := by
  simp [lgrFL8, lgrNoL, lgrWoNL, lgrLoNL, lgrcD, lgrMul2, lgrMul, Horner.mul, lgrSmul2, lgrAdd2, lgrAdd, Horner.add, lgrSmul]

/-- `P_{80}(A, X)`, grouped by powers of `A = α - (2x + 3)/5`, with
coefficients polynomials in `X = x - 2`. -/
noncomputable def lgrP80 : List (List ℝ) :=
  [[(73504174968 / 3125), (292590795899 / 3125), (418268818186 / 3125), (60170506309 / 625), (25294686578 / 625), (33102952198 / 3125), (4726694814 / 3125), (95719436 / 3125), (-8411856 / 625)],
    [(14525995573 / 125), (58256865451 / 125), (3212188469 / 5), (10290169433 / 25), (658218266 / 5), (2429771228 / 125), (79088736 / 125), (-2321232 / 25)],
    [(484249577 / 25), (5625595852 / 25), (8726003108 / 25), (4887758352 / 25), (1053646223 / 25), (50757524 / 25), (-1007436 / 5)],
    [(-520737377 / 5), (-126016603), (-150161333 / 5), (25710571 / 5), (4438666 / 5), (-98520)],
    [(-62785365), (-82767805), (-29069705), (-2468355), 110910],
    [(-9645456), (-9484328), (-1280312), 57360]]

theorem lgrP80_eq (x a : ℝ) :
    lgrH2 (lgrFL8 x a) (x + (3 / 5) * (a - 1)) 0 =
      (8 / 125) * lgrH2 lgrP80 (a - (2 * x + 3) / 5) (x - 2) := by
  simp only [lgrFL8, lgrNoL, lgrWoNL, lgrLoNL, lgrcD, lgrMul2, lgrMul, Horner.mul, lgrSmul2, lgrAdd2, lgrAdd, Horner.add, lgrSmul, Horner.smul, lgrH2, List.map, polyHorner, lgrP80]
  ring

/-- **`P_{80} > 0`** on `2/5 ≤ X ≤ 7`, `0 ≤ A ≤ 3(X + 1)/5` (one sign change in `A`). -/
theorem lgrP80_pos {X A : ℝ} (hX : 2 / 5 ≤ X) (hX7 : X ≤ 7) (hA : 0 ≤ A)
    (hAm : A ≤ 3 / 5 * X + 3 / 5) : 0 < lgrH2 lgrP80 A X := by
  simp only [lgrP80]
  apply lgr_sc2 hX hX7 hA hAm
    (OneSignChange.positive_after_shift _ 6
      (by norm_num [OneSignChange.Conditions, lgrShift, Horner.shift, lgrAdd, Horner.add, lgrSmul, Horner.smul, Nat.forall_lt_succ_right,
        Nat.le_one_iff_eq_zero_or_eq_one, List.getD, polyHorner]))
    (OneSignChange.positive_after_shift _ 6
      (by norm_num [OneSignChange.Conditions, lgrShift, Horner.shift, lgrAdd, Horner.add, lgrSmul, Horner.smul, Nat.forall_lt_succ_right,
        Nat.le_one_iff_eq_zero_or_eq_one, List.getD, polyHorner]))
    (OneSignChange.positive_after_shift _ 5
      (by norm_num [OneSignChange.Conditions, lgrShift, Horner.shift, lgrAdd, Horner.add, lgrSmul, Horner.smul, Nat.forall_lt_succ_right,
        Nat.le_one_iff_eq_zero_or_eq_one, List.getD, polyHorner]))
    (OneSignChange.negative_after_shift _ 3
      (by norm_num [OneSignChange.Conditions, lgrShift, Horner.shift, lgrAdd, Horner.add, lgrSmul, Horner.smul, Nat.forall_lt_succ_right,
        Nat.le_one_iff_eq_zero_or_eq_one, List.getD, polyHorner]))
    (OneSignChange.negative_after_shift _ 2
      (by norm_num [OneSignChange.Conditions, lgrShift, Horner.shift, lgrAdd, Horner.add, lgrSmul, Horner.smul, Nat.forall_lt_succ_right,
        Nat.le_one_iff_eq_zero_or_eq_one, List.getD, polyHorner]))
    (OneSignChange.positive_after_shift _ 7
      (by norm_num [OneSignChange.Conditions, lgrShift, Horner.shift, lgrAdd, Horner.add, lgrSmul, Horner.smul, Nat.forall_lt_succ_right,
        Nat.le_one_iff_eq_zero_or_eq_one, List.getD, polyHorner, lgrSlant]))

/-- `P_{81}(A, X)`, grouped by powers of `A = α - (2x + 3)/5`, with
coefficients polynomials in `X = x - 2`. -/
noncomputable def lgrP81 : List (List ℝ) :=
  [[(30669086394 / 3125), (23508877078 / 625), (161570652742 / 3125), (111339429026 / 3125), (9096962744 / 625), (12102627124 / 3125), (367044468 / 625), (39020432 / 3125), (-18688224 / 3125)],
    [(1379546771 / 25), (26326622341 / 125), (35430598412 / 125), (4484672324 / 25), (285657248 / 5), (211707148 / 25), (34756236 / 125), (-5281248 / 125)],
    [(769867688 / 25), (3643062136 / 25), (941994862 / 5), 97591608, (100926178 / 5), (23427968 / 25), (-2392584 / 25)],
    [(-172028102 / 5), (-32147227), (6521122 / 5), (26646571 / 5), (2462356 / 5), (-54312)],
    [(-32049762), (-40484344), (-13666154), (-1154904), 50268],
    [(-6611493), (-6100310), (-788879), 36138]]

theorem lgrP81_eq (x a : ℝ) :
    lgrH2 (lgrFL8 x a) (x + (3 / 5) * (a - 1)) 0 + ((x + (3 / 2) * (a - 1)) - (x + (3 / 5) * (a - 1))) / 3 * lgrH2 (lgrD2 (lgrFL8 x a)) (x + (3 / 5) * (a - 1)) 0 =
      (4 / 25) * lgrH2 lgrP81 (a - (2 * x + 3) / 5) (x - 2) := by
  simp only [lgrFL8, lgrNoL, lgrWoNL, lgrLoNL, lgrcD, lgrMul2, lgrMul, Horner.mul, lgrSmul2, lgrAdd2, lgrAdd, Horner.add, lgrSmul, Horner.smul, lgrD2, lgrH2, List.map, polyHorner, lgrP81]
  ring

/-- **`P_{81} > 0`** on `2/5 ≤ X ≤ 7`, `0 ≤ A ≤ 3(X + 1)/5` (one sign change in `A`). -/
theorem lgrP81_pos {X A : ℝ} (hX : 2 / 5 ≤ X) (hX7 : X ≤ 7) (hA : 0 ≤ A)
    (hAm : A ≤ 3 / 5 * X + 3 / 5) : 0 < lgrH2 lgrP81 A X := by
  simp only [lgrP81]
  apply lgr_sc2 hX hX7 hA hAm
    (OneSignChange.positive_after_shift _ 6
      (by norm_num [OneSignChange.Conditions, lgrShift, Horner.shift, lgrAdd, Horner.add, lgrSmul, Horner.smul, Nat.forall_lt_succ_right,
        Nat.le_one_iff_eq_zero_or_eq_one, List.getD, polyHorner]))
    (OneSignChange.positive_after_shift _ 6
      (by norm_num [OneSignChange.Conditions, lgrShift, Horner.shift, lgrAdd, Horner.add, lgrSmul, Horner.smul, Nat.forall_lt_succ_right,
        Nat.le_one_iff_eq_zero_or_eq_one, List.getD, polyHorner]))
    (OneSignChange.positive_after_shift _ 5
      (by norm_num [OneSignChange.Conditions, lgrShift, Horner.shift, lgrAdd, Horner.add, lgrSmul, Horner.smul, Nat.forall_lt_succ_right,
        Nat.le_one_iff_eq_zero_or_eq_one, List.getD, polyHorner]))
    (OneSignChange.negative_after_shift _ 3
      (by norm_num [OneSignChange.Conditions, lgrShift, Horner.shift, lgrAdd, Horner.add, lgrSmul, Horner.smul, Nat.forall_lt_succ_right,
        Nat.le_one_iff_eq_zero_or_eq_one, List.getD, polyHorner]))
    (OneSignChange.negative_after_shift _ 2
      (by norm_num [OneSignChange.Conditions, lgrShift, Horner.shift, lgrAdd, Horner.add, lgrSmul, Horner.smul, Nat.forall_lt_succ_right,
        Nat.le_one_iff_eq_zero_or_eq_one, List.getD, polyHorner]))
    (OneSignChange.positive_after_shift _ 7
      (by norm_num [OneSignChange.Conditions, lgrShift, Horner.shift, lgrAdd, Horner.add, lgrSmul, Horner.smul, Nat.forall_lt_succ_right,
        Nat.le_one_iff_eq_zero_or_eq_one, List.getD, polyHorner, lgrSlant]))

/-- `P_{82}(A, X)`, grouped by powers of `A = α - (2x + 3)/5`, with
coefficients polynomials in `X = x - 2`. -/
noncomputable def lgrP82 : List (List ℝ) :=
  [[(12453349716 / 3125), (45699775424 / 3125), (11904229628 / 625), (38339803112 / 3125), (2977846376 / 625), (4074649456 / 3125), (680530464 / 3125), (3106624 / 625), (-8249088 / 3125)],
    [(3166511872 / 125), (464302588 / 5), (15288069884 / 125), (9565572472 / 125), (3036777488 / 125), (452963984 / 125), (15089568 / 125), (-2377344 / 125)],
    [(564179291 / 25), (410964323 / 5), (2392238582 / 25), (1173542802 / 25), (235265654 / 25), (10600076 / 25), (-1112784 / 25)],
    [(-8014141), (-10774379 / 5), (35835478 / 5), (17978986 / 5), (1235152 / 5), (-138432 / 5)],
    [(-14363907), (-18360973), (-6211484), (-545316), 23052],
    [(-3799767), (-3452483), (-441950), 20316]]

theorem lgrP82_eq (x a : ℝ) :
    lgrH2 (lgrFL8 x a) (x + (3 / 2) * (a - 1)) 0 - ((x + (3 / 2) * (a - 1)) - (x + (3 / 5) * (a - 1))) / 3 * lgrH2 (lgrD2 (lgrFL8 x a)) (x + (3 / 2) * (a - 1)) 0 =
      (2 / 5) * lgrH2 lgrP82 (a - (2 * x + 3) / 5) (x - 2) := by
  simp only [lgrFL8, lgrNoL, lgrWoNL, lgrLoNL, lgrcD, lgrMul2, lgrMul, Horner.mul, lgrSmul2, lgrAdd2, lgrAdd, Horner.add, lgrSmul, Horner.smul, lgrD2, lgrH2, List.map, polyHorner, lgrP82]
  ring

/-- **`P_{82} > 0`** on `2/5 ≤ X ≤ 7`, `0 ≤ A ≤ 3(X + 1)/5` (one sign change in `A`). -/
theorem lgrP82_pos {X A : ℝ} (hX : 2 / 5 ≤ X) (hX7 : X ≤ 7) (hA : 0 ≤ A)
    (hAm : A ≤ 3 / 5 * X + 3 / 5) : 0 < lgrH2 lgrP82 A X := by
  simp only [lgrP82]
  apply lgr_sc2 hX hX7 hA hAm
    (OneSignChange.positive_after_shift _ 6
      (by norm_num [OneSignChange.Conditions, lgrShift, Horner.shift, lgrAdd, Horner.add, lgrSmul, Horner.smul, Nat.forall_lt_succ_right,
        Nat.le_one_iff_eq_zero_or_eq_one, List.getD, polyHorner]))
    (OneSignChange.positive_after_shift _ 6
      (by norm_num [OneSignChange.Conditions, lgrShift, Horner.shift, lgrAdd, Horner.add, lgrSmul, Horner.smul, Nat.forall_lt_succ_right,
        Nat.le_one_iff_eq_zero_or_eq_one, List.getD, polyHorner]))
    (OneSignChange.positive_after_shift _ 5
      (by norm_num [OneSignChange.Conditions, lgrShift, Horner.shift, lgrAdd, Horner.add, lgrSmul, Horner.smul, Nat.forall_lt_succ_right,
        Nat.le_one_iff_eq_zero_or_eq_one, List.getD, polyHorner]))
    (OneSignChange.negative_after_shift _ 3
      (by norm_num [OneSignChange.Conditions, lgrShift, Horner.shift, lgrAdd, Horner.add, lgrSmul, Horner.smul, Nat.forall_lt_succ_right,
        Nat.le_one_iff_eq_zero_or_eq_one, List.getD, polyHorner]))
    (OneSignChange.negative_after_shift _ 2
      (by norm_num [OneSignChange.Conditions, lgrShift, Horner.shift, lgrAdd, Horner.add, lgrSmul, Horner.smul, Nat.forall_lt_succ_right,
        Nat.le_one_iff_eq_zero_or_eq_one, List.getD, polyHorner]))
    (OneSignChange.positive_after_shift _ 7
      (by norm_num [OneSignChange.Conditions, lgrShift, Horner.shift, lgrAdd, Horner.add, lgrSmul, Horner.smul, Nat.forall_lt_succ_right,
        Nat.le_one_iff_eq_zero_or_eq_one, List.getD, polyHorner, lgrSlant]))

/-- `P_{83}(A, X)`, grouped by powers of `A = α - (2x + 3)/5`, with
coefficients polynomials in `X = x - 2`. -/
noncomputable def lgrP83 : List (List ℝ) :=
  [[(2461839408 / 3125), (8562904696 / 3125), (10300108472 / 3125), (5886458224 / 3125), (409934128 / 625), (594669248 / 3125), (118484256 / 3125), (3010432 / 3125), (-1810176 / 3125)],
    [(708995642 / 125), (2509120778 / 125), (3237126472 / 125), (2002412804 / 125), (634004776 / 125), (95377936 / 125), (3241824 / 125), (-530304 / 125)],
    [(33856637 / 5), (538737317 / 25), (116874998 / 5), (275082558 / 25), (53781874 / 25), (2361784 / 25), (-50928 / 5)],
    [(652529 / 5), 2423575, (15252932 / 5), (5240462 / 5), (292478 / 5), (-33648 / 5)],
    [(-2935533), (-3948911), (-1377244), (-129000), 5316],
    [(-1025691), (-919207), (-116914), 5352]]

theorem lgrP83_eq (x a : ℝ) :
    lgrH2 (lgrFL8 x a) (x + (3 / 2) * (a - 1)) 0 =
      2 * lgrH2 lgrP83 (a - (2 * x + 3) / 5) (x - 2) := by
  simp only [lgrFL8, lgrNoL, lgrWoNL, lgrLoNL, lgrcD, lgrMul2, lgrMul, Horner.mul, lgrSmul2, lgrAdd2, lgrAdd, Horner.add, lgrSmul, Horner.smul, lgrH2, List.map, polyHorner, lgrP83]
  ring

/-- **`P_{83} > 0`** on `2/5 ≤ X ≤ 7`, `0 ≤ A ≤ 3(X + 1)/5` (one sign change in `A`). -/
theorem lgrP83_pos {X A : ℝ} (hX : 2 / 5 ≤ X) (hX7 : X ≤ 7) (hA : 0 ≤ A)
    (hAm : A ≤ 3 / 5 * X + 3 / 5) : 0 < lgrH2 lgrP83 A X := by
  simp only [lgrP83]
  apply lgr_sc3 hX hX7 hA hAm
    (OneSignChange.positive_after_shift _ 6
      (by norm_num [OneSignChange.Conditions, lgrShift, Horner.shift, lgrAdd, Horner.add, lgrSmul, Horner.smul, Nat.forall_lt_succ_right,
        Nat.le_one_iff_eq_zero_or_eq_one, List.getD, polyHorner]))
    (OneSignChange.positive_after_shift _ 6
      (by norm_num [OneSignChange.Conditions, lgrShift, Horner.shift, lgrAdd, Horner.add, lgrSmul, Horner.smul, Nat.forall_lt_succ_right,
        Nat.le_one_iff_eq_zero_or_eq_one, List.getD, polyHorner]))
    (OneSignChange.positive_after_shift _ 5
      (by norm_num [OneSignChange.Conditions, lgrShift, Horner.shift, lgrAdd, Horner.add, lgrSmul, Horner.smul, Nat.forall_lt_succ_right,
        Nat.le_one_iff_eq_zero_or_eq_one, List.getD, polyHorner]))
    (OneSignChange.positive_after_shift _ 4
      (by norm_num [OneSignChange.Conditions, lgrShift, Horner.shift, lgrAdd, Horner.add, lgrSmul, Horner.smul, Nat.forall_lt_succ_right,
        Nat.le_one_iff_eq_zero_or_eq_one, List.getD, polyHorner]))
    (OneSignChange.negative_after_shift _ 2
      (by norm_num [OneSignChange.Conditions, lgrShift, Horner.shift, lgrAdd, Horner.add, lgrSmul, Horner.smul, Nat.forall_lt_succ_right,
        Nat.le_one_iff_eq_zero_or_eq_one, List.getD, polyHorner]))
    (OneSignChange.positive_after_shift _ 7
      (by norm_num [OneSignChange.Conditions, lgrShift, Horner.shift, lgrAdd, Horner.add, lgrSmul, Horner.smul, Nat.forall_lt_succ_right,
        Nat.le_one_iff_eq_zero_or_eq_one, List.getD, polyHorner, lgrSlant]))

/-- **The large shapes, `8` test**: the cleared numerator at `u = u_b` is positive for
`(2x + 3)/5 ≤ α ≤ x` and `x + (3/5)(α - 1) ≤ β ≤ x + (3/2)(α - 1)`. -/
theorem lgr_large8 {x a b : ℝ} (hx : 12 / 5 ≤ x) (hx9 : x ≤ 9) (ham : (2 * x + 3) / 5 ≤ a)
    (hax : a ≤ x) (hb : x + 3 / 5 * (a - 1) ≤ b) (hb' : b ≤ x + 3 / 2 * (a - 1)) :
    0 < lgrNo8 (x + 1) a (a + b) (x + 74) 100 (ssDg x b a) := by
  rw [lgrFL8_link]
  have hA : 0 ≤ a - (2 * x + 3) / 5 := by linarith
  have hAm : a - (2 * x + 3) / 5 ≤ 3 / 5 * (x - 2) + 3 / 5 := by linarith
  apply lgr_cubic_list _ (lgrFL8_len x a) (p := (x + (3 / 5) * (a - 1))) (q := (x + (3 / 2) * (a - 1))) (by nlinarith) (by linarith) (by linarith)
  · rw [lgrP80_eq]; have := lgrP80_pos (by linarith) (by linarith) hA hAm; positivity
  · rw [lgrP81_eq]; have := lgrP81_pos (by linarith) (by linarith) hA hAm; positivity
  · rw [lgrP82_eq]; have := lgrP82_pos (by linarith) (by linarith) hA hAm; positivity
  · rw [lgrP83_eq]; have := lgrP83_pos (by linarith) (by linarith) hA hAm; positivity

/-- The large-shape numerator of the `2` test (`u = u_b`) as a polynomial in `β` (outer variable;
the inner lists are constants in `x`, `α`), computed from the factored formula. -/
noncomputable def lgrFL2 (x a : ℝ) : List (List ℝ) :=
  lgrNoL 504 180 0 3528 2268 7903 (-3528) [[x + 1]] [[a]] (lgrAdd2 [[a]] [[0], [1]]) [[x + 74]] [[100]]
    (lgrcD [[x]] [[a]] [[0], [1]])

theorem lgrFL2_link (x a b : ℝ) :
    lgrNo2 (x + 1) a (a + b) (x + 74) 100 (ssDg x b a) = lgrH2 (lgrFL2 x a) b 0 := by
  have h6 := lgr_H2_cD [[x]] [[a]] [[0], [1]] b 0
  unfold lgrFL2
  rw [lgr_H2_No2L, h6]
  simp [lgrH2, polyHorner, lgrAdd2, lgrAdd, Horner.add]

/-- The large-shape numerator of the `2` test is a cubic in `β`. -/
theorem lgrFL2_len (x a : ℝ) : (lgrFL2 x a).length ≤ 4 := by
  simp [lgrFL2, lgrNoL, lgrWoNL, lgrLoNL, lgrcD, lgrMul2, lgrMul, Horner.mul, lgrSmul2, lgrAdd2, lgrAdd, Horner.add, lgrSmul]

/-- `P_{20}(A, X)`, grouped by powers of `A = α - (2x + 3)/5`, with
coefficients polynomials in `X = x - 2`. -/
noncomputable def lgrP20 : List (List ℝ) :=
  [[(18899726811 / 3125), (61073422028 / 3125), (78915560957 / 3125), (11467090408 / 625), (5154135896 / 625), (7223316346 / 3125), (1113711958 / 3125), (34221132 / 3125), (-1966032 / 625)],
    [(4094457624 / 125), (2573464386 / 25), (15389659782 / 125), (9583654518 / 125), (3198300402 / 125), (501708672 / 125), (17488512 / 125), (-91152 / 5)],
    [(147190134 / 5), (2029433639 / 25), (358588221 / 5), (764343441 / 25), (151490353 / 25), (7253028 / 25), (-163404 / 5)],
    [(44441328 / 5), (129437698 / 5), (68857054 / 5), (12766486 / 5), (317682 / 5), (-19224)],
    [(-254421), 4205907, 1138263, (-42435), (-8370)],
    [(-508272), 325864, 73656, (-6480)]]

theorem lgrP20_eq (x a : ℝ) :
    lgrH2 (lgrFL2 x a) (x + (3 / 5) * (a - 1)) 0 =
      (4 / 25) * lgrH2 lgrP20 (a - (2 * x + 3) / 5) (x - 2) := by
  simp only [lgrFL2, lgrNoL, lgrWoNL, lgrLoNL, lgrcD, lgrMul2, lgrMul, Horner.mul, lgrSmul2, lgrAdd2, lgrAdd, Horner.add, lgrSmul, Horner.smul, lgrH2, List.map, polyHorner, lgrP20]
  ring

/-- **`P_{20} > 0`** on `2/5 ≤ X ≤ 7`, `0 ≤ A ≤ 3(X + 1)/5` (one sign change in `A`). -/
theorem lgrP20_pos {X A : ℝ} (hX : 2 / 5 ≤ X) (hX7 : X ≤ 7) (hA : 0 ≤ A)
    (hAm : A ≤ 3 / 5 * X + 3 / 5) : 0 < lgrH2 lgrP20 A X := by
  simp only [lgrP20]
  apply lgr_sc4 hX hX7 hA hAm
    (OneSignChange.positive_after_shift _ 7
      (by norm_num [OneSignChange.Conditions, lgrShift, Horner.shift, lgrAdd, Horner.add, lgrSmul, Horner.smul, Nat.forall_lt_succ_right,
        Nat.le_one_iff_eq_zero_or_eq_one, List.getD, polyHorner]))
    (OneSignChange.positive_after_shift _ 6
      (by norm_num [OneSignChange.Conditions, lgrShift, Horner.shift, lgrAdd, Horner.add, lgrSmul, Horner.smul, Nat.forall_lt_succ_right,
        Nat.le_one_iff_eq_zero_or_eq_one, List.getD, polyHorner]))
    (OneSignChange.positive_after_shift _ 5
      (by norm_num [OneSignChange.Conditions, lgrShift, Horner.shift, lgrAdd, Horner.add, lgrSmul, Horner.smul, Nat.forall_lt_succ_right,
        Nat.le_one_iff_eq_zero_or_eq_one, List.getD, polyHorner]))
    (OneSignChange.positive_after_shift _ 4
      (by norm_num [OneSignChange.Conditions, lgrShift, Horner.shift, lgrAdd, Horner.add, lgrSmul, Horner.smul, Nat.forall_lt_succ_right,
        Nat.le_one_iff_eq_zero_or_eq_one, List.getD, polyHorner]))
    (OneSignChange.positive_after_shift _ 2
      (by norm_num [OneSignChange.Conditions, lgrShift, Horner.shift, lgrAdd, Horner.add, lgrSmul, Horner.smul, Nat.forall_lt_succ_right,
        Nat.le_one_iff_eq_zero_or_eq_one, List.getD, polyHorner]))
    (OneSignChange.positive_after_shift _ 7
      (by norm_num [OneSignChange.Conditions, lgrShift, Horner.shift, lgrAdd, Horner.add, lgrSmul, Horner.smul, Nat.forall_lt_succ_right,
        Nat.le_one_iff_eq_zero_or_eq_one, List.getD, polyHorner, lgrSlant]))

/-- `P_{21}(A, X)`, grouped by powers of `A = α - (2x + 3)/5`, with
coefficients polynomials in `X = x - 2`. -/
noncomputable def lgrP21 : List (List ℝ) :=
  [[(38454442932 / 3125), (120202539076 / 3125), (150734863744 / 3125), (21508313708 / 625), (9677503132 / 625), (13981570652 / 3125), (2296803236 / 3125), (78379344 / 3125), (-4538592 / 625)],
    [(9126306459 / 125), (27991701651 / 125), (33487325328 / 125), (21107315862 / 125), (7168822008 / 125), (1148547156 / 125), (41479164 / 125), (-1082592 / 25)],
    [(2013683052 / 25), (5038916638 / 25), (4412520618 / 25), (1901412126 / 25), 15176486, (18131616 / 25), (-398088 / 5)],
    [29466282, (280625387 / 5), (131464958 / 5), 4661041, (451764 / 5), (-40392)],
    [2510136, 3495348, (-1160688), (-484200), 2700],
    [(-382809), (-255502), (-76923), (-2430)]]

theorem lgrP21_eq (x a : ℝ) :
    lgrH2 (lgrFL2 x a) (x + (3 / 5) * (a - 1)) 0 + ((x + (3 / 2) * (a - 1)) - (x + (3 / 5) * (a - 1))) / 3 * lgrH2 (lgrD2 (lgrFL2 x a)) (x + (3 / 5) * (a - 1)) 0 =
      (2 / 25) * lgrH2 lgrP21 (a - (2 * x + 3) / 5) (x - 2) := by
  simp only [lgrFL2, lgrNoL, lgrWoNL, lgrLoNL, lgrcD, lgrMul2, lgrMul, Horner.mul, lgrSmul2, lgrAdd2, lgrAdd, Horner.add, lgrSmul, Horner.smul, lgrD2, lgrH2, List.map, polyHorner, lgrP21]
  ring

/-- **`P_{21} > 0`** on `2/5 ≤ X ≤ 7`, `0 ≤ A ≤ 3(X + 1)/5` (one sign change in `A`). -/
theorem lgrP21_pos {X A : ℝ} (hX : 2 / 5 ≤ X) (hX7 : X ≤ 7) (hA : 0 ≤ A)
    (hAm : A ≤ 3 / 5 * X + 3 / 5) : 0 < lgrH2 lgrP21 A X := by
  simp only [lgrP21]
  apply lgr_sc3 hX hX7 hA hAm
    (OneSignChange.positive_after_shift _ 7
      (by norm_num [OneSignChange.Conditions, lgrShift, Horner.shift, lgrAdd, Horner.add, lgrSmul, Horner.smul, Nat.forall_lt_succ_right,
        Nat.le_one_iff_eq_zero_or_eq_one, List.getD, polyHorner]))
    (OneSignChange.positive_after_shift _ 6
      (by norm_num [OneSignChange.Conditions, lgrShift, Horner.shift, lgrAdd, Horner.add, lgrSmul, Horner.smul, Nat.forall_lt_succ_right,
        Nat.le_one_iff_eq_zero_or_eq_one, List.getD, polyHorner]))
    (OneSignChange.positive_after_shift _ 5
      (by norm_num [OneSignChange.Conditions, lgrShift, Horner.shift, lgrAdd, Horner.add, lgrSmul, Horner.smul, Nat.forall_lt_succ_right,
        Nat.le_one_iff_eq_zero_or_eq_one, List.getD, polyHorner]))
    (OneSignChange.positive_after_shift _ 4
      (by norm_num [OneSignChange.Conditions, lgrShift, Horner.shift, lgrAdd, Horner.add, lgrSmul, Horner.smul, Nat.forall_lt_succ_right,
        Nat.le_one_iff_eq_zero_or_eq_one, List.getD, polyHorner]))
    (OneSignChange.negative_after_shift _ 3
      (by norm_num [OneSignChange.Conditions, lgrShift, Horner.shift, lgrAdd, Horner.add, lgrSmul, Horner.smul, Nat.forall_lt_succ_right,
        Nat.le_one_iff_eq_zero_or_eq_one, List.getD, polyHorner]))
    (OneSignChange.positive_after_shift _ 7
      (by norm_num [OneSignChange.Conditions, lgrShift, Horner.shift, lgrAdd, Horner.add, lgrSmul, Horner.smul, Nat.forall_lt_succ_right,
        Nat.le_one_iff_eq_zero_or_eq_one, List.getD, polyHorner, lgrSlant]))

/-- `P_{22}(A, X)`, grouped by powers of `A = α - (2x + 3)/5`, with
coefficients polynomials in `X = x - 2`. -/
noncomputable def lgrP22 : List (List ℝ) :=
  [[(1518518874 / 625), (22750486568 / 3125), (27258468854 / 3125), (18796872596 / 3125), (336323236 / 125), (507195512 / 625), (456527248 / 3125), (17744544 / 3125), (-5215104 / 3125)],
    [(394442982 / 25), (5946164682 / 125), (7141881576 / 125), (4569374592 / 125), (1582959648 / 125), (259636632 / 125), (1951056 / 25), (-1276992 / 125)],
    [20068530, 47898452, (1056706554 / 25), (92873871 / 5), (93750691 / 25), (4482558 / 25), (-481032 / 25)],
    [7789938, (58299934 / 5), (24659173 / 5), (4270843 / 5), (50328 / 5), (-42336 / 5)],
    [2700, (-1580823), (-1323981), (-203922), 5886],
    [(-313440), (-502811), (-89343), 3078]]

theorem lgrP22_eq (x a : ℝ) :
    lgrH2 (lgrFL2 x a) (x + (3 / 2) * (a - 1)) 0 - ((x + (3 / 2) * (a - 1)) - (x + (3 / 5) * (a - 1))) / 3 * lgrH2 (lgrD2 (lgrFL2 x a)) (x + (3 / 2) * (a - 1)) 0 =
      (2 / 5) * lgrH2 lgrP22 (a - (2 * x + 3) / 5) (x - 2) := by
  simp only [lgrFL2, lgrNoL, lgrWoNL, lgrLoNL, lgrcD, lgrMul2, lgrMul, Horner.mul, lgrSmul2, lgrAdd2, lgrAdd, Horner.add, lgrSmul, Horner.smul, lgrD2, lgrH2, List.map, polyHorner, lgrP22]
  ring

/-- **`P_{22} > 0`** on `2/5 ≤ X ≤ 7`, `0 ≤ A ≤ 3(X + 1)/5` (one sign change in `A`). -/
theorem lgrP22_pos {X A : ℝ} (hX : 2 / 5 ≤ X) (hX7 : X ≤ 7) (hA : 0 ≤ A)
    (hAm : A ≤ 3 / 5 * X + 3 / 5) : 0 < lgrH2 lgrP22 A X := by
  simp only [lgrP22]
  apply lgr_sc3 hX hX7 hA hAm
    (OneSignChange.positive_after_shift _ 7
      (by norm_num [OneSignChange.Conditions, lgrShift, Horner.shift, lgrAdd, Horner.add, lgrSmul, Horner.smul, Nat.forall_lt_succ_right,
        Nat.le_one_iff_eq_zero_or_eq_one, List.getD, polyHorner]))
    (OneSignChange.positive_after_shift _ 6
      (by norm_num [OneSignChange.Conditions, lgrShift, Horner.shift, lgrAdd, Horner.add, lgrSmul, Horner.smul, Nat.forall_lt_succ_right,
        Nat.le_one_iff_eq_zero_or_eq_one, List.getD, polyHorner]))
    (OneSignChange.positive_after_shift _ 5
      (by norm_num [OneSignChange.Conditions, lgrShift, Horner.shift, lgrAdd, Horner.add, lgrSmul, Horner.smul, Nat.forall_lt_succ_right,
        Nat.le_one_iff_eq_zero_or_eq_one, List.getD, polyHorner]))
    (OneSignChange.positive_after_shift _ 3
      (by norm_num [OneSignChange.Conditions, lgrShift, Horner.shift, lgrAdd, Horner.add, lgrSmul, Horner.smul, Nat.forall_lt_succ_right,
        Nat.le_one_iff_eq_zero_or_eq_one, List.getD, polyHorner]))
    (OneSignChange.negative_after_shift _ 2
      (by norm_num [OneSignChange.Conditions, lgrShift, Horner.shift, lgrAdd, Horner.add, lgrSmul, Horner.smul, Nat.forall_lt_succ_right,
        Nat.le_one_iff_eq_zero_or_eq_one, List.getD, polyHorner]))
    (OneSignChange.positive_after_shift _ 7
      (by norm_num [OneSignChange.Conditions, lgrShift, Horner.shift, lgrAdd, Horner.add, lgrSmul, Horner.smul, Nat.forall_lt_succ_right,
        Nat.le_one_iff_eq_zero_or_eq_one, List.getD, polyHorner, lgrSlant]))

/-- `P_{23}(A, X)`, grouped by powers of `A = α - (2x + 3)/5`, with
coefficients polynomials in `X = x - 2`. -/
noncomputable def lgrP23 : List (List ℝ) :=
  [[(57947736 / 125), (817765436 / 625), (181183108 / 125), (580373456 / 625), (50533736 / 125), (16388096 / 125), (17161936 / 625), (6336 / 5), (-238464 / 625)],
    [(83002149 / 25), (1234959429 / 125), (1492516152 / 125), (971061714 / 125), (343649076 / 125), (57831624 / 125), (90864 / 5), (-298944 / 125)],
    [(23676342 / 5), (276561958 / 25), (248440686 / 25), (111845277 / 25), 915329, (1094508 / 25), (-115128 / 25)],
    [1884972, (12081146 / 5), (4832966 / 5), (850973 / 5), (2187 / 5), (-8856 / 5)],
    [(-319950), (-1031463), (-564045), (-67644), 2538],
    [(-242625), (-265690), (-38745), 1620]]

theorem lgrP23_eq (x a : ℝ) :
    lgrH2 (lgrFL2 x a) (x + (3 / 2) * (a - 1)) 0 =
      2 * lgrH2 lgrP23 (a - (2 * x + 3) / 5) (x - 2) := by
  simp only [lgrFL2, lgrNoL, lgrWoNL, lgrLoNL, lgrcD, lgrMul2, lgrMul, Horner.mul, lgrSmul2, lgrAdd2, lgrAdd, Horner.add, lgrSmul, Horner.smul, lgrH2, List.map, polyHorner, lgrP23]
  ring

/-- **`P_{23} > 0`** on `2/5 ≤ X ≤ 7`, `0 ≤ A ≤ 3(X + 1)/5` (one sign change in `A`). -/
theorem lgrP23_pos {X A : ℝ} (hX : 2 / 5 ≤ X) (hX7 : X ≤ 7) (hA : 0 ≤ A)
    (hAm : A ≤ 3 / 5 * X + 3 / 5) : 0 < lgrH2 lgrP23 A X := by
  simp only [lgrP23]
  apply lgr_sc3 hX hX7 hA hAm
    (OneSignChange.positive_after_shift _ 7
      (by norm_num [OneSignChange.Conditions, lgrShift, Horner.shift, lgrAdd, Horner.add, lgrSmul, Horner.smul, Nat.forall_lt_succ_right,
        Nat.le_one_iff_eq_zero_or_eq_one, List.getD, polyHorner]))
    (OneSignChange.positive_after_shift _ 6
      (by norm_num [OneSignChange.Conditions, lgrShift, Horner.shift, lgrAdd, Horner.add, lgrSmul, Horner.smul, Nat.forall_lt_succ_right,
        Nat.le_one_iff_eq_zero_or_eq_one, List.getD, polyHorner]))
    (OneSignChange.positive_after_shift _ 5
      (by norm_num [OneSignChange.Conditions, lgrShift, Horner.shift, lgrAdd, Horner.add, lgrSmul, Horner.smul, Nat.forall_lt_succ_right,
        Nat.le_one_iff_eq_zero_or_eq_one, List.getD, polyHorner]))
    (OneSignChange.positive_after_shift _ 3
      (by norm_num [OneSignChange.Conditions, lgrShift, Horner.shift, lgrAdd, Horner.add, lgrSmul, Horner.smul, Nat.forall_lt_succ_right,
        Nat.le_one_iff_eq_zero_or_eq_one, List.getD, polyHorner]))
    (OneSignChange.negative_after_shift _ 2
      (by norm_num [OneSignChange.Conditions, lgrShift, Horner.shift, lgrAdd, Horner.add, lgrSmul, Horner.smul, Nat.forall_lt_succ_right,
        Nat.le_one_iff_eq_zero_or_eq_one, List.getD, polyHorner]))
    (OneSignChange.positive_after_shift _ 7
      (by norm_num [OneSignChange.Conditions, lgrShift, Horner.shift, lgrAdd, Horner.add, lgrSmul, Horner.smul, Nat.forall_lt_succ_right,
        Nat.le_one_iff_eq_zero_or_eq_one, List.getD, polyHorner, lgrSlant]))

/-- **The large shapes, `2` test**: the cleared numerator at `u = u_b` is positive for
`(2x + 3)/5 ≤ α ≤ x` and `x + (3/5)(α - 1) ≤ β ≤ x + (3/2)(α - 1)`. -/
theorem lgr_large2 {x a b : ℝ} (hx : 12 / 5 ≤ x) (hx9 : x ≤ 9) (ham : (2 * x + 3) / 5 ≤ a)
    (hax : a ≤ x) (hb : x + 3 / 5 * (a - 1) ≤ b) (hb' : b ≤ x + 3 / 2 * (a - 1)) :
    0 < lgrNo2 (x + 1) a (a + b) (x + 74) 100 (ssDg x b a) := by
  rw [lgrFL2_link]
  have hA : 0 ≤ a - (2 * x + 3) / 5 := by linarith
  have hAm : a - (2 * x + 3) / 5 ≤ 3 / 5 * (x - 2) + 3 / 5 := by linarith
  apply lgr_cubic_list _ (lgrFL2_len x a) (p := (x + (3 / 5) * (a - 1))) (q := (x + (3 / 2) * (a - 1))) (by nlinarith) (by linarith) (by linarith)
  · rw [lgrP20_eq]; have := lgrP20_pos (by linarith) (by linarith) hA hAm; positivity
  · rw [lgrP21_eq]; have := lgrP21_pos (by linarith) (by linarith) hA hAm; positivity
  · rw [lgrP22_eq]; have := lgrP22_pos (by linarith) (by linarith) hA hAm; positivity
  · rw [lgrP23_eq]; have := lgrP23_pos (by linarith) (by linarith) hA hAm; positivity

end SmoothedOctagon
