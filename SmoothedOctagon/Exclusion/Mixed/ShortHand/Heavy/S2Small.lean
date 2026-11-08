module

public import SmoothedOctagon.Exclusion.Mixed.ShortHand.Heavy.S2Face
public import SmoothedOctagon.Exclusion.Mixed.ShortHand.Heavy.S2SmallLinkA
public import SmoothedOctagon.Exclusion.Mixed.ShortHand.Heavy.S2SmallLinkB

/-!
# S2 heavy face signs: the outer face for small `α`

`hs2_outer_sign_small_proof` proves the statement of `hs2_outer_sign_small`
(`OUTER_RATIO_HAND_SIGN` §§4-5, (13), (16); inventory HS-S2 R24): for `13/6 ≤ x ≤ 12/5`,
`1 ≤ α ≤ 3/2`, `α ≤ x`, `x(x + 2) ≤ 6α²`, `β` in the strip, `q = 1/7`, `u = u_s(x, β)` and
`2 ≤ τ ≤ 7r_A`, `G_τ < 0`.

Proof: `hh2_hsF_face` and `hh2_tau_outer` reduce to `H₀ = G₂ < 0` and
`H₁ = G₂ + (T - 2)A < 0`; the log majorant `hh2_log_le_bound` makes both rational; on the enlarged
set `α ≥ a_f(x) = (36x + 25)/84` (`OUTER_RATIO_HAND_SIGN` (7)) and
`5/8 ≤ c ≤ c₊(x) = (24x + 51)/128` (`CENTRAL_RATIO_HAND_SIGN` (6)), `c = (β - x)/(α - 1)`, their
cleared numerators are `hh2SmQA`, `hh2SmQB`, positive by `Heavy/S2SmallShift`.

Denominators are cleared in two stages: `hh2_sm_stage1_*` (the face in abstract atoms) and
`hh2_sm_stage2_*` (`Heavy/S2SmallLinkA`, `-B`: the expansion of the atom polynomials).

Route: the notes' monotonicities in `α` (App. A, `A₀`, `A₁`) and `c` (`C₀`, `C₁`) and the terminal
univariate signs (App. B) are replaced by nested Bernstein certificates in `(c, s, x)`,
`s = α - a_f(x)`, on two `x`-boxes (`H₀`) and one box (`H₁`).

## Main API

* `hh2_af_le`, `hh2_strip_cplus`: the enlarged coordinates.
* `hh2_small_H0`, `hh2_small_H1`: the two duration-free signs.
* `hs2_outer_sign_small_proof`.
-/

@[expose] public section

namespace SmoothedOctagon

open Real

/-- `a_f(x) = (36x + 25)/84 ≤ α` when `x(x + 2) ≤ 6α²` (`OUTER_RATIO_HAND_SIGN` (7):
`84²x(x + 2) - 6(36x + 25)² = -720x² + 3312x - 3750 > 0` on `[13/6, 12/5]`). -/
theorem hh2_af_le {x al : ℝ} (hx : 13 / 6 ≤ x) (hx2 : x ≤ 12 / 5) (hal : 1 ≤ al)
    (hqc : x * (x + 2) ≤ 6 * al ^ 2) : (36 * x + 25) / 84 ≤ al := by
  have h1 : 6 * ((36 * x + 25) / 84) ^ 2 ≤ x * (x + 2) := by
    nlinarith [mul_nonneg (sub_nonneg.2 hx) (sub_nonneg.2 hx2)]
  have h2 : ((36 * x + 25) / 84) ^ 2 ≤ al ^ 2 := by linarith
  have h3 : 0 ≤ (36 * x + 25) / 84 := by positivity
  nlinarith [sq_nonneg ((36 * x + 25) / 84 - al), sq_nonneg ((36 * x + 25) / 84 + al)]

/-- The strip coordinate with the upper end `c₊(x) = (24x + 51)/128` (`CENTRAL_RATIO_HAND_SIGN` (6):
`96x³ - 428x² + 457x + 51 > 0`). -/
theorem hh2_strip_cplus {x al be : ℝ} (hx : 13 / 6 ≤ x) (hx2 : x ≤ 12 / 5) (hal : 1 < al)
    (hb : x + 8 * x * (al - 1) / (9 * x + 8) ≤ be)
    (hb' : be ≤ x + x * (7 * x + 1) * (al - 1) / (4 * x ^ 2 + 11 * x + 1)) :
    ∃ c : ℝ, 5 / 8 ≤ c ∧ c ≤ (24 * x + 51) / 128 ∧ be = x + c * (al - 1) := by
  have ha : 0 < al - 1 := by linarith
  refine ⟨(be - x) / (al - 1), ?_, ?_, ?_⟩
  · rw [le_div_iff₀ ha]
    have h1 : 5 / 8 * (al - 1) ≤ 8 * x * (al - 1) / (9 * x + 8) := by
      rw [le_div_iff₀ (by linarith)]
      nlinarith
    linarith
  · rw [div_le_iff₀ ha]
    have h1 : x * (7 * x + 1) * (al - 1) / (4 * x ^ 2 + 11 * x + 1) ≤ (24 * x + 51) / 128 * (al - 1) := by
      rw [div_le_iff₀ (by positivity)]
      have hq : 0 ≤ (24 * x + 51) * (4 * x ^ 2 + 11 * x + 1) - 128 * x * (7 * x + 1) := by
        nlinarith [mul_nonneg (sub_nonneg.2 hx) (sub_nonneg.2 hx2), sq_nonneg (x - 9 / 4),
          mul_nonneg (mul_nonneg (sub_nonneg.2 hx) (sub_nonneg.2 hx)) (sub_nonneg.2 hx)]
      nlinarith [mul_nonneg ha.le hq]
    linarith
  · field_simp
    ring

/-- **Stage 1 for `H₀`** (abstract atoms `S, D, B, α, u`): `H₀ · α⁵BS = Π₀ + uΠ₁`. -/
theorem hh2_sm_stage1_H0 (S D B a u : ℝ) (hS : S ≠ 0) (ha : a ≠ 0) (hB : B ≠ 0) :
    ((((6 * a ^ 2 + 1) ^ 2 - (6 * a ^ 2 + 1) * S + S ^ 2 + D ^ 2 * u - D * ((6 * a ^ 2 + 1) * (S * (u - 1) + 1 / S) + 2 * S - 1)) / (49 * a ^ 4) - 1) * 2 + 1 / 2 + ((u - 1) / (a / B) + a / B + 1 - 1 / 7 - (2 * D * u - ((6 * a ^ 2 + 1) * (S * (u - 1) + 1 / S) + 2 * S - 1)) / (7 * a ^ 2)) + (-296 / 1029 + (4 * (2 * (1 / 7 / (a / B))) / 3 - 1) - (4 * (2 * (1 / 7 / (a / B))) / 3 - 1) ^ 2 / 2 + (4 * (2 * (1 / 7 / (a / B))) / 3 - 1) ^ 3 / 3) + (2 - 7 * 2 * (1 / 7 / (a / B)) / 4) * (((6 * a ^ 2 + 1) ^ 2 - (6 * a ^ 2 + 1) * S + S ^ 2 + D ^ 2 * u - D * ((6 * a ^ 2 + 1) * (S * (u - 1) + 1 / S) + 2 * S - 1)) / (49 * a ^ 4) - 3 / 4)) * (a ^ 5 * B * S) =
      512*(B) ^ (4 : ℕ)*(S)*(a) ^ (2 : ℕ)/27783 - 32*(B) ^ (3 : ℕ)*(S)*(a) ^ (3 : ℕ)/147 - 3*(B) ^ (2 : ℕ)*(D)*(S) ^ (2 : ℕ)*(a) ^ (2 : ℕ)/49 + (B) ^ (2 : ℕ)*(D)*(S) ^ (2 : ℕ)/98 - (B) ^ (2 : ℕ)*(D)*(S)/98 + 3*(B) ^ (2 : ℕ)*(D)*(a) ^ (2 : ℕ)/49 + (B) ^ (2 : ℕ)*(D)/98 - (B) ^ (2 : ℕ)*(S) ^ (3 : ℕ)/98 + 3*(B) ^ (2 : ℕ)*(S) ^ (2 : ℕ)*(a) ^ (2 : ℕ)/49 + (B) ^ (2 : ℕ)*(S) ^ (2 : ℕ)/98 + 59*(B) ^ (2 : ℕ)*(S)*(a) ^ (4 : ℕ)/392 - 6*(B) ^ (2 : ℕ)*(S)*(a) ^ (2 : ℕ)/49 - (B) ^ (2 : ℕ)*(S)/98 + 24*(B)*(D)*(S) ^ (2 : ℕ)*(a) ^ (3 : ℕ)/49 - 4*(B)*(D)*(S) ^ (2 : ℕ)*(a)/49 + 4*(B)*(D)*(S)*(a)/49 - 24*(B)*(D)*(a) ^ (3 : ℕ)/49 - 4*(B)*(D)*(a)/49 + 4*(B)*(S) ^ (3 : ℕ)*(a)/49 - 6*(B)*(S) ^ (2 : ℕ)*(a) ^ (5 : ℕ)/7 - 17*(B)*(S) ^ (2 : ℕ)*(a) ^ (3 : ℕ)/49 - 4*(B)*(S) ^ (2 : ℕ)*(a)/49 - 909*(B)*(S)*(a) ^ (5 : ℕ)/686 + 41*(B)*(S)*(a) ^ (3 : ℕ)/49 + 4*(B)*(S)*(a)/49 + 6*(B)*(a) ^ (5 : ℕ)/7 + (B)*(a) ^ (3 : ℕ)/7 + (S)*(a) ^ (6 : ℕ) + u * (-(B) ^ (2 : ℕ)*(D) ^ (2 : ℕ)*(S)/98 + 3*(B) ^ (2 : ℕ)*(D)*(S) ^ (2 : ℕ)*(a) ^ (2 : ℕ)/49 + (B) ^ (2 : ℕ)*(D)*(S) ^ (2 : ℕ)/98 + (B) ^ (2 : ℕ)*(S)*(a) ^ (4 : ℕ) + 4*(B)*(D) ^ (2 : ℕ)*(S)*(a)/49 - 24*(B)*(D)*(S) ^ (2 : ℕ)*(a) ^ (3 : ℕ)/49 - 4*(B)*(D)*(S) ^ (2 : ℕ)*(a)/49 - 2*(B)*(D)*(S)*(a) ^ (3 : ℕ)/7 + 6*(B)*(S) ^ (2 : ℕ)*(a) ^ (5 : ℕ)/7 + (B)*(S) ^ (2 : ℕ)*(a) ^ (3 : ℕ)/7) := by
  field_simp
  ring

/-- **Stage 1 for `H₁`**: `H₁ · α⁵BS = Π₀ + uΠ₁`. -/
theorem hh2_sm_stage1_H1 (S D B a u : ℝ) (hS : S ≠ 0) (ha : a ≠ 0) (hB : B ≠ 0) :
    ((((6 * a ^ 2 + 1) ^ 2 - (6 * a ^ 2 + 1) * S + S ^ 2 + D ^ 2 * u - D * ((6 * a ^ 2 + 1) * (S * (u - 1) + 1 / S) + 2 * S - 1)) / (49 * a ^ 4) - 1) * 2 + 1 / 2 + ((u - 1) / (a / B) + a / B + 1 - 1 / 7 - (2 * D * u - ((6 * a ^ 2 + 1) * (S * (u - 1) + 1 / S) + 2 * S - 1)) / (7 * a ^ 2)) + (-296 / 1029 + (4 * (2 * (1 / 7 / (a / B))) / 3 - 1) - (4 * (2 * (1 / 7 / (a / B))) / 3 - 1) ^ 2 / 2 + (4 * (2 * (1 / 7 / (a / B))) / 3 - 1) ^ 3 / 3) + (2 - 7 * 2 * (1 / 7 / (a / B)) / 4) * (((6 * a ^ 2 + 1) ^ 2 - (6 * a ^ 2 + 1) * S + S ^ 2 + D ^ 2 * u - D * ((6 * a ^ 2 + 1) * (S * (u - 1) + 1 / S) + 2 * S - 1)) / (49 * a ^ 4) - 3 / 4) + (1 / (1 / 7 / (a / B)) - 2) * ((1 - 7 * (1 / 7 / (a / B)) / 4) * (((6 * a ^ 2 + 1) ^ 2 - (6 * a ^ 2 + 1) * S + S ^ 2 + D ^ 2 * u - D * ((6 * a ^ 2 + 1) * (S * (u - 1) + 1 / S) + 2 * S - 1)) / (49 * a ^ 4) - 3 / 4))) * (a ^ 5 * B * S) =
      512*(B) ^ (4 : ℕ)*(S)*(a) ^ (2 : ℕ)/27783 - 32*(B) ^ (3 : ℕ)*(S)*(a) ^ (3 : ℕ)/147 + (B) ^ (2 : ℕ)*(S)*(a) ^ (4 : ℕ)/7 + 3*(B)*(D)*(S) ^ (2 : ℕ)*(a) ^ (3 : ℕ)/98 - (B)*(D)*(S) ^ (2 : ℕ)*(a)/196 + (B)*(D)*(S)*(a)/196 - 3*(B)*(D)*(a) ^ (3 : ℕ)/98 - (B)*(D)*(a)/196 + (B)*(S) ^ (3 : ℕ)*(a)/196 - 6*(B)*(S) ^ (2 : ℕ)*(a) ^ (5 : ℕ)/7 + 11*(B)*(S) ^ (2 : ℕ)*(a) ^ (3 : ℕ)/98 - (B)*(S) ^ (2 : ℕ)*(a)/196 - 6957*(B)*(S)*(a) ^ (5 : ℕ)/5488 - 4*(B)*(S)*(a) ^ (3 : ℕ)/49 + (B)*(S)*(a)/196 + 6*(B)*(a) ^ (5 : ℕ)/7 + (B)*(a) ^ (3 : ℕ)/7 + 6*(D)*(S) ^ (2 : ℕ)*(a) ^ (4 : ℕ)/7 - (D)*(S) ^ (2 : ℕ)*(a) ^ (2 : ℕ)/7 + (D)*(S)*(a) ^ (2 : ℕ)/7 - 6*(D)*(a) ^ (4 : ℕ)/7 - (D)*(a) ^ (2 : ℕ)/7 + (S) ^ (3 : ℕ)*(a) ^ (2 : ℕ)/7 - 6*(S) ^ (2 : ℕ)*(a) ^ (4 : ℕ)/7 - (S) ^ (2 : ℕ)*(a) ^ (2 : ℕ)/7 + 25*(S)*(a) ^ (6 : ℕ)/28 + 12*(S)*(a) ^ (4 : ℕ)/7 + (S)*(a) ^ (2 : ℕ)/7 + u * ((B) ^ (2 : ℕ)*(S)*(a) ^ (4 : ℕ) + (B)*(D) ^ (2 : ℕ)*(S)*(a)/196 - 3*(B)*(D)*(S) ^ (2 : ℕ)*(a) ^ (3 : ℕ)/98 - (B)*(D)*(S) ^ (2 : ℕ)*(a)/196 - 2*(B)*(D)*(S)*(a) ^ (3 : ℕ)/7 + 6*(B)*(S) ^ (2 : ℕ)*(a) ^ (5 : ℕ)/7 + (B)*(S) ^ (2 : ℕ)*(a) ^ (3 : ℕ)/7 + (D) ^ (2 : ℕ)*(S)*(a) ^ (2 : ℕ)/7 - 6*(D)*(S) ^ (2 : ℕ)*(a) ^ (4 : ℕ)/7 - (D)*(S) ^ (2 : ℕ)*(a) ^ (2 : ℕ)/7) := by
  field_simp
  ring

/-- `u_s · U_d = U_n`. -/
theorem hh2_sm_us (x be : ℝ) (hS : 1 + x ≠ 0) (hb : be - 1 ≠ 0) :
    hsUs x be * (1200 * (1 + x) ^ 2 * (be - 1)) = (900 * (1 + x) ^ 2 * (be - 1) + 85 * (x - 1) ^ 3 + (1 + x) ^ 2 * (be - x)) := by
  unfold hsUs
  field_simp
  ring

/-- **Recombination**: `E · M = Π₀ + uΠ₁`, `uU_d = U_n` and `Π₀U_d + Π₁U_n = R < 0` give `E < 0`. -/
theorem hh2_combine1 {E M Ud u Un P0 P1 R : ℝ} (hM : 0 < M) (hUd : 0 < Ud)
    (hG : E * M = P0 + u * P1) (hu : u * Ud = Un) (h2 : P0 * Ud + P1 * Un = R) (hR : R < 0) : E < 0 := by
  have key : E * (M * Ud) = -(-R) := by linear_combination Ud * hG + P1 * hu + h2
  exact hh2_neg_of_mul (by positivity) (by linarith) key

/-- The small outer face: `H₀ = G₂ < 0` for any `ℓ` below the log majorant (`hh2SmQA_pos`). -/
theorem hh2_small_H0 {x al c be : ℝ} (hx : 13 / 6 ≤ x) (hx2 : x ≤ 12 / 5) (hal : (36 * x + 25) / 84 ≤ al)
    (hal' : al ≤ 3 / 2) (hc1 : 5 / 8 ≤ c) (hc2 : c ≤ (24 * x + 51) / 128) (hbe : be = x + c * (al - 1))
    (ℓ : ℝ) (hℓ : ℓ ≤ (-296 / 1029 + (4 * (2 * (1 / 7 / hsRA al be)) / 3 - 1) - (4 * (2 * (1 / 7 / hsRA al be)) / 3 - 1) ^ 2 / 2 + (4 * (2 * (1 / 7 / hsRA al be)) / 3 - 1) ^ 3 / 3)) :
    (hsWs x be al (hsUs x be) (1 / 7) - 1) * 2 + 1 / 2 + ((hsUs x be - 1) / hsRA al be + hsRA al be + 1 - 1 / 7 - hsELs x be al (hsUs x be) (1 / 7)) + ℓ + (2 - 7 * 2 * (1 / 7 / hsRA al be) / 4) * (hsWs x be al (hsUs x be) (1 / 7) - 3 / 4) < 0 := by
  calc _ ≤ (hsWs x be al (hsUs x be) (1 / 7) - 1) * 2 + 1 / 2 + ((hsUs x be - 1) / hsRA al be + hsRA al be + 1 - 1 / 7 - hsELs x be al (hsUs x be) (1 / 7)) + (-296 / 1029 + (4 * (2 * (1 / 7 / hsRA al be)) / 3 - 1) - (4 * (2 * (1 / 7 / hsRA al be)) / 3 - 1) ^ 2 / 2 + (4 * (2 * (1 / 7 / hsRA al be)) / 3 - 1) ^ 3 / 3) + (2 - 7 * 2 * (1 / 7 / hsRA al be) / 4) * (hsWs x be al (hsUs x be) (1 / 7) - 3 / 4) := by gcongr
    _ < 0 := by
      have hP := hh2SmQA_pos c al x hx hx2 hal hal' hc1 hc2
      have hal0 : 0 < al := by linarith
      have hbe1 : 0 < be - 1 := by
        rw [hbe]
        have : 0 ≤ c * (al - 1) := mul_nonneg (by linarith) (by linarith)
        linarith
      have hB : 0 < al + be := by linarith
      have hS : (0 : ℝ) < 1 + x := by linarith
      rw [hh2_Ws_outer _ _ _ _ hal0.ne' hS.ne', hh2_ELs_outer _ _ _ _ hal0.ne' hS.ne']
      unfold hsRA
      exact hh2_combine1 (M := al ^ 5 * (al + be) * (1 + x)) (Ud := (1200 * (1 + x) ^ 2 * (be - 1))) (by positivity) (by positivity)
        (hh2_sm_stage1_H0 (1 + x) (hsDg x be al) (al + be) al (hsUs x be) hS.ne' hal0.ne' hB.ne')
        (hh2_sm_us x be hS.ne' hbe1.ne') (hh2_sm_stage2_H0 x al c be hbe)
        (by have : 0 < (1 + x) * hh2SmQA c al x := by positivity
            linarith)

/-- The small outer face: `H₁ = G₂ + (T - 2)A < 0` for any `ℓ` below the log majorant
(`hh2SmQB_pos`). -/
theorem hh2_small_H1 {x al c be : ℝ} (hx : 13 / 6 ≤ x) (hx2 : x ≤ 12 / 5) (hal : (36 * x + 25) / 84 ≤ al)
    (hal' : al ≤ 3 / 2) (hc1 : 5 / 8 ≤ c) (hc2 : c ≤ (24 * x + 51) / 128) (hbe : be = x + c * (al - 1))
    (ℓ : ℝ) (hℓ : ℓ ≤ (-296 / 1029 + (4 * (2 * (1 / 7 / hsRA al be)) / 3 - 1) - (4 * (2 * (1 / 7 / hsRA al be)) / 3 - 1) ^ 2 / 2 + (4 * (2 * (1 / 7 / hsRA al be)) / 3 - 1) ^ 3 / 3)) :
    (hsWs x be al (hsUs x be) (1 / 7) - 1) * 2 + 1 / 2 + ((hsUs x be - 1) / hsRA al be + hsRA al be + 1 - 1 / 7 - hsELs x be al (hsUs x be) (1 / 7)) + ℓ + (2 - 7 * 2 * (1 / 7 / hsRA al be) / 4) * (hsWs x be al (hsUs x be) (1 / 7) - 3 / 4) +
      (1 / (1 / 7 / hsRA al be) - 2) * ((1 - 7 * (1 / 7 / hsRA al be) / 4) * (hsWs x be al (hsUs x be) (1 / 7) - 3 / 4)) < 0 := by
  calc _ ≤ (hsWs x be al (hsUs x be) (1 / 7) - 1) * 2 + 1 / 2 + ((hsUs x be - 1) / hsRA al be + hsRA al be + 1 - 1 / 7 - hsELs x be al (hsUs x be) (1 / 7)) + (-296 / 1029 + (4 * (2 * (1 / 7 / hsRA al be)) / 3 - 1) - (4 * (2 * (1 / 7 / hsRA al be)) / 3 - 1) ^ 2 / 2 + (4 * (2 * (1 / 7 / hsRA al be)) / 3 - 1) ^ 3 / 3) + (2 - 7 * 2 * (1 / 7 / hsRA al be) / 4) * (hsWs x be al (hsUs x be) (1 / 7) - 3 / 4) +
      (1 / (1 / 7 / hsRA al be) - 2) * ((1 - 7 * (1 / 7 / hsRA al be) / 4) * (hsWs x be al (hsUs x be) (1 / 7) - 3 / 4)) := by gcongr
    _ < 0 := by
      have hP := hh2SmQB_pos c al x hx hx2 hal hal' hc1 hc2
      have hal0 : 0 < al := by linarith
      have hbe1 : 0 < be - 1 := by
        rw [hbe]
        have : 0 ≤ c * (al - 1) := mul_nonneg (by linarith) (by linarith)
        linarith
      have hB : 0 < al + be := by linarith
      have hS : (0 : ℝ) < 1 + x := by linarith
      rw [hh2_Ws_outer _ _ _ _ hal0.ne' hS.ne', hh2_ELs_outer _ _ _ _ hal0.ne' hS.ne']
      unfold hsRA
      exact hh2_combine1 (M := al ^ 5 * (al + be) * (1 + x)) (Ud := (1200 * (1 + x) ^ 2 * (be - 1))) (by positivity) (by positivity)
        (hh2_sm_stage1_H1 (1 + x) (hsDg x be al) (al + be) al (hsUs x be) hS.ne' hal0.ne' hB.ne')
        (hh2_sm_us x be hS.ne' hbe1.ne') (hh2_sm_stage2_H1 x al c be hbe)
        (by have : 0 < (al * (1 + x)) * hh2SmQB c al x := by positivity
            linarith)

/-- **The outer sharp-ratio face, small `α`** (`hs2_outer_sign_small`). -/
theorem hs2_outer_sign_small_proof {x al be τ : ℝ} (hx : 13 / 6 ≤ x) (hx2 : x ≤ 12 / 5) (hal : 1 ≤ al)
    (hal' : al ≤ 3 / 2) (_hax : al ≤ x) (hqc : x * (x + 2) ≤ 6 * al ^ 2)
    (hb : x + 8 * x * (al - 1) / (9 * x + 8) ≤ be)
    (hb' : be ≤ x + x * (7 * x + 1) * (al - 1) / (4 * x ^ 2 + 11 * x + 1)) (hτ : 2 ≤ τ)
    (hτT : τ ≤ 7 * hsRA al be) :
    hsF x be al (hsUs x be) (1 / 7) τ (log (τ * (1 / 7) / hsRA al be))
      (2 - 7 * τ * (1 / 7) / (4 * hsRA al be)) < 0 := by
  have haf := hh2_af_le hx hx2 hal hqc
  obtain ⟨c, hc1, hc2, hbe⟩ := hh2_strip_cplus hx hx2 (by linarith) hb hb'
  have hal0 : 0 < al := by linarith
  have hB : 0 < al + be := by rw [hbe]; nlinarith
  have hrA : 0 < hsRA al be := by unfold hsRA; positivity
  have hk : 0 < 1 / 7 / hsRA al be := by positivity
  have hτk : τ * (1 / 7 / hsRA al be) ≤ 1 := by
    rw [mul_div_assoc', div_le_one hrA]
    linarith
  rw [hh2_hsF_face]
  have hl := hh2_log_le_bound (y := 2 * (1 / 7 / hsRA al be)) (by positivity)
  refine lt_of_le_of_lt (hh2_tau_outer hk hτ hτk) (max_lt ?_ ?_)
  · exact hh2_small_H0 hx hx2 haf hal' hc1 hc2 hbe _ hl
  · exact hh2_small_H1 hx hx2 haf hal' hc1 hc2 hbe _ hl

end SmoothedOctagon
