import sys, re, os
from fractions import Fraction as Fr
from leangen import lnum, emit_leaf
from cen_common import LINES, BPS
from common import OUT as _OUT
D_=_OUT+'/'
from gen_central import UdL, UnL, MLx
u="hsUC x be"; q="hsQc x al"
W=f"hsWs x be al ({u}) ({q})"; EL=f"hsELs x be al ({u}) ({q})"; rA="hsRA al be"
k=f"({q} / {rA})"
cc=f"(({u} - 1) / {rA} + {rA} + 1 - {q} - {EL})"
LB=f"(-296 / 1029 + (4 * (2 * {k}) / 3 - 1) - (4 * (2 * {k}) / 3 - 1) ^ 2 / 2 + (4 * (2 * {k}) / 3 - 1) ^ 3 / 3)"
def G2(l): return f"({W} - 1) * 2 + 1 / 2 + {cc} + {l} + (2 - 7 * 2 * {k} / 4) * ({W} - 3 / 4)"
Aexp=f"((1 - 7 * {k} / 4) * ({W} - 3 / 4))"
def lin(i): 
    al,be=LINES[i]; return f"({lnum(al)} + {lnum(be)} * {Aexp})"
out=[]
# ---- chord endpoint leaves
def pcoef(al,be,A):
    c0=al+be*A+2*A; c1=-A
    return [Fr(-8),Fr(12),12*c0-6,12*c1+1]
def pstr(al,be,A):
    return f"12 * τ ^ 2 * ({lnum(al)} + {lnum(be)} * {lnum(A)} - (τ - 2) * {lnum(A)}) + (τ - 2) ^ 3"
leafname={}
for i in [1,2,3,4]:
    al,be=LINES[i]
    ends=[BPS[i-1],BPS[i]] if i<4 else [BPS[3]]
    for A in ends:
        if A==0: continue
        nm=f"hh2_chord_e{i}_{len(leafname)}"
        npc,nm2=emit_leaf(out,nm,pcoef(al,be,A),Fr(2),Fr(7,2),'τ',pstr(al,be,A),None)
        leafname[(i,A)]=nm2
chords=[]
# line 0
chords.append(f'''/-- Chord 0 (`A ≤ 0`). -/
theorem hh2_chord0 {{τ A : ℝ}} (h2 : 2 ≤ τ) (hA : A ≤ 0) :
    (τ - 2) * A - (τ - 2) ^ 3 / (12 * τ ^ 2) ≤ {lnum(LINES[0][0])} + {lnum(LINES[0][1])} * A := by
  have h1 : (τ - 2) * A ≤ 0 := mul_nonpos_of_nonneg_of_nonpos (by linarith) hA
  have h3 : 0 ≤ (τ - 2) ^ 3 / (12 * τ ^ 2) := by
    have : 0 ≤ τ - 2 := by linarith
    positivity
  linarith
''')
for i in [1,2,3]:
    al,be=LINES[i]; Alo,Ahi=BPS[i-1],BPS[i]
    if Alo==0:
        e0=f"have e0 : (0 : ℝ) ≤ (τ - 2) ^ 3 := pow_nonneg (by linarith) 3"
        p0="(τ - 2) ^ 3"
    else:
        e0=f"have e0 := ({leafname[(i,Alo)]} τ h2 h7).le"
        p0=pstr(al,be,Alo)
    e1=f"have e1 := ({leafname[(i,Ahi)]} τ h2 h7).le"
    p1=pstr(al,be,Ahi)
    chords.append(f'''/-- Chord {i} (`{Alo} ≤ A ≤ {Ahi}`). -/
theorem hh2_chord{i} {{τ A : ℝ}} (h2 : 2 ≤ τ) (h7 : τ ≤ 7 / 2) (hA0 : {lnum(Alo)} ≤ A) (hA1 : A ≤ {lnum(Ahi)}) :
    (τ - 2) * A - (τ - 2) ^ 3 / (12 * τ ^ 2) ≤ {lnum(al)} + {lnum(be)} * A := by
  {e0}
  {e1}
  have hτ2 : 0 < 12 * τ ^ 2 := by positivity
  have key : 0 ≤ 12 * τ ^ 2 * ({lnum(al)} + {lnum(be)} * A - (τ - 2) * A) + (τ - 2) ^ 3 := by
    have hc : ({lnum(Ahi)} - {lnum(Alo)}) * (12 * τ ^ 2 * ({lnum(al)} + {lnum(be)} * A - (τ - 2) * A) + (τ - 2) ^ 3) =
        ({lnum(Ahi)} - A) * ({p0}) + (A - {lnum(Alo)}) * ({p1}) := by ring
    have hp : 0 ≤ ({lnum(Ahi)} - A) * ({p0}) + (A - {lnum(Alo)}) * ({p1}) :=
      add_nonneg (mul_nonneg (by linarith) e0) (mul_nonneg (by linarith) e1)
    nlinarith
  have hg : (τ - 2) ^ 3 / (12 * τ ^ 2) * (12 * τ ^ 2) = (τ - 2) ^ 3 := div_mul_cancel₀ _ (ne_of_gt hτ2)
  nlinarith
''')
al,be=LINES[4]; A4=BPS[3]
chords.append(f'''/-- Chord 4 (`A ≥ 9/196`, the endpoint `τ = 7/2`). -/
theorem hh2_chord4 {{τ A : ℝ}} (h2 : 2 ≤ τ) (h7 : τ ≤ 7 / 2) (hA0 : {lnum(A4)} ≤ A) :
    (τ - 2) * A - (τ - 2) ^ 3 / (12 * τ ^ 2) ≤ {lnum(al)} + {lnum(be)} * A := by
  have e1 := ({leafname[(4,A4)]} τ h2 h7).le
  have hτ2 : 0 < 12 * τ ^ 2 := by positivity
  have hm : 0 ≤ (7 / 2 - τ) * (A - {lnum(A4)}) := mul_nonneg (by linarith) (by linarith)
  have key : 0 ≤ 12 * τ ^ 2 * ({lnum(al)} + {lnum(be)} * A - (τ - 2) * A) + (τ - 2) ^ 3 := by
    have hc : 12 * τ ^ 2 * ({lnum(al)} + {lnum(be)} * A - (τ - 2) * A) + (τ - 2) ^ 3 =
        ({pstr(al,be,A4)}) + 12 * τ ^ 2 * ((7 / 2 - τ) * (A - {lnum(A4)})) := by ring
    rw [hc]
    have : 0 ≤ 12 * τ ^ 2 * ((7 / 2 - τ) * (A - {lnum(A4)})) := mul_nonneg hτ2.le hm
    linarith
  have hg : (τ - 2) ^ 3 / (12 * τ ^ 2) * (12 * τ ^ 2) = (τ - 2) ^ 3 := div_mul_cancel₀ _ (ne_of_gt hτ2)
  nlinarith
''')
# ---- H-lemmas
hyps=f"""{{x al be t ℓ : ℝ}} (hx : 13 / 6 ≤ x) (hx2 : x ≤ 12 / 5) (hal : 1 ≤ al)
    (hal' : al ≤ 4 / 3) (ht0 : 0 ≤ t) (ht1 : t ≤ 229 / 1024)
    (hbe : be = x + ((24 * x + 51) / 128 - t) * (al - 1)) (hℓ : ℓ ≤ {LB})"""
lines=[]
for i in range(5):
    lines.append(f'''/-- The central face against chord `{i}`: `G₂ + ℓ{i}(A) < 0` for any `ℓ` below the log majorant
(`hh2CnL{i}_pos`). -/
theorem hh2_cen_line{i} {hyps} :
    {G2("ℓ")} + {lin(i)} < 0 := by
  calc _ ≤ {G2(LB)} + {lin(i)} := by gcongr
    _ < 0 := by
      have hS : (0 : ℝ) < 1 + x := by linarith
      have hK : 0 < x * (x + 2) + al ^ 2 := by positivity
      have hal0 : 0 < al := by linarith
      have hbe1 : 0 < be - 1 := by
        rw [hbe]
        have : 0 ≤ ((24 * x + 51) / 128 - t) * (al - 1) := mul_nonneg (by linarith) (by linarith)
        linarith
      have hB : 0 < al + be := by linarith
      rw [hh2_Ws_central _ _ _ _ hal0.ne' hS.ne' hK.ne', hh2_ELs_central _ _ _ _ hal0.ne' hS.ne' hK.ne']
      unfold hsQc hsRA
      have hc := hh2CnL{i}_pos t x al ht0 ht1 hx hx2 hal hal'
      rw [hh2CnL{i}_eq] at hc
      exact hh2_combine (M := {MLx}) (Ud := {UdL}) (by positivity) (by positivity)
        (hh2_cen_stage1_G (1 + x) (x * (x + 2) + al ^ 2) (hsDg x be al) (al + be) al (hsUC x be)
          hK.ne' hal0.ne' hB.ne')
        (hh2_cen_stage1_A (1 + x) (x * (x + 2) + al ^ 2) (hsDg x be al) (al + be) al (hsUC x be)
          hK.ne' hal0.ne' hB.ne')
        (hh2_cen_uC x be hS.ne' hbe1.ne') (hh2_cen_stage2_G t x al be hbe) (hh2_cen_stage2_A t x al be hbe)
        (hh2_cen_stage2_D t x al be hbe) hc
''')
G2log=G2(f"log (2 * {k})")
main=f'''/-- Duration elimination with the cubic loss (`CENTRAL_RATIO_HAND_SIGN` (9)-(10), with `τ` in
place of `T` in the loss): `G(τ) ≤ G(2) + ((τ - 2)A - (τ - 2)³/(12τ²))` for `τ ≥ 2`. -/
theorem hh2_tau_cubic {{W c k τ : ℝ}} (hk : 0 < k) (h2 : 2 ≤ τ) :
    (W - 1) * τ + 1 / τ + c + log (τ * k) + (2 - 7 * τ * k / 4) * (W - 3 / 4) ≤
      (W - 1) * 2 + 1 / 2 + c + log (2 * k) + (2 - 7 * 2 * k / 4) * (W - 3 / 4) +
        ((τ - 2) * ((1 - 7 * k / 4) * (W - 3 / 4)) - (τ - 2) ^ 3 / (12 * τ ^ 2)) := by
  have hτ0 : 0 < τ := by linarith
  have hlog : log (τ * k) = log (2 * k) + log (τ / 2) := by
    rw [← log_mul (by positivity) (by positivity)]
    congr 1
    field_simp
  have hcl := hh2_log_le_cubic_loss (z := τ / 2) (by linarith)
  have e1 : (τ / 2 - 1 / (τ / 2)) / 2 - (τ / 2 - 1) ^ 3 / (6 * (τ / 2) ^ 2) =
      τ / 4 - 1 / τ - (τ - 2) ^ 3 / (12 * τ ^ 2) := by field_simp; ring
  rw [e1] at hcl
  rw [hlog]
  nlinarith [hcl]

/-- The strip coordinate `t = c₊(x) - (β - x)/(α - 1) ∈ [0, 229/1024]` (`CENTRAL_RATIO_HAND_SIGN` (6)-(7);
`t = 0` when `α = 1`). -/
theorem hh2_strip_t {{x al be : ℝ}} (hx : 13 / 6 ≤ x) (hx2 : x ≤ 12 / 5) (hal : 1 ≤ al)
    (hb : x + 8 * x * (al - 1) / (9 * x + 8) ≤ be)
    (hb' : be ≤ x + x * (7 * x + 1) * (al - 1) / (4 * x ^ 2 + 11 * x + 1)) :
    ∃ t : ℝ, 0 ≤ t ∧ t ≤ 229 / 1024 ∧ be = x + ((24 * x + 51) / 128 - t) * (al - 1) := by
  rcases eq_or_lt_of_le hal with h | h
  · subst h
    refine ⟨0, le_refl _, by norm_num, ?_⟩
    simp only [sub_self, mul_zero, zero_div, add_zero] at hb hb' ⊢
    linarith
  · have ha : 0 < al - 1 := by linarith
    refine ⟨(24 * x + 51) / 128 - (be - x) / (al - 1), ?_, ?_, ?_⟩
    · have h1 : x * (7 * x + 1) * (al - 1) / (4 * x ^ 2 + 11 * x + 1) ≤ (24 * x + 51) / 128 * (al - 1) := by
        rw [div_le_iff₀ (by positivity)]
        have hq : 0 ≤ (24 * x + 51) * (4 * x ^ 2 + 11 * x + 1) - 128 * x * (7 * x + 1) := by
          nlinarith [mul_nonneg (sub_nonneg.2 hx) (sub_nonneg.2 hx2), sq_nonneg (x - 9 / 4),
            mul_nonneg (mul_nonneg (sub_nonneg.2 hx) (sub_nonneg.2 hx)) (sub_nonneg.2 hx)]
        nlinarith [mul_nonneg ha.le hq]
      have : (be - x) / (al - 1) ≤ (24 * x + 51) / 128 := by
        rw [div_le_iff₀ ha]; linarith
      linarith
    · have h1 : 5 / 8 * (al - 1) ≤ 8 * x * (al - 1) / (9 * x + 8) := by
        rw [le_div_iff₀ (by linarith)]
        nlinarith
      have : 5 / 8 ≤ (be - x) / (al - 1) := by
        rw [le_div_iff₀ ha]; linarith
      linarith
    · field_simp
      ring

/-- **The central sharp-ratio face** (`hs2_central_sign`). -/
theorem hs2_central_sign_proof {{x al be τ : ℝ}} (hx : 13 / 6 ≤ x) (hx2 : x ≤ 12 / 5) (hal : 1 ≤ al)
    (hqc : 6 * al ^ 2 ≤ x * (x + 2)) (hb : x + 8 * x * (al - 1) / (9 * x + 8) ≤ be)
    (hb' : be ≤ x + x * (7 * x + 1) * (al - 1) / (4 * x ^ 2 + 11 * x + 1)) (hτ : 2 ≤ τ)
    (hτT : τ * hsQc x al ≤ hsRA al be) :
    hsF x be al (hsUC x be) (hsQc x al) τ (log (τ * hsQc x al / hsRA al be))
      (2 - 7 * τ * hsQc x al / (4 * hsRA al be)) < 0 := by
  have hal' : al ≤ 4 / 3 := by
    nlinarith [sq_nonneg (al - 4 / 3), mul_nonneg (sub_nonneg.2 hx) (sub_nonneg.2 hx2)]
  obtain ⟨t, ht0, ht1, hbe⟩ := hh2_strip_t hx hx2 hal hb hb'
  have hal0 : 0 < al := by linarith
  have hbx : x ≤ be := by
    rw [hbe]
    have : 0 ≤ ((24 * x + 51) / 128 - t) * (al - 1) := mul_nonneg (by linarith) (by linarith)
    linarith
  have hB : 0 < al + be := by linarith
  have hrA : 0 < hsRA al be := by unfold hsRA; positivity
  have hq : 0 < hsQc x al := by unfold hsQc; positivity
  have hk : 0 < hsQc x al / hsRA al be := by positivity
  have hτk : τ * (hsQc x al / hsRA al be) ≤ 1 := by
    rw [mul_div_assoc', div_le_one hrA]
    exact hτT
  have hK : 0 < x * (x + 2) + al ^ 2 := by positivity
  have hk27 : 2 / 7 ≤ hsQc x al / hsRA al be := by
    have e : hsQc x al / hsRA al be = al * (al + be) / (x * (x + 2) + al ^ 2) := by
      unfold hsQc hsRA
      field_simp
    rw [e, le_div_iff₀ hK]
    have h1 : 1 * x ≤ al * be := mul_le_mul hal hbx (by linarith) hal0.le
    nlinarith
  have hτ7 : τ ≤ 7 / 2 := by
    have := mul_le_mul_of_nonneg_left hk27 (by linarith : (0 : ℝ) ≤ τ)
    linarith
  rw [hh2_hsF_face]
  have hl := hh2_log_le_bound (y := 2 * (hsQc x al / hsRA al be)) (by positivity)
  refine lt_of_le_of_lt (hh2_tau_cubic hk hτ) ?_
  by_cases h0 : {Aexp} ≤ 0
  · exact lt_of_le_of_lt (add_le_add (le_refl _) (hh2_chord0 hτ h0))
      (hh2_cen_line0 hx hx2 hal hal' ht0 ht1 hbe hl)
  by_cases h1 : {Aexp} ≤ {lnum(BPS[1])}
  · exact lt_of_le_of_lt (add_le_add (le_refl _) (hh2_chord1 hτ hτ7 (by linarith) h1))
      (hh2_cen_line1 hx hx2 hal hal' ht0 ht1 hbe hl)
  by_cases h2 : {Aexp} ≤ {lnum(BPS[2])}
  · exact lt_of_le_of_lt (add_le_add (le_refl _) (hh2_chord2 hτ hτ7 (by linarith) h2))
      (hh2_cen_line2 hx hx2 hal hal' ht0 ht1 hbe hl)
  by_cases h3 : {Aexp} ≤ {lnum(BPS[3])}
  · exact lt_of_le_of_lt (add_le_add (le_refl _) (hh2_chord3 hτ hτ7 (by linarith) h3))
      (hh2_cen_line3 hx hx2 hal hal' ht0 ht1 hbe hl)
  · exact lt_of_le_of_lt (add_le_add (le_refl _) (hh2_chord4 hτ hτ7 (by linarith)))
      (hh2_cen_line4 hx hx2 hal hal' ht0 ht1 hbe hl)
'''
imports="\n".join("public import SmoothedOctagon.Exclusion.Mixed.ShortHand.Heavy."+m for m in
                  ["S2CenStage","S2CenLinkG","S2CenLinkA","S2CenLinkD"]+[f"S2CenL{i}" for i in range(5)])
txt=f'''module

{imports}

/-!
# S2 heavy face signs: the central face

`hs2_central_sign_proof` proves the statement of `hs2_central_sign` (`CENTRAL_RATIO_HAND_SIGN` (5);
inventory HS-S2 R23): for `13/6 ≤ x ≤ 12/5`, `1 ≤ α`, `6α² ≤ x(x + 2)`, `β` in the strip, `q = q_c`,
`u = u_C(x, β)` and `2 ≤ τ ≤ T`, `G_τ < 0`.

Proof. Duration: `G(τ) - G(2) = (τ - 2)A + log(τ/2) - (τ² - 4)/(4τ)` and
`log z ≤ (z - 1/z)/2 - (z - 1)³/(6z²)` give `G(τ) ≤ G₂ + (τ - 2)A - (τ - 2)³/(12τ²)`
(`hh2_tau_cubic`); since `k ≥ 2/7`, `τ ≤ 7/2`, and the upper envelope of
`A ↦ (τ - 2)A - (τ - 2)³/(12τ²)` over `τ ∈ [2, 7/2]` is below the piecewise-linear chords
`ℓ₀, …, ℓ₄` (`hh2_chord0`-`4`, breakpoints `A = 0, 1/250, 3/250, 9/196`; each chord is checked at its
two endpoints by a cubic in `τ`). Each sign `G₂ + ℓᵢ(A) < 0` (with the log majorant) is a polynomial
sign on `t ∈ [0, 229/1024]`, `x ∈ [13/6, 12/5]`, `α ∈ [1, 4/3]` (`t = c₊(x) - c`, `c = (β - x)/(α - 1)`),
proved by the nested Bernstein certificates `hh2CnL{{i}}_pos` after the two-stage clearing
`hh2_cen_stage1_*` (abstract atoms) and `hh2_cen_stage2_*` (expansion).

Route: the notes' cubic loss `8TA² + TA/18` with the `β`-monotonicities (App. A), the exact-log
`x`-derivatives `Q₀`, `Q₁` (App. B) and the terminal polynomials `P₀`, `P₁` (App. C) are replaced by
the chord bounds of the exact cubic loss and five trivariate Bernstein certificates (no derivative
in `x` or `β`).

## Main API

* `hh2_tau_cubic`, `hh2_chord0`-`hh2_chord4`, `hh2_strip_t`, `hh2_cen_line0`-`hh2_cen_line4`.
* `hs2_central_sign_proof`.
-/

@[expose] public section

namespace SmoothedOctagon

open Real

''' + "\n".join(out) + "\n" + "\n".join(chords) + "\n" + "\n".join(lines) + "\n" + main + "\nend SmoothedOctagon\n"
open(D_+'S2Central.lean','w').write(txt); print(len(txt))
