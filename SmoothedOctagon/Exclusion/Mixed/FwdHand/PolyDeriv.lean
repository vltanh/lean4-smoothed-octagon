module

public import Mathlib.Analysis.Calculus.Deriv.MeanValue
public import Mathlib.Analysis.Calculus.Deriv.Pow
public import Mathlib.Analysis.Calculus.Deriv.Mul

/-!
# Derivatives of explicit polynomials and one-variable sign propagation

Small calculus helpers for the hand proofs of `docs/lighter-proofs/` (PR #2): a polynomial is
written by its coefficient list in Horner form (`lrhHorner`), whose derivative is again explicit
(`lrhHornerD`, `lrh_hasDerivAt_horner`); then the sign of a derivative on an interval is
propagated to the function (`hrl_mono`, `hrl_anti`) and a function with antitone derivative that
is positive at both ends is positive in between (`hrl_concave_pos`).

## Main API

* `lrhHorner`, `lrhHornerD`, `lrh_hasDerivAt_horner`.
* `hrl_mono`, `hrl_anti`, `hrl_concave_pos`.
-/

@[expose] public section

namespace SmoothedOctagon

/-- Horner evaluation of a coefficient list. -/
noncomputable def lrhHorner : List ℝ → ℝ → ℝ
  | [], _ => 0
  | c :: cs, s => c + s * lrhHorner cs s

/-- The derivative of `lrhHorner cs` at `s`. -/
noncomputable def lrhHornerD : List ℝ → ℝ → ℝ
  | [], _ => 0
  | _ :: cs, s => lrhHorner cs s + s * lrhHornerD cs s

theorem lrh_hasDerivAt_horner (cs : List ℝ) (s : ℝ) :
    HasDerivAt (lrhHorner cs) (lrhHornerD cs s) s := by
  induction cs with
  | nil =>
    have e : lrhHorner [] = fun _ => (0 : ℝ) := by funext u; rfl
    rw [e]; exact hasDerivAt_const s 0
  | cons c cs ih =>
    have := (hasDerivAt_const s c).add ((hasDerivAt_id s).mul ih)
    convert this using 1
    · funext u; simp [lrhHorner]
    · simp [lrhHornerD]

/-- A nonnegative derivative on `[a, b]` makes the function nondecreasing there. -/
theorem hrl_mono {f f' : ℝ → ℝ} {a b : ℝ} (hd : ∀ s, HasDerivAt f (f' s) s)
    (hpos : ∀ s, a ≤ s → s ≤ b → 0 ≤ f' s) {u v : ℝ} (hau : a ≤ u) (huv : u ≤ v) (hvb : v ≤ b) :
    f u ≤ f v := by
  have hmono : MonotoneOn f (Set.Icc a b) := by
    apply monotoneOn_of_deriv_nonneg (convex_Icc a b)
    · exact fun s _ => (hd s).continuousAt.continuousWithinAt
    · exact fun s _ => (hd s).differentiableAt.differentiableWithinAt
    · intro s hs
      rw [interior_Icc] at hs
      rw [(hd s).deriv]
      exact hpos s hs.1.le hs.2.le
  exact hmono ⟨hau, huv.trans hvb⟩ ⟨hau.trans huv, hvb⟩ huv

/-- A nonpositive derivative on `[a, b]` makes the function nonincreasing there. -/
theorem hrl_anti {f f' : ℝ → ℝ} {a b : ℝ} (hd : ∀ s, HasDerivAt f (f' s) s)
    (hneg : ∀ s, a ≤ s → s ≤ b → f' s ≤ 0) {u v : ℝ} (hau : a ≤ u) (huv : u ≤ v) (hvb : v ≤ b) :
    f v ≤ f u := by
  have := hrl_mono (f := fun s => -f s) (f' := fun s => -f' s) (fun s => (hd s).neg)
    (fun s h1 h2 => by have := hneg s h1 h2; linarith) hau huv hvb
  linarith

/-- **Concave positivity**: if `f'` is antitone on `[a, b]` and `f(a), f(b) > 0`, then `f > 0`
on `[a, b]`. -/
theorem hrl_concave_pos {f f' : ℝ → ℝ} {a b : ℝ} (hd : ∀ s, HasDerivAt f (f' s) s)
    (hanti : ∀ u v, a ≤ u → u ≤ v → v ≤ b → f' v ≤ f' u) (ha : 0 < f a) (hb : 0 < f b) {x : ℝ}
    (hax : a ≤ x) (hxb : x ≤ b) : 0 < f x := by
  rcases le_or_gt 0 (f' x) with h0 | h0
  · have : f a ≤ f x :=
      hrl_mono hd (fun s h1 h2 => le_trans h0 (hanti s x h1 h2 hxb)) le_rfl hax le_rfl
    linarith
  · have : f b ≤ f x :=
      hrl_anti hd (fun s h1 h2 => le_trans (hanti x s hax h1 h2) h0.le) le_rfl hxb le_rfl
    linarith

end SmoothedOctagon
