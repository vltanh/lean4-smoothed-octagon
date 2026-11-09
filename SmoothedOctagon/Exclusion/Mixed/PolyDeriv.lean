module

public import Mathlib.Analysis.Calculus.Deriv.MeanValue
public import Mathlib.Analysis.Calculus.Deriv.Pow
public import Mathlib.Analysis.Calculus.Deriv.Mul

/-!
# Derivatives of explicit polynomials and one-variable sign propagation

Small calculus helpers for the one-variable sign arguments: a polynomial is written by its
coefficient list in Horner form (`polyHorner`), whose derivative is again explicit (`polyHornerD`,
`poly_hasDerivAt_horner`); then the sign of a derivative on an interval is propagated to the
function (`poly_mono`, `poly_anti`) and a function with antitone derivative that is positive at both
ends is positive in between (`poly_concave_pos`).

## Main API

* `polyHorner`, `polyHornerD`, `poly_hasDerivAt_horner`.
* `poly_mono`, `poly_anti`, `poly_concave_pos`.
-/

@[expose] public section

namespace SmoothedOctagon

/-- Horner evaluation of a coefficient list. -/
noncomputable def polyHorner : List ℝ → ℝ → ℝ
  | [], _ => 0
  | c :: cs, s => c + s * polyHorner cs s

/-- The derivative of `polyHorner cs` at `s`. -/
noncomputable def polyHornerD : List ℝ → ℝ → ℝ
  | [], _ => 0
  | _ :: cs, s => polyHorner cs s + s * polyHornerD cs s

theorem poly_hasDerivAt_horner (cs : List ℝ) (s : ℝ) :
    HasDerivAt (polyHorner cs) (polyHornerD cs s) s := by
  induction cs with
  | nil =>
    have e : polyHorner [] = fun _ => (0 : ℝ) := by funext u; rfl
    rw [e]; exact hasDerivAt_const s 0
  | cons c cs ih =>
    have := (hasDerivAt_const s c).add ((hasDerivAt_id s).mul ih)
    convert this using 1
    · funext u; simp [polyHorner]
    · simp [polyHornerD]

/-- A nonnegative derivative on `[a, b]` makes the function nondecreasing there. -/
theorem poly_mono {f f' : ℝ → ℝ} {a b : ℝ} (hd : ∀ s, HasDerivAt f (f' s) s)
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
theorem poly_anti {f f' : ℝ → ℝ} {a b : ℝ} (hd : ∀ s, HasDerivAt f (f' s) s)
    (hneg : ∀ s, a ≤ s → s ≤ b → f' s ≤ 0) {u v : ℝ} (hau : a ≤ u) (huv : u ≤ v) (hvb : v ≤ b) :
    f v ≤ f u := by
  have := poly_mono (f := fun s => -f s) (f' := fun s => -f' s) (fun s => (hd s).neg)
    (fun s h1 h2 => by have := hneg s h1 h2; linarith) hau huv hvb
  linarith

/-- **Concave positivity**: if `f'` is antitone on `[a, b]` and `f(a), f(b) > 0`, then `f > 0`
on `[a, b]`. -/
theorem poly_concave_pos {f f' : ℝ → ℝ} {a b : ℝ} (hd : ∀ s, HasDerivAt f (f' s) s)
    (hanti : ∀ u v, a ≤ u → u ≤ v → v ≤ b → f' v ≤ f' u) (ha : 0 < f a) (hb : 0 < f b) {x : ℝ}
    (hax : a ≤ x) (hxb : x ≤ b) : 0 < f x := by
  rcases le_or_gt 0 (f' x) with h0 | h0
  · have : f a ≤ f x :=
      poly_mono hd (fun s h1 h2 => le_trans h0 (hanti s x h1 h2 hxb)) le_rfl hax le_rfl
    linarith
  · have : f b ≤ f x :=
      poly_anti hd (fun s h1 h2 => le_trans (hanti x s hax h1 h2) h0.le) le_rfl hxb le_rfl
    linarith

end SmoothedOctagon
