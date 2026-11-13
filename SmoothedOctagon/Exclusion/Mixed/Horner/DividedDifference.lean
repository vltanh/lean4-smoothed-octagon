module

public import SmoothedOctagon.Exclusion.Mixed.Horner

/-! # Divided differences in Horner form -/

@[expose] public section
namespace SmoothedOctagon.Horner

/-- Synthetic division of `p(x) - p(a)` by `x - a`. -/
noncomputable def dividedDifference : List ℝ → ℝ → List ℝ
  | [], _ => []
  | _ :: p, a => add [polyHorner p a] (0 :: dividedDifference p a)

theorem eval_dividedDifference (p : List ℝ) (a x : ℝ) :
    (x - a) * polyHorner (dividedDifference p a) x = polyHorner p x - polyHorner p a := by
  induction p with
  | nil => simp [dividedDifference, polyHorner]
  | cons c p ih =>
    simp only [dividedDifference, eval_add, polyHorner]
    nlinarith only [congrArg (fun y : ℝ => x * y) ih]

theorem eval_nonneg (p : List ℝ) (hp : ∀ c ∈ p, 0 ≤ c) {x : ℝ} (hx : 0 ≤ x) :
    0 ≤ polyHorner p x := by
  induction p with
  | nil => simp [polyHorner]
  | cons c p ih =>
    have hc := hp c (by simp)
    have ht := ih (fun d hd => hp d (List.mem_cons_of_mem c hd))
    simp only [polyHorner]
    exact add_nonneg hc (mul_nonneg hx ht)

end SmoothedOctagon.Horner
