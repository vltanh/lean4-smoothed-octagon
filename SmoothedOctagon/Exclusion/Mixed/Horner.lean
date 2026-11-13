module

public import SmoothedOctagon.Exclusion.Mixed.PolyDeriv
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Positivity

/-!
# Arithmetic of polynomial coefficient lists

These operations retain the factored definitions of rational curves while
allowing their derivatives and translates to be evaluated in Horner form.
-/

@[expose] public section
namespace SmoothedOctagon.Horner

noncomputable def add : List ℝ → List ℝ → List ℝ
  | [], q => q
  | c :: p, [] => c :: p
  | c :: p, d :: q => (c + d) :: add p q

theorem eval_add (p q : List ℝ) (x : ℝ) :
    polyHorner (add p q) x = polyHorner p x + polyHorner q x := by
  induction p generalizing q with
  | nil => simp [add, polyHorner]
  | cons c p ih =>
    cases q with
    | nil => simp [add, polyHorner]
    | cons d q => simp only [add, polyHorner, ih]; ring

noncomputable def smul (a : ℝ) : List ℝ → List ℝ
  | [] => []
  | c :: p => (a * c) :: smul a p

theorem eval_smul (a : ℝ) (p : List ℝ) (x : ℝ) :
    polyHorner (smul a p) x = a * polyHorner p x := by
  induction p with
  | nil => simp [smul, polyHorner]
  | cons c p ih => simp only [smul, polyHorner, ih]; ring

noncomputable def mul : List ℝ → List ℝ → List ℝ
  | [], _ => []
  | c :: p, q => add (smul c q) (0 :: mul p q)

theorem eval_mul (p q : List ℝ) (x : ℝ) :
    polyHorner (mul p q) x = polyHorner p x * polyHorner q x := by
  induction p with
  | nil => simp [mul, polyHorner]
  | cons c p ih => simp only [mul, eval_add, eval_smul, polyHorner, ih]; ring

noncomputable def pow (p : List ℝ) : ℕ → List ℝ
  | 0 => [1]
  | n + 1 => mul p (pow p n)

theorem eval_pow (p : List ℝ) (n : ℕ) (x : ℝ) :
    polyHorner (pow p n) x = polyHorner p x ^ n := by
  induction n with
  | zero => simp [pow, polyHorner]
  | succ n ih => simp only [pow, eval_mul, ih]; ring

noncomputable def derivative : List ℝ → List ℝ
  | [] => []
  | _ :: p => add p (0 :: derivative p)

theorem eval_derivative (p : List ℝ) (x : ℝ) :
    polyHorner (derivative p) x = polyHornerD p x := by
  induction p with
  | nil => simp [derivative, polyHorner, polyHornerD]
  | cons c p ih => simp only [derivative, eval_add, polyHorner, polyHornerD, ih]; ring

theorem deriv_add (p q : List ℝ) (x : ℝ) :
    polyHornerD (add p q) x = polyHornerD p x + polyHornerD q x := by
  have h : HasDerivAt (polyHorner (add p q)) (polyHornerD p x + polyHornerD q x) x := by
    convert (poly_hasDerivAt_horner p x).add (poly_hasDerivAt_horner q x) using 1
    funext y
    exact eval_add p q y
  exact (poly_hasDerivAt_horner _ x).unique h

theorem deriv_smul (a : ℝ) (p : List ℝ) (x : ℝ) :
    polyHornerD (smul a p) x = a * polyHornerD p x := by
  have h : HasDerivAt (polyHorner (smul a p)) (a * polyHornerD p x) x := by
    convert (poly_hasDerivAt_horner p x).const_mul a using 1
    funext y
    exact eval_smul a p y
  exact (poly_hasDerivAt_horner _ x).unique h

noncomputable def shift (a : ℝ) : List ℝ → List ℝ
  | [] => []
  | c :: p => add [c] (add (smul a (shift a p)) (0 :: shift a p))

theorem eval_shift (a : ℝ) (p : List ℝ) (x : ℝ) :
    polyHorner (shift a p) x = polyHorner p (a + x) := by
  induction p with
  | nil => simp [shift, polyHorner]
  | cons c p ih => simp only [shift, eval_add, eval_smul, polyHorner, ih]; ring

theorem eval_nonpos (p : List ℝ) (hp : ∀ c ∈ p, c ≤ 0) {x : ℝ} (hx : 0 ≤ x) :
    polyHorner p x ≤ 0 := by
  induction p with
  | nil => simp [polyHorner]
  | cons c p ih =>
    have hc := hp c (by simp)
    have ht := ih (fun d hd => hp d (List.mem_cons_of_mem c hd))
    simp only [polyHorner]
    exact add_nonpos hc (mul_nonpos_of_nonneg_of_nonpos hx ht)

theorem antitone_of_derivative_coefficients (p : List ℝ)
    (hp : ∀ c ∈ derivative p, c ≤ 0) {x y : ℝ} (hx : 0 ≤ x) (hxy : x ≤ y) :
    polyHorner p y ≤ polyHorner p x := by
  apply poly_anti (fun s => poly_hasDerivAt_horner p s) _ le_rfl hxy le_rfl
  intro s hs _
  rw [← eval_derivative]
  exact eval_nonpos _ hp (hx.trans hs)

end SmoothedOctagon.Horner
