module

public import SmoothedOctagon.Interval.Expr

/-!
# The branch-and-bound checker

A certificate `Cert` is a subdivision tree of a box. An inner node splits one coordinate, at the
midpoint (`split`) or at a given scaled point (`cut`, which emulates the contractions of the C++
engine: one side is then a thin slab excluded by a single residual). A leaf excludes its box by

* `byR i`: the natural enclosure of residual `i` has upper end `< 0`, or
* `byS ws`: the slope enclosure of `∑ₖ wₖ f_{iₖ}` (natural weights `wₖ`, residual indices `iₖ`)
  has upper end `< 0`; a single residual is `byS [(i, 1)]`;
* `hole k`: the box is the `k`-th box of a list `done` of boxes excluded elsewhere (a separate
  theorem). This splits a large certificate into chunks, each checked in its own declaration,
  which bounds the kernel's memory.

`check fs done B c : Bool` runs the tree; `check_sound` says that if every box of `done` is
excluded and `check fs done B c = true`, then at every point of `B` some residual of `fs` is
negative. Run by `decide +kernel`, this is a proof by reflection.

## Main API

`Cert`, `check`, `Excluded`, `check_sound`, `excluded_of_check`, `AllNonneg`.
-/

@[expose] public section

namespace SmoothedOctagon.Interval

open Ival

/-- A subdivision tree with exclusion reasons at the leaves. -/
inductive Cert where
  /-- Split coordinate `j` at the midpoint of its interval. -/
  | split (j : ℕ) (l r : Cert)
  /-- Split coordinate `j` at the scaled point `p`. -/
  | cut (j : ℕ) (p : ℤ) (l r : Cert)
  /-- The natural enclosure of residual `i` is negative. -/
  | byR (i : ℕ)
  /-- The slope enclosure of `∑ₖ wₖ f_{iₖ}` is negative. -/
  | byS (ws : List (ℕ × ℕ))
  /-- The box is entry `k` of the list of boxes excluded elsewhere. -/
  | hole (k : ℕ)

/-- All residuals are nonnegative at `ρ`. -/
def AllNonneg (fs : List IExpr) (ρ : ℕ → ℝ) : Prop := ∀ f ∈ fs, 0 ≤ f.denote ρ

/-- Every point of the box `B` has a negative residual. -/
def Excluded (fs : List IExpr) (B : List Ival) : Prop := ∀ ρ, InBox B ρ → ¬ AllNonneg fs ρ

/-- Equality of intervals. -/
def ivEq (x y : Ival) : Bool := zle x.lo y.lo && zle y.lo x.lo && zle x.hi y.hi && zle y.hi x.hi

/-- Equality of boxes. -/
def boxEq : List Ival → List Ival → Bool
  | [], [] => true
  | x :: xs, y :: ys => ivEq x y && boxEq xs ys
  | _, _ => false

theorem boxEq_eq : ∀ {B D : List Ival}, boxEq B D = true → B = D
  | [], [], _ => rfl
  | x :: xs, y :: ys, h => by
    simp only [boxEq, ivEq, Bool.and_eq_true, zle_iff] at h
    obtain ⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩ := h
    obtain ⟨xl, xh⟩ := x; obtain ⟨yl, yh⟩ := y
    simp only at h1 h2 h3 h4
    rw [boxEq_eq h5, show xl = yl by omega, show xh = yh by omega]
  | [], _ :: _, h => by simp [boxEq] at h
  | _ :: _, [], h => by simp [boxEq] at h

/-- The slope form of `∑ₖ wₖ f_{iₖ}`. -/
def combS (fs : List IExpr) (B : List Ival) : List (ℕ × ℕ) → Option Slope
  | [] => some (Slope.const zero)
  | (i, w) :: ws =>
    fs[i]?.bind fun f => (f.evalS B).bind fun s => (combS fs B ws).map fun t => (s.scale w).add t

/-- The checker. -/
def check (fs : List IExpr) (done : List (List Ival)) : List Ival → Cert → Bool
  | B, .split j l r =>
    match B[j]? with
    | some I =>
      check fs done (B.set j ⟨I.lo, mid I⟩) l && check fs done (B.set j ⟨mid I, I.hi⟩) r
    | none => false
  | B, .cut j p l r =>
    match B[j]? with
    | some I => check fs done (B.set j ⟨I.lo, p⟩) l && check fs done (B.set j ⟨p, I.hi⟩) r
    | none => false
  | B, .byR i =>
    match fs[i]? with
    | some f =>
      match f.evalR B with
      | some I => zNeg I.hi
      | none => false
    | none => false
  | B, .byS ws =>
    match combS fs B ws with
    | some s => zNeg (zmin (s.bound B).hi s.r.hi)
    | none => false
  | B, .hole k =>
    match done[k]? with
    | some D => boxEq B D
    | none => false

theorem combS_sound {fs : List IExpr} {B : List Ival} {ρ : ℕ → ℝ} (hB : InBox B ρ)
    (hf : AllNonneg fs ρ) :
    ∀ (ws : List (ℕ × ℕ)) {s : Slope}, combS fs B ws = some s →
      ∃ y, 0 ≤ y ∧ s.Sound B.length (dvec B ρ) y
  | [], s, h => by
    simp only [combS, Option.some.injEq] at h; subst h
    exact ⟨0, le_rfl, Slope.sound_const mem_zero _ _⟩
  | (i, w) :: ws, s, h => by
    simp only [combS, Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
    obtain ⟨f, hfi, s1, hs1, t, ht, rfl⟩ := h
    obtain ⟨y, hy, hty⟩ := combS_sound hB hf ws ht
    have hmem : f ∈ fs := List.mem_of_getElem? hfi
    refine ⟨w * f.denote ρ + y, by have := hf f hmem; positivity, ?_⟩
    exact Slope.sound_add (Slope.sound_scale w (IExpr.evalS_sound hB f hs1)) hty

theorem inBox_set {B : List Ival} {ρ : ℕ → ℝ} (hB : InBox B ρ) {j : ℕ} {I J : Ival}
    (_hj : B[j]? = some I) (hJ : J.Mem (ρ j)) : InBox (B.set j J) ρ := by
  intro i K hK
  rw [List.getElem?_set] at hK
  split_ifs at hK with h
  · subst h
    simp at hK; subst hK; exact hJ
  · exact hB i K hK

/-- Splitting at any scaled point `p`: the point lies in one of the two halves. -/
theorem inBox_split {B : List Ival} {ρ : ℕ → ℝ} (hB : InBox B ρ) {j : ℕ} {I : Ival}
    (hj : B[j]? = some I) (p : ℤ) :
    InBox (B.set j ⟨I.lo, p⟩) ρ ∨ InBox (B.set j ⟨p, I.hi⟩) ρ := by
  have hI := hB j I hj
  rcases le_total (ρ j * 2 ^ prec) p with h | h
  · exact Or.inl (inBox_set hB hj ⟨hI.1, h⟩)
  · exact Or.inr (inBox_set hB hj ⟨h, hI.2⟩)

/-- **Soundness of the checker.** -/
theorem check_sound (fs : List IExpr) (done : List (List Ival))
    (hdone : ∀ D ∈ done, Excluded fs D) :
    ∀ (B : List Ival) (c : Cert), check fs done B c = true → Excluded fs B
  | B, .split j l r, h, ρ, hB, hf => by
    simp only [check] at h
    split at h
    · rename_i I hj
      simp only [Bool.and_eq_true] at h
      rcases inBox_split hB hj (mid I) with h' | h'
      · exact check_sound fs done hdone _ l h.1 ρ h' hf
      · exact check_sound fs done hdone _ r h.2 ρ h' hf
    · cases h
  | B, .cut j p l r, h, ρ, hB, hf => by
    simp only [check] at h
    split at h
    · rename_i I hj
      simp only [Bool.and_eq_true] at h
      rcases inBox_split hB hj p with h' | h'
      · exact check_sound fs done hdone _ l h.1 ρ h' hf
      · exact check_sound fs done hdone _ r h.2 ρ h' hf
    · cases h
  | B, .byR i, h, ρ, hB, hf => by
    simp only [check] at h
    split at h
    · rename_i f hfi
      split at h
      · rename_i I hI
        have h1 := neg_of_mem (IExpr.evalR_sound hB f hI) h
        exact absurd (hf f (List.mem_of_getElem? hfi)) (not_le.2 h1)
      · cases h
    · cases h
  | B, .byS ws, h, ρ, hB, hf => by
    simp only [check] at h
    split at h
    · rename_i s hs
      obtain ⟨y, hy, hsy⟩ := combS_sound hB hf ws hs
      have hb := Slope.bound_sound hB hsy
      have hr := hsy.1
      rw [zNeg_iff, zmin_eq] at h
      have hp : (0 : ℝ) < 2 ^ prec := by positivity
      rcases min_lt_iff.1 h with h1 | h1
      · have : ((s.bound B).hi : ℝ) < 0 := by exact_mod_cast h1
        nlinarith [hb.2]
      · have : (s.r.hi : ℝ) < 0 := by exact_mod_cast h1
        nlinarith [hr.2]
    · cases h
  | B, .hole k, h, ρ, hB, hf => by
    simp only [check] at h
    split at h
    · rename_i D hD
      rw [boxEq_eq h] at hB
      exact hdone D (List.mem_of_getElem? hD) ρ hB hf
    · cases h

/-- A self-contained certificate (no holes) excludes its box. -/
theorem excluded_of_check {fs : List IExpr} {B : List Ival} {c : Cert}
    (h : check fs [] B c = true) : Excluded fs B :=
  check_sound fs [] (by simp) B c h

/-- `List.Forall` form of the hypothesis on `done`, convenient for a literal list of
chunk theorems. -/
theorem excluded_of_check_done {fs : List IExpr} {done : List (List Ival)} {B : List Ival}
    {c : Cert} (h : check fs done B c = true) (hdone : done.Forall (Excluded fs)) :
    Excluded fs B :=
  check_sound fs done (List.forall_iff_forall_mem.1 hdone) B c h

end SmoothedOctagon.Interval
