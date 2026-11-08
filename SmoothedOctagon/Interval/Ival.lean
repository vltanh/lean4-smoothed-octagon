module

public import Mathlib.Analysis.SpecialFunctions.Log.Deriv

/-!
# Fixed-point intervals for kernel-checked interval arithmetic

An `Ival` is a pair of integers `lo ≤ hi` read as the real interval `[lo/2^prec, hi/2^prec]`, with
`prec = 60` fractional bits. Every operation rounds outward with `Int` shifts and `Nat` divisions,
which the kernel evaluates with GMP, so a Bool-valued checker built from these operations can be
run by `decide +kernel` (proof by reflection, no `native_decide`).

The operations are written for cheap kernel reduction (measured: about 1.5 times faster than the
same code through the `+`/`*` instances): arithmetic calls `Int.add`, `Int.mul`, … directly, the
roundings `fl`/`ce` shift a `Nat` under the `Int` constructor, signs are read off the
constructors (`zNonneg`, `zNonpos`), comparisons go through `Nat.ble`, and products are selected
by sign cases so that a product costs two `Int` multiplications.

## Main API

* `prec`, `Ival`, `Ival.Mem` (`x ∈ [lo/2^prec, hi/2^prec]`, stated as `lo ≤ x·2^prec ≤ hi`).
* Operations: `Ival.add`, `neg`, `sub`, `mul`, `sq`, `inv` (`Option`: `none` when the interval
  meets `0`), `ofRat` (outward rounding of `n/d`), `smul` (exact scaling by a natural number),
  `point`, `zero`.
* Soundness: `Ival.mem_add`, `mem_neg`, `mem_sub`, `mem_mul`, `mem_sq`, `mem_inv`, `mem_ofRat`,
  `mem_smul`, `mem_point`, and the sign readers `Ival.neg_of_mem` (`hi < 0 → x < 0`).
-/

@[expose] public section

namespace SmoothedOctagon.Interval

/-- Number of fractional bits of the fixed-point representation. -/
def prec : ℕ := 60

/-! ### Kernel-cheap integer helpers -/

/-- `0 ≤ n`, read off the constructor. -/
def zNonneg : ℤ → Bool
  | .ofNat _ => true
  | .negSucc _ => false

/-- `n ≤ 0`, read off the constructor. -/
def zNonpos : ℤ → Bool
  | .ofNat 0 => true
  | .ofNat (_ + 1) => false
  | .negSucc _ => true

/-- `n < 0`, read off the constructor. -/
def zNeg : ℤ → Bool
  | .ofNat _ => false
  | .negSucc _ => true

/-- `a ≤ b` through `Nat.ble`. -/
def zle : ℤ → ℤ → Bool
  | .ofNat a, .ofNat b => Nat.ble a b
  | .ofNat _, .negSucc _ => false
  | .negSucc _, .ofNat _ => true
  | .negSucc a, .negSucc b => Nat.ble b a

/-- `min a b`. -/
def zmin (a b : ℤ) : ℤ := cond (zle a b) a b

/-- `max a b`. -/
def zmax (a b : ℤ) : ℤ := cond (zle a b) b a

/-- `⌊x / 2^prec⌋`, by a `Nat` shift on the constructor. -/
def fl : ℤ → ℤ
  | .ofNat n => .ofNat (n >>> prec)
  | .negSucc n => .negSucc (n >>> prec)

/-- `⌈x / 2^prec⌉`, by a `Nat` shift on the constructor. -/
def ce : ℤ → ℤ
  | .ofNat n => .ofNat ((n + (2 ^ prec - 1)) >>> prec)
  | .negSucc n => Int.neg (.ofNat ((n + 1) >>> prec))

theorem zNonneg_iff (n : ℤ) : zNonneg n = true ↔ 0 ≤ n := by
  cases n <;> simp [zNonneg]

theorem zNonpos_iff (n : ℤ) : zNonpos n = true ↔ n ≤ 0 := by
  rcases n with (_ | n) | n <;> simp [zNonpos]
  omega

theorem zNeg_iff (n : ℤ) : zNeg n = true ↔ n < 0 := by
  cases n <;> simp [zNeg]

theorem zle_iff (a b : ℤ) : zle a b = true ↔ a ≤ b := by
  cases a <;> cases b <;> simp [zle, Nat.ble_eq] <;> omega

theorem zmin_eq (a b : ℤ) : zmin a b = min a b := by
  unfold zmin
  cases h : zle a b
  · have : ¬ a ≤ b := by rw [← zle_iff]; simp [h]
    simp; omega
  · have : a ≤ b := (zle_iff a b).1 h
    simp [this]

theorem zmax_eq (a b : ℤ) : zmax a b = max a b := by
  unfold zmax
  cases h : zle a b
  · have : ¬ a ≤ b := by rw [← zle_iff]; simp [h]
    simp; omega
  · have : a ≤ b := (zle_iff a b).1 h
    simp [this]

theorem zneg_def (a : ℤ) : Int.neg a = -a := rfl

theorem zsub_def (a b : ℤ) : Int.sub a b = a - b := rfl

theorem fl_eq (x : ℤ) : fl x = x >>> prec := by cases x <;> rfl

theorem ce_eq (x : ℤ) : ce x = -((-x) >>> prec) := by
  rcases x with (_ | n) | n
  · rfl
  · show Int.ofNat ((n + 1 + (2 ^ prec - 1)) >>> prec) = -((Int.negSucc n) >>> prec)
    rw [show Int.negSucc n >>> prec = Int.negSucc (n >>> prec) from rfl, Int.neg_negSucc]
    congr 1
    rw [Nat.shiftRight_eq_div_pow, Nat.shiftRight_eq_div_pow]
    have h : n + 1 + (2 ^ prec - 1) = n + 2 ^ prec := by
      have : 1 ≤ 2 ^ prec := Nat.one_le_two_pow; omega
    rw [h, Nat.add_div_right _ (by positivity)]
  · rfl

theorem fl_mul_le (x : ℤ) : fl x * 2 ^ prec ≤ x := by
  rw [fl_eq, Int.shiftRight_eq_div_pow]
  have h := Int.ediv_mul_le x (b := ((2 ^ prec : ℕ) : ℤ)) (by positivity)
  push_cast at h ⊢
  exact h

theorem le_ce_mul (x : ℤ) : x ≤ ce x * 2 ^ prec := by
  rw [ce_eq, Int.shiftRight_eq_div_pow]
  have h := Int.ediv_mul_le (-x) (b := ((2 ^ prec : ℕ) : ℤ)) (by positivity)
  push_cast at h ⊢
  linarith [neg_mul (-x / 2 ^ prec) (2 ^ prec)]

theorem fl_le_of_le {x : ℤ} {r : ℝ} (h : (x : ℝ) ≤ r * 2 ^ prec) : (fl x : ℝ) ≤ r := by
  have h1 : ((fl x * 2 ^ prec : ℤ) : ℝ) ≤ x := by exact_mod_cast fl_mul_le x
  push_cast at h1
  have hp : (0 : ℝ) < 2 ^ prec := by positivity
  nlinarith

theorem le_ce_of_le {x : ℤ} {r : ℝ} (h : r * 2 ^ prec ≤ (x : ℝ)) : r ≤ (ce x : ℝ) := by
  have h1 : (x : ℝ) ≤ ((ce x * 2 ^ prec : ℤ) : ℝ) := by exact_mod_cast le_ce_mul x
  push_cast at h1
  have hp : (0 : ℝ) < 2 ^ prec := by positivity
  nlinarith

/-! ### Intervals -/

/-- The interval `[lo/2^prec, hi/2^prec]`. -/
structure Ival where
  /-- Lower endpoint, scaled by `2^prec`. -/
  lo : ℤ
  /-- Upper endpoint, scaled by `2^prec`. -/
  hi : ℤ

namespace Ival

/-- `x` lies in the interval: `lo ≤ x·2^prec ≤ hi`. -/
def Mem (I : Ival) (x : ℝ) : Prop := (I.lo : ℝ) ≤ x * 2 ^ prec ∧ x * 2 ^ prec ≤ I.hi

/-- The zero interval. -/
def zero : Ival := ⟨0, 0⟩

/-- The degenerate interval at the scaled integer `n`, i.e. at `n/2^prec`. -/
def point (n : ℤ) : Ival := ⟨n, n⟩

/-- Sum. -/
def add (x y : Ival) : Ival := ⟨Int.add x.lo y.lo, Int.add x.hi y.hi⟩

/-- Negation. -/
def neg (x : Ival) : Ival := ⟨Int.neg x.hi, Int.neg x.lo⟩

/-- Difference. -/
def sub (x y : Ival) : Ival := ⟨Int.sub x.lo y.hi, Int.sub x.hi y.lo⟩

/-- Exact scaling by a natural number. -/
def smul (w : ℕ) (x : Ival) : Ival := ⟨Int.mul (.ofNat w) x.lo, Int.mul (.ofNat w) x.hi⟩

/-- The extreme products of `[a, b] × [c, d]`, selected by sign cases. -/
def mulRaw (a b c d : ℤ) : ℤ × ℤ :=
  cond (zNonneg a)
    (cond (zNonneg c) (Int.mul a c, Int.mul b d) (cond (zNonpos d) (Int.mul b c, Int.mul a d) (Int.mul b c, Int.mul b d)))
    (cond (zNonpos b)
      (cond (zNonneg c) (Int.mul a d, Int.mul b c) (cond (zNonpos d) (Int.mul b d, Int.mul a c) (Int.mul a d, Int.mul a c)))
      (cond (zNonneg c) (Int.mul a d, Int.mul b d)
        (cond (zNonpos d) (Int.mul b c, Int.mul a c) (zmin (Int.mul a d) (Int.mul b c), zmax (Int.mul a c) (Int.mul b d)))))

/-- Product, rounded outward. -/
def mul (x y : Ival) : Ival :=
  let p := mulRaw x.lo x.hi y.lo y.hi
  ⟨fl p.1, ce p.2⟩

/-- Square, rounded outward. -/
def sq (x : Ival) : Ival :=
  cond (zNonneg x.lo) ⟨fl (Int.mul x.lo x.lo), ce (Int.mul x.hi x.hi)⟩
    (cond (zNonpos x.hi) ⟨fl (Int.mul x.hi x.hi), ce (Int.mul x.lo x.lo)⟩
      ⟨0, ce (zmax (Int.mul x.lo x.lo) (Int.mul x.hi x.hi))⟩)

/-- `2^(2 prec)`, the numerator of a scaled reciprocal. -/
def unit2 : ℕ := 2 ^ (2 * prec)

/-- Reciprocal, rounded outward; `none` unless the interval is strictly positive or strictly
negative. -/
def inv (x : Ival) : Option Ival :=
  match x.lo, x.hi with
  | .ofNat (l + 1), .ofNat h => some ⟨.ofNat (unit2 / h), .ofNat ((unit2 + l) / (l + 1))⟩
  | .negSucc l, .negSucc h =>
      some ⟨-(.ofNat ((unit2 + h) / (h + 1))), -(.ofNat (unit2 / (l + 1)))⟩
  | _, _ => none

/-- The rational `n/d`, rounded outward (`n/0 = 0`). -/
def ofRat (n : ℤ) (d : ℕ) : Ival :=
  ⟨(n * 2 ^ prec) / (d : ℤ), -((-n * 2 ^ prec) / (d : ℤ))⟩

/-! ### Soundness -/

theorem mem_point (n : ℤ) : (point n).Mem ((n : ℝ) / 2 ^ prec) := by
  have hp : (2 : ℝ) ^ prec ≠ 0 := by positivity
  simp [Mem, point, div_mul_cancel₀ _ hp]

theorem mem_zero : zero.Mem 0 := by simp [Mem, zero]

theorem mem_add {x y : Ival} {a b : ℝ} (ha : x.Mem a) (hb : y.Mem b) : (x.add y).Mem (a + b) := by
  obtain ⟨h1, h2⟩ := ha; obtain ⟨h3, h4⟩ := hb
  simp only [Mem, add, Int.add_def]; push_cast; constructor <;> linarith

theorem mem_neg {x : Ival} {a : ℝ} (ha : x.Mem a) : x.neg.Mem (-a) := by
  obtain ⟨h1, h2⟩ := ha
  simp only [Mem, neg, zneg_def]; push_cast; constructor <;> linarith

theorem mem_sub {x y : Ival} {a b : ℝ} (ha : x.Mem a) (hb : y.Mem b) : (x.sub y).Mem (a - b) := by
  obtain ⟨h1, h2⟩ := ha; obtain ⟨h3, h4⟩ := hb
  simp only [Mem, sub, zsub_def]; push_cast; constructor <;> linarith

theorem mem_smul (w : ℕ) {x : Ival} {a : ℝ} (ha : x.Mem a) : (x.smul w).Mem (w * a) := by
  obtain ⟨h1, h2⟩ := ha
  have hw : (0 : ℝ) ≤ w := by positivity
  simp only [Mem, smul, Int.mul_def, Int.ofNat_eq_natCast]; push_cast
  constructor <;> nlinarith

theorem zNonneg_of {n : ℤ} (h : 0 ≤ n) : zNonneg n = true := (zNonneg_iff n).2 h

theorem zNonneg_of_neg {n : ℤ} (h : n < 0) : zNonneg n = false := by
  cases e : zNonneg n
  · rfl
  · exact absurd ((zNonneg_iff n).1 e) (not_le.2 h)

theorem zNonpos_of {n : ℤ} (h : n ≤ 0) : zNonpos n = true := (zNonpos_iff n).2 h

theorem zNonpos_of_pos {n : ℤ} (h : 0 < n) : zNonpos n = false := by
  cases e : zNonpos n
  · rfl
  · exact absurd ((zNonpos_iff n).1 e) (not_le.2 h)

private theorem castNN {n : ℤ} (h : 0 ≤ n) : (0 : ℝ) ≤ n := by exact_mod_cast h
private theorem castNP {n : ℤ} (h : n ≤ 0) : (n : ℝ) ≤ 0 := by exact_mod_cast h
private theorem castN {n : ℤ} (h : n < 0) : (n : ℝ) < 0 := by exact_mod_cast h
private theorem castP {n : ℤ} (h : 0 < n) : (0 : ℝ) < n := by exact_mod_cast h

/-- The extreme products enclose every product. -/
theorem mulRaw_spec {a b c d : ℤ} {X Y : ℝ} (h1 : (a : ℝ) ≤ X) (h2 : X ≤ b) (h3 : (c : ℝ) ≤ Y)
    (h4 : Y ≤ d) : ((mulRaw a b c d).1 : ℝ) ≤ X * Y ∧ X * Y ≤ ((mulRaw a b c d).2 : ℝ) := by
  unfold mulRaw
  simp only [Int.mul_def]
  rcases le_or_gt 0 a with ha | ha
  · have := castNN ha
    rw [zNonneg_of ha, Bool.cond_true]
    rcases le_or_gt 0 c with hc | hc
    · have := castNN hc
      rw [zNonneg_of hc, Bool.cond_true]; dsimp only; push_cast; constructor <;> nlinarith
    · have := castN hc
      rw [zNonneg_of_neg hc, Bool.cond_false]
      rcases le_or_gt d 0 with hd | hd
      · have := castNP hd
        rw [zNonpos_of hd, Bool.cond_true]; dsimp only; push_cast; constructor <;> nlinarith
      · have := castP hd
        rw [zNonpos_of_pos hd, Bool.cond_false]; dsimp only; push_cast; constructor <;> nlinarith
  · have := castN ha
    rw [zNonneg_of_neg ha, Bool.cond_false]
    rcases le_or_gt b 0 with hb | hb
    · have := castNP hb
      rw [zNonpos_of hb, Bool.cond_true]
      rcases le_or_gt 0 c with hc | hc
      · have := castNN hc
        rw [zNonneg_of hc, Bool.cond_true]; dsimp only; push_cast; constructor <;> nlinarith
      · have := castN hc
        rw [zNonneg_of_neg hc, Bool.cond_false]
        rcases le_or_gt d 0 with hd | hd
        · have := castNP hd
          rw [zNonpos_of hd, Bool.cond_true]; dsimp only; push_cast; constructor <;> nlinarith
        · have := castP hd
          rw [zNonpos_of_pos hd, Bool.cond_false]; dsimp only; push_cast; constructor <;> nlinarith
    · have := castP hb
      rw [zNonpos_of_pos hb, Bool.cond_false]
      rcases le_or_gt 0 c with hc | hc
      · have := castNN hc
        rw [zNonneg_of hc, Bool.cond_true]; dsimp only; push_cast; constructor <;> nlinarith
      · have := castN hc
        rw [zNonneg_of_neg hc, Bool.cond_false]
        rcases le_or_gt d 0 with hd | hd
        · have := castNP hd
          rw [zNonpos_of hd, Bool.cond_true]; dsimp only; push_cast; constructor <;> nlinarith
        · have := castP hd
          rw [zNonpos_of_pos hd, Bool.cond_false]; dsimp only
          rw [zmin_eq, zmax_eq]; push_cast
          constructor
          · rcases le_or_gt 0 X with hX | hX
            · exact min_le_of_right_le (by nlinarith)
            · exact min_le_of_left_le (by nlinarith)
          · rcases le_or_gt 0 X with hX | hX
            · exact le_max_of_le_right (by nlinarith)
            · exact le_max_of_le_left (by nlinarith)

theorem mem_mul {x y : Ival} {a b : ℝ} (ha : x.Mem a) (hb : y.Mem b) : (x.mul y).Mem (a * b) := by
  obtain ⟨h1, h2⟩ := ha; obtain ⟨h3, h4⟩ := hb
  obtain ⟨k1, k2⟩ := mulRaw_spec h1 h2 h3 h4
  have e : a * 2 ^ prec * (b * 2 ^ prec) = (a * b * 2 ^ prec) * 2 ^ prec := by ring
  rw [e] at k1 k2
  exact ⟨fl_le_of_le k1, le_ce_of_le k2⟩

theorem mem_sq {x : Ival} {a : ℝ} (ha : x.Mem a) : x.sq.Mem (a ^ 2) := by
  obtain ⟨h1, h2⟩ := ha
  have e : a ^ 2 * 2 ^ prec * 2 ^ prec = (a * 2 ^ prec) * (a * 2 ^ prec) := by ring
  unfold sq
  simp only [Int.mul_def]
  rcases le_or_gt 0 x.lo with hl | hl
  · have := castNN hl
    rw [zNonneg_of hl, Bool.cond_true]
    refine ⟨fl_le_of_le ?_, le_ce_of_le ?_⟩ <;> rw [e] <;> push_cast <;> nlinarith
  · have := castN hl
    rw [zNonneg_of_neg hl, Bool.cond_false]
    rcases le_or_gt x.hi 0 with hh | hh
    · have := castNP hh
      rw [zNonpos_of hh, Bool.cond_true]
      refine ⟨fl_le_of_le ?_, le_ce_of_le ?_⟩ <;> rw [e] <;> push_cast <;> nlinarith
    · have := castP hh
      rw [zNonpos_of_pos hh, Bool.cond_false]
      refine ⟨by simp only [Int.cast_zero]; positivity, le_ce_of_le ?_⟩
      rw [e, zmax_eq]; push_cast
      rcases le_or_gt 0 (a * 2 ^ prec) with hX | hX
      · exact le_max_of_le_right (by nlinarith)
      · exact le_max_of_le_left (by nlinarith)

theorem unit2_eq : (unit2 : ℝ) = 2 ^ prec * 2 ^ prec := by
  simp [unit2, ← pow_add, two_mul]

/-- `⌊N/h⌋ ≤ N/h` in `ℝ` for a natural division. -/
theorem nat_div_le (N h : ℕ) : ((N / h : ℕ) : ℝ) ≤ (N : ℝ) / h := Nat.cast_div_le

/-- `N/(l+1) ≤ ⌈N/(l+1)⌉ = (N + l)/(l + 1)`. -/
theorem le_nat_div_ceil (N l : ℕ) : (N : ℝ) / (l + 1) ≤ (((N + l) / (l + 1) : ℕ) : ℝ) := by
  have hl : (0 : ℝ) < l + 1 := by positivity
  rw [div_le_iff₀ hl]
  have h := Nat.lt_div_mul_add (a := N + l) (b := l + 1) (by omega)
  have h' : N + l < (N + l) / (l + 1) * (l + 1) + (l + 1) := by
    have := Nat.lt_succ_of_le (Nat.le_of_lt_succ h); omega
  have h'' : N ≤ (N + l) / (l + 1) * (l + 1) := by omega
  exact_mod_cast h''

theorem mem_inv {x y : Ival} {a : ℝ} (hx : x.inv = some y) (ha : x.Mem a) : y.Mem a⁻¹ := by
  obtain ⟨h1, h2⟩ := ha
  have hp : (0 : ℝ) < 2 ^ prec := by positivity
  unfold inv at hx
  split at hx
  · rename_i l h hl hh
    cases hx
    rw [hl] at h1; rw [hh] at h2
    simp only [Int.ofNat_eq_natCast, Int.cast_natCast, Nat.cast_succ] at h1 h2
    push_cast at h1 h2
    have hX : (0 : ℝ) < a * 2 ^ prec := by linarith [(by positivity : (0 : ℝ) ≤ l)]
    have ha0 : 0 < a := by nlinarith
    have hh0 : (0 : ℝ) < h := lt_of_lt_of_le hX h2
    have key : a⁻¹ * 2 ^ prec = (unit2 : ℝ) / (a * 2 ^ prec) := by
      rw [unit2_eq]; field_simp
    simp only [Mem, Int.ofNat_eq_natCast, Int.cast_natCast, key]
    constructor
    · refine le_trans (nat_div_le _ _) ?_
      exact div_le_div_of_nonneg_left (by positivity) hX h2
    · refine le_trans ?_ (le_nat_div_ceil _ _)
      exact div_le_div_of_nonneg_left (by positivity) (by positivity) h1
  · rename_i l h hl hh
    cases hx
    rw [hl] at h1; rw [hh] at h2
    simp only [Int.cast_negSucc, Nat.cast_add, Nat.cast_one] at h1 h2
    have hX : a * 2 ^ prec < 0 := by linarith [(by positivity : (0 : ℝ) ≤ h)]
    have ha0 : a < 0 := by nlinarith
    have key : a⁻¹ * 2 ^ prec = -((unit2 : ℝ) / (-(a * 2 ^ prec))) := by
      rw [unit2_eq, div_neg, neg_neg]; field_simp
    simp only [Mem, Int.ofNat_eq_natCast, Int.cast_neg, Int.cast_natCast, key, neg_le_neg_iff]
    constructor
    · refine le_trans ?_ (le_nat_div_ceil _ _)
      exact div_le_div_of_nonneg_left (by positivity) (by positivity) (by linarith)
    · refine le_trans (nat_div_le _ _) ?_
      exact div_le_div_of_nonneg_left (by positivity) (by linarith) (by push_cast; linarith)
  · cases hx

theorem mem_ofRat (n : ℤ) (d : ℕ) : (ofRat n d).Mem ((n : ℝ) / d) := by
  rcases Nat.eq_zero_or_pos d with rfl | hd
  · simp [Mem, ofRat]
  have hd' : (0 : ℝ) < d := by exact_mod_cast hd
  have hdz : (0 : ℤ) < d := by exact_mod_cast hd
  have e : (n : ℝ) / d * 2 ^ prec = ((n * 2 ^ prec : ℤ) : ℝ) / d := by push_cast; ring
  simp only [Mem, ofRat, e]
  constructor
  · rw [le_div_iff₀ hd']
    have := Int.ediv_mul_le (n * 2 ^ prec) (Int.ne_of_gt hdz)
    exact_mod_cast this
  · rw [div_le_iff₀ hd']
    have := Int.ediv_mul_le (-n * 2 ^ prec) (Int.ne_of_gt hdz)
    have h2 : ((n * 2 ^ prec : ℤ) : ℝ) ≤ (-((-n * 2 ^ prec) / (d : ℤ)) : ℤ) * (d : ℤ) := by
      have : (n * 2 ^ prec : ℤ) ≤ -((-n * 2 ^ prec) / (d : ℤ)) * d := by
        have e2 : -n * 2 ^ prec = -(n * 2 ^ prec) := by ring
        rw [e2] at this ⊢; linarith
      exact_mod_cast this
    push_cast at h2 ⊢; linarith

/-- An interval with negative upper end contains only negative numbers. -/
theorem neg_of_mem {x : Ival} {a : ℝ} (ha : x.Mem a) (h : zNeg x.hi = true) : a < 0 := by
  have h' : (x.hi : ℝ) < 0 := by exact_mod_cast (zNeg_iff _).1 h
  have hp : (0 : ℝ) < 2 ^ prec := by positivity
  nlinarith [ha.2]

/-- An interval with nonnegative lower end contains only nonnegative numbers. -/
theorem nonneg_of_mem {x : Ival} {a : ℝ} (ha : x.Mem a) (h : zNonneg x.lo = true) : 0 ≤ a := by
  have h' : (0 : ℝ) ≤ x.lo := by exact_mod_cast (zNonneg_iff _).1 h
  have hp : (0 : ℝ) < 2 ^ prec := by positivity
  nlinarith [ha.1]

end Ival

end SmoothedOctagon.Interval
