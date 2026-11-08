module

public import SmoothedOctagon.Interval.Ival
public import Mathlib.Analysis.Real.Sqrt

/-!
# Interval enclosures of `√`, `log` and `Hlog`

Kernel-evaluable outward enclosures of the special functions the covers use, on the fixed-point
intervals of `SmoothedOctagon.Interval.Ival`.

* `√`: integer square roots by Newton's iteration from above (`isqrt`, structural on a fuel
  bound), with the result checked by squaring, so the enclosure never depends on convergence.
* `log`: for a point `x = m/2^prec`, `m = 2^k·y` with `y ∈ [1, 2)`, `log x = (k - prec)·log 2 +
  log y`, and `log y = 2 atanh t`, `t = (y - 1)/(y + 1) ∈ [0, 1/3)`, by twenty terms of the atanh
  series (tail `< 2⁻⁶⁰`, one unit in the last place); `log 2 = 2 atanh (1/3)` the same way.
  On an interval, `log` is monotone.
* `Hlog z = (log(1 + z) - z + z²/2)/z³` (`1/3` at `0`): at a point `z ≤ 1/4`, the alternating
  series `∑ₖ (-1)ᵏ zᵏ/(k + 3)` (32 terms, tail `< 2⁻⁶⁰`, `Real.abs_log_sub_add_sum_range_le`);
  at a point `z > 1/4`, the closed form with the `log` enclosure. On an interval in `[0, ∞)`,
  `Hlog` is antitone.

## Main API

`hlogR` (the real function), `Ival.sqrtI`, `Ival.logI`, `Ival.hlogI`, with
`Ival.mem_sqrtI`, `Ival.mem_logI`, `Ival.mem_hlogI`; also `Ival.hornerI` (`mem_hornerI`),
`Ival.logPt` (`mem_logPt`), `Ival.hPt` (`mem_hPt`), `hlogR_antitoneOn`.

`arctan` and `logDiv` are in `SmoothedOctagon.Interval.Trig`.
-/

@[expose] public section

namespace SmoothedOctagon.Interval

/-- `H(z) = (log(1 + z) - z + z²/2)/z³` with `H(0) = 1/3`; the same function as
`SmoothedOctagon.Certificates.Nonshort.Hlog`. -/
noncomputable def hlogR (z : ℝ) : ℝ :=
  if z = 0 then 1 / 3 else (Real.log (1 + z) - z + z ^ 2 / 2) / z ^ 3

/-! ### Integer square root -/

/-- Newton's iteration for `⌊√n⌋` from an upper guess, with a fuel bound. -/
def isqrtIter : ℕ → ℕ → ℕ → ℕ
  | 0, _, g => g
  | fuel + 1, n, g =>
    let g' := (g + n / g) / 2
    cond (Nat.ble g g') g (isqrtIter fuel n g')

/-- A candidate for `⌊√n⌋` (checked by the callers). -/
def isqrt (n : ℕ) : ℕ := isqrtIter 64 n (2 ^ (Nat.log2 n / 2 + 1))

/-- A certified lower square root: `s` with `s² ≤ n`. -/
def sqrtLo (n : ℕ) : ℕ :=
  let s := isqrt n
  cond (Nat.ble (s * s) n) s 0

/-- A certified upper square root: `t` with `n ≤ t²`. -/
def sqrtHi (n : ℕ) : ℕ :=
  let s := isqrt n
  cond (Nat.ble n (s * s)) s (cond (Nat.ble n ((s + 1) * (s + 1))) (s + 1) (n + 1))

theorem sqrtLo_sq_le (n : ℕ) : sqrtLo n * sqrtLo n ≤ n := by
  unfold sqrtLo; dsimp only
  cases h : Nat.ble (isqrt n * isqrt n) n
  · simp
  · simpa using h

theorem le_sqrtHi_sq (n : ℕ) : n ≤ sqrtHi n * sqrtHi n := by
  unfold sqrtHi; dsimp only
  cases h : Nat.ble n (isqrt n * isqrt n)
  · cases h' : Nat.ble n ((isqrt n + 1) * (isqrt n + 1))
    · simp only [Bool.cond_false]; nlinarith
    · simpa using h'
  · simpa using h

namespace Ival

/-- The scaled natural number `max n 0`. -/
def toNat0 : ℤ → ℕ
  | .ofNat n => n
  | .negSucc _ => 0

/-- Square root (`Real.sqrt`, which is `0` on `(-∞, 0]` and monotone). -/
def sqrtI (x : Ival) : Ival :=
  ⟨.ofNat (sqrtLo (toNat0 x.lo * 2 ^ prec)), .ofNat (sqrtHi (toNat0 x.hi * 2 ^ prec))⟩

theorem toNat0_eq (n : ℤ) : (toNat0 n : ℤ) = max n 0 := by
  cases n <;> simp [toNat0]

theorem mem_sqrtI {x : Ival} {a : ℝ} (ha : x.Mem a) : x.sqrtI.Mem (Real.sqrt a) := by
  obtain ⟨h1, h2⟩ := ha
  have hp : (0 : ℝ) < 2 ^ prec := by positivity
  have e : Real.sqrt a * 2 ^ prec = Real.sqrt (a * 2 ^ prec * 2 ^ prec) := by
    rw [Real.sqrt_mul' _ hp.le, Real.sqrt_mul' _ hp.le, mul_assoc, Real.mul_self_sqrt hp.le]
  simp only [Mem, sqrtI, Int.ofNat_eq_natCast, Int.cast_natCast, e]
  constructor
  · set n := toNat0 x.lo * 2 ^ prec
    have hn : (n : ℝ) ≤ max (a * 2 ^ prec * 2 ^ prec) 0 := by
      have h0 : ((toNat0 x.lo : ℤ) : ℝ) = max (x.lo : ℝ) 0 := by
        rw [toNat0_eq]; push_cast; rfl
      simp only [n, Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat]
      have h0' : (toNat0 x.lo : ℝ) = max (x.lo : ℝ) 0 := by exact_mod_cast h0
      rw [h0']
      rcases le_total (x.lo : ℝ) 0 with hl | hl
      · rw [max_eq_right hl, zero_mul]; exact le_max_right _ _
      · rw [max_eq_left hl]; exact le_max_of_le_left (by nlinarith)
    have hs := sqrtLo_sq_le n
    have hs' : ((sqrtLo n : ℕ) : ℝ) ^ 2 ≤ n := by rw [pow_two]; exact_mod_cast hs
    calc ((sqrtLo n : ℕ) : ℝ) ≤ Real.sqrt n := (Real.le_sqrt (by positivity) (by positivity)).2 hs'
      _ ≤ Real.sqrt (max (a * 2 ^ prec * 2 ^ prec) 0) := Real.sqrt_le_sqrt hn
      _ = Real.sqrt (a * 2 ^ prec * 2 ^ prec) := by
          rcases le_total (a * 2 ^ prec * 2 ^ prec) 0 with h | h
          · rw [max_eq_right h, Real.sqrt_zero, Real.sqrt_eq_zero'.2 h]
          · rw [max_eq_left h]
  · set n := toNat0 x.hi * 2 ^ prec
    have hn : a * 2 ^ prec * 2 ^ prec ≤ n := by
      have h0 : ((toNat0 x.hi : ℤ) : ℝ) = max (x.hi : ℝ) 0 := by
        rw [toNat0_eq]; push_cast; rfl
      have h0' : (toNat0 x.hi : ℝ) = max (x.hi : ℝ) 0 := by exact_mod_cast h0
      simp only [n, Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat, h0']
      exact mul_le_mul_of_nonneg_right (le_max_of_le_left h2) hp.le
    have hs := le_sqrtHi_sq n
    have hs' : (n : ℝ) ≤ ((sqrtHi n : ℕ) : ℝ) ^ 2 := by rw [pow_two]; exact_mod_cast hs
    calc Real.sqrt (a * 2 ^ prec * 2 ^ prec) ≤ Real.sqrt n := Real.sqrt_le_sqrt hn
      _ ≤ ((sqrtHi n : ℕ) : ℝ) := (Real.sqrt_le_left (by positivity)).2 hs'

/-! ### Horner evaluation -/

/-- `c₀ + x(c₁ + x(c₂ + …))` on intervals. -/
def hornerI (x : Ival) : List Ival → Ival
  | [] => zero
  | c :: cs => c.add (x.mul (hornerI x cs))

/-- `c₀ + x(c₁ + x(c₂ + …))` on reals. -/
noncomputable def hornerR (x : ℝ) : List ℝ → ℝ
  | [] => 0
  | c :: cs => c + x * hornerR x cs

theorem mem_hornerI {x : Ival} {a : ℝ} (ha : x.Mem a) :
    ∀ (cs : List Ival) (rs : List ℝ), List.Forall₂ (fun (c : Ival) r => c.Mem r) cs rs →
      (hornerI x cs).Mem (hornerR a rs)
  | [], [], _ => mem_zero
  | _ :: cs, _ :: rs, .cons h hs => mem_add h (mem_mul ha (mem_hornerI ha cs rs hs))

/-! ### Logarithm -/

/-- Exact scaling by an integer. -/
def zsmul : ℤ → Ival → Ival
  | .ofNat n, x => x.smul n
  | .negSucc n, x => (x.smul (n + 1)).neg

/-- The rational `n/d` of naturals (`d > 0`), rounded outward. -/
def ratI (n d : ℕ) : Ival := ⟨.ofNat (n * 2 ^ prec / d), .ofNat ((n * 2 ^ prec + (d - 1)) / d)⟩

/-- The coefficients `1/(2k + 1)`, `k < 20`, of the atanh series. -/
def atanhCoeffs : List Ival := (List.range 20).map fun k => ofRat 1 (2 * k + 1)

/-- `2 atanh t = log((1 + t)/(1 - t))` for `t ∈ T ⊆ [0, 1/3]`: twenty terms and one unit for the
tail. -/
def logT (T : Ival) : Ival :=
  let S := T.mul (hornerI T.sq atanhCoeffs)
  ⟨2 * S.lo, 2 * S.hi + 1⟩

/-- `log 2 = 2 atanh (1/3)`. -/
def log2I : Ival := logT (ofRat 1 3)

/-- `log (m/2^prec)` for `m > 0`. -/
def logPt (m : ℕ) : Ival :=
  let k := Nat.log2 m
  let pk := 2 ^ k
  (logT (ratI (m - pk) (m + pk))).add (zsmul ((k : ℤ) - prec) log2I)

/-- `log` on a positive interval; `none` unless `lo > 0`. -/
def logI (x : Ival) : Option Ival :=
  match x.lo, x.hi with
  | .ofNat (l + 1), .ofNat h => some ⟨(logPt (l + 1)).lo, (logPt h).hi⟩
  | _, _ => none

/-! ### `Hlog` -/

/-- The coefficients `(-1)ᵏ/(k + 3)`, `k < 32`, of `H(z) = ∑ₖ (-1)ᵏ zᵏ/(k + 3)`. -/
def hCoeffs : List Ival :=
  (List.range 32).map fun k => ofRat (cond (Nat.beq (k % 2) 0) 1 (-1)) (k + 3)

/-- `H` at the point `m/2^prec ≥ 0`. -/
def hPt (m : ℕ) : Option Ival :=
  cond (Nat.ble (4 * m) (2 ^ prec))
    (let S := hornerI (point m) hCoeffs
     some ⟨S.lo - 1, S.hi + 1⟩)
    (let Z := point m
     let N := ((logPt (2 ^ prec + m)).sub Z).add (Z.sq.mul (ofRat 1 2))
     (Z.sq.mul Z).inv.map N.mul)

/-- `H` on an interval in `[0, ∞)`, where it is antitone; `none` unless `lo ≥ 0`. -/
def hlogI (x : Ival) : Option Ival :=
  match x.lo, x.hi with
  | .ofNat l, .ofNat h =>
    match hPt h, hPt l with
    | some a, some b => some ⟨a.lo, b.hi⟩
    | _, _ => none
  | _, _ => none

/-! ### Proofs: series -/

theorem hornerR_range (x : ℝ) : ∀ (n : ℕ) (f : ℕ → ℝ),
    hornerR x ((List.range n).map f) = ∑ k ∈ Finset.range n, f k * x ^ k
  | 0, f => by simp [hornerR]
  | n + 1, f => by
    rw [List.range_succ_eq_map, List.map_cons, List.map_map, hornerR, Finset.sum_range_succ',
      hornerR_range x n (f ∘ Nat.succ), Finset.mul_sum]
    simp only [Function.comp, pow_zero, mul_one, pow_succ]
    rw [add_comm]
    congr 1
    exact Finset.sum_congr rfl fun k _ => by ring

theorem atanhCoeffs_mem : List.Forall₂ (fun (c : Ival) r => c.Mem r) atanhCoeffs
    ((List.range 20).map fun k : ℕ => (1 : ℝ) / (2 * (k : ℝ) + 1)) := by
  rw [atanhCoeffs, List.forall₂_map_left_iff, List.forall₂_map_right_iff, List.forall₂_same]
  intro k _
  have := mem_ofRat 1 (2 * k + 1)
  push_cast at this
  exact this

/-- The atanh series with twenty terms, and its tail below one unit in the last place. -/
theorem atanh_bounds {t : ℝ} (h0 : 0 ≤ t) (h1 : t ≤ 1 / 3) :
    (∑ k ∈ Finset.range 20, 2 * (1 / (2 * (k : ℝ) + 1)) * t ^ (2 * k + 1)) ≤
        Real.log (1 + t) - Real.log (1 - t) ∧
      Real.log (1 + t) - Real.log (1 - t) ≤
        (∑ k ∈ Finset.range 20, 2 * (1 / (2 * (k : ℝ) + 1)) * t ^ (2 * k + 1)) + 1 / 2 ^ prec := by
  have ht : |t| < 1 := abs_lt.2 ⟨by linarith, by linarith⟩
  have hs := Real.hasSum_log_sub_log_of_abs_lt_one ht
  have hnn : ∀ k : ℕ, 0 ≤ 2 * (1 / (2 * (k : ℝ) + 1)) * t ^ (2 * k + 1) := fun k => by positivity
  refine ⟨sum_le_hasSum _ (fun k _ => hnn k) hs, ?_⟩
  have htail := (hasSum_nat_add_iff' 20).2 hs
  have ht2 : t ^ 2 < 1 := by nlinarith
  have hgeo := (hasSum_geometric_of_lt_one (sq_nonneg t) ht2).mul_left (2 * t ^ 41)
  have hle := hasSum_le (fun n => ?_) htail hgeo
  · have h41 : t ^ 41 ≤ (1 / 3) ^ 41 := pow_le_pow_left₀ h0 h1 41
    have hinv : (1 - t ^ 2)⁻¹ ≤ 9 / 8 := by
      rw [inv_le_comm₀ (by nlinarith) (by norm_num)]; nlinarith
    have : 2 * t ^ 41 * (1 - t ^ 2)⁻¹ ≤ 1 / 2 ^ prec := by
      calc 2 * t ^ 41 * (1 - t ^ 2)⁻¹ ≤ 2 * (1 / 3) ^ 41 * (9 / 8) := by
            gcongr
          _ ≤ 1 / 2 ^ prec := by norm_num [prec]
    linarith
  · have hk : (0 : ℝ) < 2 * ((n + 20 : ℕ) : ℝ) + 1 := by positivity
    have h1' : 2 * (1 / (2 * ((n + 20 : ℕ) : ℝ) + 1)) ≤ 2 := by
      rw [mul_one_div]; rw [div_le_iff₀ hk]; push_cast; nlinarith
    have e : t ^ (2 * (n + 20) + 1) = t ^ 41 * (t ^ 2) ^ n := by
      rw [← pow_mul, ← pow_add]; ring_nf
    rw [e]
    have : 0 ≤ t ^ 41 * (t ^ 2) ^ n := by positivity
    nlinarith

theorem mem_logT {T : Ival} {t : ℝ} (hT : T.Mem t) (h0 : 0 ≤ t) (h1 : t ≤ 1 / 3) :
    (logT T).Mem (Real.log (1 + t) - Real.log (1 - t)) := by
  have hS := mem_mul hT (mem_hornerI (mem_sq hT) _ _ atanhCoeffs_mem)
  rw [hornerR_range] at hS
  set S := T.mul (hornerI T.sq atanhCoeffs)
  have e : t * ∑ k ∈ Finset.range 20, 1 / (2 * (k : ℝ) + 1) * (t ^ 2) ^ k =
      (∑ k ∈ Finset.range 20, 2 * (1 / (2 * (k : ℝ) + 1)) * t ^ (2 * k + 1)) / 2 := by
    rw [Finset.mul_sum, div_eq_mul_inv, Finset.sum_mul]
    exact Finset.sum_congr rfl fun k _ => by ring
  rw [e] at hS
  obtain ⟨b1, b2⟩ := atanh_bounds h0 h1
  obtain ⟨s1, s2⟩ := hS
  have hp : (0 : ℝ) < 2 ^ prec := by positivity
  simp only [Mem, logT]
  push_cast
  constructor
  · nlinarith
  · have : (1 : ℝ) / 2 ^ prec * 2 ^ prec = 1 := by field_simp
    nlinarith

theorem mem_ofRat_one_three : (ofRat 1 3).Mem (1 / 3) := by
  have := mem_ofRat 1 3; push_cast at this; exact this

theorem mem_log2I : log2I.Mem (Real.log 2) := by
  have h := mem_logT mem_ofRat_one_three (by norm_num) le_rfl
  have e : Real.log (1 + 1 / 3) - Real.log (1 - 1 / 3) = Real.log 2 := by
    rw [← Real.log_div (by norm_num) (by norm_num)]; norm_num
  rw [e] at h; exact h

theorem mem_ratI (n l : ℕ) : (ratI n (l + 1)).Mem ((n : ℝ) / (l + 1)) := by
  have hl : (0 : ℝ) < l + 1 := by positivity
  have e : (n : ℝ) / (l + 1) * 2 ^ prec = ((n * 2 ^ prec : ℕ) : ℝ) / (l + 1) := by
    push_cast; ring
  simp only [Mem, ratI, Int.ofNat_eq_natCast, Int.cast_natCast, e]
  constructor
  · have := nat_div_le (n * 2 ^ prec) (l + 1); push_cast at this ⊢; exact this
  · have := le_nat_div_ceil (n * 2 ^ prec) l
    simp only [Nat.add_sub_cancel] at this ⊢
    exact this

theorem mem_zsmul (e : ℤ) {x : Ival} {a : ℝ} (ha : x.Mem a) : (zsmul e x).Mem (e * a) := by
  cases e with
  | ofNat n => simpa [zsmul] using mem_smul n ha
  | negSucc n =>
    have := mem_neg (mem_smul (n + 1) ha)
    simp only [zsmul]
    convert this using 1
    push_cast [Int.cast_negSucc]; ring

theorem mem_logPt {m : ℕ} (hm : 0 < m) : (logPt m).Mem (Real.log (m / 2 ^ prec)) := by
  set k := Nat.log2 m with hk
  have hk1 : 2 ^ k ≤ m := Nat.log2_self_le (by omega)
  have hk2 : m < 2 ^ (k + 1) := Nat.lt_log2_self
  have hpk : (0 : ℝ) < 2 ^ k := by positivity
  have hm' : (0 : ℝ) < m := by exact_mod_cast hm
  have hk1' : (2 : ℝ) ^ k ≤ m := by exact_mod_cast hk1
  have hk2' : (m : ℝ) < 2 * 2 ^ k := by
    have : (m : ℝ) < ((2 ^ (k + 1) : ℕ) : ℝ) := by exact_mod_cast hk2
    rw [Nat.cast_pow, pow_succ] at this; push_cast at this; linarith
  set t : ℝ := ((m - 2 ^ k : ℕ) : ℝ) / ((m + 2 ^ k - 1 : ℕ) + 1) with ht
  have htv : t = (m - 2 ^ k) / (m + 2 ^ k) := by
    rw [ht, Nat.cast_sub hk1]
    have : ((m + 2 ^ k - 1 : ℕ) : ℝ) + 1 = m + 2 ^ k := by
      have h1 : 1 ≤ m + 2 ^ k := by omega
      rw [Nat.cast_sub h1]; push_cast; ring
    rw [this]; push_cast; ring
  have hT : (ratI (m - 2 ^ k) (m + 2 ^ k)).Mem t := by
    have h := mem_ratI (m - 2 ^ k) (m + 2 ^ k - 1)
    have e : m + 2 ^ k - 1 + 1 = m + 2 ^ k := by have : 1 ≤ m + 2 ^ k := by omega
                                                 omega
    rw [e] at h; rw [ht]
    convert h using 2
  have ht0 : 0 ≤ t := by rw [htv]; apply div_nonneg <;> linarith
  have ht1 : t ≤ 1 / 3 := by
    rw [htv, div_le_iff₀ (by linarith)]; linarith
  have h1 := mem_logT hT ht0 ht1
  have e1 : Real.log (1 + t) - Real.log (1 - t) = Real.log (m / 2 ^ k) := by
    rw [← Real.log_div (by linarith) (by linarith)]
    congr 1
    rw [htv]; field_simp; ring
  rw [e1] at h1
  have h2 := mem_zsmul ((k : ℤ) - prec) mem_log2I
  have e3 : Real.log ((2 : ℝ) ^ k / 2 ^ prec) = ((k : ℤ) - prec : ℤ) * Real.log 2 := by
    rw [Real.log_div (by positivity) (by positivity), Real.log_pow, Real.log_pow]
    push_cast; ring
  have e2 : Real.log (m / 2 ^ prec) = Real.log (m / 2 ^ k) + ((k : ℤ) - prec : ℤ) * Real.log 2 := by
    have : (m : ℝ) / 2 ^ prec = (m / 2 ^ k) * (2 ^ k / 2 ^ prec) := by field_simp
    rw [this, Real.log_mul (by positivity) (by positivity), e3]
  rw [e2]
  exact mem_add h1 h2

attribute [local irreducible] logPt in
theorem mem_logI {x y : Ival} {a : ℝ} (hx : x.logI = some y) (ha : x.Mem a) :
    y.Mem (Real.log a) := by
  obtain ⟨lo, hi⟩ := x
  obtain ⟨h1, h2⟩ := ha
  have hp : (0 : ℝ) < 2 ^ prec := by positivity
  rcases lo with (_ | l) | l <;> rcases hi with h | h <;>
    simp only [logI, reduceCtorEq, Option.some.injEq] at hx
  subst hx
  simp only [Int.ofNat_eq_natCast, Int.cast_natCast] at h1 h2
  have hl0 : (0 : ℝ) < ((l + 1 : ℕ) : ℝ) := by positivity
  have ha0 : 0 < a := by nlinarith
  have hh0 : (0 : ℝ) < h := by nlinarith
  have hh0' : 0 < h := by exact_mod_cast hh0
  obtain ⟨p1, -⟩ := mem_logPt (m := l + 1) (by omega)
  obtain ⟨-, q2⟩ := mem_logPt hh0'
  have m1 : ((l + 1 : ℕ) : ℝ) / 2 ^ prec ≤ a := by rw [div_le_iff₀ hp]; exact h1
  have m2 : a ≤ (h : ℝ) / 2 ^ prec := by rw [le_div_iff₀ hp]; exact h2
  have l1 := Real.log_le_log (by positivity) m1
  have l2 := Real.log_le_log ha0 m2
  exact ⟨le_trans p1 (by nlinarith), le_trans (by nlinarith) q2⟩

/-! ### Proofs: `Hlog` -/

theorem hlogR_zero : hlogR 0 = 1 / 3 := by simp [hlogR]

theorem hlogR_of_ne {z : ℝ} (hz : z ≠ 0) :
    hlogR z = (Real.log (1 + z) - z + z ^ 2 / 2) / z ^ 3 := by simp [hlogR, hz]

theorem hCoeffs_mem : List.Forall₂ (fun (c : Ival) r => c.Mem r) hCoeffs
    ((List.range 32).map fun k : ℕ => (-1 : ℝ) ^ k / ((k : ℝ) + 3)) := by
  rw [hCoeffs, List.forall₂_map_left_iff, List.forall₂_map_right_iff, List.forall₂_same]
  intro k _
  have := mem_ofRat (cond (Nat.beq (k % 2) 0) 1 (-1)) (k + 3)
  rw [Nat.cast_add, Nat.cast_ofNat] at this
  convert this using 2
  rcases Nat.even_or_odd k with he | ho
  · have : k % 2 = 0 := Nat.even_iff.1 he
    simp [this, he.neg_one_pow]
  · have : k % 2 = 1 := Nat.odd_iff.1 ho
    simp [this, ho.neg_one_pow]

/-- `∑_{i < n+2} (-z)^{i+1}/(i+1) = -z + z²/2 - z³ ∑_{k<n} (-1)ᵏ zᵏ/(k+3)`. -/
theorem log_series_shift (z : ℝ) : ∀ n : ℕ,
    ∑ i ∈ Finset.range (n + 2), (-z) ^ (i + 1) / (i + 1) =
      -z + z ^ 2 / 2 - z ^ 3 * ∑ k ∈ Finset.range n, (-1) ^ k * z ^ k / (k + 3)
  | 0 => by simp [Finset.sum_range_succ]; ring
  | n + 1 => by
    rw [Finset.sum_range_succ, log_series_shift z n, Finset.sum_range_succ]
    push_cast
    have : (-z) ^ (n + 2 + 1) = -(z ^ 3 * ((-1) ^ n * z ^ n)) := by
      rw [neg_pow]; ring_nf
    rw [this]; ring

theorem hlog_series {z : ℝ} (h0 : 0 < z) (h1 : z ≤ 1 / 4) :
    |hlogR z - ∑ k ∈ Finset.range 32, (-1) ^ k * z ^ k / (k + 3)| ≤ 1 / 2 ^ prec := by
  have hx : |(-z)| < 1 := by rw [abs_neg, abs_of_pos h0]; linarith
  have h := Real.abs_log_sub_add_sum_range_le hx 34
  rw [log_series_shift z 32, abs_neg, abs_of_pos h0, sub_neg_eq_add] at h
  rw [hlogR_of_ne h0.ne']
  set P := ∑ k ∈ Finset.range 32, (-1) ^ k * z ^ k / (k + 3)
  have hz3 : 0 < z ^ 3 := by positivity
  have e : (Real.log (1 + z) - z + z ^ 2 / 2) / z ^ 3 - P =
      (-z + z ^ 2 / 2 - z ^ 3 * P + Real.log (1 + z)) / z ^ 3 := by
    field_simp; ring
  rw [e, abs_div, abs_of_pos hz3, div_le_iff₀ hz3]
  refine le_trans h ?_
  have hz' : 0 < 1 - z := by linarith
  rw [div_le_iff₀ hz']
  have e2 : z ^ (34 + 1) = z ^ 32 * z ^ 3 := by ring
  rw [e2]
  have : z ^ 32 ≤ (1 / 4) ^ 32 := pow_le_pow_left₀ h0.le h1 32
  have h4 : (1 / 4 : ℝ) ^ 32 ≤ 1 / 2 ^ prec * (3 / 4) := by norm_num [prec]
  have h5 : 1 / 2 ^ prec * (3 / 4) ≤ 1 / 2 ^ prec * (1 - z) := by
    gcongr; linarith
  nlinarith

theorem mem_ofRat_one_two : (ofRat 1 2).Mem (1 / 2) := by
  have := mem_ofRat 1 2; push_cast at this; exact this

theorem mem_hPt {m : ℕ} {I : Ival} (h : hPt m = some I) :
    I.Mem (hlogR (m / 2 ^ prec)) := by
  have hp : (0 : ℝ) < 2 ^ prec := by positivity
  unfold hPt at h
  cases hc : Nat.ble (4 * m) (2 ^ prec)
  · rw [hc, Bool.cond_false] at h
    have hm : 2 ^ prec < 4 * m := by
      by_contra h'; rw [Nat.ble_eq_true_of_le (Nat.le_of_not_lt h')] at hc; cases hc
    have hz : (1 : ℝ) / 4 < m / 2 ^ prec := by
      rw [lt_div_iff₀ hp]; have : ((2 ^ prec : ℕ) : ℝ) < ((4 * m : ℕ) : ℝ) := by exact_mod_cast hm
      push_cast at this; linarith
    set z : ℝ := m / 2 ^ prec
    have hz0 : z ≠ 0 := by intro h0; rw [h0] at hz; norm_num at hz
    simp only [Option.map_eq_some_iff] at h
    obtain ⟨w, hw, rfl⟩ := h
    have hZ : (point m).Mem z := by simpa [z] using mem_point (m : ℤ)
    have hL : (logPt (2 ^ prec + m)).Mem (Real.log (1 + z)) := by
      have := mem_logPt (m := 2 ^ prec + m) (by positivity)
      convert this using 2
      push_cast; simp only [z]; field_simp
    have hN := mem_add (mem_sub hL hZ) (mem_mul (mem_sq hZ) mem_ofRat_one_two)
    have hW := mem_inv hw (mem_mul (mem_sq hZ) hZ)
    have := mem_mul hN hW
    rw [hlogR_of_ne hz0]
    convert this using 1
    rw [div_eq_mul_inv]; ring
  · rw [hc, Bool.cond_true] at h
    simp only [Option.some.injEq] at h
    subst h
    have hm : 4 * m ≤ 2 ^ prec := Nat.le_of_ble_eq_true hc
    have hS := mem_hornerI (mem_point (m : ℤ)) _ _ hCoeffs_mem
    rw [hornerR_range] at hS
    set z : ℝ := m / 2 ^ prec
    have hzv : ((m : ℤ) : ℝ) / 2 ^ prec = z := by simp [z]
    rw [hzv] at hS
    set P := ∑ k ∈ Finset.range 32, (-1 : ℝ) ^ k / (k + 3) * z ^ k
    have hP : P = ∑ k ∈ Finset.range 32, (-1) ^ k * z ^ k / (k + 3) :=
      Finset.sum_congr rfl fun k _ => by ring
    obtain ⟨s1, s2⟩ := hS
    have herr : |hlogR z - P| ≤ 1 / 2 ^ prec := by
      rcases Nat.eq_zero_or_pos m with h0 | h0
      · have : z = 0 := by simp [z, h0]
        rw [this, hlogR_zero]
        simp [P, this, Finset.sum_range_succ]
      · have hz0 : 0 < z := by simp only [z]; positivity
        have hz1 : z ≤ 1 / 4 := by
          simp only [z]; rw [div_le_iff₀ hp]
          have : ((4 * m : ℕ) : ℝ) ≤ ((2 ^ prec : ℕ) : ℝ) := by exact_mod_cast hm
          push_cast at this; linarith
        rw [hP]; exact hlog_series hz0 hz1
    rw [abs_le] at herr
    have e1 : (1 : ℝ) / 2 ^ prec * 2 ^ prec = 1 := by field_simp
    simp only [Mem]
    push_cast
    constructor <;> nlinarith

/-! #### Monotonicity of `Hlog` -/

/-- `F(z) = log(1 + z) - z + z²/2` and its derivative `z²/(1 + z)`. -/
theorem hasDerivAt_F {x : ℝ} (hx : -1 < x) :
    HasDerivAt (fun z => Real.log (1 + z) - z + z ^ 2 / 2) ((1 + x)⁻¹ - 1 + x) x := by
  have h1 : HasDerivAt (fun z => 1 + z) 1 x := (hasDerivAt_id' x).const_add 1
  have h2 := h1.log (by linarith)
  refine ((h2.sub (hasDerivAt_id' x)).add ((hasDerivAt_pow 2 x).div_const 2)).congr_deriv ?_
  push_cast; ring

theorem F_le_cube {z : ℝ} (hz : 0 ≤ z) : Real.log (1 + z) - z + z ^ 2 / 2 ≤ z ^ 3 / 3 := by
  let G : ℝ → ℝ := fun z => z ^ 3 / 3 - (Real.log (1 + z) - z + z ^ 2 / 2)
  have hG : ∀ x, -1 < x → HasDerivAt G (x ^ 2 - ((1 + x)⁻¹ - 1 + x)) x := fun x hx => by
    refine (((hasDerivAt_pow 3 x).div_const 3).sub (hasDerivAt_F hx)).congr_deriv ?_
    push_cast; ring
  have hmono : MonotoneOn G (Set.Ici 0) := by
    apply monotoneOn_of_deriv_nonneg (convex_Ici 0)
    · intro x hx; exact (hG x (by simp at hx; linarith)).continuousAt.continuousWithinAt
    · intro x hx
      rw [interior_Ici] at hx
      exact (hG x (by simp at hx; linarith)).differentiableAt.differentiableWithinAt
    · intro x hx
      rw [interior_Ici] at hx
      have hx0 : 0 < x := hx
      rw [(hG x (by linarith)).deriv]
      have : x ^ 2 - ((1 + x)⁻¹ - 1 + x) = x ^ 3 / (1 + x) := by field_simp; ring
      rw [this]; positivity
  have := hmono (Set.mem_Ici.2 le_rfl) (Set.mem_Ici.2 hz) hz
  simp only [G] at this
  norm_num at this
  linarith

theorem cube_le_F {z : ℝ} (hz : 0 ≤ z) :
    z ^ 3 / (1 + z) ≤ 3 * (Real.log (1 + z) - z + z ^ 2 / 2) := by
  let M : ℝ → ℝ := fun z => 3 * (Real.log (1 + z) - z + z ^ 2 / 2) - z ^ 3 / (1 + z)
  have hM : ∀ x, -1 < x →
      HasDerivAt M (3 * ((1 + x)⁻¹ - 1 + x) -
        (3 * x ^ 2 * (1 + x) - x ^ 3 * 1) / (1 + x) ^ 2) x := fun x hx => by
    have h1 : HasDerivAt (fun z => 1 + z) 1 x := (hasDerivAt_id' x).const_add 1
    refine (((hasDerivAt_F hx).const_mul 3).sub
      ((hasDerivAt_pow 3 x).div h1 (by linarith))).congr_deriv ?_
    push_cast; ring
  have hmono : MonotoneOn M (Set.Ici 0) := by
    apply monotoneOn_of_deriv_nonneg (convex_Ici 0)
    · intro x hx; exact (hM x (by simp at hx; linarith)).continuousAt.continuousWithinAt
    · intro x hx
      rw [interior_Ici] at hx
      exact (hM x (by simp at hx; linarith)).differentiableAt.differentiableWithinAt
    · intro x hx
      rw [interior_Ici] at hx
      have hx0 : 0 < x := hx
      rw [(hM x (by linarith)).deriv]
      have : 3 * ((1 + x)⁻¹ - 1 + x) - (3 * x ^ 2 * (1 + x) - x ^ 3 * 1) / (1 + x) ^ 2 =
          x ^ 3 / (1 + x) ^ 2 := by field_simp; ring
      rw [this]; positivity
  have := hmono (Set.mem_Ici.2 le_rfl) (Set.mem_Ici.2 hz) hz
  simp only [M] at this
  norm_num at this
  linarith

theorem hlogR_antitoneOn_pos : AntitoneOn hlogR (Set.Ioi 0) := by
  let g : ℝ → ℝ := fun z => (Real.log (1 + z) - z + z ^ 2 / 2) / z ^ 3
  have hg : ∀ x, 0 < x → HasDerivAt g
      ((((1 + x)⁻¹ - 1 + x) * x ^ 3 - (Real.log (1 + x) - x + x ^ 2 / 2) * (3 * x ^ 2)) /
        (x ^ 3) ^ 2) x := fun x hx => by
    refine ((hasDerivAt_F (by linarith : -1 < x)).div (hasDerivAt_pow 3 x)
      (by positivity)).congr_deriv ?_
    push_cast; ring
  have hanti : AntitoneOn g (Set.Ioi 0) := by
    apply antitoneOn_of_deriv_nonpos (convex_Ioi 0)
    · intro x hx; exact (hg x hx).continuousAt.continuousWithinAt
    · intro x hx
      rw [interior_Ioi] at hx
      exact (hg x hx).differentiableAt.differentiableWithinAt
    · intro x hx
      rw [interior_Ioi] at hx
      have hx0 : 0 < x := hx
      rw [(hg x hx0).deriv]
      apply div_nonpos_of_nonpos_of_nonneg _ (by positivity)
      have h1 := cube_le_F hx0.le
      have e : ((1 + x)⁻¹ - 1 + x) * x ^ 3 = x ^ 2 * (x ^ 3 / (1 + x)) := by
        field_simp; ring
      rw [e]
      have : 0 ≤ x ^ 2 := sq_nonneg x
      nlinarith
  intro x hx y hy hxy
  rw [hlogR_of_ne (ne_of_gt hx), hlogR_of_ne (ne_of_gt hy)]
  exact hanti hx hy hxy

theorem hlogR_antitoneOn : AntitoneOn hlogR (Set.Ici 0) := by
  intro x hx y hy hxy
  simp only [Set.mem_Ici] at hx hy
  rcases hx.lt_or_eq with hx0 | hx0
  · exact hlogR_antitoneOn_pos hx0 (lt_of_lt_of_le hx0 hxy) hxy
  · subst hx0
    rcases hy.lt_or_eq with hy0 | hy0
    · rw [hlogR_zero, hlogR_of_ne hy0.ne', div_le_iff₀ (by positivity)]
      have := F_le_cube hy; linarith
    · subst hy0; exact le_rfl

theorem mem_hlogI {x y : Ival} {a : ℝ} (hx : x.hlogI = some y) (ha : x.Mem a) :
    y.Mem (hlogR a) := by
  obtain ⟨h1, h2⟩ := ha
  have hp : (0 : ℝ) < 2 ^ prec := by positivity
  unfold hlogI at hx
  split at hx
  · rename_i l h hl hh
    rw [hl] at h1; rw [hh] at h2
    simp only [Int.ofNat_eq_natCast, Int.cast_natCast] at h1 h2
    split at hx
    · rename_i A B hA hB
      cases hx
      have m1 : (l : ℝ) / 2 ^ prec ≤ a := by rw [div_le_iff₀ hp]; exact h1
      have m2 : a ≤ (h : ℝ) / 2 ^ prec := by rw [le_div_iff₀ hp]; exact h2
      have hl0 : (0 : ℝ) ≤ l / 2 ^ prec := by positivity
      have ha0 : 0 ≤ a := le_trans hl0 m1
      have k1 := hlogR_antitoneOn (Set.mem_Ici.2 ha0) (Set.mem_Ici.2 (le_trans ha0 m2)) m2
      have k2 := hlogR_antitoneOn (Set.mem_Ici.2 hl0) (Set.mem_Ici.2 ha0) m1
      obtain ⟨p1, -⟩ := mem_hPt hA
      obtain ⟨-, q2⟩ := mem_hPt hB
      exact ⟨le_trans p1 (by nlinarith), le_trans (by nlinarith) q2⟩
    · cases hx
  · cases hx

end Ival

end SmoothedOctagon.Interval
