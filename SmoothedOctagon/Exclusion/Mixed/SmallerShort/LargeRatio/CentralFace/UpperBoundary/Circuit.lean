module

public import SmoothedOctagon.Exclusion.Mixed.SmallerShort.LargeRatio.CentralFace

/-!
# The exact upper beta boundary

The strong order bounds beta by `x + x(7x+1)(a-1)/(4x²+11x+1)`.
Multiplication by the fourth power of its denominator clears each central
numerator. The formula below keeps the scaled norm, diagonal and pairing
in factored form.
-/

@[expose] public section
namespace SmoothedOctagon.S0Central

def gapDenominator {R : Type*} [CommRing R] (x : R) : R := 4 * x ^ 2 + 11 * x + 1

def betaNumerator {R : Type*} [CommRing R] (x a : R) : R :=
  x * gapDenominator x + x * (7 * x + 1) * (a - 1)

def cleared {R : Type*} [CommRing R]
    (e1 e2 e3 e4 c1 c2 c3 c4 c5 c6 : R) (x a : R) : R :=
  let q := gapDenominator x
  let b := betaNumerator x a
  let S := x + 1
  let K := x ^ 2 + 2 * x + a ^ 2
  let B := a * q + b
  let U := 3 * S * (35 * x + 13) * (b - q) + (x - 1) ^ 2 * (b + (7 * x - 8) * q)
  let V := 4 * S * (35 * x + 13) * (b - q)
  let D := (a ^ 2 + 1 + 2 * x) * q + 2 * (a - x) * b
  let E := S ^ 3 * (U - V) + (3 * S - 1) * V
  let W := q ^ 2 * S ^ 2 * (S ^ 2 - S + 1) * V + D ^ 2 * U - q * D * E
  let L := 2 * D * U - q * E
  e1 * q * a * B * K * L - (e2 * a * B + e3 * q * K) * W - e4 * q * B ^ 2 * K ^ 2 * U +
    V * (q * (c1 * B ^ 2 * K ^ 2 + c2 * a ^ 2 * B ^ 2 * K) +
      q ^ 2 * (c3 * a * B * K ^ 2 + c4 * a ^ 3 * B * K) +
      q ^ 3 * (c5 * K ^ 3 + c6 * a ^ 2 * K ^ 2))

def numerator2 {R : Type*} [CommRing R] (x a : R) : R :=
  cleared 72 180 0 72 72 (-180) 151 72 0 (-72) x a

def numeratorT {R : Type*} [CommRing R] (x a : R) : R :=
  cleared 8 4 8 8 8 (-8) (-5) 8 8 (-8) x a

def numerator8 {R : Type*} [CommRing R] (x a : R) : R :=
  cleared 72 36 64 72 72 (-81) (-37) 72 64 (-72) x a

theorem numerator2_link (x a : ℝ) (hq : gapDenominator x ≠ 0) :
    (gapDenominator x) ^ 4 *
      lgrN2 (x + 1) (x ^ 2 + 2 * x + a ^ 2) a
        (a + betaNumerator x a / gapDenominator x)
        (lgrUc x (betaNumerator x a / gapDenominator x))
        (lgrVc x (betaNumerator x a / gapDenominator x))
        (ssDg x (betaNumerator x a / gapDenominator x) a) = numerator2 x a := by
  unfold lgrN2 lgrLN lgrWN lgrUc lgrVc ssDg numerator2 cleared
  dsimp only
  field_simp
  ring

theorem numeratorT_link (x a : ℝ) (hq : gapDenominator x ≠ 0) :
    (gapDenominator x) ^ 4 *
      lgrNT (x + 1) (x ^ 2 + 2 * x + a ^ 2) a
        (a + betaNumerator x a / gapDenominator x)
        (lgrUc x (betaNumerator x a / gapDenominator x))
        (lgrVc x (betaNumerator x a / gapDenominator x))
        (ssDg x (betaNumerator x a / gapDenominator x) a) = numeratorT x a := by
  unfold lgrNT lgrLN lgrWN lgrUc lgrVc ssDg numeratorT cleared
  dsimp only
  field_simp
  ring

theorem numerator8_link (x a : ℝ) (hq : gapDenominator x ≠ 0) :
    (gapDenominator x) ^ 4 *
      lgrN8 (x + 1) (x ^ 2 + 2 * x + a ^ 2) a
        (a + betaNumerator x a / gapDenominator x)
        (lgrUc x (betaNumerator x a / gapDenominator x))
        (lgrVc x (betaNumerator x a / gapDenominator x))
        (ssDg x (betaNumerator x a / gapDenominator x) a) = numerator8 x a := by
  unfold lgrN8 lgrLN lgrWN lgrUc lgrVc ssDg numerator8 cleared
  dsimp only
  field_simp
  ring

end SmoothedOctagon.S0Central
