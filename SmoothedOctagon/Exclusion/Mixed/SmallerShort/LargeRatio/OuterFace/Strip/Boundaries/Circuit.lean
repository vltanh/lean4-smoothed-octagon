module

public import SmoothedOctagon.Exclusion.Mixed.SmallerShort.LargeRatio.OuterFace
public import SmoothedOctagon.Exclusion.Mixed.SmallerShort.LargeRatio.CentralFace.UpperBoundary.Circuit

/-!
# Cleared outer numerators at an order boundary

For beta represented as `b/q`, multiplication by `q^4` clears every
denominator in its numerator. The norm and pairing remain factored.
-/

@[expose] public section
namespace SmoothedOctagon.S0Outer.Boundaries

def cleared {R : Type*} [CommRing R]
    (e1 e2 e3 e4 c1 c2 c3 x a q b : R) : R :=
  let S := x + 1
  let M := 6 * a ^ 2 + 1
  let B := a * q + b
  let U := 3 * S * (35 * x + 13) * (b - q) + (x - 1) ^ 2 * (b + (7 * x - 8) * q)
  let V := 4 * S * (35 * x + 13) * (b - q)
  let D := (a ^ 2 + 1 + 2 * x) * q + 2 * (a - x) * b
  let E := M * (S ^ 2 * (U - V) + V) + (2 * S - 1) * S * V
  let W := q ^ 2 * S * (M ^ 2 - M * S + S ^ 2) * V + S * D ^ 2 * U - q * D * E
  let L := 2 * S * D * U - q * E
  e1 * q * a ^ 2 * B * L - (e2 * B + e3 * q * a) * W - e4 * q * a ^ 3 * B ^ 2 * S * U +
    V * (q * c1 * a ^ 3 * B ^ 2 * S + q ^ 2 * c2 * a ^ 4 * B * S + q ^ 3 * c3 * a ^ 5 * S)

def numerator2 {R : Type*} [CommRing R] (x a q b : R) : R :=
  cleared 504 180 0 3528 2268 7903 (-3528) x a q b

theorem numerator2_link (x a q b : ℝ) (hq : q ≠ 0) :
    q ^ 4 * lgrNo2 (x + 1) a (a + b / q)
      (lgrUc x (b / q)) (lgrVc x (b / q)) (ssDg x (b / q) a) = numerator2 x a q b := by
  unfold lgrNo2 lgrWoN lgrLoN lgrUc lgrVc ssDg numerator2 cleared
  dsimp only
  field_simp
  ring

def numeratorT {R : Type*} [CommRing R] (x a q b : R) : R :=
  cleared 56 4 56 392 336 (-189) 2352 x a q b

theorem numeratorT_link (x a q b : ℝ) (hq : q ≠ 0) :
    q ^ 4 * lgrNoT (x + 1) a (a + b / q)
      (lgrUc x (b / q)) (lgrVc x (b / q)) (ssDg x (b / q) a) = numeratorT x a q b := by
  unfold lgrNoT lgrWoN lgrLoN lgrUc lgrVc ssDg numeratorT cleared
  dsimp only
  field_simp
  ring

def numerator8 {R : Type*} [CommRing R] (x a q b : R) : R :=
  cleared 1008 72 896 7056 5922 (-2618) 36848 x a q b

theorem numerator8_link (x a q b : ℝ) (hq : q ≠ 0) :
    q ^ 4 * lgrNo8 (x + 1) a (a + b / q)
      (lgrUc x (b / q)) (lgrVc x (b / q)) (ssDg x (b / q) a) = numerator8 x a q b := by
  unfold lgrNo8 lgrWoN lgrLoN lgrUc lgrVc ssDg numerator8 cleared
  dsimp only
  field_simp
  ring

end SmoothedOctagon.S0Outer.Boundaries
