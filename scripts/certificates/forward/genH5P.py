import sympy as sp
from leangen2 import lean_poly
m,v,z=sp.symbols('m v z')
exec(open('genH5R.py').read().split("def hom_cert")[0].split("m,v,mu=sp.symbols('m v mu')")[1])
L=lambda p: lean_poly(p,(m,v))
txt=f'''
/-- The cubic `P` of the rational bound of the integral `H₅`, with `l = λ`. -/
noncomputable def fs_H5P (z l v : ℝ) : ℝ :=
  (z + l) ^ 2 * v ^ 3 - 3 * z * (1 - l) * (1 + z) * (z + l) * v ^ 2 +
    ((1 + l) * (1 - l) * (1 + z) * z * (3 * (z - 1) + (1 - l)) - 6 * (z + l) * (z - l) * (1 - z * l)) * v +
    (1 + l) * (1 - l) * (1 + z) * (3 * (z - 1) + (1 - l)) * (z - l)

/-- **`P > 0`** (H5_INTEGRAL_RATIONAL_BOUND §§3-4): `(2 - m)³P = R₀ + R₁p + R₂p² + R₃p³`,
`m = 1 - λ`, `p = (2 - m)z - (2 + m) = U - 3`. -/
theorem fs_H5P_pos {{z l v : ℝ}} (hl0 : 0 < l) (hl1 : l < 1) (hvm : 1 - l ≤ v) (hv1 : v ≤ 1)
    (hv0 : 0 < v) (hp : 0 ≤ (1 + l) * z - (3 - l)) : 0 < fs_H5P z l v := by
  obtain ⟨m, rfl⟩ : ∃ m, l = 1 - m := ⟨1 - l, by ring⟩
  have hm0 : 0 ≤ m := by linarith
  have hmv : m ≤ v := by linarith
  have h0 := fs_H5_R0 hm0 hmv hv1 hv0
  have h1 := fs_H5_R1 hm0 hmv hv1
  have h2 := fs_H5_R2 hm0 hmv hv1
  have h3 := fs_H5_R3 hm0 hmv hv1
  have key : (2 - m) ^ 3 * fs_H5P z (1 - m) v =
      ({L(R0)}) + ({L(R1)}) * ((2 - m) * z - (2 + m)) +
      ({L(R2)}) * ((2 - m) * z - (2 + m)) ^ 2 +
      ({L(R3)}) * ((2 - m) * z - (2 + m)) ^ 3 := by
    unfold fs_H5P; ring
  have hp' : 0 ≤ (2 - m) * z - (2 + m) := by linarith
  have hpos : 0 < (2 - m) ^ 3 * fs_H5P z (1 - m) v := by
    rw [key]
    have := mul_nonneg h1 hp'
    have := mul_nonneg h2 (pow_nonneg hp' 2)
    have := mul_nonneg h3 (pow_nonneg hp' 3)
    linarith
  exact pos_of_mul_pos_right hpos (by have : 0 < 2 - m := by linarith
                                      positivity)
'''
open('H5P.lean','w').write(txt)
