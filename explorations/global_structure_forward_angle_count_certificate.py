"""Exact arithmetic supplement to GLOBAL_STRUCTURE_FORWARD_ANGLE_COUNT.

Python 3 standard library only. Fixed rational identities, no scans,
optimization, period enumeration, Lean, Lake, typechecking, or CI.
The hand proof supplies all trigonometric and PMP/winding implications.
Run: python explorations/global_structure_forward_angle_count_certificate.py
"""

from fractions import Fraction as F


checks = 0


def check(condition):
    global checks
    assert condition
    checks += 1


eps_upper = F(11, 672)
lower = F(3, 2) - F(3, 4) * eps_upper**2 - F(13, 15) * eps_upper
check(F(22, 7) / 192 == eps_upper)
check(F(26, 15) ** 2 - 3 == F(1, 225))
check(lower == F(13417577, 9031680))
check(lower - F(205, 138) == F(21871, 207728640))
check(lower > F(205, 138))
check(F(16, 3) * F(3, 32) == F(1, 2))
check(F(192, 3) == 64)
check(61 % 3 == 1 and 64 % 3 == 1)

print(f"{checks} exact rational identities/sign checks passed")
