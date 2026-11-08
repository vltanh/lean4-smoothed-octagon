"""Exact exploratory algebra for vertex words of the Reinhardt system.

Domain: margins p_i > 0 with p_0*p_1+p_1*p_2+p_2*p_0 = 4.
Each vertex arc has w > 1 and w < 1+p_(i-1)/p_i.  These strict
inequalities are mathematical hypotheses; this script does not decide
them.  The symbolic substitutions below impose the terminal state twist
for the two distinct-letter words of length three.  They do not presume
the terminal group constraint.

Reproduction: python explorations/vertex_word_algebra.py
Used Python 3.12.14 and SymPy 1.14.0.  Only exact rational expressions
are used.  There is no optimization, sampled feasibility check, floating
point tolerance, or enumeration of longer words.

This is exploratory/reproducibility support, not a proof certificate.
The hand argument and all sign hypotheses are in
docs/VERTEX_WORD_REDUCTION.md.  In particular, zero symbolic residuals
do not certify the unrestricted Reinhardt conjecture or kernel checking.
"""

import sys

import sympy as sp


Z = (
    sp.Matrix([[0, 1], [1, 0]]),
    sp.Matrix([[1, -2], [0, -1]]),
    sp.Matrix([[-1, -2], [0, 1]]),
)
R = sp.Matrix([[sp.Rational(1, 2), -sp.Rational(3, 2)],
               [sp.Rational(1, 2), sp.Rational(1, 2)]])


def factor_matrix(matrix):
    return matrix.applyfunc(sp.factor)


def state(p):
    """Reconstruct the scaled traceless state from its three margins."""
    total = sum(p)
    return sum(((total - p[i]) * Z[i] for i in range(3)), sp.zeros(2)) / 4


def vertex_arc(p, i, w):
    """Exact endpoint state and right group factor, without sampling."""
    x = state(p)
    a = p[i]
    group_factor = sp.eye(2) + a * (
        (w - 1 / w) * x + (w + 1 / w - 2) * x * Z[i]
    ) / 4
    result = list(p)
    result[(i + 1) % 3] = (a + p[(i + 1) % 3]) * w - a
    result[(i - 1) % 3] = (a + p[(i - 1) % 3]) / w - a
    return [sp.factor(v) for v in result], factor_matrix(group_factor)


def word(initial, letters, parameters):
    p = list(initial)
    g = sp.eye(2)
    for i, w in zip(letters, parameters, strict=True):
        p, factor = vertex_arc(p, i, w)
        g = factor_matrix(g * factor)
    return p, g


def main():
    print(f"Python {sys.version.split()[0]}; SymPy {sp.__version__}")
    a, b, B, C = sp.symbols("a b B C", positive=True)
    c = (4 - a * b) / (a + b)
    initial = [a, b, c]
    target = [c, a, b]

    forward_w = [
        (a + B) / (a + b),
        (a + B) * (b + B) / (B**2 + 4),
        (b + B) / (a + b),
    ]
    forward_p, forward_g = word(initial, [0, 1, 2], forward_w)
    print("forward state-twist residual:",
          [sp.factor(v - t) for v, t in zip(forward_p, target)])
    forward_det = 2 * (4 + a * b - B * (a + b)) / (B**2 + 4)
    print("forward determinant identity residual:",
          sp.factor((forward_g - R).det() - forward_det))
    B0 = (a * b + 4) / (a + b)
    denominator = (a * b + 4)**2 + 4 * (a + b)**2
    positive_1 = a * (b**2 + 4) + b * (12 - b**2)
    positive_2 = 4 * (a + b)**2 + a * b * (16 - (a - b)**2)
    forward_entry = a * positive_1 * positive_2 / (
        8 * (a + b)**2 * denominator
    )
    print("forward final-entry identity residual:",
          sp.factor((forward_g[1, 1] - R[1, 1]).subs(B, B0) - forward_entry))

    Brev = (4 - a * C) / (a + C)
    reverse_w = [
        (a + c) / (a + C),
        (Brev + C) / (a + C),
        (a + b) / (a + C),
    ]
    reverse_p, reverse_g = word(initial, [0, 2, 1], reverse_w)
    print("reverse state-twist residual:",
          [sp.factor(v - t) for v, t in zip(reverse_p, target)])
    reverse_det = 4 * a * C * (a + C)**2 / ((a**2 + 4) * (C**2 + 4))
    print("reverse determinant identity residual:",
          sp.factor((reverse_g - R).det() - reverse_det))


if __name__ == "__main__":
    main()
