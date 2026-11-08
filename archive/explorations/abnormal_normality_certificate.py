#!/usr/bin/env python3
"""Exact algebra companion to docs/GLOBAL_NORMALITY.md.

Run from the repository root:
    python explorations/abnormal_normality_certificate.py

Requires Python 3 and SymPy. The test has 22 fixed named algebraic checks;
there are no random inputs, numerical optimizers, ODE integrations, or
word-length searches. Symbols b,c,q are positive, and the displayed
rational identities hold where their denominators are defined. The
mathematical proof separately uses b,c,q>1 and strict-star inequalities.

This checks the displayed matrix formulas and scalar expansions. It does
not prove the PMP interface, positivity, backwards transport, compactness,
or the global word argument, and is not a Lean or independent peer review.
"""
import platform
import sympy as s


def main():
    checks = []

    def equal(name, actual, expected):
        delta = actual - expected
        entries = list(delta) if isinstance(delta, s.MatrixBase) else [delta]
        if any(s.cancel(e) != 0 for e in entries):
            raise AssertionError(name + ': ' + str(delta))
        checks.append(name)

    identity = s.eye(2)
    d = [s.Matrix([[-1, 0], [0, 1]]),
         s.Matrix([[1, -2], [0, -1]]),
         s.Matrix([[1, 0], [2, -1]])]
    b, c, q = s.symbols('b c q', positive=True)
    p0, p1, p2 = s.symbols('p0 p1 p2', positive=True)

    def v(matrix):
        return s.Matrix([matrix[0, 0], matrix[0, 1], matrix[1, 0]])

    def factor(label, z):
        return (z + 1/z)*identity/2 + (1/z - z)*d[label]/2

    def half_factor(label, z):
        # sqrt(z)*T_label(sqrt(z)); the scalar cancels in conjugations.
        return (z + 1)*identity/2 + (1 - z)*d[label]/2

    def ad(matrix, vector):
        return matrix*vector*matrix.inv()

    state = s.Matrix([-p0/2, (p0 + p2)/2, (-p0 - p1)/2])
    for label in range(3):
        equal('D_%d squared' % label, d[label]*d[label], identity)
    equal('three D matrices span sl2', s.Matrix.hstack(*map(v, d)).det(), 4)

    def data(second, third):
        upper = s.Matrix.hstack(v(d[0]), v(d[second]),
                               v(ad(factor(second, b), d[third])))
        lower = s.Matrix.hstack(v(d[0]), v(d[second]),
                               v(ad(half_factor(second, b), d[third])))
        linear = lower*upper.inv()

        def residual(label, upper_prefix=identity, lower_prefix=identity):
            return (v(ad(lower_prefix, d[label]))
                    - linear*v(ad(upper_prefix, d[label])))

        r1 = residual(third)
        r2 = residual(0, factor(second, b), half_factor(second, b))
        full = factor(second, b)*factor(third, c)
        half = half_factor(second, b)*half_factor(third, c)
        return upper.det(), linear, r1, r2, residual(0, full, half), residual(second, full, half)

    df, lf, rf1, rf2, uf, ubf = data(1, 2)
    dr, lr, rr1, rr2, ur, ubr = data(2, 1)
    equal('forward upper determinant', df, 4*b**2)
    equal('reverse upper determinant', dr, -4/b**2)
    equal('forward transfer L', lf, s.Matrix([[1, 0, (1-b)/b],
                                              [0, 1, (b-1)/b], [0, 0, 1/b]]))
    equal('reverse transfer L', lr, s.Matrix([[1, 1-b, 0],
                                              [0, b, 0], [0, 1-b, 1]]))
    equal('forward first needle', rf1, 2*(b-1)/b*s.Matrix([1, -1, 1]))
    equal('forward second needle', rf2, s.Matrix([0, -2*(b-1)/b**2, 0]))
    equal('reverse first needle', rr1, 2*(b-1)*s.Matrix([-1, 1, -1]))
    equal('reverse second needle', rr2, s.Matrix([0, 0, -2*b*(b-1)]))
    equal('0120 fourth residual', uf, s.Matrix([
        -2*c*(b-1)*(c-1),
        2*c*(b-1)/b**2*(b*(b-1)*(c-1)-c), -2*b*c*(c-1)]))
    equal('0210 fourth residual', ur, -2/(b*c**2)*s.Matrix([
        (b-1)*(c-1), c-1, (b-1)*((c-1)+b*(b-c+1))]))
    equal('0121 triple-tie identity', ubf, b**2*(c-1)/(c**2*(b-1))*rf1)
    equal('0212 triple-tie identity', ubr, c*(c-1)/(b*(b-1))*rr1)
    sf = (c-1)*(b**2*(p1+p2)-p1)+(b-1)*p1
    sr = (c-1)*(p1-(b-1)*p2)+b*(b-1)*p2
    equal('forward first cross pairing', state.cross(uf).dot(rf1),
          -2*c*(b-1)/b**3*sf)
    equal('forward second cross pairing', state.cross(uf).dot(rf2),
          2*c*(b-1)*(c-1)/b**2*(p0-(b-1)*p1))
    equal('reverse first cross pairing', state.cross(ur).dot(rr1),
          2*(b-1)/c**2*sr)
    equal('reverse second cross pairing', state.cross(ur).dot(rr2),
          -2*(b-1)*(c-1)/c**2*(b*p0+(b-1)*p2))
    equal('terminal triple tie, vertex 1',
          v(ad(half_factor(0, q), d[1])-ad(factor(0, q), d[1])),
          s.Matrix([0, 2*q*(q-1), 0]))
    equal('terminal triple tie, vertex 2',
          v(ad(half_factor(0, q), d[2])-ad(factor(0, q), d[2])),
          s.Matrix([0, 0, 2*(q-1)/q**2]))
    assert len(checks) == 22
    print('Python', platform.python_version(), 'SymPy', s.__version__)
    for name in checks:
        print('PASS', name)
    print('PASS all 22 fixed exact algebra checks')


if __name__ == '__main__':
    main()
