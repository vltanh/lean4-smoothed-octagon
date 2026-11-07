#!/usr/bin/env python3
"""Exact cross-check of docs/LOCAL_FORWARD_SIX.md; not a proof of L1.

Run: OPENBLAS_NUM_THREADS=1 python3 explorations/local_forward_stationary_obstruction.py
Finite input: word 012012, factors (11/10,11/10,121/100,121/100,11/10,121/100),
raw initial margins (1,1,4761/3950). No randomness, optimization or sampling.
Uses SymPy rational differentiation and exact comparisons, not floats. Runtime
versions are printed. The hand note contains the actual mathematical argument.
The result is a strict SAME-WORD local minimum only: different-word or nonlocal
replacements remain possible. No claim of arbitrary-control optimality or a
counterexample to Reinhardt. No Lean/Lake/CI command is executed.
"""
import json
import platform
import sympy as S


def main():
    t, L = S.symbols('t L')
    qs = S.symbols('q1:7', positive=True)
    base = S.Rational(11, 10)
    qvals = [base, base, base**2, base**2, base, base**2]
    word = [0, 1, 2, 0, 1, 2]
    t0 = S.Rational(4761, 3950)
    sigma2 = S.Rational(1975, 1684)
    sub = dict(zip(qs, qvals))
    logsub = {S.log(base): L, S.log(base**2): 2*L}

    def fixed(expr):
        return S.expand(expr.subs(sub).xreplace(logsub))

    p, F, j = S.Matrix([1, 1, t]), S.eye(2), S.Integer(0)
    for i, q in zip(word, qs):
        a, b, c = p[i], p[(i+1) % 3], p[(i-1) % 3]
        j += a/8 * ((a+b)*(q-1)+(a+c)*(1-1/q)-a*S.log(q))
        p = p.copy()
        p[(i+1) % 3] = (a+b)*q-a
        p[(i-1) % 3] = (a+c)/q-a
        T = [S.diag(q, 1/q), S.Matrix([[1/q, q-1/q], [0, q]]),
             S.Matrix([[1/q, 0], [1/q-q, q]])][i]
        F = F*T
    E = [F[0, 0], F[0, 1], F[1, 0], p[0], p[1]]
    M = S.Matrix([[fixed(S.diff(e, q)) for q in qs] for e in E])
    c = S.Matrix([[fixed(S.diff(j, q)) for q in qs]])
    w = S.Matrix([1, S.Rational(3049, 23100), S.Rational(115641, 100000),
                  -S.Rational(115641, 100000), -S.Rational(3049, 23100), -base])
    expected_minor = -S.Rational(362717989263, 20796875000000000000000000) * (
        1750*t+2689)*(787648050*t+11392799401)
    assert S.factor(M[:, :5].det()-expected_minor) == 0
    assert all(S.factor(e) == 0 for e in M*w)
    expected_first = (3950*t-4761) * (
        170241480950*L*t+167093446379*L-20663242950*t-22373451219
    ) / 2541000000000000
    assert S.factor((c*w)[0]-expected_first) == 0
    assert fixed(F[0, 0]) > 0
    assert sigma2*(1+2*t0) == 4
    assert S.factor(sigma2*fixed(j).subs(t, t0) -
                    (147129319-407979220*L)/234143360) == 0

    HE = [S.Matrix([[fixed(S.diff(e, qi, qj)).subs(t, t0) for qj in qs]
                    for qi in qs]) for e in E]
    HJ = S.Matrix([[fixed(S.diff(j, qi, qj)).subs(t, t0) for qj in qs]
                   for qi in qs])
    A0 = M[:, :5].subs(t, t0)
    multipliers = c[:, :5].subs(t, t0)*A0.inv()
    expected_Q = (79359517360976760690-828902398596084416617*L) / S.Integer(
        58144054680260010000)
    Q = sigma2*((w.T*HJ*w)[0] - sum(
        multipliers[k]*(w.T*HE[k]*w)[0] for k in range(5)))
    assert S.factor(Q-expected_Q) == 0
    assert expected_Q.subs(L, S.Rational(143, 1500)) > S.Rational(1, 200)

    # Exact whole-arc sector checks, using Bernstein coefficients.
    U = lambda pp: S.Matrix([[-pp[0], pp[0]+pp[2]], [-pp[0]-pp[1], pp[0]]])/2
    Ds = [S.diag(-1, 1), S.Matrix([[1, -2], [0, -1]]),
          S.Matrix([[1, 0], [2, -1]])]
    vs = [S.Matrix(vv) for vv in [(1, 1), (1, 0), (0, -1), (-1, -1)]]
    lowers = [
        [[0, 293, 645], [10000, 10323, 10646]],
        [[586, 969, 1383], [9678, 9937, 10148]],
        [[1258, 2142, 3161], [9225, 9659, 9910]],
        [[2613, 3594, 4873], [8190, 8404, 8618]],
        [[4027, 4628, 5229], [7122, 7229, 7274]],
        [[4753, 5887, 6991], [6613, 6808, 6736]],
    ]
    u, z = S.symbols('u z')
    p, g = S.Matrix([1, 1, t0]), S.eye(2)
    margins = [list(p)]
    for k, (i, q) in enumerate(zip(word, qvals)):
        step = S.eye(2)+sigma2*p[i]/4 * (
            (z-1/z)*U(p)-(z+1/z-2)*U(p)*Ds[i])
        gg = g*step
        for contact in range(3):
            v, vn = vs[contact], vs[contact+1]
            gv = gg*v
            for side, expr in enumerate([
                    -S.det(S.Matrix.hstack(v, gv)),
                    -S.det(S.Matrix.hstack(gv, vn))]):
                poly = S.Poly(S.cancel(z*expr).subs(z, 1+(q-1)*u).expand(), u)
                a, b, cc = [poly.nth(n) for n in range(3)]
                bernstein = [a, a+b/2, a+b+cc]
                for pos, beta in enumerate(bernstein):
                    assert 10000*beta >= lowers[k][side][pos]
        g = S.simplify(gg.subs(z, q))
        a, b, cc = p[i], p[(i+1) % 3], p[(i-1) % 3]
        p = p.copy()
        p[(i+1) % 3] = (a+b)*q-a
        p[(i-1) % 3] = (a+cc)/q-a
        assert all(v > 0 for v in p)
        margins.append(list(p))
    print(json.dumps({
        'python': platform.python_version(), 'sympy': S.__version__,
        'word': '012012', 'factors': [str(q) for q in qvals],
        'raw_initial_state': ['1', '1', str(t0)],
        'exact_identities_checked': ['rank-five minor', 'endpoint null vector',
            'zero first variation', 'positive constrained second variation',
            'cost bound', 'all switching margins', 'all whole-arc sector bounds'],
        'constrained_Q_lower_bound': '1/200',
        'scope': 'Same-word local minimum obstruction; L1 remains open.',
        'raw_switching_margins': [[str(v) for v in row] for row in margins],
    }, indent=2))


if __name__ == '__main__':
    main()
