#!/usr/bin/env python3
"""Incomplete floating-point local endpoint-fiber diagnostic; NOT a proof.

Run: OPENBLAS_NUM_THREADS=1 python3 explorations/local_six_fiber_probe.py
Tested: Python 3.13.5, NumPy 2.3.5, SciPy 1.17.0; seed 761106.
Finite input: five fixed words, three seeded tuples per word. Initial p0,p1
are in [0.7,1.4], p2=(4-p0*p1)/(p0+p1); six log factors in [0.025,0.12].
All generated inputs and output residuals are printed. No theorem uses them.

SLSQP: 150 iterations, ftol=1e-11, log factors in [1e-7,2], endpoint state
margins >=1e-7. These are arbitrary numerical bounds, not exhaustive ones.
Three tangent entries determine F only on the chart F00!=0; the two terminal
state margins use the positive determinant-one chart. Complex-step Jacobians
still use floating point, not certified arithmetic.

Limitations: no sector test, no full-domain cover, no singular-rank proof,
no exact zero-duration endpoint, no Lean/Lake/CI execution. Original run:
6/15 reported convergence at a numerical factor bound; 9/15 did not converge
and have nonzero endpoint residuals. Failed runs are not feasible competitors.
"""
import json
import platform

import numpy as np
import scipy
from scipy.optimize import minimize


def eval_window(p0, word, s):
    p = np.array(p0, dtype=np.result_type(s, float))
    F = np.eye(2, dtype=p.dtype)
    J = 0.0
    states = [p.copy()]
    for i, logq in zip(word, s):
        q = np.exp(logq)
        a, b, c = p[i], p[(i + 1) % 3], p[(i - 1) % 3]
        J += a / 8 * ((a + b) * (q - 1) + (a + c) * (1 - 1 / q) - a * logq)
        if i == 0:
            T = np.array([[q, 0], [0, 1 / q]])
        elif i == 1:
            T = np.array([[1 / q, q - 1 / q], [0, q]])
        else:
            T = np.array([[1 / q, 0], [1 / q - q, q]])
        F = F @ T
        p = p.copy()
        p[(i + 1) % 3] = (a + b) * q - a
        p[(i - 1) % 3] = (a + c) / q - a
        states.append(p.copy())
    endpoint = np.array([F[0, 0], F[0, 1], F[1, 0], p[0], p[1]])
    return J, endpoint, np.array(states)


def jac(function, x):
    x = np.asarray(x, dtype=float)
    directions = np.eye(len(x))
    return np.stack([
        np.imag(function(x.astype(complex) + 1e-20j * direction)) / 1e-20
        for direction in directions
    ], axis=-1)


def main():
    words = ['012012', '021021', '021210', '010201', '021012']
    rng = np.random.default_rng(761106)
    records = []
    for word_string in words:
        word = list(map(int, word_string))
        for trial in range(3):
            a, b = rng.uniform(0.7, 1.4, 2)
            p0 = [a, b, (4 - a * b) / (a + b)]
            s0 = rng.uniform(0.025, 0.12, 6)
            start_cost, target, states = eval_window(p0, word, s0)
            if np.min(states) <= 0 or abs(target[0]) < 1e-6:
                records.append({'word': word_string, 'trial': trial,
                                'p0': p0, 'log_factors0': s0.tolist(),
                                'skipped': 'outside positive chart'})
                continue
            objective = lambda s: eval_window(p0, word, s)[0]
            endpoint = lambda s: eval_window(p0, word, s)[1] - target
            margins = lambda s: eval_window(p0, word, s)[2].flatten() - 1e-7
            result = minimize(
                objective, s0, jac=lambda x: jac(objective, x), method='SLSQP',
                bounds=[(1e-7, 2.0)] * 6,
                constraints=[
                    {'type': 'eq', 'fun': endpoint, 'jac': lambda x: jac(endpoint, x)},
                    {'type': 'ineq', 'fun': margins, 'jac': lambda x: jac(margins, x)},
                ], options={'maxiter': 150, 'ftol': 1e-11},
            )
            solution = result.x
            matrix = jac(lambda s: eval_window(p0, word, s)[1], solution)
            records.append({
                'word': word_string, 'trial': trial,
                'p0': p0, 'log_factors0': s0.tolist(),
                'log_factors_end': solution.tolist(),
                'start_cost': float(start_cost),
                'end_cost': float(objective(solution)),
                'min_log_factor': float(np.min(solution)),
                'min_state_margin': float(np.min(margins(solution) + 1e-7)),
                'endpoint_residual': float(np.max(np.abs(endpoint(solution)))),
                'rank_singular_values': np.linalg.svd(matrix, compute_uv=False).tolist(),
                'success': bool(result.success), 'message': str(result.message),
            })
    print(json.dumps({
        'python': platform.python_version(), 'numpy': np.__version__,
        'scipy': scipy.__version__, 'seed': 761106, 'records': records,
        'interpretation': 'Exploration only; no analytic exclusion proved.'
    }, indent=2))


if __name__ == '__main__':
    main()
