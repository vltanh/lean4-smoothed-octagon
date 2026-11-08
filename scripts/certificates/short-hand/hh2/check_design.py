"""Numerical margins of the three S2 face signs (sampling; orientation only, not a proof premise).

Prints, on random samples of each domain, the maximum of the exact face value over the duration
(`max_τ G_τ`) and of the bounds certified in Lean (outer: `max(H₀, H₁)` with the log majorant;
central: `G₂ + ℓᵢ(A)` for the five chords).
"""
import numpy as np

LBAR = -296 / 1029

def logb(y):
    t = 4 * y / 3 - 1
    return LBAR + t - t**2 / 2 + t**3 / 3

def uC(x, b):
    S = 1 + x
    return 0.75 + (680 * (x - 1)**3 + 3 * S**2 * (b - x)) / (9600 * S**2 * (b - 1))

def us(x, b):
    S = 1 + x
    return 0.75 + (17 * (x - 1)**3 / (240 * S**2) + (b - x) / 1200) / (b - 1)

def uv(x):
    return 0.75 + 2 * (x - 1)**2 / ((1 + x) * (35 * x + 13))

def face(x, a, b, u, q):
    """w_*, E_{L,*}-based constant c and k = q/r_A at scale q (central q = q_c, outer q = 1/7)."""
    S = 1 + x
    D = a * a + 2 * a * b + 1 + 2 * x - 2 * b * x
    e, n, d = 1 - 1 / a**2, S / a**2, D / a**2
    E0 = S * (u - 1) + 1 / S
    A1 = 2 * e + n + d * E0
    A2 = e * e + e * n + n * n + d * d * u + d * e * E0 - d * (2 * S - 1) / a**2
    A3 = 2 * d * u + e * E0 - (2 * S - 1) / a**2
    w = 1 - q * A1 + q * q * A2
    EL = -E0 + q * A3
    rA = a / (a + b)
    c = (u - 1) / rA + rA + 1 - q - EL
    return w, c, q / rA

def G(tau, w, c, k, log=np.log):
    return (w - 1) * tau + 1 / tau + c + log(tau * k) + (2 - 7 * tau * k / 4) * (w - 0.75)

def gmax(w, c, k):
    best = G(2.0, w, c, k)
    for s in np.linspace(0, 1, 401)[1:]:
        tau = 2 + s * (1 / k - 2)
        best = np.maximum(best, G(tau, w, c, k))
    return best

def strip(x, a, rng, n):
    lo = x + 8 * x * (a - 1) / (9 * x + 8)
    hi = x + x * (7 * x + 1) * (a - 1) / (4 * x * x + 11 * x + 1)
    return lo + (hi - lo) * rng.uniform(0, 1, n)

def main(N=400000, seed=1):
    rng = np.random.default_rng(seed)
    x = rng.uniform(13 / 6, 12 / 5, N)
    # central
    am = np.sqrt(x * (x + 2) / 6)
    a = 1 + (am - 1) * rng.uniform(0, 1, N)
    b = strip(x, a, rng, N)
    q = a * a / (x * (x + 2) + a * a)
    w, c, k = face(x, a, b, uC(x, b), q)
    G2 = G(2.0, w, c, k, logb)
    A = (1 - 7 * k / 4) * (w - 0.75)
    lines = [(0, 0), (0, 97 / 500), (-347 / 312500, 1179 / 2500),
             (9 / 196 + 1 / 50000 - 1.2197 * 9 / 196, 1.2197), (-9 / 392 + 1 / 50000, 1.5)]
    print('central: max_tau G =', gmax(w, c, k).max())
    for i, (al, be) in enumerate(lines):
        print(f'  line {i}: max G2 + l(A) =', (G2 + al + be * A).max())
    # outer
    for name in ['small', 'large']:
        if name == 'small':
            a = am + (1.5 - am) * rng.uniform(0, 1, N)
        else:
            a = 1.5 + (x - 1.5) * rng.uniform(0, 1, N)
        b = strip(x, a, rng, N)
        u = us(x, b) if name == 'small' else uv(x)
        w, c, k = face(x, a, b, u, 1 / 7)
        H0 = G(2.0, w, c, k, logb)
        H1 = H0 + (1 / k - 2) * (1 - 7 * k / 4) * (w - 0.75)
        print(f'{name}: max_tau G =', gmax(w, c, k).max(), ' max H0 =', H0.max(), ' max H1 =', H1.max())

if __name__ == '__main__':
    main()
