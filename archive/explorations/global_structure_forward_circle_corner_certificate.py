"""Exact rational interval check for the central circular corner.

This is a fixed five-variable domain, not a word-length enumeration.
Only rational interval arithmetic and elementary log bounds enter the
derivative estimate.  The symbolic identities use SymPy as a redundant
reconstruction check; the stated formulas are directly differentiable.
"""
from fractions import Fraction as F
from math import ceil


class I:
    __slots__ = ("lo", "hi")

    def __init__(self, lo, hi=None):
        if isinstance(lo, I):
            self.lo, self.hi = lo.lo, lo.hi
        else:
            self.lo, self.hi = F(lo), F(lo if hi is None else hi)
        assert self.lo <= self.hi

    def __add__(self, other):
        other = I(other)
        return I(self.lo + other.lo, self.hi + other.hi)

    __radd__ = __add__

    def __neg__(self):
        return I(-self.hi, -self.lo)

    def __sub__(self, other):
        return self + -I(other)

    def __rsub__(self, other):
        return I(other) + -self

    def __mul__(self, other):
        other = I(other)
        p = (self.lo * other.lo, self.lo * other.hi,
             self.hi * other.lo, self.hi * other.hi)
        return I(min(p), max(p))

    __rmul__ = __mul__

    def inv(self):
        assert self.lo > 0 or self.hi < 0
        return I(1 / self.hi, 1 / self.lo)

    def __truediv__(self, other):
        return self * I(other).inv()

    def __rtruediv__(self, other):
        return I(other) * self.inv()

    def __pow__(self, n):
        assert isinstance(n, int)
        if n < 0:
            return self.inv() ** -n
        if n == 0:
            return I(1)
        if n % 2 == 0:
            p = self ** (n // 2)
            if p.lo >= 0:
                return I(p.lo * p.lo, p.hi * p.hi)
            if p.hi <= 0:
                return I(p.hi * p.hi, p.lo * p.lo)
            return I(0, max(p.lo * p.lo, p.hi * p.hi))
        return self * (self ** (n - 1))

    def log(self):
        assert self.lo > 0
        # (x-1)/x <= log(x) <= x-1 for every x>0.
        return I((self.lo - 1) / self.lo, self.hi - 1)

    def abs_upper(self):
        return max(abs(self.lo), abs(self.hi))

    def __repr__(self):
        return f"[{self.lo}, {self.hi}]"


class Jet:
    N = 5

    def __init__(self, val, grad=None, hess=None):
        self.val = I(val)
        self.grad = grad if grad is not None else [I(0) for _ in range(self.N)]
        self.hess = hess if hess is not None else [
            [I(0) for _ in range(self.N)] for _ in range(self.N)]

    @classmethod
    def variable(cls, val, i):
        j = cls(val)
        j.grad[i] = I(1)
        return j

    @classmethod
    def lift(cls, x):
        return x if isinstance(x, cls) else cls(x)

    def __add__(self, other):
        other = self.lift(other)
        return Jet(self.val + other.val,
                   [a + b for a, b in zip(self.grad, other.grad)],
                   [[self.hess[i][j] + other.hess[i][j] for j in range(self.N)]
                    for i in range(self.N)])

    __radd__ = __add__

    def __neg__(self):
        return Jet(-self.val, [-g for g in self.grad],
                   [[-h for h in row] for row in self.hess])

    def __sub__(self, other):
        return self + -self.lift(other)

    def __rsub__(self, other):
        return self.lift(other) + -self

    def __mul__(self, other):
        other = self.lift(other)
        return Jet(self.val * other.val,
                   [self.grad[i] * other.val + self.val * other.grad[i]
                    for i in range(self.N)],
                   [[self.hess[i][j] * other.val
                     + self.grad[i] * other.grad[j]
                     + self.grad[j] * other.grad[i]
                     + self.val * other.hess[i][j]
                     for j in range(self.N)] for i in range(self.N)])

    __rmul__ = __mul__

    def unary(self, val, first, second):
        return Jet(val, [first * x for x in self.grad],
                   [[first * self.hess[i][j] + second * self.grad[i] * self.grad[j]
                     for j in range(self.N)] for i in range(self.N)])

    def inv(self):
        return self.unary(self.val.inv(), -(self.val ** -2), 2 * self.val ** -3)

    def __truediv__(self, other):
        return self * self.lift(other).inv()

    def __rtruediv__(self, other):
        return self.lift(other) * self.inv()

    def __pow__(self, n):
        assert isinstance(n, int)
        if n == 0:
            return Jet(1)
        return self.unary(self.val ** n, n * self.val ** (n-1),
                          n * (n-1) * self.val ** (n-2))

    def log(self):
        return self.unary(self.val.log(), self.val.inv(), -(self.val ** -2))


def system(U, z, w, h, k, log):
    S, T, K = 1 + z, 1 + w, 1 + U
    Wz, Ww = z*z + U, w*w + U
    q = S*T/K
    A = 1+z+w-1/S-1/T+1/K-log(q)
    B = Wz*h/S + 1 - z*z*S/(Wz*h) - z*z/S + z**3/Wz - z*log(h)
    C = Ww*k/T + 1 - w*w*T/(Ww*k) - w*w/T + w**3/Ww - w*log(k)
    alphaL = K*(h*S-z)/Wz
    alphaR = K*(k*T-w)/Ww
    nL = S*S*(U-z)*(h-1)/Wz
    nR = T*T*(U-w)*(k-1)/Ww
    mL = alphaL*T - K*K*h/(S*Wz)
    mR = alphaR*S - K*K*k/(T*Ww)
    RL, RR = alphaL*A-B, alphaR*A-C
    L1, L2 = nL+mR, mL+nR
    residual = RL+RR-F(3, 4)*(L1+L2)
    return residual, L1, L2, A


def main():
    import sympy as s
    U, z, w, h, k = s.symbols("U z w h k", positive=True)
    residual, _, _, _ = system(U, z, w, h, k, s.log)
    base = s.factor(residual.subs({U: 3, z: 1, w: 1}))
    expected = -(h*h-1)/(2*h)+s.log(h)-(k*k-1)/(2*k)+s.log(k)
    assert s.simplify(base-expected) == 0
    for x in (U, z, w):
        assert s.simplify(s.diff(residual, x).subs({U: 3,z: 1,w: 1,h: 1,k: 1})) == 0
    print("circle residual identity and three vanishing central derivatives passed")

    variables = [Jet.variable(I(F(299,100), 3), 0),
                 Jet.variable(I(1, F(101,100)), 1),
                 Jet.variable(I(1, F(101,100)), 2),
                 Jet.variable(I(1, 2), 3), Jet.variable(I(1, 2), 4)]
    result, _, _, _ = system(*variables, log=lambda x: x.log())
    bounds = [[ceil(result.hess[i][j].abs_upper()) for j in range(5)]
              for i in range(3)]
    print("ceilings of all 3-by-5 mixed Hessian absolute interval bounds:")
    for row in bounds:
        print(row)
    B = max(max(row) for row in bounds)
    assert B <= 10
    print("uniform Hessian bound B <=", B)

    # Independent lower bounds for the positive row coefficients.
    assert F(4)*F(198,100)/F(40301,10000) > 1
    assert F(399,100)**2/(F(201,100)*F(40301,10000)) > 1
    eta = F(1, 12500)
    Ebound = F(3,4)+(24*10+F(7,2))*eta+12*10*eta*eta
    assert Ebound < F(77,100)
    casimir_floor = F(4,3)*(F(9,4)-F(77,100)**2)
    assert casimir_floor > F(276,125)
    print("corner E upper:", Ebound)
    print("corner physical Casimir lower:", casimir_floor, ">", F(276,125))
    # The theorem explicitly excludes t=0; its algebraic fibre is nontrivial.
    base_residual, base_l1, base_l2, base_A = system(
        F(3), F(1), F(1), F(1), F(1), lambda x: F(0))
    assert (base_residual, base_l1, base_l2, base_A) == (0, 0, 0, F(9,4))
    assert F(4,3)*(4-F(7,4)**2) == F(5,4)
    print("degenerate t=0 fibre retained; positive-window theorem requires t>0")
    print("All exact corner checks passed.")


if __name__ == "__main__":
    main()
