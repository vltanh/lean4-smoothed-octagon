"""Factored (Horner-friendly) forms of the S4 surrogate numerators, as Lean strings, checked
against the expanded sympy forms of s4atomsN."""
import sympy as sp, re
from s4atomsN import NF, X, AL, A, Sg, S, U, D, Pn, nu, du, k, L0
P2 = "(2 : ℕ)"; P3 = "(3 : ℕ)"; P4 = "(4 : ℕ)"
W = f"X ^ {P2} * (X + 2) ^ {P2} * du"
Hn = "(2 * k * AL * A - Sg)"
common_tail = (f"96 * Sg ^ {P3} * A ^ {P2} * (nu - du) + 96 * du * Sg ^ {P3} * AL ^ {P2} - "
               f"96 * du * Sg ^ {P2} * AL ^ {P3} * A - 96 * Sg ^ {P2} * AL * A * (2 * D * nu - Pn) + "
               f"96 * du * AL * A * (L0 * Sg ^ {P3} + {Hn} * Sg ^ {P2} - {Hn} ^ {P2} * Sg / 2 + {Hn} ^ {P3} / 3)")
head = f"42 * Sg ^ {P3} * AL * A * (4 * nu * du * S ^ {P2} * U - Pn ^ {P2})"
cc = "(76818 / 625)"   # 672 * 1829/10000
STRUCT = {
 'Phi': (f"{head} - {W} * ({cc} * du * Sg ^ {P3} * AL * A + 192 * Sg * AL * A * (S ^ {P2} * U * du + D ^ {P2} * nu - D * Pn) - "
         f"48 * du * Sg ^ {P3} * AL * A + {common_tail})"),
 'Psi': (f"{head} - {W} * ({cc} * du * Sg ^ {P3} * AL * A + 96 * Sg ^ {P2} * (S ^ {P2} * U * du + D ^ {P2} * nu - D * Pn) - "
         f"72 * du * Sg ^ {P4} + 96 * du * Sg ^ {P3} * AL * A + {common_tail})"),
}
def to_sympy(s):
    t = re.sub(r"\^ \((\d+) : ℕ\)", r"** \1", s)
    return sp.sympify(t, locals=dict(X=X, AL=AL, A=A, Sg=Sg, S=S, U=U, D=D, Pn=Pn, nu=nu, du=du, k=k, L0=L0))
if __name__ == "__main__":
    for w in ('Phi', 'Psi'):
        N, M = NF(w)
        print(w, sp.expand(to_sympy(STRUCT[w]) - N) == 0)
