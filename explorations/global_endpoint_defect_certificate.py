"""Exact symbolic identities for the conjugator-free polar endpoint defect.

Run: python explorations/global_endpoint_defect_certificate.py
Uses SymPy only. No trajectory samples, optimization, Lean, or CI.
The geometric angle branch and complete-period inequalities remain hand proof.
"""
import sympy as sp

J = sp.Matrix([[0, -1], [1, 0]])
a,b,c,d,e,f,g,h = sp.symbols("a b c d e f g h", real=True)
P = sp.Matrix([[a,b],[c,d]])
Q = sp.Matrix([[e,f],[g,h]])
re = (a+d)*(e+h)+(c-b)*(g-f)
im = (a+d)*(g-f)-(c-b)*(e+h)
assert sp.expand(re-sp.trace(P.T*Q)-sp.trace(P.adjugate()*Q)) == 0
assert sp.expand(im+sp.trace(P.T*J*Q)+sp.trace(P.adjugate()*J*Q)) == 0
print("PASS universal real and imaginary bilinear identities")

# Every SL(2) matrix with nonzero upper-left entry has this chart.
x,y,z,X,Y,Z,u,v,w,kappa = sp.symbols("x y z X Y Z u v w kappa", nonzero=True, real=True)
def sl(a,b,c):
    return sp.Matrix([[a,b],[c,(1+b*c)/a]])
H, Gs, Gt = sl(u,v,w), sl(x,y,z), sl(X,Y,Z)
Lam0 = -kappa*H*J*H.inv()
assert sp.simplify(H.inv().T*H.inv()-J*Lam0/kappa) == sp.zeros(2)
Ls = Gs.inv()*Lam0*Gs
M = Gs.inv()*Gt
P, Q = H.inv()*Gs, H.inv()*Gt
r = sp.trace(P.T*Q)+sp.trace(P.inv()*Q)
i = -sp.trace(P.T*J*Q)-sp.trace(P.inv()*J*Q)
assert sp.factor(r-sp.trace((sp.eye(2)+J*Ls/kappa)*M)) == 0
assert sp.factor(i-sp.trace((Ls/kappa-J)*M)) == 0
print("PASS conjugator elimination and both endpoint formulas")

# The symbolic chart is dense and all underlying determinant-one identities
# are polynomial after using adjugates; continuity supplies omitted charts.
assert sp.expand(sp.det(sp.Matrix([[a,b],[c,d]]))) == a*d-b*c
print("All five substantive exact identities passed; angle branch and scope require the hand proof.")
