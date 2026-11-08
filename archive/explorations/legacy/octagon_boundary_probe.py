#!/usr/bin/env python3
"""Finite octagon-to-reverse-eight insertion test (NOT a proof).

Run: python explorations/octagon_boundary_probe.py
Requires NumPy >=1.24, SciPy >=1.10 and structural_case_probe.py.
The inserted factors exp(epsilon) have positive log epsilon. Correct
the other five old state/factor parameters to preserve both exact
closed-period endpoints. Uses a local implicit-function branch only.
No random search, Lean, Lake, typechecking, or CI.
"""
import math
import sys
import numpy as np
from scipy.optimize import root
from structural_case_probe import trajectory, derivative, R

WORD=(0,2,1,0,2,1,0,2)
INSERTED=[3,5,7,9]
CORRECTED=[0,1,2,4,6]
RINV=np.linalg.inv(R)


def evaluate(v):
    p0,p1=v[:2]
    p2=(4-p0*p1)/(p0+p1)
    F,pend,J,m=trajectory(WORD,v[2:],(p0,p1,p2))
    U=F@RINV
    residual=np.array([U[0,0]-1,U[0,1],U[1,0],
                       pend[0]-p2,pend[1]-p0])
    return np.r_[residual,J]


def main():
    print(f"Python {sys.version.split()[0]}, NumPy {np.__version__}; "
          "all results floating point")
    q=math.sqrt(2)
    a=math.sqrt(4*q/(4-q))
    b=a*(2/q-1)
    base=np.array([a,b,math.log(q),0.,math.log(q),0.,
                   math.log(q),0.,math.log(q),0.])
    out=evaluate(base)
    jac=derivative(evaluate,base)
    print(f"octagon cost={out[-1]*math.sqrt(12):.12f}, "
          f"closure_max={max(abs(out[:5])):.3g}")
    for j in INSERTED:
        corrected=-np.linalg.solve(jac[:5,CORRECTED],jac[:5,j])
        dcost=(jac[5,j]+jac[5,CORRECTED]@corrected)*math.sqrt(12)
        print(f"insert position {j-2}: compensated dC/dlogq={dcost:.12f}")
    for eps in (.001,.005,.015,.04):
        template=base.copy(); template[INSERTED]=eps
        def put(z):
            r=template.copy();r[CORRECTED]=z
            return r
        def fun(z):
            return evaluate(put(z))[:5]
        def jacfun(z):
            return derivative(evaluate,put(z))[:5,CORRECTED]
        sol=root(fun,base[CORRECTED],jac=jacfun,tol=1e-11)
        v=put(sol.x)
        p2=(4-v[0]*v[1])/(v[0]+v[1])
        _,_,J,m=trajectory(WORD,v[2:],(v[0],v[1],p2))
        print(f"epsilon={eps:.3f}: root_success={sol.success}, "
              f"endpoint_max={max(abs(evaluate(v)[:5])):.3g}, "
              f"C-Aoct={(J-out[-1])*math.sqrt(12):.12f}, "
              f"min_margin={m.min():.8f}, min_old_log={min(v[[2,4,6,8]]):.8f}")
    print("Root convergence/positive margins at these four points are "
          "not a uniform cost comparison or a rigorous interval certificate.")


if __name__=="__main__":
    main()
