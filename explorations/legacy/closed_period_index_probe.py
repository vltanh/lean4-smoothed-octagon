#!/usr/bin/env python3
"""Deterministic full-period first/second variation diagnostic, NOT a proof.

Run: python explorations/closed_period_index_probe.py
Requires Python >=3.11, NumPy >=1.24 and structural_case_probe.py.
Test only the octagon and two other known standard regular closed
families; method validation, not word-length enumeration.
No random seed, nonlinear optimization, Lean, Lake, typecheck, or CI.
Cost is physical C/sqrt(12); Hessian includes endpoint curvature.
"""
import math
import sys
import numpy as np
from structural_case_probe import trajectory,derivative,R

RINV=np.linalg.inv(R)


def full_map(v,word):
    p0,p1=v[:2]
    p2=(4-p0*p1)/(p0+p1)
    F,p,J,m=trajectory(word,v[2:],(p0,p1,p2))
    U=F@RINV
    return np.r_[[U[0,0]-1,U[0,1],U[1,0],
                   p[0]-p2,p[1]-p0],J]


def closed_hessian(word,vals,h=1.e-4):
    jac=derivative(lambda v: full_map(v,word),vals)
    DE,grad=jac[:5],jac[5]
    mu,*_=np.linalg.lstsq(DE.T,grad,rcond=None)
    stationarity=np.linalg.norm(DE.T@mu-grad)
    def dLag(v):
        j=derivative(lambda u: full_map(u,word),v)
        return j[5]-mu@j[:5]
    H=np.empty((len(vals),len(vals)))
    for i in range(len(vals)):
        dv=np.zeros(len(vals));dv[i]=h
        H[:,i]=(dLag(vals+dv)-dLag(vals-dv))/(2*h)
    H=(H+H.T)/2
    _,s,Vh=np.linalg.svd(DE,full_matrices=True)
    basis=Vh[5:].T
    eig=np.linalg.eigvalsh(basis.T@H@basis)
    return s,stationarity,eig


def main():
    print(f"Python {sys.version.split()[0]}, NumPy {np.__version__}; "
          "first derivatives complex-step, Hessian central diff 1e-4")
    for k in (1,2,3):
        N=3*k+1
        q=2*math.cos(math.pi*k/N)
        a=math.sqrt(4*q/(4-q))
        b=a*(2/q-1)
        v=np.r_[a,b,np.log([q]*N)]
        word=tuple(i%3 for i in range(N))
        result=full_map(v,word)
        singular,resid,eig=closed_hessian(word,v)
        print(f"N={N:2d}, cost={result[-1]*math.sqrt(12):.9f}, "
              f"closure_max={np.max(abs(result[:5])):.3g}, "
              f"minSV={singular[-1]:.6g}, stationarity={resid:.3g}, "
              f"negative_index={sum(eig < -1e-5)}, "
              f"eigenvalues={np.round(eig,7).tolist()}")
    print("All are known standard forward family inputs; "
          "no asymmetric or mixed class has been excluded.")


if __name__=="__main__":
    main()
