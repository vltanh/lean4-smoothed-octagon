"""Exact Bernstein tools (Fractions). Polynomials: dict {exponent tuple: Fraction}."""
from fractions import Fraction as Fr
from math import comb
import sympy as sp

def from_sympy(expr, vars_):
    P=sp.Poly(sp.expand(expr), *vars_)
    return {m: Fr(int(sp.Rational(c).p), int(sp.Rational(c).q)) for m,c in P.terms()}

def uni_coeffs(d, var_index, nvars):
    """Split poly dict into list of coefficient dicts (in the other vars) by power of var."""
    out={}
    for m,c in d.items():
        e=m[var_index]
        mm=m[:var_index]+m[var_index+1:]
        out.setdefault(e,{})
        out[e][mm]=out[e].get(mm,Fr(0))+c
    n=max(out) if out else 0
    return [out.get(i,{}) for i in range(n+1)]

def taylor_shift_scale(cs, lo, hi):
    """cs: list of numbers (coeffs of p(y)=sum cs[i] y^i). Return coeffs of q(t)=p(lo+(hi-lo)t)."""
    n=len(cs)-1; d=hi-lo
    out=[Fr(0)]*(n+1)
    for i,ci in enumerate(cs):
        if ci==0: continue
        # (lo + d t)^i = sum_j C(i,j) lo^(i-j) d^j t^j
        for j in range(i+1):
            out[j]+=ci*comb(i,j)*lo**(i-j)*d**j
    return out

def bern_from_power01(ds):
    """power coeffs on [0,1] -> Bernstein coeffs (degree n=len-1)."""
    n=len(ds)-1
    return [sum(Fr(comb(k,j),comb(n,j))*ds[j] for j in range(k+1)) for k in range(n+1)]

def elevate(bs, r):
    n=len(bs)-1; m=n+r
    return [sum(Fr(comb(n,j)*comb(r,k-j),comb(m,k))*bs[j] for j in range(max(0,k-r),min(n,k)+1)) for k in range(m+1)]

def uni_bern(cs, lo, hi):
    return bern_from_power01(taylor_shift_scale(cs, lo, hi))

def uni_min_bern(cs, lo, hi):
    return min(uni_bern(cs,lo,hi))

# linear combination of polys (dicts) with weights
def lincomb(polys, ws):
    out={}
    for p,w in zip(polys,ws):
        if w==0: continue
        for m,c in p.items():
            out[m]=out.get(m,Fr(0))+w*c
    return {m:c for m,c in out.items() if c!=0}

def bern_weights(n, lo, hi):
    """W[k][i]: Bernstein coeff k of y^i on [lo,hi] (so that b_k = sum_i W[k][i] c_i)."""
    W=[]
    for i in range(n+1):
        cs=[Fr(0)]*(n+1); cs[i]=Fr(1)
        W.append(uni_bern(cs,lo,hi))
    return [[W[i][k] for i in range(n+1)] for k in range(n+1)]
