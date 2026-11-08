"""Nested Bernstein planner: P dict over vars (v0,v1,v2); order = (lvl1, lvl2, leaf) indices.
Level 1 and 2 can subdivide their intervals; leaf univariate splits/elevation counted."""
from fractions import Fraction as Fr
from bern import *

def uni_split(cs, lo, hi, maxdepth=8, maxelev=6):
    """Return list of (lo,hi,elev) pieces where Bernstein coeffs positive, or None."""
    n=len(cs)-1
    for r in range(maxelev+1):
        bs=uni_bern(cs,lo,hi)
        if r: bs=elevate(bs,r)
        if min(bs)>0: return [(lo,hi,r)]
    if maxdepth==0: return None
    mid=(lo+hi)/2
    L=uni_split(cs,lo,mid,maxdepth-1,maxelev); 
    if L is None: return None
    R=uni_split(cs,mid,hi,maxdepth-1,maxelev)
    if R is None: return None
    return L+R

def sub_poly(P, i):
    return uni_coeffs(P,i,None)

def level(P, var, lo, hi):
    """Bernstein coefficient polys (dicts in the remaining vars) of P in variable index var on [lo,hi]."""
    cs=uni_coeffs(P,var,None)
    n=len(cs)-1
    W=bern_weights(n,lo,hi)
    return [lincomb(cs,W[k]) for k in range(n+1)]

def plan(P, order, box, split1=None, split2=None, verbose=False):
    """order: (i1,i2,i3) variable indices; box: list of (lo,hi) per var index.
    split1: list of breakpoints for lvl1 var; split2 similarly (uniform for all)."""
    i1,i2,i3=order
    pts1=split1 or [box[i1][0],box[i1][1]]
    pts2=split2 or [box[i2][0],box[i2][1]]
    nleaf=0; fails=[]
    for p in range(len(pts1)-1):
        B1=level(P,i1,pts1[p],pts1[p+1])
        rem=[v for v in range(3) if v!=i1]
        j2=rem.index(i2); j3=rem.index(i3)
        for k,bk in enumerate(B1):
            for q in range(len(pts2)-1):
                B2=level(bk,j2,pts2[q],pts2[q+1])
                for l,bl in enumerate(B2):
                    deg=max([m[0] for m in bl] or [0])
                    cs=[bl.get((e,),Fr(0)) for e in range(deg+1)]
                    sp_=uni_split(cs,*box[i3])
                    if sp_ is None:
                        fails.append((p,k,q,l)); 
                    else: nleaf+=len(sp_)
    return nleaf, fails
