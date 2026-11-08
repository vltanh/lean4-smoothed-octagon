"""Numerical probe (discovery only): the largest value of each face test on its face domain."""
from model import *
import numpy as np
fs={'c2':central_two(x,al,be),'cT':central_T(x,al,be),'c8':central_8(x,al,be),
    'oT':outer(x,al,be,'T'),'o8':outer(x,al,be,'8'),'o2':outer(x,al,be,'2')}
for k,f in fs.items():
    f=lambdify((x,al,be),f,'numpy'); mx=-1e9; arg=None
    for X in np.linspace(2.4,9,81):
        A=np.linspace(1,(5*X+4)/12,81) if k[0]=='c' else np.linspace((22*X+20)/55,X,81)
        for a in A:
            hi=X+X*(7*X+1)*(a-1)/(4*X**2+11*X+1)
            B=np.linspace(X,hi,81) if hi>X else np.array([X])
            v=f(X,a,B); i=np.argmax(v)
            if v[i]>mx: mx=v[i]; arg=(X,a,B[i])
    print(k,mx,arg)
