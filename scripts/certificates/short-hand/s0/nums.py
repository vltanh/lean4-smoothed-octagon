"""Cleared numerators of the six face tests (writes nums.pkl): F = n/d with d > 0 on the faces."""
from model import *
import pickle
res={}
for k,f in [('c2',central_two(x,al,be)),('cT',central_T(x,al,be)),('c8',central_8(x,al,be)),
            ('oT',outer(x,al,be,'T')),('o8',outer(x,al,be,'8')),('o2',outer(x,al,be,'2'))]:
    n,d=fraction(together(f))
    n=expand(n); d=factor(d)
    P=Poly(n,x,al,be)
    print(k,'den:',d,' terms',len(P.terms()),'deg',P.degree(x),P.degree(al),P.degree(be))
    res[k]=(n,d)
pickle.dump(res,open('nums.pkl','wb'))
