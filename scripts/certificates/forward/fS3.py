import pickle, sympy as sp
from bern import *
a,t=sp.symbols('a t')
res=pickle.load(open('S_E34.pkl','rb'))
R,cI,cc,Bn,Bd=res['E4']
f=sp.lambdify((a,t),Bn/Bd)
pos=[]
for i in range(71):
    for j in range(101):
        av=i/70/7; tv=j/100/4
        v=f(av,tv)
        tm=(1-av*av)/(4+av*av)
        if v>0: pos.append((av,tv,tv-tm))
print(len(pos))
print(min(p[2] for p in pos) if pos else None)
print(pos[:5])
# check on the domain t<=tmax only
mx=-1e9
for i in range(141):
    av=i/140/7; tm=(1-av*av)/(4+av*av)
    for j in range(201):
        tv=tm*j/200
        mx=max(mx,f(av,tv+1e-12))
print('max on domain',mx)
