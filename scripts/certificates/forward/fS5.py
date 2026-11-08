import pickle, sympy as sp
from bern import *
a,t=sp.symbols('a t')
res=pickle.load(open('S_E34.pkl','rb'))
R,cI,cc,Bn,Bd=res['E4']
f=sp.lambdify((a,t),Bn)
# for each t, smallest a where Bn>0
for tv in [0,0.01,0.02,0.04,0.06,0.08,0.1,0.12,0.14,0.2,0.25]:
    amin=None
    for i in range(1001):
        av=i/1000/7
        if f(av,tv)>0: amin=av;break
    print(tv,amin)
# try boxes
def tryb(a0,a1,t0,t1):
    C=bern2(Bn,a,t,((a0,a1),(t0,t1)))
    return float(max(max(r) for r in C))
print(tryb(0,Fr(1,7),Fr(1,10),Fr(1,4)))
print(tryb(0,Fr(1,10),Fr(0),Fr(1,10)))
print(tryb(0,Fr(1,14),Fr(0),Fr(1,10)))
print('A',tryb(0,Fr(1,7),Fr(39,400),Fr(1,4)))
print('B',tryb(0,Fr(1,10),Fr(0),Fr(1,4)))
