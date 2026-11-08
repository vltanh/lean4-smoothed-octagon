from defs import *
c=mpf(1)/35;b=mpf(1)/64
def GB(U,S,T): K=1+U; return K**2/(16*U*U)*(4*(mpf(3)/4+c-b)*(mpf(3)/4+b)-(e0(U)+(c-b)*S+b*T)**2)
def GA(U,S): K=1+U; return K**2/(16*U*U)*(4*(mpf(3)/4+c)*(mpf(3)/4)-(e0(U)+c*S)**2)
import mpmath
wA=1e9;wB=1e9;argA=None;argB=None
N=4000
for i in range(N+1):
    U=mpf(11)/5+(mpf(3)-mpf(11)/5)*i/N
    sig=2+5*(U-1)/3  # max S+T
    T=min(mpf(7)/3,sig-2); S=min(sig-T,T)
    vB=GB(U,S,T)-mpf(23)/125
    smax=min(mpf(7)/3,sig/2)
    vA=GA(U,smax)-mpf(23)/125
    if vB<wB: wB=vB;argB=U
    if vA<wA: wA=vA;argA=U
print('A',wA,argA,'B',wB,argB)
