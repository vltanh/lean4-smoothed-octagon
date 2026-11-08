import sympy as sp
a,t,H = sp.symbols('a t H', real=True)
LI,Lc,Lh = sp.symbols('LI Lc Lh')
zz=(1+a)/(1-a); S=2/(1-a); I=1+t; Z=S**2/I; UU=sp.simplify(Z-zz**2); K=1+UU; c=1-a*I
h=1+H
def f(r, lr): return (r-1/r)/2 - lr
# log(S/2) symbol l1 and log(4/K) symbol l2 with 2 l1 + l2 = LI - Lc
l1=sp.Symbol('l1')
l2=LI-Lc-2*l1
Phi=2*f(S/2,l1)+f(4/K,l2)
d=3-UU;x=zz-1
P=d*d*(x*x+4*x+2)+8*d*x*zz+2*x*x*(8+4*x-x*x)
r=(d*x*(d+2*x)+H*P)/(8*S*Z)+H*H*zz*(d+4*x+x*x)/(2*h*Z)+K*(1+S*H)/Z*Phi-zz*f(h,Lh)
n=S**2*(UU-zz)*H/Z
q=S**2/K
m=K**2/(S*Z)*(q-1+H*(q*S-1))
def L(zv,hv,lhv): return (zv-1)*((zv-1)+2*zv*(hv-1))/(4*(1+zv)**2)+zv*hv/(1+zv)*(f(hv,lhv)/(hv-1))
LvI=L(zz,I,LI)
ES = r - n/35 - (m-n)*LvI
ES=sp.expand(sp.together(ES))
num,den=sp.fraction(sp.together(ES))
num=sp.expand(num)
pn=sp.Poly(num, LI,Lc,Lh,l1)
print('den',sp.factor(den))
for mon,cf in pn.terms():
    print(mon, sp.factor(cf))
