# transport-form face functions (sympy), both faces
import sympy as sp
x,al,be,u=sp.symbols('x al be u',positive=True)
S=1+x; X=S**2-1
D=al**2+2*al*be+1+2*x-2*be*x
B=al+be
rA=al/B
c=sp.Rational(7,96); g=sp.Rational(9193,50000)
def ellz(z): return 2*z+sp.Rational(2,3)*z**3
def ell(y): return ellz((y-1)/(y+1))
def face(f):
    if f=='c':
        K=X+al**2; rho=1/S**2; q=al**2/K
    else:
        K=6*al**2+1; rho=1/K; q=sp.Rational(1,7)
    lam=1/(1+rho*(al**2-1)); d=lam*rho*D
    t0=rho*S; v=1-t0+t0**2
    Es=S*(u-1)+1/S+rho*(2*S-1)
    w=lam**2*v+d**2*u-d*lam*Es
    EL=2*d*u-lam*Es
    Gam=(4*u*v-Es**2)/(16*(1-rho)**2)
    T=rA/q
    R2=2*w-sp.Rational(1,2)+(u-1)/rA+rA-q-EL+ell(2/T)
    F0=Gam-c*R2-g
    F1=F0-c*(T-2)*(w-sp.Rational(3,4))
    return dict(K=K,rho=rho,q=q,lam=lam,d=d,v=v,Es=Es,w=w,EL=EL,Gam=Gam,T=T,R2=R2,F0=F0,F1=F1)
Ul=sp.Rational(3,4)+(x-1)**2*(be+15*x-16)/(8*S*(35*x+13)*(be-1))
Uf=sp.Rational(3,4)+(x-1)**2/(28*S**2)
Vb=sp.Rational(3,4)+2*(x-1)**2/(S*(35*x+13))
bm=x+8*x*(al-1)/(9*x+8)
bp=x+x*(7*x+1)*(al-1)/(4*x**2+11*x+1)
aU=(1013*x+676)/sp.Integer(2340)
aL=(4375*x+2797)/sp.Integer(10000)
