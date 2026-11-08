"""Replay a fixed exact central-face integer certificate.

Python 3.12 / SymPy 1.14.  No optimization, floating arithmetic, interval
mesh, Lean, Lake, typecheck or CI. The CSV file is a static displayed
coefficient table, not a generated assertion of positivity.

Scope: the central convex-chord face for either diagonal sign, under
the strengthened genuine two-secant order. The truncated face is separate.
"""
from pathlib import Path
import csv
import sympy as s
from sympy.polys.rings import ring
from sympy.polys.domains import ZZ

HERE=Path(__file__).resolve().parent
checks=0
def identity(expr):
    global checks
    assert s.factor(expr)==0
    checks+=1

t=s.symbols('t',positive=True)
V=(131*t**4+229*t**3+163*t**2+47*t+6)/(6*(t+1)*(3*t+1)**3)
z=(t-1)/(t+1)
a=z/(2+z)
identity(V-(s.Rational(5,4)+z/4-(1+z)*(2*a+s.Rational(2,3)*a**3)/(2*z)))
zz=s.symbols('z',positive=True)
TT=2*(1+zz)/(1-zz)
mm=2*(1+zz)+s.Rational(2,3)*zz*(1+zz)**2
identity(TT-mm-s.Rational(2,3)*zz*(1+zz)*(2+zz**2)/(1-zz))
identity(2/(1-zz**2)-s.diff(2*zz+s.Rational(2,3)*zz**3,zz)-2*zz**4/(1-zz**2))

pp,qq,dd,aa,ee,uu,vv,qq0=s.symbols('P Q D A E u v q',positive=True)
hh=pp+2*qq;cc=5*pp**2+8*pp*qq+12*qq**2
ww=(qq0**2*vv+dd**2*uu-dd*qq0*ee)/pp**2
el=(2*dd*uu-qq0*ee)/pp
tt=pp/qq;tb=qq/aa**2;zt=(pp-2*qq)/(pp+2*qq)
mt=2*(1+zt)+s.Rational(2,3)*zt*(1+zt)**2
rat=mt*(ww-s.Rational(3,4))+(uu-1)*tb+1+1/tb-1/(tt*tb)-el-2*zt-s.Rational(2,3)*zt**3
cleared=(qq*cc*(4*(qq0**2*vv+dd**2*uu-dd*qq0*ee)-3*pp**2)
         +3*pp*hh**3*(uu-1)*qq**2/aa**2+3*qq*pp*hh**3
         +3*aa**2*pp*hh**3-3*aa**2*qq*hh**3
         -3*qq*hh**3*(2*dd*uu-qq0*ee)
         -qq*pp*(6*(pp-2*qq)*hh**2+2*(pp-2*qq)**3))
identity(cleared-3*qq*pp*hh**3*rat)
xx,yy=s.symbols('x y',positive=True)
q0=(1+xx)*(1+yy)
eb=(uu-1)*(1+xx)+(vv-1)*(1+yy)+1+1/(1+xx)+1/(1+yy)-1/q0
identity(q0*eb-(q0*(uu-1)*(1+xx)+q0*(vv-1)*(1+yy)+q0+(1+xx)+(1+yy)-1))

# First form the polynomial before the order substitution.
R,h,j,k,l=ring('h,j,k,l',ZZ)
A=1+h;x=A+j;B=x+k;y=x+l
q=(1+x)*(1+y);P=q+A*A-1;Q=A*(A+B)
D=A*A+2*A*B+1+2*x-2*B*x
H=P+2*Q;C=5*P*P+8*P*Q+12*Q*Q
def numerator(u,v):
    qe=q*(u-1)*(1+x)+q*(v-1)*(1+y)+q+(1+x)+(1+y)-1
    wn=q*q*v+D*D*u-D*qe
    return (Q*C*(4*wn-3*P*P)
            +3*P*H**3*(u-1)*(A+B)**2+3*Q*P*H**3
            +3*A*A*P*H**3-3*A*A*Q*H**3
            -3*Q*H**3*(2*D*u-qe)
            -Q*P*(6*(P-2*Q)*H**2+2*(P-2*Q)**3))
n0=numerator(0,0);nu=numerator(1,0)-n0;nv=numerator(0,1)-n0
def vn(z):return 131*z**4+229*z**3+163*z**2+47*z+6
def vd(z):return 6*(z+1)*(3*z+1)**3
raw=-(nu*vn(x)*vd(y)+nv*vn(y)*vd(x)+n0*vd(x)*vd(y))
assert max(e[2]for e in raw)==5
checks+=1


# Strengthened order: beta-x=7*h*x*z/[(7+2*x)(1+z)].
S,h,j,z,l=ring('h,j,z,l',ZZ)
parts=[S.zero for _ in range(6)]
for (a,b,c,d),value in raw.items():parts[c][(a,b,0,d)]=value
x=1+h+j
B=(7+2*x)*(1+z);kn=7*h*x*z
poly=S.zero
for i,part in enumerate(parts):poly+=part*kn**i*B**(5-i)
G=B*(j*(j+2)+(h+j+2)*l-2*h*(h+1))-2*(h+1)*kn
remainder=S.zero;rows=0
with (HERE/'mixed_global_short_bridge_central_face_positive.csv').open()as f:
    for row in csv.DictReader(f):
        ex=tuple(int(row[k])for k in ['h','j','z','ell'])
        value=int(row['coefficient'])
        assert min(ex)>=0 and value>0 and ex not in remainder
        remainder[ex]=value;rows+=1
assert rows==13348
checks+=1
assert poly==j*j*z**3*(1625975783424+1310584209408*z)*G+remainder
checks+=1
assert remainder[(0,3,0,0)]==29720334827520
assert remainder[(0,3,5,0)]==6129819058176
checks+=1
assert sum(int(v)<0 for v in poly.values())==3
checks+=1
print(f'{checks} exact identities/table checks passed; 13348 positive coefficients, two explicit G multipliers, either D sign.')
