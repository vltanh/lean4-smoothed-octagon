"""Fixed exact certificate for the whole short-bridge upper endpoint.

Python 3.12 / SymPy 1.14. No optimization, floats, mesh, Lean/Lake or CI.
The separate CSV is the complete static positive-coefficient table.
"""
from pathlib import Path
import csv
import sympy as s
from sympy.polys.rings import ring
from sympy.polys.domains import ZZ
checks=0
def check(expr):
    global checks
    assert s.factor(expr)==0
    checks+=1

z=s.symbols('z',positive=True)
lower=z/(1+z)*(1+z/2-2*z*z/(12+5*z))
check(1/(1+z)-s.diff(lower,z)-z**3*(16-5*z)/(2*(1+z)**2*(12+5*z)**2))
x=s.symbols('x',positive=True)
rr=(x-1)/(x+1)
Vbar=(55*x*x+64*x+25)/(4*(x+1)*(17*x+7))
check(Vbar-s.Rational(3,4)-rr**2/(12+5*rr))

A,B,x,y,u,v,q,H=s.symbols('A B x y u v q H',positive=True)
sig=A*A-1;P=q+sig;Q=A*(A+B)
D=A*A+2*A*B+1+2*x-2*B*x;Z=D-Q
E=H-s.log(q)-1/q
w=(q*q*v+D*D*u-D*q*E)/P**2
EL=(2*D*u-q*E)/P;T=P/Q;TB=Q/A**2
RT=(w-1)*T+(u-1)*TB+1+1/T+1/TB-1/(T*TB)-EL
M=(u-1)*(A+B)**2+A*B+1
N=(v-1)*q*q+Z*q*s.log(q)+q*(M+1-Z*H)+Z+u*Z*Z-M
check(P*Q*RT-N)
check(s.diff(N,q,2)-2*(v-1)-Z/q)
q0=(1+x)*(1+y)
eb=(u-1)*(1+x)+(v-1)*(1+y)+1+1/(1+x)+1/(1+y)-1/q0
N0=v*q0*q0-Z*q0*eb+u*Z*Z+(q0-1)*(M-q0)
Np=2*(v-1)*q0+M+1+Z*(1-eb-1/q0)
check(N.subs({q:q0,H:eb+s.log(q0)+1/q0},simultaneous=True)-N0)
check(s.diff(N,q).subs({q:q0,H:eb+s.log(q0)+1/q0},simultaneous=True)-Np)
check(s.diff(N0,u)-((Z-(1+x))*(Z-(q0-1)*(1+x))+(q0-1)*((A+B)**2-(1+x)**2)))
check(s.diff(N0,v)-q0*(1+y)*(1+x-Z))

# The explicit six-block positive formula for the initial derivative.
h,j,k,l=s.symbols('h j k l',nonnegative=True)
S=h+j+2;xx=h+j+1
P1=h**3+6*h*h*j+7*h*h+9*h*j*j+22*h*j+10*h+4*j**3+15*j*j+16*j+4
P2=h**3+6*h*h*j+5*h*h+9*h*j*j+16*h*j+4*h+4*j**3+11*j*j+6*j
P3=h**3+6*h*h*j+5*h*h+9*h*j*j+16*h*j+4*h+4*j**3+12*j*j+8*j
P4=h**3+6*h*h*j+3*h*h+9*h*j*j+10*h*j+4*j**3+8*j*j
positive=k*k*xx*(l+S)+k*(l*P1+S*P2)+xx*(l*P3+S*P4)
UU=1-1/(1+x)+1/(1+x)**2;VV=1-1/(1+y)+1/(1+y)**2
expanded=(-((1+x)**2)*(1+y)*Np.subs({u:UU,v:VV})).subs({A:1+h,x:1+h+j,B:1+h+j+k,y:1+h+j+l},simultaneous=True)
check(expanded-positive)

# Generate the numerator independently of the coefficient table.
R,h,j,k,l=ring('h,j,k,l',ZZ)
A=1+h;x=A+j;B=x+k;y=x+l;q=(1+x)*(1+y)
Q=A*(A+B);D=A*A+2*A*B+1+2*x-2*B*x;Z=D-Q
def n0(uu,vv):
    qe=q*(uu-1)*(1+x)+q*(vv-1)*(1+y)+q+(1+x)+(1+y)-1
    MM=(uu-1)*(A+B)**2+A*B+1
    return vv*q*q-Z*qe+uu*Z*Z+(q-1)*(MM-q)
c=n0(0,0);cu=n0(1,0)-c;cv=n0(0,1)-c
def vn(t):return 55*t*t+64*t+25
def vd(t):return 4*(t+1)*(17*t+7)
raw=-(c*vd(x)*vd(y)+cu*vn(x)*vd(y)+cv*vn(y)*vd(x))
assert max(e[2]for e in raw)==2
checks+=1
S,h,j,z,l=ring('h,j,z,l',ZZ)
parts=[S.zero for _ in range(3)]
for (a,b,c,d),value in raw.items():parts[c][(a,b,0,d)]=value
xx=1+h+j
poly=S.zero
for i,part in enumerate(parts):poly+=part*(7*h*xx*z)**i*((7+2*xx)*(1+z))**(2-i)
remainder=S.zero;rows=0
with Path(__file__).with_name('mixed_global_short_bridge_upper_endpoint_positive.csv').open()as f:
    for row in csv.DictReader(f):
        ex=tuple(int(row[k])for k in ['h','j','z','ell']);value=int(row['coefficient'])
        assert min(ex)>=0 and value>0 and ex not in remainder
        remainder[ex]=value;rows+=1
assert rows==803
checks+=1
assert poly==73344*h*j*j*z*z*(h-1)**2+remainder
checks+=1
assert remainder[(0,3,0,0)]==1492992 and remainder[(0,3,2,0)]==1492992
checks+=1
print(f'{checks} exact identities/table checks passed; 803 positive coefficients and one explicit square.')
