"""Exact algebra for the truncated outer-root scale reduction.

The literal CSVs contain complete positive remainders and multipliers.
No numerical optimizer, sampled sign, Lean, Lake, typechecking, or CI.
"""
import csv
from pathlib import Path
import sympy as s
from sympy.polys.rings import ring
from sympy.polys.domains import ZZ

ROOT=Path(__file__).resolve().parent
A,B,X,Y,q,u,v=s.symbols('A B X Y q u v',positive=True)
sig=A*A-1;SS=1+X;TT=1+Y;q0=SS*TT;PP=q+sig;QQ=A*(A+B)
DD=(A+B)**2+SS*SS-(B+X)**2;TB=1+B/A
f=lambda zz:zz-1/zz-s.log(zz)
hh=lambda zz:s.log(zz)-1+1/zz
gg=lambda zz,n:n*zz-f(zz)
EE=gg(SS,u)+gg(TT,v)-hh(q)
ww=(q*q*v+DD*DD*u-DD*q*EE)/(PP*PP)
EL=(2*DD*u-q*EE)/PP
R2=2*ww-f(2)+gg(TB,u)-hh(PP/(A*A))-EL
H=gg(SS,u)+gg(TT,v)+1
C=gg(TB,u)-f(2)+1+2*s.log(A)
N=2*q*q*v+2*DD*DD*u-2*DD*u*PP+q*(PP-2*DD)*(H-s.log(q)-1/q)+PP*PP*(C-s.log(PP))-A*A*PP
checks=0
def check(name,left,right=0):
 global checks
 expr=(left-right).replace(lambda e:e.func==s.log,lambda e:s.log(s.factor(e.args[0])))
 if s.factor(s.expand_log(expr,force=True))!=0:raise AssertionError(name)
 checks+=1

check('exact root numerator',PP*PP*R2,N)
check('domain coefficient identity',2*QQ-DD-sig,2*X*(B-1))
check('third derivative',s.diff(N,q,3),-2/q-2/PP+(sig-2*DD)/q**2)
check('second derivative',s.diff(N,q,2),4*v+2*H+2*C-2*s.log(q)-2*s.log(PP)-6-(sig-2*DD)/q)
H0=(u-1)*SS+(v-1)*TT+1/SS+1/TT+1
C0=(u-1)*TB+1/TB-s.Rational(1,2)
Aq=2*q+sig-2*DD
W=Aq*H0+2*PP*C0+4*q*v-2*DD*u-2*PP+2*DD-1-A*A
check('exact derivative logarithmic decomposition',s.diff(N,q),W-Aq*s.log(q/q0)-2*PP*s.log(PP/(2*QQ)))
check('norm derivative u',s.diff(W,u),Aq*SS+2*PP*TB-2*DD)
check('norm derivative v',s.diff(W,v),Aq*TT+4*q)
vp=lambda zz:(131*zz**4+229*zz**3+163*zz**2+47*zz+6)/(6*(zz+1)*(3*zz+1)**3)
aa=(X-1)/(3*X+1)
check('rational norm upper identity',1+X/(2*(1+X))-X/(X-1)*(2*aa+s.Rational(2,3)*aa**3),vp(X))
Wu=W.subs({u:vp(X),v:vp(Y)})
Bc=(Wu-4*PP*(PP-2*QQ)/(PP+2*QQ)).subs(q,q0)
Bo=(Wu-2*Aq*(q-q0)/(q+q0)).subs(q,2*QQ-sig)
dc=6*A*(A+B)*SS*TT*(3*X+1)**3*(3*Y+1)**3*(q0+sig+2*QQ)
do=6*SS*TT*(3*X+1)**3*(3*Y+1)**3*(2*QQ-sig+q0)
pc=s.Poly(s.cancel(-dc*Bc),A,B,X,Y)
po=s.Poly(s.cancel(-do*Bo),A,B,X,Y)
assert pc.degree(B)==3 and po.degree(B)==3
checks+=1

ring4,h,j,z,l=ring('h,j,z,l',ZZ)
al=1+h;xx=1+h+j;yy=xx+l;bn=xx*(1+(1+h)*z);db=1+z
def normalize(poly):
 out=ring4.zero
 for (ea,eb,ex,ey),c in poly.terms():
  assert s.Rational(c).q==1
  out+=int(c)*al**ea*bn**eb*xx**ex*yy**ey*db**(3-eb)
 return out
pcn=normalize(pc);pon=normalize(po)
G=(1+z)*(j*(j+2)+(h+j+2)*l-2*h*(h+1))-2*(h+1)*h*xx*z
Dt=(1+z)*((1+h)**2+2*(1+h)*xx+1+2*xx-2*xx**2)-2*j*h*xx*z
generators=[-G,Dt,G*G,-G*Dt,Dt*Dt]
def read_positive(name,count):
 global checks
 out=ring4.zero;seen=set()
 with (ROOT/name).open(newline='') as f:
  rows=list(csv.DictReader(f))
 for row in rows:
  powers=tuple(int(row[n]) for n in ('h','j','z','ell'))
  coefficient=int(row['coefficient'])
  assert powers not in seen and min(powers)>=0 and coefficient>0
  seen.add(powers);out+=ring4.from_dict({powers:coefficient})
 assert len(rows)==count
 checks+=1
 return out
rc=read_positive('mixed_global_short_bridge_truncated_scale_q0_positive.csv',3242)
ro=read_positive('mixed_global_short_bridge_truncated_scale_t2_positive.csv',2172)
assert pcn==393216*j*z*z*G+rc
checks+=1
mm=ring4.zero;seen=set()
with (ROOT/'mixed_global_short_bridge_truncated_scale_t2_multipliers.csv').open(newline='') as f:
 rows=list(csv.DictReader(f))
for row in rows:
 gn=int(row['generator']);powers=tuple(int(row[n]) for n in ('h','j','z','ell'));c=int(row['coefficient'])
 assert 0<=gn<5 and min(powers)>=0 and c>0 and (gn,powers) not in seen
 seen.add((gn,powers));mm+=ring4.from_dict({powers:c})*generators[gn]
assert len(rows)==39 and 183*pon==mm+ro
checks+=1
print(f'All {checks} exact truncated-scale identities and complete-table checks passed.')
