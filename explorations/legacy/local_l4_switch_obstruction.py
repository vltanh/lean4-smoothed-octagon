#!/usr/bin/env python3
"""Finite exact reproduction for docs/LOCAL_SIX_VARIATION.md.

Domain: word 010201; base q=(1,11/10,11/10,6/5,11/10,1);
raw p=(r,1,3), 1.0249705 < r < 1.0249706, normalized by
2/sqrt(4r+3). The first and last base arcs have zero duration;
the hand argument uses an implicit-function continuation to make
both positive. Fixed initial state and both actual endpoints are
retained in every variation; the stronger paired endpoint is used
for correcting needles. No closed-word equation F=R is imposed.

Finite inputs only; no random seeds, optimization, or parameter search.
Run: python3 explorations/local_l4_switch_obstruction.py
Dependencies: Python 3, SymPy (versions are printed below).
Failures: any lost exactness, failed rational bound, or nonpositive
Bernstein coefficient raises AssertionError. The output verifies
identities, not universal L4 exclusion or global/local minimality.
No Lean, Lake, typechecking, or CI is called.
"""
from fractions import Fraction as F
import sys
import sympy as s
print("versions", sys.version.split()[0], "SymPy", s.__version__)
r,L,M=s.symbols('r L M');qbase=[s.Integer(1),s.Rational(11,10),s.Rational(11,10),s.Rational(6,5),s.Rational(11,10),s.Integer(1)];logs=[0,L,L,M,L,0];w=[0,1,0,2,0,1]
D=[s.Matrix([[-1,0],[0,1]]),s.Matrix([[1,-2],[0,-1]]),s.Matrix([[1,0],[2,-1]])]
def T(i,q):return [s.Matrix([[q,0],[0,1/q]]),s.Matrix([[1/q,q-1/q],[0,q]]),s.Matrix([[1/q,0],[1/q-q,q]])][i]
def Q(i,q):return [s.Matrix([[1,0],[0,q]]),s.Matrix([[q,1-q],[0,1]]),s.Matrix([[q,0],[q-1,1]])][i]
def stage(p,i,q,lq):
 A,B,C=p[i],p[(i+1)%3],p[(i-1)%3]
 pnew=list(p);pnew[(i+1)%3]=(A+B)*q-A;pnew[(i-1)%3]=(A+C)/q-A
 J=A*((A+B)*(q-1)+(A+C)*(1-1/q)-A*lq)/8
 return s.Matrix(pnew),J

def evalad(word,qq,ll):
 n=len(word);p=s.Matrix([r,1,3]);dp=s.zeros(3,n);g=s.zeros(n,1);cost=0;states=[p];F=G=s.eye(2);cols=[]
 for k,(i,q,lq) in enumerate(zip(word,qq,ll)):
  q=s.sympify(q); lq=s.sympify(lq)
  AA=-F*D[i]*F.inv();BB=-G*D[i]*G.inv()/2;cols.append(s.Matrix([AA[0,0],AA[0,1],AA[1,0],BB[0,0],BB[0,1],BB[1,0]]))
  A,B,C=p[i],p[(i+1)%3],p[(i-1)%3];tA=s.zeros(1,3);tA[0,i]=(2*A*(q-1)+B*(q-1)+2*A*(1-1/q)+C*(1-1/q)-2*A*lq)/8;tA[0,(i+1)%3]=A*(q-1)/8;tA[0,(i-1)%3]=A*(1-1/q)/8
  g+=dp.T*tA.T;g[k]+=A*((A+B)*q+(A+C)/q-A)/8
  newp,J=stage(p,i,q,lq);cost+=J
  mat=s.eye(3);mat[(i+1)%3,i]=q-1;mat[(i+1)%3,(i+1)%3]=q;mat[(i-1)%3,i]=1/q-1;mat[(i-1)%3,(i-1)%3]=1/q
  dp=mat*dp;dp[(i+1)%3,k]+=(A+B)*q;dp[(i-1)%3,k]-=(A+C)/q
  p=s.simplify(newp);states.append(p);F=s.simplify(F*T(i,q));G=s.simplify(G*Q(i,q).inv())
 return s.simplify(cost),g,s.Matrix.hstack(*cols),states
cost,g,B,states=evalad(w,qbase,logs); lm=s.simplify(B.T.inv()*g);X=s.Matrix([[-r,r+3],[-r-1,r]])/2
C=s.factor(lm.dot(s.Matrix([0,0,0,X[0,0],X[0,1],X[1,0]])))
print('STATIONARITY',C,flush=True)
assert all(not x.atoms(s.Float) for x in lm)
ns=[]
for k in range(5):
 j=3-w[k]-w[k+1];ww=w[:k+1]+[j]+w[k+1:];qs=qbase[:k+1]+[1]+qbase[k+1:];ll=logs[:k+1]+[0]+logs[k+1:]
 _,gi,Bi,_=evalad(ww,qs,ll);nn=s.factor(gi[k+1]-lm.dot(Bi[:,k+1]));ns.append(nn);print('SWITCH',k,s.factor(nn),flush=True)
for name,val in [('C',C),('cost',cost)]+[(f'n{k}',x)for k,x in enumerate(ns)]:
 print('COEFF',name,s.Poly(s.together(val).as_numer_denom()[0],r), 'DEN',s.together(val).as_numer_denom()[1],flush=True)

assert all(not x.atoms(s.Float) for x in [C,*ns])
vals=[C,*ns]
class I:
 def __init__(self,lo,hi=None):self.lo=F(lo);self.hi=F(hi if hi is not None else lo)
 def __add__(self,b):
  b=b if isinstance(b,I) else I(b);return I(self.lo+b.lo,self.hi+b.hi)
 __radd__=__add__
 def __neg__(self):return I(-self.hi,-self.lo)
 def __sub__(self,b):return self+-b if isinstance(b,I)else self+I(-b)
 def __rsub__(self,b):return -self+b
 def __mul__(self,b):
  b=b if isinstance(b,I)else I(b);v=[self.lo*b.lo,self.lo*b.hi,self.hi*b.lo,self.hi*b.hi];return I(min(v),max(v))
 __rmul__=__mul__
 def __truediv__(self,b):
  b=b if isinstance(b,I)else I(b);assert b.lo*b.hi>0;return self*I(1/b.hi,1/b.lo)
 def __pow__(self,n):
  ans=I(1)
  for _ in range(n):ans*=self
  return ans
 def __repr__(self):return f'[{float(self.lo):.15g}, {float(self.hi):.15g}]'
def ev(ex,R):
 if ex==r:return R
 if ex==L:return IL
 if ex==M:return IM
 if ex.is_Rational:return I(F(int(ex.p),int(ex.q)))
 if ex.is_Add:
  ans=I(0)
  for a in ex.args:ans+=ev(a,R)
  return ans
 if ex.is_Mul:
  ans=I(1)
  for a in ex.args:ans*=ev(a,R)
  return ans
 if ex.is_Pow:
  a,b=ex.args
  if b==-1:return I(1)/ev(a,R)
  return ev(a,R)**int(b)
 raise Exception(ex)
IL=I(F(9531017980432485,10**17),F(9531017980432487,10**17));IM=I(F(18232155679395461,10**17),F(18232155679395464,10**17))
lo=F(10249705,10**7);hi=F(10249706,10**7);RR=I(lo,hi)
# Horner expansion first in r to reduce interval dependency, retaining L,M affine coefficients.
def horner(ex,R):return ev(s.horner(s.expand(ex),r),R)
for name,ex,R in [('Clo',vals[0],I(lo)),('Chi',vals[0],I(hi)),('Cprime',s.diff(vals[0],r),RR)]+[(f'N{k+1}',ex,RR)for k,ex in enumerate(vals[1:])]:
 v=horner(ex,R);print(name,v,flush=True)
# Rational arctanh log series certifies constants.
for z,target in [(F(1,21),IL),(F(1,11),IM)]:
 for n in [6,7,8,9]:
  a=2*sum((z**(2*k+1)/F(2*k+1) for k in range(n)),F(0));rem=2*z**(2*n+1)/(F(2*n+1)*(1-z*z))
  if target.lo<a and a+rem<target.hi:print('log certificate z,n',z,n,'fits',True);break
costraw=((-478500000*L-1650000*M+88396250)*r**2+(-225192000*L+123750000*M+337113375)*r-306590460*L-2320312500*M+1134919431)/1932612000
print('normalized cost',horner(costraw,RR)*4/(RR*4+3))
# State positivity and frame sector certificate, in the root interval.
D=[s.Matrix([[-1,0],[0,1]]),s.Matrix([[1,-2],[0,-1]]),s.Matrix([[1,0],[2,-1]])]
def T(i,q):return [s.Matrix([[q,0],[0,1/q]]),s.Matrix([[1/q,q-1/q],[0,q]]),s.Matrix([[1/q,0],[1/q-q,q]])][i]
def Q(i,q):return [s.Matrix([[1,0],[0,q]]),s.Matrix([[q,1-q],[0,1]]),s.Matrix([[q,0],[q-1,1]])][i]
X0=s.Matrix([[-r,r+3],[-r-1,r]])/2
Ft=Ht=s.eye(2);X=X0
z,u,v=s.symbols('z u v')
from math import comb
def bern(poly):
 p=s.Poly(s.expand(poly),u,v);du=p.degree(u);dv=p.degree(v);out=[]
 for i in range(du+1):
  for j in range(dv+1):
   bb=sum(p.coeff_monomial(u**k*v**l)*s.Rational(comb(i,k),comb(du,k))*s.Rational(comb(j,l),comb(dv,l))for k in range(i+1)for l in range(j+1))
   out.append(bb)
 return min(out),max(out)
for k,(idx,q)in enumerate(zip([1,0,2,0],[s.Rational(11,10),s.Rational(11,10),s.Rational(6,5),s.Rational(11,10)])):
 Xi=Q(idx,z)*X*Q(idx,z).inv();Fi=Ft*T(idx,z);g=s.simplify(-4*X0*Fi*Xi/(4*r+3))
 sectors=[g[0,0],g[1,1]-g[0,1],g[1,0]+g[1,1]]
 bs=[]
 for ee in sectors:
  poly=s.factor((4*r+3)*z*(ee-s.Rational(1,2)))
  poly=poly.subs({r:1+s.Rational(1,20)*v,z:1+(q-1)*u})
  bc=bern(poly);bs.append(bc[0]);assert bc[0]>0
 print('sector Bernstein minima',k+1,bs)
 Ft=s.simplify(Ft*T(idx,q));Ht=s.simplify(Q(idx,q)*Ht);X=s.simplify(Ht*X0*Ht.inv())
 pp=s.Matrix([-2*X[0,0],-2*X[1,0]+2*X[0,0],2*X[0,1]+2*X[0,0]])
 print('state raw',k+1,[horner(x,RR)for x in pp])

assert horner(vals[0],I(lo)).lo>F(6,10**9)
assert horner(vals[0],I(hi)).hi<-F(13,10**9)
assert horner(s.diff(vals[0],r),RR).hi<-F(1,5)
for ex,bnd in zip(ns,[F(1,30),F(3,200),F(7,20000),F(1,200),F(1,80)]):
 assert horner(ex,RR).lo>bnd
assert (horner(costraw,RR)*4/(RR*4+3)).hi<F(1,3)
print("PASS: exact stationary-root, five positive switch needles, cost, and sector certificates")
