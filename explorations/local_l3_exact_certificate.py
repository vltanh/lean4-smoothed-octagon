#!/usr/bin/env python3
"""Reproduce the finite algebra in LOCAL_L3_STRONG_MINIMUM.md.

Input: one tuple only, word 021210, all factors 5/4,
raw initial state (1, 2, 193/112), physical scale squared 448/803.
No random inputs, optimization, or word search.
Run: python3 explorations/local_l3_exact_certificate.py
Reproduced with Python 3.12.14 and SymPy 1.14.0; versions are printed.

The script checks finite rational/logarithmic identities, not a universal
local improvement, a distant-replacement comparison, or a global optimum.
All logarithm signs and the sufficient-optimality application are proved
in the hand note. No Lean/Lake/typecheck/CI operation is performed.
"""
import platform
import sympy as s

L,M,r,z=s.symbols('L M r z')
q=s.Rational(5,4)
scale2=s.Rational(448,803)
word=(0,2,1,2,1,0)
initial=(s.Rational(1),s.Rational(2),s.Rational(193,112))

class Jet:
    def __init__(self,v,d=0,dd=0):
        self.v,self.d,self.dd=map(s.sympify,(v,d,dd))
    def __add__(self,o):
        o=coerce(o);return Jet(self.v+o.v,self.d+o.d,self.dd+o.dd)
    __radd__=__add__
    def __neg__(self):return Jet(-self.v,-self.d,-self.dd)
    def __sub__(self,o):return self+-coerce(o)
    def __rsub__(self,o):return coerce(o)+-self
    def __mul__(self,o):
        o=coerce(o)
        return Jet(self.v*o.v,self.d*o.v+self.v*o.d,
                   self.dd*o.v+2*self.d*o.d+self.v*o.dd)
    __rmul__=__mul__
    def inv(self):
        return Jet(1/self.v,-self.d/self.v**2,
                   2*self.d**2/self.v**3-self.dd/self.v**2)
    def __truediv__(self,o):return self*coerce(o).inv()
    def __rtruediv__(self,o):return coerce(o)*self.inv()
    def log(self,value):
        return Jet(value,self.d/self.v,self.dd/self.v-self.d**2/self.v**2)

def coerce(x):return x if isinstance(x,Jet)else Jet(x)
def mul(A,B):
    return [[sum(A[i][k]*B[k][j]for k in range(2))for j in range(2)]for i in range(2)]
def tangent(i,Q):
    return ([[Q,Jet(0)],[Jet(0),1/Q]],
            [[1/Q,Q-1/Q],[Jet(0),Q]],
            [[1/Q,Jet(0)],[1/Q-Q,Q]])[i]

def evaluate(letters,factors,log_values):
    p=list(map(Jet,initial));F=[[Jet(1),Jet(0)],[Jet(0),Jet(1)]]
    cost=Jet(0);stages=[p.copy()]
    for i,Q,log_value in zip(letters,factors,log_values):
        a,b,c=p[i],p[(i+1)%3],p[(i-1)%3]
        cost+=a*((a+b)*(Q-1)+(a+c)*(1-1/Q)-a*Q.log(log_value))/8
        F=mul(F,tangent(i,Q));p=p.copy()
        p[(i+1)%3]=(a+b)*Q-a;p[(i-1)%3]=(a+c)/Q-a
        stages.append(p.copy())
    end=[F[0][0],F[0][1],F[1][0],p[0],p[1]]
    return end,cost,F,stages

out=[evaluate(word,[Jet(q,int(i==j))for i in range(6)],[L]*6)for j in range(6)]
Jac=s.Matrix([[out[j][0][i].d for j in range(6)]for i in range(5)])
grad=s.Matrix([out[j][1].d for j in range(6)])
integer_J=s.Matrix([
    [7,-7,-25,-25,-7,7],
    [72,-72,200,0,128,-72],
    [72,-128,0,-200,72,-72],
    [-1484,2185,-1305,2405,-1525,0],
    [9441,-6065,-4055,-8595,-1525,7625],
])
assert s.diag(20,125,125,875,3500)*Jac==integer_J
assert Jac[:,[0,2,3,4,5]].det()==s.Rational(343552,546875)
v=s.Matrix([0,-1,-1,1,1,0])
assert Jac*v==s.zeros(5,1)
lam=s.Matrix([
    (685080*L-95041)/54880,
    5*(257840*L-3053)/175616,
    -5*(257840*L-3053)/175616,
    -3*(167840*L-18853)/1366400,
    -9*(76120*L-18789)/341600,
])
assert all(s.factor(x)==0 for x in grad-Jac.T*lam)
directional=evaluate(word,[Jet(q,x)for x in v],[L]*6)
end2=s.Matrix([x.dd for x in directional[0]])
assert list(end2)==[s.Rational(192,25),-s.Rational(3072,625),
                    s.Rational(3072,625),-s.Rational(2816,875),s.Rational(8096,875)]
assert s.factor(directional[1].dd+11*(3760*L+4359)/8750)==0
assert s.factor(directional[1].dd-(lam.T*end2)[0]-121*(51-224*L)/2450)==0
assert s.factor(scale2*out[0][1].v-(4535-4898*L)/5621)==0

def needle(arc,label):
    letters=list(word[:arc])+[word[arc],label,word[arc]]+list(word[arc+1:])
    factors=[Jet(q)]*arc+[Jet(r),Jet(1,1),Jet(q/r)]+[Jet(q)]*(5-arc)
    logs=[L]*arc+[M,0,L-M]+[L]*(5-arc)
    end,cost,_,_=evaluate(letters,factors,logs)
    return s.factor(cost.d-(lam.T*s.Matrix([x.d for x in end]))[0])

P01=(711040*L-20548)*r*r+(55685-352800*L)*r-98000-294000*r*M
P02=-50176*r*r+(894720*L-247172)*r+387365-1289200*L+136640*r*M
P10=(7043-23440*L)*r*r+(23440*L-5063)*r-1980-3660*r*M
P11=-36*r*r+(145-920*L)*r+1000*L-125+120*r*M
P20=-17600*r*r+(15760*L+1940)*r+24287-53840*L+31440*r*M
P22=(32*L-4)*r*r+(9-32*L)*r-5-8*r*M
first={(0,1):P01/392000,(0,2):P02/(200704*r*r),
       (1,0):11*P10/62720,(1,1):121*P11/(12544*r*r),
       (2,0):11*P20/(200704*r*r),(2,2):605*P22/3136}
for (arc,label),expected in first.items():
    assert s.factor(needle(arc,label)-expected)==0
    reflected_label=0 if label==0 else 3-label
    reflected=expected.subs({r:q/r,M:L-M},simultaneous=True)
    assert s.factor(needle(5-arc,reflected_label)-reflected)==0

def state_matrix(p):
    a,b,c=p
    return s.Matrix([[-a,a+c],[-a-b,a]])/2
def sector_forms(g):
    a,b,c,d=g[0,0],g[0,1],g[1,0],g[1,1]
    return [a+b-c-d,c+d,-c,a,b,d-b]

Ds=[s.diag(-1,1),s.Matrix([[1,-2],[0,-1]]),s.Matrix([[1,0],[2,-1]])]
tables=[
    [[0,417,946],[6424,7003,7414],[0,336,840],[6424,7115,7750],[0,305,610],[6424,7034,7644]],
    [[52976,95436,137896],[415184,439824,464464],[47040,87570,131796],[434000,476700,509335],[34160,58560,93025],[428064,468834,503235]],
    [[275792,429726,643390],[928928,954184,934010],[263592,425901,588210],[1018670,1069760,1120850],[186050,314150,456550],[1006470,1065935,1065670]],
    [[1029424,1456752,1884080],[1494416,1454068,1413720],[941136,1265754,1580285],[1793360,1895540,1900975],[730480,1015280,1396825],[1705072,1704542,1597180]],
    [[753632,919512,1121230],[565488,581658,570570],[632114,758079,884044],[760390,800040,839690],[558730,701130,852110],[638872,638607,602504]],
    [[4484920,5425635,6352014],[2282280,2278465,2194976],[3536176,4137546,4818590],[3358760,3590585,3728400],[3408440,4113515,4818590],[2410016,2302496,2194976]],
]
denominators=[6424,449680,1124200,2248400,1124200,5621000]
p=list(initial);g=s.eye(2)
for arc,i in enumerate(word):
    a,b,c=p[i],p[(i+1)%3],p[(i-1)%3];X=state_matrix(p)
    delta=s.eye(2)+(scale2*a/4)*((r-1/r)*X-(r+1/r-2)*X*Ds[i])
    path=(g*delta).applyfunc(s.factor)
    for row,f in enumerate(sector_forms(path)):
        poly=s.Poly(s.cancel(r*f).subs(r,1+z/4).expand(),z)
        assert poly.degree()<=2
        bern=[poly.nth(0),poly.nth(0)+poly.nth(1)/2,poly.eval(1)]
        assert [s.factor(x*denominators[arc])for x in bern]==tables[arc][row]
        assert all(x>=0 for x in tables[arc][row])
        assert tables[arc][row][1]>0 and tables[arc][row][2]>0
        if arc:assert tables[arc][row][0]>0
    g=path.subs(r,q).applyfunc(s.factor)
    p=p.copy();p[(i+1)%3]=(a+b)*q-a;p[(i-1)%3]=(a+c)/q-a
assert p==[1,s.Rational(193,112),2]
expected_frame=s.Matrix([[s.Rational(74568,140525),s.Rational(68837,100375)],
                         [-s.Rational(68837,100375),s.Rational(500969,501875)]])
assert g==expected_frame

print({'python':platform.python_version(),'sympy':s.__version__,
       'finite_input':'word021210, allfactors5/4, rawinitial(1,2,193/112)',
       'identities':'endpoint rank, stationarity, constrained Hessian, cost, all12 needle formulas, full sector Bernstein tables',
       'result':'all displayed exact identities reproduced',
       'limitation':'no universal L3 exclusion or distant-replacement comparison'})
