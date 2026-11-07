"""Finite diagnostic for reverse-five rational lower bound; NOT a certificate.
Exact tangent domain: q,r>1, other factors fixed by docs/REVERSE_FIVE_ARC.md.
Evaluated variables: q=1+exp(u), r=1+exp(v), u,v in [-18,18].
Deterministic 61x61 grid plus 3000 seeded uniform points in this box,
plus the symmetric golden-ratio point. No optimizer, interval arithmetic,
exhaustive real-domain coverage, or mathematical lower bound is claimed.
Python 3.12.14, mpmath 1.3.0. Reproduce from the repository root with
python explorations/reverse_five_rational_diagnostic.py.
All values evaluated with mpmath at 80 decimal digits; suspicious minima
should be independently reevaluated. State feasibility uses N>0,
strictly positive B_i (the proved orientation), and
B_i B_(i+1)<4N at switching states.
"""
import mpmath as m
import random
m.mp.dps=80
TARGET=m.mpf(109)/120

def value(q,r):
 A=m.sqrt(q*q-1); B=m.sqrt(r*r-1); W=m.sqrt(q*q+r*r-1)
 Q=[W/B,q,r,W/A,q*r/(A*B)]
 P=m.fprod(Q); F=1-sum(Q)+sum(Q[i]*Q[(i+2)%5] for i in range(5))
 N=P-F*F/4
 if N<=0: return None
 b=[2*Q[i]*(Q[(i+2)%5]+Q[(i+3)%5]-1)-F for i in range(5)]
 if not all(t>0 for t in b): return None
 slack=[4*N-b[i]*b[(i+1)%5] for i in range(5)]
 if min(slack)<=0: return None
 alg=20*N-3*sum(b[i]*b[(i+1)%5] for i in range(5))
 L=[(t-1/t)/6+m.mpf(4)/3*(t-1)/(t+1) for t in Q]
 rat=(alg-sum(t*t*l for t,l in zip(b,L)))/(8*N)
 actual=(alg-sum(t*t*m.log(w) for t,w in zip(b,Q)))/(8*N)
 return rat,actual,min(abs(t) for t in b)/m.sqrt(N),min(slack)/N

phi=(1+m.sqrt(5))/2
best=(m.inf,None); counts={'tested':0,'feasible_numerically':0,'below_target':0}
def test(q,r,tag):
 global best
 counts['tested']+=1
 v=value(q,r)
 if v is None:return
 counts['feasible_numerically']+=1
 if v[0]<TARGET: counts['below_target']+=1
 if v[0]<best[0]:best=(v[0],(q,r,tag,v))
test(phi,phi,'symmetric exact radical')
for i in range(61):
 for j in range(61):
  u=m.mpf(-18)+m.mpf(36)*i/60;v=m.mpf(-18)+m.mpf(36)*j/60
  test(1+m.exp(u),1+m.exp(v),'grid')
rng=random.Random(5102)
for _ in range(3000):
 u=m.mpf(str(rng.uniform(-18,18)));v=m.mpf(str(rng.uniform(-18,18)))
 test(1+m.exp(u),1+m.exp(v),'seeded finite points')
print('finite diagnostic only:',counts)
q,r,tag,v=best[1]
print('smallest evaluated rational value:',m.nstr(best[0],40))
print('at q,r:',m.nstr(q,35),m.nstr(r,35),tag)
print('exact-formula density at same point:',m.nstr(v[1],40))
print('margin from proposed109/120:',m.nstr(v[0]-TARGET,35))
print('evaluated minimum active margin, normalized star slack:',m.nstr(v[2],20),m.nstr(v[3],20))
