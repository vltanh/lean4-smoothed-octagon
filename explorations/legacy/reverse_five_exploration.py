"""Exploratory evaluation of exact reverse-five endpoint formulas; NOT a proof.
Domain: q,r>1; p=√(q²+r²−1)/√(r²−1), s=√(q²+r²−1)/√(q²−1),
z=qr/(√(q²−1)√(r²−1)). All five factors >1.
The tangent product is exactly R by the separate hand derivation.
K=RH fixes the initial state when elliptic; every switching margin is checked.
A finite list below is a diagnostic only, not optimization or a global bound.
Python 3.12.14, mpmath 1.3.0; 50 decimal digits; no random choices.
Also checks the proposed fixed-U symmetrization at U=exp(-4),
t=0,1/5,...,1. Those rounded evaluations are diagnostics, not derivative
certificates. Reproduce from the repository root with
python explorations/reverse_five_exploration.py.
"""
import mpmath as m
m.mp.dps=50
Z=[m.matrix([[0,1],[1,0]]),m.matrix([[1,-2],[0,-1]]),m.matrix([[-1,-2],[0,1]])]
R=m.matrix([[m.mpf('0.5'),m.mpf('-1.5')],[m.mpf('0.5'),m.mpf('0.5')]])
I=m.eye(2)
word=[0,2,1,0,2]
def tr(M): return M[0,0]+M[1,1]
def family(q,r):
 q=m.mpf(q); r=m.mpf(r)
 W=m.sqrt(q*q+r*r-1); A=m.sqrt(q*q-1); B=m.sqrt(r*r-1)
 f=[W/B,q,r,W/A,q*r/(A*B)]
 H=I.copy()
 for j,x in zip(word,f):
  ell=m.log(x)/2
  H=(m.cosh(ell)*I-m.sinh(ell)*Z[j])*H
 K=R*H
 d=1-tr(K)**2/4
 if d<=0: return {'elliptic':False,'d':d}
 Y=K-tr(K)/2*I
 X=m.sign(Y[1,0])*Y/m.sqrt(d)
 p=[-tr(z*X) for z in Z]
 minmargin=min(p); active=[]; delta=0
 for j,x in zip(word,f):
  a=p[j];b=p[(j+1)%3];c=p[(j-1)%3]
  active.append(a)
  delta+=a*((a+b)*(x-1)+(a+c)*(1-1/x)-a*m.log(x))/8
  p[(j+1)%3]=(a+b)*x-a
  p[(j-1)%3]=(a+c)/x-a
  minmargin=min(minmargin,*p)
 return {'elliptic':True,'cost':2*m.sqrt(3)*delta,'minmargin':minmargin,'traceK':tr(K),'factors':f,'active':active}
if __name__=='__main__':
 for q,r in [('1.01','1.01'),('1.1','1.1'),('1.225','1.225'),('1.61803398875','1.61803398875'),('2','2'),('5','5'),('100','100'),('1.1','2'),('1.1','10'),('2','5'),('2','100'),('10','100')]:
  a=family(q,r)
  print(q,r,{k:m.nstr(v,18) for k,v in a.items() if k not in ['elliptic','factors','active']})
 print('Fixed-U symmetrization diagnostic; not a monotonicity certificate:')
 U=m.exp(-4)
 for j in range(6):
  t=m.mpf(j)/5
  v=family(m.sqrt(1+U*m.exp(2*t)),m.sqrt(1+U*m.exp(-2*t)))
  Q=v['factors']; a=v['active']
  alg=20-3*sum(a[i]*a[(i+1)%5] for i in range(5))
  L=[(w-1/w)/6+m.mpf(4)/3*(w-1)/(w+1) for w in Q]
  rational=(alg-sum(c*c*l for c,l in zip(a,L)))/8
  print('t=',m.nstr(t,5),'rational=',m.nstr(rational,20),
        'exact-formula density=',m.nstr(v['cost']/(2*m.sqrt(3)),20))
