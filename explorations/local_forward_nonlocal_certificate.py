#!/usr/bin/env python3
"""Exact finite check of LOCAL_FORWARD_NONLOCAL_REPLACEMENT.md.

Run: python3 explorations/local_forward_nonlocal_certificate.py
Finite input: one rational 012012 input and one rational 012021 center.
No randomness, optimizer, floating-point root, or sampling is used. Runtime
versions are printed. The hand note supplies the contraction and cost proof.
This checks one replacement only and does not prove universal L1. No Lean,
Lake, typechecking, or CI command is executed.
"""
import json
import platform
import sympy as S

qvals=list(map(S.Rational,[
 '1.182504115604994555893003849647',
 '1.121181801593551227623891266831',
 '1.322925994119170300909296093597',
 '1.129614983346815860414127778040',
 '1.125598579575947873122187353667', '1.09']))
word=[0,1,2,0,2,1]
t0=S.Rational(4761,3950)
sigma2=S.Rational(1975,1684)
p0=S.Matrix([1,1,t0])
r=S.Rational(11,10)
oldq=[r,r,r*r,r*r,r,r*r]
oldword=[0,1,2,0,1,2]
B=S.Matrix([
 [20238092,15378147,-6613901,1537414,-4365336],
 [-4754669,-3229164,1533209,-374696,1063914],
 [73193410,51482313,-28689302,1567271,-17523544],
 [-26513687,-19260435,9169587,-1205849,6505239],
 [-66589556,-46277963,26327041,-695457,16168477],
])/10**6
def calc(w,qq):
 p=p0.copy();F=S.eye(2);nonlog=S.Integer(0);coeff=[];states=[p.copy()]
 for i,q in zip(w,qq):
  a,b,c=p[i],p[(i+1)%3],p[(i-1)%3];nonlog+=a/8*((a+b)*(q-1)+(a+c)*(1-1/q));coeff.append(a*a/8)
  Ts=[S.diag(q,1/q),S.Matrix([[1/q,q-1/q],[0,q]]),S.Matrix([[1/q,0],[1/q-q,q]])];F=F*Ts[i]
  p=p.copy();p[(i+1)%3]=(a+b)*q-a;p[(i-1)%3]=(a+c)/q-a;states.append(p.copy())
 return S.Matrix([F[0,0],F[0,1],F[1,0],p[0],p[1]]),nonlog,coeff,states
def de(w,qq,col):
 p=p0.copy();dp=S.zeros(3,1);F=S.eye(2);dF=S.zeros(2,2)
 for k,(i,q) in enumerate(zip(w,qq)):
  dq=int(k==col);a,b,c=p[i],p[(i+1)%3],p[(i-1)%3];da,db,dc=dp[i],dp[(i+1)%3],dp[(i-1)%3];pp=p.copy();dpp=dp.copy();pp[(i+1)%3]=(a+b)*q-a;pp[(i-1)%3]=(a+c)/q-a;dpp[(i+1)%3]=(da+db)*q+(a+b)*dq-da;dpp[(i-1)%3]=(da+dc)/q-(a+c)*dq/q**2-da
  Ts=[S.diag(q,1/q),S.Matrix([[1/q,q-1/q],[0,q]]),S.Matrix([[1/q,0],[1/q-q,q]])];dTs=[S.diag(1,-1/q**2),S.Matrix([[-1/q**2,1+1/q**2],[0,1]]),S.Matrix([[-1/q**2,0],[-1/q**2-1,1]])]
  dF=dF*Ts[i]+F*dTs[i]*dq;F=F*Ts[i];p,dp=pp,dpp
 return S.Matrix([dF[0,0],dF[0,1],dF[1,0],dp[0],dp[1]])

orig=calc(oldword,oldq)
new=calc(word,qvals)
f0=new[0]-orig[0]
M=S.Matrix.hstack(*[de(word,qvals,k) for k in range(5)])
row_norm=lambda mat:max(sum(abs(v) for v in mat.row(k)) for k in range(mat.rows))
R=S.eye(5)-B*M
rho=S.Rational(1,10**15)
assert row_norm(B)<200
assert row_norm(R)<S.Rational(1,10**5)
assert max(abs(v) for v in f0)<S.Rational(1,10**28)
assert max(abs(v) for v in B*f0)<S.Rational(1,10**25)
assert min(v for pp in new[3] for v in pp)>S.Rational(7,10)
assert orig[0][0]>0
assert all(1<q-rho and q+rho<2 for q in qvals)
assert S.Rational(1,10**5)+200*102400*rho<S.Rational(1,2)
assert S.Rational(1,10**25)<rho/2
assert S.Rational(7,10)-5*972*rho>0

N=12
Rlog=2*S.Rational(1,7)**(2*N+1)/((2*N+1)*(1-S.Rational(1,7)**2))
def log_bounds(q):
 assert 1<=q<=S.Rational(4,3)
 z=(q-1)/(q+1)
 lower=2*sum(z**(2*k+1)/S.Integer(2*k+1) for k in range(N))
 return lower,lower+Rlog

def cost_bounds(data,qq):
 _,nonlog,coeff,_=data
 lowers,uppers=zip(*[log_bounds(q) for q in qq])
 return (sigma2*(nonlog-sum(c*u for c,u in zip(coeff,uppers))),
         sigma2*(nonlog-sum(c*l for c,l in zip(coeff,lowers))))

olo,ohi=cost_bounds(orig,oldq)
nlo,nhi=cost_bounds(new,qvals)
lower=olo-nhi
upper=ohi-nlo
assert lower>S.Rational(10263,10**9)
assert upper<S.Rational(10264,10**9)
P=S.Integer(486)
actual_derivative_bound=5*2*6*(5*P*972/4+5*P**2/8)
assert actual_derivative_bound<10**8
assert lower-10**8*rho>S.Rational(1,100000)
print(json.dumps({
 'python':platform.python_version(), 'sympy':S.__version__,
 'old_word':'012012', 'replacement_word':'012021',
 'exact_checks':['endpoint residual', 'approximate inverse residual',
  'contraction constants', 'positive whole-arc state margins',
  'rational logarithm bounds', 'strict cost decrease'],
 'contraction_ball_radius':'1/10^15',
 'proved_normalized_cost_decrease':'>1/100000',
 'scope':'One exact nonlocal six-piece replacement. Universal L1 remains open.'
},indent=2))
