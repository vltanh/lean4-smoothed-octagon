#!/usr/bin/env python3
"""Exact algebra checks for GLOBAL_RADIAL_COMPLETION_BOUND.md; no sampling."""
import sympy as s
checks=0

def check(name,expr):
 global checks
 assert s.simplify(s.factor(expr))==0,(name,s.factor(expr))
 checks+=1;print('PASS',name)

x,y,z=s.symbols('x y z',real=True);x=s.symbols('x',nonzero=True,real=True)
B=s.Matrix([[x,y],[z,(1+y*z)/x]]);J=s.Matrix([[0,-1],[1,0]])
check('radial trace',-s.trace(J*B.inv()*J*B)/2-s.trace(B.T*B)/2)
p,mb,n,m=s.symbols('p mb n m',positive=True)
Q=s.Matrix([[mb+n,m],[m,mb-n]]);X=J*Q;P=s.diag(p,1/p);Pd=X.T*P+P*X
check('radial logarithmic derivative',Pd[0,0]/(2*p)+m)
check('determinant-one relation',Q.det()-(mb**2-n**2-m**2))
check('weighted trace',s.trace(Q*P.inv())/(2*mb)-((p+1/p)/2-(n/mb)*(p-1/p)/2))
t,b,c,H=s.symbols('t b c H',real=True)
check('ratio derivative',s.diff((b+c*H*t)/s.sqrt(1-t*t),t)-(c*H+b*t)/(1-t*t)**s.Rational(3,2))
A,z=s.symbols('A z',positive=True);kap=s.Rational(3,2)/A;c=kap+s.Rational(3,2);b=s.Rational(3,2)-kap;zs=(A+1/A)/2
check('joining hyperbolic tangent',b/c-(A-1)/(A+1))
num=b+c*(z-A)/(z+1);den2=1-(z-A)**2/(z*z-1)
check('radial coefficient squared',num**2/den2-3*kap*(z-1)/(z+1)*(z-zs))
check('positive numerator',num-3*(z-zs)/(z+1))
check('potential normalization',c*c-3*kap*(zs+1))
e=s.symbols('eta',positive=True);zz=zs+(zs+1)*e*e
check('potential derivative parametrized',s.diff(c*(e-s.atan(e)),e)-c*e*e/(1+e*e))
check('radial integral derivative squared',(c*e*e/(1+e*e)/(2*(zs+1)*e))**2-3*kap*(zz-zs)/(4*(zz+1)**2))
print(f'{checks} exact checks passed')
