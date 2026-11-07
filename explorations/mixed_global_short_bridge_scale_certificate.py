"""Exact identities and complete positive tables for the scale lemma.

This checks algebra, not the open endpoint signs. No numerical sampling,
Lean, Lake, typechecking, CI, or complete-case claim.
"""
import sympy as s

A,B,X,P,T,h,j,k,t,z,rho,u,v=s.symbols('A B X P T h j k t z rho u v')
sigma=A*A-1; S=1+X; Q=A*(A+B)
D=(A+B)**2+S*S-(B+X)**2
ustar=(A*A+A*B+B*B)/(A+B)**2
Z=A*A+D*ustar; C=2*Q-D+S; L=C+Q-Z; H=2*Q-Z
AA=Q*(Q-D+S)
BB=Q*Q-(2*Z-sigma)*Q+D*Z-S*S-S*sigma-sigma*sigma
JJ=4*AA+2*BB-sigma*H
tables={
 'L': {
 (4,0):4, (3,1):12, (3,0):3*(7*h+6), (2,2):12,
 (2,1):3*(15*h+13), (2,0):43*h*h+73*h+29,
 (1,3):4, (1,2):3*(9*h+8), (1,1):2*(29*h*h+50*h+20),
 (1,0):(h+1)*(39*h*h+58*h+16), (0,3):3*(h+1),
 (0,2):15*h*h+27*h+11, (0,1):(h+1)*(5*h+2)*(5*h+6),
 (0,0):h*(h+1)**2*(13*h+16)},
 'H': {
 (4,0):2, (3,1):6, (3,0):2*(5*h+4), (2,2):6,
 (2,1):2*(11*h+9), (2,0):22*h*h+36*h+13,
 (1,3):2, (1,2):2*(7*h+6), (1,1):2*(16*h*h+27*h+10),
 (1,0):(h+1)*(23*h*h+34*h+8), (0,3):2*(h+1),
 (0,2):10*h*h+18*h+7, (0,1):(h+1)*(17*h*h+28*h+8),
 (0,0):3*h*(h+1)**2*(3*h+4)},
 'J': {
 (6,0):8, (5,1):32, (5,0):8*(7*h+5), (4,2):48,
 (4,1):8*(23*h+17), (4,0):4*(h+1)*(44*h+21),
 (3,3):32, (3,2):24*(9*h+7), (3,1):2*(227*h*h+348*h+118),
 (3,0):4*(76*h**3+172*h*h+116*h+21),
 (2,4):8, (2,3):8*(13*h+11), (2,2):2*(193*h*h+312*h+113),
 (2,1):4*(143*h**3+338*h*h+242*h+49),
 (2,0):292*h**4+890*h**3+923*h*h+358*h+32,
 (1,4):16*(h+1), (1,3):2*(57*h*h+100*h+40),
 (1,2):4*(76*h**3+190*h*h+146*h+33),
 (1,1):2*(174*h**4+555*h**3+612*h*h+264*h+32),
 (1,0):h*(h+1)*(139*h**3+384*h*h+336*h+96),
 (0,4):6*(h+1)**2, (0,3):4*(h+1)*(9*h*h+15*h+5),
 (0,2):80*h**4+268*h**3+317*h*h+154*h+24,
 (0,1):h*(h+1)*(73*h**3+210*h*h+196*h+64),
 (0,0):h*h*(h+1)**2*(21*h*h+42*h+16)}
}
checks=0
def check(name,left,right=0):
 global checks
 if s.factor(left-right)!=0: raise AssertionError(name)
 checks+=1

sub={A:1+h,X:1+h+j,B:1+h+j+k}
for name,expression,count in [('L',L,33),('H',H,33),('J',JJ,76)]:
 reconstructed=sum(s.sympify(c)*j**i*k**l for (i,l),c in tables[name].items())
 check(name+' complete coefficient identity',
       ((A+B)**2*expression).subs(sub,simultaneous=True),reconstructed)
 coefficients=s.Poly(reconstructed,h,j,k).coeffs()
 if len(coefficients)!=count or not all(c>0 for c in coefficients):
  raise AssertionError(name+' strict positive coefficient table')
 checks+=1

check('bridge order lower bound', D.subs(B,A*X),
 A*(2+4*X-2*X*X)+(1+2*X)*(A-1)**2)
check('root domain positive coefficient',2*Q-D-sigma,2*X*(B-1))
check('leading base coefficient',Q-D+S,B*(2*X-A)-X)
w=1-1/T+1/T**2
vstar=1-S/(P-sigma)+S*S/(P-sigma)**2
Ns=T*T*(P*P*w-(P-sigma)**2*vstar)
check('norm clipping polynomial',Ns,
      (1-T)*P*P+T*T*(S+2*sigma)*P-T*T*(S*S+S*sigma+sigma*sigma))
Rc=T*T*(2*P-sigma-D*T)*(P-Z)-2*sigma*T*(T*T-T+1)*P
lam=1-sigma/P
der=(2-(sigma+D*T)/P)*(P-Z)+(sigma+T*D)*P/D*(w-lam*lam*vstar)-2*T*sigma*w
check('norm-upper derivative',P*T*T*der,Rc+(T+sigma/D)*Ns)
dercrit=(2-(sigma+D*T)/P)*(P-Z)-2*T*sigma*w
check('clipped-norm derivative',P*T*T*dercrit,Rc)
positive=(T+1)*z*z+(C*t*t+(2*L+2*C+sigma)*t+4*L)*z
positive+=T*(AA*t*t+(2*AA+(JJ+sigma*H)/2)*t+JJ)
check('compact positive decomposition',
      ((Rc+T*Ns)/T).subs(P,T*Q+z),positive.subs(t,T-2))

# Independently differentiate the original transported root expression.
lamr=1/(1+rho*sigma); dr=lamr*rho*D
Y=s.symbols('Y',positive=True)
Er=1+1/S+1/(1+Y)-rho+s.log(rho*S*(1+Y))-(1-u)*S-(1-v)*(1+Y)
F0=Er-rho*D*u; Fr=lamr*F0; wr=lamr*lamr*v-dr*Fr
EL=dr*u-Fr; Pr=1/rho+sigma
hh=lambda zz:s.log(zz)-1+1/zz
der_original=T*s.diff(wr,rho)-s.diff(hh(Pr/(A*A)),rho)-s.diff(EL,rho)
der_formula=lamr*((1+lamr-dr*T)*s.diff(F0,rho)-(sigma+T*D)*Fr-2*T*sigma*wr)
check('actual root scale derivative',der_original,der_formula)
check('central scale derivative',s.diff(F0,rho),1/rho-1-D*u)
check('affine norm derivative u',s.diff((2-(sigma+D*T)/P)*(P-A*A-D*u)+(sigma+T*D)*P/D*(w-lam*lam*v)-2*T*sigma*w,u),-D*(2-(sigma+D*T)/P))
check('affine norm derivative v',s.diff((2-(sigma+D*T)/P)*(P-A*A-D*u)+(sigma+T*D)*P/D*(w-lam*lam*v)-2*T*sigma*w,v),-(sigma+T*D)*P*lam*lam/D)

if __name__=='__main__':
 print(f'All {checks} exact scale identities and complete positive-table checks passed.')
