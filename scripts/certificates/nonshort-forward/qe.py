from model import *
R_=sp.Rational
# Q elimination quantities
eta = p/W
def wU_(kk, vv):
    B=Bk(kk); H=kk/t*(vv-1+t**2)+t*(2-t)
    return (kk**2-kk*t+t**2+H*Y+vv*Y**2)/B**2
def alq(kk,vv): return Bk(kk)*(wU_(kk,vv)-1)/(p*W)
def beq(kk): return p*W/Bk(kk)
def Cs(kk,vv):
    a=alq(kk,vv); b=beq(kk)
    return (12*eta**2-6*eta-12*a+12*b-12, 18*eta**2-7*eta-18*a+6*b-12, 6*eta**2-eta-6*a-1)
# check identity (8): F - g - (h(q)-h(1)) with L+ = y/(6(y+1)(y+2)) (C0+C1y+C2y^2)
yy=sp.Symbol('yy')
a=sp.Symbol('a'); b=sp.Symbol('b'); et=sp.Symbol('et')
qq=1+yy
Lpq=(qq-1)*(qq**2+10*qq+1)/(6*qq*(qq+1))
lhs = et+(et**2-a)*yy+b*yy/qq-(1+et*qq/yy)*Lpq
C0=12*et**2-6*et-12*a+12*b-12; C1=18*et**2-7*et-18*a+6*b-12; C2=6*et**2-et-6*a-1
print('id8', sp.simplify(lhs - yy/(6*(yy+1)*(yy+2))*(C0+C1*yy+C2*yy**2)))
# monotonicity in k: alpha(k)-alpha(1) - (beta(k)-beta(1))
d = sp.factor(sp.together((alq(k,v)-alq(1,v)) - (beq(k)-beq(1))))
print('alpha-beta diff', d)
