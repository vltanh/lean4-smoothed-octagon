from sympy import *
t,x,k,q,v,L,y,s,z = symbols('t x k q v L y s z')
W=1+x; X=x+2; p=t+x; Yn=x*(x+2)
def B(k): return k+2*t*x+x**2
def N(k,v,L):
    Bk=B(k); Z=q*Bk/W
    H0 = k/t*(v-1+t**2)+t*(2-t)
    wU = (k**2-k*t+t**2+H0*Yn+v*Yn**2)/Bk**2
    R = (1-t)+Z-p**2/W-p**2/Z+p**3/Bk-p*L-W*v-Z*wU+p*(H0+2*v*Yn)/Bk
    return t*Bk*q*W*R
vbar = 1+(1-t)**2/W-2*(1-t)/X*(1+x**2/(3*X**2))
Lp = (q-1)*(q**2+10*q+1)/(6*q*(q+1))
Fl = 1+p**2*q/W**2-p/W*(q**2+10*q+1)/(6*(q+1))
def pol(cs,var): return sum(Rational(cc)*var**i for i,cc in enumerate(cs))
