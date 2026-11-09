from common import *
Nk = together(N(k,v,L))
num,den = fraction(Nk)
print('den',factor(den))
# affine in k?
e = expand(cancel(N(k,v,L)))
print('deg k', Poly(e, k).degree())
A = e.coeff(k,1)
P = 6*(q+1)*W**2*X**3*(N(1,vbar,Lp)-(q-1)*(vbar-Fl))
P = cancel(P.subs(q,1+y))
Pp = Poly(expand(P), y)
print('deg y', Pp.degree(), 'is poly', P.is_polynomial(t,x,y))
C = [Pp.coeff_monomial(y**i) for i in range(4)]
C = [factor(cc) for cc in C]
for cc in C: print(cc)
import pickle
pickle.dump(C, open('unitC.pkl','wb'))
