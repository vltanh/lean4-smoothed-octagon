from nsrN import *
N = expand(nsrN(t,x,k,q,v,L))
A = N.coeff(k,1)
Av = A.coeff(v,1); AL = A.coeff(L,1)
print('Av', factor(Av)); print('AL', factor(AL))
U = 1-t+t**2
lb = q*t*x*(1-t)*((q-1)*(2*x+1)+t*x)
d = expand(A.subs({v:U, L:q-1}) - lb)
print('diff', factor(d))
Nv = N.coeff(v,1); print('Nv', factor(Nv))
NL = N.coeff(L,1); print('NL', factor(NL))
