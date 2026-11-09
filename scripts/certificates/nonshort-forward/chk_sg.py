from model import *
from qe import alq, beq, wU_
R_=sp.Rational
# check 2v - e Hd/p = 2v - A L' - A^2 (w-1) - (1 - chi)
w_=sp.Symbol('w')
B=Bk(k); Z=q*B/W; e=q/W
Sd=(1-t)+Z-p**2/W-p**2/Z+p**3/B-p*L
Hd=(B/p)*(W*v+Z*w_-Sd)
A=e*B/p; chi=p*e
Lp_=L+(W*v-c+p**2/W)/p
print(sp.simplify(2*v-e*Hd/p - (2*v - A*Lp_ - A**2*(w_-1) - (1-chi))))
# Hd(wU)/B = log q + alpha q + beta/q + (Wv - c + p^2/W)/p - p^2/B
expr = Hd.subs(w_, wU_(k,v))/B - (L + alq(k,v)*q + beq(k)/q + (W*v-c+p**2/W)/p - p**2/B)
print(sp.simplify(expr))
