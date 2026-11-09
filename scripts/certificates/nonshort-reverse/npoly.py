from common import *
e = expand(cancel(N(k,v,L)))
P = Poly(e, k, v, L, q)
for mon, co in sorted(P.terms()):
    print(mon, factor(co))
