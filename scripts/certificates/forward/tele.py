import sympy as sp
am,a,ap,Ls,Lt,LK,LK1=sp.symbols('am a ap Ls Lt LK LK1')
# switch j: prev am=a_{j-1}, a=a_j, next ap=a_{j+1}; Ls=log(am+a), Lt=log(a+ap), LK=log(a^2+4), LK1=log(ap^2+4)
b=(4-am*a)/(am+a)
q=(am+a)*(a+ap)/(a**2+4)
Lq=Ls+Lt-LK
raw=a*((a+b)*(q-1)+(a+am)*(1-1/q)-a*Lq)
G=3*a*ap-4-(a**2+ap**2)*Lt+(a**2*LK+ap**2*LK1)/2
psi=lambda am,a,Ls,LK: a*(am-(4-am*a)/(am+a))-a**2*Ls+a**2*LK/2
print(sp.simplify(raw-(G+psi(am,a,Ls,LK)-psi(a,ap,Lt,LK1))))
