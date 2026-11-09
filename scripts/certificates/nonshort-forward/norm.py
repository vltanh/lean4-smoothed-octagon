import sympy as sp
t,x,k,q,v,L,y,h,j,z = sp.symbols('t x k q v L y h j z')
c=1-t; p=t+x; W=1+x; X=x+2; Y=x*(x+2); J=t+Y
def Bk(k): return k+2*t*x+x**2
B=Bk(k); e=q/W
D=e*J-p; E=e**2*B+1-2*p*e
HU = k/t*(v-1+t**2)+t*(2-t)
wU = (k**2-k*t+t**2+HU*Y+v*Y**2)/B**2
TU = (v - e**2*(HU+2*v*Y) + e**4*B**2*wU)/E**2
Cs = t*W**2*D*E**2/e
Zz = q*B/W
R = (1-t)+Zz-p**2/W-p**2/Zz+p**3/B-p*L-W*v-Zz*wU+p*(HU+2*v*Y)/B
N = t*B*q*W*R
Tstar = TU + e*(J*e**2-1)/(t*W**2*D*E**2)*N
