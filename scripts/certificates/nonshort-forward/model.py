import sympy as sp
t,x,k,q,v,L,y,h,j,z,a,b = sp.symbols('t x k q v L y h j z a b')
c=1-t; p=t+x; W=1+x; X=x+2; Y=x*(x+2); J=t+Y; R=x**2+10*x+15
def Bk(k): return k+2*t*x+x**2
# Lean nsrN
def nsrN(t,x,k,q,v,L):
    return (-t * (t + x) ** 2 * (1 + x) ** 2
    - t * (2 * t ** 3 * x + 5 * t ** 2 * x ** 2 - 2 * t ** 2 * x - 2 * t ** 2 + 2 * t * x ** 3
      - 6 * t * x ** 2 - 4 * t * x - 2 * x ** 3 - x ** 2) * q
    + t * (5 * t ** 2 * x ** 2 + 2 * t ** 2 * x - t ** 2 + 4 * t * x ** 3 - 2 * t * x ** 2 - 4 * t * x
      + x ** 4) * q ** 2
    - t * x * (t + x) * (2 * t + x) * (1 + x) * L * q
    + t * x * (1 + x) * (2 * t + x ** 2 + 3 * x) * v * q
    - t * x ** 2 * (x + 2) ** 2 * v * q ** 2
    + k * ((t ** 3 * x + t ** 2 * x ** 2 - 2 * t ** 2 * x - t ** 2 - t * x ** 2 - x ** 2 - x) * q
      + (-t ** 2 * x ** 2 + 2 * t ** 2 * x + t ** 2 + 2 * t * x ** 2 + x ** 2 + 2 * x) * q ** 2
      - t * (t + x) * (1 + x) * L * q
      + x * (1 - t) * (1 + x) * v * q
      - x * (x + 2) * v * q ** 2))
def Hpol(k,v): return k*(v-1+t**2)+t**2*(2-t)          # t*H_U
def Kpol(k,v): return t*(k**2-k*t+t**2)+Hpol(k,v)*Y+t*v*Y**2   # t*B^2*w_U
def Nc(k,v,L):
    B=Bk(k)
    return t*B*q*W*c+t*q**2*B**2-t*B*q*p**2-t*p**2*W**2+t*q*W*p**3-t*B*q*W*p*L-t*B*q*W**2*v-q**2*Kpol(k,v)+q*W*p*(Hpol(k,v)+2*t*v*Y)
def E0(k): return q**2*Bk(k)+W**2-2*p*q*W
def transportPart(k,v):  # = 4 q W^2 * C_*(3/4 - T_U)
    return (q*J-p*W)*(3*t*E0(k)**2-4*t*v*W**4+4*q**2*W**2*(Hpol(k,v)+2*t*v*Y)-4*q**4*Kpol(k,v))
def Fl(q_): return 1+p**2*q_/W**2-p/W*(q_**2+10*q_+1)/(6*(q_+1))
Lp = (q-1)*(q**2+10*q+1)/(6*q*(q+1))
VG = 1-c*p/W**2+c*x/W**2*((90-19*x**2)/(12*R)-t)
V3 = 1+c**2/W-2*c/X*(1+x**2/(3*X**2)+x**4/(5*X**4))
Vq = 1+c**2/W-3*c*(x+2)/(x**2+6*x+6)
V2 = 1-c*p/W**2+c*x/W**2*(sp.Rational(1,2)-x/3+x**2/12-t)
Uc = 1-t+t**2
gc = 1-c*p/W**2
# combined (cleared by 4qW^2): (alpha+1-Je^2) N + C*(3/4-T_U) + M (Fl - v)
def comb(alpha,M,k,v,L,Fv):
    return 4*q*((alpha+1)*W**2-J*q**2)*Nc(k,v,L)+transportPart(k,v)+4*q*W**2*M*(Fv-v)
