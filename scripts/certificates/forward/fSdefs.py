import sympy as sp
a,t,LI,Lc,tau=sp.symbols('a t LI Lc tau')
b=1-a; c=1-a*(1+t); D=a+t+a*t; z=(1+a)/(1-a)
N1=35*a**5*t**2 + 70*a**5*t + 35*a**5 + 35*a**4*t**2 - 35*a**4 - 70*a**3*t**2 - 210*a**3*t - 105*a**3 - 70*a**2*t**2 + 70*a**2*t + 105*a**2 + 35*a*t**2 + 206*a*t - 4*a + 35*t**2 - 4*t + 4
X1=a**3*t**2 + 2*a**3*t + a**3 + a**2*t**2 - a**2 - 3*a*t**2 - 6*a*t - 2*a - t**2
A0=a*D*(a**2*t + a**2 + 2*a*t + 2*a + t - 3)/(2*b) + a*c*(a*t + a + 3*t + 1)/(t*b)*LI + c*Lc
A1=-N1/(70*b**2) - X1/(t*b)*LI + 2*c/b*Lc
Hc=(2*(1-a**2)-t*(5+3*a+2*a**2))/(3*b)
tc=Hc/(1+Hc); tt=t/(1+t)
def psi(A0,A1,D,z,tau): return A0*(1/tau-1)+A1+z*(D*tau/2-tau**2/(3*(2-tau)))
def dpsi(A0,D,z,tau): return -A0/tau**2+z*(D/2-(4*tau-tau**2)/(3*(2-tau)**2))
E3=psi(A0,A1,D,z,tc)
E4=E3+dpsi(A0,D,z,tc)*(tt-tc)
