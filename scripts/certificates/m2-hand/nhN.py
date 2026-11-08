from sympy import *
t,x,k,q,v,L = symbols('t x k q v L')
def nhN(t,x,k,q,v,L):
    return (-t*(t+x)**2*(1+x)**2
     - t*(2*t**3*x + 5*t**2*x**2 - 2*t**2*x - 2*t**2 + 2*t*x**3 - 6*t*x**2 - 4*t*x - 2*x**3 - x**2)*q
     + t*(5*t**2*x**2 + 2*t**2*x - t**2 + 4*t*x**3 - 2*t*x**2 - 4*t*x + x**4)*q**2
     - t*x*(t+x)*(2*t+x)*(1+x)*L*q
     + t*x*(1+x)*(2*t+x**2+3*x)*v*q
     - t*x**2*(x+2)**2*v*q**2
     + k*((t**3*x + t**2*x**2 - 2*t**2*x - t**2 - t*x**2 - x**2 - x)*q
          + (-t**2*x**2 + 2*t**2*x + t**2 + 2*t*x**2 + x**2 + 2*x)*q**2
          - t*(t+x)*(1+x)*L*q
          + x*(1-t)*(1+x)*v*q
          - x*(x+2)*v*q**2))
