from mpmath import mp, mpf, log, matrix, lu_solve
import random
mp.dps=40
def Ga(a,b): return 3*b-2*a*log(a+b)-(a*a+b*b)/(a+b)+a*log(a*a+4)+a**3/(a*a+4)
def fac(x,y,z): return (x+y)*(y+z)/(y*y+4)
def Cph(x,y,z): return x+y+z-y*y*(1/(x+y)+1/(y+z))+y**3/(y*y+4)-y*log(fac(x,y,z))
def F(x,r): return 1+x*x*r-x*r*log(r)/(r-1)
for trial in range(3):
    a=mpf(random.uniform(1.16,1.34)); b=a*mpf(random.uniform(1,1.3)); c=a*mpf(random.uniform(1,1.3))
    p=a*mpf(random.uniform(1,1.5)); d=a*mpf(random.uniform(1,1.5))
    h=fac(p,b,a); q=fac(b,a,c); k=fac(a,c,d)
    def ws(mu):  # mu = (mu_{i-1}, mu_i, mu_{i+1}) at switch m
        mm1,m0,mp1=mu
        mu_ip1_m1 = h*h*(mm1+mp1)-mm1
        w_m2=-mu_ip1_m1; w_m1=-mm1; w_0=-m0
        mu_ip1_1=q*q*(m0+mp1)-m0; mu_im1_1=(m0+mm1)/(q*q)-m0
        w_1=-mu_ip1_1
        mu_im1_2=k*k*(mu_ip1_1+mu_im1_1)-mu_ip1_1
        w_2=-mu_im1_2
        return w_m2,w_m1,w_0,w_1,w_2
    def stat(w,aa,ap,an):  # piece with active aa, prev ap, next an; w=(wprev,w,wnext)
        return (w[0]+w[1])/(ap+aa)+(w[1]+w[2])/(aa+an)-2*aa*w[1]/(aa*aa+4)-(Ga(aa,ap)+Ga(aa,an))/8
    def eqs(mu):
        w=ws(mu)
        return [stat(w[0:3],b,p,a),stat(w[1:4],a,b,c),stat(w[2:5],c,a,d)]
    # linear: build matrix
    base=eqs([0,0,0]); M=matrix(3,3)
    for j in range(3):
        e=[0,0,0];e[j]=1; r=eqs(e)
        for i in range(3): M[i,j]=r[i]-base[i]
    mu=lu_solve(M,matrix([-x for x in base]))
    w=ws([mu[0],mu[1],mu[2]])
    u=4*(w[1]+w[2])/(a+b)**2; v=4*(w[2]+w[3])/(a+c)**2; E=8*w[2]/(a*a+4)
    K=a*a+4;Kb=b*b+4;Kc=c*c+4;s=a+b;t=a+c
    A=Cph(b,a,c);B=Cph(p,b,a);C=Cph(a,c,d)
    Mn=lambda a,b,h:(a+b)**2*(4-a*b)*(h-1)/(a*(b*b+4))
    Mm=lambda a,b,q,h:(a*a+4)**2*(a*(q-1)+(h-1)*((a+b)*q-a))/(a*(a+b)*(b*b+4))
    Mal=lambda a,b,h:(a*a+4)*(h*(a+b)-b)/(a*(b*b+4))
    print('row0',s*u+t*v-a*E-A)
    print('rowL',Mn(a,b,h)*u+Mm(a,b,q,h)*v-(Mal(a,b,h)*A-B))
    print('rowR',Mm(a,c,q,k)*u+Mn(a,c,k)*v-(Mal(a,c,k)*A-C))
    print('u,v,E',u,v,E, 'floors', u-F(b/s,h), v-F(c/t,k))
