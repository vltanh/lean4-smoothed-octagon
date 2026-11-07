#!/usr/bin/env python3
"""Exact checks for the symmetric M1 interval 11/10 <= h <= 13/10.

Run: python explorations/m1_interval_certificate.py
Requires SymPy. Symbolic rational identities and finite Bernstein tables;
no samples, optimization, numerical integration, Lean, Lake or CI.
This supplements the hand proof in M1_SYMMETRIC_ESCAPE_INTERVAL.md.
"""
import platform
import sympy as s


def main():
    h,L=s.symbols('h L',positive=True);cancel=s.cancel
    D=[s.diag(-1,1),s.Matrix([[1,-2],[0,-1]]),s.Matrix([[1,0],[2,-1]])]
    def T(i,r):return ((r+1/r)*s.eye(2)+(1/r-r)*D[i])/2
    word=[0,2,1,2,1,0];d=3*h-2;U=3*h*h-10*h+4;V=3*h*h-9*h+2
    z=cancel((-3*h**3+10*h*h-7*h+2)/d)
    p=s.Matrix([1,2,z]);dp=s.zeros(3,6);g=s.zeros(1,6);F=s.eye(2);cols=[];states=[p.copy()]
    for j,i in enumerate(word):
        a,b,c=p[i],p[(i+1)%3],p[(i-1)%3]
        da,db,dc=dp[i,:],dp[(i+1)%3,:],dp[(i-1)%3,:]
        ez=s.zeros(1,6);ez[j]=1
        M=cancel((a+b)*(h-1)+(a+c)*(1-1/h)-a*L)
        dm=(da+db)*(h-1)+(a+b)*h*ez+(da+dc)*(1-1/h)+(a+c)/h*ez-da*L-a*ez
        g=(g+(da*M+a*dm)/8).applyfunc(cancel)
        cols.append((-F*D[i]*F.inv()).applyfunc(cancel))
        F=(F*T(i,h)).applyfunc(cancel)
        dp[(i+1)%3,:]=((da+db)*h+(a+b)*h*ez-da).applyfunc(cancel)
        dp[(i-1)%3,:]=((da+dc)/h-(a+c)/h*ez-da).applyfunc(cancel)
        p[(i+1)%3]=cancel((a+b)*h-a);p[(i-1)%3]=cancel((a+c)/h-a);states.append(p.copy())
    J=s.zeros(5,6)
    for j,C in enumerate(cols):
        df=(C*F).applyfunc(cancel)
        J[:,j]=s.Matrix([df[0,0],df[0,1],df[1,0],dp[0,j],dp[1,j]])
    def poly(v):return sum(x*h**i for i,x in enumerate(v))
    N0=poly([-24,200,-622,873,-568,186,-72,27])+L*poly([0,-24,176,-432,388,-78,-18])
    N1=poly([-24,192,-568,771,-553,257,-93,18])+L*poly([0,-24,172,-408,354,-90])
    N3=poly([24,-224,846,-1657,1869,-1338,660,-207,27])+L*poly([0,24,-184,524,-660,342,-54])
    N4=poly([-24,208,-646,875,-518,141,-63,27])+L*poly([0,-24,176,-432,388,-78,-18])
    nu=s.Matrix([-N0/(8*h*(h-1)*d*d*(h*h-2)),
       -h*N1/(16*(h-1)*d*d*(h*h-2)),h*N1/(16*(h-1)*d*d*(h*h-2)),
       -N3/(8*h*h*(h-1)*d*U),N4/(8*h*h*(h-1)*d*U)])
    checks=[]
    def zero(name,expr):
        assert cancel(expr)==0,name;checks.append(name)
    zero('endpoint minor',J[:,[0,2,3,4,5]].det()-32*(h-1)**2*(3*h-1)*(h*h-2)*U/(h*h*d*d))
    for j,v in enumerate(J.T*nu-g.T):zero('normal stationarity '+str(j),v)
    zero('frame chart',F[0,0]-(2-h*h))
    for j,v in enumerate(p-s.Matrix([1,z,2])):zero('reflected endpoint '+str(j),v)
    r=s.symbols('r',positive=True);pref=(F*T(0,h).inv()).applyfunc(cancel);start=states[5]
    def gaps(j):
        p=start.copy();a,b,c=p
        p[1]=cancel((a+b)*r-a);p[2]=cancel((a+c)/r-a)
        a,b,c=p[j],p[(j+1)%3],p[(j-1)%3]
        dg=cancel(a*(a+b+c)/8);dp=s.zeros(3,1)
        dp[(j+1)%3]=a+b;dp[(j-1)%3]=-(a+c)
        a,b,c=p;da,db,dc=dp;v=h/r;logv=L-s.log(r)
        M=(a+b)*(v-1)+(a+c)*(1-1/v)-a*logv
        dm=(da+db)*(v-1)+(da+dc)*(1-1/v)-da*logv
        dg=cancel(dg+(da*M+a*dm)/8)
        dp[1]=cancel((da+db)*v-da);dp[2]=cancel((da+dc)/v-da)
        df=(pref*T(0,r)*(-D[j])*T(0,h/r)).applyfunc(cancel)
        ep=s.Matrix([df[0,0],df[0,1],df[1,0],dp[0],dp[1]])
        at=lambda v:cancel(v.subs(r,1))
        return cancel(at(dg)-(ep.applyfunc(at).T*nu)[0]),cancel(at(s.diff(dg,r))-(ep.diff(r).applyfunc(at).T*nu)[0])
    edge,third=gaps(1),gaps(2)
    P=(-30*h**4+108*h**3-100*h*h+24*h)*L+6*h**6-35*h**5+114*h**4-245*h**3+280*h*h-144*h+24
    E=(-26*h**3+40*h*h-12*h)*L+6*h**5-21*h**4+56*h**3-87*h*h+58*h-12
    zero('edge tie',edge[0])
    zero('edge gap slope',edge[1]+(3*h-1)*P/(8*h*(h-1)*d*d))
    zero('third gap',third[0]-(h-1)*(3*h-1)**2*(h*L-h+1)/(d*d))
    zero('third gap combination',2*third[0]+third[1]-(3*h-1)*E/(8*h*(h-1)*d))
    kap=cancel(4/(2+3*z));b=states[5][1];qs=s.sqrt(3)/3
    a=cancel(qs*(b-1)/(b+1));w0=cancel(3*kap*(1+b)**2/16);W=kap/4;c=cancel(W/(qs-a))
    zero('exit ratio',(1+W)/(2*qs*c)-3*h)
    zero('outgoing location',a-qs*h*(3*h-4)/U)
    zero('mu-a^2',-kap*edge[1]/w0-2*(3*h-1)*P/(3*h*(h-1)*U*U))
    zero('B0',-4*kap*w0*third[0]/3+4*(h-1)*U*U*(h*L-h+1)/(d*d*V*V))
    zero('B1',-4*kap*w0*(2*third[0]+third[1])/(3*c)+s.sqrt(3)*U*E/(3*h*(h-1)*d*V))
    lo=2*(h-1)/(h+1);hi=(h-1)*(h*h+10*h+1)/(6*h*(h+1))
    polys=[6*h**5-17*h**4-21*h**3+120*h*h-120*h+24,
       9*h**4-51*h**3+105*h*h-82*h+15,
       6*h**4-3*h**3-29*h*h+46*h-12,
       9*h**4-11*h**3-27*h*h+56*h-15,
       -3*h**3+10*h*h-7*h+2,-3*h**3+13*h*h-11*h+2,-6*h**3+17*h*h-12*h+2]
    zero('P lower envelope',P.subs(L,lo)-(h-1)**2*polys[0]/(h+1))
    zero('P upper envelope',P.subs(L,hi)-2*(h-1)**2*(h+2)*polys[1]/(3*(h+1)))
    zero('E lower envelope',E.subs(L,lo)-(h-1)**2*polys[2]/(h+1))
    zero('E upper envelope',E.subs(L,hi)-2*(h-1)**2*polys[3]/(3*(h+1)))
    rows=[(25000,[-149441,-128256,-106357,-84208,-62145,-40328]),
       (10000,[-28541,-22648,-16619,-10682,-4921]),
       (30000,[249048,253929,259742,267891,280068]),
       (10000,[124659,126952,129381,132518,137079]),
       (3000,[7221,8043,8869,9627]),(3000,[4911,6253,7719,9237]),
       (750,[1038,1219,1372,1461])]
    t=s.symbols('t')
    for j,(p,(scale,coeffs)) in enumerate(zip(polys,rows)):
        n=len(coeffs)-1
        bern=sum(v*s.binomial(n,k)*t**k*(1-t)**(n-k) for k,v in enumerate(coeffs))
        zero('Bernstein row '+str(j),scale*p.subs(h,(11+2*t)/10)-bern)
        assert all(v<0 for v in coeffs) if j<2 else all(v>0 for v in coeffs)
    print('Python',platform.python_version(),'SymPy',s.__version__)
    for name in checks:print('PASS',name)
    print('Total:',len(checks),'exact identities; seven uniform-sign Bernstein rows.')

if __name__=='__main__':main()
