#!/usr/bin/env python3
"""Finite-event normal PMP continuation using analytic vertex flows.

Run: python explorations/pmp_return_probe.py --dps 60 --output results.json
Requires mpmath. Arbitrary precision is NOT interval certification.
No ODE time stepping, optimizer, randomness, Lean, Lake or CI.
The normal initial lifts are reconstructed from exact stationary examples;
the pending general normality theorem is not a premise of these tests.
"""
from __future__ import annotations
import argparse
from dataclasses import dataclass
import json
import platform
from pathlib import Path
import mpmath as mp


def mat(a,b,c,d): return mp.matrix([[a,b],[c,d]])
def eye(): return mp.eye(2)
def norm(A): return max(abs(v) for v in A)
def trace(A): return A[0,0]+A[1,1]
def qstar(): return 1/mp.sqrt(3)
def rot(k):
    a=k*mp.pi/3
    return mat(mp.cos(a),-mp.sin(a),mp.sin(a),mp.cos(a))
def octagon_cost():
    return 2*mp.sqrt(3)*(8-4*mp.sqrt(2)-mp.log(2))/(2*mp.sqrt(2)-1)
def generators(): return (mat(-1,0,0,1),mat(1,-2,0,-1),mat(1,0,2,-1))
def basis():
    q=qstar(); return mat(q,q,1,-1)
def phi(xy):
    x,y=xy; return mat(x,-x*x-y*y,1,-x)/y

def margins(xy):
    x,y=xy; q=qstar()
    return [mp.sqrt(3)*(x*x+y*y-q*q)/y,2*(q-x)/y,2*(q+x)/y]

def xy_from_margins(p):
    return mp.matrix([(p[2]-p[1])/(mp.sqrt(3)*(p[1]+p[2])),
                      4/(mp.sqrt(3)*(p[1]+p[2]))])

def rotate_xy(xy,k):
    M=rot(-k); a,b,c,d=M[0,0],M[0,1],M[1,0],M[1,1];x,y=xy
    den=(c*x+d)**2+(c*y)**2
    out=mp.matrix([((a*x+b)*(c*x+d)+a*c*y*y)/den,y/den])
    v=1/(c*(x+1j*y)+d)**2
    return out,mat(v.real,-v.imag,v.imag,v.real)

def trajectory(word,logs,xy0):
    p=margins(xy0);F=eye();C=mp.mpf(0);T=mp.mpf(0);D=generators()
    for i,z in zip(word,logs):
        q=mp.exp(z);a,b,c=p[i],p[(i+1)%3],p[(i-1)%3]
        C+=mp.sqrt(12)*a*((a+b)*(q-1)+(a+c)*(1-1/q)-a*z)/8
        T+=a*z/2
        p[(i+1)%3]=(a+b)*q-a;p[(i-1)%3]=(a+c)/q-a
        F=F*((q+1/q)*eye()+(1/q-q)*D[i])/2
    end=xy_from_margins(p);B=basis()
    g=phi(xy0)*B*F*(B**-1)*(phi(end)**-1)
    return g,end,C,T

def derivative(f,x):
    base=list(x);out=mp.matrix(len(f(base)),len(base))
    for j in range(len(base)):
        def varied(z):
            v=base.copy();v[j]=z;return mp.matrix(f(v))
        col=mp.diff(varied,base[j])
        for i in range(out.rows):out[i,j]=col[i]
    return out

def group_covector(v): return mat(v[0]/2,v[2],v[1],-v[0]/2)

@dataclass
class Phase:
    g: mp.matrix
    xy: mp.matrix
    lam: mp.matrix
    p: mp.matrix
    cost: object=0
    time: object=0

def local_phase(word,factors,initial):
    xy0=xy_from_margins(initial);logs=[mp.log(q) for q in factors]
    gref,_,_,_=trajectory(word,logs,xy0);gi=gref**-1
    def output(v):
        g,xy,C,_=trajectory(word,v[2:],v[:2]);U=g*gi
        return [U[0,0]-1,U[0,1],U[1,0],xy[0],xy[1],C]
    jac=derivative(output,list(xy0)+logs);de=jac[:5,2:];gradient=jac[5,2:].T
    nu,_=mp.qr_solve(de.T,gradient)
    residual=norm(de.T*nu-gradient)
    p0=jac[:5,:2].T*nu-jac[5,:2].T
    if residual>mp.power(10,-mp.mp.dps//2):raise ValueError('nonstationary local input')
    return Phase(eye(),xy0,group_covector(nu[:3]),p0),residual

def regular_phase(k):
    N=3*k+1;q=2*mp.cos(mp.pi*k/N);a=mp.sqrt(4*q/(4-q));b=a*(2/q-1)
    xy0=xy_from_margins([a,b,a]);word=tuple(i%3 for i in range(N))
    def output(v):
        g,xy,C,_=trajectory(word,v[2:],v[:2]);U=g*rot(-1)
        target,_=rotate_xy(v[:2],1)
        return [U[0,0]-1,U[0,1],U[1,0],xy[0]-target[0],xy[1]-target[1],C]
    jac=derivative(output,list(xy0)+[mp.log(q)]*N)
    nu,_=mp.qr_solve(jac[:5,:].T,jac[5,:].T)
    residual=norm(jac[:5,:].T*nu-jac[5,:].T);_,rt=rotate_xy(xy0,1)
    return Phase(eye(),xy0,group_covector(nu[:3]),rt.T*nu[3:]),residual

def fields(i,xy):
    x,y=xy;q=qstar()
    if i==1:return mp.matrix([y,-y*y/(q-x)])
    if i==2:return mp.matrix([y,y*y/(q+x)])
    d=x*x+y*y-q*q
    return mp.matrix([y*(x*x-y*y-q*q)/d,2*x*y*y/d])

def hamiltonians(ph):
    x,y=ph.xy;cost_rate=mp.mpf(3)/2*(1+x*x+y*y)/y
    common=trace(ph.lam*phi(ph.xy))-cost_rate
    return [common+mp.fdot(ph.p,fields(i,ph.xy)) for i in range(3)]

class VertexArc:
    """Normal zero-Hamiltonian flow rotated to control 1, with r>=1."""
    def __init__(self,ph,active,zero):
        self.start=ph;self.active=active;self.k=(1-active)%3;self.rot=rot(self.k)
        xy,jac=rotate_xy(ph.xy,self.k);self.a,self.y0=xy;self.w0=1/self.y0**2
        q=qstar();self.W=(q-self.a)**2*self.w0;self.c=self.W/(q-self.a)
        self.exit_ratio=(1+self.W)/(2*q*self.c)
        if self.exit_ratio<=1:raise ValueError('not strict star')
        la=-mp.mpf(2)/3*self.rot.T*ph.lam*self.rot
        p=-mp.mpf(2)/3*(jac.T**-1)*ph.p
        K=mat(1,self.a,0,1);M=(K**-1)*la*K
        self.m=M[0,1];self.n=M[1,0];self.kappa=2*M[0,0];self.mu=-1-self.m
        self.pw0=-p[1]*self.y0**3/2
        px=p[0]-la[1,0]
        hz=1+(self.a**2-self.mu)*self.w0+px+2*self.w0/(q-self.a)*self.pw0
        if abs(hz)>zero*100:raise ValueError('nonzero active Hamiltonian')
        self.B0=self.n-self.qfun(1)
        u=self.c;pw=self.pw0;W=self.W;mu=self.mu;x=self.a;w=self.w0
        dpdu=W*(mu-x*x)/u**2-2*pw/u
        dq=2*x*W/u**2*w+(x*x-mu)*2*u/W+(W+1)/W**2*(3*u*u*pw+u**3*dpdu)
        self.B1=-self.kappa-dq

    def edge_numerator(self,r):
        u=self.c*r;c=self.c;W=self.W;q=qstar()
        return c*c*self.pw0+W*(self.mu-q*q)*(u-c)+2*q*W*W*mp.log(r)+W**3*(1/u-1/c)
    def edge_derivative(self,r):
        x=qstar()-self.W/(self.c*r)
        return self.c*self.W*(self.mu-x*x)
    def bfun(self,r):
        S=self.c*(r-1)
        return self.B0+self.B1*S+mp.mpf(4)/3*S*S-2*qstar()*(self.W+1)*self.c*(r*mp.log(r)-r+1)
    def bprime(self,r):
        return self.B1+mp.mpf(8)/3*self.c*(r-1)-2*qstar()*(self.W+1)*mp.log(r)
    def qfun(self,r):
        u=self.c*r;x=qstar()-self.W/u;w=u*u/self.W
        return 1+(x*x-self.mu)*w+(self.W+1)*u*self.edge_numerator(r)/self.W**2
    def cost_increment(self,r):
        u=self.c*r;W=self.W;c=self.c
        return mp.mpf(3)/2*((1+W)*W*(1/c-1/u)+mp.mpf(4)/3*(u-c)-2*qstar()*W*mp.log(r))
    def frame_at(self,r):
        u=self.c*r;S=u-self.c;x=qstar()-self.W/u
        grot=mat(1,self.a,0,1)*mat(1,0,S,1)*mat(1,-x,0,1)
        return self.start.g*self.rot*grot*self.rot.T
    def at(self,r):
        u=self.c*r;S=u-self.c;W=self.W;q=qstar();x=q-W/u;y=mp.sqrt(W)/u;w=u*u/W
        pw=self.edge_numerator(r)/(u*u)
        px=-1-(x*x-self.mu)*w-2*w/(q-x)*pw
        k=self.kappa+2*self.m*S
        M=mat(k/2,self.m,self.n-self.kappa*S-self.m*S*S,-k/2)
        K=mat(1,x,0,1);la=K*M*(K**-1)
        pr=-mp.mpf(3)/2*mp.matrix([px+la[1,0],-2*pw/y**3]);lar=-mp.mpf(3)/2*la
        xy,back=rotate_xy([x,y],-self.k);p=(back.T**-1)*pr
        return Phase(self.frame_at(r),xy,self.rot*lar*self.rot.T,p,
                     self.start.cost+self.cost_increment(r),self.start.time+mp.sqrt(W)*mp.log(r))

@dataclass
class Settings:
    zero: object
    root: object
    returned: object
    max_arcs: int=64

def settings():
    return Settings(mp.power(10,-mp.mp.dps//2),mp.power(10,-mp.mp.dps+12),mp.power(10,-mp.mp.dps//2+3))

def root(f,a,b,cfg):
    a,b=mp.mpf(a),mp.mpf(b);fa,fb=f(a),f(b)
    if fa==0:return a
    if fb==0:return b
    if fa*fb>=0:raise ValueError('unbracketed root')
    for _ in range(4*mp.mp.dps+32):
        m=(a+b)/2;fm=f(m)
        if fm==0 or b-a<=cfg.root*max(1,abs(m)):return m
        if fa*fm<0:b,fb=m,fm
        else:a,fa=m,fm
    raise ValueError('bisection iteration limit')

def monotone_roots(f,nodes,cfg):
    vals=[f(r) for r in nodes];tol=cfg.zero*max(1,max(abs(v) for v in vals));roots=[];unknown=[]
    for j in range(1,len(nodes)-1):
        if abs(vals[j])<=tol:unknown.append(nodes[j])
    if abs(vals[0])<=tol:vals[0]=0
    if abs(vals[-1])<=tol:unknown.append(nodes[-1])
    for a,b,fa,fb in zip(nodes,nodes[1:],vals,vals[1:]):
        if fa*fb<0:roots.append(root(f,a,b,cfg))
    return roots,unknown

def first_switch(arc,cfg):
    Rr=arc.exit_ratio;e=lambda r:arc.edge_numerator(r)/arc.c**2
    ed=lambda r:arc.edge_derivative(r)/arc.c**2
    b=lambda r:arc.bfun(r)/arc.c**2;bd=lambda r:arc.bprime(r)/arc.c
    for name,f,df in (('EDGE',e,ed),('THIRD',b,bd)):
        if f(1)>cfg.zero*10:return mp.mpf(1),None,'INVALID_ACTIVE_'+name
        if abs(f(1))<=cfg.zero and df(1)>=-cfg.zero:return mp.mpf(1),None,'UNKNOWN_NONTRANSVERSE_'+name
    ec=[mp.mpf(1),Rr]
    if arc.mu>=0:
        for x in (-mp.sqrt(arc.mu),mp.sqrt(arc.mu)):
            if arc.a<x<qstar()-arc.W/(arc.c*Rr):ec.append((qstar()-arc.a)/(qstar()-x))
    er,eu=monotone_roots(e,sorted(ec),cfg)
    dc=sorted([mp.mpf(1),Rr]+([Rr/2] if Rr>2 else []));dr=[]
    for a,z in zip(dc,dc[1:]):
        if bd(a)*bd(z)<0:dr.append(root(bd,a,z,cfg))
    if Rr>2 and abs(bd(Rr/2))<=cfg.zero and abs(b(Rr/2))<=cfg.zero:
        return Rr/2,None,'UNKNOWN_MULTIPLE_THIRD_ROOT'
    br,bu=monotone_roots(b,sorted([mp.mpf(1),*dr,Rr]),cfg)
    events=[(r,(2-arc.k)%3,'SWITCH') for r in er if r>1+8*cfg.root]
    events += [(r,(0-arc.k)%3,'SWITCH') for r in br if r>1+8*cfg.root]
    events += [(r,None,'UNKNOWN_TANGENCY_OR_BOUNDARY') for r in eu+bu]
    events.append((Rr,None,'STAR_BOUNDARY_LIMIT'));events.sort(key=lambda z:z[0]);first=events[0]
    if len(events)>1 and abs(events[1][0]-first[0])<=100*cfg.root and first[2]=='SWITCH':
        return first[0],None,'UNKNOWN_SIMULTANEOUS_EVENTS'
    return first

def polar(g): return mp.mpc(g[0,0]+g[1,1],g[1,0]-g[0,1])
def residual(ph,initial):
    xy,jac=rotate_xy(initial.xy,1)
    return dict(frame=norm(ph.g-rot(1)),state=norm(ph.xy-xy),
                frame_costate=norm(ph.lam-rot(-1)*initial.lam*rot(1)),
                state_costate=norm(ph.p-(jac.T**-1)*initial.p))

def continue_phase(initial,active=0,budget=None,cfg=None):
    cfg=cfg or settings();budget=octagon_cost() if budget is None else budget
    if not 0<budget<=mp.pi:raise ValueError('primary-angle guard requires budget <= pi')
    if norm(initial.g-eye())>cfg.zero or abs(initial.cost)>cfg.zero:raise ValueError('rebase to g=I,cost=0')
    ph=initial;labels=[];events=[];drift=mp.mpf(0);hd=mp.mpf(0);star=None
    def result(status,extra=None):
        ans=dict(status=status,word=''.join(map(str,labels)),arcs=len(labels),cost=ph.cost,time=ph.time,
                 spatial_drift=drift,active_H_drift=hd,min_sampled_star_margin=star,events=events)
        if extra:ans.update(extra)
        return ans
    for _ in range(cfg.max_arcs):
        H=hamiltonians(ph)
        if max(H)>100*cfg.zero or abs(H[active])>100*cfg.zero:return result('UNKNOWN_HAMILTONIAN_DRIFT')
        if sum(abs(h-H[active])<=cfg.zero for h in H)==3:return result('UNKNOWN_TRIPLE_TIE')
        try:arc=VertexArc(ph,active,cfg.zero);rlimit,nxt,reason=first_switch(arc,cfg)
        except ValueError as exc:return result('UNKNOWN_ARC',dict(detail=str(exc)))
        if rlimit<=1+8*cfg.root:return result(reason)
        labels.append(active)
        if ph.cost+arc.cost_increment(rlimit)>budget+cfg.zero:
            rlimit=root(lambda r:ph.cost+arc.cost_increment(r)-budget,1,rlimit,cfg);reason='NUMERICAL_COST_BUDGET';nxt=None
        angular=lambda r:mp.im(mp.exp(-1j*mp.pi/3)*polar(arc.frame_at(r)))
        if angular(rlimit)>=-cfg.zero and angular(1)<-cfg.zero:
            if angular(rlimit)>cfg.zero:rlimit=root(angular,1,rlimit,cfg)
            reason='PRIMARY_RETURN_SECTION';nxt=None
        for j in range(5):
            r=1+(rlimit-1)*j/4
            if r>=arc.exit_ratio-cfg.root:continue
            t=arc.at(r);drift=max(drift,norm(t.g*t.lam*(t.g**-1)-initial.lam))
            hd=max(hd,abs(hamiltonians(t)[active]));m=min(margins(t.xy));star=m if star is None else min(star,m)
        ph=arc.at(rlimit)
        events.append(dict(active=active,reason=reason,r=rlimit,cost=ph.cost,exit_ratio=arc.exit_ratio))
        if reason=='PRIMARY_RETURN_SECTION':
            rs=residual(ph,initial);status='NUMERICAL_CLOSED_RETURN' if max(rs.values())<=cfg.returned else 'NUMERICAL_RETURN_MISMATCH'
            return result(status,dict(return_residual=rs))
        if reason!='SWITCH':return result(reason)
        active=nxt
    return result('UNKNOWN_ARC_LIMIT')

def safe_json(value):
    if isinstance(value,(mp.mpf,mp.mpc)) or hasattr(value,'_mpf_'):return mp.nstr(value,30)
    if isinstance(value,dict):return {k:safe_json(v) for k,v in value.items()}
    if isinstance(value,(list,tuple)):return [safe_json(v) for v in value]
    return value

def run():
    cases=[]
    for k in (1,2,3):
        ph,res=regular_phase(k)
        for budget in (octagon_cost(),mp.pi):
            out=continue_phase(ph,budget=budget);out.update(name=f'standard_N{3*k+1}',budget=budget,stationarity=res);cases.append(out)
    scale=mp.sqrt(mp.mpf(448)/803)
    ph,res=local_phase((0,2,1,2,1,0),[mp.mpf(5)/4]*6,[scale,2*scale,scale*193/112])
    out=continue_phase(ph);out.update(name='M1_exact_5_over_4',stationarity=res);cases.append(out)
    # Inspect the untruncated outgoing arc after the five original switches.
    active=0;end=ph
    for _ in range(5):
        arc=VertexArc(end,active,settings().zero);r,active,status=first_switch(arc,settings())
        if status!='SWITCH':raise RuntimeError('known M1 switch regression failed')
        end=arc.at(r)
    arc=VertexArc(end,active,settings().zero)
    cases.append(dict(name='M1_outgoing_escape',a=arc.a,W=arc.W,mu_minus_a2=arc.mu-arc.a**2,
                      pw=arc.pw0,B0=arc.B0,B1=arc.B1,exit_ratio=arc.exit_ratio,
                      next_event=first_switch(arc,settings())[2],B_exit=arc.bfun(arc.exit_ratio)))
    eta=mp.mpf(1)/10
    ph=Phase(eye(),mp.matrix([0,1]),mat(0,mp.mpf(3)/2,2*eta-mp.mpf(3)/2,0),mp.matrix([2*eta,0]))
    out=continue_phase(ph,active=1);out['name']='cubic_switch';cases.append(out)
    ph=Phase(eye(),mp.matrix([0,1]),-mp.mpf(3)/2*mat(0,-1,1,0)+mp.mpf(1)/10*mat(1,0,0,-1),mp.matrix([0,0]))
    out=continue_phase(ph);out['name']='triple_tie';cases.append(out)
    return dict(python=platform.python_version(),mpmath=mp.__version__,decimal_precision=mp.mp.dps,
                budget=octagon_cost(),settings=vars(settings()),cases=cases,
                limitation='All solver outcomes are numerical diagnostics, not interval or universal certificates.')

def main():
    parser=argparse.ArgumentParser(description=__doc__);parser.add_argument('--dps',type=int,default=60)
    parser.add_argument('--output',type=Path);args=parser.parse_args()
    if args.dps<30:parser.error('use at least 30 decimal digits')
    mp.mp.dps=args.dps;data=safe_json(run());text=json.dumps(data,indent=2,allow_nan=False)
    if args.output:args.output.write_text(text+'\n',encoding='utf-8')
    else:print(text)

if __name__=='__main__':main()
