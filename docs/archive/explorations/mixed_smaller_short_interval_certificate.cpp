// Directed MPFR port of the M2 smaller-short scalar-cover prototype.
// This certifies the displayed scalar cover only. Its PMP-domain reduction
// must be supplied and independently reviewed separately.
#include "certified_mpfr_interval.hpp"
#include <algorithm>
#include <array>
#include <cmath>
#include <cstdio>
#include <cstdlib>
#include <vector>
#include <chrono>
#include <iostream>
#include <stdexcept>
using namespace std;
using certified::I; using certified::R; using J=certified::Jet<6>;
using certified::intersect; using certified::sq; using certified::rt;
using certified::atanfun; using certified::logdiv;
I q(intmax_t n,uintmax_t d=1){return I::rational(n,d);}
const I root_three=certified::rt(I(3));
struct Box{array<I,6>x;int depth=0;};
J sec(const J&A,const J&B,const J&P){J h=(P+B)/(A+B),xi=B/(A+B);return 1+sq(xi)/h-xi*logdiv(h);}
using Mat=array<array<J,2>,2>;
Mat mul(const Mat&A,const Mat&B){Mat C;for(int i=0;i<2;++i)for(int j=0;j<2;++j)C[i][j]=A[i][0]*B[0][j]+A[i][1]*B[1][j];return C;}
vector<J> jets(const Box&b,bool mid){
 array<J,6>v0;for(int i=0;i<6;++i)v0[i]=J::var(mid?I(certified::midpoint(b.x[i])):b.x[i],i);
 J r=v0[0],delta=v0[1],al=v0[2],rho=v0[3],v=v0[4],E=v0[5];
 J x=1/r-1,be=(1+delta)*x,S=1+x,A=al+be,B=be+x;
 J xi=1-r,h=xi*(2+delta),u=1+xi/(2+delta)-xi*logdiv(h);
 J ax=al*r/(1-r),ha=(2+delta)/(1+delta+ax),xa=(1+delta)/(1+delta+ax);
 J ua=1+sq(xa)/ha-xa*logdiv(ha);
 u.v=intersect(u.v,I(q(3,4).l,R(1)));ua.v=intersect(ua.v,I(q(3,4).l,R(1)));
 J Elo=(u-1)/r+(v-1)*r/rho+1+r+rho/r-rho;
 J Eupperpoly=r*(u+v-2)+2*r*sq(r)-rho*sq(r)+rho-sq(r)*E;
 J gam=(4*u*v-sq(E))/(16*sq(1-rho));
 J D=sq(al)+2*al*be+1+2*x-2*be*x,lambda=1/(1+rho*(sq(al)-1)),ed=rho*D;
 J w=sq(lambda)*(v-ed*E+sq(ed)*u),EL=lambda*(2*ed*u-E);
 J rhoA=sq(al)*lambda*rho,ti=lambda*rho*al*A,TB=A/al;
 J zeta=(1-2*ti)/(1+2*ti),m0=2*(1+zeta)+q(2,3)*zeta*sq(1+zeta);
 J Rbar=m0*(w-q(3,4))+(u-1)*TB+1+1/TB-rhoA-EL-2*zeta-q(2,3)*zeta*sq(zeta);
 J gap1=(1-rho-v)*sq(r)+rho*(E-1+rho)*r+rho*(1-rho-u);
 
 J pmid=sq(be)*rho*sq(x)-sq(be)*rho+sq(be)-4*be*rho*sq(x)-4*be*rho*x+2*be*x+3*rho*sq(x)+4*rho*x+rho+sq(x);
 J fmid=(1-rho)*(sq(be)*rho+be*rho*x+rho*sq(x)-rho+1)-v-rho*E*(be*x-2*x-1)-rho*u*pmid;
 J ra=al/A,fouter=(1-rhoA-w)*sq(ra)+rhoA*(EL-1+rhoA)*ra+rhoA*(1-rhoA-u);
 vector<J> out={u-ua,1-r+sq(r)-u,sq(r)*(1-v)-rho*r+sq(rho),sq(A)*(1-u)-al*be,
  gam-q(27,256),q(23,125)-gam,w-q(3,4),1-ti+sq(ti)-w,Rbar,
  q(3,20)-rhoA,3*rhoA-EL,gap1,Eupperpoly,3*rho-E,fmid,fouter,
   sq(r)-rho,x-al,al-1-delta*(1+2*x/7),1-rho*(sq(al)+2*al*be+1),
   1-rho*(1+be*x),(u-1)*sq(2+delta)+(1+delta),q(13,16)-u};
 if(gam.v.l<=0)return out;
 J kap=rt(12*gam),U=(1-rho)/rho,N=(U-x)/S,Z=(U-al*be)/A;
 Mat P={{{0-N-2,x+2},{N,x}}},Qinv={{{0-al/(2*U),(al+2*be)/(2*U)},{Z/(2*U),(Z+2*be)/(2*U)}}},FF={{{S/A,0},{(sq(S)-sq(B))/(S*A),A/S}}};
 Mat mm=mul(mul(P,FF),Qinv);
 J h11=E*(r-rho*S)-u*(1-sq(rho*S))+v*(1-sq(r));
 J h12=u*sq(1+rho*S)+v*sq(1+r)-E*(1+r)*(1+rho*S);
 J h21=0-u*sq(1-rho*S)-v*sq(1-r)-E*(1-r)*(1-rho*S);
 J Tk=2*kap*sq(1-rho);
 J AA=Tk*(mm[0][0]+mm[1][1])+h12*mm[1][1]-h11*(mm[0][1]+3*mm[1][0])-3*h21*mm[0][0];
 J BB=h11*(mm[1][1]-mm[0][0])+h12*mm[1][0]+h21*mm[0][1]+Tk/3*(3*mm[1][0]-mm[0][1]);
 out.push_back(AA-2*Tk);out.push_back(BB);out.push_back(AA-BB);
 out.push_back(AA+BB-4*Tk); // Actual angle/modulus filter, independently audited.
 J AB=AA+BB; if(AB.v.l<=0)return out;
 J cost=root_three*(rho*u/(1-rho)*(2*be*x-x-al*be)+(be*x-al)/(S*A));
 // theta = pi/6 + atan((3*BB-AA)/(sqrt(3)*(AA+BB))) on the actual angle branch.
 J theta_centered=atanfun((3*BB-AA)/(root_three*AB));
 J excess=cost+(kap+q(3,2))*(q(6283,12000)-theta_centered)-q(2501,800);
 out.push_back(0-excess);
 return out;
}

I taylor(const J&at,const J&all,const Box&b){
 return certified::taylor(at,all,b.x,certified::centers(b.x));
}
bool contract(Box&b){
 auto&r=b.x[0];auto&de=b.x[1];auto&al=b.x[2];auto&rho=b.x[3];auto&v=b.x[4];auto&E=b.x[5];
 for(int it=0;it<4;++it){
  rho.h=min(rho.h,sq(I(r.h)).h);
  r.l=max(r.l,rt(I(rho.l)).l);
  al.h=min(al.h,min((1/I(r.l)-1).h,rt(3*(1-I(rho.l))/(17*I(rho.l))).h));
  r.h=min(r.h,(1/(1+I(al.l))).h);
  R xl=(1/I(r.h)-1).l;
  al.l=max(al.l,(1+I(de.l)*(1+2*I(xl)/7)).l);
  de.h=min(de.h,((I(al.h)-1)/(1+2*I(xl)/7)).h);
  rho.h=min(rho.h,min((1/(sq(I(al.l))+2*I(al.l)*(1+I(de.l))*I(xl)+1)).h,
                       (1/(1+(1+I(de.l))*sq(I(xl)))).h));
  R tl=(I(rho.l)/I(r.h)).l;
  v.h=min(v.h,(1-I(tl)+sq(I(tl))).h);
  E.h=min(E.h,(3*I(rho.h)).h);
  for(const I&xx:b.x)if(xx.empty())return false;
 }
 return true;
}
struct LP {
 int m,n;vector<int>B,N;vector<vector<double>>D,T;
 LP(const vector<vector<double>>&A,const vector<double>&b):m(b.size()),n(A[0].size()),B(m),N(n+1),D(m+2,vector<double>(n+2)),T(m+2,vector<double>(m)){
  for(int i=0;i<m;++i){for(int j=0;j<n;++j)D[i][j]=A[i][j];B[i]=n+i;D[i][n]=-1;D[i][n+1]=b[i];T[i][i]=1;}
  for(int j=0;j<n;++j)N[j]=j;N[n]=-1;D[m+1][n]=1;
 }
 void pivot(int r,int s){double iv=1/D[r][s];for(int i=0;i<m+2;++i)if(i!=r)for(int j=0;j<m;++j)T[i][j]-=T[r][j]*D[i][s]*iv;for(double&v:T[r])v*=iv;for(int i=0;i<m+2;++i)if(i!=r)for(int j=0;j<n+2;++j)if(j!=s)D[i][j]-=D[r][j]*D[i][s]*iv;for(int j=0;j<n+2;++j)if(j!=s)D[r][j]*=iv;for(int i=0;i<m+2;++i)if(i!=r)D[i][s]*=-iv;D[r][s]=iv;swap(B[r],N[s]);}
 bool phase(){for(int it=0;it<200;++it){int s=-1;for(int j=0;j<=n;++j)if(s==-1||D[m+1][j]<D[m+1][s]-1e-12||(abs(D[m+1][j]-D[m+1][s])<1e-12&&N[j]<N[s]))s=j;if(D[m+1][s]>=-1e-12)return true;int r=-1;for(int i=0;i<m;++i)if(D[i][s]>1e-12){if(r==-1||D[i][n+1]/D[i][s]<D[r][n+1]/D[r][s]-1e-12||(abs(D[i][n+1]/D[i][s]-D[r][n+1]/D[r][s])<1e-12&&B[i]<B[r]))r=i;}if(r==-1)return false;pivot(r,s);}return false;}
 bool infeasible(){int r=0;for(int i=1;i<m;++i)if(D[i][n+1]<D[r][n+1])r=i;if(D[r][n+1]>=-1e-12)return false;pivot(r,n);if(!phase())return false;return D[m+1][n+1]<-1e-9;}
};

// Native floating-point LP data are proposal heuristics only. The sole
// rejection is a newly evaluated directed interval Taylor upper bound for
// an exact nonnegative dyadic combination of the original constraints.
bool linreject(const vector<J>&mid,const vector<J>&all,const Box&b){
 vector<vector<double>>A;vector<double>rhs,scales;vector<int>ids;
 array<double,6>ri;
 for(int j=0;j<6;++j)ri[j]=(b.x[j].h.get_d()-b.x[j].l.get_d())/2;
 for(int o=0;o<(int)min(all.size(),mid.size());++o){
  const J&at=mid[o];const J&box=all[o];double upper=at.v.h.get_d();
  vector<double>row(6);
  for(int i=0;i<6;++i){
   double gl=at.d[i].l.get_d(),gh=at.d[i].h.get_d(),g=(gl+gh)/2;
   row[i]=-2*ri[i]*g;upper-=g*ri[i];upper+=(gh-gl)*ri[i]/2;
   for(int j=0;j<6;++j){
    double hl=box.dd[i][j].l.get_d(),hh=box.dd[i][j].h.get_d();
    double dxhi=ri[i]*ri[j],dxlo=i==j?0:-dxhi;
    upper+=.5*max(max(hl*dxlo,hl*dxhi),max(hh*dxlo,hh*dxhi));
   }
  }
  double scale=abs(upper);for(double val:row)scale=max(scale,abs(val));
  if(!isfinite(scale)||scale>1e100||scale<1e-30)continue;
  for(double&val:row)val/=scale;
  upper/=scale;A.push_back(row);rhs.push_back(upper);scales.push_back(scale);ids.push_back(o);
 }
 int active=A.size();if(!active)return false;
 for(int j=0;j<6;++j){vector<double>row(6);row[j]=1;A.push_back(row);rhs.push_back(1);}
 LP lp(A,rhs);if(!lp.infeasible())return false;
 double mx=0;for(int i=0;i<active;++i)mx=max(mx,lp.T[lp.m+1][i]/scales[i]);
 if(!isfinite(mx)||mx<=0)return false;
 J cm=0,ca=0;
 for(int i=0;i<active;++i){
  double proposed=lp.T[lp.m+1][i]/scales[i]/mx;
  if(!isfinite(proposed))return false;
  proposed=max(0.,proposed);
  double num=floor(proposed*1048576.+.5);
  if(!isfinite(num)||num<0||num>1048576.)return false;
  uintmax_t n=static_cast<uintmax_t>(num);
  if(n){J wt(q(static_cast<intmax_t>(n),1048576));cm=cm+wt*mid[ids[i]];ca=ca+wt*all[ids[i]];}
 }
 return taylor(cm,ca,b).h<0;
}
int judge(Box&b){
 if(!contract(b))return 1;
 auto all=jets(b,false);
 for(int i=0;i<(int)all.size();++i)if(all[i].v.h<0)return 10+i;
 auto mid=jets(b,true);
 for(int i=0;i<(int)min(all.size(),mid.size());++i)if(taylor(mid[i],all[i],b).h<0)return 10+i;
 if(linreject(mid,all,b))return 39;
 return 0;
}

int main(int argc,char**argv){
 try{
  certified::check_environment();
  long long limit=argc>1?atoll(argv[1]):2000000;
  if(limit<=0)throw runtime_error("node budget must be positive");
  vector<Box>stack;Box b;
  b.x={I(q(1,10).l,q(1,2).h),I(0,2),I(R(1),q(631,100).h),
       I(q(1,226).l,q(3,20).h),I(q(3,4).l,R(1)),I(q(-23,16).l,q(9,20).h)};
  stack.push_back(b);
  long long count=0,leaves[40]={},unknown=0,domain_splits=0;int md=0;
  auto st=chrono::steady_clock::now();
  cout<<"MPFR "<<mpfr_get_version()<<" precision "<<certified::precision<<" bits; directed bounds\n";
  while(!stack.empty()&&count<limit){
   Box cell=stack.back();stack.pop_back();++count;md=max(md,cell.depth);int reason=0;
   try{reason=judge(cell);}catch(const domain_error&){++domain_splits;}
   if(reason){++leaves[reason];}
   else if(cell.depth>=70){
    ++unknown;
    if(unknown<6){cout<<"UNKNOWN ";for(const I&xx:cell.x)cout<<"["<<xx.l.str()<<","<<xx.h.str()<<"] ";cout<<"\n";}
   }else{
    int ax=0;double ww=-1,sc[]={.4,2,5.31,.15,.25,1.9};
    for(int i=0;i<6;++i){double wi=certified::width_up(cell.x[i]).get_d(MPFR_RNDU)/sc[i];if(wi>ww){ww=wi;ax=i;}}
    R ce=certified::midpoint(cell.x[ax]);
    if(ce<=cell.x[ax].l||ce>=cell.x[ax].h){++unknown;}
    else{
     Box other=cell;other.x[ax].l=ce;cell.x[ax].h=ce;++cell.depth;++other.depth;
     stack.push_back(other);stack.push_back(cell);
    }
   }
   if(count%1000==0){
    printf("nodes %lld stack %zu depth %d unknown %lld LP %lld sec %.2f\n",count,stack.size(),md,unknown,leaves[39],chrono::duration<double>(chrono::steady_clock::now()-st).count());fflush(stdout);
   }
  }
  certified::check_flags();
  printf("FINAL nodes %lld stack %zu depth %d unknown %lld domain_splits %lld sec %.2f\n",count,stack.size(),md,unknown,domain_splits,chrono::duration<double>(chrono::steady_clock::now()-st).count());
  for(int i=0;i<40;++i)if(leaves[i])printf("reason%d leaves%lld\n",i,leaves[i]);
  if(!stack.empty()||unknown){cout<<"INCOMPLETE: no certificate claimed.\n";return 1;}
  cout<<"PASS: the full initial scalar box is excluded by directed interval bounds.\n";
 }catch(const exception&e){cerr<<"FAIL: "<<e.what()<<"\n";return 2;}
}
