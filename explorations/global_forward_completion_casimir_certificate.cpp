// Exact rational interval engine for the full forward Casimir certificate.
#include <algorithm>
#include <array>
#include <cmath>
#include <cstdio>
#include <cstdlib>
#include <vector>
#include <chrono>
#include <iostream>
#include <stdexcept>
#include <gmpxx.h>
using R=mpq_class;
R rmin(const R&a,const R&b){return a<b?a:b;}
R rmax(const R&a,const R&b){return a>b?a:b;}
using namespace std;
static const mpz_class DYADIC_DEN=mpz_class(1)<<80;
R rd(const R&x){mpz_class n=x.get_num()*DYADIC_DEN,q;mpz_fdiv_q(q.get_mpz_t(),n.get_mpz_t(),x.get_den().get_mpz_t());R r(q,DYADIC_DEN);r.canonicalize();return r;}
R ru(const R&x){mpz_class n=x.get_num()*DYADIC_DEN,q;mpz_cdiv_q(q.get_mpz_t(),n.get_mpz_t(),x.get_den().get_mpz_t());R r(q,DYADIC_DEN);r.canonicalize();return r;}
struct I { R l,h; I(long a=0):l(a),h(a){} I(const R&a):l(a),h(a){} I(R a,R b):l(a),h(b){} };
I operator+(I a,I b){return {rd(a.l+b.l),ru(a.h+b.h)};}
I operator-(I a,I b){return {rd(a.l-b.h),ru(a.h-b.l)};}
I operator-(I a){return {-a.h,-a.l};}
I operator*(I a,I b){R x[]={a.l*b.l,a.l*b.h,a.h*b.l,a.h*b.h};return {rd(*min_element(x,x+4)),ru(*max_element(x,x+4))};}
I operator/(I a,I b){if(b.l<=0&&b.h>=0)throw runtime_error("interval denominator contains zero");return a*I(rd(1/b.h),ru(1/b.l));}
I sq(I a){return {rd(a.l<=0&&a.h>=0?R(0):rmin(a.l*a.l,a.h*a.h)),ru(rmax(a.l*a.l,a.h*a.h))};}
I intersect(I a,I b){return {rmax(a.l,b.l),rmin(a.h,b.h)};}
struct Box {array<I,5>x;int depth=0;};
struct J {
 I v; array<I,5>d; array<array<I,5>,5>dd;
 J(long a=0):v(a){} J(const R&a):v(a){} J(I a):v(a){}
 static J var(I a,int n){J r(a);r.d[n]=1;return r;}
};
J operator+(const J&a,const J&b){J r(a.v+b.v);for(int i=0;i<5;++i){r.d[i]=a.d[i]+b.d[i];for(int j=0;j<5;++j)r.dd[i][j]=a.dd[i][j]+b.dd[i][j];}return r;}
J operator-(const J&a,const J&b){J r(a.v-b.v);for(int i=0;i<5;++i){r.d[i]=a.d[i]-b.d[i];for(int j=0;j<5;++j)r.dd[i][j]=a.dd[i][j]-b.dd[i][j];}return r;}
J operator*(const J&a,const J&b){J r(a.v*b.v);for(int i=0;i<5;++i){r.d[i]=a.d[i]*b.v+a.v*b.d[i];for(int j=0;j<5;++j)r.dd[i][j]=a.dd[i][j]*b.v+a.d[i]*b.d[j]+a.d[j]*b.d[i]+a.v*b.dd[i][j];}return r;}
J fun(const J&a,I val,I der,I der2){J r(val);for(int i=0;i<5;++i){r.d[i]=der*a.d[i];for(int j=0;j<5;++j)r.dd[i][j]=der2*a.d[i]*a.d[j]+der*a.dd[i][j];}return r;}
J inv(const J&a){return fun(a,1/a.v,-1/sq(a.v),2/(sq(a.v)*a.v));}
J operator/(const J&a,const J&b){return a*inv(b);}
J sq(const J&a){return fun(a,sq(a.v),2*a.v,2);}
// Positive series encloses the actual analytic f, including its cubic zero.
I f_at(const R&r){
 if(r<1)throw runtime_error("f argument below one");
 I t=(I(r)-1)/(I(r)+1),t2=sq(t),pow=t*t2,sum=0;
 for(int n=1;n<=14;++n){sum=sum+I(R(4*n)/R(2*n+1))*pow;pow=pow*t2;}
 I tail=2*pow/(1-t2);
 return I(sum.l,ru(sum.h+tail.h));
}
J ffun(const J&r){
 I lo=f_at(r.v.l),hi=f_at(r.v.h);
 return fun(r,I(lo.l,hi.h),sq(r.v-1)/(2*sq(r.v)),(r.v-1)/(sq(r.v)*r.v));
}
// This fixed rational truncation is <= F_{r}(h)-3/4, not an approximate equality.
J floordelta(const J&r,const J&h){
 J t=(h-1)/(h+1),t2=sq(t),pow=t2,p=0;
 for(int n=1;n<=10;++n){p=p+J(R(4*n)/R(2*n+1))*pow;pow=pow*t2;}
 return sq(r-J(R(1)/2))+(h-1)*r*(r-J(R(1)/2))+r*h*p/(h+1);
}
array<J,7> jets(const Box&b,bool mid){
 array<J,5>x;for(int i=0;i<5;++i)x[i]=J::var(mid?I((b.x[i].l+b.x[i].h)/2):b.x[i],i);
 J U=x[0],z=x[1],w=x[2],h=x[3],k=x[4];
 J S=1+z,T=1+w,K=1+U,Z=sq(z)+U,W=sq(w)+U;
 J d=3-U,X=z-1,Y=w-1,H=h-1,L=k-1;
 J qgap=(d+2*X+2*Y+X*Y)/K,q=1+qgap;
 J nL=sq(S)*(U-z)*H/Z,nR=sq(T)*(U-w)*L/W;
 J mL=sq(K)*(qgap+H*(1+X+S*qgap))/(S*Z);
 J mR=sq(K)*(qgap+L*(1+Y+T*qgap))/(T*W);
 J phi=ffun(S/2)+ffun(T/2)+ffun(4/K);
 J e0=J(R(3)/4)+d*(K+2)/(8*K),E0=e0-phi;
 auto resid=[&](const J&v,const J&t,const J&A,const J&B,const J&factor){
  J p=sq(d)*(sq(v)+4*v+2)+8*d*v*(v+1)+2*sq(v)*(8+4*v-sq(v));
  return (d*v*(d+2*v)+factor*p)/(8*A*B)
   +sq(factor)*t*(d+4*v+sq(v))/(2*(1+factor)*B)
   +K*(1+A*factor)/B*phi-t*ffun(1+factor);
 };
 J rL=resid(X,z,S,Z,H),rR=resid(Y,w,T,W,L);
 J dl=floordelta(z/S,h),dr=floordelta(w/T,k);
 J D=sq(K)*sq(K)*qgap/(S*T*Z*W)
  *(qgap+H*(1+X+S*qgap)+L*(1+Y+T*qgap)
    +H*L*(q+1)*(q*(S+T)-sq(q)-1));
 if(D.v.l<=0)throw runtime_error("positive determinant not yet enclosed");
 J du=(mL*rR-nR*rL)/D,dv=(mR*rL-nL*rR)/D;
 J ell=S*du+T*dv,E=E0+ell;
 J cx=J(R(-3)/2)*X-d*S*(K+2)/(4*K);
 J cy=J(R(-3)/2)*Y-d*T*(K+2)/(4*K);
 J excess=J(R(7)/2000)+(J(R(-1)/64)*sq(sq(d))
  +sq(K)*(2*e0*phi-sq(phi)+cx*du+cy*dv+2*phi*ell+4*du*dv-sq(ell)))
  /(16*sq(U));
 return {rL-nL*dl-mL*dr,rR-mR*dl-nR*dr,du-dl,dv-dr,E,excess,D};
}
I taylor(const J&at,const J&all,const Box&b){
 R lo=at.v.l,hi=at.v.h;
 for(int i=0;i<5;++i){
  R ri=(b.x[i].h-b.x[i].l)/2;I linear=at.d[i]*I(-ri,ri);lo+=linear.l;hi+=linear.h;
  for(int j=0;j<5;++j){R rj=(b.x[j].h-b.x[j].l)/2;
   I term=all.dd[i][j]*I(i==j?R(0):R(-ri*rj),ri*rj)*I(R(1)/2);
   lo+=term.l;hi+=term.h;
  }
 }
 return intersect(I(lo,hi),all.v);
}
// Every contraction uses a necessary condition and exact rational endpoints.
bool contract(Box&b){
 auto &U=b.x[0],&z=b.x[1],&w=b.x[2],&h=b.x[3],&k=b.x[4];
 for(int it=0;it<3;++it){
  U.l=rmax(U.l,1+3*(z.l+w.l)/5);
  z.h=rmin(z.h,rmin(w.h,5*(U.h-1)/3-w.l));
  w.h=rmin(w.h,5*(U.h-1)/3-z.l);w.l=rmax(w.l,z.l);
  if(U.l>U.h||z.l>z.h||w.l>w.h)return false;
  h.l=rmax(h.l,(1+z.l)*(1+z.l)/(z.l*z.l+U.h));h.h=rmin(h.h,1+1/z.l);
  k.l=rmax(k.l,(1+w.l)*(1+w.l)/(w.l*w.l+U.h));k.h=rmin(k.h,1+1/w.l);
  if(h.l>h.h||k.l>k.h)return false;
 }
 return true;
}
// 1=empty; 10+i=necessary quantity negative; 20=Casimir cap contradicted.
int judge(Box&b){
 if(!contract(b))return 1;
 auto all=jets(b,false);
 for(int i=0;i<5;++i)if(all[i].v.h<0)return 10+i;
 if(all[5].v.l>0)return 20;
 auto mid=jets(b,true);
 for(int i=0;i<5;++i)if(taylor(mid[i],all[i],b).h<0)return 10+i;
 if(taylor(mid[5],all[5],b).l>0)return 20;
 return 0;
}
int main(int argc,char**argv){
 long long limit=argc>1?atoll(argv[1]):200000;
 vector<Box>stack;Box b;
 // The omitted central cube lies in s<=3/32<3/20 and is excluded by hand.
 b.x={I(R(11)/5,R(95)/32),I(1,R(5)/4),I(1,R(5)/4),I(1,2),I(1,2)};
 stack.push_back(b);
 b.x[0]=I(R(95)/32,3);b.x[1]=I(R(33)/32,R(5)/4);stack.insert(stack.begin(),b);
 b.x[1]=I(1,R(33)/32);b.x[2]=I(R(33)/32,R(5)/4);stack.insert(stack.begin(),b);
 long long count=0,leaves[21]={},unknown=0;int maxdepth=0;
 auto start=chrono::steady_clock::now();
 while(!stack.empty()&&count<limit){
  Box cell=stack.back();stack.pop_back();++count;maxdepth=max(maxdepth,cell.depth);
  int reason=0;try{reason=judge(cell);}catch(const runtime_error&){}
  if(reason){++leaves[reason];continue;}
  if(cell.depth>=70){++unknown;continue;}
  int axis=0;R width=-1;R scale[]={R(4)/5,R(1)/4,R(1)/4,1,1};
  for(int i=0;i<5;++i){R wi=(cell.x[i].h-cell.x[i].l)/scale[i];if(wi>width){width=wi;axis=i;}}
  R center=(cell.x[axis].l+cell.x[axis].h)/2;
  Box other=cell;other.x[axis].l=center;cell.x[axis].h=center;++cell.depth;++other.depth;
  stack.push_back(other);stack.push_back(cell);
  if(count%500==0){printf("nodes %lld stack %zu depth %d seconds %.1f\n",count,stack.size(),maxdepth,chrono::duration<double>(chrono::steady_clock::now()-start).count());fflush(stdout);}
 }
 printf("FINAL nodes %lld stack %zu max_depth %d unknown %lld seconds %.2f\n",count,stack.size(),maxdepth,unknown,chrono::duration<double>(chrono::steady_clock::now()-start).count());
 for(int i=0;i<=20;++i)if(leaves[i])printf("reason %d leaves %lld\n",i,leaves[i]);
 if(!stack.empty()||unknown){cout<<"INCOMPLETE: not an F proof.\n";return 1;}
 cout<<"PASS: exact complementary-domain certificate; combine with the stated hand lemmas.\n";
}
