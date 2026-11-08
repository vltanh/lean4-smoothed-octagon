// PENDING reverse-next boundary comparison certificate; independently audit before use.
// Inputs satisfy z0=0, with only retained boundary inequalities.
#include "certified_mpfr_interval.hpp"
#include "certified_lp_proposal.hpp"
#include <array>
#include <vector>
#include <chrono>
#include <iostream>
#include <cstdlib>
#include <fstream>
using namespace certified;
using J=Jet<5>;

template<class T>T powi(T a,unsigned n){T r=1;while(n){if(n&1)r=r*a;n>>=1;if(n)a=a*a;}return r;}
#include "mixed_nonshort_coefficients.hpp"

// H and its first two derivatives, with rigorous endpoint enclosures.
std::array<I,3> Hpoint(const R& x){
 if(x<0)throw std::domain_error("negative H point");
 I z(x);std::array<I,3> o;
 if(x<=I::rational(1,8).l){
  I eta=z/(1+z);
  for(unsigned k=0;k<3;++k){
   I sum=0,power=1;
   for(unsigned n=0;n<25;++n){sum=sum+power/I((n+k+1)*(n+k+2)*(n+k+3));power=power*eta;}
   I tail=power/(I((26+k)*(27+k)*(28+k))*(1-eta));
   unsigned fac=k==0?2:k==1?6:24;
   I value=I(fac)*(sum+I(R(0),tail.h))/powi(1+z,k+1);
   o[k]=(k==1)?-value:value;
  }
 }else{
  I N=lg(1+z)-z+sq(z)/2;
  o[0]=N/powi(z,3);
  o[1]=1/(z*(1+z))-3*N/powi(z,4);
  o[2]=-(4+5*z)/(sq(z)*sq(1+z))+12*N/powi(z,5);
 }
 return o;
}
std::array<I,3> Hbounds(const I& a){
 a.valid();if(a.l<0)throw std::domain_error("negative H interval");
 auto low=Hpoint(a.l),high=Hpoint(a.h);
 return {I(high[0].l,low[0].h),I(low[1].l,high[1].h),I(high[2].l,low[2].h)};
}
I Hfun(const I&a){return Hbounds(a)[0];}
J Hfun(const J&a){auto x=Hbounds(a.v);return fun(a,x[0],x[1],x[2]);}

// A formal polynomial in epsilon.  Its coefficients are interval jets in
// the four shape/weight variables; the formal degree never exceeds eight.
template<class T>struct Poly{
 std::array<T,9> c{};std::array<bool,9> present{};
 Poly()=default;Poly(long n){c[0]=T(n);present[0]=(n!=0);}
 Poly(const T&x){c[0]=x;present[0]=true;}
 Poly(const T&a,const T&b){c[0]=a;c[1]=b;present[0]=present[1]=true;}
 friend Poly operator+(const Poly&a,const Poly&b){Poly r;for(int i=0;i<9;++i){r.c[i]=a.c[i]+b.c[i];r.present[i]=a.present[i]||b.present[i];}return r;}
 friend Poly operator-(const Poly&a,const Poly&b){Poly r;for(int i=0;i<9;++i){r.c[i]=a.c[i]-b.c[i];r.present[i]=a.present[i]||b.present[i];}return r;}
 friend Poly operator-(const Poly&a){return Poly(0)-a;}
 friend Poly operator*(const Poly&a,const Poly&b){Poly r;for(int i=0;i<9;++i)if(a.present[i])for(int j=0;j<9;++j)if(b.present[j]){
   if(i+j>=9)throw std::runtime_error("formal polynomial overflow");
   r.c[i+j]=r.c[i+j]+a.c[i]*b.c[j];r.present[i+j]=true;
  }return r;}
};

template<class T>T centered_polynomial(const T&a,const T&c,const T&eps,const T&l0,const T&l1,const T&l2){
 using P=Poly<T>;T K=sq(a)+4,T0=a+c;
 P ap(a),cp(c),kp(K),tp(T0),z0(T(0),l0),z1(T(0),l1),z2(T(0),l2);
 P d=ap+tp*z1,W=tp*(1+z1),Q=d*d+4,Y=W*W-tp*tp,q=1+z2;
 P N=d*W-q*Y;
 P KU=kp*kp-ap*kp*tp*(1+z0)+ap*ap*tp*tp*(1+z0)*(1+z0);
 P vn=ap*W+cp*cp+P(c/2)*z1*W;
 P Vn=-ap*Q*W*W-ap*q*Y*Y+2*ap*d*W*Y+kp*tp*N;
 P Bn=-kp*tp*tp+2*ap*ap*tp*tp*(1+z0)+kp*ap*ap-ap*ap*ap*tp;
 P Cn=Q*Q*q*q-d*d*Q*q+d*d*W*W*(q-1)+4*cp*W*q;
 P num=2*ap*tp*W*Cn+2*q*Vn*vn-2*ap*tp*W*q*q*KU+2*W*q*N*Bn
       -ap*tp*W*q*kp*N*(2*z0-z0*z0)-ap*tp*W*q*d*Q*W*(2*z2-z2*z2);
 // Coefficients zero and one vanish identically; the exact checker proves
 // this before any interval evaluation or division by epsilon occurs.
 T value=0;for(int i=8;i>=3;--i)value=value*eps+num.c[i];
 T c2=powi(T0,3)*(4-sq(a)-2*a*c)*sq(a*(l0+l2)+c*l1);
 return value*eps+c2;
}

template<class T>struct Values{std::vector<T> needed;T gamma_excess,phi,u,v,h,w,nextnorm,a,b,c,d,r,epsilon;};
template<class T>Values<T> evaluate(const std::array<T,5>& x,int chart,int branch){
 T a=x[0],c=x[1],eps=x[2],l0,l1,l2;
 if(chart==0){l0=1;l1=x[3];l2=x[4];}
 else if(chart==1){l0=x[3];l1=1;l2=x[4];}
 else {l0=x[3];l1=x[4];l2=1;}
 T z0=eps*l0,z1=eps*l1,z2=eps*l2,K=sq(a)+4,T0=a+c;
 T S=K/(T0*(1+z0)),b=S-a,d=a+T0*z1,W=T0*(1+z1),Q=sq(d)+4;
 T q=1+z2,Z=Q*q/W,r=Z-d,Y=sq(W)-sq(T0),N=d*W-q*Y;
 T H0=Hfun(z0),H1=Hfun(z1),H2=Hfun(z2);
 T Bv=c*(4-sq(a))+8*a+a*z1*(sq(c)+4)+z2*T0*(z1+2)*(K+a*T0*z1*(z1+2));
 T base=centered_polynomial_cancelled(a,c,eps,l0,l1,l2)/(2*a*Q*sq(1+z1)*q);
 T phi=base-eps*K*N*powi(l0,3)*H0/(Q*W)+eps*c*T0*powi(l1,3)*Bv*H1/(a*Q*W)-eps*d*powi(l2,3)*H2;
 T D1=sq(K)/(a*Q*W*(1+z0))*(a*(l0+l2)+c*l1+a*eps*l0*l2+T0*eps*l1*l2*(2+eps*l1));
 T shift=eps*phi/D1;
 T rr=a*T0/K,tt=a/T0,rho=sq(a)/K,xc=c/T0;
 T u0=1-rr+sq(rr),v0=1-tt+sq(tt),h0=K*(-1+2*(rr+tt)-rho)/16;
 T du=(2*sq(rr)-rr)*z0+sq(rr)*sq(z0)+shift;
 T dv=z1*(xc/2-sq(xc))+sq(z1)*(sq(xc)/(1+z1)-xc*H1);
 T dh=K*(2*rr*z0-lg(1+z0)+dv/tt+(S/a)*shift)/16;
 T u=u0+du,v=v0+dv,h=h0+dh;
 T excess=T(I::rational(7,2000))+sq(K)*(v0*du+u0*dv+du*dv)/64-2*h0*dh-sq(dh);
 T hd=h+v*Y/8,w=(u*sq(K)+16*h*Y+v*sq(Y))/sq(Q),Kr=sq(r)+4;
 T hn=-hd+w*sq(Z)/8,tn=(sq(Q)*v-16*hd*sq(Z)+w*sq(sq(Z)))/sq(Kr);
 T L2=1-z2/2+sq(z2)*H2;
 T Fend=1+sq(d/W)*q-(d/W)*q*L2,Fstart=1+sq(d/Z)*q-(d/Z)*q*L2;
 T turn=(T(I::rational(1,2))-(1-xc+z1)/sq(1+z1)-z1*H1);
 T upper_turn=xc-T(I::rational(1,2))-z1*(xc/(1+z1)-H1);
 const T compact_min(I::rational(2,15)),half(I::rational(1,2));
 // Positive-factor forms of b>=c, c^2>=a*d and r>=a avoid
 // interval cancellation. The two inactive margins are >=2/15.
 std::vector<T> needed={c-a,K-sq(T0)*(1+z0),12-17*sq(a),
  4-c*d-compact_min*W,c-compact_min-(d+compact_min)*z2,
  4-sq(a)-2*a*c-sq(T0)*z1+Q*z2,c-a*(1+z1),
  -phi,upper_turn,turn,v-Fend,
  8-d,8-r,T0-half,W-half,Z-half};
 if(chart==2)needed.push_back(c-a-T0*z1);
 if(branch==0)needed.push_back(tn-T(I::rational(3,4)));
 else{
  T ar=a+r,zz=T0*z1/ar;
  T LL=1-zz/2+sq(zz)*Hfun(zz);
  T ceiling=1+sq(r)/(ar*Z)-r/ar*LL;
  needed.push_back(sq(r)-a*d);needed.push_back(ceiling-w);
 }
 return {needed,excess,phi,u,v,h,w,tn,a,b,c,d,r,eps};
}

struct Box{std::array<I,5>x;int chart=0,depth=0,branch=0;};
int weight_axis(int chart,int which){
 if(which==chart)return -1;
 if(chart==0)return which==1?3:4;
 if(chart==1)return which==0?3:4;
 return which==0?3:4;
}
I weight(const Box&b,int which){int ax=weight_axis(b.chart,which);return ax<0?I(1):b.x[ax];}
bool cap_product(Box&b,int which,const R&cap){
 if(cap<0)return false;auto &e=b.x[2];int ax=weight_axis(b.chart,which);
 if(ax<0)e.h=rmin(e.h,cap);
 else{
  auto&w=b.x[ax];if(w.l>0)e.h=rmin(e.h,div(cap,w.l,MPFR_RNDU));
  if(e.l>0)w.h=rmin(w.h,div(cap,e.l,MPFR_RNDU));
  if(w.empty())return false;
 }
 return !e.empty();
}
bool floor_product(Box&b,int which,const R&floor){
 if(floor<=0)return true;auto&e=b.x[2];int ax=weight_axis(b.chart,which);
 if(ax<0)e.l=rmax(e.l,floor);
 else{
  auto&w=b.x[ax];if(w.h<=0||e.h<=0)return false;
  e.l=rmax(e.l,div(floor,w.h,MPFR_RNDD));
  w.l=rmax(w.l,div(floor,e.h,MPFR_RNDD));
  if(w.empty())return false;
 }
 return !e.empty();
}
bool contract(Box&b){
 const I compact_min=I::rational(2,15),half=I::rational(1,2);
 for(int it=0;it<3;++it){
  auto &a=b.x[0],&c=b.x[1];
  a.h=rmin(a.h,rt(I::rational(12,17)).h);
  if(a.empty()||c.empty())return false;
  I z0=b.x[2]*weight(b,0),z1=b.x[2]*weight(b,1);
  I lo0(z0.l),lo1(z1.l);
  if(b.chart==2&&lo1.l>=1)return false;
  I bound=I(a.l)*(1+lo1);c.l=rmax(c.l,bound.l);
  if(b.chart==2){
   bound=I(a.l)*(1+lo1)/(1-lo1);c.l=rmax(c.l,bound.l);
   bound=I(c.h)*(1-lo1)/(1+lo1);a.h=rmin(a.h,bound.h);
  }
  bound=half-I(a.h);c.l=rmax(c.l,bound.l);
  bound=half-I(c.h);a.l=rmax(a.l,bound.l);
  if(a.empty()||c.empty()||a.l<=0||c.l<=0)return false;
  // For fixed delta0, sqrt((a^2+4)/(1+delta0))-a decreases in a.
  bound=rt((sq(I(a.l))+4)/(1+lo0))-I(a.l);c.h=rmin(c.h,bound.h);
  if(c.empty())return false;
  // Stable positive quadratic root from (a+c)^2(1+delta0)<=a^2+4.
  I cp(c.l),numerator=4-sq(cp)*(1+lo0);
  if(numerator.h<0)return false;
  bound=numerator/(cp*(1+lo0)+rt(sq(cp)*(1+lo0)+4*lo0));
  a.h=rmin(a.h,bound.h);
  bound=I(c.h)/(1+lo1);a.h=rmin(a.h,bound.h);
  bound=rt(4/(sq(2+lo1)*(1+lo0)-1));a.h=rmin(a.h,bound.h);
  // Inactive margin at c->d: 4-c*d-m(c+d)>=0.
  bound=(4-sq(cp)*lo1-compact_min*cp*(1+lo1))/((cp+compact_min)*(1+lo1));
  a.h=rmin(a.h,bound.h);
  if(lo1.l>0){bound=(8-I(a.l)*(1+lo1))/lo1;c.h=rmin(c.h,bound.h);}
  if(a.empty()||c.empty())return false;
  I aa(a.l),cc(c.l),T=aa+cc;
  I cap0=(sq(aa)+4)/sq(T)-1;
  if(!cap_product(b,0,cap0.h))return false;
  I cap1a=I(c.h)/aa-1;
  I cap1b=(4-aa*cc-compact_min*T)/(T*(cc+compact_min));
  I cap1c=(8-aa)/T;
  if(!cap_product(b,1,rmin(cap1a.h,rmin(cap1b.h,cap1c.h))))return false;
  // In max chart 2, the exact first-event gap implies d<=c.
  if(b.chart==2){
   I chart_cap=(I(c.h)-aa)/(aa+I(c.h));
   if(!cap_product(b,1,chart_cap.h))return false;
  }
  I delta1=b.x[2]*weight(b,1);
  I cap2=(I(c.h)-compact_min)/(aa+(aa+I(c.h))*I(delta1.l)+compact_min);
  if(!cap_product(b,2,cap2.h))return false;
  // Natural outward enclosures suffice for these lower/upper contractors;
  // no monotonicity of the full rational expressions is assumed.
  I fullT=a+c,fullK=sq(a)+4,fullD=a+fullT*(b.x[2]*weight(b,1));
  I fullW=c+fullD,fullQ=sq(fullD)+4;
  I lower2=(fullT*fullD+a*c-4)/fullQ;
  if(!floor_product(b,2,lower2.l))return false;
  I upper2=fullW*(fullD+8)/fullQ-1;
  if(!cap_product(b,2,upper2.h))return false;
 }
 return true;
}
bool basic_empty(const Box&b){
 I a=b.x[0],c=b.x[1],e=b.x[2],z0=e*weight(b,0),z1=e*weight(b,1),z2=e*weight(b,2);
 I K=sq(a)+4,T=a+c,S=K/(T*(1+z0)),bb=S-a,d=a+T*z1,W=T*(1+z1),Q=sq(d)+4,Z=Q*(1+z2)/W,r=Z-d;
 const I compact_min=I::rational(2,15),half=I::rational(1,2);
 std::array<I,13> cs={c-a,K-sq(T)*(1+z0),12-17*sq(a),
  4-c*d-compact_min*W,c-compact_min-(d+compact_min)*z2,
  4-sq(a)-2*a*c-sq(T)*z1+Q*z2,c-a*(1+z1),r,
  8-d,8-r,T-half,W-half,Z-half};
 for(auto v:cs)if(v.h<0)return true;
 if(b.chart==2&&(c-a-T*z1).h<0)return true;
 return false;
}
int judge(Box&b){
 if(!contract(b)||basic_empty(b))return 1;
 auto simple=evaluate(b.x,b.chart,b.branch);
 for(unsigned i=0;i<simple.needed.size();++i)if(simple.needed[i].h<0)return 10+i;
 auto all=evaluate(variables(b.x),b.chart,b.branch);
 auto mid=centers(b.x);auto at=evaluate(variables_at(mid),b.chart,b.branch);
 for(unsigned i=0;i<all.needed.size();++i)
  if(taylor(at.needed[i],all.needed[i],b.x,mid).h<0)return 10+i;
 if(linear_combination_reject(at.needed,all.needed,b.x))return 60;
 return 0;
}

void put_point(std::ostream&out,const R&r){
 mpz_t n;mpz_init(n);mpfr_exp_t ex=mpfr_get_z_2exp(n,r.ptr());
 char*text=mpz_get_str(nullptr,10,n);out<<text<<" "<<ex<<"\n";
 void(*freefun)(void*,size_t);mp_get_memory_functions(nullptr,nullptr,&freefun);freefun(text,std::strlen(text)+1);mpz_clear(n);
}
R get_point(std::istream&in){
 std::string text;mpfr_exp_t ex;in>>text>>ex;if(!in)throw std::runtime_error("invalid checkpoint point");
 mpz_t n;mpz_init(n);if(mpz_set_str(n,text.c_str(),10))throw std::runtime_error("invalid checkpoint integer");
 R r;if(mpfr_set_z_2exp(r.ptr(),n,ex,MPFR_RNDN)!=0)throw std::runtime_error("inexact checkpoint point");mpz_clear(n);require_finite(r);return r;
}
void save_stack(const std::vector<Box>&stack,int branch){
 std::ofstream out("mixed_nonshort_completion_pending_"+std::to_string(branch)+".txt");
 out<<"nonshort_max_charts_v1 "<<stack.size()<<"\n";
 for(const auto&b:stack){out<<b.chart<<" "<<b.branch<<" "<<b.depth<<"\n";for(const auto&x:b.x){put_point(out,x.l);put_point(out,x.h);}}
 if(!out)throw std::runtime_error("checkpoint write failed");
}
std::vector<Box>load_stack(const char*file,int branch){
 std::ifstream in(file);std::string id;size_t size;in>>id>>size;if(id!="nonshort_max_charts_v1"||size>1000000)throw std::runtime_error("invalid checkpoint header");
 std::vector<Box>stack;for(size_t i=0;i<size;++i){Box b;in>>b.chart>>b.branch>>b.depth;if(!in||b.chart<0||b.chart>2||b.branch!=branch||b.depth<0)throw std::runtime_error("invalid checkpoint box");for(auto&x:b.x){R lo=get_point(in);R hi=get_point(in);x=I(lo,hi);x.valid();}stack.push_back(b);}return stack;
}
void dump_box(const Box&b){
 std::cout<<"FRONTIER chart "<<b.chart<<" branch "<<b.branch<<" depth "<<b.depth<<"\n";
 for(auto x:b.x)std::cout<<x.l.str()<<" "<<x.h.str()<<"\n";
 try{auto v=evaluate(b.x,b.chart,b.branch);for(size_t i=0;i<v.needed.size();++i)std::cout<<"constraint "<<i<<" "<<v.needed[i].l.str()<<" "<<v.needed[i].h.str()<<"\n";}catch(const std::exception&e){std::cout<<"frontier evaluation: "<<e.what()<<"\n";}
}

void probe(){
 for(int chart=0;chart<3;++chart){
  std::array<I,5>x={I::rational(2,3),I::rational(7,5),I(0),I::rational(1,2),I::rational(1,3)};
  auto vv=evaluate(x,chart,0);std::cout<<"corner "<<chart<<" gamma excess "<<vv.gamma_excess.l.str()<<" "<<vv.gamma_excess.h.str()<<"\n";
 }
 I a=I::decimal(".6584371034748513"),c=I::decimal("1.4461080514038527"),d=I::decimal("1.6862971375290967"),r=I::decimal(".879931042213547");
 I K=sq(a)+4,T=a+c,Q=sq(d)+4,W=c+d,z0=K/sq(T)-1,z1=(d-a)/T,z2=W*(d+r)/Q-1;
 std::array<I,5>x={a,c,z1,z0/z1,z2/z1};auto vv=evaluate(x,1,0);
 for(auto nameval:std::vector<std::pair<const char*,I>>{{"u",vv.u},{"v",vv.v},{"h",vv.h},{"w",vv.w},{"nextnorm",vv.nextnorm},{"gamma excess",vv.gamma_excess}})
  std::cout<<nameval.first<<" "<<nameval.second.l.str()<<" "<<nameval.second.h.str()<<"\n";
}
int main(int argc,char**argv){
 check_environment();
 if(argc>1&&std::string(argv[1])=="probe"){probe();check_flags();return 0;}
 long long limit=argc>1?std::atoll(argv[1]):10000;int branch=1;
 std::vector<Box>stack;
 if(argc>3)stack=load_stack(argv[3],branch);
 else for(int chart=1;chart<3;++chart){Box b;b.chart=chart;b.branch=branch;
  b.x={I(I::rational(2,15).l,I::rational(17,20).h),I(I::rational(2,15).l,R(2)),
   I(I::rational(1,32).l,R(15)),I(0),I(R(0),R(1))};
  stack.push_back(b);
 }
 long long count=0,unknown=0,leaves[64]={};int maxdepth=0;auto start=std::chrono::steady_clock::now();
 std::ofstream unresolved("mixed_nonshort_completion_unresolved_"+std::to_string(branch)+".txt");
 while(!stack.empty()&&count<limit){
  Box b=stack.back();stack.pop_back();++count;maxdepth=std::max(maxdepth,b.depth);
  int reason=0;try{reason=judge(b);}catch(const std::domain_error&){}
  if(reason){++leaves[reason];continue;}
  if(b.depth>=85){++unknown;unresolved<<"chart "<<b.chart<<" depth "<<b.depth<<"\n";for(auto x:b.x)unresolved<<x.l.str()<<" "<<x.h.str()<<"\n";continue;}
  int axis=0;double score=-1;
  for(int i=0;i<5;++i){double width=width_up(b.x[i]).get_d(MPFR_RNDU),den=i==2?(1+b.x[i].l.get_d()):i==0?0.5:i==1?1.0:1.0;double s=width/den;if(s>score){score=s;axis=i;}}
  R mid=midpoint(b.x[axis]);if(mid==b.x[axis].l||mid==b.x[axis].h)throw std::runtime_error("bisection stagnation");
  Box other=b;other.x[axis].l=mid;b.x[axis].h=mid;++b.depth;++other.depth;stack.push_back(other);stack.push_back(b);
  if(count%100==0){std::printf("nodes %lld stack %zu depth %d unknown %lld seconds %.2f\n",count,stack.size(),maxdepth,unknown,std::chrono::duration<double>(std::chrono::steady_clock::now()-start).count());std::fflush(stdout);}
 }
 check_flags();std::printf("FINAL branch %d nodes %lld stack %zu depth %d unknown %lld seconds %.2f\n",branch,count,stack.size(),maxdepth,unknown,std::chrono::duration<double>(std::chrono::steady_clock::now()-start).count());
 for(int i=0;i<64;++i)if(leaves[i])std::printf("reason %d leaves %lld\n",i,leaves[i]);
 if(!stack.empty()||unknown){save_stack(stack,branch);if(!stack.empty())dump_box(stack.back());std::cout<<"INCOMPLETE: no M2 exclusion.\n";return 1;}
 if(argc>3)std::cout<<"PASS: supplied pending domain exhausted; not a stand-alone quantified proof.\n";
 else std::cout<<"PASS: complete two-chart reverse boundary domain excluded; interface audit still required.\n";
}
