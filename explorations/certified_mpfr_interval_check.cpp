// Independent exact-rational arithmetic checks and analytic regression checks.
// No search result or sample here certifies an M2 theorem.
#include "certified_mpfr_interval.hpp"
#include <gmpxx.h>
#include <iostream>
#include <random>
#include <vector>
#include <functional>

namespace ci=certified;
using Q=mpq_class;
static std::size_t checks=0;
static void demand(bool ok,const char* what) {
    if(!ok) throw std::runtime_error(what);
    ++checks;
}
static Q rational(long n,unsigned long d=1) {Q q(n,d);q.canonicalize();return q;}
static Q exact(const ci::R& x) {Q q;mpfr_get_q(q.get_mpq_t(),x.ptr());return q;}
static void encloses(const ci::I& x,const Q& l,const Q& h,const char* what) {
    demand(!x.empty() && mpfr_cmp_q(x.l.ptr(),l.get_mpq_t())<=0
           && mpfr_cmp_q(x.h.ptr(),h.get_mpq_t())>=0,what);
}
static ci::I bounds(const Q& l,const Q& h) {
    return {ci::I::from_q(l.get_mpq_t()).l,ci::I::from_q(h.get_mpq_t()).h};
}
static Q qmin(const Q&a,const Q&b){return a<b?a:b;}
static Q qmax(const Q&a,const Q&b){return a>b?a:b;}
static void rejects(const std::function<void()>& f,const char* what) {
    bool caught=false;
    try{f();}catch(const std::exception&){caught=true;}
    demand(caught,what);
}
static Q power(Q x,unsigned n){Q y=1;while(n){if(n&1)y*=x;x*=x;n>>=1;}return y;}
static std::pair<Q,Q> atan_rational(Q x,unsigned n=180) {
    if(x<0){auto p=atan_rational(-x,n);return {-p.second,-p.first};}
    demand(x<1,"atan reference domain");
    Q sum=0,term=x,xx=x*x;
    for(unsigned k=0;k<n;++k){Q s=term/(2*k+1);if(k&1)sum-=s;else sum+=s;term*=xx;}
    Q next=term/(2*n+1);
    if(n&1)return {sum-next,sum};
    return {sum,sum+next};
}
static std::pair<Q,Q> log_rational(Q x,unsigned n=180) {
    if(x<1){auto p=log_rational(1/x,n);return {-p.second,-p.first};}
    Q t=(x-1)/(x+1),tt=t*t,term=t,sum=0;
    for(unsigned k=0;k<n;++k){sum+=2*term/(2*k+1);term*=tt;}
    return {sum,sum+2*term/((2*n+1)*(1-tt))};
}
static std::pair<Q,Q> exp_one(unsigned n=130) {
    Q sum=1,term=1;
    for(unsigned k=1;k<=n;++k){term/=k;sum+=term;}
    Q tail=term/(n+1)/(1-rational(1,n+2));
    return {sum,sum+tail};
}

static void arithmetic_checks() {
    std::mt19937_64 rng(0x7af9b328159dULL);
    for(unsigned k=0;k<12000;++k){
        auto pick=[&](){return rational(static_cast<long>(rng()%20001)-10000,
                                       1+static_cast<unsigned long>(rng()%257));};
        Q x=pick(),y=pick(),z=pick(),w=pick();
        ci::I a=bounds(qmin(x,y),qmax(x,y)),b=bounds(qmin(z,w),qmax(z,w));
        // Reference extrema use the represented endpoints exactly, thereby
        // checking every sign branch even after rational-input enlargement.
        Q al=exact(a.l),ah=exact(a.h),bl=exact(b.l),bh=exact(b.h);
        encloses(a+b,al+bl,ah+bh,"addition lost an endpoint");
        encloses(a-b,al-bh,ah-bl,"subtraction lost an endpoint");
        encloses(-a,-ah,-al,"negation lost an endpoint");
        std::array<Q,4> p={al*bl,al*bh,ah*bl,ah*bh};
        encloses(a*b,*std::min_element(p.begin(),p.end()),*std::max_element(p.begin(),p.end()),
                 "multiplication lost an extremum");
        Q sql=al<=0&&ah>=0?Q(0):qmin(al*al,ah*ah),sqh=qmax(al*al,ah*ah);
        encloses(ci::sq(a),sql,sqh,"square lost an extremum");
        if(bl>0||bh<0){
            std::array<Q,4> d={al/bl,al/bh,ah/bl,ah/bh};
            encloses(a/b,*std::min_element(d.begin(),d.end()),*std::max_element(d.begin(),d.end()),
                     "division lost an extremum");
        }
        ci::I positive=ci::sq(a);ci::I root=ci::rt(positive);
        Q rl=exact(root.l),rh=exact(root.h);
        demand(rl>=0&&rl*rl<=exact(positive.l)&&rh*rh>=exact(positive.h),"sqrt direction failed");
    }
    for(long n=-50;n<=50;++n)for(unsigned long d=1;d<=71;++d){
        Q q=rational(n,d);encloses(ci::I::rational(n,d),q,q,"rational conversion failed");
    }
    encloses(ci::I::decimal("0.1"),rational(1,10),rational(1,10),"decimal input failed");
    encloses(ci::I::decimal("-12.3456789"),rational(-123456789,10000000),
             rational(-123456789,10000000),"negative decimal input failed");
    std::vector<ci::R> values;
    for(long i=0;i<20000;++i)values.emplace_back(i-10000);
    for(long i=0;i<20000;++i)demand(values[i]==ci::R(i-10000),"custom-storage move/copy failed");
    ci::R a(7),b=a;a=ci::R(3);demand(b==ci::R(7),"point copy aliases its source");
    static_assert(!std::is_convertible_v<double,ci::I>,"implicit double constants are unsafe");
    static_assert(!std::is_convertible_v<double,ci::Jet<6>>,"implicit double jet constants are unsafe");
    rejects([](){(void)(ci::I(1)/ci::I(-1,1));},"zero denominator was accepted");
    rejects([](){(void)ci::rt(ci::I(-1,1));},"negative root domain was accepted");
    rejects([](){(void)ci::lg(ci::I(0,1));},"zero log domain was accepted");
    rejects([](){(void)(ci::I(2,1)+1);},"empty interval arithmetic was accepted");
}

static void analytic_checks() {
    for(Q x:{rational(1,2),Q(1),rational(3,2),Q(2),Q(3)}){
        auto ref=log_rational(x);
        encloses(ci::lg(ci::I::from_q(x.get_mpq_t())),ref.first,ref.second,"log rational series failed");
    }
    for(Q x:{rational(-1,2),Q(0),rational(1,5),rational(1,2)}){
        auto ref=atan_rational(x);
        encloses(ci::atanfun(ci::I::from_q(x.get_mpq_t())),ref.first,ref.second,"atan alternating series failed");
    }
    auto e=exp_one();encloses(ci::expfun(ci::I(1)),e.first,e.second,"exp positive series failed");
    auto a=atan_rational(rational(1,5)),b=atan_rational(rational(1,239));
    encloses(ci::pi(),16*a.first-4*b.second,16*a.second-4*b.first,"Machin pi bounds failed");
    using J=ci::Jet<2>;
    for(long i=-30;i<=30;++i)for(long j=1;j<=20;++j){
        Q x=rational(i,16),y=rational(j,16),A=x*x+x*y+1,B=y*y+2;
        J X=J::var(ci::I::from_q(x.get_mpq_t()),0),Y=J::var(ci::I::from_q(y.get_mpq_t()),1);
        J f=(ci::sq(X)+X*Y+1)/(ci::sq(Y)+2);
        std::array<Q,6> refs={A/B,(2*x+y)/B,x/B-2*y*A/(B*B),2/B,
            1/B-2*y*(2*x+y)/(B*B),-4*x*y/(B*B)-2*A/(B*B)+8*y*y*A/(B*B*B)};
        encloses(f.v,refs[0],refs[0],"rational jet value");
        encloses(f.d[0],refs[1],refs[1],"rational jet dx");
        encloses(f.d[1],refs[2],refs[2],"rational jet dy");
        encloses(f.dd[0][0],refs[3],refs[3],"rational jet dxx");
        encloses(f.dd[0][1],refs[4],refs[4],"rational jet dxy");
        encloses(f.dd[1][1],refs[5],refs[5],"rational jet dyy");
        J ar=ci::atanfun(X);Q d1=1/(1+x*x),d2=-2*x/((1+x*x)*(1+x*x));
        encloses(ar.d[0],d1,d1,"atan derivative");
        encloses(ar.dd[0][0],d2,d2,"atan second derivative");
    }
    // Near the removable singularity the true derivatives are finite.
    using U=ci::Jet<1>;
    U at_one=ci::logdiv(U::var(ci::I(1),0));
    encloses(at_one.v,Q(1),Q(1),"logdiv joining value");
    encloses(at_one.d[0],rational(-1,2),rational(-1,2),"logdiv joining derivative");
    encloses(at_one.dd[0][0],rational(2,3),rational(2,3),"logdiv joining second derivative");
    for(Q x:{rational(1,2),rational(3,4),rational(7,8),rational(9,8),rational(3,2),Q(2)}){
        U f=ci::logdiv(U::var(ci::I::from_q(x.get_mpq_t()),0));
        auto lr=log_rational(x);Q den=x-1;
        Q v0=lr.first/den,v1=lr.second/den;
        encloses(f.v,qmin(v0,v1),qmax(v0,v1),"logdiv series value");
        auto first=[&](const Q& L)->Q{return (den/x-L)/(den*den);};
        auto second=[&](const Q& L)->Q{return 2*L/(den*den*den)-(3*x-1)/(x*x*den*den);};
        Q f0=first(lr.first),f1=first(lr.second),s0=second(lr.first),s1=second(lr.second);
        encloses(f.d[0],qmin(f0,f1),qmax(f0,f1),"logdiv series first derivative");
        encloses(f.dd[0][0],qmin(s0,s1),qmax(s0,s1),"logdiv series second derivative");
    }
}

static void taylor_checks() {
    using J=ci::Jet<2>;
    auto f=[](const std::array<J,2>& x){return (ci::sq(x[0])+x[0]*x[1]+1)/(ci::sq(x[1])+2);};
    for(long k=-12;k<=12;++k){
        std::array<ci::I,2> box={ci::I(ci::R(k),ci::R(k+1)),ci::I(1,2)};
        auto center=ci::centers(box);auto all=f(ci::variables(box)),at=f(ci::variables_at(center));
        auto range=ci::taylor(at,all,box,center);
        for(long i=0;i<=8;++i)for(long j=0;j<=8;++j){
            Q x=rational(8*k+i,8),y=rational(8+j,8),value=(x*x+x*y+1)/(y*y+2);
            encloses(range,value,value,"Taylor range lost a rational evaluation");
        }
    }
    // Adjacent representable endpoints have a midpoint rounded to an endpoint.
    // This catches the unsound assumption that half-width remains an exact
    // symmetric displacement bound after midpoint rounding.
    using U=ci::Jet<1>;
    ci::R lo(1),hi(1);mpfr_nextabove(hi.ptr());
    std::array<ci::I,1> box={ci::I(lo,hi)};auto center=ci::centers(box);
    U all=ci::sq(ci::variables(box)[0]),at=ci::sq(ci::variables_at(center)[0]);
    auto range=ci::taylor(at,all,box,center);
    encloses(range,exact(lo)*exact(lo),exact(hi)*exact(hi),"rounded-center Taylor bound failed");
}

int main(){
    try{
        ci::check_environment();
        arithmetic_checks();analytic_checks();taylor_checks();ci::check_flags();
        std::cout<<"PASS "<<checks<<" independent checks; MPFR "<<mpfr_get_version()
                 <<"; precision "<<ci::precision<<" bits; no range/domain flags\n";
    }catch(const std::exception& e){std::cerr<<"FAIL after "<<checks<<" checks: "<<e.what()<<"\n";return 1;}
}
