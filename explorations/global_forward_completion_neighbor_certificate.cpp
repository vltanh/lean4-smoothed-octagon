// Exact rational interval certificate for the forward neighbor contraction.
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
struct Box {array<I,4>x;int depth=0;};
struct J {
 I v; array<I,4>d; array<array<I,4>,4>dd;
 J(long a=0):v(a){} J(const R&a):v(a){} J(I a):v(a){}
 static J var(I a,int n){J r(a);r.d[n]=1;return r;}
};
J operator+(const J&a,const J&b){J r(a.v+b.v);for(int i=0;i<4;++i){r.d[i]=a.d[i]+b.d[i];for(int j=0;j<4;++j)r.dd[i][j]=a.dd[i][j]+b.dd[i][j];}return r;}
J operator-(const J&a,const J&b){J r(a.v-b.v);for(int i=0;i<4;++i){r.d[i]=a.d[i]-b.d[i];for(int j=0;j<4;++j)r.dd[i][j]=a.dd[i][j]-b.dd[i][j];}return r;}
J operator*(const J&a,const J&b){J r(a.v*b.v);for(int i=0;i<4;++i){r.d[i]=a.d[i]*b.v+a.v*b.d[i];for(int j=0;j<4;++j)r.dd[i][j]=a.dd[i][j]*b.v+a.d[i]*b.d[j]+a.d[j]*b.d[i]+a.v*b.dd[i][j];}return r;}
J fun(const J&a,I val,I der,I der2){J r(val);for(int i=0;i<4;++i){r.d[i]=der*a.d[i];for(int j=0;j<4;++j)r.dd[i][j]=der2*a.d[i]*a.d[j]+der*a.dd[i][j];}return r;}
J inv(const J&a){return fun(a,1/a.v,-1/sq(a.v),2/(sq(a.v)*a.v));}
J operator/(const J&a,const J&b){return a*inv(b);}
J sq(const J&a){return fun(a,sq(a.v),2*a.v,2);}
J lop(const J&v){J t=(v-1)/(v+1),t2=sq(t);return 2*t*(1+t2/3+t2*t2/(5*(1-t2)));}
J lom(const J&v){J t=(v-1)/(v+1),t2=sq(t);return 2*t*(1+t2/3+t2*t2/5);}
J ff(const J&x,const J&v){J t=(v-1)/(v+1),t2=sq(t);return 1+sq(x)*v-x*(1+t)*(1+t2/3+t2*t2/(5*(1-t2)));}
J jet(const Box&b,bool mid){
 array<J,4>x;for(int i=0;i<4;++i)x[i]=J::var(mid?I((b.x[i].l+b.x[i].h)/2):b.x[i],i);
 J U=x[0],z=x[1],w=x[2],h=x[3],S=1+z,T=1+w,L=1+U,Z=sq(z)+U,W=sq(w)+U,q=S*T/L,ii=sq(T)/W;
 J A=1+z+w-1/S-1/T+1/L-lom(q);
 J B=Z*h/S+1-sq(z)*S/(Z*h)-sq(z)/S+sq(z)*z/Z-z*lop(h);
 J n=sq(S)*(U-z)*(h-1)/Z,m=sq(L)*(q-1+(h-1)*(S*q-1))/(S*Z),al=L*(h*S-z)/Z;
 return al*A-B-n*ff(z/S,h)-m*ff(w/T,ii);
}
I taylor(const J&at,const J&all,const Box&b){
 R lo=at.v.l,hi=at.v.h;
 for(int i=0;i<4;++i){R ri=(b.x[i].h-b.x[i].l)/2;I t=at.d[i]*I(-ri,ri);lo+=t.l;hi+=t.h;
  for(int j=0;j<4;++j){R rj=(b.x[j].h-b.x[j].l)/2;I t=all.dd[i][j]*I(i==j?R(0):R(-ri*rj),ri*rj)*I(R(1)/2);lo+=t.l;hi+=t.h;}}
 return intersect(I(lo,hi),all.v);
}
int judge(Box&b){
 auto &U=b.x[0],&z=b.x[1],&w=b.x[2],&h=b.x[3];
 for(int it=0;it<3;++it){
 U.l=rmax(U.l,1+3*(z.l+w.l)/5);z.h=rmin(z.h,rmin(w.h,5*(U.h-1)/3-w.l));w.h=rmin(w.h,5*(U.h-1)/3-z.l);w.l=rmax(w.l,z.l);
 if(U.l>U.h||z.l>z.h||w.l>w.h)return 1;
 h.l=rmax(h.l,(1+z.l)*(1+z.l)/(z.l*z.l+U.h));h.h=rmin(h.h,(1+z.l)/z.l);if(h.l>h.h)return 1;
 }
 J all=jet(b,false);if(all.v.h<0)return 2;
 if(b.depth>8){J mid=jet(b,true);if(taylor(mid,all,b).h<0)return 3;}
 return 0;
}
int main(int argc,char**argv){
 long long limit=argc>1?atoll(argv[1]):100000;
 vector<Box>stack;Box init;init.x={I(R(11)/5,3),I(1,R(7)/3),I(R(5)/4,R(7)/3),I(1,2)};stack.push_back(init);
 long long cnt=0,leaves[4]={},unknown=0;int maxdepth=0;auto t=chrono::steady_clock::now();
 while(!stack.empty()&&cnt<limit){Box b=stack.back();stack.pop_back();++cnt;maxdepth=std::max(maxdepth,b.depth);int code=0;try{code=judge(b);}catch(const runtime_error&){}if(code){leaves[code]++;continue;}
 if(b.depth>70){++unknown;continue;}
 int j=0;R width=-1;R scale[]={R(4)/5,R(4)/3,R(13)/12,1};for(int i=0;i<4;++i){R w=(b.x[i].h-b.x[i].l)/scale[i];if(w>width){width=w;j=i;}}
 R mid=(b.x[j].l+b.x[j].h)/2;Box c=b;c.x[j].l=mid;b.x[j].h=mid;b.depth++;c.depth++;stack.push_back(c);stack.push_back(b);
 if(cnt%1000==0){printf("nodes %lld stack %zu depth %d time %.1f\n",cnt,stack.size(),maxdepth,chrono::duration<double>(chrono::steady_clock::now()-t).count());fflush(stdout);}}
 printf("FINAL nodes %lld stack %zu depth %d unknown %lld time %.2f leaves %lld %lld %lld\n",cnt,stack.size(),maxdepth,unknown,chrono::duration<double>(chrono::steady_clock::now()-t).count(),leaves[1],leaves[2],leaves[3]);
 if(!stack.empty()){printf("NEXT ");for(auto x:stack.back().x)cout<<"["<<x.l<<","<<x.h<<"] ";printf("\n");}
 if(!stack.empty()||unknown)return 1;
 cout<<"PASS: every box was excluded by exact rational bounds.\n";
 return 0;
}
