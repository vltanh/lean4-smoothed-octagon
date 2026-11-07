#pragma once
// Proposal-only LP extracted from the audited smaller-short caller, SHA256
// 68ad563d1db8e0743eb6e2f94ef8d13a4f7fbf1f4e78c8f2dac9bcb0e350b36a.
// Generalized only from dimension 6 to Jet<N>, plus names/box interface.
// Any proposed exact nonnegative dyadic weights are sound: a box is rejected
// solely by its freshly computed directed interval Taylor bound, never by LP.
#include "certified_mpfr_interval.hpp"
#include <algorithm>
#include <array>
#include <cmath>
#include <cstdint>
#include <vector>
namespace certified {
using std::array;using std::vector;using std::min;using std::max;
using std::abs;using std::isfinite;using std::floor;using std::swap;
struct ProposalLP {
 int m,n;vector<int>B,N;vector<vector<double>>D,T;
 ProposalLP(const vector<vector<double>>&A,const vector<double>&b):m(b.size()),n(A[0].size()),B(m),N(n+1),D(m+2,vector<double>(n+2)),T(m+2,vector<double>(m)){
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
template<std::size_t N>
bool linear_combination_reject(const vector<Jet<N>>&mid,const vector<Jet<N>>&all,const std::array<I,N>&box){
 using J=Jet<N>;
 vector<vector<double>>A;vector<double>rhs,scales;vector<int>ids;
 array<double,N>ri;
 for(int j=0;j<N;++j)ri[j]=(box[j].h.get_d()-box[j].l.get_d())/2;
 for(int o=0;o<(int)min(all.size(),mid.size());++o){
  const J&at=mid[o];const J&box=all[o];double upper=at.v.h.get_d();
  vector<double>row(N);
  for(int i=0;i<N;++i){
   double gl=at.d[i].l.get_d(),gh=at.d[i].h.get_d(),g=(gl+gh)/2;
   row[i]=-2*ri[i]*g;upper-=g*ri[i];upper+=(gh-gl)*ri[i]/2;
   for(int j=0;j<N;++j){
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
 for(int j=0;j<N;++j){vector<double>row(N);row[j]=1;A.push_back(row);rhs.push_back(1);}
 ProposalLP lp(A,rhs);if(!lp.infeasible())return false;
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
  if(n){J wt(I::rational(static_cast<intmax_t>(n),1048576));cm=cm+wt*mid[ids[i]];ca=ca+wt*all[ids[i]];}
 }
 return certified::taylor(cm,ca,box,certified::centers(box)).h<0;
}
} // namespace certified
