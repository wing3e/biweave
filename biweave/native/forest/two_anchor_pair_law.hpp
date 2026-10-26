#pragma once
#include <algorithm>
#include <array>
#include <cstdint>
#include <limits>
#include <stdexcept>
#include <gmpxx.h>

struct TwoAnchorPairLaw {
 using Count=std::uint64_t;using I=std::int64_t;using Wide=__int128_t;
 struct Input {
  Count qi=0,qj=0,T=0;
  I low=1,high=2;
  Wide beta_i=0,beta_j=0,X=0,Y=0;
  bool two_anchor=true;
 };
 struct Split {Wide Ri=0,Rj=0,lo=0,hi=0;Count K=0;};
 struct Law {Input input;Count L=0,U=0;Wide Bi=0,C=0,delta=0;mpz_class initial=1,total=0;};
 struct Draw {Count z=0;Wide Pi=0,Pj=0,Qi=0,Qj=0;};
 static Wide floor_div(Wide a,Wide d){
  if(d<=0)throw std::invalid_argument("nonpositive divisor");
  const Wide q=a/d,r=a%d;return q-(r<0);
 }
 static Wide ceil_div(Wide a,Wide d){
  if(d<=0)throw std::invalid_argument("nonpositive divisor");
  const Wide q=a/d,r=a%d;return q+(r>0);
 }
 static Count count(Wide a){
  if(a<0||a>Wide(std::numeric_limits<Count>::max()))throw std::overflow_error("integer count out of uint64 range");
  return Count(a);
 }
 static void validate(const Input&v){
  static_assert(sizeof(unsigned long)>=sizeof(Count),"GMP scalar law requires 64-bit unsigned long");
  const Wide imax=std::numeric_limits<I>::max();
  if(v.low<=0||v.high<=v.low)throw std::invalid_argument("require distinct positive integer weights");
  if(v.qi>std::numeric_limits<Count>::max()-v.qj||v.T>v.qi+v.qj)throw std::invalid_argument("invalid total private quota");
  if(v.beta_i<1||v.beta_j<1||v.beta_i>imax||v.beta_j>imax)throw std::invalid_argument("residual strengths outside source signed64 qualification");
  if(v.X<1||v.X>imax||v.Y<0||v.Y>imax||(!v.two_anchor&&v.Y!=0))throw std::invalid_argument("public total outside source signed64 qualification");
  if(v.two_anchor&&(v.X<2||v.Y<2))throw std::invalid_argument("two positive public rows require X,Y>=2");
  if(!v.two_anchor&&v.X<2)throw std::invalid_argument("single positive public pair requires X>=2");
 }
 static Split split(const Law&p,Count z){
  if(z<p.L||z>p.U)throw std::invalid_argument("profile outside legal interval");
  Split s;s.Ri=p.Bi-p.delta*Wide(z);s.Rj=p.C-s.Ri;
  if(p.input.two_anchor){
   s.lo=std::max<Wide>(1,s.Ri-p.input.Y+1);
   s.hi=std::min(s.Ri-1,p.input.X-1);
   if(s.lo>s.hi||s.Ri<2||s.Rj<2)throw std::logic_error("empty two-anchor public split");
   s.K=count(s.hi-s.lo+1);
  }else{
   if(s.Ri<1||s.Rj<1)throw std::logic_error("invalid single-anchor public split");
   s.lo=s.hi=s.Ri;s.K=1;
  }
  return s;
 }
 static void advance(mpz_class&base,const Law&p,Count z){
  const Count d0=z+1,d1=p.input.qj-(p.input.T-z)+1;
  if(!d0||!d1||!mpz_divisible_ui_p(base.get_mpz_t(),static_cast<unsigned long>(d0)))throw std::logic_error("first relative mass division not exact");
  base/=d0;
  if(!mpz_divisible_ui_p(base.get_mpz_t(),static_cast<unsigned long>(d1)))throw std::logic_error("second relative mass division not exact");
  base/=d1;base*=p.input.qi-z;base*=p.input.T-z;
  if(base<=0)throw std::logic_error("nonpositive relative profile mass");
 }
 static Law build(const Input&v){
  validate(v);Law p;p.input=v;p.delta=Wide(v.high)-v.low;p.Bi=v.beta_i-Wide(v.low)*v.qi;p.C=v.X+v.Y;

  const Wide actual=v.beta_i+v.beta_j-Wide(v.low)*(v.qi+v.qj)-p.delta*Wide(v.T);
  if(actual!=p.C)throw std::invalid_argument("residual row and public column totals disagree");
  const Wide minimum=v.two_anchor?2:1;
  const Wide lowz=std::max({Wide(0),Wide(v.T)-v.qj,ceil_div(p.Bi-p.C+minimum,p.delta)});
  const Wide highz=std::min({Wide(v.qi),Wide(v.T),floor_div(p.Bi-minimum,p.delta)});
  if(lowz>highz)throw std::invalid_argument("empty legal high-count interval");
  p.L=count(lowz);p.U=count(highz);
  for(Count z=p.L;z<p.U;++z){p.initial*=z+1;p.initial*=v.qj-(v.T-z)+1;}
  mpz_class base=p.initial;
  for(Count z=p.L;;++z){p.total+=base*split(p,z).K;if(z==p.U)break;advance(base,p,z);}
  if(p.total<=0)throw std::logic_error("nonpositive weighted total mass");
  return p;
 }
 static Count unrank(const Law&p,mpz_class rank){
  if(rank<0||rank>=p.total)throw std::invalid_argument("profile rank outside mass");
  mpz_class base=p.initial;
  for(Count z=p.L;;++z){const mpz_class weight=base*split(p,z).K;if(rank<weight)return z;
   rank-=weight;if(z==p.U)break;advance(base,p,z);
  }
  throw std::logic_error("weighted profile rank lost");
 }
 static Draw fill(const Law&p,Count z,Count xi_rank){
  const auto s=split(p,z);if(xi_rank>=s.K)throw std::invalid_argument("public split rank outside K");
  Draw d;d.z=z;d.Pi=s.lo+xi_rank;d.Pj=p.input.X-d.Pi;
  if(p.input.two_anchor){d.Qi=s.Ri-d.Pi;d.Qj=p.input.Y-d.Qi;}
  return d;
 }
 template<class BigPick,class SmallPick>static Draw draw(const Law&p,BigPick&&bigpick,SmallPick&&smallpick){
  const Count z=p.L==p.U?p.L:unrank(p,bigpick(p.total));const auto s=split(p,z);
   
  const Count x=s.K==1?0:smallpick(s.K);return fill(p,z,x);
 }
};
