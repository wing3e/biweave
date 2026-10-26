#pragma once
#include <array>
#include <limits>
#include <ostream>
#include <stdexcept>

struct EndpointRectangleAudit {
 U calls=0,interior_holds=0,singleton_holds=0,cap_holds=0;
 U proposals=0,accepted=0,rejected=0;
 void check()const{
  if(calls!=interior_holds+singleton_holds+cap_holds+proposals||proposals!=accepted+rejected)
   throw std::runtime_error("endpoint rectangle audit accounting");
 }
 void metadata(std::ostream&f)const{
  check();
  f<<"\"endpoint_rectangle_calls\":"<<calls<<",\"endpoint_interior_holds\":"<<interior_holds
   <<",\"endpoint_singleton_holds\":"<<singleton_holds<<",\"endpoint_cap_holds\":"<<cap_holds
   <<",\"endpoint_proposals\":"<<proposals<<",\"endpoint_accepted\":"<<accepted
   <<",\"endpoint_rejected\":"<<rejected<<",";
 }
};

static I draw_endpoint_soft_rectangle(Engine&e,Graph&g,Rectangle r,int power,EndpointRectangleAudit*audit=nullptr){
 if(power<0||power>8||e.opt.kappa||e.opt.anchor_mode!="dual")
  throw std::runtime_error("unsupported endpoint soft rectangle configuration");
 if(r.i<0||r.j>=g.nr||r.i>=r.j||r.k<0||r.l>=g.nc||r.k>=r.l||g.D<0||(g.D&1))
  throw std::runtime_error("invalid endpoint soft rectangle state/descriptor");
 if(audit)++audit->calls;
 const auto old=g.cells(r);const auto interval=Engine::interval(old);
 const I lo=interval.first,hi=interval.second;
 const U old_m=U(g.edges.size()),old_H=g.Hproduct(r,0);
 if(!old_H||old_m<2||lo>0||hi<0||lo>hi)
  throw std::runtime_error("invalid endpoint soft rectangle current line");
 if(e.coverage_cap.requested&&old_m>e.coverage_cap.bound)
  throw std::runtime_error("endpoint conditional support omitted current state");
 if(lo==hi){if(audit)++audit->singleton_holds;return 0;}
 if(lo!=0&&hi!=0){if(audit)++audit->interior_holds;return 0;}
 const I delta=lo==0?hi:lo;
 if(!delta)throw std::runtime_error("endpoint distinct proposal is zero");
 const std::array<S128,4>next{S128(old[0])+delta,S128(old[1])-delta,S128(old[2])-delta,S128(old[3])+delta};
 std::array<int,4>before{},after{};int old_nz=0,new_nz=0;
 for(size_t j=0;j<4;++j){
  if(old[j]<0||next[j]<0||next[j]>S128(std::numeric_limits<I>::max()))
   throw std::runtime_error("endpoint rectangle weight arithmetic");
  before[j]=old[j]>0;after[j]=next[j]>0;old_nz+=before[j];new_nz+=after[j];
 }
 const S128 next_m=S128(old_m)-old_nz+new_nz;
 if(next_m<2||next_m>S128(std::numeric_limits<U>::max()))
  throw std::runtime_error("endpoint rectangle support arithmetic");
 if(e.coverage_cap.requested&&next_m>S128(e.coverage_cap.bound)){
  if(audit)++audit->cap_holds;return 0;
 }
 const std::array<int,4>vertices{r.i,r.j,g.nr+r.k,g.nr+r.l};
 const std::array<int,4>changes{
  after[0]+after[1]-before[0]-before[1],after[2]+after[3]-before[2]-before[3],
  after[0]+after[2]-before[0]-before[2],after[1]+after[3]-before[1]-before[3]};
 auto abs128=[](S128 v){return v<0?-v:v;};
 S128 next_D=g.D;
 for(size_t j=0;j<4;++j){
  const int v=vertices[j];const S128 degree=S128(g.degree[v])+changes[j];
  if(degree<0||degree>S128(std::numeric_limits<int>::max()))
   throw std::runtime_error("endpoint rectangle degree arithmetic");
  next_D-=abs128(S128(g.degree[v])-g.target_degree[v]);
  next_D+=abs128(degree-g.target_degree[v]);
 }
 if(next_D<0||next_D>S128(std::numeric_limits<I>::max())||(next_D&1)||abs128(next_D-g.D)>8)
  throw std::runtime_error("endpoint rectangle defect arithmetic");
 const U new_m=U(next_m),new_H=U(after[0]&&after[3])+U(after[1]&&after[2]);
 if(!new_H)throw std::runtime_error("endpoint rectangle zero reverse descriptor probability");

 mpz_class numerator=mpz_class(new_H)*old_m*old_m;
 mpz_class denominator=mpz_class(old_H)*new_m*new_m;
 const S128 exponent_wide=S128(power)*(S128(g.D)-next_D)/2;
 if(exponent_wide<-32||exponent_wide>32)
  throw std::runtime_error("endpoint rectangle potential exponent arithmetic");
 const I exponent=I(exponent_wide);
 if(exponent>0)mpz_mul_2exp(numerator.get_mpz_t(),numerator.get_mpz_t(),unsigned(exponent));
 else if(exponent<0)mpz_mul_2exp(denominator.get_mpz_t(),denominator.get_mpz_t(),unsigned(-exponent));
 if(audit)++audit->proposals;
 const bool accept=exact_accept(e.rng,rational(numerator,denominator));
 if(audit){if(accept)++audit->accepted;else ++audit->rejected;}
 return accept?delta:I(0);
}
