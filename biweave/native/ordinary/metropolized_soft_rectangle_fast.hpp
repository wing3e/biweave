#pragma once
#include "metropolized_soft_rectangle.hpp"

static I draw_metropolized_soft_rectangle_fast(Engine&e,Graph&g,Rectangle r,int power){
 if(power<0||power>8||e.opt.kappa||e.opt.anchor_mode!="dual")
  throw std::runtime_error("unsupported metropolized soft rectangle configuration");
 if(r.i<0||r.j>=g.nr||r.i>=r.j||r.k<0||r.l>=g.nc||r.k>=r.l||g.D<0||(g.D&1))
  throw std::runtime_error("invalid metropolized soft rectangle state/descriptor");
 const auto old=g.cells(r);const auto bounds=Engine::interval(old);
 const I lo=bounds.first,hi=bounds.second;
 const S128 width=S128(hi)-S128(lo);
 if(width<=0||width>S128(std::numeric_limits<I>::max())||!g.Hproduct(r,0))
  throw std::runtime_error("invalid metropolized soft rectangle line");
 struct Class{I lower=0,upper=0,D=0;U count=0,m=0,H=0;};
 std::array<Class,3> classes{};size_t count=0;
 const U old_m=U(g.edges.size());
 const std::array<int,4>vertices{r.i,r.j,g.nr+r.k,g.nr+r.l};
 auto abs128=[](S128 v){return v<0?-v:v;};
 auto append=[&](I lower,I upper){
  if(lower>upper)return;
  const I delta=lower;
  const std::array<S128,4>next{S128(old[0])+delta,S128(old[1])-delta,S128(old[2])-delta,S128(old[3])+delta};
  std::array<int,4>before{},after{};int old_nz=0,new_nz=0;
  for(size_t j=0;j<4;++j){
   if(old[j]<0||next[j]<0||next[j]>S128(std::numeric_limits<I>::max()))
    throw std::runtime_error("metropolized soft rectangle weight arithmetic");
   before[j]=old[j]>0;after[j]=next[j]>0;old_nz+=before[j];new_nz+=after[j];
  }
  const S128 new_m=S128(old_m)-old_nz+new_nz;
  if(new_m<2||new_m>S128(std::numeric_limits<U>::max()))
   throw std::runtime_error("metropolized soft rectangle support arithmetic");

  if(e.coverage_cap.requested&&new_m>S128(e.coverage_cap.bound))return;
  const std::array<int,4>changes{
   after[0]+after[1]-before[0]-before[1],
   after[2]+after[3]-before[2]-before[3],
   after[0]+after[2]-before[0]-before[2],
   after[1]+after[3]-before[1]-before[3]};
  S128 new_D=g.D;
  for(size_t j=0;j<4;++j){
   const int v=vertices[j];const S128 new_degree=S128(g.degree[v])+changes[j];
   if(new_degree<0||new_degree>S128(std::numeric_limits<int>::max()))
    throw std::runtime_error("metropolized soft rectangle degree arithmetic");
   new_D-=abs128(S128(g.degree[v])-g.target_degree[v]);
   new_D+=abs128(new_degree-g.target_degree[v]);
  }
  if(new_D<0||new_D>S128(std::numeric_limits<I>::max())||(new_D&1)||abs128(new_D-g.D)>8)
   throw std::runtime_error("metropolized soft rectangle defect arithmetic");
  const U H=U(after[0]&&after[3])+U(after[1]&&after[2]);
  if(!H)throw std::runtime_error("metropolized soft rectangle has zero reverse descriptor mass");
  const S128 cardinality=S128(upper)-lower+1;
  if(cardinality<=0||cardinality>S128(std::numeric_limits<U>::max())||count==classes.size())
   throw std::runtime_error("metropolized soft rectangle class arithmetic");
  Class &c=classes[count++];c.lower=lower;c.upper=upper;c.D=I(new_D);c.count=U(cardinality);c.m=U(new_m);c.H=H;
 };
 append(lo,lo);append(hi,hi);if(width>1)append(lo+1,hi-1);
 if(!count)throw std::runtime_error("metropolized soft rectangle empty conditional line");
 bool contains_current=false;I minimum_D=classes[0].D;
 for(size_t j=0;j<count;++j){minimum_D=std::min(minimum_D,classes[j].D);contains_current|=classes[j].lower<=0&&0<=classes[j].upper;}
 if(!contains_current)throw std::runtime_error("metropolized soft rectangle omitted current state");
  
 size_t current_index=classes.size();
 for(size_t j=0;j<count;++j){
  const Class &c=classes[j];
  if(c.lower<=0&&0<=c.upper){
   if(current_index!=classes.size())throw std::runtime_error("fast NS duplicate delta0 class");
   current_index=j;
   if(c.m!=old_m||c.D!=g.D||c.H!=g.Hproduct(r,0))
    throw std::runtime_error("fast NS current-state factors mismatch");
  }
 }
 if(current_index==classes.size())throw std::runtime_error("fast NS missing current mass");
 using Wide=__uint128_t;
 const Wide wide_max=~Wide(0),small_max=Wide(std::numeric_limits<U>::max());
 auto gcd=[](Wide a,Wide b){while(b){const Wide rem=a%b;a=b;b=rem;}return a;};
 auto multiply=[](Wide a,Wide b,Wide limit,Wide&out){
  if(a>limit||b>limit||(a&&b>limit/a))return false;
  out=a*b;return true;
 };
 struct Tickets{std::array<Wide,3>weights{},groups{};Wide total=0,old=0,proposal=0;};
 auto make_tickets=[&](Wide limit,Tickets&result){
   
  std::array<Wide,3>numerators{},denominators{};Wide common=1;
  for(size_t j=0;j<count;++j){
   const Class &c=classes[j];const S128 difference=S128(c.D)-minimum_D;
   if(difference<0||(difference&1)||difference>8)
    throw std::runtime_error("fast NS class potential arithmetic");
   const unsigned exponent=unsigned(S128(power)*difference/2);
   if(exponent>=128)return false;  
   Wide square=0,denominator=0;
   if(!multiply(Wide(c.m),Wide(c.m),limit,square)||
      !multiply(square,Wide(1)<<exponent,limit,denominator))return false;
   Wide numerator=Wide(c.H);const Wide divisor=gcd(numerator,denominator);
   if(!divisor)return false;
   numerator/=divisor;denominator/=divisor;
   numerators[j]=numerator;denominators[j]=denominator;
   const Wide common_divisor=gcd(common,denominator);Wide next=0;
   if(!common_divisor||!multiply(common/common_divisor,denominator,limit,next))return false;
   common=next;
  }
  Tickets local;
  for(size_t j=0;j<count;++j){
   if(!denominators[j]||common%denominators[j])return false;
   Wide ticket=0,mass=0;
   if(!multiply(numerators[j],common/denominators[j],limit,ticket)||!ticket||
      !multiply(Wide(classes[j].count),ticket,limit,mass)||mass>limit-local.total)return false;
   const U eligible=classes[j].count-U(classes[j].lower<=0&&0<=classes[j].upper);Wide eligible_mass=0;
   if(!multiply(Wide(eligible),ticket,limit,eligible_mass))return false;
   local.weights[j]=ticket;local.groups[j]=eligible_mass;local.total+=mass;
  }
  local.old=local.weights[current_index];
  if(!local.old||local.total<local.old)return false;
  local.proposal=local.total-local.old;result=local;return true;
 };
 Tickets tickets;
 const bool native64=make_tickets(small_max,tickets);
 if(!native64&&!make_tickets(wide_max,tickets))
  return draw_metropolized_soft_rectangle(e,g,r,power);
 if(!tickets.proposal)return 0;
 auto below_wide=[&](Wide n){
  if(!n)throw std::runtime_error("fast NS empty uint128 choice");
  if(n==1)return Wide(0);
  if(n<=small_max)return Wide(e.rng.below(U(n)));
  const Wide two64=Wide(1)<<64;
  if(n==two64)return Wide(e.rng.gen());
  unsigned bits=0;for(Wide v=n-1;v;v>>=1)++bits;
  if(bits<65||bits>128)throw std::runtime_error("fast NS uint128 bit width");
  const Wide mask=bits==128?wide_max:(Wide(1)<<bits)-1;
  for(;;){
   const U high=e.rng.gen(),low=e.rng.gen();
   const Wide draw=((Wide(high)<<64)|Wide(low))&mask;
   if(draw<n)return draw;
  }
 };

 Wide draw=below_wide(tickets.proposal);
 for(size_t j=0;j<count;++j){
  const Class &c=classes[j];const bool contains_zero=c.lower<=0&&0<=c.upper;
  const U available=c.count-U(contains_zero);if(!available)continue;
  const Wide group_mass=tickets.groups[j];
  if(draw<group_mass){
   const U rank=available==1?0:e.rng.below(available);
   S128 selected=S128(c.lower)+rank;if(contains_zero&&selected>=0)++selected;
   if(selected<c.lower||selected>c.upper||selected==0||
      selected<S128(std::numeric_limits<I>::min())||selected>S128(std::numeric_limits<I>::max()))
    throw std::runtime_error("fast NS invalid nonzero delta rank");
   if(tickets.total<=tickets.weights[j])throw std::runtime_error("fast NS invalid reverse mass");
   const Wide reverse_total=tickets.total-tickets.weights[j];
   const bool accept=tickets.proposal>=reverse_total||below_wide(reverse_total)<tickets.proposal;
   return accept?I(selected):I(0);
  }
  draw-=group_mass;
 }
 throw std::runtime_error("fast NS rank beyond proposal mass");
}
