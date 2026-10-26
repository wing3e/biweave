#pragma once

static I draw_soft_rectangle(Engine&e,Graph&g,Rectangle r,int power){
 if(power<0||power>8||e.opt.kappa||e.opt.anchor_mode!="dual")
  throw std::runtime_error("unsupported soft rectangle Gibbs configuration");
 if(r.i<0||r.j>=g.nr||r.i>=r.j||r.k<0||r.l>=g.nc||r.k>=r.l||g.D<0||(g.D&1))
  throw std::runtime_error("invalid soft rectangle Gibbs state/descriptor");
 const auto old=g.cells(r);const auto bounds=Engine::interval(old);
 const I lo=bounds.first,hi=bounds.second;
 const S128 width=S128(hi)-S128(lo);
 if(width<=0||width>S128(std::numeric_limits<I>::max())||!g.Hproduct(r,0))
  throw std::runtime_error("invalid soft rectangle Gibbs line");
 struct Class{I lower=0,upper=0,D=0;U count=0,m=0,H=0;mpq_class mass=0;mpz_class tickets=0;};
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
    throw std::runtime_error("soft rectangle Gibbs weight arithmetic");
   before[j]=old[j]>0;after[j]=next[j]>0;old_nz+=before[j];new_nz+=after[j];
  }
  const S128 new_m=S128(old_m)-old_nz+new_nz;
  if(new_m<2||new_m>S128(std::numeric_limits<U>::max()))
   throw std::runtime_error("soft rectangle Gibbs support arithmetic");

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
    throw std::runtime_error("soft rectangle Gibbs degree arithmetic");
   new_D-=abs128(S128(g.degree[v])-g.target_degree[v]);
   new_D+=abs128(new_degree-g.target_degree[v]);
  }
  if(new_D<0||new_D>S128(std::numeric_limits<I>::max())||(new_D&1)||abs128(new_D-g.D)>8)
   throw std::runtime_error("soft rectangle Gibbs defect arithmetic");
  const U H=U(after[0]&&after[3])+U(after[1]&&after[2]);
  if(!H)throw std::runtime_error("soft rectangle Gibbs has zero reverse descriptor mass");
  const S128 cardinality=S128(upper)-lower+1;
  if(cardinality<=0||cardinality>S128(std::numeric_limits<U>::max())||count==classes.size())
   throw std::runtime_error("soft rectangle Gibbs class arithmetic");
  Class &c=classes[count++];c.lower=lower;c.upper=upper;c.D=I(new_D);c.count=U(cardinality);c.m=U(new_m);c.H=H;
 };
 append(lo,lo);append(hi,hi);if(width>1)append(lo+1,hi-1);
 if(!count)throw std::runtime_error("soft rectangle Gibbs empty conditional line");
 bool contains_current=false;I minimum_D=classes[0].D;
 for(size_t j=0;j<count;++j){minimum_D=std::min(minimum_D,classes[j].D);contains_current|=classes[j].lower<=0&&0<=classes[j].upper;}
 if(!contains_current)throw std::runtime_error("soft rectangle Gibbs omitted current state");
 mpz_class common_denominator=1,total=0;
 for(size_t j=0;j<count;++j){
  Class &c=classes[j];const S128 difference=S128(c.D)-minimum_D;
  if(difference<0||(difference&1)||difference>8)
   throw std::runtime_error("soft rectangle Gibbs class potential arithmetic");
  mpz_class numerator=mpz_class(c.count)*c.H,denominator=mpz_class(c.m)*c.m;
  const unsigned exponent=unsigned(S128(power)*difference/2);
  if(exponent)mpz_mul_2exp(denominator.get_mpz_t(),denominator.get_mpz_t(),exponent);
  c.mass=rational(numerator,denominator);
  mpz_lcm(common_denominator.get_mpz_t(),common_denominator.get_mpz_t(),c.mass.get_den().get_mpz_t());
 }
 for(size_t j=0;j<count;++j){Class &c=classes[j];c.tickets=c.mass.get_num()*(common_denominator/c.mass.get_den());if(c.tickets<=0)throw std::runtime_error("soft rectangle Gibbs nonpositive class mass");total+=c.tickets;}
 if(total<=0)throw std::runtime_error("soft rectangle Gibbs nonpositive total mass");
 mpz_class draw=zbig(e.rng.below_big(bigz(total)));
 for(size_t j=0;j<count;++j){const Class &c=classes[j];if(draw<c.tickets)return c.lower==c.upper?c.lower:e.rng.integer(c.lower,c.upper);draw-=c.tickets;}
 throw std::runtime_error("soft rectangle Gibbs rank beyond total mass");
}
