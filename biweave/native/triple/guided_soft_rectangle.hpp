#pragma once

struct GuidedDefectAnchors {
 std::map<int,U>badmap;U mass=0;
 U clears=0,verified_rollbacks=0,vertex_refreshes=0,background_draws=0,defect_draws=0,second_uniform_draws=0;
 static U defect(const Graph&g,int v){
  if(v<0||size_t(v)>=g.degree.size()||size_t(v)>=g.target_degree.size())
   throw std::runtime_error("guided defect vertex outside graph");
  const S128 difference=S128(g.degree[v])-g.target_degree[v];
  const S128 value=difference<0?-difference:difference;
  if(value>S128(std::numeric_limits<U>::max()))throw std::runtime_error("guided vertex defect overflow");
  return U(value);
 }
 void clear_F(const Graph&g){
   
  if(g.D||mass||!badmap.empty())throw std::runtime_error("guided clear must start at synchronized F");
  badmap.clear();mass=0;++clears;
 }
 void reset_after_verified_rollback(const Graph&g){

  if(g.D)throw std::runtime_error("guided reset requires verified rollback to F");
  for(const auto&entry:badmap)if(defect(g,entry.first))
   throw std::runtime_error("guided rollback left cached vertex outside target degree");
  badmap.clear();mass=0;++verified_rollbacks;
 }
 void refresh_rectangle(const Graph&g,Rectangle r){
  if(r.i<0||r.j>=g.nr||r.i>=r.j||r.k<0||r.l>=g.nc||r.k>=r.l||
     S128(g.nr)+g.nc>std::numeric_limits<int>::max()||g.D<0||(g.D&1))
   throw std::runtime_error("guided refresh rectangle/state invalid");
  const std::array<int,4>vertices{r.i,r.j,g.nr+r.k,g.nr+r.l};
  std::array<U,4>next{};U old_sum=0,new_sum=0;
  for(size_t j=0;j<4;++j){
   const int v=vertices[j];auto found=badmap.find(v);const U old=found==badmap.end()?0:found->second;
   next[j]=defect(g,v);
   if(next[j]&&(g.degree[v]<=0||size_t(v)>=g.adj.size()||g.adj[v].size()!=U(g.degree[v])||
                 size_t(v)>=g.target_strength.size()||g.target_strength[v]<=0))
    throw std::runtime_error("guided positive defect has no positive-strength incident edge");
   old_sum=checked_u128(__uint128_t(old_sum)+old,"guided old local defect");
   new_sum=checked_u128(__uint128_t(new_sum)+next[j],"guided new local defect");
  }
  if(old_sum>mass)throw std::runtime_error("guided cached mass underflow");
  const U new_mass=checked_u128(__uint128_t(mass-old_sum)+new_sum,"guided refreshed total defect");
  if(new_mass!=U(g.D))throw std::runtime_error("guided four-vertex refresh missed degree mutation");
  for(size_t j=0;j<4;++j){if(next[j])badmap[vertices[j]]=next[j];else badmap.erase(vertices[j]);}
  mass=new_mass;vertex_refreshes+=4;
 }
 void check_sparse(const Graph&g)const{
  if(g.D<0||(g.D&1)||mass!=U(g.D))throw std::runtime_error("guided sparse total defect mismatch");
  U sum=0;for(const auto&entry:badmap){
   const int v=entry.first;const U d=entry.second;
   if(!d||defect(g,v)!=d||g.degree[v]<=0||size_t(v)>=g.adj.size()||g.adj[v].size()!=U(g.degree[v])||
      size_t(v)>=g.target_strength.size()||g.target_strength[v]<=0)
    throw std::runtime_error("guided sparse vertex/adjacency mismatch");
   sum=checked_u128(__uint128_t(sum)+d,"guided sparse total check");
  }
  if(sum!=mass)throw std::runtime_error("guided sparse mass mismatch");
 }
 int draw_first_edge(Engine&e,const Graph&g){
  if(g.D<0||(g.D&1)||mass!=U(g.D)||mass==std::numeric_limits<U>::max())
   throw std::runtime_error("guided first-edge state not synchronized");
  const U m=U(g.edges.size());if(!m)return -1;
   
  if(!mass){if(!badmap.empty())throw std::runtime_error("guided zero mass has cached defects");
   ++background_draws;++e.stat.first_edge_uniform_branch;return int(e.rng.below(m));}
  U draw=e.rng.below(mass+1);
  if(!draw){++background_draws;++e.stat.first_edge_uniform_branch;return int(e.rng.below(m));}
  --draw;
  for(const auto&entry:badmap){
   if(draw<entry.second){const int v=entry.first;
    if(!entry.second||defect(g,v)!=entry.second||g.degree[v]<=0||size_t(v)>=g.adj.size()||g.adj[v].size()!=U(g.degree[v]))
     throw std::runtime_error("guided selected defect vertex is stale");
    ++defect_draws;++e.stat.first_edge_defect_branch;
    return g.adj[v][e.rng.below(U(g.adj[v].size()))];
   }
   draw-=entry.second;
  }
  throw std::runtime_error("guided defect ticket exceeds sparse mass");
 }
 bool draw_rectangle(Engine&e,Graph&g,Rectangle&r){
  const U m=U(g.edges.size());if(m<2){++e.stat.invalid_pairs;return false;}
  const int first=draw_first_edge(e,g);if(first<0||U(first)>=m)throw std::runtime_error("guided first-edge id invalid");
  ++second_uniform_draws;++e.stat.first_edge_uniform_branch;const int second=int(e.rng.below(m));
  const Edge x=g.edges[first],y=g.edges[second];
  if(x.r==y.r||x.c==y.c){++e.stat.invalid_pairs;return false;}
  r={std::min(x.r,y.r),std::max(x.r,y.r),std::min(x.c,y.c),std::max(x.c,y.c)};return true;
 }
};

static I draw_guided_soft_rectangle(Engine&e,Graph&g,Rectangle r,int power){
 if(power<0||power>8||e.opt.kappa||e.opt.anchor_mode!="dual")
  throw std::runtime_error("unsupported guided soft rectangle configuration");
 if(r.i<0||r.j>=g.nr||r.i>=r.j||r.k<0||r.l>=g.nc||r.k>=r.l||g.D<0||(g.D&1))
  throw std::runtime_error("invalid guided soft rectangle state/descriptor");
 const auto old=g.cells(r);const auto bounds=Engine::interval(old);
 const I lo=bounds.first,hi=bounds.second;
 const S128 width=S128(hi)-S128(lo);
 if(width<=0||width>S128(std::numeric_limits<I>::max())||!g.Hproduct(r,0))
  throw std::runtime_error("invalid guided soft rectangle line");
 struct Class{I lower=0,upper=0,D=0;U count=0,m=0,H=0;std::array<U,4>degrees{};mpq_class mass=0;mpz_class tickets=0;};
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
    throw std::runtime_error("guided soft rectangle weight arithmetic");
   before[j]=old[j]>0;after[j]=next[j]>0;old_nz+=before[j];new_nz+=after[j];
  }
  const S128 new_m=S128(old_m)-old_nz+new_nz;
  if(new_m<2||new_m>S128(std::numeric_limits<U>::max()))
   throw std::runtime_error("guided soft rectangle support arithmetic");

  if(e.coverage_cap.requested&&new_m>S128(e.coverage_cap.bound))return;
  const std::array<int,4>changes{
   after[0]+after[1]-before[0]-before[1],
   after[2]+after[3]-before[2]-before[3],
   after[0]+after[2]-before[0]-before[2],
   after[1]+after[3]-before[1]-before[3]};
  S128 new_D=g.D;std::array<U,4>new_degrees{};
  for(size_t j=0;j<4;++j){
   const int v=vertices[j];const S128 new_degree=S128(g.degree[v])+changes[j];
   if(new_degree<=0||new_degree>S128(std::numeric_limits<int>::max()))
    throw std::runtime_error("guided soft rectangle degree arithmetic");
   new_degrees[j]=U(new_degree);new_D-=abs128(S128(g.degree[v])-g.target_degree[v]);
   new_D+=abs128(new_degree-g.target_degree[v]);
  }
  if(new_D<0||new_D>S128(std::numeric_limits<I>::max())||(new_D&1)||abs128(new_D-g.D)>8)
   throw std::runtime_error("guided soft rectangle defect arithmetic");
  const U H=U(after[0]&&after[3])+U(after[1]&&after[2]);
  if(!H)throw std::runtime_error("guided soft rectangle has zero reverse descriptor mass");
  const S128 cardinality=S128(upper)-lower+1;
  if(cardinality<=0||cardinality>S128(std::numeric_limits<U>::max())||count==classes.size())
   throw std::runtime_error("guided soft rectangle class arithmetic");
  Class &c=classes[count++];c.lower=lower;c.upper=upper;c.D=I(new_D);c.count=U(cardinality);c.m=U(new_m);c.H=H;c.degrees=new_degrees;
 };
 append(lo,lo);append(hi,hi);if(width>1)append(lo+1,hi-1);
 if(!count)throw std::runtime_error("guided soft rectangle empty conditional line");
 bool contains_current=false;I minimum_D=classes[0].D;
 for(size_t j=0;j<count;++j){minimum_D=std::min(minimum_D,classes[j].D);contains_current|=classes[j].lower<=0&&0<=classes[j].upper;}
 if(!contains_current)throw std::runtime_error("guided soft rectangle omitted current state");
 mpz_class common_denominator=1,total=0;
 for(size_t j=0;j<count;++j){
  Class &c=classes[j];const S128 difference=S128(c.D)-minimum_D;
  if(difference<0||(difference&1)||difference>8)
   throw std::runtime_error("guided soft rectangle class potential arithmetic");

  mpq_class anchor=rational(mpz_class(2),mpz_class(c.m));
  for(size_t v=0;v<4;++v){
   const S128 d=abs128(S128(c.degrees[v])-g.target_degree[vertices[v]]);
   if(d>S128(std::numeric_limits<U>::max())||!c.degrees[v])
    throw std::runtime_error("guided rectangle vertex fraction arithmetic");
   anchor+=rational(mpz_class(U(d)),mpz_class(c.degrees[v]));
  }
  mpz_class denominator=mpz_class(c.m)*(mpz_class(c.D)+1);
  const unsigned exponent=unsigned(S128(power)*difference/2);
  if(exponent)mpz_mul_2exp(denominator.get_mpz_t(),denominator.get_mpz_t(),exponent);
  c.mass=anchor*rational(mpz_class(c.H),denominator);
  mpz_lcm(common_denominator.get_mpz_t(),common_denominator.get_mpz_t(),c.mass.get_den().get_mpz_t());
 }
 Class *current=nullptr;
 for(size_t j=0;j<count;++j){
  Class &c=classes[j];c.tickets=c.mass.get_num()*(common_denominator/c.mass.get_den());
  if(c.tickets<=0)throw std::runtime_error("guided soft rectangle nonpositive per-state mass");
  total+=mpz_class(c.count)*c.tickets;
  if(c.lower<=0&&0<=c.upper){
   if(current)throw std::runtime_error("guided soft rectangle duplicate delta0 class");
   current=&c;
   if(c.m!=old_m||c.D!=g.D||c.H!=g.Hproduct(r,0))
    throw std::runtime_error("guided soft rectangle current-state factors mismatch");
  }
 }
 if(!current||total<=0)throw std::runtime_error("guided soft rectangle missing current mass");
 const mpz_class old_weight=current->tickets;
 const mpz_class proposal_total=total-old_weight;
 if(proposal_total==0)return 0;
 if(proposal_total<0)throw std::runtime_error("guided soft rectangle negative proposal mass");
 mpz_class draw=zbig(e.rng.below_big(bigz(proposal_total)));
 for(size_t j=0;j<count;++j){
  const Class &c=classes[j];const bool contains_zero=c.lower<=0&&0<=c.upper;
  const U available=c.count-U(contains_zero);
  if(!available)continue;
  const mpz_class group_mass=mpz_class(available)*c.tickets;
  if(draw<group_mass){
   const U rank=available==1?0:e.rng.below(available);
   S128 selected=S128(c.lower)+rank;
    
   if(contains_zero&&selected>=0)++selected;
   if(selected<c.lower||selected>c.upper||selected==0||selected<S128(std::numeric_limits<I>::min())||selected>S128(std::numeric_limits<I>::max()))
    throw std::runtime_error("guided soft rectangle invalid nonzero delta rank");
   const mpz_class reverse_total=total-c.tickets;
   if(reverse_total<=0)throw std::runtime_error("guided soft rectangle nonpositive reverse proposal mass");
   const bool accept=exact_accept(e.rng,rational(proposal_total,reverse_total));
   return accept?I(selected):I(0);
  }
  draw-=group_mass;
 }
 throw std::runtime_error("guided soft rectangle rank beyond proposal mass");
}
