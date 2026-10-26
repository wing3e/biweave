#pragma once

#include "grouped_buffer_kernel.hpp"
struct SharedRootGroupedRankOneProblem {
 using Allocation=SharedRootGroupedBufferProblem::Allocation;
 struct Draw {
  std::vector<int>owners;std::array<I,3>root_weights{},double_weights{};
  Allocation allocation;std::array<int,3>quota{};int a=-1,b=-1;I lo=0,hi=0;
  Big completions;U supports=0;
 };
 std::vector<I>weights;std::array<int,3>h;std::array<I,3>bound;I C;
 U dfs_nodes=0,groups_total=0,groups_max=0,quota_classes=0,quota_trials=0,quota_prunes=0,bound_prunes=0,reservoir_choices=0,shuffle_draws=0;
 SharedRootGroupedRankOneProblem(std::vector<I>w,std::array<int,3>h_,std::array<I,3>B,I C_):weights(std::move(w)),h(h_),bound(B),C(C_){
  if(weights.size()>9||C<2)throw std::runtime_error("invalid grouped rankone width/strength");
  int sum=0;for(int i=0;i<3;++i){if(h[i]<0||h[i]>int(weights.size())+1||bound[i]<=0)throw std::runtime_error("invalid grouped rankone row constraints");sum+=h[i];}
  if(sum!=int(weights.size())+2)throw std::runtime_error("grouped rankone degree sum mismatch");
  for(I w:weights)if(w<=0)throw std::runtime_error("nonpositive rankone private weight");
 }
 template<class Visitor>void enumerate(Visitor visitor){
  for(int a=0;a<3;++a)for(int b=a+1;b<3;++b){
   std::array<int,3>quota=h;--quota[a];--quota[b];bool possible=true;
   for(int i=0;i<3;++i)if(quota[i]<0||quota[i]>int(weights.size()))possible=false;
   if(!possible)continue;
   SharedRootGroupedBufferProblem problem(weights,quota,bound);
   groups_total+=problem.groups.size();groups_max=std::max(groups_max,U(problem.groups.size()));
   problem.enumerate([&](const Allocation&allocation,U ways,const std::array<I,3>&residual){
    S128 lo=std::max<S128>(1,S128(C)-residual[b]+1),hi=std::min<S128>(S128(C)-1,S128(residual[a])-1);
    if(lo>hi)return;
    Big mass(U(hi-lo+1));mass*=ways;++quota_classes;
    visitor(a,b,quota,allocation,ways,residual,I(lo),I(hi),mass);
   });
   dfs_nodes+=problem.dfs_nodes;quota_trials+=problem.quota_trials;quota_prunes+=problem.quota_prunes;bound_prunes+=problem.bound_prunes;
  }
 }
 template<class Random>Draw draw(Random&random){
  Draw result;enumerate([&](int a,int b,const auto&quota,const Allocation&allocation,U ways,const auto&residual,I lo,I hi,const Big&mass){
   result.completions+=mass;result.supports+=ways;++reservoir_choices;
   if(random.below_big(result.completions)<mass){result.a=a;result.b=b;result.quota=quota;result.allocation=allocation;result.root_weights=residual;result.lo=lo;result.hi=hi;}
  });
  if(result.completions==Big(0)||result.a<0)throw std::runtime_error("current grouped rankone completion missing");
  SharedRootGroupedBufferProblem decoder(weights,result.quota,bound);
  result.owners=decoder.shuffle_owners(result.allocation,random);shuffle_draws+=decoder.shuffle_draws;
  I z=random.integer(result.lo,result.hi);result.double_weights[result.a]=z;result.double_weights[result.b]=C-z;
  result.root_weights[result.a]-=z;result.root_weights[result.b]-=C-z;
  for(I w:result.root_weights)if(w<=0)throw std::runtime_error("nonpositive grouped root residual");
  return result;
 }
};
struct SharedRootGroupedRankOneKernel {
 std::array<std::vector<int>,2>roots;
 U calls=0,empty_roots=0,empty_double=0,empty_private=0,changed=0,dfs_nodes=0,scan_visits=0;
  
 U feasible_total=0,feasible_supports=0,owner_changed_calls=0,double_support_changed_calls=0,root_weight_changed_calls=0;
 U rankzero_calls=0,rankone_calls=0,singletons=0,groups_total=0,groups_max=0,quota_classes=0,quota_trials=0,quota_prunes=0,bound_prunes=0,reservoir_choices=0,shuffle_draws=0;
 Big completion_total;
 static constexpr int cap=9;
 explicit SharedRootGroupedRankOneKernel(const Graph&g){
  for(int c=0;c<g.nc;++c)if(g.target_degree[g.nr+c]>=3)roots[0].push_back(c);
  for(int r=0;r<g.nr;++r)if(g.target_degree[r]>=3)roots[1].push_back(r);
 }
 bool step(Engine&e,Graph&g,bool allow_rankzero=false){
  ++calls;++e.stat.work;if(g.D)throw std::runtime_error("rankone buffer needs exact degree state");
  int o=int(e.rng.below(2));if(roots[o].empty()){++empty_roots;return false;}
  int root=roots[o][e.rng.below(roots[o].size())],rv=o?root:g.nr+root;
  const auto&adj=g.adj[rv];int d=int(adj.size());if(d<3)throw std::runtime_error("root degree changed");
  std::array<int,3>ix{},nodes{};
  for(int k=0;k<3;++k){int z=int(e.rng.below(d-k));auto used=ix;std::sort(used.begin(),used.begin()+k);
   for(int j=0;j<k;++j)if(z>=used[j])++z;ix[k]=z;const auto&ed=g.edges[adj[z]];nodes[k]=o?ed.c:ed.r;}
  std::sort(nodes.begin(),nodes.end());
  auto value=[&](int i,int c){return o?g.value(c,nodes[i]):g.value(nodes[i],c);};
  auto put=[&](int i,int c,I w){if(o)g.set_raw(c,nodes[i],w);else g.set_raw(nodes[i],c,w);};
  std::vector<int>united;
  for(int node:nodes){int v=o?g.nr+node:node;for(int id:g.adj[v]){const auto&ed=g.edges[id];united.push_back(o?ed.r:ed.c);++scan_visits;}}
  std::sort(united.begin(),united.end());united.erase(std::unique(united.begin(),united.end()),united.end());
  std::vector<int>cols,doubles;
  for(int c:united){int arity=0;for(int i=0;i<3;++i)arity+=value(i,c)>0;
   if(c!=root&&arity==1)cols.push_back(c);else if(c!=root&&arity==2)doubles.push_back(c);}
  bool rankzero=doubles.empty();if(rankzero){++empty_double;if(!allow_rankzero)return false;if(cols.empty()){++empty_private;return false;}}
  int shared=rankzero?-1:doubles[e.rng.below(doubles.size())];
  if(cols.size()>cap){for(int k=0;k<cap;++k)std::swap(cols[k],cols[k+e.rng.below(cols.size()-k)]);cols.resize(cap);std::sort(cols.begin(),cols.end());}
  int m=int(cols.size());std::vector<I>weights(m);std::vector<int>current(m),chosen(m);
  std::array<int,3>h{};std::array<I,3>bound{},newroot{},oldroot{},olddouble{},newdouble{};
  auto add_checked=[&](I&a,I w){S128 s=S128(a)+w;if(s>std::numeric_limits<I>::max())throw std::runtime_error("rankone strength overflow");a=I(s);};
  I C=0;for(int i=0;i<3;++i){bound[i]=oldroot[i]=value(i,root);olddouble[i]=rankzero?0:value(i,shared);
   if(olddouble[i]){++h[i];add_checked(bound[i],olddouble[i]);add_checked(C,olddouble[i]);}}
  if(!rankzero&&C<2)throw std::runtime_error("two-neighbor column needs strength >=2");
  for(int j=0;j<m;++j)for(int i=0;i<3;++i){I w=value(i,cols[j]);if(w){weights[j]=w;current[j]=i;++h[i];add_checked(bound[i],w);}}
  Big count;U supports=0;
  if(rankzero){
   ++rankzero_calls;SharedRootGroupedBufferProblem problem(weights,h,bound);auto draw=problem.draw(e.rng);
   chosen=std::move(draw.owners);newroot=draw.root_weights;count=Big(draw.completions);supports=draw.completions;
   dfs_nodes+=problem.dfs_nodes;groups_total+=problem.groups.size();groups_max=std::max(groups_max,U(problem.groups.size()));quota_classes+=problem.feasible_classes;
   quota_trials+=problem.quota_trials;quota_prunes+=problem.quota_prunes;bound_prunes+=problem.bound_prunes;reservoir_choices+=problem.reservoir_choices;shuffle_draws+=problem.shuffle_draws;
  }else{
   ++rankone_calls;SharedRootGroupedRankOneProblem problem(weights,h,bound,C);auto draw=problem.draw(e.rng);
   chosen=std::move(draw.owners);newroot=draw.root_weights;newdouble=draw.double_weights;count=draw.completions;supports=draw.supports;
   dfs_nodes+=problem.dfs_nodes;groups_total+=problem.groups_total;groups_max=std::max(groups_max,problem.groups_max);quota_classes+=problem.quota_classes;
   quota_trials+=problem.quota_trials;quota_prunes+=problem.quota_prunes;bound_prunes+=problem.bound_prunes;reservoir_choices+=problem.reservoir_choices;shuffle_draws+=problem.shuffle_draws;
  }
  completion_total+=count;feasible_supports+=supports;feasible_total+=supports;if(count==Big(1))++singletons;
  bool owner_change=chosen!=current,double_support_change=false;
  for(int i=0;i<3;++i)double_support_change|=(newdouble[i]>0)!=(olddouble[i]>0);
  if(!owner_change&&newroot==oldroot&&newdouble==olddouble)return false;
  for(int j=0;j<m;++j)for(int i=0;i<3;++i)put(i,cols[j],chosen[j]==i?weights[j]:0);
  for(int i=0;i<3;++i){put(i,root,newroot[i]);if(!rankzero)put(i,shared,newdouble[i]);}
  ++changed;++e.stat.changed_outer;owner_changed_calls+=owner_change;double_support_changed_calls+=double_support_change;root_weight_changed_calls+=(newroot!=oldroot);return true;
 }
};
 
struct SharedRootGroupedLowRankKernel:SharedRootGroupedRankOneKernel {
 explicit SharedRootGroupedLowRankKernel(const Graph&g):SharedRootGroupedRankOneKernel(g){}
 bool step(Engine&e,Graph&g){return SharedRootGroupedRankOneKernel::step(e,g,true);}
};
