#pragma once

#include "weighted_kernels.hpp"

struct SharedRootGroupedBufferProblem {
 using Allocation=std::vector<std::array<int,3>>;
 struct Group {I weight;std::vector<int>positions;};
 struct Draw {std::vector<int>owners;std::array<I,3>root_weights{};Allocation allocation;U completions=0;};
 std::vector<I>weights;std::array<int,3>quota;std::array<I,3>bound;
 std::vector<Group>groups;std::vector<int>suffix_size,start;
 std::vector<S128>sorted_prefix;
 U dfs_nodes=0,quota_trials=0,quota_prunes=0,bound_prunes=0,feasible_classes=0,reservoir_choices=0,shuffle_draws=0;
 static constexpr int cap=9;
 static U multinomial(int n,const std::array<int,3>&x){
  static constexpr U factorial[10]={1,1,2,6,24,120,720,5040,40320,362880};
  if(n<0||n>cap||x[0]<0||x[1]<0||x[2]<0||x[0]+x[1]+x[2]!=n)throw std::runtime_error("invalid grouped multinomial");
  return factorial[n]/(factorial[x[0]]*factorial[x[1]]*factorial[x[2]]);
 }
 SharedRootGroupedBufferProblem(std::vector<I>w,std::array<int,3>q,std::array<I,3>B):weights(std::move(w)),quota(q),bound(B){
  if(weights.size()>cap)throw std::runtime_error("grouped buffer supports at most9 private labels");
  int sum=0;for(int i=0;i<3;++i){if(quota[i]<0||quota[i]>cap||bound[i]<=0)throw std::runtime_error("invalid grouped quota/bound");sum+=quota[i];}
  if(sum!=int(weights.size()))throw std::runtime_error("grouped quota sum mismatch");
  std::map<I,std::vector<int>>index;
  for(size_t j=0;j<weights.size();++j){if(weights[j]<=0)throw std::runtime_error("nonpositive private weight");index[weights[j]].push_back(int(j));}
  for(const auto&item:index)groups.push_back({item.first,item.second});
  start.push_back(0);sorted_prefix.push_back(0);
  for(const auto&group:groups){for(size_t j=0;j<group.positions.size();++j)sorted_prefix.push_back(sorted_prefix.back()+S128(group.weight));start.push_back(int(sorted_prefix.size())-1);}
  for(int j:start)suffix_size.push_back(int(weights.size())-j);
 }
  
 S128 suffix_min(int g,int k)const{return sorted_prefix.at(start.at(g)+k)-sorted_prefix.at(start.at(g));}
 template<class Visitor>void enumerate(Visitor visitor){
  Allocation allocation(groups.size());std::array<int,3>used{};std::array<S128,3>load{};
  auto visit=[&](auto&&self,int g,U mass)->void{
   ++dfs_nodes;int remaining=suffix_size[g];
   for(int i=0;i<3;++i){int need=quota[i]-used[i];if(need<0||need>remaining){++quota_prunes;return;}
    if(load[i]+suffix_min(g,need)>=S128(bound[i])){++bound_prunes;return;}}
   if(g==int(groups.size())){
    if(used!=quota)throw std::runtime_error("grouped terminal quota mismatch");std::array<I,3>root{};
    for(int i=0;i<3;++i){S128 r=S128(bound[i])-load[i];if(r<=0||r>std::numeric_limits<I>::max())throw std::runtime_error("invalid grouped residual");root[i]=I(r);}
    ++feasible_classes;visitor(allocation,mass,root);return;
   }
   const auto&group=groups[g];int n=int(group.positions.size());
   for(int x0=0;x0<=std::min(n,quota[0]-used[0]);++x0)for(int x1=0;x1<=std::min(n-x0,quota[1]-used[1]);++x1){
    std::array<int,3>x{x0,x1,n-x0-x1};++quota_trials;
    if(x[2]>quota[2]-used[2]){++quota_prunes;continue;}
    bool possible=true;for(int i=0;i<3;++i)if(load[i]+S128(group.weight)*x[i]>=S128(bound[i]))possible=false;
    if(!possible){++bound_prunes;continue;}
    allocation[g]=x;U ways=multinomial(n,x);

    __uint128_t product=__uint128_t(mass)*ways;if(product>1680)throw std::runtime_error("grouped mass exceeds cap9 labeled bound");
    for(int i=0;i<3;++i){used[i]+=x[i];load[i]+=S128(group.weight)*x[i];}
    self(self,g+1,U(product));
    for(int i=0;i<3;++i){used[i]-=x[i];load[i]-=S128(group.weight)*x[i];}
   }
  };visit(visit,0,1);
 }
 template<class Random>std::vector<int>shuffle_owners(const Allocation&allocation,Random&random){
  if(allocation.size()!=groups.size())throw std::runtime_error("grouped allocation size mismatch");
  std::vector<int>owners(weights.size(),-1);
  for(size_t g=0;g<groups.size();++g){const auto&group=groups[g];const auto&x=allocation[g];int n=int(group.positions.size());U ways=multinomial(n,x);
   std::vector<int>positions=group.positions;

   if(ways>1)for(int j=0;j+1<n;++j){int selected=j+int(random.below(n-j));std::swap(positions[j],positions[selected]);++shuffle_draws;}
   int offset=0;for(int i=0;i<3;++i)for(int j=0;j<x[i];++j)owners[positions[offset++]]=i;
   if(offset!=n)throw std::runtime_error("grouped shuffle quota mismatch");
  }
  return owners;
 }
 template<class Random>Draw draw(Random&random){
  Draw result;enumerate([&](const Allocation&a,U mass,const std::array<I,3>&root){
   if(result.completions>1680-mass)throw std::runtime_error("grouped total exceeds cap9 labeled bound");
   result.completions+=mass;++reservoir_choices;
   if(random.below(result.completions)<mass){result.allocation=a;result.root_weights=root;}
  });
  if(!result.completions)throw std::runtime_error("current grouped buffer completion missing");
  result.owners=shuffle_owners(result.allocation,random);return result;
 }
};
struct SharedRootGroupedBufferKernel {
 std::array<std::vector<int>,2> roots;
 U calls=0,empty_roots=0,empty_private=0,singletons=0,changed=0;
 U owner_changed_calls=0,root_weight_changed_calls=0,feasible_total=0,dfs_nodes=0,scan_visits=0;
 U groups_total=0,groups_max=0,quota_classes=0,quota_trials=0,quota_prunes=0,bound_prunes=0,reservoir_choices=0,shuffle_draws=0;
 static constexpr int cap=9;
 explicit SharedRootGroupedBufferKernel(const Graph&g){
  for(int c=0;c<g.nc;++c)if(g.target_degree[g.nr+c]>=3)roots[0].push_back(c);
  for(int r=0;r<g.nr;++r)if(g.target_degree[r]>=3)roots[1].push_back(r);
 }
 bool step(Engine&e,Graph&g){
  ++calls;++e.stat.work;if(g.D)throw std::runtime_error("buffer needs exact degree state");
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
  std::vector<int>cols;for(int c:united){int arity=0;for(int i=0;i<3;++i)arity+=value(i,c)>0;if(c!=root&&arity==1)cols.push_back(c);}
  if(cols.empty()){++empty_private;return false;}
  if(cols.size()>cap){for(int k=0;k<cap;++k)std::swap(cols[k],cols[k+e.rng.below(cols.size()-k)]);cols.resize(cap);std::sort(cols.begin(),cols.end());}
  int m=int(cols.size());std::vector<I>weights(m);std::vector<int>current(m),chosen(m);
  std::array<int,3>quota{};std::array<I,3>bound{},newroot{},oldroot{};
  for(int i=0;i<3;++i)bound[i]=oldroot[i]=value(i,root);
  for(int j=0;j<m;++j){for(int i=0;i<3;++i){I w=value(i,cols[j]);if(w){weights[j]=w;current[j]=i;++quota[i];
    S128 b=S128(bound[i])+w;if(b>std::numeric_limits<I>::max())throw std::runtime_error("buffer strength overflow");bound[i]=I(b);}}}
  SharedRootGroupedBufferProblem problem(weights,quota,bound);auto draw=problem.draw(e.rng);
  chosen=std::move(draw.owners);newroot=draw.root_weights;U count=draw.completions;
  dfs_nodes+=problem.dfs_nodes;groups_total+=problem.groups.size();groups_max=std::max(groups_max,U(problem.groups.size()));
  quota_classes+=problem.feasible_classes;quota_trials+=problem.quota_trials;quota_prunes+=problem.quota_prunes;bound_prunes+=problem.bound_prunes;
  reservoir_choices+=problem.reservoir_choices;shuffle_draws+=problem.shuffle_draws;
  feasible_total+=count;if(count==1)++singletons;
  bool owner_change=chosen!=current,weight_change=newroot!=oldroot;
  if(!owner_change&&!weight_change)return false;
  for(int j=0;j<m;++j)for(int i=0;i<3;++i)put(i,cols[j],chosen[j]==i?weights[j]:0);
  for(int i=0;i<3;++i)put(i,root,newroot[i]);
  ++changed;++e.stat.changed_outer;owner_changed_calls+=owner_change;root_weight_changed_calls+=weight_change;
  return true;
 }
};
