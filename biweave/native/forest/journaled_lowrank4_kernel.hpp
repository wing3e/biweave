#pragma once

#include "grouped_rankone_kernel.hpp"
struct JournaledLowrank4Kernel:SharedRootGroupedRankOneKernel {
 struct CellUndo {int r,c;I old;};
 std::vector<CellUndo> undo;
 void journal_put(Graph&g,int r,int c,I w){undo.push_back({r,c,g.value(r,c)});g.set_raw(r,c,w);}
 void rollback_journal(Graph&g){for(auto it=undo.rbegin();it!=undo.rend();++it)g.set_raw(it->r,it->c,it->old);}

 struct Scratch {
  std::vector<U>stamp;std::vector<uint8_t>mask;std::vector<I>first_weight;
  std::vector<int>touched,cols,doubles;U epoch=0;
  explicit Scratch(int n=0):stamp(n,0),mask(n,0),first_weight(n,0){}
  bool next_epoch(){bool reset=false;if(epoch==std::numeric_limits<U>::max()){std::fill(stamp.begin(),stamp.end(),U(0));epoch=1;reset=true;}else ++epoch;
   touched.clear();cols.clear();doubles.clear();return reset;
  }
  U estimated_bytes()const{return U(stamp.capacity())*sizeof(U)+U(mask.capacity())*sizeof(uint8_t)+U(first_weight.capacity())*sizeof(I)+U(touched.capacity()+cols.capacity()+doubles.capacity())*sizeof(int);}
 };
 std::array<Scratch,2>scratch;U selector_classifications=0,selector_epoch_resets=0;
 std::array<std::vector<int>,2> active;
 U fallback_calls=0,fallback_changed=0,fallback_too_few=0,fallback_empty_private=0,fallback_singletons=0,fallback_complete_assignments=0;
 explicit JournaledLowrank4Kernel(const Graph&g):SharedRootGroupedRankOneKernel(g),scratch{Scratch(g.nc),Scratch(g.nr)}{
  for(int o=0;o<2;++o){int n=o?g.nc:g.nr,offset=o?g.nr:0;for(int v=0;v<n;++v)if(g.target_degree[offset+v]>0)active[o].push_back(v);}
 }

 bool private_four(Engine&e,Graph&g,int o){
  ++fallback_calls;const auto&pool=active[o];const int r=std::min(4,int(pool.size()));
  if(r<2){++fallback_too_few;return false;}
   
  std::vector<int>selected;
  for(U j=U(pool.size())-U(r);j<U(pool.size());++j){int k=int(e.rng.below(j+1));if(std::find(selected.begin(),selected.end(),k)!=selected.end())k=int(j);selected.push_back(k);}
  std::vector<int>nodes(r);for(int i=0;i<r;++i)nodes[i]=pool[selected[i]];std::sort(nodes.begin(),nodes.end());
  auto value=[&](int i,int c){return o?g.value(c,nodes[i]):g.value(nodes[i],c);};
  auto put=[&](int i,int c,I w){if(o)journal_put(g,c,nodes[i],w);else journal_put(g,nodes[i],c,w);};
  auto&tmp=scratch[o];if(tmp.next_epoch())++selector_epoch_resets;
  for(int i=0;i<r;++i){int v=o?g.nr+nodes[i]:nodes[i];for(int id:g.adj[v]){const auto&ed=g.edges[id];int c=o?ed.r:ed.c;++scan_visits;
   if(tmp.stamp[c]!=tmp.epoch){tmp.stamp[c]=tmp.epoch;tmp.mask[c]=0;tmp.touched.push_back(c);}tmp.mask[c]|=uint8_t(1u<<i);}}
  auto&cols=tmp.cols;for(int c:tmp.touched){++selector_classifications;if(__builtin_popcount(unsigned(tmp.mask[c]))==1)cols.push_back(c);}
  std::sort(cols.begin(),cols.end());
  constexpr int private_cap=8;  
  if(cols.size()>private_cap){for(int k=0;k<private_cap;++k)std::swap(cols[k],cols[k+e.rng.below(cols.size()-k)]);cols.resize(private_cap);std::sort(cols.begin(),cols.end());}
  if(cols.empty()){++fallback_empty_private;return false;}
  std::vector<std::vector<I>>rows(r,std::vector<I>(cols.size()));for(int i=0;i<r;++i)for(size_t j=0;j<cols.size();++j)rows[i][j]=value(i,cols[j]);
  UnitCapacityPrivateV19 problem(rows);fallback_complete_assignments+=problem.total;fallback_singletons+=problem.total==1;
  auto draw=problem.draw(e.rng,false);  
  bool differs=false;for(int i=0;i<r;++i)for(size_t j=0;j<cols.size();++j)differs|=rows[i][j]!=draw[i][j];
  if(!differs)return false;
  for(int i=0;i<r;++i)for(size_t j=0;j<cols.size();++j)put(i,cols[j],draw[i][j]);
  ++changed;++e.stat.changed_outer;++fallback_changed;return true;
 }
 static constexpr int cap=6;  
 U selector_scratch_bytes()const{return scratch[0].estimated_bytes()+scratch[1].estimated_bytes();}
 bool step(Engine&e,Graph&g){
  undo.clear();const bool allow_rankzero=true;
  ++calls;++e.stat.work;if(g.D)throw std::runtime_error("rankone buffer needs exact degree state");
  int o=int(e.rng.below(2));if(roots[o].empty()){++empty_roots;return private_four(e,g,o);}
  int root=roots[o][e.rng.below(roots[o].size())],rv=o?root:g.nr+root;
  const auto&adj=g.adj[rv];int d=int(adj.size());if(d<3)throw std::runtime_error("root degree changed");
  std::array<int,3>ix{},nodes{};
  for(int k=0;k<3;++k){int z=int(e.rng.below(d-k));auto used=ix;std::sort(used.begin(),used.begin()+k);
   for(int j=0;j<k;++j)if(z>=used[j])++z;ix[k]=z;const auto&ed=g.edges[adj[z]];nodes[k]=o?ed.c:ed.r;}
  std::sort(nodes.begin(),nodes.end());
  auto value=[&](int i,int c){return o?g.value(c,nodes[i]):g.value(nodes[i],c);};
  auto put=[&](int i,int c,I w){if(o)journal_put(g,c,nodes[i],w);else journal_put(g,nodes[i],c,w);};
  auto&tmp=scratch[o];if(tmp.next_epoch())++selector_epoch_resets;
   
  for(int i=0;i<3;++i){int v=o?g.nr+nodes[i]:nodes[i];for(int id:g.adj[v]){const auto&ed=g.edges[id];int c=o?ed.r:ed.c;++scan_visits;
   if(tmp.stamp[c]!=tmp.epoch){tmp.stamp[c]=tmp.epoch;tmp.mask[c]=0;tmp.first_weight[c]=ed.w;tmp.touched.push_back(c);}
   tmp.mask[c]|=uint8_t(1u<<i);
  }}
  auto&cols=tmp.cols;auto&doubles=tmp.doubles;
  for(int c:tmp.touched){++selector_classifications;if(c==root)continue;int arity=__builtin_popcount(unsigned(tmp.mask[c]));
   if(arity==1)cols.push_back(c);else if(arity==2)doubles.push_back(c);}
   
  std::sort(cols.begin(),cols.end());std::sort(doubles.begin(),doubles.end());
  bool rankzero=doubles.empty();if(rankzero){++empty_double;if(!allow_rankzero)return false;if(cols.empty()){++empty_private;return false;}}
  int shared=rankzero?-1:doubles[e.rng.below(doubles.size())];
  if(cols.size()>cap){for(int k=0;k<cap;++k)std::swap(cols[k],cols[k+e.rng.below(cols.size()-k)]);cols.resize(cap);std::sort(cols.begin(),cols.end());}
  int m=int(cols.size());std::vector<I>weights(m);std::vector<int>current(m),chosen(m);
  std::array<int,3>h{};std::array<I,3>bound{},newroot{},oldroot{},olddouble{},newdouble{};
  auto add_checked=[&](I&a,I w){S128 s=S128(a)+w;if(s>std::numeric_limits<I>::max())throw std::runtime_error("rankone strength overflow");a=I(s);};
  I C=0;for(int i=0;i<3;++i){bound[i]=oldroot[i]=value(i,root);olddouble[i]=rankzero?0:value(i,shared);
   if(olddouble[i]){++h[i];add_checked(bound[i],olddouble[i]);add_checked(C,olddouble[i]);}}
  if(!rankzero&&C<2)throw std::runtime_error("two-neighbor column needs strength >=2");
  for(int j=0;j<m;++j){int c=cols[j];unsigned mask=tmp.mask[c];
   if(tmp.stamp[c]!=tmp.epoch||__builtin_popcount(mask)!=1)throw std::runtime_error("stale/nonprivate selector scratch");
   int i=__builtin_ctz(mask);I w=tmp.first_weight[c];weights[j]=w;current[j]=i;++h[i];add_checked(bound[i],w);
  }
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
