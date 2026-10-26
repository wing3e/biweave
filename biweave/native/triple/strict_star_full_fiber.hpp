#pragma once
#include "grouped_two_problem.hpp"
#include <memory>

struct StrictStarFullFiber {
 bool requested=false,certificate=false,active=false;int orientation=-1,hub=-1;
 std::string reason="not_requested";std::vector<int>actors,leaves,actor_position;
 std::vector<I>leaf_weights,beta;std::vector<U>d,cap,initial_high;
 std::vector<size_t>low_labels,high_labels;I low=0,high=0;
 std::unique_ptr<grouped_two::GroupedTwoProblem>problem;
 U count_builds=0,cells_bound=0,work_bound=0,bits_bound=0,payload_estimate=0,cached_cells=0,cached_bits=0,relative_normalizer_bits=0;
 U calls=0,profile_draws=0,fixed_class_calls=0,changed_profiles=0,changed_roots=0,changed_labels=0,moved_labels=0,cell_writes=0;
 bool deficit=false;U coordinate_target=0;
 int actor_vertex(const Graph&g,int a)const{return orientation?g.nr+a:a;}
 int object_vertex(const Graph&g,int c)const{return orientation?c:g.nr+c;}
 std::pair<int,int>cell(int a,int c)const{return orientation?std::make_pair(c,a):std::make_pair(a,c);}
 I value(const Graph&g,int a,int c)const{auto p=cell(a,c);return g.value(p.first,p.second);}
 bool detect_axis(const Graph&g,int o){
  const int na=o?g.nc:g.nr,no=o?g.nr:g.nc,ao=o?g.nr:0,oo=o?0:g.nr;
  int root=-1;size_t active_actors=0;
  for(int a=0;a<na;++a){if(g.target_degree[ao+a]>0)++active_actors;else if(g.target_strength[ao+a]!=0)throw std::runtime_error("strict star isolate strength");}
  for(int c=0;c<no;++c){const int q=g.target_degree[oo+c];if(q>1){if(root>=0)return false;root=c;}else if(q==0&&g.target_strength[oo+c]!=0)throw std::runtime_error("strict star isolate strength");}
  if(root<0||U(g.target_degree[oo+root])!=active_actors)return false;
  std::set<I>weights;for(int c=0;c<no;++c)if(c!=root&&g.target_degree[oo+c]>0){if(g.target_degree[oo+c]!=1)return false;weights.insert(g.target_strength[oo+c]);}
  if(weights.size()!=2)return false;
  orientation=o;hub=root;low=*weights.begin();high=*weights.rbegin();
  actor_position.assign(na,-1);
  for(int a=0;a<na;++a)if(g.target_degree[ao+a]>0){actor_position[a]=int(actors.size());actors.push_back(a);d.push_back(U(g.target_degree[ao+a]-1));beta.push_back(g.target_strength[ao+a]);}
  for(int c=0;c<no;++c)if(c!=root&&g.target_degree[oo+c]>0){leaves.push_back(c);leaf_weights.push_back(g.target_strength[oo+c]);size_t j=leaves.size()-1;(leaf_weights.back()==low?low_labels:high_labels).push_back(j);}
  cap.resize(actors.size());initial_high.assign(actors.size(),0);U quota=0;
  for(size_t i=0;i<actors.size();++i){const S128 spare=S128(beta[i])-S128(low)*S128(d[i])-1;if(spare<0)throw std::runtime_error("strict star invalid root ledger");const S128 c=std::min<S128>(S128(d[i]),spare/(S128(high)-low));cap[i]=U(c);quota+=d[i];if(value(g,actors[i],hub)<=0)throw std::runtime_error("strict star hub missing forced edge");}
  if(quota!=leaves.size())throw std::runtime_error("strict star quota total");
  std::vector<U>live_quota(actors.size());std::vector<S128>live_beta(actors.size());
  for(size_t i=0;i<actors.size();++i)live_beta[i]=value(g,actors[i],hub);
  for(size_t j=0;j<leaves.size();++j){const auto&adj=g.adj[object_vertex(g,leaves[j])];if(adj.size()!=1)throw std::runtime_error("strict star live leaf degree");const Edge ed=g.edges[adj[0]];const int a=orientation?ed.c:ed.r;const int obj=orientation?ed.r:ed.c;if(obj!=leaves[j]||ed.w!=leaf_weights[j]||a<0||a>=na||actor_position[a]<0)throw std::runtime_error("strict star forced leaf weight/owner");const size_t i=size_t(actor_position[a]);++live_quota[i];live_beta[i]+=ed.w;if(ed.w==high)++initial_high[i];}
  for(size_t i=0;i<actors.size();++i)if(live_quota[i]!=d[i]||live_beta[i]!=beta[i]||initial_high[i]>cap[i])throw std::runtime_error("strict star initial fiber ledger");
  return true;
 }
 void initialize(const Graph&g,bool want,bool build_counts){
  requested=want;if(!want){reason="not_requested";return;}reason="not_two_weight_strict_star";
  try{for(int o=0;o<2;++o)if(detect_axis(g,o)){certificate=true;break;}if(!certificate)return;
   reason="certificate_only";if(!build_counts)return;
   ++count_builds;problem=std::make_unique<grouped_two::GroupedTwoProblem>();problem->initialize(d,cap,high_labels.size());
   cells_bound=problem->cells_bound;work_bound=problem->work_bound;bits_bound=problem->bits_bound;payload_estimate=problem->estimated_bytes;deficit=problem->deficit;coordinate_target=problem->target;
   if(!problem->active){reason=problem->reason;problem.reset();return;}
   cached_cells=problem->cached_cells();cached_bits=problem->maximum_cached_bits();relative_normalizer_bits=mpz_sizeinbase(problem->suffix[0].value[problem->target].get_mpz_t(),2);active=true;reason="compiled_complete_fiber";
  }catch(const std::bad_alloc&){problem.reset();active=false;reason="allocation_failure";}
 }

 bool commit(Graph&g,const std::vector<size_t>&owner,const std::vector<U>&h){
  if(!active||owner.size()!=leaves.size()||h.size()!=actors.size())throw std::runtime_error("strict star commit shape");
  std::vector<U>new_d(actors.size()),new_h(actors.size()),old_d(actors.size()),old_h(actors.size());
  std::vector<S128>new_load(actors.size()),old_load(actors.size());std::vector<I>new_root(actors.size());std::vector<int>old_owner(leaves.size());
  for(size_t j=0;j<leaves.size();++j){if(owner[j]>=actors.size())throw std::runtime_error("strict star new owner");const size_t i=owner[j];++new_d[i];new_load[i]+=leaf_weights[j];new_h[i]+=leaf_weights[j]==high;
   const auto&adj=g.adj[object_vertex(g,leaves[j])];if(adj.size()!=1)throw std::runtime_error("strict star live commit leaf degree");const Edge ed=g.edges[adj[0]];const int a=orientation?ed.c:ed.r;if((orientation?ed.r:ed.c)!=leaves[j]||ed.w!=leaf_weights[j]||a<0||a>=int(actor_position.size())||actor_position[a]<0)throw std::runtime_error("strict star stale owner");old_owner[j]=a;const size_t oi=size_t(actor_position[a]);++old_d[oi];old_load[oi]+=ed.w;old_h[oi]+=ed.w==high;
  }
  bool roots_changed=false,profile_changed=false,labels_changed=false;
  for(size_t i=0;i<actors.size();++i){if(new_d[i]!=d[i]||new_h[i]!=h[i]||h[i]>cap[i]||old_d[i]!=d[i]||old_load[i]+value(g,actors[i],hub)!=beta[i])throw std::runtime_error("strict star complete ledger mismatch");const S128 r=S128(beta[i])-new_load[i];if(r<1||r>std::numeric_limits<I>::max())throw std::runtime_error("strict star positive root range");new_root[i]=I(r);roots_changed|=new_root[i]!=value(g,actors[i],hub);profile_changed|=h[i]!=old_h[i];}
  for(size_t j=0;j<leaves.size();++j)if(old_owner[j]!=actors[owner[j]]){labels_changed=true;++moved_labels;auto a=cell(old_owner[j],leaves[j]),b=cell(actors[owner[j]],leaves[j]);g.set_raw(a.first,a.second,0);g.set_raw(b.first,b.second,leaf_weights[j]);cell_writes+=2;}
  for(size_t i=0;i<actors.size();++i){auto p=cell(actors[i],hub);if(g.value(p.first,p.second)!=new_root[i]){g.set_raw(p.first,p.second,new_root[i]);++cell_writes;}}
  changed_profiles+=profile_changed;changed_roots+=roots_changed;changed_labels+=labels_changed;return labels_changed||roots_changed;
 }
 bool step(Engine&e,Graph&g,bool fixed_class){
  if(!active)throw std::runtime_error("strict star inactive step");++calls;std::vector<U>h;
  if(fixed_class){++fixed_class_calls;h=initial_high;}else{++profile_draws;h=problem->draw([&](const mpz_class&n){return zbig(e.rng.below_big(bigz(n)));});}
  std::vector<size_t>owner(leaves.size());
  auto partition=[&](const std::vector<size_t>&labels,bool high_class){std::vector<size_t>order=labels;for(size_t k=order.size();k>1;--k)std::swap(order[k-1],order[size_t(e.rng.below(k))]);size_t at=0;for(size_t i=0;i<actors.size();++i){U quota=high_class?h[i]:d[i]-h[i];for(U j=0;j<quota;++j){if(at>=order.size())throw std::runtime_error("strict star class quota overflow");owner[order[at++]]=i;}}if(at!=order.size())throw std::runtime_error("strict star class quota residue");};
  partition(low_labels,false);partition(high_labels,true);bool changed=commit(g,owner,h);++e.stat.work;e.stat.changed_outer+=changed;return changed;
 }
 void metadata(std::ostream&f,bool strict_requested,bool fixed_class)const{
  f<<"\"strict_star_requested\":"<<(strict_requested?"true":"false")<<",\"strict_star_certificate\":"<<(certificate?"true":"false")<<",\"strict_star_active\":"<<(active?"true":"false")<<",\"strict_star_whole_IID\":"<<((active&&!fixed_class)?"true":"false")<<",\"strict_star_reason\":\""<<reason<<"\",\"strict_star_orientation\":"<<orientation<<",\"strict_star_hub\":"<<hub<<",\"strict_star_profile_update\":\""<<(fixed_class?"fixed_class":"exact")<<"\",\"STAR_actors\":"<<actors.size()<<",\"STAR_leaves\":"<<leaves.size()<<",\"STAR_high_labels\":"<<high_labels.size()<<",\"STAR_low_weight\":"<<low<<",\"STAR_high_weight\":"<<high<<",\"STAR_count_builds\":"<<count_builds<<",\"STAR_cells_bound\":"<<cells_bound<<",\"STAR_work_proxy\":"<<work_bound<<",\"STAR_bits_bound\":"<<bits_bound<<",\"STAR_count_payload_estimate\":"<<payload_estimate<<",\"STAR_cached_cells\":"<<cached_cells<<",\"STAR_cached_max_bits\":"<<cached_bits<<",\"STAR_relative_normalizer_bits\":"<<relative_normalizer_bits<<",\"STAR_deficit_coordinate\":"<<(deficit?"true":"false")<<",\"STAR_coordinate_target\":"<<coordinate_target<<",\"STAR_calls\":"<<calls<<",\"STAR_profile_draws\":"<<profile_draws<<",\"STAR_fixed_class_calls\":"<<fixed_class_calls<<",\"STAR_changed_profiles\":"<<changed_profiles<<",\"STAR_changed_roots\":"<<changed_roots<<",\"STAR_changed_labels\":"<<changed_labels<<",\"STAR_moved_labels\":"<<moved_labels<<",\"STAR_cell_writes\":"<<cell_writes<<",";
 }
};
