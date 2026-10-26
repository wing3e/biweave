#pragma once

struct DistinctPrivateBufferSelector {
 U calls=0,record_draws=0,value_lookups=0,root_position_lookups=0,nonprivate_drops=0,selected_total=0,max_selected=0,epoch_resets=0;
 std::array<U,3>actor_take_counts{};std::array<U,7>width_counts{};std::map<std::string,U>quota_counts;
 template<class Pick>std::vector<int> select_with_pick(const Graph&g,BalancedPrivateHeatbath::Scene&s,JournaledLowrank4Kernel&shared,bool keep_full_pools,Pick&&pick){
  ++calls;std::sort(s.nodes.begin(),s.nodes.end());if(s.nodes[0]==s.nodes[1]||s.nodes[1]==s.nodes[2])throw std::runtime_error("distinct repeated participants");s.quota={0,0,0};auto&tmp=shared.scratch[s.o];
  if(!keep_full_pools){for(auto&p:s.pools)p.clear();if(tmp.next_epoch())++epoch_resets;}
  std::vector<int>selected;selected.reserve(6);
  for(int i=0;i<3;++i){const int v=s.o?g.nr+s.nodes[i]:s.nodes[i];const auto&adj=g.adj[v];if(adj.empty()||adj.size()!=size_t(g.target_degree[v]))throw std::runtime_error("distinct actor degree changed");
   ++root_position_lookups;const int root_id=s.o?g.find(s.root,s.nodes[i]):g.find(s.nodes[i],s.root);if(root_id<0)throw std::runtime_error("distinct common root missing");const auto root_edge=g.edges[root_id];const int root_pos=s.o?root_edge.pc:root_edge.pr;
   if(root_edge.w<=0||root_pos<0||size_t(root_pos)>=adj.size()||adj[root_pos]!=root_id)throw std::runtime_error("distinct stale root position");
   const U n=adj.size()-1,t=std::min<U>(2,n);++actor_take_counts[t];U first=0;
   for(U j=0;j<t;++j){const U bound=n-j;const U raw=pick(bound);if(raw>=bound)throw std::runtime_error("distinct raw draw out of range");const U chosen=j?(raw+(raw>=first)):raw;if(!j)first=chosen;const U pos=chosen+(chosen>=U(root_pos));if(pos>=adj.size()||pos==U(root_pos))throw std::runtime_error("distinct root skip mapping");
    ++record_draws;const auto ed=g.edges[adj[pos]];const int col=s.o?ed.r:ed.c;int owner=-1,arity=0;I weight=0;
    for(int k=0;k<3;++k){++value_lookups;const I w=BalancedPrivateHeatbath::value(g,s,k,col);if(w>0){++arity;owner=k;weight=w;}}
    if(col==s.root)throw std::runtime_error("distinct root sampled");if(arity!=1){++nonprivate_drops;continue;}if(owner!=i||weight!=ed.w)throw std::runtime_error("distinct private record owner mismatch");
    selected.push_back(col);++s.quota[owner];if(keep_full_pools){if(tmp.stamp[col]!=tmp.epoch||tmp.mask[col]!=(1u<<owner)||tmp.first_weight[col]!=weight)throw std::runtime_error("distinct full scratch stale");}
    else{tmp.stamp[col]=tmp.epoch;tmp.mask[col]=uint8_t(1u<<owner);tmp.first_weight[col]=weight;tmp.touched.push_back(col);s.pools[owner].push_back(col);}
   }
  }
  if(selected.size()>6)throw std::runtime_error("distinct selected capacity");for(int q:s.quota)if(q<0||q>2)throw std::runtime_error("distinct quota capacity");selected_total+=selected.size();max_selected=std::max<U>(max_selected,selected.size());++width_counts[selected.size()];++quota_counts[std::to_string(s.quota[0])+":"+std::to_string(s.quota[1])+":"+std::to_string(s.quota[2])];return selected;
 }
 std::vector<int> select(Engine&e,const Graph&g,BalancedPrivateHeatbath::Scene&s,JournaledLowrank4Kernel&shared,bool keep_full_pools){return select_with_pick(g,s,shared,keep_full_pools,[&](U n){++e.stat.work;return e.rng.below(n);});}
 void metadata(std::ostream&f)const{
  f<<"\"NRB_calls\":"<<calls<<",\"NRB_record_draws\":"<<record_draws<<",\"NRB_value_lookups\":"<<value_lookups<<",\"NRB_root_position_lookups\":"<<root_position_lookups<<",\"NRB_nonprivate_drops\":"<<nonprivate_drops<<",\"NRB_selected_total\":"<<selected_total<<",\"NRB_max_selected\":"<<max_selected<<",\"NRB_epoch_resets\":"<<epoch_resets<<",\"NRB_actor_take_counts\":[";for(size_t i=0;i<actor_take_counts.size();++i){if(i)f<<',';f<<actor_take_counts[i];}f<<"],\"NRB_width_counts\":[";for(size_t i=0;i<width_counts.size();++i){if(i)f<<',';f<<width_counts[i];}f<<"],\"NRB_quota_counts\":{";bool first=true;for(const auto&x:quota_counts){if(!first)f<<',';first=false;f<<'\"'<<x.first<<"\":"<<x.second;}f<<"},";
 }
};
