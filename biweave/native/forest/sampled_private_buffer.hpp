#pragma once

struct SampledPrivateBufferSelector {
 static constexpr U RECORDS_PER_ACTOR=2;
 U calls=0,record_draws=0,value_lookups=0,root_drops=0,nonprivate_drops=0,duplicate_drops=0,selected_total=0,max_selected=0,epoch_resets=0;
 std::array<U,7>width_counts{};
 std::map<std::string,U>quota_counts;
 template<class Pick>std::vector<int> select_with_pick(const Graph&g,BalancedPrivateHeatbath::Scene&s,JournaledLowrank4Kernel&shared,bool keep_full_pools,Pick&&pick){
  ++calls;std::sort(s.nodes.begin(),s.nodes.end());if(s.nodes[0]==s.nodes[1]||s.nodes[1]==s.nodes[2])throw std::runtime_error("sampled repeated participants");
  s.quota={0,0,0};auto&tmp=shared.scratch[s.o];
  if(!keep_full_pools){for(auto&p:s.pools)p.clear();if(tmp.next_epoch())++epoch_resets;}
  std::vector<int>selected;selected.reserve(6);
  for(int i=0;i<3;++i){if(BalancedPrivateHeatbath::value(g,s,i,s.root)<=0)throw std::runtime_error("sampled root missing");
   const int v=s.o?g.nr+s.nodes[i]:s.nodes[i];const auto&adj=g.adj[v];if(adj.empty()||adj.size()!=size_t(g.target_degree[v]))throw std::runtime_error("sampled degree changed");
   for(U j=0;j<RECORDS_PER_ACTOR;++j){++record_draws;const U chosen=pick(adj.size());if(chosen>=adj.size())throw std::runtime_error("sampled raw draw out of range");const auto ed=g.edges[adj[chosen]];const int col=s.o?ed.r:ed.c;int owner=-1,arity=0;I weight=0;
    for(int k=0;k<3;++k){++value_lookups;const I w=BalancedPrivateHeatbath::value(g,s,k,col);if(w>0){++arity;owner=k;weight=w;}}
    if(col==s.root){if(arity!=3)throw std::runtime_error("sampled common root lost support");++root_drops;continue;}
    if(arity!=1){++nonprivate_drops;continue;}
    if(owner!=i||weight!=ed.w)throw std::runtime_error("sampled private record owner mismatch");
    if(std::find(selected.begin(),selected.end(),col)!=selected.end()){++duplicate_drops;continue;}
    selected.push_back(col);++s.quota[owner];
    if(keep_full_pools){if(tmp.stamp[col]!=tmp.epoch||tmp.mask[col]!=(1u<<owner)||tmp.first_weight[col]!=weight)throw std::runtime_error("sampled full scratch stale");}
    else{tmp.stamp[col]=tmp.epoch;tmp.mask[col]=uint8_t(1u<<owner);tmp.first_weight[col]=weight;tmp.touched.push_back(col);s.pools[owner].push_back(col);}
   }
  }
  if(selected.size()>6)throw std::runtime_error("sampled private capacity exceeded");
  for(int q:s.quota)if(q<0||q>2)throw std::runtime_error("sampled participant quota exceeded");
  selected_total+=selected.size();max_selected=std::max<U>(max_selected,selected.size());++width_counts[selected.size()];
  ++quota_counts[std::to_string(s.quota[0])+":"+std::to_string(s.quota[1])+":"+std::to_string(s.quota[2])];return selected;
 }
 std::vector<int> select(Engine&e,const Graph&g,BalancedPrivateHeatbath::Scene&s,JournaledLowrank4Kernel&shared,bool keep_full_pools){return select_with_pick(g,s,shared,keep_full_pools,[&](U n){++e.stat.work;return e.rng.below(n);});}
 void metadata(std::ostream&f)const{
  f<<"\"SPB_calls\":"<<calls<<",\"SPB_record_draws\":"<<record_draws<<",\"SPB_value_lookups\":"<<value_lookups<<",\"SPB_root_drops\":"<<root_drops<<",\"SPB_nonprivate_drops\":"<<nonprivate_drops<<",\"SPB_duplicate_drops\":"<<duplicate_drops<<",\"SPB_selected_total\":"<<selected_total<<",\"SPB_max_selected\":"<<max_selected<<",\"SPB_epoch_resets\":"<<epoch_resets<<",\"SPB_width_counts\":[";
  for(size_t i=0;i<width_counts.size();++i){if(i)f<<',';f<<width_counts[i];}f<<"],\"SPB_quota_counts\":{";bool first=true;for(const auto&x:quota_counts){if(!first)f<<',';first=false;f<<'\"'<<x.first<<"\":"<<x.second;}f<<"},";
 }
};
