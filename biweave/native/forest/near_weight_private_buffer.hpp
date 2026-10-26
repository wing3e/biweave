#pragma once

struct NearWeightClassIndex {
 Graph*graph=nullptr;bool active=false;
 void*previous_context=nullptr;void(*previous_hook)(void*,int,int,I,I)=nullptr;
 std::vector<std::map<I,std::vector<int>>>groups;
 std::unordered_map<U,std::array<U,2>>positions;
 U updates=0,adds=0,removes=0,initial_entries=0,peak_entries=0,class_count=0,peak_classes=0,checks=0,checked_entries=0;
 double build_cpu_seconds=0;
 void add(int r,int c,I w){
  const U key=cellkey(r,c);if(w<=0||positions.count(key))throw std::runtime_error("near index duplicate/nonpositive add");
  class_count+=!groups[r].count(w);class_count+=!groups[graph->nr+c].count(w);
  auto&rr=groups[r][w];auto&cc=groups[graph->nr+c][w];positions.emplace(key,std::array<U,2>{U(rr.size()),U(cc.size())});rr.push_back(c);cc.push_back(r);++adds;peak_entries=std::max<U>(peak_entries,positions.size());peak_classes=std::max(peak_classes,class_count);
 }
 void remove(int r,int c,I w){
  const U key=cellkey(r,c);auto it=positions.find(key);if(it==positions.end())throw std::runtime_error("near index missing position");const auto p=it->second;
  auto&rm=groups[r];auto ri=rm.find(w);if(ri==rm.end()||p[0]>=ri->second.size()||ri->second[p[0]]!=c)throw std::runtime_error("near stale row class");auto&rr=ri->second;int lastc=rr.back();rr[p[0]]=lastc;positions.at(cellkey(r,lastc))[0]=p[0];rr.pop_back();if(rr.empty()){rm.erase(ri);--class_count;}
  auto&cm=groups[graph->nr+c];auto ci=cm.find(w);if(ci==cm.end()||p[1]>=ci->second.size()||ci->second[p[1]]!=r)throw std::runtime_error("near stale column class");auto&cc=ci->second;int lastr=cc.back();cc[p[1]]=lastr;positions.at(cellkey(lastr,c))[1]=p[1];cc.pop_back();if(cc.empty()){cm.erase(ci);--class_count;}positions.erase(it);++removes;
 }
 static void hook(void*ctx,int r,int c,I old,I now){auto*self=static_cast<NearWeightClassIndex*>(ctx);++self->updates;if(old)self->remove(r,c,old);if(now)self->add(r,c,now);if(self->previous_hook)self->previous_hook(self->previous_context,r,c,old,now);}
 void initialize(Graph&g,bool want){
  if(!want)return;if(active||graph)throw std::runtime_error("near index initialized twice");double ts=process_cpu();graph=&g;groups.resize(g.nr+g.nc);positions.reserve(g.edges.size()*2+64);for(const auto&e:g.edges)add(e.r,e.c,e.w);initial_entries=positions.size();previous_context=g.mutation_context;previous_hook=g.mutation_hook;g.mutation_context=this;g.mutation_hook=&hook;active=true;build_cpu_seconds=process_cpu()-ts;
 }
 void check(const Graph&g){
  if(!active){if(!groups.empty()||!positions.empty())throw std::runtime_error("near disabled index nonempty");return;}
  ++checks;if(graph!=&g||positions.size()!=g.edges.size())throw std::runtime_error("near index graph/cardinality");U total=0,classes=0;
  for(const auto&e:g.edges){++checked_entries;auto p=positions.at(cellkey(e.r,e.c));auto&rr=groups[e.r].at(e.w);auto&cc=groups[g.nr+e.c].at(e.w);if(p[0]>=rr.size()||p[1]>=cc.size()||rr[p[0]]!=e.c||cc[p[1]]!=e.r)throw std::runtime_error("near graph/index disagreement");}
  for(const auto&node:groups)for(const auto&c:node){if(c.first<=0||c.second.empty())throw std::runtime_error("near retained empty class");total+=c.second.size();++classes;}if(total!=2*g.edges.size()||classes!=class_count||adds-removes!=positions.size())throw std::runtime_error("near count invariant");
 }
 void metadata(std::ostream&f)const{f<<"\"NWI_active\":"<<(active?"true":"false")<<",\"NWI_updates\":"<<updates<<",\"NWI_adds\":"<<adds<<",\"NWI_removes\":"<<removes<<",\"NWI_initial_entries\":"<<initial_entries<<",\"NWI_final_entries\":"<<positions.size()<<",\"NWI_peak_entries\":"<<peak_entries<<",\"NWI_final_classes\":"<<class_count<<",\"NWI_peak_classes\":"<<peak_classes<<",\"NWI_checks\":"<<checks<<",\"NWI_checked_entries\":"<<checked_entries<<",\"NWI_build_cpu_seconds\":"<<build_cpu_seconds<<",";}
};

struct NearWeightPrivateBufferSelector {
 NearWeightClassIndex*index=nullptr;std::string mode="nearest_indexed";U uniform_calls=0,scan_calls=0,scan_record_visits=0,scan_nonroot_records=0;
 U calls=0,empty_nonroot=0,seed_draws=0,record_draws=0,value_lookups=0,root_position_lookups=0,class_position_lookups=0,nearest_candidates=0,root_only_class_skips=0,nonprivate_drops=0,selected_total=0,max_selected=0,epoch_resets=0;
 U classes_total=0,max_classes=0,one_class_windows=0;
 std::array<U,7>class_take_counts{},width_counts{};std::map<std::string,U>quota_counts;
 using ClassMap=std::map<I,std::vector<int>>;struct RootInfo {int v=0,adjpos=0;I weight=0;U classpos=0;const ClassMap*map=nullptr;bool hasroot=true;};
 U count(const RootInfo&r,I w)const{auto it=r.map->find(w);return it==r.map->end()?0:U(it->second.size())-U(r.hasroot&&w==r.weight);}
 std::vector<I> nearest_classes(const std::array<RootInfo,3>&r,I a){
  using Map=std::map<I,std::vector<int>>;using It=Map::const_iterator;
  struct Cursor{It lo,hi;bool haslo=false;};std::array<Cursor,3>c;
  for(int i=0;i<3;++i){auto&m=*r[i].map;c[i].hi=m.upper_bound(a);c[i].haslo=c[i].hi!=m.begin();if(c[i].haslo)c[i].lo=std::prev(c[i].hi);}
  std::vector<I>chosen;chosen.reserve(6);
  for(int step=0;step<6;++step){I best=0;U distance=0;auto consider=[&](I w){++nearest_candidates;U d=w<a?U(a)-U(w):U(w)-U(a);if(!best||d<distance||(d==distance&&w<best)){best=w;distance=d;}};
   for(int i=0;i<3;++i){auto&m=*r[i].map;auto&x=c[i];while(x.haslo&&!count(r[i],x.lo->first)){++root_only_class_skips;if(x.lo==m.begin())x.haslo=false;else --x.lo;}while(x.hi!=m.end()&&!count(r[i],x.hi->first)){++root_only_class_skips;++x.hi;}if(x.haslo)consider(x.lo->first);if(x.hi!=m.end())consider(x.hi->first);}
   if(!best)break;chosen.push_back(best);
   for(int i=0;i<3;++i){auto&m=*r[i].map;auto&x=c[i];if(x.haslo&&x.lo->first==best){if(x.lo==m.begin())x.haslo=false;else --x.lo;}if(x.hi!=m.end()&&x.hi->first==best)++x.hi;}
  }return chosen;
 }
 void finish(BalancedPrivateHeatbath::Scene&s,const std::vector<int>&selected){if(selected.size()>6)throw std::runtime_error("near selected capacity");for(int q:s.quota)if(q<0||q>6)throw std::runtime_error("near selected quota");selected_total+=selected.size();max_selected=std::max<U>(max_selected,selected.size());++width_counts[selected.size()];++quota_counts[std::to_string(s.quota[0])+":"+std::to_string(s.quota[1])+":"+std::to_string(s.quota[2])];}
 template<class Pick>std::vector<int>select_with_pick(const Graph&g,BalancedPrivateHeatbath::Scene&s,JournaledLowrank4Kernel&shared,bool keep,Pick&&pick){
  if(mode!="nearest_indexed"&&mode!="uniform_indexed"&&mode!="nearest_scan")throw std::runtime_error("near selector invalid mode");if(mode!="nearest_scan"&&(!index||!index->active||index->graph!=&g))throw std::runtime_error("near selector missing index");++calls;uniform_calls+=mode=="uniform_indexed";scan_calls+=mode=="nearest_scan";std::sort(s.nodes.begin(),s.nodes.end());if(s.nodes[0]==s.nodes[1]||s.nodes[1]==s.nodes[2])throw std::runtime_error("near repeated participants");s.quota={0,0,0};auto&tmp=shared.scratch[s.o];if(!keep){for(auto&p:s.pools)p.clear();if(tmp.next_epoch())++epoch_resets;}
  std::array<RootInfo,3>r{};std::array<ClassMap,3>scanned;U pool=0;for(int i=0;i<3;++i){auto&x=r[i];x.v=s.o?g.nr+s.nodes[i]:s.nodes[i];const auto&adj=g.adj[x.v];if(adj.empty()||adj.size()!=size_t(g.target_degree[x.v]))throw std::runtime_error("near actor degree");++root_position_lookups;int id=s.o?g.find(s.root,s.nodes[i]):g.find(s.nodes[i],s.root);if(id<0)throw std::runtime_error("near absent root");const auto&e=g.edges[id];x.adjpos=s.o?e.pc:e.pr;x.weight=e.w;if(x.adjpos<0||size_t(x.adjpos)>=adj.size()||adj[x.adjpos]!=id||x.weight<=0)throw std::runtime_error("near root position");if(mode=="nearest_scan"){x.map=&scanned[i];x.hasroot=false;for(int edgeid:adj){++scan_record_visits;const auto&ed=g.edges[edgeid];int col=s.o?ed.r:ed.c;if(col==s.root)continue;scanned[i][ed.w].push_back(col);++scan_nonroot_records;}}else{x.map=&index->groups[x.v];++class_position_lookups;x.classpos=index->positions.at(cellkey(e.r,e.c))[s.o?1:0];const auto&v=x.map->at(x.weight);if(x.classpos>=v.size()||v[x.classpos]!=s.root)throw std::runtime_error("near root class position");}pool+=adj.size()-1;}
  std::vector<int>selected;selected.reserve(6);if(!pool){++empty_nonroot;finish(s,selected);return selected;}
  auto draw=[&](U n){U k=pick(n);if(!n||k>=n)throw std::runtime_error("near draw bounds");return k;};auto classify=[&](int owner,int col,I w){++record_draws;int arity=0,liveowner=-1;I actual=0;for(int k=0;k<3;++k){++value_lookups;I v=BalancedPrivateHeatbath::value(g,s,k,col);if(v>0){++arity;liveowner=k;actual=v;}}if(arity!=1){++nonprivate_drops;return;}if(owner!=liveowner||actual!=w)throw std::runtime_error("near private carried record");if(std::find(selected.begin(),selected.end(),col)!=selected.end())throw std::runtime_error("near duplicate private label");selected.push_back(col);++s.quota[owner];if(keep){if(tmp.stamp[col]!=tmp.epoch||tmp.mask[col]!=(1u<<owner)||tmp.first_weight[col]!=w)throw std::runtime_error("near full scratch stale");}else{tmp.stamp[col]=tmp.epoch;tmp.mask[col]=uint8_t(1u<<owner);tmp.first_weight[col]=w;tmp.touched.push_back(col);s.pools[owner].push_back(col);}};
  if(mode=="uniform_indexed"){const U t=std::min<U>(6,pool);std::array<U,6>taken{};for(U j=0;j<t;++j){U rank=draw(pool-j);for(U k=0;k<j;++k)if(rank>=taken[k])++rank;U insert=j;while(insert>0&&rank<taken[insert-1]){taken[insert]=taken[insert-1];--insert;}taken[insert]=rank;U local=rank;bool found=false;for(int i=0;i<3;++i){const auto&adj=g.adj[r[i].v];U n=adj.size()-1;if(local>=n){local-=n;continue;}U pos=local+(local>=U(r[i].adjpos));const auto&ed=g.edges[adj[pos]];classify(i,s.o?ed.r:ed.c,ed.w);found=true;break;}if(!found)throw std::runtime_error("near uniform pooled rank");}finish(s,selected);return selected;}
  ++seed_draws;U seed=draw(pool);I a=0;for(const auto&x:r){const auto&adj=g.adj[x.v];U n=adj.size()-1;if(seed>=n){seed-=n;continue;}U pos=seed+(seed>=U(x.adjpos));a=g.edges[adj[pos]].w;break;}if(a<=0)throw std::runtime_error("near seed mapping");
  auto weights=nearest_classes(r,a);if(weights.empty()||weights[0]!=a)throw std::runtime_error("near nearest-class order");classes_total+=weights.size();max_classes=std::max<U>(max_classes,weights.size());one_class_windows+=weights.size()==1;
  std::vector<U>counts(weights.size()),take(weights.size());for(U j=0;j<weights.size();++j)for(const auto&x:r)counts[j]+=count(x,weights[j]);U total=0,goal=std::min<U>(6,pool);
  while(total<goal){U before=total;for(U j=0;j<weights.size()&&total<goal;++j)if(take[j]<counts[j]){++take[j];++total;}if(total==before)throw std::runtime_error("near insufficient class capacity");}
  for(U z=0;z<weights.size();++z){I w=weights[z];U n=counts[z],t=take[z];if(!n||!t)throw std::runtime_error("near unused nearest class");++class_take_counts[t];std::array<U,6>taken{};
   for(U j=0;j<t;++j){U rank=draw(n-j);for(U k=0;k<j;++k)if(rank>=taken[k])++rank;U insert=j;while(insert>0&&rank<taken[insert-1]){taken[insert]=taken[insert-1];--insert;}taken[insert]=rank;
    U local=rank;int owner=-1,col=-1;for(int i=0;i<3;++i){U sz=count(r[i],w);if(local>=sz){local-=sz;continue;}const auto&v=r[i].map->at(w);U pos=local+U(r[i].hasroot&&w==r[i].weight&&local>=r[i].classpos);if(pos>=v.size()||v[pos]==s.root)throw std::runtime_error("near class rank/root exclusion");owner=i;col=v[pos];break;}if(owner<0||col<0)throw std::runtime_error("near pooled class rank");classify(owner,col,w);
   }
  }finish(s,selected);return selected;
 }
 std::vector<int>select(Engine&e,const Graph&g,BalancedPrivateHeatbath::Scene&s,JournaledLowrank4Kernel&k,bool keep){return select_with_pick(g,s,k,keep,[&](U n){++e.stat.work;return e.rng.below(n);});}
 void metadata(std::ostream&f)const{f<<"\"NWB_uniform_calls\":"<<uniform_calls<<",\"NWB_scan_calls\":"<<scan_calls<<",\"NWB_scan_record_visits\":"<<scan_record_visits<<",\"NWB_scan_nonroot_records\":"<<scan_nonroot_records<<",\"NWB_calls\":"<<calls<<",\"NWB_empty_nonroot\":"<<empty_nonroot<<",\"NWB_seed_draws\":"<<seed_draws<<",\"NWB_record_draws\":"<<record_draws<<",\"NWB_value_lookups\":"<<value_lookups<<",\"NWB_root_position_lookups\":"<<root_position_lookups<<",\"NWB_class_position_lookups\":"<<class_position_lookups<<",\"NWB_nearest_candidates\":"<<nearest_candidates<<",\"NWB_root_only_class_skips\":"<<root_only_class_skips<<",\"NWB_nonprivate_drops\":"<<nonprivate_drops<<",\"NWB_selected_total\":"<<selected_total<<",\"NWB_max_selected\":"<<max_selected<<",\"NWB_classes_total\":"<<classes_total<<",\"NWB_max_classes\":"<<max_classes<<",\"NWB_one_class_windows\":"<<one_class_windows<<",\"NWB_epoch_resets\":"<<epoch_resets<<",\"NWB_class_take_counts\":[";for(U i=0;i<7;++i){if(i)f<<',';f<<class_take_counts[i];}f<<"],\"NWB_width_counts\":[";for(U i=0;i<7;++i){if(i)f<<',';f<<width_counts[i];}f<<"],\"NWB_quota_counts\":{";bool first=true;for(const auto&x:quota_counts){if(!first)f<<',';first=false;f<<'\"'<<x.first<<"\":"<<x.second;}f<<"},";}
};
