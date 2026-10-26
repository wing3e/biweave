#pragma once
 
struct RootExcessTripleGuide {
 struct Selection {bool usable=false;std::array<int,3>actors{};};
 bool active=false,guided=false,productive=false,static_guard_ready=false;std::array<U,2>global_active_actor_counts{};U setup_node_visits=0,static_axis_holds=0,local_identity_holds=0;double build_cpu_seconds=0;
 U calls=0,positive_excess_calls=0,zero_excess_calls=0,identity_holds=0,weighted_first_calls=0,uniform_active_first_calls=0,uniform_full_first_calls=0,scan_record_visits=0,neighbor_draws=0,max_excess=0,max_active=0,min_public_sum=0,max_public_sum=0;
 __uint128_t public_sum_total=0,selected_active_excess_total=0,active_actors_total=0;
 std::array<U,4>selected_active_counts{};std::map<I,U>public_sum_counts;
 void initialize(const Graph&g,bool want,bool guide,bool product){
  if(!want)return;if(active||static_guard_ready)throw std::runtime_error("root guide duplicate initialize");const double ts=process_cpu();active=true;guided=guide;productive=product;
  for(int o=0;o<2;++o){int n=o?g.nc:g.nr,off=o?g.nr:0;for(int v=0;v<n;++v){++setup_node_visits;global_active_actor_counts[o]+=g.target_degree[off+v]>1;}}
  static_guard_ready=true;build_cpu_seconds=process_cpu()-ts;
 }
 template<class Pick>Selection draw_with_pick(const Graph&g,int o,int root,Pick&&pick){
  if(o<0||o>1||root<0||root>=(o?g.nr:g.nc))throw std::runtime_error("root guide axis/root bounds");
  const int vertex=o?root:g.nr+root;const auto&adj=g.adj[vertex];const U d=adj.size();
  if(d<3||d!=U(g.target_degree[vertex]))throw std::runtime_error("root guide requires fixed degree>=3");
  if(static_guard_ready&&global_active_actor_counts[o]<2){++calls;++identity_holds;++static_axis_holds;return {};}
  std::vector<U>eligible;eligible.reserve(d);S128 strength=0,uAll=0,uActive=0;
  for(U pos=0;pos<d;++pos){++scan_record_visits;const auto&ed=g.edges[adj[pos]];if(ed.w<=0||(o?ed.r:ed.c)!=root)throw std::runtime_error("root guide stale/nonpositive adjacency");strength+=S128(ed.w);uAll+=S128(ed.w)-1;int actorVertex=o?g.nr+ed.c:ed.r;if(g.target_degree[actorVertex]>1){eligible.push_back(pos);uActive+=S128(ed.w)-1;}}
  if(strength!=S128(g.target_strength[vertex])||uAll!=S128(g.target_strength[vertex])-S128(d)||uActive<0||uActive>uAll||uAll<0||uAll>S128(std::numeric_limits<I>::max()))throw std::runtime_error("root guide strength/excess ledger");
  const U m=eligible.size();++calls;positive_excess_calls+=uActive>0;zero_excess_calls+=uActive==0;max_excess=std::max<U>(max_excess,U(uActive));max_active=std::max(max_active,m);active_actors_total+=__uint128_t(m);
  if(productive&&m<2){++identity_holds;++local_identity_holds;return {};}
  auto draw=[&](U n){if(!n)throw std::runtime_error("root guide empty choice");U k=pick(n);if(k>=n)throw std::runtime_error("root guide callback range");++neighbor_draws;return k;};
  std::array<U,3>positions{};U firstActive=0;
  if(guided&&uActive>0){++weighted_first_calls;U rank=draw(U(uActive));bool found=false;for(U j=0;j<m;++j){++scan_record_visits;const U mass=U(g.edges[adj[eligible[j]]].w-1);if(rank>=mass){rank-=mass;continue;}positions[0]=eligible[j];firstActive=j;found=true;break;}if(!found)throw std::runtime_error("root guide active excess rank");}
  else if(productive){++uniform_active_first_calls;firstActive=draw(m);positions[0]=eligible[firstActive];}
  else{++uniform_full_first_calls;positions[0]=draw(d);}
  if(productive){U rank=draw(m-1);if(rank>=firstActive)++rank;positions[1]=eligible[rank];}
  else{positions[1]=draw(d-1);if(positions[1]>=positions[0])++positions[1];}
  positions[2]=draw(d-2);const U lo=std::min(positions[0],positions[1]),hi=std::max(positions[0],positions[1]);if(positions[2]>=lo)++positions[2];if(positions[2]>=hi)++positions[2];
  Selection result;result.usable=true;S128 C=0,Ut=0;U k=0;for(int i=0;i<3;++i){const auto&ed=g.edges[adj[positions[i]]];result.actors[i]=o?ed.c:ed.r;C+=S128(ed.w);int av=o?g.nr+ed.c:ed.r;if(g.target_degree[av]>1){++k;Ut+=S128(ed.w)-1;}}
  if(C<3||C>S128(std::numeric_limits<I>::max())||Ut<0||Ut>C-3)throw std::runtime_error("root guide public ledger range");std::sort(result.actors.begin(),result.actors.end());if(result.actors[0]==result.actors[1]||result.actors[1]==result.actors[2])throw std::runtime_error("root guide repeated actors");
  U sum=U(C);min_public_sum=public_sum_counts.empty()?sum:std::min(min_public_sum,sum);max_public_sum=std::max(max_public_sum,sum);public_sum_total+=__uint128_t(sum);selected_active_excess_total+=__uint128_t(Ut);++selected_active_counts[k];++public_sum_counts[I(C)];return result;
 }
 Selection draw(Engine&e,const Graph&g,int o,int root){if(!active)throw std::runtime_error("inactive root guide draw");return draw_with_pick(g,o,root,[&](U n){++e.stat.work;return e.rng.below(n);});}
 void metadata(std::ostream&f)const{
  f<<"\"RG_static_axis_holds\":"<<static_axis_holds<<",\"RG_local_identity_holds\":"<<local_identity_holds<<",\"RG_setup_node_visits\":"<<setup_node_visits<<",\"RG_build_cpu_seconds\":"<<build_cpu_seconds<<",\"RG_global_active_actor_counts\":["<<global_active_actor_counts[0]<<','<<global_active_actor_counts[1]<<"],";
  f<<"\"RG_active\":"<<(active?"true":"false")<<",\"RG_calls\":"<<calls<<",\"RG_positive_excess_calls\":"<<positive_excess_calls<<",\"RG_zero_excess_calls\":"<<zero_excess_calls<<",\"RG_identity_holds\":"<<identity_holds<<",\"RG_weighted_first_calls\":"<<weighted_first_calls<<",\"RG_uniform_active_first_calls\":"<<uniform_active_first_calls<<",\"RG_uniform_full_first_calls\":"<<uniform_full_first_calls<<",\"RG_scan_record_visits\":"<<scan_record_visits<<",\"RG_neighbor_draws\":"<<neighbor_draws<<",\"RG_max_excess\":"<<max_excess<<",\"RG_max_active\":"<<max_active<<",\"RG_active_actors_total\":\""<<GlobalDegreeWorkBatch::wide_string(active_actors_total)<<"\",\"RG_min_public_sum\":"<<min_public_sum<<",\"RG_max_public_sum\":"<<max_public_sum<<",\"RG_public_sum_total\":\""<<GlobalDegreeWorkBatch::wide_string(public_sum_total)<<"\",\"RG_selected_active_excess_total\":\""<<GlobalDegreeWorkBatch::wide_string(selected_active_excess_total)<<"\",\"RG_selected_active_counts\":[";for(int i=0;i<4;++i){if(i)f<<',';f<<selected_active_counts[i];}f<<"],\"RG_public_sum_counts\":{";bool first=true;for(const auto&z:public_sum_counts){if(!first)f<<',';first=false;f<<'"'<<z.first<<"\":"<<z.second;}f<<"},";
 }
};
