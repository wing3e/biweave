#pragma once

struct GlobalEqualWeightSwitch {
 U calls=0,changes=0,no_edges=0,singleton_weight_class=0,same_endpoint_holds=0,cross_positive_holds=0,edge_writes=0;
 U selected_weight_class_size_total=0,max_selected_weight_class=0;
 bool bulk_requested=false,bulk_active=false,bulk_nonself=false;
 std::vector<std::pair<int,bool>> bulk_columns;
 U bulk_calls=0,bulk_changes=0,bulk_scans=0,bulk_windows=0,bulk_identical=0,bulk_moved_labels=0,bulk_max_width=0,bulk_shuffle_draws=0,bulk_self_redraws=0;
  
 bool apply_bulk(Engine&e,Graph&g,const Edge&x,const Edge&y){
  if(x.r==y.r){++same_endpoint_holds;return false;}
  const int r1=x.r,r2=y.r;const I w=x.w;bulk_columns.clear();U a=0,b=0;
  for(int side=0;side<2;++side){int r=side?r2:r1,other=side?r1:r2;
   for(int id:g.adj[r]){++bulk_scans;const Edge ed=g.edges[id];
    if(ed.w==w&&g.value(other,ed.c)==0){bulk_columns.emplace_back(ed.c,side==0);if(side)++b;else++a;}
   }
  }
  const U q=bulk_columns.size();bulk_max_width=std::max(bulk_max_width,q);
  if(!a||!b){++cross_positive_holds;return false;}
  ++bulk_windows;
  U moved=0;

  if(bulk_nonself&&(a==1||b==1)){
    
   if(a==1){const U j=1+e.rng.below(b);std::swap(bulk_columns[0],bulk_columns[j]);}
   else{const U i=e.rng.below(a);std::swap(bulk_columns[i],bulk_columns[a]);}
   ++bulk_shuffle_draws;moved=2;
  }else do{
   for(U i=0;i<a;++i){const U j=i+e.rng.below(q-i);std::swap(bulk_columns[i],bulk_columns[j]);++bulk_shuffle_draws;}
   moved=0;for(U i=0;i<q;++i)if(bulk_columns[i].second!=(i<a))++moved;
   if(bulk_nonself&&!moved)++bulk_self_redraws;
  }while(bulk_nonself&&!moved);
  if(!moved){++bulk_identical;return false;}
   
  for(U i=0;i<q;++i)if(bulk_columns[i].second!=(i<a)){const int c=bulk_columns[i].first;g.set_raw(bulk_columns[i].second?r1:r2,c,0);}
  for(U i=0;i<q;++i)if(bulk_columns[i].second!=(i<a)){const int c=bulk_columns[i].first;g.set_raw(i<a?r1:r2,c,w);}
  ++changes;++bulk_changes;edge_writes+=2*moved;bulk_moved_labels+=moved;return true;
 }
 void bulk_metadata(std::ostream&f)const{
  if(!bulk_requested)return;
  f<<"\"GWT_requested\":true,\"GWT_active\":"<<(bulk_active?"true":"false")
   <<",\"GWT_policy\":\"raw positive-edge/sameweight distinct-edge row-pair; all sameweight opposite-zero private columns; uniform complete allocation retaining each row quota; other positive entries locked; partial Fisher-Yates; current excluded only in nonself mode; conditional block scheduled by outer dispatcher; optional exchange batching recorded separately; no weight occurrence expansion\","
   <<"\"GWT_nonself\":"<<(bulk_nonself?"true":"false")<<",\"GWT_self_redraws\":"<<bulk_self_redraws<<"," 
   <<"\"GWT_calls\":"<<bulk_calls<<",\"GWT_changes\":"<<bulk_changes<<",\"GWT_scan_records\":"<<bulk_scans<<",\"GWT_windows\":"<<bulk_windows
   <<",\"GWT_identical_assignment_holds\":"<<bulk_identical<<",\"GWT_moved_labels\":"<<bulk_moved_labels
   <<",\"GWT_max_width\":"<<bulk_max_width<<",\"GWT_shuffle_draws\":"<<bulk_shuffle_draws<<",";
 }

 bool class_balanced=false;U balanced_calls=0,no_eligible_class_holds=0;

 bool conditional_requested=false,conditional_legal=false;
 const std::vector<U>*legal_row_bits=nullptr;U legal_row_words=0;int legal_row_opposite=0;
 std::array<std::vector<int>,2>legal_candidates;
 U conditional_calls=0,raw_valid_fast=0,recovery_calls=0,raw_same_column=0;
 U recovery_bitset_calls=0,recovery_adjacency_calls=0,word_visits=0,membership_checks=0,adjacency_edge_visits=0;
 U A_size_total=0,B_size_total=0,max_A_size=0,max_B_size=0,empty_A_holds=0,empty_B_holds=0,empty_both_holds=0,recovered_changes=0;
 template<class Bits>void bind_scene(const Bits&bits){
  if(!conditional_legal)return;const auto&a=bits.axis[0];if(a.active){legal_row_bits=&a.bits;legal_row_words=a.words;legal_row_opposite=a.opposite;}
 }
 void collect_legal(const Graph&g,int r1,int r2,I w){
  legal_candidates[0].clear();legal_candidates[1].clear();
  const auto&group=g.weight_groups.at(w);
  if(legal_row_bits){
   ++recovery_bitset_calls;
   const U*p=legal_row_bits->data()+U(r1)*legal_row_words,*q=legal_row_bits->data()+U(r2)*legal_row_words;
   for(U k=0;k<legal_row_words;++k){
    std::array<U,2>masks{p[k]&~q[k],q[k]&~p[k]};word_visits+=2;
    for(int side=0;side<2;++side){U mask=masks[side];while(mask){
     unsigned bit=__builtin_ctzll(mask);mask&=mask-1;U col=k*64+bit;
     if(col>=U(legal_row_opposite))throw std::runtime_error("GWC support padding bit");
     ++membership_checks;int row=side?r2:r1;
     if(group.position.count(cellkey(row,int(col))))legal_candidates[side].push_back(int(col));
    }}
   }
  }else{
   ++recovery_adjacency_calls;
   for(int side=0;side<2;++side){const int row=side?r2:r1,other=side?r1:r2;
    for(int id:g.adj[row]){++adjacency_edge_visits;const Edge ed=g.edges[id];
     if(ed.w==w&&g.value(other,ed.c)==0)legal_candidates[side].push_back(ed.c);
    }
   }
  }
  const U a=legal_candidates[0].size(),b=legal_candidates[1].size();
  A_size_total+=a;B_size_total+=b;max_A_size=std::max(max_A_size,a);max_B_size=std::max(max_B_size,b);
 }
 template<class Rand>bool apply_conditional_pair(Rand&rng,Graph&g,const Edge&x,const Edge&y){
  const int r1=x.r,r2=y.r;const I w=x.w;
  if(w<=0||y.w!=w||g.value(r1,x.c)!=w||g.value(r2,y.c)!=w)throw std::runtime_error("GWC invalid raw witness");
  if(r1==r2){++same_endpoint_holds;return false;}
  if(x.c!=y.c&&g.value(r1,y.c)==0&&g.value(r2,x.c)==0){
   ++raw_valid_fast;return apply_pair(g,x,y);
  }
  ++recovery_calls;raw_same_column+=(x.c==y.c);collect_legal(g,r1,r2,w);
  const U a=legal_candidates[0].size(),b=legal_candidates[1].size();
  if(!a||!b){empty_A_holds+=!a;empty_B_holds+=!b;empty_both_holds+=!a&&!b;++cross_positive_holds;return false;}
   
  const int c1=legal_candidates[0][rng.below(a)],c2=legal_candidates[1][rng.below(b)];
  const int i=g.find(r1,c1),j=g.find(r2,c2);if(i<0||j<0)throw std::runtime_error("GWC missing legal edge");
  const Edge aedge=g.edges[i],bedge=g.edges[j];
  if(!apply_pair(g,aedge,bedge))throw std::runtime_error("GWC complete candidate was not legal");
  ++recovered_changes;return true;
 }
 void conditional_metadata(std::ostream&f)const{
  if(!conditional_requested)return;
  f<<"\"global_equal_weight_selection\":\"conditional_legal\",\"GWC_active\":"<<(conditional_legal?"true":"false")
   <<",\"GWC_policy\":\"fixed raw positive-edge/same-weight distinct-edge rowpair; raw legal fast path else complete opposite-zero sameweight A/B independent uniform draws; empty hold no retry; existing support mask or full adjacency; all costs charged\","
   <<"\"GWC_calls\":"<<conditional_calls<<",\"GWC_raw_valid_fast\":"<<raw_valid_fast<<",\"GWC_recovery_calls\":"<<recovery_calls<<",\"GWC_raw_same_column\":"<<raw_same_column
   <<",\"GWC_bitset_recovery_calls\":"<<recovery_bitset_calls<<",\"GWC_adjacency_recovery_calls\":"<<recovery_adjacency_calls<<",\"GWC_word_visits\":"<<word_visits<<",\"GWC_membership_checks\":"<<membership_checks<<",\"GWC_adjacency_edge_visits\":"<<adjacency_edge_visits
   <<",\"GWC_A_size_total\":"<<A_size_total<<",\"GWC_B_size_total\":"<<B_size_total<<",\"GWC_max_A_size\":"<<max_A_size<<",\"GWC_max_B_size\":"<<max_B_size
   <<",\"GWC_empty_A_holds\":"<<empty_A_holds<<",\"GWC_empty_B_holds\":"<<empty_B_holds<<",\"GWC_empty_both_holds\":"<<empty_both_holds<<",\"GWC_recovered_changes\":"<<recovered_changes
   <<",\"GWC_phase_CPU_measured\":false,";
 }
 void initialize(Graph&g,bool requested,bool active){class_balanced=requested&&active;g.initialize_switch_classes(class_balanced);}

 bool apply_pair(Graph&g,const Edge&x,const Edge&y){
   
  const int r1=x.r,c1=x.c,r2=y.r,c2=y.c;const I w=x.w;
  if(w<=0||y.w!=w||g.value(r1,c1)!=w||g.value(r2,c2)!=w)throw std::runtime_error("GWS invalid equal-weight pair");
  if(r1==r2||c1==c2){++same_endpoint_holds;return false;}
  if(g.find(r1,c2)>=0||g.find(r2,c1)>=0){++cross_positive_holds;return false;}
  g.set_raw(r1,c1,0);g.set_raw(r2,c2,0);g.set_raw(r1,c2,w);g.set_raw(r2,c1,w);
  ++changes;edge_writes+=4;return true;
 }
 bool step(Engine&e,Graph&g,bool allow_bulk=true){
  ++calls;if(bulk_active&&allow_bulk)++bulk_calls;if(conditional_legal)++conditional_calls;if(g.edges.empty()){++no_edges;return false;}
  if(!g.maintain_weight_groups)throw std::runtime_error("GWS requires existing weight index");
  if(class_balanced){
   ++balanced_calls;const U K=g.switch_weights.size();if(!K){++no_eligible_class_holds;return false;}
   const I w=g.switch_weights[e.rng.below(K)];const auto& group=g.weight_groups.at(w);const U q=group.cells.size();if(q<2)throw std::runtime_error("stale eligible weight class");
   const U first=e.rng.below(q);U second=e.rng.below(q-1);if(second>=first)++second;
   const U k1=group.cells[first],k2=group.cells[second];const int i=g.find(int(k1>>32),int(uint32_t(k1))),j=g.find(int(k2>>32),int(uint32_t(k2)));if(i<0||j<0)throw std::runtime_error("stale balanced switch cells");
   const Edge x=g.edges[i],y=g.edges[j];selected_weight_class_size_total+=q;max_selected_weight_class=std::max(max_selected_weight_class,q);return apply_pair(g,x,y);
  }
  const Edge x=g.edges[e.rng.below(g.edges.size())];const U key=cellkey(x.r,x.c);
  const auto&group=g.weight_groups.at(x.w);const U q=group.cells.size();
  selected_weight_class_size_total+=q;max_selected_weight_class=std::max(max_selected_weight_class,q);
  if(q<2){++singleton_weight_class;return false;}
  const U first=U(group.position.at(key));U second=e.rng.below(q-1);if(second>=first)++second;
  const U other=group.cells[second];const int id=g.find(int(other>>32),int(uint32_t(other)));
  if(id<0)throw std::runtime_error("GWS stale weight-group cell");
  const Edge y=g.edges[id];if(bulk_active&&allow_bulk)return apply_bulk(e,g,x,y);return conditional_legal?apply_conditional_pair(e.rng,g,x,y):apply_pair(g,x,y);
 }
};

struct GlobalBridgeSwap {
 std::array<std::vector<int>,2> centers;
 U calls=0,changes=0,empty_centers=0,empty_outside_neighbors=0,same_actor_holds=0,cross_positive_holds=0,nonpositive_compensation_holds=0;
 U row_orientation=0,column_orientation=0,equal_weight_pairs=0,edge_writes_attempted=0,changed_cell_writes=0,center_pool_total=0;
 void initialize(const Graph&g,bool active){if(!active)return;for(int o=0;o<2;++o){int n=o?g.nc:g.nr,off=o?g.nr:0;for(int v=0;v<n;++v)if(g.target_degree[off+v]>=2)centers[o].push_back(v);}center_pool_total=centers[0].size()+centers[1].size();}
 static I value(const Graph&g,int o,int a,int c){return o?g.value(c,a):g.value(a,c);}
 static void put(Graph&g,int o,int a,int c,I w){if(o)g.set_raw(c,a,w);else g.set_raw(a,c,w);}
 bool apply_descriptor(Graph&g,int o,int center,int c,int d,int a,int z){
  if(o<0||o>1||c==d||a==center||z==center)throw std::runtime_error("GBS invalid descriptor");
  if(a==z){++same_actor_holds;return false;}
  const I u=value(g,o,a,c),v=value(g,o,z,d),p=value(g,o,center,c),q=value(g,o,center,d);
  if(u<=0||v<=0||p<=0||q<=0)throw std::runtime_error("GBS missing descriptor edge");
  if(value(g,o,a,d)>0||value(g,o,z,c)>0){++cross_positive_holds;return false;}
  equal_weight_pairs+=(u==v);
  const S128 pp=S128(p)+S128(u)-S128(v),qq=S128(q)-S128(u)+S128(v);
  if(pp<=0||qq<=0){++nonpositive_compensation_holds;return false;}
  if(pp>std::numeric_limits<I>::max()||qq>std::numeric_limits<I>::max())throw std::runtime_error("GBS compensation exceeds int64");
  const U before=g.counters?g.counters->cell_updates:0;
  put(g,o,center,c,I(pp));put(g,o,center,d,I(qq));
  put(g,o,a,c,0);put(g,o,z,d,0);put(g,o,a,d,u);put(g,o,z,c,v);
  edge_writes_attempted+=6;changed_cell_writes+=(u==v?4:6);
  if(g.counters&&g.counters->cell_updates-before!=(u==v?4:6))throw std::runtime_error("GBS cell counter mismatch");
  ++changes;return true;
 }
 bool step(Engine&e,Graph&g){
  ++calls;const int o=int(e.rng.below(2));if(o)++column_orientation;else++row_orientation;
  const auto&pool=centers[o];if(pool.empty()){++empty_centers;return false;}
  const int center=pool[e.rng.below(pool.size())],cv=o?g.nr+center:center;
  const auto&adj=g.adj[cv];const U n=adj.size();if(n<2)throw std::runtime_error("GBS fixed center degree changed");
  U i=e.rng.below(n),j=e.rng.below(n-1);if(j>=i)++j;
  const Edge ce=g.edges[adj[i]],de=g.edges[adj[j]];const int c=o?ce.r:ce.c,d=o?de.r:de.c;
  const auto&ca=g.adj[o?c:g.nr+c];const auto&da=g.adj[o?d:g.nr+d];
  if(ca.size()<2||da.size()<2){++empty_outside_neighbors;return false;}
  const U cp=U(o?ce.pr:ce.pc),dp=U(o?de.pr:de.pc);
  U ai=e.rng.below(ca.size()-1),zi=e.rng.below(da.size()-1);if(ai>=cp)++ai;if(zi>=dp)++zi;
  const Edge ae=g.edges[ca[ai]],ze=g.edges[da[zi]];const int a=o?ae.c:ae.r,z=o?ze.c:ze.r;
  return apply_descriptor(g,o,center,c,d,a,z);
 }
};
