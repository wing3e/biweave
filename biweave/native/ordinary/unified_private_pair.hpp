#pragma once
#include "two_anchor_pair_law.hpp"
#include "unified_budget_pair.hpp"

struct UnifiedPrivatePair {
 struct Label {int object=0,owner=0;I weight=0;};
 struct Cell {int r=0,c=0;I before=0,after=0;};
 bool requested=false,active=false,update_second_public=true;std::string profile_mode="heatbath",label_mode="full_resample";
 std::array<std::vector<int>,2>roots;
 UnifiedBudgetPair classes;
 U calls=0,empty_roots=0,too_few_active=0,uniform_pairs=0,guided_pairs=0;
 U root_scan_records=0,actor_scan_records=0,classification_lookups=0,shared_candidates=0;
 U single_anchor=0,two_anchor=0,empty_private=0,single_class=0,two_class=0;
 U profile_builds=0,profile_draws=0,profile_hold_calls=0,profile_singletons=0,profile_changes=0,public_split_draws=0,public_split_singletons=0,frozen_second_public=0;
 U label_shuffle_draws=0,labels_examined=0,moved_labels=0,root_cell_writes=0,cell_writes=0,changes=0;
 U transport_calls=0,transport_zero_delta=0,transport_subset_draws=0,transport_subset_labels=0,transport_donor_records=0,transport_preserved_labels=0,transport_private_cell_writes=0,transport_max_abs_delta=0;
 __uint128_t transport_abs_delta_total=0;
 U quota_first_calls=0,quota_first_changed_quantity_minimal_calls=0,quota_first_unchanged_quantity_full_calls=0;
 U quota_first_unchanged_single_class_calls=0,quota_first_unchanged_empty_private_calls=0;
 U quota_first_full_labels_examined=0,quota_first_full_moved_labels=0,quota_first_full_preserved_labels=0,quota_first_full_private_cell_writes=0,quota_first_full_shuffle_draws=0;
 U max_eligible=0,max_selected_labels=0,max_private_quota=0,max_span=0,max_relative_bits=0;
 __uint128_t excess_total=0,selected_public_total=0,span_total=0;
 static std::string decimal(__uint128_t v){if(!v)return "0";std::string s;while(v){s.push_back(char('0'+v%10));v/=10;}std::reverse(s.begin(),s.end());return s;}
 static I checked_weight(S128 x){if(x<0||x>std::numeric_limits<I>::max())throw std::runtime_error("UA cell weight outside signed64");return I(x);}
 void initialize(const Graph&g,bool want,bool run){requested=want;active=want&&run;if(!active)return;
  for(int o=0;o<2;++o){const int count=o?g.nr:g.nc,offset=o?0:g.nr;
   for(int r=0;r<count;++r)if(g.target_degree[offset+r]>=2)roots[o].push_back(r);}}
 template<class Pick>void shuffle(std::vector<int>&labels,Pick&&pick){for(size_t j=labels.size();j>1;--j){std::swap(labels[j-1],labels[pick(j)]);++label_shuffle_draws;}}
  
 template<class Pick>std::vector<int> transport_subset(const std::vector<int>&labels,U k,Pick&&pick){
  const U n=labels.size();if(k>n)throw std::runtime_error("UA transport subset quota");
  std::unordered_set<U>chosen;chosen.reserve(size_t(k));std::vector<int>result;result.reserve(size_t(k));
  for(U j=n-k;j<n;++j){U index=pick(j+1);if(index>j)throw std::runtime_error("UA transport Floyd range");if(chosen.count(index))index=j;chosen.insert(index);result.push_back(labels[index]);++transport_subset_draws;}
  transport_subset_labels+=result.size();return result;
 }
  
 template<class SmallPick,class BigPick>bool block_with(Engine&e,Graph&g,int o,int P,const std::array<int,2>&nodes,int Q,SmallPick&&pick,BigPick&&bigpick){
  if(o<0||o>1)throw std::runtime_error("UA descriptor orientation");const int actors=o?g.nc:g.nr,objects=o?g.nr:g.nc;
  if(nodes[0]<0||nodes[1]>=actors||nodes[0]>=nodes[1]||P<0||P>=objects||Q<-1||Q>=objects||Q==P)throw std::runtime_error("UA duplicate/self/out-of-range descriptor");
  auto value=[&](int owner,int c){++classification_lookups;return o?g.value(c,nodes[owner]):g.value(nodes[owner],c);};
  const I p0=value(0,P),p1=value(1,P),q0=Q<0?0:value(0,Q),q1=Q<0?0:value(1,Q);
  if(p0<=0||p1<=0||(Q>=0&&(q0<=0||q1<=0||Q==P)))throw std::runtime_error("UA invalid live public descriptor");
  const S128 X=S128(p0)+p1,Y=S128(q0)+q1,C=X+Y;selected_public_total+=__uint128_t(C);
  if(Q<0)++single_anchor;else ++two_anchor;
  std::map<I,std::vector<Label>>groups;std::map<I,U>freq;
  for(int owner=0;owner<2;++owner){const int vertex=o?g.nr+nodes[owner]:nodes[owner];
   if(g.degree[vertex]!=g.target_degree[vertex])throw std::runtime_error("UA requires exact actor degree");
   for(int id:g.adj[vertex]){const auto&edge=g.edges[id];const int c=o?edge.r:edge.c;++actor_scan_records;
    if(c==P||c==Q)continue;const I other=value(1-owner,c);if(other)continue;
    if(edge.w<=0)throw std::runtime_error("UA nonpositive private carried weight");
    groups[edge.w].push_back(Label{c,owner,edge.w});++freq[edge.w];}}
  if(freq.empty())++empty_private;
  const auto choice=classes.draw(freq,C,Q<0?2:4,pick);
  std::array<U,2>quota{},old_high{};std::array<S128,2>beta{S128(p0)+q0,S128(p1)+q1};
  std::vector<Label>selected;std::vector<int>low_labels,high_labels;
  for(const auto&group:groups)if(group.first==choice.low||(choice.pair&&group.first==choice.high))for(const auto&label:group.second){
   selected.push_back(label);++quota[label.owner];beta[label.owner]+=label.weight;
   if(choice.pair&&label.weight==choice.high){++old_high[label.owner];}}
  std::sort(selected.begin(),selected.end(),[](const Label&a,const Label&b){return a.object<b.object;});
  for(size_t k=0;k<selected.size();++k){if(choice.pair&&selected[k].weight==choice.high)high_labels.push_back(int(k));else low_labels.push_back(int(k));}
  max_private_quota=std::max({max_private_quota,quota[0],quota[1]});
  labels_examined+=selected.size();max_selected_labels=std::max(max_selected_labels,U(selected.size()));
  const bool move_Q=Q>=0&&update_second_public;const S128 frozen_q0=move_Q?0:q0,frozen_q1=move_Q?0:q1;
  const S128 active_C=move_Q?C:X;if(Q>=0&&!move_Q)++frozen_second_public;
  U new_hi=old_high[0];TwoAnchorPairLaw::Draw draw;
  if(choice.pair){++two_class;TwoAnchorPairLaw::Input input;
   input.qi=quota[0];input.qj=quota[1];input.T=high_labels.size();input.low=choice.low;input.high=choice.high;
   input.beta_i=beta[0]-frozen_q0;input.beta_j=beta[1]-frozen_q1;input.X=X;input.Y=move_Q?Y:0;input.two_anchor=move_Q;
   ++profile_builds;const auto law=TwoAnchorPairLaw::build(input);const U span=law.U-law.L;span_total+=span;max_span=std::max(max_span,span);
   max_relative_bits=std::max(max_relative_bits,U(mpz_sizeinbase(law.total.get_mpz_t(),2)));
   profile_singletons+=law.L==law.U;
   if(profile_mode=="fixed_profile"){++profile_hold_calls;const auto split=TwoAnchorPairLaw::split(law,old_high[0]);draw=TwoAnchorPairLaw::fill(law,old_high[0],split.K==1?0:pick(split.K));}
   else{++profile_draws;draw=TwoAnchorPairLaw::draw(law,bigpick,pick);}
   new_hi=draw.z;profile_changes+=new_hi!=old_high[0];
   const auto split=TwoAnchorPairLaw::split(law,new_hi);public_split_draws+=split.K>1;public_split_singletons+=split.K==1;
  }else{++single_class;const S128 Ri=beta[0]-frozen_q0-S128(choice.low)*quota[0],Rj=beta[1]-frozen_q1-S128(choice.low)*quota[1];
   if(Ri+Rj!=active_C)throw std::runtime_error("UA single-class public total mismatch");
   if(!move_Q){if(Ri<1||Rj<1)throw std::runtime_error("UA single-anchor positivity");draw.Pi=Ri;draw.Pj=Rj;++public_split_singletons;}
   else{const S128 lo=std::max<S128>(1,Ri-Y+1),hi=std::min<S128>(Ri-1,X-1);
    if(lo>hi||Ri<2||Rj<2)throw std::runtime_error("UA empty single-class public split");
    const U count=U(hi-lo+1);public_split_draws+=count>1;public_split_singletons+=count==1;
    draw.Pi=lo+(count==1?0:pick(count));draw.Pj=X-draw.Pi;draw.Qi=Ri-draw.Pi;draw.Qj=Y-draw.Qi;}}
  std::vector<Cell>writes;std::array<S128,2>new_strength{};std::array<U,2>new_quota{};
  auto add=[&](int owner,int c,I after){const int r=o?c:nodes[owner],col=o?nodes[owner]:c;const I before=g.value(r,col);
   if(before!=after)writes.push_back(Cell{r,col,before,after});};
  const bool quota_first=label_mode=="quota_first",same_quantity=new_hi==old_high[0];
  const U moved_before=moved_labels,shuffle_before=label_shuffle_draws;
  if(quota_first){++quota_first_calls;if(same_quantity){++quota_first_unchanged_quantity_full_calls;quota_first_unchanged_single_class_calls+=!choice.pair;quota_first_unchanged_empty_private_calls+=selected.empty();}else ++quota_first_changed_quantity_minimal_calls;}
  if(label_mode=="full_resample"||(quota_first&&same_quantity)){
  shuffle(high_labels,pick);shuffle(low_labels,pick);
  std::vector<int>new_owner(selected.size(),-1);
  for(size_t i=0;i<high_labels.size();++i)new_owner[high_labels[i]]=i<new_hi?0:1;
  if(new_hi>quota[0])throw std::runtime_error("UA drawn high count exceeds quota");const U low0=quota[0]-new_hi;
  for(size_t i=0;i<low_labels.size();++i)new_owner[low_labels[i]]=i<low0?0:1;
  writes.reserve(2*selected.size()+4);
  for(size_t k=0;k<selected.size();++k){const auto&label=selected[k];const int owner=new_owner[k];if(owner<0||owner>1)throw std::runtime_error("UA missing label owner");++new_quota[owner];new_strength[owner]+=label.weight;
   if(owner!=label.owner){++moved_labels;add(label.owner,label.object,0);add(owner,label.object,label.weight);}}
  }else if(label_mode=="minimal_transport"||(quota_first&&!same_quantity)){
   ++transport_calls;const bool increase=new_hi>=old_high[0];const U delta=increase?new_hi-old_high[0]:old_high[0]-new_hi;
   transport_abs_delta_total+=delta;transport_max_abs_delta=std::max(transport_max_abs_delta,delta);transport_zero_delta+=delta==0;
   if(delta>selected.size()/2)throw std::runtime_error("UA transport exceeds selected labels");
   transport_preserved_labels+=selected.size()-2*delta;writes.reserve(size_t(4*delta)+4);
   new_quota=quota;const S128 signed_delta=increase?S128(delta):-S128(delta),gap=choice.pair?S128(choice.high)-choice.low:0;
   new_strength={beta[0]-p0-q0+signed_delta*gap,beta[1]-p1-q1-signed_delta*gap};
   if(delta){
    std::vector<int>high_donor,low_donor;const int high_owner=increase?1:0,low_owner=1-high_owner;
    for(int index:high_labels){++transport_donor_records;if(selected[index].owner==high_owner)high_donor.push_back(index);}
    for(int index:low_labels){++transport_donor_records;if(selected[index].owner==low_owner)low_donor.push_back(index);}
    const auto high_moves=transport_subset(high_donor,delta,pick),low_moves=transport_subset(low_donor,delta,pick);
    auto move=[&](int index){const auto&label=selected[index];++moved_labels;add(label.owner,label.object,0);add(1-label.owner,label.object,label.weight);};
    for(int index:high_moves)move(index);for(int index:low_moves)move(index);
   }
   if(writes.size()!=4*delta)throw std::runtime_error("UA transport private writes invariant");transport_private_cell_writes+=writes.size();
  }else throw std::runtime_error("UA unknown label update mode");
  if(quota_first&&same_quantity){const U moved=moved_labels-moved_before;quota_first_full_labels_examined+=selected.size();quota_first_full_moved_labels+=moved;quota_first_full_preserved_labels+=selected.size()-moved;quota_first_full_private_cell_writes+=writes.size();quota_first_full_shuffle_draws+=label_shuffle_draws-shuffle_before;}
  new_strength[0]+=draw.Pi+draw.Qi+frozen_q0;new_strength[1]+=draw.Pj+draw.Qj+frozen_q1;
  if(new_quota!=quota||new_strength!=beta||draw.Pi<1||draw.Pj<1||draw.Pi+draw.Pj!=X||
    (move_Q&&(draw.Qi<1||draw.Qj<1||draw.Qi+draw.Qj!=Y)))throw std::runtime_error("UA completion ledger invalid");
  const size_t private_writes=writes.size();add(0,P,checked_weight(draw.Pi));add(1,P,checked_weight(draw.Pj));
  if(move_Q){add(0,Q,checked_weight(draw.Qi));add(1,Q,checked_weight(draw.Qj));}
  root_cell_writes+=writes.size()-private_writes;cell_writes+=writes.size();
  for(const Cell&cell:writes){if(g.value(cell.r,cell.c)!=cell.before)throw std::runtime_error("UA stale precommit cell");g.set_raw(cell.r,cell.c,cell.after);}
  if(writes.empty())return false;++changes;++e.stat.changed_outer;return true;
 }
 bool block(Engine&e,Graph&g,int o,int P,const std::array<int,2>&nodes,int Q){return block_with(e,g,o,P,nodes,Q,[&](U bound){return e.rng.below(bound);},[&](const mpz_class&bound){return zbig(e.rng.below_big(bigz(bound)));});}
 bool step(Engine&e,Graph&g){if(!active)throw std::runtime_error("UA inactive step");++calls;++e.stat.work;
  if(g.D)throw std::runtime_error("UA requires exact degree state");const int o=choose_orientation(e.rng,g);
  if(roots[o].empty()){++empty_roots;return false;}const int P=roots[o][e.rng.below(roots[o].size())],root_vertex=o?P:g.nr+P;
  const auto&adj=g.adj[root_vertex];if(adj.size()!=U(g.target_degree[root_vertex]))throw std::runtime_error("UA root degree changed");
  std::vector<int>eligible;std::vector<U>excess;S128 total=0;
  for(int id:adj){const auto&edge=g.edges[id];++root_scan_records;const int actor=o?edge.c:edge.r,vertex=o?g.nr+actor:actor;
   if(g.target_degree[vertex]<=1)continue;eligible.push_back(actor);excess.push_back(U(edge.w-1));total+=edge.w-1;}
  max_eligible=std::max(max_eligible,U(eligible.size()));if(eligible.size()<2){++too_few_active;return false;}
  if(total<0||total>std::numeric_limits<I>::max())throw std::runtime_error("UA eligible excess outside source strength range");
  const U u=U(total);excess_total+=u;size_t first=0;
  if(u){++guided_pairs;U rank=e.rng.below(u);while(rank>=excess[first]){rank-=excess[first];++first;}}
  else{++uniform_pairs;first=e.rng.below(eligible.size());}
  size_t second=e.rng.below(eligible.size()-1);if(second>=first)++second;
  std::array<int,2>nodes{eligible[first],eligible[second]};std::sort(nodes.begin(),nodes.end());
  std::vector<int>shared;const int vertex=o?g.nr+nodes[0]:nodes[0];
  for(int id:g.adj[vertex]){const auto&edge=g.edges[id];const int c=o?edge.r:edge.c;++actor_scan_records;if(c==P)continue;
   ++classification_lookups;if((o?g.value(c,nodes[1]):g.value(nodes[1],c))>0)shared.push_back(c);}
  std::sort(shared.begin(),shared.end());shared_candidates+=shared.size();const int Q=shared.empty()?-1:shared[e.rng.below(shared.size())];
  return block(e,g,o,P,nodes,Q);
 }
 void metadata(std::ostream&f)const{
  if(label_mode=="minimal_transport"){
   f<<"\"UA_private_label_update\":\"minimal_transport\",\"UA_label_kernel_scope\":\"uniform required high/low current-owner subsets; delta0 labels retained; target stationary, not complete block IID\",";
#define UA_TRANSPORT_FIELD(name) f<<"\"UA_" #name "\":"<<name<<",";
   UA_TRANSPORT_FIELD(transport_calls) UA_TRANSPORT_FIELD(transport_zero_delta) UA_TRANSPORT_FIELD(transport_subset_draws) UA_TRANSPORT_FIELD(transport_subset_labels) UA_TRANSPORT_FIELD(transport_donor_records) UA_TRANSPORT_FIELD(transport_preserved_labels) UA_TRANSPORT_FIELD(transport_private_cell_writes) UA_TRANSPORT_FIELD(transport_max_abs_delta)
#undef UA_TRANSPORT_FIELD
   f<<"\"UA_transport_abs_delta_total\":\""<<decimal(transport_abs_delta_total)<<"\",";
  }
  if(label_mode=="quota_first"){
   f<<"\"UA_private_label_update\":\"quota_first\",\"UA_label_kernel_scope\":\"changed high quantity uses required high/low subset transport; unchanged quantity uses full label heatbath including single/empty private pools; target stationary, not complete block IID\",";
#define UA_QUOTA_FIRST_FIELD(name) f<<"\"UA_" #name "\":"<<name<<",";
   UA_QUOTA_FIRST_FIELD(quota_first_calls) UA_QUOTA_FIRST_FIELD(quota_first_changed_quantity_minimal_calls) UA_QUOTA_FIRST_FIELD(quota_first_unchanged_quantity_full_calls)
   UA_QUOTA_FIRST_FIELD(quota_first_unchanged_single_class_calls) UA_QUOTA_FIRST_FIELD(quota_first_unchanged_empty_private_calls)
   UA_QUOTA_FIRST_FIELD(quota_first_full_labels_examined) UA_QUOTA_FIRST_FIELD(quota_first_full_moved_labels) UA_QUOTA_FIRST_FIELD(quota_first_full_preserved_labels) UA_QUOTA_FIRST_FIELD(quota_first_full_private_cell_writes) UA_QUOTA_FIRST_FIELD(quota_first_full_shuffle_draws)
   UA_QUOTA_FIRST_FIELD(transport_calls) UA_QUOTA_FIRST_FIELD(transport_zero_delta) UA_QUOTA_FIRST_FIELD(transport_subset_draws) UA_QUOTA_FIRST_FIELD(transport_subset_labels) UA_QUOTA_FIRST_FIELD(transport_donor_records) UA_QUOTA_FIRST_FIELD(transport_preserved_labels) UA_QUOTA_FIRST_FIELD(transport_private_cell_writes) UA_QUOTA_FIRST_FIELD(transport_max_abs_delta)
#undef UA_QUOTA_FIRST_FIELD
   f<<"\"UA_transport_abs_delta_total\":\""<<decimal(transport_abs_delta_total)<<"\",";
  }
  f<<"\"UA_private_profile_update\":\""<<profile_mode<<"\",\"UA_second_public_update\":"<<(update_second_public?1:0)<<",";
  f<<"\"unified_private_pair_requested\":true,\"UA_active\":"<<(active?"true":"false")<<",\"UA_policy\":\""<<(label_mode=="quota_first"?"active-excess pair; shared Q; compatible class tickets; exact f*K/public split; changed quantity minimal transport and unchanged quantity complete labels":(label_mode=="minimal_transport"?"active-excess pair; shared Q; compatible class tickets; exact f*K/public split and required high/low subset transport":"active-excess pair; shared Q; compatible class tickets; exact f*K and complete label/public split"))<<"\",\"UA_per_pair_timing_active\":false,";
#define UA_FIELD(name) f<<"\"UA_" #name "\":"<<name<<",";
  UA_FIELD(calls) UA_FIELD(empty_roots) UA_FIELD(too_few_active) UA_FIELD(uniform_pairs) UA_FIELD(guided_pairs)
  UA_FIELD(root_scan_records) UA_FIELD(actor_scan_records) UA_FIELD(classification_lookups) UA_FIELD(shared_candidates)
  UA_FIELD(single_anchor) UA_FIELD(two_anchor) UA_FIELD(empty_private) UA_FIELD(single_class) UA_FIELD(two_class)
  UA_FIELD(profile_builds) UA_FIELD(profile_draws) UA_FIELD(profile_hold_calls) UA_FIELD(frozen_second_public) UA_FIELD(profile_singletons) UA_FIELD(profile_changes) UA_FIELD(public_split_draws) UA_FIELD(public_split_singletons)
  UA_FIELD(label_shuffle_draws) UA_FIELD(labels_examined) UA_FIELD(moved_labels) UA_FIELD(root_cell_writes) UA_FIELD(cell_writes) UA_FIELD(changes)
  UA_FIELD(max_eligible) UA_FIELD(max_selected_labels) UA_FIELD(max_private_quota) UA_FIELD(max_span) UA_FIELD(max_relative_bits)
#undef UA_FIELD
  f<<"\"UA_excess_total\":\""<<decimal(excess_total)<<"\",\"UA_selected_public_total\":\""<<decimal(selected_public_total)<<"\",\"UA_span_total\":\""<<decimal(span_total)<<"\",\"UA_class_calls\":"<<classes.calls<<",\"UA_class_pair_draws\":"<<classes.pair_draws<<",\"UA_class_single_fallbacks\":"<<classes.single_fallbacks<<",\"UA_class_empty\":"<<classes.empty<<",\"UA_class_visits\":"<<classes.class_visits<<",\"UA_max_classes\":"<<classes.max_classes<<",\"UA_max_tickets\":"<<classes.max_tickets<<",";
 }
};
