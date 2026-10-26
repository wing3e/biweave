#pragma once

struct ResidualHeavyIndex {
 Graph* graph=nullptr;std::vector<std::vector<int>> columns;std::vector<std::unordered_map<int,U>> position;
 U initial_records=0,updates=0,adds=0,removes=0,checks=0,checked_entries=0;bool active=false;
 bool eligible(int c,I w)const{return w>=2&&graph->target_degree[graph->nr+c]>=2;}
 static void notify(void*p,int r,int c,I old,I w){static_cast<ResidualHeavyIndex*>(p)->update(r,c,old,w);}
 void initialize(Graph&g,bool requested){active=requested;if(!active)return;if(g.residual_mutation_hook)throw std::runtime_error("residual hook already installed");graph=&g;columns.resize(g.nr);position.resize(g.nr);for(const auto&e:g.edges)if(eligible(e.c,e.w)){position[e.r][e.c]=columns[e.r].size();columns[e.r].push_back(e.c);++initial_records;}g.residual_mutation_context=this;g.residual_mutation_hook=&notify;}
 void update(int r,int c,I old,I w){if(!active)throw std::runtime_error("inactive residual hook");const bool before=eligible(c,old),after=eligible(c,w);if((position[r].find(c)!=position[r].end())!=before)throw std::runtime_error("stale residual before write");if(before==after)return;++updates;
  if(after){position[r][c]=columns[r].size();columns[r].push_back(c);++adds;}
  else{U p=position[r].at(c);const int last=columns[r].back();columns[r][p]=last;position[r][last]=p;columns[r].pop_back();position[r].erase(c);++removes;}
 }
 U degree(int r,int excluded=-1)const{const U n=columns[r].size();return n-(excluded>=0&&position[r].count(excluded)?1:0);}
 int choice(int r,int excluded,U k)const{const U n=degree(r,excluded);if(k>=n)throw std::runtime_error("residual choice range");auto it=position[r].find(excluded);if(it!=position[r].end()&&k>=it->second)++k;return columns[r][k];}
 void check(const Graph&g){if(!active)return;++checks;U total=0;for(int r=0;r<g.nr;++r){if(columns[r].size()!=position[r].size())throw std::runtime_error("residual index cardinality");for(U j=0;j<columns[r].size();++j){int c=columns[r][j];if(position[r].at(c)!=j||!eligible(c,g.value(r,c)))throw std::runtime_error("residual index entry");++total;}}U want=0;for(const auto&e:g.edges)want+=eligible(e.c,e.w);if(total!=want||total!=initial_records+adds-removes||updates!=adds+removes)throw std::runtime_error("residual index total");checked_entries+=total;}
};
struct ResidualCycleRefresh {
 struct EdgeStep {int r=0,c=0;I old=0;bool minus=false;};
 struct Problem {std::vector<int>nodes;std::vector<EdgeStep>edges;U entry=0,entry_degree=0;I Mminus=0;bool valid=false;};
 ResidualHeavyIndex heavy;std::vector<int>starts;std::vector<U>stamp,first;U epoch=0;
 bool uniform_delta=true,scan_mode=false,scan_dyadic=false,scan_uniform=false,scan_local=false;U local_cap_calls=0,local_cap_zero_holds=0,max_local_cap=0,local_start_on_cycle_proposals=0,local_scale_ratio_changes=0;__uint128_t local_cap_scan_records=0,local_cap_total=0;U scan_row_calls=0,scan_column_calls=0,scan_row_eligible=0,scan_column_eligible=0,scale_draws=0,max_scale_index=0,max_selected_delta=0;__uint128_t scan_records=0,selected_delta_total=0;U calls=0,empty_starts=0,dead_ends=0,two_cycle_holds=0,proposals=0,accepts=0,rejects=0;
 U start_rows=0,start_columns=0,path_steps=0,max_path_steps=0,prefix_nodes_total=0,cycle_edges_total=0,max_cycle_edges=0;
 U row_entry_proposals=0,column_entry_proposals=0,max_delta=0,changed_cell_writes=0,accept_ratio_max_bits=0;__uint128_t delta_total=0;
 void initialize(Graph&g,bool active,bool uniform=true,const std::string&scan=""){uniform_delta=uniform;scan_mode=!scan.empty();scan_local=scan=="dyadic_local";scan_dyadic=scan=="dyadic_scan"||scan_local;scan_uniform=scan=="uniform_scan";heavy.initialize(g,active&&!scan_mode);if(!active)return;for(int v=0;v<g.nr+g.nc;++v)if(g.target_degree[v]>=2&&(!scan_mode||g.target_strength[v]-g.target_degree[v]>=1))starts.push_back(v);stamp.resize(g.nr+g.nc);first.resize(g.nr+g.nc);}
 U choice_count(const Graph&g,int v,int previous)const{return v<g.nr?heavy.degree(v,previous<0?-1:previous-g.nr):g.adj[v].size()-(previous>=0?1:0);}
 int next_for_choice(const Graph&g,int v,int previous,U k)const{if(v<g.nr)return g.nr+heavy.choice(v,previous<0?-1:previous-g.nr,k);const U n=choice_count(g,v,previous);if(k>=n)throw std::runtime_error("residual column choice range");if(previous>=0){const int id=g.find(previous,v-g.nr);if(id<0)throw std::runtime_error("residual incoming column edge missing");if(k>=U(g.edges[id].pc))++k;}return g.edges[g.adj[v][k]].r;}
 static EdgeStep edge(const Graph&g,int v,int next){EdgeStep x;x.minus=v<g.nr;x.r=x.minus?v:next;x.c=x.minus?next-g.nr:v-g.nr;x.old=g.value(x.r,x.c);if(x.old<=0||(x.minus&&x.old<2))throw std::runtime_error("residual unavailable edge");return x;}
 Problem compile_path(const Graph&g,const std::vector<int>&nodes)const{
  if(nodes.size()<3||nodes.back()<0||nodes.back()>=g.nr+g.nc)throw std::runtime_error("residual malformed path");Problem p;p.nodes=nodes;auto it=std::find(nodes.begin(),nodes.end()-1,nodes.back());if(it==nodes.end()-1)throw std::runtime_error("residual path not closed");p.entry=it-nodes.begin();
  std::set<int>unique(nodes.begin(),nodes.end()-1);if(unique.size()!=nodes.size()-1)throw std::runtime_error("residual not first repeat");
  for(U j=0;j+1<nodes.size();++j){const int v=nodes[j],z=nodes[j+1];if((v<g.nr)==(z<g.nr))throw std::runtime_error("residual nonbipartite path");if(v<g.nr){if(g.target_degree[z]<2|| (j&&nodes[j-1]==z)||heavy.position[v].count(z-g.nr)==0)throw std::runtime_error("residual ineligible decrement");}p.edges.push_back(edge(g,v,z));}
  const U len=p.edges.size()-p.entry;if(len==2)return p;if(len<4||len%2)throw std::runtime_error("residual invalid cycle length");p.Mminus=std::numeric_limits<I>::max();for(U j=p.entry;j<p.edges.size();++j)if(p.edges[j].minus)p.Mminus=std::min(p.Mminus,p.edges[j].old-1);if(p.Mminus<=0)throw std::runtime_error("residual no positive delta");p.valid=true;return p;
 }
 mpq_class acceptance_ratio(const Graph&g,const Problem&p,I delta,bool uniform)const{
  if(!p.valid||delta<1||delta>p.Mminus)throw std::runtime_error("residual invalid delta");mpz_class n=1,d=1;const int entrance=p.nodes[p.entry];
  if(entrance<g.nr){const int excluded=p.entry? p.nodes[p.entry-1]-g.nr:-1;const U oldD=heavy.degree(entrance,excluded);const auto&minus=p.edges[p.entry];const auto&plus=p.edges.back();if(!minus.minus||plus.minus||!oldD)throw std::runtime_error("residual row-entry geometry");const S128 newD=S128(oldD)+(plus.old==1)-(minus.old-delta==1);if(newD<=0||newD>std::numeric_limits<U>::max())throw std::runtime_error("residual reverse row degree");n*=oldD;d*=U(newD);}
  if(uniform){S128 reverseM=std::numeric_limits<I>::max();for(U j=p.entry;j<p.edges.size();++j)if(!p.edges[j].minus)reverseM=std::min(reverseM,S128(p.edges[j].old)+delta-1);if(reverseM<=0||reverseM>std::numeric_limits<I>::max())throw std::runtime_error("residual reverse delta interval");n*=U(p.Mminus);d*=U(reverseM);}
  return rational(n,d);
 }
 void commit(Graph&g,const Problem&p,I delta){if(!p.valid||delta<1||delta>p.Mminus)throw std::runtime_error("residual commit delta");
  for(U j=p.entry;j<p.edges.size();++j){const auto&e=p.edges[j];if(g.value(e.r,e.c)!=e.old)throw std::runtime_error("residual stale commit edge");const S128 w=S128(e.old)+(e.minus?-S128(delta):S128(delta));if(w<1||w>std::numeric_limits<I>::max())throw std::runtime_error("residual positive weight overflow");}
   
  for(bool minus:{true,false})for(U j=p.entry;j<p.edges.size();++j){const auto&e=p.edges[j];if(e.minus==minus)g.set_raw(e.r,e.c,I(S128(e.old)+(minus?-S128(delta):S128(delta))));}
  changed_cell_writes+=p.edges.size()-p.entry;
 }

 static U scale_levels(U excess){if(!excess)throw std::runtime_error("empty scan scale range");U n=0;while(excess){++n;excess>>=1;}return n;}
 std::vector<int> scan_choices(const Graph&g,int v,int previous,I threshold,bool account=false){
  if(threshold<1)throw std::runtime_error("invalid scan threshold");std::vector<int>choices;
  if(account){scan_records+=g.adj[v].size();if(v<g.nr)++scan_row_calls;else ++scan_column_calls;}
  for(int id:g.adj[v]){const auto&e=g.edges[id];if(v<g.nr){const int z=g.nr+e.c;if(z!=previous&&g.target_degree[z]>=2&&S128(e.w)>threshold)choices.push_back(z);}
   else{const int z=e.r;if(z!=previous&&g.target_degree[z]>=2&&S128(g.target_strength[z])-g.target_degree[z]>=threshold)choices.push_back(z);}}
  if(account){if(v<g.nr)scan_row_eligible+=choices.size();else scan_column_eligible+=choices.size();}return choices;
 }
 Problem compile_scan_path(const Graph&g,const std::vector<int>&nodes,I threshold,U supplied_entry_count=0){
  if(threshold<1||nodes.size()<3||nodes.back()<0||nodes.back()>=g.nr+g.nc)throw std::runtime_error("scan malformed path");Problem p;p.nodes=nodes;auto it=std::find(nodes.begin(),nodes.end()-1,nodes.back());if(it==nodes.end()-1)throw std::runtime_error("scan path not closed");p.entry=it-nodes.begin();
  std::set<int>unique(nodes.begin(),nodes.end()-1);if(unique.size()!=nodes.size()-1)throw std::runtime_error("scan not first repeat");
  for(U j=0;j+1<nodes.size();++j){const int v=nodes[j],z=nodes[j+1];if((v<g.nr)==(z<g.nr)|| (j&&nodes[j-1]==z))throw std::runtime_error("scan invalid bipartite nonbacktracking path");
   if(v<g.nr){if(g.target_degree[z]<2||S128(g.value(v,z-g.nr))<=threshold)throw std::runtime_error("scan ineligible decrement");}
   else if(g.target_degree[z]<2||S128(g.target_strength[z])-g.target_degree[z]<threshold)throw std::runtime_error("scan inactive increment endpoint");
   p.edges.push_back(edge(g,v,z));}
  const U len=p.edges.size()-p.entry;if(len<4||len%2)throw std::runtime_error("scan invalid cycle length");p.Mminus=std::numeric_limits<I>::max();for(U j=p.entry;j<p.edges.size();++j)if(p.edges[j].minus)p.Mminus=std::min(p.Mminus,p.edges[j].old-1);if(p.Mminus<threshold)throw std::runtime_error("scan insufficient decrement slack");
  if(nodes[p.entry]<g.nr){const int previous=p.entry?nodes[p.entry-1]:-1;p.entry_degree=supplied_entry_count?supplied_entry_count:scan_choices(g,nodes[p.entry],previous,threshold).size();if(!p.entry_degree)throw std::runtime_error("scan no entry choices");}p.valid=true;return p;
 }
 std::pair<U,U> scan_entry_ratio(const Graph&g,const Problem&p,I delta,I threshold)const{
  if(!p.valid||delta<1||delta>p.Mminus)throw std::runtime_error("scan invalid delta");if(p.nodes[p.entry]>=g.nr)return {1,1};const auto&minus=p.edges[p.entry];const auto&plus=p.edges.back();const U oldD=p.entry_degree;if(!oldD||!minus.minus||plus.minus)throw std::runtime_error("scan row-entry geometry");
  const S128 newD=S128(oldD)+(S128(plus.old)<=threshold)-(S128(minus.old)-delta<=threshold);if(newD<=0||newD>std::numeric_limits<int>::max())throw std::runtime_error("scan reverse row degree");return {oldD,U(newD)};
 }
 mpq_class scan_acceptance_ratio(const Graph&g,const Problem&p,I delta,I threshold,bool post_uniform)const{
  const auto q=scan_entry_ratio(g,p,delta,threshold);mpz_class n=q.first,d=q.second;
  if(post_uniform){S128 reverseM=std::numeric_limits<I>::max();for(U j=p.entry;j<p.edges.size();++j)if(!p.edges[j].minus)reverseM=std::min(reverseM,S128(p.edges[j].old)+delta-1);if(reverseM<=0||reverseM>std::numeric_limits<I>::max())throw std::runtime_error("scan reverse delta range");n*=U(p.Mminus);d*=U(reverseM);}return rational(n,d);
 }
 struct LocalCap {U cap=0;std::array<std::pair<U,int>,3>top{{{0,-1},{0,-1},{0,-1}}};};

 LocalCap local_cap(const Graph&g,int start,bool account=false){
  if(start<0||start>=g.nr+g.nc)throw std::runtime_error("local cap start coordinate");LocalCap p;
  if(account){++local_cap_calls;local_cap_scan_records+=g.adj[start].size();}
  for(int id:g.adj[start]){const auto&e=g.edges[id];const int z=start<g.nr?g.nr+e.c:e.r;if(g.target_degree[z]<2)continue;const U c=U(e.w-1);for(U j=0;j<3;++j)if(p.top[j].second<0||c>p.top[j].first){for(U k=2;k>j;--k)p.top[k]=p.top[k-1];p.top[j]={c,z};break;}}
  p.cap=p.top[0].first;if(account){local_cap_total+=p.cap;max_local_cap=std::max(max_local_cap,p.cap);}return p;
 }
 U reverse_local_cap(const Graph&g,const Problem&p,I delta,const LocalCap&old)const{
  if(!p.valid||delta<1||delta>p.Mminus||old.cap==0)throw std::runtime_error("local reverse cap geometry");if(p.entry)return old.cap;
  const int start=p.nodes[0];const auto&a=p.edges.front();const auto&b=p.edges.back();const int ac=start<g.nr?g.nr+a.c:a.r,bc=start<g.nr?g.nr+b.c:b.r;if(ac==bc)throw std::runtime_error("local reverse distinct incident edges");U c=0;
  for(const auto&v:old.top)if(v.second>=0&&v.second!=ac&&v.second!=bc){c=v.first;break;}
  for(const auto*e:{&a,&b}){const S128 w=S128(e->old)+(e->minus?-S128(delta):S128(delta));if(w<1||w>std::numeric_limits<I>::max())throw std::runtime_error("local reverse incident overflow");c=std::max(c,U(w-1));}if(!c)throw std::runtime_error("local reverse zero scale range");return c;
 }
 std::pair<U,U> local_acceptance_integer_ratio(const Graph&g,const Problem&p,I delta,const LocalCap&cap)const{
  const auto entry=scan_entry_ratio(g,p,delta,delta);const U before=scale_levels(cap.cap),after=scale_levels(reverse_local_cap(g,p,delta,cap));const __uint128_t n=__uint128_t(entry.first)*before,d=__uint128_t(entry.second)*after;
  if(!n||!d||n>std::numeric_limits<U>::max()||d>std::numeric_limits<U>::max())throw std::runtime_error("local exact ratio integer range");return {U(n),U(d)};
 }
 mpq_class local_acceptance_ratio(const Graph&g,const Problem&p,I delta,const LocalCap&cap)const{const auto q=local_acceptance_integer_ratio(g,p,delta,cap);return rational(mpz_class(q.first),mpz_class(q.second));}
 bool step_scan(Engine&e,Graph&g){++calls;if(starts.empty()){++empty_starts;return false;}const int start=starts[e.rng.below(starts.size())];if(start<g.nr)++start_rows;else++start_columns;
  LocalCap cap;if(scan_local){cap=local_cap(g,start,true);if(!cap.cap){++local_cap_zero_holds;++dead_ends;return false;}}
  I threshold=1;if(scan_dyadic){const U excess=scan_local?cap.cap:U(g.target_strength[start]-g.target_degree[start]),k=e.rng.below(scale_levels(excess));threshold=I(U(1)<<k);++scale_draws;max_scale_index=std::max(max_scale_index,k);selected_delta_total+=U(threshold);max_selected_delta=std::max(max_selected_delta,U(threshold));}
  if(++epoch==0){std::fill(stamp.begin(),stamp.end(),U(0));epoch=1;}std::vector<int>nodes{start};std::vector<U>degrees;stamp[start]=epoch;first[start]=0;
  for(;;){const int v=nodes.back(),prev=nodes.size()>1?nodes[nodes.size()-2]:-1;const auto choices=scan_choices(g,v,prev,threshold,true);if(choices.empty()){++dead_ends;max_path_steps=std::max(max_path_steps,U(nodes.size()-1));return false;}
   degrees.push_back(choices.size());const int next=choices[e.rng.below(choices.size())];nodes.push_back(next);++path_steps;if(stamp[next]==epoch)break;stamp[next]=epoch;first[next]=nodes.size()-1;if(nodes.size()>stamp.size())throw std::runtime_error("scan natural first-repeat bound");}
  max_path_steps=std::max(max_path_steps,U(nodes.size()-1));const U entry=first[nodes.back()];const auto p=compile_scan_path(g,nodes,threshold,degrees.at(entry));++proposals;prefix_nodes_total+=p.entry;const U len=p.edges.size()-p.entry;cycle_edges_total+=len;max_cycle_edges=std::max(max_cycle_edges,len);if(p.nodes[p.entry]<g.nr)++row_entry_proposals;else++column_entry_proposals;
  const I delta=scan_dyadic?threshold:scan_uniform?I(e.rng.below(U(p.Mminus)))+1:1;delta_total+=U(delta);max_delta=std::max(max_delta,U(delta));bool accepted;
  if(scan_dyadic){auto q=scan_local?local_acceptance_integer_ratio(g,p,delta,cap):scan_entry_ratio(g,p,delta,threshold);if(scan_local){local_start_on_cycle_proposals+=(p.entry==0);local_scale_ratio_changes+=scale_levels(cap.cap)!=scale_levels(reverse_local_cap(g,p,delta,cap));}const U divisor=std::gcd(q.first,q.second);q.first/=divisor;q.second/=divisor;const U largest=std::max(q.first,q.second);U bits=0;for(U t=largest;t;t>>=1)++bits;accept_ratio_max_bits=std::max(accept_ratio_max_bits,bits);accepted=q.first>=q.second||e.rng.below(q.second)<q.first;}
  else{const auto q=scan_acceptance_ratio(g,p,delta,threshold,scan_uniform);accept_ratio_max_bits=std::max(accept_ratio_max_bits,U(std::max(mpz_sizeinbase(q.get_num().get_mpz_t(),2),mpz_sizeinbase(q.get_den().get_mpz_t(),2))));accepted=exact_accept(e.rng,q);}
  if(!accepted){++rejects;return false;}commit(g,p,delta);++accepts;++e.stat.changed_outer;return true;
 }
 bool step(Engine&e,Graph&g){if(scan_mode)return step_scan(e,g);++calls;if(starts.empty()){++empty_starts;return false;}const int start=starts[e.rng.below(starts.size())];if(start<g.nr)++start_rows;else++start_columns;
  if(++epoch==0){std::fill(stamp.begin(),stamp.end(),U(0));epoch=1;}
  std::vector<int>nodes{start};stamp[start]=epoch;first[start]=0;
  for(;;){const int v=nodes.back(),prev=nodes.size()>1?nodes[nodes.size()-2]:-1;const U count=choice_count(g,v,prev);if(!count){++dead_ends;max_path_steps=std::max(max_path_steps,U(nodes.size()-1));return false;}
   const int next=next_for_choice(g,v,prev,e.rng.below(count));nodes.push_back(next);++path_steps;if(stamp[next]==epoch)break;stamp[next]=epoch;first[next]=nodes.size()-1;
   if(nodes.size()>stamp.size())throw std::runtime_error("residual natural first-repeat bound");
  }
  max_path_steps=std::max(max_path_steps,U(nodes.size()-1));const auto p=compile_path(g,nodes);if(!p.valid){++two_cycle_holds;return false;}
  ++proposals;prefix_nodes_total+=p.entry;const U len=p.edges.size()-p.entry;cycle_edges_total+=len;max_cycle_edges=std::max(max_cycle_edges,len);
  if(p.nodes[p.entry]<g.nr)++row_entry_proposals;else++column_entry_proposals;
  const I delta=uniform_delta?I(e.rng.below(U(p.Mminus)))+1:1;delta_total+=U(delta);max_delta=std::max(max_delta,U(delta));const mpq_class q=acceptance_ratio(g,p,delta,uniform_delta);accept_ratio_max_bits=std::max(accept_ratio_max_bits,U(std::max(mpz_sizeinbase(q.get_num().get_mpz_t(),2),mpz_sizeinbase(q.get_den().get_mpz_t(),2))));
  if(!exact_accept(e.rng,q)){++rejects;return false;}commit(g,p,delta);++accepts;++e.stat.changed_outer;return true;
 }
};
