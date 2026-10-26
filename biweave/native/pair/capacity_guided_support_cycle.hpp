#pragma once
#include <algorithm>
#include <limits>
#include <ostream>
#include <stdexcept>
#include <unordered_map>
#include <unordered_set>
#include <vector>

struct CapacityGuidedSupportCycle {
 struct EdgeIndex {
  struct IndexedEdge {int r=0,c=0;U pr=0,pc=0;};
  int nr=0;
  std::vector<IndexedEdge> edges;
  std::vector<std::vector<U>> adj;
  std::unordered_map<U,U> position;
  void initialize(int rows,int columns){nr=rows;adj.resize(U(rows)+U(columns));}
  bool contains(int r,int c)const{return position.count(cellkey(r,c))!=0;}
  void add(int r,int c){
   const U key=cellkey(r,c),id=edges.size();
   if(position.count(key))throw std::runtime_error("CGC duplicate indexed edge");
   edges.push_back({r,c,U(adj[r].size()),U(adj[nr+c].size())});
   adj[r].push_back(id);adj[nr+c].push_back(id);position.emplace(key,id);
  }
  void remove(int r,int c){
   auto it=position.find(cellkey(r,c));if(it==position.end())throw std::runtime_error("CGC missing indexed edge");
   const U id=it->second;const IndexedEdge old=edges[id];
   auto&ra=adj[r];U last=ra.back();ra[old.pr]=last;edges[last].pr=old.pr;ra.pop_back();
   auto&ca=adj[nr+c];last=ca.back();ca[old.pc]=last;edges[last].pc=old.pc;ca.pop_back();
   position.erase(it);const U end=edges.size()-1;
   if(id!=end){const auto moved=edges.back();edges[id]=moved;
    adj[moved.r][moved.pr]=id;adj[nr+moved.c][moved.pc]=id;position[cellkey(moved.r,moved.c)]=id;}
   edges.pop_back();
  }
  void audit()const{
   if(position.size()!=edges.size())throw std::runtime_error("CGC index cardinality");
   U entries=0;
   for(U id=0;id<edges.size();++id){const auto&x=edges[id];
    if(position.at(cellkey(x.r,x.c))!=id||adj[x.r].at(x.pr)!=id||adj[nr+x.c].at(x.pc)!=id)
     throw std::runtime_error("CGC index positions");}
   for(U v=0;v<adj.size();++v)for(U k=0;k<adj[v].size();++k){const U id=adj[v][k];
    if(id>=edges.size())throw std::runtime_error("CGC index adjacency ID");const auto&x=edges[id];
    if(v<U(nr)?(x.r!=int(v)||x.pr!=k):(nr+x.c!=int(v)||x.pc!=k))
     throw std::runtime_error("CGC index adjacency position");++entries;}
   if(entries!=2*edges.size())throw std::runtime_error("CGC index adjacency count");
  }
 };
 Graph*graph=nullptr;
 bool requested=false,active=false,weighted_first=true,static_no_cycle=false;
 bool maximum_degree2=true,in_conditional_commit=false,initialized=false;
 void*previous_context=nullptr;
 void(*previous_hook)(void*,int,int,I,I)=nullptr;
 EdgeIndex support,candidate,down_index;
 bool residual_aux_gibbs=false,gibbs_nonself=true;
 U gibbs_draws=0,gibbs_zero_draws=0,gibbs_row_meetings=0,gibbs_column_meetings=0;
 U residual_hook_calls=0,down_adds=0,down_removes=0,initial_down_edges=0;
 U residual_calls=0,residual_dead=0,residual_proposals=0,residual_accepts=0,residual_MH_holds=0;
 U residual_down_decisions=0,residual_reverse_decisions=0,residual_overlay_edges=0;
 std::vector<S128>capacity,published_capacity;
 std::vector<unsigned char>dirty_flag;
 std::vector<int>dirty_vertices,positive_roots,root_position;
 std::unordered_set<U>dirty_support_cells;
 Fenwick root_tree;
 U row_capacity_total=0,positive_rows=0,positive_columns=0;
 std::vector<U>stamp,first;U generation=0;
 U calls=0,cycles=0,changes=0,draws=0,zero_draws=0,changed_cell_writes=0;
 U static_holds=0,zero_capacity_holds=0,dynamic_no_cycle_holds=0;
 U empty_holds=0,leaf_holds=0,cap_holds=0,singleton_holds=0;
 U paths=0,path_steps=0,max_path_steps=0,cycle_edges=0,max_cycle_edges=0,interval_max=0;
 __uint128_t interval_total=0;
 U mutation_hook_calls=0,eligible_mutations=0,conditional_hook_writes=0;
 U support_adds=0,support_removes=0,support_events=0;
 U candidate_adds=0,candidate_removes=0;
 U synchronize_calls=0,synchronize_no_work=0,synchronized_vertices=0;
 U capacity_threshold_crossings=0,reconcile_scan_records=0,reconciled_cells=0,root_tree_updates=0;
 U initial_support_edges=0,initial_candidate_edges=0,initial_positive_rows=0,initial_positive_columns=0;
 U max_dirty_vertices=0,max_dirty_cells=0,index_checks=0,index_checked_entries=0;

 bool eligible(int r,int c)const{
  return graph->target_degree[r]>=2&&graph->target_degree[graph->nr+c]>=2;
 }
 static S128 contribution(I w){return w>0?S128(w)-1:0;}
 static U unsigned_checked(S128 value,const char*message){
  if(value<0||value>S128(std::numeric_limits<U>::max()))throw std::runtime_error(message);return U(value);
 }
 void mark_dirty(int vertex){
  if(!dirty_flag[vertex]){dirty_flag[vertex]=1;dirty_vertices.push_back(vertex);}
 }
 static void notify(void*context,int r,int c,I old,I now){
  auto*self=static_cast<CapacityGuidedSupportCycle*>(context);++self->mutation_hook_calls;
  if(self->residual_aux_gibbs)self->update_down(r,c,old,now);
  if(self->in_conditional_commit){

   if(old<=0||now<=0||!self->eligible(r,c))throw std::runtime_error("CGC invalid atomic support write");
   ++self->conditional_hook_writes;
  }else self->update(r,c,old,now);
   
  if(self->previous_hook)self->previous_hook(self->previous_context,r,c,old,now);
 }
 void update(int r,int c,I old,I now){
  if(!active)throw std::runtime_error("CGC inactive mutation observer");
  if(!eligible(r,c))return;++eligible_mutations;
  const int column=graph->nr+c;const S128 delta=contribution(now)-contribution(old);
  if(delta){
   if(capacity[r]+delta<0||capacity[column]+delta<0)throw std::runtime_error("CGC capacity underflow");
   capacity[r]+=delta;capacity[column]+=delta;mark_dirty(r);mark_dirty(column);
  }
  if((old>0)!=(now>0)){
   ++support_events;mark_dirty(r);mark_dirty(column);dirty_support_cells.insert(cellkey(r,c));

   if(now>0){support.add(r,c);++support_adds;}else{support.remove(r,c);++support_removes;}
  }
  max_dirty_vertices=std::max(max_dirty_vertices,U(dirty_vertices.size()));
  max_dirty_cells=std::max(max_dirty_cells,U(dirty_support_cells.size()));
 }
 void root_add(int r){
  if(root_position[r]>=0)throw std::runtime_error("CGC duplicate positive root");
  root_position[r]=int(positive_roots.size());positive_roots.push_back(r);
 }
 void root_remove(int r){
  const int position=root_position[r];if(position<0)throw std::runtime_error("CGC missing positive root");
  const int last=positive_roots.back();positive_roots[position]=last;root_position[last]=position;
  positive_roots.pop_back();root_position[r]=-1;
 }
 void update_down(int r,int c,I old,I now){
  ++residual_hook_calls;if(!eligible(r,c))return;
  if(old<2&&now>=2){down_index.add(r,c);++down_adds;}
  else if(old>=2&&now<2){down_index.remove(r,c);++down_removes;}
 }
 void initialize(Graph&g,bool want,bool weighted=true,bool residual=false,bool nonself=true){
  if(initialized)throw std::runtime_error("CGC initialization repeated");initialized=true;
  graph=&g;requested=want;weighted_first=weighted;residual_aux_gibbs=residual;gibbs_nonself=nonself;
  if(residual&&(!want||weighted))throw std::runtime_error("residual auxiliary Gibbs requires requested uniform CGC");
  if(!want)return;
  U nonleaf_rows=0,nonleaf_columns=0;
  for(U v=0;v<g.target_degree.size();++v){const int d=g.target_degree[v];maximum_degree2&=d<=2;
   if(d>=2){if(v<U(g.nr))++nonleaf_rows;else++nonleaf_columns;}}
  static_no_cycle=nonleaf_rows<2||nonleaf_columns<2;
   
  if(static_no_cycle)return;
  active=true;const U vertices=U(g.nr)+U(g.nc);
  support.initialize(g.nr,g.nc);candidate.initialize(g.nr,g.nc);
  if(residual_aux_gibbs)down_index.initialize(g.nr,g.nc);
  capacity.assign(vertices,0);dirty_flag.assign(vertices,0);stamp.assign(vertices,0);first.resize(vertices);
  root_position.assign(g.nr,-1);if(weighted_first)root_tree=Fenwick(g.nr);
  for(const auto&x:g.edges)if(eligible(x.r,x.c)){
   support.add(x.r,x.c);capacity[x.r]+=S128(x.w)-1;capacity[g.nr+x.c]+=S128(x.w)-1;
   if(residual_aux_gibbs&&x.w>=2)down_index.add(x.r,x.c);}
  initial_down_edges=down_index.edges.size();
  S128 total=0;
  for(U v=0;v<vertices;++v){
   if(capacity[v]<0||capacity[v]>g.target_strength[v])throw std::runtime_error("CGC initial capacity range");
   if(v<U(g.nr)){total+=capacity[v];if(capacity[v]>0){++positive_rows;root_add(int(v));
     if(weighted_first)root_tree.add(int(v),I(capacity[v]));}}
   else positive_columns+=capacity[v]>0;
  }
  row_capacity_total=unsigned_checked(total,"CGC root capacity total overflow");
  for(const auto&x:support.edges)if(capacity[x.r]>0&&capacity[g.nr+x.c]>0)candidate.add(x.r,x.c);
  published_capacity=capacity;initial_support_edges=support.edges.size();initial_candidate_edges=candidate.edges.size();
  initial_positive_rows=positive_rows;initial_positive_columns=positive_columns;
  previous_context=g.residual_mutation_context;previous_hook=g.residual_mutation_hook;
  if(previous_hook==&notify)throw std::runtime_error("CGC mutation-hook cycle");
  g.residual_mutation_context=this;g.residual_mutation_hook=&notify;
 }
 void initialise(Graph&g,bool want,bool weighted=true){initialize(g,want,weighted);}
 void synchronize(Graph&g){
  if(graph!=&g)throw std::runtime_error("CGC graph identity");if(!active)return;++synchronize_calls;
  if(g.D)throw std::runtime_error("CGC synchronize requires a complete valid commit");
  if(dirty_vertices.empty()&&dirty_support_cells.empty()){++synchronize_no_work;return;}
  for(int v:dirty_vertices){
   if(g.degree[v]!=g.target_degree[v]||capacity[v]<0||capacity[v]>g.target_strength[v])
    throw std::runtime_error("CGC commit capacity/degree range");
   const S128 old=published_capacity[v],now=capacity[v];const bool before=old>0,after=now>0;
   if(v<g.nr){
    row_capacity_total=unsigned_checked(S128(row_capacity_total)+now-old,"CGC root capacity update overflow");
    if(weighted_first&&now!=old){root_tree.add(v,I(now-old));++root_tree_updates;}
    if(before!=after){if(after){root_add(v);++positive_rows;}else{root_remove(v);--positive_rows;}}
   }else if(before!=after){if(after)++positive_columns;else --positive_columns;}
   if(before!=after){
    ++capacity_threshold_crossings;

    for(U id:support.adj[v]){const auto&x=support.edges[id];dirty_support_cells.insert(cellkey(x.r,x.c));++reconcile_scan_records;}
   }
   published_capacity[v]=now;++synchronized_vertices;
  }
  max_dirty_cells=std::max(max_dirty_cells,U(dirty_support_cells.size()));
  for(U key:dirty_support_cells){const int r=int(key>>32),c=int(uint32_t(key));
   const bool want=support.contains(r,c)&&capacity[r]>0&&capacity[g.nr+c]>0;
   const bool present=candidate.contains(r,c);
   if(want&&!present){candidate.add(r,c);++candidate_adds;}
   else if(!want&&present){candidate.remove(r,c);++candidate_removes;}++reconciled_cells;
  }
  for(int v:dirty_vertices)dirty_flag[v]=0;dirty_vertices.clear();dirty_support_cells.clear();
 }
 bool refresh(Engine&e,Graph&g,const std::vector<U>&path,U start){
  const U length=path.size()-start;if(length<4||length%2)throw std::runtime_error("CGC invalid simple bipartite cycle");
  struct Cell{int r,c;I w;bool plus;};std::vector<Cell>cells;cells.reserve(length);
  S128 lower=-S128(std::numeric_limits<I>::max()),upper=std::numeric_limits<I>::max();
  for(U j=0;j<length;++j){const auto&x=candidate.edges.at(path[start+j]);const I weight=g.value(x.r,x.c);
   if(weight<=0||capacity[x.r]<=0||capacity[g.nr+x.c]<=0)throw std::runtime_error("CGC stale cycle descriptor");
   const bool plus=j%2==0;cells.push_back({x.r,x.c,weight,plus});
   if(plus){lower=std::max(lower,1-S128(weight));upper=std::min(upper,S128(std::numeric_limits<I>::max())-weight);}
   else{lower=std::max(lower,S128(weight)-std::numeric_limits<I>::max());upper=std::min(upper,S128(weight)-1);}
  }
  if(lower>0||upper<0||lower>upper)throw std::runtime_error("CGC current state missing from interval");
  const U width=unsigned_checked(upper-lower+1,"CGC conditional interval overflow");
  ++cycles;cycle_edges+=length;max_cycle_edges=std::max(max_cycle_edges,length);
  interval_total+=width;interval_max=std::max(interval_max,width);
  if(width==1){++singleton_holds;return false;}
  S128 delta=lower+S128(e.rng.below(width-1));if(delta>=0)++delta;++draws;
  if(!delta){++zero_draws;throw std::runtime_error("CGC nonself delta unexpectedly zero");}
  for(const auto&x:cells){const S128 now=S128(x.w)+(x.plus?delta:-delta);
   if(now<1||now>std::numeric_limits<I>::max()||g.value(x.r,x.c)!=x.w)
    throw std::runtime_error("CGC invalid positive conditional write");}
  if(in_conditional_commit||!dirty_vertices.empty()||!dirty_support_cells.empty())throw std::runtime_error("CGC unsynchronized conditional commit");
  const U before=e.stat.cell_updates;in_conditional_commit=true;
  try{for(const auto&x:cells)g.set_raw(x.r,x.c,I(S128(x.w)+(x.plus?delta:-delta)));}
  catch(...){in_conditional_commit=false;throw;}
  in_conditional_commit=false;
  if(e.stat.cell_updates-before!=length)throw std::runtime_error("CGC conditional cell counter");
  ++changes;changed_cell_writes+=length;++e.stat.changed_outer;return true;
 }

 mpz_class gibbs_z(U value)const{return mpz_class(std::to_string(value));}
 bool residual_refresh(Engine&e,Graph&g,int root,const std::vector<U>&path,U start){
  const U length=path.size()-start;
  if(length<4||length%2)throw std::runtime_error("Gibbs invalid simple bipartite cycle");
  ++cycles;cycle_edges+=length;max_cycle_edges=std::max(max_cycle_edges,length);
  S128 lower=-S128(std::numeric_limits<I>::max()),upper=std::numeric_limits<I>::max();
  for(U j=start;j<path.size();++j){const auto&x=candidate.edges.at(path[j]);const I w=g.value(x.r,x.c);
   if(w<=0||capacity[x.r]<=0||capacity[g.nr+x.c]<=0)throw std::runtime_error("Gibbs stale positive descriptor");

   if(g.target_degree[x.r]<2||g.target_degree[g.nr+x.c]<2||g.target_strength[x.r]<0||g.target_strength[g.nr+x.c]<0)
    throw std::runtime_error("Gibbs positive-line margin certificate");
   if(j%2==0)upper=std::min(upper,S128(w)-1);
   else lower=std::max(lower,1-S128(w));
  }
  if(lower>0||upper<0||lower>upper)throw std::runtime_error("Gibbs current line state missing");
  const U width=unsigned_checked(upper-lower+1,"Gibbs conditional line width overflow");
  interval_total+=width;interval_max=std::max(interval_max,width);
  if(width==1){++singleton_holds;return false;}
  mpz_class wI=2,wL=1,wU=1;
  if(start%2==0){
   ++gibbs_row_meetings;const auto&first_edge=candidate.edges.at(path[start]);
   const auto&last_edge=candidate.edges.at(path.back());const int meeting=first_edge.r;
   if(last_edge.r!=meeting)throw std::runtime_error("Gibbs row meeting mismatch");
   const I wf=g.value(first_edge.r,first_edge.c),wl=g.value(last_edge.r,last_edge.c);
   S128 k=S128(down_index.adj.at(meeting).size())-I(wf>=2)-I(wl>=2)+2;
   if(start){const auto&previous=candidate.edges.at(path[start-1]);
    if(previous.r!=meeting)throw std::runtime_error("Gibbs prefix preceding meeting mismatch");
    k-=g.value(previous.r,previous.c)>=2;
   }
   if(k<2)throw std::runtime_error("Gibbs virtual interior down count below2");
   const U K=unsigned_checked(k,"Gibbs k overflow");
   const U nL=U(S128(wl)+lower==1),nU=U(S128(wf)-upper==1);
   wI=2*gibbs_z(K-nL)*gibbs_z(K-nU);
   wL=gibbs_z(K)*gibbs_z(K-nU);wU=gibbs_z(K)*gibbs_z(K-nL);
  }else ++gibbs_column_meetings;
  const U interior_count=width-2;
  const mpz_class interior_mass=gibbs_z(interior_count)*wI;
  const mpz_class total=wL+interior_mass+wU;
  auto state_weight=[&](S128 delta)->mpz_class{
   if(delta==lower)return wL;if(delta==upper)return wU;return wI;
  };
  const mpz_class current_weight=state_weight(0);
  mpz_class zero_begin=0;
  if(0==upper)zero_begin=wL+interior_mass;
  else if(0!=lower)zero_begin=wL+gibbs_z(unsigned_checked(-lower-1,"Gibbs zero rank"))*wI;
  mpz_class available=total;if(gibbs_nonself)available-=current_weight;
  if(available<=0)throw std::runtime_error("Gibbs missing nonself conditional state");
  mpz_class rank=zbig(e.rng.below_big(bigz(available)));++gibbs_draws;
  if(gibbs_nonself&&rank>=zero_begin)rank+=current_weight;
  S128 delta=lower;
  if(rank>=wL){rank-=wL;
   if(rank<interior_mass){const mpz_class index=rank/wI;
    delta=lower+1+S128(U(std::stoull(index.get_str())));
   }else delta=upper;
  }
  if(!delta){if(gibbs_nonself)throw std::runtime_error("Gibbs nonself proposed zero");++gibbs_zero_draws;return false;}
  ++draws;++residual_proposals;
  if(gibbs_nonself){const mpz_class proposed_weight=state_weight(delta);
   const mpq_class acceptance=rational(total-current_weight,total-proposed_weight);
   if(!exact_accept(e.rng,acceptance)){++residual_MH_holds;return false;}
  }
  for(U j=start;j<path.size();++j){const auto&x=candidate.edges.at(path[j]);
   const S128 now=S128(g.value(x.r,x.c))+(j%2==0?-delta:delta);
   if(now<1||now>std::numeric_limits<I>::max())throw std::runtime_error("Gibbs positive/int64 line write invalid");
  }
  if(in_conditional_commit||!dirty_vertices.empty()||!dirty_support_cells.empty())
   throw std::runtime_error("Gibbs unsynchronized conditional commit");
  const U before=e.stat.cell_updates;in_conditional_commit=true;
  try{for(U j=start;j<path.size();++j){const auto&x=candidate.edges.at(path[j]);
    g.set_raw(x.r,x.c,I(S128(g.value(x.r,x.c))+(j%2==0?-delta:delta)));}}
  catch(...){in_conditional_commit=false;throw;}
  in_conditional_commit=false;
  if(e.stat.cell_updates-before!=length)throw std::runtime_error("Gibbs conditional cell counter");
  ++residual_accepts;++changes;changed_cell_writes+=length;++e.stat.changed_outer;return true;
 }
 U residual_pick_down(Engine&e,int row,U previous){
  const U degree=down_index.adj.at(row).size();U excluded=degree;
  if(previous!=std::numeric_limits<U>::max()){
   const auto&x=candidate.edges.at(previous);const auto it=down_index.position.find(cellkey(x.r,x.c));
   if(it!=down_index.position.end())excluded=down_index.edges.at(it->second).pr;
  }
  const U count=degree-U(excluded<degree);++residual_down_decisions;
  if(!count)return std::numeric_limits<U>::max();
  U pick=e.rng.below(count);if(pick>=excluded)++pick;
  const auto&x=down_index.edges.at(down_index.adj.at(row).at(pick));
  return candidate.position.at(cellkey(x.r,x.c));
 }
 bool residual_step(Engine&e,Graph&g){
  if(graph!=&g||!requested||weighted_first)throw std::runtime_error("RA unrequested/nonuniform update");
  ++calls;++residual_calls;++e.stat.work;
  if(static_no_cycle){++static_holds;return false;}
  if(!active)throw std::runtime_error("RA inactive update");synchronize(g);
  if(!row_capacity_total||positive_roots.empty()){++zero_capacity_holds;return false;}
  if(positive_rows<2||positive_columns<2){++dynamic_no_cycle_holds;return false;}
  if(candidate.edges.empty()){++empty_holds;return false;}
  const int root=positive_roots[e.rng.below(positive_roots.size())];int vertex=root;
  if(capacity[root]<=0||down_index.adj[root].empty())throw std::runtime_error("RA positive root lacks down edge");
  if(++generation==0){std::fill(stamp.begin(),stamp.end(),0);generation=1;}
  U id=residual_pick_down(e,root,std::numeric_limits<U>::max());
  stamp[root]=generation;first[root]=0;std::vector<U>path;path.reserve(256);++paths;
  const U natural=positive_rows+positive_columns+1;
  const U limit=maximum_degree2?natural:std::min(U(256),natural);
  for(U j=0;j<limit;++j){
   if(id==std::numeric_limits<U>::max()){++residual_dead;++leaf_holds;return false;}
   path.push_back(id);++path_steps;const auto&x=candidate.edges.at(id);
   const int next=vertex<g.nr?g.nr+x.c:x.r;
   max_path_steps=std::max(max_path_steps,U(path.size()));
   if(stamp[next]==generation)return residual_refresh(e,g,root,path,first[next]);
   stamp[next]=generation;first[next]=path.size();
   if(next<g.nr)id=residual_pick_down(e,next,id);
   else{
    const U degree=candidate.adj.at(next).size();
    if(degree<2){++residual_dead;++leaf_holds;return false;}
    U pick=e.rng.below(degree-1);if(pick>=x.pc)++pick;id=candidate.adj[next][pick];
   }
   vertex=next;
  }
  ++cap_holds;return false;
 }

 bool step(Engine&e,Graph&g){
  if(residual_aux_gibbs)return residual_step(e,g);
  if(graph!=&g||!requested)throw std::runtime_error("CGC unrequested update");++calls;++e.stat.work;
  if(static_no_cycle){++static_holds;return false;}
  if(!active)throw std::runtime_error("CGC inactive ordinary update");synchronize(g);
  if(!row_capacity_total||positive_roots.empty()){++zero_capacity_holds;return false;}
  if(positive_rows<2||positive_columns<2){++dynamic_no_cycle_holds;return false;}
  if(candidate.edges.empty()){++empty_holds;return false;}
  const int row=weighted_first?root_tree.select(e.rng.below(row_capacity_total)):
   positive_roots[e.rng.below(positive_roots.size())];
  if(capacity[row]<=0||candidate.adj[row].empty())throw std::runtime_error("CGC positive root has no candidate edge");
  if(++generation==0){std::fill(stamp.begin(),stamp.end(),0);generation=1;}
  U id=candidate.adj[row][e.rng.below(candidate.adj[row].size())];int vertex=row;
  stamp[row]=generation;first[row]=0;std::vector<U>path;path.reserve(256);++paths;

  const U natural=positive_rows+positive_columns+1;
  const U limit=maximum_degree2?natural:std::min(U(256),natural);
  for(U j=0;j<limit;++j){
   path.push_back(id);++path_steps;const auto&x=candidate.edges[id];
   const int next=vertex<g.nr?g.nr+x.c:x.r;
   if(stamp[next]==generation){max_path_steps=std::max(max_path_steps,U(path.size()));return refresh(e,g,path,first[next]);}
   stamp[next]=generation;first[next]=path.size();const U degree=candidate.adj[next].size();
   if(degree<2){++leaf_holds;max_path_steps=std::max(max_path_steps,U(path.size()));return false;}
   const U previous=next<g.nr?x.pr:x.pc;U pick=e.rng.below(degree-1);if(pick>=previous)++pick;
   id=candidate.adj[next][pick];vertex=next;
  }
  ++cap_holds;max_path_steps=std::max(max_path_steps,U(path.size()));return false;
 }
 void check(Graph&g){
  if(graph!=&g)throw std::runtime_error("CGC check graph identity");if(!active)return;synchronize(g);++index_checks;
  support.audit();candidate.audit();std::vector<S128>want(capacity.size(),0);U h=0,a=0;
  for(const auto&x:g.edges)if(eligible(x.r,x.c)){
   ++h;want[x.r]+=S128(x.w)-1;want[g.nr+x.c]+=S128(x.w)-1;
   if(!support.contains(x.r,x.c))throw std::runtime_error("CGC missing H edge");
   const bool eligible_capacity=capacity[x.r]>0&&capacity[g.nr+x.c]>0;a+=eligible_capacity;
   if(candidate.contains(x.r,x.c)!=eligible_capacity)throw std::runtime_error("CGC candidate membership");
  }
  if(want!=capacity||capacity!=published_capacity||h!=support.edges.size()||a!=candidate.edges.size())
   throw std::runtime_error("CGC full capacity/index mismatch");
  if(h!=initial_support_edges+support_adds-support_removes||a!=initial_candidate_edges+candidate_adds-candidate_removes)
   throw std::runtime_error("CGC edge update accounting");
  U rows=0,columns=0;S128 total=0;std::vector<U>prefix(g.nr+1,0);
  for(U v=0;v<capacity.size();++v){
   if(capacity[v]<0||capacity[v]>g.target_strength[v]||dirty_flag[v])throw std::runtime_error("CGC final capacity range");
   if(v<U(g.nr)){rows+=capacity[v]>0;total+=capacity[v];
    if((root_position[v]>=0)!=(capacity[v]>0))throw std::runtime_error("CGC root membership");
    prefix[v+1]=unsigned_checked(total,"CGC audited row total overflow");}
   else columns+=capacity[v]>0;
  }
  if(rows!=positive_rows||columns!=positive_columns||rows!=positive_roots.size()||U(total)!=row_capacity_total)
   throw std::runtime_error("CGC positive capacity totals");
  for(U i=0;i<positive_roots.size();++i)if(root_position[positive_roots[i]]!=int(i))throw std::runtime_error("CGC root position");
  if(weighted_first){
   if(root_tree.total()!=row_capacity_total)throw std::runtime_error("CGC Fenwick total");
   for(U i=1;i<root_tree.tree.size();++i)if(root_tree.tree[i]!=prefix[i]-prefix[i-(i&(~i+1))])
    throw std::runtime_error("CGC Fenwick point sum");
  }
  if(residual_aux_gibbs){
   down_index.audit();U wanted=0;for(const auto&x:g.edges)if(eligible(x.r,x.c)&&x.w>=2){
    ++wanted;if(!down_index.contains(x.r,x.c))throw std::runtime_error("residual missing down-index edge");}
   if(wanted!=down_index.edges.size()||wanted!=initial_down_edges+down_adds-down_removes)
    throw std::runtime_error("residual down-index cardinality/accounting");
   if(gibbs_draws!=residual_proposals+gibbs_zero_draws||cycles!=gibbs_draws+singleton_holds)throw std::runtime_error("Gibbs line draw accounting");
   if(residual_proposals!=residual_accepts+residual_MH_holds||residual_accepts!=changes||draws!=residual_proposals)
    throw std::runtime_error("residual MH accounting");
  }
  if(changed_cell_writes!=conditional_hook_writes||zero_draws||
     (!residual_aux_gibbs&&(draws!=changes||cycles!=changes+singleton_holds)))
   throw std::runtime_error("CGC conditional move accounting");index_checked_entries+=h+a;
 }
 void metadata(std::ostream&f)const{
  if(active&&(!dirty_vertices.empty()||!dirty_support_cells.empty()||in_conditional_commit))
   throw std::runtime_error("CGC synchronize before metadata");
  f<<"\"CGC_requested\":"<<(requested?"true":"false")<<",\"CGC_active\":"<<(active?"true":"false")
   <<",\"CGC_weighted_first\":"<<(weighted_first?"true":"false")<<",\"CGC_static_no_cycle\":"<<(static_no_cycle?"true":"false")
   <<",\"CGC_policy_applies_to_residual_off\":true"
   <<",\"CGC_policy\":\"fixed degree>=2 H; full a=sum_H(w-1); omit a=0 vertices; first row capacity-weighted or uniform positive-capacity; uniform nonbacktracking candidate neighbors; first-repeat simple cycle; exact uniform conditional integer excluding0; singleton/dead-end hold without productive retry\""
   <<",\"CGC_index_policy\":\"prewrite residual hook, coordinate H index, O1 numeric capacity per eligible edge; commit-time dirty threshold incident scans and Fenwick updates; atomic support cycles bypass transient own-index churn; previous residual hook forwarded\""
   <<",\"CGC_general_path_limit\":256,\"CGC_hook_CPU_separately_measured\":false"
   <<",\"CGC_residual_aux_gibbs\":"<<(residual_aux_gibbs?"true":"false")
   <<",\"RA_policy\":\"Scott-Gandy auxiliary path pairing adapted to fixed four-margin integer bipartite H/a conditional line; uniform positive-capacity root; indexed decrementable down/positive up; first repeat no retry; exact endpoint/interior three-class Gibbs heatbath or nonself scalar normalizer correction\""
   <<",\"GB_nonself\":"<<(gibbs_nonself?"true":"false")<<",\"GB_draws\":"<<gibbs_draws
   <<",\"GB_zero_draws\":"<<gibbs_zero_draws<<",\"GB_row_meetings\":"<<gibbs_row_meetings<<",\"GB_column_meetings\":"<<gibbs_column_meetings
   <<",\"GB_per_node_strength_int64_certificate\":true,\"GB_stricter_per_cell_cap_supported\":false"
   <<",\"RA_calls\":"<<residual_calls<<",\"RA_dead_holds\":"<<residual_dead
   <<",\"RA_proposals\":"<<residual_proposals<<",\"RA_MH_accepts\":"<<residual_accepts<<",\"RA_MH_holds\":"<<residual_MH_holds
   <<",\"RA_down_decisions\":"<<residual_down_decisions<<",\"RA_reverse_decisions\":"<<residual_reverse_decisions
   <<",\"RA_overlay_edges\":"<<residual_overlay_edges<<",\"RA_full_row_scans\":0"
   <<",\"RA_down_initial_edges\":"<<initial_down_edges<<",\"RA_down_final_edges\":"<<down_index.edges.size()
   <<",\"RA_down_adds\":"<<down_adds<<",\"RA_down_removes\":"<<down_removes<<",\"RA_hook_calls\":"<<residual_hook_calls
   <<",\"CGC_calls\":"<<calls<<",\"CGC_cycles\":"<<cycles<<",\"CGC_changes\":"<<changes
   <<",\"CGC_draws\":"<<draws<<",\"CGC_zero_draws\":"<<zero_draws<<",\"CGC_changed_cell_writes\":"<<changed_cell_writes
   <<",\"CGC_static_holds\":"<<static_holds<<",\"CGC_zero_capacity_holds\":"<<zero_capacity_holds
   <<",\"CGC_dynamic_no_cycle_holds\":"<<dynamic_no_cycle_holds<<",\"CGC_empty_holds\":"<<empty_holds
   <<",\"CGC_leaf_holds\":"<<leaf_holds<<",\"CGC_cap_holds\":"<<cap_holds<<",\"CGC_singleton_holds\":"<<singleton_holds
   <<",\"CGC_path_steps\":"<<path_steps<<",\"CGC_max_path_steps\":"<<max_path_steps
   <<",\"CGC_cycle_edges\":"<<cycle_edges<<",\"CGC_max_cycle_edges\":"<<max_cycle_edges<<",\"CGC_interval_max\":"<<interval_max
   <<",\"CGC_H_initial_edges\":"<<initial_support_edges<<",\"CGC_H_final_edges\":"<<support.edges.size()
   <<",\"CGC_candidate_initial_edges\":"<<initial_candidate_edges<<",\"CGC_candidate_final_edges\":"<<candidate.edges.size()
   <<",\"CGC_positive_rows\":"<<positive_rows<<",\"CGC_positive_columns\":"<<positive_columns
   <<",\"CGC_row_capacity_total\":"<<row_capacity_total
   <<",\"CGC_mutation_hook_calls\":"<<mutation_hook_calls<<",\"CGC_eligible_mutations\":"<<eligible_mutations
   <<",\"CGC_conditional_hook_writes\":"<<conditional_hook_writes
   <<",\"CGC_H_adds\":"<<support_adds<<",\"CGC_H_removes\":"<<support_removes<<",\"CGC_support_events\":"<<support_events
   <<",\"CGC_candidate_adds\":"<<candidate_adds<<",\"CGC_candidate_removes\":"<<candidate_removes
   <<",\"CGC_synchronize_calls\":"<<synchronize_calls<<",\"CGC_synchronize_no_work\":"<<synchronize_no_work
   <<",\"CGC_synchronized_vertices\":"<<synchronized_vertices<<",\"CGC_capacity_threshold_crossings\":"<<capacity_threshold_crossings
   <<",\"CGC_reconcile_scan_records\":"<<reconcile_scan_records<<",\"CGC_reconciled_cells\":"<<reconciled_cells
   <<",\"CGC_root_tree_updates\":"<<root_tree_updates<<",\"CGC_max_dirty_vertices\":"<<max_dirty_vertices
   <<",\"CGC_max_dirty_cells\":"<<max_dirty_cells<<",\"CGC_index_checks\":"<<index_checks
   <<",\"CGC_index_checked_entries\":"<<index_checked_entries<<",";
 }
};
