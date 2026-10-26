#pragma once

struct GuidedSupportCycleHeatbath {
 struct IndexedEdge {int r=0,c=0;U pr=0,pc=0;};
 Graph* graph=nullptr;
 bool active=false,core=false,nontrivial=false,maximum_degree2=true;
 std::vector<IndexedEdge> edges;
 std::vector<std::vector<U>> adj;
 std::unordered_map<U,U> position;
 std::vector<U> stamp,first;U generation=0;
 U calls=0,holds_empty=0,holds_leaf=0,holds_cap=0,holds_singleton=0;
 U paths=0,path_steps=0,max_path_steps=0,cycles=0,cycle_edges=0,max_cycle_edges=0;
 U draws=0,changes=0,zero_draws=0,changed_cell_writes=0;
 U index_initial_edges=0,index_adds=0,index_removes=0,index_support_events=0;
 U index_checks=0,index_checked_entries=0,interval_max=0;
 __uint128_t interval_total=0;
 bool eligible(int r,int c)const{return graph->target_degree[r]>=2&&graph->target_degree[graph->nr+c]>=2;}
 static void notify(void*p,int r,int c,I old,I now){static_cast<GuidedSupportCycleHeatbath*>(p)->update(r,c,old,now);}
 void add(int r,int c){
  const U key=cellkey(r,c),id=edges.size();if(position.count(key))throw std::runtime_error("GC duplicate support edge");
  edges.push_back({r,c,U(adj[r].size()),U(adj[graph->nr+c].size())});
  adj[r].push_back(id);adj[graph->nr+c].push_back(id);position.emplace(key,id);
 }
 void remove(int r,int c){
  const U key=cellkey(r,c);auto it=position.find(key);if(it==position.end())throw std::runtime_error("GC missing support edge");
  const U id=it->second;const IndexedEdge x=edges[id];auto&ra=adj[r];U last=ra.back();ra[x.pr]=last;edges[last].pr=x.pr;ra.pop_back();
  auto&ca=adj[graph->nr+c];last=ca.back();ca[x.pc]=last;edges[last].pc=x.pc;ca.pop_back();position.erase(it);
  const U end=edges.size()-1;if(id!=end){const auto moved=edges.back();edges[id]=moved;adj[moved.r][moved.pr]=id;adj[graph->nr+moved.c][moved.pc]=id;position[cellkey(moved.r,moved.c)]=id;}edges.pop_back();
 }
 void update(int r,int c,I old,I now){
  if(!active||!core)throw std::runtime_error("GC inactive support observer");
  if((old>0)==(now>0))return;++index_support_events;
  if(!eligible(r,c))return;if(now>0){add(r,c);++index_adds;}else{remove(r,c);++index_removes;}
 }
 void initialize(Graph&g,bool want,bool filter,bool exclude_current){
  graph=&g;active=want;core=filter;nontrivial=exclude_current;if(!active)return;
  for(int d:g.target_degree)maximum_degree2&=d<=2;
  stamp.assign(U(g.nr)+U(g.nc),0);first.resize(stamp.size());
  if(core){if(g.residual_mutation_hook)throw std::runtime_error("GC residual observer already installed");
   adj.resize(stamp.size());for(const auto&e:g.edges)if(eligible(e.r,e.c))add(e.r,e.c);index_initial_edges=edges.size();
   g.residual_mutation_context=this;g.residual_mutation_hook=&notify;
  }
 }
 U edge_count(const Graph&g)const{return core?edges.size():g.edges.size();}
 int edge_row(const Graph&g,U id)const{return core?edges[id].r:g.edges[id].r;}
 int edge_col(const Graph&g,U id)const{return core?edges[id].c:g.edges[id].c;}
 U edge_position(const Graph&g,U id,int vertex)const{
  if(core)return vertex<g.nr?edges[id].pr:edges[id].pc;
  return U(vertex<g.nr?g.edges[id].pr:g.edges[id].pc);
 }
 U degree(const Graph&g,int vertex)const{return core?adj[vertex].size():g.adj[vertex].size();}
 U adjacent(const Graph&g,int vertex,U which)const{return core?adj[vertex][which]:U(g.adj[vertex][which]);}
 bool refresh(Engine&e,Graph&g,const std::vector<U>&path,U start){
  const U n=path.size()-start;if(n<4||n%2)throw std::runtime_error("GC invalid bipartite cycle");
  S128 lo=0,hi=0;bool initialized=false;

  struct Cell {int r,c;I w;bool plus;};std::vector<Cell>cells;cells.reserve(n);
  for(U j=0;j<n;++j){const U id=path[start+j];const int r=edge_row(g,id),c=edge_col(g,id);const I w=g.value(r,c);if(w<=0)throw std::runtime_error("GC stale support path");const bool plus=(j%2)==0;cells.push_back({r,c,w,plus});
   if(!initialized){lo=1-S128(w);hi=std::numeric_limits<I>::max();initialized=true;}
   if(plus)lo=std::max(lo,1-S128(w));else hi=std::min(hi,S128(w)-1);
  }
  if(lo>0||hi<0||lo>hi)throw std::runtime_error("GC current state missing from line");
  const S128 wide=hi-lo+1;if(wide<1||wide>S128(std::numeric_limits<U>::max()))throw std::runtime_error("GC conditional interval overflow");const U width=U(wide);
  ++cycles;cycle_edges+=n;max_cycle_edges=std::max(max_cycle_edges,n);interval_total+=width;interval_max=std::max(interval_max,width);
  if(width==1){++holds_singleton;return false;}
  S128 delta;if(nontrivial){delta=lo+S128(e.rng.below(width-1));if(delta>=0)++delta;}else delta=lo+S128(e.rng.below(width));++draws;
  if(!delta){++zero_draws;return false;}
  for(const auto&x:cells){const S128 now=S128(x.w)+(x.plus?delta:-delta);if(now<1||now>std::numeric_limits<I>::max())throw std::runtime_error("GC positive weight range");if(g.value(x.r,x.c)!=x.w)throw std::runtime_error("GC stale conditional ledger");}
  const U before=e.stat.cell_updates;
  for(const auto&x:cells)g.set_raw(x.r,x.c,I(S128(x.w)+(x.plus?delta:-delta)));
  if(e.stat.cell_updates-before!=n)throw std::runtime_error("GC conditional cell counter");
  ++changes;changed_cell_writes+=n;++e.stat.changed_outer;return true;
 }
 bool step(Engine&e,Graph&g){
  if(!active)throw std::runtime_error("GC inactive update");++calls;++e.stat.work;
  const U count=edge_count(g);if(!count){++holds_empty;return false;}
  if(++generation==0){std::fill(stamp.begin(),stamp.end(),0);generation=1;}
  U id=e.rng.below(count);int vertex=edge_row(g,id);stamp[vertex]=generation;first[vertex]=0;
  std::vector<U>path;path.reserve(256);++paths;

  const U cap=maximum_degree2?stamp.size()+1:256;
  for(U j=0;j<cap;++j){
   path.push_back(id);++path_steps;const int next=vertex<g.nr?g.nr+edge_col(g,id):edge_row(g,id);
   if(stamp[next]==generation){max_path_steps=std::max(max_path_steps,U(path.size()));return refresh(e,g,path,first[next]);}
   stamp[next]=generation;first[next]=path.size();const U d=degree(g,next);
   if(d<2){++holds_leaf;max_path_steps=std::max(max_path_steps,U(path.size()));return false;}
   const U previous=edge_position(g,id,next);U pick=e.rng.below(d-1);if(pick>=previous)++pick;id=adjacent(g,next,pick);vertex=next;
  }
  ++holds_cap;max_path_steps=std::max(max_path_steps,U(path.size()));return false;
 }
 void check(const Graph&g){
  if(!active||!core)return;++index_checks;if(position.size()!=edges.size())throw std::runtime_error("GC index cardinality");
  U want=0;for(const auto&e:g.edges)want+=eligible(e.r,e.c);if(want!=edges.size()||edges.size()!=index_initial_edges+index_adds-index_removes)throw std::runtime_error("GC index total");
  U total=0;for(U id=0;id<edges.size();++id){const auto&e=edges[id];if(!eligible(e.r,e.c)||g.value(e.r,e.c)<=0||position.at(cellkey(e.r,e.c))!=id||adj[e.r][e.pr]!=id||adj[g.nr+e.c][e.pc]!=id)throw std::runtime_error("GC indexed edge");++total;}
  U adjacent_total=0;for(U v=0;v<adj.size();++v)for(U k=0;k<adj[v].size();++k){const U id=adj[v][k];if(id>=edges.size())throw std::runtime_error("GC adjacency ID");const auto&e=edges[id];if(v<U(g.nr)?(e.r!=int(v)||e.pr!=k):(g.nr+e.c!=int(v)||e.pc!=k))throw std::runtime_error("GC adjacency position");++adjacent_total;}
  if(adjacent_total!=2*total)throw std::runtime_error("GC adjacency count");index_checked_entries+=total;
 }
 void metadata(std::ostream&f)const{
  f<<"\"SC_active\":"<<(active?"true":"false")<<",\"SC_core_filter\":"<<(core?"true":"false")<<",\"SC_nontrivial_draw\":"<<(nontrivial?"true":"false")<<",\"SC_calls\":"<<calls<<",\"SC_cycles\":"<<cycles<<",\"SC_changes\":"<<changes<<",\"SC_zero_draws\":"<<zero_draws<<",\"SC_empty_holds\":"<<holds_empty<<",\"SC_leaf_holds\":"<<holds_leaf<<",\"SC_cap_holds\":"<<holds_cap<<",\"SC_singleton_holds\":"<<holds_singleton<<",\"SC_path_steps\":"<<path_steps<<",\"SC_max_path_steps\":"<<max_path_steps<<",\"SC_cycle_edges\":"<<cycle_edges<<",\"SC_max_cycle_edges\":"<<max_cycle_edges<<",\"SC_interval_max\":"<<interval_max<<",\"SC_changed_cell_writes\":"<<changed_cell_writes<<",\"SC_index_initial_edges\":"<<index_initial_edges<<",\"SC_index_final_edges\":"<<edges.size()<<",\"SC_index_adds\":"<<index_adds<<",\"SC_index_removes\":"<<index_removes<<",\"SC_index_support_events\":"<<index_support_events<<",\"SC_index_checks\":"<<index_checks<<",\"SC_index_checked_entries\":"<<index_checked_entries<<",";
 }
};
