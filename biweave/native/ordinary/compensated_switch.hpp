#pragma once
#include <algorithm>
#include <array>
#include <cstddef>
#include <cstdint>
#include <limits>
#include <ostream>
#include <stdexcept>
#include <unordered_map>
#include <vector>

struct CompensatedSwitch {
 struct Record {int r=0,c=0;I w=0;};
 struct ExcessIndex {
  std::vector<Record> records;
  std::unordered_map<U,std::size_t> position;
  std::vector<U> bit;
  U total=0;

  static U key(int r,int c){return (U(std::uint32_t(r))<<32)|U(std::uint32_t(c));}
  static U mass(I w){return w>1?U(w-1):0;}
  std::size_t capacity()const{return bit.empty()?0:bit.size()-1;}
  void initialize(std::size_t slots){bit.assign(slots+1,0);}
  void set_mass(std::size_t id,U old,U now){
   if(id>=capacity())throw std::runtime_error("CS Fenwick slot out of bounds");
   const bool increase=now>=old;const U delta=increase?now-old:old-now;
   if(increase){if(total>std::numeric_limits<U>::max()-delta)throw std::runtime_error("CS mass overflow");total+=delta;}
   else{if(total<delta)throw std::runtime_error("CS mass underflow");total-=delta;}
   for(std::size_t k=id+1;k<bit.size();k+=k&(~k+1)){
    if(increase){if(bit[k]>std::numeric_limits<U>::max()-delta)throw std::runtime_error("CS tree overflow");bit[k]+=delta;}
    else{if(bit[k]<delta)throw std::runtime_error("CS tree underflow");bit[k]-=delta;}
   }
  }
  void change_weight(std::size_t id,I w){
   if(id>=records.size()||w<0)throw std::runtime_error("CS invalid indexed weight");
   set_mass(id,mass(records[id].w),mass(w));records[id].w=w;
  }
  void add(int r,int c,I w){
   const U k=key(r,c);if(w<=0||position.count(k)||records.size()>=capacity())
    throw std::runtime_error("CS duplicate/index support-cap failure");
   const std::size_t id=records.size();records.push_back({r,c,0});position.emplace(k,id);change_weight(id,w);
  }
  void remove(int r,int c){
   const U k=key(r,c);auto found=position.find(k);
   if(found==position.end())throw std::runtime_error("CS missing indexed record");
   const std::size_t id=found->second,last=records.size()-1;
   if(id!=last){const Record moved=records[last];change_weight(id,moved.w);change_weight(last,0);
    records[id]=moved;position.at(key(moved.r,moved.c))=id;}
   else change_weight(last,0);
   position.erase(k);records.pop_back();
  }
  U prefix(std::size_t end)const{
   if(end>capacity())throw std::runtime_error("CS invalid prefix");
   U value=0;for(std::size_t k=end;k;k-=k&(~k+1))value+=bit[k];return value;
  }
  std::size_t select(U order)const{
   if(order>=total)throw std::runtime_error("CS empty/range surplus draw");
   std::size_t id=0,jump=1;while(jump<=capacity()/2)jump*=2;
   for(;jump;jump/=2){const std::size_t next=id+jump;
    if(next<bit.size()&&bit[next]<=order){id=next;order-=bit[next];}}
   if(id>=records.size()||mass(records[id].w)==0)throw std::runtime_error("CS Fenwick returned zero/absent record");
   return id;
  }
 };

 Graph*graph=nullptr;
 bool initialized=false,requested=false,weighted_first=false;
 int rows=0,columns=0;
 std::array<std::vector<int>,2> anchors;
 ExcessIndex excess;
 void*previous_context=nullptr;
 void(*previous_hook)(void*,int,int,I,I)=nullptr;
 U calls=0,changes=0,axis_calls[2]={0,0},axis_changes[2]={0,0};
 U empty_anchor_holds=0,zero_surplus_holds=0,leaf_actor_holds=0;
 U cross_positive_holds=0,equal_weight_holds=0,compensation_holds=0;
 U proposals=0,cell_writes=0,hook_calls=0,core_hook_calls=0;
 U index_checks=0,index_checked_records=0;

 static U key(int r,int c){return ExcessIndex::key(r,c);}
 bool core(int r,int c)const{
  return graph->target_degree.at(std::size_t(r))>=2&&
         graph->target_degree.at(std::size_t(rows+c))>=2;
 }
 int vertex(int side,int label)const{return side?rows+label:label;}
 int neighbor(const Graph&g,int edge_id,int from_side)const{
  const auto edge=g.edges.at(std::size_t(edge_id));return from_side?edge.r:edge.c;
 }
 I value(const Graph&g,int actor_side,int actor,int object)const{
  return actor_side?g.value(object,actor):g.value(actor,object);
 }
 void put(Graph&g,int actor_side,int actor,int object,I weight){
  if(actor_side)g.set_raw(object,actor,weight);else g.set_raw(actor,object,weight);++cell_writes;
 }
 static void notify(void*context,int r,int c,I old,I now){
  auto*self=static_cast<CompensatedSwitch*>(context);++self->hook_calls;
  if(self->core(r,c)){
   ++self->core_hook_calls;auto found=self->excess.position.find(key(r,c));
   if(old>0){if(found==self->excess.position.end()||self->excess.records[found->second].w!=old)
     throw std::runtime_error("CS stale prewrite core index");
    if(now>0)self->excess.change_weight(found->second,now);else self->excess.remove(r,c);
   }else if(now>0){if(found!=self->excess.position.end())throw std::runtime_error("CS occupied prewrite insertion");
    self->excess.add(r,c,now);}
  }
   
  if(self->previous_hook)self->previous_hook(self->previous_context,r,c,old,now);
 }
 void initialize(Graph&g,bool enabled,bool weighted=false){
  if(initialized)throw std::runtime_error("CS initialized twice");initialized=true;
  graph=&g;rows=g.nr;columns=g.nc;requested=enabled;weighted_first=weighted;
  if(!enabled)return;
  if(rows<1||columns<1||g.D||g.target_degree.size()!=std::size_t(rows)+std::size_t(columns))
   throw std::runtime_error("CS initialization requires a complete feasible graph");
  for(int axis=0;axis<2;++axis){const int n=axis?columns:rows;
   for(int c=0;c<n;++c)if(g.target_degree.at(std::size_t(vertex(axis,c)))>=2)anchors[axis].push_back(c);}
  if(!weighted)return;
  const __uint128_t slots=__uint128_t(g.edges.size())*2+2;
  if(slots>std::numeric_limits<std::size_t>::max()-1)throw std::runtime_error("CS index capacity overflow");
  excess.initialize(std::size_t(slots));
  for(const auto edge:g.edges)if(core(edge.r,edge.c))excess.add(edge.r,edge.c,edge.w);
  previous_context=g.residual_mutation_context;previous_hook=g.residual_mutation_hook;
  if(previous_hook==&notify)throw std::runtime_error("CS residual-hook cycle");
  g.residual_mutation_context=this;g.residual_mutation_hook=&notify;
 }
 bool step(Engine&e,Graph&g){
  if(!requested||graph!=&g||g.D)throw std::runtime_error("CS step requires enabled complete graph");
  ++calls;++e.stat.work;const int axis=int(e.rng.below(2)),actor_side=1-axis;++axis_calls[axis];
  int c=-1,i=-1,j=-1;
  if(weighted_first){
   if(excess.total==0){++zero_surplus_holds;return false;}
   const Record chosen=excess.records.at(excess.select(e.rng.below(excess.total)));
   c=axis?chosen.c:chosen.r;i=axis?chosen.r:chosen.c;
   const auto&adj=g.adj.at(std::size_t(vertex(axis,c)));
   const int id=g.find(chosen.r,chosen.c);
   if(id<0||g.edges.at(std::size_t(id)).w!=chosen.w||adj.size()<2)
    throw std::runtime_error("CS weighted descriptor is stale");
    
   const auto edge=g.edges.at(std::size_t(id));const std::size_t first=std::size_t(axis?edge.pc:edge.pr);
   if(first>=adj.size()||adj[first]!=id)throw std::runtime_error("CS adjacency position mismatch");
   U second=e.rng.below(U(adj.size()-1));if(second>=first)++second;
   j=neighbor(g,adj.at(std::size_t(second)),axis);
  }else{
   const auto&pool=anchors[axis];if(pool.empty()){++empty_anchor_holds;return false;}
   c=pool.at(std::size_t(e.rng.below(U(pool.size()))));const auto&adj=g.adj.at(std::size_t(vertex(axis,c)));
   if(adj.size()!=std::size_t(g.target_degree.at(std::size_t(vertex(axis,c))))||adj.size()<2)
    throw std::runtime_error("CS fixed anchor degree mismatch");
   U first=e.rng.below(U(adj.size())),second=e.rng.below(U(adj.size()-1));if(second>=first)++second;
   i=neighbor(g,adj.at(std::size_t(first)),axis);j=neighbor(g,adj.at(std::size_t(second)),axis);
  }
  if(i==j)throw std::runtime_error("CS selected duplicate actors");
  const auto&ai=g.adj.at(std::size_t(vertex(actor_side,i)));
  const auto&aj=g.adj.at(std::size_t(vertex(actor_side,j)));
  if(ai.size()<2||aj.size()<2){++leaf_actor_holds;return false;}
  const int a=neighbor(g,ai.at(std::size_t(e.rng.below(U(ai.size())))),actor_side);
  const int b=neighbor(g,aj.at(std::size_t(e.rng.below(U(aj.size())))),actor_side);
  if(a==b||value(g,actor_side,i,b)>0||value(g,actor_side,j,a)>0){++cross_positive_holds;return false;}
  const I wa=value(g,actor_side,i,a),wb=value(g,actor_side,j,b);
  const I p=value(g,actor_side,i,c),q=value(g,actor_side,j,c);
  if(wa<=0||wb<=0||p<=0||q<=0)throw std::runtime_error("CS selected nonpositive record");
  if(wa==wb){++equal_weight_holds;return false;}
  const S128 delta=S128(wa)-S128(wb),np=S128(p)+delta,nq=S128(q)-delta;
  ++proposals;if(np<=0||nq<=0){++compensation_holds;return false;}
  if(np>S128(std::numeric_limits<I>::max())||nq>S128(std::numeric_limits<I>::max()))
   throw std::runtime_error("CS compensated weight exceeds certified int64 domain");
  const std::size_t before_edges=g.edges.size();

  put(g,actor_side,i,c,I(np));put(g,actor_side,j,c,I(nq));
  put(g,actor_side,i,a,0);put(g,actor_side,j,b,0);
  put(g,actor_side,j,a,wa);put(g,actor_side,i,b,wb);
  if(g.D||g.edges.size()!=before_edges)throw std::runtime_error("CS commit failed to close degree margins");
  ++changes;++axis_changes[axis];++e.stat.changed_outer;return true;
 }
 void check(const Graph&g){
  if(!requested)return;if(graph!=&g||g.nr!=rows||g.nc!=columns||g.D)
   throw std::runtime_error("CS check requires original complete graph");
  for(int axis=0;axis<2;++axis){std::vector<int>expected;const int n=axis?columns:rows;
   for(int c=0;c<n;++c)if(g.target_degree.at(std::size_t(vertex(axis,c)))>=2)expected.push_back(c);
   if(expected!=anchors[axis])throw std::runtime_error("CS static anchor pool changed");}
  if(!weighted_first)return;++index_checks;
  if(g.residual_mutation_hook!=&notify||g.residual_mutation_context!=this)
   throw std::runtime_error("CS weighted index must be the final chained residual-hook installer");
  U count=0;__uint128_t mass=0;
  for(const auto edge:g.edges)if(core(edge.r,edge.c)){
   ++count;auto it=excess.position.find(key(edge.r,edge.c));
   if(it==excess.position.end())throw std::runtime_error("CS indexed core edge missing");
   const std::size_t id=it->second;const auto record=excess.records.at(id);
   if(record.r!=edge.r||record.c!=edge.c||record.w!=edge.w||
      excess.prefix(id+1)-excess.prefix(id)!=ExcessIndex::mass(edge.w))
    throw std::runtime_error("CS indexed coordinate/weight/Fenwick point mismatch");
   mass+=ExcessIndex::mass(edge.w);++index_checked_records;
  }
  if(count!=excess.records.size()||count!=excess.position.size()||
     mass!=excess.total||excess.prefix(excess.capacity())!=excess.total)
   throw std::runtime_error("CS full core-excess index audit failed");
 }
 void metadata(std::ostream&f)const{
  f<<"\"CS_requested\":"<<(requested?"true":"false")
   <<",\"CS_weighted_first\":"<<(weighted_first?"true":"false")
   <<",\"CS_calls\":"<<calls<<",\"CS_changes\":"<<changes
   <<",\"CS_row_anchor_calls\":"<<axis_calls[0]<<",\"CS_column_anchor_calls\":"<<axis_calls[1]
   <<",\"CS_row_anchor_changes\":"<<axis_changes[0]<<",\"CS_column_anchor_changes\":"<<axis_changes[1]
   <<",\"CS_empty_anchor_holds\":"<<empty_anchor_holds<<",\"CS_zero_surplus_holds\":"<<zero_surplus_holds
   <<",\"CS_leaf_actor_holds\":"<<leaf_actor_holds<<",\"CS_cross_positive_holds\":"<<cross_positive_holds
   <<",\"CS_equal_weight_holds\":"<<equal_weight_holds<<",\"CS_compensation_holds\":"<<compensation_holds
   <<",\"CS_proposals\":"<<proposals<<",\"CS_cell_writes\":"<<cell_writes
   <<",\"CS_hook_calls\":"<<hook_calls<<",\"CS_core_hook_calls\":"<<core_hook_calls
   <<",\"CS_core_records\":"<<excess.records.size()<<",\"CS_core_excess\":"<<excess.total
   <<",\"CS_index_checks\":"<<index_checks<<",\"CS_index_checked_records\":"<<index_checked_records
   <<",\"CS_policy\":\"BES compensated state transformation; fair axis; uniform fixed-degree anchor and two neighbors, or exact core-surplus edge then uniform distinct second neighbor; one uniform incident record per actor; invalid/equal-weight proposals hold; no retry or state filtering by feasibility; six hooked writes\",";
 }
};
