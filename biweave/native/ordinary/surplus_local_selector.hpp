#pragma once
#include "compensated_switch.hpp"

struct SurplusLocalSelector:CompensatedSwitch {
 U surplus_ticket_draws=0,uniform_reserve_draws=0,zero_mass_reserves=0;
 U empty_core_holds=0,leaf_second_holds=0,pair_descriptors=0;
 U zero_surplus_anchor_pairs=0;

 bool select(Engine&e,Graph&g,int actor_side,int&first_actor,int&second_actor,int&anchor){
  if(!requested||!weighted_first||graph!=&g||g.D)
   throw std::runtime_error("local surplus selector requires enabled complete graph");
  ++calls;++axis_calls[actor_side];
  if(excess.records.empty()){++empty_core_holds;return false;}
  if(excess.total==std::numeric_limits<U>::max())throw std::runtime_error("local surplus ticket overflow");
  const U ticket=e.rng.below(excess.total+1);std::size_t position=0;
  if(ticket==0){++uniform_reserve_draws;zero_mass_reserves+=excess.total==0;
   position=std::size_t(e.rng.below(U(excess.records.size())));}
  else{++surplus_ticket_draws;position=excess.select(ticket-1);}
  const Record chosen=excess.records.at(position);
  first_actor=actor_side?chosen.c:chosen.r;
  anchor=actor_side?chosen.r:chosen.c;
  const int anchor_side=1-actor_side;
  const auto&adj=g.adj.at(std::size_t(vertex(anchor_side,anchor)));
  const int edge_id=g.find(chosen.r,chosen.c);
  if(edge_id<0||g.edges.at(std::size_t(edge_id)).w!=chosen.w||adj.size()<2)
   throw std::runtime_error("local surplus core descriptor stale");
  const auto edge=g.edges.at(std::size_t(edge_id));
  const std::size_t first=std::size_t(actor_side?edge.pr:edge.pc);
  if(first>=adj.size()||adj[first]!=edge_id)throw std::runtime_error("local surplus adjacency position mismatch");
  U second=e.rng.below(U(adj.size()-1));if(second>=first)++second;
  second_actor=neighbor(g,adj.at(std::size_t(second)),anchor_side);
  if(first_actor==second_actor)throw std::runtime_error("local surplus duplicate actors");
  if(g.target_degree.at(std::size_t(vertex(actor_side,second_actor)))<2){++leaf_second_holds;return false;}
  const I a=value(g,actor_side,first_actor,anchor),b=value(g,actor_side,second_actor,anchor);
  if(a<=0||b<=0)throw std::runtime_error("local surplus selected nonpositive anchor edge");
  zero_surplus_anchor_pairs+=a==1&&b==1;++pair_descriptors;
  return true;
 }
 void metadata(std::ostream&f)const{
  f<<"\"LSEL_requested\":"<<(requested?"true":"false")
   <<",\"LSEL_calls\":"<<calls<<",\"LSEL_pair_descriptors\":"<<pair_descriptors
   <<",\"LSEL_row_actor_calls\":"<<axis_calls[0]<<",\"LSEL_column_actor_calls\":"<<axis_calls[1]
   <<",\"LSEL_surplus_ticket_draws\":"<<surplus_ticket_draws
   <<",\"LSEL_uniform_reserve_draws\":"<<uniform_reserve_draws
   <<",\"LSEL_zero_mass_reserves\":"<<zero_mass_reserves
   <<",\"LSEL_zero_surplus_anchor_pairs\":"<<zero_surplus_anchor_pairs
   <<",\"LSEL_empty_core_holds\":"<<empty_core_holds
   <<",\"LSEL_leaf_second_holds\":"<<leaf_second_holds
   <<",\"LSEL_index_checks\":"<<index_checks<<",\"LSEL_index_checked_records\":"<<index_checked_records
   <<",\"LSEL_hook_calls\":"<<hook_calls<<",\"LSEL_core_hook_calls\":"<<core_hook_calls
   <<",\"LSEL_core_records\":"<<excess.records.size()<<",\"LSEL_core_excess\":"<<excess.total
   <<",\"LSEL_policy\":\"selector only; original full two-vertex L conditional/count/MH/completion unchanged; one uniform core-edge reserve ticket plus Z integer surplus tickets; fixed orientation; uniform distinct second neighbor; leaf second holds; no tunable mixture parameter\",";
 }
};
