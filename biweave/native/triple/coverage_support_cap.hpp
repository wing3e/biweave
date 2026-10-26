#pragma once
 
struct CoverageSupportCap {
 bool requested=false;
 U initial_edges=0,bound=0,peak_bound=0,calls=0,projection_checks=0,capacity_aborts=0,rollback_rectangles=0,max_projected_support=0,max_complete_support=0,max_abort_steps=0;
 static void validate_nodes(int nr,int nc){if(nr<1||nc<1||__uint128_t(nr)+__uint128_t(nc)>__uint128_t(std::numeric_limits<int>::max()-1))throw std::runtime_error("coverage support cap node index exceeds int");}
 static std::pair<U,U> bounds(__uint128_t edges){
   
  const __uint128_t max_edges=(__uint128_t(std::numeric_limits<int>::max())-2)/2;
  if(edges>max_edges)throw std::runtime_error("coverage support cap 2E+2 exceeds int edge index");
  return {U(edges*2+1),U(edges*2+2)};
 }
 static U projected(U current,const std::array<I,4>&old,I delta){
  const std::array<S128,4> next{S128(old[0])+delta,S128(old[1])-delta,S128(old[2])-delta,S128(old[3])+delta};
  U removed=0,added=0;
  for(int k=0;k<4;++k){if(old[k]<0||next[k]<0||next[k]>std::numeric_limits<I>::max())throw std::runtime_error("coverage support cap invalid proposed weight");removed+=old[k]>0;added+=next[k]>0;}
  if(current<removed||__uint128_t(current-removed)+added>std::numeric_limits<U>::max())throw std::runtime_error("coverage support cap support arithmetic");
  return current-removed+added;
 }
 static void increment(U&x){if(x==std::numeric_limits<U>::max())throw std::runtime_error("coverage support cap counter overflow");++x;}
 void initialize(const Graph&g,bool on){requested=on;if(!on)return;validate_nodes(g.nr,g.nc);auto b=bounds(g.edges.size());initial_edges=U(g.edges.size());bound=b.first;peak_bound=b.second;max_complete_support=initial_edges;max_projected_support=initial_edges;}
 void begin(const Graph&g){if(!requested)return;if(g.edges.size()!=initial_edges)throw std::runtime_error("coverage support cap target E changed");increment(calls);}
 bool allows(const Graph&g,const std::array<I,4>&old,I delta){
  if(!requested)return true;if(g.edges.size()>bound)throw std::runtime_error("coverage support cap current support escaped bound");increment(projection_checks);U n=projected(U(g.edges.size()),old,delta);max_projected_support=std::max(max_projected_support,n);return n<=bound;
 }
 void metadata(std::ostream&f)const{if(!requested)return;f<<"\"coverage_support_cap_requested\":1,\"RSC_initial_edges\":"<<initial_edges<<",\"RSC_bound\":"<<bound<<",\"RSC_peak_index_bound\":"<<peak_bound<<",\"RSC_calls\":"<<calls<<",\"RSC_projection_checks\":"<<projection_checks<<",\"RSC_capacity_aborts\":"<<capacity_aborts<<",\"RSC_rollback_rectangles\":"<<rollback_rectangles<<",\"RSC_max_projected_support\":"<<max_projected_support<<",\"RSC_max_complete_support\":"<<max_complete_support<<",\"RSC_max_abort_steps\":"<<max_abort_steps<<",\"RSC_phase_CPU_measured\":false,\"RSC_policy\":\"original full delta then complete support gate 2E+1; abort whole excursion and undo; no retry; intermediate set_raw peak at most2E+2; path length and exact products unbounded\",";}
};
