#pragma once

struct GlobalDegreeWorkBatch {
 using Wide=__uint128_t;
 bool requested=false,active=false;
 U repetitions=1,macro_calls=0,total_attempts=0;
 Wide degree_square_sum=0,degree_sum=0;U fixed_edge_count=0;
 bool representation_requested=false,representation_active=false;
 Wide representation_proxy=0;
 std::array<bool,2>representation_axis_active{false,false};
 std::array<U,2>representation_words{0,0};
 static std::string wide_string(Wide x){if(!x)return "0";std::string s;while(x){s.push_back(char('0'+x%10));x/=10;}std::reverse(s.begin(),s.end());return s;}
 void initialize(const Graph&g,bool request,bool gws_active,U outer){
  requested=request;active=request&&gws_active;if(!active)return;
  fixed_edge_count=g.edges.size();for(int d:g.target_degree){if(d<0)throw std::runtime_error("GWB negative fixed degree");degree_sum+=Wide(d);degree_square_sum+=Wide(d)*Wide(d);}
  if(degree_sum!=Wide(2)*Wide(fixed_edge_count))throw std::runtime_error("GWB fixed degree ledger inconsistent");
  if(fixed_edge_count){const Wide numerator=Wide(3)*degree_square_sum,denominator=Wide(4)*fixed_edge_count;const Wide r=numerator/denominator+(numerator%denominator!=0);if(!r||r>std::numeric_limits<U>::max())throw std::runtime_error("GWB repetitions outside uint64");repetitions=U(r);}
   
  if(outer&&repetitions>std::numeric_limits<U>::max()/outer)throw std::runtime_error("GWB outer times repetitions exceeds uint64 counter range");
 }

 template<class Bits>void refine_representation(const Graph&g,const Bits&bits,bool request,U outer){
  representation_requested=request;representation_active=request&&active;
  if(!representation_active)return;
  if(g.target_degree.size()!=size_t(g.nr)+size_t(g.nc))throw std::runtime_error("GRWB fixed degree dimensions");
  if(g.edges.size()!=fixed_edge_count)throw std::runtime_error("GRWB fixed edge ledger changed before refinement");
  for(int o=0;o<2;++o){representation_axis_active[o]=bits.axis[o].active;representation_words[o]=bits.axis[o].words;}
  for(size_t v=0;v<g.target_degree.size();++v){
   const int d=g.target_degree[v];if(d<0)throw std::runtime_error("GRWB negative fixed degree");
   const int o=v<size_t(g.nr)?0:1;const U ell=representation_axis_active[o]?std::min(U(d),representation_words[o]):U(d);
   representation_proxy+=Wide(d)*Wide(ell);
  }
  if(representation_proxy>degree_square_sum)throw std::runtime_error("GRWB proxy exceeds legacy degree-square proxy");
  if(fixed_edge_count){const Wide numerator=Wide(3)*representation_proxy,denominator=Wide(4)*fixed_edge_count;const Wide r=numerator/denominator+(numerator%denominator!=0);if(!r||r>std::numeric_limits<U>::max())throw std::runtime_error("GRWB repetitions outside uint64");repetitions=U(r);}
  else repetitions=1;
  if(outer&&repetitions>std::numeric_limits<U>::max()/outer)throw std::runtime_error("GRWB outer times refined repetitions exceeds uint64 counter range");
 }
 void step(Engine&e,Graph&g,GlobalEqualWeightSwitch&gws){
  if(!active)throw std::runtime_error("GWB inactive dispatch");
  ++macro_calls;for(U k=0;k<repetitions;++k)gws.step(e,g,k==0);total_attempts+=repetitions;
 }
};
