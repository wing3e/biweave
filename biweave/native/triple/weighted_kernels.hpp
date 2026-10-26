#pragma once
#include "audit_constraint_core.inc"
#include "degree2_ewens.hpp"
#include "support_cycle_heatbath.hpp"
#include "margin_orbit_refresh.hpp"
#include "sirius_native.hpp"

template<class Labels>
void complementary_step(Engine&e,Graph&g,Labels&labels,TradeCounters&stats,
                        int width,int maxr){
 if(labels.unit_forced){kdd_unit_step(e,g);return;}
 U branch=e.rng.below(10);
 if(branch<8)invariant_trade(e,g,labels,stats,true,true,width,maxr,0);
 else if(branch==8)invariant_trade(e,g,labels,stats,true,false,std::min(width,8),maxr,0);
 else e.standard_optimized_step(g);
}

struct ResidualMarginLabels:ConstraintAwareLabels {
 int preferred_axis=-1;
 explicit ResidualMarginLabels(const Graph&g):ConstraintAwareLabels(g){
  int variable[2]={0,0};for(int v=0;v<g.nr;++v)variable[0]+=g.target_degree[v]>1;
  for(int v=0;v<g.nc;++v)variable[1]+=g.target_degree[g.nr+v]>1;
  if(variable[0]<=1&&variable[1]>=2)preferred_axis=1;
  else if(variable[1]<=1&&variable[0]>=2)preferred_axis=0;
 }
 std::vector<int>select(Engine&e,const Graph&g,int&o,int r,bool guided){
  if(preferred_axis>=0)o=e.rng.below(10)<9?preferred_axis:1-preferred_axis;
  return ConstraintAwareLabels::select(e,g,o,r,guided);
 }
};

template<class Labels>
void covered_complementary_step(Engine&e,Graph&g,Labels&labels,TradeCounters&stats,
                                int width,int maxr){
 if(e.rng.below(100)==0)e.candidate(g);
 else complementary_step(e,g,labels,stats,width,maxr);
}

template<class Labels>
void efficient_covered_step(Engine&e,Graph&g,Labels&labels,TradeCounters&stats,
                            int width,int maxr){
 if(labels.unit_forced){kdd_unit_step(e,g);return;}
 if(e.rng.below(100)==0){e.candidate(g);return;}
 U branch=e.rng.below(100);
 if(branch<94)invariant_trade(e,g,labels,stats,true,true,width,maxr,0);
 else if(branch<99)invariant_trade(e,g,labels,stats,true,false,std::min(width,8),maxr,0);
 else e.standard_optimized_step(g);
}

struct LeafQuotaOrbitCertificate {
 bool eligible=false;int leaf_axis=-1;int weight_classes=0;
 explicit LeafQuotaOrbitCertificate(const Graph&g){
  for(int side=0;side<2;++side){int n=side?g.nc:g.nr,off=side?g.nr:0,opposite=side?g.nr:g.nc,other_off=side?0:g.nr;
   int active_other=0;for(int v=0;v<opposite;++v)active_other+=g.target_degree[other_off+v]>0;
   int hub=-1;bool good=true;std::set<I>weights;
   for(int v=0;v<n;++v){int degree=g.target_degree[off+v];if(!degree)continue;
    if(degree==1)weights.insert(g.target_strength[off+v]);
    else if(hub<0)hub=v;else good=false;
   }
   if(!good||weights.empty()||weights.size()>2)continue;
   if(hub>=0&&(g.target_degree[off+hub]!=active_other||g.target_strength[off+hub]!=active_other))continue;
   I low=*weights.begin(),high=*weights.rbegin();
   for(int v=0;v<opposite&&good;++v){int d=g.target_degree[other_off+v];I s=g.target_strength[other_off+v];if(!d){good=s==0;continue;}
    int residual_d=d-(hub>=0);S128 residual_s=S128(s)-(hub>=0);
    if(residual_d<0||residual_s<0){good=false;break;}
    S128 numerator=residual_s-S128(low)*residual_d;
    if(low==high){good=numerator==0;continue;}
    I difference=high-low;good=numerator>=0&&numerator%difference==0&&numerator/difference<=residual_d;
   }
   if(good){eligible=true;leaf_axis=side;weight_classes=int(weights.size());return;}
  }
 }
};
