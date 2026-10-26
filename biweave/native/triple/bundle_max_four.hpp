#pragma once
#include <array>
#include <ostream>
#include <stdexcept>

struct BundleMaxFourDispatch {
 bool requested=false,active=false;
 std::array<int,2>route={0,0};  
 U dispatch_calls=0,axis_dispatch_calls=0,static_axis_skips=0;
 U no_static_candidates=0,changes=0,index_checks=0;
 U B3_calls=0,B4_calls=0;
 std::array<U,2>axis_B3_calls={0,0},axis_B4_calls={0,0},axis_changes={0,0};

 void initialize(const Graph&g,bool want,const DisconnectedBundleHeatbath&d3,
                 const DisconnectedFourBundleHeatbath&d4){
  requested=want;if(!want)return;
  if(!d3.requested||!d4.requested||g.D)
   throw std::runtime_error("max-four requires both exact-margin child kernels");
  for(int axis=0;axis<2;++axis){
   route[axis]=d4.axis_active[axis]?4:(d3.axis_active[axis]?3:0);
   active|=route[axis]!=0;
  }
 }

 void check(const Graph&g,const DisconnectedBundleHeatbath&d3,
            const DisconnectedFourBundleHeatbath&d4){
  if(!requested)return;++index_checks;
  if(!d3.requested||!d4.requested||g.D)
   throw std::runtime_error("max-four exact-margin child audit");
  for(int axis=0;axis<2;++axis){
   const int n=axis?g.nc:g.nr,opposite=axis?g.nr:g.nc,offset=axis?g.nr:0;
   U count=0;for(int v=0;v<n;++v)count+=g.target_degree[offset+v]==2;
   const int expected=opposite>=8&&count>=4?4:(opposite>=6&&count>=3?3:0);
   if(route[axis]!=expected||
      route[axis]!=(d4.axis_active[axis]?4:(d3.axis_active[axis]?3:0)))
    throw std::runtime_error("max-four static routing audit");
  }
  if(active!=(route[0]!=0||route[1]!=0))throw std::runtime_error("max-four active audit");
  if(axis_dispatch_calls!=2*dispatch_calls||B3_calls!=axis_B3_calls[0]+axis_B3_calls[1]||
     B4_calls!=axis_B4_calls[0]+axis_B4_calls[1]||
     axis_dispatch_calls!=B3_calls+B4_calls+static_axis_skips)
   throw std::runtime_error("max-four dispatch accounting");
 }

 bool compose(Engine&e,Graph&g,DisconnectedBundleHeatbath&d3,
              DisconnectedFourBundleHeatbath&d4){
  if(!requested||g.D)throw std::runtime_error("unrequested max-four compose");
  ++dispatch_calls;if(!active)++no_static_candidates;
  bool changed=false;

  for(int axis:{1,0}){
   ++axis_dispatch_calls;bool axis_changed=false;
   if(route[axis]==4){++B4_calls;++axis_B4_calls[axis];axis_changed=d4.step_axis(e,g,axis);}
   else if(route[axis]==3){++B3_calls;++axis_B3_calls[axis];axis_changed=d3.step_axis(e,g,axis);}
   else ++static_axis_skips;
   if(axis_changed){++axis_changes[axis];changed=true;}
  }
  if(changed)++changes;return changed;
 }

 void metadata(std::ostream&f)const{
  f<<"\"BD_requested\":"<<(requested?"true":"false")
   <<",\"BD_active\":"<<(active?"true":"false")
   <<",\"BD_row_route\":"<<route[0]<<",\"BD_column_route\":"<<route[1]
   <<",\"BD_dispatch\":"<<dispatch_calls<<",\"BD_dispatch_calls\":"<<dispatch_calls
   <<",\"BD_axis_dispatch_calls\":"<<axis_dispatch_calls
   <<",\"BD_B3_calls\":"<<B3_calls<<",\"BD_B4_calls\":"<<B4_calls
   <<",\"BD_row_B3_calls\":"<<axis_B3_calls[0]<<",\"BD_column_B3_calls\":"<<axis_B3_calls[1]
   <<",\"BD_row_B4_calls\":"<<axis_B4_calls[0]<<",\"BD_column_B4_calls\":"<<axis_B4_calls[1]
   <<",\"BD_static_axis_skips\":"<<static_axis_skips
   <<",\"BD_no_static_candidates\":"<<no_static_candidates
   <<",\"BD_changes\":"<<changes<<",\"BD_row_changes\":"<<axis_changes[0]
   <<",\"BD_column_changes\":"<<axis_changes[1]<<",\"BD_index_checks\":"<<index_checks
   <<",\"BD_policy\":\"fixed target-degree and axis dimensions choose D4 else D3 else identity; exactly one kernel per direction, column then row, selected coverage branch only; no fallback after hold; original child index audits retained\",";
 }
};
