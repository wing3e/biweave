 
#define main frozen_probe_v14_main
#include "native_sampler_probe.cpp"
#undef main
#include "exclusive_assignment.hpp"
#include "grouped_private.hpp"
#include "unit_capacity_private.hpp"

struct MarginalLabels {
 std::array<std::vector<int>,2>active;
 std::array<std::map<int,std::vector<int>>,2>by_degree;
 explicit MarginalLabels(const Graph&g){
  for(int o=0;o<2;++o){int n=o?g.nc:g.nr,off=o?g.nr:0;
   for(int v=0;v<n;++v)if(g.target_degree[off+v]>0){active[o].push_back(v);by_degree[o][g.target_degree[off+v]].push_back(v);}
   for(auto&item:by_degree[o])std::sort(item.second.begin(),item.second.end(),[&](int a,int b){
    if(g.target_strength[off+a]!=g.target_strength[off+b])return g.target_strength[off+a]<g.target_strength[off+b];
     
    return mix64(U(a)+17)<mix64(U(b)+17);
   });
  }
 }
 std::vector<int>select(Engine&e,const Graph&g,int o,int r,bool guided){
  const auto&pool=active[o];if(int(pool.size())<r)return {};
  if(!guided||e.rng.below(5)==0){std::vector<int>out;
   for(int j=int(pool.size())-r;j<int(pool.size());++j){int k=int(e.rng.below(U(j)+1));if(std::find(out.begin(),out.end(),k)!=out.end())k=j;out.push_back(k);}
   for(int&v:out)v=pool[v];std::sort(out.begin(),out.end());return out;
  }
  int anchor=pool[e.rng.below(pool.size())],off=o?g.nr:0;
  const auto&group=by_degree[o].at(g.target_degree[off+anchor]);if(int(group.size())<r)return {};

  int start=int(e.rng.below(group.size()));std::vector<int>out;
  for(int j=0;j<r;++j)out.push_back(group[(start+j)%group.size()]);
  std::sort(out.begin(),out.end());return out;
 }
};

struct ConstraintAwareLabels {
 struct Group{std::vector<int>nodes;bool uniform;};
 std::array<std::array<std::vector<Group>,7>,2>groups;
 std::array<std::array<std::vector<U>,7>,2>prefix;
 std::array<std::vector<int>,2>active;
 bool unit_forced=true;
 explicit ConstraintAwareLabels(const Graph&g){
  for(int v=0;v<g.nr;++v)unit_forced&=g.target_strength[v]==g.target_degree[v];
  MarginalLabels base(g);active=base.active;
  for(int o=0;o<2;++o){int off=o?g.nr:0;
   for(int r=2;r<=6;++r){
    auto add=[&](const std::vector<int>&v,bool uni){if(int(v.size())<r)return;groups[o][r].push_back({v,uni});U mass=v.size();if(!prefix[o][r].empty())mass+=prefix[o][r].back();prefix[o][r].push_back(mass);};
    for(const auto&item:base.by_degree[o]){
     const auto&v=item.second;
     if(item.first==1){size_t start=0;while(start<v.size()){size_t end=start+1;while(end<v.size()&&g.target_strength[off+v[end]]==g.target_strength[off+v[start]])++end;add(std::vector<int>(v.begin()+start,v.begin()+end),true);start=end;}}
     else add(v,g.target_strength[off+v.front()]==g.target_strength[off+v.back()]);
    }
   }
  }
 }
 static std::vector<int>uniform_subset(Engine&e,const std::vector<int>&pool,int r){
  if(int(pool.size())<r)return {};std::vector<int>out;
  for(int j=int(pool.size())-r;j<int(pool.size());++j){int k=int(e.rng.below(U(j)+1));if(std::find(out.begin(),out.end(),k)!=out.end())k=j;out.push_back(k);}
  for(int&v:out)v=pool[v];std::sort(out.begin(),out.end());return out;
 }
 std::vector<int>select(Engine&e,const Graph&,int&o,int r,bool guided){
  if(!guided||e.rng.below(5)==0)return uniform_subset(e,active[o],r);
  bool available0=!groups[0][r].empty(),available1=!groups[1][r].empty();
  if(!available0&&!available1)return {};
  if(!available0)o=1;else if(!available1)o=0;
  const auto&cumulative=prefix[o][r];U draw=e.rng.below(cumulative.back());
  size_t index=std::upper_bound(cumulative.begin(),cumulative.end(),draw)-cumulative.begin();
  const auto&group=groups[o][r][index];if(group.uniform)return uniform_subset(e,group.nodes,r);
  size_t start=e.rng.below(group.nodes.size());std::vector<int>out;
  for(int j=0;j<r;++j)out.push_back(group.nodes[(start+j)%group.nodes.size()]);std::sort(out.begin(),out.end());return out;
 }
};

void kdd_unit_step(Engine&e,Graph&g){
 e.stat.work++;if(g.edges.empty())return;
 auto x=g.edges[e.rng.below(g.edges.size())],y=g.edges[e.rng.below(g.edges.size())];
 if(x.r==y.r||x.c==y.c||g.find(x.r,y.c)>=0||g.find(y.r,x.c)>=0)return;
 if(x.w!=1||y.w!=1)throw std::runtime_error("unit constraint dispatch found nonunit edge");
 g.set_raw(x.r,x.c,0);g.set_raw(y.r,y.c,0);g.set_raw(x.r,y.c,1);g.set_raw(y.r,x.c,1);e.stat.changed_outer++;
}

struct TradeCounters {
 U calls=0,private_calls=0,joint_calls=0,empty_labels=0,nontrivial=0,singletons=0,changed=0;
 U full_private_columns=0,sampled_private_columns=0,dp_states=0,dp_branches=0,grouped_fast_calls=0,grouped_fallback_calls=0,unit_capacity_calls=0;
 unsigned long long selection_ns=0,solve_ns=0,commit_ns=0;
};

void base_branch(Engine&e,Graph&g){int m=int(e.rng.below(3));if(m==0){U a=g.hash1,b=g.hash2;e.cycle(g);e.stat.changed_outer+=a!=g.hash1||b!=g.hash2;}else e.optimized_swap(g,m==2);}

template<class Labels>
void invariant_trade(Engine&e,Graph&g,Labels&labels,TradeCounters&st,
                     bool guided,bool joint,int width,int maxr,int strong_parts=1){
 if(e.rng.below(2)==0){e.stat.work++;e.stat.lazy++;return;}
 if(e.rng.below(10)<U(strong_parts)){base_branch(e,g);return;}
 e.stat.work++;st.calls++;int o=int(e.rng.below(2));int rr=joint?2:2+int(e.rng.below(maxr-1));
 auto begin=Clock::now();auto nodes=labels.select(e,g,o,rr,guided);
 if(nodes.empty()){st.empty_labels++;return;}
 std::vector<int>unioncols;
 for(int v:nodes)for(int id:g.adj[o?g.nr+v:v])unioncols.push_back(o?g.edges[id].r:g.edges[id].c);
 std::sort(unioncols.begin(),unioncols.end());unioncols.erase(std::unique(unioncols.begin(),unioncols.end()),unioncols.end());
 std::vector<int>chosen;
 if(joint)chosen=unioncols;
 else for(int c:unioncols){int arity=0;for(int v:nodes)arity+=(o?g.value(c,v):g.value(v,c))>0;if(arity==1)chosen.push_back(c);}
 st.full_private_columns+=chosen.size();

 if(int(chosen.size())>width){std::vector<int>idx;
  for(int j=int(chosen.size())-width;j<int(chosen.size());++j){int k=int(e.rng.below(U(j)+1));if(std::find(idx.begin(),idx.end(),k)!=idx.end())k=j;idx.push_back(k);}
  std::vector<int>cap;for(int k:idx)cap.push_back(chosen[k]);chosen=std::move(cap);std::sort(chosen.begin(),chosen.end());
 }
 st.sampled_private_columns+=chosen.size();st.selection_ns+=std::chrono::duration_cast<std::chrono::nanoseconds>(Clock::now()-begin).count();
 if(chosen.empty()){st.singletons++;return;}
 std::vector<std::vector<I>>rows(rr,std::vector<I>(chosen.size()));
 for(int j=0;j<rr;++j)for(size_t k=0;k<chosen.size();++k)rows[j][k]=o?g.value(chosen[k],nodes[j]):g.value(nodes[j],chosen[k]);
 auto solving=Clock::now();std::vector<std::vector<I>>draw;
 if(joint){st.joint_calls++;FastCountedBlock cb(rows[0],rows[1],&e.stat);bool multiple=cb.nontrivial();st.nontrivial+=multiple;st.singletons+=!multiple;
  OwnerRandomAdapter random{e.rng};auto result=cb.draw_metropolis_refresh(random);draw={std::move(result.first),std::move(result.second)};
 }else{st.private_calls++;UnitCapacityPrivateV19 cb(rows);st.nontrivial+=cb.total>1;st.singletons+=cb.total==1;if(cb.fastbool){st.unit_capacity_calls++;st.grouped_fast_calls++;}else if(cb.fallback->fastbool)st.grouped_fast_calls++;else{st.grouped_fallback_calls++;st.dp_states+=cb.fallback->fallback->dp_states;st.dp_branches+=cb.fallback->fallback->dp_branches;}draw=cb.draw(e.rng,true);}
 st.solve_ns+=std::chrono::duration_cast<std::chrono::nanoseconds>(Clock::now()-solving).count();
 auto commit=Clock::now();bool changed=false;
 for(int j=0;j<rr;++j)for(size_t k=0;k<chosen.size();++k){changed|=draw[j][k]!=rows[j][k];if(o)g.set_raw(chosen[k],nodes[j],draw[j][k]);else g.set_raw(nodes[j],chosen[k],draw[j][k]);}
 st.commit_ns+=std::chrono::duration_cast<std::chrono::nanoseconds>(Clock::now()-commit).count();st.changed+=changed;e.stat.changed_outer+=changed;
}

void kdd_unit_injected_v19(Engine&e,Graph&g,U ia,U ib){
 e.stat.work++;if(g.edges.empty())return;
 auto x=g.edges[ia],y=g.edges[ib];
 if(x.r==y.r||x.c==y.c||g.find(x.r,y.c)>=0||g.find(y.r,x.c)>=0)return;
 if(x.w!=1||y.w!=1)throw std::runtime_error("unit constraint dispatch found nonunit edge");
 g.set_raw(x.r,x.c,0);g.set_raw(y.r,y.c,0);g.set_raw(x.r,y.c,1);g.set_raw(y.r,x.c,1);e.stat.changed_outer++;
}
