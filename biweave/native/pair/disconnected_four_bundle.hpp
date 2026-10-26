#pragma once
#include <algorithm>
#include <array>
#include <ostream>
#include <stdexcept>
#include <vector>

struct DisconnectedFourBundleHeatbath {
 struct Label{int node=-1,old_owner=-1;I weight=0;};
 using Partition=std::array<int,8>;
 bool requested=false,active=false;std::array<bool,2>axis_active={false,false};
 std::array<std::vector<int>,2>objects;int rows=0,columns=0;
 U compose_calls=0,no_static_candidates=0,changes=0,selected_quadruples=0;
 std::array<U,2>axis_calls={0,0},axis_changes={0,0};
 U shared_opposite_holds=0,partitions_examined=0,legal_partitions=0,max_legal_partitions=0;
 U singleton_holds=0,rank_draws=0,selected_original=0,pair_sum_builds=0,candidate_pair_checks=0;
 U moved_records=0,cell_writes=0,index_checks=0;
 void initialize(const Graph&g,bool want){
  requested=want;if(!want)return;rows=g.nr;columns=g.nc;
  if(g.D)throw std::runtime_error("D4 initialization outside exact degree margins");
  for(int axis=0;axis<2;++axis){const int n=axis?g.nc:g.nr,opposite=axis?g.nr:g.nc,offset=axis?g.nr:0;

   if(opposite<8)continue;U count=0;
   for(int v=0;v<n;++v)count+=g.target_degree[offset+v]==2;
   if(count<4)continue;auto&pool=objects[axis];pool.reserve(size_t(count));
   for(int v=0;v<n;++v)if(g.target_degree[offset+v]==2)pool.push_back(v);
   axis_active[axis]=true;active=true;
  }
 }
 void check(const Graph&g){
  if(!requested)return;++index_checks;
  if(g.nr!=rows||g.nc!=columns||g.D)throw std::runtime_error("D4 graph audit");
  for(int axis=0;axis<2;++axis){const int n=axis?g.nc:g.nr,opposite=axis?g.nr:g.nc,offset=axis?g.nr:0;
   U count=0;for(int v=0;v<n;++v)count+=g.target_degree[offset+v]==2;
   const bool expected=opposite>=8&&count>=4;
   if(axis_active[axis]!=expected||(expected&&objects[axis].size()!=count)||(!expected&&!objects[axis].empty()))throw std::runtime_error("D4 static pool size");
   if(!expected)continue;U k=0;
   for(int v=0;v<n;++v)if(g.target_degree[offset+v]==2){
    if(objects[axis].at(size_t(k++))!=v||g.degree[offset+v]!=2||g.adj[offset+v].size()!=2)throw std::runtime_error("D4 static pool label");
   }
  }
  if(active!=(axis_active[0]||axis_active[1]))throw std::runtime_error("D4 active flag audit");
 }
 bool step_axis(Engine&e,Graph&g,int axis){
  if(axis<0||axis>1||!requested||!axis_active[axis]||g.D)throw std::runtime_error("D4 invalid step");
  ++axis_calls[axis];++e.stat.work;const auto&pool=objects[axis];const U n=U(pool.size());
  std::array<U,4>selected{};int used=0;
  for(U j=n-4;j<n;++j){U k=e.rng.below(j+1);bool duplicate=false;
   for(int i=0;i<used;++i)duplicate|=selected[i]==k;
   if(duplicate)k=j;selected[used++]=k;
  }
  std::array<int,4>nodes{};for(int i=0;i<4;++i)nodes[i]=pool[size_t(selected[i])];
  std::sort(nodes.begin(),nodes.end());++selected_quadruples;
  std::array<Label,8>labels;std::array<I,4>strengths{};int next=0;
  for(int owner=0;owner<4;++owner){const int v=axis?g.nr+nodes[owner]:nodes[owner];
   if(g.target_degree[v]!=2||g.degree[v]!=2||g.adj[v].size()!=2)throw std::runtime_error("D4 selected object degree");
   strengths[owner]=g.target_strength[v];S128 sum=0;
   for(int id:g.adj[v]){const auto edge=g.edges.at(size_t(id));
    if(edge.w<=0||(axis?edge.c:edge.r)!=nodes[owner])throw std::runtime_error("D4 adjacency record");
    labels[size_t(next++)]={axis?edge.r:edge.c,owner,edge.w};sum+=S128(edge.w);
   }
   if(sum!=S128(strengths[owner]))throw std::runtime_error("D4 selected strength");
  }
  if(next!=8)throw std::runtime_error("D4 named record count");
  std::sort(labels.begin(),labels.end(),[](const Label&a,const Label&b){return a.node<b.node;});
  for(int i=1;i<8;++i)if(labels[i-1].node==labels[i].node){++shared_opposite_holds;return false;}
  Partition original{};for(int i=0;i<8;++i)original[i]=labels[i].old_owner;
  std::array<std::array<S128,8>,8>sums{};
  for(int a=0;a<8;++a)for(int b=a+1;b<8;++b){sums[a][b]=S128(labels[a].weight)+labels[b].weight;++pair_sum_builds;}
  std::vector<Partition>legal;legal.reserve(2520);U original_count=0;

  for(int a=0;a<8;++a)for(int b=a+1;b<8;++b){
   ++candidate_pair_checks;if(sums[a][b]!=S128(strengths[0]))continue;
   for(int c=0;c<8;++c)if(c!=a&&c!=b)for(int d=c+1;d<8;++d)if(d!=a&&d!=b){
    ++candidate_pair_checks;if(sums[c][d]!=S128(strengths[1]))continue;
    for(int f=0;f<8;++f)if(f!=a&&f!=b&&f!=c&&f!=d)
     for(int h=f+1;h<8;++h)if(h!=a&&h!=b&&h!=c&&h!=d){
      ++candidate_pair_checks;if(sums[f][h]!=S128(strengths[2]))continue;
      std::array<int,2>remaining{};int count=0;
      for(int i=0;i<8;++i)if(i!=a&&i!=b&&i!=c&&i!=d&&i!=f&&i!=h)remaining[count++]=i;
      if(count!=2)throw std::runtime_error("D4 remaining pair count");
      ++candidate_pair_checks;if(sums[remaining[0]][remaining[1]]!=S128(strengths[3]))continue;
      Partition assignment{};assignment.fill(3);assignment[a]=assignment[b]=0;assignment[c]=assignment[d]=1;assignment[f]=assignment[h]=2;
      legal.push_back(assignment);original_count+=assignment==original;
     }
   }
  }
  if(legal.empty()||legal.size()>2520||original_count!=1)throw std::runtime_error("D4 completeness/current audit");
  partitions_examined+=2520;legal_partitions+=U(legal.size());max_legal_partitions=std::max(max_legal_partitions,U(legal.size()));
  if(legal.size()==1){++singleton_holds;++selected_original;return false;}
  const Partition chosen=legal[size_t(e.rng.below(U(legal.size())))];++rank_draws;
  if(chosen==original){++selected_original;return false;}
  std::array<int,8>opposite_degree{};
  for(int i=0;i<8;++i){const int v=axis?labels[i].node:g.nr+labels[i].node;opposite_degree[i]=g.degree[v];
   if(opposite_degree[i]!=g.target_degree[v]||g.adj[v].size()!=U(opposite_degree[i]))throw std::runtime_error("D4 opposite precommit degree");
   for(int owner=0;owner<4;++owner){const I w=axis?g.value(labels[i].node,nodes[owner]):g.value(nodes[owner],labels[i].node);
    if(w!=(owner==original[i]?labels[i].weight:0))throw std::runtime_error("D4 precommit destination collision");
   }
  }
  const U old_edges=U(g.edges.size());
  auto put=[&](int i,int owner,I w){if(axis)g.set_raw(labels[i].node,nodes[owner],w);else g.set_raw(nodes[owner],labels[i].node,w);++cell_writes;};

  for(int i=0;i<8;++i)if(chosen[i]!=original[i])put(i,original[i],0);
  for(int i=0;i<8;++i)if(chosen[i]!=original[i]){put(i,chosen[i],labels[i].weight);++moved_records;}
  if(g.D||U(g.edges.size())!=old_edges)throw std::runtime_error("D4 commit did not close");
  for(int owner=0;owner<4;++owner){const int v=axis?g.nr+nodes[owner]:nodes[owner];
   if(g.degree[v]!=2||g.adj[v].size()!=2)throw std::runtime_error("D4 final object degree");
   S128 sum=0;for(int id:g.adj[v])sum+=S128(g.edges.at(size_t(id)).w);
   if(sum!=S128(strengths[owner]))throw std::runtime_error("D4 final object strength");
  }
  for(int i=0;i<8;++i){const int v=axis?labels[i].node:g.nr+labels[i].node;
   const I w=axis?g.value(labels[i].node,nodes[chosen[i]]):g.value(nodes[chosen[i]],labels[i].node);
   if(g.degree[v]!=opposite_degree[i]||w!=labels[i].weight)throw std::runtime_error("D4 final opposite margin");
  }
  ++changes;++axis_changes[axis];++e.stat.changed_outer;return true;
 }
 bool compose(Engine&e,Graph&g){
  if(!requested)throw std::runtime_error("unrequested D4 composition");
  ++compose_calls;if(!active){++no_static_candidates;return false;}
  bool changed=false;if(axis_active[1])changed=step_axis(e,g,1)||changed;if(axis_active[0])changed=step_axis(e,g,0)||changed;return changed;
 }
 void metadata(std::ostream&f)const{
  f<<"\"D4_requested\":"<<(requested?"true":"false")<<",\"D4_active\":"<<(active?"true":"false")
   <<",\"D4_row_axis_active\":"<<(axis_active[0]?"true":"false")<<",\"D4_column_axis_active\":"<<(axis_active[1]?"true":"false")
   <<",\"D4_row_object_pool\":"<<objects[0].size()<<",\"D4_column_object_pool\":"<<objects[1].size()
   <<",\"D4_compose_calls\":"<<compose_calls<<",\"D4_no_static_candidates\":"<<no_static_candidates
   <<",\"D4_row_axis_calls\":"<<axis_calls[0]<<",\"D4_column_axis_calls\":"<<axis_calls[1]
   <<",\"D4_changes\":"<<changes<<",\"D4_row_axis_changes\":"<<axis_changes[0]<<",\"D4_column_axis_changes\":"<<axis_changes[1]
   <<",\"D4_selected_quadruples\":"<<selected_quadruples<<",\"D4_shared_opposite_holds\":"<<shared_opposite_holds
   <<",\"D4_partitions_examined\":"<<partitions_examined<<",\"D4_legal_partitions\":"<<legal_partitions<<",\"D4_max_legal_partitions\":"<<max_legal_partitions
   <<",\"D4_singleton_holds\":"<<singleton_holds<<",\"D4_rank_draws\":"<<rank_draws<<",\"D4_selected_original\":"<<selected_original
   <<",\"D4_pair_sum_builds\":"<<pair_sum_builds<<",\"D4_candidate_pair_checks\":"<<candidate_pair_checks
   <<",\"D4_moved_records\":"<<moved_records<<",\"D4_cell_writes\":"<<cell_writes<<",\"D4_index_checks\":"<<index_checks
   <<",\"D4_policy\":\"fixed targetdegree2 four-object uniform subset; eight distinct named endpoints keep weights; 2520 theoretical 2+2+2+2 labelled assignments, 28 S128 pair sums and early filtering; uniform legal rank including current; only selected coverage branch after optional D3, column then row before T; no productive retry; priority certificate forbidden\",";
 }
};
