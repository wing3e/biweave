#pragma once
#include <algorithm>
#include <array>
#include <limits>
#include <ostream>
#include <stdexcept>
#include <vector>

struct DisconnectedBundleHeatbath {
 struct Label {int node=-1,old_owner=-1;I weight=0;};
 using Partition=std::array<int,6>;
 bool requested=false,active=false;
 std::array<bool,2> axis_active={false,false};
  
 std::array<std::vector<int>,2> objects;
 int rows=0,columns=0;
 U compose_calls=0,no_static_candidates=0,changes=0;
 std::array<U,2> axis_calls={0,0},axis_changes={0,0};
 U selected_triples=0,shared_opposite_holds=0,partitions_examined=0;
 U legal_partitions=0,max_legal_partitions=0,singleton_holds=0;
 U candidate_pair_checks=0,pair_sum_builds=0;
 U rank_draws=0,selected_original=0,moved_records=0,cell_writes=0,index_checks=0;

 void initialize(const Graph&g,bool want){
  requested=want;if(!want)return;rows=g.nr;columns=g.nc;
  if(g.D)throw std::runtime_error("bundle initialization outside exact margins");
  for(int axis=0;axis<2;++axis){
   const int n=axis?g.nc:g.nr,opposite=axis?g.nr:g.nc,offset=axis?g.nr:0;

   if(opposite<6)continue;
   U count=0;for(int v=0;v<n;++v)count+=g.target_degree[offset+v]==2;
   if(count<3)continue;
   auto&pool=objects[axis];pool.reserve(size_t(count));
   for(int v=0;v<n;++v)if(g.target_degree[offset+v]==2)pool.push_back(v);
   axis_active[axis]=true;active=true;
  }
 }

 void check(const Graph&g){
  if(!requested)return;++index_checks;
  if(g.nr!=rows||g.nc!=columns||g.D)throw std::runtime_error("bundle graph/degree audit");
  for(int axis=0;axis<2;++axis){
   const int n=axis?g.nc:g.nr,opposite=axis?g.nr:g.nc,offset=axis?g.nr:0;
   U count=0;for(int v=0;v<n;++v)count+=g.target_degree[offset+v]==2;
   const bool expected=opposite>=6&&count>=3;
   if(axis_active[axis]!=expected||(expected&&objects[axis].size()!=count)||(!expected&&!objects[axis].empty()))
    throw std::runtime_error("bundle static target pool cardinality");
   if(!expected)continue;
   U k=0;for(int v=0;v<n;++v)if(g.target_degree[offset+v]==2){
    if(objects[axis].at(size_t(k++))!=v||g.degree[offset+v]!=2||g.adj[offset+v].size()!=2)
     throw std::runtime_error("bundle static target pool labels");
   }
  }
  if(active!=(axis_active[0]||axis_active[1]))throw std::runtime_error("bundle active audit");
 }

 bool step_axis(Engine&e,Graph&g,int axis){
  if(axis<0||axis>1||!requested||!axis_active[axis])throw std::runtime_error("unrequested bundle direction");
  if(g.D)throw std::runtime_error("bundle step outside exact degree state");
  ++axis_calls[axis];++e.stat.work;
  const auto&pool=objects[axis];const U n=U(pool.size());
   
  std::array<U,3>selected{};int used=0;
  for(U j=n-3;j<n;++j){U k=e.rng.below(j+1);bool duplicate=false;
   for(int t=0;t<used;++t)duplicate|=selected[t]==k;
   if(duplicate)k=j;selected[used++]=k;
  }
  std::array<int,3>nodes={pool[size_t(selected[0])],pool[size_t(selected[1])],pool[size_t(selected[2])]};
  std::sort(nodes.begin(),nodes.end());++selected_triples;
  std::array<Label,6>labels;std::array<I,3>strengths{};int next=0;
  for(int owner=0;owner<3;++owner){
   const int vertex=axis?g.nr+nodes[owner]:nodes[owner];
   if(g.target_degree[vertex]!=2||g.degree[vertex]!=2||g.adj[vertex].size()!=2)
    throw std::runtime_error("bundle selected object no longer degree two");
   strengths[owner]=g.target_strength[vertex];S128 sum=0;
   for(int id:g.adj[vertex]){const auto edge=g.edges.at(size_t(id));
    if(edge.w<=0||(axis?edge.c:edge.r)!=nodes[owner])throw std::runtime_error("bundle adjacency record");
    labels[size_t(next++)]={axis?edge.r:edge.c,owner,edge.w};sum+=S128(edge.w);
   }
   if(sum!=S128(strengths[owner]))throw std::runtime_error("bundle selected object strength");
  }
  if(next!=6)throw std::runtime_error("bundle label count");
  std::sort(labels.begin(),labels.end(),[](const Label&a,const Label&b){return a.node<b.node;});
  for(int i=1;i<6;++i)if(labels[i-1].node==labels[i].node){++shared_opposite_holds;return false;}

  Partition original{};for(int i=0;i<6;++i)original[i]=labels[i].old_owner;
  std::vector<Partition>legal;legal.reserve(90);const U examined=90;U original_count=0;

  std::array<std::array<S128,6>,6>pair_sums{};
  for(int a=0;a<6;++a)for(int b=a+1;b<6;++b){pair_sums[a][b]=S128(labels[a].weight)+labels[b].weight;++pair_sum_builds;}
  for(int a=0;a<6;++a)for(int b=a+1;b<6;++b){
   ++candidate_pair_checks;if(pair_sums[a][b]!=S128(strengths[0]))continue;
   for(int c=0;c<6;++c)if(c!=a&&c!=b)
    for(int d=c+1;d<6;++d)if(d!=a&&d!=b){
     ++candidate_pair_checks;if(pair_sums[c][d]!=S128(strengths[1]))continue;
     std::array<int,2>remaining{};int next_remaining=0;
     for(int i=0;i<6;++i)if(i!=a&&i!=b&&i!=c&&i!=d)remaining[next_remaining++]=i;
     if(next_remaining!=2)throw std::runtime_error("bundle fast remaining pair count");
     ++candidate_pair_checks;
     if(pair_sums[remaining[0]][remaining[1]]!=S128(strengths[2]))continue;
     Partition partition{};partition.fill(2);partition[a]=partition[b]=0;partition[c]=partition[d]=1;
     legal.push_back(partition);original_count+=partition==original;
    }
  }
  if(examined!=90||original_count!=1||legal.empty()||legal.size()>90)
   throw std::runtime_error("bundle partition completeness/original audit");
  partitions_examined+=examined;legal_partitions+=U(legal.size());max_legal_partitions=std::max(max_legal_partitions,U(legal.size()));
  if(legal.size()==1){++singleton_holds;++selected_original;return false;}
  const Partition chosen=legal[size_t(e.rng.below(U(legal.size())))];++rank_draws;
  if(chosen==original){++selected_original;return false;}

  std::array<int,6>opposite_degree{};
  for(int i=0;i<6;++i){const int v=axis?labels[i].node:g.nr+labels[i].node;opposite_degree[i]=g.degree[v];
   if(opposite_degree[i]!=g.target_degree[v]||g.adj[v].size()!=U(opposite_degree[i]))throw std::runtime_error("bundle opposite precommit degree");
   for(int owner=0;owner<3;++owner){const I w=axis?g.value(labels[i].node,nodes[owner]):g.value(nodes[owner],labels[i].node);
    const I expected=owner==original[i]?labels[i].weight:0;
    if(w!=expected)throw std::runtime_error("bundle precommit collision audit");
   }
  }
  const U old_edges=U(g.edges.size());
  auto put=[&](int i,int owner,I w){if(axis)g.set_raw(labels[i].node,nodes[owner],w);else g.set_raw(nodes[owner],labels[i].node,w);++cell_writes;};

  for(int i=0;i<6;++i)if(chosen[i]!=original[i])put(i,original[i],0);
  for(int i=0;i<6;++i)if(chosen[i]!=original[i]){put(i,chosen[i],labels[i].weight);++moved_records;}
  if(g.D||U(g.edges.size())!=old_edges)throw std::runtime_error("bundle nonclosed commit");
  for(int owner=0;owner<3;++owner){const int v=axis?g.nr+nodes[owner]:nodes[owner];
   if(g.degree[v]!=2||g.adj[v].size()!=2)throw std::runtime_error("bundle object final degree");
   S128 sum=0;for(int id:g.adj[v])sum+=S128(g.edges.at(size_t(id)).w);
   if(sum!=S128(strengths[owner]))throw std::runtime_error("bundle object final strength");
  }
  for(int i=0;i<6;++i){const int v=axis?labels[i].node:g.nr+labels[i].node;
   const I w=axis?g.value(labels[i].node,nodes[chosen[i]]):g.value(nodes[chosen[i]],labels[i].node);
   if(g.degree[v]!=opposite_degree[i]||w!=labels[i].weight)throw std::runtime_error("bundle opposite final margin");
  }
  ++changes;++axis_changes[axis];++e.stat.changed_outer;return true;
 }

 bool compose(Engine&e,Graph&g){
  if(!requested)throw std::runtime_error("unrequested bundle composition");
  ++compose_calls;if(!active){++no_static_candidates;return false;}
  bool changed=false;

  if(axis_active[1])changed=step_axis(e,g,1)||changed;
  if(axis_active[0])changed=step_axis(e,g,0)||changed;
  return changed;
 }

 void metadata(std::ostream&f)const{
  f<<"\"DB_requested\":"<<(requested?"true":"false")<<",\"DB_active\":"<<(active?"true":"false")
   <<",\"DB_row_axis_active\":"<<(axis_active[0]?"true":"false")<<",\"DB_column_axis_active\":"<<(axis_active[1]?"true":"false")
   <<",\"DB_row_object_pool\":"<<objects[0].size()<<",\"DB_column_object_pool\":"<<objects[1].size()
   <<",\"DB_compose_calls\":"<<compose_calls<<",\"DB_no_static_candidates\":"<<no_static_candidates
   <<",\"DB_row_axis_calls\":"<<axis_calls[0]<<",\"DB_column_axis_calls\":"<<axis_calls[1]
   <<",\"DB_changes\":"<<changes<<",\"DB_row_axis_changes\":"<<axis_changes[0]<<",\"DB_column_axis_changes\":"<<axis_changes[1]
   <<",\"DB_selected_triples\":"<<selected_triples<<",\"DB_shared_opposite_holds\":"<<shared_opposite_holds
   <<",\"DB_partitions_examined\":"<<partitions_examined<<",\"DB_legal_partitions\":"<<legal_partitions<<",\"DB_max_legal_partitions\":"<<max_legal_partitions
   <<",\"DB_singleton_holds\":"<<singleton_holds<<",\"DB_rank_draws\":"<<rank_draws<<",\"DB_selected_original\":"<<selected_original
   <<",\"DB_candidate_pair_checks\":"<<candidate_pair_checks<<",\"DB_pair_sum_builds\":"<<pair_sum_builds
   <<",\"DB_moved_records\":"<<moved_records<<",\"DB_cell_writes\":"<<cell_writes<<",\"DB_index_checks\":"<<index_checks
   <<",\"DB_policy\":\"fixed degree2 three-object uniform subset; six distinct named endpoints keep weights; exact uniform among 90 theoretical labelled unordered 2+2+2 assignments, pair-sum early filtering in unchanged v1 order; actual comparisons in DB_candidate_pair_checks and fifteen pair sums per descriptor; include original; column then row before T; no productive retry\",";
 }
};
