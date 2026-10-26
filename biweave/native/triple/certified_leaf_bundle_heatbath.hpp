#pragma once
#include <algorithm>
#include <array>
#include <cstddef>
#include <limits>
#include <ostream>
#include <stdexcept>
#include <vector>

struct CertifiedLeafBundleHeatbath {
 using Wide=__uint128_t;
 struct Label {int node=-1,old_owner=-1;I weight=0;};
 using Partition=std::array<int,8>;
 struct Fiber {
  std::vector<Partition> legal;
  Partition original{};
  U pair_sum_builds=0,pair_checks=0,terminal_checks=0;
  U partition_upper_bound=0;
 };
 bool requested=false,active=false;
 int rows=0,columns=0;
 std::array<bool,2> axis_certified={false,false},axis_active={false,false};
 std::array<std::vector<int>,2> objects;
 std::array<U,2> object_counts={0,0};
 std::array<int,2> window_size={0,0};
 U compose_calls=0,no_static_candidates=0,index_checks=0,inactive_checks=0,changes=0;
 U selected_blocks=0,valid_tables=0,margin_checks=0,margin_records_checked=0;
 U subset_draws=0,sigma_checks=0;
 std::array<U,2> axis_calls={0,0},axis_changes={0,0};
 std::array<U,3> k_calls={0,0,0};
 U pair_sum_builds=0,pair_checks=0,terminal_checks=0;
 U partition_upper_bound_total=0,legal_partitions=0,max_legal_partitions=0;
 U singleton_holds=0,rank_draws=0,selected_original=0,moved_records=0,cell_writes=0;

 static U upper_bound(int k) {
  if(k==2)return 6;if(k==3)return 90;if(k==4)return 2520;
  throw std::runtime_error("leaf bundle window size must be2,3,4");
 }

 static Fiber enumerate(const std::array<Label,8>&labels,
                        const std::array<I,4>&strengths,int k) {
  Fiber out;out.partition_upper_bound=upper_bound(k);out.original.fill(-1);
  const int count=2*k;std::array<int,4> cardinality{};std::array<S128,4> original_sum{};
  for(int i=0;i<count;++i){const Label&label=labels[i];
   if(label.node<0||label.weight<=0||label.old_owner<0||label.old_owner>=k)
    throw std::runtime_error("leaf bundle invalid positive record");
   for(int j=0;j<i;++j)if(labels[j].node==label.node)
    throw std::runtime_error("leaf bundle names must be distinct global leaves");
   ++cardinality[label.old_owner];original_sum[label.old_owner]+=S128(label.weight);
   out.original[i]=label.old_owner;
  }
  for(int owner=0;owner<k;++owner)
   if(cardinality[owner]!=2||strengths[owner]<2||original_sum[owner]!=S128(strengths[owner]))
    throw std::runtime_error("leaf bundle original object ledger");
  std::array<std::array<S128,8>,8> sums{};
  for(int a=0;a<count;++a)for(int b=a+1;b<count;++b){
   sums[a][b]=S128(labels[a].weight)+S128(labels[b].weight);++out.pair_sum_builds;}
  out.legal.reserve(size_t(out.partition_upper_bound));Partition assignment{};assignment.fill(-1);
  U original_count=0;
  auto recurse=[&](auto&&self,int owner,unsigned remaining)->void {
   if(owner==k-1){std::array<int,2> pair{};int used=0;
    for(int i=0;i<count;++i)if(remaining&(1U<<i)){
     if(used>=2)throw std::runtime_error("leaf bundle forced pair cardinality");pair[used++]=i;}
    if(used!=2)throw std::runtime_error("leaf bundle incomplete forced pair");
    ++out.pair_checks;++out.terminal_checks;
    if(sums[pair[0]][pair[1]]!=S128(strengths[owner]))return;
    assignment[pair[0]]=assignment[pair[1]]=owner;
    if(out.legal.size()>=out.partition_upper_bound)throw std::runtime_error("leaf bundle partition bound");
    original_count+=assignment==out.original;out.legal.push_back(assignment);
    assignment[pair[0]]=assignment[pair[1]]=-1;return;
   }
   for(int a=0;a<count;++a)if(remaining&(1U<<a))
    for(int b=a+1;b<count;++b)if(remaining&(1U<<b)){
     ++out.pair_checks;if(sums[a][b]!=S128(strengths[owner]))continue;
     assignment[a]=assignment[b]=owner;
     self(self,owner+1,remaining&~((1U<<a)|(1U<<b)));
     assignment[a]=assignment[b]=-1;
    }
  };
  recurse(recurse,0,(1U<<count)-1);
  if(out.legal.empty()||out.legal.size()>out.partition_upper_bound||original_count!=1)
   throw std::runtime_error("leaf bundle complete fiber/original audit");
  return out;
 }
 static const Partition&unrank(const Fiber&fiber,U rank) {
  if(rank>=fiber.legal.size())throw std::runtime_error("leaf bundle rank range");
  return fiber.legal[size_t(rank)];
 }
 void full_margin(const Graph&g,int vertex) {
  ++margin_checks;
  const int degree=g.target_degree.at(size_t(vertex));
  if(degree<0||g.target_strength.at(size_t(vertex))<0||
     g.degree.at(size_t(vertex))!=degree||g.adj.at(size_t(vertex)).size()!=size_t(degree))
   throw std::runtime_error("leaf bundle full degree margin");
  S128 strength=0;
  for(int id:g.adj.at(size_t(vertex))){const auto edge=g.edges.at(size_t(id));++margin_records_checked;
   if(edge.w<=0||edge.r<0||edge.r>=g.nr||edge.c<0||edge.c>=g.nc||
      (vertex<g.nr?edge.r!=vertex:g.nr+edge.c!=vertex))
    throw std::runtime_error("leaf bundle full adjacency margin");
   strength+=S128(edge.w);
  }
  if(strength!=S128(g.target_strength.at(size_t(vertex))))
   throw std::runtime_error("leaf bundle full strength margin");
 }
 static void shape(const Graph&g) {
  if(g.nr<0||g.nc<0||g.D)throw std::runtime_error("leaf bundle graph outside closed F");
  const size_t n=size_t(g.nr)+size_t(g.nc);
  if(g.target_degree.size()!=n||g.target_strength.size()!=n||g.degree.size()!=n||g.adj.size()!=n)
   throw std::runtime_error("leaf bundle graph margin vector shape");
 }
 void initialize(const Graph&g,bool want) {
  *this=CertifiedLeafBundleHeatbath{};requested=want;if(!want)return;
  shape(g);rows=g.nr;columns=g.nc;
  for(int axis=0;axis<2;++axis){
   const int n=axis?g.nc:g.nr,offset=axis?g.nr:0;
   const int opposite=axis?g.nr:g.nc,opposite_offset=axis?0:g.nr;
   bool certified=true;
   for(int node=0;node<opposite;++node){const int degree=g.target_degree[opposite_offset+node];
    if(degree<0)throw std::runtime_error("leaf bundle negative target degree");
    certified&=degree<=1;}
   axis_certified[axis]=certified;if(!certified)continue;
   U count=0;for(int node=0;node<n;++node){
    if(g.target_degree[offset+node]<0)throw std::runtime_error("leaf bundle negative object target degree");
    count+=g.target_degree[offset+node]==2;}
   object_counts[axis]=count;const int k=int(std::min<U>(4,count));window_size[axis]=k;
   auto&pool=objects[axis];pool.reserve(size_t(count));
   for(int node=0;node<n;++node)if(g.target_degree[offset+node]==2)pool.push_back(node);
   if(k<2)continue;
   axis_active[axis]=true;active=true;
  }
 }
 void check(const Graph&g) {
  if(!requested)return;
  shape(g);if(g.nr!=rows||g.nc!=columns)throw std::runtime_error("leaf bundle graph/F audit");

  if(!active){++inactive_checks;return;}
  ++index_checks;
  for(int axis=0;axis<2;++axis){
   const int n=axis?g.nc:g.nr,offset=axis?g.nr:0;
   const int opposite=axis?g.nr:g.nc,opposite_offset=axis?0:g.nr;
   bool certified=true;
   for(int node=0;node<opposite;++node){const int degree=g.target_degree[opposite_offset+node];
    if(degree<0)throw std::runtime_error("leaf bundle negative audit degree");certified&=degree<=1;}
   U count=0;if(certified)for(int node=0;node<n;++node)count+=g.target_degree[offset+node]==2;
   const int k=int(std::min<U>(4,count));const bool expected=certified&&k>=2;
   if(axis_certified[axis]!=certified||object_counts[axis]!=count||window_size[axis]!=k||
      axis_active[axis]!=expected||objects[axis].size()!=size_t(count))
    throw std::runtime_error("leaf bundle static certificate/pool audit");
   if(certified){U next=0;
    for(int node=0;node<n;++node)if(g.target_degree[offset+node]==2)
     if(objects[axis].at(size_t(next++))!=node)
      throw std::runtime_error("leaf bundle static object label audit");
   }
  }
  if(active!=(axis_active[0]||axis_active[1]))
   throw std::runtime_error("leaf bundle active certificate audit");
   
  for(size_t vertex=0;vertex<g.adj.size();++vertex)full_margin(g,int(vertex));
 }
 bool step_axis(Engine&e,Graph&g,int axis) {
  if(axis<0||axis>1||!requested||!axis_active[axis]||!axis_certified[axis]||g.D)
   throw std::runtime_error("leaf bundle invalid certified step");
  ++axis_calls[axis];++e.stat.work;
  const auto&pool=objects[axis];const U n=U(pool.size());const int k=window_size[axis],count=2*k;
  if(k<2||k>4||U(k)>n)throw std::runtime_error("leaf bundle initialized window range");
  ++k_calls[k-2];std::array<U,4> positions{};
  if(n==U(k)){for(int i=0;i<k;++i)positions[i]=U(i);}
  else{int used=0;
   for(U j=n-U(k);j<n;++j){U choice=e.rng.below(j+1);++subset_draws;bool duplicate=false;
    for(int i=0;i<used;++i)duplicate|=positions[i]==choice;
    if(duplicate)choice=j;positions[used++]=choice;}
  }
  std::array<int,4>nodes{};for(int owner=0;owner<k;++owner)nodes[owner]=pool[size_t(positions[owner])];
  std::sort(nodes.begin(),nodes.begin()+k);++selected_blocks;
  std::array<Label,8>labels{};std::array<I,4>strengths{};int next=0;
  for(int owner=0;owner<k;++owner){const int vertex=axis?g.nr+nodes[owner]:nodes[owner];
   if(g.target_degree[vertex]!=2||g.degree[vertex]!=2||g.adj[vertex].size()!=2)
    throw std::runtime_error("leaf bundle selected object degree");
   full_margin(g,vertex);
   strengths[owner]=g.target_strength[vertex];
   for(int id:g.adj[vertex]){const auto edge=g.edges.at(size_t(id));
    if(edge.w<=0||(axis?edge.c:edge.r)!=nodes[owner])throw std::runtime_error("leaf bundle adjacency record");
    const int node=axis?edge.r:edge.c,v=axis?node:g.nr+node;
    if(g.target_degree[v]!=1||g.degree[v]!=1||g.adj[v].size()!=1||g.target_strength[v]!=edge.w)
     throw std::runtime_error("leaf bundle opposite node is not a strength-locked leaf");
    full_margin(g,v);
    labels[size_t(next++)]={node,owner,edge.w};
   }
  }
  if(next!=count)throw std::runtime_error("leaf bundle selected record count");
  std::sort(labels.begin(),labels.begin()+count,[](const Label&a,const Label&b){return a.node<b.node;});
  const Fiber fiber=enumerate(labels,strengths,k);
  valid_tables+=U(fiber.legal.size());
  pair_sum_builds+=fiber.pair_sum_builds;pair_checks+=fiber.pair_checks;terminal_checks+=fiber.terminal_checks;
  partition_upper_bound_total+=fiber.partition_upper_bound;legal_partitions+=U(fiber.legal.size());
  max_legal_partitions=std::max(max_legal_partitions,U(fiber.legal.size()));
  if(fiber.legal.size()==1){++singleton_holds;++selected_original;return false;}
  const Partition chosen=unrank(fiber,e.rng.below(U(fiber.legal.size())));++rank_draws;
  if(chosen==fiber.original){++selected_original;return false;}
  auto value=[&](int i,int owner){return axis?g.value(labels[i].node,nodes[owner]):g.value(nodes[owner],labels[i].node);};
  for(int i=0;i<count;++i)for(int owner=0;owner<k;++owner)
   if(value(i,owner)!=(owner==fiber.original[i]?labels[i].weight:I(0)))
    throw std::runtime_error("leaf bundle precommit destination collision");
  const U old_edges=U(g.edges.size());
  const auto old_sigma=g.exact_sumw2;
  Wide window_sigma=0;
  for(int i=0;i<count;++i)window_sigma+=Wide(U(labels[i].weight))*U(labels[i].weight);
  auto put=[&](int i,int owner,I weight){
   if(axis)g.set_raw(labels[i].node,nodes[owner],weight);else g.set_raw(nodes[owner],labels[i].node,weight);
   ++cell_writes;
  };

  for(int i=0;i<count;++i)put(i,fiber.original[i],0);
  for(int i=0;i<count;++i){put(i,chosen[i],labels[i].weight);moved_records+=chosen[i]!=fiber.original[i];}
  if(g.D||U(g.edges.size())!=old_edges||(g.maintain_exact_sumw2&&g.exact_sumw2!=old_sigma))
   throw std::runtime_error("leaf bundle commit did not close or changed Sigma");
  Wide after_sigma=0;
  for(int owner=0;owner<k;++owner){const int vertex=axis?g.nr+nodes[owner]:nodes[owner];
   full_margin(g,vertex);
   if(g.target_degree[vertex]!=2||g.target_strength[vertex]!=strengths[owner])
    throw std::runtime_error("leaf bundle final object target margin");
   for(int id:g.adj[vertex]){const I weight=g.edges.at(size_t(id)).w;after_sigma+=Wide(U(weight))*U(weight);}
  }
  for(int i=0;i<count;++i){const int v=axis?labels[i].node:g.nr+labels[i].node;
   full_margin(g,v);
   if(g.target_degree[v]!=1||g.degree[v]!=1||g.adj[v].size()!=1||value(i,chosen[i])!=g.target_strength[v])
    throw std::runtime_error("leaf bundle final leaf margin");
  }

  ++sigma_checks;if(after_sigma!=window_sigma)throw std::runtime_error("leaf bundle exact Sigma invariant");
  ++changes;++axis_changes[axis];++e.stat.changed_outer;return true;
 }
 bool compose(Engine&e,Graph&g) {
  if(!requested)throw std::runtime_error("unrequested leaf bundle composition");
  shape(g);if(g.nr!=rows||g.nc!=columns)throw std::runtime_error("leaf bundle changed graph shape");
  ++compose_calls;if(!active){++no_static_candidates;return false;}
  bool changed=false;
  if(axis_active[1])changed=step_axis(e,g,1)||changed;
  if(axis_active[0])changed=step_axis(e,g,0)||changed;
  return changed;
 }
 bool compose_both_axes(Engine&e,Graph&g){return compose(e,g);}
 void metadata(std::ostream&f)const {
  f<<"\"LF_requested\":"<<(requested?"true":"false")<<",\"LF_active\":"<<(active?"true":"false")
   <<",\"LF_axis_certificate\":["<<(axis_certified[0]?"true":"false")<<','<<(axis_certified[1]?"true":"false")<<']'
   <<",\"LF_eligible_count\":["<<object_counts[0]<<','<<object_counts[1]<<']'
   <<",\"LF_k\":["<<window_size[0]<<','<<window_size[1]<<']'
   <<",\"LF_row_axis_certified\":"<<(axis_certified[0]?"true":"false")
   <<",\"LF_column_axis_certified\":"<<(axis_certified[1]?"true":"false")
   <<",\"LF_row_axis_active\":"<<(axis_active[0]?"true":"false")
   <<",\"LF_column_axis_active\":"<<(axis_active[1]?"true":"false")
   <<",\"LF_row_object_pool\":"<<object_counts[0]<<",\"LF_column_object_pool\":"<<object_counts[1]
   <<",\"LF_row_k\":"<<window_size[0]<<",\"LF_column_k\":"<<window_size[1]
   <<",\"LF_compose_calls\":"<<compose_calls<<",\"LF_no_static_candidates\":"<<no_static_candidates
   <<",\"LF_selected_blocks\":"<<selected_blocks<<",\"LF_valid_tables\":"<<valid_tables
   <<",\"LF_row_calls\":"<<axis_calls[0]<<",\"LF_column_calls\":"<<axis_calls[1]
   <<",\"LF_k2_calls\":"<<k_calls[0]<<",\"LF_k3_calls\":"<<k_calls[1]<<",\"LF_k4_calls\":"<<k_calls[2]
   <<",\"LF_changes\":"<<changes<<",\"LF_row_changes\":"<<axis_changes[0]<<",\"LF_column_changes\":"<<axis_changes[1]
   <<",\"LF_pair_sum_builds\":"<<pair_sum_builds<<",\"LF_pair_checks\":"<<pair_checks
   <<",\"LF_terminal_checks\":"<<terminal_checks<<",\"LF_partition_upper_bound_total\":"<<partition_upper_bound_total
   <<",\"LF_legal_partitions\":"<<legal_partitions<<",\"LF_max_legal_partitions\":"<<max_legal_partitions
   <<",\"LF_singleton_holds\":"<<singleton_holds<<",\"LF_rank_draws\":"<<rank_draws
   <<",\"LF_selected_original\":"<<selected_original<<",\"LF_moved_records\":"<<moved_records
   <<",\"LF_cell_writes\":"<<cell_writes<<",\"LF_index_checks\":"<<index_checks
   <<",\"LF_inactive_checks\":"<<inactive_checks
   <<",\"LF_margin_checks\":"<<margin_checks<<",\"LF_margin_records_checked\":"<<margin_records_checked
   <<",\"LF_subset_draws\":"<<subset_draws<<",\"LF_sigma_checks\":"<<sigma_checks
   <<",\"LF_phase_CPU_measured\":false"
   <<",\"LF_policy\":\"static whole-axis opposite targetdegree<=1 certificate; fixed degree2 object pool; k=min(4,poolsize), fewer than2 hold; uniform unordered object subset; exact uniform legal labelled pair assignments including current, theoretical maxima6/90/2520; all leaf weights strength-locked and Sigma invariant; normal Graph.set_raw hooks; no own dynamic index/cache/hook, retry, frequency or new probability; keep R0; no claim on uncertified real subgraphs\",";
 }
};
