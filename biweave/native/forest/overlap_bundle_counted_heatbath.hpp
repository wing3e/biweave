#pragma once
#include <algorithm>
#include <array>
#include <cstddef>
#include <ostream>
#include <stdexcept>
#include <vector>

struct OverlapBundleHeatbath {
 struct Label { int node=-1,old_owner=-1; I weight=0; };
 struct Cell { int node=-1; I weight=0; };
 using Table=std::array<Cell,6>;  
 using Partition=std::array<int,6>;
 struct Fiber {
  std::array<Table,90> tables{};
  Table original{};

  U size=0,raw_size=0,preimage_multiplicity=1,raw_current_count=0;
  U pair_sum_builds=0,pair_checks=0,mask_checks=0;
 };
 bool requested=false,active=false;
 std::array<bool,2> axis_active={false,false};
 std::array<std::vector<int>,2> objects;
 int rows=0,columns=0;
 U compose_calls=0,no_static_candidates=0,changes=0,index_checks=0;
 std::array<U,2> axis_calls={0,0},axis_changes={0,0};
 U selected_triples=0,repeated_opposite_triples=0;
 U partitions_examined=0,raw_legal_partitions=0,legal_tables=0;
 U duplicate_output_preimages=0,max_legal_tables=0,singleton_holds=0;
 U candidate_pair_checks=0,mask_disjoint_checks=0,pair_sum_builds=0;
 U rank_draws=0,selected_original=0,cell_writes=0,changed_cells=0;

 static bool cell_less(const Cell&a,const Cell&b) {
  return a.node!=b.node?a.node<b.node:a.weight<b.weight;
 }
 static bool table_less(const Table&a,const Table&b) {
  for(int i=0;i<6;++i) {
   if(cell_less(a[i],b[i]))return true;
   if(cell_less(b[i],a[i]))return false;
  }
  return false;
 }
 static bool table_equal(const Table&a,const Table&b) {
  for(int i=0;i<6;++i)
   if(a[i].node!=b[i].node||a[i].weight!=b[i].weight)return false;
  return true;
 }
 static Table make_table(const std::array<Label,6>&labels,
                         const Partition&assignment) {
  Table out{};std::array<int,3> count={0,0,0};
  for(int i=0;i<6;++i) {
   const int owner=assignment[i];
   if(owner<0||owner>=3||count[owner]>=2)
    throw std::runtime_error("overlap bundle assignment cardinality");
   out[2*owner+count[owner]++]={labels[i].node,labels[i].weight};
  }
  for(int owner=0;owner<3;++owner) {
   if(count[owner]!=2||out[2*owner].node==out[2*owner+1].node)
    throw std::runtime_error("overlap bundle repeated node inside object");
   if(cell_less(out[2*owner+1],out[2*owner]))
    std::swap(out[2*owner],out[2*owner+1]);
  }
  return out;
 }

 static Fiber enumerate(const std::array<Label,6>&labels,
                        const std::array<I,3>&strengths) {
  Fiber out;Partition original{};std::array<S128,3> old_sums{};
  for(int i=0;i<6;++i) {
   if(labels[i].node<0||labels[i].weight<=0||labels[i].old_owner<0||labels[i].old_owner>=3)
    throw std::runtime_error("overlap bundle invalid positive record");
   original[i]=labels[i].old_owner;
   old_sums[original[i]]+=S128(labels[i].weight);
  }
  out.original=make_table(labels,original);
  for(int i=0;i<6;++i) {
   bool seen=false;
   for(int j=0;j<i;++j)
    seen|=labels[i].node==labels[j].node&&labels[i].weight==labels[j].weight;
   if(seen)continue;
   U multiplicity=0;
   for(int j=0;j<6;++j)
    multiplicity+=labels[i].node==labels[j].node&&labels[i].weight==labels[j].weight;
   if(multiplicity<1||multiplicity>3)
    throw std::runtime_error("counted overlap bundle type multiplicity outside simple three-object scope");
   for(U k=2;k<=multiplicity;++k)out.preimage_multiplicity*=k;
  }
  for(int owner=0;owner<3;++owner)
   if(old_sums[owner]!=S128(strengths[owner]))
    throw std::runtime_error("overlap bundle input object strength");
  struct Pair {int a=0,b=0;unsigned mask=0;S128 sum=0;bool distinct=false;};
  std::array<Pair,15>pairs{};std::array<int,64>by_mask{};by_mask.fill(-1);
  int n=0;
  for(int a=0;a<6;++a)for(int b=a+1;b<6;++b) {
   const unsigned mask=(1U<<a)|(1U<<b);
   pairs[n]={a,b,mask,S128(labels[a].weight)+labels[b].weight,labels[a].node!=labels[b].node};
   by_mask[mask]=n++;++out.pair_sum_builds;
  }
  if(n!=15)throw std::runtime_error("overlap bundle fifteen-pair audit");
  for(const Pair&p:pairs) {
   ++out.pair_checks;
   if(!p.distinct||p.sum!=S128(strengths[0]))continue;
   for(const Pair&q:pairs) {
    ++out.mask_checks;if(p.mask&q.mask)continue;
    ++out.pair_checks;
    if(!q.distinct||q.sum!=S128(strengths[1]))continue;
    const unsigned remaining=63U^(p.mask|q.mask);
    const int ri=by_mask[remaining];
    if(ri<0)throw std::runtime_error("overlap bundle forced pair mask");
    const Pair&r=pairs[ri];++out.pair_checks;
    if(!r.distinct||r.sum!=S128(strengths[2]))continue;
    Partition assignment{};assignment.fill(2);
    assignment[p.a]=assignment[p.b]=0;assignment[q.a]=assignment[q.b]=1;
    if(out.raw_size>=90)throw std::runtime_error("overlap bundle assignment bound");
    out.tables[size_t(out.raw_size++)]=make_table(labels,assignment);
   }
  }
  if(!out.raw_size||out.raw_size>90||!out.preimage_multiplicity||
     out.raw_size%out.preimage_multiplicity)
   throw std::runtime_error("counted overlap bundle raw fiber multiplicity audit");
  out.size=out.raw_size/out.preimage_multiplicity;
  for(U i=0;i<out.raw_size;++i)
   out.raw_current_count+=table_equal(out.tables[size_t(i)],out.original);
  if(!out.size||out.raw_current_count!=out.preimage_multiplicity)
   throw std::runtime_error("counted overlap bundle current-table preimage audit");
  return out;
 }
 static Table unrank(const Fiber&fiber,U raw_rank) {
  if(raw_rank>=fiber.raw_size)
   throw std::runtime_error("counted overlap bundle raw rank outside fiber");
  return fiber.tables[size_t(raw_rank)];
 }

 void initialize(const Graph&g,bool want) {
  requested=want;if(!want)return;rows=g.nr;columns=g.nc;
  if(g.D)throw std::runtime_error("overlap bundle initialization outside exact margins");
  for(int axis=0;axis<2;++axis) {
   const int n=axis?g.nc:g.nr,opposite=axis?g.nr:g.nc,offset=axis?g.nr:0;
    
   if(opposite<2)continue;
   U count=0;for(int v=0;v<n;++v)count+=g.target_degree[offset+v]==2;
   if(count<3)continue;
   auto&pool=objects[axis];pool.reserve(size_t(count));
   for(int v=0;v<n;++v)if(g.target_degree[offset+v]==2)pool.push_back(v);
   axis_active[axis]=true;active=true;
  }
 }
 void check(const Graph&g) {
  if(!requested)return;++index_checks;
  if(g.nr!=rows||g.nc!=columns||g.D)
   throw std::runtime_error("overlap bundle graph/degree audit");
  for(int axis=0;axis<2;++axis) {
   const int n=axis?g.nc:g.nr,opposite=axis?g.nr:g.nc,offset=axis?g.nr:0;
   U count=0;for(int v=0;v<n;++v)count+=g.target_degree[offset+v]==2;
   const bool expected=opposite>=2&&count>=3;
   if(axis_active[axis]!=expected||(expected&&objects[axis].size()!=count)||
      (!expected&&!objects[axis].empty()))
    throw std::runtime_error("overlap bundle static target pool cardinality");
   if(!expected)continue;
   U k=0;for(int v=0;v<n;++v)if(g.target_degree[offset+v]==2) {
    if(objects[axis].at(size_t(k++))!=v||g.degree[offset+v]!=2||g.adj[offset+v].size()!=2)
     throw std::runtime_error("overlap bundle static target pool labels");
   }
  }
  if(active!=(axis_active[0]||axis_active[1]))
   throw std::runtime_error("overlap bundle active audit");
 }
 bool step_axis(Engine&e,Graph&g,int axis) {
  if(axis<0||axis>1||!requested||!axis_active[axis]||g.D)
   throw std::runtime_error("overlap bundle invalid direction");
  ++axis_calls[axis];++e.stat.work;
  const auto&pool=objects[axis];const U n=U(pool.size());
  std::array<U,3>selected{};int used=0;
   
  for(U j=n-3;j<n;++j) {
   U k=e.rng.below(j+1);bool duplicate=false;
   for(int t=0;t<used;++t)duplicate|=selected[t]==k;
   if(duplicate)k=j;selected[used++]=k;
  }
  std::array<int,3>nodes={pool[size_t(selected[0])],pool[size_t(selected[1])],pool[size_t(selected[2])]};
  std::sort(nodes.begin(),nodes.end());++selected_triples;
  std::array<Label,6>labels{};std::array<I,3>strengths{};int next=0;
  for(int owner=0;owner<3;++owner) {
   const int vertex=axis?g.nr+nodes[owner]:nodes[owner];
   if(g.target_degree[vertex]!=2||g.degree[vertex]!=2||g.adj[vertex].size()!=2)
    throw std::runtime_error("overlap bundle selected object degree");
   strengths[owner]=g.target_strength[vertex];
   for(int id:g.adj[vertex]) {
    const auto edge=g.edges.at(size_t(id));
    if(edge.w<=0||(axis?edge.c:edge.r)!=nodes[owner])
     throw std::runtime_error("overlap bundle adjacency record");
    labels[size_t(next++)]={axis?edge.r:edge.c,owner,edge.w};
   }
  }
  if(next!=6)throw std::runtime_error("overlap bundle six-record audit");
  bool repeated=false;
  for(int i=0;i<6;++i)for(int j=0;j<i;++j)repeated|=labels[i].node==labels[j].node;
  repeated_opposite_triples+=repeated;
  const Fiber fiber=enumerate(labels,strengths);
  partitions_examined+=90;raw_legal_partitions+=fiber.raw_size;
  legal_tables+=fiber.size;duplicate_output_preimages+=fiber.raw_size-fiber.size;
  max_legal_tables=std::max(max_legal_tables,fiber.size);
  pair_sum_builds+=fiber.pair_sum_builds;candidate_pair_checks+=fiber.pair_checks;
  mask_disjoint_checks+=fiber.mask_checks;
  if(fiber.size==1){++singleton_holds;++selected_original;return false;}
   
  const Table chosen=unrank(fiber,e.rng.below(fiber.raw_size));++rank_draws;
  if(table_equal(chosen,fiber.original)){++selected_original;return false;}
  auto value=[&](int owner,int node) {return axis?g.value(node,nodes[owner]):g.value(nodes[owner],node);};
  auto put=[&](int owner,const Cell&cell,I w) {
   if(axis)g.set_raw(cell.node,nodes[owner],w);else g.set_raw(nodes[owner],cell.node,w);
   ++cell_writes;
  };
  std::array<int,6>opposite_nodes{};std::array<int,6>opposite_degree{};int unique=0;
  for(const Label&label:labels) {
   bool seen=false;for(int i=0;i<unique;++i)seen|=opposite_nodes[i]==label.node;
   if(!seen)opposite_nodes[unique++]=label.node;
  }
  for(int i=0;i<unique;++i) {
   const int v=axis?opposite_nodes[i]:g.nr+opposite_nodes[i];
   opposite_degree[i]=g.degree[v];
   if(g.degree[v]!=g.target_degree[v]||g.adj[v].size()!=U(g.degree[v]))
    throw std::runtime_error("overlap bundle opposite precommit degree");
   for(int owner=0;owner<3;++owner) {
    I expected=0;
    for(int t=2*owner;t<2*owner+2;++t)
     if(fiber.original[t].node==opposite_nodes[i])expected=fiber.original[t].weight;
    if(value(owner,opposite_nodes[i])!=expected)
     throw std::runtime_error("overlap bundle precommit complete-table collision");
   }
  }
  const U old_edges=U(g.edges.size());

  for(int owner=0;owner<3;++owner)
   for(int t=2*owner;t<2*owner+2;++t)put(owner,fiber.original[t],0);
  for(int owner=0;owner<3;++owner)
   for(int t=2*owner;t<2*owner+2;++t)put(owner,chosen[t],chosen[t].weight);
  if(g.D||U(g.edges.size())!=old_edges)
   throw std::runtime_error("overlap bundle commit did not close");
  for(int owner=0;owner<3;++owner) {
   const int vertex=axis?g.nr+nodes[owner]:nodes[owner];
   if(g.degree[vertex]!=2||g.adj[vertex].size()!=2)
    throw std::runtime_error("overlap bundle final object degree");
   S128 sum=0;for(int id:g.adj[vertex])sum+=S128(g.edges.at(size_t(id)).w);
   if(sum!=S128(strengths[owner]))
    throw std::runtime_error("overlap bundle final object strength");
  }
  for(int i=0;i<unique;++i) {
   const int v=axis?opposite_nodes[i]:g.nr+opposite_nodes[i];
   if(g.degree[v]!=opposite_degree[i])
    throw std::runtime_error("overlap bundle final opposite degree");
   S128 before=0,after=0;
   for(int owner=0;owner<3;++owner) {
    I old_w=0,new_w=0;
    for(int t=2*owner;t<2*owner+2;++t) {
     if(fiber.original[t].node==opposite_nodes[i])old_w=fiber.original[t].weight;
     if(chosen[t].node==opposite_nodes[i])new_w=chosen[t].weight;
    }
    if(value(owner,opposite_nodes[i])!=new_w)
     throw std::runtime_error("overlap bundle final complete-table audit");
    before+=S128(old_w);after+=S128(new_w);changed_cells+=old_w!=new_w;
   }
   if(before!=after)throw std::runtime_error("overlap bundle final opposite local strength");
  }
  ++changes;++axis_changes[axis];++e.stat.changed_outer;return true;
 }
 bool compose(Engine&e,Graph&g) {
  if(!requested)throw std::runtime_error("unrequested overlap bundle compose");
  ++compose_calls;if(!active){++no_static_candidates;return false;}
  bool changed=false;
   
  if(axis_active[1])changed=step_axis(e,g,1)||changed;
  if(axis_active[0])changed=step_axis(e,g,0)||changed;
  return changed;
 }
 void metadata(std::ostream&f)const {
  f<<"\"OB_requested\":"<<(requested?"true":"false")
   <<",\"OB_active\":"<<(active?"true":"false")
   <<",\"OB_row_axis_active\":"<<(axis_active[0]?"true":"false")
   <<",\"OB_column_axis_active\":"<<(axis_active[1]?"true":"false")
   <<",\"OB_row_object_pool\":"<<objects[0].size()<<",\"OB_column_object_pool\":"<<objects[1].size()
   <<",\"OB_compose_calls\":"<<compose_calls<<",\"OB_no_static_candidates\":"<<no_static_candidates
   <<",\"OB_row_axis_calls\":"<<axis_calls[0]<<",\"OB_column_axis_calls\":"<<axis_calls[1]
   <<",\"OB_changes\":"<<changes<<",\"OB_row_axis_changes\":"<<axis_changes[0]
   <<",\"OB_column_axis_changes\":"<<axis_changes[1]<<",\"OB_selected_triples\":"<<selected_triples
   <<",\"OB_repeated_opposite_triples\":"<<repeated_opposite_triples
   <<",\"OB_partitions_examined\":"<<partitions_examined
   <<",\"OB_raw_legal_partitions\":"<<raw_legal_partitions<<",\"OB_legal_tables\":"<<legal_tables
   <<",\"OB_duplicate_output_preimages\":"<<duplicate_output_preimages
   <<",\"OB_max_legal_tables\":"<<max_legal_tables<<",\"OB_singleton_holds\":"<<singleton_holds
   <<",\"OB_rank_draws\":"<<rank_draws<<",\"OB_selected_original\":"<<selected_original
   <<",\"OB_candidate_pair_checks\":"<<candidate_pair_checks
   <<",\"OB_mask_disjoint_checks\":"<<mask_disjoint_checks<<",\"OB_pair_sum_builds\":"<<pair_sum_builds
   <<",\"OB_cell_writes\":"<<cell_writes<<",\"OB_changed_cells\":"<<changed_cells
   <<",\"OB_index_checks\":"<<index_checks
   <<",\"OB_policy\":\"fixed target-degree-two uniform three-object subset; repeated opposite nodes allowed; each object two distinct users; positive user-weight multiset preserved; <=90 legal raw record partitions, each complete matrix has product multiplicity-factorial preimages; uniform raw-rank heatbath; no candidate sort or dedup; OB_legal_tables counts distinct matrices analytically; include original; column then row; no retries; remove all six old cells before six insertions\",";
 }
};
