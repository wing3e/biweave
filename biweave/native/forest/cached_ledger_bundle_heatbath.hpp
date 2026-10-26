#pragma once
#include "ledger_bundle_heatbath.hpp"
#include <cstdint>
#include <new>
#include <optional>
#include <unordered_map>
#include <utility>

struct CachedLedgerBundleHeatbath : LedgerBundleHeatbath {
 using Base=LedgerBundleHeatbath;
 struct Key {
  std::array<I,16> words{};
  bool operator==(const Key&other)const{return words==other.words;}
 };
 struct KeyHash {
  size_t operator()(const Key&key)const noexcept {
   uint64_t h=UINT64_C(1469598103934665603);
   for(I v:key.words){uint64_t x=uint64_t(v);
    for(int b=0;b<8;++b){h^=(x&UINT64_C(255));h*=UINT64_C(1099511628211);x>>=8;}}
   return size_t(h);
  }
 };
 struct Store {
  Descriptor descriptor{};
  std::vector<Plan> plans;  
  Wide total=0;U access_stamp=0;size_t payload_bytes=0;
 };
 using Cache=std::unordered_map<Key,Store,KeyHash>;
 struct Canonical {
  Key key{};Descriptor actual{};
  std::array<int,6> role_to_actual{};
  std::array<Label,6> labels{};
  Table original_actual{},original_canonical{};
 };
 struct View {
  const Descriptor*descriptor=nullptr;const Plan*plans=nullptr;
  size_t size=0;Wide total=0;
 };
 static constexpr size_t byte_cap=size_t(64)*1024*1024;

 static constexpr size_t entry_cap=byte_cap/(sizeof(Cache::value_type)+sizeof(Plan));
 Cache cache;
 bool cache_requested=false,cache_active=false;
 U cache_queries=0,cache_hits=0,cache_misses=0,cache_builds=0,cache_off_builds=0;
 U cache_evictions=0,cache_allocation_fallbacks=0,cache_checks=0,access_clock=0;
 size_t cache_bytes=0,peak_cache_bytes=0,peak_cache_entries=0;

 static void sort_owner_cells(Table&t) {
  for(int owner=0;owner<3;++owner)
   if(cell_less(t[2*owner+1],t[2*owner]))std::swap(t[2*owner],t[2*owner+1]);
 }
 static Canonical canonicalize(const std::array<Label,6>&labels,
                               const std::array<I,3>&strengths) {
  Canonical out;out.role_to_actual.fill(-1);
  out.actual=describe(labels,strengths,out.original_actual);
  auto roles=out.actual.actors;
  std::sort(roles.begin(),roles.begin()+out.actual.actor_count,
   [](const Actor&a,const Actor&b){
    if(a.degree!=b.degree)return a.degree<b.degree;
    if(a.strength!=b.strength)return a.strength<b.strength;
    return a.node<b.node;
   });
  for(int o=0;o<3;++o)out.key.words[o]=strengths[o];
  out.key.words[3]=out.actual.actor_count;
  for(int role=0;role<out.actual.actor_count;++role){
   out.role_to_actual[role]=roles[role].node;
   out.key.words[4+2*role]=roles[role].degree;
   out.key.words[5+2*role]=roles[role].strength;
  }
  auto role_of=[&](int node){
   for(int role=0;role<out.actual.actor_count;++role)
    if(out.role_to_actual[role]==node)return role;
   throw std::runtime_error("ledger cached unknown actual actor");
  };
  out.labels=labels;for(auto&label:out.labels)label.node=role_of(label.node);
  out.original_canonical=out.original_actual;
  for(auto&cell:out.original_canonical)cell.node=role_of(cell.node);
  sort_owner_cells(out.original_canonical);
  return out;
 }
 static Table draw_compiled(const View&view,Wide rank) {
  if(!view.descriptor||!view.plans||rank>=view.total)
   throw std::runtime_error("ledger cached unrank domain");
  for(size_t k=0;k<view.size;++k){const Plan&plan=view.plans[k];
   if(rank<plan.count)return unrank_plan(*view.descriptor,plan,rank);
   rank-=plan.count;
  }
  throw std::runtime_error("ledger cached global rank missing");
 }
 void clear_cache() {
  cache_evictions+=U(cache.size());Cache empty;cache.swap(empty);cache_bytes=0;
 }
 void next_stamp() {
  if(access_clock==std::numeric_limits<U>::max()){clear_cache();access_clock=0;}
  ++access_clock;
 }
 void evict_oldest() {
  if(cache.empty())throw std::runtime_error("ledger cached eviction of empty map");
  auto oldest=cache.begin();
  for(auto it=cache.begin();it!=cache.end();++it)
   if(it->second.access_stamp<oldest->second.access_stamp)oldest=it;
  if(oldest->second.payload_bytes>cache_bytes)
   throw std::runtime_error("ledger cached eviction byte audit");
  cache_bytes-=oldest->second.payload_bytes;cache.erase(oldest);++cache_evictions;
 }
 View compiled(const Canonical&current,std::optional<Fiber>&scratch) {
  ++cache_queries;
  if(cache_active){next_stamp();auto found=cache.find(current.key);
   if(found!=cache.end()){
    ++cache_hits;found->second.access_stamp=access_clock;const Store&s=found->second;
    return {&s.descriptor,s.plans.data(),s.plans.size(),s.total};
   }
   ++cache_misses;
  }else ++cache_off_builds;
  scratch.emplace(enumerate(current.labels,current.actual.strengths));++cache_builds;
  const Fiber&fiber=*scratch;
  if(!table_equal(fiber.original,current.original_canonical))
   throw std::runtime_error("ledger cached compilation original audit");
   
  supports_examined+=fiber.supports_examined;forest_supports+=fiber.forest_supports;
  cycle_supports+=fiber.cycle_supports;rank2_supports+=fiber.rank2_supports;
  const View fallback={&fiber.descriptor,fiber.plans.data(),size_t(fiber.size),fiber.total};
  if(!cache_active)return fallback;
  try {
   Store store;store.descriptor=fiber.descriptor;store.total=fiber.total;
   store.access_stamp=access_clock;
   store.plans.assign(fiber.plans.begin(),fiber.plans.begin()+size_t(fiber.size));
   if(store.plans.capacity()>(std::numeric_limits<size_t>::max()-sizeof(Cache::value_type))/sizeof(Plan))
    throw std::runtime_error("ledger cached payload size range");
   store.payload_bytes=sizeof(Cache::value_type)+store.plans.capacity()*sizeof(Plan);
   if(store.payload_bytes>byte_cap){++cache_allocation_fallbacks;return fallback;}
   while(!cache.empty()&&(cache.size()>=entry_cap||store.payload_bytes>byte_cap-cache_bytes))evict_oldest();
   auto inserted=cache.emplace(current.key,std::move(store));
   if(!inserted.second)throw std::runtime_error("ledger cached duplicate insertion");
   const Store&s=inserted.first->second;cache_bytes+=s.payload_bytes;
   peak_cache_bytes=std::max(peak_cache_bytes,cache_bytes);
   peak_cache_entries=std::max(peak_cache_entries,cache.size());
   return {&s.descriptor,s.plans.data(),s.plans.size(),s.total};
  }catch(const std::bad_alloc&){
   ++cache_allocation_fallbacks;return fallback;  
  }
 }
 void initialize(const Graph&g,bool want,bool cacheBool=false) {
  static_cast<Base&>(*this)=Base{};
  Cache empty;cache.swap(empty);
  cache_requested=cacheBool;cache_active=want&&cacheBool;
  cache_queries=cache_hits=cache_misses=cache_builds=cache_off_builds=0;
  cache_evictions=cache_allocation_fallbacks=cache_checks=access_clock=0;
  cache_bytes=peak_cache_bytes=peak_cache_entries=0;
  Base::initialize(g,want);
 }
 void check(const Graph&g) {
  if(!requested)return;
  Base::check(g);++cache_checks;
  if(cache_active!=(requested&&cache_requested)||(!cache_active&&!cache.empty())||
     cache.size()>entry_cap||cache_bytes>byte_cap)
   throw std::runtime_error("ledger cached mode/budget audit");
  size_t bytes=0;
  for(const auto&item:cache){const Key&key=item.first;const Store&s=item.second;
   if(s.plans.empty()||s.plans.size()>90||!s.total||s.access_stamp>access_clock||
      s.descriptor.actor_count<2||s.descriptor.actor_count>6||
      key.words[3]!=s.descriptor.actor_count)
    throw std::runtime_error("ledger cached store domain audit");
   for(int o=0;o<3;++o)if(key.words[o]!=s.descriptor.strengths[o])
    throw std::runtime_error("ledger cached strength key audit");
   for(int a=0;a<s.descriptor.actor_count;++a)
    if(s.descriptor.actors[a].node!=a||key.words[4+2*a]!=s.descriptor.actors[a].degree||
       key.words[5+2*a]!=s.descriptor.actors[a].strength)
     throw std::runtime_error("ledger cached role key audit");
   for(int a=s.descriptor.actor_count;a<6;++a)
    if(key.words[4+2*a]||key.words[5+2*a])throw std::runtime_error("ledger cached key padding");
   Wide total=0;for(const Plan&plan:s.plans){
    if(!plan.count||total>Wide(-1)-plan.count)throw std::runtime_error("ledger cached count range");
    total+=plan.count;
   }
   if(total!=s.total||s.payload_bytes!=sizeof(Cache::value_type)+s.plans.capacity()*sizeof(Plan)||
      s.payload_bytes>byte_cap-bytes)
    throw std::runtime_error("ledger cached payload/count audit");
   bytes+=s.payload_bytes;
  }
  if(bytes!=cache_bytes||cache_queries!=cache_hits+cache_misses+cache_off_builds||
     cache_builds!=cache_misses+cache_off_builds)
   throw std::runtime_error("ledger cached aggregate audit");
 }
 bool step_axis(Engine&e,Graph&g,int axis) {
  if(axis<0||axis>1||!requested||!axis_active[axis]||g.D)throw std::runtime_error("ledger invalid direction");
  ++axis_calls[axis];++e.stat.work;
  const auto&pool=objects[axis];const U n=U(pool.size());std::array<U,3>selected{};int used=0;
  for(U j=n-3;j<n;++j){U k=e.rng.below(j+1);bool duplicate=false;
   for(int t=0;t<used;++t)duplicate|=selected[t]==k;
   if(duplicate)k=j;selected[used++]=k;}
  std::array<int,3>nodes={pool[size_t(selected[0])],pool[size_t(selected[1])],pool[size_t(selected[2])]};
  std::sort(nodes.begin(),nodes.end());++selected_triples;
  std::array<Label,6>labels{};std::array<I,3>strengths{};int next=0;
  for(int owner=0;owner<3;++owner) {
   const int vertex=axis?g.nr+nodes[owner]:nodes[owner];
   if(g.target_degree[vertex]!=2||g.degree[vertex]!=2||g.adj[vertex].size()!=2)
    throw std::runtime_error("ledger selected object degree");
   strengths[owner]=g.target_strength[vertex];
   for(int id:g.adj[vertex]){const auto edge=g.edges.at(size_t(id));
    if(edge.w<=0||(axis?edge.c:edge.r)!=nodes[owner])throw std::runtime_error("ledger adjacency record");
    labels[size_t(next++)]={axis?edge.r:edge.c,owner,edge.w};}
  }
  if(next!=6)throw std::runtime_error("ledger six-record audit");
  const Canonical current=canonicalize(labels,strengths);
  std::optional<Fiber> scratch;  
  const View view=compiled(current,scratch);const auto&d=current.actual;
  repeated_opposite_triples+=d.actor_count<6;fast_leaf_calls+=d.all_actor_degree_one;
  max_fiber_count=std::max(max_fiber_count,view.total);
  if(view.total==1){++singleton_holds;++selected_original;return false;}
  const Table canonical_chosen=draw_compiled(view,below(e,view.total));++rank_draws;
  Table chosen=canonical_chosen;
  for(auto&cell:chosen){
   if(cell.node<0||cell.node>=d.actor_count)throw std::runtime_error("ledger cached role range");
   cell.node=current.role_to_actual[size_t(cell.node)];
  }
  sort_owner_cells(chosen);
  const bool unchanged=table_equal(chosen,current.original_actual);
  if(unchanged!=table_equal(canonical_chosen,current.original_canonical))
   throw std::runtime_error("ledger cached fresh-original mapping audit");
  if(unchanged){++selected_original;return false;}
  auto value=[&](int owner,int node){return axis?g.value(node,nodes[owner]):g.value(nodes[owner],node);};
  auto put=[&](int owner,const Cell&cell,I weight){
   if(axis)g.set_raw(cell.node,nodes[owner],weight);else g.set_raw(nodes[owner],cell.node,weight);++cell_writes;};
  for(int a=0;a<d.actor_count;++a) {
   const int v=axis?d.actors[a].node:g.nr+d.actors[a].node;
   if(g.degree[v]!=g.target_degree[v]||g.adj[v].size()!=U(g.degree[v])||d.actors[a].strength>g.target_strength[v])
    throw std::runtime_error("ledger actor precommit margin");
   for(int owner=0;owner<3;++owner){I expected=0;
    for(int t=2*owner;t<2*owner+2;++t)if(current.original_actual[t].node==d.actors[a].node)expected=current.original_actual[t].weight;
    if(value(owner,d.actors[a].node)!=expected)throw std::runtime_error("ledger complete-table collision");}
  }
  const U old_edges=U(g.edges.size());

  for(int owner=0;owner<3;++owner)for(int t=2*owner;t<2*owner+2;++t)put(owner,current.original_actual[t],0);
  for(int owner=0;owner<3;++owner)for(int t=2*owner;t<2*owner+2;++t)put(owner,chosen[t],chosen[t].weight);
  if(g.D||U(g.edges.size())!=old_edges)throw std::runtime_error("ledger commit did not close");
  for(int owner=0;owner<3;++owner) {
   const int v=axis?g.nr+nodes[owner]:nodes[owner];S128 sum=0;
   for(int id:g.adj[v])sum+=S128(g.edges.at(size_t(id)).w);
   if(g.degree[v]!=2||g.adj[v].size()!=2||sum!=S128(strengths[owner]))
    throw std::runtime_error("ledger final object margin");
  }
  for(int a=0;a<d.actor_count;++a) {
   const int v=axis?d.actors[a].node:g.nr+d.actors[a].node;S128 full=0,local=0;int degree=0;
   for(int id:g.adj[v])full+=S128(g.edges.at(size_t(id)).w);
   for(int owner=0;owner<3;++owner){const I w=value(owner,d.actors[a].node);local+=S128(w);degree+=w>0;}
   if(g.degree[v]!=g.target_degree[v]||full!=S128(g.target_strength[v])||
      degree!=d.actors[a].degree||local!=S128(d.actors[a].strength))
    throw std::runtime_error("ledger final actor margin");
  }
  ++changes;++axis_changes[axis];++e.stat.changed_outer;return true;
 }
 bool compose_uniform_block(Engine&e,Graph&g) {
  if(!requested)throw std::runtime_error("unrequested ledger composition");
  ++compose_calls;if(!active){++no_static_candidates;return false;}
  ++uniform_block_calls;

  const Wide rank=below(e,total_groups);const int axis=rank<axis_groups[0]?0:1;
  return step_axis(e,g,axis);
 }
 bool compose(Engine&e,Graph&g) {return compose_uniform_block(e,g);}
 bool compose_both_axes(Engine&e,Graph&g) {
  if(!requested)throw std::runtime_error("unrequested ledger dual composition");
  ++compose_calls;if(!active){++no_static_candidates;return false;}
  ++both_axis_calls;
  bool changed=false;
  if(axis_active[1])changed=step_axis(e,g,1)||changed;
  if(axis_active[0])changed=step_axis(e,g,0)||changed;
  return changed;
 }
 void metadata(std::ostream&f)const {
  Base::metadata(f);
  f<<"\"LC_requested\":"<<(cache_requested?"true":"false")
   <<",\"LC_active\":"<<(cache_active?"true":"false")
   <<",\"LC_queries\":"<<cache_queries<<",\"LC_hits\":"<<cache_hits
   <<",\"LC_misses\":"<<cache_misses<<",\"LC_builds\":"<<cache_builds
   <<",\"LC_off_builds\":"<<cache_off_builds<<",\"LC_evictions\":"<<cache_evictions
   <<",\"LC_allocation_fallbacks\":"<<cache_allocation_fallbacks
   <<",\"LC_checks\":"<<cache_checks<<",\"LC_entries\":"<<cache.size()
   <<",\"LC_peak_entries\":"<<peak_cache_entries<<",\"LC_entry_cap\":"<<entry_cap
   <<",\"LC_payload_bytes\":"<<cache_bytes<<",\"LC_peak_payload_bytes\":"<<peak_cache_bytes
   <<",\"LC_payload_byte_cap\":"<<byte_cap<<",\"LC_bucket_count\":"<<cache.bucket_count()
   <<",\"LC_bucket_bytes\":"<<(Wide(cache.bucket_count())*sizeof(void*)<=Wide(std::numeric_limits<size_t>::max())?
      std::to_string(cache.bucket_count()*sizeof(void*)):decimal(Wide(cache.bucket_count())*sizeof(void*)))
   <<",\"LC_phase_CPU_measured\":false"
   <<",\"LC_policy\":\"same canonical role path with cache off/on; exact ordered object-strength and actor degree/strength key; valid-plan const references and fresh current original; managed payload bound excludes hash buckets and allocator overhead; LRU stamp without clock or RNG; LB support counters only actual compilation\",";
 }
};
