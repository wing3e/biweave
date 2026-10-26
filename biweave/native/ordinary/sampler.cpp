#include "convergence_distance_cpu.hpp"

#include "journaled_lowrank4_kernel.hpp"
#include <gmpxx.h>
#include <functional>
#include <unordered_set>
#include <time.h>
#include "rankable_four_margin.hpp"
#include "fixed_support_suffix_dp.hpp"
#include "global_equal_weight_switch.hpp"
#include "unlabeled_structure_trace.hpp"
#include "global_degree_work_batch.hpp"
#include "dynamic_support_bitset_scene.hpp"
static bool fixed_support_dp=false;
static bool minimal_anchor_window=false;
static bool two_weight_complement=false;
static bool two_weight_scaled_counts=false;
static bool two_weight_slack_certificate=false;
static bool pair_specific_complement=false,wide_complement_proposal=false;
static bool budget_compatible_complement=false;
static bool budget_pair_filter=true;
static std::string two_weight_profile_update="heatbath";
static bool pair_conditional_profile_mode(){return two_weight_profile_update=="pair_conditional_gibbs"||two_weight_profile_update=="pair_conditional_profile_hold";}

static bool node_weighted_orientation=false;
static int choose_orientation(RNG&rng,const Graph&g){
 if(!node_weighted_orientation)return int(rng.below(2));
 const U total=U(g.nr)+U(g.nc);
 if(!total)return int(rng.below(2));
 return rng.below(total)<U(g.nr)?0:1;
}
static double process_cpu(){timespec ts{};if(clock_gettime(CLOCK_PROCESS_CPUTIME_ID,&ts))throw std::runtime_error("cpu clock");return double(ts.tv_sec)+double(ts.tv_nsec)/1e9;}
static mpz_class zbig(const Big&b){mpz_class z;if(!b.a.empty())mpz_import(z.get_mpz_t(),b.a.size(),-1,sizeof(uint32_t),0,0,b.a.data());return z;}
static Big bigz(const mpz_class&z){if(z<0)throw std::runtime_error("negative GMP integer");Big b;if(z==0)return b;b.a.resize((mpz_sizeinbase(z.get_mpz_t(),2)+31)/32);size_t n=0;mpz_export(b.a.data(),&n,-1,sizeof(uint32_t),0,0,z.get_mpz_t());b.a.resize(n);b.trim();return b;}
#include "root_excess_triple_guide.hpp"
#include "strict_star_full_fiber.hpp"
#include "unified_private_pair.hpp"
static mpq_class rational(mpz_class a,mpz_class b){if(b<=0)throw std::runtime_error("nonpositive rational denominator");mpq_class q(a,b);q.canonicalize();return q;}
static mpz_class choose_exact(U n,U k){if(k>n)return 0;k=std::min(k,n-k);mpz_class z=1;for(U j=1;j<=k;++j){z*=n-k+j;z/=j;}return z;}
static bool exact_accept(RNG&rng,const mpq_class&q){if(q<=0)return false;if(q>=1)return true;return rng.below_big(bigz(q.get_den()))<bigz(q.get_num());}
#include "soft_rectangle_gibbs.hpp"
#include "metropolized_soft_rectangle.hpp"
#include "metropolized_soft_rectangle_fast.hpp"
#include "guided_soft_rectangle.hpp"
#include "guided_heatbath_rectangle.hpp"
#include "guided_harmonic_rectangle.hpp"
#include "endpoint_soft_rectangle.hpp"
#include "soft_defect_endpoint.hpp"

struct WholeGraphSmallIID {
 std::unique_ptr<rankable_four_margin::Arena> arena;
 std::unique_ptr<rankable_four_margin::Compiler> compiler;
 bool requested=false,attempted=false,active=false,guard_failed=false;
 std::string guard_reason="not_requested",exact_count="unknown";
 U memo_states=0,memo_hits=0,positive_branches=0,max_node_branches=0,work=0,row_candidates=0,row_upper_total=0,arena_peak_bytes=0;
 U raw_row_upper_score=0,raw_column_upper_score=0;int dp_rows=0,dp_cols=0;bool transposed=false;
 U calls=0,changes=0,rank_words=0,rank_rejections=0,edge_writes_attempted=0,changed_cell_writes=0;
 double build_cpu_seconds=0,draw_cpu_seconds=0;
 void snapshot(){if(arena)arena_peak_bytes=arena->peak;if(!compiler)return;memo_states=compiler->memo.size();memo_hits=compiler->memo_hits;positive_branches=compiler->positive_branches;max_node_branches=compiler->max_node_branches;work=compiler->work;row_candidates=compiler->row_candidates;row_upper_total=compiler->row_upper_total;raw_row_upper_score=compiler->raw_row_upper_score;raw_column_upper_score=compiler->raw_column_upper_score;dp_rows=compiler->n;dp_cols=compiler->m;transposed=compiler->transposed;}
 void initialize(const Graph&g,bool want,bool old_direct){
  requested=want;if(!want)return;if(old_direct){guard_reason="existing_whole_direct_has_priority";return;}
  if(U(g.nr)*U(g.nc)>rankable_four_margin::CELLS){guard_reason="more_than_20_cells";guard_failed=true;return;}
  attempted=true;const double begin=process_cpu();
  try{arena=std::make_unique<rankable_four_margin::Arena>();compiler=std::make_unique<rankable_four_margin::Compiler>(*arena);compiler->n=compiler->original_n=g.nr;compiler->m=compiler->original_m=g.nc;
   for(int i=0;i<g.nr;++i){if(g.target_degree[i]<0||g.target_strength[i]<0)throw std::runtime_error("invalid graph margins for whole compiler");compiler->rd[i]=g.target_degree[i];compiler->rs[i]=g.target_strength[i];}
   for(int j=0;j<g.nc;++j){if(g.target_degree[g.nr+j]<0||g.target_strength[g.nr+j]<0)throw std::runtime_error("invalid graph margins for whole compiler");compiler->cd[j]=g.target_degree[g.nr+j];compiler->cs[j]=g.target_strength[g.nr+j];}
   compiler->compile();snapshot();exact_count=compiler->total.str();active=true;guard_reason="complete_four_margin_fiber_certified";
  }catch(const rankable_four_margin::ResourceFailure&ex){snapshot();guard_failed=true;guard_reason=ex.what();compiler.reset();arena.reset();}
  build_cpu_seconds=process_cpu()-begin;
 }
 rankable_four_margin::Big draw_rank(RNG&rng){using rankable_four_margin::Big;const Big&bound=compiler->total;if(bound<=1)return Big(0);unsigned bits=(bound-Big(1)).bits();for(;;){Big value;value.used=(bits+63)/64;for(unsigned i=0;i<value.used;++i){value.a[i]=rng.gen();++rank_words;}unsigned part=bits%64;if(part)value.a[value.used-1]&=(U(1)<<part)-1;value.trim();if(value<bound)return value;++rank_rejections;}}
 bool commit(Engine&e,Graph&g,const std::array<uint64_t,rankable_four_margin::CELLS>&x){
  if(!active||g.nr!=compiler->original_n||g.nc!=compiler->original_m)throw std::runtime_error("whole compiler commit outside certified shape");bool changed=false;const U old_updates=e.stat.cell_updates;
  for(int i=0;i<g.nr;++i)for(int j=0;j<g.nc;++j){U w=x[i*g.nc+j];if(w>U(std::numeric_limits<I>::max()))throw std::runtime_error("whole compiler weight exceeds graph integer");changed|=g.value(i,j)!=I(w);g.set_raw(i,j,I(w));++edge_writes_attempted;}
  changed_cell_writes+=e.stat.cell_updates-old_updates;if(changed){++changes;++e.stat.changed_outer;}return changed;
 }
 bool draw(Engine&e,Graph&g){if(!active)throw std::runtime_error("uncertified whole compiler draw");++calls;++e.stat.work;return commit(e,g,compiler->unrank(draw_rank(e.rng)));}
};

static mpq_class owner_self_probability(const FastCountedBlock&cb,bool heatbath){
 const mpz_class S=zbig(cb.total_big());if(heatbath)return rational(1,S);
 const U current=cb.current_owner_mask();auto owners=cb.support_counts();mpz_class w=0;
 for(const auto&v:owners)if(v.first==current){w=zbig(v.second);break;}
 if(w<=0)throw std::runtime_error("current owner missing in self count");
 if(S==w)return rational(1,w);
 mpq_class answer=0;std::map<mpz_class,U> multiplicities;
 for(const auto&item:owners){if(item.first==current)continue;const mpz_class v=zbig(item.second);if(v<w)++multiplicities[v];}
 for(const auto&item:multiplicities){const mpz_class&v=item.first;answer+=rational(v*(w-v)*item.second,w*(S-w)*(S-v));}
 if(answer<0||answer>1)throw std::runtime_error("invalid exact A self probability");return answer;
}

static bool fixed_margin_A_identity(const Graph&g){
 for(int side=0;side<2;++side){const int n=side?g.nc:g.nr,off=side?g.nr:0,other=side?g.nr:g.nc,other_off=side?0:g.nr;
  bool eligible=true;std::set<I>leaf_weights,object_strengths;int leaves=0;
  for(int v=0;v<n;++v){const int d=g.target_degree[off+v];if(!d)continue;++leaves;
   if(d!=1||!leaf_weights.insert(g.target_strength[off+v]).second){eligible=false;break;}}
  if(!eligible||!leaves)continue;
  for(int v=0;v<other;++v){const int d=g.target_degree[other_off+v];if(!d)continue;
   if(d>2||!object_strengths.insert(g.target_strength[other_off+v]).second){eligible=false;break;}}
  if(eligible)return true;
 }
 return false;
}

struct LeafPairMatchingProblem {
 std::vector<int>leaves,objects;std::vector<I>weights,strengths;
 std::vector<std::vector<std::pair<int,int>>>pairs;std::vector<U>memo;
 U total=0,visited_masks=0;uint32_t full=0;
 LeafPairMatchingProblem(std::vector<int>l,std::vector<int>o,std::vector<I>w,std::vector<I>s):leaves(std::move(l)),objects(std::move(o)),weights(std::move(w)),strengths(std::move(s)){
  const int n=int(leaves.size()),r=int(objects.size());if(r<1||r>10||n!=2*r)throw std::runtime_error("matching compiler requires at most10degree2 objects");
  full=(uint32_t(1)<<n)-1;memo.assign(size_t(full)+1,std::numeric_limits<U>::max());pairs.resize(r);
  for(int k=0;k<r;++k)for(int a=0;a<n;++a)for(int b=a+1;b<n;++b)if(S128(weights[a])+weights[b]==strengths[k])pairs[k].push_back({a,b});
  total=count(0);if(!total)throw std::runtime_error("current matching missing from exact compiler");
 }
 U count(uint32_t mask){U&stored=memo[mask];if(stored!=std::numeric_limits<U>::max())return stored;++visited_masks;if(mask==full)return stored=1;
  const int k=__builtin_popcount(mask)/2;U answer=0;
  for(auto [a,b]:pairs[k]){const uint32_t bits=(uint32_t(1)<<a)|(uint32_t(1)<<b);if(mask&bits)continue;const U suffix=count(mask|bits);
   if(answer>std::numeric_limits<U>::max()-suffix)throw std::runtime_error("matching exact count overflow");answer+=suffix;}
  return stored=answer;
 }
 std::vector<int> unrank(U rank){if(rank>=total)throw std::runtime_error("matching rank outside fiber");std::vector<int>owners(leaves.size(),-1);uint32_t mask=0;
  for(int k=0;k<int(objects.size());++k){bool found=false;for(auto [a,b]:pairs[k]){const uint32_t bits=(uint32_t(1)<<a)|(uint32_t(1)<<b);if(mask&bits)continue;const U suffix=count(mask|bits);
    if(rank>=suffix){rank-=suffix;continue;}owners[a]=owners[b]=k;mask|=bits;found=true;break;}
   if(!found)throw std::runtime_error("matching unrank failed");}
  if(mask!=full||rank)throw std::runtime_error("matching unrank remainder");return owners;
 }
};

struct StaticXorMatchingProblem {
 struct Literal {int object,choice;};
 std::vector<int>leaves,objects;std::vector<I>weights,strengths;
 std::vector<std::vector<std::pair<int,int>>>pairs;
 std::vector<int>parent,rank,parity,object_group,object_parity;
 bool eligible=false,contradiction=false;std::string guard_reason="not_started";
 U pair_checks=0,candidate_pairs=0,max_leaf_occurrence=0,constraint_equations=0,unions=0,free_components=0;
 U calls=0,changes=0,free_bit_draws=0,moved_leaves=0,edge_writes=0;
 mpz_class exact_count=0;
 StaticXorMatchingProblem(std::vector<int>l,std::vector<int>o,std::vector<I>w,std::vector<I>s):leaves(std::move(l)),objects(std::move(o)),weights(std::move(w)),strengths(std::move(s)){
  const int L=leaves.size(),O=objects.size();if(!O||L!=2*O||weights.size()!=leaves.size()||strengths.size()!=objects.size()){guard_reason="invalid_sizes";return;}
  std::unordered_map<I,int>byweight;byweight.reserve(L*2);std::vector<std::pair<I,int>>sorted;
  for(int a=0;a<L;++a){if(weights[a]<=0||!byweight.emplace(weights[a],a).second){guard_reason="nonunique_or_nonpositive_leaf_weights";return;}sorted.push_back({weights[a],a});}
  std::sort(sorted.begin(),sorted.end());pairs.resize(O);std::vector<std::vector<Literal>>occ(L);
  for(int j=0;j<O;++j){const I S=strengths[j];
   for(auto [w,a]:sorted){if(S128(w)*2>=S)break;++pair_checks;auto it=byweight.find(S-w);if(it==byweight.end())continue;const int b=it->second;
    pairs[j].push_back({std::min(a,b),std::max(a,b)});++candidate_pairs;
    if(pairs[j].size()>2){guard_reason="object_more_than_two_complete_candidate_pairs";return;}
   }
   std::sort(pairs[j].begin(),pairs[j].end());if(pairs[j].empty()){contradiction=true;guard_reason="object_has_no_complete_candidate_pair";return;}
   for(int t=0;t<int(pairs[j].size());++t)for(int a:{pairs[j][t].first,pairs[j][t].second}){occ[a].push_back({j,t});max_leaf_occurrence=std::max<U>(max_leaf_occurrence,occ[a].size());if(occ[a].size()>2){guard_reason="leaf_more_than_two_candidate_occurrences";return;}}
  }
  parent.resize(O+1);rank.assign(O+1,0);parity.assign(O+1,0);for(int j=0;j<=O;++j)parent[j]=j;
  auto impose=[&](int a,int b,int p){++constraint_equations;if(!unite(a,b,p)){contradiction=true;guard_reason="affine_constraints_inconsistent";return false;}return true;};
  for(int j=0;j<O;++j)if(pairs[j].size()==1&&!impose(j,O,0))return;
  for(int a=0;a<L;++a){if(occ[a].empty()){contradiction=true;guard_reason="leaf_has_no_candidate_occurrence";return;}
   const Literal first=occ[a][0];if(occ[a].size()==1){if(!impose(first.object,O,first.choice))return;}
   else{const Literal second=occ[a][1];if(!impose(first.object,second.object,1^first.choice^second.choice))return;}
  }
  const auto anchor=find(O);std::map<int,int>groups;object_group.assign(O,-1);object_parity.resize(O);
  for(int j=0;j<O;++j){const auto root=find(j);if(root.first==anchor.first)object_parity[j]=root.second^anchor.second;
   else{auto inserted=groups.emplace(root.first,int(groups.size()));object_group[j]=inserted.first->second;object_parity[j]=root.second;}}
  free_components=groups.size();exact_count=1;mpz_mul_2exp(exact_count.get_mpz_t(),exact_count.get_mpz_t(),free_components);eligible=true;guard_reason="complete_affine_fiber_certified";
 }
 std::pair<int,int>find(int x){if(parent[x]==x)return{x,0};auto z=find(parent[x]);parity[x]^=z.second;parent[x]=z.first;return{parent[x],parity[x]};}
 bool unite(int a,int b,int value){auto x=find(a),y=find(b);if(x.first==y.first)return(x.second^y.second)==value;if(rank[x.first]<rank[y.first])std::swap(x,y);parent[y.first]=x.first;parity[y.first]=x.second^y.second^value;if(rank[x.first]==rank[y.first])++rank[x.first];++unions;return true;}
 std::vector<int>owners_for_bits(const std::vector<int>&bits)const{
  if(!eligible||bits.size()!=free_components)throw std::runtime_error("uncertified XOR draw or wrong free-bit count");for(int bit:bits)if(bit<0||bit>1)throw std::runtime_error("nonbinary XOR bit");std::vector<int>owners(leaves.size(),-1);
  for(int j=0;j<int(objects.size());++j){const int t=object_parity[j]^(object_group[j]<0?0:bits[object_group[j]]);if(t>=int(pairs[j].size()))throw std::runtime_error("XOR chose nonexistent candidate");for(int a:{pairs[j][t].first,pairs[j][t].second}){if(owners[a]>=0)throw std::runtime_error("XOR leaf duplicate owner");owners[a]=j;}}
  if(std::find(owners.begin(),owners.end(),-1)!=owners.end())throw std::runtime_error("XOR leaf missing owner");return owners;
 }
 bool commit(Engine&e,Graph&g,int leaf_axis,const std::vector<int>&owners){
  if(owners.size()!=leaves.size())throw std::runtime_error("XOR owner count");bool differs=false;
  for(size_t a=0;a<leaves.size();++a){const int leaf=leaves[a],v=leaf_axis?g.nr+leaf:leaf;if(g.adj[v].size()!=1)throw std::runtime_error("XOR current leaf degree");const auto&edge=g.edges[g.adj[v][0]];const int oldobject=leaf_axis?edge.r:edge.c,newobject=objects[owners[a]];if(oldobject==newobject)continue;differs=true;++moved_leaves;
   if(leaf_axis){g.set_raw(oldobject,leaf,0);g.set_raw(newobject,leaf,weights[a]);}else{g.set_raw(leaf,oldobject,0);g.set_raw(leaf,newobject,weights[a]);}edge_writes+=2;
  }
  if(differs){++changes;++e.stat.changed_outer;}return differs;
 }
 bool draw(Engine&e,Graph&g,int leaf_axis){++calls;++e.stat.work;std::vector<int>bits(free_components);for(int&bit:bits){bit=int(e.rng.below(2));++free_bit_draws;}return commit(e,g,leaf_axis,owners_for_bits(bits));}
};

struct CertifiedMatchingJointKernel:JournaledLowrank4Kernel {
 std::unique_ptr<StaticXorMatchingProblem>xor_problem;double xor_build_cpu_seconds=0;
 bool matching_eligible=false;int leaf_axis=-1;std::vector<int>object_pool;
 std::unique_ptr<LeafPairMatchingProblem>global_problem;
 struct Component {std::vector<int>objects,leaves;std::unique_ptr<LeafPairMatchingProblem>cached;U exact_count=0;};
 std::vector<Component>components;std::vector<int>leaf_component,object_component;
 U feasibility_checks=0,feasibility_pairs=0,component_cache_count=0,component_cache_bytes=0;
 static constexpr U component_cache_budget=64ULL*1024*1024;
 bool factor_count_known=false;mpz_class factor_count_product=1;
 U matching_calls=0,matching_changed=0,matching_patch_builds=0,matching_cache_hits=0,matching_masks_built=0,matching_completion_total=0;
 explicit CertifiedMatchingJointKernel(const Graph&g,bool build_matching=true,bool try_xor=false):JournaledLowrank4Kernel(g){
  for(int side=0;side<2;++side){const int n=side?g.nc:g.nr,off=side?g.nr:0,other=side?g.nr:g.nc,other_off=side?0:g.nr;bool good=true;int leaves=0;std::set<I>ws,ss;std::vector<int>pool;
   for(int v=0;v<n;++v){const int d=g.target_degree[off+v];if(!d)continue;++leaves;if(d!=1||!ws.insert(g.target_strength[off+v]).second){good=false;break;}}
   if(!good||!leaves)continue;
   for(int v=0;v<other;++v){const int d=g.target_degree[other_off+v];if(!d)continue;if(d!=2||!ss.insert(g.target_strength[other_off+v]).second){good=false;break;}pool.push_back(v);}
   if(good&&!pool.empty()){matching_eligible=true;leaf_axis=side;object_pool=std::move(pool);break;}
  }
  if(matching_eligible&&build_matching){
   if(try_xor){const double begin=process_cpu();std::vector<int>leaves;std::vector<I>weights,strengths;const int L=leaf_axis?g.nc:g.nr;for(int leaf=0;leaf<L;++leaf){const int v=leaf_axis?g.nr+leaf:leaf;if(g.target_degree[v]){leaves.push_back(leaf);weights.push_back(g.target_strength[v]);}}for(int object:object_pool)strengths.push_back(g.target_strength[leaf_axis?object:g.nr+object]);xor_problem=std::make_unique<StaticXorMatchingProblem>(leaves,object_pool,weights,strengths);xor_build_cpu_seconds=process_cpu()-begin;if(xor_problem->contradiction)throw std::runtime_error("XOR complete candidate law contradicts input margins");}
   if(!xor_problem||!xor_problem->eligible)build_components(g,true);
  }
 }

 void build_components(const Graph&g,bool build_matching){
  const int nleaf=leaf_axis?g.nc:g.nr,nobject=leaf_axis?g.nr:g.nc;
  std::vector<int>leaves;for(int v=0;v<nleaf;++v)if(g.target_degree[leaf_axis?g.nr+v:v])leaves.push_back(v);
  const int L=leaves.size(),O=object_pool.size();std::vector<int>parent(L+O),size(L+O,1);for(int v=0;v<L+O;++v)parent[v]=v;
  auto find=[&](int v){while(parent[v]!=v){parent[v]=parent[parent[v]];v=parent[v];}return v;};
  auto unite=[&](int a,int b){a=find(a);b=find(b);if(a==b)return;if(size[a]<size[b])std::swap(a,b);parent[b]=a;size[a]+=size[b];};
  std::unordered_map<I,int>byweight;byweight.reserve(leaves.size()*2);std::vector<std::pair<I,int>>sorted;
  for(int i=0;i<L;++i){const I w=g.target_strength[leaf_axis?g.nr+leaves[i]:leaves[i]];byweight.emplace(w,i);sorted.push_back({w,i});}
  std::sort(sorted.begin(),sorted.end());
  for(int j=0;j<O;++j){const I S=g.target_strength[leaf_axis?object_pool[j]:g.nr+object_pool[j]];
   for(auto [w,a]:sorted){if(S128(w)*2>=S)break;++feasibility_checks;auto it=byweight.find(S-w);if(it==byweight.end())continue;const int b=it->second;
    unite(a,L+j);unite(b,L+j);++feasibility_pairs;}}
  std::map<int,std::pair<std::vector<int>,std::vector<int>>>groups;
  for(int i=0;i<L;++i)groups[find(i)].first.push_back(leaves[i]);for(int j=0;j<O;++j)groups[find(L+j)].second.push_back(object_pool[j]);
  for(auto&item:groups){Component c;c.leaves=std::move(item.second.first);c.objects=std::move(item.second.second);if(c.leaves.size()!=2*c.objects.size()||c.objects.empty())throw std::runtime_error("constraint component does notfactor into2leaves perobject");components.push_back(std::move(c));}
  std::sort(components.begin(),components.end(),[](const Component&a,const Component&b){return a.objects[0]<b.objects[0];});
  leaf_component.assign(nleaf,-1);object_component.assign(nobject,-1);
  for(int k=0;k<int(components.size());++k){S128 leaf_sum=0,object_sum=0;for(int leaf:components[k].leaves){leaf_component[leaf]=k;leaf_sum+=g.target_strength[leaf_axis?g.nr+leaf:leaf];}for(int object:components[k].objects){object_component[object]=k;object_sum+=g.target_strength[leaf_axis?object:g.nr+object];}if(leaf_sum!=object_sum)throw std::runtime_error("component strength totals do notfactor");}
  for(const auto&ed:g.edges){const int leaf=leaf_axis?ed.c:ed.r,object=leaf_axis?ed.r:ed.c;if(leaf_component[leaf]!=object_component[object])throw std::runtime_error("current edge outside fixedconstraintcomponent");}
  factor_count_known=build_matching;
  if(build_matching)for(auto&c:components){if(c.objects.size()>10){factor_count_known=false;continue;}auto p=compile(g,c.objects);c.exact_count=p->total;factor_count_product*=p->total;++matching_patch_builds;matching_masks_built+=p->visited_masks;
   const U bytes=U(p->memo.capacity())*sizeof(U)+U(p->leaves.capacity()+p->objects.capacity())*sizeof(int)+U(p->weights.capacity()+p->strengths.capacity())*sizeof(I)+U(p->pairs.capacity())*sizeof(std::vector<std::pair<int,int>>);
   U extra=0;for(const auto&ps:p->pairs)extra+=U(ps.capacity())*sizeof(std::pair<int,int>);
   if(bytes+extra<=component_cache_budget-component_cache_bytes){component_cache_bytes+=bytes+extra;++component_cache_count;c.cached=std::move(p);}
  }
 }
 std::unique_ptr<LeafPairMatchingProblem> compile(const Graph&g,const std::vector<int>&objects){
  std::vector<int>leaves;std::vector<I>weights,strengths;for(int object:objects){strengths.push_back(g.target_strength[leaf_axis?object:g.nr+object]);const int v=leaf_axis?object:g.nr+object;
   if(g.adj[v].size()!=2)throw std::runtime_error("matching object degree changed");for(int id:g.adj[v])leaves.push_back(leaf_axis?g.edges[id].c:g.edges[id].r);}
  std::sort(leaves.begin(),leaves.end());if(std::adjacent_find(leaves.begin(),leaves.end())!=leaves.end())throw std::runtime_error("matching leaf not unique");
  for(int leaf:leaves){const int v=leaf_axis?g.nr+leaf:leaf;if(g.target_degree[v]!=1||g.degree[v]!=1)throw std::runtime_error("matching pool contains nonleaf");weights.push_back(g.target_strength[v]);}
  return std::make_unique<LeafPairMatchingProblem>(leaves,objects,weights,strengths);
 }
 bool step(Engine&e,Graph&g){
  if(!matching_eligible)return JournaledLowrank4Kernel::step(e,g);
  ++calls;++matching_calls;++e.stat.work;undo.clear();std::unique_ptr<LeafPairMatchingProblem>local;LeafPairMatchingProblem*problem=nullptr;
  Component&component=components[e.rng.below(components.size())];
  if(component.cached){++matching_cache_hits;problem=component.cached.get();}
  else{const auto&pool=component.objects;const int r=std::min<int>(10,pool.size());std::vector<int>objects;
   if(r==int(pool.size()))objects=pool;
   else{std::vector<int>selected;for(U j=U(pool.size())-r;j<U(pool.size());++j){int k=int(e.rng.below(j+1));if(std::find(selected.begin(),selected.end(),k)!=selected.end())k=int(j);selected.push_back(k);}for(int k:selected)objects.push_back(pool[k]);std::sort(objects.begin(),objects.end());}
   local=compile(g,objects);problem=local.get();++matching_patch_builds;matching_masks_built+=problem->visited_masks;
  }
  matching_completion_total+=problem->total;auto owners=problem->unrank(e.rng.below(problem->total));bool differs=false;
  for(size_t i=0;i<problem->leaves.size();++i){const int leaf=problem->leaves[i],v=leaf_axis?g.nr+leaf:leaf;const auto&edge=g.edges[g.adj[v][0]];const int oldobject=leaf_axis?edge.r:edge.c,newobject=problem->objects[owners[i]];if(oldobject==newobject)continue;
   differs=true;const I w=problem->weights[i];if(leaf_axis){journal_put(g,oldobject,leaf,0);journal_put(g,newobject,leaf,w);}else{journal_put(g,leaf,oldobject,0);journal_put(g,leaf,newobject,w);}
  }
  if(differs){++changed;++matching_changed;++e.stat.changed_outer;}return differs;
 }

 bool full_sweep_available()const{
  if(!matching_eligible||components.empty()||!factor_count_known)return false;
  for(const auto&c:components)if(c.objects.size()>10)return false;
  return true;
 }
 bool sweep(Engine&e,Graph&g){
  if(!full_sweep_available())throw std::runtime_error("uncertified matching sweep");
  bool any=false;
  for(auto&component:components){
   ++calls;++matching_calls;++e.stat.work;undo.clear();
   std::unique_ptr<LeafPairMatchingProblem>local;LeafPairMatchingProblem*problem=nullptr;
   if(component.cached){++matching_cache_hits;problem=component.cached.get();}
   else{local=compile(g,component.objects);problem=local.get();++matching_patch_builds;matching_masks_built+=problem->visited_masks;}
   matching_completion_total+=problem->total;auto owners=problem->unrank(e.rng.below(problem->total));bool differs=false;
   for(size_t i=0;i<problem->leaves.size();++i){const int leaf=problem->leaves[i],v=leaf_axis?g.nr+leaf:leaf;const auto&edge=g.edges[g.adj[v][0]];
    const int oldobject=leaf_axis?edge.r:edge.c,newobject=problem->objects[owners[i]];if(oldobject==newobject)continue;
    differs=true;const I w=problem->weights[i];if(leaf_axis){journal_put(g,oldobject,leaf,0);journal_put(g,newobject,leaf,w);}else{journal_put(g,leaf,oldobject,0);journal_put(g,leaf,newobject,w);}}
   if(differs){++changed;++matching_changed;++e.stat.changed_outer;any=true;}
  }
  return any;
 }
};

struct RegularDegreeTwoIID {
 bool eligible=false;I strength=0;int n=0;std::vector<int>rows,columns;
 U calls=0,permutation_attempts=0,fixedpoint_rejections=0,rejected_fixedpoints=0,crp_insertions=0;
 U object_shuffle_draws=0,cycles_drawn=0,last_cycles=0,edge_writes=0,changed=0;

 using CInt=mpz_class;
 bool no_rejection_requested=false,no_rejection_active=false,cache_ready=false,cache_guard_fallback=false;
 U cache_budget_bytes=64*1024*1024,cache_bytes=0,cache_workspace_bound_bytes=0,cache_build_terms=0;
 U derangement_steps=0,two_cycle_steps=0,insertion_steps=0,bernoulli_words=0,boundary_hits=0,refinement_words=0,ratio_rebuilds=0;
 double cache_build_cpu_seconds=0;std::vector<U>q64;
 static U ceil_log2(U x){U b=0;if(x)for(--x;x;x>>=1)++b;return b;}
 static std::pair<CInt,CInt> exact_ratio(int m,U theta){
  if(m<2)throw std::runtime_error("derangement requires m>=2");CInt previous2=1,previous1=0;
  for(int k=2;k<m;++k){CInt den=previous1+CInt(theta)*previous2;CInt next=CInt(2)*U(k-1)*den;previous2=std::move(previous1);previous1=std::move(next);}
  CInt num=CInt(theta)*previous2,den=previous1+num;return {std::move(num),std::move(den)};
 }
 template<class Raw>static bool exact_bool(CInt num,const CInt&den,Raw&&raw){
  if(den<=0||num<0||num>den)throw std::runtime_error("Bernoulli ratio outside[0,1]");
  for(;;){if(num==0)return false;if(num==den)return true;
   CInt expanded=num<<64,quotient=expanded/den,remainder=expanded%den;
   const U q=quotient.get_ui(),u=raw();if(u<q)return true;if(u>q)return false;num=std::move(remainder);
  }
 }
 bool build_cache(){

  const __uint128_t table=__uint128_t(U(n)+1)*sizeof(U);
  const __uint128_t max_bits=__uint128_t(U(n))*(2+ceil_log2(U(n))+ceil_log2(U(strength-1)))+128;
  const __uint128_t workspace=16*((max_bits+7)/8);
  cache_workspace_bound_bytes=workspace>std::numeric_limits<U>::max()?std::numeric_limits<U>::max():U(workspace);
  if(table+workspace>cache_budget_bytes){cache_guard_fallback=true;return false;}
  q64.assign(size_t(n)+1,U(0));cache_bytes=q64.capacity()*sizeof(U);
  CInt previous2=1,previous1=0;const U theta=U(strength-1);
  for(int m=2;m<=n;++m){CInt num=CInt(theta)*previous2,den=previous1+num;
   if(num!=0&&num!=den){CInt q=(num<<64)/den;q64[m]=q.get_ui();}
   CInt next=CInt(2)*U(m-1)*den;previous2=std::move(previous1);previous1=std::move(next);++cache_build_terms;
  }cache_ready=true;return true;
 }
 template<class Raw>bool choose_two_words(int m,Raw&&raw){
  if(m==2)return true;if(m==3)return false;if(m<2||m>n||!cache_ready)throw std::runtime_error("derangement cached m invalid");
  ++bernoulli_words;const U u=raw(),q=q64[m];if(u<q)return true;if(u>q)return false;
  ++boundary_hits;++ratio_rebuilds;auto ratio=exact_ratio(m,U(strength-1));CInt remainder=(ratio.first<<64)-CInt(q)*ratio.second;
  return exact_bool(std::move(remainder),ratio.second,[&](){++bernoulli_words;++refinement_words;return U(raw());});
 }
 bool choose_two(Engine&e,int m){return choose_two_words(m,[&](){return U(e.rng.gen());});}
 template<class Choose,class Pick>void build_sigma(std::vector<int>&sigma,Choose&&choose,Pick&&pick){
  struct Frame{bool pair;int label,other;};std::vector<int>active(n);std::iota(active.begin(),active.end(),0);
  std::vector<Frame>frames;frames.reserve(n);sigma.assign(n,-1);
  while(!active.empty()){const int m=int(active.size());if(m<2)throw std::runtime_error("derangement reached invalid singleton");
   const bool pair=choose(m);const U index=pick(U(m-1));if(index>=U(m-1))throw std::runtime_error("derangement partner index");
   const int label=active.back(),other=active[index];frames.push_back({pair,label,other});++derangement_steps;
   if(pair){++two_cycle_steps;active[index]=active[m-2];active.resize(m-2);}else{++insertion_steps;active.pop_back();}
  }
  for(auto it=frames.rbegin();it!=frames.rend();++it){if(it->pair){sigma[it->label]=it->other;sigma[it->other]=it->label;}
   else{if(sigma[it->other]<0)throw std::runtime_error("derangement predecessor absent");sigma[it->label]=sigma[it->other];sigma[it->other]=it->label;}}
 }

 explicit RegularDegreeTwoIID(const Graph&g,bool requested=false,U budget=64*1024*1024):no_rejection_requested(requested),cache_budget_bytes(budget){
  if(g.nr!=g.nc)return;
  for(int axis=0;axis<2;++axis){const int count=axis?g.nc:g.nr,off=axis?g.nr:0;
   for(int label=0;label<count;++label){const int d=g.target_degree[off+label];const I S=g.target_strength[off+label];
    if(!d){if(S)return;continue;}if(d!=2||S<2||(!requested&&S>6))return;if(strength&&strength!=S)return;strength=S;
    (axis?columns:rows).push_back(label);}}
  if(rows.size()!=columns.size()||rows.size()<2)return;n=rows.size();eligible=true;
  if(requested){const double start=process_cpu();no_rejection_active=build_cache();cache_build_cpu_seconds=process_cpu()-start;if(!no_rejection_active)eligible=strength<=6;}
 }
 bool draw(Engine&e,Graph&g){
  if(!eligible)throw std::runtime_error("regular IID certificate absent");
  ++calls;const U before1=g.hash1,before2=g.hash2,theta=U(strength-1);
  std::vector<int>sigma(n);std::vector<I>phase(n,0);std::vector<int>pi=columns;
  if(no_rejection_active){++permutation_attempts;const U before_steps=derangement_steps;build_sigma(sigma,[&](int m){return choose_two(e,m);},[&](U count){return e.rng.below(count);});e.stat.work+=derangement_steps-before_steps;}
  else for(;;){++permutation_attempts;
   for(int i=0;i<n;++i){++crp_insertions;++e.stat.work;const U r=e.rng.below(theta+2*U(i));
    if(r<theta)sigma[i]=i;else{const int j=int((r-theta)/2);sigma[i]=sigma[j];sigma[j]=i;}}
   U fixed=0;for(int i=0;i<n;++i)fixed+=sigma[i]==i;
   if(!fixed)break;++fixedpoint_rejections;rejected_fixedpoints+=fixed;
  }
  for(int i=n-1;i>0;--i){++object_shuffle_draws;++e.stat.work;std::swap(pi[i],pi[e.rng.below(U(i)+1)]);}
  last_cycles=0;
  for(int i=0;i<n;++i)if(!phase[i]){++last_cycles;++cycles_drawn;++e.stat.work;const I x=I(e.rng.below(theta))+1;
   int j=i;do{if(phase[j])throw std::runtime_error("regular permutation cycle overlaps");phase[j]=x;j=sigma[j];}while(j!=i);}
  std::vector<std::pair<int,int>>old_cells;old_cells.reserve(g.edges.size());for(const auto&ed:g.edges)old_cells.push_back({ed.r,ed.c});
  for(auto [r,c]:old_cells){g.set_raw(r,c,0);++edge_writes;}
  for(int u=0;u<n;++u){g.set_raw(rows[u],pi[u],phase[u]);g.set_raw(rows[u],pi[sigma[u]],strength-phase[u]);edge_writes+=2;}
  const bool differs=before1!=g.hash1||before2!=g.hash2;if(differs){++changed;++e.stat.changed_outer;}return differs;
 }
};

struct BalancedPrivateHeatbath {
 struct Scene {int o=0,root=-1;std::array<int,3>nodes{},quota{};std::array<std::vector<int>,3>pools;};
 struct Problem {
  Scene scene;std::vector<int>columns,current;std::vector<I>weights;std::array<I,3>bound{};
  std::vector<std::vector<int>>owners;std::vector<std::array<I,3>>root_weights;
 };
 JournaledLowrank4Kernel&shared;int cap=2;
 U calls=0,changes=0,empty_roots=0,completions=0,singletons=0,scan_visits=0,epoch_resets=0;
 U selected_private_total=0,private_pool_total=0,compiled_windows=0,enumeration_nodes=0;
 U max_completions=0,max_selected_private=0;double cpu_seconds=0;
 std::map<std::string,U>privateowner_counts;
 explicit BalancedPrivateHeatbath(JournaledLowrank4Kernel&k,int c):shared(k),cap(c){if(c<1||c>3)throw std::runtime_error("balanced private cap must be1..3");}
 static I value(const Graph&g,const Scene&s,int i,int col){return s.o?g.value(col,s.nodes[i]):g.value(s.nodes[i],col);}
 static void put(Graph&g,const Scene&s,int i,int col,I w){if(s.o)g.set_raw(col,s.nodes[i],w);else g.set_raw(s.nodes[i],col,w);}
 Scene make_scene(const Graph&g,int o,int root,std::array<int,3>nodes){
  std::sort(nodes.begin(),nodes.end());if(nodes[0]==nodes[1]||nodes[1]==nodes[2])throw std::runtime_error("balanced participants repeated");
  Scene s;s.o=o;s.root=root;s.nodes=nodes;auto&tmp=shared.scratch[o];if(tmp.next_epoch())++epoch_resets;
  for(int i=0;i<3;++i){if(value(g,s,i,root)<=0)throw std::runtime_error("balanced common edge absent");
   const int vertex=o?g.nr+nodes[i]:nodes[i];for(int id:g.adj[vertex]){++scan_visits;const auto&ed=g.edges[id];const int col=o?ed.r:ed.c;
    if(tmp.stamp[col]!=tmp.epoch){tmp.stamp[col]=tmp.epoch;tmp.mask[col]=0;tmp.touched.push_back(col);}tmp.mask[col]|=uint8_t(1u<<i);}}
  for(int col:tmp.touched)if(col!=root&&__builtin_popcount(unsigned(tmp.mask[col]))==1){const int owner=__builtin_ctz(unsigned(tmp.mask[col]));s.pools[owner].push_back(col);}
  for(int i=0;i<3;++i)s.quota[i]=std::min(cap,int(s.pools[i].size()));return s;
 }
 Problem compile(const Graph&g,const Scene&s,std::vector<int>selected){
  Problem p;p.scene=s;std::sort(selected.begin(),selected.end());if(std::adjacent_find(selected.begin(),selected.end())!=selected.end())throw std::runtime_error("balanced private label repeated");
  p.columns=std::move(selected);if(p.columns.size()>size_t(3*cap))throw std::runtime_error("balanced width exceeded");
  std::array<int,3>current_counts{};for(int i=0;i<3;++i)p.bound[i]=value(g,s,i,s.root);
  for(int col:p.columns){if(col==s.root)throw std::runtime_error("balanced private contains root");int owner=-1;I w=0;
   for(int i=0;i<3;++i){const I v=value(g,s,i,col);if(v){if(owner>=0)throw std::runtime_error("balanced selected object is not private");owner=i;w=v;}}
   if(owner<0)throw std::runtime_error("balanced private edge missing");++current_counts[owner];p.current.push_back(owner);p.weights.push_back(w);
   const S128 sum=S128(p.bound[owner])+w;if(sum>std::numeric_limits<I>::max())throw std::runtime_error("balanced local sum overflow");p.bound[owner]=I(sum);
  }
  if(current_counts!=s.quota)throw std::runtime_error("balanced selected quota mismatch");
  std::vector<int>owners(p.columns.size(),-1);std::array<int,3>remaining=s.quota;std::array<I,3>residual=p.bound;
  std::function<void(size_t)>dfs=[&](size_t j){++enumeration_nodes;
   if(j==p.columns.size()){if(remaining!=std::array<int,3>{0,0,0})throw std::runtime_error("balanced terminal quota");p.owners.push_back(owners);p.root_weights.push_back(residual);return;}
   for(int i=0;i<3;++i)if(remaining[i]&&p.weights[j]<residual[i]){--remaining[i];residual[i]-=p.weights[j];owners[j]=i;dfs(j+1);residual[i]+=p.weights[j];++remaining[i];}
  };dfs(0);
  if(p.owners.empty()||p.owners.size()>1680)throw std::runtime_error("balanced original completion absent or bound exceeded");
  if(std::find(p.owners.begin(),p.owners.end(),p.current)==p.owners.end())throw std::runtime_error("balanced original arrangement excluded");
  return p;
 }
 bool commit(Engine&e,Graph&g,const Problem&p,size_t index){
  if(index>=p.owners.size())throw std::runtime_error("balanced draw index outside exact options");const auto&owners=p.owners[index];bool differs=owners!=p.current;
  for(int i=0;i<3;++i)differs|=p.root_weights[index][i]!=value(g,p.scene,i,p.scene.root);if(!differs)return false;
  for(size_t j=0;j<p.columns.size();++j)for(int i=0;i<3;++i)put(g,p.scene,i,p.columns[j],owners[j]==i?p.weights[j]:0);
  for(int i=0;i<3;++i)put(g,p.scene,i,p.scene.root,p.root_weights[index][i]);++changes;++e.stat.changed_outer;return true;
 }
 bool step(Engine&e,Graph&g){
  ++calls;++e.stat.work;if(g.D)throw std::runtime_error("balanced requires four exact margins");const int o=choose_orientation(e.rng,g);const auto&roots=shared.roots[o];
  if(roots.empty()){++empty_roots;return false;}const int root=roots[e.rng.below(roots.size())],vertex=o?root:g.nr+root;const auto&adj=g.adj[vertex];
  if(adj.size()<3)throw std::runtime_error("balanced root degree changed");std::vector<int>ix;
  for(U j=adj.size()-3;j<adj.size();++j){int k=int(e.rng.below(j+1));if(std::find(ix.begin(),ix.end(),k)!=ix.end())k=int(j);ix.push_back(k);}
  std::array<int,3>nodes{};for(int i=0;i<3;++i){const auto&ed=g.edges[adj[ix[i]]];nodes[i]=o?ed.c:ed.r;}
  Scene scene=make_scene(g,o,root,nodes);std::vector<int>selected;
  for(int i=0;i<3;++i){const auto&pool=scene.pools[i];const U p=pool.size(),m=scene.quota[i];std::vector<int>chosen;
   for(U j=p-m;j<p;++j){int k=int(e.rng.below(j+1));if(std::find(chosen.begin(),chosen.end(),k)!=chosen.end())k=int(j);chosen.push_back(k);}
   for(int k:chosen)selected.push_back(pool[k]);private_pool_total+=p;selected_private_total+=m;
  }
  const std::string key=std::to_string(scene.quota[0])+":"+std::to_string(scene.quota[1])+":"+std::to_string(scene.quota[2]);++privateowner_counts[key];
  Problem problem=compile(g,scene,std::move(selected));++compiled_windows;completions+=problem.owners.size();singletons+=problem.owners.size()==1;
  max_completions=std::max<U>(max_completions,problem.owners.size());max_selected_private=std::max<U>(max_selected_private,problem.columns.size());
  return commit(e,g,problem,size_t(e.rng.below(problem.owners.size())));
 }
 std::string owner_count_json()const{std::ostringstream f;f<<'{';bool first=true;for(const auto&item:privateowner_counts){if(!first)f<<',';first=false;f<<'"'<<item.first<<"\":"<<item.second;}f<<'}';return f.str();}
};

struct TypedLocalCompiler:BalancedPrivateHeatbath {
 static constexpr U heterogeneous_capacity=6;
 SupportSceneBitset* scene_bitset=nullptr;
 std::string mode;U disabled_equal_calls=0,disabled_enumerated_calls=0,equal_compiled_calls=0,equal_changes=0,enumerated_changes=0,equal_moved_labels=0,enumerated_moved_labels=0;
 struct GroupEntry {U stamp=0,count=0,head=std::numeric_limits<U>::max();I weight=0;std::array<U,3>quota{};};
 struct PrivateRecord {int column=0,owner=0;I weight=0;U next=std::numeric_limits<U>::max();};
 struct EqualProblem {Scene scene;I weight=0;std::vector<int>columns,current;std::array<U,3>quota{};};
 std::vector<GroupEntry>table;std::vector<U>group_slots,ties;std::vector<PrivateRecord>records;U group_epoch=0;
 U equal_calls=0,enumerated_calls=0,equal_singletons=0,equal_objects_total=0,max_equal_objects=0,max_equal_quota=0;
 U moved_labels=0,group_entries_total=0,max_groups=0,group_epoch_resets=0,max_table_slots=0;
 double scan_cpu_seconds=0,group_cpu_seconds=0,solve_cpu_seconds=0,write_cpu_seconds=0;
 explicit TypedLocalCompiler(JournaledLowrank4Kernel&k,std::string mode_="full"):BalancedPrivateHeatbath(k,2),mode(std::move(mode_)){if(mode!="full"&&mode!="heterogeneous-only"&&mode!="homogeneous-only")throw std::runtime_error("typed mode");}
 Scene make_scene(const Graph&g,int o,int root,std::array<int,3>nodes){
  std::sort(nodes.begin(),nodes.end());if(nodes[0]==nodes[1]||nodes[1]==nodes[2])throw std::runtime_error("typed repeated participants");Scene s;s.o=o;s.root=root;s.nodes=nodes;auto&tmp=shared.scratch[o];if(tmp.next_epoch())++epoch_resets;
  for(int i=0;i<3;++i)if(value(g,s,i,root)<=0)throw std::runtime_error("typed root missing");
  const bool bitset_collected=scene_bitset&&scene_bitset->collect(g,o,nodes,s.pools,tmp);
  if(!bitset_collected){
   for(int i=0;i<3;++i){const int vertex=o?g.nr+nodes[i]:nodes[i];
    for(int id:g.adj[vertex]){++scan_visits;const auto&ed=g.edges[id];const int col=o?ed.r:ed.c;if(tmp.stamp[col]!=tmp.epoch){tmp.stamp[col]=tmp.epoch;tmp.mask[col]=0;tmp.first_weight[col]=ed.w;tmp.touched.push_back(col);}tmp.mask[col]|=uint8_t(1u<<i);}}
   for(int col:tmp.touched)if(col!=root&&__builtin_popcount(unsigned(tmp.mask[col]))==1){const int owner=__builtin_ctz(unsigned(tmp.mask[col]));s.pools[owner].push_back(col);}
  }
  for(int i=0;i<3;++i)s.quota[i]=std::min(2,int(s.pools[i].size()));return s;
 }
 void group(const Scene&s){
  U p=0;for(const auto&pool:s.pools)p+=pool.size();U need=8;while(need<2*p){if(need>std::numeric_limits<U>::max()/2)throw std::runtime_error("typed group table size");need*=2;}
  if(table.size()<need){table.assign(size_t(need),GroupEntry{});group_epoch=1;}else if(group_epoch==std::numeric_limits<U>::max()){for(auto&e:table)e.stamp=0;group_epoch=1;++group_epoch_resets;}else ++group_epoch;
  max_table_slots=std::max<U>(max_table_slots,table.size());group_slots.clear();records.clear();ties.clear();records.reserve(size_t(p));const auto&tmp=shared.scratch[s.o];
  for(int owner=0;owner<3;++owner)for(int col:s.pools[owner]){if(tmp.stamp[col]!=tmp.epoch||__builtin_popcount(unsigned(tmp.mask[col]))!=1)throw std::runtime_error("typed grouping stale scene");const I w=tmp.first_weight[col];if(w<=0)throw std::runtime_error("typed private nonpositive");U slot=mix64(U(w))&U(table.size()-1);
   while(table[slot].stamp==group_epoch&&table[slot].weight!=w)slot=(slot+1)&U(table.size()-1);auto&e=table[slot];if(e.stamp!=group_epoch){e.stamp=group_epoch;e.weight=w;e.count=0;e.quota={0,0,0};e.head=std::numeric_limits<U>::max();group_slots.push_back(slot);}records.push_back({col,owner,w,e.head});e.head=records.size()-1;++e.count;++e.quota[owner];}
  U maximum=0;for(U slot:group_slots)maximum=std::max(maximum,table[slot].count);for(U slot:group_slots)if(table[slot].count==maximum)ties.push_back(slot);group_entries_total+=group_slots.size();max_groups=std::max<U>(max_groups,group_slots.size());
 }
 bool equal_mode()const{return !ties.empty()&&table[ties[0]].count>heterogeneous_capacity;}
 EqualProblem compile_equal(const Scene&s,U slot)const{
  if(slot>=table.size()||table[slot].stamp!=group_epoch)throw std::runtime_error("typed stale group");const auto&e=table[slot];EqualProblem p;p.scene=s;p.weight=e.weight;p.quota=e.quota;for(U j=e.head;j!=std::numeric_limits<U>::max();j=records[j].next){p.columns.push_back(records[j].column);p.current.push_back(records[j].owner);}if(p.columns.size()!=e.count)throw std::runtime_error("typed equal group cardinality");return p;
 }
 template<class Pick>std::vector<uint8_t> subset(U q,U k,Pick&&pick){
  if(k>q)throw std::runtime_error("typed subset quota");const bool complement=k>q-k;const U m=std::min(k,q-k);std::vector<uint8_t>chosen(q,0);for(U j=q-m;j<q;++j){U x=pick(j+1);if(x>j)throw std::runtime_error("typed Floyd range");if(chosen[x])x=j;chosen[x]=1;++subset_draws;}if(complement)for(auto&v:chosen)v^=1;return chosen;
 }
 U subset_draws=0;
 template<class Pick>std::vector<int> draw_equal(const EqualProblem&p,Pick&&pick){
  const U q=p.columns.size();if(p.quota[0]+p.quota[1]+p.quota[2]!=q)throw std::runtime_error("typed equal totalquota");auto first=subset(q,p.quota[0],pick);std::vector<U>remaining;remaining.reserve(q-p.quota[0]);std::vector<int>owners(q,2);for(U j=0;j<q;++j){if(first[j])owners[j]=0;else remaining.push_back(j);}auto second=subset(remaining.size(),p.quota[1],pick);for(U j=0;j<remaining.size();++j)if(second[j])owners[remaining[j]]=1;return owners;
 }
 bool commit_equal(Engine&e,Graph&g,const EqualProblem&p,const std::vector<int>&owners){
  if(owners.size()!=p.columns.size())throw std::runtime_error("typed equal width");std::array<U,3>counts{};for(int owner:owners){if(owner<0||owner>2)throw std::runtime_error("typed equal owner");++counts[owner];}if(counts!=p.quota)throw std::runtime_error("typed equal quota");bool differs=false;
  for(U j=0;j<owners.size();++j)if(owners[j]!=p.current[j]){put(g,p.scene,p.current[j],p.columns[j],0);put(g,p.scene,owners[j],p.columns[j],p.weight);++moved_labels;differs=true;}if(differs){++changes;++e.stat.changed_outer;}return differs;
 }
 bool step(Engine&e,Graph&g){
  ++calls;++e.stat.work;if(g.D)throw std::runtime_error("typed requires exact margins");const int o=choose_orientation(e.rng,g);const auto&roots=shared.roots[o];if(roots.empty()){++empty_roots;return false;}
  const int root=roots[e.rng.below(roots.size())],vertex=o?root:g.nr+root;const auto&adj=g.adj[vertex];if(adj.size()<3)throw std::runtime_error("typed root degree changed");std::vector<int>ix;for(U j=adj.size()-3;j<adj.size();++j){int k=int(e.rng.below(j+1));if(std::find(ix.begin(),ix.end(),k)!=ix.end())k=int(j);ix.push_back(k);}std::array<int,3>nodes{};for(int i=0;i<3;++i){const auto&ed=g.edges[adj[ix[i]]];nodes[i]=o?ed.c:ed.r;}
  double ts=process_cpu();Scene scene=make_scene(g,o,root,nodes);scan_cpu_seconds+=process_cpu()-ts;for(const auto&pool:scene.pools)private_pool_total+=pool.size();
  ts=process_cpu();group(scene);group_cpu_seconds+=process_cpu()-ts;
  if(equal_mode()){
   ++equal_calls;const U slot=ties[e.rng.below(ties.size())];const auto&entry=table[slot];const U q=entry.count;equal_objects_total+=q;max_equal_objects=std::max(max_equal_objects,q);U positiveowners=0;for(U k:entry.quota){positiveowners+=k>0;max_equal_quota=std::max(max_equal_quota,k);}if(mode=="heterogeneous-only"){++disabled_equal_calls;return false;}if(positiveowners<=1){++equal_singletons;++singletons;return false;}EqualProblem p=compile_equal(scene,slot);++equal_compiled_calls;
   ts=process_cpu();auto owners=draw_equal(p,[&](U n){return e.rng.below(n);});solve_cpu_seconds+=process_cpu()-ts;ts=process_cpu();const U oldmoves=moved_labels;bool changed=commit_equal(e,g,p,owners);equal_changes+=changed;equal_moved_labels+=moved_labels-oldmoves;write_cpu_seconds+=process_cpu()-ts;return changed;
  }
  ++enumerated_calls;std::vector<int>selected;for(int i=0;i<3;++i){const auto&pool=scene.pools[i];const U p=pool.size(),m=scene.quota[i];std::vector<int>chosen;for(U j=p-m;j<p;++j){int k=int(e.rng.below(j+1));if(std::find(chosen.begin(),chosen.end(),k)!=chosen.end())k=int(j);chosen.push_back(k);}for(int k:chosen)selected.push_back(pool[k]);selected_private_total+=m;}
  const std::string key=std::to_string(scene.quota[0])+":"+std::to_string(scene.quota[1])+":"+std::to_string(scene.quota[2]);++privateowner_counts[key];if(mode=="homogeneous-only"){++disabled_enumerated_calls;return false;}ts=process_cpu();Problem problem=compile(g,scene,std::move(selected));++compiled_windows;completions+=problem.owners.size();singletons+=problem.owners.size()==1;max_completions=std::max<U>(max_completions,problem.owners.size());max_selected_private=std::max<U>(max_selected_private,problem.columns.size());const U draw=e.rng.below(problem.owners.size());U moving=0;for(U j=0;j<problem.current.size();++j)moving+=problem.owners[draw][j]!=problem.current[j];moved_labels+=moving;enumerated_moved_labels+=moving;solve_cpu_seconds+=process_cpu()-ts;ts=process_cpu();bool changed=commit(e,g,problem,draw);enumerated_changes+=changed;write_cpu_seconds+=process_cpu()-ts;return changed;
 }
};

#include "metropolized_profile_refresh.hpp"
#include "geometric_profile_refresh.hpp"
#include "root_orbit_profile_refresh.hpp"
#include "pair_conditional_profile.hpp"
#include "two_weight_complement.hpp"
#include "two_weight_slack_certificate.hpp"
#include "two_weight_single_proposal.hpp"
#include "budget_compatible_pair.hpp"
#include "sampled_private_buffer.hpp"
#include "distinct_private_buffer.hpp"
#include "near_weight_private_buffer.hpp"
struct FactorizedLocalCompiler:TypedLocalCompiler {
 struct Window {Scene scene;std::vector<int>selected,current;std::vector<I>weights;std::array<I,3>root{};std::vector<I>weight_ties;EqualProblem equal;std::vector<TwoWeightComplement::Record>complement_records;std::map<I,U>other_weight_counts;bool certificate_allows_tw=true;};
 TwoWeightComplement tw;TwoWeightSlackCertificate certificate;RootExcessTripleGuide root_guide;TwoWeightSingleProposal wide;BudgetCompatiblePair budget_pair;U pair_geometry_calls=0,pair_geometry_narrow=0,pair_geometry_wide=0;
 U primary_probe_calls=0,primary_probe_visits=0,primary_probe_empty=0;
 std::string factor_mode;bool profile=false;bool sampled_private=false,disable_M=false,distinct_private=false,near_private=false;SampledPrivateBufferSelector sampled;DistinctPrivateBufferSelector distinct;NearWeightPrivateBufferSelector near;U M_skipped_windows=0;
 U descriptor_windows=0,empty_selected=0,weight_tie_choices=0,complement_visits=0,B_closedform_windows=0,B_DFS_windows=0;
 U M_factor_windows=0,M_nontrivial_windows=0,M_oneholder_windows=0,M_empty_windows=0,M_objects_total=0,max_M_objects=0;
 U disabled_B_windows=0,disabled_M_windows=0,B_factor_changes=0,M_factor_changes=0,both_factor_changes=0,B_moved_labels=0,M_moved_labels=0,root_weight_changes=0;
 U M_root_weight_changes=0;
 double descriptor_cpu_seconds=0,B_solve_cpu_seconds=0,M_solve_cpu_seconds=0,joint_write_cpu_seconds=0;
 explicit FactorizedLocalCompiler(JournaledLowrank4Kernel&k,std::string mode_="full",bool profile_=false):TypedLocalCompiler(k,"full"),factor_mode(std::move(mode_)),profile(profile_){if(factor_mode!="full"&&factor_mode!="heterogeneous-only"&&factor_mode!="homogeneous-only")throw std::runtime_error("factorized mode");}
 Window make_window(const Graph&g,const Scene&s,std::vector<int>selected)const{
  Window p;p.scene=s;std::sort(selected.begin(),selected.end());if(std::adjacent_find(selected.begin(),selected.end())!=selected.end())throw std::runtime_error("factorized repeated selected label");p.selected=std::move(selected);if(p.selected.size()>6)throw std::runtime_error("factorized small capacity");std::array<int,3>counts{};std::vector<I>ordered;
  const auto&tmp=shared.scratch[s.o];for(int i=0;i<3;++i)p.root[i]=value(g,s,i,s.root);
  for(int col:p.selected){if(tmp.stamp[col]!=tmp.epoch||col==s.root||__builtin_popcount(unsigned(tmp.mask[col]))!=1)throw std::runtime_error("factorized selected is not private");const int owner=__builtin_ctz(unsigned(tmp.mask[col]));const I w=tmp.first_weight[col];if(w<=0)throw std::runtime_error("factorized selected weight");p.current.push_back(owner);p.weights.push_back(w);ordered.push_back(w);++counts[owner];}
  if(counts!=s.quota)throw std::runtime_error("factorized selected quota");std::sort(ordered.begin(),ordered.end());U best=0;
  for(size_t a=0;a<ordered.size();){size_t b=a+1;while(b<ordered.size()&&ordered[b]==ordered[a])++b;const U multiplicity=b-a;if(multiplicity>best){best=multiplicity;p.weight_ties.clear();}if(multiplicity==best)p.weight_ties.push_back(ordered[a]);a=b;}return p;
 }
 void compile_complement(Window&p,U tie_index,RNG*pair_rng=nullptr){
  if(tie_index>=p.weight_ties.size())throw std::runtime_error("factorized weight tie index");p.equal.scene=p.scene;p.equal.weight=p.weight_ties[tie_index];const auto&tmp=shared.scratch[p.scene.o];
  if(budget_compatible_complement){
   if(!pair_rng)throw std::runtime_error("budget pair missing RNG");std::map<I,U>counts;
   for(int owner=0;owner<3;++owner)for(int col:p.scene.pools[owner]){++complement_visits;if(std::binary_search(p.selected.begin(),p.selected.end(),col))continue;const I w=tmp.first_weight[col];if(w<=0||tmp.stamp[col]!=tmp.epoch||__builtin_popcount(unsigned(tmp.mask[col]))!=1)throw std::runtime_error("budget pair stale private label");p.complement_records.push_back({col,owner,w});++counts[w];}
   S128 C=0;for(I root:p.root)C+=S128(root);const auto choice=budget_pair.draw(counts,C,[&](U q){return pair_rng->below(q);},budget_pair_filter);
   if(!choice.primary)return;p.equal.weight=choice.primary;if(choice.pair)p.other_weight_counts[choice.other]=counts.at(choice.other);
   for(const auto&record:p.complement_records)if(record.weight==p.equal.weight){p.equal.columns.push_back(record.col);p.equal.current.push_back(record.owner);++p.equal.quota[record.owner];}
   return;
  }
  if(two_weight_slack_certificate&&!pair_specific_complement&&two_weight_complement&&factor_mode!="heterogeneous-only")p.certificate_allows_tw=certificate.evaluate(p.root,p.equal.weight,p.scene.pools,tmp).allow;

  if(two_weight_complement&&factor_mode!="heterogeneous-only"&&p.certificate_allows_tw){
   ++primary_probe_calls;bool primary_present=false;
   for(int owner=0;owner<3&&!primary_present;++owner)for(int col:p.scene.pools[owner]){
    ++primary_probe_visits;
    if(tmp.first_weight[col]==p.equal.weight&&!std::binary_search(p.selected.begin(),p.selected.end(),col)){primary_present=true;break;}
   }
   if(!primary_present){++primary_probe_empty;return;}
  }
  for(int owner=0;owner<3;++owner)for(int col:p.scene.pools[owner]){++complement_visits;if(std::binary_search(p.selected.begin(),p.selected.end(),col))continue;if(two_weight_complement&&factor_mode!="heterogeneous-only"&&p.certificate_allows_tw){const I w=tmp.first_weight[col];p.complement_records.push_back({col,owner,w});if(w!=p.equal.weight)++p.other_weight_counts[w];}if(tmp.first_weight[col]!=p.equal.weight)continue;if(tmp.stamp[col]!=tmp.epoch||__builtin_popcount(unsigned(tmp.mask[col]))!=1)throw std::runtime_error("factorized complement stale private label");p.equal.columns.push_back(col);p.equal.current.push_back(owner);++p.equal.quota[owner];}
 }
 bool commit_joint(Engine&e,Graph&g,const Window&p,const std::vector<int>&Bowners,const std::array<I,3>&roots,const std::vector<int>&Mowners){
  if(Bowners.size()!=p.selected.size()||Mowners.size()!=p.equal.columns.size())throw std::runtime_error("factorized owner dimensions");std::array<int,3>bcounts{};std::array<U,3>mcounts{};for(int x:Bowners){if(x<0||x>2)throw std::runtime_error("factorized B owner");++bcounts[x];}for(int x:Mowners){if(x<0||x>2)throw std::runtime_error("factorized M owner");++mcounts[x];}if(bcounts!=p.scene.quota||mcounts!=p.equal.quota)throw std::runtime_error("factorized quota changed");
  std::array<S128,3>bound{},newbound{};for(int i=0;i<3;++i){if(roots[i]<=0)throw std::runtime_error("factorized root nonpositive");bound[i]=p.root[i];newbound[i]=roots[i];}for(U j=0;j<p.selected.size();++j){bound[p.current[j]]+=p.weights[j];newbound[Bowners[j]]+=p.weights[j];}if(bound!=newbound)throw std::runtime_error("factorized B ledger changed");
  bool bc=false,mc=false;for(U j=0;j<p.selected.size();++j)if(Bowners[j]!=p.current[j]){put(g,p.scene,p.current[j],p.selected[j],0);put(g,p.scene,Bowners[j],p.selected[j],p.weights[j]);++B_moved_labels;bc=true;}
  for(U j=0;j<p.equal.columns.size();++j)if(Mowners[j]!=p.equal.current[j]){put(g,p.scene,p.equal.current[j],p.equal.columns[j],0);put(g,p.scene,Mowners[j],p.equal.columns[j],p.equal.weight);++M_moved_labels;mc=true;}
  for(int i=0;i<3;++i)if(roots[i]!=p.root[i]){put(g,p.scene,i,p.scene.root,roots[i]);++root_weight_changes;bc=true;}B_factor_changes+=bc;M_factor_changes+=mc;both_factor_changes+=bc&&mc;const bool changed=bc||mc;if(changed){++changes;++e.stat.changed_outer;}return changed;
 }
 bool step(Engine&e,Graph&g){
  ++calls;++e.stat.work;if(g.D)throw std::runtime_error("factorized requires exact margins");const int o=choose_orientation(e.rng,g);const auto&roots=shared.roots[o];if(roots.empty()){++empty_roots;return false;}const int root=roots[e.rng.below(roots.size())],vertex=o?root:g.nr+root;const auto&adj=g.adj[vertex];if(adj.size()<3)throw std::runtime_error("factorized root degree changed");std::array<int,3>nodes{};if(root_guide.active){auto choice=root_guide.draw(e,g,o,root);if(!choice.usable){++singletons;return false;}nodes=choice.actors;}else{std::vector<int>ix;for(U j=adj.size()-3;j<adj.size();++j){int k=int(e.rng.below(j+1));if(std::find(ix.begin(),ix.end(),k)!=ix.end())k=int(j);ix.push_back(k);}for(int i=0;i<3;++i){const auto&ed=g.edges[adj[ix[i]]];nodes[i]=o?ed.c:ed.r;}}
  double ts=profile?process_cpu():0;Scene scene;std::vector<int>selected;
  if(sampled_private){
   if(disable_M){scene.o=o;scene.root=root;scene.nodes=nodes;}
   else{scene=make_scene(g,o,root,nodes);for(const auto&pool:scene.pools)private_pool_total+=pool.size();}
   selected=near_private?near.select(e,g,scene,shared,!disable_M):(distinct_private?distinct.select(e,g,scene,shared,!disable_M):sampled.select(e,g,scene,shared,!disable_M));selected_private_total+=selected.size();
  }else{scene=make_scene(g,o,root,nodes);for(int i=0;i<3;++i){const auto&pool=scene.pools[i];const U P=pool.size(),m=scene.quota[i];std::vector<int>chosen;for(U j=P-m;j<P;++j){int k=int(e.rng.below(j+1));if(std::find(chosen.begin(),chosen.end(),k)!=chosen.end())k=int(j);chosen.push_back(k);}for(int k:chosen)selected.push_back(pool[k]);private_pool_total+=P;selected_private_total+=m;}}
  Window p=make_window(g,scene,std::move(selected));++descriptor_windows;max_selected_private=std::max<U>(max_selected_private,p.selected.size());if(p.selected.empty()){++empty_selected;++singletons;if(profile)descriptor_cpu_seconds+=process_cpu()-ts;return false;}
  if(disable_M){++M_skipped_windows;}else{++weight_tie_choices;compile_complement(p,budget_compatible_complement?0:e.rng.below(p.weight_ties.size()),budget_compatible_complement?&e.rng:nullptr);++M_factor_windows;}const U q=p.equal.columns.size();M_objects_total+=q;max_M_objects=std::max(max_M_objects,q);U holders=0;for(U k:p.equal.quota)holders+=k>0;if(!disable_M){M_nontrivial_windows+=holders>=2;M_empty_windows+=q==0;M_oneholder_windows+=q>0&&holders==1;}if(profile)descriptor_cpu_seconds+=process_cpu()-ts;
  std::vector<int>Bowners=p.current,Mowners=p.equal.current;std::array<I,3>newroots=p.root;const std::string key=std::to_string(scene.quota[0])+":"+std::to_string(scene.quota[1])+":"+std::to_string(scene.quota[2]);++privateowner_counts[key];
  if(factor_mode=="homogeneous-only")++disabled_B_windows;
  else{ts=profile?process_cpu():0;++compiled_windows;const bool identical=std::all_of(p.weights.begin(),p.weights.end(),[&](I w){return w==p.weights[0];});
   if(identical){++B_closedform_windows;EqualProblem B;B.scene=scene;B.weight=p.weights[0];B.columns=p.selected;B.current=p.current;for(int i=0;i<3;++i)B.quota[i]=U(scene.quota[i]);U count=1;for(U j=2;j<=p.selected.size();++j)count*=j;for(int i=0;i<3;++i)for(U j=2;j<=U(scene.quota[i]);++j)count/=j;completions+=count;max_completions=std::max(max_completions,count);singletons+=count==1&&holders<2;Bowners=draw_equal(B,[&](U n){return e.rng.below(n);});}
   else{++B_DFS_windows;Problem B=compile(g,scene,p.selected);if(sampled_private&&B.owners.size()>90)throw std::runtime_error("sampled B exceeds labeled owner bound90");completions+=B.owners.size();max_completions=std::max<U>(max_completions,B.owners.size());singletons+=B.owners.size()==1&&holders<2;const U k=e.rng.below(B.owners.size());Bowners=std::move(B.owners[k]);newroots=B.root_weights[k];}if(profile)B_solve_cpu_seconds+=process_cpu()-ts;}
  if(!disable_M&&two_weight_complement&&factor_mode!="heterogeneous-only"){

   const bool bc=commit_joint(e,g,p,Bowners,newroots,p.equal.current);bool mc=false;
   ++tw.calls;tw.complement_records_total+=p.complement_records.size();tw.other_classes_total+=p.other_weight_counts.size();
   U most=0;std::vector<I>ties;for(const auto&entry:p.other_weight_counts){if(entry.second>most){most=entry.second;ties.clear();}if(entry.second==most)ties.push_back(entry.first);}
   if(!p.certificate_allows_tw){}
   else if(p.equal.columns.empty()){++tw.empty_primary_class;}
   else if(ties.empty()){++tw.no_other_class;}
   else{
    ++tw.other_class_choices;const I other=ties[e.rng.below(ties.size())];const double mts=profile?process_cpu():0;auto M=tw.compile(g,p.scene,p.equal.weight,other,p.complement_records,!pair_specific_complement);
    if(pair_specific_complement){++pair_geometry_calls;if(!pair_conditional_profile_mode()){if(M.slack<=TwoWeightComplement::SLACK_CAP){++pair_geometry_narrow;M=tw.finish_counts(std::move(M));}else ++pair_geometry_wide;}}if(profile)tw.compile_cpu_seconds+=process_cpu()-mts;
    if(pair_conditional_profile_mode()){
     const double dts=profile?process_cpu():0;auto draw=tw.draw_pair_conditional(M,*this,e.rng,two_weight_profile_update=="pair_conditional_profile_hold",profile);if(profile)tw.draw_cpu_seconds+=process_cpu()-dts;
     const double cts=profile?process_cpu():0;auto events=tw.commit(g,M,draw);if(profile)tw.pair_conditional.commit_cpu_seconds+=process_cpu()-cts;
     tw.pair_conditional.moved_labels+=events.moved_labels;tw.pair_conditional.root_writes+=events.root_changes;tw.pair_conditional.cell_writes+=2*events.moved_labels+events.root_changes;tw.pair_conditional.label_changed_windows+=events.moved_labels>0;tw.pair_conditional.changed_windows+=events.changed;mc=events.changed;
     M_moved_labels+=events.moved_labels;M_root_weight_changes+=events.root_changes;if(mc){++M_factor_changes;if(bc)++both_factor_changes;else{++changes;++e.stat.changed_outer;}}
     return bc||mc;
    }
    if(pair_specific_complement&&wide_complement_proposal&&M.slack>TwoWeightComplement::SLACK_CAP){
     TwoWeightComplement::Draw d;if(wide.draw(M,*this,e.rng,d)){
      ++tw.profile_draws;tw.profile_changes+=d.a!=M.initial;const double cts=profile?process_cpu():0;auto events=tw.commit(g,M,d);if(profile)tw.commit_cpu_seconds+=process_cpu()-cts;mc=events.changed;
      M_moved_labels+=events.moved_labels;M_root_weight_changes+=events.root_changes;if(mc){++M_factor_changes;if(bc)++both_factor_changes;else{++changes;++e.stat.changed_outer;}}
      return bc||mc;
     }
    }
    if(M.active&&two_weight_slack_certificate&&M.profiles.size()<=1){++certificate.single_profile_fallbacks;}
    if(M.active&&(!two_weight_slack_certificate||M.profiles.size()>1)){if(two_weight_slack_certificate)++certificate.generalized_draws;const double dts=profile?process_cpu():0;auto draw=tw.draw(M,*this,e.rng);if(profile)tw.draw_cpu_seconds+=process_cpu()-dts;const double cts=profile?process_cpu():0;auto events=tw.commit(g,M,draw);if(profile)tw.commit_cpu_seconds+=process_cpu()-cts;mc=events.changed;
     M_moved_labels+=events.moved_labels;M_root_weight_changes+=events.root_changes;if(mc){++M_factor_changes;if(bc)++both_factor_changes;else{++changes;++e.stat.changed_outer;}}
     return bc||mc;
    }
   }

   ++tw.old_single_class_fallbacks;
   if(holders>=2){const double mts=profile?process_cpu():0;++equal_compiled_calls;Mowners=draw_equal(p.equal,[&](U n){return e.rng.below(n);});if(profile)tw.fallback_draw_cpu_seconds+=process_cpu()-mts;}
   Window after=p;after.current=Bowners;after.root=newroots;const bool fallback_changed=commit_joint(e,g,after,Bowners,newroots,Mowners);
   if(bc&&fallback_changed){--changes;--e.stat.changed_outer;++both_factor_changes;}
   return bc||fallback_changed;
  }
  if(disable_M||factor_mode=="heterogeneous-only")++disabled_M_windows;
  else if(holders>=2){ts=profile?process_cpu():0;++equal_compiled_calls;Mowners=draw_equal(p.equal,[&](U n){return e.rng.below(n);});if(profile)M_solve_cpu_seconds+=process_cpu()-ts;}
  ts=profile?process_cpu():0;const bool changed=commit_joint(e,g,p,Bowners,newroots,Mowners);if(profile)joint_write_cpu_seconds+=process_cpu()-ts;return changed;
 }
};

struct WeightClassTrade {
 struct Scene{int o=0,root=-1;std::array<int,2>nodes{};std::vector<int>columns,owners;std::vector<I>weights;};
 struct Class{Scene scene;I weight=0;std::vector<int>columns,owners;U quota=0;};
 bool nontrivial=false;U eligible_records_total=0,eligible_classes_total=0,empty_eligible=0,max_eligible_records=0;
 JournaledLowrank4Kernel&shared;std::array<std::vector<int>,2>roots;
 U calls=0,changes=0,empty_roots=0,empty_private=0,singletons=0,scan_visits=0,epoch_resets=0;
 U private_total=0,class_total=0,max_class=0,subset_draws=0,moved_labels=0;double cpu_seconds=0;
 explicit WeightClassTrade(JournaledLowrank4Kernel&k,const Graph&g,bool enabled,bool nontrivial_=false):shared(k),nontrivial(nontrivial_){if(enabled)for(int o=0;o<2;++o){const int n=o?g.nr:g.nc,off=o?0:g.nr;for(int r=0;r<n;++r)if(g.target_degree[off+r]>=2)roots[o].push_back(r);}}
 static I value(const Graph&g,const Scene&s,int i,int col){return s.o?g.value(col,s.nodes[i]):g.value(s.nodes[i],col);}
 static void put(Graph&g,const Scene&s,int i,int col,I w){if(s.o)g.set_raw(col,s.nodes[i],w);else g.set_raw(s.nodes[i],col,w);}
 Scene make_scene(const Graph&g,int o,int root,std::array<int,2>nodes){
  std::sort(nodes.begin(),nodes.end());if(nodes[0]==nodes[1])throw std::runtime_error("T repeated participants");Scene s;s.o=o;s.root=root;s.nodes=nodes;auto&tmp=shared.scratch[o];if(tmp.next_epoch())++epoch_resets;
  for(int i=0;i<2;++i){if(value(g,s,i,root)<=0)throw std::runtime_error("T root absent");const int v=o?g.nr+nodes[i]:nodes[i];for(int id:g.adj[v]){++scan_visits;const auto&ed=g.edges[id];const int c=o?ed.r:ed.c;
   if(tmp.stamp[c]!=tmp.epoch){tmp.stamp[c]=tmp.epoch;tmp.mask[c]=0;tmp.first_weight[c]=ed.w;tmp.touched.push_back(c);}tmp.mask[c]|=uint8_t(1u<<i);}}
  for(int c:tmp.touched)if(c!=root&&__builtin_popcount(unsigned(tmp.mask[c]))==1){s.columns.push_back(c);s.owners.push_back(__builtin_ctz(unsigned(tmp.mask[c])));s.weights.push_back(tmp.first_weight[c]);}
  return s;
 }
 std::vector<U> eligible_indices(const Scene&s){
  std::unordered_map<I,std::array<U,2>>counts;counts.reserve(s.columns.size());for(U j=0;j<s.columns.size();++j)++counts[s.weights[j]][s.owners[j]];
  U classes=0;for(const auto&item:counts)classes+=item.second[0]>0&&item.second[1]>0;
  std::vector<U>indices;indices.reserve(s.columns.size());for(U j=0;j<s.columns.size();++j){const auto&count=counts.at(s.weights[j]);if(count[0]&&count[1])indices.push_back(j);}
  eligible_records_total+=indices.size();eligible_classes_total+=classes;max_eligible_records=std::max<U>(max_eligible_records,indices.size());return indices;
 }
 Class compile(const Scene&s,U private_index){
  if(private_index>=s.columns.size())throw std::runtime_error("T private seed outside pool");Class p;p.scene=s;p.weight=s.weights[private_index];
  for(U j=0;j<s.columns.size();++j)if(s.weights[j]==p.weight){p.columns.push_back(s.columns[j]);p.owners.push_back(s.owners[j]);p.quota+=s.owners[j]==0;}
  if(p.weight<=0||p.columns.empty())throw std::runtime_error("T invalid weight class");return p;
 }
 template<class Pick>std::vector<uint8_t> draw_first(U q,U k,Pick&&pick){
  if(k>q)throw std::runtime_error("T invalid quota");const bool complement=k>q-k;const U m=std::min(k,q-k);std::unordered_set<U>chosen;chosen.reserve(size_t(m));
  for(U j=q-m;j<q;++j){U index=pick(j+1);if(index>j)throw std::runtime_error("T Floyd index");if(chosen.count(index))index=j;chosen.insert(index);++subset_draws;}
  std::vector<uint8_t>first(q,complement?1:0);for(U index:chosen)first[index]=complement?0:1;return first;
 }
 bool commit(Engine&e,Graph&g,const Class&p,const std::vector<uint8_t>&first){
  if(first.size()!=p.columns.size())throw std::runtime_error("T subset width");U count=0;bool changed=false;for(U j=0;j<first.size();++j)count+=first[j]!=0;if(count!=p.quota)throw std::runtime_error("T subset quota");
  for(U j=0;j<first.size();++j){const int owner=first[j]?0:1;if(owner==p.owners[j])continue;put(g,p.scene,p.owners[j],p.columns[j],0);put(g,p.scene,owner,p.columns[j],p.weight);++moved_labels;changed=true;}
  if(changed){++changes;++e.stat.changed_outer;}return changed;
 }
 bool step(Engine&e,Graph&g){
  ++calls;++e.stat.work;if(g.D)throw std::runtime_error("T requires exact margins");const int o=choose_orientation(e.rng,g);const auto&pool=roots[o];if(pool.empty()){++empty_roots;return false;}
  const int root=pool[e.rng.below(pool.size())],rv=o?root:g.nr+root;const auto&adj=g.adj[rv];const U d=adj.size();if(d<2)throw std::runtime_error("T fixed root degree changed");
  const U ia=e.rng.below(d);U ib=e.rng.below(d-1);if(ib>=ia)++ib;const auto&a=g.edges[adj[ia]];const auto&b=g.edges[adj[ib]];Scene scene=make_scene(g,o,root,{o?a.c:a.r,o?b.c:b.r});private_total+=scene.columns.size();
  if(scene.columns.empty()){++empty_private;return false;}U private_index;if(nontrivial){auto eligible=eligible_indices(scene);if(eligible.empty()){++empty_eligible;return false;}private_index=eligible[e.rng.below(eligible.size())];}else private_index=e.rng.below(scene.columns.size());Class p=compile(scene,private_index);class_total+=p.columns.size();max_class=std::max<U>(max_class,p.columns.size());singletons+=p.quota==0||p.quota==p.columns.size();
  return commit(e,g,p,draw_first(p.columns.size(),p.quota,[&](U n){return e.rng.below(n);}));
 }
};

struct GlobalWeightClassTrade {
 using Scene=WeightClassTrade::Scene;using Class=WeightClassTrade::Class;
 Graph* graph=nullptr;bool active=false;
 std::vector<std::unordered_map<I,std::vector<int>>> node_groups;
 std::unordered_map<U,std::array<U,2>> positions;
 U calls=0,changes=0,no_edges=0,singleton_global_class=0,same_node_holds=0,seed_same_object=0;
 U scan_visits=0,private_total=0,max_private=0,singleton_private=0,subset_draws=0,moved_labels=0;
 U index_updates=0,index_adds=0,index_removes=0,index_initial_entries=0,index_peak_entries=0,index_checks=0,index_checked_entries=0;
 U node_group_count=0,node_group_peak=0;
 double index_build_cpu_seconds=0,cpu_seconds=0;
 void add(int r,int c,I w){
  const U key=cellkey(r,c);if(positions.count(key))throw std::runtime_error("GT duplicate position");
  node_group_count+=!node_groups[r].count(w);node_group_count+=!node_groups[graph->nr+c].count(w);node_group_peak=std::max(node_group_peak,node_group_count);
  auto&rr=node_groups[r][w];auto&cc=node_groups[graph->nr+c][w];positions.emplace(key,std::array<U,2>{U(rr.size()),U(cc.size())});rr.push_back(c);cc.push_back(r);++index_adds;index_peak_entries=std::max<U>(index_peak_entries,positions.size());
 }
 void remove(int r,int c,I w){
  const U key=cellkey(r,c);auto it=positions.find(key);if(it==positions.end())throw std::runtime_error("GT missing position");const auto pos=it->second;
  auto&rm=node_groups[r];auto ri=rm.find(w);if(ri==rm.end()||pos[0]>=ri->second.size()||ri->second[pos[0]]!=c)throw std::runtime_error("GT row stale index");auto&rr=ri->second;const int lastc=rr.back();rr[pos[0]]=lastc;positions.at(cellkey(r,lastc))[0]=pos[0];rr.pop_back();if(rr.empty()){rm.erase(ri);--node_group_count;}
  auto&cm=node_groups[graph->nr+c];auto ci=cm.find(w);if(ci==cm.end()||pos[1]>=ci->second.size()||ci->second[pos[1]]!=r)throw std::runtime_error("GT column stale index");auto&cc=ci->second;const int lastr=cc.back();cc[pos[1]]=lastr;positions.at(cellkey(lastr,c))[1]=pos[1];cc.pop_back();if(cc.empty()){cm.erase(ci);--node_group_count;}positions.erase(it);++index_removes;
 }
 static void hook(void*context,int r,int c,I old,I now){auto*self=static_cast<GlobalWeightClassTrade*>(context);++self->index_updates;if(old)self->remove(r,c,old);if(now)self->add(r,c,now);}
 void initialize(Graph&g,bool enable){
  if(!enable)return;if(g.mutation_hook)throw std::runtime_error("GT Graph hook already installed");if(!g.maintain_weight_groups)throw std::runtime_error("GT needs legacy global groups");const double start=process_cpu();graph=&g;active=true;node_groups.resize(g.nr+g.nc);positions.reserve(g.edges.size()*2+64);for(const auto&e:g.edges)add(e.r,e.c,e.w);index_initial_entries=positions.size();g.mutation_context=this;g.mutation_hook=&hook;index_build_cpu_seconds=process_cpu()-start;
 }
 void check(const Graph&g,bool allow_other_hook=false){
  if(!active){if(!positions.empty()||(!allow_other_hook&&g.mutation_hook))throw std::runtime_error("GT disabled index exists");return;}
  ++index_checks;if(positions.size()!=g.edges.size())throw std::runtime_error("GT index cardinality");
  for(const auto&e:g.edges){++index_checked_entries;const auto p=positions.at(cellkey(e.r,e.c));const auto&rr=node_groups[e.r].at(e.w);const auto&cc=node_groups[g.nr+e.c].at(e.w);if(p[0]>=rr.size()||p[1]>=cc.size()||rr[p[0]]!=e.c||cc[p[1]]!=e.r)throw std::runtime_error("GT index inconsistent with graph");}
  U total=0;for(const auto&node:node_groups)for(const auto&b:node){total+=b.second.size();if(b.second.empty())throw std::runtime_error("GT empty node group retained");}if(total!=2*g.edges.size())throw std::runtime_error("GT node group excess");
 }
 Class compile(const Graph&g,int o,int a,int b,I w){
  if(!active||o<0||o>1||a==b||w<=0)throw std::runtime_error("GT invalid descriptor");Class p;p.scene.o=o;p.scene.nodes={a,b};std::sort(p.scene.nodes.begin(),p.scene.nodes.end());p.scene.root=-1;p.weight=w;
  for(int owner=0;owner<2;++owner){const int node=p.scene.nodes[owner],other=p.scene.nodes[1-owner],v=o?g.nr+node:node;const auto it=node_groups[v].find(w);if(it==node_groups[v].end())continue;
   for(int object:it->second){++scan_visits;const I overlap=o?g.value(object,other):g.value(other,object);if(overlap>0)continue;p.columns.push_back(object);p.owners.push_back(owner);p.quota+=owner==0;}}
  std::vector<U>order(p.columns.size());for(U j=0;j<order.size();++j)order[j]=j;std::sort(order.begin(),order.end(),[&](U x,U y){return p.columns[x]<p.columns[y];});std::vector<int>columns,owners;columns.reserve(order.size());owners.reserve(order.size());for(U j:order){columns.push_back(p.columns[j]);owners.push_back(p.owners[j]);}p.columns.swap(columns);p.owners.swap(owners);return p;
 }
 template<class Pick>std::vector<uint8_t> draw_first(U q,U k,Pick&&pick){
  if(k>q)throw std::runtime_error("GT invalid quota");const bool complement=k>q-k;const U m=std::min(k,q-k);std::unordered_set<U>chosen;chosen.reserve(size_t(m));
  for(U j=q-m;j<q;++j){U index=pick(j+1);if(index>j)throw std::runtime_error("GT Floyd index");if(chosen.count(index))index=j;chosen.insert(index);++subset_draws;}
  std::vector<uint8_t>first(q,complement?1:0);for(U index:chosen)first[index]=complement?0:1;return first;
 }
 bool commit(Engine&e,Graph&g,const Class&p,const std::vector<uint8_t>&first){
  if(first.size()!=p.columns.size())throw std::runtime_error("GT subset width");U count=0;for(uint8_t x:first)count+=x!=0;if(count!=p.quota)throw std::runtime_error("GT quota");bool differs=false;
  for(U j=0;j<first.size();++j){const int owner=first[j]?0:1;if(owner==p.owners[j])continue;WeightClassTrade::put(g,p.scene,p.owners[j],p.columns[j],0);WeightClassTrade::put(g,p.scene,owner,p.columns[j],p.weight);++moved_labels;differs=true;}
  if(differs){++changes;++e.stat.changed_outer;}return differs;
 }
 bool step(Engine&e,Graph&g){
  if(!active)throw std::runtime_error("GT inactive step");++calls;++e.stat.work;if(g.D)throw std::runtime_error("GT requires exact margins");const int o=choose_orientation(e.rng,g);if(g.edges.empty()){++no_edges;return false;}
  const Edge seed=g.edges[e.rng.below(g.edges.size())];const auto&group=g.weight_groups.at(seed.w);const U q=group.cells.size();if(q<2){++singleton_global_class;return false;}
  const U oldpos=group.position.at(cellkey(seed.r,seed.c));U pick=e.rng.below(q-1);if(pick>=oldpos)++pick;const U key=group.cells[pick];const int r=int(key>>32),c=int(uint32_t(key));if(g.value(r,c)!=seed.w)throw std::runtime_error("GT global group stale");
  const int a=o?seed.c:seed.r,b=o?c:r;seed_same_object+=(o?seed.r:seed.c)==(o?r:c);if(a==b){++same_node_holds;return false;}Class p=compile(g,o,a,b,seed.w);private_total+=p.columns.size();max_private=std::max<U>(max_private,p.columns.size());if(!p.quota||p.quota==p.columns.size()){++singleton_private;return false;}
  return commit(e,g,p,draw_first(p.columns.size(),p.quota,[&](U n){return e.rng.below(n);}));
 }
};

struct MinimalAnchorWindow {
 static int vertex(const Graph&g,int o,int actor){return o?g.nr+actor:actor;}
 static int root_edge(const Graph&g,int o,int actor,int root){return o?g.find(root,actor):g.find(actor,root);}
 static int partner(const Graph&g,int o,int actor,int root,U reduced_index){
  const int id=root_edge(g,o,actor,root);if(id<0)throw std::runtime_error("minimal root edge missing");
  const auto&adj=g.adj[vertex(g,o,actor)];if(adj.size()<2||reduced_index>=adj.size()-1)throw std::runtime_error("minimal partner index");
  const auto&edge=g.edges[id];const U rootpos=o?edge.pc:edge.pr;U pos=reduced_index;if(pos>=rootpos)++pos;
  const auto&other=g.edges[adj[pos]];return o?other.r:other.c;
 }
 static std::vector<int> make(const Graph&g,int o,int a,int b,int root,U ia,U ib){
  const int x=partner(g,o,a,root,ia),y=partner(g,o,b,root,ib);
  std::vector<int>out{root,x,y};std::sort(out.begin(),out.end());out.erase(std::unique(out.begin(),out.end()),out.end());return out;
 }
};

#include "whole_private_conditional.hpp"
#include "cohort_eligible_root_index.hpp"
#include "cohort_conditional.hpp"
#include "shared_weight_heatbath.hpp"
#include "residual_cycle_refresh.hpp"
#include "guided_support_cycle.hpp"
#include "capacity_guided_support_cycle.hpp"

#include "surplus_local_selector.hpp"
static SurplusLocalSelector* local_pair_selector=nullptr;
struct CountedDelayedFallback {
 U MA_calls=0,MA_degenerate_holds=0,MA_degree_one_holds=0,MA_windows=0,MA_neighbor_draws=0,MA_width_two=0,MA_width_three=0,MA_max_columns=0,MA_root_shared_interval=0,MA_two_private_owner=0,MA_mixed_shared_private=0,MA_two_shared=0,MA_changes=0,MA_FSDP_attempts=0,MA_FSDP_calls=0,MA_IE_calls=0;
 double MA_FSDP_build_cpu_seconds=0,MA_FSDP_draw_cpu_seconds=0;
 U FSDP_attempts=0,FSDP_calls=0,FSDP_resource_failures=0,FSDP_nontrivial=0,FSDP_changes=0,FSDP_flipped=0,FSDP_total_cells=0,FSDP_max_cells=0,FSDP_max_estimated_bytes=0,FSDP_max_count_bits=0,FSDP_guard_cell=0,FSDP_guard_memory=0,FSDP_guard_allocation=0;
 double FSDP_build_cpu_seconds=0,FSDP_draw_cpu_seconds=0;
 struct Descriptor {int o=0,a=-1,b=-1,anchor=-1;std::vector<int>columns;U old_union=0;bool degenerate=false,global_labels=false;};
 U A_holds=0,J_proposals=0,J_changed_proposals=0,J_accepts=0,J_rejects=0,reverse_invalid=0,reverse_zero_stay=0;
 U accepted_J_changes=0,self_count_calls=0,reverse_count_calls=0,rollback_cells=0;
 std::string mode,owner_update;CertifiedMatchingJointKernel&joint;bool certified_identity=false;U certified_dispatches=0;std::string window;U global_small_calls=0;bool disable_A=false;U disabled_A_dispatches=0,local_identity_holds=0;std::string joint_policy;U certified_A_only_calls=0;
 explicit CountedDelayedFallback(std::string m,std::string owner,CertifiedMatchingJointKernel&j,bool identity=false,std::string win="union",bool noA=false,std::string policy="certified"):mode(std::move(m)),owner_update(std::move(owner)),joint(j),certified_identity(identity),window(std::move(win)),disable_A(noA),joint_policy(std::move(policy)){}
 static I value(const Graph&g,const Descriptor&d,int node,int col){return d.o?g.value(col,node):g.value(node,col);}
 static int side_vertex(const Graph&g,const Descriptor&d,int node){return d.o?g.nr+node:node;}
 static std::vector<int> union_columns(const Graph&g,const Descriptor&d){std::vector<int>all;for(int node:{d.a,d.b})for(int id:g.adj[side_vertex(g,d,node)])all.push_back(d.o?g.edges[id].r:g.edges[id].c);std::sort(all.begin(),all.end());all.erase(std::unique(all.begin(),all.end()),all.end());return all;}
 static void put(Graph&g,const Descriptor&d,int node,int col,I w){if(d.o)g.set_raw(col,node,w);else g.set_raw(node,col,w);}
 static void rows(const Graph&g,const Descriptor&d,std::vector<I>&a,std::vector<I>&b){a.clear();b.clear();for(int c:d.columns){a.push_back(value(g,d,d.a,c));b.push_back(value(g,d,d.b,c));}}

 static mpq_class descriptor_ratio(const Graph&g,const Descriptor&d,int cap,bool&valid){
  valid=true;if(d.degenerate||d.global_labels)return 1;auto all=union_columns(g,d);const U k=d.columns.size();
  if(k!=std::min<U>(cap,all.size())){valid=false;return 0;}
  for(int c:d.columns)if(!std::binary_search(all.begin(),all.end(),c)){valid=false;return 0;}
  const U forced=d.anchor>=0;
  if(forced&&(!(value(g,d,d.a,d.anchor)>0)||!(value(g,d,d.b,d.anchor)>0))){valid=false;return 0;}
  return rational(choose_exact(d.old_union-forced,k-forced),choose_exact(all.size()-forced,k-forced));
 }
 bool step(Engine&e,Graph&g){
  if(disable_A){++disabled_A_dispatches;if(mode=="none"||(joint_policy=="certified"&&!certified_identity)){++local_identity_holds;++e.stat.work;return false;}
   ++J_proposals;const bool changed=joint.step(e,g);J_changed_proposals+=changed;++J_accepts;accepted_J_changes+=changed;return changed;}
  if(certified_identity){++certified_dispatches;if(mode=="none"){++A_holds;++e.stat.work;return false;}
   ++J_proposals;const bool changed=joint.step(e,g);J_changed_proposals+=changed;++J_accepts;accepted_J_changes+=changed;return changed;}
  ++e.stat.work;++e.stat.block_calls;const auto select_start=Clock::now();Descriptor d;
  d.o=e.opt.orientation=="row"?0:e.opt.orientation=="col"?1:choose_orientation(e.rng,g);
  const int n=d.o?g.nc:g.nr;std::string pair=e.opt.block_mode;if(pair=="mixed")pair=e.rng.below(2)?"anchor":"uniform";
  if(local_pair_selector){++e.stat.block_wedge_pairs;if(!local_pair_selector->select(e,g,d.o,d.a,d.b,d.anchor))d.degenerate=true;}
  else if(n<2)d.degenerate=true;
  else if(pair=="uniform"){++e.stat.block_uniform_pairs;d.a=int(e.rng.below(n));d.b=int(e.rng.below(n-1));if(d.b>=d.a)++d.b;}
  else{++e.stat.block_wedge_pairs;const auto&p=e.wedge_prefix[d.o];const U total=p.empty()?0:p.back();
   if(!total){d.degenerate=true;++e.stat.block_empty_wedge;}
   else{d.anchor=int(std::upper_bound(p.begin(),p.end(),e.rng.below(total))-p.begin());const int v=d.o?d.anchor:g.nr+d.anchor;const auto&adj=g.adj[v];
    U ia=e.rng.below(adj.size()),ib=e.rng.below(adj.size()-1);if(ib>=ia)++ib;
    d.a=d.o?g.edges[adj[ia]].c:g.edges[adj[ia]].r;d.b=d.o?g.edges[adj[ib]].c:g.edges[adj[ib]].r;
   }
  }
  if(minimal_anchor_window){++MA_calls;if(d.degenerate)++MA_degenerate_holds;}
  std::unique_ptr<FastCountedBlock> cb;std::unique_ptr<FixedSupportSuffixDP> fsdp;std::vector<I>a,b;
  if(!d.degenerate){if(d.a>d.b)std::swap(d.a,d.b);const int opposite=d.o?g.nr:g.nc;
   if(minimal_anchor_window){
    const U da=g.adj[side_vertex(g,d,d.a)].size(),db=g.adj[side_vertex(g,d,d.b)].size();
    if(da<2||db<2){++MA_degree_one_holds;d.degenerate=true;}
    else{
     const U ia=e.rng.below(da-1),ib=e.rng.below(db-1);d.columns=MinimalAnchorWindow::make(g,d.o,d.a,d.b,d.anchor,ia,ib);
     ++MA_windows;MA_neighbor_draws+=2;MA_max_columns=std::max<U>(MA_max_columns,d.columns.size());
     if(d.columns.size()==2){++MA_width_two;++MA_root_shared_interval;}
     else{++MA_width_three;int shared=0;for(int c:d.columns)if(c!=d.anchor)shared+=(value(g,d,d.a,c)>0&&value(g,d,d.b,c)>0);if(shared==0)++MA_two_private_owner;else if(shared==1)++MA_mixed_shared_private;else ++MA_two_shared;}
    }
   }else{
    d.global_labels=window=="global-small"&&opposite<=e.opt.block_width;
    if(d.global_labels){++global_small_calls;for(int c=0;c<opposite;++c)d.columns.push_back(c);}
    auto all=union_columns(g,d);d.old_union=all.size();
    e.stat.block_scan_neighbor_visits+=g.adj[side_vertex(g,d,d.a)].size()+g.adj[side_vertex(g,d,d.b)].size();
    const int width=std::min<int>(e.opt.block_width,all.size());if(!d.global_labels){
    if(d.anchor>=0){d.columns.push_back(d.anchor);auto it=std::lower_bound(all.begin(),all.end(),d.anchor);if(it==all.end()||*it!=d.anchor)throw std::runtime_error("sampled anchor not in union");all.erase(it);}
    const int remaining=width-int(d.columns.size());for(int k=0;k<remaining;++k){int z=k+int(e.rng.below(all.size()-k));std::swap(all[k],all[z]);d.columns.push_back(all[k]);}std::sort(d.columns.begin(),d.columns.end());}
   }
   if(!d.degenerate){
   rows(g,d,a,b);
   if(fixed_support_dp&&joint_policy=="certified"&&std::equal(a.begin(),a.end(),b.begin(),[](I x,I y){return(x>0)==(y>0);})){
    ++FSDP_attempts;MA_FSDP_attempts+=minimal_anchor_window;const double ts=process_cpu();fsdp=std::make_unique<FixedSupportSuffixDP>(a,b);const double dt=process_cpu()-ts;FSDP_build_cpu_seconds+=dt;if(minimal_anchor_window)MA_FSDP_build_cpu_seconds+=dt;
    if(fsdp->active){++FSDP_calls;MA_FSDP_calls+=minimal_anchor_window;FSDP_nontrivial+=fsdp->count()>Big(1);FSDP_flipped+=fsdp->flipped;FSDP_total_cells+=fsdp->dp_cells;FSDP_max_cells=std::max(FSDP_max_cells,fsdp->dp_cells);FSDP_max_estimated_bytes=std::max(FSDP_max_estimated_bytes,fsdp->estimated_bytes);FSDP_max_count_bits=std::max<U>(FSDP_max_count_bits,fsdp->count().bits());e.stat.block_nontrivial+=fsdp->count()>Big(1);}
    else{FSDP_resource_failures+=fsdp->resource_failed;FSDP_guard_cell+=fsdp->guard_reason=="dp_cell_budget";FSDP_guard_memory+=fsdp->guard_reason=="dp_memory_budget";FSDP_guard_allocation+=fsdp->guard_reason=="allocation_failed";fsdp.reset();}
   }
   if(!fsdp){MA_IE_calls+=minimal_anchor_window;cb=std::make_unique<FastCountedBlock>(a,b,&e.stat);e.stat.block_nontrivial+=cb->nontrivial();e.stat.block_support_nontrivial+=cb->support_count()>1;}
   }
  }
  e.stat.block_select_nanoseconds+=std::chrono::duration_cast<std::chrono::nanoseconds>(Clock::now()-select_start).count();
  bool changed=false,support_changed=false;
  if(cb||fsdp){std::pair<std::vector<I>,std::vector<I>>draw;
   if(fsdp){const double ts=process_cpu();draw=fsdp->draw(e.rng);const double dt=process_cpu()-ts;FSDP_draw_cpu_seconds+=dt;if(minimal_anchor_window)MA_FSDP_draw_cpu_seconds+=dt;}
   else if(owner_update=="heatbath")draw=cb->draw(e.rng);else{OwnerRandomAdapter random{e.rng};draw=cb->draw_metropolis_refresh(random);}
   for(size_t k=0;k<d.columns.size();++k){changed|=draw.first[k]!=a[k]||draw.second[k]!=b[k];support_changed|=(draw.first[k]>0)!=(a[k]>0)||(draw.second[k]>0)!=(b[k]>0);
    put(g,d,d.a,d.columns[k],draw.first[k]);put(g,d,d.b,d.columns[k],draw.second[k]);}
  }
  MA_changes+=minimal_anchor_window&&changed;FSDP_changes+=bool(fsdp)&&changed;e.stat.block_changed+=changed;e.stat.block_support_changed+=support_changed;e.stat.changed_outer+=changed;
  if(joint_policy=="certified")++certified_A_only_calls;if(changed)return true;++A_holds;if(mode=="none"||joint_policy=="certified")return false;
  ++J_proposals;const U old_changed=e.stat.changed_outer,old_jchanged=joint.changed,old_fchanged=joint.fallback_changed,old_mchanged=joint.matching_changed;
  const U hash1=g.hash1,hash2=g.hash2;bool proposed=joint.step(e,g);J_changed_proposals+=proposed;
  if(!proposed){++J_accepts;return false;}
  bool accept=true;
  if(mode=="corrected"){
   mpq_class rx=1;if(cb){++self_count_calls;rx=owner_self_probability(*cb,owner_update=="heatbath");if(rx<=0)throw std::runtime_error("observed A hold with zero exact probability");}
   bool valid;const mpq_class sr=descriptor_ratio(g,d,e.opt.block_width,valid);
   if(!valid){++reverse_invalid;accept=false;}
   else{mpq_class ry=1;if(!d.degenerate){std::vector<I>ya,yb;rows(g,d,ya,yb);FastCountedBlock reverse(ya,yb,&e.stat);++reverse_count_calls;ry=owner_self_probability(reverse,owner_update=="heatbath");}
    if(ry==0)++reverse_zero_stay;accept=exact_accept(e.rng,sr*ry/rx);}
  }
  if(accept){++J_accepts;++accepted_J_changes;return true;}
  ++J_rejects;rollback_cells+=joint.undo.size();joint.rollback_journal(g);e.stat.changed_outer=old_changed;joint.changed=old_jchanged;joint.fallback_changed=old_fchanged;joint.matching_changed=old_mchanged;
  if(g.hash1!=hash1||g.hash2!=hash2||g.D)throw std::runtime_error("fallback rollback failed");return false;
 }
};

#include "strict_star_observation.hpp"
#include "whole_class_triple_heatbath.hpp"
#include "disconnected_bundle_fast.hpp"
#include "disconnected_four_bundle.hpp"
#include "bundle_max_four.hpp"
#include "overlap_bundle_counted_heatbath.hpp"
#include "ledger_bundle_heatbath.hpp"
#include "cached_ledger_bundle_heatbath.hpp"
#include "certified_leaf_bundle_heatbath.hpp"
#include "certified_coverage_priority.hpp"

#ifndef BALANCED_V10_LIBRARY_ONLY
int main(int argc,char**argv){try{
 std::map<std::string,std::string>a;for(int k=1;k<argc;k+=2){if(k+1==argc||!a.emplace(argv[k],argv[k+1]).second)throw std::runtime_error("flags require unique values");}
 auto get=[&](std::string k,std::string d){return a.count(k)?a.at(k):d;};
 const std::set<std::string>allowed={"--local-surplus-selector","--leaf-certified","--ledger-cache","--ledger-update","--ledger-joint","--overlap-bundle","--overlap-coverage-only","--bundle-max-four","--disconnected-four-bundle","--bundle-coverage-only","--coverage-certified-priority","--disconnected-bundle","--coverage-first-lazy","--analysis-cpu-millis","--analysis-cpu-check","--coverage-soft-mode","--coverage-degree-power","--coverage-rho-den","--coverage-add-bp","--coverage-hazard-rule","--whole-class-core-start","--legacy-local-bypass","--whole-class-triple-heatbath","--capacity-cycle","--capacity-cycle-weighted-first","--global-weight-class-bulk-nonself","--cycle-core-filter","--cycle-nontrivial-draw","--reference-input","--convergence-every","--ablation-module","--global-weight-class-bulk","--coverage-per-actor-auxiliary","--coverage-weighted-column-extra-lazy","--coverage-weighted-column-axis","--coverage-weighted-column-gibbs","--coverage-support-cap","--global-equal-weight-selection","--unified-private-label-update","--unified-private-profile-update","--unified-second-public","--unified-private-pair","--allpostburn-sigma-histogram","--two-weight-profile-update","--budget-compatible-mode","--budget-compatible-complement","--pair-specific-complement","--wide-complement-proposal","--near-weight-mode","--productive-triple","--root-excess-triple-guide","--near-weight-private-buffer","--sampled-private-buffer-without-replacement","--sampled-private-buffer","--disable-factorized-M","--strict-star-iid","--strict-star-profile-update","--strict-star-full-owner-observer","--input","--out","--queries","--seed","--outer","--burn","--check-every","--trace-every","--fallback-mode","--coverage-bp","--pair","--owner-update","--histogram","--cycle-every","--orbit-every","--anchor-lazy","--design","--cycle-compose","--certificate-skip","--window","--local-steps","--disable-A","--joint-policy","--composition","--matching-sweep","--regular-iid","--balanced-local","--balanced-private-per-person","--weight-class-trade","--weight-class-nontrivial","--regular-no-rejection","--cycle-when-maxdegree-two","--global-weight-class-trade","--typed-local-compile","--typed-mode","--matching-xor","--factorized-local-compile","--factorized-mode","--factorized-profile","--node-weighted-orientation","--global-small-iid","--fixed-support-dp","--global-equal-weight-switch","--disable-factorized-joint","--global-bridge-swap","--minimal-anchor-window","--dynamic-support-bitset-scene","--two-weight-complement","--global-degree-work-batch","--two-weight-scaled-counts","--two-weight-slack-certificate","--global-representation-work-batch","--global-weight-class-balanced","--unlabeled-structure-trace","--whole-private-conditional","--whole-private-reuse-layout","--shared-weight-heatbath","--shared-weight-heatbath-compose","--shared-weight-heatbath-intersection","--residual-cycle-refresh","--residual-cycle-delta","--cohort-two-class","--cohort-root-selector","--cohort-profile-update","--cohort-ledger-compiler","--cohort-ledger-cache","--coverage-compose","--cohort-local-private"};
 const U coverage_priority_requested=probe_unsigned_v12(get("--coverage-certified-priority","0"),"coverage-certified-priority");if(coverage_priority_requested>1)throw std::runtime_error("invalid certified priority flag");
 const U disconnected_bundle_requested=probe_unsigned_v12(get("--disconnected-bundle","0"),"disconnected-bundle");if(disconnected_bundle_requested>1)throw std::runtime_error("invalid disconnected-bundle flag");
 const U disconnected_four_bundle_requested=probe_unsigned_v12(get("--disconnected-four-bundle","0"),"disconnected-four-bundle");if(disconnected_four_bundle_requested>1)throw std::runtime_error("invalid D4 flag");
 const U bundle_coverage_only_requested=probe_unsigned_v12(get("--bundle-coverage-only","0"),"bundle-coverage-only");if(bundle_coverage_only_requested>1||(bundle_coverage_only_requested&&!disconnected_bundle_requested&&!disconnected_four_bundle_requested))throw std::runtime_error("coverage-only bundle requires D3 or D4 and binary flag");U bundle_coverage_selected_rounds=0;
 if(disconnected_four_bundle_requested&&(!bundle_coverage_only_requested||coverage_priority_requested))throw std::runtime_error("D4 requires coverage-only and forbids the D3-only priority certificate; D3 may be ablated");
 const U bundle_max_four_requested=probe_unsigned_v12(get("--bundle-max-four","0"),"bundle-max-four");if(bundle_max_four_requested>1||(bundle_max_four_requested&&(!disconnected_bundle_requested||!disconnected_four_bundle_requested||!bundle_coverage_only_requested||coverage_priority_requested)))throw std::runtime_error("max-four requires D3 and D4, coverage-only, and priority0");
 const U OB_requested=probe_unsigned_v12(get("--overlap-bundle","0"),"overlap-bundle");if(OB_requested>1||(OB_requested&&(disconnected_bundle_requested||disconnected_four_bundle_requested||bundle_max_four_requested||coverage_priority_requested)))throw std::runtime_error("overlap bundle requires binary flag and old D3/D4/BD/priority0");
 const U OB_coverage_only_requested=probe_unsigned_v12(get("--overlap-coverage-only","0"),"overlap-coverage-only");if(OB_coverage_only_requested>1||(OB_coverage_only_requested&&!OB_requested))throw std::runtime_error("overlap coverage-only requires overlap1 and binary flag");
 const U WCT_requested=probe_unsigned_v12(get("--whole-class-triple-heatbath","0"),"whole-class-triple-heatbath");if(WCT_requested>1)throw std::runtime_error("invalid WCT flag");
 const U JL_requested=probe_unsigned_v12(get("--ledger-joint","0"),"ledger-joint");if(JL_requested>1||(JL_requested&&(WCT_requested||disconnected_bundle_requested||disconnected_four_bundle_requested||bundle_max_four_requested||OB_requested||coverage_priority_requested)))throw std::runtime_error("ledger joint requires binary flag and old B/D/OB/priority0");const U JL_cache_requested=probe_unsigned_v12(get("--ledger-cache","0"),"ledger-cache"),JL_update_enabled=probe_unsigned_v12(get("--ledger-update","1"),"ledger-update");if(JL_cache_requested>1||JL_update_enabled>1||(JL_cache_requested&&!JL_requested)||(!JL_update_enabled&&!JL_requested))throw std::runtime_error("ledger cache/update require binary flags and ledger-joint1 for cache1 or update0");const U LF_requested=probe_unsigned_v12(get("--leaf-certified","0"),"leaf-certified");if(LF_requested>1||(LF_requested&&(JL_requested||WCT_requested||disconnected_bundle_requested||disconnected_four_bundle_requested||bundle_max_four_requested||OB_requested||coverage_priority_requested)))throw std::runtime_error("leaf certified requires binary flag, ledger-joint0 and oldB/D/OB/priority0");U LF_ordinary_dispatches=0,LF_coverage_dispatches=0,LF_inactive_ordinary_holds=0,LF_inactive_coverage_holds=0,LF_skipped_W_calls=0;U JL_ordinary_dispatches=0,JL_coverage_dispatches=0,JL_disabled_dispatches=0;
 const U legacy_local_bypass_requested=probe_unsigned_v12(get("--legacy-local-bypass","0"),"legacy-local-bypass");if(legacy_local_bypass_requested>1|| (legacy_local_bypass_requested&&!WCT_requested))throw std::runtime_error("legacy bypass requires B");U legacy_local_bypass_calls=0;const U WCT_core_start_requested=probe_unsigned_v12(get("--whole-class-core-start","0"),"whole-class-core-start");if(WCT_core_start_requested>1|| (WCT_core_start_requested&&!WCT_requested))throw std::runtime_error("core start requires B");
 for(auto&p:a)if(!allowed.count(p.first))throw std::runtime_error("unknown flag "+p.first);
 std::string input=get("--input",""),out=get("--out",""),queries=get("--queries",""),pair=get("--pair","uniform"),mode=get("--fallback-mode","corrected"),owner=get("--owner-update","heatbath");
 U seed=probe_unsigned_v12(get("--seed",std::to_string(0x78c3d7e7ULL)),"seed"),N=probe_unsigned_v12(get("--outer","25600"),"outer"),B=probe_unsigned_v12(get("--burn","5120"),"burn"),check=probe_unsigned_v12(get("--check-every","100000"),"check"),trace=probe_unsigned_v12(get("--trace-every","40"),"trace"),coverage=probe_unsigned_v12(get("--coverage-bp","50"),"coverage"),hist=probe_unsigned_v12(get("--histogram","0"),"histogram");
 const U weighted_column_gibbs_requested=probe_unsigned_v12(get("--coverage-weighted-column-gibbs","0"),"coverage-weighted-column-gibbs");if(weighted_column_gibbs_requested>1)throw std::runtime_error("invalid coverage-weighted-column-gibbs flag");
 const U coverage_auxiliary=probe_unsigned_v12(get("--coverage-per-actor-auxiliary","0"),"coverage-per-actor-auxiliary");
 if(coverage_auxiliary>1||coverage_auxiliary&&!weighted_column_gibbs_requested)throw std::runtime_error("invalid per-actor auxiliary request");
 const U coverage_extra_lazy=probe_unsigned_v12(get("--coverage-weighted-column-extra-lazy","1"),"coverage-weighted-column-extra-lazy");
 if(coverage_extra_lazy>1)throw std::runtime_error("invalid coverage-weighted-column-extra-lazy");
 if(!coverage_extra_lazy&&!weighted_column_gibbs_requested)throw std::runtime_error("intrinsic-hold R requires coverage-weighted-column-gibbs 1");
 const std::string coverage_axis_policy=get("--coverage-weighted-column-axis","fair");
 if(coverage_axis_policy!="fair"&&coverage_axis_policy!="input_bound")throw std::runtime_error("invalid coverage-weighted-column-axis");
 if(coverage_axis_policy=="input_bound"&&!weighted_column_gibbs_requested)throw std::runtime_error("input_bound axis requires coverage-weighted-column-gibbs 1");
 const U coverage_cap_requested=probe_unsigned_v12(get("--coverage-support-cap","0"),"coverage-support-cap");if(coverage_cap_requested>1)throw std::runtime_error("invalid coverage-support-cap flag");
 const std::string window=get("--window","union");if(window!="union"&&window!="global-small")throw std::runtime_error("window");if(window=="global-small"&&pair!="uniform")throw std::runtime_error("global-small window requires uniform pair selection");const U local_steps=probe_unsigned_v12(get("--local-steps","1"),"local-steps");if(!local_steps)throw std::runtime_error("local-steps must be positive");
 const std::string policy=get("--joint-policy","certified"),composition=get("--composition","CAC");if(policy!="certified"&&policy!="delayed")throw std::runtime_error("joint-policy");if(composition!="ACA"&&composition!="CAC"&&composition!="none"&&composition!="MC"&&composition!="CM")throw std::runtime_error("composition");
 const U minimal_anchor_requested=probe_unsigned_v12(get("--minimal-anchor-window","0"),"minimal-anchor-window");if(minimal_anchor_requested>1)throw std::runtime_error("invalid minimal-anchor-window flag");if(minimal_anchor_requested&&(policy!="certified"||pair!="anchor"||window!="union"))throw std::runtime_error("minimal-anchor-window requires certified policy, anchor pair and union window");minimal_anchor_window=minimal_anchor_requested;
 const U bitset_scene_requested=probe_unsigned_v12(get("--dynamic-support-bitset-scene","0"),"dynamic-support-bitset-scene");if(bitset_scene_requested>1)throw std::runtime_error("invalid dynamic-support-bitset-scene flag");
 const U tw_requested=probe_unsigned_v12(get("--two-weight-complement","0"),"two-weight-complement");if(tw_requested>1)throw std::runtime_error("invalid two-weight-complement flag");two_weight_complement=tw_requested;
 const U tw_scaled_requested=probe_unsigned_v12(get("--two-weight-scaled-counts","0"),"two-weight-scaled-counts");if(tw_scaled_requested>1)throw std::runtime_error("invalid two-weight-scaled-counts flag");two_weight_scaled_counts=tw_scaled_requested;
 const U tw_certificate_requested=probe_unsigned_v12(get("--two-weight-slack-certificate","0"),"two-weight-slack-certificate");if(tw_certificate_requested>1)throw std::runtime_error("invalid two-weight-slack-certificate flag");if(tw_certificate_requested&&!tw_requested)throw std::runtime_error("two-weight-slack-certificate requires two-weight-complement1");two_weight_slack_certificate=tw_certificate_requested;
 const U pair_specific_requested=probe_unsigned_v12(get("--pair-specific-complement","0"),"pair-specific-complement"),wide_proposal_requested=probe_unsigned_v12(get("--wide-complement-proposal","0"),"wide-complement-proposal");
 if(pair_specific_requested>1||wide_proposal_requested>1)throw std::runtime_error("invalid pair complement flags");
 if(wide_proposal_requested&&!pair_specific_requested)throw std::runtime_error("wide proposal requires pair-specific-complement1");
 if(pair_specific_requested&&!tw_requested)throw std::runtime_error("pair complement requires two-weight-complement1");
 pair_specific_complement=pair_specific_requested;wide_complement_proposal=wide_proposal_requested;
 const U budget_pair_requested=probe_unsigned_v12(get("--budget-compatible-complement","0"),"budget-compatible-complement");if(budget_pair_requested>1)throw std::runtime_error("invalid budget pair flag");if(budget_pair_requested&&!pair_specific_requested)throw std::runtime_error("budget pair requires pair-specific-complement1");budget_compatible_complement=budget_pair_requested;const std::string budget_pair_mode=get("--budget-compatible-mode","budget");if(budget_pair_mode!="budget"&&budget_pair_mode!="all")throw std::runtime_error("invalid budget pair mode");if(budget_pair_mode=="all"&&!budget_pair_requested)throw std::runtime_error("all-pair control requires budget-compatible-complement1");budget_pair_filter=budget_pair_mode=="budget";two_weight_profile_update=get("--two-weight-profile-update","heatbath");if(two_weight_profile_update!="heatbath"&&two_weight_profile_update!="metropolis_refresh"&&two_weight_profile_update!="geometric_refresh"&&two_weight_profile_update!="root_orbit_geometric_refresh"&&two_weight_profile_update!="pair_conditional_gibbs"&&two_weight_profile_update!="pair_conditional_profile_hold")throw std::runtime_error("invalid profile-update rule");if(two_weight_profile_update!="heatbath"&&(!tw_requested||!pair_specific_requested))throw std::runtime_error("profile refresh requires exact pair-complement path");
 const U whole_private_requested=probe_unsigned_v12(get("--whole-private-conditional","0"),"whole-private-conditional");if(whole_private_requested>1)throw std::runtime_error("invalid whole-private-conditional flag");
 const U whole_reuse_requested=probe_unsigned_v12(get("--whole-private-reuse-layout","0"),"whole-private-reuse-layout");if(whole_reuse_requested>1)throw std::runtime_error("invalid whole-private-reuse-layout flag");if(whole_reuse_requested&&!whole_private_requested)throw std::runtime_error("whole-private-reuse-layout requires whole-private-conditional1");
 const U WS_requested=probe_unsigned_v12(get("--shared-weight-heatbath","0"),"shared-weight-heatbath");if(WS_requested>1)throw std::runtime_error("invalid shared-weight-heatbath flag");if(WS_requested&&policy!="certified")throw std::runtime_error("shared-weight-heatbath requires certified policy");
 const U WS_compose_requested=probe_unsigned_v12(get("--shared-weight-heatbath-compose","0"),"shared-weight-heatbath-compose");const U WS_intersection_requested=probe_unsigned_v12(get("--shared-weight-heatbath-intersection","0"),"shared-weight-heatbath-intersection");
 if(WS_compose_requested>1||WS_intersection_requested>1)throw std::runtime_error("shared-weight heatbath compose/intersection must be0/1");
 if(WS_compose_requested&&WS_requested)throw std::runtime_error("shared-weight heatbath compose cannot replace A");
 if((WS_compose_requested||WS_intersection_requested)&&policy!="certified")throw std::runtime_error("shared-weight heatbath compose/intersection requires certified policy");
 if(WS_intersection_requested&&!WS_requested&&!WS_compose_requested)throw std::runtime_error("shared-weight heatbath intersection requires replace or compose");
 const U residual_requested=probe_unsigned_v12(get("--residual-cycle-refresh","0"),"residual-cycle-refresh");const std::string residual_delta=get("--residual-cycle-delta","uniform");if(residual_requested>1)throw std::runtime_error("invalid residual-cycle-refresh flag");if(residual_delta!="unit"&&residual_delta!="uniform"&&residual_delta!="unit_scan"&&residual_delta!="uniform_scan"&&residual_delta!="dyadic_scan"&&residual_delta!="dyadic_local")throw std::runtime_error("residual-cycle-delta");if(residual_requested&&policy!="certified")throw std::runtime_error("residual-cycle-refresh requires certified policy");if(residual_requested&&(WS_requested||WS_compose_requested||WS_intersection_requested))throw std::runtime_error("residual cycle cannot combine with shared-weight heatbath");
 const U disableA=probe_unsigned_v12(get("--disable-A","0"),"disable-A");if(disableA>1)throw std::runtime_error("invalid disable-A flag");
 const U global_equal_weight_switch=probe_unsigned_v12(get("--global-equal-weight-switch","0"),"global-equal-weight-switch");if(global_equal_weight_switch>1)throw std::runtime_error("invalid global-equal-weight-switch flag");
 const U class_balanced_requested=probe_unsigned_v12(get("--global-weight-class-balanced","0"),"global-weight-class-balanced");if(class_balanced_requested>1)throw std::runtime_error("invalid global-weight-class-balanced flag");if(class_balanced_requested&&!global_equal_weight_switch)throw std::runtime_error("global-weight-class-balanced requires global-equal-weight-switch1");
 const U bulk_requested=probe_unsigned_v12(get("--global-weight-class-bulk","0"),"global-weight-class-bulk");if(bulk_requested>1)throw std::runtime_error("invalid weight class bulk flag");
 const U bulk_nonself_requested=probe_unsigned_v12(get("--global-weight-class-bulk-nonself","0"),"global-weight-class-bulk-nonself");if(bulk_nonself_requested>1||(bulk_nonself_requested&&!bulk_requested))throw std::runtime_error("bulk nonself requires bulk1");
 if(bulk_requested&&(!global_equal_weight_switch||class_balanced_requested))throw std::runtime_error("weight class bulk requires GWS1 and classbalanced0");
 const std::string gws_selection=get("--global-equal-weight-selection","raw");if(gws_selection!="raw"&&gws_selection!="conditional_legal")throw std::runtime_error("invalid global-equal-weight-selection");
 if(gws_selection!="raw"&&(!global_equal_weight_switch||class_balanced_requested))throw std::runtime_error("conditional legal GWS requires global-equal-weight-switch1 and class-balanced0");
 const U structure_trace_requested=probe_unsigned_v12(get("--unlabeled-structure-trace","0"),"unlabeled-structure-trace");if(structure_trace_requested>1)throw std::runtime_error("invalid unlabeled-structure-trace flag");
 const U allpostburn_sigma_requested=probe_unsigned_v12(get("--allpostburn-sigma-histogram","0"),"allpostburn-sigma-histogram");if(allpostburn_sigma_requested>1||(allpostburn_sigma_requested&&!structure_trace_requested))throw std::runtime_error("allpostburn Sigma flag requires structure trace");
 const U global_degree_work_batch=probe_unsigned_v12(get("--global-degree-work-batch","0"),"global-degree-work-batch");if(global_degree_work_batch>1)throw std::runtime_error("invalid global-degree-work-batch flag");
 const U global_representation_work_batch=probe_unsigned_v12(get("--global-representation-work-batch","0"),"global-representation-work-batch");if(global_representation_work_batch>1)throw std::runtime_error("invalid global-representation-work-batch flag");if(global_representation_work_batch&&!global_degree_work_batch)throw std::runtime_error("global-representation-work-batch requires global-degree-work-batch1");
 const U global_bridge_swap=probe_unsigned_v12(get("--global-bridge-swap","0"),"global-bridge-swap");if(global_bridge_swap>1)throw std::runtime_error("invalid global-bridge-swap flag");
 const U disable_factorized_joint=probe_unsigned_v12(get("--disable-factorized-joint","0"),"disable-factorized-joint");if(disable_factorized_joint>1)throw std::runtime_error("invalid disable-factorized-joint flag");
 const U fixed_support_dp_requested=probe_unsigned_v12(get("--fixed-support-dp","0"),"fixed-support-dp");if(fixed_support_dp_requested>1)throw std::runtime_error("invalid fixed-support-dp flag");fixed_support_dp=fixed_support_dp_requested;
 const U global_small_iid=probe_unsigned_v12(get("--global-small-iid","0"),"global-small-iid");if(global_small_iid>1)throw std::runtime_error("invalid global-small-iid flag");
 const U matching_xor=probe_unsigned_v12(get("--matching-xor","0"),"matching-xor");if(matching_xor>1)throw std::runtime_error("invalid matching-xor flag");
 const U matching_sweep=probe_unsigned_v12(get("--matching-sweep","0"),"matching-sweep");if(matching_sweep>1)throw std::runtime_error("invalid matching-sweep flag");
 const U regular_iid=probe_unsigned_v12(get("--regular-iid","0"),"regular-iid");if(regular_iid>1)throw std::runtime_error("invalid regular-iid flag");
 const U regular_no_rejection=probe_unsigned_v12(get("--regular-no-rejection","0"),"regular-no-rejection");if(regular_no_rejection>1)throw std::runtime_error("invalid regular-no-rejection flag");
 const U cycle_when_maxdegree_two=probe_unsigned_v12(get("--cycle-when-maxdegree-two","0"),"cycle-when-maxdegree-two");if(cycle_when_maxdegree_two>1)throw std::runtime_error("invalid fixed-degree cycle flag");
 const U weight_class_nontrivial=probe_unsigned_v12(get("--weight-class-nontrivial","0"),"weight-class-nontrivial");if(weight_class_nontrivial>1)throw std::runtime_error("invalid nontrivial T flag");
 const std::string typed_mode=get("--typed-mode","full");if(typed_mode!="full"&&typed_mode!="heterogeneous-only"&&typed_mode!="homogeneous-only")throw std::runtime_error("typed-mode");
 const U node_orientation_requested=probe_unsigned_v12(get("--node-weighted-orientation","0"),"node-weighted-orientation");if(node_orientation_requested>1)throw std::runtime_error("invalid orientation flag");node_weighted_orientation=node_orientation_requested;
 const std::string factorized_mode=get("--factorized-mode","full");if(factorized_mode!="full"&&factorized_mode!="heterogeneous-only"&&factorized_mode!="homogeneous-only")throw std::runtime_error("factorized mode");
 const U factorized_local_compile=probe_unsigned_v12(get("--factorized-local-compile","0"),"factorized-local-compile"),factorized_profile=probe_unsigned_v12(get("--factorized-profile","0"),"factorized-profile");if(factorized_local_compile>1||factorized_profile>1)throw std::runtime_error("invalid factorized flags");
 const std::string unified_label_mode=get("--unified-private-label-update","full_resample");if(unified_label_mode!="full_resample"&&unified_label_mode!="minimal_transport"&&unified_label_mode!="quota_first")throw std::runtime_error("invalid unified-private-label-update mode");
 const U unified_requested=probe_unsigned_v12(get("--unified-private-pair","0"),"unified-private-pair");if(unified_requested>1)throw std::runtime_error("invalid unified-private-pair flag");
 if(!unified_requested&&unified_label_mode!="full_resample")throw std::runtime_error("minimal label transport requires unified-private-pair1");
 const std::string unified_profile_mode=get("--unified-private-profile-update","heatbath");const U unified_second_public=probe_unsigned_v12(get("--unified-second-public","1"),"unified-second-public");if((unified_profile_mode!="heatbath"&&unified_profile_mode!="fixed_profile")||unified_second_public>1||(!unified_requested&&(unified_profile_mode!="heatbath"||unified_second_public!=1)))throw std::runtime_error("unified ablations require unified-private-pair1 with heatbath/fixed_profile and second-public0/1");
 const U productive_requested=probe_unsigned_v12(get("--productive-triple","0"),"productive-triple");if(productive_requested>1)throw std::runtime_error("invalid productive-triple flag");
 const U root_guide_requested=probe_unsigned_v12(get("--root-excess-triple-guide","0"),"root-excess-triple-guide");if(root_guide_requested>1)throw std::runtime_error("invalid root-excess-triple-guide flag");
 const U cohort_local_requested=probe_unsigned_v12(get("--cohort-local-private","0"),"cohort-local-private");if(cohort_local_requested>1)throw std::runtime_error("invalid cohort-local-private flag");
 const U cohort_requested=probe_unsigned_v12(get("--cohort-two-class","0"),"cohort-two-class");const std::string cohort_selector=get("--cohort-root-selector","leaf_guided"),cohort_update=get("--cohort-profile-update","exact");
 if(cohort_requested>1)throw std::runtime_error("invalid cohort-two-class flag");if(cohort_selector!="leaf_guided"&&cohort_selector!="uniform_root"&&cohort_selector!="eligible_root"&&cohort_selector!="uniform_union")throw std::runtime_error("cohort-root-selector");if(cohort_update!="exact"&&cohort_update!="fixed_class")throw std::runtime_error("cohort-profile-update");
 if(cohort_requested&&(!factorized_local_compile||disable_factorized_joint||factorized_mode!="full"||policy!="certified"||whole_private_requested))throw std::runtime_error("cohort requires full factorized certified slot and whole-private0");
 if(cohort_selector=="eligible_root"&&!cohort_requested)throw std::runtime_error("eligible_root requires cohort-two-class1");
 const U cohort_ledger_requested=probe_unsigned_v12(get("--cohort-ledger-compiler","0"),"cohort-ledger-compiler"),cohort_cache_requested=probe_unsigned_v12(get("--cohort-ledger-cache","1"),"cohort-ledger-cache");if(cohort_ledger_requested>1||cohort_cache_requested>1)throw std::runtime_error("invalid cohort-ledger compiler/cache flag");if(cohort_ledger_requested&&!cohort_requested)throw std::runtime_error("cohort-ledger-compiler requires cohort-two-class1");
 if(cohort_local_requested&&(!cohort_requested||cohort_selector!="uniform_union"||!cohort_ledger_requested||cohort_cache_requested))throw std::runtime_error("local cohort requires cohort1, uniform_union, ledger-compiler1, ledger-cache0");
 const U typed_local_compile=probe_unsigned_v12(get("--typed-local-compile","0"),"typed-local-compile");if(typed_local_compile>1)throw std::runtime_error("invalid typed compiler flag");
 const U global_weight_class_trade=probe_unsigned_v12(get("--global-weight-class-trade","0"),"global-weight-class-trade");if(global_weight_class_trade>1)throw std::runtime_error("invalid global T flag");
 const U weight_class_trade=probe_unsigned_v12(get("--weight-class-trade","0"),"weight-class-trade");if(weight_class_trade>1)throw std::runtime_error("invalid T flag");
 if(global_weight_class_trade&&weight_class_trade)throw std::runtime_error("global and root-local T are mutually exclusive");
 const U balanced_local=probe_unsigned_v12(get("--balanced-local","0"),"balanced-local"),balanced_cap=probe_unsigned_v12(get("--balanced-private-per-person","2"),"balanced-private-per-person");if(balanced_local>1||balanced_cap<1||balanced_cap>3)throw std::runtime_error("invalid balanced flags");
 if(factorized_local_compile&&(typed_local_compile||global_weight_class_trade||weight_class_trade||balanced_local))throw std::runtime_error("factorized joint replaces other independent slots");
 if(typed_local_compile&&(global_weight_class_trade||weight_class_trade||balanced_local))throw std::runtime_error("typed joint update replaces separateGT/T/B slots");
 const U coverage_compose_requested=probe_unsigned_v12(get("--coverage-compose","0"),"coverage-compose");if(coverage_compose_requested>1)throw std::runtime_error("invalid coverage-compose flag");if(coverage_compose_requested&&(coverage!=0||policy!="certified"||mode!="corrected"))throw std::runtime_error("coverage-compose requires coverage-bp0 and certified corrected policy");
 const U compose=probe_unsigned_v12(get("--cycle-compose","1"),"cycle-compose"),certskip=probe_unsigned_v12(get("--certificate-skip","1"),"certificate-skip");
 if(compose>1||certskip>1)throw std::runtime_error("invalid compose/certificate flag");
 const U cycle_core_requested=probe_unsigned_v12(get("--cycle-core-filter","0"),"cycle-core-filter"),cycle_nontrivial_requested=probe_unsigned_v12(get("--cycle-nontrivial-draw","0"),"cycle-nontrivial-draw");
 if(cycle_core_requested>1||cycle_nontrivial_requested>1)throw std::runtime_error("invalid support-cycle innovation flag");
 if((cycle_core_requested||cycle_nontrivial_requested)&&(!compose||composition!="MC"||policy!="certified"||residual_requested))throw std::runtime_error("support-cycle innovation requires certified compositionMC cycle-compose1 residual0");
 const U capacity_requested=probe_unsigned_v12(get("--capacity-cycle","0"),"capacity-cycle"),capacity_weighted_first=probe_unsigned_v12(get("--capacity-cycle-weighted-first","1"),"capacity-cycle-weighted-first");
 if(capacity_requested>1||capacity_weighted_first>1)throw std::runtime_error("invalid capacity cycle flags");
 if(capacity_requested&&(!compose||composition!="MC"||policy!="certified"||residual_requested||cycle_core_requested||cycle_nontrivial_requested))throw std::runtime_error("capacity cycle requires isolated certified MC dispatch");
 if(input.empty()||out.empty()||queries.empty()||!N||B>=N||coverage>10000||hist>1)throw std::runtime_error("invalid flags");
 if(mode!="corrected"&&mode!="none"&&mode!="unconditional")throw std::runtime_error("fallback-mode");if(owner!="metropolis_refresh"&&owner!="heatbath")throw std::runtime_error("owner-update");if(pair!="uniform"&&pair!="anchor"&&pair!="mixed")throw std::runtime_error("pair");
 for(auto key:{"--cycle-every","--orbit-every","--anchor-lazy"})if(probe_unsigned_v12(get(key,"0"),key))throw std::runtime_error("fallback driver has no "+std::string(key));
 const std::string ablation_module=get("--ablation-module","none");
 if(ablation_module!="none"&&ablation_module!="local"&&ablation_module!="exchange"&&ablation_module!="coverage")throw std::runtime_error("invalid ablation-module");
 U ablated_local_calls=0,ablated_exchange_calls=0,ablated_coverage_calls=0;
 if(JL_requested&&(composition!="MC"||local_steps!=1||compose!=capacity_requested||coverage_compose_requested||ablation_module=="local"||ablation_module=="coverage"))throw std::runtime_error("ledger joint requires one MC bank, capacity/compose matched, no extra R or local/coverage ablation");
 const U sampled_private_requested=probe_unsigned_v12(get("--sampled-private-buffer","0"),"sampled-private-buffer"),disable_M_requested=probe_unsigned_v12(get("--disable-factorized-M","0"),"disable-factorized-M");
 const U distinct_private_requested=probe_unsigned_v12(get("--sampled-private-buffer-without-replacement","0"),"sampled-private-buffer-without-replacement");if(distinct_private_requested>1||(distinct_private_requested&&!sampled_private_requested))throw std::runtime_error("without-replacement requires sampled-private-buffer1 and flag0or1");
 const std::string near_private_mode=get("--near-weight-mode","nearest_indexed");if(near_private_mode!="nearest_indexed"&&near_private_mode!="uniform_indexed"&&near_private_mode!="nearest_scan")throw std::runtime_error("invalid near-weight-mode");
 const U near_private_requested=probe_unsigned_v12(get("--near-weight-private-buffer","0"),"near-weight-private-buffer");if(near_private_requested>1||(near_private_requested&&(!sampled_private_requested||distinct_private_requested)))throw std::runtime_error("near-weight-private-buffer requires sampled-private-buffer1 without-replacement0 and flag0or1");
 if((root_guide_requested||productive_requested)&&(!factorized_local_compile||disable_factorized_joint||sampled_private_requested))throw std::runtime_error("root guide requires original factorized B/M selector");
 if(sampled_private_requested>1||disable_M_requested>1)throw std::runtime_error("invalid sampled-private/M-disabled flag");
 if((sampled_private_requested||disable_M_requested)&&(!factorized_local_compile||disable_factorized_joint||factorized_mode!="full"||policy!="certified"||cohort_requested||whole_private_requested))throw std::runtime_error("sampled-private/M-disabled requires original full certified factorized slot, cohort0 whole-private0");
 if(unified_requested&&(policy!="certified"||!factorized_local_compile||factorized_mode!="full"||typed_local_compile||whole_private_requested||cohort_requested||WS_requested||WS_compose_requested||residual_requested||weight_class_trade||global_weight_class_trade||balanced_local||sampled_private_requested||near_private_requested||local_steps!=1||composition!="none"||compose))throw std::runtime_error("unified pair requires ordinary full certified slot, no alternative local modules, local-steps1 compositionnone cycle-compose0");
 const U strict_star_requested=probe_unsigned_v12(get("--strict-star-iid","0"),"strict-star-iid"),strict_owner_requested=probe_unsigned_v12(get("--strict-star-full-owner-observer","0"),"strict-star-full-owner-observer");const std::string strict_update=get("--strict-star-profile-update","exact");if(strict_star_requested>1||strict_owner_requested>1||(strict_update!="exact"&&strict_update!="fixed_class"))throw std::runtime_error("invalid strict-star flags");
 auto start=Clock::now();double cpu_start=process_cpu();ConvergenceDistanceCPUObserver convergence_observer;const std::string convergence_reference=get("--reference-input","");const U convergence_every=probe_unsigned_v12(get("--convergence-every","0"),"convergence-every");if(convergence_reference.empty()!=(convergence_every==0))throw std::runtime_error("reference/every both required");Options opt;opt.seed=seed;opt.orientation="both";opt.block_mode=pair;opt.block_shape="union";opt.block_width=12;opt.support_only=false;opt.owner_update=owner;opt.acceptance="exact";opt.kappa=0;opt.block_cache_capacity=0;opt.coverage_support_cap=coverage_cap_requested;opt.coverage_weighted_column_gibbs=weighted_column_gibbs_requested;opt.coverage_weighted_column_extra_lazy=coverage_extra_lazy;
 if(allpostburn_sigma_requested&&(strict_star_requested||strict_owner_requested))throw std::runtime_error("allpostburn Sigma observer supports ordinary dispatcher; strict-star early return excluded");
 if(JL_requested&&(strict_star_requested||strict_owner_requested))throw std::runtime_error("ledger joint forbids strict-star early-return dispatch");
 if(LF_requested&&(strict_star_requested||strict_owner_requested||regular_iid||matching_sweep||matching_xor||global_small_iid||policy!="certified"||mode!="corrected"||composition!="MC"||local_steps!=1||compose!=capacity_requested||coverage_compose_requested||ablation_module=="local"||ablation_module=="coverage"||factorized_local_compile||factorized_profile||fixed_support_dp_requested||minimal_anchor_requested||typed_local_compile||whole_private_requested||cohort_requested||cohort_local_requested||unified_requested||WS_requested||WS_compose_requested||WS_intersection_requested||residual_requested||balanced_local||weight_class_trade||global_weight_class_trade||productive_requested||root_guide_requested||pair_specific_requested||wide_proposal_requested||budget_pair_requested||tw_requested||tw_scaled_requested||tw_certificate_requested||near_private_requested||distinct_private_requested||sampled_private_requested||bitset_scene_requested||cycle_core_requested||cycle_nontrivial_requested))throw std::runtime_error("leaf certified requires one corrected MC bank, no IID/extra/local modules or unused local indexes");
 const U LSEL_requested=probe_unsigned_v12(get("--local-surplus-selector","0"),"local-surplus-selector");if(LSEL_requested>1)throw std::runtime_error("invalid local surplus selector flag");
 const U coverage_hazard=probe_unsigned_v12(get("--coverage-rho-den","4"),"coverage-rho-den");const U analysis_cpu_millis=probe_unsigned_v12(get("--analysis-cpu-millis","0"),"analysis-cpu-millis"),analysis_cpu_check=probe_unsigned_v12(get("--analysis-cpu-check","256"),"analysis-cpu-check");if(analysis_cpu_millis>36000000||!analysis_cpu_check)throw std::runtime_error("invalid CPU observation budget");const U requested_N=N;double cpu_deadline_elapsed=-1;const U coverage_mode=probe_unsigned_v12(get("--coverage-soft-mode","0"),"coverage-soft-mode"),degree_power=probe_unsigned_v12(get("--coverage-degree-power","0"),"coverage-degree-power"),coverage_add=probe_unsigned_v12(get("--coverage-add-bp","0"),"coverage-add-bp"),hazard_rule=probe_unsigned_v12(get("--coverage-hazard-rule","0"),"coverage-hazard-rule");if(coverage_mode==8&&degree_power)throw std::runtime_error("harmonic mode requires zero power");if(coverage_hazard<2||coverage_hazard>1000000||coverage_mode>9||degree_power>8||((coverage_mode==0||coverage_mode==3)&&degree_power)||(coverage_mode==0&&hazard_rule)||hazard_rule>1||coverage_add>10000||(coverage_add&&coverage))throw std::runtime_error("invalid certified coverage configuration");opt.rho_den=int(coverage_hazard);const U coverage_first_lazy=probe_unsigned_v12(get("--coverage-first-lazy","1"),"coverage-first-lazy");if(coverage_first_lazy>1||(!coverage_first_lazy&&(coverage_mode==0||coverage_mode==3)))throw std::runtime_error("invalid first-lazy configuration");SoftDefectCoverage coverage_kernel;coverage_kernel.extra_lazy=coverage_first_lazy;coverage_kernel.mode=int(coverage_mode);coverage_kernel.power=int(degree_power);coverage_kernel.hazard_rule=int(hazard_rule); Engine e(opt);e.graphs.push_back(Graph::load(input,false,true,opt.coverage_support_cap,opt.coverage_weighted_column_gibbs));Graph&g=e.graphs[0];e.coverage_cap.initialize(g,opt.coverage_support_cap);e.weighted_rectangle.initialize(g,opt.coverage_weighted_column_gibbs,coverage_axis_policy=="input_bound",coverage_auxiliary);g.counters=&e.stat;StrictStarFullFiber strict_star;strict_star.initialize(g,strict_star_requested||strict_owner_requested,strict_star_requested);if(strict_star.active&&(disconnected_bundle_requested||disconnected_four_bundle_requested||coverage_priority_requested))throw std::runtime_error("disconnected bundle cannot use strict-star early-return dispatcher");if(strict_star.active)return run_strict_star(e,g,strict_star,strict_update=="fixed_class",structure_trace_requested,strict_owner_requested,out,queries,seed,N,B,trace,check,hist,cpu_start,start);if(strict_owner_requested&&!strict_star.certificate)throw std::runtime_error("strict-star owner observer requires strict shape certificate");e.initialize_wedges(g);ResidualMarginLabels labels(g);CertifiedMatchingJointKernel joint(g,mode!="none",matching_xor&&policy=="certified");SupportCycleHeatbath cycle(g);const bool identity=(policy=="certified"||certskip)&&fixed_margin_A_identity(g);CountedDelayedFallback algorithm(mode,owner,joint,identity,window,disableA,policy);
 BalancedPrivateHeatbath balanced(joint,int(balanced_cap));TypedLocalCompiler typed(joint,typed_mode);FactorizedLocalCompiler factorized(joint,factorized_mode,factorized_profile);
 WholePrivateConditional whole_private(joint);whole_private.reuse_layout=whole_reuse_requested;
 WeightClassTrade value_trade(joint,g,weight_class_trade,weight_class_nontrivial);
 RegularDegreeTwoIID regular(g,regular_no_rejection&&regular_iid);const bool regular_iid_active=regular_iid&&regular.eligible;
 if(!g.check()||g.D)throw std::runtime_error("bad margins");if(hist&&U(g.nr)*U(g.nc)>64)throw std::runtime_error("histogram only small");
 const bool xor_iid_active=matching_xor&&policy=="certified"&&mode!="none"&&identity&&joint.xor_problem&&joint.xor_problem->eligible;
 const bool exact_iid_active=matching_sweep&&policy=="certified"&&mode!="none"&&identity&&joint.full_sweep_available();
 if(exact_iid_active&&!cycle.margin_certified_forest)throw std::runtime_error("matching sweep C identity certificate failed");
 WholeGraphSmallIID whole;whole.initialize(g,global_small_iid,regular_iid_active||exact_iid_active||xor_iid_active);const bool global_iid_active=whole.active;
 const bool degree_two_margin=std::all_of(g.target_degree.begin(),g.target_degree.end(),[](int d){return d<=2;});
 const bool degree_two_cycle_active=cycle_when_maxdegree_two&&degree_two_margin&&!JL_requested&&!LF_requested&&!regular_iid_active&&!exact_iid_active&&!xor_iid_active&&!global_iid_active;
 GlobalWeightClassTrade global_trade;const bool global_T_active=global_weight_class_trade&&!regular_iid_active&&!exact_iid_active&&!xor_iid_active&&!global_iid_active;global_trade.initialize(g,global_T_active);global_trade.check(g);
 UnifiedPrivatePair unified;const bool UA_active=unified_requested&&!regular_iid_active&&!exact_iid_active&&!xor_iid_active&&!global_iid_active;unified.profile_mode=unified_profile_mode;unified.label_mode=unified_label_mode;unified.update_second_public=unified_second_public;unified.initialize(g,unified_requested,UA_active);
 const bool typed_active=typed_local_compile&&!regular_iid_active&&!exact_iid_active&&!xor_iid_active&&!global_iid_active;
 if(whole_private_requested&&(!factorized_local_compile||disable_factorized_joint||factorized_mode!="full"||policy!="certified"))throw std::runtime_error("whole-private conditional requires active full factorized slot and certified policy");
 factorized.sampled_private=sampled_private_requested;factorized.disable_M=disable_M_requested;factorized.distinct_private=distinct_private_requested;factorized.near_private=near_private_requested;factorized.near.mode=near_private_mode;
 const bool factorized_active=!UA_active&&factorized_local_compile&&!disable_factorized_joint&&!regular_iid_active&&!exact_iid_active&&!xor_iid_active&&!global_iid_active;
 const bool whole_private_active=whole_private_requested&&factorized_active;
 CohortConditional cohort;cohort.initialize(g,cohort_requested&&factorized_active,cohort_selector,cohort_update,cohort_local_requested);cohort.ledger_compiler=cohort_ledger_requested;cohort.ledger_cache=cohort_cache_requested;const bool cohort_active=cohort.active;const bool factorized_original_active=factorized_active&&!cohort_active;
 if(!unified_requested&&pair_specific_requested&&(!factorized_original_active||whole_private_active||factorized.disable_M||factorized.factor_mode!="full"))throw std::runtime_error("pair complement requires ordinary full B/M");
 factorized.root_guide.initialize(g,(root_guide_requested||productive_requested)&&factorized_original_active&&!whole_private_active,root_guide_requested,productive_requested);
 NearWeightClassIndex near_index;const bool near_private_active=near_private_requested&&factorized_original_active&&!whole_private_active;near_index.initialize(g,near_private_active&&near_private_mode!="nearest_scan");factorized.near.index=&near_index;near_index.check(g);
 if(bulk_requested&&gws_selection!="raw")throw std::runtime_error("weight class bulk requires raw selection");
 GlobalEqualWeightSwitch gws;const bool GWS_active=global_equal_weight_switch&&!regular_iid_active&&!exact_iid_active&&!xor_iid_active&&!global_iid_active;
 gws.conditional_requested=gws_selection=="conditional_legal";gws.conditional_legal=gws.conditional_requested&&GWS_active;
 gws.bulk_requested=bulk_requested;gws.bulk_active=bulk_requested&&GWS_active;
 gws.bulk_nonself=bulk_nonself_requested&&GWS_active;
 gws.initialize(g,class_balanced_requested,GWS_active);
 GlobalDegreeWorkBatch gws_batch;gws_batch.initialize(g,global_degree_work_batch,GWS_active,N);
 SharedWeightHeatbath ws;const bool WS_ordinary=!identity&&!regular_iid_active&&!exact_iid_active&&!xor_iid_active&&!global_iid_active;const bool WS_replace_active=WS_requested&&!disableA&&WS_ordinary;const bool WS_compose_active=WS_compose_requested&&WS_ordinary;const bool WS_active=WS_replace_active||WS_compose_active;const bool WS_intersection_active=WS_intersection_requested&&WS_active;ws.initialize(g,WS_active);
 ResidualCycleRefresh residual;const bool residual_active=residual_requested&&!disableA&&!identity&&!regular_iid_active&&!exact_iid_active&&!xor_iid_active&&!global_iid_active;if(residual_active){const __uint128_t local_count=__uint128_t(local_steps)*(composition=="ACA"?2:1);if(local_count>std::numeric_limits<U>::max()||(__uint128_t(N)*local_count)>std::numeric_limits<U>::max())throw std::runtime_error("residual call counter overflow preflight");}residual.initialize(g,residual_active,residual_delta=="uniform",(residual_delta.find("_scan")!=std::string::npos||residual_delta=="dyadic_local")?residual_delta:std::string());
 GuidedSupportCycleHeatbath guided_cycle;const bool guided_cycle_active=(cycle_core_requested||cycle_nontrivial_requested)&&!regular_iid_active&&!exact_iid_active&&!xor_iid_active&&!global_iid_active;guided_cycle.initialize(g,guided_cycle_active,cycle_core_requested,cycle_nontrivial_requested);guided_cycle.check(g);
 if(LF_requested&&(regular_iid_active||exact_iid_active||xor_iid_active||global_iid_active||coverage_add))throw std::runtime_error("leaf certified forbids native shortcuts and appended R");CertifiedLeafBundleHeatbath leaf_bundle;leaf_bundle.initialize(g,LF_requested!=0);leaf_bundle.check(g);const bool LF_replace_W=LF_requested&&leaf_bundle.active;
 CapacityGuidedSupportCycle capacity_cycle;const bool capacity_cycle_dispatch=capacity_requested&&!LF_replace_W&&!regular_iid_active&&!exact_iid_active&&!xor_iid_active&&!global_iid_active;
 capacity_cycle.initialize(g,capacity_cycle_dispatch,capacity_weighted_first);capacity_cycle.check(g);
 WholeClassTripleHeatbath whole_class;const bool WCT_active=WCT_requested&&!regular_iid_active&&!exact_iid_active&&!xor_iid_active&&!global_iid_active;whole_class.initialize(g,WCT_active);if(WCT_core_start_requested&&(!capacity_requested||!capacity_weighted_first))throw std::runtime_error("B core start requires weighted capacity");whole_class.core=&capacity_cycle;whole_class.core_start=WCT_core_start_requested;whole_class.check(g);
 GlobalBridgeSwap gbs;const bool GBS_active=global_bridge_swap&&!regular_iid_active&&!exact_iid_active&&!xor_iid_active&&!global_iid_active;gbs.initialize(g,GBS_active);
 SupportSceneBitset scene_bits;scene_bits.initialize(g,bitset_scene_requested,typed_active||factorized_active||UA_active||WS_intersection_active);if(scene_bits.requested){typed.scene_bitset=&scene_bits;factorized.scene_bitset=&scene_bits;whole_private.scene_bitset=&scene_bits;}scene_bits.check(g);gws.bind_scene(scene_bits);CohortEligibleRootIndex eligible_roots;eligible_roots.initialize(g,cohort_active&&cohort_selector=="eligible_root");if(eligible_roots.active)cohort.eligible_index=&eligible_roots;eligible_roots.check(g);if(!residual.scan_mode)residual.heavy.check(g);gws_batch.refine_representation(g,scene_bits,global_representation_work_batch,N);
 if(LSEL_requested&&(LF_requested||JL_requested||WCT_requested||legacy_local_bypass_requested||local_steps!=1||composition!="MC"||!capacity_requested||!compose||coverage_add||disableA||identity||unified_requested||pair!="anchor"||window!="union"||policy!="certified"||node_weighted_orientation||minimal_anchor_requested))throw std::runtime_error("surplus local selector requires registered full-L WT route");
 SurplusLocalSelector local_selector;local_selector.initialize(g,LSEL_requested!=0,LSEL_requested!=0);local_selector.check(g);if(LSEL_requested)local_pair_selector=&local_selector;
 UnlabeledStructureTrace structure_observer;structure_observer.initialize(g,structure_trace_requested,out,B,N,trace,allpostburn_sigma_requested);
 const bool coverage_compose_active=coverage_compose_requested&&!regular_iid_active&&!exact_iid_active&&!xor_iid_active&&!global_iid_active;
 auto ws_draw=[&](){return WS_intersection_active?ws.step_intersection(e,g,scene_bits):ws.step(e,g);};
 auto cycle_draw=[&](){if(LF_replace_W){++LF_skipped_W_calls;return;}if(capacity_cycle_dispatch)capacity_cycle.step(e,g);else if(guided_cycle_active)guided_cycle.step(e,g);else cycle.step(e,g);};
 DisconnectedBundleHeatbath disconnected_bundle;disconnected_bundle.initialize(g,disconnected_bundle_requested!=0);disconnected_bundle.check(g);
 DisconnectedFourBundleHeatbath disconnected_four_bundle;disconnected_four_bundle.initialize(g,disconnected_four_bundle_requested!=0);disconnected_four_bundle.check(g);
 BundleMaxFourDispatch bundle_max_four;bundle_max_four.initialize(g,bundle_max_four_requested!=0,disconnected_bundle,disconnected_four_bundle);bundle_max_four.check(g,disconnected_bundle,disconnected_four_bundle);
 OverlapBundleHeatbath overlap_bundle;overlap_bundle.initialize(g,OB_requested!=0);overlap_bundle.check(g);
 if(JL_requested&&(regular_iid_active||exact_iid_active||xor_iid_active||global_iid_active||coverage_add))throw std::runtime_error("ledger joint requires ordinary native dispatch and no appended R");
 CachedLedgerBundleHeatbath ledger_joint;ledger_joint.initialize(g,JL_requested&&JL_update_enabled,JL_cache_requested!=0);ledger_joint.check(g);
 CertifiedCoveragePriority coverage_priority;
 if(coverage_priority_requested){
  if(coverage!=50||(coverage_mode!=5&&coverage_mode!=9)||coverage_first_lazy||hazard_rule||coverage_add||coverage_compose_requested||weighted_column_gibbs_requested||!coverage_cap_requested||ablation_module!="none")throw std::runtime_error("priority requires fast-NS or endpoint-mix/nohalf/geometric capped R and gamma50, no coverage ablation/composition");
  if(policy!="certified"||mode!="corrected"||pair!="anchor"||window!="union"||!minimal_anchor_requested||local_steps!=1||composition!="MC"||!compose||!capacity_requested||!capacity_weighted_first||!WCT_requested||!disconnected_bundle_requested||!global_equal_weight_switch||legacy_local_bypass_requested||WCT_core_start_requested||disableA)throw std::runtime_error("priority requires registered minimal-anchor full BW plus D configuration");
  if(UA_active||residual_requested||WS_requested||WS_compose_requested||typed_local_compile||whole_private_requested||cohort_requested||cohort_local_requested||weight_class_trade||global_weight_class_trade||balanced_local||global_bridge_swap||cycle_core_requested||cycle_nontrivial_requested||disable_factorized_joint||!factorized_local_compile||factorized_mode!="full"||typed_mode!="full")throw std::runtime_error("priority unsupported alternative ordinary module");
  coverage_priority.initialize(g,true);
  if(coverage_priority.static_eligible&&(regular_iid_active||exact_iid_active||xor_iid_active||global_iid_active||identity||!capacity_cycle_dispatch||!WCT_active||!GWS_active))throw std::runtime_error("priority static family reached unexpected dispatcher");
  coverage_kernel.priority_requested=true;coverage_kernel.priority_endpoint=[&](const Graph&state){return coverage_priority.current(state);};
 }
 U sweep_dispatches=0;
 if(convergence_every)convergence_observer.initialize(g,convergence_reference,out,convergence_every,cpu_start,queries);FixedProbeStatistics observer(g,B,N,queries,0,trace,!convergence_every);std::unique_ptr<StrictStarOwnerObserver>strict_owner;if(strict_owner_requested)strict_owner=std::make_unique<StrictStarOwnerObserver>(g,observer,strict_star,N,B,trace);std::map<std::string,U>counts;std::vector<std::pair<U,std::string>>snapshots;std::string cached;U oldhash1=0,oldhash2=0;bool cached_ok=false;U rcalls=0,composed_R_calls=0,checks=1,changed_macro=0;double setup_cpu=process_cpu()-cpu_start;
 for(U t=1;t<=N;++t){const U h1=g.hash1,h2=g.hash2;bool coverage_selected=false;
  if(coverage_priority_requested){coverage_priority.begin_round(g);coverage_kernel.priority_start_S=coverage_priority.round_S;}
  if(regular_iid_active){regular.draw(e,g);}
  else if(xor_iid_active){joint.xor_problem->draw(e,g,joint.leaf_axis);}
  else if(exact_iid_active){++sweep_dispatches;++algorithm.certified_dispatches;++algorithm.J_proposals;const bool differs=joint.sweep(e,g);algorithm.J_changed_proposals+=differs;++algorithm.J_accepts;algorithm.accepted_J_changes+=differs;}
  else if(global_iid_active){const double ts=process_cpu();whole.draw(e,g);whole.draw_cpu_seconds+=process_cpu()-ts;}
  else if(!coverage_compose_active&&((coverage_priority_requested&&coverage_priority.round_S)||e.rng.below(10000)<coverage)){coverage_selected=true;if(ablation_module=="coverage")++ablated_coverage_calls;else{++rcalls;coverage_kernel.candidate(e,g);}}
  else{auto local_bank=[&](){if(LF_requested){++LF_ordinary_dispatches;if(leaf_bundle.active)leaf_bundle.compose(e,g);else ++LF_inactive_ordinary_holds;return;}if(JL_requested){++JL_ordinary_dispatches;if(JL_update_enabled)ledger_joint.compose(e,g);else ++JL_disabled_dispatches;return;}if(ablation_module=="local"){++ablated_local_calls;return;}if(legacy_local_bypass_requested){++legacy_local_bypass_calls;if(WCT_active)whole_class.step(e,g);return;}if(UA_active){unified.step(e,g);return;}for(U local=0;local<local_steps;++local){if(residual_active)residual.step(e,g);else if(WS_replace_active)ws_draw();else algorithm.step(e,g);if(weight_class_trade){const double ts=process_cpu();value_trade.step(e,g);value_trade.cpu_seconds+=process_cpu()-ts;}if(global_T_active){const double ts=process_cpu();global_trade.step(e,g);global_trade.cpu_seconds+=process_cpu()-ts;}if(typed_active){const double ts=process_cpu();typed.step(e,g);typed.cpu_seconds+=process_cpu()-ts;}if(factorized_active){const double ts=process_cpu();if(cohort_active){cohort.step(e,g);cohort.cpu_seconds+=process_cpu()-ts;}else if(whole_private_active){whole_private.step(e,g);whole_private.cpu_seconds+=process_cpu()-ts;}else{factorized.step(e,g);factorized.cpu_seconds+=process_cpu()-ts;}}if(balanced_local){const double bs=process_cpu();balanced.step(e,g);balanced.cpu_seconds+=process_cpu()-bs;}}if(WCT_active)whole_class.step(e,g);};
   if(degree_two_cycle_active){local_bank();cycle_draw();}
   else if(composition=="ACA"){local_bank();if(compose)cycle_draw();local_bank();}
   else if(composition=="CAC"){if(compose)cycle_draw();local_bank();if(compose)cycle_draw();}
   else if(composition=="MC"){local_bank();if(compose)cycle_draw();}
   else if(composition=="CM"){if(compose)cycle_draw();local_bank();}
   else{local_bank();}}
  if(WS_compose_active)ws_draw();
  if(coverage_compose_active){coverage_selected=true;++composed_R_calls;coverage_kernel.candidate(e,g);}if(coverage_add&&e.rng.below(10000)<coverage_add){coverage_selected=true;++composed_R_calls;coverage_kernel.candidate(e,g);}
  bundle_coverage_selected_rounds+=coverage_selected;
  if(bundle_max_four_requested){
   if(coverage_selected)bundle_max_four.compose(e,g,disconnected_bundle,disconnected_four_bundle);
  }else{
  if(disconnected_bundle_requested&&(!bundle_coverage_only_requested||coverage_selected)){
    
   if(coverage_priority_requested&&coverage_priority.cached_true&&coverage_priority.current(g))++coverage_priority.D_identity_skips;
   else disconnected_bundle.compose(e,g);
  }
  if(disconnected_four_bundle_requested&&coverage_selected)disconnected_four_bundle.compose(e,g);
  }
  if(LF_requested&&coverage_selected){++LF_coverage_dispatches;if(leaf_bundle.active)leaf_bundle.compose(e,g);else ++LF_inactive_coverage_holds;}
  if(JL_requested&&coverage_selected){++JL_coverage_dispatches;if(JL_update_enabled)ledger_joint.compose(e,g);else ++JL_disabled_dispatches;}
  if(OB_requested&&(!OB_coverage_only_requested||coverage_selected))overlap_bundle.compose(e,g);
  if(GWS_active){if(ablation_module=="exchange")++ablated_exchange_calls;else if(gws_batch.active)gws_batch.step(e,g,gws);else gws.step(e,g);}
  if(GBS_active)gbs.step(e,g);
  changed_macro+=(h1!=g.hash1||h2!=g.hash2);++e.stat.outer;observer.observe(g,t,e.stat.cell_updates);if(convergence_every)convergence_observer.observe(g,t);structure_observer.observe(g,t);if(strict_owner)strict_owner->observe(g,t);
  if(hist&&t>B){if(!cached_ok||g.hash1!=oldhash1||g.hash2!=oldhash2){cached=g.flat();oldhash1=g.hash1;oldhash2=g.hash2;cached_ok=true;}++counts[cached];if(trace&&t%trace==0)snapshots.emplace_back(t,cached);}
  if(analysis_cpu_millis&&t>B&&t%analysis_cpu_check==0){const double elapsed=process_cpu()-cpu_start;if(elapsed>=double(analysis_cpu_millis)/1000){cpu_deadline_elapsed=elapsed;N=t;}}
  if((check&&t%check==0)||t==N){if(!g.check()||g.D)throw std::runtime_error("four margins changed");global_trade.check(g,near_index.active);near_index.check(g);scene_bits.check(g);eligible_roots.check(g);if(!residual.scan_mode)residual.heavy.check(g);guided_cycle.check(g);capacity_cycle.check(g);whole_class.check(g);disconnected_bundle.check(g);disconnected_four_bundle.check(g);bundle_max_four.check(g,disconnected_bundle,disconnected_four_bundle);overlap_bundle.check(g);ledger_joint.check(g);leaf_bundle.check(g);local_selector.check(g);++checks;}
 }
 if(analysis_cpu_millis&&N!=requested_N){observer.budget=N;structure_observer.budget=N;if(trace&&N%trace){observer.record(g,N);if(structure_observer.active)structure_observer.record(g,N);}}
 if(convergence_every)convergence_observer.finish(g,N);structure_observer.finish();
 const double loop_cpu=process_cpu()-cpu_start-setup_cpu;observer.write(out);if(strict_owner)strict_owner->write(out);
 if(hist){std::ofstream f(out+".hist.json");f<<"{\"postburn_count\":"<<N-B<<",\"counts\":{";bool first=true;for(auto&p:counts){if(!first)f<<',';first=false;f<<'\"'<<p.first<<"\":"<<p.second;}f<<"},\"snapshots\":[";first=true;for(auto&p:snapshots){if(!first)f<<',';first=false;f<<"["<<p.first<<",\""<<p.second<<"\"]";}f<<"]}\n";if(!f)throw std::runtime_error("hist write");}
 std::ofstream final(out+".final.graph");final<<g.nr<<' '<<g.nc<<'\n';for(auto&ed:g.edges)final<<ed.r<<' '<<ed.c<<' '<<ed.w<<'\n';final.close();if(!final)throw std::runtime_error("final write");
 const double cpu=process_cpu()-cpu_start,wall=std::chrono::duration<double>(Clock::now()-start).count();
 std::ofstream f(out+".run.json");f<<std::setprecision(17)<<"{";f<<"\"analysis_cpu_millis\":"<<analysis_cpu_millis<<",\"analysis_cpu_check\":"<<analysis_cpu_check<<",\"analysis_requested_outer_max\":"<<requested_N<<",\"analysis_actual_outer\":"<<N<<",\"analysis_cpu_stop_elapsed\":"<<cpu_deadline_elapsed<<",";f<<"\"legacy_local_bypass_requested\":"<<legacy_local_bypass_requested<<",\"legacy_local_bypass_calls\":"<<legacy_local_bypass_calls<<",";if(ablation_module!="none")f<<"\"ablation_module\":\""<<ablation_module<<"\",\"ablated_local_calls\":"<<ablated_local_calls<<",\"ablated_exchange_calls\":"<<ablated_exchange_calls<<",\"ablated_coverage_calls\":"<<ablated_coverage_calls<<",";local_selector.metadata(f);capacity_cycle.synchronize(g);capacity_cycle.metadata(f);whole_class.metadata(f);disconnected_bundle.metadata(f);disconnected_four_bundle.metadata(f);bundle_max_four.metadata(f);overlap_bundle.metadata(f);ledger_joint.metadata(f);leaf_bundle.metadata(f);f<<"\"LF_replace_W\":"<<(LF_replace_W?"true":"false")<<",\"LF_ordinary_dispatches\":"<<LF_ordinary_dispatches<<",\"LF_coverage_dispatches\":"<<LF_coverage_dispatches<<",\"LF_inactive_ordinary_holds\":"<<LF_inactive_ordinary_holds<<",\"LF_inactive_coverage_holds\":"<<LF_inactive_coverage_holds<<",\"LF_skipped_W_calls\":"<<LF_skipped_W_calls<<",";f<<"\"JL_requested\":"<<(JL_requested?"true":"false")<<",\"JL_ordinary_dispatches\":"<<JL_ordinary_dispatches<<",\"JL_coverage_dispatches\":"<<JL_coverage_dispatches<<",\"JL_update_enabled\":"<<(JL_update_enabled?"true":"false")<<",\"JL_disabled_dispatches\":"<<JL_disabled_dispatches<<",\"JL_cache_requested\":"<<(JL_cache_requested?"true":"false")<<",";f<<"\"OB_coverage_only_requested\":"<<(OB_coverage_only_requested?"true":"false")<<",";f<<"\"DB_coverage_only_requested\":"<<bundle_coverage_only_requested<<",\"DB_coverage_selected_rounds\":"<<bundle_coverage_selected_rounds<<",";coverage_priority.metadata(f);guided_cycle.metadata(f);e.coverage_cap.metadata(f);e.weighted_rectangle.metadata(f,opt.coverage_weighted_column_extra_lazy);gws.conditional_metadata(f);gws.bulk_metadata(f);if(unified_requested){unified.metadata(f);f<<"\"UA_replaces_A_B_M\":"<<(UA_active?"true":"false")<<",\"UA_legacy_profile_mode_requested\":\""<<two_weight_profile_update<<"\",";}if(allpostburn_sigma_requested){f<<"\"allpostburn_sigma_histogram_requested\":1,\"Sigma_histogram_postburn_count\":"<<structure_observer.histogram_postburn_count<<",\"Sigma_histogram_unique_values\":"<<structure_observer.histogram_counts.size()<<",";}if(two_weight_profile_update!="heatbath"&&!unified_requested){f<<"\"two_weight_profile_update\":\""<<two_weight_profile_update<<"\",\"profile_update_scope\":\""<<(pair_conditional_profile_mode()?"ALL selected two-class M blocks; exact pair-conditionals or frozen high-count profile; final high/low label refresh always; no old profile enumeration/wide proposal":"exact multi-profile M draw only; conditional high/low label refresh follows every profile draw; inherited singleton fallback and wide proposal unchanged")<<"\",";factorized.tw.metropolis.metadata(f);factorized.tw.geometric.metadata(f);factorized.tw.root_orbit.metadata(f);if(pair_conditional_profile_mode()){f<<"\"pair_conditional_profile_requested\":true,\"PG_active\":true,\"PG_timing_active\":"<<(factorized.profile?"true":"false")<<",\"PG_profile_hold\":"<<(two_weight_profile_update=="pair_conditional_profile_hold"?"true":"false")<<",\"PG_policy\":\"ALL nonempty two-class blocks; deterministic pairs01,12,02; exact capped one-dimensional conditional counts; scalar two-pass scaled recurrence; no slack6 selection or wide proposal; final high/low labelled allocation always refreshed; profilehold skips all three count/RNG steps\",";factorized.tw.pair_conditional.metadata(f);}}if(budget_pair_requested){f<<"\"BP_mode\":\""<<budget_pair_mode<<"\",\"budget_compatible_complement_requested\":"<<budget_pair_requested<<",\"BP_active\":"<<(!unified_requested?"true":"false")<<",\"BP_policy\":\"remaining complement classes; budget mode pairs delta<=C-3, all mode no delta filter; both weighted n_i*n_j; no compatible pair -> most frequent remaining single class; no retry; after-B exact geometry; selected pair primary is lower weight; compatible is necessary not sufficient\",";factorized.budget_pair.metadata(f);}if(pair_specific_requested){f<<"\"PC_active\":"<<(!unified_requested?"true":"false")<<",\"PC_policy\":\""<<(pair_conditional_profile_mode()?"after B only; exact h,beta,c geometry; all widths use pair conditional or profilehold; PC_narrow/PC_wide both0, no wide proposal calls; missing class uses original single M":"after B only; pair-specific h,beta,c,NH,D,slack; wide legal is not necessarily changed; failed wide proposal performs original single-class M; no retries")<<"\",\"pair_specific_complement_requested\":"<<pair_specific_requested<<",\"wide_complement_proposal_requested\":"<<wide_proposal_requested<<",\"PC_geometry_calls\":"<<factorized.pair_geometry_calls<<",\"PC_narrow\":"<<factorized.pair_geometry_narrow<<",\"PC_wide\":"<<factorized.pair_geometry_wide<<",";factorized.wide.metadata(f);}if(root_guide_requested||productive_requested){f<<"\"root_excess_triple_guide_requested\":"<<root_guide_requested<<",\"productive_triple_requested\":"<<productive_requested<<",\"PJ_identity_windows\":"<<factorized.root_guide.identity_holds<<",";factorized.root_guide.metadata(f);}if(near_private_requested){f<<"\"near_weight_private_buffer_requested\":"<<near_private_requested<<",\"NWB_mode\":\""<<near_private_mode<<"\",\"NWB_active\":"<<(near_private_active?"true":"false")<<",\"NWB_policy\":\"original root/triple; nearest modes uniformseed from pooled nonrootrecords; uniform_indexed uses pooledWOR with same maintainedindex; nearest_scan rebuilds classes from threeadj with no dynamicindex; nearest classes ordered by distance to seedweight then smallerweight; cycle onequota per nearestclass until min(6,N), pooledclass uniform withoutreplacement; filter sharedrecords withoutretry; selectedprivatequota0to6 and positive rootledger; completeowner heatbath atmost90; live coordinate index allmutations charged, epoch maintenance may scanaxis; retainedM stillfullpool scan; no universal speed or irreducibility claim\",";factorized.near.metadata(f);near_index.metadata(f);}if(distinct_private_requested){f<<"\"sampled_private_buffer_without_replacement_requested\":"<<distinct_private_requested<<",\"NRB_active\":"<<((factorized_original_active&&!whole_private_active)?"true":"false")<<",\"NRB_policy\":\"original root/triple; eachactor excludes live rootrecord via pr/pc, samples min(2,D-1) uniform nonroot records withoutreplacement, filters nonprivate with no redraw; atmost6 selected carriedlabels/90 completeowner outcomes; privatequota/localstrength kept; classificationlookups atmost18 plus3 separate root-position lookups, no adjacency rootsearch; scratch epoch maintenance may scanaxis; empty selected skips B and M; retained M codes unchanged but sampledinputs/opportunities differ; stationary conditional kernel, no universal performance or irreducibility claim\",";factorized.distinct.metadata(f);}if(sampled_private_requested||disable_M_requested){f<<"\"sampled_private_buffer_requested\":"<<sampled_private_requested<<",\"SPB_active\":"<<((sampled_private_requested&&!distinct_private_requested&&!near_private_requested&&factorized_original_active&&!whole_private_active)?"true":"false")<<",\"disable_factorized_M_requested\":"<<disable_M_requested<<",\"PJ_M_disabled_active\":"<<((disable_M_requested&&factorized_original_active&&!whole_private_active)?"true":"false")<<",\"PJ_M_skipped_windows\":"<<factorized.M_skipped_windows<<",\"SPB_policy\":\"original root and actor triple; each actor exactly2 independent positive-record draws with replacement; remove root/nonprivate/duplicates, no retry; at most6 carried private labels, original quotas and root ledger; complete owner heatbath at most90 labeled outcomes includingcurrent; Moff avoids whole private-pool scan; SPB_value_lookups counts only18 classification values per window excluding3 root validations and subsequent compilation; selector constant records except scratch epoch maintenance; PJ_private_pool_total is uncollected rather than truezero for sampledMoff; empty selected skips B and M; preserved M code has new sampled inputs/opportunities, not identical trajectory; stationary conditional kernel, no universal speed or irreducibility claim\",";factorized.sampled.metadata(f);}if(strict_star_requested||strict_owner_requested){strict_star.metadata(f,bool(strict_star_requested),strict_update=="fixed_class");f<<"\"strict_star_full_owner_observer\":"<<(strict_owner_requested?"true":"false")<<",";}if(coverage_compose_requested){f<<"\"coverage_compose_requested\":"<<coverage_compose_requested<<",\"coverage_compose_active\":"<<(coverage_compose_active?"true":"false")<<",\"composed_R_calls\":"<<composed_R_calls<<",\"coverage_compose_policy\":\"ordinary complete local bank then one unchanged corrected first-return R then global switches; original random coverage branch disabled; direct IID shortcuts retained; composite stationary generally not reversible\",";}if(cohort_local_requested||cohort_selector=="uniform_union"){f<<"\"cohort_local_private_requested\":"<<cohort_local_requested<<",\"COHORT_local_private_active\":"<<((cohort_active&&cohort_local_requested)?"true":"false")<<",\"COHORT_uniform_union_active\":"<<((cohort_active&&cohort_selector=="uniform_union")?"true":"false")<<",\"COHORT_local_collection_calls\":"<<cohort.local_collect_calls<<",\"COHORT_local_collection_guard_holds\":"<<cohort.local_collect_guard_holds<<",\"COHORT_local_collection_allocation_holds\":"<<cohort.local_collect_allocation_holds<<",\"COHORT_local_collection_max_estimated_bytes\":"<<cohort.local_collect_max_bytes<<",\"COHORT_local_collection_max_scan_bound\":"<<cohort.local_collect_max_scan_bound<<",\"COHORT_local_commit_validation_calls\":"<<cohort.local_commit_validation_calls<<",\"COHORT_local_commit_validation_holds\":"<<cohort.local_commit_validation_holds<<",\"COHORT_local_commit_validation_scan_records\":\""<<GlobalDegreeWorkBatch::wide_string(cohort.local_commit_validation_scan_records)<<"\",\"COHORT_local_policy\":\"uniform fixed union degree>=2 roots; FULL current root-neighbor cohort; localarity exactly1 labels, carriedweights fixed by outside strengths; outside/shared edges excluded; sparse arity-saturated2 map with fixed-degree payload preflight; strict fullcohort precommit validation; original Full/Two counts, cache0; exact/fixed-class matched guards; stationary conditional kernel, no universal block dominance or graph-wide IID claim\",";}if(cohort_selector=="eligible_root"){f<<"\"COHORT_eligible_active\":"<<(eligible_roots.active?"true":"false")<<",\"COHORT_eligible_initial_roots\":"<<eligible_roots.initial_roots<<",\"COHORT_eligible_final_roots\":"<<eligible_roots.pool.size()<<",\"COHORT_eligible_payload_bytes\":"<<eligible_roots.payload_bytes<<",\"COHORT_eligible_support_calls\":"<<eligible_roots.support_calls<<",\"COHORT_eligible_flag_transitions\":"<<eligible_roots.flag_transitions<<",\"COHORT_eligible_neighbor_visits\":"<<eligible_roots.neighbor_visits<<",\"COHORT_eligible_adds\":"<<eligible_roots.adds<<",\"COHORT_eligible_removes\":"<<eligible_roots.removes<<",\"COHORT_eligible_checks\":"<<eligible_roots.checks<<",\"COHORT_eligible_checked_edges\":"<<eligible_roots.checked_edges<<",\"COHORT_eligible_build_cpu_seconds\":"<<eligible_roots.build_cpu_seconds<<",\"COHORT_eligible_policy\":\"uniform union of degree>=2 roots with >=2 neighboring actors holding globally degree-one labels; whole eligibility set invariant under cohort; exact eager support index includes temporary off-fibre and rollback; empty union holds; original A/R/GWS retained\",";}if(cohort_ledger_requested){f<<"\"cohort_ledger_compiler_requested\":"<<cohort_ledger_requested<<",\"COHORT_ledger_active\":"<<(cohort_active?"true":"false")<<",\"COHORT_ledger_cache_requested\":"<<cohort_cache_requested<<",\"COHORT_ledger_full_attempts\":"<<cohort.ledger_full_attempts<<",\"COHORT_ledger_two_attempts\":"<<cohort.ledger_two_attempts<<",\"COHORT_ledger_cache_hits\":"<<cohort.ledger_cache_hits<<",\"COHORT_ledger_cache_misses\":"<<cohort.ledger_cache_misses<<",\"COHORT_ledger_cache_evictions\":"<<cohort.ledger_cache_evictions<<",\"COHORT_ledger_full_cache_hits\":"<<cohort.ledger_full_cache_hits<<",\"COHORT_ledger_two_cache_hits\":"<<cohort.ledger_two_cache_hits<<",\"COHORT_ledger_guard_cache_hits\":"<<cohort.ledger_guard_cache_hits<<",\"COHORT_ledger_allocation_uncached\":"<<cohort.ledger_allocation_uncached<<",\"COHORT_ledger_full_builds\":"<<cohort.ledger_full_builds<<",\"COHORT_ledger_two_builds\":"<<cohort.ledger_two_builds<<",\"COHORT_ledger_peak_tables\":"<<cohort.ledger_peak_tables<<",\"COHORT_ledger_max_table_bytes\":"<<cohort.ledger_max_table_bytes<<",\"COHORT_ledger_reachable_states\":\""<<GlobalDegreeWorkBatch::wide_string(cohort.ledger_reachable_states)<<"\",\"COHORT_ledger_reachable_transitions\":\""<<GlobalDegreeWorkBatch::wide_string(cohort.ledger_reachable_transitions)<<"\",\"COHORT_ledger_max_reachable_states\":"<<cohort.ledger_max_reachable_states<<",\"COHORT_ledger_max_frontier_bytes\":"<<cohort.ledger_max_frontier_bytes<<",";}f<<"\"status\":\"ok\",\"design\":\"rankable_global_compiler_v21\",\"fallback_mode\":\""<<mode<<"\",\"owner_update\":\""<<owner<<"\",\"uniform_target_claim\":"<<((mode=="unconditional"&&!(regular_iid_active||exact_iid_active||xor_iid_active||global_iid_active))?"false":"true")<<",\"seed\":"<<seed<<",\"outer\":"<<N<<",\"burn\":"<<B<<",\"cpu_seconds\":"<<cpu<<",\"setup_cpu_seconds\":"<<setup_cpu<<",\"loop_cpu_seconds\":"<<loop_cpu<<",\"wall_seconds\":"<<wall<<",\"all_margins_passed\":true,\"checks\":"<<checks<<",\"joint_policy\":\""<<policy<<"\",\"composition\":\""<<composition<<"\",\"macro_reversible_guarantee\":"<<((regular_iid_active||exact_iid_active||xor_iid_active||global_iid_active||(!coverage_compose_active&&!WS_compose_active&&!residual_active&&!balanced_local&&!typed_active&&!factorized_active&&!weight_class_trade&&!global_T_active&&!degree_two_cycle_active&&!GWS_active&&!GBS_active&&(!compose||(composition!="MC"&&composition!="CM"))))?"true":"false")<<",\"R_is_outer_fixed_mixture\":"<<(!(coverage_compose_active||regular_iid_active||exact_iid_active||xor_iid_active||global_iid_active)?"true":"false")<<",\"cohort_two_class_requested\":"<<cohort_requested<<",\"COHORT_active\":"<<(cohort_active?"true":"false")<<",\"COHORT_static_no_leaves_fallback\":"<<(cohort.static_fallback?"true":"false")<<",\"COHORT_root_selector\":\""<<cohort_selector<<"\""<<",\"COHORT_profile_update\":\""<<cohort_update<<"\""<< (cohort_local_requested?",\"COHORT_policy\":\"local singleton labels within FULL root cohort, outside/shared edges fixed; existing exact full/two-class conditional counting with matched fixed-class resources; no global IID or general dominance claim\"":",\"COHORT_policy\":\"globally degree-one labels only; one-holder identity; all-permutation-positive certificate permits whole-pool uniform shuffle; otherwise full-class multinomial suffix DP when invariant resources permit, otherwise fresh pooled-label two-class DP; leaf-guided seed forgotten; uniform-root uses half orientation; fixed-class uses matched full/two geometry and resource qualification, holding selected per-actor class quotas; ordinary joint slot replaces B/M, no graph-wide IID claim\"")<<",\"COHORT_calls\":"<<cohort.calls<<",\"COHORT_seed_draws\":"<<cohort.seed_draws<<",\"COHORT_seed_dead_holds\":"<<cohort.seed_dead_holds<<",\"COHORT_empty_roots\":"<<cohort.empty_roots<<",\"COHORT_root_draws\":"<<cohort.root_draws<<",\"COHORT_row_orientation\":"<<cohort.row_orientation<<",\"COHORT_column_orientation\":"<<cohort.column_orientation<<",\"COHORT_windows\":"<<cohort.windows<<",\"COHORT_empty_pools\":"<<cohort.empty_pools<<",\"COHORT_single_actor_holds\":"<<cohort.single_actor_holds<<",\"COHORT_whole_free_calls\":"<<cohort.whole_free_calls<<",\"COHORT_single_class_calls\":"<<cohort.single_class_calls<<",\"COHORT_fixed_class_calls\":"<<cohort.fixed_class_calls<<",\"COHORT_full_attempts\":"<<cohort.full_attempts<<",\"COHORT_full_qualified\":"<<cohort.full_qualified<<",\"COHORT_full_compiled\":"<<cohort.full_compiled<<",\"COHORT_full_guard_fallbacks\":"<<cohort.full_guard_fallbacks<<",\"COHORT_two_attempts\":"<<cohort.two_attempts<<",\"COHORT_two_qualified\":"<<cohort.two_qualified<<",\"COHORT_two_compiled\":"<<cohort.two_compiled<<",\"COHORT_resource_holds\":"<<cohort.resource_holds<<",\"COHORT_allocation_holds\":"<<cohort.allocation_holds<<",\"COHORT_class_first_draws\":"<<cohort.class_first_draws<<",\"COHORT_class_second_draws\":"<<cohort.class_second_draws<<",\"COHORT_pool_total\":"<<cohort.pool_total<<",\"COHORT_max_pool\":"<<cohort.max_pool<<",\"COHORT_actors_total\":"<<cohort.actors_total<<",\"COHORT_max_actors\":"<<cohort.max_actors<<",\"COHORT_classes_total\":"<<cohort.classes_total<<",\"COHORT_max_classes\":"<<cohort.max_classes<<",\"COHORT_pruned_zero_rows\":"<<cohort.pruned_zero_rows<<",\"COHORT_profile_changes\":"<<cohort.profile_changes<<",\"COHORT_label_changes\":"<<cohort.label_changes<<",\"COHORT_root_changes\":"<<cohort.root_changes<<",\"COHORT_changes\":"<<cohort.changes<<",\"COHORT_moved_labels\":"<<cohort.moved_labels<<",\"COHORT_adjacency_pool_calls\":"<<cohort.adjacency_pool_calls<<",\"COHORT_leaf_pool_calls\":"<<cohort.leaf_pool_calls<<",\"COHORT_max_dp_cells\":"<<cohort.max_dp_cells<<",\"COHORT_max_dp_bits\":"<<cohort.max_dp_bits<<",\"COHORT_max_dp_bytes\":"<<cohort.max_dp_bytes<<",\"COHORT_max_dp_work\":"<<cohort.max_dp_work<<",\"COHORT_deficit_calls\":"<<cohort.deficit_calls<<",\"COHORT_seed_scan_records\":\""<<GlobalDegreeWorkBatch::wide_string(cohort.seed_scan_records)<<"\""<<",\"COHORT_pool_scan_records\":\""<<GlobalDegreeWorkBatch::wide_string(cohort.pool_scan_records)<<"\""<<",\"COHORT_root_scan_records\":\""<<GlobalDegreeWorkBatch::wide_string(cohort.root_scan_records)<<"\""<<",\"COHORT_dp_cells_total\":\""<<GlobalDegreeWorkBatch::wide_string(cohort.dp_cells_total)<<"\""<<",\"COHORT_dp_work_total\":\""<<GlobalDegreeWorkBatch::wide_string(cohort.dp_work_total)<<"\""<<",\"COHORT_global_leaf_count\":"<<cohort.leaf_nodes.size()<<",\"COHORT_row_leaf_labels\":"<<cohort.leaf_labels[1].size()<<",\"COHORT_column_leaf_labels\":"<<cohort.leaf_labels[0].size()<<",\"COHORT_memory_budget\":"<<CohortConditional::MEMORY_BUDGET<<",\"COHORT_cell_budget\":"<<CohortConditional::CELL_BUDGET<<",\"COHORT_work_budget\":"<<CohortConditional::WORK_BUDGET<<",\"COHORT_cpu_seconds\":"<<cohort.cpu_seconds<<",\"shared_weight_heatbath_requested\":"<<WS_requested<<",\"WS_active\":"<<(WS_active?"true":"false")<<",\"shared_weight_heatbath_compose_requested\":"<<WS_compose_requested<<",\"shared_weight_heatbath_intersection_requested\":"<<WS_intersection_requested<<",\"WS_replace_active\":"<<(WS_replace_active?"true":"false")<<",\"WS_compose_active\":"<<(WS_compose_active?"true":"false")<<",\"WS_intersection_active\":"<<(WS_intersection_active?"true":"false")<<",\"WS_policy\":\""<<(WS_compose_active?"classic BiWES positive four-cycle conditional heatbath; original A and joint bank retained; exactly once after ordinary full macro including R and before GWS; direct and certified identity shortcuts preserved; stationary composition not claimed reversible":WS_intersection_active?"classic BiWES positive four-cycle conditional heatbath; root-first and uniform common object excluding root; replaces ordinary nonidentity A slot only; support-invariant selector, no MH; direct and certified identity shortcuts preserved":"classic BiWES positive four-cycle conditional heatbath; root-first and one extra record descriptor; replaces ordinary nonidentity A slot only, direct and certified identity dispatch preserved; general composed macro not claimed reversible")<<"\""<<",\"WS_intersection_policy\":\"support-only common object excluding root; existing bitset AND if active and2wordwidth<=smallerdegree, otherwise scan smaller adjacency; representation proxy is not an optimal cost claim\""<<",\"WS_intersection_calls\":"<<ws.intersection_calls<<",\"WS_intersection_empty_holds\":"<<ws.intersection_empty_holds<<",\"WS_intersection_bitset_calls\":"<<ws.intersection_bitset_calls<<",\"WS_intersection_sparse_calls\":"<<ws.intersection_sparse_calls<<",\"WS_intersection_word_visits\":\""<<GlobalDegreeWorkBatch::wide_string(ws.intersection_word_visits)<<"\""<<",\"WS_intersection_scan_records\":\""<<GlobalDegreeWorkBatch::wide_string(ws.intersection_scan_records)<<"\""<<",\"WS_intersection_eligible_total\":\""<<GlobalDegreeWorkBatch::wide_string(ws.intersection_eligible_total)<<"\""<<",\"WS_intersection_max_eligible\":"<<ws.intersection_max_eligible<<",\"WS_intersection_partner_draws\":"<<ws.intersection_partner_draws<<",\"WS_calls\":"<<ws.calls<<",\"WS_row_orientation\":"<<ws.row_orientation<<",\"WS_column_orientation\":"<<ws.column_orientation<<",\"WS_empty_roots\":"<<ws.empty_roots<<",\"WS_root_draws\":"<<ws.root_draws<<",\"WS_partner_is_root_holds\":"<<ws.partner_is_root_holds<<",\"WS_partner_missing_holds\":"<<ws.partner_missing_holds<<",\"WS_windows\":"<<ws.windows<<",\"WS_singleton_windows\":"<<ws.singleton_windows<<",\"WS_changes\":"<<ws.changes<<",\"WS_root_neighbor_draws\":"<<ws.root_neighbor_draws<<",\"WS_partner_record_draws\":"<<ws.partner_record_draws<<",\"WS_interval_width_total\":"<<ws.interval_width_total<<",\"WS_max_interval_width\":"<<ws.max_interval_width<<",\"WS_cell_writes_attempted\":"<<ws.cell_writes_attempted<<",\"WS_changed_cell_writes\":"<<ws.changed_cell_writes<<",\"WS_root_pool_total\":"<<ws.root_pool_total<<",\"residual_cycle_refresh_requested\":"<<residual_requested<<",\"residual_cycle_active\":"<<(residual_active?"true":"false")<<",\"residual_cycle_delta\":\""<<residual_delta<<"\""<<",\"residual_cycle_policy\":\""<<(residual.scan_local?"dynamic dyadic scale selected from eligible incident max(w-1) before path; no persistent heavy index; exact entry-degree times old/new scale-level MH; cap0 deliberately holds though a prefix could be feasible; ordinary A slot only":residual.scan_mode?"fixed-support first-repeat alternating residual loop; indexed legacy unit/uniform preserved; scan modes use static positive-slack starts and active-row column filtering; dyadic_scan chooses fixed-margin power-of-two delta before path, scans decrement w>=delta+1, unique entry-degree MH; matched unit/uniform_scan use threshold1, latter keeps postpath interval ratio; no persistent heavy index in scan modes; ordinary A slot only":"fixed-support first-repeat alternating residual directed loop; decrement row-heavy eligible columns excluding incoming; increment column records excluding incoming row; dead hold, first repeat has at least4edges; exact reverse-path MH, no arbitrary cutoff; ordinary A slot only")<<"\""<<",\"RC_local_active\":"<<((residual_active&&residual.scan_local)?"true":"false")<<",\"RC_local_cap_calls\":"<<residual.local_cap_calls<<",\"RC_local_cap_zero_holds\":"<<residual.local_cap_zero_holds<<",\"RC_local_cap_scan_records\":\""<<GlobalDegreeWorkBatch::wide_string(residual.local_cap_scan_records)<<"\""<<",\"RC_local_cap_total\":\""<<GlobalDegreeWorkBatch::wide_string(residual.local_cap_total)<<"\""<<",\"RC_max_local_cap\":"<<residual.max_local_cap<<",\"RC_local_start_on_cycle_proposals\":"<<residual.local_start_on_cycle_proposals<<",\"RC_local_scale_ratio_changes\":"<<residual.local_scale_ratio_changes<<",\"RC_scan_active\":"<<((residual_active&&residual.scan_mode)?"true":"false")<<",\"RC_dyadic_active\":"<<((residual_active&&residual.scan_dyadic)?"true":"false")<<",\"RC_persistent_heavy_active\":"<<(residual.heavy.active?"true":"false")<<",\"RC_scan_row_calls\":"<<residual.scan_row_calls<<",\"RC_scan_column_calls\":"<<residual.scan_column_calls<<",\"RC_scan_records\":\""<<GlobalDegreeWorkBatch::wide_string(residual.scan_records)<<"\""<<",\"RC_scan_row_eligible\":"<<residual.scan_row_eligible<<",\"RC_scan_column_eligible\":"<<residual.scan_column_eligible<<",\"RC_scale_draws\":"<<residual.scale_draws<<",\"RC_max_scale_index\":"<<residual.max_scale_index<<",\"RC_selected_delta_total\":\""<<GlobalDegreeWorkBatch::wide_string(residual.selected_delta_total)<<"\""<<",\"RC_max_selected_delta\":"<<residual.max_selected_delta<<",\"RC_calls\":"<<residual.calls<<",\"RC_empty_starts\":"<<residual.empty_starts<<",\"RC_dead_ends\":"<<residual.dead_ends<<",\"RC_two_cycle_holds\":"<<residual.two_cycle_holds<<",\"RC_proposals\":"<<residual.proposals<<",\"RC_accepts\":"<<residual.accepts<<",\"RC_rejects\":"<<residual.rejects<<",\"RC_start_rows\":"<<residual.start_rows<<",\"RC_start_columns\":"<<residual.start_columns<<",\"RC_path_steps\":"<<residual.path_steps<<",\"RC_max_path_steps\":"<<residual.max_path_steps<<",\"RC_prefix_nodes_total\":"<<residual.prefix_nodes_total<<",\"RC_cycle_edges_total\":"<<residual.cycle_edges_total<<",\"RC_max_cycle_edges\":"<<residual.max_cycle_edges<<",\"RC_row_entry_proposals\":"<<residual.row_entry_proposals<<",\"RC_column_entry_proposals\":"<<residual.column_entry_proposals<<",\"RC_delta_total\":\""<<GlobalDegreeWorkBatch::wide_string(residual.delta_total)<<"\""<<",\"RC_max_delta\":"<<residual.max_delta<<",\"RC_changed_cell_writes\":"<<residual.changed_cell_writes<<",\"RC_accept_ratio_max_bits\":"<<residual.accept_ratio_max_bits<<",\"RC_start_pool_size\":"<<residual.starts.size()<<",\"RH_initial_records\":"<<residual.heavy.initial_records<<",\"RH_updates\":"<<residual.heavy.updates<<",\"RH_adds\":"<<residual.heavy.adds<<",\"RH_removes\":"<<residual.heavy.removes<<",\"RH_checks\":"<<residual.heavy.checks<<",\"RH_checked_entries\":"<<residual.heavy.checked_entries<<",\"RH_final_records\":"<<(residual.heavy.initial_records+residual.heavy.adds-residual.heavy.removes)<<",\"whole_private_conditional_requested\":"<<whole_private_requested<<",\"WPC_active\":"<<(whole_private_active?"true":"false")<<",\"whole_private_reuse_layout_requested\":"<<whole_reuse_requested<<",\"WPC_reuse_active\":"<<((whole_reuse_requested&&whole_private_active)?"true":"false")<<",\"WPC_reused_ledger_calls\":"<<whole_private.reused_ledger_calls<<",\"WPC_deferred_full_arrays\":"<<whole_private.deferred_full_arrays<<",\"WPC_direct_record_geometry_calls\":"<<whole_private.direct_record_geometry_calls<<",\"WPC_policy\":\"one conditional draw: whole feasible-label closed form; whole-small P<=6 grouped solver; large top-two feasible-label closed form or scaled small-slack profiles; guarded fine primary-only fallback; no B then M stages\""<<",\"WPC_calls\":"<<whole_private.calls<<",\"WPC_changes\":"<<whole_private.changes<<",\"WPC_empty_roots\":"<<whole_private.empty_roots<<",\"WPC_windows\":"<<whole_private.windows<<",\"WPC_empty_private\":"<<whole_private.empty_private<<",\"WPC_small_calls\":"<<whole_private.small_calls<<",\"WPC_single_class_calls\":"<<whole_private.single_class_calls<<",\"WPC_two_class_calls\":"<<whole_private.two_class_calls<<",\"WPC_two_compiled_calls\":"<<whole_private.two_compiled_calls<<",\"WPC_single_fallbacks\":"<<whole_private.single_fallbacks<<",\"WPC_whole_free_calls\":"<<whole_private.whole_free_calls<<",\"WPC_two_free_calls\":"<<whole_private.two_free_calls<<",\"WPC_count_calls\":"<<whole_private.count_calls<<",\"WPC_complete_options_total\":"<<whole_private.complete_options_total<<",\"WPC_max_complete_options\":"<<whole_private.max_complete_options<<",\"WPC_profiles_total\":"<<whole_private.profiles_total<<",\"WPC_max_profiles\":"<<whole_private.max_profiles<<",\"WPC_moved_private_labels\":"<<whole_private.moved_private_labels<<",\"WPC_root_changes\":"<<whole_private.root_changes<<",\"WPC_pool_total\":"<<whole_private.pool_total<<",\"WPC_max_pool\":"<<whole_private.max_pool<<",\"WPC_classes_total\":"<<whole_private.classes_total<<",\"WPC_scan_visits\":"<<whole_private.scan_visits<<",\"WPC_cpu_seconds\":"<<whole_private.cpu_seconds<<",\"WPC_two_slack_failures\":"<<whole_private.two.slack_failures<<",\"WPC_two_startup_guard_failures\":"<<whole_private.two.startup_guard_failures<<",\"WPC_two_memory_guard_failures\":"<<whole_private.two.memory_guard_failures<<",\"WPC_small_pool_cap\":"<<WholePrivateConditional::SMALL_POOL_CAP<<",\"matching_xor_requested\":"<<matching_xor<<",\"matching_xor_eligible\":"<<((joint.xor_problem&&joint.xor_problem->eligible)?"true":"false")<<",\"matching_xor_active\":"<<(xor_iid_active?"true":"false")<<",\"XOR_guard_reason\":\""<<(joint.xor_problem?joint.xor_problem->guard_reason:"not_attempted")<<"\""<<",\"XOR_build_cpu_seconds\":"<<joint.xor_build_cpu_seconds<<",\"XOR_pair_checks\":"<<(joint.xor_problem?joint.xor_problem->pair_checks:0)<<",\"XOR_candidate_pairs\":"<<(joint.xor_problem?joint.xor_problem->candidate_pairs:0)<<",\"XOR_max_leaf_occurrence\":"<<(joint.xor_problem?joint.xor_problem->max_leaf_occurrence:0)<<",\"XOR_constraint_equations\":"<<(joint.xor_problem?joint.xor_problem->constraint_equations:0)<<",\"XOR_free_components\":"<<(joint.xor_problem?joint.xor_problem->free_components:0)<<",\"XOR_exact_count\":\""<<(joint.xor_problem&&joint.xor_problem->eligible?joint.xor_problem->exact_count.get_str():"unknown")<<"\""<<",\"XOR_calls\":"<<(joint.xor_problem?joint.xor_problem->calls:0)<<",\"XOR_changes\":"<<(joint.xor_problem?joint.xor_problem->changes:0)<<",\"XOR_free_bit_draws\":"<<(joint.xor_problem?joint.xor_problem->free_bit_draws:0)<<",\"XOR_moved_leaves\":"<<(joint.xor_problem?joint.xor_problem->moved_leaves:0)<<",\"XOR_edge_writes\":"<<(joint.xor_problem?joint.xor_problem->edge_writes:0)<<",\"global_small_iid_requested\":"<<global_small_iid<<",\"global_small_iid_attempted\":"<<(whole.attempted?"true":"false")<<",\"global_small_iid_active\":"<<(global_iid_active?"true":"false")<<",\"GD_guard_failed\":"<<(whole.guard_failed?"true":"false")<<",\"GD_guard_reason\":"<<"\""<<whole.guard_reason<<"\""<<",\"GD_exact_count\":"<<"\""<<whole.exact_count<<"\""<<",\"GD_max_cells\":"<<rankable_four_margin::CELLS<<",\"GD_arena_budget_bytes\":"<<rankable_four_margin::ARENA_BYTES<<",\"GD_work_cap\":"<<rankable_four_margin::WORK_CAP<<",\"GD_integer_bits\":"<<512<<",\"GD_build_cpu_seconds\":"<<whole.build_cpu_seconds<<",\"GD_draw_cpu_seconds\":"<<whole.draw_cpu_seconds<<",\"GD_memo_states\":"<<whole.memo_states<<",\"GD_memo_hits\":"<<whole.memo_hits<<",\"GD_positive_branches\":"<<whole.positive_branches<<",\"GD_max_node_branches\":"<<whole.max_node_branches<<",\"GD_compile_work\":"<<whole.work<<",\"GD_row_candidates\":"<<whole.row_candidates<<",\"GD_row_upper_total\":"<<whole.row_upper_total<<",\"GD_raw_row_upper_score\":"<<whole.raw_row_upper_score<<",\"GD_raw_column_upper_score\":"<<whole.raw_column_upper_score<<",\"GD_dp_rows\":"<<whole.dp_rows<<",\"GD_dp_cols\":"<<whole.dp_cols<<",\"GD_arena_peak_bytes\":"<<whole.arena_peak_bytes<<",\"GD_calls\":"<<whole.calls<<",\"GD_changes\":"<<whole.changes<<",\"GD_rank_words\":"<<whole.rank_words<<",\"GD_rank_rejections\":"<<whole.rank_rejections<<",\"GD_edge_writes_attempted\":"<<whole.edge_writes_attempted<<",\"GD_changed_cell_writes\":"<<whole.changed_cell_writes<<",\"GD_transposed\":"<<(whole.transposed?"true":"false")<<",\"node_weighted_orientation\":"<<(node_weighted_orientation?"true":"false")<<",\"global_degree_work_batch_requested\":"<<global_degree_work_batch<<",\"GWB_active\":"<<(gws_batch.active?"true":"false")<<",\"GWB_repetitions\":"<<gws_batch.repetitions<<",\"GWB_degree_square_sum\":\""<<GlobalDegreeWorkBatch::wide_string(gws_batch.degree_square_sum)<<"\",\"GWB_degree_sum\":\""<<GlobalDegreeWorkBatch::wide_string(gws_batch.degree_sum)<<"\",\"GWB_fixed_edge_count\":"<<gws_batch.fixed_edge_count<<",\"GWB_macro_calls\":"<<gws_batch.macro_calls<<",\"GWB_total_gws_attempts\":"<<gws_batch.total_attempts<<",\"GWB_policy\":\""<<(gws_batch.representation_active?"ceil(3*sum_v degree_v*min(degree_v,wordwidth_if_axis_active_else_degree_v)/(4E)); fixed initialized representation proxy; not complete kernel CPU cost":"ceil(3*sum_both_sides_degree_squared/(4E)); fixed-margin work-size proxy; replaces one SES slot with a deterministic power; one identity attempt on E0; inactive without GWS or on all whole-IID branches")<<"\""<<",\"global_representation_work_batch_requested\":"<<global_representation_work_batch<<",\"GRWB_active\":"<<(gws_batch.representation_active?"true":"false")<<",\"GRWB_work_proxy\":\""<<GlobalDegreeWorkBatch::wide_string(gws_batch.representation_proxy)<<"\""<<",\"GRWB_row_axis_active\":"<<(gws_batch.representation_axis_active[0]?"true":"false")<<",\"GRWB_column_axis_active\":"<<(gws_batch.representation_axis_active[1]?"true":"false")<<",\"GRWB_row_wordwidth\":"<<gws_batch.representation_words[0]<<",\"GRWB_column_wordwidth\":"<<gws_batch.representation_words[1]<<",\"GRWB_effective_repetitions\":"<<gws_batch.repetitions<<",\"GRWB_policy\":\"immutable initialized support representation; pervertex ell=min(fixed_degree,axis.wordwidth) if active else fixed_degree; proxy=sum(degree*ell); ceil(3proxy/(4E)); E0 one identity; skipped on all whole-IID branches; not solver/label/index/observer cost\""<<",\"global_bridge_swap_requested\":"<<global_bridge_swap<<",\"GBS_active\":"<<(GBS_active?"true":"false")<<",\"GBS_standalone_reversible\":true,\"GBS_dispatch_policy\":\"once after GWS at each general macro including R; skipped on all whole-IID branches\",\"GBS_selector_policy\":\"uniform side and fixed degree>=2 center; ordered distinct center neighbors; uniform outside neighbor on each; invalid descriptors hold without retry; equal weights allowed\",\"GBS_calls\":"<<gbs.calls<<",\"GBS_changes\":"<<gbs.changes<<",\"GBS_empty_centers\":"<<gbs.empty_centers<<",\"GBS_empty_outside_neighbors\":"<<gbs.empty_outside_neighbors<<",\"GBS_same_actor_holds\":"<<gbs.same_actor_holds<<",\"GBS_cross_positive_holds\":"<<gbs.cross_positive_holds<<",\"GBS_nonpositive_compensation_holds\":"<<gbs.nonpositive_compensation_holds<<",\"GBS_row_orientation\":"<<gbs.row_orientation<<",\"GBS_column_orientation\":"<<gbs.column_orientation<<",\"GBS_equal_weight_pairs\":"<<gbs.equal_weight_pairs<<",\"GBS_edge_writes_attempted\":"<<gbs.edge_writes_attempted<<",\"GBS_changed_cell_writes\":"<<gbs.changed_cell_writes<<",\"GBS_center_pool_total\":"<<gbs.center_pool_total<<",\"global_equal_weight_switch_requested\":"<<global_equal_weight_switch<<",\"GWS_active\":"<<(GWS_active?"true":"false")<<",\"GWS_class_balanced_requested\":"<<class_balanced_requested<<",\"GWS_class_balanced_active\":"<<(gws.class_balanced?"true":"false")<<",\"GWS_balanced_calls\":"<<gws.balanced_calls<<",\"GWS_no_eligible_class_holds\":"<<gws.no_eligible_class_holds<<",\"GWS_eligible_classes_final\":"<<g.switch_weights.size()<<",\"GWS_class_index_adds\":"<<g.switch_class_adds<<",\"GWS_class_index_removes\":"<<g.switch_class_removes<<",\"unlabeled_structure_trace_requested\":"<<structure_trace_requested<<",\"structure_trace_active\":"<<(structure_observer.active?"true":"false")<<",\"structure_trace_snapshots\":"<<structure_observer.snapshots<<",\"structure_trace_postburn_snapshots\":"<<structure_observer.postburn_snapshots<<",\"exact_structure_accumulator_updates\":"<<g.exact_sumw2_updates<<",\"GWS_standalone_reversible\":true,\"GWS_preserves_node_weight_histograms\":true,\"GWS_after_coverage_R\":true,\"GWS_dispatch_policy\":\"once after each general macro including R; skipped on all whole-IID branches\",\"GWS_selector_policy\":\""<<(gws.conditional_requested?"uniform positive seed edge, uniform distinct equal-weight second edge fixes rowpair/w; same-row/singleton hold; raw-valid immediate switch; else complete opposite-zero sameweight A/B uniform, empty hold":"uniform positive seed edge, uniform distinct equal-weight second edge; singleton/same endpoint/occupied cross hold without retry")<<"\",\"GWS_calls\":"<<gws.calls<<",\"GWS_changes\":"<<gws.changes<<",\"GWS_no_edges\":"<<gws.no_edges<<",\"GWS_singleton_weight_class\":"<<gws.singleton_weight_class<<",\"GWS_same_endpoint_holds\":"<<gws.same_endpoint_holds<<",\"GWS_cross_positive_holds\":"<<gws.cross_positive_holds<<",\"GWS_edge_writes\":"<<gws.edge_writes<<",\"GWS_selected_weight_class_size_total\":"<<gws.selected_weight_class_size_total<<",\"GWS_max_selected_weight_class\":"<<gws.max_selected_weight_class<<",\"disable_factorized_joint\":"<<disable_factorized_joint<<",\"factorized_mode\":\""<<factorized_mode<<"\""<<",\"factorized_local_compile_requested\":"<<factorized_local_compile<<",\"factorized_active\":"<<(factorized_original_active?"true":"false")<<",\"factorized_profile\":"<<factorized_profile<<",\"PJ_calls\":"<<factorized.calls<<",\"PJ_changes\":"<<factorized.changes<<",\"PJ_empty_roots\":"<<factorized.empty_roots<<",\"PJ_descriptor_windows\":"<<factorized.descriptor_windows<<",\"PJ_empty_selected\":"<<factorized.empty_selected<<",\"PJ_weight_tie_choices\":"<<factorized.weight_tie_choices<<",\"PJ_scan_visits\":"<<factorized.scan_visits<<",\"PJ_private_pool_total\":"<<factorized.private_pool_total<<",\"PJ_selected_private_total\":"<<factorized.selected_private_total<<",\"PJ_max_selected_private\":"<<factorized.max_selected_private<<",\"PJ_complement_visits\":"<<factorized.complement_visits<<",\"PJ_M_factor_windows\":"<<factorized.M_factor_windows<<",\"PJ_M_nontrivial_windows\":"<<factorized.M_nontrivial_windows<<",\"PJ_M_empty_windows\":"<<factorized.M_empty_windows<<",\"PJ_M_oneholder_windows\":"<<factorized.M_oneholder_windows<<",\"PJ_M_objects_total\":"<<factorized.M_objects_total<<",\"PJ_max_M_objects\":"<<factorized.max_M_objects<<",\"PJ_B_compiled_windows\":"<<factorized.compiled_windows<<",\"PJ_B_completions\":"<<factorized.completions<<",\"PJ_max_B_completions\":"<<factorized.max_completions<<",\"PJ_B_enumeration_nodes\":"<<factorized.enumeration_nodes<<",\"PJ_B_closedform_windows\":"<<factorized.B_closedform_windows<<",\"PJ_B_DFS_windows\":"<<factorized.B_DFS_windows<<",\"PJ_M_compiled_windows\":"<<factorized.equal_compiled_calls<<",\"PJ_subset_draws\":"<<factorized.subset_draws<<",\"PJ_disabled_B_windows\":"<<factorized.disabled_B_windows<<",\"PJ_disabled_M_windows\":"<<factorized.disabled_M_windows<<",\"PJ_B_changes\":"<<factorized.B_factor_changes<<",\"PJ_M_changes\":"<<factorized.M_factor_changes<<",\"PJ_both_changes\":"<<factorized.both_factor_changes<<",\"PJ_B_moved_labels\":"<<factorized.B_moved_labels<<",\"PJ_M_moved_labels\":"<<factorized.M_moved_labels<<",\"PJ_root_weight_changes\":"<<factorized.root_weight_changes<<",\"PJ_cpu_seconds\":"<<factorized.cpu_seconds<<",\"PJ_descriptor_cpu_seconds\":"<<factorized.descriptor_cpu_seconds<<",\"PJ_B_solve_cpu_seconds\":"<<factorized.B_solve_cpu_seconds<<",\"PJ_M_solve_cpu_seconds\":"<<factorized.M_solve_cpu_seconds<<",\"PJ_joint_write_cpu_seconds\":"<<factorized.joint_write_cpu_seconds<<",\"typed_mode\":\""<<typed_mode<<"\""<<",\"TL_disabled_equal_calls\":"<<typed.disabled_equal_calls<<",\"TL_disabled_enumerated_calls\":"<<typed.disabled_enumerated_calls<<",\"TL_equal_compiled_calls\":"<<typed.equal_compiled_calls<<",\"TL_equal_changes\":"<<typed.equal_changes<<",\"TL_enumerated_changes\":"<<typed.enumerated_changes<<",\"TL_equal_moved_labels\":"<<typed.equal_moved_labels<<",\"TL_enumerated_moved_labels\":"<<typed.enumerated_moved_labels<<",\"typed_local_compile_requested\":"<<typed_local_compile<<",\"typed_active\":"<<(typed_active?"true":"false")<<",\"TL_calls\":"<<typed.calls<<",\"TL_changes\":"<<typed.changes<<",\"TL_equal_calls\":"<<typed.equal_calls<<",\"TL_enumerated_calls\":"<<typed.enumerated_calls<<",\"TL_empty_roots\":"<<typed.empty_roots<<",\"TL_singletons\":"<<typed.singletons<<",\"TL_equal_singletons\":"<<typed.equal_singletons<<",\"TL_equal_objects_total\":"<<typed.equal_objects_total<<",\"TL_max_equal_objects\":"<<typed.max_equal_objects<<",\"TL_max_equal_quota\":"<<typed.max_equal_quota<<",\"TL_private_pool_total\":"<<typed.private_pool_total<<",\"TL_scan_visits\":"<<typed.scan_visits<<",\"TL_epoch_resets\":"<<typed.epoch_resets<<",\"TL_moved_labels\":"<<typed.moved_labels<<",\"TL_subset_draws\":"<<typed.subset_draws<<",\"TL_group_entries_total\":"<<typed.group_entries_total<<",\"TL_max_groups\":"<<typed.max_groups<<",\"TL_group_table_slots\":"<<typed.table.size()<<",\"TL_group_table_peak_slots\":"<<typed.max_table_slots<<",\"TL_group_epoch_resets\":"<<typed.group_epoch_resets<<",\"TL_compiled_windows\":"<<typed.compiled_windows<<",\"TL_completions\":"<<typed.completions<<",\"TL_max_completions\":"<<typed.max_completions<<",\"TL_enumeration_nodes\":"<<typed.enumeration_nodes<<",\"TL_selected_private_total\":"<<typed.selected_private_total<<",\"TL_max_selected_private\":"<<typed.max_selected_private<<",\"TL_cpu_seconds\":"<<typed.cpu_seconds<<",\"TL_scan_cpu_seconds\":"<<typed.scan_cpu_seconds<<",\"TL_group_cpu_seconds\":"<<typed.group_cpu_seconds<<",\"TL_solve_cpu_seconds\":"<<typed.solve_cpu_seconds<<",\"TL_write_cpu_seconds\":"<<typed.write_cpu_seconds<<",\"global_weight_class_trade_requested\":"<<global_weight_class_trade<<",\"global_T_active\":"<<(global_T_active?"true":"false")<<",\"GT_class_policy\":\"uniform positive seed edge, weight size-biased q/E; uniform other equal-weight record\""<<",\"GT_calls\":"<<global_trade.calls<<",\"GT_changes\":"<<global_trade.changes<<",\"GT_no_edges\":"<<global_trade.no_edges<<",\"GT_singleton_global_class\":"<<global_trade.singleton_global_class<<",\"GT_same_node_holds\":"<<global_trade.same_node_holds<<",\"GT_seed_same_object\":"<<global_trade.seed_same_object<<",\"GT_scan_visits\":"<<global_trade.scan_visits<<",\"GT_private_total\":"<<global_trade.private_total<<",\"GT_max_private\":"<<global_trade.max_private<<",\"GT_singleton_private\":"<<global_trade.singleton_private<<",\"GT_subset_draws\":"<<global_trade.subset_draws<<",\"GT_moved_labels\":"<<global_trade.moved_labels<<",\"GT_cpu_seconds\":"<<global_trade.cpu_seconds<<",\"GT_index_build_cpu_seconds\":"<<global_trade.index_build_cpu_seconds<<",\"GT_index_updates\":"<<global_trade.index_updates<<",\"GT_index_adds\":"<<global_trade.index_adds<<",\"GT_index_removes\":"<<global_trade.index_removes<<",\"GT_index_initial_entries\":"<<global_trade.index_initial_entries<<",\"GT_index_current_entries\":"<<global_trade.positions.size()<<",\"GT_index_peak_entries\":"<<global_trade.index_peak_entries<<",\"GT_node_group_count\":"<<global_trade.node_group_count<<",\"GT_node_group_peak\":"<<global_trade.node_group_peak<<",\"GT_index_checks\":"<<global_trade.index_checks<<",\"GT_index_checked_entries\":"<<global_trade.index_checked_entries<<",\"GT_preserves_node_weight_histograms\":true"<<",\"weight_class_nontrivial_requested\":"<<weight_class_nontrivial<<",\"T_nontrivial_filter_active\":"<<((weight_class_trade&&weight_class_nontrivial&&!regular_iid_active&&!exact_iid_active&&!xor_iid_active&&!global_iid_active)?"true":"false")<<",\"T_empty_eligible\":"<<value_trade.empty_eligible<<",\"T_eligible_records_total\":"<<value_trade.eligible_records_total<<",\"T_eligible_classes_total\":"<<value_trade.eligible_classes_total<<",\"T_max_eligible_records\":"<<value_trade.max_eligible_records<<",\"weight_class_trade_requested\":"<<weight_class_trade<<",\"T_calls\":"<<value_trade.calls<<",\"T_changes\":"<<value_trade.changes<<",\"T_empty_roots\":"<<value_trade.empty_roots<<",\"T_empty_private\":"<<value_trade.empty_private<<",\"T_singletons\":"<<value_trade.singletons<<",\"T_scan_visits\":"<<value_trade.scan_visits<<",\"T_epoch_resets\":"<<value_trade.epoch_resets<<",\"T_private_total\":"<<value_trade.private_total<<",\"T_class_total\":"<<value_trade.class_total<<",\"T_max_class\":"<<value_trade.max_class<<",\"T_subset_draws\":"<<value_trade.subset_draws<<",\"T_moved_labels\":"<<value_trade.moved_labels<<",\"T_cpu_seconds\":"<<value_trade.cpu_seconds<<",\"T_preserves_node_weight_histograms\":true,\"balanced_local_requested\":"<<balanced_local<<",\"balanced_private_per_person\":"<<balanced_cap<<",\"B_calls\":"<<balanced.calls<<",\"B_changes\":"<<balanced.changes<<",\"B_empty_roots\":"<<balanced.empty_roots<<",\"B_completions\":"<<balanced.completions<<",\"B_singletons\":"<<balanced.singletons<<",\"B_compiled_windows\":"<<balanced.compiled_windows<<",\"B_privateowner_counts\":"<<balanced.owner_count_json()<<",\"B_private_pool_total\":"<<balanced.private_pool_total<<",\"B_selected_private_total\":"<<balanced.selected_private_total<<",\"B_max_completions\":"<<balanced.max_completions<<",\"B_max_selected_private\":"<<balanced.max_selected_private<<",\"B_scan_visits\":"<<balanced.scan_visits<<",\"B_enumeration_nodes\":"<<balanced.enumeration_nodes<<",\"B_cpu_seconds\":"<<balanced.cpu_seconds<<",\"B_epoch_resets\":"<<balanced.epoch_resets<<",\"regular_no_rejection_requested\":"<<regular_no_rejection<<",\"regular_no_rejection_active\":"<<(regular.no_rejection_active?"true":"false")<<",\"regular_cache_guard_fallback\":"<<(regular.cache_guard_fallback?"true":"false")<<",\"regular_cache_budget_bytes\":"<<regular.cache_budget_bytes<<",\"regular_cache_bytes\":"<<regular.cache_bytes<<",\"regular_cache_workspace_bound_bytes\":"<<regular.cache_workspace_bound_bytes<<",\"regular_cache_build_terms\":"<<regular.cache_build_terms<<",\"regular_cache_build_cpu_seconds\":"<<regular.cache_build_cpu_seconds<<",\"regular_derangement_steps\":"<<regular.derangement_steps<<",\"regular_two_cycle_steps\":"<<regular.two_cycle_steps<<",\"regular_insertion_steps\":"<<regular.insertion_steps<<",\"regular_bernoulli_words\":"<<regular.bernoulli_words<<",\"regular_boundary_hits\":"<<regular.boundary_hits<<",\"regular_refinement_words\":"<<regular.refinement_words<<",\"regular_ratio_rebuilds\":"<<regular.ratio_rebuilds<<",\"regular_iid_requested\":"<<regular_iid<<",\"regular_iid_eligible\":"<<(regular.eligible?"true":"false")<<",\"regular_iid_active\":"<<(regular_iid_active?"true":"false")<<",\"whole_graph_exact_iid\":"<<((regular_iid_active||exact_iid_active||xor_iid_active||global_iid_active)?"true":"false")<<",\"regular_active_n\":"<<regular.n<<",\"regular_strength\":"<<regular.strength<<",\"regular_direct_calls\":"<<regular.calls<<",\"regular_permutation_attempts\":"<<regular.permutation_attempts<<",\"regular_fixedpoint_rejections\":"<<regular.fixedpoint_rejections<<",\"regular_rejected_fixedpoints\":"<<regular.rejected_fixedpoints<<",\"regular_crp_insertions\":"<<regular.crp_insertions<<",\"regular_object_shuffle_draws\":"<<regular.object_shuffle_draws<<",\"regular_cycles_drawn\":"<<regular.cycles_drawn<<",\"regular_last_cycles\":"<<regular.last_cycles<<",\"regular_edge_writes\":"<<regular.edge_writes<<",\"matching_sweep_requested\":"<<matching_sweep<<",\"exact_iid_active\":"<<(exact_iid_active?"true":"false")<<",\"sweep_dispatches\":"<<sweep_dispatches<<",\"sweep_component_draws\":"<<(exact_iid_active?joint.matching_calls:0)<<",\"matching_eligible\":"<<(joint.matching_eligible?"true":"false")<<",\"matching_components\":"<<joint.components.size()<<",\"feasibility_checks\":"<<joint.feasibility_checks<<",\"feasibility_pairs\":"<<joint.feasibility_pairs<<",\"component_cache_count\":"<<joint.component_cache_count<<",\"component_cache_bytes\":"<<joint.component_cache_bytes<<",\"component_factor_count_known\":"<<(joint.factor_count_known?"true":"false")<<",\"component_factor_count_product\":\""<<(joint.factor_count_known?joint.factor_count_product.get_str():"unknown")<<"\",\"matching_calls\":"<<joint.matching_calls<<",\"matching_changed\":"<<joint.matching_changed<<",\"matching_patch_builds\":"<<joint.matching_patch_builds<<",\"matching_cache_hits\":"<<joint.matching_cache_hits<<",\"matching_masks_built\":"<<joint.matching_masks_built<<",\"matching_completion_total\":"<<joint.matching_completion_total<<",\"two_weight_complement_requested\":"<<tw_requested<<",\"TW_active\":"<<((two_weight_complement&&factorized_original_active&&!whole_private_active&&!disable_M_requested&&factorized_mode!="heterogeneous-only")?"true":"false")<<",\"TW_policy\":\""<<(pair_conditional_profile_mode()?"post-B exact pair geometry; ALL two-class blocks use deterministic pair conditionals or fixed-profile label refresh; no slack6 enumeration/wide rejection; scalar counting/label/commit CPU charged":pair_specific_complement?"post-B pair geometry; slack<=6 exact mass-counted profiles; optional slack>6 one quota-labelled proposal, legal root ledgers commit, illegal old single-class fallback; all work charged":"B exact conditional committed first; M most-frequent second weight class, exact root-compensated profile mass times uniform two-class labels; class-invariant small-slack and resource guards fall back old single-class M; not independent B-times-M product")<<"\""<<",\"TW_startup_work_budget\":"<<TwoWeightComplement::STARTUP_WORK_BUDGET<<",\"TW_estimated_memory_budget\":"<<TwoWeightComplement::MEMORY_BUDGET_BYTES<<",\"PJ_M_root_weight_changes\":"<<factorized.M_root_weight_changes<<",\"TW_primary_prefilter_active\":"<<((two_weight_complement&&!budget_compatible_complement&&!disable_M_requested)?"true":"false")<<",\"TW_primary_probe_calls\":"<<factorized.primary_probe_calls<<",\"TW_primary_probe_visits\":"<<factorized.primary_probe_visits<<",\"TW_primary_probe_empty\":"<<factorized.primary_probe_empty<<",\"two_weight_scaled_counts_requested\":"<<tw_scaled_requested<<",\"TW_scaled_active\":"<<((!pair_conditional_profile_mode()&&two_weight_scaled_counts&&two_weight_complement&&factorized_original_active&&!disable_M_requested&&factorized_mode!="heterogeneous-only")?"true":"false")<<",\"TW_scaled_policy\":\"cancel per-actor binomial constants across at most7 cached entries; exact relative profile masses, not full graph counts; same conditional law where old guards pass but different rank/RNG range; expanded exact eligibility where old payload/work guard fails\""<<",\"TW_scaled_count_attempts\":"<<factorized.tw.scaled_count_attempts<<",\"TW_scaled_compiled_windows\":"<<factorized.tw.scaled_compiled_windows<<",\"TW_scaled_startup_multiplications\":"<<factorized.tw.scaled_startup_multiplications<<",\"TW_scaled_cache_steps\":"<<factorized.tw.scaled_cache_steps<<",\"TW_scaled_max_relative_mass_bits\":"<<factorized.tw.scaled_max_relative_mass_bits<<",\"TW_scaled_max_payload_estimate\":"<<factorized.tw.scaled_max_payload_estimate<<",\"two_weight_slack_certificate_requested\":"<<tw_certificate_requested<<",\"TWC_active\":"<<((two_weight_slack_certificate&&!pair_specific_complement&&two_weight_complement&&factorized_original_active&&!disable_M_requested&&factorized_mode!="heterogeneous-only")?"true":"false")<<",\"TWC_policy\":\""<<(pair_specific_complement?"disabled: pair-specific post-B geometry replaces whole-pool sufficient certificate":"C3 oldM; C4to9 certify; C>9 whole private including U gcd relative to selected modal w0, gcd1 early oldM; gcd>1 sum floor((root_i-1)/g) in1to6 certifies; <=1 actual profile oldM; no retry, conservative sufficient certificate")<<"\""<<",\"TWC_calls\":"<<factorized.certificate.calls<<",\"TWC_C_equal_three\":"<<factorized.certificate.C_equal_three<<",\"TWC_small_public_sum_passes\":"<<factorized.certificate.small_public_sum_passes<<",\"TWC_gcd_scans\":"<<factorized.certificate.gcd_scans<<",\"TWC_gcd_weight_visits\":"<<factorized.certificate.gcd_weight_visits<<",\"TWC_gcd_one_fallbacks\":"<<factorized.certificate.gcd_one_fallbacks<<",\"TWC_gcd_zero_fallbacks\":"<<factorized.certificate.gcd_zero_fallbacks<<",\"TWC_zero_bound_fallbacks\":"<<factorized.certificate.zero_bound_fallbacks<<",\"TWC_large_bound_fallbacks\":"<<factorized.certificate.large_bound_fallbacks<<",\"TWC_spaced_weight_passes\":"<<factorized.certificate.spaced_weight_passes<<",\"TWC_certificate_passes\":"<<factorized.certificate.certificate_passes<<",\"TWC_certificate_fallbacks\":"<<factorized.certificate.certificate_fallbacks<<",\"TWC_single_profile_fallbacks\":"<<factorized.certificate.single_profile_fallbacks<<",\"TWC_generalized_draws\":"<<factorized.certificate.generalized_draws<<",\"TWC_max_T\":"<<factorized.certificate.max_T<<",\"TWC_max_gcd\":"<<factorized.certificate.max_gcd<<",\"TWC_max_public_sum\":\""<<GlobalDegreeWorkBatch::wide_string(__uint128_t(factorized.certificate.max_public_sum))<<"\""<<",\"TW_calls\":"<<factorized.tw.calls<<",\"TW_no_other_class\":"<<factorized.tw.no_other_class<<",\"TW_empty_primary_class\":"<<factorized.tw.empty_primary_class<<",\"TW_other_class_choices\":"<<factorized.tw.other_class_choices<<",\"TW_complement_records_total\":"<<factorized.tw.complement_records_total<<",\"TW_other_classes_total\":"<<factorized.tw.other_classes_total<<",\"TW_slack_eligible\":"<<factorized.tw.slack_eligible<<",\"TW_slack_failures\":"<<factorized.tw.slack_failures<<",\"TW_startup_guard_failures\":"<<factorized.tw.startup_guard_failures<<",\"TW_memory_guard_failures\":"<<factorized.tw.memory_guard_failures<<",\"TW_old_single_class_fallbacks\":"<<factorized.tw.old_single_class_fallbacks<<",\"TW_compiled_windows\":"<<factorized.tw.compiled_windows<<",\"TW_profiles_total\":"<<factorized.tw.profiles_total<<",\"TW_max_profiles\":"<<factorized.tw.max_profiles<<",\"TW_max_slack\":"<<factorized.tw.max_slack<<",\"TW_max_examined_slack\":"<<factorized.tw.max_examined_slack<<",\"TW_max_high_objects\":"<<factorized.tw.max_high_objects<<",\"TW_max_startup_work_score\":"<<factorized.tw.max_startup_work_score<<",\"TW_max_estimated_bytes\":"<<factorized.tw.max_estimated_bytes<<",\"TW_max_count_bits\":"<<factorized.tw.max_count_bits<<",\"TW_profile_draws\":"<<factorized.tw.profile_draws<<",\"TW_profile_changes\":"<<factorized.tw.profile_changes<<",\"TW_label_changes\":"<<factorized.tw.label_changes<<",\"TW_root_changes\":"<<factorized.tw.root_changes<<",\"TW_changes\":"<<factorized.tw.changes<<",\"TW_moved_labels\":"<<factorized.tw.moved_labels<<",\"TW_root_writes\":"<<factorized.tw.root_writes<<",\"TW_compile_cpu_seconds\":"<<factorized.tw.compile_cpu_seconds<<",\"TW_draw_cpu_seconds\":"<<factorized.tw.draw_cpu_seconds<<",\"TW_commit_cpu_seconds\":"<<factorized.tw.commit_cpu_seconds<<",\"TW_fallback_draw_cpu_seconds\":"<<factorized.tw.fallback_draw_cpu_seconds<<",\"dynamic_support_bitset_scene_requested\":"<<bitset_scene_requested<<",\"SB_general_consumer_active\":"<<(scene_bits.consumer_active?"true":"false")<<",\"SB_row_axis_active\":"<<(scene_bits.axis[0].active?"true":"false")<<",\"SB_column_axis_active\":"<<(scene_bits.axis[1].active?"true":"false")<<",\"SB_active\":"<<(scene_bits.active()?"true":"false")<<",\"SB_index_policy\":\"two axes share64MiB support-word payload budget; input E>=actor_count*ceil(opposite_count/64); per-call sparse fallback if3*wordwidth>three actual degrees; private pools sorted by live adjacency positions; no selector or RNG change\",\"SB_memory_budget_bytes\":"<<SupportSceneBitset::MEMORY_BUDGET_BYTES<<",\"SB_build_axis_attempts\":"<<scene_bits.build_axis_attempts<<",\"SB_density_guard_axes\":"<<scene_bits.density_guard_axes<<",\"SB_memory_guard_axes\":"<<scene_bits.memory_guard_axes<<",\"SB_allocation_guard_axes\":"<<scene_bits.allocation_guard_axes<<",\"SB_payload_bytes\":"<<scene_bits.payload_bytes<<",\"SB_initial_entries\":"<<scene_bits.initial_entries<<",\"SB_support_transition_calls\":"<<scene_bits.support_transition_calls<<",\"SB_axis_bit_updates\":"<<scene_bits.axis_bit_updates<<",\"SB_calls\":"<<scene_bits.calls<<",\"SB_bitset_calls\":"<<scene_bits.bitset_calls<<",\"SB_sparse_axis_calls\":"<<scene_bits.sparse_axis_calls<<",\"SB_sparse_cost_calls\":"<<scene_bits.sparse_cost_calls<<",\"SB_word_visits\":"<<scene_bits.word_visits<<",\"SB_private_labels\":"<<scene_bits.private_labels<<",\"SB_max_private_labels\":"<<scene_bits.max_private_labels<<",\"SB_checks\":"<<scene_bits.checks<<",\"SB_checked_words\":"<<scene_bits.checked_words<<",\"SB_checked_entries\":"<<scene_bits.checked_entries<<",\"SB_build_cpu_seconds\":"<<scene_bits.build_cpu_seconds<<",\"SB_row_wordwidth\":"<<scene_bits.axis[0].words<<",\"SB_column_wordwidth\":"<<scene_bits.axis[1].words<<",\"minimal_anchor_window_requested\":"<<minimal_anchor_requested<<",\"MA_active\":"<<((minimal_anchor_window&&!UA_active&&!residual_active&&!WS_replace_active&&!regular_iid_active&&!exact_iid_active&&!xor_iid_active&&!global_iid_active&&!disableA&&!identity)?"true":"false")<<",\"MA_calls\":"<<algorithm.MA_calls<<",\"MA_degenerate_holds\":"<<algorithm.MA_degenerate_holds<<",\"MA_degree_one_holds\":"<<algorithm.MA_degree_one_holds<<",\"MA_windows\":"<<algorithm.MA_windows<<",\"MA_neighbor_draws\":"<<algorithm.MA_neighbor_draws<<",\"MA_width_two\":"<<algorithm.MA_width_two<<",\"MA_width_three\":"<<algorithm.MA_width_three<<",\"MA_max_columns\":"<<algorithm.MA_max_columns<<",\"MA_root_shared_interval\":"<<algorithm.MA_root_shared_interval<<",\"MA_two_private_owner\":"<<algorithm.MA_two_private_owner<<",\"MA_mixed_shared_private\":"<<algorithm.MA_mixed_shared_private<<",\"MA_two_shared\":"<<algorithm.MA_two_shared<<",\"MA_changes\":"<<algorithm.MA_changes<<",\"MA_FSDP_attempts\":"<<algorithm.MA_FSDP_attempts<<",\"MA_FSDP_calls\":"<<algorithm.MA_FSDP_calls<<",\"MA_IE_calls\":"<<algorithm.MA_IE_calls<<",\"MA_FSDP_build_cpu_seconds\":"<<algorithm.MA_FSDP_build_cpu_seconds<<",\"MA_FSDP_draw_cpu_seconds\":"<<algorithm.MA_FSDP_draw_cpu_seconds<<",\"fixed_support_dp_requested\":"<<fixed_support_dp_requested<<",\"FSDP_policy_active\":"<<((fixed_support_dp&&policy=="certified")?"true":"false")<<",\"FSDP_memory_budget_bytes\":"<<FixedSupportSuffixDP::MEMORY_BUDGET_BYTES<<",\"FSDP_cell_budget\":"<<FixedSupportSuffixDP::CELL_BUDGET<<",\"FSDP_attempts\":"<<algorithm.FSDP_attempts<<",\"FSDP_calls\":"<<algorithm.FSDP_calls<<",\"FSDP_nontrivial\":"<<algorithm.FSDP_nontrivial<<",\"FSDP_changes\":"<<algorithm.FSDP_changes<<",\"FSDP_flipped\":"<<algorithm.FSDP_flipped<<",\"FSDP_resource_failures\":"<<algorithm.FSDP_resource_failures<<",\"FSDP_guard_cell\":"<<algorithm.FSDP_guard_cell<<",\"FSDP_guard_memory\":"<<algorithm.FSDP_guard_memory<<",\"FSDP_guard_allocation\":"<<algorithm.FSDP_guard_allocation<<",\"FSDP_total_cells\":"<<algorithm.FSDP_total_cells<<",\"FSDP_max_cells\":"<<algorithm.FSDP_max_cells<<",\"FSDP_max_estimated_bytes\":"<<algorithm.FSDP_max_estimated_bytes<<",\"FSDP_max_count_bits\":"<<algorithm.FSDP_max_count_bits<<",\"FSDP_build_cpu_seconds\":"<<algorithm.FSDP_build_cpu_seconds<<",\"FSDP_draw_cpu_seconds\":"<<algorithm.FSDP_draw_cpu_seconds<<",\"certified_A_only_calls\":"<<algorithm.certified_A_only_calls<<",\"disable_A\":"<<disableA<<",\"disabled_A_dispatches\":"<<algorithm.disabled_A_dispatches<<",\"local_identity_holds\":"<<algorithm.local_identity_holds<<",\"window\":\""<<window<<"\",\"local_steps\":"<<local_steps<<",\"global_small_calls\":"<<algorithm.global_small_calls<<",\"changed_macro\":"<<changed_macro<<",\"cycle_compose\":"<<compose<<",\"cycle_when_maxdegree_two_requested\":"<<cycle_when_maxdegree_two<<",\"fixed_maxdegree_at_most_two\":"<<(degree_two_margin?"true":"false")<<",\"cycle_when_maxdegree_two_active\":"<<(degree_two_cycle_active?"true":"false")<<",\"certificate_A_identity\":"<<(identity?"true":"false")<<",\"certified_dispatches\":"<<algorithm.certified_dispatches<<",\"changed_outer\":"<<e.stat.changed_outer<<",\"buffer_calls\":"<<joint.calls<<",\"buffer_changed\":"<<joint.changed<<",\"fallback_calls\":"<<joint.fallback_calls<<",\"fallback_changed\":"<<joint.fallback_changed<<",\"anchor_calls\":"<<e.stat.block_calls<<",\"anchor_lazy\":0,\"block_calls\":"<<e.stat.block_calls<<",\"block_changed\":"<<e.stat.block_changed<<",\"coverage_calls\":"<<rcalls<<",\"first_return_inner_steps\":"<<e.stat.inner<<",\"first_return_returns\":"<<e.stat.returned<<",\"cycle_calls\":"<<cycle.calls<<",\"cycle_changed\":"<<cycle.changed<<",\"orbit_calls\":0,\"trade_calls\":0,\"A_holds\":"<<algorithm.A_holds<<",\"J_proposals\":"<<algorithm.J_proposals<<",\"J_changed_proposals\":"<<algorithm.J_changed_proposals<<",\"J_accepts\":"<<algorithm.J_accepts<<",\"J_rejects\":"<<algorithm.J_rejects<<",\"reverse_invalid\":"<<algorithm.reverse_invalid<<",\"reverse_zero_stay\":"<<algorithm.reverse_zero_stay<<",\"accepted_J_changes\":"<<algorithm.accepted_J_changes<<",\"self_count_calls\":"<<algorithm.self_count_calls<<",\"reverse_count_calls\":"<<algorithm.reverse_count_calls<<",\"rollback_cells\":"<<algorithm.rollback_cells<<",\"rss_kib\":"<<proc_memory("VmHWM")<<"}\n";coverage_kernel.save(out,e);if((coverage_kernel.mode==6||coverage_kernel.mode==7||coverage_kernel.mode==8)){std::ofstream q(out+".guided.json");auto&c=coverage_kernel.guide;q<<"{\"background_draws\":"<<c.background_draws<<",\"defect_draws\":"<<c.defect_draws<<",\"second_uniform_draws\":"<<c.second_uniform_draws<<",\"vertex_refreshes\":"<<c.vertex_refreshes<<",\"verified_rollbacks\":"<<c.verified_rollbacks<<",\"final_sparse_mass\":"<<c.mass<<",\"final_badmap_size\":"<<c.badmap.size()<<"}\n";if(!q)throw std::runtime_error("guided audit write failure");}if(!f)throw std::runtime_error("report write");return 0;
 }catch(const std::exception&ex){std::cerr<<ex.what()<<'\n';return 1;}}

#endif  
