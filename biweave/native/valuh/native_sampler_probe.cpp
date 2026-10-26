 
 
#include <memory>

#include <algorithm>
#include <array>
#include <chrono>
#include <cctype>
#include <cmath>
#include <cstdint>
#include <fstream>
#include <iomanip>
#include <iostream>
#include <limits>
#include <map>
#include <random>
#include <sstream>
#include <stdexcept>
#include <string>
#include <unordered_map>
#include <unordered_set>
#include <vector>
using I=int64_t; using U=uint64_t;using S128=__int128_t;
 
struct Big {
 std::vector<uint32_t> a;
 Big(U x=0){if(x){a.push_back(uint32_t(x));if(x>>32)a.push_back(uint32_t(x>>32));}}
 void trim(){while(!a.empty()&&a.back()==0)a.pop_back();}
 int cmp(const Big&b)const{if(a.size()!=b.a.size())return a.size()<b.a.size()?-1:1;for(size_t i=a.size();i-->0;)if(a[i]!=b.a[i])return a[i]<b.a[i]?-1:1;return 0;}
 bool operator<(const Big&b)const{return cmp(b)<0;}bool operator>(const Big&b)const{return cmp(b)>0;}bool operator>=(const Big&b)const{return cmp(b)>=0;}bool operator<=(const Big&b)const{return cmp(b)<=0;}bool operator==(const Big&b)const{return cmp(b)==0;}
 Big&operator+=(const Big&b){size_t n=std::max(a.size(),b.a.size());a.resize(n,0);U carry=0;for(size_t i=0;i<n;++i){U x=U(a[i])+(i<b.a.size()?b.a[i]:0)+carry;a[i]=uint32_t(x);carry=x>>32;}if(carry)a.push_back(uint32_t(carry));return *this;}
 Big&operator-=(const Big&b){if(*this<b)throw std::runtime_error("negative Big");U borrow=0;for(size_t i=0;i<a.size();++i){U rhs=(i<b.a.size()?b.a[i]:0)+borrow;U old=a[i];a[i]=uint32_t(old-rhs);borrow=old<rhs;}trim();return *this;}
 Big&operator*=(U x){if(!x){a.clear();return *this;}__uint128_t carry=0;for(auto&v:a){__uint128_t z=__uint128_t(v)*x+carry;v=uint32_t(z);carry=z>>32;}while(carry){a.push_back(uint32_t(carry));carry>>=32;}return *this;}
 Big operator/(U d)const{if(!d)throw std::runtime_error("Big division zero");Big b=*this;__uint128_t rem=0;for(size_t i=a.size();i-->0;){__uint128_t z=(rem<<32)+a[i];b.a[i]=uint32_t(z/d);rem=z%d;}if(rem)throw std::runtime_error("non-exact Big division");b.trim();return b;}
 unsigned bits()const{return a.empty()?0:unsigned((a.size()-1)*32+32-__builtin_clz(a.back()));}
 static Big random_bits(unsigned bits,std::mt19937_64&gen){Big b;b.a.resize((bits+31)/32);for(size_t i=0;i<b.a.size();i+=2){U x=gen();b.a[i]=uint32_t(x);if(i+1<b.a.size())b.a[i+1]=uint32_t(x>>32);}if(bits%32)b.a.back()&=(uint32_t(1)<<(bits%32))-1;b.trim();return b;}
 U div_small(U d){if(!d)throw std::runtime_error("Big division zero");__uint128_t rem=0;for(size_t i=a.size();i-->0;){__uint128_t z=(rem<<32)+a[i];a[i]=uint32_t(z/d);rem=z%d;}trim();return U(rem);}
 std::string decimal()const{if(a.empty())return "0";Big b=*this;std::string s;while(!b.a.empty())s.push_back(char('0'+b.div_small(10)));std::reverse(s.begin(),s.end());return s;}
 static Big decimal(const std::string&s){if(s.empty())throw std::runtime_error("empty Big string");Big b;for(char ch:s){if(ch<'0'||ch>'9')throw std::runtime_error("invalid Big string");b*=10;b+=Big(U(ch-'0'));}return b;}
};
Big operator*(Big a,U b){a*=b;return a;}
Big operator-(Big a,const Big&b){a-=b;return a;}

using Clock=std::chrono::steady_clock;
U checked_u128(__uint128_t x,const char*label){if(x>std::numeric_limits<U>::max())throw std::runtime_error(std::string(label)+" exceeds uint64");return U(x);}
std::string signed128(S128 value){if(!value)return "0";bool neg=value<0;__uint128_t mag=neg?__uint128_t(-(value+1))+1:__uint128_t(value);std::string s;while(mag){s.push_back(char('0'+mag%10));mag/=10;}if(neg)s.push_back('-');std::reverse(s.begin(),s.end());return s;}
U cellkey(int r,int c){return (U(uint32_t(r))<<32)|uint32_t(c);}
U mix64(U x){x+=0x9e3779b97f4a7c15ULL;x=(x^(x>>30))*0xbf58476d1ce4e5b9ULL;x=(x^(x>>27))*0x94d049bb133111ebULL;return x^(x>>31);}
struct Counters {
 U owner_cardinality_dp_cells=0,owner_combination_nodes=0,owner_sum_pruned_subtrees=0,owner_sum_pruned_masks=0,owner_feasible_masks_examined=0,owner_direct_trade_rank_calls=0;
 U work=0,outer=0,lazy=0,inner=0,invalid_pairs=0,rectangles=0,zero_delta=0;
 U returned=0,accepted=0,mh_rejected=0,timeouts=0,changed_outer=0,rollback_rectangles=0;
 U cell_updates=0,inserts=0,deletes=0,fenwick_updates=0,checks=0,checked_edges=0;
 U aux_calls=0,swap_attempts=0,swap_accepts=0,cycle_calls=0,cycle_valid=0,cycle_changed=0;
 U changed_tour=0,changed_tour_multistep=0,changed_tour_steps_total=0,first_edge_defect_branch=0,first_edge_uniform_branch=0;
 U block_calls=0,block_changed=0,block_support_changed=0,block_nontrivial=0,block_support_nontrivial=0,block_empty_wedge=0;
 U block_uniform_pairs=0,block_wedge_pairs=0,block_forced_anchors=0,block_row_orientation=0,block_col_orientation=0;
 U block_count_calls=0,block_count_terms=0,block_max_count_bits=0,block_count_nanoseconds=0,block_select_nanoseconds=0,block_commit_nanoseconds=0;
 U ses_calls=0,ses_valid=0,ses_changed=0,bes_calls=0,bes_valid=0,bes_changed=0,path_fallback_calls=0;
 U weight_index_updates=0,weight_group_creates=0,weight_group_deletes=0,weight_group_checks=0;
 U bridge_scan_edges=0,bridge_common_candidates=0,bridge_empty_common=0,bridge_compensation_invalid=0;
 U fast_unit_calls=0,fast_equal_trade_calls=0,fast_h0_calls=0,fast_h1_calls=0,fast_h2_calls=0,fast_general_calls=0,fast_singleton_calls=0;
 U fast_small_count_calls=0,fast_prefix_builds=0,fast_prefix_queries=0,hybrid_strong_calls=0,block_shape_holds=0;
 U block_local_calls=0,block_local_neighbor_draws=0,block_local_lookup_checks=0;
 U block_local_exclusive_holds=0,block_local_shared_holds=0,block_local_degree_holds=0;
 U block_scan_union_calls=0,block_scan_neighbor_visits=0;
 U block_local_two_bridge_branches=0,block_local_exclusive4_branches=0;
 U block_local_neighbor_union_branches=0,block_support_only_holds=0;
 U block_selected_exclusive_columns=0,block_selected_shared_columns=0,block_max_effective_shared=0,block_solved_max_effective_shared=0;
 U homerun_calls=0,homerun_changed=0,homerun_scan_columns=0,homerun_reservoir_draws=0;
 U homerun_reservoir_replacements=0,homerun_reservoir_removals=0;
 U owner_metropolis_calls=0,owner_proposals=0,owner_accepts=0,owner_rejects=0;
 U owner_one_support_heatbath=0,owner_completion_refreshes=0,owner_rejected_refresh_changed=0;
 U owner_matrix_changed=0,owner_support_changed=0,owner_state_holds_after_refresh=0;
 U block_general_calls=0,block_general_k2_calls=0,block_general_k3_calls=0,block_general_k4_calls=0,block_general_k6_calls=0;
 U block_effective_shared_holds=0,block_selected_width_total=0,block_selected_width_max=0;
 U triple_calls=0,triple_nodes_too_few=0,triple_neighbor_draws=0,triple_lookup_checks=0;
 U triple_exclusivity_holds=0,triple_partition_calls=0,triple_partition_candidates=0,triple_legal_assignments=0;
 U triple_nontrivial=0,triple_changed=0,triple_singleton_holds=0,triple_metropolis_draws=0;
 U triple_max_assignments=0,triple_selected_width_total=0,triple_selected_width_max=0;
 U triple_select_nanoseconds=0,triple_solve_nanoseconds=0,triple_commit_nanoseconds=0;
 U triple_row_orientation=0,triple_col_orientation=0;
 U rankone_calls=0,rankone_nodes_too_few=0,rankone_zero_degree_holds=0,rankone_neighbor_draws=0;
 U rankone_lookup_checks=0,rankone_dimension_holds=0,rankone_solver_calls=0,rankone_supports_examined=0;
 U rankone_highrank_supports=0,rankone_feasible_supports=0,rankone_tree_completions=0,rankone_cycle_completions=0;
 U rankone_current_highrank_holds=0,rankone_current_zero_label_holds=0,rankone_proposals=0,rankone_label_accepts=0,rankone_label_rejects=0;
 U rankone_zero_label_proposals=0,rankone_changed=0,rankone_support_changed=0;
 U rankone_max_completion_bits=0,rankone_max_total_bits=0,rankone_selected_width_total=0,rankone_selected_width_max=0;
 U rankone_select_nanoseconds=0,rankone_solve_nanoseconds=0,rankone_commit_nanoseconds=0;
 U rankone_row_orientation=0,rankone_col_orientation=0;
 U rankone_uniform_triples=0,rankone_wedge_triples=0,rankone_empty_wedge_fallbacks=0;
 U rankone_mixed_uniform_branches=0,rankone_mixed_wedge_branches=0,rankone_selector_neighbor_draws=0;
 U compressed_descriptor_builds=0,compressed_descriptor_terms=0,compressed_descriptor_max_terms=0,compressed_raw_subset_terms=0;
 U compressed_full_descriptor_max_terms=0,compressed_solver_descriptor_max_terms=0;
 U block_shift_gate_calls=0,block_shift_gate_nanoseconds=0,block_effective_shift_holds=0;
 U block_selected_full_shifts_total=0,block_selected_max_shifts_total=0,block_selected_max_shifts=0,block_solved_max_shifts=0;
 U block_cache_lookups=0,block_cache_hits=0,block_cache_misses=0,block_cache_evictions=0;
 U block_cache_entries_current=0,block_cache_entries_peak=0,block_cache_estimated_bytes_current=0,block_cache_estimated_bytes_peak=0;
 U block_cache_key_nanoseconds=0,block_cache_bind_nanoseconds=0,block_cache_build_nanoseconds=0;
 U max_path=0;long double max_abs_log_ratio=0;
};
struct Fenwick {
 std::vector<U> tree;
 Fenwick()=default; explicit Fenwick(int n):tree(n+1,0){}
 void add(int k,I delta){for(++k;k<int(tree.size());k+=k&-k){if(delta>=0)tree[k]+=U(delta);else tree[k]-=U(-delta);}}
 U total()const{U s=0;for(int k=int(tree.size())-1;k;k-=k&-k)s+=tree[k];return s;}
 int select(U order)const{int x=0,bit=1;while((bit<<1)<int(tree.size()))bit<<=1;for(;bit;bit>>=1){int y=x+bit;if(y<int(tree.size())&&tree[y]<=order){x=y;order-=tree[y];}}if(x>=int(tree.size())-1)throw std::runtime_error("Fenwick selection out of range");return x;}
};
struct Edge{int r,c,pr,pc;I w;};
struct Rectangle{int i,j,k,l;};
struct Undo{Rectangle r;I delta;};
struct WeightGroup {std::vector<U>cells;std::unordered_map<U,int>position;};
struct Graph {
 int nr=0,nc=0;std::vector<Edge> edges;std::vector<std::vector<int>> adj;
 std::unordered_map<U,int> lookup;std::unordered_set<U> original;
 std::vector<I> target_strength;std::vector<int> degree,target_degree;
 Fenwick bias_tree;U bias_mass=0;bool maintain_bias=false;I D=0;
 long double sumw2=0;S128 projection=0;U hash1=0,hash2=0;I overlap=0;
 int event_r=0,event_c=0;I event_threshold=0;Counters* counters=nullptr;
 bool maintain_exact_sumw2=false;__uint128_t exact_sumw2=0;U exact_sumw2_updates=0;
 bool maintain_weight_groups=false;std::unordered_map<I,WeightGroup>weight_groups;
 std::vector<I>unique_weights;std::unordered_map<I,int>unique_weight_position;
 int find(int r,int c)const{auto it=lookup.find(cellkey(r,c));return it==lookup.end()?-1:it->second;}
 I value(int r,int c)const{int id=find(r,c);return id<0?0:edges[id].w;}
 static U token1(int r,int c,I w){return mix64(cellkey(r,c)^mix64(U(w)));}
 static U token2(int r,int c,I w){return mix64(cellkey(r,c)+0xd6e8feb86659fd93ULL*U(w));}
 static int sign(int r,int c){return (mix64(cellkey(r,c))&1)?1:-1;}
 U vertex_bias(int v)const{return U(degree[v])*U(std::abs(degree[v]-target_degree[v]));}
 void weight_index_remove(I w,U key){
  if(counters)counters->weight_index_updates++;auto it=weight_groups.find(w);if(it==weight_groups.end())throw std::runtime_error("missing weight group");auto&group=it->second;auto pos=group.position.find(key);if(pos==group.position.end())throw std::runtime_error("missing grouped edge");int index=pos->second;U last=group.cells.back();group.cells[index]=last;group.position[last]=index;group.cells.pop_back();group.position.erase(key);
  if(group.cells.empty()){int index=unique_weight_position.at(w);I last_weight=unique_weights.back();unique_weights[index]=last_weight;unique_weight_position[last_weight]=index;unique_weights.pop_back();unique_weight_position.erase(w);weight_groups.erase(it);if(counters)counters->weight_group_deletes++;}
 }
 void weight_index_add(I w,U key){
  if(counters)counters->weight_index_updates++;auto it=weight_groups.find(w);if(it==weight_groups.end()){it=weight_groups.emplace(w,WeightGroup{}).first;unique_weight_position.emplace(w,int(unique_weights.size()));unique_weights.push_back(w);if(counters)counters->weight_group_creates++;}auto&group=it->second;if(group.position.count(key))throw std::runtime_error("duplicate grouped edge");group.position.emplace(key,int(group.cells.size()));group.cells.push_back(key);
 }
 void set_raw(int r,int c,I w){
  if(w<0)throw std::runtime_error("negative weight");int id=find(r,c);I old=id<0?0:edges[id].w;
  if(old==w)return;if(counters)counters->cell_updates++;
  if(maintain_exact_sumw2){const __uint128_t oldsq=__uint128_t(U(old))*U(old),newsq=__uint128_t(U(w))*U(w);if(exact_sumw2<oldsq)throw std::runtime_error("exact structure accumulator underflow");exact_sumw2-=oldsq;if(~__uint128_t(0)-exact_sumw2<newsq)throw std::runtime_error("exact structure accumulator overflow");exact_sumw2+=newsq;++exact_sumw2_updates;}
  if(maintain_weight_groups){U key=cellkey(r,c);if(old)weight_index_remove(old,key);if(w)weight_index_add(w,key);}
  if(old){hash1^=token1(r,c,old);hash2-=token2(r,c,old);sumw2-=(long double)old*old;projection-=sign(r,c)*old;}
  if(w){hash1^=token1(r,c,w);hash2+=token2(r,c,w);sumw2+=(long double)w*w;projection+=sign(r,c)*w;}
  if(old&&w){edges[id].w=w;return;}
  if(!old&&w){
   int next=int(edges.size());Edge x{r,c,int(adj[r].size()),int(adj[nr+c].size()),w};
   edges.push_back(x);adj[r].push_back(next);adj[nr+c].push_back(next);lookup.emplace(cellkey(r,c),next);
   degree[r]++;degree[nr+c]++;overlap+=original.count(cellkey(r,c));if(counters)counters->inserts++;return;
  }
  auto x=edges[id];auto &ar=adj[r];int last=ar.back();ar[x.pr]=last;edges[last].pr=x.pr;ar.pop_back();
  auto &ac=adj[nr+c];last=ac.back();ac[x.pc]=last;edges[last].pc=x.pc;ac.pop_back();lookup.erase(cellkey(r,c));
  int end=int(edges.size())-1;if(id!=end){auto moved=edges.back();edges[id]=moved;adj[moved.r][moved.pr]=id;adj[nr+moved.c][moved.pc]=id;lookup[cellkey(moved.r,moved.c)]=id;}
  edges.pop_back();degree[r]--;degree[nr+c]--;overlap-=original.count(cellkey(r,c));if(counters)counters->deletes++;
 }
 std::array<I,4> cells(Rectangle r)const{return {value(r.i,r.k),value(r.i,r.l),value(r.j,r.k),value(r.j,r.l)};}
 void apply(Rectangle r,I delta){
  if(!delta)return;auto a=cells(r);std::array<int,4> vertices{r.i,r.j,nr+r.k,nr+r.l};std::array<U,4> old{};
  for(int t=0;t<4;++t){int v=vertices[t];D-=std::abs(degree[v]-target_degree[v]);if(maintain_bias)old[t]=vertex_bias(v);}
  set_raw(r.i,r.k,a[0]+delta);set_raw(r.i,r.l,a[1]-delta);set_raw(r.j,r.k,a[2]-delta);set_raw(r.j,r.l,a[3]+delta);
  for(int t=0;t<4;++t){int v=vertices[t];D+=std::abs(degree[v]-target_degree[v]);if(maintain_bias){U now=vertex_bias(v);I change=I(now)-I(old[t]);bias_tree.add(v,change);if(change>=0)bias_mass+=U(change);else bias_mass-=U(-change);if(counters)counters->fenwick_updates++;}}
 }
 U phi(int r,int c,U kappa)const{U defect=U(std::abs(degree[r]-target_degree[r]))+U(std::abs(degree[nr+c]-target_degree[nr+c]));return checked_u128(1+__uint128_t(kappa)*defect,"edge phi");}
 U H(Rectangle r,U kappa)const{auto a=cells(r);__uint128_t h=0;if(a[0]>0&&a[3]>0)h+=__uint128_t(phi(r.i,r.k,kappa))+phi(r.j,r.l,kappa);if(a[1]>0&&a[2]>0)h+=__uint128_t(phi(r.i,r.l,kappa))+phi(r.j,r.k,kappa);return checked_u128(h,"rectangle H");}
 U Hproduct(Rectangle r,U kappa)const{auto a=cells(r);U h1=0,h2=0;if(a[0]>0&&a[3]>0)h1=checked_u128(__uint128_t(phi(r.i,r.k,kappa))*phi(r.j,r.l,kappa),"Hproduct diagonal");if(a[1]>0&&a[2]>0)h2=checked_u128(__uint128_t(phi(r.i,r.l,kappa))*phi(r.j,r.k,kappa),"Hproduct diagonal");return checked_u128(__uint128_t(h1)+h2,"rectangle Hproduct");}
 std::string flat()const{if(U(nr)*U(nc)>64)return "";std::ostringstream o;for(int r=0;r<nr;++r)for(int c=0;c<nc;++c){if(r||c)o<<':';o<<value(r,c);}return o.str();}
 static Graph load(const std::string &path,bool bias,bool groups=false){
  std::ifstream f(path);if(!f)throw std::runtime_error("cannot open graph input");Graph g;g.maintain_bias=bias;g.maintain_weight_groups=groups;
  if(!(f>>g.nr>>g.nc)||g.nr<1||g.nc<1)throw std::runtime_error("input needs positive nr nc header");
  g.adj.resize(g.nr+g.nc);g.degree.assign(g.nr+g.nc,0);g.target_degree.assign(g.nr+g.nc,0);g.target_strength.assign(g.nr+g.nc,0);g.bias_tree=Fenwick(g.nr+g.nc);
  int r,c;I w;I total_input_weight=0;U first=std::numeric_limits<U>::max();
  for(;;){f>>std::ws;if(f.eof())break;if(!(f>>r>>c>>w))throw std::runtime_error("malformed graph edge record");if(r<0||r>=g.nr||c<0||c>=g.nc||w<=0||g.find(r,c)>=0)throw std::runtime_error("invalid/duplicate input edge");
   if(g.target_strength[r]>std::numeric_limits<I>::max()-w||g.target_strength[g.nr+c]>std::numeric_limits<I>::max()-w)throw std::runtime_error("strength exceeds int64");
   if(total_input_weight>std::numeric_limits<I>::max()-w)throw std::runtime_error("total input weight exceeds supported int64 diagnostic range");total_input_weight+=w;
   g.set_raw(r,c,w);g.original.insert(cellkey(r,c));g.target_strength[r]+=w;g.target_strength[g.nr+c]+=w;
   if(cellkey(r,c)<first){first=cellkey(r,c);g.event_r=r;g.event_c=c;g.event_threshold=w;}}
  if(!f.eof())throw std::runtime_error("malformed graph edge record");
  g.target_degree=g.degree;g.D=0;g.overlap=I(g.edges.size());g.edges.reserve(g.edges.size()*2+64);g.lookup.reserve(g.edges.size()*2+64);
  return g;
 }
 bool check()const{
  if(counters){counters->checks++;counters->checked_edges+=edges.size();}
  std::vector<I> sums(nr+nc,0);std::vector<int> counts(nr+nc,0);U h1=0,h2=0;long double s2=0;I ov=0;S128 proj=0;
  if(lookup.size()!=edges.size())return false;
  for(int id=0;id<int(edges.size());++id){const auto&x=edges[id];if(x.w<=0||find(x.r,x.c)!=id||adj[x.r][x.pr]!=id||adj[nr+x.c][x.pc]!=id)return false;sums[x.r]+=x.w;sums[nr+x.c]+=x.w;counts[x.r]++;counts[nr+x.c]++;h1^=token1(x.r,x.c,x.w);h2+=token2(x.r,x.c,x.w);s2+=(long double)x.w*x.w;ov+=original.count(cellkey(x.r,x.c));proj+=sign(x.r,x.c)*x.w;}
  I d=0;U b=0;for(int v=0;v<nr+nc;++v){if(adj[v].size()!=U(counts[v]))return false;d+=std::abs(counts[v]-target_degree[v]);b+=U(counts[v])*U(std::abs(counts[v]-target_degree[v]));}
  bool numerical=std::abs(s2-sumw2)<=1e-12L*std::max(1.L,std::abs(s2));
  if(maintain_weight_groups){
   if(counters)counters->weight_group_checks++;if(unique_weights.size()!=weight_groups.size()||unique_weights.size()!=unique_weight_position.size())return false;U grouped_edges=0;
   for(size_t k=0;k<unique_weights.size();++k){I w=unique_weights[k];auto ui=unique_weight_position.find(w);auto gi=weight_groups.find(w);if(w<=0||ui==unique_weight_position.end()||ui->second!=int(k)||gi==weight_groups.end()||gi->second.cells.empty())return false;const auto&group=gi->second;if(group.cells.size()!=group.position.size())return false;
    for(size_t t=0;t<group.cells.size();++t){U key=group.cells[t];auto pi=group.position.find(key);int r=int(key>>32),c=int(uint32_t(key));if(pi==group.position.end()||pi->second!=int(t)||value(r,c)!=w)return false;grouped_edges++;}
   }if(grouped_edges!=edges.size())return false;
  }
  if(maintain_exact_sumw2){__uint128_t q=0;for(const Edge&x:edges){const __uint128_t z=__uint128_t(U(x.w))*U(x.w);if(~__uint128_t(0)-q<z)return false;q+=z;}if(q!=exact_sumw2)return false;}
  return sums==target_strength&&counts==degree&&d==D&&h1==hash1&&h2==hash2&&ov==overlap&&proj==projection&&numerical&&(!maintain_bias||(b==bias_mass&&bias_tree.total()==b));
 }
};
struct RNG {
 std::mt19937_64 gen;explicit RNG(U seed):gen(seed){}
 U below(U n){if(!n)throw std::runtime_error("empty uniform choice");return std::uniform_int_distribution<U>(0,n-1)(gen);}
 I integer(I lo,I hi){return std::uniform_int_distribution<I>(lo,hi)(gen);}
 Big below_big(const Big& n){if(n<=0)throw std::runtime_error("empty big choice");if(n==1)return 0;unsigned bits=(n-Big(1)).bits();for(;;){Big value=Big::random_bits(bits,gen);if(value<n)return value;}}
 bool pow2(unsigned long long bits){while(bits>=64){if(gen()!=0)return false;bits-=64;}return !bits||((gen()&((U(1)<<bits)-1))==0);}
 bool log_accept(long double logratio){if(logratio>=0)return true;U x;do{x=gen();}while(!x);return logl((long double)x)-64*logl(2.L)<logratio;}
};
 
Big binomial(S128 n,int k){
 if(k<0||n<k)return Big(0);Big b(1);
 for(int i=1;i<=k;++i){S128 factor=n-k+i;if(factor<0||__uint128_t(factor)>std::numeric_limits<U>::max())throw std::runtime_error("binomial factor out of supported range");b*=U(factor);b=b/U(i);}return b;
}
struct BoundedCounter {
 int h=0;std::vector<S128> shifts;std::vector<unsigned char> odd;Counters*stat=nullptr;
 explicit BoundedCounter(const std::vector<I>&bounds,Counters*s=nullptr):h(int(bounds.size())),stat(s){
  if(h>12)throw std::runtime_error("bounded counter supports <=12 variables");shifts.assign(size_t(1)<<h,0);odd.assign(shifts.size(),0);
  for(size_t mask=1;mask<shifts.size();++mask){size_t bit=mask&-mask;int j=__builtin_ctzll(U(bit));if(bounds[j]<0)throw std::runtime_error("negative composition bound");shifts[mask]=shifts[mask^bit]+S128(bounds[j])+1;odd[mask]=!odd[mask^bit];}
 }
 Big count(S128 total)const{
  if(stat)stat->block_count_calls++;if(!h)return Big(total==0);Big positive,negative;
  for(size_t mask=0;mask<shifts.size();++mask){if(stat)stat->block_count_terms++;S128 top=total-shifts[mask]+h-1;if(top<h-1)continue;Big term=binomial(top,h-1);if(odd[mask])negative+=term;else positive+=term;}
  if(positive<negative)throw std::runtime_error("negative inclusion-exclusion result");return positive-negative;
 }
};
struct CountedBlock {
 std::vector<I>a,b,c,bounds;std::vector<int>exclusive,shared;I row_sum=0;int choose=0;
 struct Support {U mask;Big count;};std::vector<Support>supports;Big total;Counters*stat=nullptr;
 CountedBlock(std::vector<I>aa,std::vector<I>bb,Counters*s=nullptr):a(std::move(aa)),b(std::move(bb)),stat(s){
  if(a.size()!=b.size()||a.size()>12)throw std::runtime_error("block arrays need same size <=12");I combined=0;int row_degree=0;
  for(size_t j=0;j<a.size();++j){if(a[j]<0||b[j]<0||a[j]>std::numeric_limits<I>::max()-b[j])throw std::runtime_error("invalid int64 block weight");I sum=a[j]+b[j];if(combined>std::numeric_limits<I>::max()-sum)throw std::runtime_error("block total exceeds int64");combined+=sum;c.push_back(sum);row_sum+=a[j];row_degree+=a[j]>0;if(a[j]>0&&b[j]>0){shared.push_back(int(j));bounds.push_back(sum-2);}else if(sum>0)exclusive.push_back(int(j));}
  choose=row_degree-int(shared.size());BoundedCounter bc(bounds,stat);
   
  std::vector<U>masks;for(U mask=0;mask<(U(1)<<exclusive.size());++mask)if(__builtin_popcountll(mask)==choose)masks.push_back(mask);
  std::sort(masks.begin(),masks.end(),[](U a,U b){if(a==b)return false;U diff=a^b,first=diff&-diff;return (a&first)!=0;});
  for(U mask:masks){S128 q=S128(row_sum)-shared.size();for(size_t z=0;z<exclusive.size();++z)if(mask>>z&1)q-=c[exclusive[z]];Big n=bc.count(q);if(n==0)continue;supports.push_back({mask,n});total+=n;}
  if(total==0)throw std::runtime_error("legal input has empty conditional fiber");if(stat)stat->block_max_count_bits=std::max(stat->block_max_count_bits,U(total.bits()));
 }
 std::pair<std::vector<I>,std::vector<I>>unrank(Big rank)const{
  if(rank>=total)throw std::runtime_error("block rank outside fiber");U chosen=0;bool found=false;
  for(const auto&s:supports){if(rank<s.count){chosen=s.mask;found=true;break;}rank-=s.count;}if(!found)throw std::runtime_error("block support draw failed");
  std::vector<I>x(a.size(),0);S128 q=S128(row_sum)-shared.size();for(size_t z=0;z<exclusive.size();++z)if(chosen>>z&1){x[exclusive[z]]=c[exclusive[z]];q-=x[exclusive[z]];}
  for(size_t t=0;t<shared.size();++t){std::vector<I>remaining;remaining.reserve(shared.size()-t);remaining.push_back(0);remaining.insert(remaining.end(),bounds.begin()+t+1,bounds.end());I lo=0,hi=bounds[t];
   while(lo<hi){I mid=lo+(hi-lo)/2;remaining[0]=mid;if(BoundedCounter(remaining,stat).count(q)>rank)hi=mid;else lo=mid+1;}
   if(lo){remaining[0]=lo-1;rank-=BoundedCounter(remaining,stat).count(q);}x[shared[t]]=lo+1;q-=lo;
  }
  if(!(rank==0)||q!=0)throw std::runtime_error("block unranking remainder nonzero");std::vector<I>y(x.size());for(size_t j=0;j<x.size();++j)y[j]=c[j]-x[j];return {x,y};
 }
};
#include "fast_block_pruned.hpp"
#include "block_class_cache.hpp"
#include "homerun.hpp"
#include "fixed_probe.hpp"
#include "triple_exclusive.hpp"
#include "triple_rankone.hpp"
struct Options {
 std::string input,method="candidate",out="run",pt_trace="cold",acceptance="log",anchor_mode="dual";
 U seed=0x135288b,budget=200000,trace_every=100,check_every=10000,max_outer=0;
 U kappa=0;std::string kappa_argument="0";int rho_den=4,q_den=16;long double cycle_mix=0;double wall_seconds=0;int butterflies=-1;
 std::string block_mode="anchor",orientation="both";int block_width=8;U cycle_probability=0,path_probability=0;
 std::string block_solver="fast",block_shape="union",budget_scope="sampling",owner_update="heatbath";U block_probability=700000;bool support_only=false;
 std::string neighbor_count="2";int max_effective_shared=-1,max_effective_shifts=-1,neighbor_k=2,mixed_neighbor_k=0;
 U triple_probability=0,rankone_probability=0;std::string rankone_selector="uniform";int block_cache_capacity=0;
 bool online_summary=false;U online_burn=0;std::string probe_queries;U probe_batch_width=1000,probe_trace_every=0;
};
struct Engine {
 Options opt;Counters stat;RNG rng;std::vector<Graph> graphs;std::vector<int> qdens;std::array<std::vector<U>,2>wedge_prefix;BlockClassCache block_cache;
 explicit Engine(Options o):opt(std::move(o)),rng(opt.seed),block_cache(size_t(opt.block_cache_capacity)){}
 int first_edge(Graph &g,U kappa){U m=g.edges.size();if(!m)return -1;if(!kappa){stat.first_edge_uniform_branch++;return int(rng.below(m));}U z=checked_u128(__uint128_t(kappa)*g.bias_mass+m,"edge selector Z");U x=rng.below(z);if(x<m){stat.first_edge_uniform_branch++;return int(x);}stat.first_edge_defect_branch++;int v=g.bias_tree.select((x-m)/kappa);return g.adj[v][rng.below(g.adj[v].size())];}
 bool rectangle(Graph &g,U kappa,Rectangle &r,bool dual=false){U m=g.edges.size();if(m<2){stat.invalid_pairs++;return false;}int a=first_edge(g,kappa),b;if(dual){b=first_edge(g,kappa);}else{b=int(rng.below(m-1));if(b>=a)b++;}auto x=g.edges[a],y=g.edges[b];if(x.r==y.r||x.c==y.c){stat.invalid_pairs++;return false;}r={std::min(x.r,y.r),std::max(x.r,y.r),std::min(x.c,y.c),std::max(x.c,y.c)};return true;}
 static std::pair<I,I> interval(const std::array<I,4>&a){return {-std::min(a[0],a[3]),std::min(a[1],a[2])};}
 static U class_size(I lo,I hi,I delta){return delta==lo||delta==hi?1:U(hi-lo-1);}
 I stratified(I lo,I hi){if(lo>=hi)throw std::runtime_error("selected rectangle is degenerate");U classes=hi-lo>1?3:2;U c=rng.below(classes);return c==0?lo:c==1?hi:rng.integer(lo+1,hi-1);}
 void rollback(Graph &g,const std::vector<Undo>&undo,U h1,U h2,I original_m,const std::string &tiny){
  for(auto it=undo.rbegin();it!=undo.rend();++it){g.apply(it->r,-it->delta);stat.work++;stat.rollback_rectangles++;}
  if(g.D!=0||g.hash1!=h1||g.hash2!=h2||I(g.edges.size())!=original_m||(!tiny.empty()&&g.flat()!=tiny))throw std::runtime_error("rollback did not restore graph");
 }
 void cycle(Graph &g){
  stat.work++;stat.cycle_calls++;int cur=int(rng.below(g.nr+g.nc));std::vector<int> nodes{cur},ids;
  for(int step=0;step<64;++step){if(g.adj[cur].empty())return;int id=g.adj[cur][rng.below(g.adj[cur].size())];auto e=g.edges[id];int next=cur<g.nr?g.nr+e.c:e.r;ids.push_back(id);auto it=std::find(nodes.begin(),nodes.end(),next);
   if(it!=nodes.end()){int start=int(it-nodes.begin()),len=int(ids.size())-start;if(len<4)return;if(len%2)throw std::runtime_error("odd bipartite cycle");I lo=std::numeric_limits<I>::min(),hi=std::numeric_limits<I>::max();for(int k=start;k<int(ids.size());++k){I w=g.edges[ids[k]].w;if((k-start)%2==0)lo=std::max(lo,1-w);else hi=std::min(hi,w-1);}I d=rng.integer(lo,hi);stat.cycle_valid++;if(!d)return;for(int k=start;k<int(ids.size());++k){auto x=g.edges[ids[k]];g.set_raw(x.r,x.c,x.w+((k-start)%2==0?d:-d));}stat.cycle_changed++;return;}
   nodes.push_back(next);cur=next;
  }
 }
 void candidate(Graph &g,bool outer_lazy=true){
  if(g.D)throw std::runtime_error("candidate outer state not in target fiber");
  U h1=g.hash1,h2=g.hash2;I m=I(g.edges.size());std::string tiny=g.flat();
  if(outer_lazy&&rng.below(2)==0){stat.work++;stat.lazy++;return;}
  if(outer_lazy&&opt.cycle_mix>0&&rng.below(2)==0){cycle(g);if(g.hash1!=h1||g.hash2!=h2)stat.changed_outer++;return;}
  std::vector<Undo> undo;long double logratio=0;Big exact_num=1,exact_den=1;U steps=0;
  for(;;){steps++;stat.work++;stat.inner++;Rectangle r{};
   if(rectangle(g,opt.kappa,r,opt.anchor_mode=="dual")){
    stat.rectangles++;auto old=g.cells(r);auto [lo,hi]=interval(old);U old_h=opt.anchor_mode=="dual"?g.Hproduct(r,opt.kappa):g.H(r,opt.kappa),old_n=class_size(lo,hi,0);I delta=stratified(lo,hi);U new_n=class_size(lo,hi,delta);
    if(delta){undo.push_back({r,delta});g.apply(r,delta);}else stat.zero_delta++;
    U new_h=opt.anchor_mode=="dual"?g.Hproduct(r,opt.kappa):g.H(r,opt.kappa);if(!old_h||!new_h||!old_n||!new_n)throw std::runtime_error("invalid path reversal factor");
    if(new_h!=old_h)logratio+=logl((long double)new_h)-logl((long double)old_h);
    if(new_n!=old_n)logratio+=logl((long double)new_n)-logl((long double)old_n);
    if(opt.acceptance=="exact"){exact_num*=new_h;exact_num*=new_n;exact_den*=old_h;exact_den*=old_n;}
   }
   if(g.D==0){stat.returned++;stat.max_path=std::max(stat.max_path,steps);stat.max_abs_log_ratio=std::max(stat.max_abs_log_ratio,std::abs(logratio));bool accept=opt.acceptance=="exact"?(exact_num>=exact_den||rng.below_big(exact_den)<exact_num):rng.log_accept(logratio);
    if(accept){stat.accepted++;if(g.hash1!=h1||g.hash2!=h2){stat.changed_outer++;stat.changed_tour++;stat.changed_tour_steps_total+=steps;stat.changed_tour_multistep+=steps>1;}}else{stat.mh_rejected++;rollback(g,undo,h1,h2,m,tiny);}return;
   }
    
   if(rng.below(opt.rho_den)==0){stat.timeouts++;stat.max_path=std::max(stat.max_path,steps);rollback(g,undo,h1,h2,m,tiny);return;}
  }
 }
 void initialize_wedges(const Graph&g){
   
  for(int orientation=0;orientation<2;++orientation){auto&p=wedge_prefix[orientation];int n=orientation?g.nr:g.nc;p.resize(n);U total=0;
   for(int j=0;j<n;++j){U d=g.target_degree[orientation?j:g.nr+j];total=checked_u128(__uint128_t(total)+__uint128_t(d)*(d-unsigned(d>0))/2,"wedge count");p[j]=total;}
  }
 }
 void block(Graph&g){
  if(g.D)throw std::runtime_error("block outer state not legal");stat.work++;stat.block_calls++;auto select_start=Clock::now();
  int orientation=opt.orientation=="row"?0:opt.orientation=="col"?1:int(rng.below(2));int n=orientation?g.nc:g.nr;stat.block_row_orientation+=orientation==0;stat.block_col_orientation+=orientation==1;
  if(n<2)return;std::string mode=opt.block_mode;if(mode=="mixed")mode=rng.below(2)?"anchor":"uniform";int a,b,anchor=-1;
  auto opposite=[&](int id){return orientation?g.edges[id].r:g.edges[id].c;};auto side_vertex=[&](int v){return orientation?g.nr+v:v;};
  if(mode=="uniform"){stat.block_uniform_pairs++;a=int(rng.below(n));b=int(rng.below(n-1));if(b>=a)b++;}
  else{stat.block_wedge_pairs++;const auto&p=wedge_prefix[orientation];U total=p.empty()?0:p.back();if(!total){stat.block_empty_wedge++;return;}anchor=int(std::upper_bound(p.begin(),p.end(),rng.below(total))-p.begin());int v=orientation?anchor:g.nr+anchor;const auto&adj=g.adj[v];if(adj.size()<2)throw std::runtime_error("stale wedge selection");U ia=rng.below(adj.size()),ib=rng.below(adj.size()-1);if(ib>=ia)ib++;a=orientation?g.edges[adj[ia]].c:g.edges[adj[ia]].r;b=orientation?g.edges[adj[ib]].c:g.edges[adj[ib]].r;}
  if(a>b)std::swap(a,b);
  std::vector<int>selected;
  std::string shape=opt.block_shape;if(shape=="local_mixed")shape=rng.below(2)?"two_bridge_local":"exclusive4_local";
  bool local=shape=="two_bridge_local"||shape=="exclusive4_local"||shape=="neighbor_union"||shape=="neighbor_union_general";
  if(local){
   stat.block_local_calls++;const auto&aa=g.adj[side_vertex(a)];const auto&bb=g.adj[side_vertex(b)];
   auto neighbor=[&](const std::vector<int>&adj,U index){stat.block_local_neighbor_draws++;return opposite(adj[index]);};
   auto present=[&](int row,int column){stat.block_local_lookup_checks++;return (orientation?g.value(column,row):g.value(row,column))>0;};
   auto hold=[&](U&reason){reason++;stat.block_shape_holds++;stat.block_select_nanoseconds+=std::chrono::duration_cast<std::chrono::nanoseconds>(Clock::now()-select_start).count();};
   if(shape=="neighbor_union_general"){
    stat.block_general_calls++;int k=opt.neighbor_k;if(opt.mixed_neighbor_k&&rng.below(2))k=opt.mixed_neighbor_k;
    stat.block_general_k2_calls+=k==2;stat.block_general_k3_calls+=k==3;stat.block_general_k4_calls+=k==4;stat.block_general_k6_calls+=k==6;
    auto subset=[&](const std::vector<int>&adj){

     U take=std::min<U>(k,adj.size());std::vector<U>indices;indices.reserve(size_t(take));
     for(U j=adj.size()-take;j<adj.size();++j){U choice=rng.below(j+1);if(std::find(indices.begin(),indices.end(),choice)!=indices.end())choice=j;indices.push_back(choice);}
     for(U index:indices)selected.push_back(neighbor(adj,index));
    };subset(aa);subset(bb);std::sort(selected.begin(),selected.end());selected.erase(std::unique(selected.begin(),selected.end()),selected.end());
   }else if(shape=="neighbor_union"){
    stat.block_local_neighbor_union_branches++;
    if(aa.size()<2||bb.size()<2){hold(stat.block_local_degree_holds);return;}
    U ia=rng.below(aa.size()),ja=rng.below(aa.size()-1);if(ja>=ia)ja++;
    U ib=rng.below(bb.size()),jb=rng.below(bb.size()-1);if(jb>=ib)jb++;
    selected={neighbor(aa,ia),neighbor(aa,ja),neighbor(bb,ib),neighbor(bb,jb)};
    std::sort(selected.begin(),selected.end());selected.erase(std::unique(selected.begin(),selected.end()),selected.end());
   }else if(shape=="two_bridge_local"){
    stat.block_local_two_bridge_branches++;
    const auto&small=aa.size()<=bb.size()?aa:bb;
    if(aa.empty()||bb.empty()||small.size()<U(mode=="uniform"?2:1)){hold(stat.block_local_degree_holds);return;}
    int u=neighbor(aa,rng.below(aa.size())),v=neighbor(bb,rng.below(bb.size()));
    if(present(b,u)||present(a,v)){hold(stat.block_local_exclusive_holds);return;}
    selected.push_back(u);selected.push_back(v);
    if(mode=="uniform"){
     U ij=rng.below(small.size()),ik=rng.below(small.size()-1);if(ik>=ij)ik++;
     int j=neighbor(small,ij),k=neighbor(small,ik);
     if(!present(a,j)||!present(b,j)||!present(a,k)||!present(b,k)){hold(stat.block_local_shared_holds);return;}
     selected.push_back(j);selected.push_back(k);
    }else{

     int k=neighbor(small,rng.below(small.size()));
     if(k==anchor||!present(a,k)||!present(b,k)){hold(stat.block_local_shared_holds);return;}
     stat.block_forced_anchors++;selected.push_back(anchor);selected.push_back(k);
    }
   }else{
    stat.block_local_exclusive4_branches++;
    if(aa.size()<2||bb.size()<2){hold(stat.block_local_degree_holds);return;}
    U ia=rng.below(aa.size()),ja=rng.below(aa.size()-1);if(ja>=ia)ja++;
    U ib=rng.below(bb.size()),jb=rng.below(bb.size()-1);if(jb>=ib)jb++;
    int u=neighbor(aa,ia),v=neighbor(aa,ja),j=neighbor(bb,ib),k=neighbor(bb,jb);
    if(present(b,u)||present(b,v)||present(a,j)||present(a,k)){hold(stat.block_local_exclusive_holds);return;}
    selected={u,v,j,k};
   }
  }else{
  std::vector<int>all;stat.block_scan_union_calls++;stat.block_scan_neighbor_visits+=g.adj[side_vertex(a)].size()+g.adj[side_vertex(b)].size();
  for(int id:g.adj[side_vertex(a)])all.push_back(opposite(id));for(int id:g.adj[side_vertex(b)])all.push_back(opposite(id));std::sort(all.begin(),all.end());all.erase(std::unique(all.begin(),all.end()),all.end());
  auto pick=[&](std::vector<int>values,int count){for(int t=0;t<count;++t){int k=t+int(rng.below(values.size()-t));std::swap(values[t],values[k]);selected.push_back(values[t]);}};
  if(opt.block_shape=="union"){
   int width=std::min<int>(opt.block_width,all.size());if(mode=="anchor"){stat.block_forced_anchors++;auto it=std::lower_bound(all.begin(),all.end(),anchor);if(it==all.end()||*it!=anchor)throw std::runtime_error("anchor outside dynamic union");all.erase(it);selected.push_back(anchor);}pick(all,width-int(selected.size()));
  }else{
   std::vector<int>A,B,H;for(int j:all){bool av=(orientation?g.value(j,a):g.value(a,j))>0,bv=(orientation?g.value(j,b):g.value(b,j))>0;if(av&&bv)H.push_back(j);else if(av)A.push_back(j);else if(bv)B.push_back(j);}
   bool available=opt.block_shape=="two_bridge"?(!A.empty()&&!B.empty()&&H.size()>=2):(A.size()>=2&&B.size()>=2);
   if(!available){stat.block_shape_holds++;stat.block_select_nanoseconds+=std::chrono::duration_cast<std::chrono::nanoseconds>(Clock::now()-select_start).count();return;}
   if(opt.block_shape=="two_bridge"){pick(A,1);pick(B,1);if(mode=="anchor"){stat.block_forced_anchors++;auto it=std::lower_bound(H.begin(),H.end(),anchor);if(it==H.end()||*it!=anchor)throw std::runtime_error("two-bridge anchor not shared");H.erase(it);selected.push_back(anchor);pick(H,1);}else pick(H,2);}
   else{pick(A,2);pick(B,2);}
  }
  }
  std::sort(selected.begin(),selected.end());
  stat.block_selected_width_total+=selected.size();stat.block_selected_width_max=std::max(stat.block_selected_width_max,U(selected.size()));
  std::vector<I>aa,bb;for(int j:selected){aa.push_back(orientation?g.value(j,a):g.value(a,j));bb.push_back(orientation?g.value(j,b):g.value(b,j));}
  U exclusive=0,shared=0,effective_shared=0;for(size_t j=0;j<aa.size();++j){exclusive+=(aa[j]>0)!=(bb[j]>0);shared+=(aa[j]>0)&&(bb[j]>0);effective_shared+=(aa[j]>0)&&(bb[j]>0)&&(aa[j]+bb[j]>2);}
  stat.block_selected_exclusive_columns+=exclusive;stat.block_selected_shared_columns+=shared;stat.block_max_effective_shared=std::max(stat.block_max_effective_shared,effective_shared);
  if(opt.support_only&&exclusive<2){stat.block_support_only_holds++;stat.block_select_nanoseconds+=std::chrono::duration_cast<std::chrono::nanoseconds>(Clock::now()-select_start).count();return;}
  if(opt.max_effective_shared>=0&&effective_shared>U(opt.max_effective_shared)){stat.block_effective_shared_holds++;stat.block_select_nanoseconds+=std::chrono::duration_cast<std::chrono::nanoseconds>(Clock::now()-select_start).count();return;}
  if(opt.max_effective_shifts>=0){auto gate_start=Clock::now();std::vector<I>shared_bounds;for(size_t j=0;j<aa.size();++j)if(aa[j]>0&&bb[j]>0&&aa[j]+bb[j]>2)shared_bounds.push_back(aa[j]+bb[j]-2);auto work=effective_shift_work(shared_bounds);stat.block_shift_gate_calls++;stat.block_shift_gate_nanoseconds+=std::chrono::duration_cast<std::chrono::nanoseconds>(Clock::now()-gate_start).count();stat.block_selected_full_shifts_total+=work.first;stat.block_selected_max_shifts_total+=work.second;stat.block_selected_max_shifts=std::max(stat.block_selected_max_shifts,work.second);
   if(work.second>U(opt.max_effective_shifts)){stat.block_effective_shift_holds++;stat.block_select_nanoseconds+=std::chrono::duration_cast<std::chrono::nanoseconds>(Clock::now()-select_start).count();return;}stat.block_solved_max_shifts=std::max(stat.block_solved_max_shifts,work.second);
  }
  stat.block_solved_max_effective_shared=std::max(stat.block_solved_max_effective_shared,effective_shared);
  stat.block_select_nanoseconds+=std::chrono::duration_cast<std::chrono::nanoseconds>(Clock::now()-select_start).count();auto count_start=Clock::now();std::pair<std::vector<I>,std::vector<I>>draw;
  if(opt.block_solver=="reference"){CountedBlock cb(aa,bb,&stat);stat.block_nontrivial+=cb.total>Big(1);stat.block_support_nontrivial+=cb.supports.size()>1;draw=cb.unrank(rng.below_big(cb.total));}
  else if(!opt.block_cache_capacity){FastCountedBlock cb(aa,bb,&stat);stat.block_nontrivial+=cb.nontrivial();stat.block_support_nontrivial+=cb.support_count()>1;if(opt.owner_update=="metropolis_refresh"){OwnerRandomAdapter random{rng};draw=cb.draw_metropolis_refresh(random);}else draw=cb.draw(rng);}
  else draw=block_cache.use(aa,bb,stat,[&](FastCountedBlock&cb){stat.block_nontrivial+=cb.nontrivial();stat.block_support_nontrivial+=cb.support_count()>1;if(opt.owner_update=="metropolis_refresh"){OwnerRandomAdapter random{rng};return cb.draw_metropolis_refresh(random);}return cb.draw(rng);});
  auto&x=draw.first;auto&y=draw.second;stat.block_count_nanoseconds+=std::chrono::duration_cast<std::chrono::nanoseconds>(Clock::now()-count_start).count();bool changed=false,support_changed=false;
  auto commit_start=Clock::now();for(size_t k=0;k<selected.size();++k){int j=selected[k];changed|=x[k]!=aa[k]||y[k]!=bb[k];support_changed|=(x[k]>0)!=(aa[k]>0)||(y[k]>0)!=(bb[k]>0);if(orientation){g.set_raw(j,a,x[k]);g.set_raw(j,b,y[k]);}else{g.set_raw(a,j,x[k]);g.set_raw(b,j,y[k]);}}
  stat.block_commit_nanoseconds+=std::chrono::duration_cast<std::chrono::nanoseconds>(Clock::now()-commit_start).count();stat.block_changed+=changed;stat.block_support_changed+=support_changed;stat.changed_outer+=changed;

 }
 void homerun(Graph&g){
  stat.work++;stat.homerun_calls++;
  int orientation=opt.orientation=="row"?0:opt.orientation=="col"?1:int(rng.below(2));
  int n=orientation?g.nc:g.nr,width=orientation?g.nr:g.nc;if(n<2)return;
  int a=int(rng.below(n)),b=int(rng.below(n-1));if(b>=a)b++;if(a>b)std::swap(a,b);
  int va=orientation?g.nr+a:a,vb=orientation?g.nr+b:b;
  std::vector<I>aa(width),bb(width);for(int j=0;j<width;++j){aa[j]=orientation?g.value(j,a):g.value(a,j);bb[j]=orientation?g.value(j,b):g.value(b,j);}
  auto draw=home_run_rows(aa,bb,rng,g.target_degree[va],g.target_degree[vb],&stat);bool changed=false;
  for(int j=0;j<width;++j){changed|=aa[j]!=draw.first[j]||bb[j]!=draw.second[j];if(orientation){g.set_raw(j,a,draw.first[j]);g.set_raw(j,b,draw.second[j]);}else{g.set_raw(a,j,draw.first[j]);g.set_raw(b,j,draw.second[j]);}}
  stat.homerun_changed+=changed;stat.changed_outer+=changed;
 }
 void homerun_step(Graph&g){if(rng.below(2)==0){stat.work++;stat.lazy++;return;}homerun(g);}
 void triple(Graph&g){
  if(g.D)throw std::runtime_error("triple outer state not legal");stat.work++;stat.triple_calls++;auto select_start=Clock::now();
  auto finish_selection=[&](){stat.triple_select_nanoseconds+=std::chrono::duration_cast<std::chrono::nanoseconds>(Clock::now()-select_start).count();};
  int orientation=opt.orientation=="row"?0:opt.orientation=="col"?1:int(rng.below(2));int n=orientation?g.nc:g.nr;stat.triple_row_orientation+=orientation==0;stat.triple_col_orientation+=orientation==1;
  if(n<3){stat.triple_nodes_too_few++;finish_selection();return;}
  std::array<int,3>nodes;nodes[0]=int(rng.below(n));nodes[1]=int(rng.below(n-1));if(nodes[1]>=nodes[0])nodes[1]++;
  int lo=std::min(nodes[0],nodes[1]),hi=std::max(nodes[0],nodes[1]);nodes[2]=int(rng.below(n-2));if(nodes[2]>=lo)nodes[2]++;if(nodes[2]>=hi)nodes[2]++;std::sort(nodes.begin(),nodes.end());
  auto opposite=[&](int id){return orientation?g.edges[id].r:g.edges[id].c;};std::vector<int>selected;
  for(int node:nodes){const auto&adj=g.adj[orientation?g.nr+node:node];if(adj.empty())continue;U first=rng.below(adj.size());selected.push_back(opposite(adj[first]));stat.triple_neighbor_draws++;
   if(adj.size()>=2){U second=rng.below(adj.size()-1);if(second>=first)second++;selected.push_back(opposite(adj[second]));stat.triple_neighbor_draws++;}
  }
  std::sort(selected.begin(),selected.end());selected.erase(std::unique(selected.begin(),selected.end()),selected.end());stat.triple_selected_width_total+=selected.size();stat.triple_selected_width_max=std::max(stat.triple_selected_width_max,U(selected.size()));
  std::array<std::vector<I>,3>rows;for(int j:selected){int arity=0;for(int r=0;r<3;++r){I value=orientation?g.value(j,nodes[r]):g.value(nodes[r],j);rows[r].push_back(value);arity+=value>0;stat.triple_lookup_checks++;}if(arity!=1){stat.triple_exclusivity_holds++;finish_selection();return;}}
  finish_selection();auto solve_start=Clock::now();ExclusiveTriple solver(rows[0],rows[1],rows[2],&stat);auto draw=solver.draw(rng,opt.owner_update=="metropolis_refresh");stat.triple_solve_nanoseconds+=std::chrono::duration_cast<std::chrono::nanoseconds>(Clock::now()-solve_start).count();
  auto commit_start=Clock::now();bool changed=false;for(int r=0;r<3;++r)for(size_t j=0;j<selected.size();++j){changed|=draw[r][j]!=rows[r][j];if(orientation)g.set_raw(selected[j],nodes[r],draw[r][j]);else g.set_raw(nodes[r],selected[j],draw[r][j]);}
  stat.triple_commit_nanoseconds+=std::chrono::duration_cast<std::chrono::nanoseconds>(Clock::now()-commit_start).count();stat.triple_changed+=changed;stat.changed_outer+=changed;
 }
 std::array<int,3> rankone_nodes(const Graph&g,int orientation){
  int n=orientation?g.nc:g.nr;if(n<3)throw std::runtime_error("rankone node selector requires n>=3");
  bool wedge=opt.rankone_selector=="wedge_triple";
  if(opt.rankone_selector=="mixed"){wedge=rng.below(2)!=0;stat.rankone_mixed_wedge_branches+=wedge;stat.rankone_mixed_uniform_branches+=!wedge;}
  const auto&prefix=wedge_prefix[orientation];U total=prefix.empty()?0:prefix.back();
  if(wedge&&!total){stat.rankone_empty_wedge_fallbacks++;wedge=false;}
  std::array<int,3>nodes;
  if(!wedge){stat.rankone_uniform_triples++;nodes[0]=int(rng.below(n));nodes[1]=int(rng.below(n-1));if(nodes[1]>=nodes[0])nodes[1]++;}
  else{stat.rankone_wedge_triples++;int anchor=int(std::upper_bound(prefix.begin(),prefix.end(),rng.below(total))-prefix.begin());const auto&adj=g.adj[orientation?anchor:g.nr+anchor];if(adj.size()<2)throw std::runtime_error("rankone stale wedge prefix");U first=rng.below(adj.size()),second=rng.below(adj.size()-1);if(second>=first)second++;auto a=g.edges[adj[first]],b=g.edges[adj[second]];nodes[0]=orientation?a.c:a.r;nodes[1]=orientation?b.c:b.r;stat.rankone_selector_neighbor_draws+=2;}
   
  int lo=std::min(nodes[0],nodes[1]),hi=std::max(nodes[0],nodes[1]);nodes[2]=int(rng.below(n-2));if(nodes[2]>=lo)nodes[2]++;if(nodes[2]>=hi)nodes[2]++;std::sort(nodes.begin(),nodes.end());return nodes;
 }
 void rankone(Graph&g){
  if(g.D)throw std::runtime_error("rankone outer state not legal");stat.work++;stat.rankone_calls++;auto select_start=Clock::now();
  auto finish_selection=[&](){stat.rankone_select_nanoseconds+=std::chrono::duration_cast<std::chrono::nanoseconds>(Clock::now()-select_start).count();};
  int orientation=opt.orientation=="row"?0:opt.orientation=="col"?1:int(rng.below(2));int n=orientation?g.nc:g.nr;stat.rankone_row_orientation+=orientation==0;stat.rankone_col_orientation+=orientation==1;
  if(n<3){stat.rankone_nodes_too_few++;finish_selection();return;}
  auto nodes=rankone_nodes(g,orientation);
  for(int node:nodes)if(g.adj[orientation?g.nr+node:node].empty()){stat.rankone_zero_degree_holds++;finish_selection();return;}
  std::vector<int>selected;for(int node:nodes){const auto&adj=g.adj[orientation?g.nr+node:node];auto edge=g.edges[adj[rng.below(adj.size())]];selected.push_back(orientation?edge.r:edge.c);stat.rankone_neighbor_draws++;}
  std::sort(selected.begin(),selected.end());selected.erase(std::unique(selected.begin(),selected.end()),selected.end());stat.rankone_selected_width_total+=selected.size();stat.rankone_selected_width_max=std::max(stat.rankone_selected_width_max,U(selected.size()));
  RankOneTriple::Rows rows;int positive_edges=0;for(int j:selected)for(int r=0;r<3;++r){I value=orientation?g.value(j,nodes[r]):g.value(nodes[r],j);rows[r].push_back(value);positive_edges+=value>0;stat.rankone_lookup_checks++;}
   
  if(positive_edges>3+int(selected.size())){stat.rankone_dimension_holds++;finish_selection();return;}
  finish_selection();auto solve_start=Clock::now();RankOneTriple solver(rows,&stat);OwnerRandomAdapter random{rng};auto draw=solver.draw_corrected(random);stat.rankone_solve_nanoseconds+=std::chrono::duration_cast<std::chrono::nanoseconds>(Clock::now()-solve_start).count();
  auto commit_start=Clock::now();bool changed=false,support_changed=false;for(int r=0;r<3;++r)for(size_t j=0;j<selected.size();++j){changed|=draw[r][j]!=rows[r][j];support_changed|=(draw[r][j]>0)!=(rows[r][j]>0);if(orientation)g.set_raw(selected[j],nodes[r],draw[r][j]);else g.set_raw(nodes[r],selected[j],draw[r][j]);}
  stat.rankone_commit_nanoseconds+=std::chrono::duration_cast<std::chrono::nanoseconds>(Clock::now()-commit_start).count();stat.rankone_changed+=changed;stat.rankone_support_changed+=support_changed;stat.changed_outer+=changed;
 }
 void block_step(Graph&g){
  if(rng.below(2)==0){stat.work++;stat.lazy++;return;}U branch=rng.below(1000000);
  if(branch<opt.cycle_probability){U h1=g.hash1,h2=g.hash2;cycle(g);stat.changed_outer+=h1!=g.hash1||h2!=g.hash2;}
  else if(branch<opt.cycle_probability+opt.triple_probability)triple(g);
  else if(branch<opt.cycle_probability+opt.triple_probability+opt.rankone_probability)rankone(g);
  else if(branch<opt.cycle_probability+opt.triple_probability+opt.rankone_probability+opt.path_probability){stat.path_fallback_calls++;candidate(g,false);}
  else block(g);
 }
 void swap_reference(Graph&g,bool bridge){
  stat.work++;if(bridge)stat.bes_calls++;else stat.ses_calls++;U m=g.edges.size();if(m<2)return;U ia=rng.below(m),ib=rng.below(m-1);if(ib>=ia)ib++;auto x=g.edges[ia],y=g.edges[ib];bool rows=true;int k=-1;
  if(bridge){rows=bool(rng.below(2));k=int(rng.below(rows?g.nr:g.nc));}
  if(x.r==y.r||x.c==y.c||g.find(x.r,y.c)>=0||g.find(y.r,x.c)>=0)return;
  if(!bridge){if(x.w!=y.w)return;stat.ses_valid++;g.set_raw(x.r,x.c,0);g.set_raw(y.r,y.c,0);g.set_raw(x.r,y.c,x.w);g.set_raw(y.r,x.c,y.w);stat.ses_changed++;stat.changed_outer++;return;}
  if(x.w==y.w)return;I p,q,delta=x.w-y.w;
  if(rows){if(k==x.r||k==y.r)return;p=g.value(k,x.c);q=g.value(k,y.c);}else{if(k==x.c||k==y.c)return;p=g.value(x.r,k);q=g.value(y.r,k);}
  if(p<=0||q<=0||S128(p)+delta<=0||S128(q)-delta<=0)return;if(S128(p)+delta>std::numeric_limits<I>::max()||S128(q)-delta>std::numeric_limits<I>::max())throw std::runtime_error("reference compensation exceeds int64");stat.bes_valid++;
  if(rows){g.set_raw(k,x.c,p+delta);g.set_raw(k,y.c,q-delta);}else{g.set_raw(x.r,k,p+delta);g.set_raw(y.r,k,q-delta);}
  g.set_raw(x.r,x.c,0);g.set_raw(y.r,y.c,0);if(rows){g.set_raw(x.r,y.c,x.w);g.set_raw(y.r,x.c,y.w);}else{g.set_raw(y.r,x.c,x.w);g.set_raw(x.r,y.c,y.w);}stat.bes_changed++;stat.changed_outer++;
 }
 void standard_step(Graph&g){if(rng.below(2)==0){stat.work++;stat.lazy++;return;}int move=int(rng.below(3));if(!move){U h1=g.hash1,h2=g.hash2;cycle(g);stat.changed_outer+=h1!=g.hash1||h2!=g.hash2;}else swap_reference(g,move==2);}
 void optimized_swap(Graph&g,bool bridge){
  stat.work++;if(bridge)stat.bes_calls++;else stat.ses_calls++;U m=g.edges.size();if(m<2)return;Edge x,y;
  if(!bridge){

   if(!g.maintain_weight_groups)throw std::runtime_error("optimized SES needs weight groups");if(g.unique_weights.empty())return;I w=g.unique_weights[rng.below(g.unique_weights.size())];const auto&group=g.weight_groups.at(w);U n=group.cells.size();if(n<2)return;U ia=rng.below(n),ib=rng.below(n);if(ia==ib)return;U ka=group.cells[ia],kb=group.cells[ib];int a=g.find(int(ka>>32),int(uint32_t(ka))),b=g.find(int(kb>>32),int(uint32_t(kb)));if(a<0||b<0)throw std::runtime_error("stale grouped SES edge");x=g.edges[a];y=g.edges[b];
  }else{U ia=rng.below(m),ib=rng.below(m-1);if(ib>=ia)ib++;x=g.edges[ia];y=g.edges[ib];}
  bool rows=true;if(bridge)rows=bool(rng.below(2));
  if(x.r==y.r||x.c==y.c||g.find(x.r,y.c)>=0||g.find(y.r,x.c)>=0)return;
  if(!bridge){if(x.w!=y.w)throw std::runtime_error("weight group changed midselection");stat.ses_valid++;g.set_raw(x.r,x.c,0);g.set_raw(y.r,y.c,0);g.set_raw(x.r,y.c,x.w);g.set_raw(y.r,x.c,y.w);stat.ses_changed++;stat.changed_outer++;return;}
  if(x.w==y.w)return;

  std::vector<int>common;
  if(rows){int c1=x.c,c2=y.c;if(g.adj[g.nr+c1].size()>g.adj[g.nr+c2].size())std::swap(c1,c2);const auto&adj=g.adj[g.nr+c1];stat.bridge_scan_edges+=adj.size();for(int id:adj){int k=g.edges[id].r;if(k!=x.r&&k!=y.r&&g.find(k,c2)>=0)common.push_back(k);}}
  else{int r1=x.r,r2=y.r;if(g.adj[r1].size()>g.adj[r2].size())std::swap(r1,r2);const auto&adj=g.adj[r1];stat.bridge_scan_edges+=adj.size();for(int id:adj){int k=g.edges[id].c;if(k!=x.c&&k!=y.c&&g.find(r2,k)>=0)common.push_back(k);}}
  stat.bridge_common_candidates+=common.size();if(common.empty()){stat.bridge_empty_common++;return;}int k=common[rng.below(common.size())];I p=rows?g.value(k,x.c):g.value(x.r,k),q=rows?g.value(k,y.c):g.value(y.r,k),delta=x.w-y.w;
  if(p<=0||q<=0)throw std::runtime_error("nonpositive common-neighbor bridge");if(S128(p)+delta<=0||S128(q)-delta<=0){stat.bridge_compensation_invalid++;return;}if(S128(p)+delta>std::numeric_limits<I>::max()||S128(q)-delta>std::numeric_limits<I>::max())throw std::runtime_error("optimized compensation exceeds int64");stat.bes_valid++;
  if(rows){g.set_raw(k,x.c,p+delta);g.set_raw(k,y.c,q-delta);}else{g.set_raw(x.r,k,p+delta);g.set_raw(y.r,k,q-delta);}
  g.set_raw(x.r,x.c,0);g.set_raw(y.r,y.c,0);if(rows){g.set_raw(x.r,y.c,x.w);g.set_raw(y.r,x.c,y.w);}else{g.set_raw(y.r,x.c,x.w);g.set_raw(x.r,y.c,y.w);}stat.bes_changed++;stat.changed_outer++;
 }
 void standard_optimized_step(Graph&g){if(rng.below(2)==0){stat.work++;stat.lazy++;return;}int move=int(rng.below(3));if(!move){U h1=g.hash1,h2=g.hash2;cycle(g);stat.changed_outer+=h1!=g.hash1||h2!=g.hash2;}else optimized_swap(g,move==2);}
 void hybrid_step(Graph&g){
  if(rng.below(2)==0){stat.work++;stat.lazy++;return;}U branch=rng.below(1000000);
  if(branch<opt.block_probability)block(g);
  else if(branch<opt.block_probability+opt.triple_probability)triple(g);
  else if(branch<opt.block_probability+opt.triple_probability+opt.rankone_probability)rankone(g);
  else if(branch<opt.block_probability+opt.triple_probability+opt.rankone_probability+opt.path_probability){stat.path_fallback_calls++;candidate(g,false);}
  else{stat.hybrid_strong_calls++;int move=int(rng.below(3));if(!move){U h1=g.hash1,h2=g.hash2;cycle(g);stat.changed_outer+=h1!=g.hash1||h2!=g.hash2;}else optimized_swap(g,move==2);}
 }
 struct LineClass {I lo,hi;U count,m,nu;int error;Big mass;};
 void auxiliary(Graph &g,int qden){
  stat.work++;stat.aux_calls++;if(rng.below(2)==0){stat.lazy++;return;}Rectangle r{};if(!rectangle(g,0,r))return;
  stat.rectangles++;auto a=g.cells(r);auto [lo,hi]=interval(a);if(lo>=hi)throw std::runtime_error("degenerate selected aux rectangle");
  std::array<int,4> verts{r.i,r.j,g.nr+r.k,g.nr+r.l};std::array<int,4> outside{
   g.degree[r.i]-int(a[0]>0)-int(a[1]>0),g.degree[r.j]-int(a[2]>0)-int(a[3]>0),
   g.degree[g.nr+r.k]-int(a[0]>0)-int(a[2]>0),g.degree[g.nr+r.l]-int(a[1]>0)-int(a[3]>0)};
  U mout=g.edges.size();for(I x:a)mout-=U(x>0);
  std::vector<LineClass> c{{lo,lo,1,0,0,0,0},{hi,hi,1,0,0,0,0}};if(hi-lo>1)c.push_back({lo+1,hi-1,U(hi-lo-1),0,0,0,0});
  int minerr=std::numeric_limits<int>::max(),maxerr=0;
  for(auto &s:c){std::array<I,4>x{a[0]+s.lo,a[1]-s.lo,a[2]-s.lo,a[3]+s.lo};std::array<int,4> pos{int(x[0]>0),int(x[1]>0),int(x[2]>0),int(x[3]>0)};std::array<int,4>d{outside[0]+pos[0]+pos[1],outside[1]+pos[2]+pos[3],outside[2]+pos[0]+pos[2],outside[3]+pos[1]+pos[3]};s.error=0;for(int t=0;t<4;++t)s.error+=std::abs(d[t]-g.target_degree[verts[t]]);s.m=mout;for(int b:pos)s.m+=b;s.nu=U(pos[0]&&pos[3])+U(pos[1]&&pos[2]);if(!s.nu||s.m<2)throw std::runtime_error("zero reverse rectangle selector");minerr=std::min(minerr,s.error);maxerr=std::max(maxerr,s.error);}
  if(maxerr-minerr>4)throw std::runtime_error("degree-class bound violated");

  Big denom_product=1;for(const auto&s:c){denom_product*=s.m;denom_product*=s.m-1;}
  Big total=0;for(auto &s:c){U power=1;for(int t=s.error;t<maxerr;++t)power*=qden;s.mass=denom_product/(s.m*(s.m-1));s.mass*=s.count;s.mass*=s.nu;s.mass*=power;total+=s.mass;}
  Big draw=rng.below_big(total);for(const auto &s:c){if(draw<s.mass){I delta=rng.integer(s.lo,s.hi);if(delta)g.apply(r,delta);else stat.zero_delta++;return;}draw-=s.mass;}throw std::runtime_error("aux class selection failed");
 }
 void pt_sweep(){for(size_t i=0;i<graphs.size();++i)auxiliary(graphs[i],qdens[i]);int i=int(rng.below(3)),j=i+1;stat.work++;stat.swap_attempts++;I difference=graphs[i].D-graphs[j].D;int ratio=qdens[j]/qdens[i],bits=ratio==2?1:2;bool accept=difference<=0||rng.pow2(U(difference)*bits);if(accept){std::swap(graphs[i],graphs[j]);stat.swap_accepts++;}}
};

long proc_memory(const std::string &name){std::ifstream f("/proc/self/status");std::string line;while(std::getline(f,line)){std::istringstream in(line);std::string k;long v;if(in>>k>>v&&k==name+":")return v;}return -1;}
void trace(std::ofstream &out,const Graph &g,const Engine &e,U iteration,int replica,int qden,double elapsed,bool butterflies){
 I binary=0;long double wmin=0,wdot=0,bfly=0;
 if(g.nr>=2){for(int id:g.adj[0]){const auto &x=g.edges[id];I y=g.value(1,x.c);if(y){binary++;wmin+=std::min(x.w,y);wdot+=(long double)x.w*y;}}}
 if(butterflies){for(int i=0;i<g.nr;++i)for(int j=i+1;j<g.nr;++j){I common=0;int source=g.adj[i].size()<g.adj[j].size()?i:j,other=source==i?j:i;for(int id:g.adj[source])common+=g.value(other,g.edges[id].c)>0;bfly+=(long double)common*(common-1)/2;}}
 I cell=g.value(g.event_r,g.event_c);out<<iteration<<','<<e.stat.work<<','<<replica<<','<<qden<<','<<std::setprecision(12)<<elapsed<<','<<g.D<<','<<(g.D==0)<<','<<g.edges.size()<<','<<std::hex<<g.hash1<<':'<<g.hash2<<std::dec<<','<<g.overlap<<','<<std::setprecision(21)<<g.sumw2<<','<<signed128(g.projection)<<','<<cell<<','<<(cell>=g.event_threshold)<<','<<binary<<','<<wmin<<','<<wdot<<',';if(butterflies)out<<bfly;out<<','<<g.flat()<<'\n';
}
int qden_from(const std::string &s){long double q=std::stold(s);for(int d:{1,2,4,16})if(std::abs(q-1.L/d)<1e-15L)return d;throw std::runtime_error("q must be 1, .5, .25 or .0625");}
U fixed_probability(const std::string&s){long double p=std::stold(s),n=roundl(p*1000000);if(p<0||p>1||std::abs(p*1000000-n)>1e-8L)throw std::runtime_error("probability must be a multiple of 0.000001 in [0,1]");return U(n);}
 
struct Json {std::string scalar;std::vector<Json>array;std::map<std::string,Json>object;};
struct JsonReader {
 std::string s;size_t p=0;explicit JsonReader(std::string text):s(std::move(text)){}
 void ws(){while(p<s.size()&&std::isspace(static_cast<unsigned char>(s[p])))p++;}
 std::string string(){ws();if(p==s.size()||s[p++]!='"')throw std::runtime_error("JSON needs string");std::string result;while(p<s.size()){char c=s[p++];if(c=='"')return result;if(c=='\\'){if(p==s.size())break;c=s[p++];if(c=='n')c='\n';else if(c=='r')c='\r';else if(c=='t')c='\t';else if(c!='"'&&c!='\\'&&c!='/')throw std::runtime_error("unsupported JSON escape");}result+=c;}throw std::runtime_error("unterminated JSON string");}
 Json value(){ws();if(p==s.size())throw std::runtime_error("JSON ends early");Json j;char c=s[p];if(c=='"'){j.scalar=string();return j;}if(c=='['){p++;ws();if(p<s.size()&&s[p]==']'){p++;return j;}for(;;){j.array.push_back(value());ws();if(p==s.size())throw std::runtime_error("JSON array ends early");char sep=s[p++];if(sep==']')break;if(sep!=',')throw std::runtime_error("JSON array separator");}return j;}if(c=='{'){p++;ws();if(p<s.size()&&s[p]=='}'){p++;return j;}for(;;){std::string key=string();ws();if(p==s.size()||s[p++]!=':')throw std::runtime_error("JSON object colon");j.object.emplace(key,value());ws();if(p==s.size())throw std::runtime_error("JSON object ends early");char sep=s[p++];if(sep=='}')break;if(sep!=',')throw std::runtime_error("JSON object separator");}return j;}size_t start=p;while(p<s.size()&&s[p]!=','&&s[p]!=']'&&s[p]!='}'&&!std::isspace(static_cast<unsigned char>(s[p])))p++;if(start==p)throw std::runtime_error("JSON invalid scalar");j.scalar=s.substr(start,p-start);return j;}
 Json parse(){Json j=value();ws();if(p!=s.size())throw std::runtime_error("trailing JSON");return j;}
};
void write_integer_array(std::ostream&o,const std::vector<I>&v){o<<'[';for(size_t i=0;i<v.size();++i)o<<(i?",":"")<<v[i];o<<']';}
int fast_block_audit(const std::string&path){
 std::ifstream f(path);if(!f)throw std::runtime_error("cannot read fast block fixtures");std::ostringstream content;content<<f.rdbuf();Json root=JsonReader(content.str()).parse();const auto&fixtures=root.object.at("fixtures").array;
 std::cout<<"{\"solver\":\"fast\",\"fixtures\":[";for(size_t i=0;i<fixtures.size();++i){const auto&item=fixtures[i].object;std::vector<I>a,b;for(const auto&x:item.at("a").array)a.push_back(std::stoll(x.scalar));for(const auto&x:item.at("b").array)b.push_back(std::stoll(x.scalar));FastCountedBlock cb(a,b);Big total=cb.total_big();auto counts=cb.support_counts();if(i)std::cout<<',';std::cout<<"{\"effective_shared_dimension\":"<<cb.variable.size()<<",\"unit_shortcut\":"<<(cb.unit?"true":"false")<<",\"equal_trade_shortcut\":"<<(cb.equal_trade?"true":"false")<<",\"total\":\""<<total.decimal()<<"\",\"support_counts\":[";
  for(size_t z=0;z<counts.size();++z){if(z)std::cout<<',';std::cout<<"{\"support\":[";bool first=true;for(size_t t=0;t<cb.exclusive.size();++t)if(counts[z].first>>t&1){if(!first)std::cout<<',';first=false;std::cout<<cb.exclusive[t];}std::cout<<"],\"count\":\""<<counts[z].second.decimal()<<"\"}";}std::cout<<"],\"draws\":[";
  std::vector<Big>ranks;if(item.count("ranks")){for(const auto&x:item.at("ranks").array)ranks.push_back(Big::decimal(x.scalar));}else{if(total>Big(10000))throw std::runtime_error("fast audit needs explicit ranks when total >10000");for(Big r(0);r<total;r+=Big(1))ranks.push_back(r);}
  for(size_t z=0;z<ranks.size();++z){if(z)std::cout<<',';auto [x,y]=cb.unrank(ranks[z]);std::cout<<"{\"rank\":\""<<ranks[z].decimal()<<"\",\"a\":";write_integer_array(std::cout,x);std::cout<<",\"b\":";write_integer_array(std::cout,y);std::cout<<'}';}std::cout<<"]}";
 }std::cout<<"]}\n";return 0;
}
int block_audit(const std::string&path,const std::string&solver="reference"){
 if(solver=="fast")return fast_block_audit(path);if(solver!="reference")throw std::runtime_error("audit solver must be fast or reference");
 std::ifstream f(path);if(!f)throw std::runtime_error("cannot read block-audit fixtures");std::ostringstream content;content<<f.rdbuf();Json root=JsonReader(content.str()).parse();const auto&fixtures=root.object.at("fixtures").array;
 std::cout<<"{\"fixtures\":[";for(size_t i=0;i<fixtures.size();++i){const auto&item=fixtures[i].object;std::vector<I>a,b;for(const auto&x:item.at("a").array)a.push_back(std::stoll(x.scalar));for(const auto&x:item.at("b").array)b.push_back(std::stoll(x.scalar));CountedBlock cb(a,b);if(i)std::cout<<',';std::cout<<"{\"total\":\""<<cb.total.decimal()<<"\",\"support_counts\":[";
  for(size_t z=0;z<cb.supports.size();++z){if(z)std::cout<<',';std::cout<<"{\"support\":[";bool first=true;for(size_t t=0;t<cb.exclusive.size();++t)if(cb.supports[z].mask>>t&1){if(!first)std::cout<<',';first=false;std::cout<<cb.exclusive[t];}std::cout<<"],\"count\":\""<<cb.supports[z].count.decimal()<<"\"}";}std::cout<<"],\"draws\":[";
  std::vector<Big>ranks;if(item.count("ranks")){for(const auto&x:item.at("ranks").array)ranks.push_back(Big::decimal(x.scalar));}else{if(cb.total>Big(10000))throw std::runtime_error("audit needs explicit ranks when total >10000");for(Big r(0);r<cb.total;r+=Big(1))ranks.push_back(r);}
  for(size_t z=0;z<ranks.size();++z){if(z)std::cout<<',';auto [x,y]=cb.unrank(ranks[z]);std::cout<<"{\"rank\":\""<<ranks[z].decimal()<<"\",\"a\":";write_integer_array(std::cout,x);std::cout<<",\"b\":";write_integer_array(std::cout,y);std::cout<<'}';}std::cout<<"]}";
 }std::cout<<"]}\n";return 0;
}
int main(int argc,char **argv){try{
 std::map<std::string,std::string>a;for(int i=1;i<argc;i+=2){if(i+1>=argc)throw std::runtime_error("each flag requires a value");a[argv[i]]=argv[i+1];}auto get=[&](const std::string&k,const std::string&d){return a.count(k)?a[k]:d;};if(a.count("--block-audit"))return block_audit(a.at("--block-audit"),get("--block-solver","reference"));Options o;
 o.anchor_mode=get("--anchor-mode","dual");if(o.anchor_mode!="single"&&o.anchor_mode!="dual")throw std::runtime_error("anchor-mode must be single or dual");o.input=get("--input","");o.method=get("--method","candidate");o.out=get("--out","run");o.seed=std::stoull(get("--seed",std::to_string(0x135288bULL)));o.budget=std::stoull(get("--primitive-budget","200000"));o.wall_seconds=std::stod(get("--wall-seconds","0"));o.trace_every=std::stoull(get("--trace-every","100"));o.check_every=std::stoull(get("--check-every","10000"));o.max_outer=std::stoull(get("--outer-budget","0"));o.kappa_argument=get("--kappa","0");bool kappa_initial=o.kappa_argument=="m"||o.kappa_argument=="m0";if(!kappa_initial){if(o.kappa_argument.empty()||o.kappa_argument.find_first_not_of("0123456789")!=std::string::npos)throw std::runtime_error("kappa needs nonnegative integer or m0");o.kappa=std::stoull(o.kappa_argument);}o.q_den=qden_from(get("--q",".0625"));o.pt_trace=get("--pt-trace","cold");o.acceptance=get("--acceptance","log");o.cycle_mix=std::stold(get("--cycle-mix","0"));o.butterflies=std::stoi(get("--butterflies","-1"));o.block_mode=get("--block-mode","anchor");o.block_width=std::stoi(get("--block-width","8"));o.orientation=get("--orientation","both");o.cycle_probability=fixed_probability(get("--cycle-prob","0"));o.path_probability=fixed_probability(get("--path-prob","0"));o.triple_probability=fixed_probability(get("--triple-prob","0"));o.rankone_probability=fixed_probability(get("--rankone-prob","0"));o.rankone_selector=get("--rankone-selector","uniform");if(o.rankone_selector!="uniform"&&o.rankone_selector!="wedge_triple"&&o.rankone_selector!="mixed")throw std::runtime_error("rankone-selector must be uniform, wedge_triple or mixed");o.block_probability=fixed_probability(get("--block-prob",".7"));o.block_solver=get("--block-solver","fast");o.block_shape=get("--block-shape","union");if(o.block_shape=="twobridge")o.block_shape="two_bridge";o.budget_scope=get("--budget-scope","sampling");auto support_flag=get("--support-only","0");if(support_flag!="0"&&support_flag!="1")throw std::runtime_error("support-only must be 0 or 1");o.support_only=support_flag=="1";o.owner_update=get("--owner-update","heatbath");if(o.owner_update!="heatbath"&&o.owner_update!="metropolis_refresh")throw std::runtime_error("owner-update must be heatbath or metropolis_refresh");if(o.owner_update=="metropolis_refresh"&&o.block_solver!="fast")throw std::runtime_error("metropolis_refresh requires fast block solver");auto cache_flag=get("--block-cache-capacity","0");if(cache_flag!="0"&&cache_flag!="128")throw std::runtime_error("block-cache-capacity must be 0 or 128");o.block_cache_capacity=std::stoi(cache_flag);if(o.block_cache_capacity&&o.block_solver!="fast")throw std::runtime_error("block cache requires fast solver");o.neighbor_count=get("--neighbor-count","2");if(o.neighbor_count!="2"&&o.neighbor_count!="3"&&o.neighbor_count!="4"&&o.neighbor_count!="6"&&o.neighbor_count!="mixed23"&&o.neighbor_count!="mixed24")throw std::runtime_error("neighbor-count must be 2,3,4,6,mixed23 or mixed24");if(o.neighbor_count=="mixed23"||o.neighbor_count=="mixed24"){o.neighbor_k=2;o.mixed_neighbor_k=o.neighbor_count=="mixed23"?3:4;}else o.neighbor_k=std::stoi(o.neighbor_count);auto shared_limit=get("--max-effective-shared","-1");if(shared_limit!="-1"&&(shared_limit.empty()||shared_limit.find_first_not_of("0123456789")!=std::string::npos))throw std::runtime_error("max-effective-shared must be -1 or 0..12");o.max_effective_shared=std::stoi(shared_limit);if(o.max_effective_shared< -1||o.max_effective_shared>12)throw std::runtime_error("max-effective-shared must be -1 or 0..12");auto shift_limit=get("--max-effective-shifts","-1");if(shift_limit!="-1"&&(shift_limit.empty()||shift_limit.find_first_not_of("0123456789")!=std::string::npos))throw std::runtime_error("max-effective-shifts must be -1 or 0..4096");o.max_effective_shifts=std::stoi(shift_limit);if(o.max_effective_shifts< -1||o.max_effective_shifts>4096)throw std::runtime_error("max-effective-shifts must be -1 or 0..4096");if(o.block_shape=="neighbor_union_general"){int maxk=o.neighbor_count=="mixed23"?3:o.neighbor_count=="mixed24"?4:std::stoi(o.neighbor_count);int width=2*maxk;if(a.count("--block-width")&&o.block_width!=width)throw std::runtime_error("general block-width must match 2*maximum neighbor-count");o.block_width=width;}
 auto online_flag=get("--online-summary","0");if(online_flag!="0"&&online_flag!="1")throw std::runtime_error("online-summary must be 0 or 1");o.online_summary=online_flag=="1";o.online_burn=probe_unsigned_v12(get("--online-burn","0"),"online-burn");
 o.probe_queries=get("--probe-queries","");o.probe_batch_width=probe_unsigned_v12(get("--probe-batch-width","1000"),"probe-batch-width");o.probe_trace_every=probe_unsigned_v12(get("--probe-trace-every","0"),"probe-trace-every");if(o.online_summary&&o.probe_queries.empty())throw std::runtime_error("probe-queries required when online-summary1");if(!o.online_summary&&(!o.probe_queries.empty()||o.probe_trace_every))throw std::runtime_error("probe queries and trace require online-summary1");
 if(o.online_summary){o.max_outer=probe_unsigned_v12(get("--outer-budget","0"),"outer-budget");o.budget=probe_unsigned_v12(get("--primitive-budget","200000"),"primitive-budget");if(!o.max_outer||o.budget||o.wall_seconds!=0||o.online_burn>=o.max_outer||(o.method!="standard_opt"&&o.method!="hybrid"&&o.method!="block"&&o.method!="homerun"))throw std::runtime_error("online requires fixed outer-budget N, primitive-budget 0, wall-seconds 0, 0<=burn<N and a supported target kernel");if((o.method=="hybrid"||o.method=="block")&&o.path_probability&&o.acceptance!="exact")throw std::runtime_error("online path mixtures require exact acceptance");}else if(o.online_burn)throw std::runtime_error("online-burn requires online-summary 1");
 long double rho=std::stold(get("--rho",".25"));if(std::abs(rho-.25L)<1e-15L)o.rho_den=4;else if(std::abs(rho-.0625L)<1e-15L)o.rho_den=16;else throw std::runtime_error("rho must be .25 or .0625");
 if(o.input.empty()||(o.method!="candidate"&&o.method!="aux"&&o.method!="pt"&&o.method!="block"&&o.method!="standard"&&o.method!="standard_opt"&&o.method!="hybrid"&&o.method!="homerun")||(o.cycle_mix!=0&&o.cycle_mix!=.5L)||(o.acceptance!="log"&&o.acceptance!="exact")||!o.trace_every||(o.budget==0&&o.wall_seconds<=0&&o.max_outer==0))throw std::runtime_error("invalid options");
 if((o.block_mode!="uniform"&&o.block_mode!="wedge"&&o.block_mode!="anchor"&&o.block_mode!="mixed")||(o.block_width!=4&&o.block_width!=6&&o.block_width!=8&&o.block_width!=12)||(o.orientation!="row"&&o.orientation!="col"&&o.orientation!="both")||o.cycle_probability+o.triple_probability+o.rankone_probability+o.path_probability>1000000||(o.method=="hybrid"&&o.block_probability+o.triple_probability+o.rankone_probability+o.path_probability>1000000)||(o.block_solver!="reference"&&o.block_solver!="fast")||(o.block_shape!="union"&&o.block_shape!="two_bridge"&&o.block_shape!="exclusive4"&&o.block_shape!="two_bridge_local"&&o.block_shape!="exclusive4_local"&&o.block_shape!="local_mixed"&&o.block_shape!="neighbor_union"&&o.block_shape!="neighbor_union_general")||(o.block_shape!="union"&&o.block_shape!="neighbor_union_general"&&o.block_width!=4)||((o.block_shape=="exclusive4"||o.block_shape=="exclusive4_local"||o.block_shape=="local_mixed"||o.block_shape=="neighbor_union"||o.block_shape=="neighbor_union_general")&&(o.block_mode=="anchor"||o.block_mode=="mixed"))||(o.budget_scope!="sampling"&&o.budget_scope!="end_to_end"))throw std::runtime_error("invalid block options");
 if(o.pt_trace!="cold"&&o.pt_trace!="all")throw std::runtime_error("pt-trace must be cold or all");
 auto total_start=Clock::now();Engine e(o);e.graphs.push_back(Graph::load(o.input,(o.method=="candidate"||((o.method=="block"||o.method=="hybrid")&&o.path_probability>0))&&(o.kappa>0||kappa_initial),o.method=="standard_opt"||o.method=="hybrid"));if(kappa_initial){o.kappa=e.graphs[0].original.size();e.opt.kappa=o.kappa;}if(o.method=="pt"){e.qdens={1,2,4,16};for(int i=1;i<4;++i)e.graphs.push_back(e.graphs[0]);}else e.qdens={o.q_den};
 if(o.method=="homerun")for(const auto&edge:e.graphs[0].edges)if(edge.w!=1)throw std::runtime_error("HomeRun supports binary initial weights only");
 if(o.method=="block"||o.method=="hybrid")e.initialize_wedges(e.graphs[0]);
 for(auto&g:e.graphs){g.counters=&e.stat;if(!g.check())throw std::runtime_error("initial invariant failed");}
 bool butterflies=o.butterflies<0?U(e.graphs[0].nr)*U(e.graphs[0].nc)<=256:o.butterflies!=0;
 std::unique_ptr<FixedProbeStatistics> online;if(o.online_summary)online=std::make_unique<FixedProbeStatistics>(e.graphs[0],o.online_burn,o.max_outer,o.probe_queries,o.probe_batch_width,o.probe_trace_every);
 double build_seconds=std::chrono::duration<double>(Clock::now()-total_start).count();
 std::ofstream tr(o.out+".trace.csv"),ck(o.out+".checks.csv");if(!tr||!ck)throw std::runtime_error("cannot create output files");
 tr<<"iteration,primitive_work,replica,q_denominator,elapsed_seconds,D,is_target,m,state_signature,support_overlap,sum_w2,hash_projection,cell_weight,cell_tail,row_pair_binary_overlap,row_pair_weighted_overlap_min,row_pair_weighted_dot,butterflies,flat_state\n";
 ck<<"iteration,primitive_work,replica,all_strengths_degrees_indices_stats_exact\n";
 auto run_start=Clock::now();auto seconds=[&](){return std::chrono::duration<double>(Clock::now()-run_start).count();};
 auto emit=[&](){for(size_t r=0;r<e.graphs.size();++r){if(o.method=="pt"&&o.pt_trace=="cold"&&r!=3)continue;trace(tr,e.graphs[r],e,e.stat.outer,int(r),e.qdens[r],seconds(),butterflies);}};
 auto check=[&](){for(size_t r=0;r<e.graphs.size();++r){bool ok=e.graphs[r].check()&&((o.method!="candidate"&&o.method!="block"&&o.method!="standard"&&o.method!="standard_opt"&&o.method!="hybrid"&&o.method!="homerun")||e.graphs[r].D==0);ck<<e.stat.outer<<','<<e.stat.work<<','<<r<<','<<ok<<'\n';if(!ok)throw std::runtime_error("checkpoint invariant failed");}};
 emit();check();U last_trace=0,last_check=0;
 for(;;){if(o.budget&&e.stat.work>=o.budget)break;if(o.max_outer&&e.stat.outer>=o.max_outer)break;if(o.wall_seconds>0&&(o.budget_scope=="sampling"?seconds():std::chrono::duration<double>(Clock::now()-total_start).count())>=o.wall_seconds)break;
  if(o.method=="candidate")e.candidate(e.graphs[0]);else if(o.method=="aux")e.auxiliary(e.graphs[0],o.q_den);else if(o.method=="pt")e.pt_sweep();else if(o.method=="block")e.block_step(e.graphs[0]);else if(o.method=="standard_opt")e.standard_optimized_step(e.graphs[0]);else if(o.method=="hybrid")e.hybrid_step(e.graphs[0]);else if(o.method=="homerun")e.homerun_step(e.graphs[0]);else e.standard_step(e.graphs[0]);e.stat.outer++;
  if(online)online->observe(e.graphs[0],e.stat.outer,e.stat.cell_updates);
  if(e.stat.outer%o.trace_every==0){emit();last_trace=e.stat.outer;}if(o.check_every&&e.stat.outer%o.check_every==0){check();last_check=e.stat.outer;}
 }
 if(last_trace!=e.stat.outer)emit();if(last_check!=e.stat.outer)check();tr.flush();ck.flush();if(online)online->write(o.out);double run_seconds=seconds(),total_seconds=std::chrono::duration<double>(Clock::now()-total_start).count();
 std::ofstream report(o.out+".json");if(!report)throw std::runtime_error("cannot write summary");auto &s=e.stat;const auto&g=e.graphs[0];
 double actual_block=o.method=="hybrid"?double(o.block_probability)/1000000:o.method=="block"?1.-double(o.cycle_probability+o.triple_probability+o.rankone_probability+o.path_probability)/1000000:0.;double actual_path=(o.method=="hybrid"||o.method=="block")?double(o.path_probability)/1000000:0.;double actual_triple=(o.method=="hybrid"||o.method=="block")?double(o.triple_probability)/1000000:0.;double actual_rankone=(o.method=="hybrid"||o.method=="block")?double(o.rankone_probability)/1000000:0.;double actual_strong=o.method=="hybrid"?1.-actual_block-actual_triple-actual_rankone-actual_path:o.method=="standard_opt"?1.:0.;double actual_cycle=o.method=="block"?double(o.cycle_probability)/1000000:actual_strong/3.;
 report<<std::setprecision(18)<<"{\n\"observer_format\":\"fixed_probe_statistics_v1\",\n\"probe_batch_width\":"<<o.probe_batch_width<<",\n\"probe_trace_every\":"<<o.probe_trace_every<<",\n\"block_cache_capacity\":"<<o.block_cache_capacity<<",\n\"block_cache_policy\":\"process-local bounded LRU of exact conditional class; ordered local (column sum,arity), row0 degree/strength and width key; no current point or live stat pointers retained; every use rebinds current a/b and all suffix stat pointers; no RNG consumption or selector change; estimated bytes approximate retained payload, not RSS\",\n\"online_summary\":"<<(o.online_summary?"true":"false")<<",\n\"online_burn_outer\":"<<o.online_burn<<",\n\"online_initialization_seconds\":"<<(online?double(online->initialization_nanoseconds)/1e9:0.)<<",\n\"online_observation_seconds\":"<<(online?double(online->observation_nanoseconds)/1e9:0.)<<",\n\"online_finalization_seconds\":"<<(online?double(online->finalization_nanoseconds)/1e9:0.)<<",\n\"online_timing_policy\":\"Diagnostic observer-call and finalization intervals; clock overhead and online output included in total_seconds_including_build\",\n\"rankone_selector\":\""<<o.rankone_selector<<"\",\n\"rankone_selector_policy\":\"uniform triple or fixed .5/.5 mixed; wedge pair then uniform third; sorted triple discards pair/anchor witness; empty wedge falls back uniform; marginal triple mass sum(pair common-neighbor counts)/[Z_w*(n-2)] is class invariant; anchor is not forced into union\",\n\"rankone_probability_given_nonlazy\":"<<double(o.rankone_probability)/1000000<<",\n\"rankone_policy\":\"selected unordered three nodes; each draws one uniform neighbor; union has <=3 columns; active support E>3+width holds; enumerate complete tree/unicyclic conditional fiber with exact interval counts; proposal uniform then label multiplicity MH min(1,Mnew/Mold); rejection retains original matrix; independent of owner-update\",\n\"triple_probability_given_nonlazy\":"<<double(o.triple_probability)/1000000<<",\n\"triple_policy\":\"uniform unordered three nodes; each draws min(2,degree) neighbors without replacement; partial column arity must be one else hold; all labeled rowcount/strength assignments enumerated <=90; uniform or equal-mass MetGibbs exclude current; no weight splits\",\n\"neighbor_count\":\""<<o.neighbor_count<<"\",\n\"max_effective_shared\":"<<o.max_effective_shared<<",\n\"max_effective_shifts\":"<<o.max_effective_shifts<<",\n\"compressed_shift_policy\":\"exact signed IE shifts merged; suffix descriptors precomputed once per solver; Dmax covers full and all decoder suffixes; h<=2 direct kernels have effective D0; optional class-invariant cap keeps invalid holds without retry; cap off builds no extra gate descriptor\",\n\"general_selector_policy\":\"each row uniformly draws min(k,degree) neighbors without replacement using Floyd; union is complete conditional label; mixed23/mixed24 coin fixed .5/.5; cap checks effective shared dimension after selection; all skipped labels hold without retry\",\n\"owner_update\":\""<<o.owner_update<<"\",\n\"owner_update_policy\":\"metropolis_refresh proposes other owners proportional to their exact completion count; MH chooses final owner then always uniformly refreshes its completion, including rejected proposals; single-owner falls back to original conditional heatbath\",\n\"support_only\":"<<(o.support_only?"true":"false")<<",\n\"homerun_policy\":\"HomeRun Algorithm 2 implementation; binary-only; full row/column scan; common fixed .5 outer laziness; dense extraction and runtime margin guards included\",\n\"homerun_source\":\"https://rionda.to/papers/ContrerasCatalanRiondato-HomeRun-WWW.pdf\",\n\"selector_policy\":\"local shapes: fixed uniform neighbor draws, invalid holds, no resampling; two_bridge_local wedge uses sampled anchor as one shared block column; exclusive4_local and neighbor_union wedge use anchor only for row pair selection; local_mixed has fixed .5/.5 branches\",\n\"kernel_mixture_given_nonlazy\":{\"block\":"<<actual_block<<",\"path\":"<<actual_path<<",\"triple\":"<<actual_triple<<",\"rankone\":"<<actual_rankone<<",\"cycle\":"<<actual_cycle<<",\"SES\":"<<actual_strong/3.<<",\"BES\":"<<actual_strong/3.<<",\"HomeRun\":"<<(o.method=="homerun"?1.:0.)<<"},\n\"block_solver\":\""<<o.block_solver<<"\",\n\"block_shape\":\""<<o.block_shape<<"\",\n\"block_probability_given_nonlazy\":"<<double(o.block_probability)/1000000<<",\n\"budget_scope\":\""<<o.budget_scope<<"\",\n\"wall_budget_overshoot_seconds\":"<<(o.wall_seconds>0?std::max(0.,(o.budget_scope=="sampling"?run_seconds:total_seconds)-o.wall_seconds):0)<<",\n\"weight_group_index_enabled\":"<<(g.maintain_weight_groups?"true":"false")<<",\n\"standard_opt_policy\":\"isolated research adaptation: uniform weight groups with replacement SES; common-support-neighbor BES; invalid compensation holds retained; intrinsic index maintenance included\",\n\"block_mode\":\""<<o.block_mode<<"\",\n\"block_width\":"<<o.block_width<<",\n\"orientation\":\""<<o.orientation<<"\",\n\"cycle_probability_given_nonlazy\":"<<double(o.cycle_probability)/1000000<<",\n\"path_probability_given_nonlazy\":"<<double(o.path_probability)/1000000<<",\n\"status\":\"completed\",\n\"anchor_mode\":\""<<o.anchor_mode<<"\",\n\"method\":\""<<o.method<<"\",\n\"seed\":"<<o.seed<<",\n\"nr\":"<<g.nr<<",\n\"nc\":"<<g.nc<<",\n\"initial_edges\":"<<g.original.size()<<",\n\"kappa_argument\":\""<<o.kappa_argument<<"\",\n\"kappa\":"<<o.kappa<<",\n\"rho_denominator\":"<<o.rho_den<<",\n\"q_denominator\":"<<o.q_den<<",\n\"cycle_mix\":"<<o.cycle_mix<<",\n\"acceptance\":\""<<o.acceptance<<"\",\n\"pt_trace\":\""<<o.pt_trace<<"\",\n\"build_seconds\":"<<build_seconds<<",\n\"run_seconds_including_checks_and_trace\":"<<run_seconds<<",\n\"total_seconds_including_build\":"<<total_seconds<<",\n\"proc_vm_hwm_kib\":"<<proc_memory("VmHWM")<<",\n\"requested_primitive_budget\":"<<o.budget<<",\n\"requested_wall_seconds\":"<<o.wall_seconds<<",\n\"trace_every_outer_iterations\":"<<o.trace_every<<",\n\"check_every_outer_iterations\":"<<o.check_every<<",\n\"butterflies_computed\":"<<(butterflies?"true":"false")<<",\n\"event_cell\":["<<g.event_r<<','<<g.event_c<<"],\n\"event_threshold\":"<<g.event_threshold<<",\n\"counters\":{\n";
 #define COUNT(name) report<<"\""#name"\":"<<s.name<<",\n"
 COUNT(owner_cardinality_dp_cells);COUNT(owner_combination_nodes);COUNT(owner_sum_pruned_subtrees);COUNT(owner_sum_pruned_masks);COUNT(owner_feasible_masks_examined);COUNT(owner_direct_trade_rank_calls);COUNT(work);COUNT(outer);COUNT(lazy);COUNT(inner);COUNT(invalid_pairs);COUNT(rectangles);COUNT(zero_delta);COUNT(returned);COUNT(accepted);COUNT(mh_rejected);COUNT(timeouts);COUNT(changed_outer);COUNT(rollback_rectangles);COUNT(cell_updates);COUNT(inserts);COUNT(deletes);COUNT(fenwick_updates);COUNT(checks);COUNT(checked_edges);COUNT(aux_calls);COUNT(swap_attempts);COUNT(swap_accepts);COUNT(cycle_calls);COUNT(cycle_valid);COUNT(cycle_changed);COUNT(max_path);COUNT(changed_tour);COUNT(changed_tour_multistep);COUNT(changed_tour_steps_total);COUNT(first_edge_defect_branch);COUNT(first_edge_uniform_branch);COUNT(block_calls);COUNT(block_changed);COUNT(block_support_changed);COUNT(block_nontrivial);COUNT(block_support_nontrivial);COUNT(block_empty_wedge);COUNT(block_uniform_pairs);COUNT(block_wedge_pairs);COUNT(block_forced_anchors);COUNT(block_row_orientation);COUNT(block_col_orientation);COUNT(block_count_calls);COUNT(block_count_terms);COUNT(block_max_count_bits);COUNT(block_count_nanoseconds);COUNT(block_select_nanoseconds);COUNT(block_commit_nanoseconds);COUNT(ses_calls);COUNT(ses_valid);COUNT(ses_changed);COUNT(bes_calls);COUNT(bes_valid);COUNT(bes_changed);COUNT(path_fallback_calls);COUNT(weight_index_updates);COUNT(weight_group_creates);COUNT(weight_group_deletes);COUNT(weight_group_checks);COUNT(bridge_scan_edges);COUNT(bridge_common_candidates);COUNT(bridge_empty_common);COUNT(bridge_compensation_invalid);COUNT(fast_unit_calls);COUNT(fast_equal_trade_calls);COUNT(fast_h0_calls);COUNT(fast_h1_calls);COUNT(fast_h2_calls);COUNT(fast_general_calls);COUNT(fast_singleton_calls);COUNT(fast_small_count_calls);COUNT(fast_prefix_builds);COUNT(fast_prefix_queries);COUNT(hybrid_strong_calls);COUNT(block_shape_holds);COUNT(block_local_calls);COUNT(block_local_neighbor_draws);COUNT(block_local_lookup_checks);COUNT(block_local_exclusive_holds);COUNT(block_local_shared_holds);COUNT(block_local_degree_holds);COUNT(block_scan_union_calls);COUNT(block_scan_neighbor_visits);COUNT(block_local_two_bridge_branches);COUNT(block_local_exclusive4_branches);COUNT(block_local_neighbor_union_branches);COUNT(block_support_only_holds);COUNT(block_selected_exclusive_columns);COUNT(block_selected_shared_columns);COUNT(block_max_effective_shared);COUNT(block_solved_max_effective_shared);COUNT(homerun_calls);COUNT(homerun_changed);COUNT(homerun_scan_columns);COUNT(homerun_reservoir_draws);COUNT(homerun_reservoir_replacements);COUNT(homerun_reservoir_removals);COUNT(owner_metropolis_calls);COUNT(owner_proposals);COUNT(owner_accepts);COUNT(owner_rejects);COUNT(owner_one_support_heatbath);COUNT(owner_completion_refreshes);COUNT(owner_rejected_refresh_changed);COUNT(owner_matrix_changed);COUNT(owner_support_changed);COUNT(owner_state_holds_after_refresh);COUNT(block_general_calls);COUNT(block_general_k2_calls);COUNT(block_general_k3_calls);COUNT(block_general_k4_calls);COUNT(block_general_k6_calls);COUNT(block_effective_shared_holds);COUNT(block_selected_width_total);COUNT(block_selected_width_max);COUNT(triple_calls);COUNT(triple_nodes_too_few);COUNT(triple_neighbor_draws);COUNT(triple_lookup_checks);COUNT(triple_exclusivity_holds);COUNT(triple_partition_calls);COUNT(triple_partition_candidates);COUNT(triple_legal_assignments);COUNT(triple_nontrivial);COUNT(triple_changed);COUNT(triple_singleton_holds);COUNT(triple_metropolis_draws);COUNT(triple_max_assignments);COUNT(triple_selected_width_total);COUNT(triple_selected_width_max);COUNT(triple_select_nanoseconds);COUNT(triple_solve_nanoseconds);COUNT(triple_commit_nanoseconds);COUNT(triple_row_orientation);COUNT(triple_col_orientation);COUNT(rankone_calls);COUNT(rankone_nodes_too_few);COUNT(rankone_zero_degree_holds);COUNT(rankone_neighbor_draws);COUNT(rankone_lookup_checks);COUNT(rankone_dimension_holds);COUNT(rankone_solver_calls);COUNT(rankone_supports_examined);COUNT(rankone_highrank_supports);COUNT(rankone_feasible_supports);COUNT(rankone_tree_completions);COUNT(rankone_cycle_completions);COUNT(rankone_current_highrank_holds);COUNT(rankone_current_zero_label_holds);COUNT(rankone_proposals);COUNT(rankone_label_accepts);COUNT(rankone_label_rejects);COUNT(rankone_zero_label_proposals);COUNT(rankone_changed);COUNT(rankone_support_changed);COUNT(rankone_max_completion_bits);COUNT(rankone_max_total_bits);COUNT(rankone_selected_width_total);COUNT(rankone_selected_width_max);COUNT(rankone_select_nanoseconds);COUNT(rankone_solve_nanoseconds);COUNT(rankone_commit_nanoseconds);COUNT(rankone_row_orientation);COUNT(rankone_col_orientation);COUNT(rankone_uniform_triples);COUNT(rankone_wedge_triples);COUNT(rankone_empty_wedge_fallbacks);COUNT(rankone_mixed_uniform_branches);COUNT(rankone_mixed_wedge_branches);COUNT(rankone_selector_neighbor_draws);COUNT(compressed_descriptor_builds);COUNT(compressed_descriptor_terms);COUNT(compressed_descriptor_max_terms);COUNT(compressed_raw_subset_terms);COUNT(compressed_full_descriptor_max_terms);COUNT(compressed_solver_descriptor_max_terms);COUNT(block_shift_gate_calls);COUNT(block_shift_gate_nanoseconds);COUNT(block_effective_shift_holds);COUNT(block_selected_full_shifts_total);COUNT(block_selected_max_shifts_total);COUNT(block_selected_max_shifts);COUNT(block_solved_max_shifts);COUNT(block_cache_lookups);COUNT(block_cache_hits);COUNT(block_cache_misses);COUNT(block_cache_evictions);COUNT(block_cache_entries_current);COUNT(block_cache_entries_peak);COUNT(block_cache_estimated_bytes_current);COUNT(block_cache_estimated_bytes_peak);COUNT(block_cache_key_nanoseconds);COUNT(block_cache_bind_nanoseconds);COUNT(block_cache_build_nanoseconds);
 #undef COUNT
 report<<"\"max_abs_log_ratio\":"<<s.max_abs_log_ratio<<"},\n\"all_checkpoints_passed\":true,\n\"budget_policy\":\"stop only after a complete outer iteration; no path hard cap; final work may exceed budget\",\n\"work_unit_definition\":\"one lazy outer hold, counted block call, cycle/SES/BES attempt, full HomeRun row trade, exclusive triple call, path inner proposal, aux call, rollback rectangle, or PT swap attempt; wall time is main cross-method cost\",\n\"numerics\":\"counted block counts and unranking, aux class draws and PT swaps exact integer; candidate/fallback log MH uses long double unless acceptance=exact\",\n\"sample_policy\":\"all scheduled traces retain repeats; only rows with is_target=1 have the intended exact-degree conditional target\"\n}\n";
 std::cout<<o.method<<" completed work="<<s.work<<" outer="<<s.outer<<" run_seconds="<<run_seconds<<" target_D="<<g.D<<'\n';return 0;
 }catch(const std::exception&e){std::cerr<<e.what()<<'\n';return 1;}}
