#pragma once
#include "cohort_local_private_scene.hpp"

struct CohortConditional {
 static constexpr U MEMORY_BUDGET=64ULL*1024*1024,CELL_BUDGET=1000000,WORK_BUDGET=0x1312d00;
 struct Record {int label,owner;I weight;};
 struct Scene {int o=0,root=0;std::vector<int>actors;std::vector<Record>records;bool local_private=false,collection_hold=false;std::vector<int>full_actors;std::vector<std::pair<int,I>>full_pool_signature;};
 static Big multiply(const Big&a,const Big&b){Big c;if(a.a.empty()||b.a.empty())return c;c.a.assign(a.a.size()+b.a.size(),0);for(U i=0;i<a.a.size();++i){U carry=0;for(U j=0;j<b.a.size();++j){U z=U(a.a[i])*b.a[j]+c.a[i+j]+carry;c.a[i+j]=uint32_t(z);carry=z>>32;}U k=i+b.a.size();while(carry){U z=U(c.a[k])+carry;c.a[k]=uint32_t(z);carry=z>>32;++k;if(carry&&k==c.a.size())c.a.push_back(0);}}c.trim();return c;}
 static U sat_product(U a,U b,U stop){if(!a||!b)return 0;return a>stop/b?stop+1:a*b;}
 static U sat_add(U a,U b,U stop){return a>stop||b>stop-a?stop+1:a+b;}
 static Big binomial(U n,U k){if(k>n)return Big(0);k=std::min(k,n-k);Big result(1);for(U j=1;j<=k;++j){result*=n-k+j;result=result/j;}return result;}
 static unsigned binomial_bound_bits(U n,U k){mpz_class z;mpz_bin_uiui(z.get_mpz_t(),n,std::min(k,n-k));return unsigned(mpz_sizeinbase(z.get_mpz_t(),2));}
 static U estimated_bytes(U cells,U bits,U extra_per_cell=0){__uint128_t z=__uint128_t(cells)*(sizeof(Big)+32+2*((bits+31)/32)*sizeof(uint32_t)+extra_per_cell);return z>std::numeric_limits<U>::max()?std::numeric_limits<U>::max():U(z);}
 struct TwoProblem {
  std::vector<U>d,cap,lo,hi,suffix_cap,suffix_d;std::vector<S128>beta;I low=0,high=0;U H=0,P=0,D=0,target=0,cells=0,work=0,bytes=0,bits=0,cache_cells=0;bool deficit=false,scaled=false,active=false;std::string reason;
  std::vector<std::vector<Big>>coef;std::vector<Big>table;
  const Big&at(U row,U t)const{return table[row*(target+1)+t];}
  Big&at(U row,U t){return table[row*(target+1)+t];}
  U high_for(U row,U value)const{return deficit?cap[row]-value:value;}
  const Big&coefficient(U row,U h)const{return coef[row][h-lo[row]];}
  void initialize(const std::vector<U>&quota,const std::vector<S128>&ledger,I a,I b,U count_high,bool build=true){
   d=quota;beta=ledger;low=a;high=b;H=count_high;reason="not_built";if(a<=0||b<=a||d.size()!=beta.size())throw std::runtime_error("cohort two geometry");
   U u=d.size();cap.resize(u);lo.resize(u);hi.resize(u);suffix_cap.assign(u+1,0);suffix_d.assign(u+1,0);P=0;
   for(U i=0;i<u;++i){P+=d[i];S128 v=beta[i]-S128(a)*d[i]-1;if(v<0)throw std::runtime_error("cohort current not feasible");S128 c=v/(S128(b)-a);cap[i]=c>=S128(d[i])?d[i]:U(c);}
   for(U i=u;i-->0;){suffix_cap[i]=suffix_cap[i+1]+cap[i];suffix_d[i]=suffix_d[i+1]+d[i];}if(H>P||suffix_cap[0]<H)throw std::runtime_error("cohort current profile missing");
   D=suffix_cap[0]-H;deficit=D<H;target=std::min(H,D);
   cells=sat_product(u+1,target+1,CELL_BUDGET);if(cells>CELL_BUDGET){reason="cell_guard";return;}
   work=0;cache_cells=0;U canonical_start=0,scaled_start=0,scaled_bits=1;for(U i=0;i<u;++i){lo[i]=cap[i]>D?cap[i]-D:0;hi[i]=std::min(cap[i],H);if(lo[i]>hi[i])throw std::runtime_error("cohort empty cache");U n=hi[i]-lo[i]+1;cache_cells+=n;work=sat_add(work,sat_product(target+1,n,WORK_BUDGET),WORK_BUDGET);canonical_start=sat_add(canonical_start,std::min(lo[i],d[i]-lo[i]),WORK_BUDGET);U m=std::min(D,cap[i]);scaled_start=sat_add(scaled_start,2*m,WORK_BUDGET);scaled_bits=sat_add(scaled_bits,sat_product(m,d[i]?64-__builtin_clzll(d[i]):0,std::numeric_limits<unsigned>::max()),std::numeric_limits<unsigned>::max());}

   U kbound=std::min(H,P/2),pwidth=P?64-__builtin_clzll(P):0;U coarse_bits=std::min<U>(P+1,sat_add(sat_product(kbound,pwidth,std::numeric_limits<unsigned>::max()),1,std::numeric_limits<unsigned>::max()));bool canonical_available=!(deficit&&scaled_bits<=kbound)&&kbound<=WORK_BUDGET&&estimated_bytes(1,coarse_bits+64)<=MEMORY_BUDGET;U canonical_bits=canonical_available?binomial_bound_bits(P,kbound):std::numeric_limits<unsigned>::max();scaled=deficit&&scaled_bits<canonical_bits;if(!scaled&&!canonical_available){reason="bound_guard";return;}bits=scaled?scaled_bits:canonical_bits;work=sat_add(work,scaled?scaled_start:canonical_start,WORK_BUDGET);if(canonical_available)work=sat_add(work,kbound,WORK_BUDGET);
   if(work>WORK_BUDGET){reason="work_guard";return;}
   bytes=estimated_bytes(cells,bits+64);for(U i=0;i<u;++i){U local_bits=scaled?std::min(D,cap[i])*(d[i]?64-__builtin_clzll(d[i]):0)+1:binomial_bound_bits(d[i],std::min(hi[i],d[i]/2));bytes=sat_add(bytes,estimated_bytes(hi[i]-lo[i]+1,local_bits+64),MEMORY_BUDGET);}bytes=sat_add(bytes,sat_product(u,128,MEMORY_BUDGET),MEMORY_BUDGET);if(bytes>MEMORY_BUDGET){reason="memory_guard";return;}
   if(!build){active=true;reason="two_class_qualified_count_not_built";return;}
   try{coef.resize(u);for(U i=0;i<u;++i){coef[i].resize(hi[i]-lo[i]+1);if(scaled){U m=std::min(D,cap[i]);Big c(1);for(U j=1;j<=m;++j)c*=d[i]-cap[i]+j;for(U t=0;t<=m;++t){U h=cap[i]-t;if(h>=lo[i]&&h<=hi[i])coef[i][h-lo[i]]=c;if(t<m){c=c/(d[i]-cap[i]+t+1);c*=cap[i]-t;}}}else{Big c=binomial(d[i],lo[i]);coef[i][0]=c;for(U h=lo[i];h<hi[i];++h){c*=d[i]-h;c=c/(h+1);coef[i][h+1-lo[i]]=c;}}}
    table.resize(cells);at(u,0)=Big(1);for(U i=u;i-->0;)for(U t=0;t<=target;++t){if(deficit&&suffix_cap[i]>H+t)continue;Big result;for(U h=lo[i];h<=hi[i];++h){U v=deficit?cap[i]-h:h;if(v<=t){const Big&z=at(i+1,t-v);if(z>Big(0))result+=multiply(coefficient(i,h),z);}}at(i,t)=std::move(result);}
    if(at(0,target)==Big(0))throw std::runtime_error("cohort canonical DP lost current");active=true;reason="exact_two_class";
   }catch(const std::bad_alloc&){coef.clear();table.clear();reason="allocation_guard";}
  }
  std::vector<U>draw(RNG&rng)const{if(!active)throw std::runtime_error("cohort inactive two DP draw");std::vector<U>out(d.size());U t=target;for(U i=0;i<d.size();++i){Big rank=rng.below_big(at(i,t));bool found=false;for(U h=lo[i];h<=hi[i];++h){U v=deficit?cap[i]-h:h;if(v>t)continue;Big mass=multiply(coefficient(i,h),at(i+1,t-v));if(rank<mass){out[i]=h;t-=v;found=true;break;}rank-=mass;}if(!found)throw std::runtime_error("cohort two rank failure");}if(t)throw std::runtime_error("cohort residual target");return out;}
 };
 struct FullProblem {
  std::vector<U>d,n,suffix_d;std::vector<S128>beta;std::vector<I>weights;std::vector<U>stride;U grid=0,cells=0,work=0,bytes=0,bits=0,largest=0,P=0;bool active=false;std::string reason;
  std::vector<Big>memo;std::vector<uint8_t>done;bool reachable=false;U reachable_states=0,reachable_transitions=0,frontier_payload_bytes=0;
  U key(U row,const std::vector<U>&r)const{U z=0;for(U c=0;c<r.size();++c)if(c!=largest)z+=r[c]*stride[c];return row*grid+z;}
  template<class F> void options(U row,const std::vector<U>&r,F callback)const{
   const U k=n.size();std::vector<U>x(k,0);std::function<void(U,U,S128,Big)>walk=[&](U c,U left,S128 load,Big factor){
    if(c==k){if(left==0&&load<beta[row])callback(x,factor);return;}
    U upper=std::min(left,r[c]);U after=0;for(U j=c+1;j<k;++j)after+=r[j];U lower=left>after?left-after:0;
    for(U v=lower;v<=upper;++v){S128 next=load+S128(weights[c])*v;if(next>=beta[row])break;x[c]=v;walk(c+1,left-v,next,multiply(factor,binomial(left,v)));}
   };walk(0,d[row],0,Big(1));
  }
  template<class F>void geometry_options(U row,const std::vector<U>&r,F callback)const{
   std::vector<U>x(n.size(),0);std::function<void(U,U,S128)>walk=[&](U c,U left,S128 load){
    if(c==n.size()){if(!left&&load<beta[row])callback(x);return;}
    U upper=std::min(left,r[c]),after=0;for(U j=c+1;j<n.size();++j)after+=r[j];U lower=left>after?left-after:0;
    for(U v=lower;v<=upper;++v){S128 next=load+S128(weights[c])*v;if(next>=beta[row])break;x[c]=v;walk(c+1,left-v,next);}
   };walk(0,d[row],0);
  }
  std::vector<U>decode_remaining(U row,U slot)const{std::vector<U>r(n.size(),0);U sum=0;for(U c=0;c<n.size();++c)if(c!=largest){r[c]=(slot/stride[c])%(n[c]+1);sum+=r[c];}if(sum>suffix_d[row]||suffix_d[row]-sum>n[largest])throw std::runtime_error("cohort frontier ledger decode");r[largest]=suffix_d[row]-sum;return r;}
  void build_reachable(){

   std::vector<uint32_t>frontier;frontier.reserve(cells);std::vector<U>offset(d.size()+2,0);frontier.push_back(uint32_t(key(0,n)));done[key(0,n)]=1;offset[1]=1;
   for(U row=0;row<d.size();++row){for(U pos=offset[row];pos<offset[row+1];++pos){auto r=decode_remaining(row,frontier[pos]%grid);geometry_options(row,r,[&](const std::vector<U>&x){auto next=r;for(U c=0;c<n.size();++c)next[c]-=x[c];U ix=key(row+1,next);++reachable_transitions;if(!done[ix]){done[ix]=1;frontier.push_back(uint32_t(ix));}});}offset[row+2]=frontier.size();}
   reachable_states=frontier.size();frontier_payload_bytes=frontier.capacity()*sizeof(uint32_t)+offset.size()*sizeof(U);
   for(U row=d.size()+1;row-->0;){for(U pos=offset[row];pos<offset[row+1];++pos){U ix=frontier[pos];auto r=decode_remaining(row,ix%grid);if(row==d.size()){bool empty=true;for(U v:r)empty&=!v;memo[ix]=Big(empty?1:0);continue;}Big sum;options(row,r,[&](const std::vector<U>&x,const Big&factor){auto next=r;for(U c=0;c<n.size();++c)next[c]-=x[c];U ni=key(row+1,next);if(!done[ni])throw std::runtime_error("cohort absent reachable successor");sum+=multiply(factor,memo[ni]);});memo[ix]=std::move(sum);}}
  }
  const Big&count(U row,const std::vector<U>&r){U index=key(row,r);if(done[index])return memo[index];if(reachable)throw std::runtime_error("cohort requested unreachable suffix count");done[index]=1;if(row==d.size()){bool empty=true;for(U v:r)empty&=v==0;memo[index]=Big(empty?1:0);return memo[index];}
   Big sum;options(row,r,[&](const std::vector<U>&x,const Big&factor){std::vector<U>next=r;for(U c=0;c<r.size();++c)next[c]-=x[c];sum+=multiply(factor,count(row+1,next));});memo[index]=std::move(sum);return memo[index];
  }
  void initialize(const std::vector<U>&quota,const std::vector<S128>&ledger,const std::vector<I>&values,const std::vector<U>&counts,bool build=true,bool reachable_only=false){
   reachable=reachable_only;d=quota;beta=ledger;weights=values;n=counts;reason="not_built";if(d.empty()||n.size()<3||weights.size()!=n.size()||beta.size()!=d.size())throw std::runtime_error("cohort full geometry");
   P=0;for(U v:n)P+=v;if(std::accumulate(d.begin(),d.end(),U(0))!=P)throw std::runtime_error("cohort full quota");largest=std::max_element(n.begin(),n.end())-n.begin();stride.assign(n.size(),0);grid=1;for(U c=0;c<n.size();++c)if(c!=largest){stride[c]=grid;grid=sat_product(grid,n[c]+1,CELL_BUDGET);}
   cells=sat_product(grid,d.size()+1,CELL_BUDGET);if(cells>CELL_BUDGET){reason="cell_guard";return;}
   work=0;for(U v:d){U choices=1;for(U c=0;c<n.size();++c)if(c!=largest)choices=sat_product(choices,std::min(v,n[c])+1,WORK_BUDGET);work=sat_add(work,sat_product(sat_product(grid,choices,WORK_BUDGET),n.size()+v+1,WORK_BUDGET),WORK_BUDGET);}
   if(work>WORK_BUDGET){reason="work_guard";return;}
   U logk=64-__builtin_clzll(U(n.size()-1));__uint128_t bound=__uint128_t(P)*logk+1;if(bound>std::numeric_limits<unsigned>::max()){reason="memory_guard";return;}bits=U(bound);bytes=estimated_bytes(cells,bits+64,reachable?13:1);if(reachable)bytes=sat_add(bytes,64,MEMORY_BUDGET);if(bytes>MEMORY_BUDGET){reason="memory_guard";return;}
   if(!build){active=true;reason="full_class_qualified_count_not_built";return;}
   try{memo.resize(cells);done.assign(cells,0);suffix_d.assign(d.size()+1,0);for(U i=d.size();i-->0;)suffix_d[i]=suffix_d[i+1]+d[i];if(reachable)build_reachable();else for(U row=d.size()+1;row-->0;)for(U slot=0;slot<grid;++slot){std::vector<U>r(n.size(),0);U sum=0;for(U c=0;c<n.size();++c)if(c!=largest){r[c]=(slot/stride[c])%(n[c]+1);sum+=r[c];}if(sum>suffix_d[row]||suffix_d[row]-sum>n[largest])continue;r[largest]=suffix_d[row]-sum;count(row,r);}if(count(0,n)==Big(0))throw std::runtime_error("cohort full lost current");active=true;reason="exact_all_classes";}catch(const std::bad_alloc&){memo.clear();done.clear();reason="allocation_guard";}
  }
  std::vector<std::vector<U>>draw(RNG&rng){if(!active)throw std::runtime_error("cohort inactive full DP draw");std::vector<std::vector<U>>out(d.size());auto remaining=n;for(U i=0;i<d.size();++i){Big rank=rng.below_big(count(i,remaining));bool found=false;options(i,remaining,[&](const std::vector<U>&x,const Big&factor){if(found)return;auto next=remaining;for(U c=0;c<n.size();++c)next[c]-=x[c];Big mass=multiply(factor,count(i+1,next));if(rank<mass){out[i]=x;found=true;}else rank-=mass;});if(!found)throw std::runtime_error("cohort full rank failure");for(U c=0;c<n.size();++c)remaining[c]-=out[i][c];}return out;}
 };
 CohortEligibleRootIndex*eligible_index=nullptr;
 bool local_private=false;U local_collect_calls=0,local_collect_guard_holds=0,local_collect_allocation_holds=0,local_collect_max_bytes=0,local_collect_max_scan_bound=0,local_commit_validation_calls=0,local_commit_validation_holds=0;__uint128_t local_commit_validation_scan_records=0;
 bool ledger_compiler=false,ledger_cache=true,cache_valid=false;int cache_kind=0;bool cache_build=false;
 std::unique_ptr<FullProblem>cached_full;std::unique_ptr<TwoProblem>cached_two;
 U ledger_full_attempts=0,ledger_two_attempts=0,ledger_cache_hits=0,ledger_cache_misses=0,ledger_cache_evictions=0,ledger_full_cache_hits=0,ledger_two_cache_hits=0,ledger_full_builds=0,ledger_two_builds=0,ledger_guard_cache_hits=0,ledger_allocation_uncached=0,ledger_peak_tables=0,ledger_max_table_bytes=0;
 __uint128_t ledger_reachable_states=0,ledger_reachable_transitions=0;U ledger_max_reachable_states=0,ledger_max_frontier_bytes=0;
 void clear_count_cache(){if(cached_full||cached_two)++ledger_cache_evictions;cached_full.reset();cached_two.reset();cache_valid=false;cache_kind=0;}
 FullProblem&prepare_full(const std::vector<U>&d,const std::vector<S128>&beta,const std::vector<I>&w,const std::vector<U>&n,bool build){
  ++ledger_full_attempts;
  if(ledger_cache&&cache_valid&&cache_kind==1&&cache_build==build&&cached_full->d==d&&cached_full->beta==beta&&cached_full->weights==w&&cached_full->n==n){++ledger_cache_hits;++ledger_full_cache_hits;ledger_guard_cache_hits+=!cached_full->active;return *cached_full;}
  ++ledger_cache_misses;clear_count_cache();cached_full=std::make_unique<FullProblem>();cache_kind=1;cache_build=build;cached_full->initialize(d,beta,w,n,build,true);cache_valid=cached_full->reason!="allocation_guard";
  ledger_allocation_uncached+=!cache_valid;ledger_full_builds+=build&&cached_full->active;ledger_peak_tables=std::max<U>(ledger_peak_tables,U(build&&cached_full->active));ledger_max_table_bytes=std::max(ledger_max_table_bytes,cached_full->bytes);ledger_reachable_states+=cached_full->reachable_states;ledger_reachable_transitions+=cached_full->reachable_transitions;ledger_max_reachable_states=std::max(ledger_max_reachable_states,cached_full->reachable_states);ledger_max_frontier_bytes=std::max(ledger_max_frontier_bytes,cached_full->frontier_payload_bytes);return *cached_full;
 }
 TwoProblem&prepare_two(const std::vector<U>&d,const std::vector<S128>&beta,I low,I high,U H,bool build){
  ++ledger_two_attempts;
  if(ledger_cache&&cache_valid&&cache_kind==2&&cache_build==build&&cached_two->d==d&&cached_two->beta==beta&&cached_two->low==low&&cached_two->high==high&&cached_two->H==H){++ledger_cache_hits;++ledger_two_cache_hits;ledger_guard_cache_hits+=!cached_two->active;return *cached_two;}
  ++ledger_cache_misses;clear_count_cache();cached_two=std::make_unique<TwoProblem>();cache_kind=2;cache_build=build;cached_two->initialize(d,beta,low,high,H,build);cache_valid=cached_two->reason!="allocation_guard";ledger_allocation_uncached+=!cache_valid;ledger_two_builds+=build&&cached_two->active;ledger_peak_tables=std::max<U>(ledger_peak_tables,U(build&&cached_two->active));ledger_max_table_bytes=std::max(ledger_max_table_bytes,cached_two->bytes);return *cached_two;
 }
 bool requested=false,active=false,static_fallback=false;std::string root_selector="leaf_guided",profile_update="exact";std::vector<int>leaf_nodes;std::array<std::vector<int>,2>leaf_labels,roots;
 std::array<std::vector<U>,2>actor_stamp;U epoch=0;
 U calls=0,seed_draws=0,seed_dead_holds=0,empty_roots=0,root_draws=0,row_orientation=0,column_orientation=0,windows=0,empty_pools=0,single_actor_holds=0,whole_free_calls=0,single_class_calls=0,fixed_class_calls=0;
 U full_attempts=0,full_qualified=0,full_compiled=0,full_guard_fallbacks=0,two_attempts=0,two_qualified=0,two_compiled=0,resource_holds=0,allocation_holds=0,class_first_draws=0,class_second_draws=0;
 U pool_total=0,max_pool=0,actors_total=0,max_actors=0,classes_total=0,max_classes=0,pruned_zero_rows=0,profile_changes=0,label_changes=0,root_changes=0,changes=0,moved_labels=0;
 U adjacency_pool_calls=0,leaf_pool_calls=0,max_dp_cells=0,max_dp_bits=0,max_dp_bytes=0,max_dp_work=0,deficit_calls=0;
 __uint128_t seed_scan_records=0,pool_scan_records=0,root_scan_records=0,dp_cells_total=0,dp_work_total=0;double cpu_seconds=0;
 static int vertex(const Graph&g,int o,int label){return o?g.nr+label:label;}
 static int label_of(const Edge&ed,int o){return o?ed.r:ed.c;}
 static int owner_of(const Edge&ed,int o){return o?ed.c:ed.r;}
 static I value(const Graph&g,const Scene&s,int owner,int label){return s.o?g.value(label,s.actors[owner]):g.value(s.actors[owner],label);}
 static void put(Graph&g,const Scene&s,int owner,int label,I w){if(s.o)g.set_raw(label,s.actors[owner],w);else g.set_raw(s.actors[owner],label,w);}
 void initialize(const Graph&g,bool want,const std::string&selector,const std::string&update,bool local=false){requested=want;root_selector=selector;profile_update=update;local_private=local;if(!want)return;if(local_private){if(selector!="uniform_union")throw std::runtime_error("local cohort requires uniform_union");for(int j=0;j<g.nc;++j)if(g.target_degree[g.nr+j]>=2)roots[0].push_back(j);for(int i=0;i<g.nr;++i)if(g.target_degree[i]>=2)roots[1].push_back(i);active=true;static_fallback=false;return;}for(int v=0;v<g.nr+g.nc;++v)if(g.target_degree[v]==1){leaf_nodes.push_back(v);leaf_labels[v<g.nr?1:0].push_back(v<g.nr?v:v-g.nr);}for(int j=0;j<g.nc;++j)if(g.target_degree[g.nr+j]>=2)roots[0].push_back(j);for(int i=0;i<g.nr;++i)if(g.target_degree[i]>=2)roots[1].push_back(i);static_fallback=leaf_nodes.empty();active=!static_fallback;if(active){actor_stamp[0].assign(g.nr,0);actor_stamp[1].assign(g.nc,0);}}
 Scene collect_local(const Graph&g,int o,int root){
  ++local_collect_calls;Scene s;s.o=o;s.root=root;s.local_private=true;
  try{auto witness=CohortLocalPrivateScene::collect(g,o,root);local_collect_max_bytes=std::max(local_collect_max_bytes,witness.estimated_bytes);local_collect_max_scan_bound=std::max(local_collect_max_scan_bound,witness.scan_bound);pool_scan_records+=witness.scanned;root_scan_records+=g.adj[o?root:g.nr+root].size();if(!witness.qualified){++local_collect_guard_holds;s.collection_hold=true;return s;}
   s.actors=std::move(witness.actors);s.full_actors=s.actors;s.records.reserve(witness.records.size());s.full_pool_signature.reserve(witness.records.size());for(const auto&r:witness.records){auto it=std::lower_bound(s.actors.begin(),s.actors.end(),r.actor);if(it==s.actors.end()||*it!=r.actor)throw std::runtime_error("local cohort witness owner");s.records.push_back({r.label,int(it-s.actors.begin()),r.weight});s.full_pool_signature.push_back({r.label,r.weight});}return s;
  }catch(const std::bad_alloc&){++local_collect_allocation_holds;s.actors.clear();s.records.clear();s.full_actors.clear();s.full_pool_signature.clear();s.collection_hold=true;return s;}
 }
 bool validate_local_commit(const Graph&g,const Scene&s){
  ++local_commit_validation_calls;try{auto witness=CohortLocalPrivateScene::collect(g,s.o,s.root);local_commit_validation_scan_records+=witness.scanned;if(!witness.qualified){++local_commit_validation_holds;return false;}if(witness.actors!=s.full_actors||witness.records.size()!=s.full_pool_signature.size())throw std::runtime_error("local cohort stale FULL cohort/pool");
   for(U j=0;j<witness.records.size();++j)if(s.full_pool_signature[j]!=std::make_pair(witness.records[j].label,witness.records[j].weight))throw std::runtime_error("local cohort stale carried label weight");
   int previous=-1;for(const auto&r:s.records){if(r.owner<0||U(r.owner)>=s.actors.size()||r.label<=previous)throw std::runtime_error("local cohort repeated/invalid record");previous=r.label;auto it=std::lower_bound(witness.records.begin(),witness.records.end(),r.label,[](const CohortLocalPrivateScene::Private&a,int label){return a.label<label;});if(it==witness.records.end()||it->label!=r.label||it->actor!=s.actors[r.owner]||it->weight!=r.weight)throw std::runtime_error("local cohort stale singleton owner");}return true;
  }catch(const std::bad_alloc&){++local_commit_validation_holds;return false;}
 }
 Scene collect(const Graph&g,int o,int root){if(local_private)return collect_local(g,o,root);Scene s;s.o=o;s.root=root;int rv=o?root:g.nr+root;for(int id:g.adj[rv]){s.actors.push_back(owner_of(g.edges[id],o));++root_scan_records;}std::sort(s.actors.begin(),s.actors.end());if(++epoch==0){for(auto&v:actor_stamp)std::fill(v.begin(),v.end(),0);epoch=1;}U adjacent=0;for(int actor:s.actors){actor_stamp[o][actor]=epoch;adjacent+=g.adj[vertex(g,o,actor)].size();}
  auto add=[&](const Edge&ed){int actor=owner_of(ed,o),label=label_of(ed,o);auto where=std::lower_bound(s.actors.begin(),s.actors.end(),actor);if(where==s.actors.end()||*where!=actor)throw std::runtime_error("cohort pool owner outside root");s.records.push_back({label,int(where-s.actors.begin()),ed.w});};
  if(adjacent<=leaf_labels[o].size()){++adjacency_pool_calls;for(int actor:s.actors)for(int id:g.adj[vertex(g,o,actor)]){++pool_scan_records;const Edge&ed=g.edges[id];int label=label_of(ed,o);if(g.target_degree[o?label:g.nr+label]==1)add(ed);}}
  else{++leaf_pool_calls;for(int label:leaf_labels[o]){++pool_scan_records;int lv=o?label:g.nr+label;if(g.adj[lv].size()!=1)throw std::runtime_error("cohort global leaf support changed");const Edge&ed=g.edges[g.adj[lv][0]];if(actor_stamp[o][owner_of(ed,o)]==epoch)add(ed);}}
  std::sort(s.records.begin(),s.records.end(),[](const Record&a,const Record&b){return a.label<b.label;});return s;
 }
 template<class F>static void shuffle(std::vector<int>&labels,F below){for(U n=labels.size();n>1;--n)std::swap(labels[n-1],labels[below(n)]);}
 static std::vector<int>partition(const Scene&s,const std::vector<std::vector<U>>&counts,const std::vector<I>&weights,RNG&rng){std::vector<int>out(s.records.size(),-1);std::map<I,std::vector<int>>groups;for(U j=0;j<s.records.size();++j)groups[s.records[j].weight].push_back(int(j));for(U c=0;c<weights.size();++c){auto&indices=groups.at(weights[c]);shuffle(indices,[&](U n){return rng.below(n);});U next=0;for(U i=0;i<counts.size();++i)for(U j=0;j<counts[i][c];++j){if(next>=indices.size())throw std::runtime_error("cohort class quota overflow");out[indices[next++]]=int(i);}if(next!=indices.size())throw std::runtime_error("cohort incomplete class quota");}return out;}
 static std::vector<int>fixed_partition(const Scene&s,RNG&rng){std::vector<int>out(s.records.size(),-1);std::map<I,std::vector<int>>groups;for(U j=0;j<s.records.size();++j)groups[s.records[j].weight].push_back(int(j));for(auto&[weight,indices]:groups){std::vector<int>owners;owners.reserve(indices.size());for(int j:indices)owners.push_back(s.records[j].owner);std::sort(owners.begin(),owners.end());shuffle(indices,[&](U n){return rng.below(n);});for(U j=0;j<indices.size();++j)out[indices[j]]=owners[j];}return out;}
 bool commit(Engine&e,Graph&g,const Scene&s,const std::vector<int>&owners,const std::vector<S128>&beta,const std::vector<U>&quota){if(s.local_private&&!validate_local_commit(g,s)){++resource_holds;return false;}if(owners.size()!=s.records.size()||quota.size()!=s.actors.size()||beta.size()!=quota.size())throw std::runtime_error("cohort commit dimensions");if(s.local_private){std::vector<U>oldquota(quota.size(),0);std::vector<S128>oldbeta(quota.size());for(U i=0;i<quota.size();++i)oldbeta[i]=value(g,s,int(i),s.root);for(const auto&r:s.records){++oldquota[r.owner];oldbeta[r.owner]+=r.weight;}if(oldquota!=quota||oldbeta!=beta)throw std::runtime_error("local cohort stale quota/beta ledger");}std::vector<U>count(quota.size(),0);auto root=beta;bool changed=false;std::vector<std::map<I,U>>oldcount(quota.size()),newcount(quota.size());
  for(U j=0;j<owners.size();++j){int owner=owners[j];const auto&r=s.records[j];if(owner<0||U(owner)>=quota.size()||value(g,s,r.owner,r.label)!=r.weight||(!s.local_private&&g.target_degree[s.o?r.label:g.nr+r.label]!=1))throw std::runtime_error("cohort stale leaf commit");++count[owner];root[owner]-=r.weight;++oldcount[r.owner][r.weight];++newcount[owner][r.weight];}
  for(U i=0;i<quota.size();++i)if(count[i]!=quota[i]||root[i]<=0||root[i]>std::numeric_limits<I>::max())throw std::runtime_error("cohort invalid root/quota");if(oldcount!=newcount)++profile_changes;
  U moves=0;for(U j=0;j<owners.size();++j)if(owners[j]!=s.records[j].owner){const auto&r=s.records[j];put(g,s,r.owner,r.label,0);put(g,s,owners[j],r.label,r.weight);++moves;changed=true;}moved_labels+=moves;if(moves)++label_changes;
  bool roots_changed=false;for(U i=0;i<root.size();++i)if(value(g,s,int(i),s.root)!=I(root[i])){put(g,s,int(i),s.root,I(root[i]));roots_changed=true;changed=true;}root_changes+=roots_changed;if(changed){++changes;++e.stat.changed_outer;}return changed;
 }
 void observe_problem(U cells,U bits,U bytes,U work){max_dp_cells=std::max(max_dp_cells,cells);max_dp_bits=std::max(max_dp_bits,bits);max_dp_bytes=std::max(max_dp_bytes,bytes);max_dp_work=std::max(max_dp_work,work);dp_cells_total+=cells;dp_work_total+=work;}
 static bool whole_free_certificate(const std::vector<U>&d,const std::vector<S128>&beta,const std::map<I,U>&freq){std::vector<U>prefix_count;std::vector<S128>prefix_weight;std::vector<I>descending_weight;U count_sum=0;S128 weight_sum=0;for(auto it=freq.rbegin();it!=freq.rend();++it){count_sum+=it->second;weight_sum+=S128(it->second)*it->first;prefix_count.push_back(count_sum);prefix_weight.push_back(weight_sum);descending_weight.push_back(it->first);}bool free=true;for(U i=0;i<d.size();++i){U j=std::lower_bound(prefix_count.begin(),prefix_count.end(),d[i])-prefix_count.begin();if(j==prefix_count.size())throw std::runtime_error("cohort whole free quota");U before=j?prefix_count[j-1]:0;S128 maximum=(j?prefix_weight[j-1]:0)+S128(d[i]-before)*descending_weight[j];if(maximum>=beta[i]){free=false;break;}}return free;}
 bool execute(Engine&e,Graph&g,Scene s){++windows;actors_total+=s.actors.size();max_actors=std::max<U>(max_actors,s.actors.size());pool_total+=s.records.size();max_pool=std::max<U>(max_pool,s.records.size());if(s.records.empty()){++empty_pools;return false;}
  std::map<I,U>freq;std::vector<U>d(s.actors.size(),0);std::vector<S128>beta(s.actors.size());for(U i=0;i<s.actors.size();++i)beta[i]=value(g,s,int(i),s.root);for(const auto&r:s.records){++d[r.owner];beta[r.owner]+=r.weight;}
   
  Scene compact=s;compact.actors.clear();std::vector<int>old_to_new(d.size(),-1);std::vector<U>cd;std::vector<S128>cb;for(U i=0;i<d.size();++i)if(d[i]){old_to_new[i]=int(cd.size());compact.actors.push_back(s.actors[i]);cd.push_back(d[i]);cb.push_back(beta[i]);}else ++pruned_zero_rows;for(auto&r:compact.records)r.owner=old_to_new[r.owner];s=std::move(compact);d=std::move(cd);beta=std::move(cb);if(d.size()<=1){++single_actor_holds;return false;}for(const auto&r:s.records)++freq[r.weight];classes_total+=freq.size();max_classes=std::max<U>(max_classes,freq.size());
  std::vector<I>weights;std::vector<U>sizes;for(auto q:freq){weights.push_back(q.first);sizes.push_back(q.second);}
  bool free=whole_free_certificate(d,beta,freq);
  if(free){++whole_free_calls;if(weights.size()==1)++single_class_calls;if(profile_update=="fixed_class"){++fixed_class_calls;return commit(e,g,s,fixed_partition(s,e.rng),beta,d);}std::vector<int>labels(s.records.size());std::iota(labels.begin(),labels.end(),0);shuffle(labels,[&](U n){return e.rng.below(n);});std::vector<int>owners(labels.size());U next=0;for(U i=0;i<d.size();++i)for(U j=0;j<d[i];++j)owners[labels[next++]]=int(i);return commit(e,g,s,owners,beta,d);}
  if(weights.size()>2){++full_attempts;FullProblem local_full;FullProblem&full=ledger_compiler?prepare_full(d,beta,weights,sizes,profile_update=="exact"):local_full;if(!ledger_compiler)full.initialize(d,beta,weights,sizes,profile_update=="exact");observe_problem(full.cells,full.bits,full.bytes,full.work);if(full.active){++full_qualified;if(profile_update=="fixed_class"){++fixed_class_calls;return commit(e,g,s,fixed_partition(s,e.rng),beta,d);}++full_compiled;auto draw=full.draw(e.rng);return commit(e,g,s,partition(s,draw,weights,e.rng),beta,d);}++full_guard_fallbacks;}

  I low,high;if(weights.size()==2){low=weights[0];high=weights[1];}else{++class_first_draws;I first=s.records[e.rng.below(s.records.size())].weight;U remaining=s.records.size()-freq[first];U rank=e.rng.below(remaining);++class_second_draws;I second=0;for(const auto&r:s.records)if(r.weight!=first){if(!rank){second=r.weight;break;}--rank;}if(!second)throw std::runtime_error("cohort fresh second class missing");low=std::min(first,second);high=std::max(first,second);}
  Scene pair=s;pair.records.clear();std::vector<U>pd(s.actors.size(),0);std::vector<S128>pb(s.actors.size());for(U i=0;i<pb.size();++i)pb[i]=value(g,s,int(i),s.root);U H=0;for(const auto&r:s.records)if(r.weight==low||r.weight==high){pair.records.push_back(r);++pd[r.owner];pb[r.owner]+=r.weight;H+=r.weight==high;}
   
  std::vector<int>map(pd.size(),-1);Scene pp=pair;pp.actors.clear();std::vector<U>qd;std::vector<S128>qb;for(U i=0;i<pd.size();++i)if(pd[i]){map[i]=int(qd.size());pp.actors.push_back(pair.actors[i]);qd.push_back(pd[i]);qb.push_back(pb[i]);}else ++pruned_zero_rows;for(auto&r:pp.records)r.owner=map[r.owner];pair=std::move(pp);
  ++two_attempts;TwoProblem local_two;TwoProblem&two=ledger_compiler?prepare_two(qd,qb,low,high,H,profile_update=="exact"):local_two;if(!ledger_compiler)two.initialize(qd,qb,low,high,H,profile_update=="exact");observe_problem(two.cells,two.bits,two.bytes,two.work);if(!two.active){++resource_holds;if(two.reason=="allocation_guard")++allocation_holds;return false;}++two_qualified;deficit_calls+=two.deficit;if(profile_update=="fixed_class"){++fixed_class_calls;return commit(e,g,pair,fixed_partition(pair,e.rng),qb,qd);}++two_compiled;auto h=two.draw(e.rng);std::vector<std::vector<U>>out(h.size(),std::vector<U>(2));for(U i=0;i<h.size();++i){out[i][0]=qd[i]-h[i];out[i][1]=h[i];}return commit(e,g,pair,partition(pair,out,{low,high},e.rng),qb,qd);
 }
 bool step(Engine&e,Graph&g){if(!active)throw std::runtime_error("cohort inactive step");++calls;++e.stat.work;if(g.D)throw std::runtime_error("cohort needs exact margins");int o=0,root=-1;
  if(root_selector=="eligible_root"){if(!eligible_index)throw std::runtime_error("cohort missing eligible index");const int v=eligible_index->draw(e.rng);if(v<0){++empty_roots;return false;}o=v<g.nr?1:0;root=v<g.nr?v:v-g.nr;}
  else if(root_selector=="uniform_union"){U n=roots[0].size()+roots[1].size();if(!n){++empty_roots;return false;}U rank=e.rng.below(n);o=rank<roots[0].size()?0:1;root=roots[o][o?rank-roots[0].size():rank];}
  else if(root_selector=="uniform_root"){o=int(e.rng.below(2));if(roots[o].empty()){++empty_roots;return false;}root=roots[o][e.rng.below(roots[o].size())];}
  else{++seed_draws;int seed=leaf_nodes[e.rng.below(leaf_nodes.size())];if(g.adj[seed].size()!=1)throw std::runtime_error("cohort seed leaf changed");const Edge ed=g.edges[g.adj[seed][0]];o=seed<g.nr?1:0;int owner=owner_of(ed,o);std::vector<int>eligible;for(int id:g.adj[vertex(g,o,owner)]){++seed_scan_records;int label=label_of(g.edges[id],o);if(g.target_degree[o?label:g.nr+label]>=2)eligible.push_back(label);}if(eligible.empty()){++seed_dead_holds;return false;}root=eligible[e.rng.below(eligible.size())];}
  ++root_draws;if(o)++column_orientation;else ++row_orientation;Scene scene=collect(g,o,root);if(scene.collection_hold){++resource_holds;return false;}return execute(e,g,std::move(scene));
 }
};
