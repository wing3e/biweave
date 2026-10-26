#pragma once
#include <climits>
 
struct WholeClassTripleHeatbath {
 CapacityGuidedSupportCycle*core=nullptr;bool core_start=false;U core_selector_calls=0,core_selector_fallbacks=0;bool requested=false,active=false;Fenwick root_tree;U root_total=0;
 U calls=0,changes=0,empty_holds=0,root_holds=0,no_two_class_holds=0,windows=0,profiles=0,max_profiles=0,max_slack=0,max_selected=0;
 U profile_changes=0,root_changes=0,moved_labels=0,index_checks=0,scanned_records=0,draws=0;
 bool public_root_requested=false;std::vector<int> public_roots;
 bool public_listener_cache_requested=false,public_all_rows_eligible=false;std::vector<int>public_static_listeners;
 U public_listener_direct_calls=0,public_listener_static_calls=0,public_listener_dynamic_calls=0,public_listener_scanned_edges=0,public_listener_certificate_checks=0;
 U public_selector_calls=0,public_empty_pool_holds=0,public_insufficient_listeners_holds=0;
 U public_root_draws=0,public_listener_draws=0,public_selected_triples=0,public_pool_checks=0;
 std::vector<I> static_excess;
 static U checked(S128 x){if(x<0||__uint128_t(x)>std::numeric_limits<U>::max())throw std::runtime_error("WCT unsigned range");return U(x);}
 void initialize(Graph&g,bool want,bool public_want=false,bool cache_want=true){requested=want;public_root_requested=public_want;public_listener_cache_requested=public_want&&cache_want;if(!want)return;active=true;
  if(public_root_requested){for(int c=0;c<g.nc;++c)if(g.target_degree[g.nr+c]>=3)public_roots.push_back(c);if(public_listener_cache_requested){public_all_rows_eligible=true;for(int r=0;r<g.nr;++r){const bool eligible=g.target_degree[r]>=2;public_all_rows_eligible&=eligible;if(eligible)public_static_listeners.push_back(r);}}return;}
  root_tree=Fenwick(g.nr);static_excess.assign(g.nr,0);S128 total=0;
  for(int r=0;r<g.nr;++r)if(g.target_degree[r]>=2){S128 x=S128(g.target_strength[r])-g.target_degree[r];if(x<0||x>std::numeric_limits<I>::max())throw std::runtime_error("WCT root excess");static_excess[r]=I(x);if(x)root_tree.add(r,I(x));total+=x;}root_total=checked(total);}
 void check(Graph&g){if(!active)return;++index_checks;
  if(public_root_requested){++public_pool_checks;size_t next=0;for(int c=0;c<g.nc;++c)if(g.target_degree[g.nr+c]>=3){if(next>=public_roots.size()||public_roots[next++]!=c)throw std::runtime_error("WCT public static root pool audit");}if(next!=public_roots.size())throw std::runtime_error("WCT public root cardinality");if(public_listener_cache_requested){++public_listener_certificate_checks;bool all=true;size_t pos=0;for(int r=0;r<g.nr;++r){const bool eligible=g.target_degree[r]>=2;all&=eligible;if(eligible){if(pos>=public_static_listeners.size()||public_static_listeners[pos++]!=r)throw std::runtime_error("WCT public static listeners audit");}}if(pos!=public_static_listeners.size()||all!=public_all_rows_eligible)throw std::runtime_error("WCT public listener certificate audit");}return;}
  S128 total=0;
  for(int r=0;r<g.nr;++r){S128 sum=0;for(int id:g.adj[r])sum+=S128(g.edges[id].w)-1;
   const I expected=g.target_degree[r]>=2?g.target_strength[r]-g.target_degree[r]:0;
   if(g.degree[r]!=g.target_degree[r]||static_excess[r]!=expected||(expected&&sum!=expected))throw std::runtime_error("WCT static selector audit");total+=expected;}
  std::vector<U>prefix(g.nr+1,0);for(int r=0;r<g.nr;++r)prefix[r+1]=prefix[r]+U(static_excess[r]);for(U i=1;i<root_tree.tree.size();++i)if(root_tree.tree[i]!=prefix[i]-prefix[i-(i&(~i+1))])throw std::runtime_error("WCT tree point audit");
  if(checked(total)!=root_total||root_tree.total()!=root_total)throw std::runtime_error("WCT static tree audit");}
 struct Label{int col=0,owner=0;I weight=0;};
 static mpz_class binomial(U n,U k){if(k>n||n>ULONG_MAX)throw std::runtime_error("WCT binomial range");mpz_class x;mpz_bin_uiui(x.get_mpz_t(),static_cast<unsigned long>(n),static_cast<unsigned long>(k));return x;}
 bool step(Engine&e,Graph&g){if(!requested||!active)throw std::runtime_error("WCT unrequested step");++calls;++e.stat.work;
  const bool use_core=!public_root_requested&&core_start&&core&&core->active;if(core_start&&!use_core)++core_selector_fallbacks;
  int first=-1,P=-1;U selected_core_total=0;std::array<int,3>nodes{};
  if(public_root_requested){
   ++public_selector_calls;
   if(public_roots.empty()){++public_empty_pool_holds;++empty_holds;return false;}
   P=public_roots[size_t(e.rng.below(U(public_roots.size())))];++public_root_draws;
   if(g.D||g.degree[g.nr+P]!=g.target_degree[g.nr+P]||g.adj[g.nr+P].size()!=size_t(g.target_degree[g.nr+P]))throw std::runtime_error("WCT public listener selector requires closed column degree ledger");
   const bool direct=public_listener_cache_requested&&public_all_rows_eligible;
   const bool static_list=public_listener_cache_requested&&!direct&&g.target_degree[g.nr+P]==g.nr;
   if(direct||static_list){
    direct?++public_listener_direct_calls:++public_listener_static_calls;
    const U count=direct?U(g.adj[g.nr+P].size()):U(public_static_listeners.size());
    if(count<3){++public_insufficient_listeners_holds;++root_holds;return false;}
    std::array<U,3>position{};int used=0;
    for(U j=count-3;j<count;++j){U pick=e.rng.below(j+1);for(int i=0;i<used;++i)if(position[i]==pick){pick=j;break;}position[used++]=pick;++public_listener_draws;}
    for(int i=0;i<3;++i)nodes[i]=direct?g.edges[g.adj[g.nr+P][size_t(position[i])]].r:public_static_listeners[size_t(position[i])];
   }else{
    ++public_listener_dynamic_calls;
    std::vector<int>other;for(int id:g.adj[g.nr+P]){++scanned_records;++public_listener_scanned_edges;const int r=g.edges[id].r;if(g.target_degree[r]>=2)other.push_back(r);}
    if(other.size()<3){++public_insufficient_listeners_holds;++root_holds;return false;}
    for(int i=0;i<3;++i){const U j=e.rng.below(U(other.size()));nodes[i]=other[size_t(j)];other[size_t(j)]=other.back();other.pop_back();++public_listener_draws;}
   }
   ++public_selected_triples;
  }else{
  if(use_core){core->synchronize(g);++core_selector_calls;selected_core_total=core->row_capacity_total;if(!selected_core_total){++empty_holds;return false;}
   first=core->root_tree.select(e.rng.below(selected_core_total));U rank=e.rng.below(checked(core->capacity[first]));
   for(U id:core->support.adj[first]){++scanned_records;const auto&x=core->support.edges[id];const U z=U(g.value(x.r,x.c)-1);if(rank<z){P=x.c;break;}rank-=z;}}
  else{if(!root_total){++empty_holds;return false;}first=root_tree.select(e.rng.below(root_total));U rank=e.rng.below(U(static_excess[first]));
   for(int id:g.adj[first]){++scanned_records;const auto&x=g.edges[id];const U z=U(x.w-1);if(rank<z){P=x.c;break;}rank-=z;}}
  if(P<0)throw std::runtime_error("WCT weighted edge selection");
  std::vector<int>other;for(int id:g.adj[g.nr+P]){++scanned_records;const int r=g.edges[id].r;if(r!=first&&g.target_degree[r]>=2)other.push_back(r);}if(other.size()<2){++root_holds;return false;}
  const U j=e.rng.below(other.size());const int second=other[j];other[j]=other.back();other.pop_back();const int third=other[e.rng.below(other.size())];nodes={first,second,third};
  }
  std::sort(nodes.begin(),nodes.end());
  std::vector<Label>all;std::map<I,U>frequency;
  for(int i=0;i<3;++i)for(int id:g.adj[nodes[i]]){++scanned_records;const auto&x=g.edges[id];if(x.c==P)continue;bool private_=true;for(int j2=0;j2<3;++j2)if(j2!=i&&g.value(nodes[j2],x.c)>0){private_=false;break;}if(private_){all.push_back({x.c,i,x.w});++frequency[x.w];}}
  if(frequency.size()<2){++no_two_class_holds;return false;}
  std::vector<std::pair<I,U>>classes(frequency.begin(),frequency.end());std::sort(classes.begin(),classes.end(),[](const auto&x,const auto&y){return x.second!=y.second?x.second>y.second:x.first<y.first;});I a=classes[0].first,b=classes[1].first;if(a>b)std::swap(a,b);const S128 delta=S128(b)-a;
  std::array<U,3>k={0,0,0},old_t={0,0,0},lo={0,0,0},hi={0,0,0};std::array<S128,3>R;std::array<I,3>old_c;for(int i=0;i<3;++i){old_c[i]=g.value(nodes[i],P);if(old_c[i]<1)throw std::runtime_error("WCT common root");R[i]=old_c[i];}
  std::vector<Label>low,high;for(const auto&x:all)if(x.weight==a||x.weight==b){++k[x.owner];R[x.owner]+=x.weight;if(x.weight==b){++old_t[x.owner];high.push_back(x);}else low.push_back(x);}const U Nb=high.size(),K=low.size()+high.size();
  for(int i=0;i<3;++i){const S128 cap=(R[i]-S128(a)*k[i]-1)/delta;if(cap<0)throw std::runtime_error("WCT current not feasible");hi[i]=std::min({k[i],Nb,checked(cap)});lo[i]=Nb>K-k[i]?Nb-(K-k[i]):0;}
  for(int i=0;i<3;++i){const U rest=hi[(i+1)%3]+hi[(i+2)%3];lo[i]=std::max(lo[i],Nb>rest?Nb-rest:U(0));if(lo[i]>old_t[i]||old_t[i]>hi[i])throw std::runtime_error("WCT original profile missing");}
  const U M=hi[0]+hi[1]+hi[2]-Nb;std::array<U,3>width;std::array<std::vector<mpz_class>,3>coeff;
  for(int i=0;i<3;++i){width[i]=std::min(M,hi[i]-lo[i]);coeff[i].resize(width[i]+1);coeff[i][0]=binomial(k[i],hi[i]);for(U s=1;s<=width[i];++s){const U t=hi[i]-(s-1);coeff[i][s]=coeff[i][s-1]*static_cast<unsigned long>(t);mpz_divexact_ui(coeff[i][s].get_mpz_t(),coeff[i][s].get_mpz_t(),static_cast<unsigned long>(k[i]-t+1));}}
  mpz_class total=0;U np=0;auto visit=[&](auto fn){for(U s0=0;s0<=width[0];++s0){const U rem=M-s0;const U min1=rem>width[2]?rem-width[2]:0,max1=std::min(rem,width[1]);if(min1>max1)continue;for(U s1=min1;s1<=max1;++s1){const U s2=rem-s1;mpz_class mass=coeff[0][s0]*coeff[1][s1]*coeff[2][s2];fn(s0,s1,s2,mass);}}};
  visit([&](U,U,U,const mpz_class&mass){total+=mass;++np;});if(total<=0||!np)throw std::runtime_error("WCT zero full count");++windows;profiles+=np;max_profiles=std::max(max_profiles,np);max_slack=std::max(max_slack,M);max_selected=std::max(max_selected,K);
  mpz_class pick=zbig(e.rng.below_big(bigz(total)));std::array<U,3>t=old_t;bool found=false;visit([&](U s0,U s1,U s2,const mpz_class&mass){if(found)return;if(pick<mass){t={hi[0]-s0,hi[1]-s1,hi[2]-s2};found=true;}else pick-=mass;});if(!found)throw std::runtime_error("WCT rank missing");++draws;profile_changes+=t!=old_t;
  auto shuffle=[&](std::vector<Label>&labels){for(U n=labels.size();n>1;--n)std::swap(labels[n-1],labels[e.rng.below(n)]);};shuffle(low);shuffle(high);
  std::vector<std::pair<Label,int>>assignment;assignment.reserve(K);U il=0,ih=0;std::array<I,3>now;
  for(int i=0;i<3;++i){const S128 c=R[i]-S128(a)*k[i]-delta*t[i];if(c<1||c>std::numeric_limits<I>::max())throw std::runtime_error("WCT public weight range");now[i]=I(c);for(U z=0;z<k[i]-t[i];++z)assignment.push_back({low.at(il++),i});for(U z=0;z<t[i];++z)assignment.push_back({high.at(ih++),i});}if(il!=low.size()||ih!=high.size())throw std::runtime_error("WCT label quota");
  bool changed=now!=old_c;for(const auto&x:assignment)if(x.first.owner!=x.second){changed=true;++moved_labels;g.set_raw(nodes[x.first.owner],x.first.col,0);}for(const auto&x:assignment)if(x.first.owner!=x.second)g.set_raw(nodes[x.second],x.first.col,x.first.weight);for(int i=0;i<3;++i)if(now[i]!=old_c[i]){++root_changes;g.set_raw(nodes[i],P,now[i]);}if(g.D)throw std::runtime_error("WCT nonclosed commit");changes+=changed;if(use_core){core->synchronize(g);if(core->row_capacity_total!=selected_core_total)throw std::runtime_error("WCT core total invariance");}return changed;
 }
 void metadata(std::ostream&f)const{f<<"\"WCT_public_root_requested\":"<<(public_root_requested?"true":"false")
   <<",\"WCT_public_root_pool_size\":"<<public_roots.size()<<",\"WCT_public_selector_calls\":"<<public_selector_calls
   <<",\"WCT_public_empty_pool_holds\":"<<public_empty_pool_holds<<",\"WCT_public_insufficient_listeners_holds\":"<<public_insufficient_listeners_holds
   <<",\"WCT_public_root_draws\":"<<public_root_draws<<",\"WCT_public_listener_draws\":"<<public_listener_draws
   <<",\"WCT_public_selected_triples\":"<<public_selected_triples<<",\"WCT_public_pool_checks\":"<<public_pool_checks
   <<",\"WCT_public_listener_cache_requested\":"<<(public_listener_cache_requested?"true":"false")
   <<",\"WCT_public_all_rows_eligible\":"<<(public_all_rows_eligible?"true":"false")
   <<",\"WCT_public_static_listener_count\":"<<public_static_listeners.size()
   <<",\"WCT_public_listener_direct_calls\":"<<public_listener_direct_calls
   <<",\"WCT_public_listener_static_calls\":"<<public_listener_static_calls
   <<",\"WCT_public_listener_dynamic_calls\":"<<public_listener_dynamic_calls
   <<",\"WCT_public_listener_scanned_edges\":"<<public_listener_scanned_edges
   <<",\"WCT_public_listener_certificate_checks\":"<<public_listener_certificate_checks<<",";f<<"\"WCT_core_start_requested\":"<<(core_start?"true":"false")<<",\"WCT_core_selector_calls\":"<<core_selector_calls<<",\"WCT_core_selector_fallbacks\":"<<core_selector_fallbacks<<",";f<<"\"WCT_requested\":"<<(requested?"true":"false")<<",\"WCT_active\":"<<(active?"true":"false")<<",\"WCT_calls\":"<<calls<<",\"WCT_changes\":"<<changes<<",\"WCT_windows\":"<<windows<<",\"WCT_profiles\":"<<profiles<<",\"WCT_max_profiles\":"<<max_profiles<<",\"WCT_max_slack\":"<<max_slack<<",\"WCT_max_selected\":"<<max_selected<<",\"WCT_profile_changes\":"<<profile_changes<<",\"WCT_root_changes\":"<<root_changes<<",\"WCT_moved_labels\":"<<moved_labels<<",\"WCT_index_checks\":"<<index_checks<<",\"WCT_scanned_records\":"<<scanned_records<<",\"WCT_draws\":"<<draws<<",\"WCT_empty_holds\":"<<empty_holds<<",\"WCT_root_holds\":"<<root_holds<<",\"WCT_no_two_class_holds\":"<<no_two_class_holds<<",";}
};
