#pragma once

struct TwoWeightComplement {
 using Scene=BalancedPrivateHeatbath::Scene;
 MetropolizedProfileRefresh metropolis;
 GeometricProfileRefresh geometric;
 RootOrbitProfileRefresh root_orbit;
 PairConditionalProfileGibbs pair_conditional;
 static constexpr U STARTUP_WORK_BUDGET=1000000,MEMORY_BUDGET_BYTES=64ULL*1024*1024,SLACK_CAP=6;
 struct Record {int col=0,owner=0;I weight=0;};
 struct Problem {
  Scene scene;I low=0,high=0,delta=0;std::array<U,3>h{},c{},initial{},cache_lo{},cache_hi{};std::array<I,3>beta{};
  std::vector<int>high_columns,low_columns,high_current,low_current;
  std::array<std::vector<mpz_class>,3>binomial;std::vector<std::array<U,3>>profiles;std::vector<mpz_class>mass;mpz_class total=0;
  U NH=0,NL=0,D=0,slack=0,startup_work_score=0,estimated_bytes=0;bool active=false,deficit=false,scaled_relative_mass=false;std::string guard="unbuilt";
 };
 struct Draw {std::array<U,3>a{};std::array<I,3>roots{};std::vector<int>high_owners,low_owners;};
 struct Events {bool changed=false;U moved_labels=0,root_changes=0;};
 U calls=0,empty_primary_class=0,no_other_class=0,other_class_choices=0,complement_records_total=0,other_classes_total=0,slack_eligible=0,slack_failures=0,startup_guard_failures=0,memory_guard_failures=0,old_single_class_fallbacks=0;
 U compiled_windows=0,profiles_total=0,max_profiles=0,max_slack=0,max_examined_slack=0,max_high_objects=0,max_startup_work_score=0,max_estimated_bytes=0,max_count_bits=0;
 U scaled_count_attempts=0,scaled_compiled_windows=0,scaled_startup_multiplications=0,scaled_cache_steps=0,scaled_max_relative_mass_bits=0,scaled_max_payload_estimate=0;
 U profile_draws=0,profile_changes=0,label_changes=0,root_changes=0,changes=0,moved_labels=0,root_writes=0;
 double compile_cpu_seconds=0,draw_cpu_seconds=0,commit_cpu_seconds=0,fallback_draw_cpu_seconds=0;
 Problem compile(const Graph&g,const Scene&s,I w0,I w1,const std::vector<Record>&records,bool build_counts=true){return compile_mapped(g,s,w0,w1,records,[](const Record&r){return r;},build_counts);}
 template<class Range,class Convert>Problem compile_mapped(const Graph&g,const Scene&s,I w0,I w1,const Range&records,Convert&&convert,bool build_counts=true){
  if(w0<=0||w1<=0||w0==w1)throw std::runtime_error("two-weight classes must differ");Problem p;p.scene=s;p.low=std::min(w0,w1);p.high=std::max(w0,w1);p.delta=p.high-p.low;std::array<S128,3>sum{};
  for(int i=0;i<3;++i){I root=BalancedPrivateHeatbath::value(g,s,i,s.root);if(root<=0)throw std::runtime_error("two-weight root absent");sum[i]=root;}
  for(const auto&stored:records){const Record r=convert(stored);if(r.weight==w0||r.weight==w1){if(r.owner<0||r.owner>2||r.col==s.root||r.weight<=0)throw std::runtime_error("two-weight record invalid");if(BalancedPrivateHeatbath::value(g,s,r.owner,r.col)!=r.weight)throw std::runtime_error("two-weight complement record stale");++p.h[r.owner];sum[r.owner]+=r.weight;
   if(r.weight==p.high){p.high_columns.push_back(r.col);p.high_current.push_back(r.owner);++p.initial[r.owner];}else{p.low_columns.push_back(r.col);p.low_current.push_back(r.owner);}}}
  p.NH=p.high_columns.size();p.NL=p.low_columns.size();if(!p.NH||!p.NL)throw std::runtime_error("two-weight second class empty");
  U cap_total=0;for(int i=0;i<3;++i){if(sum[i]>std::numeric_limits<I>::max())throw std::runtime_error("two-weight local ledger overflow");p.beta[i]=I(sum[i]);const S128 residual=sum[i]-S128(p.low)*p.h[i]-1;if(residual<0)throw std::runtime_error("two-weight current root invalid");const S128 cap=residual/p.delta;p.c[i]=cap>S128(p.h[i])?p.h[i]:U(cap);if(p.initial[i]>p.c[i])throw std::runtime_error("two-weight original profile excluded");cap_total+=p.c[i];}
  if(cap_total<p.NH)throw std::runtime_error("two-weight original deficit impossible");p.D=cap_total-p.NH;p.slack=std::min(p.NH,p.D);p.deficit=p.D<p.NH;if(!build_counts){p.guard="geometry_only";return p;}return finish_counts(std::move(p));
 }
 Problem finish_counts(Problem p){
  p.scaled_relative_mass=two_weight_scaled_counts;if(p.scaled_relative_mass)++scaled_count_attempts;
  max_high_objects=std::max(max_high_objects,p.NH);max_examined_slack=std::max(max_examined_slack,p.slack);
  if(p.slack>SLACK_CAP){p.guard="slack_over6";++slack_failures;return p;}++slack_eligible;max_slack=std::max(max_slack,p.slack);
  if(p.scaled_relative_mass){

   U total_bits=5;__uint128_t bytes=0;
   for(int i=0;i<3;++i){
    p.cache_lo[i]=p.deficit?p.c[i]-std::min(p.c[i],p.D):0;p.cache_hi[i]=p.deficit?p.c[i]:std::min(p.c[i],p.NH);
    if(p.cache_lo[i]>p.cache_hi[i]||p.cache_hi[i]>p.h[i]||p.cache_hi[i]-p.cache_lo[i]>SLACK_CAP)throw std::runtime_error("scaled count cache bounds");
    const U width=p.cache_hi[i]-p.cache_lo[i];const U hbits=p.h[i]?64-__builtin_clzll(p.h[i]):1,cache_bits=std::max<U>(1,width*hbits);total_bits+=cache_bits;
    bytes+=__uint128_t(width+1)*(96+2*((cache_bits+7)/8));
    mpz_class z=1;for(U t=p.cache_lo[i];t<p.cache_hi[i];++t){z*=t+1;++scaled_startup_multiplications;}p.binomial[i].push_back(z);
    for(U a=p.cache_lo[i];a<p.cache_hi[i];++a){if(!mpz_divisible_ui_p(z.get_mpz_t(),static_cast<unsigned long>(a+1)))throw std::runtime_error("scaled recurrence not exactly divisible");z/=a+1;z*=p.h[i]-a;p.binomial[i].push_back(z);++scaled_cache_steps;}
   }
   bytes+=__uint128_t(29)*(96+2*((total_bits+7)/8));if(bytes>std::numeric_limits<U>::max())throw std::runtime_error("scaled payload estimate outside uint64");p.estimated_bytes=U(bytes);scaled_max_payload_estimate=std::max(scaled_max_payload_estimate,p.estimated_bytes);

  }else{
  const U global_bits=p.NH+p.NL+7;__uint128_t bytes=__uint128_t(29)*(96+2*((global_bits+7)/8));
  for(int i=0;i<3;++i){p.cache_lo[i]=p.deficit?p.c[i]-std::min(p.c[i],p.D):0;p.cache_hi[i]=p.deficit?p.c[i]:std::min(p.c[i],p.NH);p.startup_work_score+=std::min(p.cache_lo[i],p.h[i]-p.cache_lo[i]);bytes+=__uint128_t(p.cache_hi[i]-p.cache_lo[i]+1)*(96+2*((p.h[i]+71)/8));}
  max_startup_work_score=std::max(max_startup_work_score,p.startup_work_score);max_estimated_bytes=std::max<U>(max_estimated_bytes,bytes>std::numeric_limits<U>::max()?std::numeric_limits<U>::max():U(bytes));
  if(p.startup_work_score>STARTUP_WORK_BUDGET){p.guard="binomial_start_work_score_over1m";++startup_guard_failures;return p;}
  if(bytes>MEMORY_BUDGET_BYTES){p.guard="count_payload_estimate_over64MiB";++memory_guard_failures;return p;}p.estimated_bytes=U(bytes);
  for(int i=0;i<3;++i){mpz_class z;mpz_bin_uiui(z.get_mpz_t(),static_cast<unsigned long>(p.h[i]),static_cast<unsigned long>(p.cache_lo[i]));p.binomial[i].push_back(z);
   for(U a=p.cache_lo[i];a<p.cache_hi[i];++a){z*=p.h[i]-a;z/=a+1;p.binomial[i].push_back(z);}}
  }
  for(U x0=0;x0<=std::min(p.c[0],p.slack);++x0)for(U x1=0;x1<=std::min(p.c[1],p.slack-x0);++x1){U x2=p.slack-x0-x1;if(x2>p.c[2])continue;std::array<U,3>a{x0,x1,x2};if(p.deficit)for(int i=0;i<3;++i)a[i]=p.c[i]-a[i];mpz_class mass=1;for(int i=0;i<3;++i){if(a[i]<p.cache_lo[i]||a[i]>p.cache_hi[i])throw std::runtime_error("two-weight cache range");mass*=p.binomial[i][a[i]-p.cache_lo[i]];}if(mass<=0)throw std::runtime_error("two-weight nonpositive profile mass");p.profiles.push_back(a);p.mass.push_back(mass);p.total+=mass;}
  if(p.profiles.empty()||p.profiles.size()>28||p.total<=0||std::find(p.profiles.begin(),p.profiles.end(),p.initial)==p.profiles.end())throw std::runtime_error("two-weight original profile absent");p.active=true;p.guard="exact_small_slack";++compiled_windows;profiles_total+=p.profiles.size();max_profiles=std::max<U>(max_profiles,p.profiles.size());if(p.scaled_relative_mass){++scaled_compiled_windows;scaled_max_relative_mass_bits=std::max<U>(scaled_max_relative_mass_bits,mpz_sizeinbase(p.total.get_mpz_t(),2));}else max_count_bits=std::max<U>(max_count_bits,mpz_sizeinbase(p.total.get_mpz_t(),2));return p;
 }
 U profile_for_rank(const Problem&p,mpz_class rank)const{if(!p.active||rank<0||rank>=p.total)throw std::runtime_error("two-weight profile rank");for(U k=0;k<p.mass.size();++k){if(rank<p.mass[k])return k;rank-=p.mass[k];}throw std::runtime_error("two-weight profile rank missing");}
 template<class Solver>Draw draw(const Problem&p,Solver&solver,RNG&rng){
  U index;if(two_weight_profile_update!="heatbath"){const auto pos=std::find(p.profiles.begin(),p.profiles.end(),p.initial);if(pos==p.profiles.end())throw std::runtime_error("MPR original profile absent");const U current=U(pos-p.profiles.begin());auto pick=[&](const mpz_class&limit){return zbig(rng.below_big(bigz(limit)));};if(two_weight_profile_update=="root_orbit_geometric_refresh")index=root_orbit.draw(p.profiles,p.mass,p.total,current,p.beta,p.low,p.h,p.delta,pick);else index=two_weight_profile_update=="metropolis_refresh"?metropolis.draw(p.mass,p.total,current,pick):geometric.draw(p.mass,p.total,current,pick);}else{index=p.profiles.size()==1?0:profile_for_rank(p,zbig(rng.below_big(bigz(p.total))));}Draw d;d.a=p.profiles[index];++profile_draws;profile_changes+=d.a!=p.initial;
  for(int i=0;i<3;++i){S128 root=S128(p.beta[i])-S128(p.low)*p.h[i]-S128(p.delta)*d.a[i];if(root<=0||root>std::numeric_limits<I>::max())throw std::runtime_error("two-weight draw root invalid");d.roots[i]=I(root);}
  TypedLocalCompiler::EqualProblem high,low;high.scene=low.scene=p.scene;high.weight=p.high;low.weight=p.low;high.columns=p.high_columns;high.current=p.high_current;high.quota=d.a;low.columns=p.low_columns;low.current=p.low_current;for(int i=0;i<3;++i)low.quota[i]=p.h[i]-d.a[i];d.high_owners=solver.draw_equal(high,[&](U n){return rng.below(n);});d.low_owners=solver.draw_equal(low,[&](U n){return rng.below(n);});return d;
 }
 template<class Solver>Draw draw_pair_conditional(const Problem&p,Solver&solver,RNG&rng,bool hold=false,bool profile=false){
  auto pick=[&](const mpz_class&limit){return zbig(rng.below_big(bigz(limit)));};Draw d;
  d.a=pair_conditional.draw(p.h,p.c,p.initial,pick,hold,profile);++profile_draws;profile_changes+=d.a!=p.initial;
  for(int i=0;i<3;++i){S128 root=S128(p.beta[i])-S128(p.low)*p.h[i]-S128(p.delta)*d.a[i];if(root<=0||root>std::numeric_limits<I>::max())throw std::runtime_error("pair conditional root invalid");d.roots[i]=I(root);}
  TypedLocalCompiler::EqualProblem high,low;high.scene=low.scene=p.scene;high.weight=p.high;low.weight=p.low;high.columns=p.high_columns;high.current=p.high_current;high.quota=d.a;low.columns=p.low_columns;low.current=p.low_current;for(int i=0;i<3;++i)low.quota[i]=p.h[i]-d.a[i];
  const double lts=profile?process_cpu():0;d.high_owners=solver.draw_equal(high,[&](U n){return rng.below(n);});d.low_owners=solver.draw_equal(low,[&](U n){return rng.below(n);});if(profile)pair_conditional.label_cpu_seconds+=process_cpu()-lts;return d;
 }
 Events commit(Graph&g,const Problem&p,const Draw&d){
  if(d.high_owners.size()!=p.high_columns.size()||d.low_owners.size()!=p.low_columns.size())throw std::runtime_error("two-weight output size");std::array<U,3>hc{},lc{};for(int i:d.high_owners){if(i<0||i>2)throw std::runtime_error("two-weight high owner");++hc[i];}for(int i:d.low_owners){if(i<0||i>2)throw std::runtime_error("two-weight low owner");++lc[i];}
  for(int i=0;i<3;++i)if(hc[i]!=d.a[i]||hc[i]+lc[i]!=p.h[i]||d.roots[i]<=0||S128(d.roots[i])+S128(p.high)*hc[i]+S128(p.low)*lc[i]!=p.beta[i])throw std::runtime_error("two-weight output ledger mismatch");Events out;
  auto put=[&](int oldowner,int nowowner,int col,I weight){if(oldowner==nowowner)return;BalancedPrivateHeatbath::put(g,p.scene,oldowner,col,0);BalancedPrivateHeatbath::put(g,p.scene,nowowner,col,weight);++out.moved_labels;};
  for(U j=0;j<p.high_columns.size();++j)put(p.high_current[j],d.high_owners[j],p.high_columns[j],p.high);for(U j=0;j<p.low_columns.size();++j)put(p.low_current[j],d.low_owners[j],p.low_columns[j],p.low);
  for(int i=0;i<3;++i)if(BalancedPrivateHeatbath::value(g,p.scene,i,p.scene.root)!=d.roots[i]){BalancedPrivateHeatbath::put(g,p.scene,i,p.scene.root,d.roots[i]);++out.root_changes;}
  out.changed=out.moved_labels||out.root_changes;label_changes+=out.moved_labels>0;root_changes+=out.root_changes>0;changes+=out.changed;moved_labels+=out.moved_labels;root_writes+=out.root_changes;return out;
 }
};
