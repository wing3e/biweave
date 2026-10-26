#pragma once

struct WholePrivateConditional:TypedLocalCompiler {
 static constexpr U SMALL_POOL_CAP=6;
 struct SmallProblem {Scene scene;std::vector<int>columns,current;std::vector<I>weights;std::array<I,3>beta{};};
 TwoWeightComplement two;bool reuse_layout=false;U reused_ledger_calls=0,deferred_full_arrays=0,direct_record_geometry_calls=0;
 struct Ledger {std::array<int,3>quota{};std::array<I,3>beta{};};
 U windows=0,empty_private=0,small_calls=0,single_class_calls=0,two_class_calls=0,two_compiled_calls=0,single_fallbacks=0;
 U whole_free_calls=0,two_free_calls=0;
 U count_calls=0,complete_options_total=0,max_complete_options=0,profiles_total=0,max_profiles=0;
 U moved_private_labels=0,root_changes=0,pool_total=0,max_pool=0,classes_total=0,primary_ties=0,secondary_ties=0;
 double cpu_seconds=0;
 explicit WholePrivateConditional(JournaledLowrank4Kernel&k):TypedLocalCompiler(k,"full"){}
 SmallProblem compile_pool(const Graph&g,const Scene&s){
  SmallProblem p;p.scene=s;std::vector<int>labels;for(const auto&pool:s.pools)labels.insert(labels.end(),pool.begin(),pool.end());
p.columns=std::move(labels);std::array<int,3>counts{};std::array<S128,3>beta{};for(int i=0;i<3;++i)beta[i]=value(g,s,i,s.root);
  const auto&scratch=shared.scratch[s.o];for(int col:p.columns){if(scratch.stamp[col]!=scratch.epoch||__builtin_popcount(unsigned(scratch.mask[col]))!=1)throw std::runtime_error("whole-small stale private label");int owner=__builtin_ctz(unsigned(scratch.mask[col]));I w=scratch.first_weight[col];if(w<=0||value(g,s,owner,col)!=w)throw std::runtime_error("whole-small stale weight");p.weights.push_back(w);p.current.push_back(owner);++counts[owner];beta[owner]+=w;}
  for(int i=0;i<3;++i){if(counts[i]!=int(s.pools[i].size()))throw std::runtime_error("whole-small quota mismatch");p.scene.quota[i]=counts[i];if(beta[i]<=0||beta[i]>std::numeric_limits<I>::max())throw std::runtime_error("whole-small ledger overflow");p.beta[i]=I(beta[i]);}return p;
 }
 SmallProblem compile_small(const Graph&g,const Scene&s){auto p=compile_pool(g,s);if(p.columns.size()>SMALL_POOL_CAP)throw std::runtime_error("whole-small solver budget exceeded");std::vector<U>ix(p.columns.size());std::iota(ix.begin(),ix.end(),0);std::sort(ix.begin(),ix.end(),[&](U a,U b){return p.columns[a]<p.columns[b];});auto old=p;for(U j=0;j<ix.size();++j){p.columns[j]=old.columns[ix[j]];p.weights[j]=old.weights[ix[j]];p.current[j]=old.current[ix[j]];}return p;}
 Ledger compile_ledger(const Graph&g,const Scene&s)const{
  Ledger result;std::array<S128,3>beta{};for(int i=0;i<3;++i)beta[i]=value(g,s,i,s.root);const auto&scratch=shared.scratch[s.o];
  for(const auto&r:records){if(r.owner<0||r.owner>2||r.weight<=0||scratch.stamp[r.column]!=scratch.epoch||__builtin_popcount(unsigned(scratch.mask[r.column]))!=1||value(g,s,r.owner,r.column)!=r.weight)throw std::runtime_error("whole ledger stale private record");++result.quota[r.owner];beta[r.owner]+=r.weight;}
  for(int i=0;i<3;++i){if(result.quota[i]!=int(s.pools[i].size())||beta[i]<=0||beta[i]>std::numeric_limits<I>::max())throw std::runtime_error("whole ledger quota/overflow");result.beta[i]=I(beta[i]);}return result;
 }
 bool whole_free_certificate_ledger(const Ledger&p)const{
  std::vector<U>ordered=group_slots;std::sort(ordered.begin(),ordered.end(),[&](U a,U b){return table[a].weight>table[b].weight;});
  for(int i=0;i<3;++i){U remaining=U(p.quota[i]);S128 maximum=0;for(U slot:ordered){U take=std::min(remaining,table[slot].count);maximum+=S128(take)*table[slot].weight;remaining-=take;if(!remaining)break;}if(remaining||maximum>=S128(p.beta[i]))return false;}return true;
 }
 bool whole_free_certificate(const SmallProblem&p)const{
  std::vector<U>ordered=group_slots;std::sort(ordered.begin(),ordered.end(),[&](U a,U b){return table[a].weight>table[b].weight;});
  for(int i=0;i<3;++i){U remaining=U(p.scene.quota[i]);S128 maximum=0;for(U slot:ordered){U take=std::min(remaining,table[slot].count);maximum+=S128(take)*table[slot].weight;remaining-=take;if(!remaining)break;}if(remaining||maximum>=S128(p.beta[i]))return false;}return true;
 }
 std::vector<int> draw_free(const SmallProblem&p,RNG&rng){EqualProblem eq;eq.scene=p.scene;eq.columns=p.columns;eq.current=p.current;for(int i=0;i<3;++i)eq.quota[i]=U(p.scene.quota[i]);return draw_equal(eq,[&](U n){return rng.below(n);});}
 std::array<I,3> roots_for(const SmallProblem&p,const std::vector<int>&owners)const{std::array<S128,3>r{};for(int i=0;i<3;++i)r[i]=p.beta[i];for(U j=0;j<owners.size();++j)r[owners[j]]-=p.weights[j];std::array<I,3>out{};for(int i=0;i<3;++i){if(r[i]<=0||r[i]>std::numeric_limits<I>::max())throw std::runtime_error("whole-free root invalid");out[i]=I(r[i]);}return out;}
 static bool two_free_certificate(const TwoWeightComplement::Problem&p){for(int i=0;i<3;++i)if(p.c[i]<std::min(p.h[i],p.NH))return false;return true;}
 TwoWeightComplement::Draw draw_two_free(const TwoWeightComplement::Problem&p,RNG&rng){EqualProblem eq;eq.scene=p.scene;eq.columns=p.high_columns;eq.columns.insert(eq.columns.end(),p.low_columns.begin(),p.low_columns.end());eq.current=p.high_current;eq.current.insert(eq.current.end(),p.low_current.begin(),p.low_current.end());eq.quota=p.h;auto owners=draw_equal(eq,[&](U n){return rng.below(n);});TwoWeightComplement::Draw out;out.high_owners.assign(owners.begin(),owners.begin()+p.NH);out.low_owners.assign(owners.begin()+p.NH,owners.end());for(int i:out.high_owners)++out.a[i];for(int i=0;i<3;++i){S128 r=S128(p.beta[i])-S128(p.low)*p.h[i]-S128(p.delta)*out.a[i];if(r<=0||r>std::numeric_limits<I>::max())throw std::runtime_error("two-free root invalid");out.roots[i]=I(r);}return out;}
 bool commit_small(Engine&e,Graph&g,const SmallProblem&p,const std::vector<int>&owners,const std::array<I,3>&root){
  if(owners.size()!=p.columns.size())throw std::runtime_error("whole-small output dimension");std::array<int,3>counts{};std::array<S128,3>ledger{};for(int i=0;i<3;++i){if(root[i]<=0)throw std::runtime_error("whole-small root must remain positive");ledger[i]=root[i];}
  for(U j=0;j<owners.size();++j){int i=owners[j];if(i<0||i>2)throw std::runtime_error("whole-small invalid owner");++counts[i];ledger[i]+=p.weights[j];}
  for(int i=0;i<3;++i)if(counts[i]!=p.scene.quota[i]||ledger[i]!=p.beta[i])throw std::runtime_error("whole-small ledger changed");
  bool changed=false;for(U j=0;j<owners.size();++j)if(owners[j]!=p.current[j]){put(g,p.scene,p.current[j],p.columns[j],0);put(g,p.scene,owners[j],p.columns[j],p.weights[j]);++moved_private_labels;changed=true;}
  for(int i=0;i<3;++i)if(value(g,p.scene,i,p.scene.root)!=root[i]){put(g,p.scene,i,p.scene.root,root[i]);++root_changes;changed=true;}
  if(changed){++changes;++e.stat.changed_outer;}return changed;
 }
 std::vector<U> most_frequent(U excluded=std::numeric_limits<U>::max())const{
  U best=0;std::vector<U>result;for(U slot:group_slots)if(slot!=excluded){const U q=table[slot].count;if(q>best){best=q;result.clear();}if(q==best)result.push_back(slot);}return result;
 }
 std::vector<TwoWeightComplement::Record> all_records()const{std::vector<TwoWeightComplement::Record>result;result.reserve(records.size());for(const auto&r:records)result.push_back({r.column,r.owner,r.weight});return result;}
 bool fallback_single(Engine&e,Graph&g,const Scene&s,U primary){
  auto p=compile_equal(s,primary);auto owners=draw_equal(p,[&](U n){return e.rng.below(n);});U moves=0;for(U j=0;j<owners.size();++j)moves+=owners[j]!=p.current[j];moved_private_labels+=moves;return commit_equal(e,g,p,owners);
 }
 bool execute(Engine&e,Graph&g,const Scene&s){
  ++windows;U P=0;for(const auto&pool:s.pools)P+=pool.size();pool_total+=P;max_pool=std::max(max_pool,P);if(!P){++empty_private;return false;}
  group(s);classes_total+=group_slots.size();SmallProblem complete;bool free;
  if(reuse_layout){++reused_ledger_calls;free=whole_free_certificate_ledger(compile_ledger(g,s));}else{complete=compile_pool(g,s);free=whole_free_certificate(complete);}
  if(free){if(reuse_layout){++deferred_full_arrays;complete=compile_pool(g,s);}++whole_free_calls;auto owners=draw_free(complete,e.rng);return commit_small(e,g,complete,owners,roots_for(complete,owners));}
  if(P<=SMALL_POOL_CAP){++small_calls;++count_calls;auto p=compile_small(g,s);SharedRootGroupedBufferProblem problem(p.weights,p.scene.quota,p.beta);auto draw=problem.draw(e.rng);if(draw.completions>90)throw std::runtime_error("whole-small labelled count exceeded");complete_options_total+=draw.completions;max_complete_options=std::max(max_complete_options,draw.completions);return commit_small(e,g,p,draw.owners,draw.root_weights);}
  auto first=most_frequent();if(first.empty())throw std::runtime_error("whole pool lost its classes");++primary_ties;U primary=first[e.rng.below(first.size())];
  if(group_slots.size()==1){++single_class_calls;return fallback_single(e,g,s,primary);}
  auto second=most_frequent(primary);if(second.empty())throw std::runtime_error("whole missing second class");++secondary_ties;U secondary=second[e.rng.below(second.size())];++two_class_calls;
  TwoWeightComplement::Problem p;if(reuse_layout){++direct_record_geometry_calls;p=two.compile_mapped(g,s,table[primary].weight,table[secondary].weight,records,[](const PrivateRecord&r){return TwoWeightComplement::Record{r.column,r.owner,r.weight};},false);}else p=two.compile(g,s,table[primary].weight,table[secondary].weight,all_records(),false);if(two_free_certificate(p)){++two_free_calls;auto draw=draw_two_free(p,e.rng);auto event=two.commit(g,p,draw);moved_private_labels+=event.moved_labels;root_changes+=event.root_changes;if(event.changed){++changes;++e.stat.changed_outer;}return event.changed;}++count_calls;p=two.finish_counts(std::move(p));if(!p.active){++single_fallbacks;return fallback_single(e,g,s,primary);}
  ++two_compiled_calls;profiles_total+=p.profiles.size();max_profiles=std::max<U>(max_profiles,p.profiles.size());auto draw=two.draw(p,*this,e.rng);auto event=two.commit(g,p,draw);moved_private_labels+=event.moved_labels;root_changes+=event.root_changes;if(event.changed){++changes;++e.stat.changed_outer;}return event.changed;
 }
 bool step(Engine&e,Graph&g){
  ++calls;++e.stat.work;if(g.D)throw std::runtime_error("whole-private needs exact margins");const int o=choose_orientation(e.rng,g);const auto&roots=shared.roots[o];if(roots.empty()){++empty_roots;return false;}const int root=roots[e.rng.below(roots.size())],vertex=o?root:g.nr+root;const auto&adj=g.adj[vertex];if(adj.size()<3)throw std::runtime_error("whole root degree changed");std::vector<int>ix;for(U j=adj.size()-3;j<adj.size();++j){int k=int(e.rng.below(j+1));if(std::find(ix.begin(),ix.end(),k)!=ix.end())k=int(j);ix.push_back(k);}std::array<int,3>nodes{};for(int i=0;i<3;++i){const auto&ed=g.edges[adj[ix[i]]];nodes[i]=o?ed.c:ed.r;}return execute(e,g,make_scene(g,o,root,nodes));
 }
};
