#pragma once

struct SharedWeightHeatbath {
 struct Problem {bool valid=false;int o=0,root=0,a=0,b=0,q=0;I old=0,lo=0,hi=0;S128 Su=0,Sv=0,Cp=0;};
 std::array<std::vector<int>,2> roots;
 U calls=0,row_orientation=0,column_orientation=0,empty_roots=0,root_draws=0;
 U partner_is_root_holds=0,partner_missing_holds=0,windows=0,singleton_windows=0,changes=0;
 U root_neighbor_draws=0,partner_record_draws=0,interval_width_total=0,max_interval_width=0;
 U cell_writes_attempted=0,changed_cell_writes=0,root_pool_total=0;
 void initialize(const Graph&g,bool active){if(!active)return;for(int o=0;o<2;++o){const int n=o?g.nr:g.nc,off=o?0:g.nr;for(int c=0;c<n;++c)if(g.target_degree[off+c]>=2)roots[o].push_back(c);}root_pool_total=roots[0].size()+roots[1].size();}
 static I value(const Graph&g,int o,int a,int c){return o?g.value(c,a):g.value(a,c);}
 static void put(Graph&g,int o,int a,int c,I w){if(o)g.set_raw(c,a,w);else g.set_raw(a,c,w);}
 static Problem compile(const Graph&g,int o,int root,int a,int b,int q){
  if(o<0||o>1||a==b)throw std::runtime_error("WS invalid descriptor");
  Problem p;p.o=o;p.root=root;p.a=a;p.b=b;p.q=q;if(q==root)return p;
  const I x=value(g,o,a,root),y=value(g,o,a,q),z=value(g,o,b,root),t=value(g,o,b,q);
  if(x<=0||y<=0||z<=0)return p;if(t<=0)return p;
  p.old=x;p.Su=S128(x)+y;p.Sv=S128(z)+t;p.Cp=S128(x)+z;
  const S128 lo=std::max(S128(1),p.Cp-p.Sv+1),hi=std::min(p.Su-1,p.Cp-1);
  if(lo>hi||lo<=0||hi>std::numeric_limits<I>::max())throw std::runtime_error("WS invalid supported interval");
  p.lo=I(lo);p.hi=I(hi);p.valid=true;return p;
 }
 bool commit(Graph&g,const Problem&p,I x){
  if(!p.valid||x<p.lo||x>p.hi)throw std::runtime_error("WS invalid conditional draw");
  const S128 y=p.Su-x,z=p.Cp-x,t=p.Sv-p.Cp+x;
  if(y<=0||z<=0||t<=0||y>std::numeric_limits<I>::max()||z>std::numeric_limits<I>::max()||t>std::numeric_limits<I>::max())throw std::runtime_error("WS weight overflow");
  if(value(g,p.o,p.a,p.root)!=p.old)throw std::runtime_error("WS stale ledger");
  const U before=g.counters?g.counters->cell_updates:0;
  put(g,p.o,p.a,p.root,x);put(g,p.o,p.a,p.q,I(y));put(g,p.o,p.b,p.root,I(z));put(g,p.o,p.b,p.q,I(t));
  cell_writes_attempted+=4;const bool changed=x!=p.old;changed_cell_writes+=changed?4:0;
  if(g.counters&&g.counters->cell_updates-before!=(changed?4:0))throw std::runtime_error("WS update counter mismatch");
  if(changed)++changes;return changed;
 }
 bool step(Engine&e,Graph&g){
  ++calls;const int o=int(e.rng.below(2));if(o)++column_orientation;else++row_orientation;
  const auto&pool=roots[o];if(pool.empty()){++empty_roots;return false;}
  const int root=pool[e.rng.below(pool.size())];++root_draws;
  const auto&radj=g.adj[o?root:g.nr+root];const U d=radj.size();if(d<2)throw std::runtime_error("WS root degree changed");
  const U ia=e.rng.below(d);U ib=e.rng.below(d-1);if(ib>=ia)++ib;root_neighbor_draws+=2;
  const Edge ra=g.edges[radj[ia]],rb=g.edges[radj[ib]];const int a=o?ra.c:ra.r,b=o?rb.c:rb.r;
  const auto&aadj=g.adj[o?g.nr+a:a];if(aadj.empty())throw std::runtime_error("WS root neighbor empty");
  const Edge qe=g.edges[aadj[e.rng.below(aadj.size())]];const int q=o?qe.r:qe.c;++partner_record_draws;
  if(q==root){++partner_is_root_holds;return false;}
  if(value(g,o,b,q)<=0){++partner_missing_holds;return false;}
  const Problem p=compile(g,o,root,a,b,q);if(!p.valid)throw std::runtime_error("WS selected invalid positive rectangle");
  ++windows;const U width=U(p.hi-p.lo)+1;singleton_windows+=(width==1);interval_width_total+=width;max_interval_width=std::max(max_interval_width,width);
  const I x=p.lo+I(e.rng.below(width));const bool changed=commit(g,p,x);if(changed)++e.stat.changed_outer;return changed;
 }
  
 U intersection_calls=0,intersection_empty_holds=0,intersection_bitset_calls=0,intersection_sparse_calls=0,intersection_max_eligible=0,intersection_partner_draws=0;
 __uint128_t intersection_word_visits=0,intersection_scan_records=0,intersection_eligible_total=0;
 template<class Bits>std::vector<int> common_objects(const Graph&g,int o,int root,int a,int b,Bits&bits){
  std::vector<int>common;const auto&aa=g.adj[o?g.nr+a:a];const auto&bb=g.adj[o?g.nr+b:b];const auto&axis=bits.axis[o];
  if(axis.active&&__uint128_t(2)*axis.words<=std::min(aa.size(),bb.size())){
   ++intersection_bitset_calls;const U*x=axis.bits.data()+U(a)*axis.words,*y=axis.bits.data()+U(b)*axis.words;
   for(U k=0;k<axis.words;++k){U mask=x[k]&y[k];intersection_word_visits+=2;while(mask){const unsigned bit=__builtin_ctzll(mask);mask&=mask-1;const U q=k*64+bit;if(q>=U(axis.opposite))throw std::runtime_error("WS intersection bit padding");if(int(q)!=root)common.push_back(int(q));}}
  }else{
   ++intersection_sparse_calls;const bool shorter_a=aa.size()<=bb.size();const auto&small=shorter_a?aa:bb;const int other=shorter_a?b:a;
   for(int id:small){++intersection_scan_records;const Edge edge=g.edges[id];const int q=o?edge.r:edge.c;if(q!=root&&value(g,o,other,q)>0)common.push_back(q);}
  }
  intersection_eligible_total+=common.size();intersection_max_eligible=std::max(intersection_max_eligible,U(common.size()));return common;
 }
 template<class Bits>bool step_intersection(Engine&e,Graph&g,Bits&bits){
  ++calls;++intersection_calls;const int o=int(e.rng.below(2));if(o)++column_orientation;else++row_orientation;
  const auto&pool=roots[o];if(pool.empty()){++empty_roots;return false;}
  const int root=pool[e.rng.below(pool.size())];++root_draws;const auto&radj=g.adj[o?root:g.nr+root];const U d=radj.size();if(d<2)throw std::runtime_error("WS intersection root degree changed");
  const U ia=e.rng.below(d);U ib=e.rng.below(d-1);if(ib>=ia)++ib;root_neighbor_draws+=2;const Edge ra=g.edges[radj[ia]],rb=g.edges[radj[ib]];const int a=o?ra.c:ra.r,b=o?rb.c:rb.r;
  const auto common=common_objects(g,o,root,a,b,bits);if(common.empty()){++intersection_empty_holds;return false;}
  const int q=common[e.rng.below(common.size())];++intersection_partner_draws;const Problem p=compile(g,o,root,a,b,q);if(!p.valid)throw std::runtime_error("WS intersection invalid rectangle");
  ++windows;const U width=U(p.hi-p.lo)+1;singleton_windows+=(width==1);interval_width_total+=width;max_interval_width=std::max(max_interval_width,width);
  const I x=p.lo+I(e.rng.below(width));const bool changed=commit(g,p,x);if(changed)++e.stat.changed_outer;return changed;
 }

};
