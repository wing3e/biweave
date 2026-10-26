#pragma once

struct InvariantWeightedRectangle {
 bool requested=false,input_bound_axis=false,per_actor_auxiliary=false;int fixed_axis=0,nr=0,nc=0;
 std::array<U,2>input_degree_square_sum{0,0},input_work_bound_score{0,0};
 std::array<std::vector<U>,2>actor_prefix;std::array<U,2>stub_mass{0,0},positive_actors{0,0};
 U calls=0,lazy_calls=0,inner_steps=0,row_axis=0,column_axis=0,empty_stub_holds=0,single_actor_holds=0,same_actor_holds=0,weighted_column_draws=0,single_column_holds=0,same_column_holds=0,column_mass_value_lookups=0,rectangle_draws=0,interval_singletons=0,zero_delta=0,nonzero_delta=0,setup_actor_nodes=0,adjacency_record_visits=0,max_actor_records=0,returns=0,timeout_rollbacks=0,capacity_rollbacks=0,rolled_back_rectangles=0,applied_rectangles=0,max_interval_cardinality=0;
 static void add(U&x,U v){if(v>std::numeric_limits<U>::max()-x)throw std::runtime_error("weighted-column Gibbs counter overflow");x+=v;}
 static void inc(U&x){add(x,1);}
 void initialize(const Graph&g,bool on,bool bounded_axis=false,bool auxiliary=false){
  if(auxiliary&&!on)throw std::runtime_error("per-actor auxiliary requires weighted-column Gibbs");per_actor_auxiliary=auxiliary;
  if(bounded_axis&&!on)throw std::runtime_error("input_bound axis requires weighted-column Gibbs");
  input_bound_axis=bounded_axis;requested=on;if(!on)return;CoverageSupportCap::validate_nodes(g.nr,g.nc);nr=g.nr;nc=g.nc;
  for(int o=0;o<2;++o){const int n=o?nc:nr;auto&p=actor_prefix[o];p.reserve(n);U total=0;
   for(int a=0;a<n;++a){const int v=o?nr+a:a;const int d=g.target_degree[v];if(d<0)throw std::runtime_error("negative input degree");total=checked_u128(__uint128_t(total)+U(d),"fixed actor stub mass");p.push_back(total);positive_actors[o]+=d>0;inc(setup_actor_nodes);
    if(input_bound_axis){const U square=checked_u128(__uint128_t(U(d))*U(d),"input degree square");input_degree_square_sum[o]=checked_u128(__uint128_t(input_degree_square_sum[o])+square,"input degree square sum");}}
   if(total!=g.edges.size())throw std::runtime_error("fixed input actor degree mass mismatch");stub_mass[o]=total;
  }
  if(input_bound_axis){
   const U E=stub_mass[0];const __uint128_t e2=__uint128_t(E)*E;
   for(int o=0;o<2;++o){const __uint128_t twice=__uint128_t(2)*input_degree_square_sum[o];
    if(e2>__uint128_t(std::numeric_limits<I>::max())||twice>__uint128_t(std::numeric_limits<I>::max()))throw std::runtime_error("input-bound score exceeds signed64 domain");
    input_work_bound_score[o]=positive_actors[o]<2?0:U(std::min(e2,twice));
   }
   fixed_axis=input_work_bound_score[1]<input_work_bound_score[0]?1:0;
  }
 }
 void begin(const Graph&g){if(!requested||g.nr!=nr||g.nc!=nc)throw std::runtime_error("weighted-column Gibbs not initialized for graph");inc(calls);}
 struct Draw{bool valid=false;Rectangle rectangle{};I delta=0;};

 U auxiliary_delta_proposals=0,auxiliary_delta_rejections=0,auxiliary_max_ticket_bits=0;
 template<class Random> static __uint128_t auxiliary_below(Random&r,__uint128_t n){
  if(!n)throw std::runtime_error("empty auxiliary uint128 draw");
  if(n<=std::numeric_limits<U>::max())return r.below(U(n));
  const unsigned bits=wide_bits(n-1);
  for(;;){__uint128_t v=__uint128_t(r.gen())|(__uint128_t(r.gen())<<64);if(bits<128)v&=(__uint128_t(1)<<bits)-1;if(v<n)return v;}
 }
 static __uint128_t auxiliary_q(const std::array<I,4>&x,I delta){
  const std::array<I,4>y{x[0]+delta,x[1]-delta,x[2]-delta,x[3]+delta};
  for(I v:y)if(v<0)throw std::runtime_error("negative auxiliary rectangle cell");
  return __uint128_t(U(y[0]))*U(y[3])+__uint128_t(U(y[1]))*U(y[2]);
 }
 template<class Random> Draw draw_auxiliary(const Graph&g,Random&random,int o,int a,int b,int va,int vb){
  auto column=[&](int v){
   const U strength=U(g.target_strength[v]);U t=random.below(strength);inc(weighted_column_draws);int chosen=-1;__uint128_t mass=0;
   for(int id:g.adj[v]){inc(adjacency_record_visits);const Edge ed=g.edges[id];if(ed.w<=0)throw std::runtime_error("nonpositive auxiliary actor edge");const U w=U(ed.w);mass+=w;if(chosen<0){if(t<w)chosen=o?ed.r:ed.c;else t-=w;}}
   if(mass!=strength||chosen<0)throw std::runtime_error("auxiliary actor strength mismatch");return chosen;
  };
  const U records=checked_u128(__uint128_t(g.adj[va].size())+g.adj[vb].size(),"auxiliary actor records");max_actor_records=std::max(max_actor_records,records);
  int c0=column(va),c1=column(vb);if(c0==c1){inc(same_column_holds);return{};}
  if(a>b)std::swap(a,b);if(c0>c1)std::swap(c0,c1);const Rectangle r=o?Rectangle{c0,c1,a,b}:Rectangle{a,b,c0,c1};const auto old=g.cells(r);add(column_mass_value_lookups,4);
  const I lo=-std::min(old[0],old[3]),hi=std::min(old[1],old[2]);if(lo>0||hi<0||lo>hi)throw std::runtime_error("invalid auxiliary delta interval");
  const U cardinality=checked_u128(__uint128_t(S128(hi)-S128(lo))+1,"auxiliary interval cardinality");max_interval_cardinality=std::max(max_interval_cardinality,cardinality);if(cardinality==1)inc(interval_singletons);
  const __uint128_t maximum=std::max(auxiliary_q(old,lo),auxiliary_q(old,hi));if(!maximum)throw std::runtime_error("zero auxiliary rectangle mass");auxiliary_max_ticket_bits=std::max(auxiliary_max_ticket_bits,U(wide_bits(maximum)));
  I delta;
  for(;;){inc(auxiliary_delta_proposals);delta=random.integer(lo,hi);if(auxiliary_below(random,maximum)<auxiliary_q(old,delta))break;inc(auxiliary_delta_rejections);}
  inc(rectangle_draws);if(delta)inc(nonzero_delta);else inc(zero_delta);return{true,r,delta};
 }
 template<class Random> Draw draw(const Graph&g,Random&random){
  if(!requested||g.nr!=nr||g.nc!=nc)throw std::runtime_error("weighted-column Gibbs lifecycle");inc(inner_steps);
  const int o=input_bound_axis?fixed_axis:int(random.below(2));if(o)inc(column_axis);else inc(row_axis);const U mass=stub_mass[o];if(!mass){inc(empty_stub_holds);return{};}
  if(positive_actors[o]<2){inc(single_actor_holds);return{};}
  const auto&p=actor_prefix[o];int a=int(std::upper_bound(p.begin(),p.end(),random.below(mass))-p.begin());const U before=a?p[a-1]:0,actor_mass=p[a]-before;
  if(!actor_mass||actor_mass>=mass)throw std::runtime_error("invalid fixed actor deletion mass");U second=random.below(mass-actor_mass);if(second>=before)second+=actor_mass;int b=int(std::upper_bound(p.begin(),p.end(),second)-p.begin());
  if(a==b)throw std::runtime_error("weighted actor WOR selected same actor");const int va=o?nr+a:a,vb=o?nr+b:b;
  if(g.target_strength[va]<=0||g.target_strength[vb]<=0)throw std::runtime_error("positive input-degree actor has nonpositive strength");
  if(per_actor_auxiliary)return draw_auxiliary(g,random,o,a,b,va,vb);
  const U T=checked_u128(__uint128_t(g.target_strength[va])+__uint128_t(g.target_strength[vb]),"combined actor strength");
  U t0=random.below(T);int c0=-1,c1=-1;inc(weighted_column_draws);
  const U records=checked_u128(__uint128_t(g.adj[va].size())+g.adj[vb].size(),"combined actor records");max_actor_records=std::max(max_actor_records,records);__uint128_t scanned_mass=0;
  for(int v:{va,vb})for(int id:g.adj[v]){
   inc(adjacency_record_visits);const Edge edge=g.edges[id];if(edge.w<=0)throw std::runtime_error("nonpositive adjacency edge in weighted draw");const U w=U(edge.w);scanned_mass+=w;
   const int c=o?edge.r:edge.c;
   if(c0<0){if(t0<w)c0=c;else t0-=w;}
  }
  if(scanned_mass!=T||c0<0)throw std::runtime_error("combined current adjacency weights differ from immutable strength");
  add(column_mass_value_lookups,2);const U first_mass=checked_u128(__uint128_t(U(o?g.value(c0,a):g.value(a,c0)))+U(o?g.value(c0,b):g.value(b,c0)),"first combined column mass");
  if(!first_mass||first_mass>T)throw std::runtime_error("invalid first combined column mass");if(first_mass==T){inc(single_column_holds);return{};}
  U t1=random.below(T-first_mass);inc(weighted_column_draws);scanned_mass=0;
  for(int v:{va,vb})for(int id:g.adj[v]){
   inc(adjacency_record_visits);const Edge edge=g.edges[id];if(edge.w<=0)throw std::runtime_error("nonpositive adjacency edge in weighted WOR");const int c=o?edge.r:edge.c;if(c==c0)continue;const U w=U(edge.w);scanned_mass+=w;
   if(c1<0){if(t1<w)c1=c;else t1-=w;}
  }
  if(scanned_mass!=T-first_mass||c1<0||c1==c0)throw std::runtime_error("combined column WOR remainder mismatch");
  if(a>b)std::swap(a,b);if(c0>c1)std::swap(c0,c1);
  const Rectangle r=o?Rectangle{c0,c1,a,b}:Rectangle{a,b,c0,c1};const auto old=g.cells(r);
  const I lo=-std::min(old[0],old[3]),hi=std::min(old[1],old[2]);
  if(lo>0||hi<0||lo>hi)throw std::runtime_error("invalid full rectangle delta interval");
  const U cardinality=checked_u128(__uint128_t(S128(hi)-S128(lo))+1,"full delta interval cardinality");max_interval_cardinality=std::max(max_interval_cardinality,cardinality);if(cardinality==1)inc(interval_singletons);
  const I delta=random.integer(lo,hi);if(delta<lo||delta>hi)throw std::runtime_error("uniform delta draw outside interval");
  inc(rectangle_draws);if(delta)inc(nonzero_delta);else inc(zero_delta);return{true,r,delta};
 }
 void metadata(std::ostream&f,bool extra_lazy=true)const{
  if(!requested)return;f<<"\"coverage_weighted_column_gibbs_requested\":1,\"RWC_without_replacement\":"<<(per_actor_auxiliary?"false":"true")<<",\"RWC_prefix_initialized\":true,\"RWC_row_stub_mass\":"<<stub_mass[0]<<",\"RWC_column_stub_mass\":"<<stub_mass[1]<<",\"RWC_positive_row_actors\":"<<positive_actors[0]<<",\"RWC_positive_column_actors\":"<<positive_actors[1]<<",";
if(input_bound_axis)f<<"\"RWC_axis_policy\":\"input_bound\",\"RWC_fixed_axis\":"<<fixed_axis<<",\"RWC_input_row_degree_square_sum\":"<<input_degree_square_sum[0]<<",\"RWC_input_column_degree_square_sum\":"<<input_degree_square_sum[1]<<",\"RWC_input_row_work_bound_score\":"<<input_work_bound_score[0]<<",\"RWC_input_column_work_bound_score\":"<<input_work_bound_score[1]<<",\"RWC_orientation_coin_used\":false,\"RWC_axis_selection_scope\":\"min certified adjacency-scan bound from immutable input degrees; tie row; not CPU or mixing optimality\",";
if(!extra_lazy)f<<"\"RWC_extra_lazy_requested\":0,\"RWC_intrinsic_hold_only\":true,";
#define RWC_FIELD(name) f<<"\"RWC_" #name "\":"<<name<<",";
  RWC_FIELD(calls) RWC_FIELD(lazy_calls) RWC_FIELD(inner_steps) RWC_FIELD(row_axis) RWC_FIELD(column_axis) RWC_FIELD(empty_stub_holds) RWC_FIELD(single_actor_holds) RWC_FIELD(same_actor_holds) RWC_FIELD(weighted_column_draws) RWC_FIELD(single_column_holds) RWC_FIELD(same_column_holds) RWC_FIELD(column_mass_value_lookups) RWC_FIELD(rectangle_draws) RWC_FIELD(interval_singletons) RWC_FIELD(zero_delta) RWC_FIELD(nonzero_delta) RWC_FIELD(setup_actor_nodes) RWC_FIELD(adjacency_record_visits) RWC_FIELD(max_actor_records) RWC_FIELD(returns) RWC_FIELD(timeout_rollbacks) RWC_FIELD(capacity_rollbacks) RWC_FIELD(rolled_back_rectangles) RWC_FIELD(applied_rectangles) RWC_FIELD(max_interval_cardinality)
  if(per_actor_auxiliary){f<<"\"RWC_per_actor_auxiliary_requested\":1,\"RWC_actor_without_replacement\":true,\"RWC_column_choice_per_actor\":true,";RWC_FIELD(auxiliary_delta_proposals) RWC_FIELD(auxiliary_delta_rejections) RWC_FIELD(auxiliary_max_ticket_bits)}
#undef RWC_FIELD
  if(per_actor_auxiliary)f<<"\"RWC_path_MH_used\":false,\"RWC_path_Big_products_used\":false,\"RWC_phase_CPU_measured\":false,\"RWC_policy\":\"fixed input-degree WOR actors; one weight-proportional edge per actor; same-column hold; quadratic-weighted complete delta interval including0; exact uint128 rejection with expected proposals<2; "<<(extra_lazy?"original lazy/constant hazard/first target return":"intrinsic delta0 hold; no extra outer coin; constant hazard/first target return")<<", direct accept, independent whole support-cap kill; one complete scan per actor; no success-conditioned rectangle retry\",";
  else f<<"\"RWC_path_MH_used\":false,\"RWC_path_Big_products_used\":false,\"RWC_phase_CPU_measured\":false,\"RWC_policy\":\"fixed input-degree sequential weighted WOR actors via prefix deletion; combined positive-record sequential weighted WOR columns excludes both records of first column; fewer than2 choices hold; canonical complete nonnegative uniform delta including0; "<<(extra_lazy?"original lazy/constant hazard/first target return":"intrinsic delta0 hold; no extra outer coin; constant hazard/first target return")<<", direct accept, independent whole support-cap kill; two complete adjacency scans charged; no retry\",";
 }
};
