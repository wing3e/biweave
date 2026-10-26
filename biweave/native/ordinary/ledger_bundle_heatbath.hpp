#pragma once
#include <algorithm>
#include <array>
#include <cstddef>
#include <limits>
#include <ostream>
#include <stdexcept>
#include <string>
#include <vector>

struct LedgerBundleHeatbath {
 using Wide=__uint128_t;
 struct Label {int node=-1,old_owner=-1;I weight=0;};
 struct Cell {int node=-1;I weight=0;};
 using Table=std::array<Cell,6>;
 using Support=std::array<int,6>;
 struct Actor {int node=-1,degree=0;I strength=0;};
 struct Descriptor {
  std::array<I,3> strengths{};
  std::array<Actor,6> actors{};
  int actor_count=0;bool all_actor_degree_one=true;
 };
 enum Kind {EMPTY=0,FOREST=1,CYCLE=2,K23=3};
 struct Plan {
  Support support{};Kind kind=EMPTY;Wide count=0;
  std::array<S128,6> base{};
  std::array<int,6> sign{};
  S128 lower=0,upper=-1;
 };
 struct Fiber {
  Descriptor descriptor{};Table original{};
  std::array<Plan,90> plans{};
  U size=0,supports_examined=0,forest_supports=0,cycle_supports=0,rank2_supports=0;
  Wide total=0;
 };
 bool requested=false,active=false;
 int rows=0,columns=0;
 std::array<bool,2> axis_active={false,false};
 std::array<std::vector<int>,2> objects;
 std::array<Wide,2> axis_groups={0,0};Wide total_groups=0;
 U compose_calls=0,no_static_candidates=0,index_checks=0,changes=0;
 U uniform_block_calls=0,both_axis_calls=0;
 std::array<U,2> axis_calls={0,0},axis_changes={0,0};
 U selected_triples=0,repeated_opposite_triples=0,fast_leaf_calls=0;
 U supports_examined=0,forest_supports=0,cycle_supports=0,rank2_supports=0;
 U singleton_holds=0,selected_original=0,rank_draws=0,cell_writes=0;
 Wide max_fiber_count=0;

 static I checked_I(S128 x) {
  if(x<0||x>S128(std::numeric_limits<I>::max()))
   throw std::runtime_error("ledger per-node int64 range");
  return I(x);
 }
 static std::string decimal(Wide x) {
  if(!x)return "0";std::string s;
  while(x){s.push_back(char('0'+unsigned(x%10)));x/=10;}
  std::reverse(s.begin(),s.end());return s;
 }
 static bool cell_less(const Cell&a,const Cell&b) {
  return a.node!=b.node?a.node<b.node:a.weight<b.weight;
 }
 static bool table_equal(const Table&a,const Table&b) {
  for(int i=0;i<6;++i)if(a[i].node!=b[i].node||a[i].weight!=b[i].weight)return false;
  return true;
 }
 static int actor_index(const Descriptor&d,int node) {
  for(int i=0;i<d.actor_count;++i)if(d.actors[i].node==node)return i;
  throw std::runtime_error("ledger unknown actor");
 }
 static Descriptor describe(const std::array<Label,6>&labels,
                            const std::array<I,3>&strengths,Table&original) {
  Descriptor d;d.strengths=strengths;
  std::array<int,3> cardinality{};std::array<S128,3> object_sum{};
  std::array<S128,6> actor_sum{};
  for(const auto&x:labels) {
   if(x.node<0||x.old_owner<0||x.old_owner>=3||x.weight<=0)
    throw std::runtime_error("ledger invalid positive record");
   const int owner=x.old_owner;
   if(cardinality[owner]>=2)throw std::runtime_error("ledger object cardinality");
   original[2*owner+cardinality[owner]++]={x.node,x.weight};object_sum[owner]+=S128(x.weight);
   int a=0;while(a<d.actor_count&&d.actors[a].node!=x.node)++a;
   if(a==d.actor_count){d.actors[a].node=x.node;++d.actor_count;}
   ++d.actors[a].degree;actor_sum[a]+=S128(x.weight);
  }
  S128 total_object=0,total_actor=0;
  for(int owner=0;owner<3;++owner) {
   if(cardinality[owner]!=2||original[2*owner].node==original[2*owner+1].node||
      strengths[owner]<2||object_sum[owner]!=S128(strengths[owner]))
    throw std::runtime_error("ledger original object ledger");
   if(cell_less(original[2*owner+1],original[2*owner]))
    std::swap(original[2*owner],original[2*owner+1]);
   total_object+=object_sum[owner];
  }
  for(int a=0;a<d.actor_count;++a) {
   d.actors[a].strength=checked_I(actor_sum[a]);total_actor+=actor_sum[a];
   if(d.actors[a].degree<1||d.actors[a].degree>3||d.actors[a].strength<d.actors[a].degree)
    throw std::runtime_error("ledger actor ledger");
   d.all_actor_degree_one&=d.actors[a].degree==1;
  }
  if(total_object!=total_actor||d.actor_count<2||d.actor_count>6)
   throw std::runtime_error("ledger balanced six-edge descriptor");
   
  std::sort(d.actors.begin(),d.actors.begin()+d.actor_count,
            [](const Actor&a,const Actor&b){return a.node<b.node;});
  return d;
 }

 static Wide bounded_three(S128 A,const std::array<S128,3>&lo,
                           const std::array<S128,3>&hi) {
  if(A<0||A>S128(std::numeric_limits<I>::max()))throw std::runtime_error("ledger bounded-count actor range");
  S128 R=A;for(int j=0;j<3;++j){if(hi[j]<lo[j])return 0;
   if(lo[j]<1||hi[j]>S128(std::numeric_limits<I>::max()))throw std::runtime_error("ledger positive interval range");
   R-=lo[j];}
  if(R<0)return 0;
  S128 result=0;
  for(unsigned mask=0;mask<8;++mask) {
   S128 t=R;unsigned parity=0;
   for(int j=0;j<3;++j)if(mask&(1U<<j)){t-=hi[j]-lo[j]+1;++parity;}
   if(t<0)continue;
   const S128 n=t+2,term=n*(n-1)/2;
   if(parity&1)result-=term;else result+=term;
  }
  if(result<0)throw std::runtime_error("ledger negative bounded count");
  return Wide(result);
 }

 static Plan completion_plan(const Descriptor&d,const Support&support) {
  Plan p;p.support=support;
  std::array<int,6> u{},v{};std::array<bool,6> live{};live.fill(true);
  std::array<int,9> degree{};std::array<S128,9> residual{};
  const int vertices=3+d.actor_count;
  for(int j=0;j<3;++j)residual[j]=d.strengths[j];
  for(int a=0;a<d.actor_count;++a)residual[3+a]=d.actors[a].strength;
  for(int e=0;e<6;++e) {
   u[e]=e/2;v[e]=3+actor_index(d,support[e]);++degree[u[e]];++degree[v[e]];
  }
  for(int j=0;j<3;++j)if(support[2*j]>=support[2*j+1])
   throw std::runtime_error("ledger noncanonical support/object collision");
  for(int a=0;a<d.actor_count;++a)if(degree[3+a]!=d.actors[a].degree)
   throw std::runtime_error("ledger support actor degree");
  for(int z=0;z<vertices;++z)if(residual[z]<degree[z])return p;
   
  for(;;) {
   int leaf=-1;for(int z=0;z<vertices;++z)if(degree[z]==1){leaf=z;break;}
   if(leaf<0)break;
   int edge=-1;for(int e=0;e<6;++e)if(live[e]&&(u[e]==leaf||v[e]==leaf)){edge=e;break;}
   if(edge<0)throw std::runtime_error("ledger leaf incidence");
   const S128 weight=residual[leaf];if(weight<1||weight>S128(std::numeric_limits<I>::max()))return p;
   const int other=u[edge]==leaf?v[edge]:u[edge];p.base[edge]=weight;
   residual[leaf]=0;residual[other]-=weight;live[edge]=false;--degree[leaf];--degree[other];
   if(residual[other]<degree[other]||(degree[other]==0&&residual[other]!=0))return p;
  }
  int remaining=0;for(bool x:live)remaining+=x;
  for(int z=0;z<vertices;++z)if(degree[z]==0&&residual[z]!=0)return p;
  if(!remaining){p.kind=FOREST;p.count=1;return p;}
  if(remaining==6&&d.actor_count==2) {
   if(degree[3]!=3||degree[4]!=3)throw std::runtime_error("ledger rank-two K23 classification");
   p.kind=K23;std::array<S128,3> lo={1,1,1},hi{};
   for(int j=0;j<3;++j)hi[j]=S128(d.strengths[j])-1;
   p.count=bounded_three(d.actors[0].strength,lo,hi);return p;
  }
   
  if(remaining!=4&&remaining!=6)throw std::runtime_error("ledger unsupported core classification");
  for(int z=0;z<vertices;++z)if(degree[z]&&degree[z]!=2)
   throw std::runtime_error("ledger noncycle core");
  int pivot=-1;for(int e=0;e<6;++e)if(live[e]){pivot=e;break;}
  p.base[pivot]=0;p.sign[pivot]=1;
  for(int pass=0;pass<6;++pass) {
   bool changed=false;
   for(int z=0;z<vertices;++z)if(degree[z]==2) {
    int a=-1,b=-1;for(int e=0;e<6;++e)if(live[e]&&(u[e]==z||v[e]==z)){if(a<0)a=e;else b=e;}
    if(a<0||b<0)throw std::runtime_error("ledger cycle incidence");
    if(p.sign[a]&&!p.sign[b]){p.sign[b]=-p.sign[a];p.base[b]=residual[z]-p.base[a];changed=true;}
    else if(p.sign[b]&&!p.sign[a]){p.sign[a]=-p.sign[b];p.base[a]=residual[z]-p.base[b];changed=true;}
    else if(p.sign[a]&&p.sign[b]&&
            (p.sign[a]+p.sign[b]!=0||p.base[a]+p.base[b]!=residual[z]))return p;
   }
   if(!changed)break;
  }
  const S128 imax=std::numeric_limits<I>::max();p.lower=1;p.upper=imax;
  for(int e=0;e<6;++e)if(live[e]) {
   if(!p.sign[e])throw std::runtime_error("ledger disconnected multi-cycle core");
   if(p.sign[e]==1){p.lower=std::max(p.lower,S128(1)-p.base[e]);p.upper=std::min(p.upper,imax-p.base[e]);}
   else{p.lower=std::max(p.lower,p.base[e]-imax);p.upper=std::min(p.upper,p.base[e]-1);}
  }
  p.kind=CYCLE;if(p.lower<=p.upper)p.count=Wide(p.upper-p.lower+1);return p;
 }

 static Fiber enumerate(const std::array<Label,6>&labels,const std::array<I,3>&strengths) {
  Fiber f;f.descriptor=describe(labels,strengths,f.original);const auto&d=f.descriptor;
  std::array<int,6> tickets{};int position=0;
  for(int a=0;a<d.actor_count;++a)for(int k=0;k<d.actors[a].degree;++k)tickets[position++]=d.actors[a].node;
  if(position!=6)throw std::runtime_error("ledger six actor tickets");
  std::array<Support,90> supports{};U raw=0;

  std::array<std::array<S128,6>,6> pair_sum{};
  if(d.all_actor_degree_one)for(int a=0;a<6;++a)for(int b=a+1;b<6;++b)
   pair_sum[a][b]=S128(d.actors[a].strength)+d.actors[b].strength;
  for(int a=0;a<6;++a)for(int b=a+1;b<6;++b) {
   if(tickets[a]==tickets[b]||(d.all_actor_degree_one&&pair_sum[a][b]!=strengths[0]))continue;
   for(int c=0;c<6;++c)if(c!=a&&c!=b)
    for(int e=c+1;e<6;++e)if(e!=a&&e!=b) {
     if(tickets[c]==tickets[e]||(d.all_actor_degree_one&&pair_sum[c][e]!=strengths[1]))continue;
     std::array<int,2> rest{};int k=0;
     for(int z=0;z<6;++z)if(z!=a&&z!=b&&z!=c&&z!=e)rest[k++]=z;
     if(k!=2)throw std::runtime_error("ledger forced ticket pair");
     if(tickets[rest[0]]==tickets[rest[1]]||
        (d.all_actor_degree_one&&pair_sum[rest[0]][rest[1]]!=strengths[2]))continue;
     if(raw>=90)throw std::runtime_error("ledger ticket support bound");
     supports[size_t(raw++)]={tickets[a],tickets[b],tickets[c],tickets[e],tickets[rest[0]],tickets[rest[1]]};
    }
  }
  auto end=supports.begin()+std::ptrdiff_t(raw);std::sort(supports.begin(),end);
  const U unique=U(std::unique(supports.begin(),end)-supports.begin());
  Support original_support{};for(int e=0;e<6;++e)original_support[e]=f.original[e].node;
  bool found_original=false;
  for(U k=0;k<unique;++k) {
   Plan p;
   if(d.all_actor_degree_one) {
    p.support=supports[size_t(k)];p.kind=FOREST;p.count=1;
    for(int e=0;e<6;++e)p.base[e]=d.actors[actor_index(d,p.support[e])].strength;
   } else p=completion_plan(d,supports[size_t(k)]);
   ++f.supports_examined;if(!p.count)continue;
   found_original|=p.support==original_support;
   f.forest_supports+=p.kind==FOREST;f.cycle_supports+=p.kind==CYCLE;f.rank2_supports+=p.kind==K23;
   if(f.total>Wide(-1)-p.count)throw std::runtime_error("ledger unsigned128 count overflow");
   f.total+=p.count;f.plans[size_t(f.size++)]=p;
  }
  if(!f.size||!f.total||!found_original)throw std::runtime_error("ledger complete fiber/current support");
  if(f.rank2_supports&&(f.size!=1||d.actor_count!=2))
   throw std::runtime_error("ledger rank-two support must be unique");
  return f;
 }

 static Table unrank_plan(const Descriptor&d,const Plan&p,Wide rank) {
  if(rank>=p.count)throw std::runtime_error("ledger completion rank outside support count");
  Table out{};std::array<S128,6> weights=p.base;
  if(p.kind==CYCLE) {
   const S128 t=p.lower+S128(rank);
   for(int e=0;e<6;++e)if(p.sign[e])weights[e]=p.base[e]+p.sign[e]*t;
  } else if(p.kind==K23) {
   const S128 A=d.actors[0].strength;
   std::array<S128,3> lo={1,1,1},hi{};for(int j=0;j<3;++j)hi[j]=S128(d.strengths[j])-1;
   S128 left=1,right=hi[0];
   while(left<right) {
    const S128 mid=left+(right-left)/2;auto prefix_hi=hi;prefix_hi[0]=mid;
    if(rank<bounded_three(A,lo,prefix_hi))right=mid;else left=mid+1;
   }
   const S128 x0=left;auto before_hi=hi;before_hi[0]=x0-1;
   const Wide before=bounded_three(A,lo,before_hi);
   if(before>rank)throw std::runtime_error("ledger prefix unrank underflow");
   rank-=before;const S128 rest=A-x0;
   const S128 low1=std::max(S128(1),rest-hi[2]),high1=std::min(hi[1],rest-1);
   if(high1<low1||rank>=Wide(high1-low1+1))throw std::runtime_error("ledger residual interval rank");
   const S128 x1=low1+S128(rank);const std::array<S128,3>x={x0,x1,rest-x1};
   for(int j=0;j<3;++j)for(int e=2*j;e<2*j+2;++e)
    weights[e]=p.support[e]==d.actors[0].node?x[j]:S128(d.strengths[j])-x[j];
  } else if(p.kind!=FOREST)throw std::runtime_error("ledger empty completion plan");
  std::array<S128,3> row_sum{};std::array<S128,6> actor_sum{};std::array<int,6>actor_degree{};
  for(int e=0;e<6;++e) {
   if(weights[e]<1)throw std::runtime_error("ledger nonpositive unrank completion");
   out[e]={p.support[e],checked_I(weights[e])};row_sum[e/2]+=weights[e];
   const int a=actor_index(d,p.support[e]);actor_sum[a]+=weights[e];++actor_degree[a];
  }
  for(int j=0;j<3;++j)if(row_sum[j]!=S128(d.strengths[j]))throw std::runtime_error("ledger unrank object strength");
  for(int a=0;a<d.actor_count;++a)if(actor_sum[a]!=S128(d.actors[a].strength)||actor_degree[a]!=d.actors[a].degree)
   throw std::runtime_error("ledger unrank actor ledger");
  return out;
 }
 static Table unrank(const Fiber&f,Wide rank) {
  if(rank>=f.total)throw std::runtime_error("ledger global rank outside fiber");
  for(U k=0;k<f.size;++k) {
   const auto&p=f.plans[size_t(k)];if(rank<p.count)return unrank_plan(f.descriptor,p,rank);rank-=p.count;
  }
  throw std::runtime_error("ledger weighted support rank missing");
 }
 static Wide below(Engine&e,Wide bound) {
  if(!bound)throw std::runtime_error("ledger zero random bound");
  if(bound<=Wide(std::numeric_limits<U>::max()))return Wide(e.rng.below(U(bound)));
   
  const Wide threshold=(Wide(0)-bound)%bound;
  for(;;) {
   Wide word=0;for(int j=0;j<4;++j)word=(word<<32)|Wide(e.rng.below(U(1)<<32));
   if(word>=threshold)return word%bound;
  }
 }
 static Wide count_axis_groups(U n) {
  if(n<3)return 0;
  Wide a=n,b=n-1,c=n-2;
  if((a&1)==0)a/=2;else if((b&1)==0)b/=2;else c/=2;
  if(a%3==0)a/=3;else if(b%3==0)b/=3;else c/=3;
  if(a>Wide(-1)/b||a*b>Wide(-1)/c)throw std::runtime_error("ledger axis-group U128 range");
  return a*b*c;
 }

 void initialize(const Graph&g,bool want) {
  requested=want;if(!want)return;rows=g.nr;columns=g.nc;
  if(g.D)throw std::runtime_error("ledger initialization outside exact margins");
  for(int axis=0;axis<2;++axis) {
   const int n=axis?g.nc:g.nr,opposite=axis?g.nr:g.nc,offset=axis?g.nr:0;
   if(opposite<2)continue;
   U count=0;for(int v=0;v<n;++v)count+=g.target_degree[offset+v]==2;
   if(count<3)continue;
   auto&pool=objects[axis];pool.reserve(size_t(count));
   for(int v=0;v<n;++v)if(g.target_degree[offset+v]==2)pool.push_back(v);
   axis_active[axis]=true;active=true;axis_groups[axis]=count_axis_groups(count);
  }
  total_groups=axis_groups[0]+axis_groups[1];
 }
 void check(const Graph&g) {
  if(!requested)return;++index_checks;
  if(g.nr!=rows||g.nc!=columns||g.D)throw std::runtime_error("ledger graph/degree audit");
  for(int axis=0;axis<2;++axis) {
   const int n=axis?g.nc:g.nr,opposite=axis?g.nr:g.nc,offset=axis?g.nr:0;
   U count=0;for(int v=0;v<n;++v)count+=g.target_degree[offset+v]==2;
   const bool expected=opposite>=2&&count>=3;
   if(axis_active[axis]!=expected||(expected&&objects[axis].size()!=count)||(!expected&&!objects[axis].empty()))
    throw std::runtime_error("ledger static target pool cardinality");
   if(axis_groups[axis]!=(expected?count_axis_groups(count):Wide(0)))
    throw std::runtime_error("ledger static axis-window count");
   if(expected){U k=0;for(int v=0;v<n;++v)if(g.target_degree[offset+v]==2)
    if(objects[axis].at(size_t(k++))!=v||g.degree[offset+v]!=2||g.adj[offset+v].size()!=2)
     throw std::runtime_error("ledger static target pool labels");}
  }
  if(active!=(axis_active[0]||axis_active[1])||total_groups!=axis_groups[0]+axis_groups[1]||active!=(total_groups!=0))
   throw std::runtime_error("ledger active/window count audit");
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
  const Fiber fiber=enumerate(labels,strengths);const auto&d=fiber.descriptor;
  repeated_opposite_triples+=d.actor_count<6;fast_leaf_calls+=d.all_actor_degree_one;
  supports_examined+=fiber.supports_examined;forest_supports+=fiber.forest_supports;
  cycle_supports+=fiber.cycle_supports;rank2_supports+=fiber.rank2_supports;
  max_fiber_count=std::max(max_fiber_count,fiber.total);
  if(fiber.total==1){++singleton_holds;++selected_original;return false;}
  const Table chosen=unrank(fiber,below(e,fiber.total));++rank_draws;
  if(table_equal(chosen,fiber.original)){++selected_original;return false;}
  auto value=[&](int owner,int node){return axis?g.value(node,nodes[owner]):g.value(nodes[owner],node);};
  auto put=[&](int owner,const Cell&cell,I weight){
   if(axis)g.set_raw(cell.node,nodes[owner],weight);else g.set_raw(nodes[owner],cell.node,weight);++cell_writes;};
  for(int a=0;a<d.actor_count;++a) {
   const int v=axis?d.actors[a].node:g.nr+d.actors[a].node;
   if(g.degree[v]!=g.target_degree[v]||g.adj[v].size()!=U(g.degree[v])||d.actors[a].strength>g.target_strength[v])
    throw std::runtime_error("ledger actor precommit margin");
   for(int owner=0;owner<3;++owner){I expected=0;
    for(int t=2*owner;t<2*owner+2;++t)if(fiber.original[t].node==d.actors[a].node)expected=fiber.original[t].weight;
    if(value(owner,d.actors[a].node)!=expected)throw std::runtime_error("ledger complete-table collision");}
  }
  const U old_edges=U(g.edges.size());

  for(int owner=0;owner<3;++owner)for(int t=2*owner;t<2*owner+2;++t)put(owner,fiber.original[t],0);
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
  f<<"\"LB_requested\":"<<(requested?"true":"false")<<",\"LB_active\":"<<(active?"true":"false")
   <<",\"LB_row_axis_active\":"<<(axis_active[0]?"true":"false")<<",\"LB_column_axis_active\":"<<(axis_active[1]?"true":"false")
   <<",\"LB_compose_calls\":"<<compose_calls<<",\"LB_no_static_candidates\":"<<no_static_candidates
   <<",\"LB_uniform_block_calls\":"<<uniform_block_calls<<",\"LB_both_axis_calls\":"<<both_axis_calls
   <<",\"LB_row_window_groups\":\""<<decimal(axis_groups[0])<<"\",\"LB_column_window_groups\":\""<<decimal(axis_groups[1])
   <<"\",\"LB_total_window_groups\":\""<<decimal(total_groups)<<"\""
   <<",\"LB_row_axis_calls\":"<<axis_calls[0]<<",\"LB_column_axis_calls\":"<<axis_calls[1]
   <<",\"LB_changes\":"<<changes<<",\"LB_row_changes\":"<<axis_changes[0]<<",\"LB_column_changes\":"<<axis_changes[1]
   <<",\"LB_selected_triples\":"<<selected_triples<<",\"LB_repeated_opposite_triples\":"<<repeated_opposite_triples
   <<",\"LB_fast_leaf_calls\":"<<fast_leaf_calls<<",\"LB_supports_examined\":"<<supports_examined
   <<",\"LB_forest_supports\":"<<forest_supports<<",\"LB_cycle_supports\":"<<cycle_supports
   <<",\"LB_rank2_supports\":"<<rank2_supports<<",\"LB_max_fiber_count\":\""<<decimal(max_fiber_count)<<"\""
   <<",\"LB_singleton_holds\":"<<singleton_holds<<",\"LB_rank_draws\":"<<rank_draws
   <<",\"LB_selected_original\":"<<selected_original<<",\"LB_cell_writes\":"<<cell_writes<<",\"LB_index_checks\":"<<index_checks
   <<",\"LB_policy\":\"default one uniform fixed degree2 triple over both axes, axis weight C(poolsize,3); outside and actor local degree/strength fixed; canonical supports weighted by exact positive-integer completions; forest peeling, one-cycle interval, unique K23 bounded-three count; optional explicit dual-axis composition; no retry or live index\",";
 }
};
