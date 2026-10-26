#pragma once

struct CohortEligibleRootIndex {
 static constexpr U MEMORY_BUDGET=64ULL*1024*1024;
 Graph* graph=nullptr;bool active=false;
 void* previous_context=nullptr;void(*previous_hook)(void*,int,int,I,I)=nullptr;
 std::vector<U>leaf_count,eligible_actor_count;
 std::vector<int>pool,position;
 U initial_roots=0,payload_bytes=0,support_calls=0,flag_transitions=0,neighbor_visits=0,adds=0,removes=0;
 mutable U checks=0,checked_edges=0;double build_cpu_seconds=0;
 static double cpu(){timespec ts{};if(clock_gettime(CLOCK_PROCESS_CPUTIME_ID,&ts))throw std::runtime_error("eligible-root clock");return ts.tv_sec+1e-9*ts.tv_nsec;}
 static int opposite(const Graph&g,const Edge&edge,int vertex){return vertex<g.nr?g.nr+edge.c:edge.r;}
 bool eligible(int v)const{return graph->target_degree[v]>=2&&eligible_actor_count[v]>=2;}
 void refresh(int v){
  const bool want=eligible(v),present=position[v]>=0;
  if(want==present)return;
  if(want){position[v]=int(pool.size());pool.push_back(v);++adds;}
  else{const int at=position[v],last=pool.back();pool[at]=last;position[last]=at;pool.pop_back();position[v]=-1;++removes;}
 }
 void adjust(int v,int delta){
  if(delta<0){if(!eligible_actor_count[v])throw std::runtime_error("eligible actor count underflow");--eligible_actor_count[v];}
  else ++eligible_actor_count[v];
  refresh(v);
 }
 void propagate(int v,int excluded,int delta){
  for(int id:graph->adj[v]){++neighbor_visits;const int next=opposite(*graph,graph->edges[id],v);if(next!=excluded)adjust(next,delta);}
 }

 void update(int r,int c,I old,I now){
  if((old>0)==(now>0))throw std::runtime_error("eligible-root non-support event");
  ++support_calls;const int u=r,v=graph->nr+c;const bool before_u=leaf_count[u]>0,before_v=leaf_count[v]>0;
  const bool adding=now>0;
  if(!adding){if(before_v)adjust(u,-1);if(before_u)adjust(v,-1);}
  auto change_leaf=[&](int actor,int neighbor){if(graph->target_degree[neighbor]!=1)return;if(adding)++leaf_count[actor];else{if(!leaf_count[actor])throw std::runtime_error("leaf count underflow");--leaf_count[actor];}};
  change_leaf(u,v);change_leaf(v,u);
  const bool after_u=leaf_count[u]>0,after_v=leaf_count[v]>0;
  if(before_u!=after_u){++flag_transitions;propagate(u,adding?-1:v,after_u?1:-1);}
  if(before_v!=after_v){++flag_transitions;propagate(v,adding?-1:u,after_v?1:-1);}
  if(adding){if(after_v)adjust(u,1);if(after_u)adjust(v,1);}
 }
 static void mutation(void*ctx,int r,int c,I old,I now){
  auto&self=*static_cast<CohortEligibleRootIndex*>(ctx);
  if(self.previous_hook)self.previous_hook(self.previous_context,r,c,old,now);
  self.update(r,c,old,now);
 }
 void initialize(Graph&g,bool requested){
  if(!requested)return;if(active||graph)throw std::runtime_error("eligible-root double initialize");
  const U vertices=U(g.nr)+U(g.nc);
  const __uint128_t bound=__uint128_t(vertices)*(2*sizeof(U)+2*sizeof(int));
  if(bound>MEMORY_BUDGET||vertices>U(std::numeric_limits<int>::max()))throw std::runtime_error("eligible-root static index memory guard");
  const double begin=cpu();graph=&g;leaf_count.assign(vertices,0);eligible_actor_count.assign(vertices,0);position.assign(vertices,-1);pool.reserve(vertices);
  for(const Edge&edge:g.edges){const int u=edge.r,v=g.nr+edge.c;if(g.target_degree[v]==1)++leaf_count[u];if(g.target_degree[u]==1)++leaf_count[v];}
  for(const Edge&edge:g.edges){const int u=edge.r,v=g.nr+edge.c;eligible_actor_count[u]+=leaf_count[v]>0;eligible_actor_count[v]+=leaf_count[u]>0;}
  for(int v=0;v<int(vertices);++v)refresh(v);
  initial_roots=pool.size();payload_bytes=leaf_count.capacity()*sizeof(U)+eligible_actor_count.capacity()*sizeof(U)+position.capacity()*sizeof(int)+pool.capacity()*sizeof(int);
  if(payload_bytes>MEMORY_BUDGET)throw std::runtime_error("eligible-root actual index memory guard");
  previous_context=g.support_mutation_context;previous_hook=g.support_mutation_hook;
  g.support_mutation_context=this;g.support_mutation_hook=&CohortEligibleRootIndex::mutation;active=true;build_cpu_seconds=cpu()-begin;
 }
 int draw(RNG&rng)const{if(!active)throw std::runtime_error("inactive eligible-root index");return pool.empty()?-1:pool[rng.below(pool.size())];}
 void check(const Graph&g)const{
  if(!active)return;if(&g!=graph)throw std::runtime_error("eligible-root graph moved");++checks;
  const U vertices=U(g.nr)+U(g.nc);std::vector<U>l(vertices,0),e(vertices,0);std::vector<bool>seen(vertices,false);
  for(const Edge&edge:g.edges){++checked_edges;const int u=edge.r,v=g.nr+edge.c;if(g.target_degree[v]==1)++l[u];if(g.target_degree[u]==1)++l[v];}
  for(const Edge&edge:g.edges){const int u=edge.r,v=g.nr+edge.c;e[u]+=l[v]>0;e[v]+=l[u]>0;}
  if(l!=leaf_count||e!=eligible_actor_count)throw std::runtime_error("eligible-root count differs from fresh graph");
  for(U i=0;i<pool.size();++i){const int v=pool[i];if(v<0||U(v)>=vertices||seen[v]||position[v]!=int(i)||!eligible(v))throw std::runtime_error("eligible-root pool corrupt");seen[v]=true;}
  for(U v=0;v<vertices;++v)if(seen[v]!=eligible(int(v))||((position[v]>=0)!=seen[v]))throw std::runtime_error("eligible-root pool incomplete");
 }
};
