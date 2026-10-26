#pragma once

struct VaLUHDTraceKernel {
 struct Undo {int i,j,k,l;I a,b,c,d;};
 std::vector<Undo>path;
 std::unordered_map<U,I>initial_cells;
 U outer_calls=0,soft_calls=0,soft_accepted=0,soft_lazy=0,mh_rejected=0,nonchanging=0;
 U returned=0,killed=0,changed=0,undo_moves=0,max_soft_steps=0;
 U pair_shared_endpoint=0,matching_identity=0,matching_nonbipartite=0,matching_cross=0;
 U mh_type_increase=0,mh_type_same=0,mh_type_decrease=0;
 U kill_denominator;
 explicit VaLUHDTraceKernel(const Graph&g,U kill_den=20):kill_denominator(kill_den){
  if(!kill_denominator)throw std::runtime_error("positive geometric kill denominator required");
  if(g.edges.size()>U(std::numeric_limits<int>::max()))throw std::runtime_error("dyad type count exceeds Graph index range");
 }
 static void set_four(Graph&g,const Undo&u,I a,I b,I c,I d){
  std::array<int,4>nodes{u.i,u.k,g.nr+u.j,g.nr+u.l};
  for(int v:nodes)g.D-=std::abs(g.degree[v]-g.target_degree[v]);
  g.set_raw(u.i,u.j,a);g.set_raw(u.k,u.l,b);g.set_raw(u.i,u.l,c);g.set_raw(u.k,u.j,d);
  for(int v:nodes)g.D+=std::abs(g.degree[v]-g.target_degree[v]);
  if(g.D<0)throw std::runtime_error("negative degree discrepancy");
 }
 template<class Random>bool soft_step(Random&rng,Graph&g,Counters&stat,Undo&u){
  ++soft_calls;++stat.work;
  const U K=U(g.edges.size());
   
  if(K<2){++nonchanging;return false;}
  U first=rng.below(K),second=rng.below(K-1);if(second>=first)++second;
  const Edge first_edge=g.edges[first],second_edge=g.edges[second];
  int i=first_edge.r,j=first_edge.c,k=second_edge.r,l=second_edge.c;
  if(i==k||j==l){++pair_shared_endpoint;++nonchanging;return false;}
  U matching=rng.below(3);
  if(matching==0){++matching_identity;++nonchanging;return false;}
  if(matching==1){++matching_nonbipartite;++nonchanging;return false;}
  ++matching_cross;
  I a=g.value(i,j),b=g.value(k,l),c=g.value(i,l),d=g.value(k,j);
  if(a<=0||b<=0)throw std::runtime_error("stale positive dyad type");
  if(c==std::numeric_limits<I>::max()||d==std::numeric_limits<I>::max())throw std::runtime_error("weight overflow");
  const U Knext=K-U(a==1)-U(b==1)+U(c==0)+U(d==0);
  if(Knext<2||Knext>U(std::numeric_limits<int>::max()))throw std::runtime_error("invalid proposed type count");
  U numerator=K*(K-1),denominator=Knext*(Knext-1);
  if(Knext>K)++mh_type_increase;else if(Knext==K)++mh_type_same;else ++mh_type_decrease;

  if(numerator<denominator&&rng.below(denominator)>=numerator){++mh_rejected;return false;}
  u={i,j,k,l,a,b,c,d};set_four(g,u,a-1,b-1,c+1,d+1);
  if(g.edges.size()!=Knext)throw std::runtime_error("proposed type count mismatch");
  ++soft_accepted;return true;
 }
 void remember_initial(const Undo&u){
  initial_cells.emplace(cellkey(u.i,u.j),u.a);initial_cells.emplace(cellkey(u.k,u.l),u.b);
  initial_cells.emplace(cellkey(u.i,u.l),u.c);initial_cells.emplace(cellkey(u.k,u.j),u.d);
 }
 void rollback(Graph&g){
  for(auto it=path.rbegin();it!=path.rend();++it){const Undo&u=*it;set_four(g,u,u.a,u.b,u.c,u.d);++undo_moves;}
  if(g.D)throw std::runtime_error("VaLUH-d trace rollback did not restore F");
  for(const auto&kv:initial_cells)if(g.value(int(kv.first>>32),int(uint32_t(kv.first)))!=kv.second)throw std::runtime_error("VaLUH-d rollback cell/type mismatch");
 }
 template<class Random>bool step(Random&rng,Graph&g,Counters&stat){
  if(g.D)throw std::runtime_error("VaLUH-d trace must start in F");
  ++outer_calls;path.clear();initial_cells.clear();U steps=0;
  for(;;){
   Undo u{};++steps;bool move=soft_step(rng,g,stat,u);
   if(move){remember_initial(u);path.push_back(u);}
   if(g.D==0){
    ++returned;max_soft_steps=std::max(max_soft_steps,steps);bool differs=false;
    for(const auto&kv:initial_cells)differs|=g.value(int(kv.first>>32),int(uint32_t(kv.first)))!=kv.second;
    if(differs){++changed;++stat.changed_outer;}return differs;
   }
   if(kill_denominator==1||rng.below(kill_denominator)==0){rollback(g);++killed;max_soft_steps=std::max(max_soft_steps,steps);return false;}
  }
 }
 bool check_types(const Graph&g)const{
  std::unordered_set<U>keys;for(size_t t=0;t<g.edges.size();++t){const auto&e=g.edges[t];
   if(e.w<=0||e.r<0||e.r>=g.nr||e.c<0||e.c>=g.nc||g.find(e.r,e.c)!=int(t)||!keys.insert(cellkey(e.r,e.c)).second)return false;
  }return keys.size()==g.lookup.size();
 }
};
