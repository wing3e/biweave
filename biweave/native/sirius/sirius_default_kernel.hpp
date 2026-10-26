#pragma once

struct SiriusDefaultTraceKernel {
 struct Undo {int i,j,k,l;I a,b,c,d;U first,second;std::pair<int,int>old_first,old_second;};
 std::vector<std::pair<int,int>>occurrences;std::vector<Undo>path;
 std::unordered_map<U,I>initial_cells;
 U outer_calls=0,soft_calls=0,soft_accepted=0,soft_lazy=0,mh_rejected=0,nonchanging=0;
 U returned=0,killed=0,changed=0,undo_moves=0,max_soft_steps=0;
 static constexpr U occurrence_limit=80000000;
 U kill_denominator;
 explicit SiriusDefaultTraceKernel(const Graph&g,U kill_den=20):kill_denominator(kill_den){
  if(!kill_denominator)throw std::runtime_error("positive geometric kill denominator required");
  U total=0;for(const auto&ed:g.edges){if(U(ed.w)>occurrence_limit-total)throw std::runtime_error("Sirius occurrence-list memory limit: total weight exceeds80000000");total+=U(ed.w);}
  occurrences.reserve(total);for(const auto&ed:g.edges)for(I k=0;k<ed.w;++k)occurrences.emplace_back(ed.r,ed.c);
 }
 static void set_four(Graph&g,const Undo&u,I a,I b,I c,I d){
  std::array<int,4>nodes{u.i,u.k,g.nr+u.j,g.nr+u.l};
  for(int v:nodes)g.D-=std::abs(g.degree[v]-g.target_degree[v]);
  g.set_raw(u.i,u.j,a);g.set_raw(u.k,u.l,b);g.set_raw(u.i,u.l,c);g.set_raw(u.k,u.j,d);
  for(int v:nodes)g.D+=std::abs(g.degree[v]-g.target_degree[v]);
  if(g.D<0)throw std::runtime_error("negative degree discrepancy");
 }
 template<class Random> bool soft_step(Random&rng,Graph&g,Counters&stat,Undo&u){
  ++soft_calls;++stat.work;
  if(occurrences.size()<2){++nonchanging;return false;}
  U first=rng.below(occurrences.size()),second=first;
  while(second==first)second=rng.below(occurrences.size());
  auto[i,j]=occurrences[first];auto[k,l]=occurrences[second];
  if(i==k||j==l){++nonchanging;return false;}
  I a=g.value(i,j),b=g.value(k,l),c=g.value(i,l),d=g.value(k,j);
  if(a<=0||b<=0)throw std::runtime_error("Sirius stale occurrence list");
  U numerator=U(c+1)*U(d+1),denominator=U(a)*U(b);
  if(numerator<denominator&&rng.below(denominator)>=numerator){++mh_rejected;return false;}
   
  u={i,j,k,l,a,b,c,d,first,second,occurrences[first],occurrences[second]};
  set_four(g,u,a-1,b-1,c+1,d+1);occurrences[first]={i,l};occurrences[second]={k,j};
  ++soft_accepted;return true;
 }
 void remember_initial(const Undo&u){
  initial_cells.emplace(cellkey(u.i,u.j),u.a);initial_cells.emplace(cellkey(u.k,u.l),u.b);
  initial_cells.emplace(cellkey(u.i,u.l),u.c);initial_cells.emplace(cellkey(u.k,u.j),u.d);
 }
 void rollback(Graph&g){
  for(auto it=path.rbegin();it!=path.rend();++it){const Undo&u=*it;
   set_four(g,u,u.a,u.b,u.c,u.d);occurrences[u.first]=u.old_first;occurrences[u.second]=u.old_second;++undo_moves;
  }
  if(g.D)throw std::runtime_error("Sirius trace rollback did not restore F");
  for(const auto&kv:initial_cells)if(g.value(int(kv.first>>32),int(uint32_t(kv.first)))!=kv.second)throw std::runtime_error("Sirius trace rollback cell mismatch");
 }

 template<class Random> bool step(Random&rng,Graph&g,Counters&stat){
  if(g.D)throw std::runtime_error("Sirius trace must start in F");
  ++outer_calls;path.clear();initial_cells.clear();U steps=0;
  for(;;){
   Undo u{};++steps;bool move=soft_step(rng,g,stat,u);
   if(move){remember_initial(u);path.push_back(u);}
   if(g.D==0){
    ++returned;max_soft_steps=std::max(max_soft_steps,steps);bool differs=false;
    for(const auto&kv:initial_cells)differs|=g.value(int(kv.first>>32),int(uint32_t(kv.first)))!=kv.second;
    if(differs){++changed;++stat.changed_outer;}return differs;
   }

   if(kill_denominator==1||rng.below(kill_denominator)==0){
    rollback(g);++killed;max_soft_steps=std::max(max_soft_steps,steps);return false;
   }
  }
 }
 bool check_occurrences(const Graph&g)const{
  std::unordered_map<U,U>counts;
  for(auto[r,c]:occurrences){if(r<0||r>=g.nr||c<0||c>=g.nc)return false;++counts[cellkey(r,c)];}
  if(counts.size()!=g.edges.size())return false;
  for(const auto&e:g.edges){auto it=counts.find(cellkey(e.r,e.c));if(it==counts.end()||it->second!=U(e.w))return false;}
  return true;
 }
};
