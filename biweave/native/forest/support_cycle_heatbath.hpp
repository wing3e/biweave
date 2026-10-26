#pragma once

struct SupportCycleHeatbath {
 bool margin_certified_forest=false,maximum_degree2=true;
 U calls=0,forest_skips=0,no_cycle=0,changed=0,cycle_edges=0,rebuilds=0;
 std::vector<int>parent,depth,parent_edge,chords;
 std::vector<U>stamp;std::vector<int>position;U generation=0;
 U last_inserts=std::numeric_limits<U>::max(),last_deletes=std::numeric_limits<U>::max();
 explicit SupportCycleHeatbath(const Graph&g){
  for(int d:g.target_degree)maximum_degree2&=d<=2;

  for(int side=0;side<2;++side){int count=side?g.nc:g.nr,off=side?g.nr:0,high=0;
   for(int v=0;v<count;++v)high+=g.target_degree[off+v]>1;
   margin_certified_forest|=high<=1;
  }
  if(!maximum_degree2&&!margin_certified_forest){stamp.assign(g.nr+g.nc,0);position.resize(g.nr+g.nc);}
 }
 void refresh_line(Engine&e,Graph&g,const std::vector<int>&cycle){
  if(cycle.size()<4||cycle.size()%2)throw std::runtime_error("invalid support cycle");
  I low=std::numeric_limits<I>::min()+1,high=std::numeric_limits<I>::max();
  for(size_t j=0;j<cycle.size();++j){I w=g.edges[cycle[j]].w;
   if(j%2)high=std::min(high,w-1);else low=std::max(low,1-w);}
  I delta=e.rng.integer(low,high);cycle_edges+=cycle.size();
  if(!delta)return;
  for(size_t j=0;j<cycle.size();++j){auto x=g.edges[cycle[j]];g.set_raw(x.r,x.c,x.w+(j%2?-delta:delta));}
  changed++;e.stat.changed_outer++;
 }
 void rebuild(const Graph&g,const Counters&stat){
  int nv=g.nr+g.nc;std::vector<int>dsu(nv),size(nv,1),ids(g.edges.size());
  for(int v=0;v<nv;++v)dsu[v]=v;
  auto root=[&](int x){while(dsu[x]!=x){dsu[x]=dsu[dsu[x]];x=dsu[x];}return x;};
  for(int i=0;i<int(ids.size());++i)ids[i]=i;
  std::sort(ids.begin(),ids.end(),[&](int x,int y){return cellkey(g.edges[x].r,g.edges[x].c)<cellkey(g.edges[y].r,g.edges[y].c);});
  std::vector<std::vector<std::pair<int,int>>>tree(nv);chords.clear();
  for(int id:ids){const auto&ed=g.edges[id];int u=ed.r,v=g.nr+ed.c,ru=root(u),rv=root(v);
   if(ru==rv){chords.push_back(id);continue;}
   if(size[ru]<size[rv])std::swap(ru,rv);dsu[rv]=ru;size[ru]+=size[rv];
   tree[u].push_back({v,id});tree[v].push_back({u,id});
  }
  parent.assign(nv,-1);depth.assign(nv,0);parent_edge.assign(nv,-1);
  std::vector<int>stack;
  for(int v=0;v<nv;++v)if(parent[v]<0){parent[v]=v;stack.push_back(v);
   while(!stack.empty()){int u=stack.back();stack.pop_back();for(auto [w,id]:tree[u])if(parent[w]<0){parent[w]=u;depth[w]=depth[u]+1;parent_edge[w]=id;stack.push_back(w);}}
  }
  last_inserts=stat.inserts;last_deletes=stat.deletes;rebuilds++;
 }
 void step(Engine&e,Graph&g){
  calls++;e.stat.work++;
  if(margin_certified_forest){forest_skips++;return;}

  if(maximum_degree2){
   if(g.edges.empty()){no_cycle++;return;}
   int id=int(e.rng.below(g.edges.size())),first=g.edges[id].r,node=first;
   std::vector<int>cycle;cycle.reserve(64);
   for(size_t steps=0;steps<=g.edges.size();++steps){cycle.push_back(id);const auto&ed=g.edges[id];int next=node<g.nr?g.nr+ed.c:ed.r;
    if(next==first){refresh_line(e,g,cycle);return;}
    if(g.adj[next].size()!=2){no_cycle++;return;}
    int other=g.adj[next][0]==id?g.adj[next][1]:g.adj[next][0];node=next;id=other;
   }
   throw std::runtime_error("degree2 support traversal failed to terminate");
  }

  if(g.edges.empty()){no_cycle++;return;}
  if(++generation==0){std::fill(stamp.begin(),stamp.end(),0);generation=1;}
  int id=int(e.rng.below(g.edges.size())),node=g.edges[id].r;
  std::vector<int>nodes{node},ids;nodes.reserve(257);ids.reserve(256);
  stamp[node]=generation;position[node]=0;
  for(int step=0;step<256;++step){
   ids.push_back(id);const auto&ed=g.edges[id];int next=node<g.nr?g.nr+ed.c:ed.r;
   if(stamp[next]==generation){int start=position[next];std::vector<int>cycle(ids.begin()+start,ids.end());refresh_line(e,g,cycle);return;}
   stamp[next]=generation;position[next]=int(nodes.size());nodes.push_back(next);
   const auto&adj=g.adj[next];if(adj.size()<2){no_cycle++;return;}
   int previous=next<g.nr?ed.pr:ed.pc;int pick=int(e.rng.below(adj.size()-1));if(pick>=previous)pick++;
   node=next;id=adj[pick];
  }
  no_cycle++;return;

  if(last_inserts!=e.stat.inserts||last_deletes!=e.stat.deletes)rebuild(g,e.stat);
  if(chords.empty()){no_cycle++;return;}
  int chord=chords[e.rng.below(chords.size())];auto ed=g.edges[chord];
  int u=ed.r,v=g.nr+ed.c;std::vector<int>left,right;
  while(u!=v){if(depth[u]>=depth[v]){left.push_back(parent_edge[u]);u=parent[u];}
   else{right.push_back(parent_edge[v]);v=parent[v];}}
  std::vector<int>cycle{chord};cycle.insert(cycle.end(),right.begin(),right.end());
  cycle.insert(cycle.end(),left.rbegin(),left.rend());
  refresh_line(e,g,cycle);
 }
};
