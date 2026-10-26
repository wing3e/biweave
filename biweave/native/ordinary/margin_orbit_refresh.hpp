#ifndef MARGIN_ORBIT_REFRESH_V20_HPP
#define MARGIN_ORBIT_REFRESH_V20_HPP

struct MarginOrbitRefreshV20 {
 struct Move { int old_r,old_c,new_r,new_c;I w; };
 std::array<std::vector<std::vector<int>>,2> groups;
 U calls=0,changed_calls=0,changed_edges=0,changed_positive_cells=0;
 unsigned long long refresh_ns=0,constructor_ns=0,map_ns=0,collect_ns=0,commit_ns=0;
 int nr=0,nc=0;
 private:
 std::vector<int> fixed_degree,row_map,col_map,seen;
 std::vector<I> fixed_strength;
 std::vector<Move> moves;
 static unsigned long long elapsed(Clock::time_point start){return std::chrono::duration_cast<std::chrono::nanoseconds>(Clock::now()-start).count();}
 void guard(const Graph&g)const{
  if(g.maintain_bias)throw std::runtime_error("orbit refresh requires maintain_bias=false");
  if(g.nr!=nr||g.nc!=nc||g.target_degree!=fixed_degree||g.target_strength!=fixed_strength)
   throw std::runtime_error("orbit refresh graph or fixed margins changed");
  if(g.D!=0)throw std::runtime_error("orbit refresh requires a full-margin state");
 }
 void validate_map(const std::vector<int>&map,int n,int off){
  if(int(map.size())!=n)throw std::runtime_error("orbit map has incorrect dimension");
  seen.assign(n,0);
  for(int v=0;v<n;++v){int to=map[v];
   if(to<0||to>=n||seen[to]++)throw std::runtime_error("orbit map is not a permutation");
   if(fixed_degree[off+v]!=fixed_degree[off+to]||fixed_strength[off+v]!=fixed_strength[off+to])
    throw std::runtime_error("orbit map crosses a fixed degree-strength class");
  }
 }
 bool commit_maps(Graph&g,const std::vector<int>&rmap,const std::vector<int>&cmap){
  auto collecting=Clock::now();moves.clear();U differing=0;

  for(const auto&x:g.edges){int r=rmap[x.r],c=cmap[x.c];
   if(r!=x.r||c!=x.c){moves.push_back({x.r,x.c,r,c,x.w});differing+=g.value(r,c)!=x.w;}
  }
  collect_ns+=elapsed(collecting);

  if(!differing)return false;
  auto committing=Clock::now();
  for(const auto&x:moves)g.set_raw(x.old_r,x.old_c,0);
  for(const auto&x:moves)g.set_raw(x.new_r,x.new_c,x.w);

  commit_ns+=elapsed(committing);changed_calls++;changed_edges+=moves.size();changed_positive_cells+=differing;
  return true;
 }
 public:
 explicit MarginOrbitRefreshV20(const Graph&g):nr(g.nr),nc(g.nc){
  auto start=Clock::now();
  if(g.maintain_bias||g.D||g.target_degree.size()!=size_t(nr+nc)||g.target_strength.size()!=size_t(nr+nc))
   throw std::runtime_error("orbit constructor requires fixed full margins and maintain_bias=false");
  fixed_degree=g.target_degree;fixed_strength=g.target_strength;
  for(int o=0;o<2;++o){int n=o?nc:nr,off=o?nr:0;std::map<std::pair<int,I>,std::vector<int>>classes;
   for(int v=0;v<n;++v)if(fixed_degree[off+v]>0)classes[{fixed_degree[off+v],fixed_strength[off+v]}].push_back(v);
   for(auto&item:classes)if(item.second.size()>1)groups[o].push_back(std::move(item.second));
  }
  row_map.resize(nr);col_map.resize(nc);seen.reserve(std::max(nr,nc));moves.reserve(g.edges.size());
  constructor_ns=elapsed(start);
 }

 bool apply_maps(Graph&g,const std::vector<int>&rmap,const std::vector<int>&cmap){
  auto start=Clock::now();guard(g);validate_map(rmap,nr,0);validate_map(cmap,nc,nr);calls++;
  bool changed=commit_maps(g,rmap,cmap);refresh_ns+=elapsed(start);return changed;
 }

 template<class Random>bool refresh_with_rng(Random&rng,Graph&g){
  auto start=Clock::now();guard(g);calls++;auto mapping=Clock::now();
  for(int v=0;v<nr;++v)row_map[v]=v;for(int v=0;v<nc;++v)col_map[v]=v;
  for(int o=0;o<2;++o){auto&map=o?col_map:row_map;
   for(const auto&group:groups[o])for(size_t j=group.size();j>1;--j){size_t k=rng.below(U(j));std::swap(map[group[j-1]],map[group[k]]);}
  }
  map_ns+=elapsed(mapping);
  bool changed=commit_maps(g,row_map,col_map);refresh_ns+=elapsed(start);return changed;
 }
 bool refresh(Engine&e,Graph&g){return refresh_with_rng(e.rng,g);}
};
#endif
