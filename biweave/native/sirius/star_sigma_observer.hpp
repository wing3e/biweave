#pragma once

struct StarSigmaObserver {
 U N=0,burn=0,every=0;bool histogram_active=false;U histogram_observed_outer=0,histogram_postburn_count=0;__uint128_t histogram_initial_sigma=0,histogram_final_sigma=0;std::map<__uint128_t,U>histogram_counts;
 std::vector<std::pair<U,__uint128_t>>records;
 static std::string decimal(__uint128_t z){if(!z)return "0";std::string s;while(z){s.push_back(char('0'+z%10));z/=10;}std::reverse(s.begin(),s.end());return s;}
 StarSigmaObserver(Graph&g,U n,U b,U cadence,const FixedProbeStatistics&,bool histogram_requested=false):N(n),burn(b),every(cadence),histogram_active(histogram_requested){
  if(!every||N%640||every!=N/640||burn!=N/5)throw std::runtime_error("generic Sigma requires multiple640 N,20pctburn,641checkpoints");
  if(!g.check()||g.D)throw std::runtime_error("generic Sigma initial four margins");
   
  __uint128_t W=0;for(const auto&e:g.edges)W+=U(e.w);I rowcap=0,colcap=0;for(int r=0;r<g.nr;++r)rowcap=std::max(rowcap,g.target_strength[r]);for(int c=0;c<g.nc;++c)colcap=std::max(colcap,g.target_strength[g.nr+c]);const U cap=U(std::min(rowcap,colcap));
  if(cap&&W>(~__uint128_t(0)/2)/cap)throw std::runtime_error("generic Sigma exact-delta input resource guard");
  g.exact_sumw2=sigma(g);g.maintain_exact_sumw2=true;if(histogram_active){histogram_initial_sigma=g.exact_sumw2;histogram_final_sigma=g.exact_sumw2;}
  records.reserve(641);record(g,0);
 }
 static __uint128_t sigma(const Graph&g){__uint128_t z=0;for(const auto&e:g.edges){if(e.w<=0)throw std::runtime_error("generic Sigma nonpositive live edge");const U w=U(e.w);const __uint128_t term=__uint128_t(w)*w;if((~__uint128_t(0))-z<term)throw std::runtime_error("generic Sigma uint128 sum overflow");z+=term;}return z;}
 void observe(const Graph&g,U t){if(!histogram_active)return;if(!g.maintain_exact_sumw2||g.D||t!=histogram_observed_outer+1||t>N)throw std::runtime_error("allpostburn Sigma complete-outer lifecycle");histogram_observed_outer=t;histogram_final_sigma=g.exact_sumw2;if(t>burn){++histogram_counts[g.exact_sumw2];++histogram_postburn_count;}}
 void record(const Graph&g,U t){if(g.D)throw std::runtime_error("generic Sigma checkpoint degree deviation");if(!g.maintain_exact_sumw2||t!=records.size()*every||t>N)throw std::runtime_error("generic Sigma checkpoint order/lifecycle");records.emplace_back(t,g.exact_sumw2);}
 void write(const Graph&g,const std::string&prefix)const{if(records.size()!=641||records.back().first!=N)throw std::runtime_error("generic Sigma record count");

  __uint128_t full=0;for(int r=0;r<g.nr;++r)for(int ei:g.adj[r]){const auto&e=g.edges[ei];I w=g.value(r,e.c);if(w!=e.w||w<=0)throw std::runtime_error("generic Sigma final adjacency mismatch");const __uint128_t term=__uint128_t(U(w))*U(w);if((~__uint128_t(0))-full<term)throw std::runtime_error("generic Sigma final overflow");full+=term;}
  if(full!=records.back().second)throw std::runtime_error("generic Sigma final independent scan");
  std::ofstream f(prefix+".structure.trace.jsonl");U post=0;for(const auto&[t,z]:records){if(t>burn)++post;f<<"{\"iteration\":"<<t<<",\"weight_square_sum\":\""<<decimal(z)<<"\"}\n";}if(post!=512||!f)throw std::runtime_error("generic Sigma output/count");
  if(histogram_active){if(histogram_observed_outer!=N||histogram_postburn_count!=N-burn)throw std::runtime_error("allpostburn Sigma count mismatch");U total=0;for(const auto&x:histogram_counts){if(x.second>N-burn-total)throw std::runtime_error("allpostburn Sigma count overflow");total+=x.second;}if(total!=N-burn)throw std::runtime_error("allpostburn Sigma histogram sum mismatch");std::ofstream h(prefix+".structure.hist.json");h<<"{\"format\":\"allpostburn_sigma_histogram_v1\",\"outer_budget\":"<<N<<",\"burn_outer\":"<<burn<<",\"postburn_count\":"<<histogram_postburn_count<<",\"initial_sigma\":\""<<decimal(histogram_initial_sigma)<<"\",\"final_sigma\":\""<<decimal(histogram_final_sigma)<<"\",\"counts\":{";bool first=true;for(const auto&x:histogram_counts){if(!first)h<<',';first=false;h<<'\"'<<decimal(x.first)<<"\":"<<x.second;}h<<"}}\n";if(!h)throw std::runtime_error("allpostburn Sigma histogram write");}
 }
};
