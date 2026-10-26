#pragma once
#include "checkpoint_gate.h"
#include <fstream>
#include <algorithm>
#include <array>
#include <cstdint>
#include <limits>
#include <string>
#include <sstream>
#include <iomanip>
#include <unordered_map>
#include <vector>
#include <stdexcept>
#include <time.h>

struct ConvergenceDistanceCPUObserver {
 using Wide=__uint128_t;
 struct Ref {int r,c;long long w;};
 std::vector<Ref> reference;
 std::vector<std::vector<size_t>> reference_rows;
 std::vector<std::array<int64_t,3>> pairs,cells;
 std::unordered_map<unsigned long long,long long> lookup;
 std::ofstream stream;
 Wide total=0;unsigned long long E=0,stride=0,last=0;
 double origin_cpu=0;
 static double cpu(){timespec ts{};if(clock_gettime(CLOCK_PROCESS_CPUTIME_ID,&ts))throw std::runtime_error("convergence cpu clock");return double(ts.tv_sec)+double(ts.tv_nsec)*1e-9;}
 static std::string decimal(Wide x){if(!x)return "0";std::string s;while(x){s.push_back(char('0'+x%10));x/=10;}std::reverse(s.begin(),s.end());return s;}
 static unsigned long long key(int r,int c){return (static_cast<unsigned long long>(unsigned(r))<<32)|unsigned(c);}
 template<class G> void initialize(const G&g,const std::string&path,const std::string&out,unsigned long long every,double start,const std::string&query_path){
  if(path.empty()||!every)throw std::runtime_error("explicit reference-input and positive convergence-every required");
  stride=every;origin_cpu=start;
  std::ifstream f(path);int nr,nc;if(!(f>>nr>>nc)||nr!=g.nr||nc!=g.nc)throw std::runtime_error("convergence reference shape");
  reference_rows.resize(nr);
  std::vector<int64_t> strengths(nr+nc,0);std::vector<int> degrees(nr+nc,0);
  int r,c;long long w;
  while(f>>r>>c>>w){
   if(r<0||r>=nr||c<0||c>=nc||w<=0||!lookup.emplace(key(r,c),w).second)throw std::runtime_error("invalid convergence reference edge");
   if(strengths[r]>std::numeric_limits<long long>::max()-w||strengths[nr+c]>std::numeric_limits<long long>::max()-w)throw std::runtime_error("reference strength overflow");
   reference.push_back({r,c,w});reference_rows[r].push_back(reference.size()-1);total+=Wide(w);strengths[r]+=w;strengths[nr+c]+=w;++degrees[r];++degrees[nr+c];
  }
  if(!f.eof()||strengths!=g.target_strength||degrees!=g.target_degree||reference.size()!=g.edges.size()||reference.empty()||!total)throw std::runtime_error("convergence reference four margins mismatch");
  E=reference.size();stream.open(out+".convergence.trace.jsonl");if(!stream)throw std::runtime_error("convergence trace open");
  std::ifstream q(query_path);std::string format;int qr,qc,np,ncells;
  if(!(q>>format>>qr>>qc>>np>>ncells)||format!="fixed_probe_queries_v1"||qr!=nr||qc!=nc||np<0||ncells<0||np+ncells>10000)throw std::runtime_error("convergence fixed queries header");
  for(int i=0;i<np+ncells;++i){int64_t a,b,threshold;if(!(q>>a>>b>>threshold)||threshold<0)throw std::runtime_error("convergence fixed query triple");if(i<np){if(a<0||a>=nr||b<0||b>=nr||a==b)throw std::runtime_error("pair query label");Wide expected=0;for(size_t j:reference_rows[a]){const auto&e=reference[j];const auto it=lookup.find(key(int(b),e.c));if(it!=lookup.end())expected+=Wide(std::min(e.w,it->second));}if(expected!=Wide(threshold))throw std::runtime_error("pair threshold differs from shared W0");pairs.push_back({a,b,threshold});}else{if(a<0||a>=nr||b<0||b>=nc)throw std::runtime_error("cell query label");const auto it=lookup.find(key(int(a),int(b)));const long long expected=it==lookup.end()?0:it->second;if(expected!=threshold)throw std::runtime_error("cell threshold differs from shared W0");cells.push_back({a,b,threshold});}}
  std::string trailing;if(q>>trailing)throw std::runtime_error("convergence trailing query tokens");
  record(g,0);
 }
 template<class G> void record(const G&g,unsigned long long iteration){
  if(!checkpoint_should_emit(iteration,stride))return;
  Wide l1=0,sigma=0;unsigned long long support=0;Wide live_total=0;
  std::vector<int64_t>strengths(g.nr+g.nc,0);std::vector<int>degrees(g.nr+g.nc,0);
  if(g.edges.size()!=E)throw std::runtime_error("convergence live edge count changed");
  for(const auto&e:g.edges){
   if(e.w<=0)throw std::runtime_error("convergence live nonpositive edge");
   const auto it=lookup.find(key(e.r,e.c));const long long old=it==lookup.end()?0:it->second;
   const Wide now=Wide(e.w),before=Wide(old);l1+=now>before?now-before:before-now;
   if(!old)++support;sigma+=now*now;live_total+=now;
   strengths[e.r]+=e.w;strengths[g.nr+e.c]+=e.w;++degrees[e.r];++degrees[g.nr+e.c];
  }
  for(const auto&e:reference)if(g.value(e.r,e.c)==0){l1+=Wide(e.w);++support;}
  if(live_total!=total||l1>2*total||support>2*E||strengths!=g.target_strength||degrees!=g.target_degree)throw std::runtime_error("convergence four margins/distance conservation/bound");
  std::vector<Wide>query_minima;std::vector<int64_t>query_weights;
  for(const auto&p:pairs){int a=int(p[0]),b=int(p[1]);if(g.adj[a].size()>g.adj[b].size())std::swap(a,b);Wide value=0;for(int ei:g.adj[a]){const auto&e=g.edges[ei];value+=Wide(std::min(e.w,g.value(b,e.c)));}query_minima.push_back(value);}
  for(const auto&p:cells)query_weights.push_back(g.value(int(p[0]),int(p[1])));
  const double elapsed=cpu()-origin_cpu;
  stream<<std::setprecision(17)<<"{\"iteration\":"<<iteration<<",\"is_fixed_checkpoint\":"<<(iteration%stride==0?"true":"false")<<",\"process_cpu_seconds\":"<<elapsed<<",\"weight_L1_numerator\":\""<<decimal(l1)<<"\",\"support_symmetric_difference\":"<<support<<",\"total_weight\":\""<<decimal(total)<<"\",\"edge_count\":"<<E<<",\"Dw\":"<<double((long double)l1/(2*(long double)total))<<",\"Db\":"<<double((long double)support/(2*(long double)E))<<",\"weight_square_sum\":\""<<decimal(sigma)<<"\",\"four_margins_passed\":true,\"pair_minimum\":[";
  for(size_t i=0;i<query_minima.size();++i){if(i)stream<<',';stream<<decimal(query_minima[i]);}stream<<"],\"cell_weights\":[";for(size_t i=0;i<query_weights.size();++i){if(i)stream<<',';stream<<query_weights[i];}stream<<"]}\n";
  stream.flush();if(!stream)throw std::runtime_error("convergence trace write");last=iteration; checkpoint_gate(iteration);
 }
 template<class G> void observe(const G&g,unsigned long long iteration){if(iteration%stride==0)record(g,iteration);}
 template<class G> void finish(const G&g,unsigned long long iteration){if(last!=iteration)record(g,iteration);stream.close();if(!stream)throw std::runtime_error("convergence trace close");}
};
