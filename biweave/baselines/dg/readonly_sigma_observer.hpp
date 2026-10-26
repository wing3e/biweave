#pragma once
 
#include <map>
struct ReadOnlySigmaObserver {
 using S=__uint128_t;
 U burn,budget,interval,observed=0,post=0,last_updates=0;
 bool cache_valid=false;
 S initial_sigma=0,final_sigma=0;
 U edges=0;
 std::map<S,U> counts;
 std::string prefix;
 std::ofstream trace;
 static std::string decimal(S x){if(!x)return "0";std::string s;while(x){s.push_back(char('0'+x%10));x/=10;}std::reverse(s.begin(),s.end());return s;}
 void scan(const WgsProbeGraph&g){final_sigma=0;edges=0;for(int r=0;r<g.nr;++r)for(int c=0;c<g.nc;++c){I w=g.value(r,c);if(w<0)throw std::runtime_error("negative Sigma input");final_sigma+=S(w)*S(w);edges+=w>0;}}
 void record(U t){trace<<"{\"iteration\":"<<t<<",\"weight_square_sum\":\""<<decimal(final_sigma)<<"\",\"positive_edges\":"<<edges<<"}\n";if(!trace)throw std::runtime_error("Sigma trace write failed");}
 ReadOnlySigmaObserver(const WgsProbeGraph&g,U b,U n,U every,const std::string&p):burn(b),budget(n),interval(every),prefix(p){
  if(!interval||n%interval||b>=n)throw std::runtime_error("Sigma trace requires interval dividing outer budget");
  scan(g);initial_sigma=final_sigma;
  trace.open(prefix+".structure.trace.jsonl");if(!trace)throw std::runtime_error("cannot create Sigma trace");record(0);
 }
 void observe(const WgsProbeGraph&g,U t,U updates){
  if(t!=observed+1||t>budget||g.D)throw std::runtime_error("Sigma complete-outer lifecycle");
  observed=t;
  if(!cache_valid||updates!=last_updates){scan(g);last_updates=updates;cache_valid=true;}
  if(t>burn){++counts[final_sigma];++post;}
  if(t%interval==0||t==budget)record(t);
 }
 void finish(){
  if(observed!=budget||post!=budget-burn)throw std::runtime_error("Sigma count lifecycle incomplete");
  U total=0;for(const auto&x:counts)total+=x.second;if(total!=post)throw std::runtime_error("Sigma histogram accounting mismatch");
  trace.flush();if(!trace)throw std::runtime_error("Sigma trace flush failed");
  std::ofstream f(prefix+".structure.hist.json");
  f<<"{\"format\":\"allpostburn_sigma_histogram_v1\",\"outer_budget\":"<<budget<<",\"burn_outer\":"<<burn<<",\"postburn_count\":"<<post<<",\"initial_sigma\":\""<<decimal(initial_sigma)<<"\",\"final_sigma\":\""<<decimal(final_sigma)<<"\",\"counts\":{";
  bool first=true;for(const auto&x:counts){if(!first)f<<',';first=false;f<<'\"'<<decimal(x.first)<<"\":"<<x.second;}f<<"}}\n";f.flush();if(!f)throw std::runtime_error("Sigma histogram write failed");
 }
};
