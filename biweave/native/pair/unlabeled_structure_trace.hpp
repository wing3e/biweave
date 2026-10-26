#pragma once
 
struct UnlabeledStructureTrace {
 bool active=false,histogram_active=false;U snapshots=0,postburn_snapshots=0;U burn=0,budget=0,trace=0;
 U histogram_observed_outer=0,histogram_postburn_count=0;
 __uint128_t histogram_initial_sigma=0,histogram_final_sigma=0;
 std::map<__uint128_t,U>histogram_counts;std::string histogram_prefix;std::ofstream out;
 static std::string decimal(__uint128_t n){if(!n)return "0";std::string s;while(n){s.push_back(char('0'+n%10));n/=10;}std::reverse(s.begin(),s.end());return s;}
 void initialize(Graph&g,bool requested,const std::string&prefix,U b,U n,U interval,bool histogram_requested=false){
  if(!requested){if(histogram_requested)throw std::runtime_error("allpostburn Sigma histogram requires structure trace");return;}
  if(!interval)throw std::runtime_error("unlabeled structure trace requires trace-every>0");active=true;burn=b;budget=n;trace=interval;
  __uint128_t W=0;for(const Edge&x:g.edges)W+=U(x.w);I rowcap=0,colcap=0;for(int i=0;i<g.nr;++i)rowcap=std::max(rowcap,g.target_strength[i]);for(int i=g.nr;i<g.nr+g.nc;++i)colcap=std::max(colcap,g.target_strength[i]);const U cap=U(std::min(rowcap,colcap));
  if(cap&&W>(~__uint128_t(0)/2)/cap)throw std::runtime_error("unlabeled exact-square accumulator input resource guard");
  g.exact_sumw2=0;for(const Edge&x:g.edges)g.exact_sumw2+=__uint128_t(U(x.w))*U(x.w);g.maintain_exact_sumw2=true;
  histogram_active=histogram_requested;if(histogram_active){histogram_prefix=prefix;histogram_initial_sigma=g.exact_sumw2;histogram_final_sigma=g.exact_sumw2;}
  out.open(prefix+".structure.trace.jsonl");if(!out)throw std::runtime_error("cannot create structure trace");record(g,0);
 }
 void record(const Graph&g,U t){out<<"{\"iteration\":"<<t<<",\"weight_square_sum\":\""<<decimal(g.exact_sumw2)<<"\",\"positive_edges\":"<<g.edges.size()<<"}\n";if(!out)throw std::runtime_error("structure trace write");++snapshots;postburn_snapshots+=t>burn;}
 void observe(const Graph&g,U t){
  if(histogram_active){
   if(!g.maintain_exact_sumw2||g.D||t!=histogram_observed_outer+1||t>budget)throw std::runtime_error("allpostburn Sigma complete-outer lifecycle");
   histogram_observed_outer=t;histogram_final_sigma=g.exact_sumw2;
   if(t>burn){++histogram_counts[g.exact_sumw2];++histogram_postburn_count;}
  }
  if(active&&(t%trace==0||t==budget))record(g,t);
 }
 void finish(){
  if(active){out.flush();if(!out)throw std::runtime_error("structure trace flush");}
  if(histogram_active){
   if(histogram_observed_outer!=budget||histogram_postburn_count!=budget-burn)throw std::runtime_error("allpostburn Sigma count mismatch");
   U total=0;for(const auto&x:histogram_counts){if(x.second>budget-burn-total)throw std::runtime_error("allpostburn Sigma count overflow");total+=x.second;}
   if(total!=budget-burn)throw std::runtime_error("allpostburn Sigma histogram sum mismatch");
   std::ofstream f(histogram_prefix+".structure.hist.json");f<<"{\"format\":\"allpostburn_sigma_histogram_v1\",\"outer_budget\":"<<budget<<",\"burn_outer\":"<<burn<<",\"postburn_count\":"<<histogram_postburn_count<<",\"initial_sigma\":\""<<decimal(histogram_initial_sigma)<<"\",\"final_sigma\":\""<<decimal(histogram_final_sigma)<<"\",\"counts\":{";
   bool first=true;for(const auto&x:histogram_counts){if(!first)f<<',';first=false;f<<'\"'<<decimal(x.first)<<"\":"<<x.second;}f<<"}}\n";if(!f)throw std::runtime_error("allpostburn Sigma histogram write");
  }
 }
};
