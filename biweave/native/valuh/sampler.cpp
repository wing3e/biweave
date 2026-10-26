#include "weighted_kernels.hpp"
#include "star_sigma_observer.hpp"
#include "vaLUH_d_kernel.hpp"
int main(int argc,char**argv){try{
 std::map<std::string,std::string>a;
 for(int k=1;k<argc;k+=2){if(k+1==argc||!a.emplace(argv[k],argv[k+1]).second)throw std::runtime_error("everyflag onevalue no duplicates");}
 auto get=[&](std::string k,std::string d){return a.count(k)?a.at(k):d;};
 const std::set<std::string>allowed={"--allpostburn-sigma-histogram","--input","--out","--queries","--method","--seed","--outer","--burn","--check-every","--trace-every","--kill-denominator","--fixed-checkpoints"};
 for(const auto&kv:a)if(!allowed.count(kv.first))throw std::runtime_error("unknownflag "+kv.first);
 std::string input=get("--input",""),out=get("--out",""),queries=get("--queries",""),method=get("--method","vaLUH_d_trace");
 if(input.empty()||out.empty()||queries.empty()||method!="vaLUH_d_trace")throw std::runtime_error("input/out/queries andvaLUH_d_trace required");
 U seed=probe_unsigned_v12(get("--seed",std::to_string(0x1359143ULL)),"seed"),N=probe_unsigned_v12(get("--outer","10000"),"outer"),B=probe_unsigned_v12(get("--burn","2000"),"burn");
 U check=probe_unsigned_v12(get("--check-every","10000"),"check"),trace=probe_unsigned_v12(get("--trace-every","0"),"trace"),fixed=probe_unsigned_v12(get("--fixed-checkpoints","1"),"fixed"),kill=probe_unsigned_v12(get("--kill-denominator","20"),"kill-denominator");
 if(!N||B>=N||fixed>1||!kill||(fixed&&(B<133||N-B<534)))throw std::runtime_error("invalid budget/schedule/kill");
 U allpostburn_sigma_requested=probe_unsigned_v12(get("--allpostburn-sigma-histogram","0"),"allpostburn-sigma-histogram");if(allpostburn_sigma_requested>1)throw std::runtime_error("invalid allpostburn Sigma flag");
 auto start=Clock::now();Counters stat;Graph g=Graph::load(input,false,false);g.counters=&stat;RNG rng(seed);VaLUHDTraceKernel kernel(g,kill);
 if(!g.check()||g.D||!kernel.check_types(g))throw std::runtime_error("invalidinitial graph/types");
 if(fixed)throw std::runtime_error("generic Sigma bridge requires --fixed-checkpoints0");
 FixedProbeStatistics observer(g,B,N,queries,0,trace);StarSigmaObserver sigma(g,N,B,trace,observer,allpostburn_sigma_requested);std::vector<U>checkpoint;size_t next_checkpoint=1;
 if(fixed){for(U j=0;j<134;++j)checkpoint.push_back(U(__uint128_t(j)*B/133));for(U j=0;j<534;++j)checkpoint.push_back(B+1+U(__uint128_t(j)*(N-B-1)/533));
  if(checkpoint.size()!=668||checkpoint.front()!=0||checkpoint.back()!=N)throw std::runtime_error("checkpointbounds");
  for(size_t j=1;j<checkpoint.size();++j)if(checkpoint[j]<=checkpoint[j-1])throw std::runtime_error("checkpointunique");observer.record(g,0);}
 U checks=1,observation_version=0;double build=std::chrono::duration<double>(Clock::now()-start).count();auto sampling=Clock::now();
 for(U t=1;t<=N;++t){
  bool changed=kernel.step(rng,g,stat);if(changed)++observation_version;++stat.outer;

  observer.observe(g,t,observation_version);sigma.observe(g,t);
  if(t%trace==0)sigma.record(g,t);
  if(fixed&&next_checkpoint<checkpoint.size()&&checkpoint[next_checkpoint]==t){observer.record(g,t);++next_checkpoint;}
  if((check&&t%check==0)||t==N){if(!g.check()||g.D||(t==N&&!kernel.check_types(g)))throw std::runtime_error("fourmargins/types changed");++checks;}
 }
 double loop=std::chrono::duration<double>(Clock::now()-sampling).count();if(fixed){if(next_checkpoint!=668)throw std::runtime_error("incomplete668checkpoints");observer.trace_every=1;}observer.write(out);sigma.write(g,out);
 std::ofstream final(out+".final.graph");final<<g.nr<<' '<<g.nc<<'\n';for(const auto&ed:g.edges)final<<ed.r<<' '<<ed.c<<' '<<ed.w<<'\n';final.close();if(!final)throw std::runtime_error("finalwrite");
 double total=std::chrono::duration<double>(Clock::now()-start).count();std::ofstream report(out+".run.json");
 report<<std::setprecision(17)<<"{\"status\":\"ok\",\"method\":\"vaLUH_d_trace\",\"seed\":"<<seed<<",\"structure_trace_records\":641,\"postburn_structure_records\":512,\"structure_certificate\":\"generic exact integer square delta;641 O(1) reads; four margins at configured check cadence and final\",\"outer\":"<<N<<",\"burn\":"<<B<<",\"nr\":"<<g.nr<<",\"nc\":"<<g.nc<<",\"build_seconds\":"<<build<<",\"loop_seconds\":"<<loop<<",\"total_seconds\":"<<total<<",\"rss_kib\":"<<proc_memory("VmHWM")<<",\"checks\":"<<checks<<",\"all_margins_passed\":true,\"changed_outer\":"<<stat.changed_outer<<",\"kill_denominator\":"<<kill<<",\"soft_calls\":"<<kernel.soft_calls<<",\"soft_accepted\":"<<kernel.soft_accepted<<",\"soft_lazy\":"<<kernel.soft_lazy<<",\"soft_mh_reject\":"<<kernel.mh_rejected<<",\"soft_nonchanging\":"<<kernel.nonchanging<<",\"trace_returns\":"<<kernel.returned<<",\"trace_kills\":"<<kernel.killed<<",\"undo_moves\":"<<kernel.undo_moves<<",\"max_soft_steps\":"<<kernel.max_soft_steps<<",\"path_cell_updates\":"<<stat.cell_updates<<",\"observation_version\":"<<observation_version<<",\"edge_types\":"<<g.edges.size()<<",\"pair_shared_endpoint\":"<<kernel.pair_shared_endpoint<<",\"matching_identity\":"<<kernel.matching_identity<<",\"matching_nonbipartite\":"<<kernel.matching_nonbipartite<<",\"matching_cross\":"<<kernel.matching_cross<<",\"mh_type_increase\":"<<kernel.mh_type_increase<<",\"mh_type_same\":"<<kernel.mh_type_same<<",\"mh_type_decrease\":"<<kernel.mh_type_decrease<<",\"fixed_checkpoint_schedule\":"<<(fixed?"true":"false")<<",\"source\":\"VaLUH-d dyadic C++ implementation, uniform distinct dyad-type pair, standard Curveball3matchings, exact type-countMH, hardbipartite restriction then rho=0.25 killed first return on the feasible graph space\"}\n";
 report.close();if(!report)throw std::runtime_error("reportwrite");return 0;
}catch(const std::exception&e){std::cerr<<e.what()<<'\n';return 1;}}
