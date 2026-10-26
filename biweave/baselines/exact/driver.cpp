#include <algorithm>
#include <chrono>
#include <fstream>
#include <iomanip>
#include <iostream>
#include <limits>
#include <map>
#include <memory>
#include <stdexcept>
#include <string>
#include <vector>
#include "bridge.h"
using U=unsigned long long;
using I=long long;
using S128=__int128_t;
using Clock=std::chrono::steady_clock;
struct WgsProbeGraph {
 int nr,nc,D=0;void* handle;bool transposed=false;
 I value(int r,int c)const{
  const size_t index=transposed?static_cast<size_t>(c)*nr+r:static_cast<size_t>(r)*nc+c;
  return mh_current_matrix(handle)[index];
 }
};
#include "common_probe_observer.hpp"
std::string decimal(S128 x){return probe_decimal_v12(x);}
S128 sigma(const WgsProbeGraph&g){S128 s=0;for(int r=0;r<g.nr;++r)for(int c=0;c<g.nc;++c){S128 v=g.value(r,c);s+=v*v;}return s;}
int main(int argc,char**argv){try{
 std::map<std::string,std::string>opt;
 for(int i=1;i<argc;i+=2){if(i+1>=argc)throw std::runtime_error("Missing argument");opt[argv[i]]=argv[i+1];}
 const auto input=opt.at("--input"),queries=opt.at("--queries"),out=opt.at("--out");
 U seed=std::stoull(opt.at("--seed")),N=std::stoull(opt.at("--outer")),B=std::stoull(opt.at("--burn")),stride=std::stoull(opt.at("--trace-every"));
 U check=opt.count("--check-every")?std::stoull(opt.at("--check-every")):100000;
 std::ifstream f(input);int nr,nc;
 if(!(f>>nr>>nc)||nr<=0||nc<=0)throw std::runtime_error("Positive graph dimensions required");
 const size_t cells=static_cast<size_t>(nr)*static_cast<size_t>(nc);
 if(cells>static_cast<size_t>(std::numeric_limits<int>::max()))throw std::runtime_error("Author signed-int matrix array bound exceeded");
 std::vector<int> a(cells,0),rd(nr,0),cd(nc,0),rs(nr,0),cs(nc,0);int r,c,w;
 while(f>>r>>c>>w){
  if(r<0||r>=nr||c<0||c>=nc||w<=0)throw std::runtime_error("Invalid input");
  const size_t index=static_cast<size_t>(r)*nc+c;
  if(a[index]||rs[r]>std::numeric_limits<int>::max()-w||cs[c]>std::numeric_limits<int>::max()-w)throw std::runtime_error("Duplicate cell or author int margin bound exceeded");
  a[index]=w;rd[r]++;cd[c]++;rs[r]+=w;cs[c]+=w;
 }
 if(!f.eof())throw std::runtime_error("Malformed graph input");
 const int type=opt.count("--matrix-type")?std::stoi(opt.at("--matrix-type")):1;
 const std::string orientation=opt.count("--orientation-rule")?opt.at("--orientation-rule"):"auto";
 if(orientation!="auto"&&orientation!="original"&&orientation!="transpose")throw std::runtime_error("Invalid EXACT orientation rule");
 const bool transposed=orientation=="transpose"||(orientation=="auto"&&cells>64&&nr<nc);
 const U memory_guard=opt.count("--memory-guard-bytes")?std::stoull(opt.at("--memory-guard-bytes")):2147483648ULL;
 void*handle=nullptr;
 if(transposed){
  std::vector<int> other(cells,0);
  for(int i=0;i<nr;++i)for(int j=0;j<nc;++j)other[static_cast<size_t>(j)*nr+i]=a[static_cast<size_t>(i)*nc+j];
  a.swap(other);
 }
 std::ofstream orientation_report(out+".orientation.json");
 orientation_report<<"{\"format\":\"exact_dimension_orientation_v1\",\"original_shape\":["<<nr<<','<<nc<<"],\"counter_shape\":["<<(transposed?nc:nr)<<','<<(transposed?nr:nc)<<"],\"transposed\":"<<(transposed?"true":"false")<<",\"memory_guard_bytes\":"<<memory_guard<<"}\n";
 orientation_report.close();
 if(!orientation_report)throw std::runtime_error("EXACT orientation receipt write failed");
 handle=transposed?mh_create(nc,nr,cs.data(),rs.data(),cd.data(),rd.data(),a.data(),seed,type,memory_guard)
                  :mh_create(nr,nc,rs.data(),cs.data(),rd.data(),cd.data(),a.data(),seed,type,memory_guard);
 if(!handle)throw std::runtime_error(mh_last_error());
 if(cells>64)std::vector<int>().swap(a);
 WgsProbeGraph g{nr,nc,0,handle,transposed};FixedProbeStatistics observer(g,B,N,queries,0,stride);
 std::map<S128,U>hist;std::vector<std::pair<U,S128>>snap{{0,sigma(g)}};
 auto margins=[&](){std::vector<int>rd2(nr,0),cd2(nc,0),rs2(nr,0),cs2(nc,0);for(int i=0;i<nr;++i)for(int j=0;j<nc;++j){I z=g.value(i,j);if(z<0)throw std::runtime_error("Negative output");if(z){rd2[i]++;cd2[j]++;}rs2[i]+=z;cs2[j]+=z;}if(rd2!=rd||cd2!=cd||rs2!=rs||cs2!=cs)throw std::runtime_error("Four margins changed");};
 margins();U checks=1;
 for(U t=1;t<=N;++t){mh_joint_step(handle);observer.observe(g,t,mh_changed(handle));S128 s=sigma(g);if(t>B)hist[s]++;if(t%stride==0||t==N)snap.push_back({t,s});if((check&&t%check==0)||t==N){margins();checks++;}}
 observer.write(out);
 std::ofstream final(out+".final.graph");final<<nr<<' '<<nc<<'\n';for(int i=0;i<nr;++i)for(int j=0;j<nc;++j)if(g.value(i,j)>0)final<<i<<' '<<j<<' '<<g.value(i,j)<<'\n';final.close();
 std::ofstream tr(out+".structure.trace.jsonl");for(auto [t,s]:snap)tr<<"{\"iteration\":"<<t<<",\"weight_square_sum\":\""<<decimal(s)<<"\"}\n";tr.close();
 std::ofstream hf(out+".structure.hist.json");hf<<"{\"format\":\"allpostburn_sigma_histogram_v1\",\"outer_budget\":"<<N<<",\"burn_outer\":"<<B<<",\"postburn_count\":"<<(N-B)<<",\"counts\":{";bool comma=false;for(auto [s,n]:hist){if(comma)hf<<',';comma=true;hf<<'"'<<decimal(s)<<"\":"<<n;}hf<<"}}\n";hf.close();
 std::ofstream run(out+".run.json");run<<"{\"status\":\"ok\",\"method\":\"miller_harrison_degree_reject\",\"seed\":"<<seed<<",\"outer\":"<<N<<",\"burn\":"<<B<<",\"all_margins_passed\":true,\"checks\":"<<checks<<",\"strength_draws\":"<<mh_draws(handle)<<",\"degree_matched_accepts\":"<<mh_accepted(handle)<<",\"changed_outer\":"<<mh_changed(handle)<<",\"author_strength_count\":\""<<mh_strength_count(handle)<<"\"}\n";run.close();
 return 0;
 }catch(const std::exception&e){std::cerr<<e.what()<<'\n';return 2;}}
