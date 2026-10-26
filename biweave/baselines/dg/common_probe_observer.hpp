 

#include <set>
U probe_unsigned_v12(const std::string&s,const std::string&name){
 if(s.empty()||s.find_first_not_of("0123456789")!=std::string::npos)throw std::runtime_error(name+" requires unsigned integer");
 size_t used=0;U value=std::stoull(s,&used);if(used!=s.size())throw std::runtime_error(name+" has trailing characters");return value;
}
std::string probe_decimal_v12(S128 value){
 if(value<0)throw std::runtime_error("negative probe integer sum");if(!value)return "0";std::string s;
 while(value){s.push_back(char('0'+value%10));value/=10;}std::reverse(s.begin(),s.end());return s;
}
struct FixedProbeStatistics {
 struct Pair {int r,s;I threshold;U tail=0;S128 sum=0;};
 struct Cell {int r,c;I threshold;U presence=0,tail=0;S128 sum=0;};
 struct Batch {
  U first,last,count=0;std::vector<U>pair_tail,cell_presence,cell_tail;std::vector<S128>pair_sum,cell_sum;
  Batch(U first_,size_t np,size_t nc):first(first_),last(first_),pair_tail(np,0),cell_presence(nc,0),cell_tail(nc,0),pair_sum(np,0),cell_sum(nc,0){}
 };
 struct Record {U outer;std::vector<I>minimum,weights;};
 int nr,nc;U burn,budget,batch_width,trace_every,observed_outer=0,postburn_count=0;
 U last_updates=0,pending=0,feature_recomputations=0,run_length_extensions=0,feature_flushes=0;
 bool cached=false;std::vector<Pair>pairs;std::vector<Cell>cells;
 std::vector<I>cached_minimum,cached_weights;std::vector<Batch>batches;std::vector<Record>records;
 unsigned long long initialization_nanoseconds=0,observation_nanoseconds=0,finalization_nanoseconds=0;
 static I pair_minimum(const WgsProbeGraph&g,int r,int s){
  I result=0;for(int c=0;c<g.nc;++c)result+=std::min(g.value(r,c),g.value(s,c));return result;
 }
 FixedProbeStatistics(const WgsProbeGraph&initial,U b,U n,const std::string&queries,U width,U interval):
  nr(initial.nr),nc(initial.nc),burn(b),budget(n),batch_width(width),trace_every(interval){
  auto start=Clock::now();if(!n||b>=n)throw std::runtime_error("probe requires 0<=burn<N");
  std::ifstream in(queries);std::string magic;int qr,qc,np,ncells;
  if(!(in>>magic>>qr>>qc>>np>>ncells)||magic!="fixed_probe_queries_v1"||qr!=nr||qc!=nc||np<0||ncells<0||np>64||ncells>64||np+ncells==0)
   throw std::runtime_error("invalid probe header, shape or query count");
  std::set<std::pair<int,int>>seen_pairs,seen_cells;
  for(int p=0;p<np;++p){int r,s;I threshold;if(!(in>>r>>s>>threshold)||r<0||s<=r||s>=nr||threshold<0||!seen_pairs.insert({r,s}).second)
    throw std::runtime_error("invalid duplicate probe pair");
   if(pair_minimum(initial,r,s)!=threshold)throw std::runtime_error("probe pair threshold differs from original input");
   pairs.push_back({r,s,threshold});
  }
  for(int c=0;c<ncells;++c){int r,j;I threshold;if(!(in>>r>>j>>threshold)||r<0||r>=nr||j<0||j>=nc||threshold<0||!seen_cells.insert({r,j}).second)
    throw std::runtime_error("invalid duplicate probe cell");
   if(initial.value(r,j)!=threshold)throw std::runtime_error("probe cell threshold differs from original input");
   cells.push_back({r,j,threshold});
  }
  in>>std::ws;if(!in.eof())throw std::runtime_error("extra probe query records");
  if(batch_width&&(budget-burn-1)/batch_width+1>100000)throw std::runtime_error("probe batch count exceeds100000");
  if(trace_every&&budget/trace_every>99998)throw std::runtime_error("probe trace count exceeds100000");
  if(trace_every)record(initial,0);
  initialization_nanoseconds=std::chrono::duration_cast<std::chrono::nanoseconds>(Clock::now()-start).count();
 }
 std::pair<std::vector<I>,std::vector<I>>features(const WgsProbeGraph&g)const{
  std::vector<I>minimum,weights;minimum.reserve(pairs.size());weights.reserve(cells.size());
  for(const auto&p:pairs)minimum.push_back(pair_minimum(g,p.r,p.s));
  for(const auto&c:cells)weights.push_back(g.value(c.r,c.c));return {minimum,weights};
 }
 void record(const WgsProbeGraph&g,U outer){auto values=features(g);records.push_back({outer,std::move(values.first),std::move(values.second)});}
 void flush(){
  if(!pending)return;Batch*batch=batch_width?&batches.back():nullptr;
  for(size_t j=0;j<pairs.size();++j){U tail=cached_minimum[j]>=pairs[j].threshold?pending:0;S128 sum=S128(cached_minimum[j])*S128(pending);
   pairs[j].tail+=tail;pairs[j].sum+=sum;if(batch){batch->pair_tail[j]+=tail;batch->pair_sum[j]+=sum;}
  }
  for(size_t j=0;j<cells.size();++j){U presence=cached_weights[j]>0?pending:0,tail=cached_weights[j]>=cells[j].threshold?pending:0;S128 sum=S128(cached_weights[j])*S128(pending);
   cells[j].presence+=presence;cells[j].tail+=tail;cells[j].sum+=sum;
   if(batch){batch->cell_presence[j]+=presence;batch->cell_tail[j]+=tail;batch->cell_sum[j]+=sum;}
  }
  if(batch)batch->count+=pending;pending=0;feature_flushes++;
 }
 void observe(const WgsProbeGraph&g,U outer,U updates){
  auto start=Clock::now();if(outer!=observed_outer+1||outer>budget||g.D)throw std::runtime_error("noncontiguous or illegal probe observation");
  observed_outer=outer;
  if(outer>burn){
   if(batch_width&&(outer-burn-1)%batch_width==0){flush();batches.emplace_back(outer,pairs.size(),cells.size());}
   if(!cached||updates!=last_updates){flush();auto values=features(g);cached_minimum=std::move(values.first);cached_weights=std::move(values.second);last_updates=updates;cached=true;feature_recomputations++;}
   else run_length_extensions++;
   pending++;postburn_count++;if(batch_width){batches.back().last=outer;if((outer-burn)%batch_width==0)flush();}
  }
  if(trace_every&&(outer%trace_every==0||outer==budget))record(g,outer);
  observation_nanoseconds+=std::chrono::duration_cast<std::chrono::nanoseconds>(Clock::now()-start).count();
 }
 static void sums(std::ostream&out,const std::vector<S128>&v){out<<'[';for(size_t j=0;j<v.size();++j)out<<(j?",":"")<<'"'<<probe_decimal_v12(v[j])<<'"';out<<']';}
 static void counts(std::ostream&out,const std::vector<U>&v){out<<'[';for(size_t j=0;j<v.size();++j)out<<(j?",":"")<<v[j];out<<']';}
 static void values(std::ostream&out,const std::vector<I>&v){out<<'[';for(size_t j=0;j<v.size();++j)out<<(j?",":"")<<v[j];out<<']';}
 void write(const std::string&prefix){
  auto start=Clock::now();flush();
  if(observed_outer!=budget||postburn_count!=budget-burn||feature_recomputations+run_length_extensions!=postburn_count)
   throw std::runtime_error("incomplete probe outer accounting");
  for(const auto&p:pairs)if(p.tail>postburn_count)throw std::runtime_error("probe tail count outside samples");
  for(const auto&c:cells)if(c.presence>postburn_count||c.tail>postburn_count)throw std::runtime_error("probe cell count outside samples");
  U count=0;for(const auto&b:batches){if(b.last-b.first+1!=b.count)throw std::runtime_error("probe batch accounting mismatch");count+=b.count;}
  if(batch_width&&count!=postburn_count)throw std::runtime_error("probe batches omit observations");
  std::ofstream out(prefix+".probe.json");if(!out)throw std::runtime_error("cannot create probe output");
  out<<"{\"format\":\"fixed_probe_statistics_v1\",\"nr\":"<<nr<<",\"nc\":"<<nc<<",\"outer_budget\":"<<budget<<",\"burn_outer\":"<<burn
     <<",\"observed_outer\":"<<observed_outer<<",\"postburn_count\":"<<postburn_count<<",\"pairs\":[";
  for(size_t j=0;j<pairs.size();++j){auto&p=pairs[j];if(j)out<<',';out<<"{\"rows\":["<<p.r<<','<<p.s<<"],\"observed_threshold\":"<<p.threshold<<",\"tail_count\":"<<p.tail<<",\"pair_min_sum\":\""<<probe_decimal_v12(p.sum)<<"\"}";}
  out<<"],\"cells\":[";
  for(size_t j=0;j<cells.size();++j){auto&c=cells[j];if(j)out<<',';out<<"{\"cell\":["<<c.r<<','<<c.c<<"],\"observed_threshold\":"<<c.threshold<<",\"presence_count\":"<<c.presence<<",\"tail_count\":"<<c.tail<<",\"weight_sum\":\""<<probe_decimal_v12(c.sum)<<"\"}";}
  out<<"],\"batch_width\":"<<batch_width<<",\"batches\":[";
  for(size_t j=0;j<batches.size();++j){auto&b=batches[j];if(j)out<<',';out<<"{\"first_outer\":"<<b.first<<",\"last_outer\":"<<b.last<<",\"count\":"<<b.count<<",\"pair_tail_counts\":";counts(out,b.pair_tail);out<<",\"pair_min_sums\":";sums(out,b.pair_sum);out<<",\"cell_presence_counts\":";counts(out,b.cell_presence);out<<",\"cell_tail_counts\":";counts(out,b.cell_tail);out<<",\"cell_weight_sums\":";sums(out,b.cell_sum);out<<'}';}
  out<<"],\"probe_trace_every\":"<<trace_every<<",\"feature_recomputations\":"<<feature_recomputations<<",\"feature_flushes\":"<<feature_flushes
     <<",\"run_length_extensions\":"<<run_length_extensions<<",\"integer_precision\":\"nonnegative signed128 sums; guarded input total<=INT64_MAX; outer<=UINT64_MAX\","
     <<"\"sample_policy\":\"Each complete outer burn<t<=N, including every hold and reject; fixed contiguous batches; no RNG and no support TV\","
     <<"\"missing_truth\":\"Real large graph exact target not supplied; query estimates are not accuracy metrics\"}\n";
  out.flush();if(!out)throw std::runtime_error("probe output write failed");
  if(trace_every){std::ofstream trace(prefix+".probe.trace.jsonl");if(!trace)throw std::runtime_error("cannot create probe trace");
   for(auto&r:records){trace<<"{\"iteration\":"<<r.outer<<",\"pair_minimum\":";values(trace,r.minimum);trace<<",\"cell_weights\":";values(trace,r.weights);trace<<"}\n";}
   trace.flush();if(!trace)throw std::runtime_error("probe trace write failed");
  }
  finalization_nanoseconds=std::chrono::duration_cast<std::chrono::nanoseconds>(Clock::now()-start).count();
 }
};
