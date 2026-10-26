 
// [[Rcpp::plugins(cpp17)]]
#include "../../../external/cgsampr/src/weighted_graph.h"
#include "../../../external/cgsampr/src/AuxiliaryFunctions.h"
int sampleDelta(const Weighted::DeltaRange&,const Weighted::Factor,std::default_random_engine&);
void reset(std::vector<Weighted::Edge*>&);
#include <unordered_map>
#include <array>
#include <sstream>
#include <cstdlib>
#include <memory>
using IM=Rcpp::IntegerMatrix;
using IV=Rcpp::IntegerVector;
#include <chrono>
#include <fstream>
#include <iomanip>
#include <set>
#include <algorithm>

using WE=Weighted::Edge;
using WV=Weighted::Vertex;
class WgsAdapter : public Weighted::Directed::SG::Graph {
  int nr_,nc_,bad_=0;
  std::vector<int> rd_,cd_,target_rd_,target_cd_;
  std::mt19937_64 control_;
  struct Frame {
    std::unordered_map<WE*,int> weights;
    std::unordered_map<WV*,std::vector<WE*>> incoming;
    std::unordered_map<WV*,std::array<int,3>> scratch;
    std::unordered_map<int,int> rows,columns;
    void clear(){weights.clear();incoming.clear();scratch.clear();rows.clear();columns.clear();}
  } frame_;
  void capture(const std::vector<WE*>& cycle) {
    for(WE* e:cycle) {
      frame_.weights.emplace(e,e->weight());
      WV* head=e->head_;
      if(!frame_.incoming.count(head)) {
        frame_.incoming.emplace(head,head->in_edges);
        frame_.scratch.emplace(head,std::array<int,3>{head->n_up,head->n_low,head->n_int});
      }
      frame_.rows.emplace(e->tail_->index,rd_[e->tail_->index]);
      int c=e->head_->index-nr_;
      frame_.columns.emplace(c,cd_[c]);
    }
  }
  void degree_delta(int r,int c,int change) {
    bad_-=rd_[r]!=target_rd_[r]; bad_-=cd_[c]!=target_cd_[c];
    rd_[r]+=change; cd_[c]+=change;
    bad_+=rd_[r]!=target_rd_[r]; bad_+=cd_[c]!=target_cd_[c];
  }
public:
  unsigned long long inner=0,rollbacks=0,returns=0,discarded_walks=0,cell_updates=0;
  struct Outcome {int reason;unsigned long long inner_steps;};
  WgsAdapter(Rcpp::IntegerMatrix a,Rcpp::IntegerMatrix fixed,unsigned long long seed)
    :Weighted::Directed::SG::Graph(a,fixed),nr_(a.nrow()),nc_(a.ncol()),
      rd_(nr_),cd_(nc_),target_rd_(nr_),target_cd_(nc_),control_(seed^0x9e3779b97f4a7c15ULL) {
    generator_.seed(static_cast<std::default_random_engine::result_type>(seed));
    for(int r=0;r<nr_;++r)for(int c=0;c<nc_;++c)if(a(r,c)>0){++rd_[r];++cd_[c];}
    target_rd_=rd_;target_cd_=cd_;
  }

  ~WgsAdapter() override {
    for(int r=0;r<nr_;++r)std::free(edges_[r]);
    std::free(edges_);edges_=nullptr;
  }
  void author_step() {Weighted::Directed::SG::Graph::sampleStep();}
  void primitive_step() {
    std::vector<WE*> cycle;
    ++inner;
    int discard=sampleKernel(cycle);
    if(discard){reset(cycle);++discarded_walks;return;}
    capture(cycle);
    Weighted::DeltaRange dr=getDeltaRange(cycle);
    Weighted::Factor factor=getBoundaryWeights(cycle,dr);
    int delta=sampleDelta(dr,factor,generator_);
    if(delta!=0){mixing_+=1.;cell_updates+=cycle.size();}
     
    int sign=1;
    for(WE* e:cycle) {
      int old=e->weight(),next=old+sign*delta;
      degree_delta(e->tail_->index,e->head_->index-nr_,(next>0)-(old>0));
      sign=-sign;
    }
    updateWeights(cycle,delta);
    reset(cycle);
  }
  void rollback() {
    for(auto item:frame_.weights)item.first->weight(item.second);

    for(auto& item:frame_.incoming) {
      WV* head=item.first;
      std::vector<std::pair<WE*,int>> positive;
      for(WE* e:head->in_edges)positive.emplace_back(e,e->weight());
      for(auto p:positive)p.first->weight(0);
      std::unordered_map<WE*,int> value;
      for(auto p:positive)value.emplace(p.first,p.second);
      for(WE* e:item.second)e->weight(value.at(e));
      auto scratch=frame_.scratch.at(head);
      head->n_up=scratch[0];head->n_low=scratch[1];head->n_int=scratch[2];
    }
    for(auto item:frame_.rows)rd_[item.first]=item.second;
    for(auto item:frame_.columns)cd_[item.first]=item.second;
    bad_=0;++rollbacks;
     
    frame_.clear();
  }
  Outcome advance(const std::string& mode,double rho) {
    if(!frame_.weights.empty())Rcpp::stop("unfinished transaction");
    if(mode!="strength" && mode!="degree_reject" && mode!="trace")Rcpp::stop("unknown mode");
    if(mode=="trace" && !(rho>0&&rho<1))Rcpp::stop("rho must be fixed in (0,1)");
    unsigned long long before=inner;
    if(mode=="strength"){
      primitive_step();frame_.clear();
      return {1,inner-before};
    }
    if(bad_!=0)Rcpp::stop("joint adapter must start inside F");
    for(;;) {
      primitive_step();
      if(bad_==0){
        bool changed=false;
        for(auto item:frame_.weights)changed|=item.first->weight()!=item.second;
        frame_.clear();++returns;
        return {changed?2:3,inner-before};
      }
      if(mode=="degree_reject" || std::uniform_real_distribution<double>(0.,1.)(control_)<rho){
        rollback();
        return {4,inner-before};
      }
    }
  }
  Rcpp::List step(const std::string& mode,double rho) {
    auto result=advance(mode,rho);
    static const char* names[]={"unused","strength_step","return_move","return_hold","rollback_hold"};
    return Rcpp::List::create(Rcpp::_["reason"]=names[result.reason],Rcpp::_["inner_steps"]=double(result.inner_steps));
  }
  int violations() const{return bad_;}
  Rcpp::List signature() {
    Rcpp::List incoming(nc_);
    for(int c=0;c<nc_;++c){
      Rcpp::IntegerVector rows(vertices_[nr_+c].in_edges.size());
      for(size_t j=0;j<vertices_[nr_+c].in_edges.size();++j)rows[j]=vertices_[nr_+c].in_edges[j]->tail_->index;
      incoming[c]=rows;
    }
    Rcpp::IntegerMatrix positions(nr_,nc_);
    Rcpp::LogicalMatrix visited(nr_,nc_);
    for(int r=0;r<nr_;++r)for(int c=0;c<nc_;++c){positions(r,c)=edges_[r][c].pos();visited(r,c)=edges_[r][c].visited();}
    auto copy=generator_;Rcpp::NumericVector peek(8);
    for(int j=0;j<8;++j)peek[j]=copy();
    return Rcpp::List::create(Rcpp::_["matrix"]=Rcpp::clone(adjacency_matrix_),Rcpp::_["incoming"]=incoming,
                              Rcpp::_["positions"]=positions,Rcpp::_["visited"]=visited,Rcpp::_["next_rng"]=peek,
                              Rcpp::_["degree_violations"]=bad_,Rcpp::_["inner_steps"]=double(inner),Rcpp::_["rollbacks"]=double(rollbacks));
  }
};

// [[Rcpp::export]]
SEXP wgs_create(Rcpp::IntegerMatrix matrix,Rcpp::IntegerMatrix fixed,double seed){
  for(int r=0;r<matrix.nrow();++r){
    long long s=0;for(int c=0;c<matrix.ncol();++c){if(matrix(r,c)<0)Rcpp::stop("weights must be nonnegative");s+=matrix(r,c);}
    if(s>INT_MAX)Rcpp::stop("author int32 row-strength limit");
  }
  for(int c=0;c<matrix.ncol();++c){long long s=0;for(int r=0;r<matrix.nrow();++r)s+=matrix(r,c);if(s>INT_MAX)Rcpp::stop("author int32 column-strength limit");}
  if(seed<0||seed>9007199254740991.)Rcpp::stop("seed outside exact double integer range");
  return Rcpp::XPtr<WgsAdapter>(new WgsAdapter(matrix,fixed,static_cast<unsigned long long>(seed)),true);
}
// [[Rcpp::export]]
Rcpp::List wgs_step(SEXP pointer,std::string mode="trace",double rho=.05){return Rcpp::XPtr<WgsAdapter>(pointer)->step(mode,rho);}
// [[Rcpp::export]]
Rcpp::IntegerMatrix wgs_matrix(SEXP pointer){return Rcpp::clone(Rcpp::XPtr<WgsAdapter>(pointer)->adjacency_matrix());}
// [[Rcpp::export]]
Rcpp::List wgs_signature(SEXP pointer){return Rcpp::XPtr<WgsAdapter>(pointer)->signature();}
// [[Rcpp::export]]
void wgs_author_step(SEXP pointer){Rcpp::XPtr<WgsAdapter>(pointer)->author_step();}

using U=unsigned long long;
using I=long long;
using S128=__int128_t;
using Clock=std::chrono::steady_clock;
struct WgsProbeGraph {
  int nr,nc,D=0;Rcpp::IntegerMatrix matrix;
  explicit WgsProbeGraph(Rcpp::IntegerMatrix a):nr(a.nrow()),nc(a.ncol()),matrix(a){}
  I value(int r,int c)const{return matrix(r,c);}
};
#include "common_probe_observer.hpp"
#include "readonly_sigma_observer.hpp"
static void validate_integer_matrix(const Rcpp::IntegerMatrix& matrix){
 for(int r=0;r<matrix.nrow();++r){long long sum=0;for(int c=0;c<matrix.ncol();++c){if(matrix(r,c)<0)Rcpp::stop("negative weight");sum+=matrix(r,c);}if(sum>INT_MAX)Rcpp::stop("author int32 row-strength limit");}
 for(int c=0;c<matrix.ncol();++c){long long sum=0;for(int r=0;r<matrix.nrow();++r)sum+=matrix(r,c);if(sum>INT_MAX)Rcpp::stop("author int32 column-strength limit");}
}
 
static bool wgs_integer_budgets(double n,double burn,double trace_every){
 return n>=1&&n<=1000000000&&std::floor(n)==n&&burn>=0&&burn<n&&std::floor(burn)==burn&&trace_every>=0&&std::floor(trace_every)==trace_every;
}
// [[Rcpp::export]]
bool wgs_budget_guard(double n,double burn,double trace_every){return wgs_integer_budgets(n,burn,trace_every);}
// [[Rcpp::export]]
Rcpp::List wgs_job(std::string input,std::string queries,std::string prefix,
                  double seed,double n,double burn,double trace_every,
                  std::string mode="trace",double rho=.05,double check_every=10000){
 auto start=Clock::now();
 if(mode!="degree_reject"&&mode!="trace")Rcpp::stop("formal joint job must use degree_reject or trace");
 if(!wgs_integer_budgets(n,burn,trace_every))Rcpp::stop("bad integer budgets");
 if(!(seed>=0&&seed<=9007199254740991.&&std::floor(seed)==seed))Rcpp::stop("bad seed");
 std::ifstream in(input);int nr,nc;
 if(!(in>>nr>>nc)||nr<=0||nc<=0)Rcpp::stop("common observer requires positive shape");
 Rcpp::IntegerMatrix a(nr,nc),fixed(nr,nc);int r,c;long long w;
 for(;;){in>>std::ws;if(in.eof())break;if(!(in>>r>>c>>w))Rcpp::stop("malformed edge");if(r<0||r>=nr||c<0||c>=nc||w<=0||w>INT_MAX||a(r,c))Rcpp::stop("invalid edge");a(r,c)=w;}
 validate_integer_matrix(a);
 U N=static_cast<U>(n),B=static_cast<U>(burn),trace=static_cast<U>(trace_every),check=static_cast<U>(check_every);
 std::vector<I> target_strength(nr+nc,0);std::vector<int>target_degree(nr+nc,0);
 for(int rr=0;rr<nr;++rr)for(int cc=0;cc<nc;++cc){target_strength[rr]+=a(rr,cc);target_strength[nr+cc]+=a(rr,cc);if(a(rr,cc)>0){++target_degree[rr];++target_degree[nr+cc];}}
 auto eff=init_fixed(a,fixed);bool singleton=true;for(int j=0;j<eff.size();++j)singleton=singleton&&eff[j];
 std::unique_ptr<WgsAdapter> sampler;
 if(!singleton)sampler=std::make_unique<WgsAdapter>(a,fixed,static_cast<unsigned long long>(seed));
 WgsProbeGraph graph(sampler?sampler->adjacency_matrix():a);
 FixedProbeStatistics observer(graph,B,N,queries,0,trace);
 ReadOnlySigmaObserver sigma_observer(graph,B,N,trace,prefix);
 auto all_check=[&](){
   if(sampler&&sampler->violations()!=0)Rcpp::stop("degree violation at endpoint");
   std::vector<I> strength(nr+nc,0);std::vector<int>degrees(nr+nc,0);
   for(int rr=0;rr<nr;++rr)for(int cc=0;cc<nc;++cc){I value=graph.value(rr,cc);if(value<0)Rcpp::stop("negative weight");strength[rr]+=value;strength[nr+cc]+=value;if(value>0){++degrees[rr];++degrees[nr+cc];}}
   if(strength!=target_strength||degrees!=target_degree)Rcpp::stop("four margins changed");
 };
 all_check();U checks=1,changed=0;double build=std::chrono::duration<double>(Clock::now()-start).count();auto sampling=Clock::now();
 for(U t=1;t<=N;++t){
   if(sampler){auto result=sampler->advance(mode,rho);changed+=result.reason==2;}
   observer.observe(graph,t,sampler?sampler->cell_updates:0);sigma_observer.observe(graph,t,sampler?sampler->cell_updates:0);
   if((check&&t%check==0)||t==N){all_check();++checks;}
 }
 double loop=std::chrono::duration<double>(Clock::now()-sampling).count();sigma_observer.finish();observer.write(prefix);
 std::ofstream final(prefix+".final.graph");final<<nr<<' '<<nc<<'\n';
 for(int rr=0;rr<nr;++rr)for(int cc=0;cc<nc;++cc)if(graph.value(rr,cc)>0)final<<rr<<' '<<cc<<' '<<graph.value(rr,cc)<<'\n';final.close();if(!final)Rcpp::stop("final graph write failed");
 double total=std::chrono::duration<double>(Clock::now()-start).count();
 std::ofstream out(prefix+".run.json");out<<std::setprecision(17)<<"{\"status\":\"ok\",\"method\":\"wgs_"<<mode<<"\",\"seed\":"<<seed<<",\"outer\":"<<N<<",\"burn\":"<<B<<",\"nr\":"<<nr<<",\"nc\":"<<nc<<",\"build_seconds\":"<<build<<",\"loop_seconds\":"<<loop<<",\"total_seconds\":"<<total<<",\"checks\":"<<checks<<",\"all_margins_passed\":true,\"changed_outer\":"<<changed<<",\"rho\":"<<rho<<",\"strength_inner_steps\":"<<(sampler?sampler->inner:0)<<",\"rollbacks\":"<<(sampler?sampler->rollbacks:0)<<",\"singleton_strength_certificate\":"<<(singleton?"true":"false")<<"}\n";out.flush();if(!out)Rcpp::stop("run report write failed");
 return Rcpp::List::create(Rcpp::_["status"]="ok",Rcpp::_["total_seconds"]=total,Rcpp::_["loop_seconds"]=loop,Rcpp::_["build_seconds"]=build,Rcpp::_["outer"]=n,Rcpp::_["burn"]=burn,Rcpp::_["all_margins_passed"]=true);
}
