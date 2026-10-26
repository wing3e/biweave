#pragma once
#include <gmpxx.h>
#include <algorithm>
#include <cstdint>
#include <map>
#include <set>
#include <stdexcept>
#include <string>
#include <utility>
#include <vector>
#include <limits>
 
namespace grouped_two {
using U=uint64_t; using Wide=__uint128_t;
struct GroupedTwoProblem {
 static constexpr U CELL_BUDGET=1000000,WORK_BUDGET=0x1312d00,MEMORY_BUDGET=64ULL*1024*1024;
 struct Polynomial {std::vector<mpz_class> value;mpz_class divided_gcd=1;};
 struct Type {U d=0,cap=0;std::vector<size_t> actors;std::map<U,Polynomial> powers;};
 bool active=false,deficit=false;std::string reason="not_initialized";
 std::vector<U>d,cap;std::vector<Type>types;std::vector<Polynomial>suffix;
 U H=0,P=0,C=0,target=0,cells_bound=0,work_bound=0,bits_bound=0,estimated_bytes=0,actual_multiply_adds=0;
 static U bits(U x){U b=0;while(x){++b;x>>=1;}return b;}
 static U exact_u(Wide x){if(x>std::numeric_limits<U>::max())throw std::overflow_error("grouped core uint64 guard");return U(x);}
 static void sizes(U n,std::set<U>&out){if(!out.insert(n).second||n<=1)return;sizes(n/2,out);sizes(n-n/2,out);}
 static Polynomial normalize(std::vector<mpz_class>v){
  while(v.size()>1&&v.back()==0)v.pop_back();mpz_class g=0;
  for(const auto&x:v){if(x<0)throw std::runtime_error("negative polynomial");mpz_gcd(g.get_mpz_t(),g.get_mpz_t(),x.get_mpz_t());}
  if(g==0)throw std::runtime_error("zero polynomial");for(auto&x:v)x/=g;return {std::move(v),g};
 }
 Polynomial multiply(const Polynomial&a,const Polynomial&b){
  U n=std::min<U>(target+1,U(a.value.size()+b.value.size()-1));std::vector<mpz_class>v(n);
  for(U i=0;i<a.value.size()&&i<n;++i)for(U j=0;j<b.value.size()&&i+j<n;++j){if(++actual_multiply_adds>work_bound)throw std::runtime_error("work preflight inconsistent");v[i+j]+=a.value[i]*b.value[j];}
  return normalize(std::move(v));
 }
 Polynomial row(U di,U ci)const{
  U m=std::min(target,ci);std::vector<mpz_class>v(m+1);v[0]=1;
  if(deficit){for(U j=1;j<=m;++j)v[0]*=mpz_class(di-ci+j);
   for(U t=0;t<m;++t){mpz_class denominator=di-ci+t+1;if(!mpz_divisible_p(v[t].get_mpz_t(),denominator.get_mpz_t()))throw std::runtime_error("scaled deficit nonexact division");v[t+1]=v[t]/denominator;v[t+1]*=mpz_class(ci-t);}}
  else for(U h=0;h<m;++h){v[h+1]=v[h]*mpz_class(di-h);if(!mpz_divisible_ui_p(v[h+1].get_mpz_t(),h+1))throw std::runtime_error("canonical nonexact division");v[h+1]/=mpz_class(h+1);}
  return normalize(std::move(v));
 }
 const Polynomial&power(size_t type,U n){
  auto&t=types[type];auto old=t.powers.find(n);if(old!=t.powers.end())return old->second;
  Polynomial p;if(n==0)p={{mpz_class(1)},mpz_class(1)};else if(n==1)p=row(t.d,t.cap);else{const auto&a=power(type,n/2);const auto&b=power(type,n-n/2);p=multiply(a,b);}
  return t.powers.emplace(n,std::move(p)).first->second;
 }
 void initialize(const std::vector<U>&quota,const std::vector<U>&caps,U high){
  *this=GroupedTwoProblem();d=quota;cap=caps;H=high;if(d.size()!=cap.size()||d.empty()){reason="shape";return;}
  Wide ps=0,cs=0;std::map<std::pair<U,U>,size_t>index;
  for(size_t i=0;i<d.size();++i){if(cap[i]>d[i]){reason="capacity";return;}ps+=d[i];cs+=cap[i];auto key=std::make_pair(d[i],cap[i]);auto [it,newtype]=index.emplace(key,types.size());if(newtype)types.push_back(Type{d[i],cap[i],{}, {}});types[it->second].actors.push_back(i);}
  if(ps>std::numeric_limits<U>::max()||cs>std::numeric_limits<U>::max()){reason="quota_overflow_guard";return;}P=U(ps);C=U(cs);if(H>C||H>P){reason="infeasible";return;}U D=C-H;deficit=D<H;target=deficit?D:H;
  if(target>=CELL_BUDGET){reason="cell_guard";return;}
  Wide cell=Wide(types.size()+1)*(target+1),work=0,startup=0,primitive_bits_sum=0;
  for(auto&t:types){std::set<U>s;sizes(t.actors.size(),s);cell+=Wide(s.size())*(target+1);work+=Wide(s.size()+1)*(target+1)*(target+1);startup+=4*Wide(std::min(target,t.cap));Wide rowbits=Wide(std::min(target,t.cap))*bits(std::max<U>(1,t.d))+1;
   Wide groupbits=2+bits(target+1)+Wide(target)*(bits(t.actors.size())+bits(std::max<U>(1,target)))+Wide(std::min<U>(t.actors.size(),target))*rowbits;primitive_bits_sum+=groupbits;}
  work+=Wide(types.size()+1)*(target+1)*(target+1)+startup;

  cells_bound=cell>std::numeric_limits<U>::max()?std::numeric_limits<U>::max():U(cell);work_bound=work>std::numeric_limits<U>::max()?std::numeric_limits<U>::max():U(work);
  if(cell>CELL_BUDGET){reason="cell_guard";return;}if(work>WORK_BUDGET){reason="work_guard";return;}
  Wide highbits=std::min<Wide>(Wide(P)+1,Wide(H)*bits(P)+1);Wide defbits=2*primitive_bits_sum+2*Wide(types.size()+1)*bits(target+1)+2;
  Wide chosen_bits=deficit?defbits:highbits;if(chosen_bits>std::numeric_limits<U>::max()){reason="payload_guard";return;}bits_bound=U(chosen_bits);
  Wide per=64+8*((Wide(bits_bound)+63)/64);Wide memory=(cell+4*(target+1))*per+Wide(d.size())*32+Wide(types.size())*256;
  estimated_bytes=memory>std::numeric_limits<U>::max()?std::numeric_limits<U>::max():U(memory);if(memory>MEMORY_BUDGET){reason="payload_guard";return;}
  try{for(size_t t=0;t<types.size();++t)power(t,types[t].actors.size());suffix.resize(types.size()+1);suffix.back()={{mpz_class(1)},mpz_class(1)};
   for(size_t i=types.size();i-->0;)suffix[i]=multiply(power(i,types[i].actors.size()),suffix[i+1]);
   if(target>=suffix[0].value.size()||suffix[0].value[target]==0){reason="no_completions";return;}active=true;reason="compiled";
  }catch(const std::bad_alloc&){types.clear();suffix.clear();active=false;reason="allocation_failure";}
 }
 const mpz_class&coefficient(const Polynomial&p,U n)const{static const mpz_class zero=0;return n<p.value.size()?p.value[n]:zero;}

 template<class Pick>U choice(const Polynomial&a,const Polynomial&b,U sum,Pick&pick)const{
  std::vector<std::pair<U,mpz_class>>mass;mpz_class total=0;for(U j=0;j<=sum&&j<a.value.size();++j){mpz_class m=a.value[j]*coefficient(b,sum-j);if(m>0){mass.emplace_back(j,m);total+=m;}}
  if(total==0)throw std::runtime_error("empty conditional split");mpz_class rank=pick(total);if(rank<0||rank>=total)throw std::runtime_error("rank outside exact bound");for(auto&[j,m]:mass){if(rank<m)return j;rank-=m;}throw std::runtime_error("decode fell through");
 }
 template<class Pick>void split(size_t ti,U begin,U n,U amount,std::vector<U>&out,Pick&pick){
  auto&t=types[ti];if(amount==0){for(U j=0;j<n;++j)out[t.actors[begin+j]]=deficit?t.cap:0;return;}
  if(n==1){if(amount>t.cap)throw std::runtime_error("invalid leaf quota");out[t.actors[begin]]=deficit?t.cap-amount:amount;return;}
  U nl=n/2,nr=n-nl;U left=choice(power(ti,nl),power(ti,nr),amount,pick);split(ti,begin,nl,left,out,pick);split(ti,begin+nl,nr,amount-left,out,pick);
 }
 template<class Pick>std::vector<U>draw(Pick pick){if(!active)throw std::runtime_error("inactive grouped problem");std::vector<U>out(d.size());if(target==0){if(deficit)out=cap;return out;}U remaining=target;
  for(size_t ti=0;ti<types.size();++ti){U amount=choice(power(ti,types[ti].actors.size()),suffix[ti+1],remaining,pick);split(ti,0,types[ti].actors.size(),amount,out,pick);remaining-=amount;}
  if(remaining)throw std::runtime_error("quota residue");return out;
 }
  
 mpq_class split_probability(size_t ti,U begin,U n,U amount,const std::vector<U>&h){
  auto&t=types[ti];if(n<=1||amount==0)return 1;U nl=n/2,left=0;for(U j=0;j<nl;++j)left+=deficit?t.cap-h[t.actors[begin+j]]:h[t.actors[begin+j]];
  const auto&a=power(ti,nl);const auto&b=power(ti,n-nl);mpz_class total=0;for(U j=0;j<=amount&&j<a.value.size();++j)total+=a.value[j]*coefficient(b,amount-j);
  mpq_class q(a.value[left]*coefficient(b,amount-left),total);q.canonicalize();return q*split_probability(ti,begin,nl,left,h)*split_probability(ti,begin+nl,n-nl,amount-left,h);
 }
 mpq_class probability(const std::vector<U>&h){if(!active||h.size()!=d.size())throw std::runtime_error("probability shape");U sum=0;for(size_t i=0;i<h.size();++i){if(h[i]>cap[i])return 0;sum+=h[i];}if(sum!=H)return 0;
  mpq_class answer=1;U remaining=target;
  for(size_t ti=0;ti<types.size();++ti){U amount=0;for(size_t i:types[ti].actors)amount+=deficit?cap[i]-h[i]:h[i];const auto&a=power(ti,types[ti].actors.size());const auto&b=suffix[ti+1];mpz_class total=0;for(U j=0;j<=remaining&&j<a.value.size();++j)total+=a.value[j]*coefficient(b,remaining-j);mpq_class branch(coefficient(a,amount)*coefficient(b,remaining-amount),total);branch.canonicalize();answer*=branch;answer*=split_probability(ti,0,types[ti].actors.size(),amount,h);remaining-=amount;}
  return answer;
 }
 U maximum_cached_bits()const{U b=0;for(const auto&t:types)for(const auto&[n,p]:t.powers)for(const auto&v:p.value)if(v>0)b=std::max<U>(b,mpz_sizeinbase(v.get_mpz_t(),2));for(const auto&p:suffix)for(const auto&v:p.value)if(v>0)b=std::max<U>(b,mpz_sizeinbase(v.get_mpz_t(),2));return b;}
 U cached_cells()const{U n=0;for(const auto&t:types)for(const auto&[sz,p]:t.powers)n+=p.value.size();for(const auto&p:suffix)n+=p.value.size();return n;}
};
}
