 

#include <list>
#include <iterator>
#include <memory>
#include <utility>

struct BlockClassCache {
 using Key=std::array<I,27>;
 struct Entry {Key key;std::unique_ptr<FastCountedBlock>solver;U estimated_bytes;};
 using Entries=std::list<Entry>;
 size_t capacity=0;
 Entries entries;std::map<Key,typename Entries::iterator>lookup;
 U estimated_bytes=0;bool in_use=false;
 explicit BlockClassCache(size_t cap=0):capacity(cap){if(cap>128)throw std::runtime_error("block class cache capacity exceeds 128");}
 BlockClassCache(const BlockClassCache&)=delete;BlockClassCache&operator=(const BlockClassCache&)=delete;

 static Key key_for(const std::vector<I>&a,const std::vector<I>&b){
  if(a.size()!=b.size()||a.size()>12)throw std::runtime_error("cache arrays need same size <=12");
  Key key{};key[0]=I(a.size());I combined=0;
  for(size_t j=0;j<a.size();++j){
   if(a[j]<0||b[j]<0||a[j]>std::numeric_limits<I>::max()-b[j])throw std::runtime_error("invalid cache int64 weight");
   I c=a[j]+b[j];if(combined>std::numeric_limits<I>::max()-c)throw std::runtime_error("cache block total exceeds int64");combined+=c;
   key[1]+=a[j]>0;key[2]+=a[j];key[3+2*j]=c;key[4+2*j]=I(a[j]>0)+I(b[j]>0);
  }
  return key;
 }
 static void detach(FastCountedBlock&solver)noexcept{
  solver.stat=nullptr;for(auto&suffix:solver.suffix_counts)suffix.stat=nullptr;
  solver.a.clear();solver.b.clear();
 }
 struct Binding {
  FastCountedBlock&solver;
  Binding(FastCountedBlock&s,const std::vector<I>&a,const std::vector<I>&b,Counters&stat):solver(s){
    
   solver.a=a;solver.b=b;solver.stat=&stat;
   for(auto&suffix:solver.suffix_counts)suffix.stat=&stat;
  }
  Binding(const Binding&)=delete;Binding&operator=(const Binding&)=delete;
  ~Binding(){detach(solver);}
 };
 struct UseGuard {
  BlockClassCache&cache;
  explicit UseGuard(BlockClassCache&c):cache(c){if(cache.in_use)throw std::runtime_error("block class cache callback is not reentrant");cache.in_use=true;}
  ~UseGuard(){cache.in_use=false;}
 };
 static U payload_bytes(const FastCountedBlock&s){
   
  __uint128_t n=sizeof(Entry)+sizeof(FastCountedBlock)+sizeof(std::pair<const Key,typename Entries::iterator>)+5*sizeof(void*);
  n+=(s.a.capacity()+s.b.capacity()+s.c.capacity()+s.bounds.capacity())*sizeof(I);
  n+=(s.exclusive.capacity()+s.shared.capacity()+s.variable.capacity())*sizeof(int);
  n+=s.small_supports.capacity()*sizeof(FastCountedBlock::SmallSupport);
  n+=s.general_supports.capacity()*sizeof(FastCountedBlock::GeneralSupport);
  n+=s.general_total.a.capacity()*sizeof(uint32_t);
  for(const auto&support:s.general_supports)n+=support.count.a.capacity()*sizeof(uint32_t);
  n+=s.suffix_counts.capacity()*sizeof(ReusedCount);
  for(const auto&suffix:s.suffix_counts)n+=suffix.shift.capacity()*sizeof(S128)+suffix.coefficient.capacity()*sizeof(I);
  return checked_u128(n,"block cache estimated bytes");
 }
 void gauges(Counters&stat){
  stat.block_cache_entries_current=entries.size();stat.block_cache_entries_peak=std::max(stat.block_cache_entries_peak,U(entries.size()));
  stat.block_cache_estimated_bytes_current=estimated_bytes;stat.block_cache_estimated_bytes_peak=std::max(stat.block_cache_estimated_bytes_peak,estimated_bytes);
 }
 template<class Callback>
 auto use(const std::vector<I>&a,const std::vector<I>&b,Counters&stat,Callback&&callback)
  ->decltype(callback(std::declval<FastCountedBlock&>())){
  UseGuard guard(*this);
  if(!capacity){FastCountedBlock solver(a,b,&stat);return callback(solver);}
  stat.block_cache_lookups++;
  auto key_start=Clock::now();Key key=key_for(a,b);
  stat.block_cache_key_nanoseconds+=std::chrono::duration_cast<std::chrono::nanoseconds>(Clock::now()-key_start).count();
  auto found=lookup.find(key);typename Entries::iterator entry;
  if(found!=lookup.end()){
   stat.block_cache_hits++;entry=found->second;entries.splice(entries.begin(),entries,entry);
  }else{
   stat.block_cache_misses++;auto build_start=Clock::now();
   auto solver=std::make_unique<FastCountedBlock>(a,b,&stat);detach(*solver);
   stat.block_cache_build_nanoseconds+=std::chrono::duration_cast<std::chrono::nanoseconds>(Clock::now()-build_start).count();
   U bytes=payload_bytes(*solver);
   if(entries.size()==capacity){
    auto old=std::prev(entries.end());estimated_bytes-=old->estimated_bytes;lookup.erase(old->key);entries.erase(old);stat.block_cache_evictions++;
   }
   entries.push_front(Entry{key,std::move(solver),bytes});entry=entries.begin();
   try{lookup.emplace(key,entry);}catch(...){entries.pop_front();throw;}
   estimated_bytes=checked_u128(__uint128_t(estimated_bytes)+bytes,"block cache total estimated bytes");
  }
  gauges(stat);
  stat.block_max_count_bits=std::max(stat.block_max_count_bits,U(entry->solver->small?wide_bits(entry->solver->small_total):entry->solver->general_total.bits()));
  stat.compressed_full_descriptor_max_terms=std::max(stat.compressed_full_descriptor_max_terms,entry->solver->descriptor_terms_full);
  stat.compressed_solver_descriptor_max_terms=std::max(stat.compressed_solver_descriptor_max_terms,entry->solver->descriptor_terms_max);
  auto bind_start=Clock::now();Binding binding(*entry->solver,a,b,stat);
  stat.block_cache_bind_nanoseconds+=std::chrono::duration_cast<std::chrono::nanoseconds>(Clock::now()-bind_start).count();
  return callback(*entry->solver);
 }
};
