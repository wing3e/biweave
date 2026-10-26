#pragma once
#include <time.h>

struct SupportSceneBitset {
 static constexpr U MEMORY_BUDGET_BYTES=64ULL*1024*1024;
 struct Axis {bool active=false;int actors=0,opposite=0;U words=0;std::vector<U>bits;};
 std::array<Axis,2>axis;bool requested=false,consumer_active=false;
 U build_axis_attempts=0,density_guard_axes=0,memory_guard_axes=0,allocation_guard_axes=0,payload_bytes=0,initial_entries=0;
 U support_transition_calls=0,axis_bit_updates=0,calls=0,bitset_calls=0,sparse_axis_calls=0,sparse_cost_calls=0,word_visits=0,private_labels=0,max_private_labels=0;
 mutable U checks=0,checked_words=0,checked_entries=0;double build_cpu_seconds=0;
 static double cpu(){timespec ts{};if(clock_gettime(CLOCK_PROCESS_CPUTIME_ID,&ts))throw std::runtime_error("bitset cpu clock");return double(ts.tv_sec)+double(ts.tv_nsec)/1e9;}
 bool active()const{return axis[0].active||axis[1].active;}
 void initialize(Graph&g,bool want,bool consumer){
  requested=want;consumer_active=want&&consumer;if(!consumer_active)return;const double ts=cpu();
  for(int o=0;o<2;++o){auto&a=axis[o];a.actors=o?g.nc:g.nr;a.opposite=o?g.nr:g.nc;a.words=(U(a.opposite)+63)/64;++build_axis_attempts;
   const __uint128_t cells=__uint128_t(a.actors)*a.words,bytes=cells*sizeof(U);
   if(__uint128_t(g.edges.size())<cells){++density_guard_axes;continue;}
   if(bytes>MEMORY_BUDGET_BYTES-payload_bytes||cells>std::numeric_limits<size_t>::max()){++memory_guard_axes;continue;}
   try{a.bits.assign(size_t(cells),0);}catch(const std::bad_alloc&){std::vector<U>().swap(a.bits);++allocation_guard_axes;continue;}catch(const std::length_error&){std::vector<U>().swap(a.bits);++allocation_guard_axes;continue;}
   a.active=true;payload_bytes+=U(bytes);
   for(const auto&ed:g.edges){const int actor=o?ed.c:ed.r,col=o?ed.r:ed.c;a.bits[U(actor)*a.words+U(col)/64]|=U(1)<<(unsigned(col)&63);++initial_entries;}
  }
  if(active()){
   if(g.support_mutation_hook)throw std::runtime_error("support hook already installed");
   g.support_mutation_context=this;g.support_mutation_hook=&SupportSceneBitset::mutation;
  }
  build_cpu_seconds=cpu()-ts;
 }
 static void mutation(void*context,int r,int c,I old,I now){static_cast<SupportSceneBitset*>(context)->update(r,c,old,now);}
 void update(int r,int c,I old,I now){
  if((old>0)==(now>0))throw std::runtime_error("support hook called without support transition");++support_transition_calls;
  for(int o=0;o<2;++o){auto&a=axis[o];if(!a.active)continue;const int actor=o?c:r,col=o?r:c;if(actor<0||actor>=a.actors||col<0||col>=a.opposite)throw std::runtime_error("bitset update coordinates");
   U&word=a.bits[U(actor)*a.words+U(col)/64];const U mask=U(1)<<(unsigned(col)&63);if(bool(word&mask)!=(old>0))throw std::runtime_error("support index old bit stale");if(now>0)word|=mask;else word&=~mask;++axis_bit_updates;
  }
 }
 template<class Scratch>bool collect(const Graph&g,int o,const std::array<int,3>&nodes,std::array<std::vector<int>,3>&pools,Scratch&tmp){
  ++calls;auto&a=axis[o];if(!a.active){++sparse_axis_calls;return false;}U degrees=0;for(int n:nodes)degrees+=g.adj[o?g.nr+n:n].size();if(3*a.words>degrees){++sparse_cost_calls;return false;}++bitset_calls;
  std::array<const U*,3>row{};for(int i=0;i<3;++i){if(nodes[i]<0||nodes[i]>=a.actors)throw std::runtime_error("bitset actor label");row[i]=a.bits.data()+U(nodes[i])*a.words;}
  for(U k=0;k<a.words;++k){const U x=row[0][k],y=row[1][k],z=row[2][k];std::array<U,3>private_mask{x&~(y|z),y&~(x|z),z&~(x|y)};word_visits+=3;
   for(int i=0;i<3;++i){U mask=private_mask[i];while(mask){const unsigned bit=__builtin_ctzll(mask);mask&=mask-1;const U col=k*64+bit;if(col>=U(a.opposite))throw std::runtime_error("bitset padding bit is set");pools[i].push_back(int(col));}}
  }
  U total=0;
  for(int i=0;i<3;++i){auto&pool=pools[i];struct Position {int pos,col;I weight;};std::vector<Position>ordered;ordered.reserve(pool.size());
   for(int col:pool){const int id=o?g.find(col,nodes[i]):g.find(nodes[i],col);if(id<0)throw std::runtime_error("bitset private edge missing");const auto&ed=g.edges[id];ordered.push_back({o?ed.pc:ed.pr,col,ed.w});}
   std::sort(ordered.begin(),ordered.end(),[](const Position&x,const Position&y){return x.pos<y.pos;});pool.clear();
   for(const auto&record:ordered){const int col=record.col;pool.push_back(col);tmp.stamp[col]=tmp.epoch;tmp.mask[col]=uint8_t(1u<<i);tmp.first_weight[col]=record.weight;tmp.touched.push_back(col);++total;}
  }
  private_labels+=total;max_private_labels=std::max(max_private_labels,total);return true;
 }
 void check(const Graph&g)const{
  if(!active())return;++checks;
  for(int o=0;o<2;++o){const auto&a=axis[o];if(!a.active)continue;U total=0;
   if(a.bits.size()!=U(a.actors)*a.words)throw std::runtime_error("bitset payload dimensions");
   for(int actor=0;actor<a.actors;++actor)for(U k=0;k<a.words;++k){U mask=a.bits[U(actor)*a.words+k];++checked_words;while(mask){const unsigned bit=__builtin_ctzll(mask);mask&=mask-1;const U col=k*64+bit;if(col>=U(a.opposite)||(o?g.value(int(col),actor):g.value(actor,int(col)))<=0)throw std::runtime_error("support index has absent or padding bit");++total;++checked_entries;}}
   if(total!=g.edges.size())throw std::runtime_error("support index positive-edge count mismatch");
  }
 }
};
