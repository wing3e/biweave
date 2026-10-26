 

using Wide=__uint128_t;
Big big_wide(Wide x){Big b;while(x){b.a.push_back(uint32_t(x));x>>=32;}return b;}
U big_small(const Big&b){if(b.a.size()>2)throw std::runtime_error("Big does not fit uint64");return (b.a.empty()?0:U(b.a[0]))+(b.a.size()<2?0:(U(b.a[1])<<32));}
unsigned wide_bits(Wide x){if(!x)return 0;U high=U(x>>64);return high?64+64-__builtin_clzll(high):64-__builtin_clzll(U(x));}
Wide draw_wide(RNG&rng,Wide n){
 if(!n)throw std::runtime_error("empty wide draw");if(n<=std::numeric_limits<U>::max())return rng.below(U(n));unsigned bits=wide_bits(n-1);
 for(;;){Wide x=Wide(rng.gen())|(Wide(rng.gen())<<64);if(bits<128)x&=(Wide(1)<<bits)-1;if(x<n)return x;}
}
struct OwnerRandomAdapter {
 RNG&rng;
 Wide below_wide(Wide n){return n==1?0:draw_wide(rng,n);}
 Big below_big(const Big&n){return rng.below_big(n);}
};
U choose_small(int n,int k){if(k<0||k>n)return 0;k=std::min(k,n-k);U result=1;for(int i=1;i<=k;++i)result=result*U(n-k+i)/U(i);return result;}
Big binomial_fast(S128 n,int k){
 if(k<0||n<k)return Big(0);if(k==0)return Big(1);if(__uint128_t(n)>std::numeric_limits<U>::max())throw std::runtime_error("fast binomial top exceeds uint64");if(k==1)return Big(U(n));if(k==2)return big_wide(Wide(n)*Wide(n-1)/2);return binomial(n,k);
}

struct ReusedCount {
 int h;std::vector<S128>shift;std::vector<I>coefficient;Counters*stat;S128 bound_sum=0;
 ReusedCount(const std::vector<I>&bounds,Counters*s):h(int(bounds.size())),stat(s){
  if(h>12)throw std::runtime_error("compressed count supports <=12 variables");
  std::map<S128,I> polynomial;polynomial[0]=1;
  for(I bound:bounds){
   if(bound<0)throw std::runtime_error("negative compressed bound");bound_sum+=bound;
   auto updated=polynomial;
   for(const auto&term:polynomial)updated[term.first+S128(bound)+1]-=term.second;
   for(auto it=updated.begin();it!=updated.end();){if(it->second==0)it=updated.erase(it);else ++it;}
   polynomial=std::move(updated);
  }
  for(const auto&term:polynomial){shift.push_back(term.first);coefficient.push_back(term.second);}
  if(stat){stat->compressed_descriptor_builds++;stat->compressed_descriptor_terms+=shift.size();stat->compressed_descriptor_max_terms=std::max(stat->compressed_descriptor_max_terms,U(shift.size()));stat->compressed_raw_subset_terms+=U(1)<<h;}
 }
 Big count(S128 q,bool bounded=true)const{
  if(stat)stat->block_count_calls++;if(bounded&&!h)return Big(q==0);
  int degree=bounded?h-1:h;Big positive,negative;
  for(size_t j=0;j<shift.size();++j){
   if(stat)stat->block_count_terms++;S128 top=q-shift[j]+degree;
   if(top<degree)continue;
   Big term=binomial_fast(top,degree);I c=coefficient[j];term*=U(c<0?-c:c);
   if(c<0)negative+=term;else positive+=term;
  }
  if(positive<negative)throw std::runtime_error("negative compressed composition count");
  return positive-negative;
 }
};

template<class Visitor>
void pruned_owner_combinations_v14(const std::vector<I>&weights,int choose,S128 target,S128 residual_upper,Counters*stat,Visitor visitor){
 const int e=int(weights.size());if(e>12||choose<0||choose>e||residual_upper<0)throw std::runtime_error("invalid pruned owner parameters");
 const S128 infinity=S128(1)<<120;
 std::array<std::array<S128,13>,13>minimum,maximum;
 for(int i=0;i<=e;++i){minimum[i].fill(infinity);maximum[i].fill(-infinity);minimum[i][0]=maximum[i][0]=0;}
 for(int i=e-1;i>=0;--i)for(int need=1;need<=std::min(choose,e-i);++need){
  minimum[i][need]=minimum[i+1][need];maximum[i][need]=maximum[i+1][need];
  if(need-1<=e-i-1){minimum[i][need]=std::min(minimum[i][need],S128(weights[i])+minimum[i+1][need-1]);maximum[i][need]=std::max(maximum[i][need],S128(weights[i])+maximum[i+1][need-1]);}
  if(stat)stat->owner_cardinality_dp_cells++;
 }
 const S128 low=target-residual_upper,high=target;
 auto traverse=[&](auto&&self,int start,int need,U mask,S128 sum)->void{
  if(stat)stat->owner_combination_nodes++;
  if(sum+minimum[start][need]>high||sum+maximum[start][need]<low){
   if(stat){stat->owner_sum_pruned_subtrees++;stat->owner_sum_pruned_masks+=choose_small(e-start,need);}return;
  }
  if(!need){if(stat)stat->owner_feasible_masks_examined++;visitor(mask,target-sum);return;}
  for(int j=start;j<=e-need;++j)self(self,j+1,need-1,mask|(U(1)<<j),sum+weights[j]);
 };
 traverse(traverse,0,choose,0,0);
}
struct FastCountedBlock {
 std::vector<I>a,b,c,bounds;std::vector<int>exclusive,shared,variable;
 I row_sum=0;int choose=0;bool unit=false,equal_trade=false,small=false;I equal_weight=0;
 struct SmallSupport {U mask,count;I q,lo;};std::vector<SmallSupport>small_supports;Wide small_total=0;
 struct GeneralSupport {U mask;Big count;I q;};std::vector<GeneralSupport>general_supports;Big general_total;
 Counters*stat=nullptr;std::vector<ReusedCount>suffix_counts;U descriptor_terms_full=0,descriptor_terms_max=0;
 FastCountedBlock(std::vector<I>aa,std::vector<I>bb,Counters*s=nullptr):a(std::move(aa)),b(std::move(bb)),stat(s){
  if(a.size()!=b.size()||a.size()>12)throw std::runtime_error("fast arrays need same size <=12");I combined=0;int degree=0;unit=true;
  for(size_t j=0;j<a.size();++j){if(a[j]<0||b[j]<0||a[j]>std::numeric_limits<I>::max()-b[j])throw std::runtime_error("invalid fast int64 weight");I sum=a[j]+b[j];if(combined>std::numeric_limits<I>::max()-sum)throw std::runtime_error("fast block total exceeds int64");combined+=sum;c.push_back(sum);row_sum+=a[j];degree+=a[j]>0;unit&=(a[j]==0||a[j]==1)&&(b[j]==0||b[j]==1);
   if(a[j]>0&&b[j]>0){shared.push_back(int(j));if(sum>2){variable.push_back(int(j));bounds.push_back(sum-2);}}
   else if(sum>0)exclusive.push_back(int(j));
  }
  choose=degree-int(shared.size());equal_trade=bounds.empty();for(int j:exclusive){if(!equal_weight)equal_weight=c[j];else if(c[j]!=equal_weight)equal_trade=false;}
  if(unit||equal_trade){small=true;small_total=choose_small(int(exclusive.size()),choose);if(!small_total)throw std::runtime_error("empty combinatorial trade");if(stat){stat->fast_unit_calls+=unit;stat->fast_equal_trade_calls+=!unit;stat->block_max_count_bits=std::max(stat->block_max_count_bits,U(wide_bits(small_total)));}return;}
  std::vector<I>exclusive_weights;exclusive_weights.reserve(exclusive.size());for(int j:exclusive)exclusive_weights.push_back(c[j]);
  S128 residual_upper=0;for(I bound:bounds)residual_upper+=bound;const S128 target=S128(row_sum)-shared.size();
  int h=int(bounds.size());small=h<=2;if(stat){stat->fast_h0_calls+=h==0;stat->fast_h1_calls+=h==1;stat->fast_h2_calls+=h==2;stat->fast_general_calls+=h>=3;}
  if(small){
   pruned_owner_combinations_v14(exclusive_weights,choose,target,residual_upper,stat,[&](U mask,S128 q){
    if(stat)stat->fast_small_count_calls++;I lo=0,hi=0;
    if(h==2){lo=I(std::max<S128>(0,q-bounds[1]));hi=I(std::min<S128>(bounds[0],q));if(lo>hi)throw std::runtime_error("pruned feasible interval unexpectedly empty");}
    U n=h==2?U(hi-lo)+1:1;small_supports.push_back({mask,n,I(q),lo});small_total+=n;
   });
   if(!small_total)throw std::runtime_error("empty low-dimensional conditional fiber");if(stat)stat->block_max_count_bits=std::max(stat->block_max_count_bits,U(wide_bits(small_total)));
  }else{
   for(size_t t=0;t+2<bounds.size();++t){std::vector<I>remaining(bounds.begin()+t+1,bounds.end());suffix_counts.emplace_back(remaining,stat);if(stat)stat->fast_prefix_builds++;}
   ReusedCount counter(bounds,stat);descriptor_terms_full=counter.shift.size();descriptor_terms_max=descriptor_terms_full;for(const auto&suffix:suffix_counts)descriptor_terms_max=std::max(descriptor_terms_max,U(suffix.shift.size()));if(stat){stat->compressed_full_descriptor_max_terms=std::max(stat->compressed_full_descriptor_max_terms,descriptor_terms_full);stat->compressed_solver_descriptor_max_terms=std::max(stat->compressed_solver_descriptor_max_terms,descriptor_terms_max);}pruned_owner_combinations_v14(exclusive_weights,choose,target,residual_upper,stat,[&](U mask,S128 q){Big n=counter.count(q);if(n==0)throw std::runtime_error("pruned feasible general composition unexpectedly empty");if(q<0||q>std::numeric_limits<I>::max())throw std::runtime_error("general residual out of int64");general_supports.push_back({mask,n,I(q)});general_total+=n;});
   if(general_total==0)throw std::runtime_error("empty general conditional fiber");if(stat)stat->block_max_count_bits=std::max(stat->block_max_count_bits,U(general_total.bits()));
  }
 }
 bool nontrivial()const{return small?small_total>1:general_total>Big(1);}
 U support_count()const{return unit||equal_trade?U(small_total):small?small_supports.size():general_supports.size();}
 Big total_big()const{return small?big_wide(small_total):general_total;}
 std::vector<I>base_x(U mask)const{std::vector<I>x(a.size(),0);for(int j:shared)x[j]=1;for(size_t t=0;t<exclusive.size();++t)if(mask>>t&1)x[exclusive[t]]=c[exclusive[t]];return x;}
 std::pair<std::vector<I>,std::vector<I>>finish(std::vector<I>x)const{std::vector<I>y(x.size());for(size_t j=0;j<x.size();++j)y[j]=c[j]-x[j];return {x,y};}
 U trade_mask_rank(U rank)const{
  U mask=0;int start=0;for(int t=0;t<choose;++t){bool found=false;for(int j=start;j<int(exclusive.size());++j){U n=choose_small(int(exclusive.size())-j-1,choose-t-1);if(rank<n){mask|=U(1)<<j;start=j+1;found=true;break;}rank-=n;}if(!found)throw std::runtime_error("trade rank selection failed");}if(rank)throw std::runtime_error("trade rank residue");return mask;
 }
  
 U trade_rank_mask_v14(U mask)const{
  const int e=int(exclusive.size());if((mask>>e)||__builtin_popcountll(mask)!=choose)throw std::runtime_error("invalid current trade mask");
  U rank=0;int start=0;
  for(int t=0;t<choose;++t){int selected=start;while(selected<e&&!(mask>>selected&1))++selected;if(selected==e)throw std::runtime_error("missing current trade owner");
   for(int j=start;j<selected;++j)rank+=choose_small(e-j-1,choose-t-1);start=selected+1;
  }
  if(rank>=U(small_total))throw std::runtime_error("current trade rank out of range");if(stat)stat->owner_direct_trade_rank_calls++;return rank;
 }
 std::pair<std::vector<I>,std::vector<I>>unrank_small(Wide rank)const{
  if(!small||rank>=small_total)throw std::runtime_error("small rank out of range");if(unit||equal_trade)return finish(base_x(trade_mask_rank(U(rank))));
  for(const auto&s:small_supports){if(rank>=s.count){rank-=s.count;continue;}auto x=base_x(s.mask);if(bounds.size()==1)x[variable[0]]=s.q+1;else if(bounds.size()==2){I z=s.lo+I(rank);x[variable[0]]=z+1;x[variable[1]]=s.q-z+1;}return finish(x);}throw std::runtime_error("small support selection failed");
 }
 std::pair<std::vector<I>,std::vector<I>>unrank(Big rank)const{
  if(small){if(rank>=big_wide(small_total))throw std::runtime_error("fast rank out of range");Wide x=0;for(size_t i=rank.a.size();i-->0;)x=(x<<32)|rank.a[i];return unrank_small(x);}
  if(rank>=general_total)throw std::runtime_error("general rank out of range");const GeneralSupport*chosen=nullptr;for(const auto&s:general_supports){if(rank<s.count){chosen=&s;break;}rank-=s.count;}if(!chosen)throw std::runtime_error("general support selection failed");auto x=base_x(chosen->mask);I q=chosen->q;
  for(size_t t=0;t<variable.size();++t){size_t left=variable.size()-t;
   if(left==1){if(!(rank==0)||q<0||q>bounds[t])throw std::runtime_error("last split invalid");x[variable[t]]=q+1;q=0;break;}
   if(left==2){I lo=std::max<I>(0,q-bounds[t+1]),hi=std::min<I>(bounds[t],q);if(lo>hi||rank>=Big(U(hi-lo)+1))throw std::runtime_error("last interval rank invalid");I z=lo+I(big_small(rank));x[variable[t]]=z+1;x[variable[t+1]]=q-z+1;q=0;rank=0;break;}
   const ReusedCount&suffix=suffix_counts.at(t);Big base=suffix.count(q,false);S128 rest_sum=suffix.bound_sum;I lo=I(std::max<S128>(0,S128(q)-rest_sum)),hi=std::min<I>(bounds[t],q);
   auto prefix=[&](I cap){if(cap<0)return Big(0);if(stat)stat->fast_prefix_queries++;Big tail=suffix.count(S128(q)-cap-1,false);if(base<tail)throw std::runtime_error("negative fast prefix");return base-tail;};
   while(lo<hi){I mid=lo+(hi-lo)/2;if(prefix(mid)>rank)hi=mid;else lo=mid+1;}I z=lo;if(z)rank-=prefix(z-1);x[variable[t]]=z+1;q-=z;
  }
  if(q||!(rank==0))throw std::runtime_error("general unrank residue");return finish(x);
 }
 std::pair<std::vector<I>,std::vector<I>>draw(RNG&rng)const{
  if(!nontrivial()){if(stat)stat->fast_singleton_calls++;return {a,b};}
  if(unit||equal_trade){
    
   std::vector<int>indices(exclusive.size());for(size_t j=0;j<indices.size();++j)indices[j]=int(j);U mask=0;int k=std::min<int>(choose,int(indices.size())-choose);bool complement=choose>int(indices.size())-choose;
   for(int t=0;t<k;++t){int j=t+int(rng.below(indices.size()-t));std::swap(indices[t],indices[j]);mask|=U(1)<<indices[t];}if(complement)mask=((U(1)<<indices.size())-1)^mask;return finish(base_x(mask));
  }
  return small?unrank_small(draw_wide(rng,small_total)):unrank(rng.below_big(general_total));
 }
 U current_owner_mask()const{U mask=0;for(size_t j=0;j<exclusive.size();++j)if(a[exclusive[j]]>0)mask|=U(1)<<j;return mask;}
 std::pair<std::vector<I>,std::vector<I>>complete_small_support(const SmallSupport&s,Wide rank)const{
  if(rank>=s.count)throw std::runtime_error("owner completion rank out of range");auto x=base_x(s.mask);
  if(bounds.size()==1)x[variable[0]]=s.q+1;else if(bounds.size()==2){I z=s.lo+I(rank);x[variable[0]]=z+1;x[variable[1]]=s.q-z+1;}
  return finish(x);
 }

 template<class Random>
 std::pair<std::vector<I>,std::vector<I>>draw_metropolis_refresh(Random&random)const{
  if(stat)stat->owner_metropolis_calls++;U current=current_owner_mask(),final_owner=current;bool rejected=false;
  std::pair<std::vector<I>,std::vector<I>>output;
  if(unit||equal_trade){
   U z=U(small_total),current_rank=trade_rank_mask_v14(current);
   if(z==1){if(stat){stat->owner_one_support_heatbath++;stat->fast_singleton_calls++;}}
   else{U rank=U(random.below_wide(Wide(z-1)));if(rank>=current_rank)rank++;final_owner=trade_mask_rank(rank);if(stat){stat->owner_proposals++;stat->owner_accepts++;}}
   output=finish(base_x(final_owner));
  }else if(small){
   size_t ci=small_supports.size();for(size_t j=0;j<small_supports.size();++j)if(small_supports[j].mask==current){ci=j;break;}if(ci==small_supports.size())throw std::runtime_error("current small owner missing");size_t final_index=ci;
   if(small_supports.size()==1){if(stat)stat->owner_one_support_heatbath++;}
   else{
    Wide without_current=small_total-small_supports[ci].count,rank=random.below_wide(without_current);size_t proposed=small_supports.size();
    for(size_t j=0;j<small_supports.size();++j){if(j==ci)continue;if(rank<small_supports[j].count){proposed=j;break;}rank-=small_supports[j].count;}
    if(proposed==small_supports.size())throw std::runtime_error("small owner proposal failed");Wide without_proposed=small_total-small_supports[proposed].count;bool accepted=without_current>=without_proposed||random.below_wide(without_proposed)<without_current;
    if(stat){stat->owner_proposals++;stat->owner_accepts+=accepted;stat->owner_rejects+=!accepted;}if(accepted)final_index=proposed;else rejected=true;
   }
   const auto&s=small_supports[final_index];final_owner=s.mask;output=complete_small_support(s,s.count==1?0:random.below_wide(Wide(s.count)));if(small_total==1&&stat)stat->fast_singleton_calls++;
  }else{
   size_t ci=general_supports.size();for(size_t j=0;j<general_supports.size();++j)if(general_supports[j].mask==current){ci=j;break;}if(ci==general_supports.size())throw std::runtime_error("current general owner missing");size_t final_index=ci;
   if(general_supports.size()==1){if(stat)stat->owner_one_support_heatbath++;}
   else{
    Big without_current=general_total-general_supports[ci].count,rank=random.below_big(without_current);size_t proposed=general_supports.size();
    for(size_t j=0;j<general_supports.size();++j){if(j==ci)continue;if(rank<general_supports[j].count){proposed=j;break;}rank-=general_supports[j].count;}
    if(proposed==general_supports.size())throw std::runtime_error("general owner proposal failed");Big without_proposed=general_total-general_supports[proposed].count;bool accepted=without_current>=without_proposed||random.below_big(without_proposed)<without_current;
    if(stat){stat->owner_proposals++;stat->owner_accepts+=accepted;stat->owner_rejects+=!accepted;}if(accepted)final_index=proposed;else rejected=true;
   }
   final_owner=general_supports[final_index].mask;Big rank=random.below_big(general_supports[final_index].count);for(size_t j=0;j<final_index;++j)rank+=general_supports[j].count;output=unrank(rank);if(general_total==1&&stat)stat->fast_singleton_calls++;
  }
  if(stat){bool changed=output.first!=a||output.second!=b;stat->owner_completion_refreshes++;stat->owner_matrix_changed+=changed;stat->owner_support_changed+=final_owner!=current;stat->owner_rejected_refresh_changed+=rejected&&changed;stat->owner_state_holds_after_refresh+=!changed;}
  return output;
 }
 std::vector<std::pair<U,Big>>support_counts()const{
  std::vector<std::pair<U,Big>>out;if(unit||equal_trade){for(U rank=0;rank<U(small_total);++rank)out.push_back({trade_mask_rank(rank),Big(1)});}
  else if(small){for(const auto&s:small_supports)out.push_back({s.mask,Big(s.count)});}else{for(const auto&s:general_supports)out.push_back({s.mask,s.count});}return out;
 }
};

std::pair<U,U> effective_shift_work(const std::vector<I>&bounds){
 if(bounds.size()<=2)return {0,0};ReusedCount full(bounds,nullptr);U maximum=full.shift.size();
 for(size_t t=0;t+2<bounds.size();++t){std::vector<I>remaining(bounds.begin()+t+1,bounds.end());ReusedCount suffix(remaining,nullptr);maximum=std::max(maximum,U(suffix.shift.size()));}
 return {U(full.shift.size()),maximum};
}
