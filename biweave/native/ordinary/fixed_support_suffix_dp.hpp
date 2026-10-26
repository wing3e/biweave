 

struct FixedSupportSuffixDP {
 static constexpr U MEMORY_BUDGET_BYTES=64ULL*1024*1024;
 static constexpr U CELL_BUDGET=1000000;
 std::vector<I> a,b;
 std::vector<size_t> variables;
 std::vector<U> caps;
 std::vector<Big> suffix_cdf;
 bool active=false,flipped=false,resource_failed=false;
 std::string guard_reason="not_started";
 U effective_h=0,target=0,total_capacity=0,dp_cells=0;
 U count_bits_bound=0,estimated_bytes=0;
 Big total;
 FixedSupportSuffixDP(const std::vector<I>&aa,const std::vector<I>&bb):a(aa),b(bb){
  if(a.size()!=b.size()||a.size()>12)throw std::runtime_error("fixed support DP arrays need equal size <=12");
  S128 sum=0,T=0,C=0;
  for(size_t j=0;j<a.size();++j){
   if(a[j]<0||b[j]<0||S128(a[j])+b[j]>std::numeric_limits<I>::max())throw std::runtime_error("fixed support DP invalid weight");
   sum+=S128(a[j])+b[j];
   if(sum>std::numeric_limits<I>::max())throw std::runtime_error("fixed support DP total exceeds int64");
   if((a[j]>0)!=(b[j]>0)){guard_reason="private_support_present";return;}
   if(!a[j])continue;
   const U cap=U(S128(a[j])+b[j]-2);
   T+=a[j]-1;C+=cap;
   if(cap){variables.push_back(j);caps.push_back(cap);}
  }
  effective_h=caps.size();total_capacity=U(C);
  flipped=T>C-T;target=U(flipped?C-T:T);
  if(effective_h<3){guard_reason="at_most_two_effective_variables";return;}
  const __uint128_t cells=__uint128_t(effective_h+1)*(target+__uint128_t(1));
  if(cells>CELL_BUDGET){resource_failed=true;guard_reason="dp_cell_budget";return;}
  dp_cells=U(cells);

  U q=target+1;unsigned log=0;U z=q-1;while(z){++log;z>>=1;}
  count_bits_bound=std::max<U>(1,effective_h*U(log)+1);
  const U limbs=(count_bits_bound+31)/32;
  const __uint128_t bytes=cells*(sizeof(Big)+__uint128_t(2)*limbs*sizeof(uint32_t)+32)
   +__uint128_t(16)*limbs*sizeof(uint32_t)+4096;
  if(bytes>MEMORY_BUDGET_BYTES){resource_failed=true;guard_reason="dp_memory_budget";return;}
  estimated_bytes=U(bytes);
  try{
   suffix_cdf.resize(dp_cells);

   for(Big&v:suffix_cdf){v.a.reserve(limbs);if(v.a.capacity()>2*limbs)throw std::bad_alloc();}
   const U width=target+1;
   for(U t=0;t<=target;++t)at(effective_h,t)=Big(1);
   for(U i=effective_h;i-->0;){
    Big prefix;prefix.a.reserve(limbs);
    for(U t=0;t<=target;++t){
     Big window=at(i+1,t);
     if(t>caps[i])window-=at(i+1,t-caps[i]-1);
     prefix+=window;at(i,t)=prefix;
     if(at(i,t).bits()>count_bits_bound)throw std::runtime_error("fixed support DP integer bound violated");
    }
   }
   total=at(0,target);if(target)total-=at(0,target-1);
   if(total==Big(0))throw std::runtime_error("fixed support DP lost original completion");
  }catch(const std::bad_alloc&){
   std::vector<Big>().swap(suffix_cdf);total=Big(0);resource_failed=true;guard_reason="allocation_failed";return;
  }
  active=true;guard_reason="exact_fixed_support_suffix_dp";
 }
 Big&at(U i,U t){return suffix_cdf.at(size_t(i*(target+1)+t));}
 const Big&at(U i,U t)const{return suffix_cdf.at(size_t(i*(target+1)+t));}
 const Big&count()const{if(!active)throw std::runtime_error("inactive fixed support DP count");return total;}
 std::pair<std::vector<I>,std::vector<I>>unrank(Big rank)const{
  if(!active||rank>=total)throw std::runtime_error("fixed support DP rank outside fiber");

  if(flipped){Big reversed=total;reversed-=Big(1);reversed-=rank;rank=std::move(reversed);}
  std::vector<I>x=a,y=b;U residual=target;
  for(U i=0;i<effective_h;++i){
   U lo=0,hi=std::min(caps[i],residual);
   const Big&base=at(i+1,residual);
   auto cumulative=[&](U z){Big mass=base;if(z<residual)mass-=at(i+1,residual-z-1);return mass;};
   while(lo<hi){U mid=lo+(hi-lo)/2;if(cumulative(mid)>rank)hi=mid;else lo=mid+1;}
   U z=lo;if(z)rank-=cumulative(z-1);
   const size_t column=variables[i];const I first=I(z+1),second=I(caps[i]-z+1);
   x[column]=flipped?second:first;y[column]=flipped?first:second;residual-=z;
  }
  if(residual||!(rank==Big(0)))throw std::runtime_error("fixed support DP rank remainder");
  return{x,y};
 }
 std::pair<std::vector<I>,std::vector<I>>draw(RNG&rng)const{
  if(count()==Big(1))return{a,b};return unrank(rng.below_big(total));
 }
};
