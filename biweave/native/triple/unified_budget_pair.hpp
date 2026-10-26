#pragma once

struct UnifiedBudgetPair {
 struct Choice {bool pair=false;I low=0,high=0;U tickets=0;};
 U calls=0,pair_draws=0,single_fallbacks=0,empty=0,class_visits=0,max_classes=0,max_tickets=0;
 template<class Pick>Choice draw(const std::map<I,U>&counts,S128 public_total,U min_cells,Pick&&pick){
  ++calls;if(min_cells!=2&&min_cells!=4)throw std::runtime_error("UA public positivity minimum");
  if(public_total<S128(min_cells))throw std::runtime_error("UA public sum below positivity minimum");
  Choice out;if(counts.empty()){++empty;return out;}
  std::vector<I>w;std::vector<U>n,prefix(1,0);w.reserve(counts.size());n.reserve(counts.size());
  for(const auto&v:counts){if(v.first<=0||!v.second)throw std::runtime_error("UA invalid carried class");
   if(v.second>U(std::numeric_limits<int>::max())-prefix.back())throw std::runtime_error("UA label pool outside graph index bound");
   w.push_back(v.first);n.push_back(v.second);prefix.push_back(prefix.back()+v.second);++class_visits;}
  max_classes=std::max(max_classes,U(w.size()));const S128 gap=public_total-S128(min_cells);
  std::vector<U>mass(w.size(),0);U total=0;size_t right=1;
  for(size_t i=0;i<w.size();++i){right=std::max(right,i+1);while(right<w.size()&&S128(w[right])-w[i]<=gap)++right;
   const __uint128_t m=__uint128_t(n[i])*(prefix[right]-prefix[i+1]);
   if(m>std::numeric_limits<U>::max()-total)throw std::runtime_error("UA pair ticket overflow");
   mass[i]=U(m);total+=mass[i];}
  out.tickets=total;max_tickets=std::max(max_tickets,total);
  if(total){++pair_draws;U rank=pick(total);if(rank>=total)throw std::runtime_error("UA ticket rank");size_t i=0;
   while(rank>=mass[i]){rank-=mass[i];++i;}U second=rank/n[i];size_t j=i+1;
   while(second>=n[j]){second-=n[j];++j;}
   out.pair=true;out.low=w[i];out.high=w[j];return out;}
  ++single_fallbacks;U largest=0;std::vector<I>ties;
  for(const auto&v:counts){if(v.second>largest){largest=v.second;ties.clear();}if(v.second==largest)ties.push_back(v.first);}
  out.low=ties.size()==1?ties[0]:ties[pick(ties.size())];return out;
 }
};
