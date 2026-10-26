#pragma once

struct BudgetCompatiblePair {
 struct Choice{bool pair=false;I primary=0,other=0;U tickets=0;};
 U calls=0,empty=0,single_fallbacks=0,pair_draws=0,class_visits=0;
 U max_classes=0,max_tickets=0;__uint128_t tickets_total=0;
 template<class Pick>Choice draw(const std::map<I,U>&counts,S128 C,Pick&&pick,bool filter=true){
  ++calls;if(C<3||C>std::numeric_limits<I>::max())throw std::runtime_error("budget pair root ledger");
  if(counts.empty()){++empty;return {};}
  std::vector<I>w;std::vector<U>n,prefix{0},mass;std::vector<size_t>ends;U total=0;
  for(const auto&item:counts){if(item.first<=0||!item.second)throw std::runtime_error("budget pair class invalid");w.push_back(item.first);n.push_back(item.second);if(item.second>U(std::numeric_limits<int>::max())-prefix.back())throw std::runtime_error("budget pair unique label bound");prefix.push_back(prefix.back()+item.second);++class_visits;}
  max_classes=std::max<U>(max_classes,w.size());const S128 budget=filter?C-3:S128(std::numeric_limits<I>::max());size_t right=1;
  for(size_t i=0;i<w.size();++i){right=std::max(right,i+1);while(right<w.size()&&S128(w[right])-S128(w[i])<=budget)++right;ends.push_back(right);const __uint128_t m=__uint128_t(n[i])*(prefix[right]-prefix[i+1]);if(m>std::numeric_limits<U>::max()-total)throw std::runtime_error("budget pair ticket overflow");mass.push_back(U(m));total+=U(m);}
  Choice out;out.tickets=total;max_tickets=std::max(max_tickets,total);tickets_total+=total;
  if(total){U rank=pick(total);if(rank>=total)throw std::runtime_error("budget pair rank");size_t i=0;while(i<mass.size()&&rank>=mass[i]){rank-=mass[i];++i;}if(i==mass.size()||!n[i])throw std::runtime_error("budget pair first class");U second=rank/n[i];size_t j=i+1;for(;j<ends[i];++j){if(second<n[j])break;second-=n[j];}if(j==ends[i])throw std::runtime_error("budget pair second class");out.pair=true;out.primary=w[i];out.other=w[j];++pair_draws;return out;}
  U best=0;std::vector<I>ties;for(size_t i=0;i<w.size();++i){if(n[i]>best){best=n[i];ties.clear();}if(n[i]==best)ties.push_back(w[i]);}
  U rank=pick(ties.size());if(rank>=ties.size())throw std::runtime_error("budget pair fallback rank");out.primary=ties[rank];++single_fallbacks;return out;
 }
 void metadata(std::ostream&f)const{f<<"\"BP_calls\":"<<calls<<",\"BP_empty\":"<<empty<<",\"BP_single_fallbacks\":"<<single_fallbacks<<",\"BP_pair_draws\":"<<pair_draws<<",\"BP_class_visits\":"<<class_visits<<",\"BP_max_classes\":"<<max_classes<<",\"BP_max_tickets\":"<<max_tickets<<",\"BP_tickets_total\":\""<<GlobalDegreeWorkBatch::wide_string(tickets_total)<<"\",";}
};
