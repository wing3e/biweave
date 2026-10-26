#pragma once
#include <numeric>

struct TwoWeightSlackCertificate {
 U calls=0,C_equal_three=0,small_public_sum_passes=0,gcd_scans=0,gcd_weight_visits=0;
 U gcd_one_fallbacks=0,gcd_zero_fallbacks=0,zero_bound_fallbacks=0,large_bound_fallbacks=0,spaced_weight_passes=0;
 U certificate_passes=0,certificate_fallbacks=0,single_profile_fallbacks=0,generalized_draws=0,max_T=0,max_gcd=0;
 S128 max_public_sum=0;
 struct Result {bool allow=false;U gcd=0,T=0,visits=0;S128 C=0;std::string reason;};
 template<class Pools,class Scratch>Result evaluate(const std::array<I,3>&roots,I w0,const Pools&pools,const Scratch&tmp){
  ++calls;Result r;if(w0<=0)throw std::runtime_error("TWC nonpositive modal weight");
  for(I root:roots){if(root<=0)throw std::runtime_error("TWC nonpositive root");r.C+=S128(root);}max_public_sum=std::max(max_public_sum,r.C);
  if(r.C==3){++C_equal_three;++certificate_fallbacks;r.reason="three_unit_roots";return r;}
  if(r.C<3)throw std::runtime_error("TWC positive root ledger impossible");
  if(r.C<=9){++small_public_sum_passes;++certificate_passes;r.allow=true;r.reason="root_sum4_to9";return r;}
  ++gcd_scans;
  for(int owner=0;owner<3;++owner)for(int col:pools[owner]){
   if(tmp.stamp[col]!=tmp.epoch||__builtin_popcount(unsigned(tmp.mask[col]))!=1||!(tmp.mask[col]&(1u<<owner)))throw std::runtime_error("TWC whole private scratch invalid");
   const I w=tmp.first_weight[col];if(w<=0)throw std::runtime_error("TWC nonpositive private weight");
   const S128 difference=S128(w)-S128(w0);const U absolute=U(difference<0?-difference:difference);r.gcd=std::gcd(r.gcd,absolute);++r.visits;++gcd_weight_visits;
   if(r.gcd==1){++gcd_one_fallbacks;++certificate_fallbacks;r.reason="whole_private_gcd_one";return r;}
  }
  max_gcd=std::max(max_gcd,r.gcd);
  if(!r.gcd){++gcd_zero_fallbacks;++certificate_fallbacks;r.reason="whole_private_single_weight";return r;}
  S128 upper=0;for(I root:roots)upper+=(S128(root)-1)/S128(r.gcd);
   
  if(upper==0){++zero_bound_fallbacks;++certificate_fallbacks;r.reason="root_residue_bound_zero";return r;}
  if(upper>TwoWeightComplement::SLACK_CAP){++large_bound_fallbacks;++certificate_fallbacks;r.reason="root_residue_bound_over6";return r;}
  r.T=U(upper);max_T=std::max(max_T,r.T);++spaced_weight_passes;++certificate_passes;r.allow=true;r.reason="whole_private_gcd_root_residue_bound1_to6";return r;
 }
};
