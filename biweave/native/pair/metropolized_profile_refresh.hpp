#pragma once

struct MetropolizedProfileRefresh {
 U calls=0,single_holds=0,proposals=0,accepts=0,rejects=0;
 template<class Pick>U draw(const std::vector<mpz_class>&mass,const mpz_class&total,U current,Pick&&pick){
  ++calls;if(mass.empty()||current>=mass.size()||total<=0||mass[current]<=0)throw std::runtime_error("MPR invalid masses");
  if(mass.size()==1){if(total!=mass[current])throw std::runtime_error("MPR single total");++single_holds;return current;}
  const mpz_class others=total-mass[current];if(others<=0)throw std::runtime_error("MPR no other mass");
  mpz_class rank=pick(others);if(rank<0||rank>=others)throw std::runtime_error("MPR proposal rank");
  U candidate=0;for(;candidate<mass.size();++candidate){if(candidate==current)continue;if(rank<mass[candidate])break;rank-=mass[candidate];}
  if(candidate>=mass.size()||candidate==current||mass[candidate]<=0)throw std::runtime_error("MPR candidate");++proposals;
  const mpz_class denominator=total-mass[candidate];if(denominator<=0)throw std::runtime_error("MPR acceptance denominator");
  bool accepted=true;if(others<denominator){mpz_class arank=pick(denominator);if(arank<0||arank>=denominator)throw std::runtime_error("MPR acceptance rank");accepted=arank<others;}
  if(accepted){++accepts;return candidate;}++rejects;return current;
 }
 void metadata(std::ostream&f)const{f<<"\"MPR_calls\":"<<calls<<",\"MPR_single_holds\":"<<single_holds<<",\"MPR_proposals\":"<<proposals<<",\"MPR_accepts\":"<<accepts<<",\"MPR_rejects\":"<<rejects<<",";}
};
