#pragma once

struct GeometricProfileRefresh {
 U calls=0,single_holds=0,profile_moves=0,profile_holds=0;
 template<class Pick>U draw(const std::vector<mpz_class>&mass,const mpz_class&total,U current,Pick&&pick){
  ++calls;if(mass.empty()||current>=mass.size()||total<=0)throw std::runtime_error("GPR invalid masses");
  U largest=0;mpz_class sum=0;for(U i=0;i<mass.size();++i){if(mass[i]<=0)throw std::runtime_error("GPR nonpositive mass");sum+=mass[i];if(mass[i]>mass[largest])largest=i;}
  if(sum!=total)throw std::runtime_error("GPR total mismatch");
  if(mass.size()==1){++single_holds;return current;}
  mpz_class prefix=0;if(current!=largest){prefix=mass[largest];for(U i=0;i<current;++i)if(i!=largest)prefix+=mass[i];}
  mpz_class rank=pick(mass[current]);if(rank<0||rank>=mass[current])throw std::runtime_error("GPR current rank");
  rank+=prefix+mass[largest];if(rank>=total)rank-=total;
  U candidate=largest;if(rank>=mass[largest]){rank-=mass[largest];for(candidate=0;candidate<mass.size();++candidate){if(candidate==largest)continue;if(rank<mass[candidate])break;rank-=mass[candidate];}}
  if(candidate>=mass.size())throw std::runtime_error("GPR candidate");
  if(candidate==current)++profile_holds;else ++profile_moves;return candidate;
 }
 void metadata(std::ostream&f)const{f<<"\"GPR_calls\":"<<calls<<",\"GPR_single_holds\":"<<single_holds<<",\"GPR_profile_moves\":"<<profile_moves<<",\"GPR_profile_holds\":"<<profile_holds<<",";}
};
