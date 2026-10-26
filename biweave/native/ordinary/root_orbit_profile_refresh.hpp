#pragma once

struct RootOrbitProfileRefresh {
 GeometricProfileRefresh flow;U calls=0,groups_total=0,max_groups=0,single_group_windows=0,group_moves=0,group_holds=0;
 template<class Pick>U draw(const std::vector<std::array<U,3>>&profiles,const std::vector<mpz_class>&mass,const mpz_class&total,U current,const std::array<I,3>&beta,I low,const std::array<U,3>&h,I delta,Pick&&pick){
  ++calls;if(profiles.empty()||profiles.size()!=mass.size()||current>=profiles.size()||total<=0||low<=0||delta<=0)throw std::runtime_error("root-orbit invalid problem");
  std::map<std::array<I,3>,std::vector<U>>by_roots;std::vector<std::array<I,3>>keys;
  for(U j=0;j<profiles.size();++j){std::array<I,3>roots{};for(int i=0;i<3;++i){const S128 r=S128(beta[i])-S128(low)*h[i]-S128(delta)*profiles[j][i];if(r<=0||r>std::numeric_limits<I>::max())throw std::runtime_error("root-orbit root range");roots[i]=I(r);}std::sort(roots.begin(),roots.end());keys.push_back(roots);by_roots[roots].push_back(j);}
  std::vector<std::vector<U>>members;std::vector<mpz_class>group_mass;U old_group=0;mpz_class checked=0;
  for(const auto&x:by_roots){if(x.first==keys[current])old_group=members.size();members.push_back(x.second);mpz_class w=0;for(U j:x.second){if(mass[j]<=0)throw std::runtime_error("root-orbit nonpositive mass");w+=mass[j];}checked+=w;group_mass.push_back(w);}
  if(checked!=total)throw std::runtime_error("root-orbit total mismatch");groups_total+=members.size();max_groups=std::max<U>(max_groups,members.size());
  U next_group=0;if(members.size()==1)++single_group_windows;else next_group=flow.draw(group_mass,total,old_group,pick);
  if(next_group==old_group)++group_holds;else ++group_moves;
   
  mpz_class rank=pick(group_mass[next_group]);if(rank<0||rank>=group_mass[next_group])throw std::runtime_error("root-orbit conditional rank");
  for(U j:members[next_group]){if(rank<mass[j])return j;rank-=mass[j];}throw std::runtime_error("root-orbit profile missing");
 }
 void metadata(std::ostream&f)const{f<<"\"RO_calls\":"<<calls<<",\"RO_groups_total\":"<<groups_total<<",\"RO_max_groups\":"<<max_groups<<",\"RO_single_group_windows\":"<<single_group_windows<<",\"RO_group_moves\":"<<group_moves<<",\"RO_group_holds\":"<<group_holds<<",";}
};
