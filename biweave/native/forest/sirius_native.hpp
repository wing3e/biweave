#pragma once

struct SiriusDegreeKernel {
 std::vector<std::pair<int,int>> occurrences;
 U calls=0,accepted=0,degree_reject=0,mh_reject=0,nonchanging=0;
 static constexpr U occurrence_limit=5000000;
 explicit SiriusDegreeKernel(const Graph&g){
  U total=0;
  for(const auto&ed:g.edges){
   if(U(ed.w)>occurrence_limit-total)throw std::runtime_error("Sirius occurrence-list memory limit: total weight exceeds 5000000");
   total+=U(ed.w);
  }
  occurrences.reserve(total);
  for(const auto&ed:g.edges)for(I k=0;k<ed.w;++k)occurrences.emplace_back(ed.r,ed.c);
 }
 void step(Engine&e,Graph&g){
  calls++;e.stat.work++;
  if(occurrences.size()<2){nonchanging++;return;}
  if(e.rng.below(2)==0){e.stat.lazy++;return;}
  U first=e.rng.below(occurrences.size()),second=first;
  while(second==first)second=e.rng.below(occurrences.size());
  auto [i,j]=occurrences[first];auto [k,l]=occurrences[second];
  if(i==k||j==l){nonchanging++;return;}
  I a=g.value(i,j),b=g.value(k,l),c=g.value(i,l),d=g.value(k,j);
  if(a<=0||b<=0)throw std::runtime_error("Sirius stale occurrence list");
   
  U numerator=U(c+1)*U(d+1),denominator=U(a)*U(b);
  if(numerator<denominator&&e.rng.below(denominator)>=numerator){mh_reject++;return;}
  int lose_a=a==1,lose_b=b==1,gain_c=c==0,gain_d=d==0;
  if(gain_c!=lose_a||gain_d!=lose_b||gain_d!=lose_a||gain_c!=lose_b){degree_reject++;return;}
  g.set_raw(i,j,a-1);g.set_raw(k,l,b-1);g.set_raw(i,l,c+1);g.set_raw(k,j,d+1);
  occurrences[first]={i,l};occurrences[second]={k,j};
  accepted++;e.stat.changed_outer++;
 }
};
