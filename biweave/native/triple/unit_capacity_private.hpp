#pragma once

#include <algorithm>
#include <array>
#include <limits>
#include <memory>
#include <stdexcept>
#include <utility>
#include <vector>

struct UnitCapacityPrivateV19 {
 using Rows=std::vector<std::vector<I>>;
 using Permutation=std::array<unsigned char,6>;
 struct DrawResult{Rows rows;U total,current_rank;bool fastbool;};
 Rows rows;
 int r=0,m=0,weight_groups=0;
 bool fastbool=false;
 U total=0,current_rank=0;
 std::array<I,2>weight{};
  
 std::array<std::array<int,6>,2>column;
 std::unique_ptr<GroupedPrivateV17>fallback;

 static U factorial(int n){
  static constexpr U values[7]={1,1,2,6,24,120,720};
  if(n<2||n>6)throw std::runtime_error("V19 factorial needs2..6 nodes");return values[n];
 }
 static const std::vector<Permutation>&permutations(int n){
  if(n<2||n>6)throw std::runtime_error("V19 permutations need2..6 nodes");
   
  static const std::array<std::vector<Permutation>,7>table=[](){
   std::array<std::vector<Permutation>,7>value;
   for(int size=2;size<=6;++size){Permutation p{};for(int j=0;j<size;++j)p[j]=static_cast<unsigned char>(j);
    value[size].reserve(static_cast<size_t>(factorial(size)));
    do{value[size].push_back(p);}while(std::next_permutation(p.begin(),p.begin()+size));
   }return value;
  }();
  return table[n];
 }
 void use_grouped(){
  fallback=std::make_unique<GroupedPrivateV17>(rows);
  total=fallback->total;current_rank=fallback->current_rank;fastbool=false;
 }
 explicit UnitCapacityPrivateV19(Rows input):rows(std::move(input)),r(int(rows.size())){
  if(r<2||r>6)throw std::runtime_error("V19 needs2..6 selected nodes");
  m=int(rows[0].size());if(m>12)throw std::runtime_error("V19 private width exceeds12");
  for(const auto&row:rows)if(int(row.size())!=m)throw std::runtime_error("V19 rows need equal lengths");
  for(auto&group:column)group.fill(-1);
  if(!m){use_grouped();return;}
  I combined=0;
  for(int j=0;j<m;++j){int owner=-1;I w=0;
   for(int v=0;v<r;++v){I x=rows[v][j];if(x<0)throw std::runtime_error("V19 negative weight");
    if(x){if(owner>=0)throw std::runtime_error("V19 selected column not private");owner=v;w=x;}}
   if(owner<0)throw std::runtime_error("V19 selected column empty");
   if(combined>std::numeric_limits<I>::max()-w)throw std::runtime_error("V19 total strength overflow");combined+=w;
   int h=0;while(h<weight_groups&&weight[h]!=w)++h;
   if(h==weight_groups){if(weight_groups==2){use_grouped();return;}weight[weight_groups++]=w;}
   if(column[h][owner]>=0){use_grouped();return;}column[h][owner]=j;
  }
  for(int h=0;h<weight_groups;++h)for(int v=0;v<r;++v)if(column[h][v]<0){use_grouped();return;}
  if(m!=r*weight_groups)throw std::runtime_error("V19 unit capacities disagree with width");
  U count=factorial(r);total=weight_groups==1?count:count*count;
   
  if(permutations(r).size()!=count)throw std::runtime_error("V19 permutation table mismatch");
  current_rank=0;fastbool=true;
 }
 Rows unrank(U rank){
  if(rank>=total)throw std::runtime_error("V19 rank outside complete count");
  if(!fastbool)return fallback->unrank(rank);
  U count=factorial(r);std::array<U,2>index{rank,0};
  if(weight_groups==2){index[0]=rank/count;index[1]=rank%count;}
  const auto&table=permutations(r);Rows output(r,std::vector<I>(m,0));
  for(int h=0;h<weight_groups;++h){const auto&p=table[index[h]];
   for(int v=0;v<r;++v)output[v][column[h][p[v]]]=weight[h];
  }return output;
 }
 template<class Random>Rows draw(Random&random,bool metropolis=true){
  if(!fastbool)return fallback->draw(random,metropolis);
  U rank=random.below(total-U(metropolis))+U(metropolis);
  return unrank(rank);
 }
 template<class Random>DrawResult draw_result(Random&random,bool metropolis=true){
  return {draw(random,metropolis),total,current_rank,fastbool};
 }
};
