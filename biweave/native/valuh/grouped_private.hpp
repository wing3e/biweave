#pragma once

#include <memory>

struct GroupedPrivateV17 {
 using Rows=std::vector<std::vector<I>>;
 struct DrawResult {Rows rows;U total,current_rank;bool fastbool;};
 struct Group {
  I weight=0;
  std::vector<int>columns,capacity;
  std::vector<U>suffix_count;
  U total=1;
 };
 Rows rows;
 int r=0,m=0;
 bool fastbool=false;
 U total=0,current_rank=0;
 std::vector<int>degree,current_owner;
 std::vector<I>strength,weights;
 std::vector<Group>groups;
 std::unique_ptr<ExclusiveAssignmentV15>fallback;

 static U multiply(U a,U b){
  if(b&&a>std::numeric_limits<U>::max()/b)throw std::runtime_error("V17 assignment count overflow");
  return a*b;
 }
 static U add(U a,U b){
  if(a>std::numeric_limits<U>::max()-b)throw std::runtime_error("V17 assignment rank overflow");
  return a+b;
 }
 static U choose(int n,int k){
  if(n<0||n>12||k<0||k>n)return 0;
  k=std::min(k,n-k);U answer=1;
  for(int j=1;j<=k;++j){U numerator=multiply(answer,U(n-k+j));
   if(numerator%U(j))throw std::runtime_error("V17 nonintegral binomial count");answer=numerator/U(j);
  }
  return answer;
 }
 static U combination_rank(int n,const std::vector<int>&chosen){
  int k=int(chosen.size()),previous=-1;U rank=0;
  if(k>n)throw std::runtime_error("V17 oversized combination");
  for(int j=0;j<k;++j){int value=chosen[j];if(value<=previous||value>=n)throw std::runtime_error("V17 invalid combination labels");
   for(int v=previous+1;v<value;++v)rank=add(rank,choose(n-v-1,k-j-1));previous=value;
  }
  if(rank>=choose(n,k))throw std::runtime_error("V17 combination rank outside count");return rank;
 }
 static std::vector<int>combination_unrank(int n,int k,U rank){
  U count=choose(n,k);if(!count||rank>=count)throw std::runtime_error("V17 combination unrank outside count");
  std::vector<int>answer;int previous=-1;
  for(int j=0;j<k;++j){bool found=false;
   for(int value=previous+1;value<=n-(k-j);++value){U block=choose(n-value-1,k-j-1);
    if(rank>=block){rank-=block;continue;}answer.push_back(value);previous=value;found=true;break;
   }
   if(!found)throw std::runtime_error("V17 combination unrank failed");
  }
  if(rank)throw std::runtime_error("V17 combination rank leftover");return answer;
 }

 explicit GroupedPrivateV17(Rows input):rows(std::move(input)),r(int(rows.size())){
  if(r<2||r>6)throw std::runtime_error("V17 needs2..6 selected nodes");
  m=int(rows[0].size());if(m>12)throw std::runtime_error("V17 private width exceeds12");
  for(const auto&row:rows)if(int(row.size())!=m)throw std::runtime_error("V17 rows need equal lengths");
  degree.assign(r,0);strength.assign(r,0);weights.assign(m,0);current_owner.assign(m,-1);
  I combined=0;
  for(int j=0;j<m;++j){int arity=0;
   for(int v=0;v<r;++v){I value=rows[v][j];if(value<0)throw std::runtime_error("V17 negative weight");
    if(value){arity++;weights[j]=value;current_owner[j]=v;degree[v]++;
     if(strength[v]>std::numeric_limits<I>::max()-value)throw std::runtime_error("V17 row strength overflow");strength[v]+=value;
    }
   }
   if(arity!=1)throw std::runtime_error("V17 every selected column must be private");
   if(combined>std::numeric_limits<I>::max()-weights[j])throw std::runtime_error("V17 total strength overflow");combined+=weights[j];
  }
  auto distinct=weights;std::sort(distinct.begin(),distinct.end());distinct.erase(std::unique(distinct.begin(),distinct.end()),distinct.end());
  if(distinct.size()>2){fallback=std::make_unique<ExclusiveAssignmentV15>(rows);total=fallback->total;current_rank=fallback->current_rank;return;}
  fastbool=true;
  if(!m){total=1;current_rank=0;return;}
  groups.resize(distinct.size());
  for(size_t h=0;h<groups.size();++h){groups[h].weight=distinct[h];groups[h].capacity.assign(r,0);
   for(int j=0;j<m;++j)if(weights[j]==distinct[h])groups[h].columns.push_back(j);
  }
  if(distinct.size()==1){for(int v=0;v<r;++v){
    __int128 expected=__int128(degree[v])*__int128(distinct[0]);
    if(expected!=__int128(strength[v]))throw std::runtime_error("V17 one-weight row strength inconsistent");groups[0].capacity[v]=degree[v];
   }}else{I low=distinct[0],high=distinct[1];__int128 delta=__int128(high)-__int128(low);
   for(int v=0;v<r;++v){__int128 numerator=__int128(degree[v])*__int128(high)-__int128(strength[v]);
    if(numerator<0||numerator%delta)throw std::runtime_error("V17 two-weight row counts nonintegral");
    __int128 a=numerator/delta;if(a<0||a>degree[v])throw std::runtime_error("V17 two-weight row counts outside degree");
    groups[0].capacity[v]=int(a);groups[1].capacity[v]=degree[v]-int(a);
   }
  }
  total=1;
  for(auto&group:groups){group.suffix_count.assign(r+1,1);int suffix_size=0;
   for(int v=r;v-->0;){suffix_size+=group.capacity[v];group.suffix_count[v]=multiply(choose(suffix_size,group.capacity[v]),group.suffix_count[v+1]);}
   if(suffix_size!=int(group.columns.size()))throw std::runtime_error("V17 group capacities mismatch labels");
   group.total=group.suffix_count[0];if(!group.total)throw std::runtime_error("V17 empty feasible group");total=multiply(total,group.total);
  }
  current_rank=0;
  for(const auto&group:groups)current_rank=add(multiply(current_rank,group.total),rank_group(group));
  if(!total||current_rank>=total)throw std::runtime_error("V17 current assignment rank outside total");
 }

 U rank_group(const Group&group)const{
  std::vector<int>remaining=group.columns;U rank=0;
  for(int v=0;v<r;++v){std::vector<int>chosen;
   for(size_t j=0;j<remaining.size();++j)if(current_owner[remaining[j]]==v)chosen.push_back(int(j));
   if(int(chosen.size())!=group.capacity[v])throw std::runtime_error("V17 current group capacity inconsistent");
   rank=add(rank,multiply(combination_rank(int(remaining.size()),chosen),group.suffix_count[v+1]));
   std::vector<int>next;for(int col:remaining)if(current_owner[col]!=v)next.push_back(col);remaining=std::move(next);
  }
  if(!remaining.empty()||rank>=group.total)throw std::runtime_error("V17 group rank invalid");return rank;
 }
 void unrank_group(const Group&group,U rank,Rows&output)const{
  if(rank>=group.total)throw std::runtime_error("V17 group unrank outside count");
  std::vector<int>remaining=group.columns;
  for(int v=0;v<r;++v){U tail=group.suffix_count[v+1],combination=rank/tail;rank%=tail;
   auto chosen=combination_unrank(int(remaining.size()),group.capacity[v],combination);
   std::vector<unsigned char>selected(remaining.size(),0);for(int j:chosen){selected[j]=1;output[v][remaining[j]]=group.weight;}
   std::vector<int>next;for(size_t j=0;j<remaining.size();++j)if(!selected[j])next.push_back(remaining[j]);remaining=std::move(next);
  }
  if(!remaining.empty()||rank)throw std::runtime_error("V17 group unrank leftover");
 }
 Rows unrank(U rank){
  if(rank>=total)throw std::runtime_error("V17 unrank outside count");
  if(!fastbool)return fallback->unrank(rank);
  Rows output(r,std::vector<I>(m,0));
  std::vector<U>group_rank(groups.size(),0);
  for(size_t h=groups.size();h-->0;){group_rank[h]=rank%groups[h].total;rank/=groups[h].total;}
  if(rank)throw std::runtime_error("V17 global rank leftover");
  for(size_t h=0;h<groups.size();++h)unrank_group(groups[h],group_rank[h],output);
  return output;
 }
 template<class Random>Rows draw(Random&random,bool metropolis=true){
  if(total==1)return rows;
  U rank=random.below(total-U(metropolis));if(metropolis&&rank>=current_rank)rank++;
  return unrank(rank);
 }
 template<class Random>DrawResult draw_result(Random&random,bool metropolis=true){
  return {draw(random,metropolis),total,current_rank,fastbool};
 }
};
