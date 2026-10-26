 

struct ExclusiveAssignmentV15 {
 using Rows=std::vector<std::vector<I>>;
 Rows rows;int r=0,m=0;U full=0,total=0,current_rank=0;
 std::vector<I>weights,strength,subset_sum,suffix_strength;
 std::vector<int>degree,suffix_degree;
 std::vector<U>current_masks;
 std::vector<std::vector<U>>admissible;
 std::vector<std::vector<unsigned char>>admissible_flag;
 std::vector<std::vector<U>>memo;
 std::vector<std::vector<unsigned char>>seen;
 U admissible_masks_total=0,dp_states=0,dp_branches=0;

 explicit ExclusiveAssignmentV15(Rows input):rows(std::move(input)),r(int(rows.size())){
  if(r<2||r>6)throw std::runtime_error("V15 assignment needs 2..6 nodes");
  m=int(rows[0].size());if(m>12)throw std::runtime_error("V15 assignment private width exceeds12");
  for(const auto&row:rows)if(int(row.size())!=m)throw std::runtime_error("V15 rows need equal lengths");
  full=(U(1)<<m)-1;weights.assign(m,0);degree.assign(r,0);strength.assign(r,0);current_masks.assign(r,0);
  I combined=0;
  for(int j=0;j<m;++j){int arity=0;I weight=0;
   for(int node=0;node<r;++node){I value=rows[node][j];if(value<0)throw std::runtime_error("V15 negative weight");
    if(value){arity++;weight=value;degree[node]++;if(strength[node]>std::numeric_limits<I>::max()-value)throw std::runtime_error("V15 strength overflow");strength[node]+=value;current_masks[node]|=U(1)<<j;}
   }
   if(arity!=1)throw std::runtime_error("V15 requires every input label to be private");
   if(combined>std::numeric_limits<I>::max()-weight)throw std::runtime_error("V15 total weight overflow");combined+=weight;weights[j]=weight;
  }
  subset_sum.assign(size_t(full)+1,0);
  for(U mask=1;mask<=full;++mask){U bit=mask&(~mask+1);int j=__builtin_ctzll(bit);subset_sum[mask]=subset_sum[mask^bit]+weights[j];}
  admissible.resize(r);admissible_flag.assign(r,std::vector<unsigned char>(size_t(full)+1,0));
  auto label_lex=[](U a,U b){if(a==b)return false;U first=(a^b)&(~(a^b)+1);return bool(a&first);};
  for(int node=0;node<r;++node){
   for(U mask=0;mask<=full;++mask)if(__builtin_popcountll(mask)==degree[node]&&subset_sum[mask]==strength[node]){admissible[node].push_back(mask);admissible_flag[node][mask]=1;}
   std::sort(admissible[node].begin(),admissible[node].end(),label_lex);admissible_masks_total+=admissible[node].size();
  }
  suffix_degree.assign(r+1,0);suffix_strength.assign(r+1,0);
  for(int node=r;node-->0;){suffix_degree[node]=suffix_degree[node+1]+degree[node];suffix_strength[node]=suffix_strength[node+1]+strength[node];}
  memo.assign(r+1,std::vector<U>(size_t(full)+1,0));seen.assign(r+1,std::vector<unsigned char>(size_t(full)+1,0));
  total=count(0,full);if(!total)throw std::runtime_error("V15 current feasible partition disappeared");
  current_rank=rank_of(current_masks);if(current_rank>=total)throw std::runtime_error("V15 invalid current rank");
 }
 U count(int node,U remaining){
  if(node<0||node>r||remaining>full)throw std::runtime_error("V15 DP index out of range");
  if(seen[node][remaining])return memo[node][remaining];seen[node][remaining]=1;dp_states++;
  U value=0;
  if(__builtin_popcountll(remaining)==suffix_degree[node]&&subset_sum[remaining]==suffix_strength[node]){
   if(node==r)value=remaining==0;
   else for(U mask=remaining;;mask=(mask-1)&remaining){if(admissible_flag[node][mask]){dp_branches++;U tail=count(node+1,remaining^mask);
    if(value>std::numeric_limits<U>::max()-tail)throw std::runtime_error("V15 partition count overflow");value+=tail;}if(mask==0)break;}
  }
  memo[node][remaining]=value;return value;
 }
 U rank_of(const std::vector<U>&masks){
  if(int(masks.size())!=r)throw std::runtime_error("V15 rank needs one mask per row");
  U rank=0,remaining=full;
  for(int node=0;node<r;++node){bool found=false;
   for(U candidate:admissible[node])if((candidate&remaining)==candidate){U tail=count(node+1,remaining^candidate);
    if(candidate==masks[node]){if(!tail)throw std::runtime_error("V15 requested rank has no suffix");remaining^=candidate;found=true;break;}rank+=tail;}
   if(!found)throw std::runtime_error("V15 requested rank infeasible");
  }
  if(remaining)throw std::runtime_error("V15 rank leaves unassigned labels");return rank;
 }
 Rows unrank(U rank){
  if(rank>=total)throw std::runtime_error("V15 unrank out of range");Rows output(r,std::vector<I>(m,0));U remaining=full;
  for(int node=0;node<r;++node){bool found=false;
   for(U candidate:admissible[node])if((candidate&remaining)==candidate){U tail=count(node+1,remaining^candidate);
    if(rank>=tail){rank-=tail;continue;}
    for(int j=0;j<m;++j)if(candidate>>j&1)output[node][j]=weights[j];remaining^=candidate;found=true;break;
   }
   if(!found)throw std::runtime_error("V15 unrank failed exact suffix");
  }
  if(remaining||rank)throw std::runtime_error("V15 unrank leftover");return output;
 }
 template<class Random>Rows draw(Random&random,bool metropolis=false){
  if(total==1)return rows;
  U rank=random.below(total-(metropolis?1:0));if(metropolis&&rank>=current_rank)rank++;
  return unrank(rank);
 }
};
