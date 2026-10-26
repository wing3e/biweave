 

struct ExclusiveTriple {
 std::array<std::vector<I>,3>rows;std::vector<I>weight;std::array<int,3>degree{};std::array<I,3>strength{};
 std::array<U,3>current{};std::vector<std::array<U,3>>assignments;Counters*stat=nullptr;
 ExclusiveTriple(std::vector<I>a,std::vector<I>b,std::vector<I>c,Counters*s=nullptr):rows{std::move(a),std::move(b),std::move(c)},stat(s){
  size_t m=rows[0].size();if(rows[1].size()!=m||rows[2].size()!=m||m>6)throw std::runtime_error("triple arrays need equal size <=6");I total=0;
  for(size_t j=0;j<m;++j){I w=0;int arity=0;for(int r=0;r<3;++r){I v=rows[r][j];if(v<0||w>std::numeric_limits<I>::max()-v)throw std::runtime_error("invalid triple int64 weight");w+=v;arity+=v>0;}
   if(arity!=1)throw std::runtime_error("triple needs partial column arity one");if(total>std::numeric_limits<I>::max()-w)throw std::runtime_error("triple total exceeds int64");total+=w;weight.push_back(w);
   for(int r=0;r<3;++r)if(rows[r][j]>0){degree[r]++;strength[r]+=rows[r][j];current[r]|=U(1)<<j;}
  }
  for(int d:degree)if(d>2)throw std::runtime_error("triple each row owns at most two columns");if(stat)stat->triple_partition_calls++;
  U full=(U(1)<<m)-1;auto sum=[&](U mask){I out=0;for(size_t j=0;j<m;++j)if(mask>>j&1)out+=weight[j];return out;};
  for(U first=0;first<=full;++first){if(__builtin_popcountll(first)!=degree[0])continue;U remaining=full^first;
   for(U second=remaining;;second=(second-1)&remaining){if(__builtin_popcountll(second)==degree[1]){U third=remaining^second;if(stat)stat->triple_partition_candidates++;if(sum(first)==strength[0]&&sum(second)==strength[1]&&sum(third)==strength[2])assignments.push_back({first,second,third});}if(second==0)break;}
  }
  if(assignments.empty()||assignments.size()>90)throw std::runtime_error("invalid exclusive triple class");if(std::find(assignments.begin(),assignments.end(),current)==assignments.end())throw std::runtime_error("current triple assignment missing");if(stat){stat->triple_legal_assignments+=assignments.size();stat->triple_max_assignments=std::max(stat->triple_max_assignments,U(assignments.size()));}
 }
 template<class Random>
 std::array<std::vector<I>,3>draw(Random&random,bool metropolis=false)const{
  size_t size=assignments.size();if(size==1){if(stat)stat->triple_singleton_holds++;return rows;}if(stat)stat->triple_nontrivial++;
  U selected;if(metropolis){U current_index=U(std::find(assignments.begin(),assignments.end(),current)-assignments.begin());selected=random.below(U(size-1));if(selected>=current_index)selected++;if(stat)stat->triple_metropolis_draws++;}else selected=random.below(U(size));
  std::array<std::vector<I>,3>output;for(auto&row:output)row.assign(weight.size(),0);for(int r=0;r<3;++r)for(size_t j=0;j<weight.size();++j)if(assignments[selected][r]>>j&1)output[r][j]=weight[j];return output;
 }
};
