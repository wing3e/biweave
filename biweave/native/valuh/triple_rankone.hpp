 

struct RankOneTriple {
 using Rows=std::array<std::vector<I>,3>;
 struct Term {int r,c;S128 constant=0;int slope=0;};
 struct Completion {std::vector<Term> terms;I lo=0,hi=0;Wide count=0;int rank=0;};
 Rows rows;int width=0,current_rank=0;std::array<int,3>degree{};
 std::array<I,3>strength{};std::vector<int>arity;std::vector<I>column_sum;
 std::vector<Completion>completions;Wide total=0;U current_multiplicity=0;
 Counters*stat=nullptr;

 static U multiplicity(const Rows&a){
  size_t m=a[0].size();if(m>3||a[1].size()!=m||a[2].size()!=m)throw std::runtime_error("rankone label shape invalid");
  int result=0;for(U subset=0;subset<(U(1)<<m);++subset){int product=1;for(int r=0;r<3;++r){int d=0;for(size_t j=0;j<m;++j)d+=((subset>>j)&1)&&a[r][j]>0;product*=d;}if((m-__builtin_popcountll(subset))&1)result-=product;else result+=product;}
  if(result<0||result>27)throw std::runtime_error("rankone label multiplicity invalid");return U(result);
 }
 static int support_rank(const std::vector<Term>&edges,int m){
  std::array<std::vector<int>,6>adj;for(size_t i=0;i<edges.size();++i){adj[edges[i].r].push_back(int(i));adj[3+edges[i].c].push_back(int(i));}
  std::array<bool,6>seen{};int active=0,components=0;for(int v=0;v<3+m;++v){active+=!adj[v].empty();if(adj[v].empty()||seen[v])continue;components++;std::vector<int>stack{v};seen[v]=true;while(!stack.empty()){int u=stack.back();stack.pop_back();for(int id:adj[u]){const auto&e=edges[id];int other=u==e.r?3+e.c:e.r;if(!seen[other]){seen[other]=true;stack.push_back(other);}}}}
  return int(edges.size())-active+components;
 }
 explicit RankOneTriple(Rows a,Counters*s=nullptr):rows(std::move(a)),stat(s){
  width=int(rows[0].size());if(width<1||width>3||rows[1].size()!=size_t(width)||rows[2].size()!=size_t(width))throw std::runtime_error("rankone block requires three rows and 1..3 columns");
  arity.resize(width);column_sum.resize(width);S128 grand_total=0;std::vector<Term>current_support;
  for(int r=0;r<3;++r){S128 sum=0;for(int j=0;j<width;++j){I x=rows[r][j];if(x<0)throw std::runtime_error("rankone negative input");sum+=x;grand_total+=x;if(x){degree[r]++;arity[j]++;current_support.push_back({r,j});}if(S128(column_sum[j])+x>std::numeric_limits<I>::max())throw std::runtime_error("rankone column sum overflow");column_sum[j]+=x;}
   if(sum>std::numeric_limits<I>::max())throw std::runtime_error("rankone row sum overflow");strength[r]=I(sum);
  }
  if(grand_total>std::numeric_limits<I>::max())throw std::runtime_error("rankone total overflow");for(int j=0;j<width;++j)if(!arity[j])throw std::runtime_error("rankone empty selected column");
  current_rank=support_rank(current_support,width);current_multiplicity=multiplicity(rows);if(stat)stat->rankone_solver_calls++;
  std::vector<Term>support;std::array<int,3>partial{};
  auto visit=[&](auto&&self,int j)->void{
   if(j==width){if(partial!=degree)return;if(stat)stat->rankone_supports_examined++;Completion c;c.terms=support;c.rank=support_rank(c.terms,width);if(c.rank>1){if(stat)stat->rankone_highrank_supports++;return;}if(solve(c)){total+=c.count;if(stat){stat->rankone_feasible_supports++;stat->rankone_max_completion_bits=std::max(stat->rankone_max_completion_bits,U(wide_bits(c.count)));}completions.push_back(std::move(c));}return;}
   for(U mask=1;mask<8;++mask){if(__builtin_popcountll(mask)!=arity[j])continue;bool possible=true;for(int r=0;r<3;++r)if((mask>>r)&1){partial[r]++;possible&=partial[r]<=degree[r];support.push_back({r,j});}if(possible)self(self,j+1);for(int r=2;r>=0;--r)if((mask>>r)&1){support.pop_back();partial[r]--;}}
  };visit(visit,0);
  if(current_rank<=1&&!total)throw std::runtime_error("rankone current state absent from restricted fiber");if(stat)stat->rankone_max_total_bits=std::max(stat->rankone_max_total_bits,U(wide_bits(total)));
 }
 bool solve(Completion&out){
  std::array<std::vector<int>,6>adj;std::array<S128,6>remaining{};std::array<int,6>d{};
  for(int r=0;r<3;++r)remaining[r]=S128(strength[r])-degree[r];for(int j=0;j<width;++j)remaining[3+j]=S128(column_sum[j])-arity[j];
  int n=int(out.terms.size());std::vector<bool>alive(n,true);for(int i=0;i<n;++i){const auto&e=out.terms[i];adj[e.r].push_back(i);adj[3+e.c].push_back(i);d[e.r]++;d[3+e.c]++;}
  std::vector<int>queue;for(int v=0;v<3+width;++v){if(remaining[v]<0)return false;if(d[v]==1)queue.push_back(v);}
  size_t position=0;int left=n;while(position<queue.size()){
   int v=queue[position++];if(d[v]!=1)continue;int id=-1;for(int candidate:adj[v])if(alive[candidate]){id=candidate;break;}if(id<0)throw std::runtime_error("rankone leaf lost edge");auto&e=out.terms[id];int other=v==e.r?3+e.c:e.r;S128 y=remaining[v];if(y<0)return false;e.constant=y;e.slope=0;remaining[v]=0;remaining[other]-=y;alive[id]=false;left--;d[v]--;d[other]--;if(remaining[other]<0)return false;if(d[other]==1)queue.push_back(other);
  }
  if(!left){for(int v=0;v<3+width;++v)if(remaining[v]!=0)return false;out.lo=out.hi=0;out.count=1;if(stat)stat->rankone_tree_completions++;return true;}
  if(out.rank!=1)throw std::runtime_error("rankone nonunicyclic residual");for(int v=0;v<3+width;++v)if(d[v]&&d[v]!=2)throw std::runtime_error("rankone cycle vertex degree invalid");
  int first=-1;for(int i=0;i<n;++i)if(alive[i]){first=i;break;}int start=out.terms[first].r,vertex=3+out.terms[first].c;out.terms[first].constant=0;out.terms[first].slope=1;int previous=first,visited=1;
  while(vertex!=start){int next=-1;for(int id:adj[vertex])if(alive[id]&&id!=previous){next=id;break;}if(next<0)throw std::runtime_error("rankone cycle traversal failed");auto&curr=out.terms[next];const auto&prev=out.terms[previous];curr.constant=remaining[vertex]-prev.constant;curr.slope=-prev.slope;vertex=vertex==curr.r?3+curr.c:curr.r;previous=next;if(++visited>left)throw std::runtime_error("rankone cycle traversal overflow");}
  if(visited!=left)throw std::runtime_error("rankone residual has multiple cycles");if(out.terms[previous].slope+out.terms[first].slope!=0||out.terms[previous].constant+out.terms[first].constant!=remaining[start])return false;
  S128 lo=0,hi=std::numeric_limits<I>::max();for(int i=0;i<n;++i)if(alive[i]){const auto&e=out.terms[i];if(e.slope==1)lo=std::max(lo,-e.constant);else if(e.slope==-1)hi=std::min(hi,e.constant);else throw std::runtime_error("rankone cycle slope invalid");}
  for(int v=0;v<3+width;++v)if(!d[v]&&remaining[v]!=0)return false;if(lo>hi||lo<0||hi>std::numeric_limits<I>::max())return false;out.lo=I(lo);out.hi=I(hi);out.count=Wide(hi-lo)+1;if(stat)stat->rankone_cycle_completions++;return true;
 }
 Rows unrank(Wide rank)const{
  if(rank>=total)throw std::runtime_error("rankone completion rank out of range");const Completion*c=nullptr;for(const auto&candidate:completions){if(rank<candidate.count){c=&candidate;break;}rank-=candidate.count;}if(!c)throw std::runtime_error("rankone completion selection failed");
  S128 t=S128(c->lo)+S128(rank);Rows result;for(auto&a:result)a.assign(width,0);for(const auto&e:c->terms){S128 x=e.constant+e.slope*t+1;if(x<1||x>std::numeric_limits<I>::max())throw std::runtime_error("rankone unrank weight invalid");result[e.r][e.c]=I(x);}return result;
 }
 template<class Random>Rows draw_corrected(Random&random){
  if(current_rank>1){if(stat)stat->rankone_current_highrank_holds++;return rows;}if(!current_multiplicity){if(stat)stat->rankone_current_zero_label_holds++;return rows;}
  if(stat)stat->rankone_proposals++;Rows proposed=unrank(total==1?0:random.below_wide(total));U next_multiplicity=multiplicity(proposed);bool accepted=next_multiplicity>=current_multiplicity||(next_multiplicity>0&&random.below_wide(Wide(current_multiplicity))<next_multiplicity);
  if(stat){stat->rankone_label_accepts+=accepted;stat->rankone_label_rejects+=!accepted;stat->rankone_zero_label_proposals+=!next_multiplicity;}return accepted?proposed:rows;
 }
};
