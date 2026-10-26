 

template<class Random>
std::pair<std::vector<I>,std::vector<I>>home_run_rows(const std::vector<I>&a,const std::vector<I>&b,Random&rng,int qa,int qb,Counters*stat=nullptr){
 if(a.size()!=b.size()||a.size()>size_t(std::numeric_limits<int>::max())||qa<0||qb<0||size_t(qa)>a.size()||size_t(qb)>b.size())throw std::runtime_error("invalid HomeRun dimensions/degrees");
 int n=int(a.size()),upper_a=qa,upper_b=n-qb,capacity=std::min(upper_a,upper_b),t=0;
 std::vector<int>reservoir;std::vector<I>c(n,0),d(n,0);
 auto draw=[&](U size){if(stat)stat->homerun_reservoir_draws++;return int(rng.below(size));};
 for(int i=0;i<n;++i){
  if(stat)stat->homerun_scan_columns++;if((a[i]!=0&&a[i]!=1)||(b[i]!=0&&b[i]!=1))throw std::runtime_error("HomeRun supports binary matrices only");
  if(a[i]!=b[i]){
   t++;
   if(int(reservoir.size())<capacity)reservoir.push_back(i);
   else{int j=draw(t);if(j<capacity){int old=reservoir[j];d[old]=1;c[old]=0;reservoir[j]=i;if(stat)stat->homerun_reservoir_replacements++;}else{d[i]=1;c[i]=0;}}
  }else{
   c[i]=d[i]=a[i];if(a[i])upper_a--;else upper_b--;int next=std::min(upper_a,upper_b);
   if(next<capacity){if(int(reservoir.size())>next){int j=draw(reservoir.size()),old=reservoir[j];d[old]=1;c[old]=0;reservoir[j]=reservoir.back();reservoir.pop_back();if(stat)stat->homerun_reservoir_removals++;}capacity=next;}
  }
 }
 for(int i:reservoir){c[i]=1;d[i]=0;}
 int ca=0,cb=0;for(int i=0;i<n;++i){ca+=int(c[i]);cb+=int(d[i]);if(c[i]+d[i]!=a[i]+b[i])throw std::runtime_error("HomeRun column margin failed");}
 if(ca!=qa||cb!=qb)throw std::runtime_error("HomeRun row margin failed");return {c,d};
}
