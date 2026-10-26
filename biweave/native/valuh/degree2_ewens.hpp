#pragma once

struct Degree2EwensPlan {
 bool eligible=false;
 I strength=0;
 std::vector<int> rows,cols;
 U draws=0,raw_permutations=0,last_cycles=0;
 explicit Degree2EwensPlan(const Graph&g){
  bool good=true;
  for(int side=0;side<2;++side){int count=side?g.nc:g.nr,off=side?g.nr:0;
   auto&active=side?cols:rows;
   for(int v=0;v<count;++v){int d=g.target_degree[off+v];I s=g.target_strength[off+v];
    if(!d){if(s)good=false;continue;}
    if(d!=2)good=false;
    if(!strength)strength=s;else if(s!=strength)good=false;
    active.push_back(v);
   }
  }

  eligible=good&&rows.size()==cols.size()&&rows.size()>=2&&strength>=2&&strength<=8;
 }

 std::vector<int> permutation(RNG&rng){
  int n=int(rows.size());std::vector<int>next(n);
  for(;;){raw_permutations++;
   for(int i=0;i<n;++i){U ticket=rng.below(U(2)*U(i)+U(strength-1));
    if(ticket<U(strength-1))next[i]=i;
    else{int after=int((ticket-U(strength-1))/2);next[i]=next[after];next[after]=i;}
   }
   bool fixed=false;for(int i=0;i<n;++i)if(next[i]==i){fixed=true;break;}
   if(!fixed)return next;
  }
 }
 void draw(Engine&e,Graph&g){
  if(!eligible)throw std::runtime_error("uncertified degree2 independent draw");
  auto rho=permutation(e.rng);int n=int(rows.size());
  std::vector<int>sigma(n);for(int i=0;i<n;++i)sigma[i]=i;
  for(int i=n-1;i>0;--i)std::swap(sigma[i],sigma[e.rng.below(U(i)+1)]);
  std::vector<I>phase(n,0);last_cycles=0;
  for(int i=0;i<n;++i)if(!phase[i]){last_cycles++;I value=1+I(e.rng.below(U(strength-1)));
   int j=i;do{phase[j]=value;j=rho[j];}while(j!=i);
  }
  U old1=g.hash1,old2=g.hash2;

  while(!g.edges.empty()){auto x=g.edges.back();g.set_raw(x.r,x.c,0);}
  for(int i=0;i<n;++i){g.set_raw(rows[i],cols[sigma[i]],phase[i]);
   g.set_raw(rows[i],cols[sigma[rho[i]]],strength-phase[i]);}
  e.stat.work++;e.stat.changed_outer+=old1!=g.hash1||old2!=g.hash2;draws++;
 }
};
