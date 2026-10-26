#pragma once
#include <algorithm>
#include <array>
#include <set>
#include <ostream>
#include <stdexcept>
#include <vector>

struct CertifiedCoveragePriority {
 bool requested=false,static_eligible=false,round_S=false,cached_true=false;
 std::array<std::vector<int>,2>objects;
 std::vector<std::array<I,3>>cached_edges;
 U round_calls=0,priority_rounds=0,ordinary_rate_rounds=0,classifications=0;
 U exact_cache_hits=0,static_skips=0,h_matching_failures=0,weight_tie_failures=0;
 U triple_checks=0,shared_triple_holds=0,nonunique_triples=0,certificate_passes=0,D_identity_skips=0;

 void initialize(const Graph&g,bool want){
  requested=want;if(!want)return;

  if(g.nr!=g.nc||(g.nr!=6&&g.nr!=8)||U(g.nr)*U(g.nc)<=20)return;
  std::array<int,2>ones{},twos{};
  for(int axis=0;axis<2;++axis){const int n=axis?g.nc:g.nr,offset=axis?g.nr:0;
   for(int v=0;v<n;++v){const int d=g.target_degree[offset+v];
    if(d==1)++ones[axis];else if(d==2)++twos[axis];else return;
   }
  }
  if(ones[0]!=twos[1]||ones[1]!=twos[0]||twos[0]!=twos[1]||twos[0]<3||twos[0]>4)return;
  for(int axis=0;axis<2;++axis){const int n=axis?g.nc:g.nr,offset=axis?g.nr:0;
   for(int v=0;v<n;++v)if(g.target_degree[offset+v]==2)objects[axis].push_back(v);
  }
  static_eligible=true;
 }
 std::vector<std::array<I,3>> exact_edges(const Graph&g)const{
  std::vector<std::array<I,3>>v;v.reserve(g.edges.size());
  for(const auto&ed:g.edges)v.push_back({I(ed.r),I(ed.c),ed.w});
  std::sort(v.begin(),v.end());return v;
 }
 bool triple_identity(const Graph&g,int axis,const std::array<int,3>&nodes){
  ++triple_checks;struct Label{int node,owner;I weight;};std::array<Label,6>labels;
  std::array<I,3>strengths{};int next=0;
  for(int owner=0;owner<3;++owner){const int v=axis?g.nr+nodes[owner]:nodes[owner];
   if(g.degree[v]!=2||g.adj[v].size()!=2)throw std::runtime_error("priority triple degree audit");
   strengths[owner]=g.target_strength[v];S128 sum=0;
   for(int id:g.adj[v]){const auto ed=g.edges.at(size_t(id));
    if(ed.w<=0||(axis?ed.c:ed.r)!=nodes[owner])throw std::runtime_error("priority triple adjacency");
    labels[size_t(next++)]={axis?ed.r:ed.c,owner,ed.w};sum+=S128(ed.w);
   }
   if(sum!=S128(strengths[owner]))throw std::runtime_error("priority triple strength audit");
  }
  if(next!=6)throw std::runtime_error("priority triple record count");
  std::sort(labels.begin(),labels.end(),[](const Label&a,const Label&b){return a.node<b.node;});
  for(int i=1;i<6;++i)if(labels[i-1].node==labels[i].node){++shared_triple_holds;return true;}
  std::array<std::array<S128,6>,6>sums{};
  for(int a=0;a<6;++a)for(int b=a+1;b<6;++b)sums[a][b]=S128(labels[a].weight)+labels[b].weight;
  U legal=0,original=0;
  for(int a=0;a<6;++a)for(int b=a+1;b<6;++b){
   if(sums[a][b]!=S128(strengths[0]))continue;
   for(int c=0;c<6;++c)if(c!=a&&c!=b)for(int d=c+1;d<6;++d)if(d!=a&&d!=b){
    if(sums[c][d]!=S128(strengths[1]))continue;
    std::array<int,2>remaining{};int n=0;
    for(int i=0;i<6;++i)if(i!=a&&i!=b&&i!=c&&i!=d)remaining[n++]=i;
    if(n!=2)throw std::runtime_error("priority remaining pair count");
    if(sums[remaining[0]][remaining[1]]!=S128(strengths[2]))continue;
    ++legal;bool same=true;
    for(int i=0;i<6;++i){const int owner=(i==a||i==b)?0:((i==c||i==d)?1:2);same&=labels[i].owner==owner;}
    original+=same;
   }
  }
  if(!legal||legal>90||original!=1)throw std::runtime_error("priority complete partition audit");
  if(legal!=1){++nonunique_triples;return false;}return true;
 }
 bool current(const Graph&g){
  if(!requested)throw std::runtime_error("unrequested priority certificate");
  if(!static_eligible){++static_skips;return false;}
  if(g.D||g.degree!=g.target_degree)throw std::runtime_error("priority classifier outside F");
  const auto now=exact_edges(g);
   
  if(cached_true&&now==cached_edges){++exact_cache_hits;return true;}
  cached_true=false;cached_edges.clear();++classifications;
  std::set<I>weights;std::vector<int>hdegree(size_t(g.nr+g.nc),0);
  for(const auto&ed:g.edges){if(ed.w<=0)throw std::runtime_error("priority nonpositive record");
   if(!weights.insert(ed.w).second){++weight_tie_failures;return false;}
   if(g.target_degree[ed.r]==2&&g.target_degree[g.nr+ed.c]==2){
    if(++hdegree[ed.r]>1||++hdegree[g.nr+ed.c]>1){++h_matching_failures;return false;}
   }
  }
   
  for(int axis=0;axis<2;++axis){const auto&pool=objects[axis];const int offset=axis?g.nr:0;
   for(int v:pool)if(hdegree[offset+v]!=1){++h_matching_failures;return false;}
   for(size_t a=0;a<pool.size();++a)for(size_t b=a+1;b<pool.size();++b)for(size_t c=b+1;c<pool.size();++c)
    if(!triple_identity(g,axis,{pool[a],pool[b],pool[c]}))return false;
  }
  ++certificate_passes;cached_true=true;cached_edges=now;return true;
 }
 void begin_round(const Graph&g){if(!requested)return;++round_calls;round_S=current(g);if(round_S)++priority_rounds;else ++ordinary_rate_rounds;}
 void metadata(std::ostream&f)const{
  f<<"\"CP_requested\":"<<(requested?"true":"false")<<",\"CP_static_eligible\":"<<(static_eligible?"true":"false")
   <<",\"CP_round_calls\":"<<round_calls<<",\"CP_priority_rounds\":"<<priority_rounds<<",\"CP_ordinary_rate_rounds\":"<<ordinary_rate_rounds
   <<",\"CP_classifications\":"<<classifications<<",\"CP_exact_cache_hits\":"<<exact_cache_hits<<",\"CP_static_skips\":"<<static_skips
   <<",\"CP_h_matching_failures\":"<<h_matching_failures<<",\"CP_weight_tie_failures\":"<<weight_tie_failures
   <<",\"CP_triple_checks\":"<<triple_checks<<",\"CP_shared_triple_holds\":"<<shared_triple_holds<<",\"CP_nonunique_triples\":"<<nonunique_triples
   <<",\"CP_D_identity_skips\":"<<D_identity_skips<<",\"CP_certificate_passes\":"<<certificate_passes<<",\"CP_cached_true\":"<<(cached_true?"true":"false")
   <<",\"CP_policy\":\"bounded 3/4-block allpositive mixed-degree1/2 forest certificate; H perfect matching, distinct positive weights, BOTH axes every D3 triple singleton or shared-endpoint hold; S rate1 otherwise50/10000; exact endpoint MH before commit; cache uses exact named records\",";
 }
};
