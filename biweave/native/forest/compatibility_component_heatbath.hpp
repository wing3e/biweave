#pragma once
#include <algorithm>
#include <array>
#include <functional>
#include <map>
#include <numeric>
#include <string>
#include <unordered_map>
#include <utility>
#include <vector>

struct CompatibilityComponentHeatbath {
 struct Record { int node; I weight; bool operator==(const Record&b)const{return node==b.node&&weight==b.weight;} };
 struct Pair {int a,b;};
 struct Guard {};
 struct Component {
  std::vector<int> owners,labels;
  std::vector<std::vector<Pair>> pairs;
  std::unordered_map<std::string,mpz_class> counts;
  mpz_class total=0;
  bool guarded=false;
  U work=0;
  static bool used(const std::string&s,int i){return (static_cast<unsigned char>(s[size_t(i/8)])>>(i%8))&1;}
  static void flip(std::string&s,int i){s[size_t(i/8)]^=char(1U<<(i%8));}
  mpz_class count(int depth,std::string&mask) {
   if(depth==int(owners.size()))return 1;
   auto found=counts.find(mask);if(found!=counts.end())return found->second;
   mpz_class result=0;
   for(const auto&p:pairs[size_t(depth)]) {
    if(++work>200000)throw Guard{};
    if(used(mask,p.a)||used(mask,p.b))continue;
    flip(mask,p.a);flip(mask,p.b);result+=count(depth+1,mask);flip(mask,p.a);flip(mask,p.b);
   }
    
   if(counts.size()>=200000 || counts.size()*(mask.size()+96)>64U*1024U*1024U)throw Guard{};
   counts.emplace(mask,result);return result;
  }
  void compile(){std::string mask((labels.size()+7)/8,'\0');try{total=count(0,mask);}catch(const Guard&){guarded=true;counts.clear();total=0;}}
  template<class EngineType>void draw(EngineType&e,std::vector<int>&assignment)const {
   if(guarded)return;
   if(total<=0)throw std::runtime_error("component conditional has no original state");
   mpz_class rank=zbig(e.rng.below_big(bigz(total)));
   std::string mask((labels.size()+7)/8,'\0');
   for(int depth=0;depth<int(owners.size());++depth){bool selected=false;
    for(const auto&p:pairs[size_t(depth)]) {
     if(used(mask,p.a)||used(mask,p.b))continue;
     flip(mask,p.a);flip(mask,p.b);
     mpz_class mass=1;
     if(depth+1<int(owners.size())){auto found=counts.find(mask);if(found==counts.end())throw std::runtime_error("component suffix count missing");mass=found->second;}
     if(rank<mass){assignment[size_t(labels[size_t(p.a)])]=owners[size_t(depth)];assignment[size_t(labels[size_t(p.b)])]=owners[size_t(depth)];selected=true;break;}
     rank-=mass;flip(mask,p.a);flip(mask,p.b);
    }
    if(!selected)throw std::runtime_error("component rank did not decode");
   }
  }
 };
 struct Model {
  std::vector<Record> labels;
  std::vector<I> strengths;
  std::vector<Component> components;
  bool ready=false,guarded=false;
  U candidate_work=0;
  void compile(const std::vector<Record>&records,const std::vector<I>&totals) {
   labels=records;strengths=totals;components.clear();ready=true;guarded=false;candidate_work=0;
   const int k=int(totals.size()),m=int(records.size());
   if(m!=2*k)throw std::runtime_error("component record cardinality");
   std::unordered_map<I,std::vector<int>> weights;
   for(int a=0;a<m;++a)weights[records[size_t(a)].weight].push_back(a);
   std::vector<std::vector<Pair>> choices(size_t(k),std::vector<Pair>{});
   std::vector<int>parent(size_t(k+m));std::iota(parent.begin(),parent.end(),0);
   auto root=[&](int x){while(x!=parent[size_t(x)]){parent[size_t(x)]=parent[size_t(parent[size_t(x)])];x=parent[size_t(x)];}return x;};
   auto join=[&](int a,int b){a=root(a);b=root(b);if(a!=b)parent[size_t(a)]=b;};
   for(int owner=0;owner<k;++owner)for(int a=0;a<m;++a) {
    if(++candidate_work>200000){guarded=true;return;}
    const S128 remaining=S128(totals[size_t(owner)])-S128(records[size_t(a)].weight);
    if(remaining<=0||remaining>S128(std::numeric_limits<I>::max()))continue;
    const auto found=weights.find(I(remaining));if(found==weights.end())continue;
    for(int b:found->second)if(b>a){if(++candidate_work>200000){guarded=true;return;}
     choices[size_t(owner)].push_back({a,b});join(owner,k+a);join(owner,k+b);
    }
   }
   std::map<int,int> ids;
   for(int owner=0;owner<k;++owner){if(choices[size_t(owner)].empty())throw std::runtime_error("component owner has no original pair");const int key=root(owner);auto p=ids.emplace(key,int(ids.size()));if(p.second)components.emplace_back();components[size_t(p.first->second)].owners.push_back(owner);}
   for(int a=0;a<m;++a){auto p=ids.find(root(k+a));if(p==ids.end())throw std::runtime_error("component uncovered original endpoint");components[size_t(p->second)].labels.push_back(a);}
   for(auto&component:components) {
    if(component.labels.size()!=2*component.owners.size())throw std::runtime_error("component balanced cardinality");
    std::sort(component.owners.begin(),component.owners.end(),[&](int a,int b){return choices[size_t(a)].size()!=choices[size_t(b)].size()?choices[size_t(a)].size()<choices[size_t(b)].size():a<b;});
    std::vector<int> local(size_t(m),-1);for(size_t a=0;a<component.labels.size();++a)local[size_t(component.labels[a])]=int(a);
    for(int owner:component.owners){component.pairs.emplace_back();for(const auto&p:choices[size_t(owner)])component.pairs.back().push_back({local[size_t(p.a)],local[size_t(p.b)]});}
    component.compile();
    if(!component.guarded&&component.total<=0)throw std::runtime_error("component compiled zero conditional mass");
   }
  }
 };
 std::array<Model,2>cache;
 U calls=0,rebuilds=0,changes=0,guarded_calls=0,component_draws=0,max_component_objects=0;
 template<class EngineType,class GraphType>
 std::pair<bool,bool> step(EngineType&e,GraphType&g,int axis,const std::vector<int>&objects) {
  if(objects.size()<=4)return {false,false};
  ++calls;
  std::vector<Record>records;std::vector<int>old;std::vector<I>strengths;
  struct Carried {Record label;int owner;};std::vector<Carried>carried;
  for(int owner=0;owner<int(objects.size());++owner){const int v=axis?g.nr+objects[size_t(owner)]:objects[size_t(owner)];
   strengths.push_back(g.target_strength[size_t(v)]);
   if(g.adj[size_t(v)].size()!=2)throw std::runtime_error("component object degree");
   for(int id:g.adj[size_t(v)]){const auto edge=g.edges[size_t(id)];carried.push_back({{axis?edge.r:edge.c,edge.w},owner});}
  }
  std::sort(carried.begin(),carried.end(),[](const Carried&a,const Carried&b){return a.label.node<b.label.node;});
  for(const auto&entry:carried){if(!records.empty()&&records.back().node==entry.label.node)throw std::runtime_error("component repeated local actor");records.push_back(entry.label);old.push_back(entry.owner);}
  auto&model=cache[size_t(axis)];
  if(!model.ready||model.labels!=records||model.strengths!=strengths){model.compile(records,strengths);++rebuilds;}
  if(model.guarded){++guarded_calls;return {false,false};}  
  std::vector<int>chosen=old;
  for(const auto&component:model.components){max_component_objects=std::max(max_component_objects,U(component.owners.size()));if(component.guarded){++guarded_calls;continue;}component.draw(e,chosen);++component_draws;}
  if(chosen==old)return {true,false};
  const U before=U(g.edges.size());
  auto put=[&](size_t i,int owner,I weight){if(axis)g.set_raw(records[i].node,objects[size_t(owner)],weight);else g.set_raw(objects[size_t(owner)],records[i].node,weight);};
  for(size_t i=0;i<records.size();++i)if(chosen[i]!=old[i])put(i,old[i],0);
  for(size_t i=0;i<records.size();++i)if(chosen[i]!=old[i])put(i,chosen[i],records[i].weight);
  if(g.D||U(g.edges.size())!=before)throw std::runtime_error("component update did not close");
  ++changes;++e.stat.changed_outer;return {true,true};
 }
 void metadata(std::ostream&f)const {
  f<<"\"CC_calls\":"<<calls<<",\"CC_rebuilds\":"<<rebuilds<<",\"CC_changes\":"<<changes<<",\"CC_guarded_calls\":"<<guarded_calls<<",\"CC_component_draws\":"<<component_draws<<",\"CC_max_component_objects\":"<<max_component_objects<<',';
 }
};
