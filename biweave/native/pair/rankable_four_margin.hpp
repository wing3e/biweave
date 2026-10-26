#pragma once
#include <algorithm>
#include <array>
#include <chrono>
#include <cstdint>
#include <fstream>
#include <iostream>
#include <limits>
#include <memory_resource>
#include <random>
#include <stdexcept>
#include <string>
#include <sys/mman.h>
#include <sys/resource.h>
#include <time.h>
#include <unordered_map>
#include <vector>

namespace rankable_four_margin {
 
constexpr size_t CELLS=20, ARENA_BYTES=64ull*1024*1024;
constexpr uint64_t WORK_CAP=0x1312d00;
struct ResourceFailure:std::runtime_error {using std::runtime_error::runtime_error;};
struct Arena:std::pmr::memory_resource {
    void* base; size_t used=0, peak=0;
    Arena(){base=mmap(nullptr,ARENA_BYTES,PROT_READ|PROT_WRITE,MAP_PRIVATE|MAP_ANONYMOUS,-1,0);if(base==MAP_FAILED)throw ResourceFailure("arena_mmap_failed");}
    ~Arena(){munmap(base,ARENA_BYTES);}
    void* do_allocate(size_t n,size_t align) override {size_t pos=(used+align-1)&~(align-1);if(pos>ARENA_BYTES||n>ARENA_BYTES-pos)throw ResourceFailure("arena_64MiB_exceeded");used=pos+n;peak=std::max(peak,used);return static_cast<char*>(base)+pos;}
    void do_deallocate(void*,size_t,size_t)override{}
    bool do_is_equal(const std::pmr::memory_resource& o)const noexcept override{return this==&o;}
};

struct Big {
    std::array<uint64_t,8> a{}; unsigned used=0;
    Big(uint64_t x=0){a[0]=x;used=x?1:0;}
    void trim(){while(used&&!a[used-1])--used;}
    int compare(const Big&b)const{if(used!=b.used)return used<b.used?-1:1;for(unsigned i=used;i-->0;)if(a[i]!=b.a[i])return a[i]<b.a[i]?-1:1;return 0;}
    bool operator==(const Big&b)const{return compare(b)==0;}
    bool operator<(const Big&b)const{return compare(b)<0;}
    bool operator<=(const Big&b)const{return compare(b)<=0;}
    bool operator>=(const Big&b)const{return compare(b)>=0;}
    bool operator>(const Big&b)const{return compare(b)>0;}
    Big&operator+=(const Big&b){unsigned n=std::max(used,b.used);__uint128_t carry=0;for(unsigned i=0;i<n;++i){__uint128_t z=(__uint128_t)a[i]+b.a[i]+carry;a[i]=(uint64_t)z;carry=z>>64;}used=n;if(carry){if(used==8)throw std::runtime_error("proved_integer_bound_violation");a[used++]=(uint64_t)carry;}return *this;}
    Big&operator-=(const Big&b){if(*this<b)throw std::runtime_error("negative_count");uint64_t borrow=0;for(unsigned i=0;i<used;++i){__uint128_t sub=(__uint128_t)b.a[i]+borrow;uint64_t next=(__uint128_t)a[i]<sub;a[i]-=(uint64_t)sub;borrow=next;}trim();return *this;}
    Big operator-(const Big&b)const{Big z=*this;z-=b;return z;}
    unsigned bits()const{return used?64*(used-1)+(64-__builtin_clzll(a[used-1])):0;}
    uint64_t low()const{if(used>1)throw std::runtime_error("count_not_uint64");return a[0];}
    std::string str()const{if(!used)return "0";Big x=*this;std::string out;while(x.used){__uint128_t rem=0;for(unsigned i=x.used;i-->0;){__uint128_t z=(rem<<64)|x.a[i];x.a[i]=(uint64_t)(z/10);rem=z%10;}out.push_back(char('0'+rem));x.trim();}std::reverse(out.begin(),out.end());return out;}
};
std::ostream&operator<<(std::ostream&o,const Big&b){return o<<b.str();}
double cpu(){timespec t{};clock_gettime(CLOCK_PROCESS_CPUTIME_ID,&t);return t.tv_sec+1e-9*t.tv_nsec;}
uint64_t sat_choose(uint64_t n,unsigned k,uint64_t cap){if(k>n)return 0;k=std::min<uint64_t>(k,n-k);__uint128_t z=1;for(unsigned i=1;i<=k;++i){z=z*(n-k+i)/i;if(z>cap)return cap+1;}return static_cast<uint64_t>(z);}
uint64_t add_checked(uint64_t a,uint64_t b){if(b>UINT64_MAX-a)throw ResourceFailure("integer_strength_sum_overflow");return a+b;}
struct Row {std::array<uint64_t,CELLS> w{};};
struct Key {
    std::array<uint64_t,CELLS> s{};
    std::array<uint8_t,CELLS> d{};
    uint8_t i=0;
    bool operator==(const Key&b)const{return i==b.i&&s==b.s&&d==b.d;}
};
struct Hash {size_t operator()(const Key& k)const{uint64_t h=k.i+0x9e3779b97f4a7c15ull;for(unsigned j=0;j<CELLS;++j){h^=k.s[j]+0x9e3779b97f4a7c15ull+(h<<6)+(h>>2);h^=uint64_t(k.d[j])+0x517cc1b727220a95ull+(h<<6)+(h>>2);}return h;}};
struct Node;
struct Branch {uint32_t row_index=0;Big cumulative;const Node* child=nullptr;};
struct Node {Big count;std::pmr::vector<Branch> branches;explicit Node(Arena&a):branches(&a){};Node(Node&&)=default;Node&operator=(Node&&)=default;};
struct Compiler {
    int n=0,m=0,original_n=0,original_m=0;bool transposed=false;std::array<int,CELLS> row_label{};uint64_t raw_row_upper_score=0,raw_column_upper_score=0;std::array<uint8_t,CELLS> rd{},cd{};
    std::array<uint64_t,CELLS> rs{},cs{},suffix_s{},suffix_d{};
    std::array<uint64_t,CELLS> row_upper{};
    Arena& arena;
    std::pmr::vector<std::pmr::vector<Row>> opts;
    std::pmr::unordered_map<Key,Node,Hash> memo;
    const Node* root=nullptr;uint64_t positive_branches=0,max_node_branches=0;
    uint64_t work=0,memo_hits=0,row_candidates=0,row_upper_total=0;
    Big total=0;
    Compiler(Arena&a):arena(a),opts(&a),memo(&a){}
    void tick(){if(++work>WORK_CAP)throw ResourceFailure("fixed_20million_work_cap_exceeded");}
    void read(const std::string&path){std::ifstream f(path);if(!(f>>n>>m)||n<=0||m<=0)throw std::runtime_error("bad_shape");original_n=n;original_m=m;if(uint64_t(n)*m>CELLS)throw ResourceFailure("more_than_20_cells");std::array<uint64_t,CELLS> seen{};int i,j;uint64_t w;while(f>>i>>j>>w){if(i<0||i>=n||j<0||j>=m||!w||seen[i*m+j])throw std::runtime_error("bad_or_duplicate_edge");seen[i*m+j]=w;rd[i]++;cd[j]++;rs[i]=add_checked(rs[i],w);cs[j]=add_checked(cs[j],w);}if(!f.eof())throw std::runtime_error("bad_edge_record");for(int i=n-1;i>=0;--i){suffix_s[i]=add_checked(rs[i],i+1<n?suffix_s[i+1]:0);suffix_d[i]=rd[i]+(i+1<n?suffix_d[i+1]:0);}}
    uint64_t row_bound(int width,int d,uint64_t strength)const{uint64_t cap=ARENA_BYTES/sizeof(Row);uint64_t a=sat_choose(width,d,cap),b=d?(strength>=uint64_t(d)?sat_choose(strength-1,d-1,cap):0):1;if(a>cap||b>cap||(a&&b>cap/a))return cap+1;return a*b;}
    uint64_t axis_score(bool column)const{uint64_t cap=ARENA_BYTES/sizeof(Row),z=0;int height=column?m:n,width=column?n:m;for(int i=0;i<height;++i){uint64_t b=row_bound(width,column?cd[i]:rd[i],column?cs[i]:rs[i]);if(b>cap-z)return cap+1;z+=b;}return z;}
    void choose_direction(){raw_row_upper_score=axis_score(false);raw_column_upper_score=axis_score(true);transposed=raw_column_upper_score<raw_row_upper_score;if(transposed){std::swap(n,m);std::swap(rd,cd);std::swap(rs,cs);}std::array<int,CELLS> order{};for(int i=0;i<n;++i)order[i]=i;std::sort(order.begin(),order.begin()+n,[&](int a,int b){uint64_t x=row_bound(m,rd[a],rs[a]),y=row_bound(m,rd[b],rs[b]);return x<y||(x==y&&a<b);});auto oldd=rd;auto olds=rs;for(int i=0;i<n;++i){row_label[i]=order[i];rd[i]=oldd[order[i]];rs[i]=olds[order[i]];}suffix_s.fill(0);suffix_d.fill(0);for(int i=n-1;i>=0;--i){suffix_s[i]=add_checked(rs[i],i+1<n?suffix_s[i+1]:0);suffix_d[i]=rd[i]+(i+1<n?suffix_d[i+1]:0);}}
    void precheck(){uint64_t maxrows=ARENA_BYTES/sizeof(Row);for(int i=0;i<n;++i){uint64_t a=sat_choose(m,rd[i],maxrows),b=0;if(rd[i]==0){if(rs[i])throw std::runtime_error("bad_zero_row");b=1;}else if(rs[i]>=rd[i])b=sat_choose(rs[i]-1,rd[i]-1,maxrows);if(a>maxrows||b>maxrows||(a&&(b>maxrows/a)))throw ResourceFailure("row_candidate_upper_bound_exceeds_64MiB");row_upper[i]=a*b;if(row_upper[i]>maxrows-row_upper_total)throw ResourceFailure("all_row_candidate_upper_bounds_exceed_64MiB");row_upper_total+=row_upper[i];}}
    void gen(int i,int j,int left_d,uint64_t left_s,Row&r){tick();if(left_d<0||left_d>m-j||left_s<uint64_t(left_d))return;if(j==m){if(!left_d&&!left_s){opts[i].push_back(r);++row_candidates;}return;}if(left_d==0){if(left_s)return;for(int k=j;k<m;++k)r.w[k]=0;opts[i].push_back(r);++row_candidates;return;}r.w[j]=0;if(m-j>left_d)gen(i,j+1,left_d,left_s,r);uint64_t mx=std::min(cs[j],left_s-uint64_t(left_d-1));uint64_t first=left_d==1?left_s:1;for(uint64_t w=first;w<=mx;++w){r.w[j]=w;gen(i,j+1,left_d-1,left_s-w,r);if(w==UINT64_MAX)break;}r.w[j]=0;}
    bool feasible(const Key&k)const{if(k.i>=n)return false;uint64_t sd=0,ss=0;for(int j=0;j<m;++j){if(k.d[j]>n-k.i||k.s[j]<k.d[j]||bool(k.d[j])!=bool(k.s[j]))return false;sd+=k.d[j];ss=add_checked(ss,k.s[j]);}return sd==suffix_d[k.i]&&ss==suffix_s[k.i];}
    bool subtract(const Key&k,const Row&r,Key&next)const{next=k;next.i++;for(int j=0;j<m;++j){if(r.w[j]){if(!next.d[j]||next.s[j]<r.w[j])return false;next.d[j]--;next.s[j]-=r.w[j];}}return true;}
    const Node* count(const Key&k){tick();if(k.i==n)return nullptr;if(!feasible(k))return nullptr;auto it=memo.find(k);if(it!=memo.end()){++memo_hits;return &it->second;}Node node(arena);if(k.i==n-1){int degree=0;uint64_t strength=0;bool ok=true;for(int j=0;j<m;++j){if(k.d[j]>1)ok=false;degree+=bool(k.s[j]);strength=add_checked(strength,k.s[j]);}if(ok&&degree==rd[k.i]&&strength==rs[k.i])node.count=1;}else{for(uint32_t row_id=0;row_id<opts[k.i].size();++row_id){tick();Key next;if(!subtract(k,opts[k.i][row_id],next))continue;const Node*child=count(next);if(child&&child->count>0){node.count+=child->count;node.branches.push_back(Branch{row_id,node.count,child});++positive_branches;}}}max_node_branches=std::max<uint64_t>(max_node_branches,node.branches.size());auto result=memo.emplace(k,std::move(node));return &result.first->second;}
    Key initial()const{Key k;for(int j=0;j<m;++j){k.d[j]=cd[j];k.s[j]=cs[j];}return k;}
    void compile(){choose_direction();precheck();opts.reserve(n);for(int i=0;i<n;++i){opts.emplace_back();opts.back().reserve(row_upper[i]);Row r;gen(i,0,rd[i],rs[i],r);}memo.reserve(4096);root=count(initial());total=root?root->count:Big(0);if(total==0)throw std::runtime_error("observed_table_missing_from_fiber");}
    std::array<uint64_t,CELLS> unrank(Big rank)const{if(rank>=total)throw std::runtime_error("rank_outside_fiber");std::array<uint64_t,CELLS>x{};Key k=initial();const Node* node=root;while(k.i<n){if(k.i==n-1){for(int j=0;j<m;++j)x[k.i*m+j]=k.s[j];break;}size_t lo=0,hi=node->branches.size();while(lo<hi){size_t mid=(lo+hi)/2;if(rank<node->branches[mid].cumulative)hi=mid;else lo=mid+1;}if(lo==node->branches.size())throw std::runtime_error("unrank_missing_subtree");const Branch&b=node->branches[lo];if(lo)rank-=node->branches[lo-1].cumulative;const Row&r=opts[k.i][b.row_index];for(int j=0;j<m;++j)x[k.i*m+j]=r.w[j];Key next;if(!subtract(k,r,next))throw std::runtime_error("unrank_bad_edge");k=next;node=b.child;}std::array<uint64_t,CELLS> labeled{};for(int i=0;i<n;++i)for(int j=0;j<m;++j){if(transposed)labeled[j*original_m+row_label[i]]=x[i*m+j];else labeled[row_label[i]*original_m+j]=x[i*m+j];}return labeled;}

};
Big uniform_below(const Big& bound,std::mt19937_64&rng){if(bound<=1)return Big(0);Big top=bound-1;unsigned bits=top.bits();for(;;){Big x; x.used=(bits+63)/64;for(unsigned i=0;i<x.used;++i)x.a[i]=rng();unsigned part=bits%64;if(part)x.a[x.used-1]&=(uint64_t(1)<<part)-1;x.trim();if(x<bound)return x;}}

}  
