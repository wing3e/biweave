

#include <stdio.h>
#include <stdlib.h>
static int bw_allocation_failure_no_retry(void) {
    fputs("EXACT_RESOURCE_MEMORY_LIMIT: noninteractive allocation failure; no retry.\n", stderr);
    fflush(stderr);
    exit(71);
}
#define getchar bw_allocation_failure_no_retry

#define MAIN
#include "../../../external/exact/code/C_version/count.c"
#include "../../../external/exact/code/C_version/sample.c"
#include "bridge.h"
#include <limits.h>
#include <stdint.h>

typedef struct {
 data_t *v; int m,n,type; int *rd,*cd,*current; int **proposal;
 char *number; uint64_t draws,accepted,changed,array_bytes;
} mh_context;
static int created=0;
static char bridge_error[512];
const char *mh_last_error(void){return bridge_error;}
static void fail(const char *s){snprintf(bridge_error,sizeof(bridge_error),"%s",s);}

void *mh_create(int m,int n,const int *p,const int *q,const int *rd,const int *cd,
                const int *initial,uint64_t seed,int matrix_type,uint64_t memory_guard_bytes){
 if(created){fail("Vendor global context: only one creation per worker process");return NULL;}
 if(m<=0||n<=0||!p||!q||!rd||!cd||!initial||(matrix_type!=0&&matrix_type!=1)){
  fail("Positive dimensions and explicit margins/initial state/type0or1 required");return NULL;}
 if(sizeof(unsigned long)<sizeof(uint64_t)){fail("Fixed uint64 seed requires LP64 unsigned long");return NULL;}
 int maxq=0;int64_t ps=0,qs=0;
 for(int i=0;i<m;++i){if(p[i]<0||rd[i]<0||rd[i]>n){fail("Invalid row margins");return NULL;}ps+=p[i];}
 for(int j=0;j<n;++j){if(q[j]<0||cd[j]<0||cd[j]>m){fail("Invalid column margins");return NULL;}qs+=q[j];if(q[j]>maxq)maxq=q[j];}
 if(ps!=qs||ps>INT_MAX||maxq>INT_MAX-2){fail("Vendor int margin arithmetic bound exceeded");return NULL;}
 uint64_t mn=(uint64_t)m*n,ml=((uint64_t)m+1)*((uint64_t)maxq+2),nn=((uint64_t)n+1)*((uint64_t)n+1);
 if(mn>INT_MAX||ml>INT_MAX||nn>INT_MAX){fail("Vendor signed-int array multiplication bound exceeded");return NULL;}
 uint64_t lower=(uint64_t)sizeof(bigint)*nn+((uint64_t)sizeof(bigint)+sizeof(int))*ml+2*sizeof(int)*mn;
 if(memory_guard_bytes && lower>memory_guard_bytes){fail("Author initial dense arrays exceed declared memory cap");return NULL;}
 for(int i=0;i<m;++i){int64_t s=0;int d=0;for(int j=0;j<n;++j){int w=initial[(size_t)i*n+j];
  if(w<0||(matrix_type==0&&w>1)){fail("Invalid initial cell");return NULL;}s+=w;d+=(w>0);}
  if(s!=p[i]||d!=rd[i]){fail("Initial row margins mismatch");return NULL;}}
 for(int j=0;j<n;++j){int64_t s=0;int d=0;for(int i=0;i<m;++i){int w=initial[(size_t)i*n+j];s+=w;d+=(w>0);}
  if(s!=q[j]||d!=cd[j]){fail("Initial column margins mismatch");return NULL;}}
 mh_context *h=calloc(1,sizeof(*h));if(!h){fail("Context allocation failed");return NULL;}
 h->m=m;h->n=n;h->type=matrix_type;h->array_bytes=lower;
 h->rd=malloc(m*sizeof(int));h->cd=malloc(n*sizeof(int));h->current=malloc(mn*sizeof(int));
 if(!h->rd||!h->cd||!h->current){fail("Wrapper allocation failed");return NULL;}
 memcpy(h->rd,rd,m*sizeof(int));memcpy(h->cd,cd,n*sizeof(int));memcpy(h->current,initial,mn*sizeof(int));
 created=1;quiet_mode=1;
  
 h->v=initialize_variables((int*)p,(int*)q,m,n,"");
 gmp_randseed_ui(random_state,(unsigned long)seed);
 bigint *number=count(h->v,matrix_type);
 if(mpz_sgn(*number)<=0){fail("Author count is zero for validated initial state");return NULL;}
 h->number=mpz_get_str(NULL,10,*number);
 allocate_matrix(int,h->proposal,m,n);
 return h;
}
const char *mh_strength_count(void *handle){return ((mh_context*)handle)->number;}
const int *mh_next_strength(void *handle){mh_context*h=handle;sample(h->proposal,h->v,h->type);++h->draws;return h->proposal[0];}
int mh_joint_step(void *handle){
 mh_context*h=handle;const int *x=mh_next_strength(h);int valid=1;
 for(int i=0;i<h->m;++i){int d=0;for(int j=0;j<h->n;++j)d+=(x[(size_t)i*h->n+j]>0);if(d!=h->rd[i])valid=0;}
 for(int j=0;j<h->n;++j){int d=0;for(int i=0;i<h->m;++i)d+=(x[(size_t)i*h->n+j]>0);if(d!=h->cd[j])valid=0;}
 if(valid){++h->accepted;size_t bytes=(size_t)h->m*h->n*sizeof(int);
  h->changed+=(memcmp(x,h->current,bytes)!=0);memcpy(h->current,x,bytes);}
 return valid;
}
const int *mh_current_matrix(void *handle){return ((mh_context*)handle)->current;}
uint64_t mh_draws(void *handle){return ((mh_context*)handle)->draws;}
uint64_t mh_accepted(void *handle){return ((mh_context*)handle)->accepted;}
uint64_t mh_changed(void *handle){return ((mh_context*)handle)->changed;}
uint64_t mh_initial_array_lower_bound_bytes(void *handle){return ((mh_context*)handle)->array_bytes;}

int mh_sorted_row_label(void *handle,int index){mh_context*h=handle;return index>=0&&index<h->m?h->v->permutation[index]:-1;}
int mh_projection_entry(void *handle,int row1,int level){mh_context*h=handle;return row1>=1&&row1<=h->m&&level>=0&&level<h->v->L?h->v->S[row1][level]:-1;}
const int *mh_last_proposal(void *handle){return ((mh_context*)handle)->proposal[0];}
