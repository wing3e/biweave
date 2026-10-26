#ifndef MH_AUTHOR_BRIDGE_H
#define MH_AUTHOR_BRIDGE_H
#include <stdint.h>
#ifdef __cplusplus
extern "C" {
#endif
 
void *mh_create(int m,int n,const int *p,const int *q,const int *rd,const int *cd,
                const int *initial,uint64_t seed,int matrix_type,uint64_t memory_guard_bytes);
const char *mh_last_error(void);
const char *mh_strength_count(void *handle);
const int *mh_next_strength(void *handle);
int mh_joint_step(void *handle);
const int *mh_current_matrix(void *handle);
uint64_t mh_draws(void *handle);
uint64_t mh_accepted(void *handle);
uint64_t mh_changed(void *handle);
uint64_t mh_initial_array_lower_bound_bytes(void *handle);
int mh_sorted_row_label(void *handle,int index);
int mh_projection_entry(void *handle,int row1,int level);
const int *mh_last_proposal(void *handle);
#ifdef __cplusplus
}
#endif
#endif
 
