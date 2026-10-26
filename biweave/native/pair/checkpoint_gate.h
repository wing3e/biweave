#pragma once
#include <stdint.h>
#include <stdlib.h>
#include <unistd.h>
#include <errno.h>
 
static void checkpoint_gate(uint64_t iteration) {
 static int initialized=0,fd=-1;
 static uint64_t next=0;
 if(!initialized){
  const char* f=getenv("WWW_CONVERGENCE_GATE_FD");
  const char* n=getenv("WWW_CONVERGENCE_FIRST_GATE");
  if(f&&n){fd=atoi(f);next=strtoull(n,0,10);}
  initialized=1;
 }
 if(fd<0||!next||iteration<next)return;
 uint64_t command=0;size_t have=0;
 while(have<sizeof(command)){
  ssize_t got=read(fd,((char*)&command)+have,sizeof(command)-have);
  if(got<0&&errno==EINTR)continue;
  if(got<=0)_exit(71);  
  have+=(size_t)got;
 }
 if(command==0)_exit(0);  
 if(command<=iteration)_exit(72);
 next=command;
}

static int checkpoint_should_emit(uint64_t iteration,uint64_t stride){
 static int initialized=0,count=0,index=0;
 static uint64_t low[128],high[128];
 if(!iteration)return 1;
 if(!initialized){
  const char* spec=getenv("WWW_CONVERGENCE_OBSERVATION_WINDOWS");
  if(!spec||!*spec)return 1;
  const char* ptr=spec;
  while(*ptr){
   if(count>=128)_exit(73);
   char* end=0;low[count]=strtoull(ptr,&end,10);if(*end!=':')_exit(73);
   high[count]=strtoull(end+1,&end,10);if(high[count]<low[count])_exit(73);
   count++;if(!*end)break;if(*end!=',')_exit(73);ptr=end+1;
  }
  initialized=1;
 }
 uint64_t k=iteration/stride;
 while(index<count&&k>high[index])index++;
 return index<count&&k>=low[index]&&k<=high[index];
}
