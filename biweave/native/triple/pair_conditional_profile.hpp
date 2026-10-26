#pragma once

struct PairConditionalProfileGibbs {
 using Count = std::uint64_t;
 struct PairLaw { Count L=0,U=0,T=0,hi=0,hj=0; mpz_class initial=1,total=1; };
 Count sweeps=0,profile_hold_calls=0,pair_calls=0,nontrivial_pairs=0,singleton_holds=0,pair_changes=0,sweep_changes=0;
 Count width_span_total=0,max_width_span=0,mass_states_total=0,startup_multiplications=0,recurrence_steps=0,recurrence_divisions=0;
 Count max_mass_bits=0,max_total_bits=0,label_changed_windows=0,changed_windows=0,moved_labels=0,root_writes=0,cell_writes=0;
 double count_cpu_seconds=0,rank_cpu_seconds=0,label_cpu_seconds=0,commit_cpu_seconds=0;
 static Count bits(const mpz_class&x){return x==0?0:Count(mpz_sizeinbase(x.get_mpz_t(),2));}
 static void advance(mpz_class&mass,Count hi,Count hj,Count T,Count z){
   
  const Count d0=z+1,d1=hj-(T-z)+1;
  if(!d0||!d1||!mpz_divisible_ui_p(mass.get_mpz_t(),static_cast<unsigned long>(d0)))throw std::runtime_error("pair conditional first exact division");
  mass/=d0;
  if(!mpz_divisible_ui_p(mass.get_mpz_t(),static_cast<unsigned long>(d1)))throw std::runtime_error("pair conditional second exact division");
  mass/=d1;mass*=hi-z;mass*=T-z;
  if(mass<=0)throw std::runtime_error("pair conditional nonpositive mass");
 }
 PairLaw build(Count hi,Count hj,Count T,Count ci,Count cj,bool profile=false){
  if(hi>std::numeric_limits<Count>::max()-hj||ci>hi||cj>hj||T>ci+cj)throw std::runtime_error("pair conditional infeasible capacities");
  PairLaw p;p.hi=hi;p.hj=hj;p.T=T;p.L=T>cj?T-cj:0;p.U=std::min(ci,T);
  if(p.L>p.U||p.L>hi||T-p.L>hj)throw std::runtime_error("pair conditional empty legal interval");
  const Count span=p.U-p.L;width_span_total+=span;max_width_span=std::max(max_width_span,span);mass_states_total+=span+1;
  if(!span){++singleton_holds;max_mass_bits=std::max<Count>(max_mass_bits,1);max_total_bits=std::max<Count>(max_total_bits,1);return p;}
  ++nontrivial_pairs;
  const double start=profile?process_cpu():0;
  for(Count z=p.L;z<p.U;++z){p.initial*=z+1;p.initial*=hj-(T-z)+1;startup_multiplications+=2;}
  p.total=p.initial;mpz_class mass=p.initial;max_mass_bits=std::max(max_mass_bits,bits(mass));
  for(Count z=p.L;z<p.U;++z){advance(mass,hi,hj,T,z);++recurrence_steps;recurrence_divisions+=2;p.total+=mass;max_mass_bits=std::max(max_mass_bits,bits(mass));}
  max_total_bits=std::max(max_total_bits,bits(p.total));if(profile)count_cpu_seconds+=process_cpu()-start;return p;
 }
 static Count unrank(const PairLaw&p,mpz_class rank){
  if(rank<0||rank>=p.total)throw std::runtime_error("pair conditional rank outside mass");
  mpz_class mass=p.initial;
  for(Count z=p.L;;++z){if(rank<mass)return z;rank-=mass;if(z==p.U)break;advance(mass,p.hi,p.hj,p.T,z);}
  throw std::runtime_error("pair conditional rank lost");
 }
 template<class Picker>std::array<Count,3> draw(const std::array<Count,3>&h,const std::array<Count,3>&c,const std::array<Count,3>&initial,Picker&&pick,bool hold=false,bool profile=false){
  for(int i=0;i<3;++i)if(c[i]>h[i]||initial[i]>c[i])throw std::runtime_error("pair conditional invalid initial profile");
  if(h[0]>std::numeric_limits<Count>::max()-h[1]||h[0]+h[1]>std::numeric_limits<Count>::max()-h[2])throw std::runtime_error("pair conditional total quota overflow");
  if(hold){++profile_hold_calls;return initial;}
  ++sweeps;auto a=initial;static constexpr int pairs[3][2]={{0,1},{1,2},{0,2}};
  for(const auto&ij:pairs){const int i=ij[0],j=ij[1];++pair_calls;const Count T=a[i]+a[j];const auto law=build(h[i],h[j],T,c[i],c[j],profile);if(law.L==law.U)continue;
   const double start=profile?process_cpu():0;const Count z=unrank(law,pick(law.total));if(profile)rank_cpu_seconds+=process_cpu()-start;pair_changes+=z!=a[i];a[i]=z;a[j]=T-z;
  }
  sweep_changes+=a!=initial;return a;
 }
 void metadata(std::ostream&f)const{
  f<<"\"PG_sweeps\":"<<sweeps<<",\"PG_profile_hold_calls\":"<<profile_hold_calls<<",\"PG_pair_calls\":"<<pair_calls<<",\"PG_nontrivial_pairs\":"<<nontrivial_pairs<<",\"PG_singleton_holds\":"<<singleton_holds<<",\"PG_pair_changes\":"<<pair_changes<<",\"PG_sweep_changes\":"<<sweep_changes<<",\"PG_width_span_total\":"<<width_span_total<<",\"PG_max_width_span\":"<<max_width_span<<",\"PG_mass_states_total\":"<<mass_states_total<<",\"PG_startup_multiplications\":"<<startup_multiplications<<",\"PG_recurrence_steps\":"<<recurrence_steps<<",\"PG_recurrence_divisions\":"<<recurrence_divisions<<",\"PG_max_mass_bits\":"<<max_mass_bits<<",\"PG_max_total_bits\":"<<max_total_bits<<",\"PG_label_changed_windows\":"<<label_changed_windows<<",\"PG_changed_windows\":"<<changed_windows<<",\"PG_moved_labels\":"<<moved_labels<<",\"PG_root_writes\":"<<root_writes<<",\"PG_cell_writes\":"<<cell_writes<<",\"PG_count_cpu_seconds\":"<<count_cpu_seconds<<",\"PG_rank_cpu_seconds\":"<<rank_cpu_seconds<<",\"PG_label_cpu_seconds\":"<<label_cpu_seconds<<",\"PG_commit_cpu_seconds\":"<<commit_cpu_seconds<<",";
 }
};
