#pragma once

struct SoftDefectCoverage {
 int mode=0, power=0,hazard_rule=0;bool extra_lazy=true;GuidedDefectAnchors guide;U original_E=0;
 bool priority_requested=false,priority_start_S=false;std::function<bool(const Graph&)>priority_endpoint;
 U priority_calls=0,priority_start_S_calls=0,priority_endpoint_checks=0,priority_S_to_outside=0,priority_endpoint_rejected=0,priority_endpoint_accepted=0;
 EndpointRectangleAudit endpoint_audit;U endpoint_mix_calls=0,endpoint_mix_full_calls=0,endpoint_mix_endpoint_calls=0;
 U calls=0, lazy=0, inner=0, proposed=0, accepted_inner=0,rejected_inner=0;
 U departed=0, returns=0, changed=0, changed_multistep=0,timeouts=0,cap_aborts=0;
 U max_defect=0, max_steps=0, undo_rectangles=0;
 double cpu=0;
 bool stop(Engine&e,U step)const{
  if(!hazard_rule)return e.rng.below(U(e.opt.rho_den))==0;
  if(hazard_rule!=1||step>std::numeric_limits<U>::max()-2*U(e.opt.rho_den))throw std::runtime_error("coverage heavy hazard overflow");
  return e.rng.below(2*U(e.opt.rho_den)+step)<3;
 }
 void legacy_tail(Engine&e,Graph&g){
  if(g.D||e.opt.kappa||e.opt.anchor_mode!="dual"||e.opt.cycle_mix!=0)throw std::runtime_error("legacy tail configuration");
  e.coverage_cap.begin(g);const U h1=g.hash1,h2=g.hash2;const I m0=I(g.edges.size());const std::string tiny=g.flat();
  if(extra_lazy&&e.rng.below(2)==0){++e.stat.work;++e.stat.lazy;++lazy;return;}
  std::vector<Undo>undo;long double logratio=0;Big exact_num=1,exact_den=1;U steps=0;bool left=false;
  auto rollback=[&](){const U before=e.stat.rollback_rectangles;e.rollback(g,undo,h1,h2,m0,tiny);if((mode==6||mode==7||mode==8))guide.reset_after_verified_rollback(g);undo_rectangles+=e.stat.rollback_rectangles-before;};
  auto finish=[&](){max_steps=std::max(max_steps,steps);e.stat.max_path=std::max(e.stat.max_path,steps);};
  for(;;){
   ++steps;++inner;++e.stat.work;++e.stat.inner;Rectangle r{};
   if(((mode==6||mode==7||mode==8)?guide.draw_rectangle(e,g,r):e.rectangle(g,0,r,true))){
    ++e.stat.rectangles;const auto old=g.cells(r);const auto interval=Engine::interval(old);
    const U old_h=g.Hproduct(r,0),old_n=Engine::class_size(interval.first,interval.second,0);
    const I delta=e.stratified(interval.first,interval.second);const U new_n=Engine::class_size(interval.first,interval.second,delta);
    if(e.coverage_cap.requested&&!e.coverage_cap.allows(g,old,delta)){
     ++cap_aborts;CoverageSupportCap::increment(e.coverage_cap.capacity_aborts);e.coverage_cap.max_abort_steps=std::max(e.coverage_cap.max_abort_steps,steps);
     const U before=e.stat.rollback_rectangles;rollback();e.coverage_cap.rollback_rectangles+=e.stat.rollback_rectangles-before;finish();return;
    }
    if(delta){++proposed;undo.push_back({r,delta});g.apply(r,delta);++accepted_inner;}else ++e.stat.zero_delta;
    if(e.coverage_cap.requested)e.coverage_cap.max_complete_support=std::max(e.coverage_cap.max_complete_support,U(g.edges.size()));
    const U new_h=g.Hproduct(r,0);if(!old_h||!new_h||!old_n||!new_n)throw std::runtime_error("tail reversal factors");
    if(new_h!=old_h)logratio+=logl((long double)new_h)-logl((long double)old_h);
    if(new_n!=old_n)logratio+=logl((long double)new_n)-logl((long double)old_n);
    exact_num*=new_h;exact_num*=new_n;exact_den*=old_h;exact_den*=old_n;
   }
   max_defect=std::max(max_defect,U(g.D));
   if(g.D==0){
    if((mode==6||mode==7||mode==8))guide.check_sparse(g);++returns;++e.stat.returned;finish();e.stat.max_abs_log_ratio=std::max(e.stat.max_abs_log_ratio,std::abs(logratio));
    const bool accept=exact_num>=exact_den||e.rng.below_big(exact_den)<exact_num;
    if(accept){++e.stat.accepted;if(g.hash1!=h1||g.hash2!=h2){++changed;++e.stat.changed_outer;++e.stat.changed_tour;e.stat.changed_tour_steps_total+=steps;e.stat.changed_tour_multistep+=steps>1;changed_multistep+=steps>1;}}
    else{++e.stat.mh_rejected;rollback();}return;
   }
   if(!left){left=true;++departed;}
   if(stop(e,steps)){++timeouts;++e.stat.timeouts;finish();rollback();return;}
  }
 }
 I mixed_endpoint_delta(Engine&e,Graph&g,Rectangle r){
  ++endpoint_mix_calls;
  if(e.rng.below(2)==0){++endpoint_mix_endpoint_calls;return draw_endpoint_soft_rectangle(e,g,r,power,&endpoint_audit);}
  ++endpoint_mix_full_calls;return draw_metropolized_soft_rectangle_fast(e,g,r,power);
 }
 void candidate(Engine&e,Graph&g){
  const double started=process_cpu(); ++calls;
  if(priority_requested){if((mode!=5&&mode!=9)||extra_lazy||hazard_rule||!priority_endpoint)throw std::runtime_error("priority wrapper configuration");++priority_calls;priority_start_S_calls+=priority_start_S;}
  if(!mode){if(!extra_lazy)throw std::runtime_error("native legacy mode requires its frozen extra lazy");if(hazard_rule)throw std::runtime_error("legacy native requires geometric hazard");
   const U a=e.stat.inner,b=e.stat.returned,c=e.stat.changed_tour,d=e.stat.timeouts,l=e.stat.lazy,m=e.stat.changed_tour_multistep;
   e.candidate(g);inner+=e.stat.inner-a;returns+=e.stat.returned-b;changed+=e.stat.changed_tour-c;timeouts+=e.stat.timeouts-d;lazy+=e.stat.lazy-l;changed_multistep+=e.stat.changed_tour_multistep-m;max_steps=e.stat.max_path;
   cpu+=process_cpu()-started;return;}
  if(mode==3){legacy_tail(e,g);cpu+=process_cpu()-started;return;}
  if((mode!=1&&mode!=2&&mode!=4&&mode!=5&&mode!=6&&mode!=7&&mode!=8&&mode!=9)||power<0||power>8||e.opt.kappa||e.opt.anchor_mode!="dual"||e.opt.coverage_weighted_column_gibbs||e.opt.cycle_mix!=0)
   throw std::runtime_error("unsupported soft-degree first-return configuration");
  if(g.D)throw std::runtime_error("soft first-return must start in F");if(mode==8){if(power)throw std::runtime_error("harmonic target has no penalty power");if(!original_E)original_E=U(g.edges.size());if(original_E!=U(g.edges.size()))throw std::runtime_error("fixed original E changed");}if((mode==6||mode==7||mode==8))guide.clear_F(g);
  e.coverage_cap.begin(g);
  const U h1=g.hash1,h2=g.hash2;const I m0=I(g.edges.size());const std::string tiny=g.flat();
  if(extra_lazy&&e.rng.below(2)==0){++e.stat.work;++e.stat.lazy;++lazy;cpu+=process_cpu()-started;return;}
  std::vector<Undo>undo; U steps=0; bool left=false;
  auto finish=[&](){max_steps=std::max(max_steps,steps);e.stat.max_path=std::max(e.stat.max_path,steps);cpu+=process_cpu()-started;};
  auto rollback=[&](){const U before=e.stat.rollback_rectangles;e.rollback(g,undo,h1,h2,m0,tiny);if((mode==6||mode==7||mode==8))guide.reset_after_verified_rollback(g);undo_rectangles+=e.stat.rollback_rectangles-before;};
  for(;;){
   ++steps;++inner;++e.stat.work;++e.stat.inner;Rectangle r{};
   if(((mode==6||mode==7||mode==8)?guide.draw_rectangle(e,g,r):e.rectangle(g,0,r,true))){
    ++e.stat.rectangles;const auto old=g.cells(r);const auto interval=Engine::interval(old);
    const U old_m=U(g.edges.size()), old_h=g.Hproduct(r,0), old_n=Engine::class_size(interval.first,interval.second,0);
    const I old_D=g.D,delta=mode==9?mixed_endpoint_delta(e,g,r):(mode==6||mode==7||mode==8)?(mode==8?draw_guided_harmonic_rectangle(e,g,r,power,original_E):(mode==7?draw_guided_heatbath_rectangle(e,g,r,power):draw_guided_soft_rectangle(e,g,r,power))):(mode==5?draw_metropolized_soft_rectangle_fast(e,g,r,power):(mode==4?draw_metropolized_soft_rectangle(e,g,r,power):(mode==2?draw_soft_rectangle(e,g,r,power):e.stratified(interval.first,interval.second))));
    const U new_n=Engine::class_size(interval.first,interval.second,delta);
    if(e.coverage_cap.requested&&!e.coverage_cap.allows(g,old,delta)){
     ++cap_aborts;CoverageSupportCap::increment(e.coverage_cap.capacity_aborts);e.coverage_cap.max_abort_steps=std::max(e.coverage_cap.max_abort_steps,steps);
     const U before=e.stat.rollback_rectangles;rollback();e.coverage_cap.rollback_rectangles+=e.stat.rollback_rectangles-before;finish();return;
    }
    if(delta){
     ++proposed;g.apply(r,delta);if((mode==6||mode==7||mode==8))guide.refresh_rectangle(g,r);
     const U new_m=U(g.edges.size()),new_h=g.Hproduct(r,0);const I new_D=g.D;
     if(!old_m||!new_m||!old_h||!new_h||!old_n||!new_n||new_D<0||old_D<0||((old_D-new_D)&1)||std::abs(old_D-new_D)>8)
      throw std::runtime_error("invalid degree-potential MH factors");
      
     bool inner_accept=true;if(mode==1){mpz_class numerator=mpz_class(new_h)*new_n*old_m*old_m;
     mpz_class denominator=mpz_class(old_h)*old_n*new_m*new_m;
     const I exponent=I(power)*(old_D-new_D)/2;
     if(exponent>0)mpz_mul_2exp(numerator.get_mpz_t(),numerator.get_mpz_t(),unsigned(exponent));
     else if(exponent<0)mpz_mul_2exp(denominator.get_mpz_t(),denominator.get_mpz_t(),unsigned(-exponent));
     inner_accept=exact_accept(e.rng,rational(numerator,denominator));}
     if(inner_accept){++accepted_inner;undo.push_back({r,delta});}
     else{++rejected_inner;g.apply(r,-delta);++e.stat.work;++e.stat.rollback_rectangles;++undo_rectangles;}
    }else ++e.stat.zero_delta;
    if(e.coverage_cap.requested)e.coverage_cap.max_complete_support=std::max(e.coverage_cap.max_complete_support,U(g.edges.size()));
   }
   max_defect=std::max(max_defect,U(g.D));
   if(g.D==0){
    if((mode==6||mode==7||mode==8))guide.check_sparse(g);++returns;++e.stat.returned;
    if(priority_requested){
     bool endpoint_accept=true;
     if(priority_start_S){++priority_endpoint_checks;const bool endpoint_S=priority_endpoint(g);
      if(!endpoint_S){++priority_S_to_outside;endpoint_accept=e.rng.below(10000)<50;}
     }
     if(!endpoint_accept){++priority_endpoint_rejected;++e.stat.mh_rejected;rollback();finish();return;}
     ++priority_endpoint_accepted;
    }
    ++e.stat.accepted;
    if(g.hash1!=h1||g.hash2!=h2){++changed;++e.stat.changed_outer;++e.stat.changed_tour;e.stat.changed_tour_steps_total+=steps;e.stat.changed_tour_multistep+=steps>1;changed_multistep+=steps>1;}
    finish();return;
   }
   if(!left){left=true;++departed;}
   if(stop(e,steps)){++timeouts;++e.stat.timeouts;rollback();finish();return;}
  }
 }
 void save(const std::string&out,const Engine&e)const{
  std::ofstream f(out+".coverage.json");f<<std::setprecision(17);
  endpoint_audit.check();if(endpoint_mix_calls!=endpoint_mix_full_calls+endpoint_mix_endpoint_calls||endpoint_mix_endpoint_calls!=endpoint_audit.calls)throw std::runtime_error("endpoint mixture accounting");
  f<<"{";endpoint_audit.metadata(f);f<<"\"endpoint_mix_calls\":"<<endpoint_mix_calls<<",\"endpoint_mix_full_calls\":"<<endpoint_mix_full_calls<<",\"endpoint_mix_endpoint_calls\":"<<endpoint_mix_endpoint_calls<<",\"endpoint_mix_probability\":"<<(mode==9?0.5:0)<<",\"priority_requested\":"<<(priority_requested?"true":"false")<<",\"priority_calls\":"<<priority_calls<<",\"priority_start_S_calls\":"<<priority_start_S_calls<<",\"priority_endpoint_checks\":"<<priority_endpoint_checks<<",\"priority_S_to_outside\":"<<priority_S_to_outside<<",\"priority_endpoint_rejected\":"<<priority_endpoint_rejected<<",\"priority_endpoint_accepted\":"<<priority_endpoint_accepted<<",\"extra_lazy_probability\":"<<(extra_lazy?0.5:0)<<",\"original_E_cached\":"<<original_E<<",\"mode\":"<<mode<<",\"degree_penalty_power\":"<<power<<",\"rho_den\":"<<e.opt.rho_den<<",\"hazard_rule\":"<<hazard_rule<<",\"calls\":"<<calls<<",\"lazy\":"<<lazy<<",\"inner\":"<<inner<<",\"proposed\":"<<proposed<<",\"accepted_inner\":"<<accepted_inner<<",\"rejected_inner\":"<<rejected_inner<<",\"departed\":"<<departed<<",\"returns\":"<<returns<<",\"changed\":"<<changed<<",\"changed_multistep\":"<<changed_multistep<<",\"timeouts\":"<<timeouts<<",\"cap_aborts\":"<<cap_aborts<<",\"max_defect\":"<<max_defect<<",\"max_steps\":"<<max_steps<<",\"undo_rectangles\":"<<undo_rectangles<<",\"coverage_CPU_seconds\":"<<cpu<<",\"four_margins_final\":"<<(e.graphs[0].D==0?"true":"false")<<"}\n";
  if(!f)throw std::runtime_error("coverage metadata write failure");
 }
};
