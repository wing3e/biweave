#pragma once

struct TwoWeightSingleProposal {
 U calls=0,legal=0,invalid=0,objects_total=0,max_objects=0;
 double draw_cpu_seconds=0;
 template<class Solver>bool draw(const TwoWeightComplement::Problem&p,Solver&solver,RNG&rng,TwoWeightComplement::Draw&d){
  ++calls;const double start=process_cpu();
  TypedLocalCompiler::EqualProblem labels;labels.scene=p.scene;labels.quota=p.h;
  labels.columns=p.high_columns;labels.columns.insert(labels.columns.end(),p.low_columns.begin(),p.low_columns.end());
  const U q=labels.columns.size();objects_total+=q;max_objects=std::max(max_objects,q);
  if(q!=p.NH+p.NL||p.h[0]+p.h[1]+p.h[2]!=q)throw std::runtime_error("wide proposal total quota");
  const auto owners=solver.draw_equal(labels,[&](U count){return rng.below(count);});
  d.a={0,0,0};d.high_owners.assign(owners.begin(),owners.begin()+p.NH);d.low_owners.assign(owners.begin()+p.NH,owners.end());
  for(int owner:d.high_owners){if(owner<0||owner>2)throw std::runtime_error("wide proposal owner");++d.a[owner];}
  bool positive=true;for(int i=0;i<3;++i){const S128 root=S128(p.beta[i])-S128(p.low)*p.h[i]-S128(p.delta)*d.a[i];
   if(root>std::numeric_limits<I>::max())throw std::runtime_error("wide proposal root overflow");
   if(root<=0)positive=false;d.roots[i]=root>0?I(root):0;
  }
  draw_cpu_seconds+=process_cpu()-start;if(positive)++legal;else ++invalid;return positive;
 }
 void metadata(std::ostream&f)const{
  f<<"\"WCP_calls\":"<<calls<<",\"WCP_legal\":"<<legal<<",\"WCP_invalid\":"<<invalid<<",\"WCP_objects_total\":"<<objects_total<<",\"WCP_max_objects\":"<<max_objects<<",\"WCP_draw_cpu_seconds\":"<<draw_cpu_seconds<<",";
 }
};
