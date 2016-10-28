Require Import Coq.QArith.QArith_base.
Require Import Coq.QArith.Qabs.
Require Import Psatz.
Require Import Sequence.




Definition PointContinuousFunction_def (f:Q->Q) (r:Q) :=  forall (seq:ConvergentSequence),
    Seqr seq == r ->
    exists qseqa,  ConvergentSequence_def (fun q => f ((Seq seq) q)) (f r) qseqa.

Record PointContinuousFunction :=
  {
    PContinf : Q -> Q;
    PContinr : Q;
    PContin_spec : PointContinuousFunction_def PContinf PContinr;
}.
