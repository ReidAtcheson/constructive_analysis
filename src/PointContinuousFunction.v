Require Import Coq.QArith.QArith_base.
Require Import Coq.QArith.Qabs.
Require Import Psatz.
Require Import Sequence.




Definition PointContinuousFunction_def f r :=  forall (seq:ConvergentSequence),
    Seqr seq == r ->
    exists qseq, forall q,
        (Seq qseq) q == (f ((Seq seq) q)) /\
        (Seqr qseq) == (f (Seqr seq)).


Record PointContinuousFunction :=
  {
    PContinf : Q -> Q;
    PContinr : Q;
    PContin_spec : PointContinuousFunction_def PContinf PContinr;
}.
