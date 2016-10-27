Require Import Coq.QArith.QArith_base.
Require Import Coq.QArith.Qabs.
Require Import Coq.QArith.Qround.
Require Import Psatz.


Definition ConvergentSequence_def
(seq : Q->Q)
(r:Q)
(a:Q->Q) 
:= (forall q, q>0 -> Qabs ((seq (a q)) + -r) <= 1/q).


Record ConvergentSequence :=
{
  Seq : Q -> Q;
  Seqr : Q;
  Seqa : Q -> Q;

  Seq_spec : (ConvergentSequence_def Seq Seqr Seqa);
}.
