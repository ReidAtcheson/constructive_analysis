Require Import Coq.QArith.QArith_base.
Require Import Coq.QArith.Qabs.
Require Import Psatz.
Require Import Sequence.
Require Import PointContinuousFunction.
Require Import ContinuousFunction.



Definition fex1 (x:Q) := x.
Definition wex1 (x:Q) := x.


Lemma wex1_is_pcontin : (PointContinuousFunction_def wex1 0).
Proof.
  unfold PointContinuousFunction_def.
  intros.

  exists (Seqa seq).

  unfold wex1.
  unfold ConvergentSequence_def.
  intros.

  assert( 0 == Seqr seq ) by lra.
  rewrite H1.

  assert( H2 := Seq_spec seq).
  unfold ConvergentSequence_def in H2.
  assert( H3 := H2 q H0 ).
  apply H3.

Qed.




Definition ex1 : ContinuousFunction.
Proof.
  apply Build_ContinuousFunction with (Continf := fex1) (Continw := wex1).
  unfold ContinuousFunction_def.
  split.
  {
    apply wex1_is_pcontin.
  }
  split.
  {
    unfold IncreasingFunction_def.
    unfold wex1.
    intros.
    lra.
  }

  intros.
  split.
  {
    unfold wex1.
    apply H.
  }

  intros.
  unfold fex1.
  unfold wex1.
  lra.
  
Qed.



