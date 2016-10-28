Require Import PointContinuousFunction.
Require Import QArith.QArith_base.
Require Import Sequence.
Require Import Psatz.

Definition fex1 (x:Q) := x.
Definition rex1       := 0.

Lemma fex1_works : forall x y, x==y -> fex1 x == fex1 y.
Proof.
intros.
unfold fex1.
auto.
Qed.


Lemma ex1 : PointContinuousFunction.
Proof.
  apply Build_PointContinuousFunction with (PContinf := fex1) (PContinr := rex1).
  unfold PointContinuousFunction_def.
  intros.

  remember (fun (q:Q) => q) as qseqa.


  exists (Seqa seq).

  unfold ConvergentSequence_def.


  intros.
  
  unfold fex1.

  assert( rex1 == Seqr seq ) by lra.

  rewrite H1.

  assert (H2 := Seq_spec seq).

  unfold ConvergentSequence_def in H2.

  assert (H3 := H2 q).
  assert (H4 := H3 H0).
  apply H4.


 Qed.