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


Lemma ex1 :
  forall seq seqr seqa (Hc: ConvergentSequence seq seqr seqa),
  PointContinuousFunction Hc fex1 rex1.
Proof.
  intros.
  unfold PointContinuousFunction.
  intros.
  remember (fun n => fex1 (seq n) ) as qseq.
  exists qseq.
  remember (fex1 seqr) as qr.
  exists qr.
  remember (fun n => (seqa n)) as qa.
  exists qa.
  split.
  + unfold ConvergentSequence.
    intros.
    subst.
    unfold ConvergentSequence in Hc.
    unfold fex1.
    assert( Hcn := Hc q).
    apply Hcn.
    apply H0.
  + split.
    *subst.
     lra. 
    *subst.
     auto using fex1_works.
Qed.