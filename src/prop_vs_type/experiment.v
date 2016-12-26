Require Import Coq.QArith.QArith_base.
Require Import Coq.QArith.Qabs.
Require Import Coq.QArith.Qround.
Require Import Psatz.

Definition ConvergentSequence 
(xs : positive -> Q) (x : Q) :=
forall eps, eps>0 -> 
exists (N : positive), forall (n : positive),
(n>N)%positive -> Qabs ( (xs n) + -x ) <= eps.


Definition xs n := 1#n.


Lemma weak_archimedean :
  forall z, (z>0)%Z -> (z>=1)%Z.
Proof.
  intros.
  auto with *.
Qed.

Lemma Zpos_implies_Zge1 :
  forall a b, (a>0 -> b>=1 -> a <= b*a)%Z.
Proof.
intros.
nia.
Qed.

Lemma smaller_unit_frac : 
forall eps, eps>0 ->
1 # (Qden eps) <= eps.
Proof.
intros.
unfold Qle.
unfold Qlt in H.
simpl in H.
simpl.
assert ( (Qnum eps * 1 = Qnum eps)%Z ) by ring.
rewrite H0 in H.
assert ( (Qnum eps >=1)%Z ).
{
  auto using weak_archimedean with *.
}
auto using Zpos_implies_Zge1 with *.
Qed.

Lemma ex1_works : ConvergentSequence xs 0.
Proof.
unfold ConvergentSequence.
intros.
remember (Qden eps) as N.
exists N.
intros.
assert( xs n + -0 == xs n ) by ring.
rewrite H1.
unfold xs.
assert( 1#n >= 0 ).
{
  unfold Qlt.
  simpl.
  auto with *.
}
assert ( Qabs (1#n) == 1#n ).
{
  auto using Qabs_pos.
}
rewrite H3.
assert( 1#N <= eps ).
{
  assert( H4 := smaller_unit_frac eps H ).
  rewrite HeqN.
  apply H4.
}
assert( 1#n <= 1#N ).
{
  unfold Qle.
  simpl.
  unfold Z.le.
  unfold Z.compare.
  assert( (N <= n)%positive ).
  {
    nia.
  }
  unfold Pos.le in H5.
  apply H5.
}
eauto using Qle_trans.
Qed.


Definition modulus : forall q, q>0 -> positive.
Proof.
intros.
assert( H0 := ex1_works q H ).
destruct H0.

Defined.