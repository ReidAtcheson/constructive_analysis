Require Import Coq.QArith.QArith_base.
Require Import Coq.QArith.Qabs.
Require Import Psatz.



Lemma z_eq_minus_z : -0 == 0.
Proof.
lra.
Qed.



Lemma r_neq0_pos_or_neg : forall r, (not (r==0)) -> {r>0} + {r<0}.
Proof.
intros.
destruct (Q_dec r 0).
* destruct s.
  + auto.
  + auto. 
* auto with *.
Qed.

Lemma z_times_r_eq_z : forall r, 0*r == 0.
Proof.
intros.
lra.
Qed.

Lemma qnum_pos_r_pos : forall r, 
Z.gt (Qnum r) 0 -> r>0.
Proof.
intros.
unfold Qgt.
assert( Qnum 0 = 0%Z ) by auto.
rewrite H0.
assert( forall (z:Z), (0*z=0)%Z ) by auto.
assert( H2 := H1 (Zpos (Qden r))).
rewrite H2.
assert(  (Zpos (Qden 0)=1)%Z ) by auto.
rewrite H3.
auto with *.
Qed.

Lemma qnum_neg_r_neg : forall r,
Z.lt (Qnum r) 0 -> r<0.
Proof.
intros.
unfold Qlt.
assert( Qnum 0 = 0%Z ) by auto.
rewrite H0.
assert( forall (z:Z), (0*z=0)%Z ) by auto.
assert( H2 := H1 (Zpos (Qden r))).
rewrite H2.
assert(  (Zpos (Qden 0)=1)%Z ) by auto.
rewrite H3.
auto with *.
Qed.

Lemma r_neg_qnum_neg : forall r,
r<0 -> Z.lt (Qnum r) 0.
Proof.
intros.
destruct (Ztrichotomy (Qnum r) 0).
*auto.
*destruct H0.
  + assert (not (r < 0)) by auto with *.
    contradiction H1.
  + assert (not (r < 0)) by auto with *.
    contradiction H1. 
Qed.

Lemma r_pos_qnum_pos : forall r,
r>0 -> Z.gt (Qnum r) 0.
Proof.
intros.
destruct (Ztrichotomy (Qnum r) 0).
* assert( not (0 < r) ).
  {
    assert (P := (qnum_neg_r_neg r H0)).
    auto with *.
  }
  contradiction H1.
* destruct H0.
  + assert (not (0<r)).
    {
      assert( r==0 ) by auto with *.
      auto with *.
    }
    contradiction H1.
  + apply H0.
Qed.

Open Scope Z_scope.
Lemma z_squared_pos : forall (z:Z), z<>0->z*z>0.
Proof.
intros.
destruct (Ztrichotomy z 0).
* nia.
* nia.
Qed.
Close Scope Z_scope.


Lemma r_pos_numr_pos : forall r,
r>0 -> Z.gt (Qnum r) 0.
Proof.
intros.
unfold Qlt in H.
assert( Qnum 0 = 0 %Z) by auto.
rewrite H0 in H.
assert( Qden 0 = 1 %positive) by auto.
rewrite H1 in H.
assert ((0 * (Zpos (Qden r)) = 0)%Z) by auto.
rewrite H2 in H.
assert(( Qnum r * 1 = Qnum r)%Z) by auto with *.
rewrite H3 in H.
auto with *.
Qed.

Lemma z_neq0_pos_or_neg : forall (z:Z), (z<>0 -> {z>0} + {z<0})%Z.
Proof.
intros.
destruct (Ztrichotomy_inf z 0).
* destruct s.
  + auto.
  + auto with *.
* auto.
Qed.





Lemma r_squared_pos : forall r, (not (r==0))->r*r>0.
Proof.
intros.
destruct (r_neq0_pos_or_neg r H).
* unfold Qmult.
  assert( ((Qnum r) * (Qnum r) > 0)%Z).
  {
    assert( (Qnum r <> 0)%Z ).
    {
      auto with *.
    }
    apply (z_squared_pos (Qnum r) (H0)).
  }
  assert( (Qnum (Qnum r * Qnum r # Qden r * Qden r) = Qnum r * Qnum r)%Z) by auto with *.
  assert( (Qnum (Qnum r * Qnum r # Qden r * Qden r) > 0)%Z) by auto with *.
  apply (qnum_pos_r_pos (Qnum r * Qnum r # Qden r * Qden r) H2).  
* unfold Qmult.
  assert( ((Qnum r) * (Qnum r) > 0)%Z).
  {
    assert( (Qnum r <>0)%Z ).
    {
      auto with *.
    }
    assert( (Qnum (Qnum r * Qnum r # Qden r * Qden r) = Qnum r * Qnum r)%Z) by auto with *.
    assert( (Qnum (Qnum r * Qnum r # Qden r * Qden r) > 0)%Z).
    {
      rewrite H1.
      apply (z_squared_pos (Qnum r) H0).
    }
    auto with *.
    (*apply (qnum_pos_r_pos (Qnum r * Qnum r # Qden r * Qden r) H2).  *)
  }
  assert ( (Qnum (Qnum r * Qnum r # Qden r * Qden r) = Qnum r * Qnum r)%Z ) by auto with *.
  assert ( (Qnum (Qnum r * Qnum r # Qden r * Qden r) > 0)%Z ) by auto with *.
  apply (qnum_pos_r_pos (Qnum r * Qnum r # Qden r * Qden r) H2).
Qed.


Lemma q_eq_qmake_denqnumq : forall q,
q = (Qnum q) # (Qden q).
Proof.
intros.
destruct q.
auto.
Qed.

Lemma q_pos_invq_pos : forall q,
q>0 -> (1/q>0).
Proof.
intros.
assert( ( Qnum q > 0)%Z ).
{
  apply (r_pos_numr_pos q H).
}
unfold Qlt.
assert( (Qnum 0 = 0)%Z ) by auto with *.
rewrite H1.
assert( (0 * Zpos (Qden (1/q)) = 0)%Z ) by auto.
rewrite H2.
assert( ((Zpos (Qden 0))=1)%Z ) by auto.
rewrite H3.
assert( (Qnum (1 / q) * 1 = Qnum (1/q) )%Z ) by auto with *.
rewrite H4.
assert( 1/q = Qinv q ).
{
  unfold Qdiv.
  assert( 1 * /q = /q).
  {
    unfold Qmult.
    assert( ( Qnum 1 * Qnum (/ q) = Qnum (/ q))%Z ) by auto with *.
    rewrite H5.
    assert( (Qden 1 * Qden (/q) = Qden (/q))%positive ) by auto with *.
    rewrite H6.
    destruct (/q).
    auto.
  }
  rewrite H5.
  auto.
}
rewrite H5.
assert( 0< /q).
{
  unfold Qinv.
  destruct (Qnum q).
  + assert( not (0 > 0)%Z ) by auto with *.
    contradiction H6.
  + auto with *.
  + auto with *.
}
assert (H7 := (r_pos_qnum_pos (/q) H6)).
auto with *.
Qed.



Lemma qinvq_eq_1divq : forall q,
(/q) == (1/q).
Proof.
intros.
unfold Qdiv.
assert( 1 * /q = /q).
{
  unfold Qmult.
  assert( ( Qnum 1 * Qnum (/ q) = Qnum (/ q))%Z ) by auto with *.
  rewrite H.
  assert( (Qden 1 * Qden (/q) = Qden (/q))%positive ) by auto with *.
  rewrite H0.
  destruct (/q).
  auto.
}
rewrite H.
apply Qeq_refl.
Qed.

