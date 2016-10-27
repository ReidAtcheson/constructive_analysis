Require Import Coq.QArith.QArith_base.
Require Import Coq.QArith.Qabs.
Require Import Psatz.



Lemma my_test : forall r, r>=0 -> r <= r+r.
Proof.
  intros.
  lra.
Qed.


Lemma use_my_test : forall a b c, (a+b)>=0 -> (a+c)>=0 -> (a+b)*(a+c)>=0.
Proof.
  assert( H0 := my_test (a>0) (b>0) ).
  
Qed.
