Require Import Coq.QArith.QArith_base.
Require Import Psatz.
Require Import Sequence.


Definition abs (r:Q) := if (Qlt_le_dec r 0) then -r else r.



Record continuous_function := {
  f : Q -> Q;
  w : Q -> Q;
  w_spec1 : forall q : Q, q>=0 -> 
    (forall x y, (abs ((f x)+ -(f y))) 
    <= w (abs (x + -y))) ;
  w_spec2 : w 0 == 0 ;
  w_spec3 : forall x y, x<=y -> (w x <= w y);
}.


Definition fex1 (x:Q) := x.
Definition wex1 (x:Q) := x.
Lemma w_spec1_ex1 : forall q : Q, q>=0 -> 
    forall x y, (abs ((fex1 x)+ -(fex1 y))) 
    <= wex1 (abs (x + -y)).
Proof.
intros.
unfold wex1,fex1,abs.
destruct (Qlt_le_dec (x + -y) 0).
* apply Qle_refl.
* apply Qle_refl.
Qed.

Lemma w_spec2_ex2 : wex1 0 == 0.
Proof.
unfold wex1.
lra.
Qed.

Definition ex1 : continuous_function.
Proof.
(*eauto using Build_continuous_function, wex1_works.*)
apply Build_continuous_function with (f:=fex1) (w:=wex1).
apply w_spec1_ex1 .
Qed.










