Require Import Coq.QArith.QArith_base.
Require Import Coq.QArith.Qround.
Require Import Coq.QArith.Qabs.
Require Import Coq.Lists.SetoidList.
Require Import Coq.ZArith.Znat.
Require Import Psatz.
Require Import Sequence.
Require Import PointContinuousFunction.
Require Import Utility.

Definition IncreasingFunction_def f := forall x y , x<y -> (f x) <= (f y).

Definition ContinuousFunction_def f w :=
  PointContinuousFunction_def w 0 /\
  IncreasingFunction_def w /\
  forall q, q==0 -> w q == 0 /\
  forall x y, Qabs ((f x) + -(f y)) <=
              w (Qabs (x + -y)).
                           


Record ContinuousFunction :=
  {
    Continf : Q -> Q;
    Continw : Q -> Q;
    Contin_spec : ContinuousFunction_def Continf Continw;
  }.



Definition max r1 r2 := 
if Qlt_le_dec r1 r2 then r2 else r1.

Definition argmax (f:Q->Q) r1 r2 :=
if Qlt_le_dec (f r1) (f r2) then r2 else r1.

Definition argmin (f:Q->Q) r1 r2 :=
if Qlt_le_dec (f r1) (f r2) then r1 else r2.

Definition smaller_unit_num r := 1 # (Qden r).

Lemma smaller_unit_num_is_smaller : forall r, r>0 ->
smaller_unit_num r <= r.
Proof.
intros.
unfold smaller_unit_num.
destruct r.
simpl.
unfold Qle.
simpl.
unfold Zle.
unfold Z.mul.
destruct Qnum.
*
simpl.
assert(not (0 <0 # Qden)).
{
  unfold Qlt.
  simpl.
  auto with *. 
}
contradiction H0.
* 
simpl.
assert((Qden <= p*Qden)%positive).
{
  nia.
}
auto with *.
* simpl.
  assert(not (0 < Z.neg p # Qden) ).
  {
    assert( Z.neg p # Qden < 0 ).
    {
      auto with *.
    }
    auto with *.
  }
auto with *.
Qed.

Lemma max_refl:
  forall a a' b,
  a' == a ->
  a' <= max a b.
Proof.
  intros.
  unfold max.
  destruct (Qlt_le_dec a b); lra.
Qed.

Lemma max_trans : forall a b c,
  a <= c ->
  a <= max b c.
Proof.
intros.
unfold max.
destruct (Qlt_le_dec b c); lra.
Qed.

Definition ProperFun f := forall r1 r2,
r1==r2 -> f r1 == f r2.

Fixpoint max_of_list xs :=
  match xs with
    | nil => 0
    | cons y ys => max y (max_of_list ys)
  end.

Fixpoint argmax_of_list f xs :=
  match xs with
    | nil => 0
    | cons y ys => argmax f y (argmax_of_list f ys)
  end.

Lemma argmax_refl :
  forall f r l,
  f r <= f (argmax f r l).
Proof.
intros.
unfold argmax.
destruct (Qlt_le_dec (f r) (f l)); lra.
Qed.

Lemma argmax_refl_rev :
  forall f r l,
  f r <= f (argmax f l r).
Proof.
intros.
unfold argmax.
destruct (Qlt_le_dec (f l) (f r)); lra.
Qed.

Lemma argmax_trans_eq : 
  forall f r a l, ProperFun f ->
  r==a -> f r <= f (argmax f a l).
Proof.
  intros.
  unfold argmax.
  destruct (Qlt_le_dec (f a) (f l)).
  {
    assert(f a == f r).
    {
      unfold ProperFun in H.
      auto with *.
    }
    rewrite H1 in q.
    lra.
  }
  
  assert(f r == f a).
  {
    unfold ProperFun in H.
    auto.
  }
  rewrite H1.
  lra.
  
Qed.


Lemma argmax_trans_leq : 
  forall f r a l, ProperFun f ->
  (f r) <= (f a) -> f r <= f (argmax f a l).
Proof.
  intros.
  unfold argmax.
  destruct (Qlt_le_dec (f a) (f l)).
  {
    assert(f a <= f l) by lra.
    eauto using Qle_trans.
  }
  apply H0.  
Qed.


Lemma argmax_symm : forall f r1 r2,
 f (argmax f r1 r2) == f (argmax f r2 r1).
Proof.
  intros.
  unfold argmax.
  destruct (Qlt_le_dec (f r1) (f r2)).
  {
    destruct (Qlt_le_dec (f r2) (f r1)).
    {
      lra.
    }
    lra.
  }
  destruct ( Qlt_le_dec (f r2) (f r1) ).
  {
   lra. 
  }
  lra.
  
Qed.

Lemma argmax_of_list_works : forall f l r,
ProperFun f -> InA Qeq r l -> f r <= f (argmax_of_list f l).
Proof.
induction l; intros.
+ inversion H0.
+ inversion H0.
  - subst.
    simpl.
    assert( f r == f a).
    {
      unfold ProperFun in H.
      auto.
    }
    rewrite H1.
    auto using argmax_refl.
  - apply IHl in H2.
    {
      simpl.
      remember (argmax_of_list f l) as m.
      assert(f (argmax f a m) == f (argmax f m a)).
      {
        auto using argmax_symm.
      }
      rewrite H4.
      apply argmax_trans_leq.
      {
        apply H.
      }
      apply H2.
    }
    apply H.
Qed.



Lemma max_of_list_works : forall r l,
  InA Qeq r l -> r <= max_of_list l.
Proof.
  intros.
  unfold max_of_list.
  induction l.
  + inversion H.
  + inversion H.
    - subst.
      auto using max_refl.
    - subst.
      auto using max_trans.
Qed.


Definition discretize_i a b n i :=
  let invn := 1#n in
  let Qi   := i#1 in
  let r := (b-a) * invn in
  a + r*Qi.

Fixpoint range_to_n n :=
  match n with
   | O   => nil
   | S m => (Z.of_nat m) :: (range_to_n m)
  end.


Definition discretize a b n := 
map (discretize_i a b n) (range_to_n (Pos.to_nat (n+1))).


Definition sab a b q := (b-a)/q.
Definition wab a b q := q * (b-a).



Lemma useful_sequence : 
forall a b, a<b -> 
ConvergentSequence_def (sab a b) 0 (wab a b).
Proof.
  intros.
  unfold ConvergentSequence_def.
  intros.
  unfold sab.
  unfold wab.
  assert((b - a) / (q * (b - a)) + - 0 == 1/q).
  {
    field.
    split; lra.
  }
  rewrite H1.
  assert( 1/q > 0 ).
  {
    unfold Qdiv.
    assert (/q >0 ).
    {
      unfold Qinv.
      destruct q.
      simpl in *.
      destruct Qnum; auto.
    }
    lra.
    
      
  }
  assert( 0<=1/q) by lra.
  apply Qabs_pos in H3.
  lra.
  
Qed.

Definition nearest_element x l
  := argmax_of_list (fun z=>Qabs (z-x)) l.

(*
Lemma discretization_error : 
  forall a b x n, 
  a<b -> In x (discretize a b n)
      -> a<=x /\ x<=b
      -> Qabs (x-(nearest_element x (discretize a b n))) <= (b-a).
*)
Theorem extreme_value_theorem f (fIsProp: ProperFun f): forall w a b err,
(ContinuousFunction_def f w) ->
a < b -> err>0 ->
exists xmaxq,
forall x,
f xmaxq >= (f x) - err.
Proof.
  intros.
  unfold ContinuousFunction_def in H.
  destruct H as (Ha,(Hb,Hc)).
  unfold PointContinuousFunction_def in Ha.
  remember(
  {| Seq := sab a b;
     Seqr:= 0;
     Seqa:= wab a b;
     Seq_spec := (useful_sequence a b H0)
     |}) as tiago.
  assert( Seqr tiago == 0).
  {
    subst.
    simpl.
    lra.
  }
  assert (H2 := Ha tiago H).
  remember (smaller_unit_num err) as invq.
  remember (Qinv invq) as q.
  destruct H2 as (R,HR).
  unfold ConvergentSequence_def in HR.
  remember (R q) as rq.
  remember (Qceiling rq) as zn.
  remember (Z.to_pos zn) as n.
  remember (discretize a b n) as xs.
  remember (argmax_of_list f xs) as mxf.
  exists mxf.
  intros.
  remember (argmax_of_list (fun z => Qabs (z-x)) xs) as nearmx.
  
Qed.










