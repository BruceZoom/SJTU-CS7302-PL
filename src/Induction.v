From Coq Require Import Logic.Classical.
From Coq Require Import Psatz.

Definition Order {A : Type} (P : A -> A -> Prop) := forall a1 a2 a3 , P a1 a2 -> P a2 a3 -> P a1 a3.

Definition nonempty_set {A : Type} (Q : A -> Prop) := exists u , Q u.

Definition nonempty_relation {A B: Type} (R : A -> B -> Prop) := forall a  , exists b, R a b.

Theorem Theorem_in_slides : forall (P : nat -> Prop) , (forall n , P n) <-> (forall n k , k < n -> P k).
Proof.
  split ; intros ; auto.
  apply (H (S n) n). lia.
Qed.

Theorem Strong_induction : forall (P : nat -> Prop), P (0) -> (forall n , (forall k , k < n -> P k) -> P n) -> forall n , P n. 
Proof.
  intros.
  apply H0.
  induction n ; intros.
  - inversion H1.
  - inversion H1.
    + apply H0. auto.
    + apply IHn. lia.
Qed.

Definition well_founded {A : Type} (R : A -> A -> Prop) := ~ (exists (f : nat -> A -> Prop) , nonempty_relation f /\ forall n a1 a2, f n a1 -> f (S n) a2 -> R a1 a2).

Definition irreflexivity {A : Type} (R : A -> A -> Prop) := forall a , ~ R a a.

Theorem well_founded_imply_irreflexivity {A : Type} : forall (R : A -> A -> Prop), well_founded R -> irreflexivity R.
Proof.
  intros.
  intro. intro. apply H.
  exists (fun _ b => b = a) ; auto.
  split ;intros ; subst ; auto.
  intro. exists a. auto.
Qed.

Definition minimal_element {A : Type} (R : A -> A -> Prop) (Q : A -> Prop) (u : A) := 
  Q u /\ (forall v , Q v -> ~ R u v).

Definition injection {A B : Type} (f : A -> B -> Prop) := forall a b1 b2, f a b1 -> f a b2 -> b1 = b2.

Inductive f {A : Type} (x0 : A) (Q : A -> Prop) (R : A -> A -> Prop) : nat -> A -> Prop :=
  | f0 : Q x0 -> f x0 Q R O x0
  | fn : forall n b a1 , Q a1 -> Q b -> f x0 Q R n a1 -> R a1 b -> f x0 Q R (S n) b
.

Theorem well_founded_equiv_anysubset_has_minimal {A : Type} : forall (R : A -> A -> Prop), well_founded R <-> (forall Q , nonempty_set Q -> exists u , minimal_element R Q u).
Proof.
  split.
  - intro. apply NNPP.
    intro.
    apply not_all_ex_not in H0.
    destruct H0. 
    apply not_imply_elim in H0 as H1.
    apply not_imply_elim2 in H0.
    pose proof not_ex_all_not A (fun n => minimal_element R x n) H0.
    simpl in H2. apply H.
    destruct H1.
    admit.
  - intros. intro. destruct H0 , H0.
    set (P := (fun a => exists n , x n a)).
    assert (nonempty_set P).
    { destruct (H0 O). exists x0 , O. auto. }
    specialize (H P H2).
    destruct H. destruct H.
    subst P. simpl in *.
    destruct H.
    destruct (H0 (S x1)).
    specialize (H1 _ _ _ H H4).
    apply (H3 x2) ; auto.
    exists (S x1). auto.
Admitted.

Theorem well_founded_induction {A : Type} : forall (R : A -> A -> Prop) , well_founded R -> forall (P : A -> Prop) , (forall a , P a) <-> (forall a , (forall b , R a b -> P b) -> P a).
Proof.
  split ; intros ; auto.
  apply NNPP. intro.
  set (Q := (fun a => ~ P a)).
  assert (nonempty_set Q).
  { exists a. auto. }
  rewrite well_founded_equiv_anysubset_has_minimal in H.
  specialize (H Q H2).
  destruct H.
  destruct H. 
  assert (forall b , R x b -> ~ Q b).
  { intros. intro. apply (H3 b H5). auto. }
  apply H. apply H0.
  intros. specialize (H4 _ H5). apply NNPP in H4. auto.
Qed.
  
 
    