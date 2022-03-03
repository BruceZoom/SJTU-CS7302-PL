Require Import Coq.Init.Nat.
Require Import Coq.ZArith.ZArith.
Require Import Lia.
Require Import PL.Imp.
Require Import PL.State.

Open Scope Z.

Module BigStep.
  Inductive astep : aexp -> state -> Z -> Prop :=
  | AStep_int: forall (z: Z) st, astep z st z
  | AStep_var: forall (x: loc) st v,
      v = st x -> astep x st v
  | AStep_plus: forall a0 a1 st v0 v1 v,
      astep a0 st v0 ->
      astep a1 st v1 ->
      v = v0 + v1 ->
      astep (a0 + a1) st v
  | AStep_minus: forall a0 a1 st v0 v1 v,
      astep a0 st v0 ->
      astep a1 st v1 ->
      v = v0 - v1 ->
      astep (a0 - a1) st v
  | AStep_mult: forall a0 a1 st v0 v1 v,
      astep a0 st v0 ->
      astep a1 st v1 ->
      v = v0 * v1 ->
      astep (a0 * a1) st v
  .

  Goal forall (st: state) x y,
    st x = 1 ->
    st y = -1 ->
    astep ((x + 5) - (y * 2)) st 8.
  Proof.
    intros.
    eapply AStep_minus;
    [eapply AStep_plus | eapply AStep_mult |];
    try apply AStep_var;
    try constructor; lia.
  Qed.
  
  Definition astep_termination :=
      forall a st, exists v, astep a st v.

  Lemma astep_terminates : astep_termination.
  Proof.
    intros a st.
    induction a;
    try (destruct IHa1 as [v1 ?];
    destruct IHa2 as [v2 ?]).
    - exists n; constructor.
    - exists (st x); constructor; auto.
    - exists (v1 + v2); econstructor; auto; auto.
    - exists (v1 - v2); econstructor; auto; auto.
    - exists (v1 * v2); econstructor; auto; auto.
  Qed.

  Definition aexp_equiv a0 a1 :=
      forall v st, astep a0 st v <-> astep a1 st v.
  

  Inductive bstep: bexp -> state -> bool -> Prop :=
  | BStep_true: forall st, bstep BTrue st true
  | BStep_false: forall st, bstep BFalse st false
  | BStep_eq: forall a1 a2 st v1 v2 v,
      astep a1 st v1 ->
      astep a2 st v2 ->
      v = Z.eqb v1 v2 ->
      bstep (a1 == a2) st v
  | BStep_le: forall a1 a2 st v1 v2 v,
      astep a1 st v1 ->
      astep a2 st v2 ->
      v = Z.leb v1 v2 ->
      bstep (a1 <= a2) st v
  | BStep_not: forall b st v v0,
      bstep b st v ->
      v0 = negb v ->
      bstep (! b) st v0
  | BStep_and: forall b1 b2 st v1 v2 v0,
      bstep b1 st v1 ->
      bstep b2 st v2 ->
      v0 = andb v1 v2 ->
      bstep (b1 && b2) st v0
  | BStep_or: forall b1 b2 st v1 v2 v0,
      bstep b1 st v1 ->
      bstep b2 st v2 ->
      v0 = orb v1 v2 ->
      bstep (b1 || b2) st v0
  .

  Definition bstep_termination :=
    forall b st, exists v, bstep b st v.

  Lemma bstep_terminates : bstep_termination.
  Proof.
    intros b; induction b; intros.
    - exists true; constructor.
    - exists false; constructor.
  Admitted.

  Inductive bstep': bexp -> state -> bool -> Prop :=
  | BStep'_true: forall st, bstep' BTrue st true
  | BStep'_false: forall st, bstep' BFalse st false
  | BStep'_eq_true: forall a1 a2 st v1 v2,
      astep a1 st v1 ->
      astep a2 st v2 ->
      v1 = v2 ->
      bstep' (a1 == a2) st true
  | BStep'_eq_false: forall a1 a2 st v1 v2,
      astep a1 st v1 ->
      astep a2 st v2 ->
      ~ v1 = v2 ->
      bstep' (a1 == a2) st false
  | BStep'_le_true: forall a1 a2 st v1 v2,
      astep a1 st v1 ->
      astep a2 st v2 ->
      v1 <= v2 ->
      bstep' (a1 <= a2) st true
  | BStep'_le_false: forall a1 a2 st v1 v2,
      astep a1 st v1 ->
      astep a2 st v2 ->
      v1 > v2 ->
      bstep' (a1 <= a2) st false
  | BStep'_not_true: forall b st,
      bstep' b st false ->
      bstep' (! b) st true
  | BStep'_not_false: forall b st,
      bstep' b st true ->
      bstep' (! b) st false
  | BStep'_and_true: forall b1 b2 st,
      bstep' b1 st true ->
      bstep' b2 st true ->
      bstep' (b1 && b2) st true
  | BStep'_and_false1: forall b1 b2 st,
      bstep' b1 st false ->
      bstep' (b1 && b2) st false
  | BStep'_and_false2: forall b1 b2 st,
      bstep' b2 st false ->
      bstep' (b1 && b2) st false
  | BStep'_or_true1: forall b1 b2 st,
      bstep' b1 st true ->
      bstep' (b1 || b2) st true
  | BStep'_or_true2: forall b1 b2 st,
      bstep' b2 st true ->
      bstep' (b1 || b2) st true
  | BStep'_or_false: forall b1 b2 st,
      bstep' b1 st false ->
      bstep' b2 st false ->
      bstep' (b1 || b2) st false
  .

  Definition bstep'_termination :=
    forall b st, exists v, bstep' b st v.

  Lemma bstep'_terminates : bstep'_termination.
  Proof.
    intros b; induction b; intros.
    - exists true; constructor.
    - exists false; constructor.
  Admitted.

  Lemma bstep_bstep'_equiv: forall b st v,
    bstep b st v <-> bstep' b st v.
  Proof.
    split; intros.
    {
      induction H; try constructor.
      - destruct (v1 =? v2) eqn:eq; 
        try rewrite Z.eqb_eq in eq;
        try rewrite Z.eqb_neq in eq; subst.
        + apply BStep'_eq_true with (v1 := v2) (v2 := v2); auto.
        + apply BStep'_eq_false with (v1 := v1) (v2 := v2); auto.
      - destruct (v1 <=? v2) eqn:eq;
        try rewrite Z.leb_le in eq;
        try rewrite Z.leb_gt in eq; subst.
        + apply BStep'_le_true with (v1 := v1) (v2 := v2); auto.
        + apply BStep'_le_false with (v1 := v1) (v2 := v2); auto; lia.
      - destruct (negb v) eqn:eq;
        try rewrite Bool.negb_true_iff in eq;
        try rewrite Bool.negb_false_iff in eq; subst;
        constructor; auto.
      - destruct ((v1 && v2)%bool) eqn:eq;
        try rewrite Bool.andb_true_iff in eq;
        try rewrite Bool.andb_false_iff in eq;
        destruct eq; subst.
        + constructor; auto.
        + constructor; auto.
        + apply BStep'_and_false2; auto.
      - destruct ((v1 || v2)%bool) eqn:eq;
        try rewrite Bool.orb_true_iff in eq;
        try rewrite Bool.orb_false_iff in eq;
        destruct eq; subst.
        + constructor; auto.
        + apply BStep'_or_true2; auto.
        + constructor; auto.
    }
    {
      induction H; subst; try constructor.
      - apply BStep_eq with (v1 := v2) (v2 := v2); auto; lia.
      - apply BStep_eq with (v1 := v1) (v2 := v2); auto; lia.
      - apply BStep_le with (v1 := v1) (v2 := v2); auto; lia.
      - apply BStep_le with (v1 := v1) (v2 := v2); auto; lia.
      - apply (BStep_not _ _ false); auto; lia.
      - apply (BStep_not _ _ true); auto; lia.
      - eapply (BStep_and _ _ _ true true _); auto; lia.
      - pose proof bstep_terminates b2 st as [v ?].
        eapply (BStep_and _ _ _ false v _); auto; lia.
      - pose proof bstep_terminates b1 st as [v ?].
        eapply (BStep_and _ _ _ v false _); auto; lia.
      - pose proof bstep_terminates b2 st as [v ?].
        eapply (BStep_or _ _ _ true v _); auto; lia.
      - pose proof bstep_terminates b1 st as [v ?].
        eapply (BStep_or _ _ _ v true _); auto; lia.
      - eapply (BStep_or _ _ _ false false _); auto; lia.
    }
  Qed.

End BigStep.

