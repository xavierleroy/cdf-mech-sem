From Coq Require Import ZArith Psatz Bool String List FMaps.
From Coq Require Import FunctionalExtensionality.
From CDF Require Import Sequences IMP.
From CDF Require AbstrInterp.

Local Open Scope string_scope.
Local Open Scope Z_scope.

(** * 5.  Static analysis by abstract interpretation, improved version *)

(** ** 5.5.  Improved interface of abstract domains *)

(** We enrich the interface of abstract domains for values with
    operations for inverse analysis of conditionals and for widening. *)

Module Type VALUE_ABSTRACTION.

(** We reuse all the declarations of the simplified interface. *)

  Include AbstrInterp.VALUE_ABSTRACTION.

(** [meet] computes a lower bound of its two arguments. *)
  Parameter meet: t -> t -> t.
  Axiom meet_1: forall n N1 N2, In n N1 -> In n N2 -> In n (meet N1 N2).

(** [isIn] tests whether a concrete value belongs to an abstract value. *)
  Parameter isIn: Z -> t -> bool.
  Axiom isIn_1: forall n N, In n N -> isIn n N = true.

(** Abstract operators for inverse analysis of comparisons. *)

(** Consider a test [a1 = a2] that evaluates to true at run-time.
    Let [N1] be an abstraction of [a1] and [N2] be an abstraction of [a2].
    [eq_inv N1 N2] produces a pair of abstract values [N1', N2'].
    [N1'] is a possibly more precise abstraction for [a1]
    taking into account the fact that [a1 = a2].
    [N2'] is a possibly more precise abstraction for [a2]
    taking into account the fact that [a1 = a2]. *)

  Parameter eq_inv: t -> t -> t * t.
  Axiom eq_inv_1:
    forall n1 n2 N1 N2,
    In n1 N1 -> In n2 N2 -> n1 = n2 ->
    In n1 (fst (eq_inv N1 N2)) /\ In n2 (snd (eq_inv N1 N2)).

(** [ne_inv], [le_inv] and [gt_inv] are similar but apply to the other
    three basic comparisons: "different", "less than or equal", and
    "greater than". *)

  Parameter ne_inv: t -> t -> t * t.
  Axiom ne_inv_1:
    forall n1 n2 N1 N2,
    In n1 N1 -> In n2 N2 -> n1 <> n2 ->
    In n1 (fst (ne_inv N1 N2)) /\ In n2 (snd (ne_inv N1 N2)).

  Parameter le_inv: t -> t -> t * t.
  Axiom le_inv_1:
    forall n1 n2 N1 N2,
    In n1 N1 -> In n2 N2 -> n1 <= n2 ->
    In n1 (fst (le_inv N1 N2)) /\ In n2 (snd (le_inv N1 N2)).

  Parameter gt_inv: t -> t -> t * t.
  Axiom gt_inv_1:
    forall n1 n2 N1 N2,
    In n1 N1 -> In n2 N2 -> n1 > n2 ->
    In n1 (fst (gt_inv N1 N2)) /\ In n2 (snd (gt_inv N1 N2)).

(** [widen N1 N2] computes an upper bound of its first argument, chosen
    so as to guarantee and accelerate the convergence of fixed point
    iteration. *)

  Parameter widen: t -> t -> t.
  Axiom widen_1: forall N1 N2, le N1 (widen N1 N2).

(** To guarantee convergence, we provide a measure with nonnegative
    integer values that decreases strictly along the fixed point
    iteration with widening. *)
  Parameter measure: t -> nat.
  Axiom measure_top: measure top = 0%nat.
  Axiom widen_2: forall N1 N2, (measure (widen N1 N2) <= measure N1)%nat.
  Axiom widen_3:
    forall N1 N2, ble N2 N1 = false -> (measure (widen N1 N2) < measure N1)%nat.

End VALUE_ABSTRACTION.

(** We enrich the interface of abstract stores with a widening operation. *)

Module Type STORE_ABSTRACTION.

  Declare Module V: VALUE_ABSTRACTION.
  Parameter t: Type.
  Parameter get: ident -> t -> V.t.
  Definition In (s: store) (S: t) : Prop := forall x, V.In (s x) (get x S).
  Parameter set: ident -> V.t -> t -> t.
  Axiom set_1: forall x n N s S, V.In n N -> In s S -> In (update x n s) (set x N S).
  Definition le (S1 S2: t) : Prop :=
    forall s, In s S1 -> In s S2.
  Parameter ble: t -> t -> bool.
  Axiom ble_1: forall S1 S2, ble S1 S2 = true -> le S1 S2.
  Parameter bot: t.
  Axiom bot_1: forall s, ~(In s bot).
  Parameter top: t.
  Parameter top_1: forall s, In s top.
  Parameter join: t -> t -> t.
  Axiom join_1: forall s S1 S2, In s S1 -> In s (join S1 S2).
  Axiom join_2: forall s S1 S2, In s S2 -> In s (join S1 S2).

(** This is the new widening operator. *)

  Parameter widen: t -> t -> t.
  Axiom widen_1: forall S1 S2, le S1 (widen S1 S2).

(** The order below corresponds to consecutive rounds of the fixed point
    iteration with widening.  We require it to be well founded,
    so as to guarantee termination. *)

  Definition widen_order (S S1: t) :=
    exists S2, S = widen S1 S2 /\ ble S2 S1 = false.

  Axiom widen_order_wf: well_founded widen_order.

End STORE_ABSTRACTION.

(** ** 5.6.  The improved generic analyzer. *)

Module Analysis (ST: STORE_ABSTRACTION).

Module V := ST.V.

(** *** Computing post-fixed points with widening and narrowing. *)

Section FIXPOINT.

Variable F: ST.t -> ST.t.

Program Definition is_true (b: bool) : { b = true } + { b = false } :=
  match b with true => left _ | false => right _ end.

Lemma iter_up_acc:
  forall (S: ST.t) (acc: Acc ST.widen_order S) (S': ST.t),
  ST.ble S' S = false ->
  Acc ST.widen_order (ST.widen S S').
Proof.
  intros. eapply Acc_inv; eauto. exists S'. auto. 
Defined.

Fixpoint iter_up (S: ST.t) (acc: Acc ST.widen_order S) : ST.t :=
  let S' := F S in
  match is_true (ST.ble S' S) with
  | left LE => S
  | right NOTLE => iter_up (ST.widen S S') (iter_up_acc S acc S' NOTLE)
  end.

Fixpoint iter_down (n: nat) (S: ST.t) : ST.t :=
  match n with
  | O => S
  | S n => let S' := F S in
           if ST.ble (F S') S' then iter_down n S' else S
  end.

Definition niter_down := 3%nat.

Definition postfixpoint : ST.t :=
  iter_down niter_down (iter_up ST.bot (ST.widen_order_wf ST.bot)).

Lemma iter_up_sound:
  forall S acc, ST.le (F (iter_up S acc)) (iter_up S acc).
Proof.
  induction S using (well_founded_induction ST.widen_order_wf). 
  intros acc. destruct acc. cbn. destruct (is_true (ST.ble (F S) S)).
- apply ST.ble_1; auto.
- apply H. exists (F S); auto. 
Qed.

Lemma iter_down_sound:
  forall n S, ST.le (F S) S -> ST.le (F (iter_down n S)) (iter_down n S).
Proof.
  induction n; intros; cbn.
- auto.
- destruct (ST.ble (F (F S)) (F S)) eqn:BLE.
  + apply IHn. apply ST.ble_1; auto.
  + auto.
Qed.

Lemma postfixpoint_sound: ST.le (F postfixpoint) postfixpoint.
Proof.
  apply iter_down_sound. apply iter_up_sound.
Qed.

End FIXPOINT.

(** *** Abstract interpretation of arithmetic expressions *)

(** Same definition as in the simplified version. *)

Fixpoint Aeval (a: aexp) (S: ST.t) : V.t :=
  match a with
  | CONST n => V.const n
  | VAR x => ST.get x S
  | PLUS a1 a2 => V.add (Aeval a1 S) (Aeval a2 S)
  | MINUS a1 a2 => V.sub (Aeval a1 S) (Aeval a2 S)
  end.

Lemma Aeval_sound:
  forall s S a,
  ST.In s S -> V.In (aeval a s) (Aeval a S).
Proof.
  induction a; cbn; intros.
- apply V.const_1.
- apply H.
- apply V.add_1; auto.
- apply V.sub_1; auto.
Qed.

(** *** Inverse analysis of arithmetic and Boolean expressions *)

(** Assuming that the concrete value of [a] belongs to the abstract
    value [Res], what do we learn about the values of the variables
    that occur in [a]?  The facts that we learn are used to refine
    the abstract values of these variables in the abstract store [S]. *)

Fixpoint assume_eval (a: aexp) (Res: V.t) (S: ST.t) : ST.t :=
  match a with
  | CONST n =>
      if V.isIn n Res then S else ST.bot
  | VAR x =>
      ST.set x (V.meet Res (ST.get x S)) S
  | PLUS a1 a2 =>
      let N1 := Aeval a1 S in
      let N2 := Aeval a2 S in
      let Res1 := V.meet N1 (V.sub Res N2) in
      let Res2 := V.meet N2 (V.sub Res N1) in
      assume_eval a1 Res1 (assume_eval a2 Res2 S)
  | MINUS a1 a2 =>
      let N1 := Aeval a1 S in
      let N2 := Aeval a2 S in
      let Res1 := V.meet N1 (V.add Res N2) in
      let Res2 := V.meet N2 (V.sub N1 Res) in
      assume_eval a1 Res1 (assume_eval a2 Res2 S)
  end.

Lemma assume_eval_sound:
  forall a Res S s,
  V.In (aeval a s) Res -> ST.In s S -> ST.In s (assume_eval a Res S).
Proof.
  induction a; cbn; intros.
- (* CONST *)
  rewrite V.isIn_1 by auto. auto.
- (* VAR *)
  replace s with (update x (s x) s).
  apply ST.set_1; auto.
  apply V.meet_1; auto.
  apply functional_extensionality; intros y. 
  unfold update; destruct (string_dec x y); congruence.
- (* PLUS *)
  set (n1 := aeval a1 s) in *. set (n2 := aeval a2 s) in *.
  set (N1 := Aeval a1 S). set (N2 := Aeval a2 S).
  assert (V.In n1 N1) by (apply Aeval_sound; auto).
  assert (V.In n2 N2) by (apply Aeval_sound; auto).
  apply IHa1; fold n1.
  apply V.meet_1. auto. replace n1 with ((n1 + n2) - n2) by lia. apply V.sub_1; auto.
  apply IHa2; fold n2.
  apply V.meet_1. auto. replace n2 with ((n1 + n2) - n1) by lia. apply V.sub_1; auto.
  auto.
- (* MINUS *)
  set (n1 := aeval a1 s) in *. set (n2 := aeval a2 s) in *.
  set (N1 := Aeval a1 S). set (N2 := Aeval a2 S).
  assert (V.In n1 N1) by (apply Aeval_sound; auto).
  assert (V.In n2 N2) by (apply Aeval_sound; auto).
  apply IHa1; fold n1.
  apply V.meet_1. auto. replace n1 with ((n1 - n2) + n2) by lia. apply V.add_1; auto.
  apply IHa2; fold n2.
  apply V.meet_1. auto. replace n2 with (n1 - (n1 - n2)) by lia. apply V.sub_1; auto.
  auto.
Qed.

(** Assuming that the Boolean expression [b] evaluates concretely to
    the Boolean value [res], what do we learn about the values of the
    variables that occur in [b]?  The facts that we learn are used to
    refine the abstract values of these variables in the abstract
    store [S]. *)

Fixpoint assume_test (b: bexp) (res: bool) (S: ST.t): ST.t :=
  match b with
  | TRUE => if res then S else ST.bot
  | FALSE => if res then ST.bot else S
  | EQUAL a1 a2 =>
      let (Res1, Res2) :=
        if res
        then V.eq_inv (Aeval a1 S) (Aeval a2 S)
        else V.ne_inv (Aeval a1 S) (Aeval a2 S) in
      assume_eval a1 Res1 (assume_eval a2 Res2 S)
  | LESSEQUAL a1 a2 =>
      let (Res1, Res2) :=
        if res
        then V.le_inv (Aeval a1 S) (Aeval a2 S)
        else V.gt_inv (Aeval a1 S) (Aeval a2 S) in
      assume_eval a1 Res1 (assume_eval a2 Res2 S)
  | NOT b1 =>
      assume_test b1 (negb res) S
  | AND b1 b2 =>
      if res
      then assume_test b1 true (assume_test b2 true S)
      else ST.join (assume_test b1 false S) (assume_test b2 false S)
  end.

Lemma assume_test_sound:
  forall b res S s,
  beval b s = res -> ST.In s S -> ST.In s (assume_test b res S).
Proof.
  induction b; cbn; intros.
- (* TRUE *)
  subst res; auto.
- (* FALSE *)
  subst res; auto.
- (* EQUAL *)
  set (Res := if res
              then V.eq_inv (Aeval a1 S) (Aeval a2 S)
              else V.ne_inv (Aeval a1 S) (Aeval a2 S)).
  assert (A: V.In (aeval a1 s) (fst Res) /\ V.In (aeval a2 s) (snd Res)).
  { unfold Res; destruct res;
    [ apply V.eq_inv_1 | apply V.ne_inv_1 ]; auto using Aeval_sound.
  - apply Z.eqb_eq; auto.
  - apply Z.eqb_neq; auto.
  }
  destruct A as [A1 A2]. destruct Res as [Res1 Res2]. auto using assume_eval_sound.
- (* LESSEQUAL *)
  set (Res := if res
              then V.le_inv (Aeval a1 S) (Aeval a2 S)
              else V.gt_inv (Aeval a1 S) (Aeval a2 S)).
  assert (A: V.In (aeval a1 s) (fst Res) /\ V.In (aeval a2 s) (snd Res)).
  { unfold Res; destruct res;
    [ apply V.le_inv_1 | apply V.gt_inv_1 ]; auto using Aeval_sound.
  - apply Z.leb_le; auto.
  - apply Z.leb_nle in H. lia.
  }
  destruct A as [A1 A2]. destruct Res as [Res1 Res2]. auto using assume_eval_sound.
- (* NOT *)
  apply IHb; auto. rewrite <- H. rewrite negb_involutive; auto. 
- (* AND *)
  destruct res.
  + (* AND, true *)
    destruct (andb_prop _ _ H). 
    auto.
  + (* AND, false *)
    destruct (andb_false_elim _ _ H); [apply ST.join_1 | apply ST.join_2]; auto.
Qed.

(** *** Improved abstract interpretation of commands *)

(** We add calls to [assume_test] every time a Boolean condition
    is known to be true or to be false. *)

Fixpoint Cexec (c: com) (S: ST.t) : ST.t :=
  match c with
  | SKIP => S
  | ASSIGN x a => ST.set x (Aeval a S) S
  | SEQ c1 c2 => Cexec c2 (Cexec c1 S)
  | IFTHENELSE b c1 c2 =>
      ST.join (Cexec c1 (assume_test b true S))
              (Cexec c2 (assume_test b false S))
  | WHILE b c =>
      assume_test b false
        (postfixpoint (fun X => ST.join S (Cexec c (assume_test b true X))))
  end.

Theorem Cexec_sound:
  forall c s s' S,
  ST.In s S -> cexec s c s' -> ST.In s' (Cexec c S).
Proof.
Opaque niter_down.
  induction c; intros s s' S PRE EXEC; cbn.
- (* SKIP *)
  inversion EXEC; subst. auto.
- (* ASSIGN *)
  inversion EXEC; subst. apply ST.set_1; auto. apply Aeval_sound; auto.
- (* SEQ *)
  inversion EXEC; subst. eauto.
- (* IFTHENELSE *)
  inversion EXEC; subst. destruct (beval b s) eqn:B.
  apply ST.join_1. eapply IHc1; eauto. apply assume_test_sound; auto.
  apply ST.join_2. eapply IHc2; eauto. apply assume_test_sound; auto.
- (* WHILE *)
  set (F := fun X => ST.join S (Cexec c (assume_test b true X))).
  set (X := postfixpoint F).
  assert (L : ST.le (F X) X) by (apply postfixpoint_sound).
  assert (REC: forall s1 c1 s2,
               cexec s1 c1 s2 ->
               c1 = WHILE b c ->
               ST.In s1 X ->
               ST.In s2 (assume_test b false X)).
  { induction 1; intro EQ; inversion EQ; subst; intros.
  - (* WHILE done *)
    apply assume_test_sound; auto.
  - (* WHILE loop *)
    apply IHcexec2; auto. apply L. unfold F. apply ST.join_2.
    eapply IHc; eauto. apply assume_test_sound; auto.
  }
  eapply REC; eauto. apply L. unfold F. apply ST.join_1. auto.
Qed.

End Analysis.

(** ** 5.7.  An improved abstract domain for stores *)

(** We start from the abstract domain in module [AbstrInterp], section 5.3,
    and add the widening operator and its properties. *)

Module IdentMap := AbstrInterp.IdentMap.
Module IMFact := AbstrInterp.IMFact.
Module IMProp := AbstrInterp.IMProp.

Module StoreAbstr (VA: VALUE_ABSTRACTION) <: STORE_ABSTRACTION.

Module V := VA.

Inductive abstr_state : Type :=
  | Bot
  | Top_except (m: IdentMap.t V.t).

Definition t := abstr_state.

Definition get (x: ident) (S: t) : V.t :=
  match S with
  | Bot => V.bot
  | Top_except m =>
      match IdentMap.find x m with
      | None => V.top
      | Some v => v
      end
  end.

Definition In (s: store) (S: t) : Prop :=
  forall x, V.In (s x) (get x S).

Definition set (x: ident) (N: V.t) (S: t): t :=
  if V.ble N V.bot then Bot else 
  match S with
  | Bot => Bot
  | Top_except m => Top_except (IdentMap.add x N m)
  end.

Lemma set_1:
  forall x n N s S,
  V.In n N -> In s S -> In (update x n s) (set x N S).
Proof.
  unfold In, get, set; intros.
  destruct (V.ble N V.bot) eqn:BLE; [ | destruct S ].
- apply V.ble_1 in BLE. apply BLE in H. elim (V.bot_1 n); auto. 
- elim (V.bot_1 (s "")). auto. 
- rewrite IMFact.add_o. change IdentMap.E.eq_dec with string_dec. unfold update.
  destruct (string_dec x x0); auto.
Qed. 

(** The order between abstract states. *)

Definition le (S1 S2: t) : Prop :=
  forall s, In s S1 -> In s S2.

Definition ble (S1 S2: t) : bool :=
  match S1, S2 with
  | Bot, _ => true
  | _, Bot => false
  | Top_except m1, Top_except m2 =>
      IMProp.for_all (fun x v => V.ble (get x S1) v) m2
  end.

Lemma ble_1: forall S1 S2, ble S1 S2 = true -> le S1 S2.
Proof.
  unfold ble, le; intros.
  destruct S1 as [ | m1].
- elim (V.bot_1 (s "")). apply H0. 
- destruct S2 as [ | m2]. discriminate.
  red; cbn; intros. destruct (IdentMap.find x m2) as [N2|] eqn:F2.
  + apply IdentMap.find_2 in F2. eapply IMProp.for_all_iff in H; eauto.
    apply V.ble_1 in H. apply H. apply H0.
    hnf. intros; subst x0. hnf; intros. subst x0. auto.
  + apply V.top_1.
Qed.

Lemma ble_false: forall s1 s2,
  s2 <> Bot -> ble s1 s2 = false -> exists x, V.ble (get x s1) (get x s2) = false.
Proof.
  unfold ble; intros. 
  destruct s1 as [ | m1]. discriminate. destruct s2 as [ | m2]. congruence.
- set (p := fun (x: IdentMap.key) v => V.ble (get x (Top_except m1)) v) in *.
  set (m' := IMProp.filter (fun x v => negb (p x v)) m2).
  destruct (IdentMap.elements m') as [ | [x1 v1] l1] eqn:ELT.
+ assert (IMProp.for_all p m2 = true).
  { apply IMProp.for_all_iff.
    repeat (hnf; intros). congruence. 
    intros. destruct (p k e) eqn:P; auto.
    assert (M: IdentMap.MapsTo k e m').
    { apply IMProp.filter_iff.
      repeat (hnf; intros). congruence. 
      rewrite P; auto. }
    apply IdentMap.elements_1 in M. rewrite ELT in M. inversion M.
  }
  congruence.
+ assert (M: IdentMap.MapsTo x1 v1 m').
  { apply IdentMap.elements_2. rewrite ELT. constructor. hnf; auto. }
  apply IMProp.filter_iff in M. destruct M as [M N]. apply negb_true_iff in N.
  exists x1. unfold get at 2. erewrite IdentMap.find_1 by eauto. exact N.
  repeat (hnf; intros). congruence.
Qed.

(** The lattice operations. *)

Definition bot: t := Bot.

Lemma bot_1: forall s, ~(In s bot).
Proof.
  unfold In; cbn. intros s IN. apply (V.bot_1 (s "")). apply IN.
Qed.

Definition top: t := Top_except (IdentMap.empty V.t).

Lemma top_1: forall s, In s top.
Proof.
  unfold In, top, get; cbn. intros. apply V.top_1.
Qed. 

Definition join_aux (ov1 ov2: option V.t) : option V.t :=
  match ov1, ov2 with
  | Some v1, Some v2 => Some (V.join v1 v2)
  | _, _ => None
  end.

Definition join (S1 S2: t) : t :=
  match S1, S2 with
  | Bot, _ => S2
  | _, Bot => S1
  | Top_except m1, Top_except m2 =>
      Top_except (IdentMap.map2 join_aux m1 m2)
  end.

Lemma join_1:
  forall s S1 S2, In s S1 -> In s (join S1 S2).
Proof.
  unfold join; intros.
  destruct S1 as [ | m1]. elim (bot_1 s); auto.
  destruct S2 as [ | m2]. auto.
- red; unfold get; intros. rewrite IMFact.map2_1bis; auto.
  unfold join_aux. specialize (H x). unfold get in H.
  destruct (IdentMap.find x m1). 
  + destruct (IdentMap.find x m2).
    * apply V.join_1; auto.
    * apply V.top_1.
  + apply V.top_1.
Qed.

Lemma join_2:
  forall s S1 S2, In s S2 -> In s (join S1 S2).
Proof.
  unfold join; intros.
  destruct S1 as [ | m1]. auto.
  destruct S2 as [ | m2]. elim (bot_1 s); auto.
- red; unfold get; intros. rewrite IMFact.map2_1bis; auto.
  unfold join_aux. specialize (H x). unfold get in H.
  destruct (IdentMap.find x m1). 
  + destruct (IdentMap.find x m2).
    * apply V.join_2; auto.
    * apply V.top_1.
  + apply V.top_1.
Qed.

(** The widening operator.  We apply pointwise the [V.widen] widening
    provided by the value domain, with default cases for variables
    not described in the map, which are implicitly set to [V.top]. *)

Definition widen_aux (ov1 ov2: option V.t) : option V.t :=
  match ov1, ov2 with
  | Some v1, Some v2 => Some (V.widen v1 v2)
  | None, _ => None
  | _, None => None
  end.

Definition widen (s1 s2: t) : t :=
  match s1, s2 with
  | Bot, _ => s2
  | _, Bot => s1
  | Top_except m1, Top_except m2 => Top_except (IdentMap.map2 widen_aux m1 m2)
  end.

Lemma widen_1: forall s1 s2, le s1 (widen s1 s2).
Proof.
  unfold le, widen; intros.
  destruct s1 as [ | m1]. elim (bot_1 _ H).
  destruct s2 as [ | m2]. auto. 
  red; unfold get; intros. specialize (H x); cbn in H.
  rewrite IMFact.map2_1bis; auto. unfold widen_aux.
  destruct (IdentMap.find x m1); destruct (IdentMap.find x m2);
  auto using V.top_1.
  apply V.widen_1; auto.
Qed.

(** Constructing a well-founded order that guarantees termination is difficult.
    We start by defining a measure with nonnegative integer values
    for a finite map [IdentMap.t V.t].  This measure is the sum
    of the measures of the abstract values in the codomain of this
    finite map. *)

Definition measure_map (m: IdentMap.t V.t) : nat :=
  IdentMap.fold (fun x v n => (V.measure v + n)%nat) m 0%nat.

Remark measure_map_empty:
  forall m, IdentMap.Empty m -> measure_map m = 0%nat.
Proof.
  intros. apply IMProp.fold_Empty; auto.
Qed.

Remark measure_map_add:
  forall m x v m', ~IdentMap.In x m -> IMProp.Add x v m m' ->
  measure_map m' = (V.measure v + measure_map m)%nat.
Proof.
  intros. unfold measure_map; eapply IMProp.fold_Add with (f := fun x v n => (V.measure v + n)%nat); eauto.
  repeat (hnf; intros). congruence.
  hnf; intros. lia.
Qed.

Remark measure_map_remove:
  forall m x,
  measure_map m = (V.measure (get x (Top_except m)) + measure_map (IdentMap.remove x m))%nat.
Proof.
  intros. unfold get. destruct (IdentMap.find x m) as [v|] eqn:F.
- apply measure_map_add with x.
  apply IMFact.not_find_in_iff. rewrite IMFact.remove_eq_o; auto.
  red; intros. rewrite IMFact.add_o, IMFact.remove_o. 
  destruct (AbstrInterp.IdentMap.E.eq_dec x y); congruence.
- rewrite V.measure_top. unfold measure_map. eapply IMProp.fold_Equal. auto.
  repeat (hnf; intros). congruence.
  hnf; intros; lia.
  red; intros. rewrite IMFact.remove_o. 
  destruct (AbstrInterp.IdentMap.E.eq_dec x y); congruence.
Qed.

Lemma measure_map_le: forall m1 m2,
  (forall x, V.measure (get x (Top_except m1)) <= V.measure (get x (Top_except m2)))%nat ->
  (measure_map m1 <= measure_map m2)%nat.
Proof.
  intros m0. pattern m0. unfold measure_map at 1; apply IMProp.fold_rec.
- intros m EMPTY m2 LE. lia.
- intros x v1 n m' m'' MAP NOTIN ADD REC m2 LE.
  set (m2' := IdentMap.remove x m2).
  assert (LE': forall x, (V.measure (get x (Top_except m')) <= V.measure (get x (Top_except m2')))%nat).
  { intros y. generalize (LE y). unfold get, m2'. rewrite ADD, IMFact.add_o, IMFact.remove_o.
    destruct (AbstrInterp.IdentMap.E.eq_dec x y).
    + subst y. apply IMFact.not_find_in_iff in NOTIN. rewrite NOTIN. rewrite ! V.measure_top. lia.
    + auto. }
  apply REC in LE'.
  rewrite (measure_map_remove m2 x). fold m2'.
  specialize (LE x). unfold get at 1 in LE. rewrite ADD, IMFact.add_eq_o in LE by auto.
  lia.  
Qed.

Lemma measure_map_lt: forall m1 m2,
  (forall x, V.measure (get x (Top_except m1)) <= V.measure (get x (Top_except m2)))%nat ->
  (exists x, V.measure (get x (Top_except m1)) < V.measure (get x (Top_except m2)))%nat ->
  (measure_map m1 < measure_map m2)%nat.
Proof.
  intros m1 m2 LE (x & LT).
  rewrite (measure_map_remove m1 x), (measure_map_remove m2 x).
  assert ((measure_map (IdentMap.remove x m1) <= measure_map (IdentMap.remove x m2))%nat).
  { apply measure_map_le.
    intros y; unfold get. rewrite ! IMFact.remove_o.
    destruct (AbstrInterp.IdentMap.E.eq_dec x y).
    lia.
    apply LE. }
  lia.
Qed.

(** We then show that this measure strictly decreases during a widening
    step that does not mention [Bot]. *)

Lemma measure_widen_lt: forall m1 m2,
  ble (Top_except m2) (Top_except m1) = false ->
  (measure_map (IdentMap.map2 widen_aux m1 m2) < measure_map m1)%nat.
Proof.
  intros. apply ble_false in H. 2: congruence. destruct H as (x & BL).
  apply measure_map_lt.
- intros y. unfold get. rewrite IMFact.map2_1bis by auto. unfold widen_aux.
  destruct (IdentMap.find y m1) as [ v1 |].
  destruct (IdentMap.find y m2) as [ v2 |].
  apply V.widen_2.
  rewrite V.measure_top; lia.
  rewrite V.measure_top; lia.
- exists x. unfold get in *. rewrite IMFact.map2_1bis by auto. unfold widen_aux.
  destruct (IdentMap.find x m1) as [ v1 |].
  destruct (IdentMap.find x m2) as [ v2 |].
  apply V.widen_3 in BL; auto.
  apply V.widen_3 in BL; rewrite V.measure_top; lia.
  assert (T: forall z, V.ble z V.top = true).
  { intros. apply V.ble_2. red; intros. apply V.top_1. }
  rewrite T in BL. congruence.
Qed.

(** We conclude that the widening order is well founded. *)

Definition widen_order (S S1: t) := exists S2, S = widen S1 S2 /\ ble S2 S1 = false.

Lemma widen_order_wf: well_founded widen_order.
Proof.
  assert (A: forall m, Acc widen_order (Top_except m)).
  { induction m using (well_founded_ind (well_founded_ltof _ measure_map)).
    constructor. intros S (S2 & EQ & BLE). subst S.
    destruct S2. discriminate. apply H. apply measure_widen_lt. auto. }
  assert (B: Acc widen_order Bot).
  { constructor. intros S (S2 & EQ & BLE). subst S. 
    unfold ble in BLE. destruct S2. discriminate. apply A. }
  red. destruct a; auto.
Defined.

End StoreAbstr.

(** ** 5.8.  The abstract domain of intervals *)

(** We first define the type [zinf] of integers complemented with a
    "plus infinity" value. *)

Inductive zinf : Type := Fin (h: Z) | Inf.

Coercion Fin : Z >-> zinf.

Module Zinf.
  Definition In (n: Z) (N: zinf) : Prop :=
    match N with Fin h => n <= h | Inf => True end.

  Lemma In_mono: forall n1 n2 N, n1 <= n2 -> In n2 N -> In n1 N.
  Proof.
    unfold In; destruct N; intros. lia. auto.
  Qed.

  Definition le (N1 N2: zinf) : Prop :=
    forall n, In n N1 -> In n N2.

  Lemma le_Fin: forall n1 N2, le (Fin n1) N2 <-> In n1 N2.
  Proof.
    unfold le; cbn; intros; split; intros.
  - apply H. lia.
  - destruct N2; cbn in *; auto. lia.
  Qed.

  Lemma le_is_Inf: forall N h, (forall n, h <= n -> In n N) -> N = Inf.
  Proof.
    destruct N; cbn; intros; auto.
    specialize (H (Z.max h0 (h + 1))). lia.
  Qed.

  Lemma le_Inf: forall N, le Inf N <-> N = Inf.
  Proof.
    unfold le; intros; split; intros.
  - apply le_is_Inf with 0. intros; apply H; exact I.
  - subst N; exact I.
  Qed. 

  Definition ble (N1 N2: zinf) : bool :=
    match N1, N2 with _, Inf => true | Inf, _ => false | Fin h1, Fin h2 => h1 <=? h2 end.

  Lemma ble_1: forall N1 N2, ble N1 N2 = true -> le N1 N2.
  Proof.
    unfold ble, le, In; intros.
    destruct N1, N2; auto.
    apply Z.leb_le in H. lia.
    discriminate.
  Qed.

  Lemma ble_2: forall N1 N2, le N1 N2 -> ble N1 N2 = true.
  Proof.
    unfold ble; intros. destruct N1.
  - apply le_Fin in H. destruct N2; auto. apply Z.leb_le; auto.
  - apply le_Inf in H. rewrite H. auto.
  Qed.

  Definition max (N1 N2: zinf) : zinf :=
    match N1, N2 with Inf, _ => Inf | _, Inf => Inf | Fin h1, Fin h2 => Fin (Z.max h1 h2) end.

  Lemma max_1: forall n N1 N2, In n N1 -> In n (max N1 N2).
  Proof.
    unfold In, max; intros. destruct N1; auto. destruct N2; auto. lia.
  Qed.

  Lemma max_2: forall n N1 N2, In n N2 -> In n (max N1 N2).
  Proof.
    unfold In, max; intros. destruct N1; auto. destruct N2; auto. lia.
  Qed.

  Definition min (N1 N2: zinf) : zinf :=
    match N1, N2 with Inf, _ => N2 | _, Inf => N1 | Fin h1, Fin h2 => Fin (Z.min h1 h2) end.

  Lemma min_1: forall n N1 N2, In n N1 -> In n N2 -> In n (min N1 N2).
  Proof.
    unfold In, min; intros. destruct N1; auto. destruct N2; auto. lia.
  Qed.

  Definition add (N1 N2: zinf) : zinf :=
    match N1, N2 with Inf, _ => Inf | _, Inf => Inf | Fin h1, Fin h2 => Fin (h1 + h2) end.

  Lemma add_1: forall n1 n2 N1 N2, In n1 N1 -> In n2 N2 -> In (n1 + n2) (add N1 N2).
  Proof.
    unfold In, add; intros. destruct N1; auto. destruct N2; auto. lia.
  Qed.

  Definition isIn (n: Z) (N: zinf) : bool :=
    match N with Fin h => n <=? h | Inf => true end.

  Lemma isIn_1:
    forall n N, In n N -> isIn n N = true.
  Proof.
    unfold In, isIn; intros. destruct N; auto. apply Z.leb_le; auto.
  Qed.

  Definition pred (N: zinf) : zinf :=
    match N with Inf => Inf | Fin n => Fin (n - 1) end.

  Lemma pred_1: forall n N, In n N -> In (n - 1) (pred N).
  Proof.
    unfold pred, In; intros; destruct N; auto. lia.
  Qed.

(** We define widening between two possibly infinite integers as follows:
    if the integer increases strictly, we jump to infinity, otherwise
    we keep the first integer. *)

  Definition widen (N1 N2: zinf) : zinf :=
     if ble N2 N1 then N1 else Inf.

  Lemma widen_1: forall N1 N2, le N1 (widen N1 N2).
  Proof.
    unfold widen; intros. destruct (ble N2 N1) eqn:LE.
    red; auto.
    red; unfold In; auto.
  Qed.

  Definition measure (N: zinf) : nat :=
    match N with Inf => 0%nat | Fin _ => 1%nat end.

  Lemma measure_1: forall N, (measure N <= 1)%nat.
  Proof.
    destruct N; cbn; lia.
  Qed.

  Lemma widen_2:
    forall N1 N2, (measure (widen N1 N2) <= measure N1)%nat.
  Proof.
    intros. unfold widen. destruct (ble N2 N1) eqn:BLE.
  - lia.
  - destruct N1. cbn; lia. destruct N2; discriminate.
  Qed.

  Lemma widen_3: 
    forall N1 N2, ble N2 N1 = false -> (measure (widen N1 N2) < measure N1)%nat.
  Proof.
    destruct N1, N2; cbn; intros; auto; try discriminate. 
    unfold widen. cbn. rewrite H. cbn. lia.
  Qed.

End Zinf.

(** An interval is encoded as a pair of two [zinf].
    The second [zinf] is the upper bound.
    The first [zinf] is the opposite of the lower bound.
    This representation trick makes it possible to have only one
    infinity [Inf], instead of a negative infinity for lower bounds
    and a positive infinity for upper bounds. *)

Module Intervals <: VALUE_ABSTRACTION.

(** The type of abstract values. *)
  Record interval : Type := intv { low: zinf; high: zinf }.
  Definition t := interval.

(** Membership: [n] must be below the upper bound, and the opposite of [n]
    must be below the opposite of the lower bound. *)

  Definition In (n: Z) (N: t) : Prop :=
    Zinf.In n (high N) /\ Zinf.In (-n) (low N).

  Definition le (N1 N2: t) : Prop :=
    forall n, In n N1 -> In n N2.

(** Test whether an interval is empty. *)

  Definition isempty (N: t) : bool :=
    match N with 
    | {| low := Fin l; high := Fin h |} => h <? (-l)
    | _ => false
    end.

  Lemma isempty_1: forall n N, isempty N = true -> In n N -> False.
  Proof.
    unfold isempty, In; intros. destruct N as [[l|] [h|]]; try discriminate.
    apply Z.ltb_lt in H. cbn in H0. lia.
  Qed.

  Lemma isempty_2: forall N, isempty N = false -> exists n, In n N.
  Proof.
    unfold isempty, In; intros. destruct N as [[l|] [h|]]; cbn.
  - apply Z.ltb_ge in H. exists h; lia.
  - exists (- l); lia.
  - exists h; lia.
  - exists 0; auto.
  Qed.

  Lemma nonempty_le: forall N1 N2,
    le N1 N2 -> isempty N1 = false -> (Zinf.le (high N1) (high N2) /\ Zinf.le (low N1) (low N2)).
  Proof.
    unfold le, In, isempty; intros.
    destruct N1 as [[l1 |] [h1|]]; cbn in *; rewrite ? Zinf.le_Fin, ? Zinf.le_Inf.
  - apply Z.ltb_ge in H0. split.
    + apply H; lia.
    + replace l1 with (- - l1) by lia. apply H. lia.
  - split.
    + apply Zinf.le_is_Inf with (-l1). intros; apply H. intuition lia.
    + replace l1 with (- - l1) by lia. apply H. intuition lia.
  - split.
    + apply H. intuition lia.
    + apply Zinf.le_is_Inf with(- h1).
      intros. replace n with (- - n) by lia. apply H. intuition lia.
  - split; apply Zinf.le_is_Inf with 0; intros.
    + apply H; auto.
    + replace n with (- - n) by lia. apply H. auto.
  Qed.

(** [ble] is a Boolean-valued function that decides the [le] relation. *)

  Definition ble (N1 N2: t) : bool :=
    isempty N1 || (Zinf.ble (high N1) (high N2) && Zinf.ble (low N1) (low N2)).

  Lemma ble_1: forall N1 N2, ble N1 N2 = true -> le N1 N2.
  Proof.
    unfold ble, le, In; intros.
    destruct (isempty N1) eqn:E.
    elim (isempty_1 _ _ E H0).
    apply andb_prop in H. destruct H as [B1 B2].
    apply Zinf.ble_1 in B1. apply Zinf.ble_1 in B2.
    intuition.
  Qed.

  Lemma ble_2: forall N1 N2, le N1 N2 -> ble N1 N2 = true.
  Proof.
    unfold ble; intros. destruct (isempty N1) eqn:E; auto.
    destruct (nonempty_le N1 N2) as [P Q]; auto.
    apply andb_true_intro; split; apply Zinf.ble_2; auto.
  Qed.

(** [const n] is the abstract value for the singleton set [{n}]. *)
  Definition const (n: Z) : t := {| low := Fin (-n); high := Fin n |}.

  Lemma const_1: forall n, In n (const n).
  Proof.
    unfold const, In, Zinf.In; intros; cbn. lia.
  Qed.

(** [bot] represents the empty set. *)
  Definition bot: t := {| low := Fin 0; high := Fin (-1) |}.

  Lemma bot_1: forall n, ~(In n bot).
  Proof.
    unfold bot, In, Zinf.In; intros; cbn. lia.
  Qed.

(** [top] represents the set of all integers. *)
  Definition top: t := {| low := Inf; high := Inf |}.

  Lemma top_1: forall n, In n top.
  Proof.
    intros. split; exact I.
  Qed.

(** [join] computes an upper bound of its two arguments. *)
  Definition join (N1 N2: t) : t :=
    {| low := Zinf.max (low N1) (low N2);
       high := Zinf.max (high N1) (high N2) |}.

  Lemma join_1:
    forall n N1 N2, In n N1 -> In n (join N1 N2).
  Proof.
    unfold In, join; intros; cbn. split; apply Zinf.max_1; tauto.
  Qed.

  Lemma join_2:
    forall n N1 N2, In n N2 -> In n (join N1 N2).
  Proof.
    unfold In, join; intros; cbn. split; apply Zinf.max_2; tauto.
  Qed.

(** The abstract operators for addition and subtraction. *)

  Definition add (N1 N2: t) : t :=
    if isempty N1 || isempty N2 then bot else
    {| low := Zinf.add (low N1) (low N2);
       high := Zinf.add (high N1) (high N2) |}.

  Lemma add_1:
    forall n1 n2 N1 N2, In n1 N1 -> In n2 N2 -> In (n1 + n2) (add N1 N2).
  Proof.
    unfold add; intros.
    destruct (isempty N1) eqn:E1. elim (isempty_1 n1 N1); auto.
    destruct (isempty N2) eqn:E2. elim (isempty_1 n2 N2); auto.
    destruct H; destruct H0; split; cbn.
    apply Zinf.add_1; auto.
    replace (- (n1 + n2)) with ((-n1) + (-n2)) by lia. apply Zinf.add_1; auto.
  Qed.

  Definition opp (v: t) : t := {| low := high v; high := low v |}.

  Lemma opp_1:
    forall n v, In n v -> In (-n) (opp v).
  Proof.
    unfold In, opp; intros; cbn. replace (- - n) with n by lia. tauto.
  Qed.

  Definition sub (N1 N2: t) : t := add N1 (opp N2).

  Lemma sub_1:
    forall n1 n2 N1 N2, In n1 N1 -> In n2 N2 -> In (n1 - n2) (sub N1 N2).
  Proof.
    intros. apply add_1; auto. apply opp_1; auto.
  Qed.

(** [meet] computes a lower bound for its two arguments.*)
  Definition meet (N1 N2: t) : t :=
    {| low := Zinf.min (low N1) (low N2);
       high := Zinf.min (high N1) (high N2) |}.

  Lemma meet_1:
    forall n N1 N2, In n N1 -> In n N2 -> In n (meet N1 N2).
  Proof.
    unfold In, meet; intros; cbn. split; apply Zinf.min_1; tauto. 
  Qed.

(** [isIn] tests whether a concrete value belongs to an abstract value. *)
  Definition isIn (n: Z) (v: t) : bool :=
    Zinf.isIn n (high v) && Zinf.isIn (-n) (low v).

  Lemma isIn_1:
    forall n v, In n v -> isIn n v = true.
  Proof.
    unfold In, isIn; intros.
    apply andb_true_intro; split; apply Zinf.isIn_1; tauto. 
  Qed.

(** Abstract operators for inverse analysis of comparisons. *)

  Definition eq_inv (N1 N2: t) : t * t := (meet N1 N2, meet N1 N2).

  Lemma eq_inv_1:
    forall n1 n2 a1 a2,
    In n1 a1 -> In n2 a2 -> n1 = n2 ->
    In n1 (fst (eq_inv a1 a2)) /\ In n2 (snd (eq_inv a1 a2)).
  Proof.
    intros; cbn. subst n2. split; apply meet_1; auto.
  Qed.

  Definition ne_inv (N1 N2: t) : t * t := (N1, N2).

  Lemma ne_inv_1:
    forall n1 n2 a1 a2,
    In n1 a1 -> In n2 a2 -> n1 <> n2 ->
    In n1 (fst (ne_inv a1 a2)) /\ In n2 (snd (ne_inv a1 a2)).
  Proof.
    intros; cbn; auto.
  Qed.

(** For the [<=] comparison, the upper bound of [N1] is at most that of [N2],
    and the lower bound of [N2] is at least that of [N1]. *)

  Definition le_inv (N1 N2: t) : t * t :=
    ( {| low := low N1; high := Zinf.min (high N1) (high N2) |},
      {| low := Zinf.min (low N1) (low N2); high := high N2 |} ).

  Lemma le_inv_1:
    forall n1 n2 a1 a2,
    In n1 a1 -> In n2 a2 -> n1 <= n2 ->
    In n1 (fst (le_inv a1 a2)) /\ In n2 (snd (le_inv a1 a2)).
  Proof.
    unfold In, le_inv; intros; cbn.
    intuition auto; apply Zinf.min_1; auto.
    apply Zinf.In_mono with n2; auto.
    apply Zinf.In_mono with (-n1); auto. lia.
  Qed.

(** For the [>] comparison, the upper bound of [N1] is at least that of [N2],
    and the lower bound of [N2] is at most that of [N1] - 1. *)

  Definition gt_inv (N1 N2: t) : t * t :=
    ( {| low := Zinf.min (low N1) (Zinf.pred (low N2)); high := high N1 |},
      {| low := low N2; high := Zinf.min (high N2) (Zinf.pred (high N1)) |} ).

  Lemma gt_inv_1:
    forall n1 n2 a1 a2,
    In n1 a1 -> In n2 a2 -> n1 > n2 ->
    In n1 (fst (gt_inv a1 a2)) /\ In n2 (snd (gt_inv a1 a2)).
  Proof.
    unfold In, gt_inv; intros; cbn.
    intuition auto; apply Zinf.min_1; auto.
    apply Zinf.In_mono with ((-n2) - 1). lia. apply Zinf.pred_1; auto.
    apply Zinf.In_mono with (n1 - 1). lia. apply Zinf.pred_1; auto.
  Qed.

(** The widening operator. *)

  Definition widen (N1 N2: t) : t :=
    if isempty N1 then N2 else
    if isempty N2 then N1 else
    {| low := Zinf.widen (low N1) (low N2); high := Zinf.widen (high N1) (high N2) |}.

  Lemma widen_1: forall N1 N2, le N1 (widen N1 N2).
  Proof.
    unfold le, widen; intros.
    destruct (isempty N1) eqn:E1. elim (isempty_1 n N1); auto.
    destruct (isempty N2) eqn:E2. auto.
    destruct H. split; apply Zinf.widen_1; auto.
  Qed.

  Definition measure (v: t) : nat :=
    if isempty v then 3%nat else (Zinf.measure (low v) + Zinf.measure (high v))%nat.

  Lemma measure_top: measure top = 0%nat.
  Proof.
    auto.
  Qed.

  Remark isempty_widen: forall N1 N2,
    isempty N1 = false -> isempty N2 = false -> isempty (widen N1 N2) = false.
  Proof.
    intros. destruct (isempty (widen N1 N2)) eqn:E; auto.
    destruct (isempty_2 _ H) as (n1 & IN1).
    elim (isempty_1 n1 _ E). apply widen_1; auto.
  Qed.
  
  Lemma widen_2: 
    forall N1 N2, (measure (widen N1 N2) <= (measure N1))%nat.
  Proof.
    unfold measure; intros.
    destruct (isempty N1) eqn:E1. unfold widen; rewrite E1.
    generalize (Zinf.measure_1 (low N2)) (Zinf.measure_1 (high N2)); intros.
    destruct (isempty N2); lia.
    destruct (isempty N2) eqn:E2. unfold widen; rewrite E1, E2, E1. lia.
    rewrite isempty_widen by auto.
    unfold widen; rewrite E1, E2; cbn.
    generalize (Zinf.widen_2 (low N1) (low N2)) (Zinf.widen_2 (high N1) (high N2)). lia.
  Qed.

  Lemma widen_3: 
    forall N1 N2, ble N2 N1 = false -> (measure (widen N1 N2) < measure N1)%nat.
  Proof.
    unfold ble, measure; intros.
    destruct (isempty N2) eqn:E2. discriminate.
    destruct (isempty N1) eqn:E1.
  - unfold widen; rewrite E1, E2.
    generalize (Zinf.measure_1 (low N2)) (Zinf.measure_1 (high N2)). lia.
  - rewrite isempty_widen by auto.
    unfold widen; rewrite E1, E2. cbn.
    generalize (Zinf.widen_2 (low N1) (low N2)) (Zinf.widen_2 (high N1) (high N2)); intros.
    destruct (Zinf.ble (high N2) (high N1)) eqn:LE.
    + cbn in H. apply Zinf.widen_3 in H. lia.
    + apply Zinf.widen_3 in LE. lia.
  Qed.

End Intervals.

(** ** 5.9.  Application: an interval analysis for IMP *)

(** We instantiate the generic analyzer with the domain of intervals. *)

Module SIntervals := StoreAbstr(Intervals).
Module AIntervals := Analysis(SIntervals).

(** First program:
<<
    x := 0; y := 100; z := x + y;
    while x <= 10 do x := x + 1; y := y - 1 end
>>
*)

Definition prog1 :=
  ASSIGN "x" (CONST 0) ;;
  ASSIGN "y" (CONST 100) ;;
  ASSIGN "z" (PLUS (VAR "x") (VAR "y")) ;;
  WHILE (LESSEQUAL (VAR "x") (CONST 10))
        (ASSIGN "x" (PLUS (VAR "x") (CONST 1)) ;;
         ASSIGN "y" (MINUS (VAR "y") (CONST 1))).

Compute (let S := AIntervals.Cexec prog1 SIntervals.top in
           (SIntervals.get "x" S, SIntervals.get "y" S, SIntervals.get "z" S)).

(** Analysis result:
<<
      ({| Intervals.low := -11; Intervals.high := 11 |},
       {| Intervals.low := Inf; Intervals.high := 100 |},
       {| Intervals.low := -100; Intervals.high := 100 |})
>>
In other words: [x] is in [[11,11]], [y] in [[-inf,100]], and [z] in [[100,100]].
*)

(** Second program:
<<
    x := 0; y := 0;
    while x <= 1000 do y := x; x := x + 1 end
>>
*)

Definition prog2 :=
  ASSIGN "x" (CONST 0) ;;
  ASSIGN "y" (CONST 0) ;;
  WHILE (LESSEQUAL (VAR "x") (CONST 1000))
    (ASSIGN "y" (VAR "x") ;;
     ASSIGN "x" (PLUS (VAR "x") (CONST 1))).

Compute (let S := AIntervals.Cexec prog2 SIntervals.top in
           (SIntervals.get "x" S, SIntervals.get "y" S)).

(** Analysis result:
<<
      ({| Intervals.low := -1001; Intervals.high := 1001 |},
       {| Intervals.low := 0; Intervals.high := 1000 |})
>>
In other words: [x] is in [[1001,1001]], and [y] in [[0,1000]].
*)
