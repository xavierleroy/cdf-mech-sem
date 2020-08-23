From Coq Require Import ZArith Psatz Bool String List FMaps.
From CDF Require Import Sequences IMP.

Local Open Scope string_scope.
Local Open Scope Z_scope.

(** * 5.  Static analysis by abstract interpretation, simplified version *)

(** ** 5.1.  Interface of abstract domains *)

(** The analyzer computes over abstract values: approximations of sets
    of integer values.  The type of abstract values and the associated
    operations are grouped in a Coq module, whose interface follows. *)

Module Type VALUE_ABSTRACTION.

(** The type of abstract values. *)
  Parameter t: Type.

(** [In n N] holds if integer [n] belongs to the set represented by
    abstract value [N].  This is equivalent to the concretization
    function [γ] : [In n N] means [n ∈ γ(N)]. *)
  Parameter In: Z -> t -> Prop.

(** Abstract values are ordered by inclusion of the sets they represent. *)
  Definition le (N1 N2: t) : Prop := forall n, In n N1 -> In n N2.

(** [ble] is a Boolean-valued function that decides the [le] relation. *)
  Parameter ble: t -> t -> bool.
  Axiom ble_1: forall N1 N2, ble N1 N2 = true -> le N1 N2.
  Axiom ble_2: forall N1 N2, le N1 N2 -> ble N1 N2 = true.

(** [const n] is the abstract value for the singleton set [{n}]. *)
  Parameter const: Z -> t.
  Axiom const_1: forall n, In n (const n).

(** [bot] represents the empty set. *)
  Parameter bot: t.
  Axiom bot_1: forall n, ~(In n bot).

(** [top] represents the set of all integers. *)
  Parameter top: t.
  Parameter top_1: forall n, In n top.

(** [join] computes an upper bound of its two arguments. *)
  Parameter join: t -> t -> t.
  Axiom join_1: forall n N1 N2, In n N1 -> In n (join N1 N2).
  Axiom join_2: forall n N1 N2, In n N2 -> In n (join N1 N2).

(** Abstract operators for addition and subtraction. *)
  Parameter add: t -> t -> t.
  Axiom add_1:
    forall n1 n2 N1 N2, In n1 N1 -> In n2 N2 -> In (n1+n2) (add N1 N2).

  Parameter sub: t -> t -> t.
  Axiom sub_1:
    forall n1 n2 N1 N2, In n1 N1 -> In n2 N2 -> In (n1-n2) (sub N1 N2).

End VALUE_ABSTRACTION.

(** Store abstractions are defined in the same style: a module
    that defines a type [t] of abstract stores and the associated
    abstract operations.  Here is the interface of this module. *)

Module Type STORE_ABSTRACTION.

(** A value abstraction for integer values. *)
  Declare Module V: VALUE_ABSTRACTION.

(** The type of abstract stores. *)
  Parameter t: Type.

(** [get x S] is the abstract value associated with [x] in [S]. *)
  Parameter get: ident -> t -> V.t.

(** Whether a concrete store belongs to an abstract store. *)
  Definition In (s: store) (S: t) : Prop :=
    forall x, V.In (s x) (get x S).

(** Abstract assignment to a variable. *)
  Parameter set: ident -> V.t -> t -> t.
  Axiom set_1:
    forall x n N s S, V.In n N -> In s S -> In (update x n s) (set x N S).

(** The order between abstract stores. *)
  Definition le (S1 S2: t) : Prop := forall s, In s S1 -> In s S2.

  Parameter ble: t -> t -> bool.
  Axiom ble_1: forall S1 S2, ble S1 S2 = true -> le S1 S2.

(** Smallest and greatest abstract stores. *)
  Parameter bot: t.
  Axiom bot_1: forall s, ~(In s bot).

  Parameter top: t.
  Parameter top_1: forall s, In s top.

(** [join] computes an upper bound of its two arguments. *)
  Parameter join: t -> t -> t.
  Axiom join_1: forall s S1 S2, In s S1 -> In s (join S1 S2).
  Axiom join_2: forall s S1 S2, In s S2 -> In s (join S1 S2).

End STORE_ABSTRACTION.

(** ** 5.2.  The generic analyzer *)

(** The analyzer is presented as a module parameterized by a store abstraction,
    the latter containing a value abstraction. *)

Module Analysis (ST: STORE_ABSTRACTION).

Module V := ST.V.

(** *** Computing post-fixed points *)

(** We follow the same approach as in the 3rd lecture, module [Optim]:
    a fixed point iteration that starts from [bot] and stops as soon
    a post-fixed point is found, or when the maximal number of
    iterations is reached.  In the latter case, the result is [top]. *)

Section FIXPOINT.

Variable F: ST.t -> ST.t.

Fixpoint iter (n: nat) (S: ST.t) : ST.t :=
  match n with
  | O => ST.top
  | S n' => let S' := F S in 
            if ST.ble S' S then S else iter n' S'
  end.

Definition niter := 10%nat.

Definition postfixpoint : ST.t := iter niter ST.bot.

Lemma postfixpoint_sound:
  ST.le (F postfixpoint) postfixpoint.
Proof.
  unfold postfixpoint. generalize niter ST.bot. 
  induction n; intros S; cbn.
- red; intros; apply ST.top_1.
- destruct (ST.ble (F S) S) eqn:B.
  + apply ST.ble_1; auto.
  + apply IHn.
Qed.

End FIXPOINT.

(** *** Abstract interpretation of arithmetic operations. *)

Fixpoint Aeval (a: aexp) (S: ST.t) : V.t :=
  match a with
  | CONST n => V.const n
  | VAR x => ST.get x S
  | PLUS a1 a2 => V.add (Aeval a1 S) (Aeval a2 S)
  | MINUS a1 a2 => V.sub (Aeval a1 S) (Aeval a2 S)
  end.

(** This abstract interpretation is sound with respect to the concrete
    semantics of expressions. *)

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

(** *** Abstract interpretation of commands. *)

(** The abstract interpretation of a command [c] is a function
    [ST.t -> ST.t] that computes the abstract store "after" the
    execution of [c] as a function of the abstract store "before".
    Owing to abstraction, this computation always terminates
    and can be defined as a function. *)

Fixpoint Cexec (c: com) (S: ST.t) : ST.t :=
  match c with
  | SKIP => S
  | ASSIGN x a => ST.set x (Aeval a S) S
  | SEQ c1 c2 => Cexec c2 (Cexec c1 S)
  | IFTHENELSE b c1 c2 => ST.join (Cexec c1 S) (Cexec c2 S)
  | WHILE b c => postfixpoint (fun X => ST.join S (Cexec c X))
  end.

(** This abstract interpretation is sound with respect to the IMP
    operational semantics. *)

Theorem Cexec_sound:
  forall c s s' S,
  ST.In s S -> cexec s c s' -> ST.In s' (Cexec c S).
Proof.
Opaque niter.
  induction c; intros s s' S PRE EXEC; cbn.
- (* SKIP *)
  inversion EXEC; subst. auto.
- (* ASSIGN *)
  inversion EXEC; subst. apply ST.set_1; auto. apply Aeval_sound; auto.
- (* SEQ *)
  inversion EXEC; subst. eauto.
- (* IFTHENELSE *)
  inversion EXEC; subst. destruct (beval b s).
  apply ST.join_1; eauto.
  apply ST.join_2; eauto.
- (* WHILE *)
  set (F := fun X => ST.join S (Cexec c X)).
  set (X := postfixpoint F).
  assert (L : ST.le (F X) X) by (apply postfixpoint_sound).
  assert (REC: forall s1 c1 s2,
               cexec s1 c1 s2 ->
               c1 = WHILE b c ->
               ST.In s1 X ->
               ST.In s2 X).
  { induction 1; intro EQ; inversion EQ; subst; intros.
  - (* WHILE done *)
    auto.
  - (* WHILE loop *)
    apply IHcexec2; auto. apply L. unfold F. apply ST.join_2. eapply IHc; eauto.
  }
  eapply REC; eauto. apply L. unfold F. apply ST.join_1. auto.
Qed.

End Analysis.

(** ** 5.3.  An abstract domain for stores *)

(** We now build an abstract domain for stores that can be used
    for all non-relational analyses, in particular all value analyses. *)

(** Morally, abstract stores are functions [ident -> V.t]
    from identifiers to abstract values.  However, the order between
    abstract stores must be decidable, which is not the case if
    abstract stores are arbitrary functions over the infinite type [ident].
    Therefore, we use finite partial functions from [ident] to [V.t],
    implemented using the "maps" provided by Coq's standard library,
    and consider that any identifier not in the domain of the finite
    function is mapped to [V.top]. *)

(** As in file [Optim], we equip the type of identifiers with a decidable
    equality, then instantiate the standard library modules for maps
    on this type. *)

Module Ident_Decidable <: DecidableType with Definition t := ident.
  Definition t := ident.
  Definition eq (x y: t) := x = y.
  Definition eq_refl := @eq_refl t.
  Definition eq_sym := @eq_sym t.
  Definition eq_trans := @eq_trans t.
  Definition eq_dec := string_dec.
End Ident_Decidable.

Module IdentMap := FMapWeakList.Make(Ident_Decidable).
Module IMFact := FMapFacts.WFacts(IdentMap).
Module IMProp := FMapFacts.WProperties(IdentMap).

(** The domain of abstract stores is parameterized by a module [VA]
    defining the abstract values. *)

Module StoreAbstr (VA: VALUE_ABSTRACTION) <: STORE_ABSTRACTION.

Module V := VA.

(** An abstract store is either [Bot], associating [V.bot] to all
    variables, or [Top_except m], associating [V.top] to the variables
    that are not described in the map [m]. *)

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
      | Some N => N
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

(** The inclusion order between abstract stores. *)

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
  | Top_except m1, Top_except m2 => Top_except (IdentMap.map2 join_aux m1 m2)
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

End StoreAbstr.

(** ** 5.4.  An application: constant propagation analysis *)

(** *** The "flat" abstract domain of integers. *)

Module FlatInt <: VALUE_ABSTRACTION.

(** The abstract values: empty set, singleton set, or [Z] as a whole. *)

  Inductive abstr_value : Type := Bot | Just (n: Z) | Top.
  Definition t := abstr_value.

(** Membership and inclusion. *)

  Definition In (n: Z) (N: t) : Prop :=
    match N with
    | Bot => False
    | Just m => n = m
    | Top => True
    end.

  Definition le (N1 N2: t) : Prop :=
    forall n, In n N1 -> In n N2.

  Definition ble (N1 N2: t) : bool :=
    match N1, N2 with
    | Bot, _ => true
    | _, Top => true
    | Just n1, Just n2 => n1 =? n2
    | _, _ => false
    end.

  Lemma ble_1: forall N1 N2, ble N1 N2 = true -> le N1 N2.
  Proof.
    unfold ble, le, In; intros.
    destruct N1; try contradiction; destruct N2; try discriminate; auto.
    apply Z.eqb_eq in H. lia.
  Qed.

  Lemma ble_2: forall N1 N2, le N1 N2 -> ble N1 N2 = true.
  Proof.
    unfold ble, le, In; intros.
    destruct N1; auto.
  - specialize (H n refl_equal). destruct N2. contradiction. apply Z.eqb_eq; auto. auto.
  - destruct N2. elim (H 0); auto. specialize (H (n + 1)); lia. auto.
  Qed.

(** [const n] is the abstract value for the singleton set [{n}]. *)
  Definition const (n: Z) : t := Just n.

  Lemma const_1: forall n, In n (const n).
  Proof.
    intros; cbn; auto.
  Qed.

(** The lattice operations: [bot], [top], [join]. *)

  Definition bot: t := Bot.

  Lemma bot_1: forall n, ~(In n bot).
  Proof.
    intros. cbn. tauto.
  Qed.

  Definition top: t := Top.

  Lemma top_1: forall n, In n top.
  Proof.
    intros. cbn; auto.
  Qed.

  Definition join (N1 N2: t) : t :=
    match N1, N2 with
    | Bot, _ => N2
    | _, Bot => N1
    | Top, _ => Top
    | _, Top => Top
    | Just n1, Just n2 => if n1 =? n2 then Just n1 else Top
    end.

  Lemma join_1:
    forall n N1 N2, In n N1 -> In n (join N1 N2).
  Proof.
    unfold In, join; intros; cbn.
    destruct N1, N2; try tauto.
    destruct (Z.eqb_spec n0 n1); auto.
  Qed.

  Lemma join_2:
    forall n N1 N2, In n N2 -> In n (join N1 N2).
  Proof.
    unfold In, join; intros; cbn.
    destruct N1, N2; try tauto.
    destruct (Z.eqb_spec n0 n1); auto. congruence.
  Qed.

(** The abstract arithmetic operations *)

  Definition lift (f: Z -> Z -> Z) : t -> t -> t :=
    fun N1 N2 =>
      match N1, N2 with
      | Bot, _ => Bot
      | _, Bot => Bot
      | Just n1, Just n2 => Just (f n1 n2)
      | _, _ => Top
    end.

  Lemma lift_1:
    forall f n1 n2 N1 N2, In n1 N1 -> In n2 N2 -> In (f n1 n2) (lift f N1 N2).
  Proof.
    unfold In, lift; intros. destruct N1, N2; try tauto. congruence.
  Qed.

  Definition add := lift Z.add.

  Lemma add_1:
    forall n1 n2 N1 N2, In n1 N1 -> In n2 N2 -> In (n1+n2) (add N1 N2).
  Proof (lift_1 Z.add).

  Definition sub := lift Z.sub.

  Lemma sub_1:
    forall n1 n2 N1 N2, In n1 N1 -> In n2 N2 -> In (n1-n2) (sub N1 N2).
  Proof (lift_1 Z.sub).

End FlatInt.

(** *** The constant propagation analysis *)

(** We just have to instantiate the analyzer on the flat domain of integers
    and on the corresponding store domain. *)

Module SConstProp := StoreAbstr(FlatInt).
Module AConstProp := Analysis(SConstProp).

(** A sample program:
<<
    x := 0; y := 100; z := x + y;
    if x = 0
    then y := x + 10; x := 1
    else y := 10
>>
*)

Definition prog1 :=
  ASSIGN "x" (CONST 0) ;;
  ASSIGN "y" (CONST 100) ;;
  ASSIGN "z" (PLUS (VAR "x") (VAR "y")) ;;
  IFTHENELSE (EQUAL (VAR "x") (CONST 0))
    (ASSIGN "y" (PLUS (VAR "x") (CONST 10)) ;; ASSIGN "x" (CONST 1))
    (ASSIGN "y" (CONST 10)).

Compute (let S := AConstProp.Cexec prog1 SConstProp.top in
         (SConstProp.get "x" S, SConstProp.get "y" S, SConstProp.get "z" S)).

(** Analysis result:
<<
     = (FlatInt.Top, FlatInt.Just 10, FlatInt.Just 100) 
>>
In other words: [x] is unknown, [y] is 10, and [z] is 100.
*)

(*** Exercise (3 stars) *)

(** Write an abstract domain for sign analysis.
    For each variable, we'd like to know if its value is always
    positive or zero, or always negative, or of unknown sign. *)

Module Sign (* <: VALUE_ABSTRACTION *) .

  Inductive sign : Type :=
    | Bot
    | Pos          (**r nonnegative (positive or zero) *)
    | Neg          (**r negative (and not zero) *)
    | Top.
  Definition t := sign.

  Definition In (n: Z) (N: t) : Prop :=
    match N with
    | Bot => False
    | Pos => 0 <= n
    | Neg => n < 0
    | Top => True
    end.

  (* FILL IN HERE *)

End Sign.


