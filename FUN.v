From Coq Require Import Bool String List Program.Equality.
From CDF Require Import Sequences.

Local Open Scope string_scope.
Local Open Scope list_scope.

(** * 7.  The functional language FUN *)

(** ** 7.1.  Syntax and semantics *)

(** The FUN language is lambda-calculus (variables, function abstractions,
    function applications) extended with Booleans:
    constants [Const true] and [Const false], and a conditional
    [Cond a ifso ifnot] (that is, [if a then ifso else ifnot]).  *)
 
Inductive term: Type :=
  | Var (x: string)
  | Abs (x: string) (a: term)
  | App (a1: term) (a2: term)
  | Const (b: bool)
  | Cond (a: term) (ifso: term) (ifnot: term).

(** Values are function abstractions and Boolean constants. *)

Inductive isvalue: term -> Prop :=
  | V_Abs: forall x a,
      isvalue (Abs x a)
  | V_Const: forall b,
      isvalue (Const b).

(** [subst a x c] is the term [a] where the term [c] is substituted
    for variable [x], also written [a [x ← c]] in the lecture. *)

(** The substitution below is wrong in general, because it can capture
    variables that are free in [c].  We shall use it only when
    [c] is a closed term, without free variables.  This corresponds
    to the reduction of whole programs, without free variables.
    The type system in section 7.2 guarantees that this is the case. *)

Fixpoint subst (a: term) (x: string) (c: term) : term :=
  match a with
  | Var y => if string_dec x y then c else Var y
  | Abs y a => if string_dec x y then Abs y a else Abs y (subst a x c)
  | App a1 a2 => App (subst a1 x c) (subst a2 x c)
  | Const b => Const b
  | Cond a ifso ifnot => Cond (subst a x c) (subst ifso x c) (subst ifnot x c)
  end.

(** The reduction semantics: [red a a'] means that [a] reduces in one
    step to [a'].  We choose a call-by-value semantics, with applications
    being evaluated from left to right. *)

Inductive red: term -> term -> Prop :=
  | red_beta: forall x a v,                 (**r call-by-value beta reduction *)
      isvalue v ->
      red (App (Abs x a) v) (subst a x v)
  | red_cond: forall b ifso ifnot,            (**r reduction for conditionals *)
      red (Cond (Const b) ifso ifnot) (if b then ifso else ifnot)
  | red_app_1: forall a1 a2 a1', (**r reduction to the left of an application *)
      red a1 a1' ->
      red (App a1 a2) (App a1' a2)
  | red_app_2: forall v a2 a2', (**r reduction to the right of an application *)
      isvalue v -> red a2 a2' ->
      red (App v a2) (App v a2')
  | red_cond_1: forall a a' ifso ifnot,         (**r reduction under a [Cond] *)
      red a a' ->
      red (Cond a ifso ifnot) (Cond a' ifso ifnot).

(** *** Exercise (1 step) *)
(** Modify [red] to obtain a call-by-name semantics.
    What is the impact of this change on the results in the remainder
    of this module? *)

(** *** Exercise (2 stars) *)
(** Extend the syntax and the semantics of FUN with one or several
    of the features mentioned in the lecture: Peano integers,
    products, sums, fixed points. *)

(** Another presentation of the reduction semantics, in the style
    popularized by Wright and Felleisen.  First we define head reductions. *)

Inductive head_red: term -> term -> Prop :=
  | head_red_beta: forall x a v,
      isvalue v ->
      head_red (App (Abs x a) v) (subst a x v)
  | head_red_cond: forall b ifso ifnot,
      head_red (Cond (Const b) ifso ifnot) (if b then ifso else ifnot).

(** Then we define the reduction contexts.  Contexts are represented by
    functions [C: term -> term].  The inductive predicate
    [iscontext C] defines which functions are valid reduction contexts. *)

Inductive iscontext: (term -> term) -> Prop :=
  | iscontext_hole:                      (**r at the top *)
      iscontext (fun a => a)
  | iscontext_app_1: forall a C,         (**r to the left of an application *)
      iscontext C -> iscontext (fun x => App (C x) a)
  | iscontext_app_2: forall v C,         (**r to the right of an application *)
      isvalue v -> iscontext C -> iscontext (fun x => App v (C x))
  | iscontext_cond: forall C ifso ifnot, (**r under a conditional *)
      iscontext C -> iscontext (fun x => Cond (C x) ifso ifnot).

(** Finally, we define reductions under a context. *)

Inductive ctx_red: term -> term -> Prop :=
  | ctx_red_intro: forall a a' C,
      head_red a a' -> iscontext C ->
      ctx_red (C a) (C a').

(** Equivalence with the previous definition [red]. *)

Lemma ctx_red_to_red: 
  forall a a', ctx_red a a' -> red a a'.
Proof.
  assert (REC: forall a a', head_red a a' ->
               forall C, iscontext C ->
               red (C a) (C a')).
  { intros a a' HR; induction 1.
  - inversion HR; subst; constructor; auto.
  - apply red_app_1; auto.
  - apply red_app_2; auto.
  - apply red_cond_1; auto. }
  destruct 1. apply REC; auto.
Qed.

Lemma red_to_ctx_red:
  forall a a', red a a' -> ctx_red a a'.
Proof.
  induction 1.
- apply ctx_red_intro with (C := fun x => x).
  apply head_red_beta; auto.
  constructor.
- apply ctx_red_intro with (C := fun x => x).
  apply head_red_cond; auto.
  constructor.
- destruct IHred. apply ctx_red_intro with (C := fun x => App (C x) a2); auto using iscontext.
- destruct IHred. apply ctx_red_intro with (C := fun x => App v (C x)); auto using iscontext.
- destruct IHred. apply ctx_red_intro with (C := fun x => Cond (C x) ifso ifnot); auto using iscontext.
Qed.

(** The natural semantics. *)

Inductive eval: term -> term -> Prop :=
  | eval_abs: forall x a,
      eval (Abs x a) (Abs x a)
  | eval_app: forall a1 a2 x a v2 v,
      eval a1 (Abs x a) -> eval a2 v2 -> eval (subst a x v2) v ->
      eval (App a1 a2) v
  | eval_const: forall b,
      eval (Const b) (Const b)
  | eval_cond: forall a ifso ifnot b v,
      eval a (Const b) -> eval (if b then ifso else ifnot) v ->
      eval (Cond a ifso ifnot) v.

Lemma eval_isvalue:
  forall a v, eval a v -> isvalue v.
Proof.
  induction 1; auto using isvalue.
Qed.

Lemma isvalue_eval:
  forall v, isvalue v -> eval v v.
Proof.
  destruct 1; eauto using eval.
Qed.

(** Equivalence between natural semantics [eval a v] and reduction semantics
    (there exists a sequence of reductions from term [a] to value [v]). *)

Lemma eval_reds:
  forall a v, eval a v -> star red a v.
Proof.
  induction 1.
- apply star_refl.
- apply star_trans with (App (Abs x a) a2).
  revert IHeval1. generalize a1, (Abs x a). induction 1; eauto using star, red_app_1.
  apply star_trans with (App (Abs x a) v2).
  revert IHeval2. generalize a2, v2. induction 1; eauto using star, red_app_2, isvalue.
  eapply star_step. apply red_beta. eapply eval_isvalue; eauto.
  apply IHeval3.
- apply star_refl.
- apply star_trans with (Cond (Const b) ifso ifnot).
  revert IHeval1. generalize a, (Const b). induction 1; eauto using star, red_cond_1.
  eapply star_step. apply red_cond. 
  apply IHeval2.
Qed. 

Lemma red_eval_eval:
  forall a1 a2, red a1 a2 -> forall v, eval a2 v -> eval a1 v.
Proof.
  induction 1; intros v' E.
- eauto using eval, isvalue_eval.
- eauto using eval.
- inversion E; subst; eauto using eval.
- inversion E; subst; eauto using eval, isvalue_eval.
- inversion E; subst; eauto using eval.
Qed.

Lemma reds_eval:
  forall a v, star red a v -> isvalue v -> eval a v.
Proof.
  induction 1; intros.
- apply isvalue_eval; auto.
- apply red_eval_eval with b; auto.
Qed. 

(** ** 7.2.  Simple types *)

(** The type algebra. *)

Inductive type: Type :=
  | Bool                          (**r the type of Booleans *)
  | Fun (t1: type) (t2: type).    (**r the type of functions from [t1] to [t2] *)

Notation " t1 --> t2 " := (Fun t1 t2) (right associativity, at level 55).

(** Typing contexts associate a type to each free variable. *)

Definition context := list (string * type).

Fixpoint lookup {A: Type} (x: string) (l: list (string * A)) : option A :=
  match l with
  | nil => None
  | (y, a) :: l => if string_dec x y then Some a else lookup x l
  end.

(** The typing rules. *)

Reserved Notation "E '⊢' a '∈' t" (at level 40).

Inductive has_type : context -> term -> type -> Prop :=
  | T_Var: forall E x t,
      lookup x E = Some t ->
      E ⊢ Var x ∈ t
  | T_Abs : forall E x a t t',
      ((x, t) :: E) ⊢ a ∈ t' ->
      E ⊢ Abs x a ∈ Fun t t'
  | T_App : forall E a1 a2 t t',
      E ⊢ a1 ∈ Fun t t' -> E ⊢ a2 ∈ t ->
      E ⊢ App a1 a2 ∈ t'
  | T_Const : forall E b,
      E ⊢ Const b ∈ Bool
  | T_Cond : forall E a ifso ifnot t,
      E ⊢ a ∈ Bool -> E ⊢ ifso ∈ t -> E ⊢ ifnot ∈ t ->
      E ⊢ Cond a ifso ifnot ∈ t

where "E '⊢' a '∈' t" := (has_type E a t).

(** The main properties of the typing judgment.
    First, the weakening property. *)

Lemma weakening:
  forall E a t, 
  E ⊢ a ∈ t ->
  forall E',
  (forall x tx, lookup x E = Some tx -> lookup x E' = Some tx) ->
  E' ⊢ a ∈ t.
Proof.
  induction 1; intros E' W; eauto using has_type.
- (* Abs *)
  apply T_Abs. apply IHhas_type.
  cbn; intros. destruct (string_dec x0 x); auto.
Qed.

(** Weakening is stated in an unusual manner.
    Usually, it is stated with a syntactic concatenation of contexts:
    if [E ⊢ a ∈ t], then [E' ++ E ⊢ a ∈ t].  However, this statement
    is false if [E'] can bound variables that are already bound in [E].
    On paper, we implicitly assume that a context never binds the same
    variable twice, a constraint that can always be satisfied by
    renaming some variables.
    In our Coq development, we have no renaming nor constraints over
    contexts.  Instead, we use two arbitrary contexts [E] and [E'],
    connected by the hypothesis
    "any variable that is given a type by [E] is given the same type in [E']".
*)

(** The next property is stability of typing under substitution.
    It uses the same trick to connect
-   the context [E] in which term [a] is typed before substitution;
-   the context [E'] in which the term [subst a x c] is typed after
    substitution.

    Moreover, the lemma requires that [c] is typed in the empty
    environment, guaranteeing that [c] is closed and that the substitution
    [subst a x c] avoids variable capture. *)

Lemma substitution_preserves_typing:
  forall E a t, 
  E ⊢ a ∈ t ->
  forall x c t' E',
  nil ⊢ c ∈ t' ->
  lookup x E = Some t' ->
  (forall y ty, y <> x -> lookup y E = Some ty -> lookup y E' = Some ty) ->
  E' ⊢ subst a x c ∈ t.
Proof.
  induction 1; intros until E'; intros TYC TYX TYE; cbn.
- (* Var *)
  destruct (string_dec x0 x).
  + (* Var x *)
    replace t with t' by congruence. 
    apply weakening with (E := nil); auto.
    cbn; intros; discriminate.
  + (* Var y, y <> x *)
    apply T_Var. apply TYE; auto.
- (* Abs *)
  destruct (string_dec x0 x).
  + (* Abs x a *)
    subst x0.
    apply T_Abs. apply weakening with (E := (x, t) :: E); auto.
    cbn; intros. destruct (string_dec x0 x); auto.
  + (* Abs y a, y <> x *)
    apply T_Abs. eapply IHhas_type; eauto.
    cbn. destruct (string_dec x0 x); congruence.
    cbn; intros. destruct (string_dec y x); auto.
- (* App *)
  apply T_App with t; eauto.
- (* Const *)
  apply T_Const.
- (* Cond *)
  apply T_Cond; eauto.
Qed.

(** Finally, here is the "canonical forms" lemma, showing that the type
    of a closed value determines its shape. *)

Lemma canonical_forms:
  forall v t,
  nil ⊢ v ∈ t -> isvalue v ->
  match t with
  | Bool => exists b, v = Const b
  | Fun t1 t2 => exists x a, v = Abs x a
  end.
Proof.
  intros v t TY VAL. inversion VAL; subst; inversion TY; subst.
- (* Fun type *)
  exists x, a; auto.
- (* Bool type *)
  exists b; auto.
Qed.

(** We can, then, prove the two crucial properties that connect typing
    with reductions: preservation and progress. *)

Theorem reduction_preserves_typing:
  forall a a',
  red a a' ->
  forall t,
  nil ⊢ a ∈ t -> nil ⊢ a' ∈ t.
Proof.
  induction 1; intros t TY.
- (* red_beta *) 
  inversion TY; subst. inversion H3; subst.
  eapply substitution_preserves_typing; eauto.
  cbn. destruct (string_dec x x); congruence.
  cbn; intros. destruct (string_dec y x); congruence.
- (* red_cond *)
  inversion TY; subst.
  destruct b; auto.
- (* red_app_1 *)
  inversion TY; subst. apply T_App with t0; eauto. 
- (* red_app_2 *)
  inversion TY; subst. apply T_App with t0; eauto. 
- (* red_cond_1 *)
  inversion TY; subst. apply T_Cond; eauto.
Qed.

Theorem progress:
  forall a t,
  nil ⊢ a ∈ t -> isvalue a \/ exists a', red a a'.
Proof.
  intros a t TY; dependent induction TY.
- (* Abs x a *)
  left; apply V_Abs.
- (* App a1 a2 *)
  destruct IHTY1 as [ISVAL1 | (a1' & RED1)]; auto.
  + destruct IHTY2 as [ISVAL2 | (a2' & RED2)]; auto.
    * (* a1 et a2 sont des valeurs *)
      destruct (canonical_forms a1 (Fun t t')) as (x & a & E); auto.
      subst a1. right; exists (subst a x a2). apply red_beta; auto.
    * (* a1 est une valeur, a2 se réduit *)
      right; exists (App a1 a2'). apply red_app_2; auto.
  + (* a1 se réduit *)
    right; exists (App a1' a2). apply red_app_1; auto.
- (* Const b *)
  left; apply V_Const.
- (* Cond a ifso ifnot *)
  destruct IHTY1 as [ISVAL1 | (a' & RED1)]; auto.
  + (* a est une valeur *)
    destruct (canonical_forms a Bool) as (b & E); auto.
    subst a. right; exists (if b then ifso else ifnot). apply red_cond.
  + (* a se réduit *)
    right; exists (Cond a' ifso ifnot). apply red_cond_1; auto.
Qed.

(** Type soundness follows: a well-typed closed term does not go wrong. *)

Definition goes_wrong (a: term) : Prop :=
  exists a', star red a a' /\ irred red a' /\ ~isvalue a'.

Theorem well_typed_programs_do_not_go_wrong:
  forall a t,
  nil ⊢ a ∈ t -> ~ goes_wrong a.
Proof.
  intros a t TY (a' & REDS & IRRED & NOTVAL).
  assert (TY': nil ⊢ a' ∈ t).
  { clear IRRED NOTVAL. revert a a' REDS TY.
    induction 1; eauto using reduction_preserves_typing. }
  destruct (progress a' t TY') as [ISVAL | (a'' & RED)].
  - apply NOTVAL. auto.
  - apply IRRED with a''. auto.
Qed.

(** A more positive presentation of the type soundness  result.
    We define coinductively the predicate [safe a], meaning
    "a executes without going wrong".  It covers both the case
    where the reduction of [a] terminates on a value, and the
    case where the reduction of [a] diverges. *)

CoInductive safe: term -> Prop :=
  | safe_value: forall v,
      isvalue v ->
      safe v
  | safe_red: forall a a',
      red a a' -> safe a' ->
      safe a.

Theorem well_typed_programs_are_safe:
  forall a t,
  nil ⊢ a ∈ t -> safe a.
Proof.
  cofix CIH; intros.
  destruct (progress a t H) as [ISVAL | (a' & RED)].
- apply safe_value; auto.
- apply safe_red with a'; auto.
  apply CIH with t. apply reduction_preserves_typing with a; auto.
Qed.

(** *** Exercise (2 or 3 stars) *)
(** Extend the type system with one or several of the features
    mentioned in the lecture: Peano integers, products, sums, fixed points.
    Update the proof of type soundness accordingly. *)

(** *** Exercise (3 stars) *)
(** In the definition of the type algebra, replace [Inductive type ...]
    by [CoInductive type ...].
    This makes it possible to work with infinite type expressions
    such as [Bool --> Bool --> ... --> Bool --> ...].

-   Check that the proof of type soundness still works.
-   Show that we can type the fixed-point combinator [Y] shown
    in the lecture, giving it the type [(t --> t) --> t] for any type [t]. *)

Remark type_Y: forall t,
  let D := Abs "x" (App (Var "f") (App (Var "x") (Var "x"))) in
  let Y := Abs "f" (App D D) in
  nil ⊢ Y ∈ ((t --> t) --> t).
Proof.
  intros t D Y.
  (* FILL IN HERE *)
Abort.

(** *** Exercise (3 stars) *)
(** Write a type-checker for our type system with simple types.
    It's a function [context -> term -> option type]
    that checks whether a term is well-typed in a given context.
    If yes, the type of the term is returned; if not, [None] is returned.
    Prove that this type-checker is sound and complete with respect
    to the typing rules. *)

Fixpoint typecheck (E: context) (a: term) : option type :=
  (* FILL IN HERE *) None.

Lemma typecheck_sound:
  forall E a t, typecheck E a = Some t -> has_type E a t.
Proof.
  intros E a; revert a E; induction a; cbn; intros E t T.
  (* FILL IN HERE *)
Abort.

Lemma typecheck_complete:
  forall E a t, has_type E a t -> typecheck E a = Some t.
Proof.
  induction 1; cbn.
  (* FILL IN HERE *)
Abort.

(** ** 7.3.  Subtyping *)

Module Subtyping.

(** We extend the type algebra with [Top], the universal type of all values. *)

Inductive type: Type :=
  | Top                           (**r universal type *)
  | Bool                          (**r type of Booleans *)
  | Fun (t1: type) (t2: type).    (**r type of functions from [t1] to [t2] *)

Reserved Notation "t '<:' s" (at level 40).

(** The subtyping relation.  Intuitively, [t] is subtype of [s]
    if every value of type [t] can be used with type [s]. *)

Inductive subtype: type -> type -> Prop :=
  | subtype_top: forall t,
      t <: Top
  | subtype_bool:
      Bool <: Bool
  | subtype_fun: forall s1 t1 s2 t2,
      s2 <: s1 -> t1 <: t2 ->
      Fun s1 t1 <: Fun s2 t2

where "t '<:' s" := (subtype t s).

(** Every type is subtype of itself. *)

Lemma subtype_refl:
  forall t, t <: t.
Proof.
  induction t; auto using subtype.
Qed.

(** The subtyping relation is transitive. *)

Lemma subtype_trans:
  forall t1 t2 t3, t1 <: t2 -> t2 <: t3 -> t1 <: t3.
Proof.
  intros t1 t2; revert t2 t1.
  induction t2; intros t1 t3 S1 S2; 
  inversion S1; inversion S2; subst; eauto using subtype.
Qed.

(** We extend the type system with a subsumption rule [T_Sub]
    that allows us to use a term with a super-type of its type. *)

Definition context := list (string * type).

Inductive has_type : context -> term -> type -> Prop :=
  | T_Var: forall E x t,
      lookup x E = Some t ->
      E ⊢ Var x ∈ t
  | T_Abs : forall E x a t t',
      ((x, t) :: E) ⊢ a ∈ t' ->
      E ⊢ Abs x a ∈ Fun t t'
  | T_App : forall E a1 a2 t t',
      E ⊢ a1 ∈ Fun t t' -> E ⊢ a2 ∈ t ->
      E ⊢ App a1 a2 ∈ t'
  | T_Const : forall E b,
      E ⊢ Const b ∈ Bool
  | T_Cond : forall E a ifso ifnot t,
      E ⊢ a ∈ Bool -> E ⊢ ifso ∈ t -> E ⊢ ifnot ∈ t ->
      E ⊢ Cond a ifso ifnot ∈ t
  | T_Sub: forall E a s t,       (**r <-- new! *)
      E ⊢ a ∈ s -> s <: t ->
      E ⊢ a ∈ t

where "E '⊢' a '∈' t" := (has_type E a t).

(** *** Exercise (4 étoiles) *)
(** Prove type soundness for this type system with subtyping.
    The proof in section 7.2 can be reused with very few changes.  
    However, it is necessary to use the following inversion lemmas. *)

Lemma T_Abs_inv:
  forall E x a t,
  E ⊢ Abs x a ∈ t -> exists t1 t2, ((x, t1) :: E) ⊢ a ∈ t2 /\ Fun t1 t2 <: t.
Proof.
  intros until t; intros TY; dependent induction TY.
- exists t, t'; auto using subtype_refl.
- edestruct IHTY as (t1 & t2 & P & Q); eauto.
  exists t1, t2; split. auto. apply subtype_trans with s; auto.
Qed.

Lemma T_App_inv:
  forall E a1 a2 t,
  E ⊢ App a1 a2 ∈ t -> exists t1 t2, E ⊢ a1 ∈ Fun t1 t2 /\ E ⊢ a2 ∈ t1 /\ t2 <: t.
Proof.
  intros until t; intros TY; dependent induction TY.
- exists t, t'; auto using subtype_refl.
- edestruct IHTY as (t1 & t2 & P & Q & R); eauto.
  exists t1, t2; split. auto. split. auto. apply subtype_trans with s; auto.
Qed.

Lemma T_Cond_inv:
  forall E a ifso ifnot t,
  E ⊢ Cond a ifso ifnot ∈ t -> exists t', E ⊢ a ∈ Bool /\ E ⊢ ifso ∈ t' /\ E ⊢ ifnot ∈ t' /\ t' <: t.
Proof.
  intros until t; intros TY; dependent induction TY.
- exists t; auto using subtype_refl.
- edestruct IHTY as (t' & P & Q & R & S); eauto.
  exists t'; intuition auto. apply subtype_trans with s; auto.
Qed.

Theorem well_typed_programs_are_safe:
  forall a t,
  nil ⊢ a ∈ t -> safe a.
Proof.
  (* FILL IN HERE *)
Abort.

End Subtyping.

(** ** 7.4.  Intrinsically-typed terms *)

From Coq Require Import FunctionalExtensionality.

Module Intrinsic.

(** We now develop an abstract syntax for FUN where terms are indexed
    by their types and the contexts in which they are typed. *)

(** A context lists the free variables that can occur in the term,
    along with their types.  We use a positional notation (de Bruijn indices)
    for variables.  Consequently, the context is just a list of types:
    [t1 :: ... :: tN :: nil] is the context that assigns type [ti]
    to the variable having index [i], for [i] ranging from 1 to [N]. *)

Definition context := list type.

(** [var E t] is the type of variables that can be used in context [E]
    with type [t]. *)

Inductive var: context -> type -> Type :=
  | V1: forall {E: context} {t: type}, var (t :: E) t
  | VS: forall {E: context} {t t': type}, var E t' -> var (t :: E) t'.

(** Examples of variables. *)

Definition V2 {E: context} {t1 t2: type}: var (t1 :: t2 :: E) t2 := VS V1.
Definition V3 {E: context} {t1 t2 t3: type}: var (t1 :: t2 :: t3 :: E) t3 := VS V2.

(** [term E t] is the type of terms having type [t] in context [E]. *)

Inductive term: context -> type -> Type :=
  | Var: forall {E: context} {t: type},
         var E t ->
         term E t
  | Abs: forall {E: context} {t t': type},
         term (t :: E) t' ->
         term E (Fun t t')
  | App: forall {E: context} {t t': type},
         term E (Fun t t') -> term E t ->
         term E t'
  | Const: forall {E: context} (b: bool),
         term E Bool
  | Cond: forall {E: context} {t: type},
         term E Bool -> term E t -> term E t ->
         term E t.

(** Examples of terms. *)

(** The term [fun b => if b then false else true]. *)
Definition t_negation : term nil (Bool --> Bool) :=
  Abs (Cond (Var V1) (Const false) (Const true)).

(** The term [fun f => fun g => fun x => g (f x)]. *)
Definition t_compose (t1 t2 t3: type) :
               term nil ((t1 --> t2) --> (t2 --> t3) --> (t1 --> t3)) :=
  Abs (Abs (Abs (App (Var V2) (App (Var V3) (Var V1))))).

(** An ill-typed term that, consequently, cannot be expressed. *)
Fail Definition t_error : term nil Bool :=
  Cond (Abs (Var V1)) (Const false) (Const true).

(** We interpret a FUN type expression by a Coq type.  It's the type of
    Coq values that match this FUN type. *)

Fixpoint dtype (t: type) : Type :=
  match t with
  | Bool => bool
  | Fun t1 t2 => dtype t1 -> dtype t2
  end.

(** Likewise, we interpret a typing context by a Coq type.
    It is the type of evaluation environments corresponding to this
    context: an heterogeneous list of the values associated to the variables. *)

Fixpoint dcontext (E: context) : Type :=
  match E with
  | nil => unit
  | t :: E => dtype t * dcontext E
  end.

(** The denotational semantics of a variable.
    It is the value associated to the variable in the evaluation environment. *)

Fixpoint dvar {E: context} {t: type} (v: var E t): dcontext E -> dtype t :=
  match v with
  | V1 => (fun e => fst e)
  | VS v => (fun e => dvar v (snd e))
  end.

(** The denotational semantics of a term.
    It is a function from evaluation environments, [dcontext E],
    to Coq values matching the type of the expression, [dtype t]. *)

Fixpoint dterm {E: context} {t: type} (a: term E t) : dcontext E -> dtype t :=
  match a with
  | Var v => dvar v
  | Abs a => (fun e => (fun v => dterm a (v, e)))
  | App a1 a2 => (fun e => dterm a1 e (dterm a2 e))
  | Const b => (fun e => b)
  | Cond a ifso ifnot => (fun e => if dterm a e then dterm ifso e else dterm ifnot e)
  end.

(** The semantics of a beta-redex [App (Abs a) b] is just that of the
    binding [let 1 = b in a]: we evaluate [a] after binding the
    variable of index 1 to the value of [b]. *)

Lemma dbeta: forall (E: context) (t t': type) (a: term (t :: E) t') (b: term E t),
  forall e, dterm (App (Abs a) b) e = dterm a (dterm b e, e).
Proof.
  reflexivity.
Qed.

(** In preparation for a reduction semantics, we now build a substitution
    function over intrinsically-typed terms.
    The substitution of [b] for variable of index 1 in [a] has type
<<
   subst1 {t': type} {E: context} {t: type} (a: term (t' :: E) t) (b: term E t') : term E t
>>
    and satisfies the equation [dterm (subst1 a b) e = dterm a (dterm b e, e)]. *)

(** Definiting the substitution function is difficult:
-   Since we use a positional notation, we need to "lift" by one certain
    variable indices (function [lift] below).
-   Our functions have complex dependent types.  On the one hand, these
    types guarantee type preservation by construction.  On the other hand,
    the functions are hard to write directly.
-   We chose to prove semantic equations about our functions at the
    same time we define the functions, resulting in many subset types
    [ { x | P x } ].
*)

(** Lifting. *)

Fixpoint unlift_env (E': context) (t': type) (E: context) : dcontext (E' ++ t' :: E) -> dcontext (E' ++ E) :=
  match E' with
  | nil => fun e => snd e
  | t :: E' => fun e => (fst e, unlift_env E' t' E (snd e))
  end.

Definition lift_var  (E': context) (t': type) {E: context} {t: type} (v: var (E' ++ E) t) :
           { w : var (E' ++ t' :: E) t
           | forall e, dvar w e = dvar v (unlift_env E' t' E e)}.
Proof.
  revert E' t' E t v. induction E' as [ | t0 E' ]; cbn.
- intros. exists (VS v). auto.
- intros. dependent destruction v.
  + exists V1. auto.
  + destruct (IHE' t' _ _ v) as (w & W). exists (VS w). intros; cbn. rewrite W; auto.
Defined.

Definition lift (E': context) (t': type) {E: context} {t: type} (a: term (E' ++ E) t) :
           { b : term (E' ++ t' :: E) t
           | forall e, dterm b e = dterm a (unlift_env E' t' E e) }.
Proof.
  dependent induction a.
- destruct (lift_var E' t' v) as (w & W). exists (Var w). auto.
- destruct (IHa (t::E') _ a) as (b & B); auto.
  exists (Abs b). intros. apply functional_extensionality; intros. cbn. rewrite B. auto.
- destruct (IHa1 E' _ a1) as (b1 & B1); auto.
  destruct (IHa2 E' _ a2) as (b2 & B2); auto.
  exists (App b1 b2). cbn; intros. rewrite B1, B2. auto.
- exists (Const b); auto.
- destruct (IHa1 E' _ a1) as (b1 & B1); auto.
  destruct (IHa2 E' _ a2) as (b2 & B2); auto.
  destruct (IHa3 E' _ a3) as (b3 & B3); auto.
  exists (Cond b1 b2 b3). intros; cbn. rewrite B1, B2, B3; auto.
Defined.

Definition lift1 (t': type) {E: context} {t: type} (a: term E t) :
           { b : term (t' :: E) t
           | forall e, dterm b e = dterm a (snd e) }.
Proof.
  apply lift with (E' := nil).
Defined.

(** Substitution. *)

Fixpoint proj_env (E': context) (E: context) : dcontext (E' ++ E) -> dcontext E :=
  match E' with
  | nil => fun e => e
  | t :: E' => fun e => proj_env E' E (snd e)
  end.

Fixpoint unsubst_env (E': context) (t': type) (E: context) : dcontext (E' ++  E) -> dtype t' -> dcontext (E' ++ t' :: E) :=
  match E' with
  | nil => fun e v => (v, e)
  | t :: E' => fun e v => (fst e, unsubst_env E' t' E (snd e) v)
  end.

Definition subst_var (E': context) (t': type) {E: context} {t: type} (v: var (E' ++ t' :: E) t) (b: term E t') :
           { c : term (E' ++ E) t
           | forall e, dterm c e = dvar v (unsubst_env E' t' E e (dterm b (proj_env E' E e))) }.
Proof.
  induction E' as [ | t0 E' ]; simpl.
- dependent destruction v; simpl.
  + exists b; auto.
  + exists (Var v); auto.
- dependent destruction v; simpl.
  + exists (Var V1); auto.
  + destruct (IHE' v) as (c & C). destruct (lift1 t0 c) as (c' & C'). exists c'.
    simpl; intros. rewrite C', C. auto.
Defined.

Definition subst (E': context) (t': type) {E: context} {t: type} (a: term (E' ++ t' :: E) t) (b: term E t') :
           { c : term (E' ++ E) t
           | forall e, dterm c e = dterm a (unsubst_env E' t' E e (dterm b (proj_env E' E e))) }.
Proof.
  dependent induction a.
- apply subst_var. 
- edestruct (IHa (t :: E') t' E a) as (c & C); eauto.
  exists (Abs c). intros. apply functional_extensionality. intros v; simpl. 
  rewrite C. simpl. eauto.
- edestruct (IHa1 E' t' E a1) as (c1 & C1); eauto.
  edestruct (IHa2 E' t' E a2) as (c2 & C2); eauto.
  exists (App c1 c2). simpl; intros. rewrite C1, C2. eauto.
- exists (Const b). simpl; auto.
- edestruct (IHa1 E' t' E a1) as (c1 & C1); eauto.
  edestruct (IHa2 E' t' E a2) as (c2 & C2); eauto.
  edestruct (IHa3 E' t' E a3) as (c3 & C3); eauto.
  exists (Cond c1 c2 c3). simpl; intros. rewrite C1, C2, C3. eauto.
Defined.

Definition subst1 {t': type} {E: context} {t: type} (a: term (t' :: E) t) (b: term E t') : term E t :=
  proj1_sig (subst nil t' a b).

Lemma dterm_subst1:
  forall {t': type} {E: context} {t: type} (a: term (t' :: E) t) (b: term E t') e,
  dterm (subst1 a b) e = dterm a (dterm b e, e).
Proof.
  intros. unfold subst1. destruct (subst nil t' a b) as (c & C). apply C. 
Qed.

(** The reduction semantics. *)

Inductive isvalue: forall (E: context) (t: type), term E t -> Prop :=
  | V_Abs: forall E t1 t2 (a: term (t1 :: E) t2),
      isvalue E (Fun t1 t2) (Abs a)
  | V_Const: forall E b,
      isvalue E Bool (Const b).

Inductive red: forall E t, term E t -> term E t -> Prop :=
  | red_beta: forall E t1 t2 (a: term (t1 :: E) t2) (v: term E t1),
      isvalue E t1 v ->
      red E t2 (App (Abs a) v) (subst1 a v)
  | red_cond: forall E t (b: bool) (ifso ifnot: term E t),
      red E t (Cond (Const b) ifso ifnot) (if b then ifso else ifnot)
  | red_app_1: forall E t t' (a1 a1': term E (Fun t t')) (a2: term E t),
      red E (Fun t t') a1 a1' ->
      red E t' (App a1 a2) (App a1' a2)
  | red_app_2: forall E t t' (v: term E (Fun t t')) (a2 a2': term E t),
      isvalue E (Fun t t') v -> red E t a2 a2' ->
      red E t' (App v a2) (App v a2')
  | red_cond_1: forall E t (a a': term E Bool) (ifso ifnot: term E t),
      red E Bool a a' ->
      red E t (Cond a ifso ifnot) (Cond a' ifso ifnot).

(** Reductions are compatible with the denotational semantics. *)

Theorem red_denot:
  forall E t a1 a2, red E t a1 a2 -> forall e, dterm a1 e = dterm a2 e.
Proof.
  induction 1; simpl; intros.
- rewrite dterm_subst1; auto.
- destruct b; auto.
- rewrite IHred; auto.
- rewrite IHred; auto.
- rewrite IHred; auto.
Qed.

End Intrinsic.
