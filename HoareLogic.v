From Coq Require Import ZArith Psatz Bool String List Wellfounded Program.Equality.
From Coq Require Import FunctionalExtensionality.
From CDF Require Import IMP Sequences.

Local Open Scope string_scope.
Local Open Scope Z_scope.

(** * 4.  Program logics: Hoare logic *)

(** ** 4.1.  Prelude: direct verification of a program *)

(** We can verify the correctness of a program using nothing but an
    operational semantics for the language in which it is written.
    For example, here is an IMP program that exchanges the values of
    two variables. *) Definition swap_xy := ASSIGN "t" (VAR "x");;
    ASSIGN "x" (VAR "y");; ASSIGN "y" (VAR "t").

(** We can characterize the expected behavior of the program as
    follows: started in a store [s], the program always terminates, in
    a store [s'] where ["x"] has value [s "y"] and ["y"] has value [s
    "x"]. *)

Lemma swap_xy_correct: forall s, exists s', star red (swap_xy, s)
  (SKIP, s') /\ s' "x" = s "y" /\ s' "y" = s "x".  Proof.
  intros. econstructor; split.  - eapply star_step. apply
  red_seq_step. apply red_assign.  eapply star_step. apply
  red_seq_done.  eapply star_step. apply red_seq_step. apply
  red_assign.  eapply star_step. apply red_seq_done.  eapply
  star_step. apply red_assign.  apply star_refl.  - unfold update;
  cbn. auto.  Qed.

(** The proof script is long but not difficult.  First, we perform a
    "symbolic execution" of the program by chaining reduction steps.
    This determines the final store [s'], which is easily shown
    to satisfy the expected property. *)

(** Here is a more complicated example, involving a loop.
    The program adds ["x"] to ["y"] by incrementing ["y"] and
    decrementing ["x"] until ["x"] drops to zero. *)

Definition slow_add :=
  WHILE (LESSEQUAL (CONST 1) (VAR "x"))
        (ASSIGN "x" (MINUS (VAR "x") (CONST 1)) ;;
         ASSIGN "y" (PLUS  (VAR "y") (CONST 1))).

(** The statement of correctness for this program remains simple. *)

Lemma slow_add_correct:
  forall s,
  s "x" >= 0 ->
  exists s', star red (slow_add, s) (SKIP, s') /\ s' "y" = s "y" + s "x".
Proof.
  assert (REC: forall v, 0 <= v -> 
               forall s, s "x" = v ->
               exists s', star red (slow_add, s) (SKIP, s') /\ s' "y" = s "y" + s "x").
  { intros v0 v0POS. pattern v0. apply natlike_ind; auto.
  - intros. exists s; split.
    + apply star_one. apply red_while_done. cbn. rewrite H. apply Z.leb_nle. lia.
    + lia.
  - intros v VPOS REC s EQ.
    set (s1 := update "x" v s).
    set (s2 := update "y" (s "y" + 1) s1).
    destruct (REC s2) as (s' & REDS & EQ'). auto.
    exists s'; split.
    + eapply star_step. apply red_while_loop. cbn. rewrite EQ. apply Z.leb_le. lia.
      eapply star_step. apply red_seq_step. apply red_seq_step. apply red_assign.
      eapply star_step. apply red_seq_step. apply red_seq_done.
      eapply star_step. apply red_seq_step. apply red_assign.
      eapply star_step. apply red_seq_done.
      cbn. replace (s "x" - 1) with v by lia. apply REDS.
    + rewrite EQ'. cbn. lia.
  }
  intros. eapply REC; eauto. lia.
Qed.

(** The proof, however, is rather difficult.  We need to perform
    an explicit induction on the value [v] of variable ["x"].
    To use the induction hypothesis, we must manually determine
    some of the intermediate stores: purely symbolic execution
    no longer suffices.  It is inconceivable to verify much more
    complex programs with these techniques! *)

(** Program logics provide higher-level reasoning principles to formally
    verify programs.  In particular, they provide ways to reason about
    loops without setting up a full proof by induction. *)

(** The most familiar program logic is Hoare logic.  In this module,
    we build a Hoare logic to reason about programs written in IMP. *)

(** ** 4.2.  Assertions on the values of variables *)

(** Hoare logic manipulates formulas / claims / assertions that "talk about"
    the values of the program variables.  A typical assertion is
    [0 <= x /\ x <= y], meaning "at this program point, the value of 
    variable [x] is positive and less than or equal to the value of
    variable [y]". *)

(** In our Coq development, we represent assertions by Coq logical formulas
    (type [Prop]) parameterized by the current store, which provides
    the values of the variables.
  
    For example, the assertion [0 <= x /\ x <= y] above is represented
    by the Coq predicate [fun s => 0 <= s "x" /\ s "x" <= s "y"]. *)
    
Definition assertion : Type := store -> Prop.

(** Here are some useful assertions.
    Conjunction and disjunction of two assertions. *)

Definition aand (P Q: assertion) : assertion :=
  fun s => P s /\ Q s.

Definition aor (P Q: assertion) : assertion :=
  fun s => P s \/ Q s.

(** The assertion "arithmetic expression [a] evaluates to value [v]". *)

Definition aequal (a: aexp) (v: Z) : assertion :=
  fun s => aeval a s = v.

(** The assertions "Boolean expression [b] evaluates to true / to false". *)

Definition atrue (b: bexp) : assertion :=
  fun s => beval b s = true.

Definition afalse (b: bexp) : assertion :=
  fun s => beval b s = false.

(** The assertion written "[ P[x <- a] ]" in the literature.
    Substituting [a] for [x] in [P] amounts to evaluating [P] in
    stores where the variable [x] is equal to the value of expression [a]. *)

Definition aupdate (x: ident) (a: aexp) (P: assertion) : assertion :=
  fun s => P (update x (aeval a s) s).

(** Pointwise implication.  Unlike conjunction and disjunction, this is
    not a predicate over the store, just a Coq proposition. *)

Definition aimp (P Q: assertion) : Prop :=
  forall s, P s -> Q s.

(** A few notations to improve legibility. *)

Notation "P -->> Q" := (aimp P Q) (at level 95, no associativity).
Notation "P //\\ Q" := (aand P Q) (at level 80, right associativity).
Notation "P \\// Q" := (aor P Q) (at level 75, right associativity).

(** ** 4.3.  The rules of weak Hoare logic *)

(** Here are the base rules for Hoare logic.
    They define a relation [Hoare P c Q], where
-   [P] is the precondition, assumed to hold "before" executing [c];
-   [c] is the program or program fragment we reason about;
-   [Q] is the postcondition, guaranteed to hold "after" executing [c].

  This is a "weak" logic, meaning that it does not guarantee termination
  of the command [c].  What is guaranteed is that if [c] terminates,
  then its final store satisfies postcondition [Q]. *)

Inductive Hoare: assertion -> com -> assertion -> Prop :=
  | Hoare_skip: forall P,
      Hoare P SKIP P
  | Hoare_assign: forall P x a,
      Hoare (aupdate x a P) (ASSIGN x a) P
  | Hoare_seq: forall P Q R c1 c2,
      Hoare P c1 Q ->
      Hoare Q c2 R ->
      Hoare P (c1;;c2) R
  | Hoare_ifthenelse: forall P Q b c1 c2,
      Hoare (atrue b //\\ P) c1 Q ->
      Hoare (afalse b //\\ P) c2 Q ->
      Hoare P (IFTHENELSE b c1 c2) Q
  | Hoare_while: forall P b c,
      Hoare (atrue b //\\ P) c P ->
      Hoare P (WHILE b c) (afalse b //\\ P)
  | Hoare_consequence: forall P Q P' Q' c,
      Hoare P c Q ->
      P' -->> P ->
      Q -->> Q' ->
      Hoare P' c Q'.

(** Some derived rules. *)

Lemma Hoare_consequence_pre: forall P P' Q c,
      Hoare P c Q ->
      P' -->> P ->
      Hoare P' c Q.
Proof.
  intros. apply Hoare_consequence with (P := P) (Q := Q); unfold aimp; auto.
Qed.

Lemma Hoare_consequence_post: forall P Q Q' c,
      Hoare P c Q ->
      Q -->> Q' ->
      Hoare P c Q'.
Proof.
  intros. apply Hoare_consequence with (P := P) (Q := Q); unfold aimp; auto.
Qed.

Lemma Hoare_ifthen: forall b c P Q,
    Hoare (atrue b //\\ P) c Q ->
    afalse b //\\ P -->> Q ->
    Hoare P (IFTHENELSE b c SKIP) Q.
Proof.
  intros. apply Hoare_ifthenelse; auto.
  apply Hoare_consequence_pre with Q; auto using Hoare_skip.
Qed.

(** An example of a derivation in Hoare logic. *)

Example Hoare_swap_xy: forall m n,
  Hoare (aequal (VAR "x") m //\\ aequal (VAR "y") n)
        swap_xy
        (aequal (VAR "x") n //\\ aequal (VAR "y") m).
Proof.
  intros.
  eapply Hoare_consequence_pre.
- unfold swap_xy. eapply Hoare_seq. apply Hoare_assign.
  eapply Hoare_seq. apply Hoare_assign. apply Hoare_assign.
- unfold aequal, aupdate, aand, aimp; cbn. tauto.
Qed.

(** *** Exercise (2 stars) *)
(** Here is another way to exchange the values of two variables,
    without using a third, temporary variable. *)

Definition swap_xy_2 :=
  ASSIGN "x" (PLUS (VAR "x") (VAR "y")) ;;
  ASSIGN "y" (MINUS (VAR "x") (VAR "y")) ;;
  ASSIGN "x" (MINUS (VAR "x") (VAR "y")).

(** Prove that this program satisfies the same property as [swap_xy].
    Hint: rework the proof script for [Hoare_swap_xy], only minimal
    changes need to be made. *)

Example Hoare_swap_xy_2: forall m n,
  Hoare (aequal (VAR "x") m //\\ aequal (VAR "y") n)
        swap_xy_2
        (aequal (VAR "x") n //\\ aequal (VAR "y") m).
Proof.
  (* FILL IN HERE *)
Admitted.

(** ** 4.4.  Soundness of Hoare logic *)

(** We give a semantic interpretation to the statements [Hoare P c Q]
    of Hoare logic.  The interpretation is the relation [triple P c Q]
    defined below in terms of IMP's natural semantics
    (the relation [cexec s c s']). *)

Definition triple (P: assertion) (c: com) (Q: assertion) : Prop :=
  forall s s', cexec s c s' -> P s -> Q s'.

Notation "{{ P }} c {{ Q }}" := (triple P c Q) (at level 90, c at next level).

(** The semantic interpretation validates every rule of Hoare logic. *)

Lemma triple_skip: forall P,
     {{P}} SKIP {{P}}.
Proof.
  unfold triple; intros. inversion H; subst. auto.
Qed.

Lemma triple_assign: forall P x a,
      {{aupdate x a P}} ASSIGN x a {{P}}.
Proof.
  unfold triple, aupdate; intros. inversion H; subst. auto.
Qed.

Lemma triple_seq: forall P Q R c1 c2,
      {{P}} c1 {{Q}} ->
      {{Q}} c2 {{R}} ->
      {{P}} c1;;c2 {{R}}.
Proof.
  unfold triple; intros. inversion H1; subst. eauto.
Qed.

Lemma triple_ifthenelse: forall P Q b c1 c2,
      {{atrue b //\\ P}} c1 {{Q}} ->
      {{afalse b //\\ P}} c2 {{Q}} ->
      {{P}} IFTHENELSE b c1 c2 {{Q}}.
Proof.
  unfold triple, aand, atrue, afalse; intros. inversion H1; subst.
  destruct (beval b s) eqn:B; eauto.
Qed.

Lemma triple_while: forall P b c,
      {{atrue b //\\ P}} c {{P}} ->
      {{P}} WHILE b c {{afalse b //\\ P}}.
Proof.
  unfold triple; intros P b c T s s' E. dependent induction E; intros.
- split; auto.
- eapply IHE2; eauto. apply T with s; auto. split; auto.
Qed.

Lemma triple_consequence: forall P Q P' Q' c,
      {{P}} c {{Q}} ->
      P' -->> P ->
      Q -->> Q' ->
      {{P'}} c {{Q'}}.
Proof.
  unfold triple, aimp; intros. eauto.
Qed.

(** It follows that Hoare logic is sound: every triple derivable by the
    rules of the logic is semantically valid. *)

Theorem Hoare_sound:
  forall P c Q, Hoare P c Q -> {{P}} c {{Q}}.
Proof.
  induction 1; eauto using triple_skip, triple_assign, triple_seq,
  triple_ifthenelse, triple_while, triple_consequence.
Qed.

(** ** 4.5.  Completeness of Hoare logic *)

(** The converse of theorem [Hoare_sound] is true: a "Hoare triple"
    that holds semantically ([{{P}} c {{Q}}]) can always be derived
    using the rules of the logic ([Hoare P c Q]).  The proof relies
    on the notion of "weakest precondition" (WP). *)

(** The weakest precondition for a command [c] with postcondition [Q]. *)

Definition wp (c: com) (Q: assertion) : assertion :=
  fun s => forall s', cexec s c s' -> Q s'.

(** The WP is a precondition. *)

Lemma wp_precondition: forall c Q, {{wp c Q}} c {{Q}}.
Proof.
  unfold triple, wp; intros. auto.
Qed.

(** The WP is the weakest of all preconditions:
    any other precondition implies the WP. *)

Lemma wp_weakest: forall P c Q, {{P}} c {{Q}} -> P -->> wp c Q.
Proof.
  unfold triple, wp, aimp; intros. eauto.
Qed.

(** The rules of Hoare logic are powerful enough to derive the fact
    that [wp c Q] is a valid precondition for [c] and [Q]. *)

Lemma Hoare_wp: forall c Q, Hoare (wp c Q) c Q.
Proof.
  induction c; intros Q.
- (* SKIP *)
  eapply Hoare_consequence_pre. apply Hoare_skip. 
  unfold aimp, wp; intros. apply H. apply cexec_skip.
- (* ASSIGN *)
  eapply Hoare_consequence_pre. apply Hoare_assign.
  unfold aimp, aupdate, wp; intros. apply H. apply cexec_assign.
- (* SEQ *)
  eapply Hoare_consequence_pre.
  eapply Hoare_seq with (wp c2 Q); eauto.
  unfold aimp, wp; intros. apply H. apply cexec_seq with s'; auto.
- (* IFTHENELSE *)
  apply Hoare_ifthenelse.
  + eapply Hoare_consequence_pre. apply IHc1.
    unfold atrue, aand, aimp, wp; intros. destruct H.
    apply H1. apply cexec_ifthenelse. rewrite H; auto.
  + eapply Hoare_consequence_pre. apply IHc2.
    unfold afalse, aand, aimp, wp; intros. destruct H.
    apply H1. apply cexec_ifthenelse. rewrite H; auto.
- (* WHILE *)
  eapply Hoare_consequence_post.
  + apply Hoare_while.
    eapply Hoare_consequence_pre. apply IHc.
    unfold atrue, aand, aimp, wp; intros. destruct H.
    apply H2. apply cexec_while_loop with s'; auto.
  + unfold afalse, aand, aimp, wp; intros. destruct H.
    apply H0. apply cexec_while_done; auto.
Qed.

(** It follows that any semantically valid triple [{{P}} c {{Q}}]
    can be derived by Hoare's rules. *)

Theorem Hoare_complete: forall P c Q, {{P}} c {{Q}} -> Hoare P c Q.
Proof.
  intros. apply Hoare_consequence_pre with (wp c Q). 
- apply Hoare_wp.
- apply wp_weakest; auto.
Qed.

(** ** 4.6.  Other useful rules *)

(** Using the semantic definition of Hoare triples, it is easy to add
    new reasoning rules: these are just lemmas about the operational
    semantics that we prove once and for all.  For example: *)

Lemma triple_conj:
  forall c P1 Q1 P2 Q2,
  {{P1}} c {{Q1}} -> {{P2}} c {{Q2}} -> {{P1 //\\ P2}} c {{Q1 //\\ Q2}}.
Proof.
  intros; red; intros. destruct H2 as [PRE1 PRE2]. split; eauto.
Qed.

Lemma triple_disj:
  forall c P1 Q1 P2 Q2,
  {{P1}} c {{Q1}} -> {{P2}} c {{Q2}} -> {{P1 \\// P2}} c {{Q1 \\// Q2}}.
Proof.
  intros; red; intros. destruct H2 as [PRE1|PRE2]; [left|right]; eauto.
Qed.

(** We can also give an alternate rule to reason about assignments.
    The alternate rule is a "forward" rule (the postcondition is
    determined by the precondition), unlike Hoare's rule which is "backward". *)

Definition aexists {A: Type} (P: A -> assertion) : assertion :=
  fun (s: store) => exists (a: A), P a s.

Lemma triple_assign_fwd: forall x a P,
  {{ P }}
  ASSIGN x a 
  {{ aexists (fun m => aexists (fun n =>
     aequal (VAR x) n //\\ aupdate x (CONST m) (P //\\ aequal a n))) }}.
Proof.
  intros. unfold triple, aequal, aupdate; intros.
  inversion H; subst.
  exists (s x); exists (aeval a s); cbn.
  split. apply update_same.
  replace (update x (s x) (update x (aeval a s) s)) with s.
  split; auto.
  apply functional_extensionality; intros y.
  unfold update. destruct (string_dec x y); congruence.
Qed.

(** Finally, we build a frame rule that makes it possible to reuse
    an existing verification of [{{P} c {{Q}}]
    and add extra facts [R] to the precondition and the postcondition,
    obtaining a verification of [{{P //\\ R}} c {{Q //\\ R}}]. *)

(** For example: if we showed the correctness of [swap_xy] like this
<<
    {{ aequal (VAR "x") m //\\ aequal (VAR "y") n }}
    swap_xy
    {{ aequal (VAR "x") n //\\ aequal (VAR "y") m }}
>>
    we should be able, without having to re-do the verification de [swap_xy],
    to prove a more informative triple such as
<<
    {{ aequal (VAR "x") m //\\ aequal (VAR "y") n //\\ aequal (VAR "z") p }}
    swap_xy
    {{ aequal (VAR "x") n //\\ aequal (VAR "y") m //\\ aequal (VAR "z") p }}
>>
    to be read as: "furthermore, the value of variable [z] is unchanged". *)

(** This reasoning is valid provided the extra facts [R] mention exclusively
    variables that are not modified during the execution of [c].
    We approximate this requirement by saying that variables that occur
    as left-hand sides of an assignment in [c] can be modified,
    and other variables definitely cannot. *)

Fixpoint modified_by (c: com) (x: ident) : Prop :=
  match c with
  | SKIP => False
  | ASSIGN y a => x = y
  | SEQ c1 c2 => modified_by c1 x \/ modified_by c2 x
  | IFTHENELSE b c1 c2 => modified_by c1 x \/ modified_by c2 x
  | WHILE b c1 => modified_by c1 x
  end.

Lemma cexec_modified:
  forall x s1 c s2,
  cexec s1 c s2 -> ~modified_by c x -> s2 x = s1 x.
Proof.
  induction 1; cbn; intros MB.
- auto.
- unfold update. destruct (string_dec x0 x); congruence.
- rewrite IHcexec2, IHcexec1 by tauto. auto.
- apply IHcexec. destruct (beval b s); tauto.
- auto.
- rewrite IHcexec2, IHcexec1 by tauto. auto.
Qed.

(** Syntactically, an assertion [P] is independent from a set [vars] of
    variables if none of the variables in [vars] is mentioned in [P].
    With out encoding of assertions as predicates [store -> Prop],
    we cannot state the independence condition like this, since
    the predicates are opaque functions.
    Instead, we will say that the assertion has the same truth value
    in any two stores [s1] and [s2] that differ only on the values of
    the variables in set [vars]. *)

Definition independent_of (P: assertion) (vars: ident -> Prop) : Prop :=
  forall s1 s2,
  (forall x, ~ vars x -> s1 x = s2 x) ->
  (P s1 <-> P s2).

(** In the end, we obtain the following frame rule. *)

Lemma triple_frame:
  forall c P Q R,
  {{P}} c {{Q}} ->
  independent_of R (modified_by c) ->
  {{P //\\ R}} c {{Q //\\ R}}.
Proof.
  intros; red; intros. destruct H2 as [PRE1 PRE2]. split.
- eapply H; eauto.
- apply (H0 s' s).
  + intros. apply cexec_modified with c; auto.
  + auto.
Qed.

(** ** 4.7.  Strong Hoare triples *)

(** The Hoare logic presented above is "weak" because it does not
    guarantee program termination, and therefore can show partial
    correctness results only. *)

(** Following similar approaches, we now construct a "strong" Hoare logic
    that guarantees termination and therefore proves total correctness
    results. *)

(** As we did for the weak logic, we could give the rules of the strong
    logic as an inductive predicate, then interpret them semantically.
    To simplify the presentation, we omit the inductive predicate
    and define the "strong" logic directly from the operational semantics,
    via the relation [ [[P]] c [[Q]] ] below. *)

Definition Triple (P: assertion) (c: com) (Q: assertion) :=
  forall s, P s -> exists s', cexec s c s' /\ Q s'.

Notation "[[ P ]] c [[ Q ]]" := (Triple P c Q) (at level 90, c at next level).

(** Note the difference with the weak logic:
-   For the weak triple [ {{P}} c {{Q}} ], we conclude
    "if [c] terminates, then the final store [s'] satisfies [Q]".
-   For the strong triple [ [[P]] c [[Q]] ], we conclude
    "[c] terminates and the final store [s'] satisfies [Q]".
*)

(** The base rules for the strong logic are the same as for the weak logic,
    except for loops. *)

Lemma Triple_skip: forall P,
      [[P]] SKIP [[P]].
Proof.
  intros P s PRE. exists s; split; auto. apply cexec_skip.
Qed.

Lemma Triple_assign: forall P x a,
      [[aupdate x a P]] ASSIGN x a [[P]].
Proof.
  intros P x a s PRE. exists (update x (aeval a s) s); split.
- apply cexec_assign.
- exact PRE.
Qed.

Lemma Triple_seq: forall P Q R c1 c2,
      [[P]] c1 [[Q]] -> [[Q]] c2 [[R]] ->
      [[P]] c1;;c2 [[R]].
Proof.
  intros; intros s PRE. 
  destruct (H s PRE) as (s1 & EXEC1 & MID).
  destruct (H0 s1 MID) as (s2 & EXEC2 & POST).
  exists s2; split.
- apply cexec_seq with s1; auto.
- exact POST.
Qed.

Lemma Triple_ifthenelse: forall P Q b c1 c2,
      [[atrue b //\\ P]] c1 [[Q]] ->
      [[afalse b //\\ P]] c2 [[Q]] ->
      [[P]] IFTHENELSE b c1 c2 [[Q]].
Proof.
  intros; intros s PRE. destruct (beval b s) eqn:B.
- destruct (H s) as (s' & EXEC & POST). split; auto.
  exists s'; split; auto. constructor; rewrite B; auto.
- destruct (H0 s) as (s' & EXEC & POST). split; auto.
  exists s'; split; auto. constructor; rewrite B; auto.
Qed.

Lemma Triple_consequence: forall P Q P' Q' c,
      [[P]] c [[Q]] -> P' -->> P -> Q -->> Q' ->
      [[P']] c [[Q']].
Proof.
  intros; intros s PRE.
  destruct (H s) as (s' & EXEC & POST). apply H0; auto.
  exists s'; auto.
Qed.

(** For [WHILE b c] loops, the strong triple must guarantee that the loop
    terminates for all initial stores satisfying the precondition.
    A simple way to guarantee termination is to exhibit a "variant":
    an integer-valued expression that decreases at every loop iteration
    while remaining nonnegative. *)

Definition alessthan (a: aexp) (v: Z) : assertion :=
  fun (s: store) => 0 <= aeval a s < v.

Lemma Triple_while: forall P variant b c,
  (forall v,
     [[ P //\\ atrue b //\\ aequal variant v ]]
     c
     [[ P //\\ alessthan variant v ]])
  ->
     [[P]] WHILE b c [[P //\\ afalse b]].
Proof.
  intros P variant b c T.
  assert (REC: forall v s, P s -> aeval variant s = v ->
               exists s', cexec s (WHILE b c) s' /\ (P s' /\ beval b s' = false)).
  { induction v using (well_founded_induction (Z.lt_wf 0)).
    intros. destruct (beval b s) eqn:B.
  - destruct (T v s) as (s1 & EXEC1 & (PS1 & LT1)). unfold aand, aequal, atrue; auto.
    destruct (H _ LT1 s1 PS1) as (s2 & EXEC2 & PS2). auto.
    exists s2; split; auto. apply cexec_while_loop with s1; auto.
  - exists s; split; auto. apply cexec_while_done; auto.
  }
  intros s PRE. apply REC with (v := aeval variant s); auto.
Qed.

(** *** Exercise (3 stars) *)

(** The "variant" trick and the order on nonnegative integers are sometimes
    insufficient to show termination of a [WHILE] loop.
    Here is a more powerful rule that uses two variant expressions
    and a lexicographic ordering between pairs of nonnegative integers.
    Show that this rule is sound. *)

Lemma Triple_while_lexico: forall P variant1 variant2 b c,
  (forall v1 v2,
    [[ P //\\ atrue b //\\ aequal variant1 v1 //\\ aequal variant2 v2 ]]
    c
    [[ P //\\ (alessthan variant1 v1 \\// aequal variant1 v1 //\\ alessthan variant2 v2) ]])
  ->
    [[P]] WHILE b c [[P //\\ afalse b]].
Proof.
  intros P variant1 variant2 b c T.
  assert (REC: forall v1 v2 s, P s -> aeval variant1 s = v1 -> aeval variant2 s = v2 ->
               exists s', cexec s (WHILE b c) s' /\ (P s' /\ beval b s' = false)).
  (* FILL IN HERE *)
Admitted.

(** ** 4.8.  Verification condition generation *)

(** With the exception of the rule for [WHILE] loops, the rules of
    Hoare logic can be read as an algorithm that, given a command [c]
    and a postcondition [Q], computes the weakest precondition [P].
    For example, if [c] comprises two assignments in sequence
<<
    c = ASSIGN x1 a1 ;; ASSIGN x2 a2
>>
    the precondition [P] is determined as
<<
    P = aupdate x1 a1 (aupdate x2 a2 Q)
>>
    Such a computation is much simpler than general proof search,
    which can apply the weakening rule [triple_consequence] at any point. *)

(** Of course, the problem is with [WHILE] loops: the loop invariant
    cannot be determined automatically by a computation. *)

(** In the following, we develop a hybrid approach where loops are
    manually annotated with their loop invariants, but all other preconditions
    are automatically computed from the postconditions. *)

Module VCGEN.

(** This is the language of commands where [WHILE] loops are annotated by
    an invariant [Inv]. *)

Inductive com: Type :=
  | SKIP
  | ASSIGN (x: ident) (a: aexp)
  | SEQ (c1: com) (c2: com)
  | IFTHENELSE (b: bexp) (c1: com) (c2: com)
  | WHILE (Inv: assertion) (b: bexp) (c1: com).  (**r new! *)

(** The function [pre c Q] computes a precondition for command [c]
    and postcondition [Q], by "backward execution" of command [c] and
    application of the rules of Hoare logic.  The only exception is
    [WHILE] loops, where we take as precondition the loop invariant
    provided. *)

Fixpoint pre (c: com) (Q: assertion) : assertion :=
  match c with
  | SKIP => Q
  | ASSIGN x a => aupdate x a Q
  | SEQ c1 c2 => pre c1 (pre c2 Q)
  | IFTHENELSE b c1 c2 => atrue b //\\ pre c1 Q \\// afalse b //\\ pre c2 Q
  | WHILE Inv b c => Inv
  end.

(** The Hoare triple [ {{ pre c Q }} c {{ Q }} ] is not always valid:
    we must also ensure that the invariants provided for the loops are
    actually invariant.  For a loop [WHILE Inv b c] having postcondition [Q],
    it must be the case that
-   [afalse b //\\ Inv -->> Q] : 
    when the loop stops, the invariant implies the postcondition;
-   [atrue b //\\ Inv -->> pre c Inv] :
    when the loop iterates, the invariant implies the precondition of
    the loop body.

    The following function [vcg] (Verification Condition Generator) 
    collects all these "verification conditions" for all the loops [WHILE]
    contained in command [c]. *)

Fixpoint vcg (c: com) (Q: assertion) : Prop :=
  match c with
  | SKIP => True
  | ASSIGN x a => True
  | SEQ c1 c2 => vcg c1 (pre c2 Q) /\ vcg c2 Q
  | IFTHENELSE b c1 c2 => vcg c1 Q /\ vcg c2 Q
  | WHILE Inv b c =>
       vcg c Inv
    /\ (afalse b //\\ Inv -->> Q)
    /\ (atrue b //\\ Inv -->> pre c Inv)
  end.

(** The triple [ {{P}} c {{Q}} ] is valid as soon as
-   [P] implies the precondition [pre c Q]
-   the conditions [vcg c Q] are true.
*)

Definition vcgen (P: assertion) (c: com) (Q: assertion) : Prop :=
  (P -->> pre c Q) /\ vcg c Q.

(** To prove this verification algorithm correct, we define
    the plain IMP command [erase c] obtained from the annotated command [c]
    by erasing the loop invariants from the [WHILE] nodes. *)

Fixpoint erase (c: com) : IMP.com :=
  match c with
  | SKIP => IMP.SKIP
  | ASSIGN x a => IMP.ASSIGN x a
  | SEQ c1 c2 => IMP.SEQ (erase c1) (erase c2)
  | IFTHENELSE b c1 c2 => IMP.IFTHENELSE b (erase c1) (erase c2)
  | WHILE Inv b c => IMP.WHILE b (erase c)
  end.

(** We can then show that [pre c Q] is a valid precondition for [c] and [Q],
    provided that the conditions [vcg c Q] are true. *)

Lemma vcg_sound:
  forall c Q, vcg c Q -> {{pre c Q}} erase c {{Q}}.
Proof.
  induction c; cbn; intros.
- apply triple_skip.
- apply triple_assign.
- destruct H as (V1 & V2).
  apply triple_seq with (pre c2 Q); auto.
- destruct H as (V1 & V2). 
  apply triple_ifthenelse.
  + eapply triple_consequence. eapply IHc1; eauto.
    unfold aimp, aand, aor, atrue, afalse. intuition congruence.
    unfold aimp; auto.
  + eapply triple_consequence. eapply IHc2; eauto.
    unfold aimp, aand, aor, atrue, afalse. intuition congruence.
    unfold aimp; auto.
- destruct H as (V1 & V2 & V3).
  eapply triple_consequence.
  + apply triple_while. eapply triple_consequence. apply IHc; eauto.
    eauto. red; auto.
  + red; auto.
  + auto.
Qed.

(** The correctness of algorithm [vcgen] follows. *)

Theorem vcgen_correct:
  forall P c Q, vcgen P c Q -> {{P}} erase c {{Q}}.
Proof.
  unfold vcgen; intros. destruct H as (V1 & V2).
  eapply triple_consequence. eapply vcg_sound; eauto. auto. red; auto.
Qed.

(** *** Application: Euclidean division *)

Infix ";;" := SEQ (at level 80, right associativity).

(** Here are the precondition, the loop invariant, and the postcondition
    for the program that does Euclidean division by iterated subtraction. *)

Definition Pre (s: store) :=
  s "a" >= 0 /\ s "b" > 0.

Definition Inv (s: store) :=
  s "r" >= 0 /\ s "b" > 0 /\ s "a" = s "b" * s "q" + s "r".

Definition Post (s: store) :=
  s "q" = s "a" / s "b" /\ s "r" = s "a" mod s "b".

(** Here is the IMP program with the loop annotated by [Inv]. *)

Definition Euclidean_division :=
  ASSIGN "r" (VAR "a") ;;
  ASSIGN "q" (CONST 0) ;;
  WHILE Inv (LESSEQUAL (VAR "b") (VAR "r"))
    (ASSIGN "r" (MINUS (VAR "r") (VAR "b")) ;;
     ASSIGN "q" (PLUS (VAR "q") (CONST 1))).

(** And here is its correctness proof.  It does not use explicitly any
    rules of Hoare logic.  Instead, we apply the [vcgen_correct]
    theorem, then ask Coq to compute and simplify the verification
    condition.  In the end, all what remains is a formula in standard
    logic (not Hoare logic) that is easily proved using standard Coq
    tactics. *)

Theorem Euclidean_division_correct:
  {{Pre}} erase Euclidean_division {{Post}}.
Proof.
  apply vcgen_correct. red; cbn.
  unfold aimp, aupdate, aand, afalse, atrue, Pre, Post, Inv; cbn.
  intuition auto.
  (* The precondition implies the loop invariant. *)
  - lia.
  (* The invariant and the loop exit imply the postcondition. *)
  - apply Z.leb_gt in H0. apply Zdiv_unique with (s "r"). lia. auto.
  - apply Z.leb_gt in H0. apply Zmod_unique with (s "q"). lia. auto.
  (* The loop invariant is preserved at each iteration. *)
  - apply Z.leb_le in H0. lia.
  - lia. 
Qed.

(** *** Exercise (1 star) *)
(** Redo the verification after removing the hypothesis [s "b" > 0] from
    the precondition and the invariant.  How is it possible that
    the verification "goes through" even when the divisor [b] is zero? *)

(** *** Exercise (3 stars) *)
(** Specify and verify the following program.  It leaves in [r] the
    integer square root of [a].
<<
    r := 0; s := 1;
    while s <= a do (r := r + 1; s := s + r + r + 1)
>>
*)

End VCGEN.
