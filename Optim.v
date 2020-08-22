From Coq Require Import ZArith Psatz Bool String Program.Equality FSets Wellfounded.
From CDF Require Import Sequences IMP Simulation.

Local Open Scope string_scope.
Local Open Scope Z_scope.
Local Open Scope list_scope.

(** * 3. Optimizations and static analyses *)

(** ** 3.1.  Liveness analysis *)

(** *** Finite sets of identifiers *)

(** The static analysis considered here works with finite sets of IMP
    variables.  The Coq standard library provides efficient
    implementations of finite sets and proves many properties of set
    operations.  In order to use this library, we must provide it with
    a Coq module describing the type of set elements (IMP's
    identifiers) and a decidable equality between elements. *)

Module Ident_Decidable <: DecidableType with Definition t := ident.
  Definition t := ident.
  Definition eq (x y: t) := x = y.
  Definition eq_refl := @eq_refl t.
  Definition eq_sym := @eq_sym t.
  Definition eq_trans := @eq_trans t.
  Definition eq_dec := string_dec.
End Ident_Decidable.

(** We then instantiate the generic library modules for finite sets
    over this element type. *)

Module IdentSet := FSetWeakList.Make(Ident_Decidable).
Module ISFact := FSetFacts.WFacts(IdentSet).
Module ISProp := FSetProperties.WProperties(IdentSet).
Module ISDecide := FSetDecide.Decide(IdentSet).
Import ISDecide.

(** *** Free variables *)

(** The set of all variables mentioned in an expression. *)

Fixpoint fv_aexp (a: aexp) : IdentSet.t :=
  match a with
  | CONST n => IdentSet.empty
  | VAR v => IdentSet.singleton v
  | PLUS a1 a2 => IdentSet.union (fv_aexp a1) (fv_aexp a2)
  | MINUS a1 a2 => IdentSet.union (fv_aexp a1) (fv_aexp a2)
  end.

Fixpoint fv_bexp (b: bexp) : IdentSet.t :=
  match b with
  | TRUE => IdentSet.empty
  | FALSE => IdentSet.empty
  | EQUAL a1 a2 => IdentSet.union (fv_aexp a1) (fv_aexp a2)
  | LESSEQUAL a1 a2 => IdentSet.union (fv_aexp a1) (fv_aexp a2)
  | NOT b1 => fv_bexp b1
  | AND b1 b2 => IdentSet.union (fv_bexp b1) (fv_bexp b2)
  end.

(** The set of all variables used by a command.
    (We ignore the variables assigned but not used by the command.) *)

Fixpoint fv_com (c: com) : IdentSet.t :=
  match c with
  | SKIP => IdentSet.empty
  | ASSIGN x a => fv_aexp a
  | SEQ c1 c2 => IdentSet.union (fv_com c1) (fv_com c2)
  | IFTHENELSE b c1 c2 => IdentSet.union (fv_bexp b) (IdentSet.union (fv_com c1) (fv_com c2))
  | WHILE b c => IdentSet.union (fv_bexp b) (fv_com c)
  end.

(** *** Computing post-fixed points *)

Section FIXPOINT.

Variable F: IdentSet.t -> IdentSet.t.
Variable default: IdentSet.t.

(** We set out to compute a set [x] of variables such that
    [F x] is a subset of [x].  This is called a post-fixed point of [F].

    We use a naive algorithm based on bounded iteration:
    we iterate [F] at most [n] times starting from the empty set
    and stopping as soon as a post-fixed point is found.
    If we are unsuccessful after [n] iterations, we return a default result. *)

Fixpoint iter (n: nat) (x: IdentSet.t) : IdentSet.t :=
  match n with
  | O => default
  | S n' =>
      let x' := F x in
      if IdentSet.subset x' x then x else iter n' x'
  end.

Definition niter := 10%nat.

Definition postfixpoint : IdentSet.t := iter niter IdentSet.empty.

Lemma postfixpoint_charact:
  IdentSet.Subset (F postfixpoint) postfixpoint \/ postfixpoint = default.
Proof.
  unfold postfixpoint. generalize niter, IdentSet.empty. induction n; intros; cbn.
- auto.
- destruct (IdentSet.subset (F t) t) eqn:SUBSET.
+ left. apply IdentSet.subset_2; auto.
+ apply IHn. 
Qed.

Hypothesis F_stable:
  forall x, IdentSet.Subset x default -> IdentSet.Subset (F x) default.

Lemma postfixpoint_upper_bound:
  IdentSet.Subset postfixpoint default.
Proof.
  assert (REC: forall n x, IdentSet.Subset x default -> IdentSet.Subset (iter n x) default).
  { induction n; intros; cbn.
  - fsetdec.
  - destruct (IdentSet.subset (F x) x); auto.
  }
  apply REC. fsetdec.
Qed.

End FIXPOINT.

(** *** Liveness analysis *)

(** [L] is the set of variables that are live "after" command [c].
    The result of [live c L] is the set of variables live "before" [c]. *)

Fixpoint live (c: com) (L: IdentSet.t) : IdentSet.t :=
  match c with
  | SKIP => L
  | ASSIGN x a =>
      if IdentSet.mem x L
      then IdentSet.union (IdentSet.remove x L) (fv_aexp a)
      else L
  | SEQ c1 c2 =>
      live c1 (live c2 L)
  | IFTHENELSE b c1 c2 =>
      IdentSet.union (fv_bexp b) (IdentSet.union (live c1 L) (live c2 L))
  | WHILE b c =>
      let L' := IdentSet.union (fv_bexp b) L in
      let default := IdentSet.union (fv_com (WHILE b c)) L in
      postfixpoint (fun x => IdentSet.union L' (live c x)) default
  end.

(** An upper bound for the variables live "before" is the variables
    live "after" plus all variables used in command [c]. *)

Lemma live_upper_bound:
  forall c L,
  IdentSet.Subset (live c L) (IdentSet.union (fv_com c) L).
Proof.
  induction c; intros; simpl.
- fsetdec.
- destruct (IdentSet.mem x L) eqn:MEM; fsetdec. 
- specialize (IHc1 (live c2 L)). specialize (IHc2 L). fsetdec.
- specialize (IHc1 L). specialize (IHc2 L). fsetdec.
- apply postfixpoint_upper_bound. intros x. specialize (IHc x). fsetdec.
Qed.

(** The variables live at the entry point of a loop satisfy the following
    three conditions. *)

Lemma live_while_charact:
  forall b c L,
  let L' := live (WHILE b c) L in
  IdentSet.Subset (fv_bexp b) L'
  /\ IdentSet.Subset L L'
  /\ IdentSet.Subset (live c L') L'.
Proof.
  intros.
  generalize (postfixpoint_charact
    (fun x : IdentSet.t => IdentSet.union (IdentSet.union (fv_bexp b) L) (live c x))
          (IdentSet.union (IdentSet.union (fv_bexp b) (fv_com c)) L)).
  simpl in L'. fold L'. intros [A|A].
- split. fsetdec. split; fsetdec. 
- rewrite A. split. fsetdec. split. fsetdec. 
  eapply ISProp.subset_trans. apply live_upper_bound. fsetdec.
Qed.

(** ** 3.2.  A compiler optimization: dead code elimination *)

(** *** The program transformation *)

(** Dead code elimination (DCE) consists in replacing assignments 
    [x := a] to dead variables [x] by [SKIP] instructions. The useless
    computation of [a] is eliminated. *)

Fixpoint dce (c: com) (L: IdentSet.t): com :=
  match c with
  | SKIP => SKIP
  | ASSIGN x a => if IdentSet.mem x L then ASSIGN x a else SKIP
  | SEQ c1 c2 => SEQ (dce c1 (live c2 L)) (dce c2 L)
  | IFTHENELSE b c1 c2 => IFTHENELSE b (dce c1 L) (dce c2 L)
  | WHILE b c => WHILE b (dce c (live (WHILE b c) L))
  end.

(** Examples of optimization. *)

Print Euclidean_division.

Eval compute in (dce Euclidean_division (IdentSet.singleton "r")).

(** Effect of the code transformation:
<<
   r := a;                 ===>   r := a;
   q := 0;                        skip;
   while b <= r do                while b <= r do
     r := r - b;                    r := r - b;
     q := q + 1;                    skip;
   done                           done
>>
*)

Eval compute in (dce Euclidean_division (IdentSet.singleton "q")).

(** Here, the program is unchanged. *)

(** *** Semantic preservation *)

(** Two stores agree on a set [L] of live variables
    if they associate the same values to each live variable. *)

Definition agree (L: IdentSet.t) (s1 s2: store) : Prop :=
  forall x, IdentSet.In x L -> s1 x = s2 x.

(** This definition is monotonic with respect to the set [L]. *)

Lemma agree_mon:
  forall L L' s1 s2,
  agree L' s1 s2 -> IdentSet.Subset L L' -> agree L s1 s2.
Proof.
  unfold IdentSet.Subset, agree; intros. auto.
Qed.

(** If two stores agree on the free variables of an expression,
    this expression evaluates to the same value in both stores. *)

Lemma aeval_agree:
  forall a s1 s2, agree (fv_aexp a) s1 s2 -> aeval a s1 = aeval a s2.
Proof.
  induction a; cbn; intros.
- auto.
- apply H. fsetdec. 
- f_equal; [apply IHa1 | apply IHa2]; eapply agree_mon; eauto; fsetdec.
- f_equal; [apply IHa1 | apply IHa2]; eapply agree_mon; eauto; fsetdec.
Qed.

Lemma beval_agree:
  forall b s1 s2, agree (fv_bexp b) s1 s2 -> beval b s1 = beval b s2.
Proof.
  induction b; cbn; intros.
- auto.
- auto.
- f_equal; eapply aeval_agree; eapply agree_mon; eauto; fsetdec.
- f_equal; eapply aeval_agree; eapply agree_mon; eauto; fsetdec.
- f_equal; apply IHb; auto.
- f_equal; [apply IHb1 | apply IHb2]; eapply agree_mon; eauto; fsetdec.
Qed.

(** The [agree] relation is preserved by parallel assignment to a live variable
    (where the same value is assigned to the variable in both stores). *)

Lemma agree_update_live:
  forall s1 s2 L x v,
  agree (IdentSet.remove x L) s1 s2 ->
  agree L (update x v s1) (update x v s2).
Proof.
  unfold agree, update; intros. destruct (string_dec x x0).
- auto.
- apply H. fsetdec.
Qed.

(** The [agree] relation is preserved by unilateral assignment to a
    dead variable. *)

Lemma agree_update_dead:
  forall s1 s2 L x v,
  agree L s1 s2 -> ~IdentSet.In x L ->
  agree L (update x v s1) s2.
Proof.
  unfold agree, update; intros. destruct (string_dec x x0).
- subst x0. contradiction.
- apply H. fsetdec.
Qed.

(** We now prove that dead code elimination preserves the semantics of
    terminating programs.  We use the natural semantics of IMP to show
    the following diagram:
<<
               agree (live c L) s s1
     c / s ----------------------------- dce C L / s1
       |                                         |
       |                                         |
       |                                         |
       v                                         v
      s' -------------------------------------- s1'
                    agree L s' s1'
>>
    The proof is by induction on the execution derivation of [c].
*)

Theorem dce_correct_terminating:
  forall s c s', cexec s c s' ->
  forall L s1,
  agree (live c L) s s1 ->
  exists s1', cexec s1 (dce c L) s1' /\ agree L s' s1'.
Proof.
  induction 1; intros L s1 AG.
- (* SKIP *)
  exists s1; split. constructor. auto.
- (* ASSIGN *)
  cbn in *. destruct (IdentSet.mem x L) eqn:is_live.
  + (* x is live after *)
    assert (EVAL: aeval a s = aeval a s1) by (eapply aeval_agree; eapply agree_mon; eauto; fsetdec).
    econstructor; split.
    apply cexec_assign.
    rewrite EVAL. apply agree_update_live. eapply agree_mon; eauto. fsetdec.
  + (* x is dead after *)
    econstructor; split.
    apply cexec_skip.
    apply agree_update_dead. auto.
    red; intros. assert (IdentSet.mem x L = true) by (apply IdentSet.mem_1; auto). congruence.
- (* SEQ *)
  cbn in *.
  destruct (IHcexec1 _ _ AG) as (s1' & EXEC1 & AG1).
  destruct (IHcexec2 _ _ AG1) as (s2' & EXEC2 & AG2).
  exists s2'; split.
  apply cexec_seq with s1'; auto.
  auto.
- (* IFTHENELSE *)
  cbn in *.
  assert (EVAL: beval b s = beval b s1) by (eapply beval_agree; eapply agree_mon; eauto; fsetdec).
  destruct (IHcexec L s1) as (s1' & EXEC' & AG').
  eapply agree_mon; eauto. destruct (beval b s); fsetdec.
  exists s1'; split.
  apply cexec_ifthenelse. rewrite <- EVAL. destruct (beval b s); auto.
  auto.
- (* WHILE done *)
  change (dce (WHILE b c) L) with (WHILE b (dce c (live (WHILE b c) L))).
  destruct (live_while_charact b c L) as (P & Q & R).
  assert (EVAL: beval b s = beval b s1) by (eapply beval_agree; eapply agree_mon; eauto; fsetdec).
  exists s1; split.
  apply cexec_while_done. congruence.
  eapply agree_mon; eauto.
- (* WHILE loop *)
  change (dce (WHILE b c) L) with (WHILE b (dce c (live (WHILE b c) L))).
  destruct (live_while_charact b c L) as (P & Q & R).
  assert (EVAL: beval b s = beval b s1) by (eapply beval_agree; eapply agree_mon; eauto; fsetdec).
  destruct (IHcexec1 (live (WHILE b c) L) s1) as (s1' & EXEC1 & AG1).
  eapply agree_mon; eauto.
  destruct (IHcexec2 L s1') as (s2' & EXEC2 & AG2).
  auto.
  exists s2'; split.
  apply cexec_while_loop with s1'; auto. congruence.
  auto.
Qed.

(** **** Exercise (3 stars) *)

(** We can prove semantic preservation for all programs, whether terminating
    or diverging, by showing a simulation diagram based on the reduction
    semantics for IMP.  Here is a proof sketch for you to finish. *)

Fixpoint measure (c: com) : nat :=
  match c with
  | ASSIGN x a => 1
  | SEQ c1 c2 => measure c1
  | _ => 0
  end.

Theorem dce_simulation:
  forall c s c' s',
  red (c, s) (c', s') ->
  forall L s1,
  agree (live c L) s s1 ->
  (exists s1', red (dce c L, s1) (dce c' L, s1') /\ agree (live c' L) s' s1')
  \/
  ((measure c' < measure c)%nat /\ dce c L = dce c' L /\ agree (live c' L) s' s1).
Proof.
  intros until s'; intros STEP. dependent induction STEP; intros.
  (* FILL IN HERE *)
Abort.


(** ** 3.3. Register allocation *)

(** In a compiler producing code for a hardware processor,
    the register allocation pass consists in placing the most used
    variables of the program in processor registers (available in
    small number), the remaining variables being stored in memory,
    typically in the stack. *)

(** In the following, we study register allocation at the level of the IMP
    language.  We view register allocation as a renaming of IMP variables
    that aims at reducing the total number of variables used.  Indeed,
    the renaming need not be injective: two variables that are used
    in disjoint parts of the program can be merged. *)

(** Computing a good renaming is an algorithmically-difficult problem,
    equivalent to the graph coloring problem.  We assume that an
    external heuristic provides us with a candidate renaming,
    called [f] below.  We then give sufficient and easily verifiable
    conditions for [f] to be a correct renaming that preserves the
    semantics of the program. *)

Section RENAMING.

Variable f: ident -> ident.   (**r the candidate renaming *)

(** *** Renaming variables in an expression *)

Fixpoint rename_aexp (a: aexp) : aexp :=
  match a with
  | CONST n => CONST n
  | VAR x => VAR (f x)
  | PLUS a1 a2 => PLUS (rename_aexp a1) (rename_aexp a2)
  | MINUS a1 a2 => MINUS (rename_aexp a1) (rename_aexp a2)
  end.

Fixpoint rename_bexp (b: bexp) : bexp :=
  match b with
  | TRUE => TRUE
  | FALSE => FALSE
  | EQUAL a1 a2 => EQUAL (rename_aexp a1) (rename_aexp a2)
  | LESSEQUAL a1 a2 => LESSEQUAL (rename_aexp a1) (rename_aexp a2)
  | NOT b1 => NOT (rename_bexp b1)
  | AND b1 b2 => AND (rename_bexp b1) (rename_bexp b2)
  end.

(** *** Recognizing expressions that are variables *)

Definition expr_is_var (a: aexp): option ident :=
  match a with VAR x => Some x | _ => None end.

Lemma expr_is_var_correct:
  forall a x, expr_is_var a = Some x -> a = VAR x.
Proof.
  unfold expr_is_var; intros. destruct a; congruence.
Qed.

(** *** The code transformation *)

(** The code transformation rename variables as prescribed by [f].
    Furthermore, it eliminates dead code as previously.
    Finally, it eliminates assignments [x := y] where the variables
    [x] and [y] are renamed into the same variable [z]. *)

Fixpoint regalloc (c: com) (L: IdentSet.t) : com :=
  match c with
  | SKIP => SKIP
  | ASSIGN x a =>
      if IdentSet.mem x L then
        match expr_is_var a with
        | None => ASSIGN (f x) (rename_aexp a)
        | Some y => if string_dec (f x) (f y) then SKIP else ASSIGN (f x) (rename_aexp a)
        end
      else SKIP
  | SEQ c1 c2 =>
      SEQ (regalloc c1 (live c2 L)) (regalloc c2 L)
  | IFTHENELSE b c1 c2 =>
      IFTHENELSE (rename_bexp b) (regalloc c1 L) (regalloc c2 L)
  | WHILE b c =>
      WHILE (rename_bexp b) (regalloc c (live (WHILE b c) L))
  end.

(** *** Relating the stores *)

(** We revisit the [agree] relation between stores that we used earlier
    to reason about the DCE optimization.
    Now, two stores [s1] and [s2] agree on the live variables [L] if,
    for each live variable [x] in [L],
    the values of [x] in [s1] and of [f x] in [s2] are the same. *)

Definition agree' (L: IdentSet.t) (s1 s2: store) : Prop :=
  forall x, IdentSet.In x L -> s1 x = s2 (f x).

(** This definition is monotonic with respect to the set [L]. *)

Lemma agree'_mon:
  forall L L' s1 s2,
  agree' L' s1 s2 -> IdentSet.Subset L L' -> agree' L s1 s2.
Proof.
  unfold IdentSet.Subset, agree'; intros. auto.
Qed.

(** If two stores agree on the free variables of an expression,
    this expression in store 1 and its renaming in store 2
    evaluate to the same value. *)

Lemma aeval_agree':
  forall a s1 s2, agree' (fv_aexp a) s1 s2 -> aeval a s1 = aeval (rename_aexp a) s2.
Proof.
  induction a; cbn; intros.
- auto.
- apply H. fsetdec. 
- f_equal; [apply IHa1 | apply IHa2]; eapply agree'_mon; eauto; fsetdec.
- f_equal; [apply IHa1 | apply IHa2]; eapply agree'_mon; eauto; fsetdec.
Qed.

Lemma beval_agree':
  forall b s1 s2, agree' (fv_bexp b) s1 s2 -> beval b s1 = beval (rename_bexp b) s2.
Proof.
  induction b; cbn; intros.
- auto.
- auto.
- f_equal; eapply aeval_agree'; eapply agree'_mon; eauto; fsetdec.
- f_equal; eapply aeval_agree'; eapply agree'_mon; eauto; fsetdec.
- f_equal; apply IHb; auto.
- f_equal; [apply IHb1 | apply IHb2]; eapply agree'_mon; eauto; fsetdec.
Qed.

(** The [agree'] relation is preserved by unilateral assignment to a
    dead variable. *)

Lemma agree'_update_dead:
  forall s1 s2 L x v,
  agree' L s1 s2 -> ~IdentSet.In x L ->
  agree' L (update x v s1) s2.
Proof.
  unfold agree', update; intros. destruct (string_dec x x0).
- subst x0. contradiction.
- apply H. fsetdec.
Qed.

(** The [agree'] relation is preserved by parallel assignment of the same
    value to a live variable [x] and to its renaming [f x],
    provided that no other live variable [z] is renamed into [f x].
    This is a non-interference property that the candidate renaming [f]
    must satisfy. *)

Lemma agree'_update_live:
  forall s1 s2 L x v,
  agree' (IdentSet.remove x L) s1 s2 ->
  (forall z, IdentSet.In z L -> z <> x -> f z <> f x) ->
  agree' L (update x v s1) (update (f x) v s2).
Proof.
  unfold agree', update; intros.
  destruct (string_dec x x0); destruct (string_dec (f x) (f x0)).
- auto.
- congruence.
- exfalso. apply (H0 x0); auto.
- apply H. fsetdec.
Qed.

(** A special case of lemma [agree'_update_live], when the value assigned
    to [x] and [f x] is the value of another variable [y].
    In this case, as observed by Chaitin, the non-interference condition
    can be weakened. *)

Lemma agree'_update_move:
  forall s1 s2 L x y,
  agree' (IdentSet.union (IdentSet.remove x L) (IdentSet.singleton y)) s1 s2 ->
  (forall z, IdentSet.In z L -> z <> x -> z <> y -> f z <> f x) ->
  agree' L (update x (s1 y) s1) (update (f x) (s2 (f y)) s2).
Proof.
  unfold agree', update; intros.
  destruct (string_dec x x0); destruct (string_dec (f x) (f x0)).
- apply H. fsetdec.
- congruence.
- destruct (string_dec x0 y).
  + subst x0. apply H. fsetdec.
  + exfalso. apply (H0 x0); auto.
- apply H. fsetdec.
Qed.

(** A special case of lemma [agree'_update_move] in the case where
    [f x = f y], that is, variables [x] and [y] are placed into
    the same variable.  In this case, the assignment is replaced by [SKIP]. *)

Lemma agree'_update_coalesced_move:
  forall s1 s2 L x y,
  agree' (IdentSet.union (IdentSet.remove x L) (IdentSet.singleton y)) s1 s2 ->
  (forall z, IdentSet.In z L -> z <> x -> z <> y -> f z <> f x) ->
  f x = f y ->
  agree' L (update x (s1 y) s1) s2.
Proof.
  unfold agree', update; intros.
  destruct (string_dec x x0); destruct (string_dec (f x) (f x0)).
- rewrite <- e0, H1. apply H. fsetdec.
- congruence.
- destruct (string_dec x0 y).
  + subst x0. apply H. fsetdec.
  + exfalso. apply (H0 x0); auto.
- apply H. fsetdec.
Qed.

(** *** Semantic preservation *)

(** Grouping together all the non-interference conditions above,
    we obtain a correctness criterion for the renaming [f].
    If this Boolean-valued criterion evaluates to true,
    the renaming is a correct register allocation. *)

Fixpoint correct_allocation (c: com) (L: IdentSet.t) : bool :=
  match c with
  | SKIP =>
      true
  | ASSIGN x a =>
      if IdentSet.mem x L then
        match expr_is_var a with
        | None => 
            IdentSet.for_all (fun z => String.eqb z x || negb (String.eqb (f z) (f x))) L
        | Some y =>
            IdentSet.for_all (fun z => String.eqb z x || String.eqb z y
                                    || negb (String.eqb (f z) (f x))) L
        end
      else true
  | SEQ c1 c2 => 
      correct_allocation c1 (live c2 L) && correct_allocation c2 L
  | IFTHENELSE b c1 c2 =>
      correct_allocation c1 L && correct_allocation c2 L
  | WHILE b c =>
      correct_allocation c (live (WHILE b c) L)
  end.

(** Under the assumption that the renaming [f] satisfies [correct_allocation],
    we prove semantic preservation for register allocation using
    the same simulation diagram as for dead code elimination. *)

Theorem regalloc_correct_terminating:
  forall s c s', cexec s c s' ->
  forall L s1,
  agree' (live c L) s s1 ->
  correct_allocation c L = true ->
  exists s1', cexec s1 (regalloc c L) s1' /\ agree' L s' s1'.
Proof.
  induction 1; intros L s1 AG CORR.
- (* SKIP *)
  exists s1; split. constructor. auto.
- (* ASSIGN *)
  cbn in *. destruct (IdentSet.mem x L) eqn:is_live.
  + (* x is live after *)
    destruct (expr_is_var a) as [y|] eqn:is_var.
    * apply expr_is_var_correct in is_var. subst a.
      assert (NONINTF: forall z, IdentSet.In z L -> z <> x -> z <> y -> f z <> f x).
      { apply IdentSet.for_all_2 in CORR. 
      - intros. apply CORR in H. 
        destruct (String.eqb_spec z x). congruence.
        destruct (String.eqb_spec z y). congruence.
        destruct (String.eqb_spec (f z) (f x)). discriminate. auto.
      - hnf. intros; congruence.
      }
      destruct (string_dec (f x) (f y)).
      ** (* assignment [x := y] was eliminated *)
         econstructor; split.
         apply cexec_skip.
         apply agree'_update_coalesced_move; auto.
      ** (* assignment [x := y] was kept *)
         econstructor; split.
         apply cexec_assign.
         apply agree'_update_move; auto.
    * (* assignment [x := a], general case *)
      assert (EVAL: aeval a s = aeval (rename_aexp a) s1)
      by (eapply aeval_agree'; eapply agree'_mon; eauto; fsetdec).
      assert (NONINTF: forall z, IdentSet.In z L -> z <> x -> f z <> f x).
      { apply IdentSet.for_all_2 in CORR. 
      - intros. apply CORR in H. 
        destruct (String.eqb_spec z x). congruence.
        destruct (String.eqb_spec (f z) (f x)). discriminate. auto.
      - hnf. intros; congruence.
      }
      econstructor; split.
      apply cexec_assign.
      rewrite <- EVAL. apply agree'_update_live; auto. eapply agree'_mon; eauto. fsetdec.
  + (* x is live after *)
    econstructor; split.
    apply cexec_skip.
    apply agree'_update_dead. auto.
    red; intros. assert (IdentSet.mem x L = true) by (apply IdentSet.mem_1; auto). congruence.
- (* SEQ *)
  cbn in *. apply andb_prop in CORR; destruct CORR as [CORR1 CORR2].
  destruct (IHcexec1 _ _ AG CORR1) as (s1' & EXEC1 & AG1).
  destruct (IHcexec2 _ _ AG1 CORR2) as (s2' & EXEC2 & AG2).
  exists s2'; split.
  apply cexec_seq with s1'; auto.
  auto.
- (* IFTHENELSE *)
  cbn in *. apply andb_prop in CORR; destruct CORR as [CORR1 CORR2].
  assert (EVAL: beval b s = beval (rename_bexp b) s1)
  by (eapply beval_agree'; eapply agree'_mon; eauto; fsetdec).
  destruct (IHcexec L s1) as (s1' & EXEC' & AG').
  eapply agree_mon; eauto. destruct (beval b s); fsetdec. destruct (beval b s); auto.
  exists s1'; split.
  apply cexec_ifthenelse. rewrite <- EVAL. destruct (beval b s); auto.
  auto.
- (* WHILE done *)
Local Opaque live.
  cbn in *.
  destruct (live_while_charact b c L) as (P & Q & R).
  assert (EVAL: beval b s = beval (rename_bexp b) s1)
  by (eapply beval_agree'; eapply agree'_mon; eauto; fsetdec).
  exists s1; split.
  apply cexec_while_done. congruence.
  eapply agree_mon; eauto.
- (* WHILE loop *)
  cbn in *.
  destruct (live_while_charact b c L) as (P & Q & R).
  assert (EVAL: beval b s = beval (rename_bexp b) s1)
  by (eapply beval_agree'; eapply agree'_mon; eauto; fsetdec).
  destruct (IHcexec1 (live (WHILE b c) L) s1) as (s1' & EXEC1 & AG1).
  eapply agree_mon; eauto. auto.
  destruct (IHcexec2 L s1') as (s2' & EXEC2 & AG2).
  auto. auto.
  exists s2'; split.
  apply cexec_while_loop with s1'; auto. congruence.
  auto.
Local Transparent live.
Qed.

End RENAMING.

(** *** Examples *)

(** If the renaming is the identity function, register allocation behaves
    just like dead code elimination. *)

Definition trivial_alloc := fun (x: ident) => x.

Eval compute in (correct_allocation trivial_alloc Euclidean_division (IdentSet.singleton "r")).

(** Result: [true]. *)

Eval compute in (regalloc trivial_alloc Euclidean_division (IdentSet.singleton "r")).

(** Result:
<<
   r := a;                 ===>   r := a;
   q := 0;                        skip;
   while b <= r do                while b <= r do
     r := r - b;                    r := r - b;
     q := q + 1;                    skip;
   done                           done
>>
*)

(** Here is a nontrivial renaming that places variables "r" and "a" in
    the same register "a". *)

Definition my_alloc := fun (x: ident) => if string_dec x "r" then "a" else x.

Eval compute in (correct_allocation my_alloc Euclidean_division (IdentSet.singleton "r")).

(** Result: [true]. *)

Eval compute in (regalloc my_alloc Euclidean_division (IdentSet.singleton "r")).

(** Here is the result of register allocation.
    Note the elimination of the assignment [r := a].
<<
   r := a;                 ===>   skip;
   q := 0;                        skip;
   while b <= r do                while b <= a do
     r := r - b;                    a := a - b;
     q := q + 1;                    skip;
   done                           done
>>
*)

(** In contrast, if we try to place variables [r] and [b] in the same location,
    the validation function [correct_allocation] rejects the allocation. *)

Definition wrong_alloc := fun (x: ident) => if string_dec x "r" then "b" else x.

Eval compute in (correct_allocation my_alloc Euclidean_division (IdentSet.singleton "r")).

(** Result [false]. *)

(** ** 3.4. Advanced topic: fixed poitns *)

(** The [Fixpoints] library explains how to compute exact fixed points
    (not approximate post-fixed points) using the Knaster-Tarsky theorem. *)

From CDF Require Import Fixpoints.

(** In this section, we apply this approach to liveness analysis. *)

Section FIXPOINT_FINITE_SETS.

(** First problem: the subset order between finite sets of variables
    is not well founded!  For example, we have the following infinite,
    strictly increasing sequence
<<
  {}, {"0"}, {"0","1"}, {"0","1","2"}, {"0","1","2","3"}, ...
>>

    Therefore, we must restrict ourselves to subsets of a finite
    universe [U] of variables, typically all the variables mentioned
    in the program being analyzed.
*)

Variable U: IdentSet.t.
Definition finset := { x: IdentSet.t | IdentSet.Subset x U }.

(** We equip the type [finset] with the operations and the properties
    expected in the [Fixpoints] library. *)

Program Definition finset_eq (x y: finset) := IdentSet.Equal x y.

Program Definition finset_eq_dec (x y: finset) : {finset_eq x y} + {~finset_eq x y} :=
  match IdentSet.equal x y with true => left _ | false => right _ end.
Next Obligation.
  apply IdentSet.equal_2; auto.
Qed.
Next Obligation.
  red; intros. apply IdentSet.equal_1 in H. congruence.
Qed.

Program Definition finset_le (x y: finset) := IdentSet.Subset x y.

Lemma finset_le_trans:
  forall x y z, finset_le x y -> finset_le y z -> finset_le x z.
Proof.
  intros x y z; apply ISProp.subset_trans.
Qed.
Lemma finset_eq_le: forall x y, finset_eq x y -> finset_le y x.
Proof.
  intros. apply ISProp.subset_equal. apply ISProp.equal_sym. apply H.
Qed.

Program Definition finset_bot : finset := IdentSet.empty.
Next Obligation.
  fsetdec.
Qed.

Lemma finset_bot_smallest: forall x, finset_le finset_bot x.
Proof.
  intros; red; fsetdec.
Qed.

(** We must prove that the strict inclusion order is well founded.
    To this end, we reason on the cardinals (numbers of elements)
    of the sets of variables, which cannot exceed the cardinal
    of the universe [U]. *)

Program Definition finset_cardinal (x: finset) := IdentSet.cardinal x.

Lemma finset_cardinal_max:
  forall x, (finset_cardinal x <= IdentSet.cardinal U)%nat.
Proof.
  intros. apply ISProp.subset_cardinal. apply proj2_sig.
Qed.

Lemma finset_cardinal_le:
  forall x y, finset_le x y -> (finset_cardinal x <= finset_cardinal y)%nat.
Proof.
  intros. apply ISProp.subset_cardinal. apply H.
Qed.

Lemma finset_cardinal_lt: forall x y,
  finset_le x y -> ~finset_eq x y -> (finset_cardinal x < finset_cardinal y)%nat.
Proof.
  intros.
  destruct (IdentSet.choose (IdentSet.diff (proj1_sig y) (proj1_sig x))) as [elt|] eqn:CHOOSE.
- apply IdentSet.choose_1 in CHOOSE.
  apply ISProp.subset_cardinal_lt with elt. auto. fsetdec. fsetdec.
- apply IdentSet.choose_2 in CHOOSE.
  assert (finset_le y x).
  { intros e IN. 
    destruct (ISProp.In_dec e (proj1_sig x)); auto.
    elim (CHOOSE e). apply IdentSet.diff_3; auto. }
  elim H0. apply ISProp.subset_antisym; auto.
Qed.
 
Lemma finset_gt_wf:
  well_founded (fun x y => finset_le y x /\ ~finset_eq y x).
Proof.
  set (M := fun x => (IdentSet.cardinal U - finset_cardinal x)%nat).
  apply wf_incl with (ltof _ M).
- red; intros x y [L E]; red. unfold M.
  generalize (finset_cardinal_max x), (finset_cardinal_max y),
             (finset_cardinal_lt y x L E); intros.
  lia.
- apply well_founded_ltof.
Qed.

(** Now we can instantiate the fixed point computation provided by
    the [Fixpoints] library. *)

Definition monotone (F: finset -> finset) : Prop :=
  forall x y, finset_le x y -> finset_le (F x) (F y).

Definition finset_fixpoint (F: finset -> finset) (M: monotone F) : finset :=
  fixpoint finset finset_eq finset_eq_dec finset_le finset_gt_wf
           finset_bot finset_bot_smallest F M.

Lemma finset_fixpoint_eq:
  forall F M, finset_eq (finset_fixpoint F M) (F (finset_fixpoint F M)).
Proof.
  intros. unfold finset_fixpoint. apply fixpoint_eq.
Qed.

Lemma finset_fixpoint_smallest:
  forall F M z, finset_le (F z) z -> finset_le (finset_fixpoint F M) z.
Proof.
  intros. unfold finset_fixpoint. apply fixpoint_smallest; eauto using finset_le_trans.
Qed.

Lemma finset_fixpoint_mon:
  forall F1 M1 F2 M2,
  (forall x, finset_le (F1 x) (F2 x)) ->
  finset_le (finset_fixpoint F1 M1) (finset_fixpoint F2 M2).
Proof.
  intros. unfold finset_fixpoint. apply fixpoint_mon; eauto using finset_le_trans, finset_eq_le.
Qed.

(** Let's try to redefine liveness analysis, using finite sets [finset]
    and fixed point computation [finset_fixpoint].
*)
 
Fail Fixpoint live' (c: com) (L: finset) : finset :=
  match c with
  | SKIP => L
  | ASSIGN x a =>
      if IdentSet.mem x L
      then IdentSet.union (IdentSet.remove x L) (fv_aexp a)
      else L
  | SEQ c1 c2 =>
      live' c1 (live' c2 L)
  | IFTHENELSE b c1 c2 =>
      IdentSet.union (fv_bexp b) (IdentSet.union (live' c1 L) (live' c2 L))
  | WHILE b c =>
      let L' := IdentSet.union (fv_bexp b) L in
      finset_fixpoint (fun x => IdentSet.union L' (live' c x)) _
  end.

(** First issue: when we take the union of [L] with [fv_aexp a] or
    [fv_bexp b], nothing guarantees that we remain within the universe [U].
    We must, then, add an hypothesis [IdentSet.Subset (fv_com c) U]
    to guarantee that the program [c] under analysis is "contained"
    within universe [U].

    Second issue: in order to use [finset_fixpoint] in the [WHILE] case,
    we must provide [finset_fixpoint] with a proof that its function
    argument is monotonically increasing.  To this end, we must know
    that [live' c] is a monotonically increasing function from
    [finset] to [finset], even though we are in the process of defining
    the function [live'] !  Therefore, we must define [live']
    and at the same time prove that it is increasing.

    Both issues can be solved by giving [live'] a rich dependent type:
*)

Program Fixpoint live' (c: com) (CONT: IdentSet.Subset (fv_com c) U)
                 : { f: finset -> finset | monotone f } :=
  match c with
  | SKIP => fun L => L
  | ASSIGN x a =>
      fun L =>
        if IdentSet.mem x L
        then IdentSet.union (IdentSet.remove x L) (fv_aexp a)
        else L
  | SEQ c1 c2 =>
      fun L => live' c1 _ (live' c2 _ L)
  | IFTHENELSE b c1 c2 =>
      fun L => IdentSet.union (fv_bexp b)
                              (IdentSet.union (live' c1 _ L) (live' c2 _ L))
  | WHILE b c =>
      fun L =>
        let L' := IdentSet.union (fv_bexp b) L in
        finset_fixpoint (fun x => IdentSet.union L' (live' c _ x)) _
  end.
Next Obligation.
  red; auto.
Defined.
Next Obligation.
  cbn in CONT. generalize (proj2_sig L). fsetdec.
Defined.
Next Obligation.
  red; intros. rename x0 into L1. rename y into L2. unfold finset_le in *.
  destruct (IdentSet.mem x (proj1_sig L1)) eqn:M1; cbn.
- replace (IdentSet.mem x (proj1_sig L2)) with true. 
  cbn. fsetdec.
  symmetry. apply IdentSet.mem_1. apply H. apply IdentSet.mem_2; auto.
- destruct (IdentSet.mem x (proj1_sig L2)) eqn:M2; cbn; auto.
  apply IdentSet.mem_2 in M2. apply ISFact.not_mem_iff in M1.
  red; intros z IN. apply IdentSet.union_2. apply IdentSet.remove_2. congruence. auto.
Defined.
Next Obligation.
  cbn in CONT; fsetdec.
Defined.
Next Obligation.
  cbn in CONT; fsetdec.
Defined.
Next Obligation.
  red; intros. auto.
Defined.
Next Obligation.
  cbn in CONT; fsetdec.
Defined.
Next Obligation.
  cbn in CONT; fsetdec.
Defined.
Next Obligation.
  cbn in CONT. generalize (proj2_sig (x L)), (proj2_sig (x0 L)); fsetdec.
Defined.
Next Obligation.
  red; intros; unfold finset_le; cbn.
  destruct (live' c1) as [f1 M1], (live' c2) as [f2 M2]. cbn.
  apply ISProp.union_subset_5.
  apply ISProp.FM.union_s_m. apply M1; auto. apply M2; auto.
Defined.
Next Obligation.
  cbn in CONT; fsetdec.
Defined.
Next Obligation.
  cbn in CONT. generalize (proj2_sig (x0 x)) (proj2_sig L). fsetdec.
Defined.
Next Obligation.
  cbn in CONT. red; intros; unfold finset_le; cbn.
  destruct (live' c) as [f M]; cbn.
  apply ISProp.union_subset_5. apply M; auto.
Defined.
Next Obligation.
  cbn in CONT. red; intros. apply finset_fixpoint_mon.
  intros z; unfold finset_le; cbn.
  destruct (live' c) as [f M]; cbn.
  apply ISProp.union_subset_4. apply ISProp.union_subset_5. auto.
Defined.

(** At long last, we obtain the desired liveness analysis function. *)

Definition live'' (c: com) (CONT: IdentSet.Subset (fv_com c) U) (L: finset) : finset :=
  proj1_sig (live' c CONT) L.

End FIXPOINT_FINITE_SETS.
