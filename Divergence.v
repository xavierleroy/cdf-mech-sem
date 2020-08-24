From Coq Require Import Arith ZArith Psatz Bool String List.
From CDF Require Import Sequences IMP Compil.

(** * 6.  Semantics of divergence, first part *)

(** Some proofs in this file are not constructive and use classical logic
    through axioms, namely the axiom of excluded middle and an
    axiom of description.  These axioms are imported from the Coq
    standard library. *)

From Coq Require Import Classical Description.

Check classic.
Check constructive_definite_description.

(** ** 6.1.  Bounded interpreter *)

(** Let's reconsider the reference interpreter [cexec_f] from module [IMP],
    rewritten in monadic style.  Recall that termination of the interpreter
    is ensured by the "fuel" parameter that decreases at each recursive call.
    If the fuel drops to zero, the interpreter returns [None],
    meaning that the final store at the end of the command execution
    could not be determined: either the command diverges or we need more
    fuel to execute it to completion. *)


Definition bind {A B: Type} (m: option A) (f: A -> option B) : option B :=
  match m with None => None | Some s => f s end.

Fixpoint cinterp (fuel: nat) (c: com) (s: store) : option store :=
  match fuel with
  | O => None
  | S n =>
      match c with
      | SKIP => Some s
      | ASSIGN x a => Some (update x (aeval a s) s)
      | SEQ c1 c2 => bind (cinterp n c1 s) (cinterp n c2)
      | IFTHENELSE b c1 c2 =>
          cinterp n (if beval b s then c1 else c2) s
      | WHILE b c1 =>
          if beval b s
          then bind (cinterp n c1 s) (cinterp n (WHILE b c1))
          else Some s
      end
  end.

(** A crucial property of this bounded interpreter is that the [cinterp]
    function is monotonically increasing: more fuel gives a more defined
    result according to the following [<<=] order. *)

Inductive lessdef {A: Type}: option A -> option A -> Prop :=
  | lessdef_none: forall oa, lessdef None oa
  | lessdef_some: forall a, lessdef (Some a) (Some a).

Notation "x <<= y" := (lessdef x y) (at level 70, no associativity).

Hint Constructors lessdef : lessdef.

Remark lessdef_refl: forall (A: Type) (x: option A), x <<= x.
Proof.
  destruct x; auto with lessdef.
Qed.

Remark bind_mono: forall (A B: Type) (x x': option A) (f f': A -> option B),
  x <<= x' -> (forall v, f v <<= f' v) ->
  bind x f <<= bind x' f'.
Proof.
  intros. destruct H; cbn; auto with lessdef.
Qed.

Lemma cinterp_mono:
  forall i j c s, i <= j -> cinterp i c s <<= cinterp j c s.
Proof.
  induction i as [ | i]; intros; cbn.
- auto with lessdef.
- destruct j as [ | j]. lia. cbn.
  destruct c; auto with lessdef.
  + apply bind_mono. apply IHi; lia. intros; apply IHi; lia.
  + apply IHi; lia.
  + destruct (beval b s); auto with lessdef.
    apply bind_mono. apply IHi; lia. intros; apply IHi; lia.
Qed.

(** ** 6.2.  From the bounded interpreter to a denotational semantics *)

(** Any sequence  [nat -> option A] that is increasing for the [<<=] order
    is constant: once a certain index is reached, the values in the
    sequence no longer change.  The value in question is called the limit of
    the sequence. *)

Section LIMIT.

Context {A: Type} (f: nat -> option A).

Hypothesis f_mono: forall i j, i <= j -> f i <<= f j.

Lemma limit_exists:
  { lim : option A | exists i, forall j, i <= j -> f j = lim }.
Proof.
  apply constructive_definite_description.
  destruct (classic (forall i, f i = None)) as [DIV|TERM].
- exists None; split.
  + exists O; auto.
  + intros lim (i & LIM). rewrite <- (DIV i). apply LIM; lia.
- apply not_all_ex_not in TERM. destruct TERM as (i & TERM).
  exists (f i); split.
  + exists i; intros. destruct (f_mono i j H). congruence. auto.
  + intros lim (i2 & LIM2). set (j := Nat.max i i2).
    rewrite <- (LIM2 j) by lia.
    destruct (f_mono i j). lia. congruence. auto.
Qed.

Definition limit : option A := proj1_sig limit_exists.

Lemma limit_charact: exists i, forall j, i <= j -> f j = limit.
Proof.
  unfold limit; apply proj2_sig.
Qed.

End LIMIT.

(** We define the denotation of a command [c] in initial store [s]
    as the limit of the interpretation of [c] when fuel goes to infinity. *)

Definition denot (c: com) (s: store) : option store :=
  limit (fun n => cinterp n c s) (fun i j => cinterp_mono i j c s).

Lemma denot_charact: 
  forall c s, exists i, forall j, i <= j -> cinterp j c s = denot c s.
Proof.
  intros. apply limit_charact.
Qed.

Lemma denot_unique:
  forall c s i lim,
  (forall j, i <= j -> cinterp j c s = lim) -> denot c s = lim.
Proof.
  intros. destruct (denot_charact c s) as (i' & LIM').
  set (j := Nat.max i i').
  rewrite <- (H j), <- (LIM' j) by lia. auto.
Qed.

Lemma denot_some: forall n c s s',
  cinterp n c s = Some s' -> denot c s = Some s'.
Proof.
  intros. apply denot_unique with n.
  intros. destruct (cinterp_mono n j c s H0); congruence.
Qed.

Lemma denot_none: forall c s,
  (forall n, cinterp n c s = None) <-> denot c s = None.
Proof.
  intros; split; intros.
- apply denot_unique with O. auto.
- destruct (cinterp n c s) as [s'|] eqn:C; auto.
  apply denot_some in C. congruence.
Qed.

Lemma denot_eq: forall c s n,
  cinterp n c s = None \/ cinterp n c s = denot c s.
Proof.
  intros. destruct (cinterp n c s) as [s'|] eqn:C; auto.
  right; symmetry; apply denot_some with n; auto.
Qed.

(** This definition of [denot] satisfies the expected equations for
    an IMP denotational semantics. *)

Lemma denot_skip: forall s,
  denot SKIP s = Some s.
Proof.
  intros. apply denot_some with 1. auto.
Qed.

Lemma denot_assign: forall x a s,
  denot (ASSIGN x a) s = Some (update x (aeval a s) s).
Proof.
  intros. apply denot_some with 1. auto.
Qed.

Lemma denot_seq: forall c1 c2 s,
  denot (SEQ c1 c2) s = bind (denot c1 s) (denot c2).
Proof.
  intros. unfold bind.
  destruct (denot_charact c1 s) as  (i1 & LIM1).
  destruct (denot c1 s) as [s1|] eqn:D1.
- destruct (denot_charact c2 s1) as  (i2 & LIM2).
  apply denot_unique with (S (Nat.max i1 i2)); intros.
  destruct j as [ | j]. lia. cbn.
  unfold bind. rewrite LIM1, LIM2 by lia. auto.
- apply denot_none. intros. destruct n; cbn; auto.
  destruct (denot_eq c1 s n) as [E|E]; rewrite E, ?D1; auto.
Qed.

Lemma denot_ifthenelse: forall b c1 c2 s,
  denot (IFTHENELSE b c1 c2) s = if beval b s then denot c1 s else denot c2 s.
Proof.
  intros. 
  set (c := if beval b s then c1 else c2).
  destruct (denot_charact c s) as (i & LIM).
  apply denot_unique with (S i). intros. destruct j as [ | j]. lia.
  cbn. rewrite LIM by lia. unfold c; destruct (beval b s); auto.
Qed.

Lemma denot_while: forall b c s,
  denot (WHILE b c) s =
  if beval b s then bind (denot c s) (denot (WHILE b c)) else Some s.
Proof.
  intros. rewrite <- denot_seq. set (c' := c ;; WHILE b c).
  destruct (denot_charact c' s) as (i & LIM).
  apply denot_unique with (S i). intros. destruct j as [ | j]. lia.
  cbn. destruct (beval b s). apply (LIM (S j)). lia.
  auto.
Qed.

(** Moreover, the denotation of a loop is the least function
    [F: store -> option store] that satisfies the loop equation above. *)

Lemma denot_while_min: forall b c F,
  (forall s, F s = if beval b s then bind (denot c s) F else Some s) ->
  (forall s, denot (WHILE b c) s <<= F s).
Proof.
  intros b c F EQ.
  assert (REC: forall n s, cinterp n (WHILE b c) s <<= F s).
  { induction n as [ | n]; intros; cbn.
  - auto with lessdef.
  - rewrite EQ. destruct (beval b s); auto with lessdef.
    apply bind_mono; auto with lessdef.
    destruct (denot_eq c s n) as [E|E]; rewrite E; auto using lessdef_refl with lessdef.
  }
  intros. destruct (denot_charact (WHILE b c) s) as (i & LIM).
  rewrite <- (LIM i) by lia. apply REC.
Qed.

(** Equivalence with natural semantics.  One direction of the equivalence
    is a simple induction on a derivation of [cexec s c s'],
    using the denotational semantics equations. *)

Lemma cexec_denot: forall s c s', cexec s c s' -> denot c s = Some s'.
Proof.
  induction 1; intros.
- apply denot_skip.
- apply denot_assign.
- rewrite denot_seq, IHcexec1; auto.
- rewrite denot_ifthenelse. destruct (beval b s); auto.
- rewrite denot_while, H. auto.
- rewrite denot_while, H, IHcexec1; auto.
Qed.

(** In the other direction, we first show, by induction over [n],
    that [cinterp n c s = Some s'] implies [cexec s c s']. *)

Lemma cinterp_cexec: forall n c s s', cinterp n c s = Some s' -> cexec s c s'.
Proof.
  induction n as [ | n]; simpl; intros.
- discriminate.
- destruct c.
  + inversion H; apply cexec_skip.
  + inversion H; apply cexec_assign.
  + destruct (cinterp n c1 s) as [s1|] eqn:C1; try discriminate. simpl in H.
    apply cexec_seq with s1; auto.
  + apply cexec_ifthenelse; auto.
  + destruct (beval b s) eqn:B.
    * destruct (cinterp n c s) as [s1|] eqn:C1; try discriminate. simpl in H.
      apply cexec_while_loop with s1; auto.
    * inversion H; subst; apply cexec_while_done; auto.
Qed.

(** The result follow from the definition of [denot] as a limit. *)

Lemma denot_cexec: forall s c s', denot c s = Some s' -> cexec s c s'.
Proof.
  intros. destruct (denot_charact c s) as (i & LIM).
  apply cinterp_cexec with i. rewrite LIM by lia. auto.
Qed.

(** ** 6.3.  Coinductive natural semantics *)

(** The predicate [cexecinf s c] means that command [c] started in
    initial store [s] diverges.  The predicate is defined coinductively
    in natural semantics style. *)

CoInductive cexecinf: store -> com -> Prop :=
  | cexecinf_seq_1: forall c1 c2 s,
      cexecinf s c1 -> cexecinf s (SEQ c1 c2)
  | cexecinf_seq_2: forall c1 c2 s s',
      cexec s c1 s' -> cexecinf s' c2 -> cexecinf s (SEQ c1 c2)
  | cexecinf_ifthenelse: forall b c1 c2 s,
      cexecinf s (if beval b s then c1 else c2) ->
      cexecinf s (IFTHENELSE b c1 c2)
  | cexecinf_while_1: forall b c s,
      beval b s = true -> cexecinf s c ->
      cexecinf s (WHILE b c)
  | cexecinf_while_2: forall b c s s',
      beval b s = true -> cexec s c s' -> cexecinf s' (WHILE b c) ->
      cexecinf s (WHILE b c).

(** It is easy to show that the loop [WHILE TRUE SKIP] diverges
    according to this semantics. *)

Remark cexecinf_while_true_skip:
  forall s, cexecinf s (WHILE TRUE SKIP).
Proof.
  cofix CIH; intros.
  eapply cexecinf_while_2.
  auto.
  apply cexec_skip.
  apply CIH.
Qed.

(** Going further, we show that if [cexecinf s c] is derivable,
    there exists an infinite sequence of reductions from [c,s]. *)

Lemma red_seq_steps_plus:
  forall c2 s c s' c',
  plus red (c, s) (c', s') -> plus red ((c;;c2), s) ((c';;c2), s').
Proof.
  intros. inversion H; subst. destruct b as [c1 s1]. 
  econstructor. apply red_seq_step; eauto. apply red_seq_steps; auto.
Qed.

Lemma cexecinf_productive: forall c s,
  cexecinf s c -> exists c' s', plus red (c, s) (c', s') /\ cexecinf s' c'.
Proof.
  induction c; intros s EXEC; inversion EXEC; subst.
- destruct (IHc1 _ H1) as (c' & s' & R & E).
  exists (c' ;; c2), s'; split. 
  apply red_seq_steps_plus; auto. 
  apply cexecinf_seq_1; auto.
- exists c2, s'; split.
  eapply plus_right. apply red_seq_steps. apply cexec_to_reds; eauto.
  constructor.
  auto.
- do 2 econstructor; split.
  apply plus_one. constructor.
  auto.
- do 2 econstructor; split.
  apply plus_one. apply red_while_loop; auto.
  apply cexecinf_seq_1; auto.
- do 2 econstructor; split.
  eapply plus_right.
  eapply star_step. apply red_while_loop; auto.
  apply red_seq_steps. apply cexec_to_reds; eauto. 
  constructor.
  auto.
Qed.

Lemma cexecinf_to_diverges:
  forall s c, cexecinf s c -> diverges s c.
Proof.
  intros. set (X := fun cs => cexecinf (snd cs) (fst cs)).
  red. apply (infseq_coinduction_principle X).
- intros (c1 & s1) D. 
  destruct (cexecinf_productive _ _ D) as (c2 & s2 & P & D').
  exists (c2, s2); auto.
- auto.
Qed.

(** The converse implication --- from an infinite sequence of reductions,
    build a derivation of [cexecinf s c] --- is more difficult. *)

(** Given a configuration [(c, s)], we want to know whether reductions
    terminate in a finite number of steps on [("SKIP", s')] or an
    infinite sequence of reductions is possible.  This is the halting
    problem in a disguise.  Therefore, the proof is non-constructive
    by necessity, and uses the excluded middle axiom. *)

Lemma red_progress:
  forall c s, c = SKIP \/ exists c', exists s', red (c, s) (c', s').
Proof.
  induction c; intros.
- auto.
- right; do 2 econstructor; apply red_assign.
- right. destruct (IHc1 s) as [E | (c1' & s' & R)].
  + subst c1. do 2 econstructor; apply red_seq_done.
  + do 2 econstructor; apply red_seq_step; eauto.
- right. do 2 econstructor; apply red_ifthenelse.
- right. destruct (beval b s) eqn:B.
  + do 2 econstructor; apply red_while_loop; auto.
  + do 2 econstructor; apply red_while_done; auto.
Qed.

Lemma terminates_or_diverges:
  forall c s, diverges s c \/ exists s', terminates s c s'.
Proof.
  intros. destruct (classic (all_seq_inf red (c, s))).
- left. apply infseq_if_all_seq_inf; auto.
- apply not_all_ex_not in H. destruct H as ((c' & s') & H).
  apply imply_to_and in H. destruct H as [STAR H].
  destruct (red_progress c' s') as [E | (c'' & s'' & RED)].
  subst c'. right; exists s'; auto.
  elim H; exists (c'', s''); auto.
Qed.

(** We can, then, show inversion lemmas that analyze the structure
    of infinite reduction sequences for [SEQ] and [WHILE] commands. *)

Lemma diverges_steps_inv: forall c s c' s',
  diverges s c -> star red (c, s) (c', s') -> diverges s' c'.
Proof.
  intros. apply infseq_star_inv with (c, s); auto.
  intros; eapply red_determ; eauto.
Qed.

Lemma terminates_not_diverges:
  forall s c s', terminates s c s' -> diverges s c -> False.
Proof.
  intros. 
  assert (D: diverges s' SKIP).
  { eapply diverges_steps_inv; eauto. }
  apply infseq_inv in D. destruct D as (b & R & I). inversion R.
Qed.

Lemma diverges_seq_inv: forall s c1 c2,
  diverges s (c1 ;; c2) ->
  diverges s c1 \/ exists s', terminates s c1 s' /\ diverges s' c2.
Proof.
  intros. destruct (terminates_or_diverges c1 s) as [D | (s' & T)].
- auto.
- right; exists s'; split; auto.
  eapply diverges_steps_inv. eauto.
  eapply star_trans. apply red_seq_steps; eauto.
  apply star_one; constructor.
Qed.

Lemma diverges_loop_inv: forall s b c,
  diverges s (WHILE b c) ->
  beval b s = true /\
  (diverges s c \/ exists s', terminates s c s' /\ diverges s' (WHILE b c)).
Proof.
  intros. apply infseq_inv in H. destruct H as ((c1 & s1) & R1 & INF1).
  inversion R1; subst.
- elim (terminates_not_diverges s1 SKIP s1); auto. apply star_refl.
- split; auto.
  destruct (terminates_or_diverges c s1) as [D | (s2 & T)].
+ auto.
+ right; exists s2; split; auto.
  eapply diverges_steps_inv. eauto.
  eapply star_trans. apply red_seq_steps; eauto.
  apply star_one; constructor.
Qed.

(** Finally we prove the expected implication, by coinduction. *)

Lemma diverges_to_cexecinf:
  forall s c, diverges s c -> cexecinf s c.
Proof.
  cofix CIH; intros s c D. destruct c.
- (* SKIP *)
  eelim terminates_not_diverges; eauto.  apply star_refl.
- (* ASSIGN *)
  eelim terminates_not_diverges; eauto.  apply star_one. constructor.
- (* SEQ *)
  destruct (diverges_seq_inv _ _ _ D) as [D1 | (s' & T1 & D2)].
  + apply cexecinf_seq_1; auto.
  + apply cexecinf_seq_2 with s'; auto using reds_to_cexec.
- (* IFTHENELSE *)
  apply infseq_inv in D. destruct D as ((c' & s') & R & D).
  inversion R; subst.
  apply cexecinf_ifthenelse; auto.
- (* WHILE *)
  destruct (diverges_loop_inv _ _ _ D) as (B & [D1 | (s' & T1 & D2)]).
  + apply cexecinf_while_1; auto.
  + apply cexecinf_while_2 with s'; auto using reds_to_cexec.
Qed.

(** ** 6.4.  Application to compiler verification *)

Local Open Scope Z_scope.

(** In the second lecture, we used natural semantics to show that
    terminating IMP programs are correctly compiled. *)

Lemma compile_com_correct_terminating:
  forall s c s',
  cexec s c s' ->
  forall C pc σ,
  code_at C pc (compile_com c) ->
  transitions C
      (pc, σ, s)
      (pc + codelen (compile_com c), σ, s').
Proof Compil.compile_com_correct_terminating.

(** That was a nice proof, but it gave no guarantees on the compilation
    of diverging IMP programs.  That led us to set up a different, more
    complex proof based on transition semantics and simulation diagrams. *)

(** Now that we have a natural semantics for diverging programs,
    we can use it to give a relatively simple proof that diverging
    programs are compiled to machine code that runs forever. *)

Lemma compile_com_productive:
  forall c s,
  cexecinf s c ->
  forall C pc σ,
  code_at C pc (compile_com c) ->
  exists c' pc' s',
     plus (transition C) (pc, σ, s) (pc', σ, s')
  /\ cexecinf s' c'
  /\ code_at C pc' (compile_com c').
Proof.
  induction c; intros s EXEC C pc σ CODEAT;
  inversion EXEC; subst; clear EXEC; simpl in CODEAT.
- (* SEQ, left *)
  eapply IHc1; eauto with code.
- (* SEQ, right *)
  edestruct IHc2 as (c' & pc' & s'' & PLUS & EXEC' & CODEAT'); eauto with code.
  exists c', pc', s''; split; auto.
  eapply star_plus_trans. eapply compile_com_correct_terminating; eauto with code. exact PLUS.
- (* IFTHENELSE *)
  set (code1 := compile_com c1) in *.
  set (code2 := compile_com c2) in *.
  set (codeb := compile_bexp b 0 (codelen code1 + 1)) in *.
  destruct (beval b s) eqn:B.
  + (* The "then" branch is executed *)
    edestruct IHc1 as (c' & pc' & s' & PLUS & EXEC' & CODEAT'); eauto with code.
    exists c', pc', s'; split; auto.
    eapply star_plus_trans. eapply compile_bexp_correct with (b := b); eauto with code.
    fold codeb. rewrite B. autorewrite with code. eexact PLUS.
  + (* The "else" branch is executed *)
    edestruct IHc2 as (c' & pc' & s' & PLUS & EXEC' & CODEAT'); eauto with code.
    exists c', pc', s'; split; auto.
    eapply star_plus_trans. eapply compile_bexp_correct with (b := b); eauto with code.
    fold codeb. rewrite B. autorewrite with code. eexact PLUS.
- (* WHILE, first iteration diverges *)
    edestruct IHc as (c' & pc' & s' & PLUS & EXEC' & CODEAT'); eauto with code.
    exists c', pc', s'; split; auto.
    eapply star_plus_trans. eapply compile_bexp_correct with (b := b); eauto with code.
    rewrite H2. autorewrite with code. eexact PLUS.
- (* WHILE, first iteration terminates *)
  exists (WHILE b c), pc, s'; split; auto.
  eapply star_plus_trans. eapply compile_bexp_correct with (b := b); eauto with code.
  rewrite H1. autorewrite with code. 
  eapply star_plus_trans. eapply compile_com_correct_terminating; eauto with code.
  apply plus_one. eapply trans_branch. eauto with code. lia.
Qed.

Corollary compile_com_correct_diverging:
  forall s c,
  cexecinf s c ->
  forall C pc σ,
  code_at C pc (compile_com c) ->
  infseq (transition C) (pc, σ, s).
Proof.
  intros. 
  set (X := fun (pcss: config) =>
              let '(pc, σ, s) := pcss in
              exists c, cexecinf s c /\ code_at C pc (compile_com c)).
  apply infseq_coinduction_principle with X.
- intros [[pc1 σ1] s1] (c1 & EXEC & CODEAT).
  edestruct (compile_com_productive _ _ EXEC) as (c' & pc' & s' & PLUS & EXEC' & CODEAT'); eauto.
  exists (pc', σ1, s'); split. exact PLUS. exists c'; auto.
- exists c; auto.
Qed.
