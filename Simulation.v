From Coq Require Import Psatz.
From CDF Require Import Sequences.

(** A generic simulation diagram, to prove semantic equivalence of two
    programs based on their small-step semantics. *)

Section SIMULATION_DIAGRAM.

(** The diagram is parameterized by
    - the small-step semantics for each of the two programs:
      type of configurations and transition relation between configurations;
    - an invariant that connects the configurations of the two programs
    - a nonnegative measure over source configurations.
*)

Variable C1: Type.	            (**r the type of configurations for the source program *)
Variable step1: C1 -> C1 -> Prop.   (**r its transition relation *)

Variable C2: Type.	            (**r the type of configurations for the transformed program *)
Variable step2: C2 -> C2 -> Prop.   (**r its transition relation *)

Variable inv: C1 -> C2 -> Prop.     (**r the invariant *)

Variable measure: C1 -> nat.        (**r the measure that prevents infinite stuttering *)

(** The diagram properly speaking is the following assumption:
    every source program transition is simulated by zero, one or several
    transitions of the transformed program, while preserving the invariant
    and decreasing the measure in the stuttering case. *)

Hypothesis simulation:
  forall c1 c1', step1 c1 c1' ->
  forall c2, inv c1 c2 ->
  exists c2',
     (plus step2 c2 c2' \/ (star step2 c2 c2' /\ measure c1' < measure c1))
  /\ inv c1' c2'.

(** We first extend the simulation diagram to finite sequences of
    source transitions.  This is the crucial lemma to show semantic
    preservation when the source program terminates. *)

Lemma simulation_star:
  forall c1 c1', star step1 c1 c1' ->
  forall c2, inv c1 c2 ->
  exists c2', star step2 c2 c2' /\ inv c1' c2'.
Proof.
  induction 1; intros.
- (* zero transitions *)
  exists c2; split. apply star_refl. auto.
- (* one or several transitions *)
  destruct (simulation _ _ H _ H1) as (c2' & P & Q).
  destruct (IHstar _ Q) as (c2'' & U & V).
  exists c2''; split. 
  eapply star_trans; eauto. destruct P. apply plus_star; auto. destruct H2; auto.
  auto.
Qed.

(** Now consider a source program that performs infinitely many
    transitions.  We first show that the transformed program can
    always make progress (perform at least one transition) while
    preserving the invariant [inv].  The proof is by induction on [N],
    the greatest number of stuttering steps that the transformed
    program can make before being forced to take at least one
    transition. *)

Lemma simulation_infseq_productive:
  forall N c1 c2,
  measure c1 < N ->
  infseq step1 c1 ->
  inv c1 c2 ->
  exists c1', exists c2',
      plus step2 c2 c2'
   /\ infseq step1 c1'
   /\ inv c1' c2'.
Proof.
  induction N; intros c1 c2 MEAS INF1 INV.
- (* N = 0 *)
  lia.
- (* N > 0 *)
  destruct (infseq_inv INF1) as (c1' & STEP1 & INF1').
  destruct (simulation _ _ STEP1 _ INV) as (c2' & P & INV').
  destruct P as [STEPS2 | [STEPS2 MEAS']].
  + (* one or several *)
    exists c1'; exists c2'; auto.
  + (* zero, one or several transitions *)
    inversion STEPS2; subst; clear STEPS2.
    * (* zero transitions *)
      eapply IHN; eauto. lia.
    * (* one or several transitions *)
      exists c1'; exists c2'; split. eapply plus_left; eauto. auto.
Qed.

(** As a consequence, the transformed program performs infinitely many
    transitions if started in a configuration that is related to a
    diverging configuration of the source program. *)

Lemma simulation_infseq:
  forall c1 c2,
  infseq step1 c1 ->
  inv c1 c2 ->
  infseq step2 c2.
Proof.
  intros. 
  apply infseq_coinduction_principle with
    (X := fun c2 => exists c1, infseq step1 c1 /\ inv c1 c2).
- clear c1 c2 H H0. intros c2 (c1 & INF & INV).  
  destruct (simulation_infseq_productive (measure c1 + 1) c1 c2) 
  as (c1' & c2' & PLUS2 & INF' & INV').
  lia. auto. auto.
  exists c2'; split. auto. exists c1'; auto. 
- exists c1; auto.
Qed.

End SIMULATION_DIAGRAM.
