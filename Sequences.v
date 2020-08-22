(** A library of operators over relations,
    to define transition sequences and their properties. *)

Set Implicit Arguments.

Section SEQUENCES.

Variable A: Type.                 (**r the type of states *)
Variable R: A -> A -> Prop.       (**r the transition relation between states *)

(** ** Finite sequences of transitions *)

(** Zero, one or several transitions: reflexive transitive closure of [R]. *)

Inductive star: A -> A -> Prop :=
  | star_refl: forall a,
      star a a
  | star_step: forall a b c,
      R a b -> star b c -> star a c.

Lemma star_one:
  forall (a b: A), R a b -> star a b.
Proof.
  eauto using star.
Qed.

Lemma star_trans:
  forall (a b: A), star a b -> forall c, star b c -> star a c.
Proof.
  induction 1; eauto using star. 
Qed.

(** One or several transitions: transitive closure of [R]. *)

Inductive plus: A -> A -> Prop :=
  | plus_left: forall a b c,
      R a b -> star b c -> plus a c.

Lemma plus_one:
  forall a b, R a b -> plus a b.
Proof.
  eauto using star, plus. 
Qed.

Lemma plus_star:
  forall a b,
  plus a b -> star a b.
Proof.
  intros. inversion H. eauto using star.  
Qed.

Lemma plus_star_trans:
  forall a b c, plus a b -> star b c -> plus a c.
Proof.
  intros. inversion H. eauto using plus, star_trans.
Qed.

Lemma star_plus_trans:
  forall a b c, star a b -> plus b c -> plus a c.
Proof.
  intros. inversion H0. inversion H; eauto using plus, star, star_trans.
Qed.

Lemma plus_right:
  forall a b c, star a b -> R b c -> plus a c.
Proof.
  eauto using star_plus_trans, plus_one.
Qed.

(** Absence of transitions from a state. *)

Definition irred (a: A) : Prop := forall b, ~(R a b).

(** ** Infinite transition sequences *)

(** It is easy to characterize the fact that all transition sequences starting
  from a state [a] are infinite: it suffices to say that any finite sequence
  starting from [a] can always be extended by one more transition. *)

Definition all_seq_inf (a: A) : Prop :=
  forall b, star a b -> exists c, R b c.

(** However, this is not the notion we are trying to characterize: the case
  where there exists an infinite sequence of transitions starting from [a],
  [a --> a1 --> a2 --> ... -> aN -> ...]
  leaving open the possibility that there exists finite sequences
  starting from [a].

  Example: consider [A = nat] and [R] such that [R 0 0] and [R 0 1].  
  [all_seq_inf 0] does not hold, because a sequence [0 -->* 1] cannot
  be extended.  Yet, [R] admits an infinite sequence, namely
  [0 --> 0 --> ...].

  Another attempt would be to represent the sequence of states 
  [a0 --> a1 --> a2 --> ... -> aN -> ...] explicitly, as a function 
  [f: nat -> A] such that [f i] is the [i]-th state [ai] of the sequence. *)

Definition infseq_with_function (a: A) : Prop :=
  exists f: nat -> A, f 0 = a /\ forall i, R (f i) (f (1 + i)).

(** This is a correct characterization of the existence of an infinite
  sequence of reductions.  However, it is inconvenient to work with
  this definition in Coq's constructive logic: in most use cases, the
  function [f] is not computable and therefore cannot be defined in Coq.

  However, we do not really need the function [f]: its codomain [X] is
  all we need!  What matters is the existence of a set [X] such as
  [a] is in [X], and
  every [b] in [X] can make a transition to an element of [X].
  This suffices to prove the existence of an infinite sequence of transitions
  starting from [a].
*)

Definition infseq (a: A) : Prop :=
  exists X: A -> Prop,
  X a /\ (forall a1, X a1 -> exists a2, R a1 a2 /\ X a2).

(** This definition is essentially a coinduction principle.
  Let us show some expected properties.  For instance: if relation [R]
  contains a cycle, an infinite sequence exists. *)

Remark cycle_infseq:
  forall a, R a a -> infseq a.
Proof.
  intros. exists (fun b => b = a); split.
  auto.
  intros. subst a1. exists a; auto.
Qed.

(** Mon generally: if all sequences from [a] are infinite, there exists one
  infinite sequence starting in [a]. *)

Lemma infseq_if_all_seq_inf:
  forall a, all_seq_inf a -> infseq a.
Proof.
  intros a0 ALL0. 
  exists all_seq_inf; split; auto.
  intros a1 ALL1. destruct (ALL1 a1) as [a2 R12]. constructor. 
  exists a2; split; auto.
  intros a3 S23. destruct (ALL1 a3) as [a4 R23]. apply star_step with a2; auto.
  exists a4; auto.
Qed.

(** Likewise, the characterization [infseq_with_function] based on functions
  implies [infseq]. *)

Lemma infseq_from_function:
  forall a, infseq_with_function a -> infseq a.
Proof.
  intros a0 (f & F0 & Fn). exists (fun a => exists i, f i = a); split.
- exists 0; auto.
- intros a1 (i1 & F1). subst a1. exists (f (1 + i1)); split; auto. exists (1 + i1); auto.
Qed.  

(** An "inversion lemma" for [infseq]: if [infseq a], i.e. there exists
  an infinite sequence starting in [a], then [a] can transition to a state [b]
  that satisfies [infseq b]. *)

Lemma infseq_inv:
  forall a, infseq a -> exists b, R a b /\ infseq b.
Proof.
  intros a (X & Xa & XP). destruct (XP a Xa) as (b & Rab & Xb). 
  exists b; split; auto. exists X; auto.
Qed.

(** A very useful coinduction principle considers a set [X] where for
  every [a] in [X], we can make one *or several* transitions to reach
  a state [b] that belongs to [X].  *)

Lemma infseq_coinduction_principle:
  forall (X: A -> Prop),
  (forall a, X a -> exists b, plus a b /\ X b) ->
  forall a, X a -> infseq a.
Proof.
  intros X H a0 Xa0. 
  exists (fun a => exists b, star a b /\ X b); split.
- exists a0; auto using star_refl.
- intros a1 (a2 & S12 & X2). inversion S12; subst.
  + destruct (H a2 X2) as (a3 & P23 & X3). inversion P23; subst.
    exists b; split; auto. exists a3; auto.
  + exists b; split; auto. exists a2; auto.
Qed.

(** ** Determinism properties for functional transition relations. *)

(** A transition relation is functional if every state can transition
  to at most one other state. *)

Hypothesis R_functional:
  forall a b c, R a b -> R a c -> b = c.

(** Uniqueness of finite transition sequences. *)

Lemma star_star_inv:
  forall a b, star a b -> forall c, star a c -> star b c \/ star c b.
Proof.
  induction 1; intros.
- auto.
- inversion H1; subst.
+ right. eauto using star. 
+ assert (b = b0) by (eapply R_functional; eauto). subst b0. 
  apply IHstar; auto.
Qed.

Lemma finseq_unique:
  forall a b b',
  star a b -> irred b ->
  star a b' -> irred b' ->
  b = b'.
Proof.
  intros. destruct (star_star_inv H H1).
- inversion H3; subst. auto. elim (H0 _ H4).
- inversion H3; subst. auto. elim (H2 _ H4).
Qed.

(** A state cannot both diverge and terminate on an irreducible state. *)

Lemma infseq_inv':
  forall a b, R a b -> infseq a -> infseq b.
Proof.
  intros a b Rab Ia. 
  destruct (infseq_inv Ia) as (b' & Rab' & Xb').
  assert (b' = b) by (eapply R_functional; eauto). 
  subst b'. auto.
Qed.

Lemma infseq_star_inv:
  forall a b, star a b -> infseq a -> infseq b.
Proof.
  induction 1; intros.
- auto. 
- apply IHstar. apply infseq_inv' with a; auto.
Qed.

Lemma infseq_finseq_excl:
  forall a b,
  star a b -> irred b -> infseq a -> False.
Proof.
  intros.
  destruct (@infseq_inv b) as (c & Rbc & _). eapply infseq_star_inv; eauto. 
  apply (H0 c); auto.
Qed.

(** If there exists an infinite sequence of transitions from [a],
  all sequences of transitions arising from [a] are infinite. *)

Lemma infseq_all_seq_inf:
  forall a, infseq a -> all_seq_inf a.
Proof.
  intros. unfold all_seq_inf. intros.
  destruct (@infseq_inv b) as (c & Rbc & _). eapply infseq_star_inv; eauto.
  exists c; auto.
Qed.

End SEQUENCES.



