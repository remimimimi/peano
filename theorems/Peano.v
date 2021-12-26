(* Require Import Bool Arith List Cpdt.CpdtTactics. *)
(* Require Import Cpdt.CpdtTactics. *)
Require Import Bool List.
Set Implicit Arguments.
Set Asymmetric Patterns.

(* Inductive Natural := O | S Natural. *)

Inductive natural : Set :=
  | O : natural
  | S : natural -> natural.

Fixpoint plus (a : natural) (b : natural) : natural :=
  match a with
  | O => b
  | S n => S (plus n b)
  end.
Notation "a +++ b" := (plus a b) (at level 50, left associativity).

Axiom a_plus_one : forall a, a +++ S O = S a.
Axiom a_plus_s_b : forall a b, a +++ S b = S (a +++ b).

Lemma o_plus_a : forall a, O +++ a = a.
  intros.
  unfold plus.
  reflexivity.
Qed.

Lemma a_plus_o : forall a, a +++ O = a.
  intros.
  induction a.
  reflexivity.
  simpl.
  rewrite IHa.
  reflexivity.
Qed.

Lemma plus_comm : forall a b, a +++ b = b +++ a.
  intros.
  induction a.
  symmetry.
  rewrite a_plus_o.
  reflexivity.
  symmetry.
  rewrite a_plus_s_b.
  rewrite <- IHa.
  reflexivity.
Qed.

Lemma s_a_plus_b : forall a b, S a +++ b = S (a +++ b).
  intros.
  induction a.
  reflexivity.
  symmetry.
  rewrite plus_comm.
  rewrite a_plus_s_b.
  simpl.
  rewrite plus_comm.
  reflexivity.
Qed.

Lemma plus_assoc : forall a b c, a +++ (b +++ c) = (a +++ b) +++ c.
  intros.
  induction b.
  rewrite o_plus_a.
  rewrite a_plus_o.
  reflexivity.
  simpl.
  rewrite a_plus_s_b.
  rewrite IHb.
  symmetry.
  rewrite <- a_plus_one.
  rewrite plus_comm.
  rewrite a_plus_s_b.
  rewrite a_plus_s_b.
  rewrite plus_comm.
  rewrite s_a_plus_b.
  rewrite a_plus_o.
  reflexivity.
Qed.

(* Lemma s_a_eq_s_b : forall a b, S a = S b -> a = b. *)
(*   intros. *)
(* Qed. *)

(* Lemma s_a_eq_s_b : forall a b, a = b -> S a = S b. *)
(*   intros. *)
(*   rewrite <- a_plus_one. *)
(*   symmetry. *)
(*   rewrite <- a_plus_one. *)
(* Qed. *)

Fixpoint mul (n : natural) (m : natural) : natural :=
  match n with
  | O => O
  | S num => m +++ (mul num m)
  end.
Notation "A *** B" := (mul A B) (at level 40, left associativity).

Axiom a_mul_o : forall a, a *** O = O.
Axiom a_mul_s_b : forall a b, a *** S b = a +++ (a *** b).

Lemma o_mul_a : forall a, O *** a = O.
  intro.
  reflexivity.
Qed.

Lemma a_mul_s_o : forall a, a *** S O = a.
  intro.
  induction a.
  reflexivity.
  simpl.
  rewrite IHa.
  reflexivity.
Qed.

Lemma s_o_mul_a : forall a, S O *** a = a.
  intro.
  simpl.
  rewrite a_plus_o.
  reflexivity.
Qed.

Lemma mul_comm : forall a b, a *** b = b *** a.
  intros.
  induction a.
  simpl.
  rewrite a_mul_o.
  reflexivity.
  symmetry.
  rewrite a_mul_s_b.
  rewrite <- IHa.
  simpl.
  reflexivity.
Qed.

Lemma s_a_mul_b : forall a b, S a *** b = b +++ (b *** a).
  intros.
  induction a.
  simpl.
  symmetry.
  rewrite a_mul_o.
  reflexivity.
  simpl.
  rewrite a_mul_s_b.
  rewrite mul_comm.
  reflexivity.
Qed.

Lemma mul_distr : forall a b c, a *** (b +++ c) = a *** b +++ a *** c.
  intros.
  (* induction a. *)
  (* reflexivity. *)
  (* simpl. *)

  induction b.
  simpl.
  rewrite a_mul_o.
  reflexivity.
  rewrite a_mul_s_b.
  symmetry.
  rewrite <- plus_assoc.
  rewrite <- IHb.
  rewrite <- a_mul_s_b.
  rewrite <- s_a_plus_b.
  reflexivity.
Qed.

Lemma mul_assoc : forall a b c, a *** (b *** c) = (a *** b) *** c.
  intros.
  induction c.
  rewrite a_mul_o.
  rewrite a_mul_o.
  rewrite a_mul_o.
  reflexivity.
  rewrite a_mul_s_b.
  rewrite a_mul_s_b.
  symmetry.
  rewrite mul_comm.
  rewrite mul_distr.
  rewrite mul_comm.
  rewrite IHc.
  reflexivity.
Qed.
