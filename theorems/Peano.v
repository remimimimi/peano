Require Import ssreflect.
Set Implicit Arguments.
Set Asymmetric Patterns.

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
Proof. done. Qed.

Lemma a_plus_o : forall a, a +++ O = a.
Proof. by elim=>> //= ->. Qed.

Example two_plus_two : S (S O) +++ S (S (S O)) = S (S (S (S (S O)))).
Proof. done. Qed.

Lemma plus_comm : forall a b, a +++ b = b +++ a.
Proof.
  elim => [| a IHa] b;
    by [rewrite a_plus_o | rewrite a_plus_s_b -IHa].
Qed.

Lemma s_a_plus_b : forall a b, S a +++ b = S (a +++ b).
Proof. done. Qed.

Lemma plus_assoc : forall a b c, a +++ (b +++ c) = (a +++ b) +++ c.
Proof.
  move => a + c; elim=> /= [| b IHb].
  - by rewrite a_plus_o.
  - by rewrite a_plus_s_b;
       rewrite IHb;
       rewrite a_plus_s_b;
       rewrite s_a_plus_b.
Qed.

Lemma s_a_eq_s_b : forall a b, S a = S b -> a = b.
Proof.
  (* TODO: replace inversion by ssreflect more natural (haha) approach *)
  move =>> succ_eq; by inversion succ_eq.
Qed.

Lemma a_eq_b : forall a b, a = b -> S a = S b.
Proof. by move =>> ->. Qed.

Fixpoint mul (n : natural) (m : natural) : natural :=
  match n with
  | O => O
  | S num => m +++ (mul num m)
  end.
Notation "A *** B" := (mul A B) (at level 40, left associativity).

Axiom a_mul_o : forall a, a *** O = O.
Axiom a_mul_s_b : forall a b, a *** S b = a +++ (a *** b).

Lemma o_mul_a : forall a, O *** a = O.
Proof. done. Qed.

Lemma a_mul_s_o : forall a, a *** S O = a.
Proof.
  elim => [| a IHa]; by [|rewrite -{2}IHa].
Qed.

Lemma s_o_mul_a : forall a, S O *** a = a.
Proof.
  move =>> //=; by rewrite a_plus_o.
Qed.

Lemma mul_comm : forall a b, a *** b = b *** a.
Proof.
  elim => [| a IHa] b; by [rewrite a_mul_o | rewrite a_mul_s_b -IHa].
Qed.

Lemma s_a_mul_b : forall a b, S a *** b = b +++ (b *** a).
Proof.
  elim => /= [| a IHa] b;
    by [rewrite a_mul_o | rewrite a_mul_s_b mul_comm].
Qed.

Lemma mul_distr : forall a b c, a *** (b +++ c) = a *** b +++ a *** c.
Proof.
  move => a + c; elim => [| b IHb].
  - by rewrite a_mul_o.
  - by rewrite a_mul_s_b -plus_assoc -IHb -a_mul_s_b -s_a_plus_b.
Qed.

Lemma mul_assoc : forall a b c, a *** (b *** c) = (a *** b) *** c.
Proof.
  move => a b +; elim => [| c IHc].
  - by do 3! rewrite a_mul_o.
  - by do 2! rewrite a_mul_s_b;
       symmetry;
       rewrite mul_comm;
       rewrite mul_distr;
       rewrite mul_comm;
       rewrite IHc.
Qed.
