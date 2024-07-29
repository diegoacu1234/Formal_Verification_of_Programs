(* Natural numbers *)

Lemma right_zero_addition: forall a: nat, a + 0 = a.
Proof.
  intros a.
  induction a.
  - simpl. reflexivity.
  - simpl. rewrite IHa. reflexivity.
Qed.

Theorem zero_addition_commutative: forall a: nat, a + 0 = 0 + a.
Proof.
  intro a.
  simpl.
  rewrite right_zero_addition.
  reflexivity.
Qed.

Lemma successor_distribution: forall a b : nat, a + S(b) = S(a + b).
Proof.
  intros a b.
  induction a.
  - simpl. reflexivity.
  - simpl. rewrite IHa. reflexivity.
Qed.

Theorem addition_commutative: forall a b : nat, a + b = b + a.
Proof.
  intros a b.
  induction a.
  - rewrite -> right_zero_addition. reflexivity.
  - rewrite successor_distribution. simpl. rewrite IHa. reflexivity.
Qed.

Theorem addition_associative: forall a b c: nat, (a + b) + c = a + (b + c).
Proof.
  intros a b c.
  induction a.
  - simpl. reflexivity.
  - simpl. rewrite IHa. reflexivity.
Qed.
