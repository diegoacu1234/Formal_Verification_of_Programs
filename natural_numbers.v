(* Natural numbers *)

(* Sum *)
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

(* Multiplication *)
Lemma left_one_multiplication: forall a:nat, 1*a = a.
Proof.
intro a.
simpl. rewrite zero_addition_commutative. simpl. reflexivity.
Qed.

Lemma right_one_multiplication: forall a:nat, a*1=a.
Proof.
intro a.
induction a.
- simpl. reflexivity.
- simpl. rewrite IHa. reflexivity.
Qed.

Theorem multiplicative_identity: forall a, a*1=1*a /\ a*1=a.
Proof.
intro a.
split.
-induction a.
  + simpl. reflexivity.
  + simpl. rewrite IHa. simpl. reflexivity.
- rewrite right_one_multiplication. reflexivity.
Qed.

Lemma multiplicative_commutative_zero: forall a:nat, a*0=0*a.
Proof.
intro a.
simpl. induction a.
  + simpl. reflexivity.
  + simpl. rewrite IHa. reflexivity.
Qed.

Theorem multiplicative_zero: forall a:nat, a*0=0*a /\ 0*a=0.
Proof.
intro a.
split.
-rewrite multiplicative_commutative_zero. reflexivity.
-simpl. reflexivity.
Qed.




