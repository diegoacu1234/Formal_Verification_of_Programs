Module Bool.

Inductive Bool :=
  | True
  | False.

Definition neg(b:Bool):Bool :=
  match b with 
    | True => False
    | False => True
    end.

Definition and(b1 b2:Bool):Bool :=
  match b1 with
    | True => b2
    | False => False
    end.

Definition or(b1 b2:Bool):Bool :=
  match b1 with
    | True => True
    | False => b2
    end.



Theorem doubleNegation(b:Bool): forall b: Bool, neg(neg(b))=b.
Proof.
  intro b0.
  destruct b0.
  - (*case b0:=True*)
    simpl.
    reflexivity.
  - (*case b0:=False*)
    simpl.
    reflexivity.
Qed.

Theorem idempotenceOr: forall b: Bool, or b b = b.
Proof.
  intro b0.
  destruct b0.
  - (* b0:=True*)
    simpl.
    reflexivity.
  - (* b0:=False*)
    simpl.
    reflexivity.
Qed.


Theorem commutativeOr: forall b1 b2:Bool, or b1 b2 = or b2 b1.
Proof.
  intro b1.
  destruct b1.
  - (* b1:= True*)
    intro b2.
    destruct b2.
      + reflexivity.
      + simpl. reflexivity.
  - (* b2:=False*)
    intro b2.
    destruct b2.
      + simpl. reflexivity.
      + reflexivity.
Qed.


Theorem commutativeAnd: forall b1 b2:Bool, and b1 b2 = and b2 b1.
Proof.
  intros b1 b2.
  destruct b1.
    - destruct b2.
      + simpl. reflexivity.
      + simpl. reflexivity.
    - destruct b2.
      + simpl. reflexivity.
      + simpl. reflexivity.
Qed.


Theorem identityOr: forall b:Bool, or b False = b.
Proof.
  intro b.
  destruct b.
  - simpl. reflexivity.
  - simpl. reflexivity.
Qed.
  

Theorem deMorgan: forall b1 b2:Bool, neg (or b1 b2) = and (neg b1) (neg b2).
Proof.
  intros b1 b2.
  destruct b1.
  + simpl. reflexivity.
  + simpl. reflexivity.
Qed.

End Bool.


