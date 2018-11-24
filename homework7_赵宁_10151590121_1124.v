(** Homework 7
  * 10151590121
  * Zhao Ning
  * 赵宁
  *)
  
Theorem bool_fn_applied_thrice :
  forall (f : bool -> bool) (b : bool),
  f (f (f b)) = f b.
Proof. 
  intros f b.
  destruct (f b) eqn:Heq_.
    - destruct b.
      + rewrite Heq_. apply Heq_.
      + destruct (f true) eqn:Heq__.
        * apply Heq__.
        * apply Heq_.
    - destruct b.
      + destruct (f false) eqn:Heq__.
        * apply Heq_.
        * apply Heq__.
      + rewrite Heq_. apply Heq_.
Qed.

Example conj_disj : forall A B C : Prop, 
  A /\ B -> C \/ B \/ C.
Proof. 
  intros A B C H.
  destruct H as [HA HB].
  right. 
  left.
  apply HB.
Qed.

Example and_exercise :
  forall n m : nat, n + m = 0 -> n = 0 /\ m = 0.
Proof.
  intros n m H.
  split.
  - destruct n.
    + reflexivity.
    + destruct m.
      * inversion H.
      * inversion H.
  - destruct m.
    + reflexivity.
    + destruct n.
      * inversion H.
      * inversion H.
Qed.