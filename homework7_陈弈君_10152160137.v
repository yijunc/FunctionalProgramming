(*
  10152160137 陈弈君 homeowork 7
*)

Set Warnings "-notation-overridden,-parsing".
Require Export Logic.

(* 1 *)
Theorem bool_fn_applied_thrice :
  forall (f : bool -> bool) (b : bool),
  f (f (f b)) = f b.
Proof.
  intros f b. destruct b.
  - destruct (f true) eqn:ft.
    + rewrite ft. rewrite ft. reflexivity.
    + destruct (f false) eqn:ff.
      * rewrite ft. reflexivity.
      * rewrite ff. reflexivity.
  - destruct (f false) eqn:ff.
    + destruct (f true) eqn:ft.
      * rewrite ft. reflexivity.
      * rewrite ff. reflexivity.
    + rewrite ff. rewrite ff. reflexivity.
Qed.

(* 2 *)
Example conj_disj : forall A B C : Prop, 
  A /\ B -> C \/ B \/ C.
Proof.
  intros.
  inversion H.
  right. left. apply H1.
Qed.

(* 3 *)
Example plus_is_O : forall n m, n + m = 0 -> n = 0 /\ m = 0.
Proof.
  intros m. destruct m as [| m'].
  - intros. split.
    + reflexivity.
    + rewrite plus_O_n in H. apply H.
  - intros. inversion H.
Qed.