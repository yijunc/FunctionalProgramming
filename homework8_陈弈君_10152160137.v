(*
  10152160137 陈弈君 homeowork 8
*)

Set Warnings "-notation-overridden,-parsing".
Require Export Logic.

(* 1 *)
Theorem dist_not_exists : forall (X:Type) (P : X -> Prop),
  (forall x, P x) -> ~ (exists x, ~ P x).
Proof.
  intros. unfold not. intros.
  inversion H0. apply H1. apply H.
Qed.

(* 2. Prove that existential quantification distributes over disjunction. *)
Theorem dist_exists_or : forall (X:Type) (P Q : X -> Prop),
  (exists x, P x \/ Q x) <-> (exists x, P x) \/ (exists x, Q x).
Proof.
   intros. split.
   - intros. inversion H. destruct H0 as [HL | HR].
     + left. exists x. apply HL.
     + right. exists x. apply HR.
   - intros. destruct H as [HL | HR].
     + inversion HL. exists x. left. apply H.
     + inversion HR. exists x. right. apply H.
Qed.

(*  3. *)
Lemma In_map_iff :
  forall (A B : Type) (f : A -> B) (l : list A) (y : B),
    In y (map f l) <->
    exists x, f x = y /\ In x l.
Proof.
  intros. induction l as [|h t IHt].
  - simpl. split.
    + intros. inversion H.
    + intros. inversion H. inversion H0. apply H2.
  - split.
    + intros. induction H as [H|H].
      * exists h. split.
        -- apply H.
        -- left. reflexivity.
      * apply IHt in H. inversion H. exists x. split.
        -- apply H0.
        -- simpl. right. apply H0.
    + simpl. intros. inversion H. destruct H0. destruct H1. 
      * rewrite <- H1 in H0. left. apply H0.
      * inversion IHt. right. apply H3. exists x. split.
        -- apply H0.
        -- apply H1.
Qed.