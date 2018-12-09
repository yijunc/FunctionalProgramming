(*
  10152160137 陈弈君 homeowork 9
*)

Set Warnings "-notation-overridden,-parsing".
Require Export IndProp.

(* 1 *)
Theorem n_le_m__Sn_le_Sm : forall n m,
  n <= m -> S n <= S m.
Proof.
  intros. induction H.
  - apply le_n.
  - apply le_S. apply IHle.
Qed.

(* 2 *)
Theorem n_le_Sn : forall n, n <= S n.
Proof. intros. apply le_S. apply le_n. Qed.

Theorem Sn_le_Sm__n_le_m : forall n m,
  S n <= S m -> n <= m.
Proof.
  intros. inversion H.
  - apply le_n.
  - apply le_trans with (n := S n). apply n_le_Sn. apply H1.
Qed.

(* 3 *)
Theorem le_plus_l : forall a b,
  a <= a + b.
Proof.
  intros. induction a.
  - simpl. apply O_le_n.
  - simpl. apply n_le_m__Sn_le_Sm. apply IHa.
Qed.

(* 4 *)
Theorem plus_lt : forall n1 n2 m,
  n1 + n2 < m ->
  n1 < m /\ n2 < m.
Proof.
  unfold lt. intros. split.
  - induction H. apply n_le_m__Sn_le_Sm. 
    + apply le_plus_l.
    + apply le_S. apply IHle.
  - induction H.
    + apply n_le_m__Sn_le_Sm. rewrite -> plus_comm. apply le_plus_l.
    + apply le_S. apply IHle.
Qed.

(* 5 *)
Theorem lt_S : forall n m,
  n < m ->
  n < S m.
Proof.
  unfold lt. intros. apply le_S. apply H.
Qed.