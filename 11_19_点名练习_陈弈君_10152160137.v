(*
  10152160137 陈弈君 11/19
*)

Set Warnings "-notation-overridden,-parsing".
Require Export Tactics.

Example inversion_test : 3 = 4 -> 5 = 10.

Proof. intros H. inversion H. Qed.