(*
  10152160137 陈弈君 11/18
*)

Set Warnings "-notation-overridden,-parsing".
Require Export Poly.


Definition hd_error {X : Type} (l : list X) : option X
:= match l with
   | nil    => None
   | h :: _ => Some h
   end.

Example test_hd_error1 : hd_error [1;2] = Some 1.
Proof. simpl. reflexivity. Qed.

Example test_hd_error2 : hd_error  [[1];[2]]  = Some [1].
Proof. simpl. reflexivity. Qed.