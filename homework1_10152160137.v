(** * 2018 Functional Programming Homework1 *)

(* 
    10152160137
    陈弈君
*)

(* ################################################################# *)

(* 1. Prove the following properties.*)

Theorem mult_0_l : forall n : nat, 0 * n = 0.
Proof.
  intros n. simpl. reflexivity. Qed.

Theorem mult_Sn : forall n m : nat, (1 + n) * m = m + n * m.

Proof.
  intros n m. simpl. reflexivity. Qed.


Fixpoint exp (base power : nat) : nat :=
  match power with
    | O => S O
    | S p => mult base (exp base p)
  end.

Theorem exp_1_l: forall n : nat, exp n 1 = n * 1.

Proof.
  intros n. simpl. reflexivity. Qed.

Theorem exp_Sn : forall n m : nat, exp n (1+m) = n * (exp n  m).
Proof.
  intros n m. simpl. reflexivity. Qed.


(* 2. Define the geb function that tests whether its first argument is greater than or equal to its second argument, yielding a boolean. *)

Fixpoint geb(n1 n2 : nat) : bool :=
  match n2 with
  | 0 => true
  | S n2' => 
    match n1 with
    | 0 => false
    | S n1' => geb n1' n2'
    end
  end.

Example test_geb1 : (geb 4 4) = true.

Proof. simpl. reflexivity. Qed.

Example test_geb2 : (geb 4 6) = false.

Proof. simpl. reflexivity. Qed.

Example test_geb3 : (geb 7 5) = true.

Proof. simpl. reflexivity. Qed.


Theorem plus_3O_n : forall n : nat, 0 + 0 + 0 + n = n.

Proof. intros n. simpl. reflexivity. Qed.
