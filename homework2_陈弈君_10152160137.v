(** * 2018 Functional Programming Homework2 *)

(* 
    10152160137
    陈弈君
*)

(* ################################################################# *)

(* 1. Theorem mult_1_r : forall n : nat,  n * 1 = n. *)

Theorem mult_1_r : forall n : nat,  n * 1 = n.

Proof. 
  intros n. induction n as [|n' IHn'].
  - simpl. reflexivity. 
  - simpl. rewrite -> IHn'. reflexivity. 
  Qed.

(* 2. Theorem plus_comm_assoc : forall n m p : nat,  n + (m + p) = m + (n + p). *)
Theorem plus_n_Sm : forall n m : nat,
  S (n + m) = n + (S m).
Proof.
  intros n m. induction n as [|n' IHn'].
  - simpl. reflexivity.
  - simpl. rewrite IHn'. reflexivity.
  Qed.

Theorem plus_comm_assoc : forall n m p : nat,  n + (m + p) = m + (n + p).

Proof. 
  intros n m p.
  induction n as [|n'  IHn'].
  - simpl. reflexivity.
  - simpl. rewrite -> IHn'. rewrite plus_n_Sm. reflexivity.
  Qed.

(* 3. Theorem mult_distri_l : forall n m p : nat,  n * (m + p) = n * m + n * p. *)

Theorem mult_distri_1_pre : forall a b c d : nat,
  a + b + (c + d) = a + c + (b + d).
Proof.
  intros a b c d. induction a as [|a' IHa'].
  - simpl. rewrite plus_comm_assoc. reflexivity.
  - simpl. rewrite IHa'. reflexivity.
Qed.
  
  
Theorem mult_distri_l : forall n m p : nat,  n * (m + p) = n * m + n * p.

Proof. 
  intros n m p.
  induction n as [|n' IHn'].
  - simpl. reflexivity.
  - simpl. rewrite IHn'. rewrite mult_distri_1_pre. reflexivity.
Qed.



(* 4. Theorem mult_comm : forall m n : nat, m * n = n * m. *)

Theorem plus_0_r : forall n:nat, n + 0 = n.
Proof.
  intros n. induction n as [| n'].
  - simpl. reflexivity.
  - simpl. rewrite -> IHn'. reflexivity.  Qed.

Theorem plus_assoc : forall n m p : nat,
  n + (m + p) = (n + m) + p.
Proof.
  intros.
  induction n.
  - reflexivity.
  - simpl.
    rewrite -> IHn.
    reflexivity. 
  Qed.

Lemma plus_distr : forall n m: nat, S (n + m) = n + (S m).
  Proof.
    intros. 
    induction n.
    reflexivity.
    simpl.
    rewrite -> IHn. 
    reflexivity. 
  Qed.

Theorem plus_comm : forall n m : nat,
  n + m = m + n.
Proof.
  intros.
  induction n.
  - simpl. rewrite -> plus_0_r. reflexivity.
  - simpl. rewrite ->IHn. rewrite -> plus_distr. reflexivity.
  Qed.

Theorem plus_swap : forall n m p : nat, 
  n + (m + p) = m + (n + p).
Proof.
  intros n m p.
  rewrite -> plus_assoc.
  assert(H: m + (n + p) = (m + n) + p).
  { rewrite -> plus_assoc. reflexivity. }
  rewrite -> H.
  assert(H2: m + n = n + m).
  { rewrite -> plus_comm. reflexivity. }
  rewrite -> H2.
  reflexivity.
  Qed.


Lemma mult_distr : forall n m: nat, (n*m) + n = n*(S m).
  Proof.
    intros. 
    induction n.
    - reflexivity.
    - simpl. rewrite <- plus_n_Sm. rewrite <- IHn. rewrite -> plus_assoc. reflexivity. 
  Qed.

Lemma mult_distr2 : forall n m: nat, (n*m) + m = (S n)*m.
  Proof.
    intros. 
    induction n.
    simpl.
    rewrite -> plus_0_r.
    reflexivity.
    simpl.
    rewrite -> plus_assoc.
    assert (n*m + m = m + n*m).
      rewrite -> plus_comm.
      reflexivity.
    rewrite <- H.
    rewrite <- plus_comm with (n := n*m) (m := m + m).
    rewrite -> plus_assoc.
    reflexivity. 
  Qed.


Theorem mult_0_r : forall n:nat,
  n * 0 = 0.
Proof.
  intros.
  induction n.
  simpl.
  reflexivity.
  simpl.
  apply IHn.
  Qed.

Theorem mult_comm : forall m n : nat,
 m * n = n * m.
Proof.
  intros.
  induction n as [| n'].
  (* n = 0 *)
    simpl.
    rewrite -> mult_0_r.
    reflexivity.
  (* n = S n' *)
    rewrite <- mult_distr.
    rewrite -> IHn'.
    rewrite -> mult_distr2.
    reflexivity.
Qed.
