(* Final Exam --- January 7, 2019 *)

(****** 10152160137 

        陈弈君
******)
Require Import Nat.
Require Import List.

Notation "[ ]" := nil. 
Notation "[ x ; .. ; y ]" := (cons x .. (cons y nil) ..).


Definition admit {T: Type} : T.  Admitted.


(* 1. Prove the following two facts about natural numbers. *)

Lemma mul_0_r : forall n : nat, n * 0 = 0.
Proof.
  intro n. induction n as [| n' IHn'].
  - reflexivity.
  - simpl. rewrite -> IHn'. reflexivity. 
Qed.


Lemma mul_1_r : forall n : nat, n * 1 = n.
Proof. 
  intro n. induction n as [| n' IHn'].
  - reflexivity.
  - simpl. rewrite IHn'. reflexivity.
Qed.

(* 2. Complete the following definition so that (div5 n) returns true 
iff n is divisible by 5. *)

Fixpoint div5 (n : nat) : bool :=
  match n with
   | O => true
   | S O => false
   | S (S O) => false
   | S (S (S 0)) => false
   | S (S (S (S 0))) => false
   | S (S (S (S (S n')))) => (div5 n')
  end.

Example test1: div5 15 = true.
Proof. 
  simpl. reflexivity.
Qed.

Example test2: div5 23 = false.
Proof. 
  simpl. reflexivity.
Qed.


(* 3. Define a function createList such that (createList n) returns 
a list of n numbers from 2n to 1. *)


Fixpoint createList (n : nat) : list nat :=
  match n with
  | O => nil
  | S n' => [n*2; n*2-1] ++ (createList n')
  end.

Example test3 : createList 4 = [8;7;6;5;4;3;2;1].
Proof. 
  simpl. reflexivity.
Qed.


(* 4. (1) Define the relation gtodd between odd numbers such that 
   (gtodd m n) holds if and only if m is greater than n for odd numbers m and n.
(2) Show the transitivity of the relation gtodd. *)

Inductive od : nat -> Prop :=
  | od_1 : od (S 0)
  | od_SS : forall n : nat, od n -> od (S (S n)).

Inductive gtodd : nat -> nat -> Prop :=
  | equal : forall n, od n -> gtodd n n
  | greater : forall n m, (gtodd n m) -> (gtodd (S (S n)) m).

Example test4 : gtodd 3 1.
Proof.
  apply greater.
  apply equal.
  apply od_1.
Qed.

Example test5 : ~ (gtodd 4 3).
Proof.
  unfold not. intros. inversion H. inversion H1. inversion H4.
Qed.

Theorem gtodd_trans : forall m n p,
  gtodd m n -> gtodd n p -> gtodd m p.
Proof.
  intros. induction H.
  - apply H0.
  - apply greater. apply IHgtodd. apply H0.
Qed.


(* 5. Write a function (partition):

      partition : list nat -> list (list nat )

   which partitions a list into a list of 3 sublists. The first sublist
   contains all even numbers in the original list. The second sublist 
   contains all odd numbers divisible by 5 in the original list. The last 
   sublist contains all other elements. The order of elements in the
   three sublists should be the same as their order in the original list. 

   Hint: You can make use of the Coq function (filter).
*)

(********* Start Define evenb , oddb , orb  *************)
Fixpoint evenb (n:nat) : bool :=
  match n with
  | O        => true
  | S O      => false
  | S (S n') => evenb n'
  end.
Definition oddb (n:nat) : bool   :=   negb (evenb n).
Definition orb (b1:bool) (b2:bool) : bool :=
  match b1 with
  | true => true
  | false => b2
  end.
(********* End Define evenb , oddb , orb *************)

Definition partition (l : list nat) : list (list nat) :=
  [ filter evenb l;  
    filter div5 l; 
    filter (fun n => if orb (evenb n) (div5 n) then false else true) l].

Example test6: partition [1;2;3;9;4;5;6;15] = [[2;4;6]; [5;15]; [1;3;9]].
Proof.
  unfold partition.
  simpl. reflexivity.
Qed.


(* 6. Prove that the excluded middle axiom implies the Peirce's law. *)

Theorem peirce : 
  (forall P, P \/ ~P) -> (forall P Q : Prop, ((P->Q)->P)->P).
Proof. 
  intros. destruct (H P).
  - apply H1.
  - unfold not in H1. apply H1 in H0.
    + inversion H0.
    + intros. apply H1 in H2. inversion H2.
Qed.


(* 7. Let a sequence of numbers F(n) be given as follows.
   F(0) = 0
   F(1) = 1
   F(2) = 1
   F(n) = F(n-1) + F(n-2) + F(n-3)   for n > 2.

Define the function Seq such that (Seq n) returns the sequence.

[0; F(0); 1; F(1); 2; F(2); 3; F(3); ... ; n; F(n)].
*)

Fixpoint Seq (n: nat) : list nat :=
  match n with
  | O => [0;0]
  | S n' => match n' with
            | O => (Seq n') ++ [1;1] 
            | S m => match m with
                     | O => (Seq n') ++ [2;1]
                     | S o => (Seq n') ++ [n; (hd 0 (rev(Seq m)) + hd 0 (rev(Seq n')) + hd 0 (rev(Seq o)))]
                     end
            end
  end.

Example test7 :  Seq 10 = 
[0; 0; 1; 1; 2; 1; 3; 2; 4; 4; 5; 7; 6; 13; 7; 24; 8; 44; 9; 81; 10; 149].
Proof.
  simpl. reflexivity.
Qed.


(* 8. Consider the following type:

Inductive btree : Set :=
 | leaf : btree 
 | node : nat->btree->btree->btree.

Define a function taking as argument a natural number n
and a tree t and returning the number of occurrences of n in t.

Hint: You may use the function (eqb n m) which returns true iff the two natural
numbers n and m are equal.
*)

Inductive btree : Set :=
  | leaf : btree 
  | node : nat->btree->btree->btree.

Fixpoint occur (n: nat)(t: btree) : nat :=
  match t with
  | leaf => 0
  | node m tl tr => match (eqb m n) with
                    | true => (occur n tl) + (occur n tr) + 1
                    | false => (occur n tl) + (occur n tr)
                    end
  end.

Example test8 : occur 2 (node 1 (node 2 leaf (node 2 leaf leaf)) (node 3 (node 2 leaf leaf) leaf)) = 3.
Proof.
  simpl. reflexivity.
Qed.

(* 9 Design a sorting algorithm which transforms a list of natural numbers into 
a list sorted in ascending oder. *)

(************* Start define insert *************)
Fixpoint insert (n : nat)(l : list nat) : list nat :=
  match l with
  | nil => n :: nil
  | h :: l' => match (leb h n) with
               | false => n :: l
               | true => h :: insert n l'
               end
  end.
(************* End define insert *************)

Fixpoint transform (l: list nat) : list nat :=
  match l with
  | nil => nil
  | h :: l' => insert h (transform l')
  end.

Example test10 : transform [2;4;1;6;9;6;4;1;3;5;10] = [1;1;2;3;4;4;5;6;6;9;10].
Proof.
  simpl. reflexivity.
Qed.


(* 10. The following definitions specify the abstract syntax of
    some arithmetic expressions and an evaluation function. *)

Inductive aexp : Type :=
  | ANum : nat -> aexp
  | APlus : aexp -> aexp -> aexp
  | AMinus : aexp -> aexp -> aexp
  | AMult : aexp -> aexp -> aexp.

Fixpoint aeval (a : aexp) : nat :=
  match a with
  | ANum n => n
  | APlus a1 a2 => (aeval a1) + (aeval a2)
  | AMinus a1 a2 => (aeval a1) - (aeval a2)
  | AMult a1 a2 => (aeval a1) * (aeval a2)
  end.

(* Suppose we define a function that takes an arithmetic expression 
   and slightly simplifies it, changing every occurrence of [e * 1] 
   (i.e., [(AMult e (ANum 1)]) into just [e]. *)

Fixpoint optimize_mult1 (a:aexp) : aexp :=
  match a with
  | ANum n => ANum n
  | APlus e1 e2 => APlus (optimize_mult1 e1) (optimize_mult1 e2)
  | AMinus e1 e2 => AMinus (optimize_mult1 e1) (optimize_mult1 e2)
  | AMult e1 (ANum (S O)) => optimize_mult1 e1
  | AMult e1 e2 => AMult (optimize_mult1 e1) (optimize_mult1 e2)
  end.

(* Prove the following theorem that states the correctness of the 
optimization with respect to the evaluation of arithmetic expressions. *)

Theorem optimize_mult1_sound: forall a,
 aeval (optimize_mult1 a) = aeval a.
Proof. 
  intros a. induction a.
  - reflexivity.
  - simpl. rewrite IHa1. rewrite IHa2. reflexivity.
  - simpl. rewrite IHa1. rewrite IHa2. reflexivity.
  - destruct a2; try (simpl; simpl in IHa2; rewrite IHa1; rewrite IHa2; reflexivity).
  + simpl. destruct n eqn:eq.
    * simpl. rewrite IHa1. reflexivity.
    * simpl. destruct n0.
      ** rewrite IHa1. rewrite mul_1_r. reflexivity.
      ** simpl. rewrite IHa1. reflexivity.
Qed.