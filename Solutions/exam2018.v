(* Final Exam --- January 8, 2018 *)
Require Import Nat.
Require Import List.

Notation "[ ]" := nil. 
Notation "[ x ; .. ; y ]" := (cons x .. (cons y nil) ..).

Definition admit {T: Type} : T.  Admitted.

(* 1. Define a function createList such that (createList n) returns 
a list of n numbers from 1 to n. *)

Fixpoint createList (n : nat) : list nat :=
 match n with
 | O => nil
 | S n' => (createList n') ++ [n]
end.

Example test1 : createList 5 = [1;2;3;4;5].
Proof.
intros.
simpl.
reflexivity.
Qed.


(* 2. Complete the following definition so that (last n l) holds iff
 n is the last element of the list l. *)

Inductive last (n : nat) : list nat -> Prop :=
  | last_emp: False -> last n []
  | last_single: forall m, m = n -> last n [m]
  | last_nxt: forall m l, last n l -> last n ([m] ++ l).


Example test2 : last 5 [1;2;3;4;5].
Proof. apply last_nxt. apply last_nxt. apply last_nxt. apply last_nxt.
 apply last_single. reflexivity. Qed.

Example test3 : forall n, ~ (last n [ ]).
Proof. unfold not. intros. inversion H. inversion H0. Qed.


(* 3. Define the Fibonacci sequence. The function (fib n) returns the first
n Fibonacci numbers. *)
Fixpoint fib (n: nat) : list nat :=
  match n with
  | O => [0]
  | S n' => match n' with
            | O => (fib n') ++ [1] 
            | S m => (fib n') ++ [(hd 0 (rev(fib m)) + hd 0 (rev(fib n')))] 
            end
  end.

Print hd.

Example test4 :  fib 15 =
[0; 1; 1; 2; 3; 5; 8; 13; 21; 34; 55; 89; 144; 233; 377; 610].
Proof.
intros.
simpl.
reflexivity.
Qed.


(* 4. Prove that the excluded middle axiom implies the double negation axiom. *)
Theorem double_negation : 
  (forall P, P \/ ~P) -> (forall P, ~~P <-> P).
Proof. 
intros.
split.
- destruct (H(P)).
  + intros. apply H0.
  + intros. 
    unfold not in H1.
    unfold not in H0.
    apply H1 in H0.
    inversion H0.
- destruct (H(P)).
  + intros.
    unfold not.
    intros.
    apply H2 in H0.
    inversion H0.
  + intros.
    apply H0 in H1.
    inversion H1.
Qed. 


(* 5. Define the greater than relation and show its transitivity. *)
Inductive gt : nat -> nat -> Prop :=
| equal : forall n, gt n n
| greater : forall n m, (gt n m) -> (gt (S n) m).

Example test5 : gt 3 1.
Proof.
apply greater.
apply greater.
apply equal.
Qed.

Example test6 : ~ (gt 1 2).
Proof.
unfold not.
intros H.
inversion H.
inversion H1.
Qed.

Example gt_transitive : forall m n p,
  gt m n -> gt n p -> gt m p.
Proof.
intros.
induction H.
- apply H0.
- apply greater.
  apply IHgt.
  apply H0.
Qed.

(* 作业原题 *)

(* 6. Consider the following function f. What does this function do? *)
Fixpoint f (l: list nat) : list nat :=
   match l with
   | nil => l
   | h :: t => f t ++ [h]
   end.

Lemma app_nil_r : forall (X:Type), forall l:list X,
  l ++ [] = l.
Proof.
intros.
induction l as [| h l' IHl'].
- simpl. reflexivity.
- simpl. rewrite -> IHl'. reflexivity.
Qed.

Lemma app_assoc : forall A (l m n:list A),
  l ++ m ++ n = (l ++ m) ++ n.
Proof.
intros.
induction l as [| h l' IHl'].
- simpl. reflexivity.
- simpl. rewrite -> IHl'. reflexivity.
Qed.

Lemma rev_app_distr: forall l1 l2 : list nat,
  f (l1 ++ l2) = f l2 ++ f l1.
Proof.
intros.
induction l1 as [| h1 l1 IHl1'].
- simpl. rewrite -> app_nil_r. reflexivity.
- simpl. rewrite -> IHl1'. rewrite -> app_assoc. reflexivity.
Qed.

(* Show that function f has the following property. *)
Theorem double_f : forall l : list nat,
  f (f l) = l.
Proof.
intros.
induction l as [| h l' IHl'].
- simpl.
  reflexivity.
- simpl.
  rewrite -> rev_app_distr. rewrite -> IHl'.
  simpl.
  reflexivity.
Qed.


(* 7. Complete the following definition so that (div3 n) returns true 
iff n is divisible by 3. *)

Fixpoint div3 (n : nat) : bool :=
 match n with
 | O => true
 | S O => false
 | S (S O) => false
 | S (S (S n')) => (div3 n')
end.

Example test7: div3 12 = true.
Proof.
intros.
simpl.
reflexivity.
Qed.

Example test8: div3 13 = false.
Proof.
intros.
simpl.
reflexivity.
Qed.


(* 8. Write a function (partition):

      partition : list nat -> list nat * list nat

   which partitions a list into a pair of sublists. The first member of
   the pair is the sublist of the original list containing the
   elements divisible by 3, and the second is the sublist
   containing those that are not divisible by 3.  The order of elements in the
   two sublists should be the same as their order in the original list. 

   Hint: You can make use of the Coq function (filter).
*)

Definition partition (l : list nat)
                   : list nat * list nat :=
  (filter div3 l, filter (fun n => if (div3 n) then false else true) l).

Example test9: partition [1;2;3;4;5;6] = ([3;6], [1;2;4;5]).
Proof.
unfold partition.
reflexivity.
Qed.


(* 9. Consider the following type:

Inductive btree : Set :=
 | leaf : btree 
 | node : nat->btree->btree->btree.

Define a function taking as argument a natural number n
and a tree t: btree and returning true iff t has (at least) 
an occurrence of n. 

Hint: You may use the function (eqb n m) which returns true iff the two natural
numbers n and m are equal.
*)


Inductive btree : Set :=
 | leaf : btree
 | node : nat->btree->btree->btree.

Fixpoint occur (n: nat)(t: btree) : bool :=
  match t with
    | leaf => false
    | node m tl tr => match (eqb m n) with
                        | true => true
                        | false => orb (occur n tl)  (occur n tr)
                      end
  end.


Example test10 : occur 2 (node 1 leaf (node 3 (node 2 leaf leaf) leaf)) = true.
Proof. reflexivity. Qed.


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
  | AMinus a1 a2  => (aeval a1) - (aeval a2)
  | AMult a1 a2 => (aeval a1) * (aeval a2)
  end.

(* Suppose we define a function that takes an arithmetic expression 
   and slightly simplifies it, changing every occurrence of [e+0] 
   (i.e., [(APlus e (ANum 0)]) into just [e]. *)

Fixpoint optimize_plus0 (a:aexp) : aexp :=
  match a with
  | ANum n =>
      ANum n
  | APlus e1 (ANum 0) => optimize_plus0 e1
  | APlus e1 e2 =>
      APlus (optimize_plus0 e1) (optimize_plus0 e2)
  | AMinus e1 e2 =>
      AMinus (optimize_plus0 e1) (optimize_plus0 e2)
  | AMult e1 e2 =>
      AMult (optimize_plus0 e1) (optimize_plus0 e2)
  end.

(* Prove the following theorem that states the correctness of the 
optimization with respect to the evaluation of arithmetic expressions. *)
Theorem plus_comm : forall n m : nat,
  n + m = m + n.
Proof.
  intros n m. induction n as [|n' IHn'].
  - simpl. rewrite <- plus_n_O. reflexivity.
  - simpl. destruct m as [|m'].
  + rewrite -> IHn'. reflexivity.
  + rewrite -> IHn'. rewrite plus_n_Sm. reflexivity. Qed. 

(* 作业原题 *)
Theorem optimize_plus0_sound: forall a,
  aeval (optimize_plus0 a) = aeval a.
Proof.
  intros.
  induction a ;try (simpl;reflexivity).
  destruct a2; 
  try (simpl; simpl in IHe1; rewrite IHe1; rewrite IHe2; reflexivity).
  destruct n.
  simpl; rewrite <- IHa1; rewrite plus_comm;reflexivity.  
  simpl. rewrite <- IHa1. reflexivity. simpl. simpl in IHa2.  rewrite IHa2. rewrite <- IHa1. reflexivity.
  simpl. simpl in IHa2. rewrite IHa2. rewrite <- IHa1. reflexivity.
  simpl. simpl in IHa2. rewrite IHa2. rewrite <- IHa1. reflexivity.
  simpl. simpl in IHa2. rewrite IHa2. rewrite <- IHa1. reflexivity.
  simpl. simpl in IHa2. rewrite IHa2. rewrite <- IHa1. reflexivity.
Qed.
