(*
  10152160137 陈弈君 11/19
*)

Set Warnings "-notation-overridden,-parsing".
Require Export Tactics.

(** **** Exercise: 4 stars, advanced, recommended (forall_exists_challenge)  *)
(** Define two recursive [Fixpoints], [forallb] and [existsb].  The
    first checks whether every element in a list satisfies a given
    predicate:

      forallb oddb [1;3;5;7;9] = true

      forallb negb [false;false] = true

      forallb evenb [0;2;4;5] = false

      forallb (beq_nat 5) [] = true

    The second checks whether there exists an element in the list that
    satisfies a given predicate:

      existsb (beq_nat 5) [0;2;3;6] = false

      existsb (andb true) [true;true;false] = true

      existsb oddb [1;0;0;0;0;3] = true

      existsb evenb [] = false

    Next, define a _nonrecursive_ version of [existsb] -- call it
    [existsb'] -- using [forallb] and [negb].

    Finally, prove a theorem [existsb_existsb'] stating that
    [existsb'] and [existsb] have the same behavior. *)

Fixpoint forallb {X : Type} (p : X -> bool) (lst : list X) : bool :=
  match lst with
  | [] => true
  | x :: xs => andb (p x) (forallb p xs)
  end.

Example forallb1 : forallb oddb [1;3;5;7;9] = true.
Proof. simpl. reflexivity. Qed.
Example forallb2 : forallb negb [false;false] = true.
Proof. simpl. reflexivity. Qed.
Example forallb3 : forallb evenb [0;2;4;5] = false.
Proof. simpl. reflexivity. Qed.
Example forallb4 : forallb (beq_nat 5) [] = true.
Proof. simpl. reflexivity. Qed.


Fixpoint existsb {X : Type} (p : X -> bool) (lst : list X) : bool :=
  match lst with
  | [] => false
  | x :: xs => orb (p x) (existsb p xs)
  end.

Example existsb1 : existsb (beq_nat 5) [0;2;3;6] = false.
Proof. simpl. reflexivity. Qed.
Example existsb2 : existsb (andb true) [true;true;false] = true.
Proof. simpl. reflexivity. Qed.
Example existsb3 : existsb oddb [1;0;0;0;0;3] = true.
Proof. simpl. reflexivity. Qed.
Example existsb4 : existsb evenb [] = false.
Proof. simpl. reflexivity. Qed.


Definition existsb' {X : Type} (p : X -> bool) (lst : list X) :=
  negb (forallb (fun x => negb (p x)) lst).


Theorem or_and : forall (a b : bool), orb a (negb b) = negb (andb (negb a) b).
Proof.
  intros. destruct a.
  - destruct b. 
    + reflexivity. 
    + reflexivity.
  - destruct b. 
    + reflexivity. 
    + reflexivity.
Qed.

Theorem two_exists_is_same : forall (X : Type) (p : X -> bool) (lst : list X)
                   , existsb p lst = existsb' p lst.
Proof.
  intros X p lst. generalize dependent p.
  induction lst as [|x xs].
  - simpl. reflexivity.
  - simpl. unfold existsb'. simpl.
    intros p. rewrite <- or_and.
    apply f_equal. rewrite IHxs. reflexivity.
Qed.