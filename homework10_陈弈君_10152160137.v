(*
  10152160137 陈弈君 homeowork 10
*)

Set Warnings "-notation-overridden,-parsing".
Require Import Coq.Arith.Arith.
Require Import Coq.Bool.Bool.
Require Export Coq.Strings.String.
Require Import Coq.Logic.FunctionalExtensionality.
Require Import Coq.Lists.List.
Require Export Maps.

(* 1 *)
Lemma t_apply_empty:  forall (A:Type) (x: string) (v: A), { --> v } x = v.
Proof.
  intros. unfold t_empty. reflexivity.
Qed.

(* 2 *)
Lemma t_update_eq : forall A (m: total_map A) x v,
  (m & {x --> v}) x = v.
Proof.
  intros. unfold t_update.
  rewrite <- beq_string_refl.
  reflexivity.
Qed.

(* 3 *)
Theorem t_update_neq : forall (X:Type) v x1 x2
                         (m : total_map X),
  x1 <> x2 ->
  (m & {x1 --> v}) x2 = m x2.
Proof.
  intros. unfold t_update.
  rewrite false_beq_string.
  - reflexivity.
  - apply H.
Qed.

(* 4 *)
Lemma t_update_shadow : forall A (m: total_map A) v1 v2 x,
    m & {x --> v1 ; x --> v2} = m & {x --> v2}.
Proof.
  intros. unfold t_update.
  extensionality i. remember (beq_string x i) as e. induction e.
  - reflexivity.
  - reflexivity.
Qed.

(* 5 *)
Lemma beq_stringP : forall x y, reflect (x = y) (beq_string x y).
Proof.
  intros. apply iff_reflect.
  rewrite beq_string_true_iff. split.
  - intros. apply H.
  - intros. apply H.
Qed.

(* 6 *)
Theorem t_update_same : forall X x (m : total_map X),
    m & { x --> m x } = m.
Proof.
  intros. unfold t_update.
  extensionality i. remember (beq_string x i) as e. induction e.
  - symmetry in Heqe. 
    apply beq_string_true_iff in Heqe.
    rewrite Heqe.
    reflexivity.
  - reflexivity.
Qed.