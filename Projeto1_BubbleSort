Require Import Arith Lia.
Require Import List.
Import ListNotations.
Require Import Recdef.
Require Import Sorted.
Require Import Permutation.

(*
  Aluno: Sofia Dy La Fuente Monteiro
  Matrícula: 211055530
*)

(** * Ordenação por Borbulhamento *)

Function bubble (l: list nat) {measure length l} :=
  match l with
  | nil => nil
  | x::nil => x::nil
  | x::(y::l) =>
      if x <=? y
      then x::(bubble (y::l))
      else y::(bubble (x::l))
  end.
Proof.
  - auto.
  - auto.
Defined.

Fixpoint bs (l: list nat) :=
  match l with
  | nil => nil
  | h::l => bubble (h::(bs l))
  end.

(*
==============
  Permutação
==============
*)

Lemma bubble_perm: forall l, Permutation l (bubble l).
Proof.
  intro l.
  functional induction (bubble l).
  - apply perm_nil.
  - apply Permutation_refl.
  - apply perm_skip. assumption.
  - apply perm_trans with (y :: x :: l0).
    + apply perm_swap.
    + apply perm_skip. assumption.
Qed.

Lemma bs_perm: forall l, Permutation (bs l) l.
Proof.
  induction l.
  - simpl. apply perm_nil.
  - simpl.
    apply perm_trans with (a :: bs l).
    + apply Permutation_sym. apply bubble_perm.
    + apply perm_skip. assumption.
Qed.

(*
=============
  Ordenação
=============
*)

Definition le_all (x:nat) (l:list nat) :=
  forall y, In y l -> x <= y.

Notation "x <=* l" := (le_all x l) (at level 60).

(** Lema 1: Se x é menor ou igual a todos os elementos de l, e l é permutação de l', então x é menor ou igual a todos os elementos de l' *)
Lemma le_all_perm : forall x l l',
  le_all x l -> Permutation l l' -> le_all x l'.
Proof.
  unfold le_all.
  intros x l l' HAll HPerm y HIn.
  apply HAll.
  symmetry in HPerm.
  apply Permutation_in with (l':=l) (x:=y) in HPerm; assumption.
Qed.

(** Lema 2: Se x::l está ordenada, então x é menor ou igual a todos os elementos de l. *)
Lemma sorted_imp_le_all: forall l x,
  Sorted le (x::l) -> le_all x l.
Proof.
  intros l x. generalize dependent x.
  induction l as [|a l' IH].
  - (* Base *)
    intros x H. unfold le_all. intros y Fin. contradiction.
  - (* Passo Indutivo *)
    intros x H.
    apply Sorted_inv in H. destruct H as [HSorted HRel].
    inversion HRel; subst.
    unfold le_all. intros y Hy.
    destruct Hy as [IsHead | IsTail].
    + (* y é a cabeça *)
      subst. assumption.
    + (* y está na cauda *)
      assert (Ha: le_all a l'). { apply IH. assumption. }
      apply Nat.le_trans with a.
      * assumption.
      * apply Ha. assumption.
Qed.

(** Lema 3: Se l está ordenada e x é menor ou igual a todos os elementos de l, então x::l está ordenada. *)
Lemma le_all_sorted: forall x l,
  Sorted le l -> le_all x l -> Sorted le (x::l).
Proof.
  intros x l HS HAll.
  constructor.
  - assumption.
  - destruct l.
    + constructor.
    + constructor. apply HAll. left. reflexivity.
Qed.

(** Lema 4: A cauda de uma lista ordenada é ordenada *)
Lemma sorted_tl: forall l x, Sorted le (x::l) -> Sorted le l.
Proof.
  intros l x H.
  inversion H; subst.
  assumption.
Qed.



(*
==================
  Objetivo Final
==================
*)

(*
Theorem bubble_sort_correct:
  forall l,
    Sorted le (bs l) /\ Permutation (bs l) l.
Proof.
  intro l.
  split.
  - apply bs_sorted.
  - apply bs_perm.
Qed.
*)