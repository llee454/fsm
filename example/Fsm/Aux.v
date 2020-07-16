(*
  This file contains auxiliary definitions used by other files in
  this project.
*)
Require Import Nat.
Require Import PeanoNat.
Require Import Program.
Require Import List.
Require Import Lia.
Import ListNotations.
Import Nat.

Lemma rev_app : forall {A} (x : A) (xs : list A), xs ++ [x] = rev (x :: (rev xs)).
Proof.
  intros A x xs.
  unfold rev at 1.
  fold (rev (rev xs)).
  rewrite (rev_involutive xs).
  reflexivity.
Qed.

Lemma mod_ex : forall x y z : nat, z <> 0 -> x = y mod z -> exists k : nat, k * z + x = y.
Proof.
 intros x y z Hy%(div_mod y) ->.
 exists (y / z); symmetry.
 now rewrite mul_comm.
Qed.
