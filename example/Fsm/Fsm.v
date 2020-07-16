(*
  This module defines an record type that can be used to represent
  finite state machines and proves lemmas that can be used to
  verify machines.
*)
Require Import Nat.
Require Import PeanoNat.
Require Import Program.
Require Import List.
Require Import Lia.
Import ListNotations.
Import Nat.
Require Import Fsm.Aux.

(* Represents finite state machines *)
Record FSM : Type := {
  (* Represents states *)
  State : Set;

  (* Represents input values *)
  Input : Set;

  (* Represents output values *)
  Output : Set;

  (* specifies the initial state *)
  initial : State;

  (*
    Accepts a state and returns the output returned by the machine
    if it terminates in that state.
  *)
  output : State -> Output;

  (*
    Accepts a state and an input value and returns the state that
    the machine transitions into in response.
  *)
  transition : State -> Input -> State;

  (*
    Accepts an initial state and a sequence of input values and
    returns the resulting state.
  *)
  from : State -> list Input -> State :=
    fun initial input => fold_left transition input initial;

  (*
    Accepts an input sequence and returns the final state of the
    machine after it has processed the input.
  *)
  execute : list Input -> State := from initial;
}.

Section abstract.
  Variable fsm : FSM.

  Lemma trans_flip2 : transition fsm = flip (flip (transition fsm)).
  Proof.
    unfold flip.
    apply (functional_extensionality).
    intro s.
    apply (functional_extensionality).
    intro x.
    reflexivity.
  Qed.

  Lemma from_trans :
    forall (s : State fsm) (x : Input fsm) (xs : list (Input fsm)),
      from fsm s (xs ++ [x]) = transition fsm (from fsm s xs) x.
  Proof.
    intros s x xs.
    rewrite (rev_app x xs).
    unfold from.
    rewrite (trans_flip2) at 1.
    unfold flip at 1.
    rewrite <- (fold_left_rev_right (flip (transition fsm)) (rev (x :: rev xs)) s).
    rewrite (rev_involutive (x :: rev xs)).
    simpl.
    unfold flip.
    rewrite (fold_left_rev_right (fun y t => transition fsm t y) xs s).
    reflexivity.
  Qed.

  (* Represents invariants *)
  Definition Invariant : Type := list (Input fsm) -> (State fsm) -> Prop.

  (*
    A predicate asserting that this machine's transition rules
    preserve a given invariant
  *)
  Definition transitionPreservesInvariant (p : Invariant) : Prop :=
    forall (xs : list (Input fsm)) (s : State fsm), p xs s ->
      forall x : Input fsm, p (xs ++ [x]) (transition fsm s x).

  (*
    Proves that the transitive closure of transitions preserves a
    given invariant provided the transition function does.
  *)
  Lemma fromPreservesInvariant :
    forall (p : Invariant), transitionPreservesInvariant p ->
      forall (xs : list (Input fsm)) (s : State fsm) , p xs s -> forall ys : list (Input fsm), p (xs ++ ys) (from fsm s ys).
  Proof.
    intros p Ht xs s Hs ys. 
    rewrite <- (rev_involutive ys).
    induction (rev ys) as [|z zs Hind].
    + simpl.
      rewrite (app_nil_r xs).
      assumption.
    + rewrite <- (rev_involutive zs).
      rewrite <- (rev_app z (rev zs)).
      rewrite (from_trans s z (rev zs)).
      rewrite (app_assoc xs (rev zs) [z]).
      exact (Ht (xs ++ rev zs) (from fsm s (rev zs)) Hind z).
  Qed.

  (*
    Proves that the machine preserves a given invariant provided
    that the initial machine state satisfies the invariant and the
    transition function preserves the invariant.
  *)
  Theorem preservesInvariant :
    forall (p : Invariant), p [] (initial fsm) -> transitionPreservesInvariant p ->
      forall xs : list (Input fsm), p xs (execute fsm xs).
  Proof.
    intros p Hi Ht xs.
    unfold execute.
    exact (fromPreservesInvariant p Ht [] (initial fsm) Hi xs).
  Qed.
    
End abstract.
