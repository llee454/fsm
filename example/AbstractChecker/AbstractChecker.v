(*
  This module describes a finite state machine (FSM) that accepts
  a sequence of bits and outputs 1 iff the number encoded by the
  received bits is divisible by 3.
*)
Require Import Nat.
Require Import PeanoNat.
Require Import Program.
Require Import List.
Require Import Lia.
Import ListNotations.
Import Nat.
Require Import Fsm.Fsm.
Require Import Fsm.Aux.

Inductive Bit : Set := Zero | One.

(* Represents the states associated with the FSM below. *)
Inductive FsmS : Set := SZero | SOne | STwo.

(*
  Represents a finite state machine that accepts a sequence of bits
  and outputs 1 if the number represented by the bits is divisible
  by 3, and 0 otherwise.
*)
Definition fsm := {|
  State   := FsmS;
  Input   := Bit;
  Output  := Bit;
  initial := SZero;
  output  := fun s => match s with SZero => One | _ => Zero end;
  transition :=
    fun s b =>
      match s with
      | SZero => if b then SZero else SOne
      | SOne  => if b then STwo  else SZero
      | STwo  => if b then SOne  else STwo
      end
|}.

(* Returns the number represented by a given bit. *)
Definition decodeBit (b : Bit) : nat := match b with Zero => 0 | _ => 1 end.

(*
  Accepts a bit sequence in little endian format and returns the
  number represented by the sequence.
*)
Fixpoint decodeAux (bs : list Bit) : nat :=
  match bs with [] => 0 | c :: cs => 2 * (decodeAux cs) + decodeBit c end.

(*
  Accepts a bit sequence in big endian format and returns the number
  represented by the sequence.
*)
Definition decode (bs : list Bit) : nat := decodeAux (rev bs).

(* Returns the number represented by the given state. *)
Definition decodeState (s : FsmS) : nat := match s with SZero => 0 | SOne => 1 | STwo => 2 end.

(*
  Defines the key invariant that we will use to prove that our
  FSM is correct - i.e. if we give our FSM a sequence of bits [bs]
  then the resulting state corresponds to the remainder we get when
  we divide the number rpresented by [bs] by 3.
*)
Definition fsmInvariant (bs : list Bit) (s : FsmS) : Prop := decodeState s = decode bs mod 3.

(*
  Proves that the initial state of our FSM satisfies our invariant
  [fsmInvariant].
*)
Lemma fsmInvariantInit : fsmInvariant [] (initial fsm).
Proof.
  unfold fsmInvariant.
  reflexivity.
Qed.

Lemma decodeEq : forall bs : list Bit, decode bs = decodeAux (rev bs).
Proof.
  intro bs.
  reflexivity.
Qed.

(*
  Proves that the machine's transition rule preserves our invariant
  [fsmInvariant].
*)
Lemma fsmTransPresInvariant : transitionPreservesInvariant fsm fsmInvariant.
Proof.
  unfold transitionPreservesInvariant.
  unfold fsmInvariant.
  unfold decode at 2.
  intros xs s H x.
  rewrite (rev_app x xs).
  rewrite (rev_involutive (x :: rev xs)) at 1.
  unfold decodeAux.
  fold (decodeAux (rev xs)).
  rewrite <- (decodeEq xs) at 1.
  destruct s, x; unfold decodeState in H; lazy iota beta zeta delta -[decode modulo mul plus].
  (* state 0 *)
  + refine (ex_ind (fun k => _) (mod_ex 0 (decode xs) 3 ltac:(lia) H)).
    intro Hk.
    rewrite (add_0_r (k * 3)) in Hk.
    rewrite (add_0_r (2 * decode xs)).
    rewrite <- Hk.
    rewrite (mul_assoc 2 k 3).
    rewrite (mod_mul (2 * k) 3 ltac:(lia)).
    reflexivity.
  + refine (ex_ind (fun k => _) (mod_ex 0 (decode xs) 3 ltac:(lia) H)).
    intro Hk.
    rewrite (add_0_r (k * 3)) in Hk.
    rewrite <- Hk.
    rewrite (add_comm (2 * (k * 3)) 1).
    rewrite (mul_assoc 2 k 3).
    rewrite (mod_add 1 (2 * k) 3 ltac:(lia)).
    rewrite (mod_small 1 3 ltac:(lia)).
    reflexivity.
  (* state 1 *)
  + refine (ex_ind (fun k => _) (mod_ex 1 (decode xs) 3 ltac:(lia) H)).
    intro Hk.
    rewrite (add_0_r (2 * decode xs)).
    rewrite <- Hk.
    rewrite (mul_add_distr_l 2 (k * 3) 1).
    rewrite (mul_1_r 2).
    rewrite (add_comm (2 * (k * 3)) 2).
    rewrite (mul_assoc 2 k 3).
    rewrite (mod_add 2 (2 * k) 3 ltac:(lia)).
    rewrite (mod_small 2 3 ltac:(lia)).
    reflexivity.
  + refine (ex_ind (fun k => _) (mod_ex 1 (decode xs) 3 ltac:(lia) H)).
    intro Hk.
    rewrite <- Hk.
    rewrite (mul_add_distr_l 2 (k * 3) 1).
    rewrite (mul_1_r 2).
    rewrite <- (add_assoc (2 * (k * 3)) 2 1).
    replace (2 + 1) with 3 by lia.
    rewrite (mul_assoc 2 k 3).
    rewrite (add_comm (2 * k * 3) 3).
    rewrite (mod_add 3 (2 * k) 3 ltac:(lia)).
    rewrite (mod_same 3 ltac:(lia)).
    reflexivity.
  (* state 2 *)
  + refine (ex_ind (fun k => _) (mod_ex 2 (decode xs) 3 ltac:(lia) H)).
    intro Hk.
    rewrite (add_0_r (2 * decode xs)).
    rewrite <- Hk.
    rewrite (mul_add_distr_l 2 (k * 3) 2).
    replace (2 * 2) with 4 by lia.
    rewrite (add_comm (2 * (k * 3)) 4).
    rewrite (mul_assoc 2 k 3).
    rewrite (mod_add 4 (2 * k) 3 ltac:(lia)).
    simpl.
    reflexivity.
  + refine (ex_ind (fun k => _) (mod_ex 2 (decode xs) 3 ltac:(lia) H)).
    intro Hk.
    rewrite <- Hk.
    rewrite (mul_add_distr_l 2 (k * 3) 2).
    replace (2 * 2) with 4 by lia.
    rewrite <- (add_assoc (2 * (k * 3)) 4 1).
    replace (4 + 1) with 5 by lia.
    rewrite (add_comm (2 * (k * 3)) 5).
    rewrite (mul_assoc 2 k 3).
    rewrite (mod_add 5 (2 * k) 3 ltac:(lia)).
    simpl.
    reflexivity.
Qed.

(*
  Proves that our finite state machine is correct - i.e. that it
  accepts a sequence of bits [bs] and outputs a [1] iff the number
  represented by [bs] is divisible by 3.
*)
Theorem fsm_correct : forall bs : list Bit, decodeBit (output fsm (execute fsm bs)) = 1 <-> divide 3 (decode bs).
Proof.
  intro bs.
  rewrite <- (mod_divide (decode bs) 3 ltac:(lia)).
  set (Hi := preservesInvariant fsm fsmInvariant fsmInvariantInit fsmTransPresInvariant bs).
  unfold fsmInvariant in Hi.
  split.
  + refine (FsmS_rect (fun s => s = execute fsm bs -> decodeBit (output fsm (execute fsm bs)) = 1 -> decode bs mod 3 = 0) _ _ _ (execute fsm bs) ltac:(reflexivity));
      intro He;
      rewrite <- He in *;
      lazy iota zeta beta delta -[decode modulo];
      rewrite <- Hi;
      intro Htemp.
      - reflexivity.
      - contradict Htemp; lia.
      - contradict Htemp; lia.
  + intro H.
    refine (FsmS_rect (fun s => s = execute fsm bs -> decodeBit (output fsm (execute fsm bs)) = 1) _ _ _ (execute fsm bs) ltac:(reflexivity));
      intro He;
      rewrite <- He in *.
      - reflexivity.
      - rewrite H in Hi.
        contradict Hi.
        simpl. lia.
      - rewrite H in Hi.
        contradict Hi.
        simpl. lia.
Qed.
