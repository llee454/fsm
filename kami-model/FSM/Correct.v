(*
  This module defines an equivalence relation (a bijection) between
  the states of the Kami model and the abstract finite state machine
  and proves that the correctness invariant is preserved by this
  equivalence relation. Hence that the Kami model is correct.
*)
Require Import Kami.All.
Require Import FSM.FSM.
Require Import Fsm.Fsm.
Require Import Fsm.Machine.
Require Import List.
Import ListNotations.

Section ty.
  Variable ty : Kind -> Type.

  Definition getMethCallVals (s : Signature) (methCall : MethT) : option (SignT s) :=
    match Signature_dec s (projT1 (snd methCall)) with
    | left H => Some (eq_rect_r SignT (projT2 (snd methCall)) H)
    | _      => None 
    end.
    
  Definition getMethCallRes (j k : Kind) (methCall : MethT) : option (type k) :=
    match getMethCallVals (j, k) methCall with
    | Some (_, x) => Some x
    | None        => None
    end.

  Fixpoint getNextMethCall (n : String) (ls : list FullLabel) : option MethT :=
    match ls with
    | [] => None
    | label:remLabels =>
        match fst (snd label) with
        | Rle _         => None
        | Meth methCall => String.eqb (fst methCall) n
        end
          


  Fixpoint getNextInput (ls : list FullLabel) : option (Bit 1 @# ty) := 
    match ls with
    | [] => None
    | (label:remLabels) =>
      match fst (snd label) with
      | Rle _ => None
      | Meth methCall =>
        if String.eqb (fst methCall) "getInput"
          then
            snd (match Signature_dec (Void, Bit 1) (projT1 methCall) return
              SignT (Void, Bit 1) with
            | left Heq => (* Void, Bit 1 = projT1 methCall *)
              Some (eq_ind (projT1 methCall) SignT (projT2 methCall) (Void, Bit 1) Heq)
            | _ => None
            end)
          else None
      end
projT2
SignT
MethT

End.

Fixpoint inputEqv
  (absInput : list (Input fsm))
  (modelTrace : list (list FullLabel))
  : bool :=
  match absInput with
  | [] => match modelTrace with [] => true | _ => false end
  | (b:bs) =>
    if 

Definition eqv
  (absInput : list (Input fsm))
  (absState : State fsm)
  (modelRegs : RegsT)
  (modelTrace : list (list FullLabel)) : Prop :=
  
  
