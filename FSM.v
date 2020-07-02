(*
  This Kami module represents a device that accepts a sequence
  of bits that represents a binary number and returns a 1 iff the
  number represented by the given sequence is divisible by 3.
*)

Require Import Kami.
Require Import List.
Import ListNotations.

Definition StateMod0 := 0.
Definition StateMod1 := 1.
Definition StateMod2 := 2.
Definition stateSz := 2.
Definition State := Bit stateSz.
Definition stateReg := "state".

Open Scope kami_expr.
Open Scope kami_action.

Definition module : Mod :=
  Base (MODULE {
    Register stateReg : State <- ConstBit ($StateMod0 : word stateSz) with

    Method "input" (b : Bit 1) : Void := 
      Read state : State <- stateReg;
      Write stateReg : State <-
        Switch #state Retn State With {
          ($StateMod0 : State @# _) ::=
            IF b == $0 then $StateMod0 else $StateMod1
          ($StateMod1 : State @# _) ::=
            IF b == $0 then $StateMod2 else $StateMod0
          ($StateMod2 : State @# _) ::=
            IF b == $0 then $StateMod1 else $StateMod2
        };
      Retv with

    Method "output" () : Bool :=
      Read state : State <- stateReg;
      Ret (#state == $StateMod0)
  }).

Close Scope kami_action.
Close Scope kami_expr.
