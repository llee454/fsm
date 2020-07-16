(*
  This module defines an equivalence relation (a bijection) between
  the states of the Kami model and the abstract finite state machine
  and proves that the correctness invariant is preserved by this
  equivalence relation. Hence that the Kami model is correct.
*)
Require Import Checker.Checker.
Require Import Fsm.Fsm.
Require Import AbstractChecker.AbstractChecker.
Require Import Kami.All.
Require Import List.
Import ListNotations.

Axiom TODO : forall {A}, A.

Definition option_bind {A B : Type} (x : option A) (f : A -> option B) : option B :=
  match x with
  | None   => None
  | Some k => f k
  end.

Notation "X >>- F" := (option_bind X F) (left associativity, at level 90).

Definition option_alt {A : Type} (x y : option A) : option A :=
  match x with
  | None   => y
  | Some _ => x
  end.

Notation "X <?> Y" := (option_alt X Y) (left associativity, at level 89).

Definition isSome {A : Type} (x : option A) : bool :=
  match x with
  | Some _ => true
  | _      => false
  end.

Definition isNone {A : Type} (x : option A) : bool :=
  match x with
  | None => true
  | _    => false
  end.

Definition fromSome {A : Type} (x : option A) : isSome x = true -> A :=
  match x return isSome x = true -> A with
  | Some y => fun _ => y
  | None   => fun Hcontr : false = true => False_rect A (diff_false_true Hcontr)
  end.

Section ty.
  Variable ty : Kind -> Type.

  Definition regName : RegT -> string := fst.

  Definition regKind (r : RegT) : FullKind := projT1 (snd r).

  Definition castFullVal {k j : FullKind} (H : k = j) (x : fullType type k) : fullType type j :=
    eq_rect k (fullType type) x j H.

  Definition castVal {k j : Kind} (H : k = j) (x : type k) : type j :=
    eq_rect k type x j H.

  Definition regValue (k : Kind) (r : RegT) : option (type k) :=
    match regKind r as t return t = regKind r -> option (type k) with
    | SyntaxKind j =>
      match Kind_dec j k with
      | left Heq (* j = k *) => 
        fun H : SyntaxKind j = regKind r =>
          Some (castVal Heq (castFullVal (eq_sym H) (projT2 (snd r))))
      | right _  => fun _ => None
      end
    | NativeKind _ _ => fun _ => None
    end eq_refl.

  (*
    Accepts two arguments: s, a method signature; and methCall, a
    method call; and returns the values passed to and received from
    the method call if s matches the kinds passed to and received
    from the method call. Otherwise, this function returns None.
  *)
  Definition methCallVals (s : Signature) (methCall : MethT) : option (SignT s) :=
    match Signature_dec s (projT1 (snd methCall)) with
    | left H => Some (eq_rect_r SignT (projT2 (snd methCall)) H)
    | _      => None 
    end.

  (*
    Accepts three arguments: j, the kind of argument in a method
    call; k, the kind of value returned by a method call; and
    methCall, a method call; and returns the argument of the
    method call represented by methCall. If j and k do not match
    the signature of methCall, this function returns None.
  *)
  Definition methCallReq (j k : Kind) (methCall : MethT) : option (type j) :=
    methCallVals (j, k) methCall >>- fun vals => Some (fst vals).

  Definition methCallRes (j k : Kind) (methCall : MethT) : option (type k) :=
    methCallVals (j, k) methCall >>- fun vals => Some (snd vals).

  Definition methCallName : MethT -> string := fst.

  Definition methCallHasName (name : string) (methCall : MethT) : bool :=
    String.eqb name (methCallName methCall).

  (*
    Accepts two arguments: name, a method name; and step, an
    execution step; and returns the call to the method referenced
    by name in step. If the method isn't called, this function
    returns None.

    Note: in a wellformed module, each method can only be called
    once per step.
  *)
  Fixpoint stepMethCall (name : string) (step : list FullLabel) : option MethT :=
    match step with
    | [] => None
    | label::remLabels =>
      match fst (snd label) with
      | Rle _         => None
      | Meth methCall =>
        if (methCallHasName name methCall)
        then Some methCall
        else None
      end <?>
      (find (methCallHasName name) (snd (snd label))) <?>
      (stepMethCall name remLabels)
    end.

  (* Represents the type of input read by the module. *)
  Definition Input : Set := word 1.

  (* Represents the type of output returned by the module. *)
  Definition Output : Set := bool.

  (* 
    Accepts one argument: step, an execution step; and returns the
    input value read by the module during step. If the module did
    not read any input during step, this function returns None.
  *)
  Fixpoint stepInput (step : list FullLabel) : option Input :=
    stepMethCall "getInput" step >>- methCallRes Void (Bit 1).

  (*
    Accepts one argument: step, an execution step; and returns the
    value output by the module during step. If the module did not
    output any value during step, this function returns None.
  *)
  Fixpoint stepOutput (step : list FullLabel) : option Output :=
    stepMethCall "sendOutput" step >>- methCallReq Bool Void.

  (*
    Accepts two arguments: [name], a method name; and [step],
    the effects of the rules and methods executed during a step;
    and returns the call to the method referenced by [name].
  *)
  Fixpoint stepMethCallCut (name : string) (step : list FullLabel) : option MethT :=
    match step with
    | [] => None
    | label :: rem =>
      match fst (snd label) with
      | Rle _ => None
      | Meth methCall =>
        if methCallHasName name methCall
        then Some methCall
        else None
      end <?>
      (find (methCallHasName name) (snd (snd label))) <?>
      (stepMethCallCut name rem)
    end.

  (*
    Accepts two arguments: name, a method name; and trace; and
    returns the next call to the method named name in trace along
    with the subsequent trace labels.
  *)
  Fixpoint traceMethCallCut (name : string) (trace : list (list FullLabel)) : option (MethT * list (list FullLabel)) := 
    match trace with
    | []           => None
    | step :: cont =>
      (stepMethCallCut name step >>- fun methCall => Some (methCall, cont)) <?>
      (traceMethCallCut name cont)
    end.

  Definition inputEqv (absInput : Fsm.Input fsm) (input : Input) : bool :=
    Nat.eqb (decodeBit absInput) (wordToNat input).

  Definition outputEqv (absOutput : Fsm.Output fsm) (output : Output) : bool :=
    Nat.eqb (decodeBit absOutput) (if output then 1 else 0).

  Definition toAbsInput (intput : Input) : Fsm.Input fsm := TODO.

  Definition toAbsOutput (output : Output) : Fsm.Output fsm := TODO.

  (*
    Accepts two arguments: [absInput], a sequence of bits sent
    to the abstract machine; and [modelTrace], a Kami trace; and
    asserts that the input represented by [absInput] and [modelTrace]
    are equivalent.
  *)
  Fixpoint inputsEqv
    (absInput : list (Fsm.Input fsm))
    (modelTrace : list (list FullLabel))
    : bool :=
    match absInput with
    | [] => match modelTrace with [] => true | _ => false end
    | (b :: bs) =>
      match traceMethCallCut "getInput" modelTrace with
      | None => false
      | Some (methCall, cont) =>
        match methCallRes Void (Bit 1) methCall with
        | None => false 
        | Some input =>
          Nat.eqb (decodeBit b) (wordToNat input) &&
          inputsEqv bs cont
        end
      end
    end.

  (*
    Accepts two arguments: [absState], an abstract machine state;
    and [modelState], a state of the Kami model; and returns true
    iff they are equivalent.
  *)
  Definition stateEqv
    (absState : Fsm.State fsm)
    (modelState : RegsT)
    : bool :=
    match modelState with
    | [] => false
    | reg :: regs =>
      fromOption
        (regValue Checker.State reg >>-
          fun x : word 2 => Some (Nat.eqb (wordToNat x) (decodeState absState)))
        false
    end.

  Definition Transition : Type := (RegsT * list FullLabel).

  Definition Behavior : Type := list Transition.

  Definition behaviorTrace : Behavior -> list (list FullLabel) := map snd.

  Inductive validBehavior : Behavior -> Prop :=
    | nullBehavior :
      forall state : RegsT, Trace FSMMod state [[]] -> validBehavior [(state, [])]
    | stepBehavior :
      forall (state : RegsT) (step : list FullLabel) (b : Behavior),
      validBehavior b ->
      Trace FSMMod state (step :: behaviorTrace b) ->
      validBehavior ((state, step) :: b).

  Lemma validBehaviorNil : ~ validBehavior [].
  Proof.
    intro Hcontr.
    inversion Hcontr.
  Qed.

  Lemma behaviorInitNil : forall state step, validBehavior [(state, step)] -> step = [].
  Proof.
    intros state step H.
    destruct step.
    + reflexivity.
    + inversion H.
      contradict H2.
      exact validBehaviorNil.
  Qed.

  Definition behaviorState {b : Behavior} : validBehavior b -> RegsT :=
    match b with
    | [] => fun Hcontr : validBehavior [] => False_rect _ ltac:(inversion Hcontr)
    | t :: _ => fun _ => fst t
    end.

  Lemma validBehaviorTrace :
    forall (b : Behavior) (H : validBehavior b),
      Trace FSMMod (behaviorState H) (behaviorTrace b).
  Proof.
    destruct b as [|x xs].
    + intro H. inversion H.
    + intro Hb.
      exact
        (validBehavior_ind
          (fun b => forall H : validBehavior b, Trace FSMMod (behaviorState H) (behaviorTrace b))
          (fun state H _ => H)
          (fun state step b Hb F H _ => H)
          Hb Hb).
  Qed.

  Lemma validBehaviorTail :
    forall (t u : RegsT * list FullLabel) (b : Behavior), validBehavior (t :: u :: b) -> validBehavior (u :: b).
  Proof.
    intros t u b H.
    inversion H; assumption.
  Qed.

  (*
    Accepts four arguments: input, a model input sequence; absState,
    the state reached by the fsm in response to input; modelState,
    the state reached by the model in response to input; and
    trace, a trace produced by the model while processing input;
    and returns true iff the externally observable behavior of the
    model matches that of the fsm in response to the given input.
  *)
  Inductive behaviorEqv : list Input -> Fsm.State fsm -> Behavior -> Prop :=
    | eqvInit :
        forall modelState : RegsT,
          Trace FSMMod modelState [[]] ->
          behaviorEqv [] (Fsm.initial fsm) [(modelState, [])]
    | eqvNull :
        forall (t : Transition) (b : Behavior),
          isSome (stepInput  (snd t)) = false ->
          isSome (stepOutput (snd t)) = false ->
          forall (input : list Input) (absState : Fsm.State fsm),
            behaviorEqv input absState b ->
            behaviorEqv input absState (t :: b)
    | eqvIn :
        forall (t : Transition) (b : Behavior)
          (H : isSome (stepInput (snd t)) = true),
          isSome (stepOutput (snd t)) = false ->
          forall (input : list Input) (absState : Fsm.State fsm),
            behaviorEqv input absState b ->
            behaviorEqv (fromSome (stepInput (snd t)) H :: input)
                (Fsm.transition fsm absState (toAbsInput (fromSome (stepInput (snd t)) H)))
                (t :: b)
    | eqvOut :
        forall (t : Transition) (b : Behavior)
          (H : isSome (stepOutput (snd t)) = true),
          isSome (stepInput (snd t)) = false ->
          forall (input: list Input) (absState : Fsm.State fsm),
            behaviorEqv input absState b ->
            outputEqv (Fsm.output fsm absState) (fromSome (stepOutput (snd t)) H) = true ->
            behaviorEqv input absState (t :: b)
    | eqvInOut :
        forall (t : Transition) (b : Behavior)
          (Hin  : isSome (stepInput  (snd t)) = true)
          (Hout : isSome (stepOutput (snd t)) = true)
          (input : list Input) (absState : Fsm.State fsm),
            behaviorEqv input absState b ->
            outputEqv (Fsm.output fsm absState) (fromSome (stepOutput (snd t)) Hout) = true ->
            behaviorEqv (fromSome (stepInput (snd t)) Hin :: input)
                (Fsm.transition fsm absState (toAbsInput (fromSome (stepInput (snd t)) Hin)))
                (t :: b).

  Fixpoint eqvAbsState (b : Behavior) :
    validBehavior b -> {x : list Input * Fsm.State fsm | behaviorEqv (fst x) (snd x) b} :=
    match b return
      forall H : validBehavior b, {x | behaviorEqv (fst x) (snd x) b} with
    | [] => fun Hcontr => False_rect _ ltac:(inversion Hcontr)
    | ((state, step) :: ts) =>
      let F us :=
        match us as vs return 
          ts = vs ->
          match vs with
          | []       => validBehavior [(state, step)]       -> {x | behaviorEqv (fst x) (snd x) [(state, step)]}
          | (_ :: _) => validBehavior ((state, step) :: ts) -> {x | behaviorEqv (fst x) (snd x) ((state, step) :: ts)}
          end with
        | [] => fun _ =>
          match step with
          | []        => fun Hb => exist _ ([], Fsm.initial fsm) (eqvInit (validBehaviorTrace Hb))
          | (e :: es) => fun Hb => False_rect _ ltac:(inversion Hb; apply validBehaviorNil; assumption)
          end
        | (v :: vs) => fun Hts Hb =>
          let G :=
            @eqvAbsState ts
              (eq_rect_r 
                validBehavior
                (validBehaviorTail (eq_rect ts (fun ws => validBehavior ((state, step) :: ws)) Hb (v :: vs) Hts))
                Hts) in
          match (isSome (stepInput step), isSome (stepOutput step)) as Hinout return
            isSome (stepInput  step) = fst Hinout ->
            isSome (stepOutput step) = snd Hinout ->
            {x | behaviorEqv (fst x) (snd x) ((state, step) :: ts)} with
          | (false, false) => fun Hin Hout =>
            exist _ (proj1_sig G)
              (eqvNull (state, step) Hin Hout (proj2_sig G))
          | (true,  false) => fun Hin Hout =>
            let input := fromSome (stepInput step) Hin in
            exist _
              (input :: fst (proj1_sig G), Fsm.transition fsm (snd (proj1_sig G)) (toAbsInput input))
              (eqvIn (state, step) Hin Hout (proj2_sig G))
          | (false,  true) => fun Hin Hout =>
            exist _ (proj1_sig G) (eqvOut (state, step) Hout Hin (proj2_sig G) TODO)
          | (true,   true) => fun Hin Hout =>
            let input := fromSome (stepInput step) Hin in
            exist _
              (input :: fst (proj1_sig G), Fsm.transition fsm (snd (proj1_sig G)) (toAbsInput input))
              (eqvInOut (state, step) Hin Hout (proj2_sig G) TODO)
          end
          (eq_refl (isSome (stepInput step)))
          (eq_refl (isSome (stepOutput step)))
        end in
      match ts as us return ts = us -> validBehavior ((state, step) :: ts) -> {x | behaviorEqv (fst x) (snd x) ((state, step) :: ts)} with
      | [] => fun Hts => 
        eq_rect_r
          (fun vs =>
            validBehavior ((state, step) :: vs) ->
            {x | behaviorEqv (fst x) (snd x) ((state, step) :: vs)})
          (F [] Hts) Hts
      | (u :: us) => F (u :: us)
      end eq_refl
    end.

  Lemma behaviorEqvValidTl :
    forall (input : list Input) (absState : Fsm.State fsm) (t : Transition) (b : Behavior),
      behaviorEqv input absState b ->
      validBehavior (t :: b) ->
      validBehavior b.
  Proof.
    intros input absState t b Hb Ht.
    induction b as [|u us]; inversion Hb;
      [> apply nullBehavior; assumption | apply (@validBehaviorTail t u us); assumption ..].
  Qed.

  Lemma initStateEqv :
    forall state : RegsT, Trace FSMMod state [[]] -> stateEqv (Fsm.initial fsm) state = true.
  Proof. Admitted.

  Lemma stateStable :
    forall (state : RegsT) (step : list FullLabel) (b : Behavior) (H : validBehavior b),
      isSome (stepInput step) = false -> state = behaviorState H.
  Proof. Admitted.

  Lemma behaviorEqvTl :
    forall (input : list Input) (absState : Fsm.State fsm) (t : Transition) (b : Behavior),
      behaviorEqv input absState (t :: b) -> validBehavior b.
  Proof. Admitted.

  Lemma transitionPreservesStateEqv :
    forall (absState : Fsm.State fsm) (step : list FullLabel) (state : RegsT) (b : Behavior)
      (H : isSome (stepInput step) = true)
      (Hb : validBehavior b),
      validBehavior ((state, step) :: b) -> 
      stateEqv absState (behaviorState Hb) = true ->
      stateEqv
        (Fsm.transition fsm absState (toAbsInput (fromSome (stepInput step) H)))
        state = true.
  Proof. Admitted.

  Lemma behaviorEqvStateEqv :
    forall (b : Behavior) (input : list Input) (absState : Fsm.State fsm),
      behaviorEqv input absState b -> forall Hb : validBehavior b,
        stateEqv absState (behaviorState Hb) = true.
  Proof.
    intro b.
    induction b as [|t ts]; intros input absState He Hb.
    + contradict Hb.
      exact validBehaviorNil.
    + inversion He.
      - simpl.
        rewrite <- H.
        exact (initStateEqv H2).
      - simpl.
        rewrite (stateStable (fst t) (snd t) (behaviorEqvTl He) H1).
        exact (IHts input absState H5 (behaviorEqvTl He)). 
      - lazy delta [behaviorState] beta iota zeta.
        destruct t as [state step].
        assert (Hts : validBehavior ts).
        * exact (behaviorEqvValidTl H6 Hb).
        * apply (@transitionPreservesStateEqv _ step state ts H1 Hts Hb (@IHts input0 absState0 H6 Hts)).
      - simpl.
        rewrite (stateStable (fst t) (snd t) (behaviorEqvTl He) H2).
        exact (IHts input absState H5 (behaviorEqvTl He)).
      - lazy delta [behaviorState] beta iota zeta.
        destruct t as [state step].
        assert (Hts : validBehavior ts).
        * exact (behaviorEqvValidTl H3 Hb).
        * apply (@transitionPreservesStateEqv _ step state ts Hin0 Hts Hb (@IHts input0 absState0 H3 Hts)).
  Qed.

  Lemma stateEqvOutput :
    forall (absState : Fsm.State fsm) (state : RegsT) (step : list FullLabel) (t : list (list FullLabel)) (Hout : isSome (stepOutput step) = true),
      Trace FSMMod state (step :: t) ->
      stateEqv absState state = true ->
      outputEqv (Fsm.output fsm absState) (fromSome (stepOutput step) Hout) = true.
  Proof. Admitted.

  Lemma behaviorEqvOutputEqv
    : forall (state : RegsT) (step : list FullLabel) (b : Behavior) (xs : list Input)
        (absState : Fsm.State fsm)
        (Hout : isSome (stepOutput step) = true)
        (He : behaviorEqv xs absState ((state, step) :: b))
        (Hb : validBehavior ((state, step) :: b)),
        outputEqv (Fsm.output fsm absState) (fromSome (stepOutput step) Hout) = true.
  Proof.
    intros state step b xs absState Hout He Hb.
    exact (stateEqvOutput absState Hout
      (validBehaviorTrace Hb)
      (behaviorEqvStateEqv He Hb)).
  Qed.

  Inductive behaviorInput : Behavior -> list Input -> Prop :=
  | behaviorInputInit : forall t : Transition, behaviorInput [t] []
  | behaviorInputRead :
    forall state step b x xs (Hin : isSome (stepInput step) = true),
      fromSome (stepInput step) Hin = x ->
      behaviorInput b xs ->
      behaviorInput ((state, step) :: b) (x :: xs)
  | behaviorInputUnread :
    forall state step b xs (Hin : isSome (stepInput step) = false),
      behaviorInput b xs ->
      behaviorInput ((state, step) :: b) xs.

  (* what it means for the model to behave correctly. *)
(*
  Theorem correct :
    forall (xs : list Input) (b : Behavior), validBehavior b -> behaviorInput b xs -> behaviorEqv xs (Fsm.execute fsm (map toAbsInput xs)) b.
  Proof.
    intros xs b. 
    induction b as [|t b]; intros Hb Hin.
    + contradict Hb.
      exact validBehaviorNil.
    + destruct t as [state step].
      induction xs as [|x xs].
      - unfold Fsm.execute in *; unfold Fsm.from in *.
        lazy delta - [Fsm.initial fsm] beta zeta iota.
        lazy delta - [Fsm.initial fsm] beta zeta iota in IHb.
        destruct b as [|t b].
        * destruct step as [|e es].
          ** exact (eqvInit (validBehaviorTrace Hb)).
          ** inversion Hb.
             contradict H1.
             exact (validBehaviorNil).
        * inversion Hin.
          refine (
            match isSome (stepOutput step) as Hout return
              isSome (stepOutput step) = Hout -> behaviorEqv [] (Fsm.initial fsm) ((state, step) :: t :: b) with
              | true  => fun Hout => _
              | false => fun Hout => _
              end eq_refl).
          ** apply (eqvOut (state, step) Hout Hin0 
               (IHb (validBehaviorTail Hb) H3)).
             simpl.
*)

End ty.
