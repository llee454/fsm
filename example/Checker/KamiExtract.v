Require Import Kami.All.
Require Import Kami.Compiler.Compiler.
Require Import Kami.Compiler.Rtl.
Require Import Kami.Compiler.Test.
Require Import Kami.Simulator.NativeTest.
Require Import Kami.Simulator.CoqSim.Simulator.
Require Import Kami.Simulator.CoqSim.HaskellTypes.
Require Import Kami.Simulator.CoqSim.RegisterFile.
Require Import Kami.Simulator.CoqSim.Eval.
Require Import Kami.WfActionT.
Require Import Kami.SignatureMatch.
Require Import Checker.Checker.
Require Import List.
Import ListNotations.

Unset Extraction Optimize.
Separate Extraction
  FSMMod

  predPack
  orKind
  predPackOr
  createWriteRq
  createWriteRqMask
  pointwiseIntersectionNoMask
  pointwiseIntersectionMask
  pointwiseIntersection
  pointwiseBypass
  getDefaultConstFullKind
  CAS_RulesRf
  Fin_to_list

  getCallsWithSignPerMod
  RtlExpr'
  getRtl

  CompActionSimple
  RmeSimple
  RtlModule
  getRules

  separateModRemove
  separateModHidesNoInline


  testReg
  testAsync
  testSyncIsAddr
  testSyncNotIsAddr
  testNative

  print_Val2
  init_state
  sim_step
  initialize_files_zero
  option_map
  .
