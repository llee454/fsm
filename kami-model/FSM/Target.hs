module Target (module Syntax, module Rtl, module Word, module Fin, module PeanoNat, module CompilerSimple, module Extraction, module LibStruct, module FSM, module Test, getRtl, rtlMod) where
import CompilerSimple hiding (unsafeCoerce, __)
import PeanoNat
import Fin hiding (unsafeCoerce, Any, f2n)
import FSM hiding (unsafeCoerce, __)
import Rtl
import Syntax hiding (__)
import Extraction hiding (unsafeCoerce, Any)
import Word
import LibStruct hiding (unsafeCoerce, __)
import Test hiding (unsafeCoerce, Any, coq_Counter, coq_Data)
import UnverifiedIncompleteCompiler hiding (unsafeCoerce, Any)

rtlMod :: ([String], ([RegFileBase], BaseModule))
rtlMod = separateModRemove coq_FSMMod
