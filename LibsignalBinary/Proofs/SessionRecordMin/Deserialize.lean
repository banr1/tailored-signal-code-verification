/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SessionRecordAt.Hooks2.Deser.DeserAssemblyW
public import LibsignalBinary.Proofs.SessionRecordAt.Hooks2.Deser.DeserTransportX
public import LibsignalBinary.Proofs.SessionRecordAt.Hooks2.SerDefsX
public import LibsignalBinary.Proofs.SessionRecordAt.Swarm.TRREF.B3DeserQ.LoopW
import GeneratedLean.LibsignalSessionCode -- shake: keep
import LibsignalBinary.Proofs.ConsumeMessageKey.FindIndexProofs.Loop
import LibsignalBinary.Proofs.FnOffEq
import LibsignalBinary.Proofs.SessionRecordAt.Hooks2.Deser.RecordDeserializeX
import LibsignalBinary.Proofs.SessionRecordAt.Hooks2.DeserLoopEntryGExt
import LibsignalBinary.Proofs.SessionRecordAt.Hooks2.DeserLoopExitGExt
import LibsignalBinary.Proofs.SessionRecordAt.Hooks2.DeserLoopIterGExt
import LibsignalBinary.Proofs.SessionRecordAt.Hooks2.WaveCTemplates
import LibsignalBinary.Proofs.SessionRecordAt.Swarm.TRREF.B3DeserQ.B3DeserQ
import LibsignalBinary.Proofs.SessionRecordAt.TripleRatchet.Prost.X.BytesMergeXPhase1
import LibsignalBinary.Proofs.SessionRecordAt.TripleRatchet.Prost.X.DecodeErrorFromX
import LibsignalBinary.Proofs.SessionRecordAt.TripleRatchet.Prost.X.DecodeVarintSlowX
import LibsignalBinary.Proofs.SessionRecordAt.TripleRatchet.Prost.X.Int32MergeX
import LibsignalBinary.Proofs.SessionRecordAt.TripleRatchet.Prost.X.VarintSliceX

/-!
# Minimal Stage-2 Contracts for `SessionRecord::deserialize`

Restates the `SessionRecord::deserialize` contracts over `Stage2ContractsMin` (the 7 fields of
`Stage2ContractsA0` actually used by deserialization and serialization), generalizes them to an
arbitrary `A : RustAlloc` (`Stage2ContractsMinA`, `Stage2ContractsMinExt`), and provides relocatable
`[LibsignalPlacement]` wrappers on block `46`.
-/

@[expose] public section

set_option autoImplicit false

namespace Proofs.libsignal.Hooks2

open Arm64 ProofLib SepProp
open CryptoGames CryptoGames.LibsignalSession
open CryptoVerification CryptoVerification.RustHeap
open CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.E2E CryptoVerification.E2E.HooksE

/-- The 7 fields of `Stage2ContractsA0` that the `SessionRecord::deserialize` proofs use (field
names and types verbatim). The other 9 (`allocNW_A0`, `memcpyROX`, `memset`, `bcmp`, `randomKeys`,
`formatInner_A0`, `fmtWrite_A0`, `staticDrop`, `sharedDrop`) are not needed. -/
structure Stage2ContractsMin (img : Obj.Image) (ext : String → Option (State → State)) : Prop where
  loads : Obj.Loads libsignalSessionImage img
  alloc_A0 : subroutine_ok (SP2Ext img.base ext) (img.base + stubOff allocName)
    (((rustAllocSpec HooksE.A0).withExternStackFromAlloc').inImage img)
  deallocLayout_A0 : subroutine_ok (SP2Ext img.base ext) (img.base + stubOff deallocName)
    (((rustDeallocLayoutSpec' HooksE.A0).withExternStackFromAlloc').inImage img)
  realloc_A0 : subroutine_ok (SP2Ext img.base ext) (img.base + stubOff reallocName)
    (((rustReallocSpec HooksE.A0).withExternStackFromAlloc').inImage img)
  shim : subroutine_ok (SP2Ext img.base ext) (img.base + stubOff shimName)
    ((sessionShimSpec.withHookStack CryptoVerification.LibsignalTripleRatchet.extHookStack).inImage img)
  memcpy : subroutine_ok (SP2Ext img.base ext) (img.base + stubOff memcpyName)
    ((sessionMemcpySpec CryptoVerification.LibsignalTripleRatchet.extHookStack).inImage img)
  memmove : subroutine_ok (SP2Ext img.base ext) (img.base + stubOff memmoveName)
    ((sessionMemmoveSpec CryptoVerification.LibsignalTripleRatchet.extHookStack).inImage img)

/-- Forget the 9 fields the deserialize proofs do not use. -/
theorem Stage2ContractsA0.toMin {img : Obj.Image} {ext : String → Option (State → State)}
    (hC : Stage2ContractsA0 img ext) : Stage2ContractsMin img ext :=
  ⟨hC.loads, hC.alloc_A0, hC.deallocLayout_A0, hC.realloc_A0, hC.shim, hC.memcpy, hC.memmove⟩

end Proofs.libsignal.Hooks2

/-! ## Extern Adapters -/

namespace Proofs.libsignal.Hooks2

open Arm64 ProofLib SepProp
open CryptoGames CryptoGames.LibsignalSession
open CryptoVerification CryptoVerification.RustHeap
open CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.E2E CryptoVerification.E2E.HooksE

attribute [local irreducible] Program.fetch Program.externAt? Program.fnAddr Program.fnOff

theorem Stage2ContractsMin.memcpy_ok_at {img : Obj.Image} {ext : String → Option (State → State)}
    {name : String} {k : Nat}
    (hC : Stage2ContractsMin img ext)
    (hk : libsignalSessionCode.fnOff name + k = libsignalSessionCode.fnOff memcpyName) :
    subroutine_ok (SP2Ext img.base ext) ((SP2Ext img.base ext).fnAddr name + BitVec.ofNat 64 k)
      ((sessionMemcpySpec CryptoVerification.LibsignalTripleRatchet.extHookStack).inImage img) :=
  sub_ok_at_caller hk hC.memcpy

end Proofs.libsignal.Hooks2

/-! ## `Vec::do_reserve_and_handle` -/

namespace Proofs.libsignal.Hooks2

open Arm64 ProofLib SepProp
open CryptoGames CryptoGames.LibsignalSession
open CryptoVerification CryptoVerification.RustHeap
open CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalSession
open CryptoVerification.E2E CryptoVerification.E2E.HooksE
open Proofs.libsignal.Stage1X

set_option maxRecDepth 2000000
set_option maxHeartbeats 400000

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero

set_option maxHeartbeats 800000 in
theorem allocContractsX_of_stage2ContractsMin {img : Obj.Image} {ext : String → Option (State → State)}
    (hC : Stage2ContractsMin img ext) :
    Proofs.libsignal.Stage1X.AllocContractsX img HooksE.A0 ext where
  alloc := by
    rw [SP2Ext_fnAddr]
    refine subroutine_ok_inImage_map' hC.alloc_A0 (fun ⟨size, align⟩ R s0 hpre => ?_)
      (fun _ _ _ _ _ hp => not_satisfies_false_sepConj hp)
      (fun _ _ _ _ _ _ he => not_satisfies_false_sepConj he)
    refine ⟨(size, align), R, ?_, fun sf hpost => ?_⟩
    · simp only [Proofs.libsignal.Stage1X.rustAllocSpecWithStack, Spec.withExternStackFromAlloc', rustAllocSpec,
        Stage1X.extHookStack, stackAt_externStack_split_allocHookStack'] at hpre ⊢
      exact Satisfies.mono (Entails.of_eq (by ac_rfl)) hpre
    · simp only [Proofs.libsignal.Stage1X.rustAllocSpecWithStack, Spec.withExternStackFromAlloc', rustAllocSpec,
        Stage1X.extHookStack, stackAt_externStack_split_allocHookStack'] at hpost ⊢
      exact Satisfies.mono (Entails.of_eq (by ac_rfl)) hpost
  dealloc := by
    rw [SP2Ext_fnAddr]
    refine subroutine_ok_inImage_map' hC.deallocLayout_A0 (fun ⟨p, size, align⟩ R s0 hpre => ?_)
      (fun _ _ _ _ _ hp => not_satisfies_false_sepConj hp)
      (fun _ _ _ _ _ _ he => not_satisfies_false_sepConj he)
    refine ⟨(p, size, align), R, ?_, fun sf hpost => ?_⟩
    · simp only [Proofs.libsignal.Stage1X.rustDeallocExternSpecWithStack, Spec.withExternStackFromAlloc',
        rustDeallocLayoutSpec', rustDeallocSpec, Stage1X.extHookStack,
        stackAt_externStack_split_allocHookStack', sepConj_assoc, satisfies_pure_sepConj] at hpre ⊢
      obtain ⟨⟨hx0, hx1, hx2, hlay⟩, hmem⟩ := hpre
      refine ⟨hlay, ⟨hx0, hx1, hx2⟩, ?_⟩
      exact Satisfies.mono (Entails.of_eq (by ac_rfl)) hmem
    · simp only [Proofs.libsignal.Stage1X.rustDeallocExternSpecWithStack, Spec.withExternStackFromAlloc',
        rustDeallocLayoutSpec', rustDeallocSpec, Stage1X.extHookStack,
        stackAt_externStack_split_allocHookStack'] at hpost ⊢
      exact Satisfies.mono (Entails.of_eq (by ac_rfl)) hpost
  realloc := by
    rw [SP2Ext_fnAddr]
    refine subroutine_ok_inImage_map' hC.realloc_A0 (fun ⟨p, old_size, align, new_size, bs⟩ R s0 hpre => ?_)
      (fun _ _ _ _ _ hp => not_satisfies_false_sepConj hp)
      (fun _ _ _ _ _ _ he => not_satisfies_false_sepConj he)
    refine ⟨(p, old_size, align, new_size, bs), R, ?_, fun sf hpost => ?_⟩
    · simp only [Proofs.libsignal.Stage1X.rustReallocExternSpecWithStack, Spec.withExternStackFromAlloc',
        rustReallocSpec, Stage1X.extHookStack,
        stackAt_externStack_split_allocHookStack', sepConj_assoc, satisfies_pure_sepConj] at hpre ⊢
      obtain ⟨⟨hx0, hx1, hx2, hx3, hbs1, hbs2, _hlay_old, hlay_new⟩, hmem⟩ := hpre
      refine ⟨⟨hx0, hx1, hx2, hx3, hlay_new, hbs1, hbs2⟩, ?_⟩
      exact Satisfies.mono (Entails.of_eq (by ac_rfl)) hmem
    · simp only [Proofs.libsignal.Stage1X.rustReallocExternSpecWithStack, Proofs.libsignal.Stage1X.rustReallocSpecWithStack,
        Spec.withExternStackFromAlloc', rustReallocSpec, Stage1X.extHookStack,
        stackAt_externStack_split_allocHookStack'] at hpost ⊢
      exact Satisfies.mono (Entails.of_eq (by ac_rfl)) hpost
  shim := by
    rw [SP2Ext_fnAddr]
    exact hC.shim
  session_memmove := by
    rw [SP2Ext_fnAddr]
    exact hC.memmove

end Proofs.libsignal.Hooks2

/-! ## Deserialization Callee Bundle -/

namespace Proofs.libsignal.Hooks2

open Arm64 ProofLib CryptoGames CryptoGames.LibsignalSession
open CryptoVerification CryptoVerification.RustHeap
open CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchet.Prost
open CryptoVerification.LibsignalTripleRatchet.Prost.X
open CryptoVerification.LibsignalTripleRatchet.WireX
open CryptoVerification.E2E.Record
open Proofs.libsignal.Stage1X

/-- Assemble `DeserializeCalleesAtW img ext` from `Stage2ContractsMin img ext` and an explicit
`Prost.X.BytesMergeOkW img A0 ext`. -/
theorem deserializeCalleesAtW_of_stage2Min_bytes {img : Obj.Image}
    {ext : String → Option (State → State)}
    (hC : Stage2ContractsMin img ext)
    (hbytes : Prost.X.BytesMergeOkW img A0 ext) :
    DeserializeCalleesAtW img ext := by
  have hA : Stage1X.AllocContractsX img A0 ext := allocContractsX_of_stage2ContractsMin hC
  have hFrom : DecodeErrorFromOkW img A0 ext := decodeErrorFrom_okW hA
  have hSlow : DecodeVarintSlowOkW img A0 ext := decodeVarintSlow_okW hFrom
  have hSlice : DecodeVarintSliceOkW img A0 ext := decodeVarintSlice_okW hFrom
  exact ⟨hSlice, int32Merge_okW hFrom hSlow hSlice, hbytes, grow_one_72_ok_ext_x hA⟩

/-- Assemble `DeserializeCalleesAtW img ext` from `Stage2ContractsMin img ext`. -/
theorem deserializeCalleesAtW_of_stage2Min {img : Obj.Image}
    {ext : String → Option (State → State)}
    (hC : Stage2ContractsMin img ext) :
    DeserializeCalleesAtW img ext :=
  deserializeCalleesAtW_of_stage2Min_bytes hC
    (bytes_merge_okW hC.loads (allocContractsX_of_stage2ContractsMin hC) hC.memcpy)

end Proofs.libsignal.Hooks2

/-! ## Deserialization Loop Exit -/

namespace Proofs.libsignal.Hooks2

open Arm64 ProofLib ProofLib.ProgramReflection CryptoGames CryptoGames.LibsignalSession
open CryptoGames.LibsignalSessionApi CryptoVerification CryptoVerification.RustHeap
open CryptoVerification.LibsignalTripleRatchet CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.E2E.Record CryptoVerification.LibsignalProtoCodec
open CryptoVerification.E2E.Record.DeserializeSeed CryptoVerification.E2E.Record.DeserializeGeneral
open CryptoVerification.E2E.Record.Serialization (CanonRecord CanonSession)
open Proofs.libsignal.Hooks2 CryptoVerification.CodeLayout

set_option maxRecDepth 2000000
set_option maxHeartbeats 400000

attribute [local irreducible] Program.fetch Program.externAt?
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero

theorem memcpy_ok_extWMin {img : Obj.Image}
    {ext : String → Option (State → State)}
    (hC : Stage2ContractsMin img ext) :
    subroutine_ok (SP2Ext img.base ext)
      ((SP2Ext img.base ext).fnAddr recDeserializeName + bv% (ls_off% "memcpy" - ls_off% "<libsignal_protocol::state::session::SessionRecord>::deserialize"))
      ((sessionMemcpySpec deserCalleeStack).inImage img) := by
  have hk : libsignalSessionCode.fnOff recDeserializeName + num% (ls_off% "memcpy" - ls_off% "<libsignal_protocol::state::session::SessionRecord>::deserialize") =
      libsignalSessionCode.fnOff memcpyName := by
    fnoff_eq
  exact subroutine_ok_sessionMemcpySpec_mono (s2 := deserCalleeStack) (by decide) (by decide)
    (hC.memcpy_ok_at hk)

theorem deserLoopExitG_ok_extWMin
    (img : Obj.Image)
    (ext : String → Option (State → State))
    (hC : Stage2ContractsMin img ext)
    (x : DeserializeGenGhost) (R : SepProp) (s0 s : State) (hr : DeserializeScope x.r)
    (hs : DeserLoopGAtW img ext x R s0 (recFields x.r).length s) :
    DeserStepGAtW img ext x R s0 s (DeserRetGAt img x R s0) :=
  deserLoopExitG_ok_of_memcpy img ext (memcpy_ok_extWMin hC) x R s0 s hr hs

end Proofs.libsignal.Hooks2

/-! ## `SessionRecord::deserialize` (`A0`) -/

namespace Proofs.libsignal.Hooks2

open Arm64 ProofLib SepProp CryptoVerification
open CryptoGames CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open CryptoVerification.RustHeap
open CryptoVerification.LibsignalTripleRatchet CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.E2E.Record
open CryptoVerification.E2E.Record.DeserializeSeed
open CryptoVerification.E2E.Record.DeserializeGeneral
open CryptoVerification.E2E.Record.Serialization
open CryptoVerification.E2E.Bin

/-- Instantiate `DeserLeavesW img ext` from `Stage2ContractsMin img ext`. -/
theorem deserLeavesW_of_stage2Min (img : Obj.Image) (ext : String → Option (State → State))
    (hStage2 : Stage2ContractsMin img ext)
    (hCallees : DeserializeCalleesAtW img ext) :
    DeserLeavesW img ext := by
  exact
    { entry := fun x R s0 hpc hrun hpre hal =>
        DeserLoopEntryGExt.deserLoopEntryG_ok_atW img ext hCallees x R s0 hpc hrun hpre hal
      iter := fun hMF x R s0 k s hr hlt hs =>
        CryptoVerification.E2E.Record.DeserializeGeneral.Leaf.DeserLoopIterG.deserLoopIterG_ok_atW
          img ext hMF x R s0 k s hr hlt hs
      exit := fun x R s0 s hr hs =>
        deserLoopExitG_ok_extWMin img ext hStage2 x R s0 s hr hs }

/-- Exact `SessionRecord::deserialize` contract at `img.base + deserializeOff` from `Stage2ContractsMin`. -/
theorem deserializeExactAtX_ok_of_stage2Min {img : Obj.Image}
    {ext : String → Option (State → State)}
    (hStage2 : Stage2ContractsMin img ext) :
    subroutine_ok (contractProg img.base ext) (img.base + deserializeOff)
      (deserializeExactSpecAtX img) := by
  have hCallees := deserializeCalleesAtW_of_stage2Min hStage2
  exact deserializeExactAtX_ok_of_leaves
    (chainLeavesW_of_callees img ext hCallees)
    (mergeFieldLeavesW_of_callees img ext hStage2.loads hCallees)
    (deserLeavesW_of_stage2Min img ext hStage2 hCallees)

/-- `recordDeserializeOpenSpec A0` at `img.base + deserializeOff` from `Stage2ContractsMin`. -/
theorem recordDeserialize_ok_of_stage2Min {img : Obj.Image}
    {ext : String → Option (State → State)}
    (hStage2 : Stage2ContractsMin img ext) :
    subroutine_ok (contractProg img.base ext) (img.base + deserializeOff)
      ((recordDeserializeOpenSpec A0).inImage img) := by
  exact recordDeserializeOpen_of_exactX img (deserializeExactAtX_ok_of_stage2Min hStage2)

end Proofs.libsignal.Hooks2

/-! ## `Q`-Scope Deserialization Loop -/

namespace Symbolic.Swarm.TRREF.B3DeserQ

open Arm64 ProofLib ProofLib.ProgramReflection SepProp
open CryptoGames CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open CryptoVerification CryptoVerification.E2E.Record CryptoVerification.RustHeap
open CryptoVerification.LibsignalTripleRatchet CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalProtoCodec
open CryptoVerification.E2E.Record.DeserializeSeed CryptoVerification.E2E.Record.DeserializeGeneral
open CryptoVerification.E2E.Record.Serialization (OkAt CanonRecord CanonSession allocPanic)
open CryptoVerification.E2E.RecordX (DeserializeScopeP SessionScopeP)
open CryptoVerification.E2E.Bin (BinCanonSession recordDeserializeStack)
open CryptoVerification.E2E.Record.L1GX
open Symbolic.Swarm.TRREF.B3Defs
open Proofs.libsignal.Hooks2
open Proofs.libsignal.Hooks2.DeserLoopEntryGExt

set_option maxRecDepth 2000000
set_option maxHeartbeats 400000

attribute [local irreducible] Program.fetch Program.externAt?

theorem deserLoopExitQ_ok_extWMin (img : Obj.Image) (ext : String → Option (State → State))
    (hC : Stage2ContractsMin img ext) (x : DeserializeGenGhost) (R : SepProp) (s0 s : State)
    (hr : DeserializeScopeP_Q NonEmptyV1Q x.r) (hs : DeserLoopQAtW img ext x R s0 (recFieldsQ x.r).length s) :
    DeserStepQAtW img ext x R s0 s (DeserRetQAtW x R s0) :=
  deserLoopExitQ_ok_of_memcpy img ext (memcpy_ok_extWMin hC) x R s0 s hr hs

/-- Construct `DeserLeavesQW` from `DeserializeCalleesAtW` and `Stage2ContractsMin`. -/
theorem deserLeavesQW_of_contractsMin (img : Obj.Image) (ext : String → Option (State → State))
    (hCallees : DeserializeCalleesAtW img ext) (hC : Stage2ContractsMin img ext) : DeserLeavesQW img ext :=
  ⟨deserLoopEntryQ_ok_atW img ext hCallees, deserLoopIterQ_ok_atW img ext, deserLoopExitQ_ok_extWMin img ext hC⟩

end Symbolic.Swarm.TRREF.B3DeserQ

/-! ## `Q`-Scope `SessionRecord::deserialize` -/

namespace Symbolic.Swarm.TRREF.B3DeserQ

open Arm64 ProofLib SepProp
open CryptoGames CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open CryptoVerification CryptoVerification.E2E.Record CryptoVerification.RustHeap
open CryptoVerification.LibsignalTripleRatchet CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalProtoCodec
open CryptoVerification.E2E.Record.DeserializeSeed CryptoVerification.E2E.Record.DeserializeGeneral
open CryptoVerification.E2E.Record.Serialization (OkAt CanonRecord allocPanic)
open CryptoVerification.E2E.RecordX (DeserializeScopeP SessionScopeP)
open CryptoVerification.E2E.Bin (BinCanonSession deserializeOff)
open CryptoVerification.E2E.Record.L1GX
open Symbolic.Swarm.TRREF.B3Defs
open Proofs.libsignal.Hooks2

set_option maxRecDepth 200000
set_option maxHeartbeats 400000

/-- Exact `Q`-scope `SessionRecord::deserialize` contract at `img.base + deserializeOff`
from `Stage2ContractsMin img ext`. -/
theorem deserializeExactAtQ_ok_of_stage2Min {img : Obj.Image}
    {ext : String → Option (State → State)}
    (hStage2 : Stage2ContractsMin img ext) :
    subroutine_ok (contractProg img.base ext) (img.base + deserializeOff)
      (deserializeQExactSpecAtW img) := by
  have hCallees := deserializeCalleesAtW_of_stage2Min hStage2
  rw [← recDeserialize_fnAddr_eqX img.base ext]
  exact deserializeExactQW_ok img ext
    (deserLeavesQW_of_contractsMin img ext hCallees hStage2)
    (mergeFieldQW_ok img ext hStage2.loads hCallees)

/-- `(recordDeserializeOpenSpec_Q NonEmptyV1Q A0).inImage img` at `img.base + deserializeOff`
from `Stage2ContractsMin img ext`. -/
theorem recordDeserializeOpenQ_ok_of_stage2Min {img : Obj.Image}
    {ext : String → Option (State → State)}
    (hStage2 : Stage2ContractsMin img ext) :
    subroutine_ok (contractProg img.base ext) (img.base + deserializeOff)
      ((recordDeserializeOpenSpec_Q NonEmptyV1Q A0).inImage img) :=
  recordDeserializeOpen_of_exactQ img
    (deserializeExactAtQ_ok_of_stage2Min hStage2)

end Symbolic.Swarm.TRREF.B3DeserQ

/-! ## Serialization Contract Projection -/

namespace Proofs.libsignal.Hooks2

open Arm64 ProofLib SepProp
open CryptoGames CryptoGames.LibsignalSession
open CryptoVerification CryptoVerification.RustHeap
open CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.E2E.Record CryptoVerification.E2E.Record.Serialization
open Proofs.libsignal.Stage1X

set_option maxRecDepth 2000000 in
/-- `SerContractsX` at `HooksE.A0` from the stage-2 bundle. -/
theorem serContractsX_of_stage2ContractsMin {img : Obj.Image}
    {ext : String → Option (State → State)} (hC : Stage2ContractsMin img ext) :
    SerContractsX img CryptoVerification.E2E.HooksE.A0 ext where
  alloc := allocContractsX_of_stage2ContractsMin hC
  memcpy := hC.memcpy

end Proofs.libsignal.Hooks2

/-! ## Reduction of `Stage2ContractsA0` Headlines via `toMin` -/

namespace Proofs.libsignal.Hooks2

example {img : Arm64.Obj.Image} {ext : String → Option (Arm64.State → Arm64.State)}
    (hC : Stage2ContractsA0 img ext) :
    recordDeserialize_ok_of_stage2 hC = recordDeserialize_ok_of_stage2Min hC.toMin := rfl

example {img : Arm64.Obj.Image} {ext : String → Option (Arm64.State → Arm64.State)}
    (hC : Stage2ContractsA0 img ext) :
    deserializeExactAtX_ok_of_stage2 hC = deserializeExactAtX_ok_of_stage2Min hC.toMin := rfl

end Proofs.libsignal.Hooks2

namespace Symbolic.Swarm.TRREF.B3DeserQ

example {img : Arm64.Obj.Image} {ext : String → Option (Arm64.State → Arm64.State)}
    (hC : Proofs.libsignal.Hooks2.Stage2ContractsA0 img ext) :
    recordDeserializeOpenQ_ok_of_stage2 hC = recordDeserializeOpenQ_ok_of_stage2Min hC.toMin := rfl

example {img : Arm64.Obj.Image} {ext : String → Option (Arm64.State → Arm64.State)}
    (hC : Proofs.libsignal.Hooks2.Stage2ContractsA0 img ext) :
    deserializeExactAtQ_ok_of_stage2 hC = deserializeExactAtQ_ok_of_stage2Min hC.toMin := rfl

end Symbolic.Swarm.TRREF.B3DeserQ

/-! ## Generalization to Arbitrary `A : RustAlloc` -/

namespace Proofs.libsignal.Hooks2

open Arm64 ProofLib SepProp
open CryptoGames CryptoGames.LibsignalSession
open CryptoVerification CryptoVerification.RustHeap
open CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchet.Prost
open CryptoVerification.LibsignalTripleRatchet.Prost.X
open CryptoVerification.E2E CryptoVerification.E2E.HooksE
open CryptoVerification.E2E.Record CryptoVerification.E2E.Record.Serialization
open Proofs.libsignal.Stage1X

/-- Arbitrary-allocator (`A : RustAlloc`) generalization of `Stage2ContractsMin` on `SP2Ext`. -/
structure Stage2ContractsMinA (img : Obj.Image) (A : RustAlloc)
    (ext : String → Option (State → State)) : Prop where
  loads : Obj.Loads libsignalSessionImage img
  alloc : subroutine_ok (SP2Ext img.base ext) (img.base + stubOff allocName)
    (((rustAllocSpec A).withExternStackFromAlloc').inImage img)
  deallocLayout : subroutine_ok (SP2Ext img.base ext) (img.base + stubOff deallocName)
    (((rustDeallocLayoutSpec' A).withExternStackFromAlloc').inImage img)
  realloc : subroutine_ok (SP2Ext img.base ext) (img.base + stubOff reallocName)
    (((rustReallocSpec A).withExternStackFromAlloc').inImage img)
  shim : subroutine_ok (SP2Ext img.base ext) (img.base + stubOff shimName)
    ((sessionShimSpec.withHookStack CryptoVerification.LibsignalTripleRatchet.extHookStack).inImage img)
  memcpy : subroutine_ok (SP2Ext img.base ext) (img.base + stubOff memcpyName)
    ((sessionMemcpySpec CryptoVerification.LibsignalTripleRatchet.extHookStack).inImage img)
  memmove : subroutine_ok (SP2Ext img.base ext) (img.base + stubOff memmoveName)
    ((sessionMemmoveSpec CryptoVerification.LibsignalTripleRatchet.extHookStack).inImage img)

abbrev Stage2ContractsMinGen := Stage2ContractsMinA

theorem Stage2ContractsMin.toMinA {img : Obj.Image} {ext : String → Option (State → State)}
    (hC : Stage2ContractsMin img ext) : Stage2ContractsMinA img HooksE.A0 ext :=
  ⟨hC.loads, hC.alloc_A0, hC.deallocLayout_A0, hC.realloc_A0, hC.shim, hC.memcpy, hC.memmove⟩

theorem Stage2ContractsMinA.toA0 {img : Obj.Image} {ext : String → Option (State → State)}
    (hC : Stage2ContractsMinA img HooksE.A0 ext) : Stage2ContractsMin img ext :=
  ⟨hC.loads, hC.alloc, hC.deallocLayout, hC.realloc, hC.shim, hC.memcpy, hC.memmove⟩

theorem Stage2ContractsA0.toMinA {img : Obj.Image} {ext : String → Option (State → State)}
    (hC : Stage2ContractsA0 img ext) : Stage2ContractsMinA img HooksE.A0 ext :=
  hC.toMin.toMinA

/-- Stacked `AllocContractsX` (`extHookStack = 16384`, lifted from `memHookStack = 4096`)
minimal stage-2 contract bundle for arbitrary `A : RustAlloc`. -/
structure Stage2ContractsMinExt (img : Obj.Image) (A : RustAlloc)
    (ext : String → Option (State → State)) : Prop where
  loads : Obj.Loads libsignalSessionImage img
  alloc : Proofs.libsignal.Stage1X.AllocContractsX img A ext
  memcpy : subroutine_ok (SP2Ext img.base ext) (img.base + stubOff memcpyName)
    ((sessionMemcpySpec CryptoVerification.LibsignalTripleRatchet.extHookStack).inImage img)

section GenAHelpers

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero

theorem Stage2ContractsMinA.memcpy_ok_at {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)} {name : String} {k : Nat}
    (hC : Stage2ContractsMinA img A ext)
    (hk : libsignalSessionCode.fnOff name + k = libsignalSessionCode.fnOff memcpyName) :
    subroutine_ok (SP2Ext img.base ext) ((SP2Ext img.base ext).fnAddr name + BitVec.ofNat 64 k)
      ((sessionMemcpySpec CryptoVerification.LibsignalTripleRatchet.extHookStack).inImage img) :=
  sub_ok_at_caller hk hC.memcpy

theorem Stage2ContractsMinExt.memcpy_ok_at {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)} {name : String} {k : Nat}
    (hC : Stage2ContractsMinExt img A ext)
    (hk : libsignalSessionCode.fnOff name + k = libsignalSessionCode.fnOff memcpyName) :
    subroutine_ok (SP2Ext img.base ext) ((SP2Ext img.base ext).fnAddr name + BitVec.ofNat 64 k)
      ((sessionMemcpySpec CryptoVerification.LibsignalTripleRatchet.extHookStack).inImage img) :=
  sub_ok_at_caller hk hC.memcpy

set_option maxRecDepth 2000000 in
set_option maxHeartbeats 800000 in
/-- `Stage1X.AllocContractsX` for arbitrary `A : RustAlloc` from `Stage2ContractsMinA`. -/
theorem allocContractsX_of_stage2ContractsMinA {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)}
    (hC : Stage2ContractsMinA img A ext) :
    Proofs.libsignal.Stage1X.AllocContractsX img A ext where
  alloc := by
    rw [SP2Ext_fnAddr]
    refine subroutine_ok_inImage_map' hC.alloc (fun ⟨size, align⟩ R s0 hpre => ?_)
      (fun _ _ _ _ _ hp => not_satisfies_false_sepConj hp)
      (fun _ _ _ _ _ _ he => not_satisfies_false_sepConj he)
    refine ⟨(size, align), R, ?_, fun sf hpost => ?_⟩
    · simp only [Proofs.libsignal.Stage1X.rustAllocSpecWithStack, Spec.withExternStackFromAlloc',
        rustAllocSpec, Stage1X.extHookStack, stackAt_externStack_split_allocHookStack'] at hpre ⊢
      exact Satisfies.mono (Entails.of_eq (by ac_rfl)) hpre
    · simp only [Proofs.libsignal.Stage1X.rustAllocSpecWithStack, Spec.withExternStackFromAlloc',
        rustAllocSpec, Stage1X.extHookStack, stackAt_externStack_split_allocHookStack'] at hpost ⊢
      exact Satisfies.mono (Entails.of_eq (by ac_rfl)) hpost
  dealloc := by
    rw [SP2Ext_fnAddr]
    refine subroutine_ok_inImage_map' hC.deallocLayout (fun ⟨p, size, align⟩ R s0 hpre => ?_)
      (fun _ _ _ _ _ hp => not_satisfies_false_sepConj hp)
      (fun _ _ _ _ _ _ he => not_satisfies_false_sepConj he)
    refine ⟨(p, size, align), R, ?_, fun sf hpost => ?_⟩
    · simp only [Proofs.libsignal.Stage1X.rustDeallocExternSpecWithStack,
        Spec.withExternStackFromAlloc', rustDeallocLayoutSpec', rustDeallocSpec,
        Stage1X.extHookStack, stackAt_externStack_split_allocHookStack',
        sepConj_assoc, satisfies_pure_sepConj] at hpre ⊢
      obtain ⟨⟨hx0, hx1, hx2, hlay⟩, hmem⟩ := hpre
      refine ⟨hlay, ⟨hx0, hx1, hx2⟩, ?_⟩
      exact Satisfies.mono (Entails.of_eq (by ac_rfl)) hmem
    · simp only [Proofs.libsignal.Stage1X.rustDeallocExternSpecWithStack,
        Spec.withExternStackFromAlloc', rustDeallocLayoutSpec', rustDeallocSpec,
        Stage1X.extHookStack, stackAt_externStack_split_allocHookStack'] at hpost ⊢
      exact Satisfies.mono (Entails.of_eq (by ac_rfl)) hpost
  realloc := by
    rw [SP2Ext_fnAddr]
    refine subroutine_ok_inImage_map' hC.realloc (fun ⟨p, old_size, align, new_size, bs⟩ R s0 hpre => ?_)
      (fun _ _ _ _ _ hp => not_satisfies_false_sepConj hp)
      (fun _ _ _ _ _ _ he => not_satisfies_false_sepConj he)
    refine ⟨(p, old_size, align, new_size, bs), R, ?_, fun sf hpost => ?_⟩
    · simp only [Proofs.libsignal.Stage1X.rustReallocExternSpecWithStack,
        Spec.withExternStackFromAlloc', rustReallocSpec, Stage1X.extHookStack,
        stackAt_externStack_split_allocHookStack', sepConj_assoc, satisfies_pure_sepConj] at hpre ⊢
      obtain ⟨⟨hx0, hx1, hx2, hx3, hbs1, hbs2, _hlay_old, hlay_new⟩, hmem⟩ := hpre
      refine ⟨⟨hx0, hx1, hx2, hx3, hlay_new, hbs1, hbs2⟩, ?_⟩
      exact Satisfies.mono (Entails.of_eq (by ac_rfl)) hmem
    · simp only [Proofs.libsignal.Stage1X.rustReallocExternSpecWithStack,
        Proofs.libsignal.Stage1X.rustReallocSpecWithStack,
        Spec.withExternStackFromAlloc', rustReallocSpec, Stage1X.extHookStack,
        stackAt_externStack_split_allocHookStack'] at hpost ⊢
      exact Satisfies.mono (Entails.of_eq (by ac_rfl)) hpost
  shim := by
    rw [SP2Ext_fnAddr]
    exact hC.shim
  session_memmove := by
    rw [SP2Ext_fnAddr]
    exact hC.memmove

/-- Bridge stacked `LibsignalTripleRatchet.AllocContractsX img A ext` (`memHookStack = 4096` lifted
to `extHookStack = 16384`) to `Stage1X.AllocContractsX img A ext` for arbitrary `A : RustAlloc`. -/
theorem allocContractsX_of_trAllocContractsX_min {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)}
    (hA : CryptoVerification.LibsignalTripleRatchet.AllocContractsX img A ext) :
    Proofs.libsignal.Stage1X.AllocContractsX img A ext where
  alloc := by
    refine subroutine_ok_inImage_map' hA.alloc fun ⟨size, align⟩ R s0 hpre => ?_
    refine ⟨(size, align), R, ?_, fun sf hpost => ?_⟩
    · simp only [CryptoVerification.LibsignalTripleRatchet.rustAllocSpecWithStack,
        Proofs.libsignal.Stage1X.rustAllocSpecWithStack] at hpre ⊢
      exact hpre
    · simp only [CryptoVerification.LibsignalTripleRatchet.rustAllocSpecWithStack,
        Proofs.libsignal.Stage1X.rustAllocSpecWithStack] at hpost ⊢
      exact Satisfies.mono (Entails.of_eq (by ac_rfl)) hpost
  dealloc := by
    refine subroutine_ok_inImage_map' hA.dealloc fun ⟨p, size, align⟩ R s0 hpre => ?_
    refine ⟨(p, size, align), R, ?_, fun sf hpost => ?_⟩
    · simp only [CryptoVerification.LibsignalTripleRatchet.rustDeallocExternSpecWithStack,
        Proofs.libsignal.Stage1X.rustDeallocExternSpecWithStack] at hpre ⊢
      exact Satisfies.mono (Entails.of_eq (by ac_rfl)) hpre
    · simp only [CryptoVerification.LibsignalTripleRatchet.rustDeallocExternSpecWithStack,
        Proofs.libsignal.Stage1X.rustDeallocExternSpecWithStack] at hpost ⊢
      exact hpost
  realloc := by
    refine subroutine_ok_inImage_map' hA.realloc
      fun ⟨p, old_size, align, new_size, bs⟩ R s0 hpre => ?_
    refine ⟨(p, old_size, align, new_size, bs), R, ?_, fun sf hpost => ?_⟩
    · simp only [CryptoVerification.LibsignalTripleRatchet.rustReallocExternSpecWithStack,
        Proofs.libsignal.Stage1X.rustReallocExternSpecWithStack,
        sepConj_assoc, satisfies_pure_sepConj] at hpre ⊢
      obtain ⟨⟨hx0, hx1, hx2, hx3, hbs1, hbs2, hlay_old, hlay_new⟩, hmem⟩ := hpre
      exact ⟨⟨hx0, hx1, hx2, hx3, hlay_old, hlay_new, hbs1, hbs2⟩,
        Satisfies.mono (Entails.of_eq (by ac_rfl)) hmem⟩
    · simp only [CryptoVerification.LibsignalTripleRatchet.rustReallocExternSpecWithStack,
        CryptoVerification.LibsignalTripleRatchet.rustReallocSpecWithStack,
        Proofs.libsignal.Stage1X.rustReallocExternSpecWithStack,
        Proofs.libsignal.Stage1X.rustReallocSpecWithStack] at hpost ⊢
      exact Satisfies.mono (Entails.of_eq (by ac_rfl)) hpost
  shim := hA.shim CryptoVerification.LibsignalTripleRatchet.extHookStack (Nat.le_refl _) (by decide)
  session_memmove :=
    hA.session_memmove CryptoVerification.LibsignalTripleRatchet.extHookStack
      (Nat.le_refl _) (by decide)

theorem Stage2ContractsMinA.toExt {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)} (hC : Stage2ContractsMinA img A ext) :
    Stage2ContractsMinExt img A ext :=
  ⟨hC.loads, allocContractsX_of_stage2ContractsMinA hC, hC.memcpy⟩

theorem Stage2ContractsMin.toExt {img : Obj.Image} {ext : String → Option (State → State)}
    (hC : Stage2ContractsMin img ext) : Stage2ContractsMinExt img HooksE.A0 ext :=
  hC.toMinA.toExt

/-- Construct `Stage2ContractsMinExt img A ext` from `Obj.Loads` and stacked
`LibsignalTripleRatchet.AllocContractsX img A ext`. -/
theorem Stage2ContractsMinExt.of_trAllocContractsX {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)}
    (himg : Obj.Loads libsignalSessionImage img)
    (hA : CryptoVerification.LibsignalTripleRatchet.AllocContractsX img A ext) :
    Stage2ContractsMinExt img A ext where
  loads := himg
  alloc := allocContractsX_of_trAllocContractsX_min hA
  memcpy := by
    rw [← SP2Ext_fnAddr img.base ext memcpyName]
    exact hA.session_memcpy CryptoVerification.LibsignalTripleRatchet.extHookStack
      (Nat.le_refl _) (by decide)

/-- Construct `Stage2ContractsMinA img A ext` from raw `4096`-stack `alloc`/`dealloc`/`realloc`
stub contracts (`AllocHooks A`) and stacked `LibsignalTripleRatchet.AllocContractsX img A ext`. -/
theorem Stage2ContractsMinA.of_rawAlloc_and_trAllocContractsX {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)}
    (himg : Obj.Loads libsignalSessionImage img)
    (hAlloc : subroutine_ok (SP2Ext img.base ext) ((SP2Ext img.base ext).fnAddr allocName)
      (rustAllocSpec A))
    (hDealloc : subroutine_ok (SP2Ext img.base ext) ((SP2Ext img.base ext).fnAddr deallocName)
      (rustDeallocSpec A))
    (hRealloc : subroutine_ok (SP2Ext img.base ext) ((SP2Ext img.base ext).fnAddr reallocName)
      (rustReallocSpec A))
    (hA : CryptoVerification.LibsignalTripleRatchet.AllocContractsX img A ext) :
    Stage2ContractsMinA img A ext where
  loads := himg
  alloc := by
    rw [← SP2Ext_fnAddr img.base ext allocName]
    apply subroutine_ok_inImage_of_subroutine_ok img
    refine subroutine_ok_map_panic hAlloc fun x R s0 hpre => ?_
    refine ⟨x, memRegion (s0.sp - 16384#64) 12288 ∗ R, ?_, fun sf hpost => ?_,
      fun _ hp => False.elim (not_satisfies_false_sepConj hp)⟩
    · simpa only [Spec.withExternStackFromAlloc', sepConj_assoc] using hpre
    · simpa only [Spec.withExternStackFromAlloc', sepConj_assoc] using hpost
  deallocLayout := by
    rw [← SP2Ext_fnAddr img.base ext deallocName]
    apply subroutine_ok_inImage_of_subroutine_ok img
    refine subroutine_ok_map_panic hDealloc fun ⟨p, size, align⟩ R s0 hpre => ?_
    refine ⟨(p, size, align), memRegion (s0.sp - 16384#64) 12288 ∗ R, ?_,
      fun sf hpost => ?_, fun _ hp => False.elim (not_satisfies_false_sepConj hp)⟩
    · simp only [Spec.withExternStackFromAlloc', rustDeallocLayoutSpec',
        sepConj_assoc, satisfies_pure_sepConj] at hpre ⊢
      exact hpre.2
    · simpa only [Spec.withExternStackFromAlloc', rustDeallocLayoutSpec', sepConj_assoc] using hpost
  realloc := by
    rw [← SP2Ext_fnAddr img.base ext reallocName]
    apply subroutine_ok_inImage_of_subroutine_ok img
    refine subroutine_ok_map_panic hRealloc fun x R s0 hpre => ?_
    refine ⟨x, memRegion (s0.sp - 16384#64) 12288 ∗ R, ?_, fun sf hpost => ?_,
      fun _ hp => False.elim (not_satisfies_false_sepConj hp)⟩
    · simpa only [Spec.withExternStackFromAlloc', sepConj_assoc] using hpre
    · simpa only [Spec.withExternStackFromAlloc', sepConj_assoc] using hpost
  shim := by
    rw [← SP2Ext_fnAddr img.base ext shimName]
    exact hA.shim CryptoVerification.LibsignalTripleRatchet.extHookStack
      (Nat.le_refl _) (by decide)
  memcpy := by
    rw [← SP2Ext_fnAddr img.base ext memcpyName]
    exact hA.session_memcpy CryptoVerification.LibsignalTripleRatchet.extHookStack
      (Nat.le_refl _) (by decide)
  memmove := by
    rw [← SP2Ext_fnAddr img.base ext memmoveName]
    exact hA.session_memmove CryptoVerification.LibsignalTripleRatchet.extHookStack
      (Nat.le_refl _) (by decide)

set_option maxRecDepth 2000000 in
/-- `SerContractsX` for arbitrary `A : RustAlloc` from `Stage2ContractsMinExt`. -/
theorem serContractsX_of_stage2ContractsMinExt {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)} (hC : Stage2ContractsMinExt img A ext) :
    SerContractsX img A ext where
  alloc := hC.alloc
  memcpy := hC.memcpy

set_option maxRecDepth 2000000 in
/-- `SerContractsX` for arbitrary `A : RustAlloc` from `Stage2ContractsMinA`. -/
theorem serContractsX_of_stage2ContractsMinA {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)} (hC : Stage2ContractsMinA img A ext) :
    SerContractsX img A ext :=
  serContractsX_of_stage2ContractsMinExt hC.toExt

/-- `SerContractsX` for arbitrary `A : RustAlloc` directly from `Obj.Loads` and stacked
`LibsignalTripleRatchet.AllocContractsX`. -/
theorem serContractsX_of_trAllocContractsX_min {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)}
    (himg : Obj.Loads libsignalSessionImage img)
    (hA : CryptoVerification.LibsignalTripleRatchet.AllocContractsX img A ext) :
    SerContractsX img A ext :=
  serContractsX_of_stage2ContractsMinExt (Stage2ContractsMinExt.of_trAllocContractsX himg hA)

end GenAHelpers

end Proofs.libsignal.Hooks2

namespace Proofs.libsignal.Hooks2

open Arm64 ProofLib CryptoGames CryptoGames.LibsignalSession
open CryptoVerification CryptoVerification.RustHeap
open CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchet.Prost
open CryptoVerification.LibsignalTripleRatchet.Prost.X
open CryptoVerification.LibsignalTripleRatchet.WireX
open CryptoVerification.E2E.Record
open Proofs.libsignal.Stage1X

/-- Arbitrary-allocator (`A : RustAlloc`) generalization of `DeserializeCalleesAtW`
(definitionally equal to `Proofs.libsignal.Hooks2.DeserializeCalleesAtWA`). -/
def DeserializeCalleesAtMinA (img : Obj.Image) (A : RustAlloc)
    (ext : String → Option (State → State)) : Prop :=
  Prost.X.DecodeVarintSliceOkW img A ext ∧
    Prost.X.Int32MergeOkW img A ext ∧
    Prost.X.BytesMergeOkW img A ext ∧
    Stage1X.GrowOneChainOkX img A ext

theorem deserializeCalleesAtMinA_A0_eq (img : Obj.Image) (ext : String → Option (State → State)) :
    DeserializeCalleesAtMinA img A0 ext = DeserializeCalleesAtW img ext := rfl

theorem deserializeCalleesAtMinA_of_stage2MinExt_bytes {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)}
    (hC : Stage2ContractsMinExt img A ext)
    (hbytes : Prost.X.BytesMergeOkW img A ext) :
    DeserializeCalleesAtMinA img A ext := by
  have hFrom : DecodeErrorFromOkW img A ext := decodeErrorFrom_okW hC.alloc
  have hSlow : DecodeVarintSlowOkW img A ext := decodeVarintSlow_okW hFrom
  have hSlice : DecodeVarintSliceOkW img A ext := decodeVarintSlice_okW hFrom
  exact ⟨hSlice, int32Merge_okW hFrom hSlow hSlice, hbytes, grow_one_72_ok_ext_x hC.alloc⟩

theorem deserializeCalleesAtMinA_of_stage2MinExt {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)}
    (hC : Stage2ContractsMinExt img A ext) :
    DeserializeCalleesAtMinA img A ext :=
  deserializeCalleesAtMinA_of_stage2MinExt_bytes hC
    (bytes_merge_okW hC.loads hC.alloc hC.memcpy)

theorem deserializeCalleesAtMinA_of_stage2MinA_bytes {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)}
    (hC : Stage2ContractsMinA img A ext)
    (hbytes : Prost.X.BytesMergeOkW img A ext) :
    DeserializeCalleesAtMinA img A ext :=
  deserializeCalleesAtMinA_of_stage2MinExt_bytes hC.toExt hbytes

theorem deserializeCalleesAtMinA_of_stage2MinA {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)}
    (hC : Stage2ContractsMinA img A ext) :
    DeserializeCalleesAtMinA img A ext :=
  deserializeCalleesAtMinA_of_stage2MinExt hC.toExt

theorem deserializeCalleesAtMinA_of_trAllocContractsX {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)}
    (himg : Obj.Loads libsignalSessionImage img)
    (hA : CryptoVerification.LibsignalTripleRatchet.AllocContractsX img A ext) :
    DeserializeCalleesAtMinA img A ext :=
  deserializeCalleesAtMinA_of_stage2MinExt (Stage2ContractsMinExt.of_trAllocContractsX himg hA)

end Proofs.libsignal.Hooks2

namespace Proofs.libsignal.Hooks2

open Arm64 ProofLib ProofLib.ProgramReflection CryptoGames CryptoGames.LibsignalSession
open CryptoGames.LibsignalSessionApi CryptoVerification CryptoVerification.RustHeap
open CryptoVerification.LibsignalTripleRatchet CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.E2E.Record CryptoVerification.LibsignalProtoCodec
open CryptoVerification.E2E.Record.DeserializeSeed CryptoVerification.E2E.Record.DeserializeGeneral
open CryptoVerification.E2E.Record.Serialization (CanonRecord CanonSession)
open Proofs.libsignal.Hooks2 CryptoVerification.CodeLayout

set_option maxRecDepth 2000000
set_option maxHeartbeats 400000

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero

theorem memcpy_ok_extWMinExt {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)}
    (hC : Stage2ContractsMinExt img A ext) :
    subroutine_ok (SP2Ext img.base ext)
      ((SP2Ext img.base ext).fnAddr recDeserializeName +
        bv% (ls_off% "memcpy" - ls_off% "<libsignal_protocol::state::session::SessionRecord>::deserialize"))
      ((sessionMemcpySpec deserCalleeStack).inImage img) := by
  have hk : libsignalSessionCode.fnOff recDeserializeName +
      num% (ls_off% "memcpy" - ls_off% "<libsignal_protocol::state::session::SessionRecord>::deserialize") =
      libsignalSessionCode.fnOff memcpyName := by
    fnoff_eq
  exact subroutine_ok_sessionMemcpySpec_mono (s2 := deserCalleeStack) (by decide) (by decide)
    (hC.memcpy_ok_at hk)

theorem memcpy_ok_extWMinA {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)}
    (hC : Stage2ContractsMinA img A ext) :
    subroutine_ok (SP2Ext img.base ext)
      ((SP2Ext img.base ext).fnAddr recDeserializeName +
        bv% (ls_off% "memcpy" - ls_off% "<libsignal_protocol::state::session::SessionRecord>::deserialize"))
      ((sessionMemcpySpec deserCalleeStack).inImage img) :=
  memcpy_ok_extWMinExt hC.toExt

end Proofs.libsignal.Hooks2

/-! ## Relocatable `[LibsignalPlacement]` Proofs -/

namespace Proofs.libsignal.Hooks2

open Arm64 Arm64.Obj ProofLib SepProp CryptoVerification
open CryptoGames CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open CryptoVerification.RustHeap
open CryptoVerification.LibsignalTripleRatchet CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.E2E CryptoVerification.E2E.HooksE
open CryptoVerification.E2E.Record CryptoVerification.E2E.Record.Placed
open CryptoVerification.E2E.Bin

theorem L1_SessionRecordMin_Deserialize_Placed : True := trivial

/-- Minimal relocatable `[LibsignalPlacement]` contract bundle for `SessionRecord::deserialize`:
`Stage1X.AllocContractsPlaced HooksE.A0 H` plus `memcpy` at `extHookStack`. -/
structure Stage2ContractsMinPlaced [LibsignalPlacement] (H : LibsignalHooks) : Prop where
  alloc : Stage1X.AllocContractsPlaced HooksE.A0 H
  memcpy : ∀ {callerProg : Program} {callerBlk : Nat} [IsLsBlockProg callerProg callerBlk H],
    subroutine_ok callerProg (lsρ "memcpy")
      (withLsCl lsmpl (sessionMemcpySpec CryptoVerification.LibsignalTripleRatchet.extHookStack))

/-- Forget the unused fields of `Stage2ContractsA0Placed H`. -/
theorem Stage2ContractsA0Placed.toMin [LibsignalPlacement] {H : LibsignalHooks}
    (hC : Stage2ContractsA0Placed H) : Stage2ContractsMinPlaced H :=
  ⟨allocContractsPlaced_of_stage2ContractsA0Placed hC, hC.memcpy⟩

set_option maxRecDepth 200000 in
/-- Construct `Stage2ContractsMinPlaced H` from `HookSat H` single-step hooks. -/
theorem Stage2ContractsMinPlaced.of_hooks [LibsignalPlacement] {H : LibsignalHooks}
    (halloc : HookSat H CryptoVerification.lsRustAllocSym (rustAllocSpec HooksE.A0))
    (hdealloc : HookSat H lsRustDeallocSym (rustDeallocSpec HooksE.A0))
    (hrealloc : HookSat H lsRustReallocSym (rustReallocSpec HooksE.A0))
    (hshim : HookSat H CryptoVerification.lsRustNoAllocShimSym sessionShimSpec)
    (hmemcpy : HookSat H "memcpy"
      (sessionMemcpySpec CryptoVerification.LibsignalTripleRatchet.extHookStack))
    (hmemmove : HookSat H "memmove" (sessionMemmoveSpec Stage1X.extHookStack))
    (hpan_err : H CryptoVerification.lsHandleErrorSym = some Rust.panicked)
    (hpan_alloc : H "_RNvNtCs69KKACWg7bl_5alloc5alloc18handle_alloc_error" = some Rust.panicked) :
    Stage2ContractsMinPlaced H where
  alloc := Stage1X.AllocContractsPlaced.of_hooks
    halloc hdealloc hrealloc hshim hmemmove hpan_err hpan_alloc
  memcpy := ls_subroutine_ok_cl_of_plain_prog (ls_hook_ok_of_caller hmemcpy)

/-- `SerContractsXPlaced` at `HooksE.A0` from `Stage2ContractsMinPlaced H`. -/
theorem serContractsXPlaced_of_stage2ContractsMinPlaced [LibsignalPlacement] {H : LibsignalHooks}
    (hC : Stage2ContractsMinPlaced H) :
    SerContractsXPlaced HooksE.A0 H :=
  ⟨hC.alloc, hC.memcpy⟩

/-- Relocatable exact `SessionRecord::deserialize` contract on `lsProg_46 H` from
`Stage2ContractsMinPlaced H`. -/
theorem deserializeExact_placed_ok_of_stage2Min [LibsignalPlacement] {H : LibsignalHooks}
    (hStage2 : Stage2ContractsMinPlaced H) :
    subroutine_ok (lsProg_46 H) (blkPl_46).base deserializeExactPlacedSpecX :=
  deserializeExactPlacedX_ok_of_alloc hStage2.alloc hStage2.memcpy

abbrev deserializeExactPlacedX_ok_of_stage2Min := @deserializeExact_placed_ok_of_stage2Min

/-- Relocatable `recordDeserializeOpenSpec A0` on `lsProg_46 H` from `Stage2ContractsMinPlaced H`. -/
theorem recordDeserialize_placed_ok_of_stage2Min [LibsignalPlacement] {H : LibsignalHooks}
    (hStage2 : Stage2ContractsMinPlaced H) :
    subroutine_ok (lsProg_46 H) (blkPl_46).base
      (LibsignalTripleRatchet.withLsCodeRoLoaded lsmpl (recordDeserializeOpenSpec HooksE.A0)) :=
  recordDeserialize_placed_ok_of_alloc hStage2.alloc hStage2.memcpy

/-- Relocatable `deserializeGenPlacedSpec` on `lsProg_46 H` from `Stage2ContractsMinPlaced H`. -/
theorem deserializeGen_placed_ok_of_stage2Min [LibsignalPlacement] {H : LibsignalHooks}
    (hStage2 : Stage2ContractsMinPlaced H) :
    subroutine_ok (lsProg_46 H) (blkPl_46).base deserializeGenPlacedSpec :=
  deserializeGen_placed_ok_of_alloc hStage2.alloc hStage2.memcpy

end Proofs.libsignal.Hooks2

namespace Symbolic.Swarm.TRREF.B3DeserQ

open Arm64 Arm64.Obj ProofLib
open CryptoVerification CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.E2E.Record CryptoVerification.E2E.Record.Placed
open Symbolic.Swarm.TRREF.B3Defs
open Proofs.libsignal.Hooks2

/-- Relocatable exact `Q`-scope `SessionRecord::deserialize` contract (`deserializeQExactPlacedSpecW`)
on `lsProg_46 H` from `Stage2ContractsMinPlaced H`. -/
theorem deserializeExactQ_placed_ok_of_stage2Min [LibsignalPlacement] {H : LibsignalHooks}
    (hStage2 : Stage2ContractsMinPlaced H) :
    subroutine_ok (lsProg_46 H) (blkPl_46).base deserializeQExactPlacedSpecW :=
  deserializeExactAtQ_placed_ok_of_alloc hStage2.alloc hStage2.memcpy

abbrev deserializeExactAtQ_placed_ok_of_stage2Min := @deserializeExactQ_placed_ok_of_stage2Min

/-- Relocatable general `Q`-scope `SessionRecord::deserialize` contract (`deserializeQPlacedSpecW`)
on `lsProg_46 H` from `Stage2ContractsMinPlaced H`. -/
theorem deserializeBodyQ_placed_ok_of_stage2Min [LibsignalPlacement] {H : LibsignalHooks}
    (hStage2 : Stage2ContractsMinPlaced H) :
    subroutine_ok (lsProg_46 H) (blkPl_46).base deserializeQPlacedSpecW :=
  deserializeBodyQ_placed_ok_of_alloc hStage2.alloc hStage2.memcpy

/-- Relocatable `withLsCodeRoLoaded lsmpl (recordDeserializeOpenSpec_Q NonEmptyV1Q A0)` on `lsProg_46 H`
from `Stage2ContractsMinPlaced H`. -/
theorem recordDeserializeOpenQ_placed_ok_of_stage2Min [LibsignalPlacement] {H : LibsignalHooks}
    (hStage2 : Stage2ContractsMinPlaced H) :
    subroutine_ok (lsProg_46 H) (blkPl_46).base
      (LibsignalTripleRatchet.withLsCodeRoLoaded lsmpl (recordDeserializeOpenSpec_Q NonEmptyV1Q A0)) :=
  recordDeserializeOpenQ_placed_ok_of_alloc hStage2.alloc hStage2.memcpy

end Symbolic.Swarm.TRREF.B3DeserQ
