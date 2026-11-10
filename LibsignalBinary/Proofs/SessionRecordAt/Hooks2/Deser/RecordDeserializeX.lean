/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SessionRecordAt.Hooks2.Deser.DeserAssemblyW
public import LibsignalBinary.Proofs.SessionRecordAt.Hooks2.Deser.DeserTransportX
public import LibsignalBinary.Proofs.SessionRecordAt.Hooks2.Adapters
import LibsignalBinary.Proofs.E2E.Record.DeserializeGeneral.DeserializeLeaves
import LibsignalBinary.Proofs.SessionRecordAt.Hooks2.ChainEntryGExt
import LibsignalBinary.Proofs.SessionRecordAt.Hooks2.ChainExitGExt
import LibsignalBinary.Proofs.SessionRecordAt.Hooks2.ChainKeyFieldGExt
import LibsignalBinary.Proofs.SessionRecordAt.Hooks2.ChainMessageKeysGExt
import LibsignalBinary.Proofs.SessionRecordAt.Hooks2.ChainSenderRatchetKeyGExt
import LibsignalBinary.Proofs.SessionRecordAt.Hooks2.Deser.DeserCalleesX
import LibsignalBinary.Proofs.SessionRecordAt.Hooks2.DeserLoopEntryGExt
import LibsignalBinary.Proofs.SessionRecordAt.Hooks2.DeserLoopExitGExt
import LibsignalBinary.Proofs.SessionRecordAt.Hooks2.DeserLoopIterGExt
import LibsignalBinary.Proofs.SessionRecordAt.Hooks2.DoReserveExt
import LibsignalBinary.Proofs.SessionRecordAt.Hooks2.MergeFieldGenIdentityRootKeysExt
import LibsignalBinary.Proofs.SessionRecordAt.Hooks2.MergeFieldGenPendingPreKeyExt
import LibsignalBinary.Proofs.SessionRecordAt.Hooks2.MergeFieldGenPreviousCounterExt
import LibsignalBinary.Proofs.SessionRecordAt.Hooks2.MergeFieldGenReceiverChainsExt
import LibsignalBinary.Proofs.SessionRecordAt.Hooks2.MergeFieldGenSenderChainExt
import LibsignalBinary.Proofs.SessionRecordAt.Hooks2.MergeFieldGenSessionVersionExt

@[expose] public section

set_option autoImplicit false

/-!
# Root `SessionRecord::deserialize` Assembly

Instantiates `DeserLeaves`, `ChainLeaves`, and `MergeFieldLeaves` from their leaf proofs and
combines `DeserAssemblyW` with `DeserTransportX` to establish `recordDeserializeOpenSpec` on
`contractProg img.base ext` and under `[LibsignalPlacement]` (Block `46`).
-/

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

theorem L1_RecordDeserializeX : True := trivial

/-- `(SP2Ext b ext).fnAddr recDeserializeName` equals `b + deserializeOff`. -/
theorem recDeserialize_fnAddr_eqX (b : BitVec 64) (ext : String → Option (State → State)) :
    (SP2Ext b ext).fnAddr recDeserializeName = b + deserializeOff := by
  simp only [SP2Ext, contractProg, Program.fnAddr_rebase, deserialize_fnOff]

/-- Instantiate `DeserLeavesW img ext` from the outer deserialization leaf proofs. -/
theorem deserLeavesW_of_stage2 (img : Obj.Image) (ext : String → Option (State → State))
    (hStage2 : Stage2ContractsA0 img ext)
    (hCallees : DeserializeCalleesAtW img ext) :
    DeserLeavesW img ext := by
  exact
    { entry := fun x R s0 hpc hrun hpre hal =>
        DeserLoopEntryGExt.deserLoopEntryG_ok_atW img ext hCallees x R s0 hpc hrun hpre hal
      iter := fun hMF x R s0 k s hr hlt hs =>
        CryptoVerification.E2E.Record.DeserializeGeneral.Leaf.DeserLoopIterG.deserLoopIterG_ok_atW
          img ext hMF x R s0 k s hr hlt hs
      exit := fun x R s0 s hr hs =>
        deserLoopExitG_ok_extW img ext hStage2 x R s0 s hr hs }

/-- Instantiate `ChainLeavesW img ext` from the `Chain` leaf proofs. -/
theorem chainLeavesW_of_callees (img : Obj.Image) (ext : String → Option (State → State))
    (hCallees : DeserializeCalleesAtW img ext) :
    ChainLeavesW img ext := by
  exact
    { entry := fun x R s0 hpc hrun hpre hal =>
        CryptoVerification.E2E.Record.DeserializeGeneral.Leaf.ChainEntryG.chainEntryG_ok_impl_atW
          img hCallees x R s0 hpc hrun hpre hal
      srk := fun x R s0 k s hk htag hs =>
        CryptoVerification.E2E.Record.DeserializeGeneral.Leaf.ChainSenderRatchetKeyG.chainSenderRatchetKeyG_ok_atW
          img hCallees x R s0 k s hk htag hs
      ck := fun x R s0 k s hk htag hs =>
        CryptoVerification.E2E.Record.DeserializeGeneral.Leaf.ChainKeyFieldG.chainKeyFieldG_ok_atW
          img hCallees x R s0 k s hk htag hs
      keys := fun x R s0 k s hk htag hs =>
        CryptoVerification.E2E.Record.DeserializeGeneral.Leaf.ChainMessageKeysG.chainMessageKeysG_ok_atW
          img hCallees x R s0 k s hk htag hs
      exit := fun x R s0 s hs =>
        CryptoVerification.E2E.Record.DeserializeGeneral.Leaf.ChainExitG.chainExitG_ok_atW
          img x R s0 s hs }

/-- Instantiate `MergeFieldLeavesW img ext` from basic/chain field leaves and an explicit `tag9` hypothesis. -/
theorem mergeFieldLeavesW_of_tag9 (img : Obj.Image) (ext : String → Option (State → State))
    (hLoads : Obj.Loads libsignalSessionImage img)
    (hCallees : DeserializeCalleesAtW img ext)
    (htag9 : MergeFieldGenOkAtW img ext (fun fl => fl.tag = 9)) :
    MergeFieldLeavesW img ext := by
  exact
    { tag1 :=
        CryptoVerification.E2E.Record.DeserializeGeneral.Leaf.MergeFieldGenSessionVersion.mergeFieldGenSessionVersion_ok_extW
          img ext hLoads hCallees
      tag234 :=
        CryptoVerification.E2E.Record.DeserializeGeneral.Leaf.MergeFieldGenIdentityRootKeys.mergeFieldGenIdentityRootKeys_ok_extW
          img ext hLoads hCallees
      tag5 :=
        CryptoVerification.E2E.Record.DeserializeGeneral.Leaf.MergeFieldGenPreviousCounter.mergeFieldGenPreviousCounter_ok_extW
          img ext hLoads hCallees
      tag6 := fun hCh =>
        CryptoVerification.E2E.Record.DeserializeGeneral.Leaf.MergeFieldGenSenderChain.mergeFieldGenSenderChain_ok_extW
          img ext hLoads hCallees hCh
      tag7 := fun hCh =>
        CryptoVerification.E2E.Record.DeserializeGeneral.Leaf.MergeFieldGenReceiverChains.mergeFieldGenReceiverChains_ok_extW
          img ext hLoads hCallees hCh
      tag9 := htag9 }

/-- Instantiate `MergeFieldLeavesW img ext` from all `SessionStructure::merge_field` leaf proofs. -/
theorem mergeFieldLeavesW_of_callees (img : Obj.Image) (ext : String → Option (State → State))
    (hLoads : Obj.Loads libsignalSessionImage img)
    (hCallees : DeserializeCalleesAtW img ext) :
    MergeFieldLeavesW img ext := by
  exact mergeFieldLeavesW_of_tag9 img ext hLoads hCallees
    (CryptoVerification.E2E.Record.DeserializeGeneral.Leaf.MergeFieldGenPendingPreKey.mergeFieldGenPendingPreKey_ok_extW
      img ext hLoads hCallees)

/-- Exact `SessionRecord::deserialize` contract at `img.base + deserializeOff` from leaf bundles. -/
theorem deserializeExactAtX_ok_of_leaves {img : Obj.Image}
    {ext : String → Option (State → State)}
    (hChain : ChainLeavesW img ext)
    (hMF : MergeFieldLeavesW img ext)
    (hD : DeserLeavesW img ext) :
    subroutine_ok (contractProg img.base ext) (img.base + deserializeOff)
      (deserializeExactSpecAtX img) := by
  rw [← recDeserialize_fnAddr_eqX img.base ext]
  exact deserializeExactW_ok_of_leaves img ext hChain hMF hD

/-- `recordDeserializeOpenSpec A0` at `img.base + deserializeOff` from leaf bundles. -/
theorem recordDeserialize_ok_of_leaves {img : Obj.Image}
    {ext : String → Option (State → State)}
    (hChain : ChainLeavesW img ext)
    (hMF : MergeFieldLeavesW img ext)
    (hD : DeserLeavesW img ext) :
    subroutine_ok (contractProg img.base ext) (img.base + deserializeOff)
      ((recordDeserializeOpenSpec A0).inImage img) := by
  exact recordDeserializeOpen_of_exactX img (deserializeExactAtX_ok_of_leaves hChain hMF hD)

/-- Exact `SessionRecord::deserialize` contract at `img.base + deserializeOff` from `Stage2ContractsA0`. -/
theorem deserializeExactAtX_ok_of_stage2 {img : Obj.Image}
    {ext : String → Option (State → State)}
    (hStage2 : Stage2ContractsA0 img ext) :
    subroutine_ok (contractProg img.base ext) (img.base + deserializeOff)
      (deserializeExactSpecAtX img) := by
  have hCallees := deserializeCalleesAtW_of_stage2 hStage2
  exact deserializeExactAtX_ok_of_leaves
    (chainLeavesW_of_callees img ext hCallees)
    (mergeFieldLeavesW_of_callees img ext hStage2.loads hCallees)
    (deserLeavesW_of_stage2 img ext hStage2 hCallees)

/-- `recordDeserializeOpenSpec A0` at `img.base + deserializeOff` from `Stage2ContractsA0`. -/
theorem recordDeserialize_ok_of_stage2 {img : Obj.Image}
    {ext : String → Option (State → State)}
    (hStage2 : Stage2ContractsA0 img ext) :
    subroutine_ok (contractProg img.base ext) (img.base + deserializeOff)
      ((recordDeserializeOpenSpec A0).inImage img) := by
  exact recordDeserializeOpen_of_exactX img (deserializeExactAtX_ok_of_stage2 hStage2)

/-! ## Arbitrary-Allocator (`A : RustAlloc`) Assembly -/

/-- Instantiate `DeserLeavesWA img A ext` from `DeserLoopEntryGExt`, `DeserLoopIterGExt`, `DeserLoopExitGExt`. -/
theorem deserLeavesWA_of_stage2 (img : Obj.Image) (A : RustAlloc)
    (ext : String → Option (State → State))
    (hStage2 : Stage2ContractsA img A ext)
    (hCallees : DeserializeCalleesAtWA img A ext) :
    DeserLeavesWA img A ext :=
  { entry := fun x R s0 hpc hrun hpre hal =>
      DeserLoopEntryGExt.deserLoopEntryG_ok_atWA img A ext hCallees x R s0 hpc hrun hpre hal
    iter := fun hMF x R s0 k s hr hlt hs =>
      CryptoVerification.E2E.Record.DeserializeGeneral.Leaf.DeserLoopIterG.deserLoopIterG_ok_atWA
        img A ext hMF x R s0 k s hr hlt hs
    exit := fun x R s0 s hr hs =>
      deserLoopExitG_ok_extWA img A ext hStage2 x R s0 s hr hs }

/-- Instantiate `ChainLeavesWA img A ext` from `Chain{Entry,SenderRatchetKey,KeyField,MessageKeys,Exit}GExt`. -/
theorem chainLeavesWA_of_callees (img : Obj.Image) (A : RustAlloc)
    (ext : String → Option (State → State))
    (hCallees : DeserializeCalleesAtWA img A ext) :
    ChainLeavesWA img A ext :=
  { entry := fun x R s0 hpc hrun hpre hal =>
      CryptoVerification.E2E.Record.DeserializeGeneral.Leaf.ChainEntryG.chainEntryG_ok_impl_atWA
        img A hCallees x R s0 hpc hrun hpre hal
    srk := fun x R s0 k s hk htag hs =>
      CryptoVerification.E2E.Record.DeserializeGeneral.Leaf.ChainSenderRatchetKeyG.chainSenderRatchetKeyG_ok_atWA
        img A hCallees x R s0 k s hk htag hs
    ck := fun x R s0 k s hk htag hs =>
      CryptoVerification.E2E.Record.DeserializeGeneral.Leaf.ChainKeyFieldG.chainKeyFieldG_ok_atWA
        img A hCallees x R s0 k s hk htag hs
    keys := fun x R s0 k s hk htag hs =>
      CryptoVerification.E2E.Record.DeserializeGeneral.Leaf.ChainMessageKeysG.chainMessageKeysG_ok_atWA
        img A hCallees x R s0 k s hk htag hs
    exit := fun x R s0 s hs =>
      CryptoVerification.E2E.Record.DeserializeGeneral.Leaf.ChainExitG.chainExitG_ok_atWA
        img A x R s0 s hs }

/-- Instantiate `MergeFieldLeavesWA img A ext` from `MergeFieldGen*Ext` and an explicit `tag9` hypothesis. -/
theorem mergeFieldLeavesWA_of_tag9 (img : Obj.Image) (A : RustAlloc)
    (ext : String → Option (State → State))
    (hLoads : Obj.Loads libsignalSessionImage img)
    (hCallees : DeserializeCalleesAtWA img A ext)
    (htag9 : MergeFieldGenOkAtWA img A ext (fun fl => fl.tag = 9)) :
    MergeFieldLeavesWA img A ext :=
  { tag1 :=
      CryptoVerification.E2E.Record.DeserializeGeneral.Leaf.MergeFieldGenSessionVersion.mergeFieldGenSessionVersion_ok_extWA
        img A ext hLoads hCallees
    tag234 :=
      CryptoVerification.E2E.Record.DeserializeGeneral.Leaf.MergeFieldGenIdentityRootKeys.mergeFieldGenIdentityRootKeys_ok_extWA
        img A ext hLoads hCallees
    tag5 :=
      CryptoVerification.E2E.Record.DeserializeGeneral.Leaf.MergeFieldGenPreviousCounter.mergeFieldGenPreviousCounter_ok_extWA
        img A ext hLoads hCallees
    tag6 := fun hCh =>
      CryptoVerification.E2E.Record.DeserializeGeneral.Leaf.MergeFieldGenSenderChain.mergeFieldGenSenderChain_ok_extWA
        img A ext hLoads hCallees hCh
    tag7 := fun hCh =>
      CryptoVerification.E2E.Record.DeserializeGeneral.Leaf.MergeFieldGenReceiverChains.mergeFieldGenReceiverChains_ok_extWA
        img A ext hLoads hCallees hCh
    tag9 := htag9 }

/-- Instantiate `MergeFieldLeavesWA img A ext` from all 6 `MergeFieldGen*Ext` leaves. -/
theorem mergeFieldLeavesWA_of_callees (img : Obj.Image) (A : RustAlloc)
    (ext : String → Option (State → State))
    (hLoads : Obj.Loads libsignalSessionImage img)
    (hCallees : DeserializeCalleesAtWA img A ext) :
    MergeFieldLeavesWA img A ext :=
  mergeFieldLeavesWA_of_tag9 img A ext hLoads hCallees
    (CryptoVerification.E2E.Record.DeserializeGeneral.Leaf.MergeFieldGenPendingPreKey.mergeFieldGenPendingPreKey_ok_extWA
      img A ext hLoads hCallees)

/-- Exact `SessionRecord::deserialize` contract (`deserializeExactSpecAtXA A img`) from `*WA` leaf bundles. -/
theorem deserializeExactAtX_ok_of_leavesA {img : Obj.Image} (A : RustAlloc)
    {ext : String → Option (State → State)}
    (hChain : ChainLeavesWA img A ext)
    (hMF : MergeFieldLeavesWA img A ext)
    (hD : DeserLeavesWA img A ext) :
    subroutine_ok (contractProg img.base ext) (img.base + deserializeOff)
      (deserializeExactSpecAtXA A img) := by
  rw [← recDeserialize_fnAddr_eqX img.base ext]
  exact deserializeExactWA_ok_of_leaves img A ext hChain hMF hD

/-- General `SessionRecord::deserialize` contract (`deserializeGenSpecAtA A img`) from `*WA` leaf bundles. -/
theorem deserializeGenAtX_ok_of_leavesA {img : Obj.Image} (A : RustAlloc)
    {ext : String → Option (State → State)}
    (hChain : ChainLeavesWA img A ext)
    (hMF : MergeFieldLeavesWA img A ext)
    (hD : DeserLeavesWA img A ext) :
    subroutine_ok (contractProg img.base ext) (img.base + deserializeOff)
      (deserializeGenSpecAtA A img) := by
  rw [← recDeserialize_fnAddr_eqX img.base ext]
  exact deserializeBodyGWA_ok img A ext hD
    (mergeFieldGenWA_ok img A ext hMF (chainMergeGenWA_ok img A ext hChain))
    (deserReprGA_ok A)

/-- `recordDeserializeOpenSpec A` at `img.base + deserializeOff` from `*WA` leaf bundles. -/
theorem recordDeserialize_ok_of_leavesA {img : Obj.Image} (A : RustAlloc)
    {ext : String → Option (State → State)}
    (hChain : ChainLeavesWA img A ext)
    (hMF : MergeFieldLeavesWA img A ext)
    (hD : DeserLeavesWA img A ext) :
    subroutine_ok (contractProg img.base ext) (img.base + deserializeOff)
      ((recordDeserializeOpenSpec A).inImage img) :=
  recordDeserializeOpen_of_exactXA A img (deserializeExactAtX_ok_of_leavesA A hChain hMF hD)

/-- Exact `SessionRecord::deserialize` contract (`deserializeExactSpecAtXA A img`) from `Stage2ContractsA`. -/
theorem deserializeExactAtX_ok_of_stage2A {img : Obj.Image} (A : RustAlloc)
    {ext : String → Option (State → State)}
    (hStage2 : Stage2ContractsA img A ext) :
    subroutine_ok (contractProg img.base ext) (img.base + deserializeOff)
      (deserializeExactSpecAtXA A img) := by
  have hCallees := deserializeCalleesAtWA_of_stage2 hStage2
  exact deserializeExactAtX_ok_of_leavesA A
    (chainLeavesWA_of_callees img A ext hCallees)
    (mergeFieldLeavesWA_of_callees img A ext hStage2.loads hCallees)
    (deserLeavesWA_of_stage2 img A ext hStage2 hCallees)

/-- General `SessionRecord::deserialize` contract (`deserializeGenSpecAtA A img`, matching
`sessDeserializeExtSpec DeserializeScope A img`) from `Stage2ContractsA`. -/
theorem deserializeGenAtX_ok_of_stage2A {img : Obj.Image} (A : RustAlloc)
    {ext : String → Option (State → State)}
    (hStage2 : Stage2ContractsA img A ext) :
    subroutine_ok (contractProg img.base ext) (img.base + deserializeOff)
      (deserializeGenSpecAtA A img) := by
  have hCallees := deserializeCalleesAtWA_of_stage2 hStage2
  exact deserializeGenAtX_ok_of_leavesA A
    (chainLeavesWA_of_callees img A ext hCallees)
    (mergeFieldLeavesWA_of_callees img A ext hStage2.loads hCallees)
    (deserLeavesWA_of_stage2 img A ext hStage2 hCallees)

/-- `recordDeserializeOpenSpec A` at `img.base + deserializeOff` from `Stage2ContractsA`. -/
theorem recordDeserialize_ok_of_stage2A {img : Obj.Image} (A : RustAlloc)
    {ext : String → Option (State → State)}
    (hStage2 : Stage2ContractsA img A ext) :
    subroutine_ok (contractProg img.base ext) (img.base + deserializeOff)
      ((recordDeserializeOpenSpec A).inImage img) :=
  recordDeserializeOpen_of_exactXA A img (deserializeExactAtX_ok_of_stage2A A hStage2)

/-! ## Relocatable `[LibsignalPlacement]` `SessionRecord::deserialize` Assembly -/

section Placed

open Arm64.Obj CryptoVerification.E2E.Record.Placed

/-- Anchor declaration for incremental close checking of the `Placed` section. -/
theorem L1_RecordDeserializeX_Placed : True := trivial

/-- Instantiate `DeserLeavesPlacedW H` from a `memcpy` contract at `extHookStack` and
`DeserializeCalleesPlacedW H`. -/
theorem deserLeavesPlacedW_of_memcpy [LibsignalPlacement] (H : LibsignalHooks)
    (hmc : subroutine_ok (lsProg_46 H) (lsρ "memcpy")
      (withLsCl lsmpl (sessionMemcpySpec CryptoVerification.LibsignalTripleRatchet.extHookStack)))
    (hCallees : DeserializeCalleesPlacedW H) :
    DeserLeavesPlacedW H :=
  { entry := fun x R s0 hpc hrun hpre hal =>
      DeserLoopEntryGExt.deserLoopEntryG_placed_okW H hCallees x R s0 hpc hrun hpre hal
    iter := fun hMF x R s0 k s hr hlt hs =>
      CryptoVerification.E2E.Record.DeserializeGeneral.Leaf.DeserLoopIterG.deserLoopIterG_placed_okW
        H hMF x R s0 k s hr hlt hs
    exit := fun x R s0 s hr hs =>
      deserLoopExitG_placed_ok_of_memcpy H (memcpy_placed_ok_of_extHookStack hmc) x R s0 s hr hs }

/-- Instantiate `DeserLeavesPlacedW H` from `Stage2ContractsA0Placed H` and
`DeserializeCalleesPlacedW H`. -/
theorem deserLeavesPlacedW_of_stage2 [LibsignalPlacement] (H : LibsignalHooks)
    (hStage2 : Stage2ContractsA0Placed H)
    (hCallees : DeserializeCalleesPlacedW H) :
    DeserLeavesPlacedW H :=
  deserLeavesPlacedW_of_memcpy H hStage2.memcpy hCallees

/-- Instantiate `ChainLeavesPlacedW H` from `DeserializeCalleesPlacedW H`. -/
theorem chainLeavesPlacedW_of_callees [LibsignalPlacement] (H : LibsignalHooks)
    (hCallees : DeserializeCalleesPlacedW H) :
    ChainLeavesPlacedW H :=
  { entry := fun x R s0 hpc hrun hpre hal =>
      CryptoVerification.E2E.Record.DeserializeGeneral.Leaf.ChainEntryG.chainEntryG_placed_okW
        H hCallees x R s0 hpc hrun hpre hal
    srk := fun x R s0 k s hk htag hs =>
      CryptoVerification.E2E.Record.DeserializeGeneral.Leaf.ChainSenderRatchetKeyG.chainSenderRatchetKeyG_placed_okW
        hCallees x R s0 k s hk htag hs
    ck := fun x R s0 k s hk htag hs =>
      CryptoVerification.E2E.Record.DeserializeGeneral.Leaf.ChainKeyFieldG.chainKeyFieldG_placed_okW
        hCallees x R s0 k s hk htag hs
    keys := fun x R s0 k s hk htag hs =>
      CryptoVerification.E2E.Record.DeserializeGeneral.Leaf.ChainMessageKeysG.chainMessageKeysG_placed_okW
        hCallees x R s0 k s hk htag hs
    exit := fun x R s0 s hs =>
      CryptoVerification.E2E.Record.DeserializeGeneral.Leaf.ChainExitG.chainExitG_placed_okW
        H x R s0 s hs }

/-- Instantiate `MergeFieldLeavesPlacedW H` from `DeserializeCalleesPlacedW H` and an explicit
`tag9` hypothesis. -/
theorem mergeFieldLeavesPlacedW_of_tag9 [LibsignalPlacement] (H : LibsignalHooks)
    (hCallees : DeserializeCalleesPlacedW H)
    (htag9 : MergeFieldGenPlacedOkW H (fun fl => fl.tag = 9)) :
    MergeFieldLeavesPlacedW H :=
  { tag1 :=
      CryptoVerification.E2E.Record.DeserializeGeneral.Leaf.MergeFieldGenSessionVersion.mergeFieldGenSessionVersion_placed_okW
        H hCallees
    tag234 :=
      CryptoVerification.E2E.Record.DeserializeGeneral.Leaf.MergeFieldGenIdentityRootKeys.mergeFieldGenIdentityRootKeys_placed_okW
        H hCallees
    tag5 :=
      CryptoVerification.E2E.Record.DeserializeGeneral.Leaf.MergeFieldGenPreviousCounter.mergeFieldGenPreviousCounter_placed_okW
        H hCallees
    tag6 := fun hCh =>
      CryptoVerification.E2E.Record.DeserializeGeneral.Leaf.MergeFieldGenSenderChain.mergeFieldGenSenderChain_placed_okW
        H hCallees hCh
    tag7 := fun hCh =>
      CryptoVerification.E2E.Record.DeserializeGeneral.Leaf.MergeFieldGenReceiverChains.mergeFieldGenReceiverChains_placed_okW
        H hCallees hCh
    tag9 := htag9 }

/-- Instantiate `MergeFieldLeavesPlacedW H` from `DeserializeCalleesPlacedW H`. -/
theorem mergeFieldLeavesPlacedW_of_callees [LibsignalPlacement] (H : LibsignalHooks)
    (hCallees : DeserializeCalleesPlacedW H) :
    MergeFieldLeavesPlacedW H :=
  mergeFieldLeavesPlacedW_of_tag9 H hCallees
    (CryptoVerification.E2E.Record.DeserializeGeneral.Leaf.MergeFieldGenPendingPreKey.mergeFieldGenPendingPreKey_placed_okW
      H hCallees)

/-- Relocatable exact `SessionRecord::deserialize` contract on `lsProg_46 H` from leaf bundles. -/
theorem deserializeExactPlacedX_ok_of_leaves [LibsignalPlacement] {H : LibsignalHooks}
    (hChain : ChainLeavesPlacedW H)
    (hMF : MergeFieldLeavesPlacedW H)
    (hD : DeserLeavesPlacedW H) :
    subroutine_ok (lsProg_46 H) (blkPl_46).base deserializeExactPlacedSpecX :=
  deserializeExactPlacedW_ok_of_leaves H hChain hMF hD

/-- Relocatable `recordDeserializeOpenSpec A0` on `lsProg_46 H` from leaf bundles. -/
theorem recordDeserialize_placed_ok_of_leaves [LibsignalPlacement] {H : LibsignalHooks}
    (hChain : ChainLeavesPlacedW H)
    (hMF : MergeFieldLeavesPlacedW H)
    (hD : DeserLeavesPlacedW H) :
    subroutine_ok (lsProg_46 H) (blkPl_46).base
      (LibsignalTripleRatchet.withLsCodeRoLoaded lsmpl (recordDeserializeOpenSpec A0)) :=
  recordDeserializeOpen_placed_of_exactX lsmpl (deserializeExactPlacedX_ok_of_leaves hChain hMF hD)

/-- Relocatable exact `SessionRecord::deserialize` contract on `lsProg_46 H` from minimal
allocator + `memcpy` contracts (`Stage1X.AllocContractsPlaced A0 H` + `memcpy`). -/
theorem deserializeExactPlacedX_ok_of_alloc [LibsignalPlacement] {H : LibsignalHooks}
    (hA : Stage1X.AllocContractsPlaced A0 H)
    (hMemcpy : ∀ {callerProg : Program} {callerBlk : Nat} [IsLsBlockProg callerProg callerBlk H],
      subroutine_ok callerProg (lsρ "memcpy")
        (withLsCl lsmpl (sessionMemcpySpec CryptoVerification.LibsignalTripleRatchet.extHookStack))) :
    subroutine_ok (lsProg_46 H) (blkPl_46).base deserializeExactPlacedSpecX := by
  have hCallees := deserializeCalleesPlacedW_of_alloc hA hMemcpy
  exact deserializeExactPlacedX_ok_of_leaves
    (chainLeavesPlacedW_of_callees H hCallees)
    (mergeFieldLeavesPlacedW_of_callees H hCallees)
    (deserLeavesPlacedW_of_memcpy H hMemcpy hCallees)

/-- Relocatable `recordDeserializeOpenSpec A0` on `lsProg_46 H` from minimal allocator + `memcpy`
contracts (`Stage1X.AllocContractsPlaced A0 H` + `memcpy`). -/
theorem recordDeserialize_placed_ok_of_alloc [LibsignalPlacement] {H : LibsignalHooks}
    (hA : Stage1X.AllocContractsPlaced A0 H)
    (hMemcpy : ∀ {callerProg : Program} {callerBlk : Nat} [IsLsBlockProg callerProg callerBlk H],
      subroutine_ok callerProg (lsρ "memcpy")
        (withLsCl lsmpl (sessionMemcpySpec CryptoVerification.LibsignalTripleRatchet.extHookStack))) :
    subroutine_ok (lsProg_46 H) (blkPl_46).base
      (LibsignalTripleRatchet.withLsCodeRoLoaded lsmpl (recordDeserializeOpenSpec A0)) :=
  recordDeserializeOpen_placed_of_exactX lsmpl (deserializeExactPlacedX_ok_of_alloc hA hMemcpy)

/-- Relocatable general `SessionRecord::deserialize` contract (`deserializeGenPlacedSpec`) on
`lsProg_46 H` from minimal allocator + `memcpy` contracts. -/
theorem deserializeGen_placed_ok_of_alloc [LibsignalPlacement] {H : LibsignalHooks}
    (hA : Stage1X.AllocContractsPlaced A0 H)
    (hMemcpy : ∀ {callerProg : Program} {callerBlk : Nat} [IsLsBlockProg callerProg callerBlk H],
      subroutine_ok callerProg (lsρ "memcpy")
        (withLsCl lsmpl (sessionMemcpySpec CryptoVerification.LibsignalTripleRatchet.extHookStack))) :
    subroutine_ok (lsProg_46 H) (blkPl_46).base deserializeGenPlacedSpec := by
  have hCallees := deserializeCalleesPlacedW_of_alloc hA hMemcpy
  exact deserializeBodyGPlacedW_ok H
    (deserLeavesPlacedW_of_memcpy H hMemcpy hCallees)
    (mergeFieldGenPlacedW_ok H (mergeFieldLeavesPlacedW_of_callees H hCallees)
      (chainMergeGenPlacedW_ok H (chainLeavesPlacedW_of_callees H hCallees)))
    deserReprG_ok

/-- Relocatable exact `SessionRecord::deserialize` contract on `lsProg_46 H` from
`Stage2ContractsA0Placed H`. -/
theorem deserializeExactPlacedX_ok_of_stage2 [LibsignalPlacement] {H : LibsignalHooks}
    (hStage2 : Stage2ContractsA0Placed H) :
    subroutine_ok (lsProg_46 H) (blkPl_46).base deserializeExactPlacedSpecX :=
  deserializeExactPlacedX_ok_of_alloc
    (allocContractsPlaced_of_stage2ContractsA0Placed hStage2) hStage2.memcpy

/-- Relocatable `recordDeserializeOpenSpec A0` on `lsProg_46 H` from `Stage2ContractsA0Placed H`. -/
theorem recordDeserialize_placed_ok_of_stage2 [LibsignalPlacement] {H : LibsignalHooks}
    (hStage2 : Stage2ContractsA0Placed H) :
    subroutine_ok (lsProg_46 H) (blkPl_46).base
      (LibsignalTripleRatchet.withLsCodeRoLoaded lsmpl (recordDeserializeOpenSpec A0)) :=
  recordDeserialize_placed_ok_of_alloc
    (allocContractsPlaced_of_stage2ContractsA0Placed hStage2) hStage2.memcpy

/-- Relocatable general `SessionRecord::deserialize` contract (`deserializeGenPlacedSpec`) on
`lsProg_46 H` from `Stage2ContractsA0Placed H`. -/
theorem deserializeGen_placed_ok_of_stage2 [LibsignalPlacement] {H : LibsignalHooks}
    (hStage2 : Stage2ContractsA0Placed H) :
    subroutine_ok (lsProg_46 H) (blkPl_46).base deserializeGenPlacedSpec :=
  deserializeGen_placed_ok_of_alloc
    (allocContractsPlaced_of_stage2ContractsA0Placed hStage2) hStage2.memcpy

end Placed

end Proofs.libsignal.Hooks2
