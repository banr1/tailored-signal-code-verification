/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Heap.IfaceBudget
public import LibsignalBinary.Heap.IfaceBudgetLemmas
public import LibsignalBinary.Heap.SpecBudget
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Over.StageP2Defs
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Over.StageP2DefsPlaced
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Over.CloseDefsPlacedBudget
public import LibsignalBinary.Proofs.E2E.Record.Serialization.DefsBudget
public import LibsignalBinary.Proofs.PublicApi.StoreKit.Over.MatchDefsBudget
import LibsignalBinary.Proofs.Common.SharedHelpers
meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep

/-!
# Budget-Threaded Stage P2 Over-Path Callee Specifications and Envelopes

Defines `VmPreserved` zero-allocation miss contracts for `<SessionRecord>::promote_matching_session`
(block 50) and `RustCliAllocBudget M` contracts with allocation envelope `PromoteOverEnv` for
`<SessionRecord>::promote_state` (block 47).
-/

@[expose] public section

set_option autoImplicit false

namespace LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Over.StageP2DefsBudget

open Arm64 ProofLib SepProp
open CryptoGames.LibsignalSessionApi (Session SessionRecord)
open CryptoVerification (LibsignalPlacement lsmpl withLsCl)
open CryptoVerification.RustHeap (RustAlloc vecAt)
open CryptoVerification.LibsignalTripleRatchetRepr (SessionGhost)
open CryptoVerification.LibsignalPublicApiRepr (RecordGhost sessionRecordAt sessionStateReprAt)
open CryptoVerification.E2E.Record.Serialization (encSessionMem)
open CryptoVerification.CliHandshake.RespClosurePlaced (blkPl_518 lsProg_518)
open CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Kits (p2_stackAt_split_of_le)
open CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Matched (prevSessionsEmptyAt)
open CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.OverP2 (
  HdrP Prev1 clearPending clearPendingGhost prevElem prevVecAt
  stageP2OverEntryPlaced stageP2OverProgPlaced
)
open CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Over (
  P2PromoteMatchingMissCallGhost P2PromoteMissGhost
  P2PromoteOverCallGhost P2PromoteOverGenGhost P2SessMatchesMsg
  p2ArchiveStackX p2OverPromoteMissStackExt p2PromoteMissStack p2PromoteStackX
  p2PromoteStateName p2_bind_sepWPp_nopanic_frame p2_hdrP4_prev1_entails_prevVecAt
  prevEmpty_sessionAt_eq_sessionRecordAt sessionAt_entails_sessionStateAt
  stageP2OverCallStack stageP2OverCallStack4K stageP2OverCallStack4K_eq
  stageP2OverPureAndErrStack stageP2OverV1CallStack stageP2OverV1CallStack4K
  stageP2OverV1CallStack4K_eq
)
open LibsignalBinary.Heap (
  AllocCostModel AllocEvent BudgetLimits FitsEnv FreeOnlyEvs RustCliAllocBudget SeqEnv VmPreserved
)
open LibsignalBinary.Heap.SpecBudget (withVmPreserved)
open LibsignalBinary.Proofs.E2E.Record.Serialization.DefsBudget (BoundedRustEvs)

/-! ## `VmPreserved` `promote_matching_session` Miss Contracts (Block 50) -/

/-- `VmPreserved` instance-specialized `<SessionRecord>::promote_matching_session` miss contract
(`p2PromoteMissStack = 1248` B, zero allocations). -/
def p2PromoteMatchingMissAtSpec (A : RustAlloc) (coroPtr : BitVec 64)
    (g : RecordGhost) (recG : SessionGhost) (sess : Session (List (BitVec 8)))
    (msgVer : BitVec 8) (serBytes : List (BitVec 8)) : Spec P2PromoteMatchingMissCallGhost :=
  withVmPreserved
    (CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Over.p2PromoteMatchingMissAtSpec
      A coroPtr g recG sess msgVer serBytes)

def p2PromoteMatchingMissGenSpec (A : RustAlloc) : Spec P2PromoteMissGhost :=
  withVmPreserved
    (CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Over.p2PromoteMatchingMissGenSpec A)

def p2PromoteMatchingMissAtSpecExt (A : RustAlloc) (coroPtr : BitVec 64)
    (g : RecordGhost) (recG : SessionGhost) (sess : Session (List (BitVec 8)))
    (msgVer : BitVec 8) (serBytes : List (BitVec 8)) : Spec P2PromoteMatchingMissCallGhost :=
  withVmPreserved
    (CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Over.p2PromoteMatchingMissAtSpecExt
      A coroPtr g recG sess msgVer serBytes)

def p2PromoteMatchingMissGenSpecExt (A : RustAlloc) : Spec P2PromoteMissGhost :=
  withVmPreserved
    (CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Over.p2PromoteMatchingMissGenSpecExt A)

theorem promoteMatchingMissAt_of_gen {A : RustAlloc} {prog : Program} {entry : BitVec 64}
    (hGen : subroutine_ok prog entry (p2PromoteMatchingMissGenSpec A))
    (coroPtr : BitVec 64) (g : RecordGhost) (recG : SessionGhost)
    (sess : Session (List (BitVec 8))) (msgVer : BitVec 8) (serBytes : List (BitVec 8))
    (hmiss : ¬ P2SessMatchesMsg sess msgVer serBytes)
    (hlen : serBytes.length = 33) :
    subroutine_ok prog entry
      (p2PromoteMatchingMissAtSpec A coroPtr g recG sess msgVer serBytes) := by
  refine subroutine_ok_outcome_intro fun x R s0 hpc hrun hpre halign => ?_
  let g' : RecordGhost := ⟨g.prevCap, g.prevPtr, some recG⟩
  let xg : P2PromoteMissGhost :=
    ⟨coroPtr + 0xe0#64, msgVer, x.serPtr, serBytes, x.outPtr, g', ⟨some sess⟩, sess⟩
  have hpre' : s0.mem ⊨ (p2PromoteMatchingMissGenSpec A).pre xg s0 ∗ R := by
    refine Satisfies.mono (sepConj_mono_left ?_) hpre
    dsimp only [p2PromoteMatchingMissAtSpec, p2PromoteMatchingMissGenSpec, withVmPreserved,
      CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Over.p2PromoteMatchingMissAtSpec,
      CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Over.p2PromoteMatchingMissGenSpec, xg, g']
    have hre :
        prevSessionsEmptyAt A coroPtr g ∗ (sessionStateReprAt A (coroPtr + 0xf8#64) recG sess ∗
          ((x.serPtr ↦ₛ serBytes) ∗ (memRegion x.outPtr 16 ∗ stackAt s0.sp p2PromoteMissStack))) =
        (prevSessionsEmptyAt A coroPtr g ∗ sessionStateReprAt A (coroPtr + 0xf8#64) recG sess) ∗
          ((x.serPtr ↦ₛ serBytes) ∗ (memRegion x.outPtr 16 ∗ stackAt s0.sp p2PromoteMissStack)) := by
      ac_rfl
    rw [hre, prevEmpty_sessionAt_eq_sessionRecordAt]
    refine Entails.pure_left fun ⟨h0, h1, h2, h3, h8⟩ => ?_
    exact Entails.pure_right ⟨h0, h1, h2, h3, h8, rfl, hmiss, hlen⟩ (Entails.of_eq (by ac_rfl))
  refine hGen.mono_outcome xg R s0 hpc hrun hpre' halign ?_
  rintro sf (⟨hret, hcs, hpost⟩ | hpan | hexit | hoom)
  · refine Or.inl ⟨hret, hcs, ?_⟩
    refine Satisfies.mono (sepConj_mono_left ?_) hpost
    dsimp only [p2PromoteMatchingMissAtSpec, p2PromoteMatchingMissGenSpec, withVmPreserved,
      CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Over.p2PromoteMatchingMissAtSpec,
      CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Over.p2PromoteMatchingMissGenSpec, xg, g']
    rw [← prevEmpty_sessionAt_eq_sessionRecordAt]
    exact Entails.of_eq (by ac_rfl)
  · exact Or.inr (Or.inl hpan)
  · exact Or.inr (Or.inr (Or.inl hexit))
  · exact Or.inr (Or.inr (Or.inr hoom))

theorem promoteMatchingMissAt_of_gen_ext {A : RustAlloc} {prog : Program} {entry : BitVec 64}
    (hGen : subroutine_ok prog entry (p2PromoteMatchingMissGenSpecExt A))
    (coroPtr : BitVec 64) (g : RecordGhost) (recG : SessionGhost)
    (sess : Session (List (BitVec 8))) (msgVer : BitVec 8) (serBytes : List (BitVec 8))
    (hmiss : ¬ P2SessMatchesMsg sess msgVer serBytes)
    (hlen : serBytes.length = 33) :
    subroutine_ok prog entry
      (p2PromoteMatchingMissAtSpecExt A coroPtr g recG sess msgVer serBytes) := by
  refine subroutine_ok_outcome_intro fun x R s0 hpc hrun hpre halign => ?_
  let g' : RecordGhost := ⟨g.prevCap, g.prevPtr, some recG⟩
  let xg : P2PromoteMissGhost :=
    ⟨coroPtr + 0xe0#64, msgVer, x.serPtr, serBytes, x.outPtr, g', ⟨some sess⟩, sess⟩
  have hpre' : s0.mem ⊨ (p2PromoteMatchingMissGenSpecExt A).pre xg s0 ∗ R := by
    refine Satisfies.mono (sepConj_mono_left ?_) hpre
    dsimp only [p2PromoteMatchingMissAtSpecExt, p2PromoteMatchingMissGenSpecExt, withVmPreserved,
      CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Over.p2PromoteMatchingMissAtSpecExt,
      CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Over.p2PromoteMatchingMissGenSpecExt, xg, g']
    have hre :
        prevSessionsEmptyAt A coroPtr g ∗ (sessionStateReprAt A (coroPtr + 0xf8#64) recG sess ∗
          ((x.serPtr ↦ₛ serBytes) ∗
            (memRegion x.outPtr 16 ∗ stackAt s0.sp p2OverPromoteMissStackExt))) =
        (prevSessionsEmptyAt A coroPtr g ∗ sessionStateReprAt A (coroPtr + 0xf8#64) recG sess) ∗
          ((x.serPtr ↦ₛ serBytes) ∗
            (memRegion x.outPtr 16 ∗ stackAt s0.sp p2OverPromoteMissStackExt)) := by
      ac_rfl
    rw [hre, prevEmpty_sessionAt_eq_sessionRecordAt]
    refine Entails.pure_left fun ⟨h0, h1, h2, h3, h8⟩ => ?_
    exact Entails.pure_right ⟨h0, h1, h2, h3, h8, rfl, hmiss, hlen⟩ (Entails.of_eq (by ac_rfl))
  refine hGen.mono_outcome xg R s0 hpc hrun hpre' halign ?_
  rintro sf (⟨hret, hcs, hpost⟩ | hpan | hexit | hoom)
  · refine Or.inl ⟨hret, hcs, ?_⟩
    refine Satisfies.mono (sepConj_mono_left ?_) hpost
    dsimp only [p2PromoteMatchingMissAtSpecExt, p2PromoteMatchingMissGenSpecExt, withVmPreserved,
      CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Over.p2PromoteMatchingMissAtSpecExt,
      CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Over.p2PromoteMatchingMissGenSpecExt, xg, g']
    rw [← prevEmpty_sessionAt_eq_sessionRecordAt]
    exact Entails.of_eq (by ac_rfl)
  · exact Or.inr (Or.inl hpan)
  · exact Or.inr (Or.inr (Or.inl hexit))
  · exact Or.inr (Or.inr (Or.inr hoom))

theorem promoteMatchingMissAt_to_ext {A : RustAlloc} {prog : Program} {entry : BitVec 64}
    {coroPtr : BitVec 64} {g : RecordGhost} {recG : SessionGhost}
    {sess : Session (List (BitVec 8))} {msgVer : BitVec 8} {serBytes : List (BitVec 8)}
    (h : subroutine_ok prog entry
      (p2PromoteMatchingMissAtSpec A coroPtr g recG sess msgVer serBytes)) :
    subroutine_ok prog entry
      (p2PromoteMatchingMissAtSpecExt A coroPtr g recG sess msgVer serBytes) := by
  refine subroutine_ok_map h ?_
  intro x R s0 hpre
  dsimp only [p2PromoteMatchingMissAtSpecExt, withVmPreserved,
    CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Over.p2PromoteMatchingMissAtSpecExt] at hpre
  rw [p2_stackAt_split_of_le s0.sp p2OverPromoteMissStackExt p2PromoteMissStack
    (by decide) (by decide)] at hpre
  simp only [sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨hpure, hmem⟩
  refine ⟨x,
    memRegion (s0.sp - BitVec.ofNat 64 p2OverPromoteMissStackExt)
      (p2OverPromoteMissStackExt - p2PromoteMissStack) ∗ R,
    ?_, fun sf hpost => ?_⟩
  · dsimp only [p2PromoteMatchingMissAtSpec, withVmPreserved,
      CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Over.p2PromoteMatchingMissAtSpec]
    simp only [sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨hpure, Satisfies.of_eq hmem (by ac_rfl)⟩
  · dsimp only [p2PromoteMatchingMissAtSpec, p2PromoteMatchingMissAtSpecExt, withVmPreserved,
      CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Over.p2PromoteMatchingMissAtSpec,
      CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Over.p2PromoteMatchingMissAtSpecExt]
      at hpost ⊢
    rw [p2_stackAt_split_of_le s0.sp p2OverPromoteMissStackExt p2PromoteMissStack
      (by decide) (by decide)]
    simp only [sepConj_assoc, satisfies_pure_sepConj] at hpost ⊢
    exact ⟨hpost.1, hpost.2.1, Satisfies.of_eq hpost.2.2 (by ac_rfl)⟩

/-- Relocatable `[LibsignalPlacement]` `VmPreserved` contract for `promote_matching_session` miss
at block 50 (`lsmpl.base 50`). -/
def PromoteMatchingMissAtPlacedProp [LibsignalPlacement] (A : RustAlloc)
    (ext : String → Option (State → State))
    (coroPtr : BitVec 64) (g : RecordGhost) (recG : SessionGhost)
    (sess : Session (List (BitVec 8))) (msgVer : BitVec 8) (serBytes : List (BitVec 8)) : Prop :=
  subroutine_ok (lsProg_518 ext) (lsmpl.base 50)
    (withLsCl lsmpl (p2PromoteMatchingMissAtSpec A coroPtr g recG sess msgVer serBytes))

def PromoteMatchingMissGenPlacedProp [LibsignalPlacement] (A : RustAlloc)
    (ext : String → Option (State → State)) : Prop :=
  subroutine_ok (lsProg_518 ext) (lsmpl.base 50)
    (withLsCl lsmpl (p2PromoteMatchingMissGenSpec A))

def PromoteMatchingMissAtExtPlacedProp [LibsignalPlacement] (A : RustAlloc)
    (ext : String → Option (State → State))
    (coroPtr : BitVec 64) (g : RecordGhost) (recG : SessionGhost)
    (sess : Session (List (BitVec 8))) (msgVer : BitVec 8) (serBytes : List (BitVec 8)) : Prop :=
  subroutine_ok (lsProg_518 ext) (lsmpl.base 50)
    (withLsCl lsmpl (p2PromoteMatchingMissAtSpecExt A coroPtr g recG sess msgVer serBytes))

def PromoteMatchingMissGenExtPlacedProp [LibsignalPlacement] (A : RustAlloc)
    (ext : String → Option (State → State)) : Prop :=
  subroutine_ok (lsProg_518 ext) (lsmpl.base 50)
    (withLsCl lsmpl (p2PromoteMatchingMissGenSpecExt A))

theorem promoteMatchingMissAt_placed_of_gen [LibsignalPlacement] {A : RustAlloc}
    {ext : String → Option (State → State)}
    (hGen : PromoteMatchingMissGenPlacedProp A ext)
    (coroPtr : BitVec 64) (g : RecordGhost) (recG : SessionGhost)
    (sess : Session (List (BitVec 8))) (msgVer : BitVec 8) (serBytes : List (BitVec 8))
    (hmiss : ¬ P2SessMatchesMsg sess msgVer serBytes)
    (hlen : serBytes.length = 33) :
    PromoteMatchingMissAtPlacedProp A ext coroPtr g recG sess msgVer serBytes := by
  refine subroutine_ok_outcome_intro fun x R s0 hpc hrun hpre halign => ?_
  let g' : RecordGhost := ⟨g.prevCap, g.prevPtr, some recG⟩
  let xg : P2PromoteMissGhost :=
    ⟨coroPtr + 0xe0#64, msgVer, x.serPtr, serBytes, x.outPtr, g', ⟨some sess⟩, sess⟩
  have hpre' : s0.mem ⊨ (withLsCl lsmpl (p2PromoteMatchingMissGenSpec A)).pre xg s0 ∗ R := by
    refine Satisfies.mono (sepConj_mono_left (sepConj_mono_left ?_)) hpre
    dsimp only [p2PromoteMatchingMissAtSpec, p2PromoteMatchingMissGenSpec, withVmPreserved,
      CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Over.p2PromoteMatchingMissAtSpec,
      CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Over.p2PromoteMatchingMissGenSpec, xg, g']
    have hre :
        prevSessionsEmptyAt A coroPtr g ∗ (sessionStateReprAt A (coroPtr + 0xf8#64) recG sess ∗
          ((x.serPtr ↦ₛ serBytes) ∗ (memRegion x.outPtr 16 ∗ stackAt s0.sp p2PromoteMissStack))) =
        (prevSessionsEmptyAt A coroPtr g ∗ sessionStateReprAt A (coroPtr + 0xf8#64) recG sess) ∗
          ((x.serPtr ↦ₛ serBytes) ∗ (memRegion x.outPtr 16 ∗ stackAt s0.sp p2PromoteMissStack)) := by
      ac_rfl
    rw [hre, prevEmpty_sessionAt_eq_sessionRecordAt]
    refine Entails.pure_left fun ⟨h0, h1, h2, h3, h8⟩ => ?_
    exact Entails.pure_right ⟨h0, h1, h2, h3, h8, rfl, hmiss, hlen⟩ (Entails.of_eq (by ac_rfl))
  refine hGen.mono_outcome xg R s0 hpc hrun hpre' halign ?_
  rintro sf (⟨hret, hcs, hpost⟩ | hpan | hexit | hoom)
  · refine Or.inl ⟨hret, hcs, ?_⟩
    refine Satisfies.mono (sepConj_mono_left (sepConj_mono_right ?_)) hpost
    dsimp only [p2PromoteMatchingMissAtSpec, p2PromoteMatchingMissGenSpec, withVmPreserved,
      CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Over.p2PromoteMatchingMissAtSpec,
      CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Over.p2PromoteMatchingMissGenSpec, xg, g']
    rw [← prevEmpty_sessionAt_eq_sessionRecordAt]
    exact Entails.of_eq (by ac_rfl)
  · exact Or.inr (Or.inl hpan)
  · exact Or.inr (Or.inr (Or.inl hexit))
  · exact Or.inr (Or.inr (Or.inr hoom))

theorem promoteMatchingMissAt_ext_placed_of_gen [LibsignalPlacement] {A : RustAlloc}
    {ext : String → Option (State → State)}
    (hGen : PromoteMatchingMissGenExtPlacedProp A ext)
    (coroPtr : BitVec 64) (g : RecordGhost) (recG : SessionGhost)
    (sess : Session (List (BitVec 8))) (msgVer : BitVec 8) (serBytes : List (BitVec 8))
    (hmiss : ¬ P2SessMatchesMsg sess msgVer serBytes)
    (hlen : serBytes.length = 33) :
    PromoteMatchingMissAtExtPlacedProp A ext coroPtr g recG sess msgVer serBytes := by
  refine subroutine_ok_outcome_intro fun x R s0 hpc hrun hpre halign => ?_
  let g' : RecordGhost := ⟨g.prevCap, g.prevPtr, some recG⟩
  let xg : P2PromoteMissGhost :=
    ⟨coroPtr + 0xe0#64, msgVer, x.serPtr, serBytes, x.outPtr, g', ⟨some sess⟩, sess⟩
  have hpre' : s0.mem ⊨ (withLsCl lsmpl (p2PromoteMatchingMissGenSpecExt A)).pre xg s0 ∗ R := by
    refine Satisfies.mono (sepConj_mono_left (sepConj_mono_left ?_)) hpre
    dsimp only [p2PromoteMatchingMissAtSpecExt, p2PromoteMatchingMissGenSpecExt, withVmPreserved,
      CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Over.p2PromoteMatchingMissAtSpecExt,
      CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Over.p2PromoteMatchingMissGenSpecExt, xg, g']
    have hre :
        prevSessionsEmptyAt A coroPtr g ∗ (sessionStateReprAt A (coroPtr + 0xf8#64) recG sess ∗
          ((x.serPtr ↦ₛ serBytes) ∗
            (memRegion x.outPtr 16 ∗ stackAt s0.sp p2OverPromoteMissStackExt))) =
        (prevSessionsEmptyAt A coroPtr g ∗ sessionStateReprAt A (coroPtr + 0xf8#64) recG sess) ∗
          ((x.serPtr ↦ₛ serBytes) ∗
            (memRegion x.outPtr 16 ∗ stackAt s0.sp p2OverPromoteMissStackExt)) := by
      ac_rfl
    rw [hre, prevEmpty_sessionAt_eq_sessionRecordAt]
    refine Entails.pure_left fun ⟨h0, h1, h2, h3, h8⟩ => ?_
    exact Entails.pure_right ⟨h0, h1, h2, h3, h8, rfl, hmiss, hlen⟩ (Entails.of_eq (by ac_rfl))
  refine hGen.mono_outcome xg R s0 hpc hrun hpre' halign ?_
  rintro sf (⟨hret, hcs, hpost⟩ | hpan | hexit | hoom)
  · refine Or.inl ⟨hret, hcs, ?_⟩
    refine Satisfies.mono (sepConj_mono_left (sepConj_mono_right ?_)) hpost
    dsimp only [p2PromoteMatchingMissAtSpecExt, p2PromoteMatchingMissGenSpecExt, withVmPreserved,
      CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Over.p2PromoteMatchingMissAtSpecExt,
      CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Over.p2PromoteMatchingMissGenSpecExt, xg, g']
    rw [← prevEmpty_sessionAt_eq_sessionRecordAt]
    exact Entails.of_eq (by ac_rfl)
  · exact Or.inr (Or.inl hpan)
  · exact Or.inr (Or.inr (Or.inl hexit))
  · exact Or.inr (Or.inr (Or.inr hoom))

theorem promoteMatchingMissAt_placed_to_ext [LibsignalPlacement] {A : RustAlloc}
    {ext : String → Option (State → State)}
    {coroPtr : BitVec 64} {g : RecordGhost} {recG : SessionGhost}
    {sess : Session (List (BitVec 8))} {msgVer : BitVec 8} {serBytes : List (BitVec 8)}
    (h : PromoteMatchingMissAtPlacedProp A ext coroPtr g recG sess msgVer serBytes) :
    PromoteMatchingMissAtExtPlacedProp A ext coroPtr g recG sess msgVer serBytes := by
  refine subroutine_ok_map h ?_
  intro x R s0 hpre
  dsimp only [withLsCl, p2PromoteMatchingMissAtSpecExt, withVmPreserved,
    CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Over.p2PromoteMatchingMissAtSpecExt] at hpre
  rw [p2_stackAt_split_of_le s0.sp p2OverPromoteMissStackExt p2PromoteMissStack
    (by decide) (by decide)] at hpre
  simp only [sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨hpure, hmem⟩
  refine ⟨x,
    memRegion (s0.sp - BitVec.ofNat 64 p2OverPromoteMissStackExt)
      (p2OverPromoteMissStackExt - p2PromoteMissStack) ∗ R,
    ?_, fun sf hpost => ?_⟩
  · dsimp only [withLsCl, p2PromoteMatchingMissAtSpec, withVmPreserved,
      CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Over.p2PromoteMatchingMissAtSpec]
    simp only [sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨hpure, Satisfies.of_eq hmem (by ac_rfl)⟩
  · dsimp only [withLsCl, p2PromoteMatchingMissAtSpec, p2PromoteMatchingMissAtSpecExt,
      withVmPreserved,
      CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Over.p2PromoteMatchingMissAtSpec,
      CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Over.p2PromoteMatchingMissAtSpecExt]
      at hpost ⊢
    rw [p2_stackAt_split_of_le s0.sp p2OverPromoteMissStackExt p2PromoteMissStack
      (by decide) (by decide)]
    simp only [sepConj_assoc, satisfies_pure_sepConj] at hpost ⊢
    exact ⟨hpost.1, hpost.2.1, hpost.2.2.1, Satisfies.of_eq hpost.2.2.2 (by ac_rfl)⟩

/-! ## Budget-Threaded `<SessionRecord>::promote_state` Contracts (Block 47) -/

/-- Non-free middle allocation envelope of `SessionRecord::promote_state` on empty
`previous_sessions`: output buffer allocation (`≤ 1` event of `n` bytes), `encode_raw`
(`≤ 4 * n + 32` events of `≤ 2 * n + 16` bytes), and optional `RawVec<Vec<u8>>::grow_one`
(`≤ 1` event of 96 bytes), where `n := (encSessionMem (clearPendingGhost G) (clearPending sess)).length`. -/
def PromoteOverAllocMidEnv (G : SessionGhost) (sess : Session (List (BitVec 8))) :
    List AllocEvent → Prop :=
  let n := (encSessionMem (clearPendingGhost G) (clearPending sess)).length
  BoundedRustEvs (4 * n + 34) (2 * n + 96)

/-- Full allocation envelope of `<SessionRecord>::promote_state` on empty `previous_sessions`:
pending/Kyber pre-key drops (`FreeOnlyEvs`), middle allocations (`PromoteOverAllocMidEnv G sess`),
and epilogue `drop_glue<SessionStructure>` (`FreeOnlyEvs`). -/
def PromoteOverEnv (G : SessionGhost) (sess : Session (List (BitVec 8))) :
    List AllocEvent → Prop :=
  SeqEnv FreeOnlyEvs (SeqEnv (PromoteOverAllocMidEnv G sess) FreeOnlyEvs)

theorem PromoteOverEnv.of_steps {G : SessionGhost} {sess : Session (List (BitVec 8))}
    {e1 e2 e3 : List AllocEvent}
    (h1 : FreeOnlyEvs e1)
    (h2 : PromoteOverAllocMidEnv G sess e2)
    (h3 : FreeOnlyEvs e3) :
    PromoteOverEnv G sess (e1 ++ e2 ++ e3) := by
  rw [List.append_assoc]
  exact SeqEnv.append h1 (SeqEnv.append h2 h3)

/-- Envelope-parameterized instance-specialized budget contract for
`<SessionRecord>::promote_state(coroPtr + 0xe0, src)`. -/
def p2PromoteOverAtSpecWithEnv (M : AllocCostModel) (A : RustCliAllocBudget M)
    (lim : BudgetLimits)
    (Env : SessionGhost → Session (List (BitVec 8)) → List AllocEvent → Prop)
    (coroPtr : BitVec 64) (g : RecordGhost) (recG : SessionGhost)
    (sess : Session (List (BitVec 8))) : Spec (P2PromoteOverCallGhost × M.σ) where
  pre := fun (x, st) s =>
    ⌜s.readReg64 .x0 = coroPtr + 0xe0#64 ∧
     s.readReg64 .x1 = x.src ∧
     x.newBs.length = 344 ∧
     FitsEnv M lim st (Env recG sess)⌝ ∗
    prevSessionsEmptyAt A.repAlloc coroPtr g ∗
    sessionStateReprAt A.repAlloc (coroPtr + 0xf8#64) recG sess ∗
    A.pool lim st s ∗
    (x.src ↦ₛ x.newBs) ∗
    stackAt s.sp p2PromoteStackX
  post := fun (x, st) s0 sf =>
    ⌜sf.trace = s0.trace⌝ ∗
    (∃∗ prevCap' : BitVec 64, ∃∗ prevPtr' : BitVec 64,
      ⌜prevCap' ≠ 0#64⌝ ∗
      prevVecAt A.repAlloc (coroPtr + 0xe0#64) prevCap' prevPtr'
        [encSessionMem (clearPendingGhost recG) (clearPending sess)]) ∗
    ((coroPtr + 0xf8#64) ↦ₛ x.newBs) ∗
    (x.src ↦ₛ x.newBs) ∗
    (∃∗ evs : List AllocEvent,
      ⌜Env recG sess evs⌝ ∗ A.pool lim (M.stepEvents evs st) sf) ∗
    stackAt s0.sp p2PromoteStackX

abbrev p2PromoteOverAtSpec (M : AllocCostModel) (A : RustCliAllocBudget M)
    (lim : BudgetLimits) (coroPtr : BitVec 64) (g : RecordGhost)
    (recG : SessionGhost) (sess : Session (List (BitVec 8))) :
    Spec (P2PromoteOverCallGhost × M.σ) :=
  p2PromoteOverAtSpecWithEnv M A lim PromoteOverEnv coroPtr g recG sess

/-- Envelope-parameterized universal budget contract for `<SessionRecord>::promote_state` on empty
`previous_sessions`. -/
def p2PromoteOverGenSpecWithEnv (M : AllocCostModel) (A : RustCliAllocBudget M)
    (lim : BudgetLimits)
    (Env : SessionGhost → Session (List (BitVec 8)) → List AllocEvent → Prop) :
    Spec (P2PromoteOverGenGhost × M.σ) where
  pre := fun (x, st) s =>
    ⌜s.readReg64 .x0 = x.recPtr ∧
     s.readReg64 .x1 = x.src ∧
     x.newBs.length = 344 ∧
     (encSessionMem (clearPendingGhost x.G) (clearPending x.sess)).length < 2 ^ 32 ∧
     FitsEnv M lim st (Env x.G x.sess)⌝ ∗
    vecAt A.repAlloc 24 8 (fun (_ : Unit) _ => emp) x.recPtr x.prevCap x.prevPtr [] ∗
    sessionStateReprAt A.repAlloc (x.recPtr + 0x18#64) x.G x.sess ∗
    A.pool lim st s ∗
    (x.src ↦ₛ x.newBs) ∗
    stackAt s.sp p2PromoteStackX
  post := fun (x, st) s0 sf =>
    ⌜sf.trace = s0.trace⌝ ∗
    (∃∗ prevCap' : BitVec 64, ∃∗ prevPtr' : BitVec 64,
      ⌜prevCap' ≠ 0#64⌝ ∗
      prevVecAt A.repAlloc x.recPtr prevCap' prevPtr'
        [encSessionMem (clearPendingGhost x.G) (clearPending x.sess)]) ∗
    ((x.recPtr + 0x18#64) ↦ₛ x.newBs) ∗
    (x.src ↦ₛ x.newBs) ∗
    (∃∗ evs : List AllocEvent,
      ⌜Env x.G x.sess evs⌝ ∗ A.pool lim (M.stepEvents evs st) sf) ∗
    stackAt s0.sp p2PromoteStackX

abbrev p2PromoteOverGenSpec (M : AllocCostModel) (A : RustCliAllocBudget M)
    (lim : BudgetLimits) : Spec (P2PromoteOverGenGhost × M.σ) :=
  p2PromoteOverGenSpecWithEnv M A lim PromoteOverEnv

/-- Relocatable `[LibsignalPlacement]` envelope-parameterized contract for
`SessionRecord::promote_state` at block 47 (`lsmpl.base 47`). -/
def PromoteOverAtPlacedWithEnvProp [LibsignalPlacement] (M : AllocCostModel)
    (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (Env : SessionGhost → Session (List (BitVec 8)) → List AllocEvent → Prop)
    (ext : String → Option (State → State))
    (coroPtr : BitVec 64) (g : RecordGhost) (recG : SessionGhost)
    (sess : Session (List (BitVec 8))) : Prop :=
  subroutine_ok (lsProg_518 ext) (lsmpl.base 47)
    (withLsCl lsmpl (p2PromoteOverAtSpecWithEnv M A lim Env coroPtr g recG sess))

abbrev PromoteOverAtPlacedProp [LibsignalPlacement] (M : AllocCostModel)
    (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (ext : String → Option (State → State))
    (coroPtr : BitVec 64) (g : RecordGhost) (recG : SessionGhost)
    (sess : Session (List (BitVec 8))) : Prop :=
  PromoteOverAtPlacedWithEnvProp M A lim PromoteOverEnv ext coroPtr g recG sess

def PromoteOverGenPlacedWithEnvProp [LibsignalPlacement] (M : AllocCostModel)
    (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (Env : SessionGhost → Session (List (BitVec 8)) → List AllocEvent → Prop)
    (ext : String → Option (State → State)) : Prop :=
  subroutine_ok (lsProg_518 ext) (lsmpl.base 47)
    (withLsCl lsmpl (p2PromoteOverGenSpecWithEnv M A lim Env))

abbrev PromoteOverGenPlacedProp [LibsignalPlacement] (M : AllocCostModel)
    (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (ext : String → Option (State → State)) : Prop :=
  PromoteOverGenPlacedWithEnvProp M A lim PromoteOverEnv ext

theorem promoteOverAt_of_gen_withEnv {M : AllocCostModel} {A : RustCliAllocBudget M}
    {lim : BudgetLimits} {prog : Program} {entry : BitVec 64}
    {Env : SessionGhost → Session (List (BitVec 8)) → List AllocEvent → Prop}
    (hGen : subroutine_ok prog entry (p2PromoteOverGenSpecWithEnv M A lim Env))
    (coroPtr : BitVec 64) (g : RecordGhost) (recG : SessionGhost)
    (sess : Session (List (BitVec 8)))
    (hlen : (encSessionMem (clearPendingGhost recG) (clearPending sess)).length < 2 ^ 32) :
    subroutine_ok prog entry
      (p2PromoteOverAtSpecWithEnv M A lim Env coroPtr g recG sess) := by
  refine subroutine_ok_outcome_intro fun ⟨x, st⟩ R s0 hpc hrun hpre halign => ?_
  let xg : P2PromoteOverGenGhost :=
    ⟨coroPtr + 0xe0#64, x.src, g.prevCap, g.prevPtr, recG, sess, x.newBs⟩
  have hrec_eq :
      prevSessionsEmptyAt A.repAlloc coroPtr g ∗
        sessionStateReprAt A.repAlloc (coroPtr + 0xf8#64) recG sess =
      vecAt A.repAlloc 24 8 (fun (_ : Unit) _ => emp) (coroPtr + 0xe0#64) g.prevCap g.prevPtr [] ∗
      sessionStateReprAt A.repAlloc (coroPtr + 0xe0#64 + 0x18#64) recG sess := by
    rw [prevEmpty_sessionAt_eq_sessionRecordAt]
    rfl
  have hpre' : s0.mem ⊨ (p2PromoteOverGenSpecWithEnv M A lim Env).pre (xg, st) s0 ∗ R := by
    refine Satisfies.mono (sepConj_mono_left ?_) hpre
    dsimp only [p2PromoteOverAtSpecWithEnv, p2PromoteOverGenSpecWithEnv, xg]
    refine Entails.pure_left fun ⟨h0, h1, hnb, hfit⟩ => ?_
    have hre :
        prevSessionsEmptyAt A.repAlloc coroPtr g ∗
          (sessionStateReprAt A.repAlloc (coroPtr + 0xf8#64) recG sess ∗
            (A.pool lim st s0 ∗ ((x.src ↦ₛ x.newBs) ∗ stackAt s0.sp p2PromoteStackX))) =
        (prevSessionsEmptyAt A.repAlloc coroPtr g ∗
          sessionStateReprAt A.repAlloc (coroPtr + 0xf8#64) recG sess) ∗
            (A.pool lim st s0 ∗ ((x.src ↦ₛ x.newBs) ∗ stackAt s0.sp p2PromoteStackX)) := by
      ac_rfl
    rw [hre, hrec_eq]
    exact Entails.pure_right ⟨h0, h1, hnb, hlen, hfit⟩ (Entails.of_eq (by ac_rfl))
  refine hGen.mono_outcome (xg, st) R s0 hpc hrun hpre' halign ?_
  rintro sf (⟨hret, hcs, hpost⟩ | hpan | hexit | hoom)
  · refine Or.inl ⟨hret, hcs, ?_⟩
    refine Satisfies.mono (sepConj_mono_left ?_) hpost
    dsimp only [p2PromoteOverAtSpecWithEnv, p2PromoteOverGenSpecWithEnv, xg]
    simp only [BitVec.add_assoc, BitVec.reduceAdd]
    exact Entails.of_eq (by ac_rfl)
  · exact Or.inr (Or.inl hpan)
  · exact Or.inr (Or.inr (Or.inl hexit))
  · exact Or.inr (Or.inr (Or.inr hoom))

theorem promoteOverAt_of_gen {M : AllocCostModel} {A : RustCliAllocBudget M}
    {lim : BudgetLimits} {prog : Program} {entry : BitVec 64}
    (hGen : subroutine_ok prog entry (p2PromoteOverGenSpec M A lim))
    (coroPtr : BitVec 64) (g : RecordGhost) (recG : SessionGhost)
    (sess : Session (List (BitVec 8)))
    (hlen : (encSessionMem (clearPendingGhost recG) (clearPending sess)).length < 2 ^ 32) :
    subroutine_ok prog entry (p2PromoteOverAtSpec M A lim coroPtr g recG sess) :=
  promoteOverAt_of_gen_withEnv hGen coroPtr g recG sess hlen

theorem promoteOverAt_placed_of_gen_withEnv [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {Env : SessionGhost → Session (List (BitVec 8)) → List AllocEvent → Prop}
    {ext : String → Option (State → State)}
    (hGen : PromoteOverGenPlacedWithEnvProp M A lim Env ext)
    (coroPtr : BitVec 64) (g : RecordGhost) (recG : SessionGhost)
    (sess : Session (List (BitVec 8)))
    (hlen : (encSessionMem (clearPendingGhost recG) (clearPending sess)).length < 2 ^ 32) :
    PromoteOverAtPlacedWithEnvProp M A lim Env ext coroPtr g recG sess := by
  refine subroutine_ok_outcome_intro fun ⟨x, st⟩ R s0 hpc hrun hpre halign => ?_
  let xg : P2PromoteOverGenGhost :=
    ⟨coroPtr + 0xe0#64, x.src, g.prevCap, g.prevPtr, recG, sess, x.newBs⟩
  have hrec_eq :
      prevSessionsEmptyAt A.repAlloc coroPtr g ∗
        sessionStateReprAt A.repAlloc (coroPtr + 0xf8#64) recG sess =
      vecAt A.repAlloc 24 8 (fun (_ : Unit) _ => emp) (coroPtr + 0xe0#64) g.prevCap g.prevPtr [] ∗
      sessionStateReprAt A.repAlloc (coroPtr + 0xe0#64 + 0x18#64) recG sess := by
    rw [prevEmpty_sessionAt_eq_sessionRecordAt]
    rfl
  have hpre' : s0.mem ⊨
      (withLsCl lsmpl (p2PromoteOverGenSpecWithEnv M A lim Env)).pre (xg, st) s0 ∗ R := by
    refine Satisfies.mono (sepConj_mono_left (sepConj_mono_left ?_)) hpre
    dsimp only [p2PromoteOverAtSpecWithEnv, p2PromoteOverGenSpecWithEnv, xg]
    refine Entails.pure_left fun ⟨h0, h1, hnb, hfit⟩ => ?_
    have hre :
        prevSessionsEmptyAt A.repAlloc coroPtr g ∗
          (sessionStateReprAt A.repAlloc (coroPtr + 0xf8#64) recG sess ∗
            (A.pool lim st s0 ∗ ((x.src ↦ₛ x.newBs) ∗ stackAt s0.sp p2PromoteStackX))) =
        (prevSessionsEmptyAt A.repAlloc coroPtr g ∗
          sessionStateReprAt A.repAlloc (coroPtr + 0xf8#64) recG sess) ∗
            (A.pool lim st s0 ∗ ((x.src ↦ₛ x.newBs) ∗ stackAt s0.sp p2PromoteStackX)) := by
      ac_rfl
    rw [hre, hrec_eq]
    exact Entails.pure_right ⟨h0, h1, hnb, hlen, hfit⟩ (Entails.of_eq (by ac_rfl))
  refine hGen.mono_outcome (xg, st) R s0 hpc hrun hpre' halign ?_
  rintro sf (⟨hret, hcs, hpost⟩ | hpan | hexit | hoom)
  · refine Or.inl ⟨hret, hcs, ?_⟩
    refine Satisfies.mono (sepConj_mono_left (sepConj_mono_right ?_)) hpost
    dsimp only [p2PromoteOverAtSpecWithEnv, p2PromoteOverGenSpecWithEnv, xg]
    simp only [BitVec.add_assoc, BitVec.reduceAdd]
    exact Entails.of_eq (by ac_rfl)
  · exact Or.inr (Or.inl hpan)
  · exact Or.inr (Or.inr (Or.inl hexit))
  · exact Or.inr (Or.inr (Or.inr hoom))

theorem promoteOverAt_placed_of_gen [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)}
    (hGen : PromoteOverGenPlacedProp M A lim ext)
    (coroPtr : BitVec 64) (g : RecordGhost) (recG : SessionGhost)
    (sess : Session (List (BitVec 8)))
    (hlen : (encSessionMem (clearPendingGhost recG) (clearPending sess)).length < 2 ^ 32) :
    PromoteOverAtPlacedProp M A lim ext coroPtr g recG sess :=
  promoteOverAt_placed_of_gen_withEnv hGen coroPtr g recG sess hlen

theorem promoteOverGenPlacedWithEnv_mono [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {Env₁ Env₂ : SessionGhost → Session (List (BitVec 8)) → List AllocEvent → Prop}
    {ext : String → Option (State → State)}
    (himp : ∀ G sess evs, Env₁ G sess evs → Env₂ G sess evs)
    (h : PromoteOverGenPlacedWithEnvProp M A lim Env₁ ext) :
    PromoteOverGenPlacedWithEnvProp M A lim Env₂ ext := by
  refine subroutine_ok_mono h
    (fun ⟨x, st⟩ _ s0 hp => ?_)
    (fun ⟨x, st⟩ _ s0 sf hq => ?_)
  · dsimp only [withLsCl, p2PromoteOverGenSpecWithEnv] at hp ⊢
    rw [sepConj_assoc, sepConj_assoc, satisfies_pure_sepConj] at hp ⊢
    rcases hp with ⟨⟨h0, h1, hnb, hlen, hfit⟩, hmem⟩
    exact ⟨⟨h0, h1, hnb, hlen, hfit.mono (himp x.G x.sess)⟩, hmem⟩
  · dsimp only [withLsCl, p2PromoteOverGenSpecWithEnv] at hq ⊢
    refine Satisfies.mono (sepConj_mono_left ?_) hq
    refine sepConj_mono_right (sepConj_mono_right
      (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_left ?_)))))
    refine Entails.sepExists_elim fun evs => Entails.sepExists_right evs ?_
    exact Entails.pure_left fun hevs => Entails.pure_right (himp x.G x.sess evs hevs) (Entails.refl _)

theorem promoteOverAtPlacedWithEnv_mono [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {Env₁ Env₂ : SessionGhost → Session (List (BitVec 8)) → List AllocEvent → Prop}
    {ext : String → Option (State → State)}
    {coroPtr : BitVec 64} {g : RecordGhost} {recG : SessionGhost}
    {sess : Session (List (BitVec 8))}
    (himp : ∀ G sess evs, Env₁ G sess evs → Env₂ G sess evs)
    (h : PromoteOverAtPlacedWithEnvProp M A lim Env₁ ext coroPtr g recG sess) :
    PromoteOverAtPlacedWithEnvProp M A lim Env₂ ext coroPtr g recG sess := by
  refine subroutine_ok_mono h
    (fun ⟨x, st⟩ _ s0 hp => ?_)
    (fun ⟨x, st⟩ _ s0 sf hq => ?_)
  · dsimp only [withLsCl, p2PromoteOverAtSpecWithEnv] at hp ⊢
    rw [sepConj_assoc, sepConj_assoc, satisfies_pure_sepConj] at hp ⊢
    rcases hp with ⟨⟨h0, h1, hnb, hfit⟩, hmem⟩
    exact ⟨⟨h0, h1, hnb, hfit.mono (himp recG sess)⟩, hmem⟩
  · dsimp only [withLsCl, p2PromoteOverAtSpecWithEnv] at hq ⊢
    refine Satisfies.mono (sepConj_mono_left ?_) hq
    refine sepConj_mono_right (sepConj_mono_right
      (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_left ?_)))))
    refine Entails.sepExists_elim fun evs => Entails.sepExists_right evs ?_
    exact Entails.pure_left fun hevs => Entails.pure_right (himp recG sess evs hevs) (Entails.refl _)

end LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Over.StageP2DefsBudget
