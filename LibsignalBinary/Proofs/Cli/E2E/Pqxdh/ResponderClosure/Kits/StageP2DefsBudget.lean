/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Heap.IfaceBudget
public import LibsignalBinary.Heap.SpecBudget
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.DecryptPq.Trap.SameAccount
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.Reloc.DropSessionStructure3
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Fetch
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP2Defs
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderStore.SessionRecordCallees
public import LibsignalBinary.Proofs.E2E.Pqxdh.ResponderClosure.AssemblyP2a
public import LibsignalBinary.Proofs.E2E.Pqxdh.ResponderClosure.AssemblyP2b
public import LibsignalBinary.Proofs.E2E.Pqxdh.ResponderCore.InitBobCut
public import LibsignalBinary.Proofs.E2E.Pqxdh.ResponderStore.KeyPairCallees
public import LibsignalBinary.Proofs.PublicApi.StoreKit.IdentitySelfStoreKit
public import LibsignalBinary.Proofs.PublicApi.StoreKit.KyberPreKeyStoreKit
public import LibsignalBinary.Proofs.PublicApi.StoreKit.SignedPreKeyStoreKit
public import LibsignalBinary.Proofs.SpqrV1.Top.InitialState.Defs
import Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic
import LibsignalBinary.Proofs.Common.SharedHelpers
meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep
import LibsignalBinary.Proofs.E2E.Pqxdh.ResponderClosure.AssemblyP2bAux
import LibsignalBinary.Proofs.E2E.Pqxdh.ResponderClosure.StoreEmpty

/-!
# Budget-Threaded Stage P2 Shared Helpers

Provides `RustCliAllocBudget M` generic-capacity `vecU8` helpers and `VmPreserved`-augmented
0-allocation callee contracts (`memcpy`, `promote_state`, `is_same_account`) with stack-lift
bridges.
-/

@[expose] public section

set_option autoImplicit false

namespace LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP2DefsBudget

open Arm64 ProofLib SepProp
open CryptoGames CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open CryptoVerification CryptoVerification.RustHeap
open CryptoVerification.RecordCodecs CryptoVerification.RecordCodecsBinary
open CryptoVerification.LibsignalSession CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchet CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalTripleRatchet.Getters
open CryptoVerification.LibsignalTripleRatchet.FromRecordCallees
open CryptoVerification.LibsignalPublicApi CryptoVerification.LibsignalPublicApiRepr
open CryptoVerification.LibsignalPublicApi.StoreSession
open CryptoVerification.LibsignalPublicApi.StoreKit
open CryptoVerification.LibsignalPublicApi.StoreKit.Identity
open CryptoVerification.LibsignalPublicApi.StoreKit.IdentitySelf
open CryptoVerification.E2E.Bin
open CryptoVerification.E2E.Pqxdh
open CryptoVerification.E2E.Pqxdh.Initiator
open CryptoVerification.E2E.Pqxdh.WireEntries
open CryptoVerification.E2E.Pqxdh.ResponderStore
open CryptoVerification.E2E.Pqxdh.ResponderCore
open CryptoVerification.E2E.Pqxdh.ResponderClosure
open CryptoVerification.Cli.E2E.Pqxdh.ResponderStore
open LibsignalBinary.Heap (AllocCostModel RustCliAllocBudget)
open LibsignalBinary.Heap.SpecBudget (withVmPreserved)

export CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Kits (
  stageP2PureAndErrStack spkGetCallStack kpkGetCallStack pkGetCallStack
  selfKpCallStack selfRegIdCallStack stageP2Sub1To4Stack stageP2Sub56Stack stageP2CallStack
  p2_stackAt_split_of_le p2_stageP2bV1_le_pure p2_stageP2b_le_pure p2_stageP2a_le_pure
  p2_alloc_le_pure p2_dropSS3_le_pure p2_pure_le_sub1To4 p2_pure_le_sub56
  p2_sub1To4_le_stageP2 p2_sub56_le_stageP2 p2_pure_le_stageP2
  stageP2PureAndErrStack4K spkGetCallStack4K kpkGetCallStack4K pkGetCallStack4K
  selfKpCallStack4K selfRegIdCallStack4K stageP2Sub1To4Stack4K stageP2Sub56Stack4K
  stageP2CallStack4K
  p2_pure_le_pure4K p2_bobExt_le_pure4K p2_pure4K_le_sub1To4_4K p2_pure4K_le_sub56_4K
  p2_sub1To4_4K_le_stageP2_4K p2_sub56_4K_le_stageP2_4K p2_pure4K_le_stageP2_4K
  p2_sub1To4_le_4K p2_sub56_le_4K p2_callStack_le_4K
  p2_calleeSavedVRegs_setPC_pre p2_calleeSavedVRegs_setMem_setPC_pre
  p2_calleeSavedVRegs_writeVReg128_0 p2_calleeSavedVRegs_writeVReg128_1
  p2_calleeSavedVRegs_writeVReg128_2 p2_calleeSavedVRegs_writeVReg128_3
  p2_calleeSavedVRegs_writeVReg128_4 p2_calleeSavedVRegs_writeVReg128_5
  p2_calleeSavedVRegs_writeVReg128_6 p2_calleeSavedVRegs_writeVReg128_7
  p2_calleeSavedVRegs_writeVReg64_0 p2_calleeSavedVRegs_writeVReg64_1
  p2_cond_ne_adds64_of_ne_neg3 p2_cond_ne_adds64_of_ne_neg2
  p2_cond_eq_adds64_of_ne_neg1 p2_zext64_trunc32_id
  p2PollCellsAt p2_words5_repack p2_speWordsAt_eq_pollCellsAt p2CoroDoneAt
  p2_vecBuf_dealloc_nonzero
  p2BobSpqrParams p2BobSpqrVecBuf p2BobHead144Bv8V1 p2BobSession344Bv8V1
  p2BobSessHead56Bv8 p2BobSessMid280V1 p2BobSessRegIdsV1
  p2BobSessHead56Bv8_length p2BobSessMid280V1_length p2BobSession344Bv8V1_eq_head56_mid280V1
)

/-! ## 1. `RustCliAllocBudget M` Generic-Capacity `vecU8` Helpers -/

/-- Heap part of a `Vec<u8>` with capacity `cap` at `ptr` holding `bs` over `A.repAlloc`. -/
def p2BobSpqrVecBufBudget {M : AllocCostModel} (A : RustCliAllocBudget M)
    (cap ptr : BitVec 64) (bs : List (BitVec 8)) : SepProp :=
  CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Kits.p2BobSpqrVecBuf A.repAlloc cap ptr bs

/-- Rejoin a non-empty `vecU8` buffer into `A.repAlloc.live ptr cap.toNat 1 ∗ memRegion ptr cap.toNat`
for `__rust_dealloc`. -/
theorem p2_vecBuf_dealloc_nonzero_budget {M : AllocCostModel} (A : RustCliAllocBudget M)
    (cap ptr : BitVec 64) (xs : List (BitVec 8))
    (hcap_ne : cap ≠ 0#64) (hxs_le : xs.length ≤ cap.toNat) :
    (if cap = 0 then emp
     else A.repAlloc.live ptr cap.toNat 1 ∗ (ptr ↦ₛ xs) ∗
       memRegion (ptr + BitVec.ofNat 64 xs.length) (cap.toNat - xs.length)) ⊢
      A.repAlloc.live ptr cap.toNat 1 ∗ memRegion ptr cap.toNat :=
  CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Kits.p2_vecBuf_dealloc_nonzero
    A.repAlloc cap ptr xs hcap_ne hxs_le

/-! ## 2. `VmPreserved`-Augmented `0`-Allocation Callee Contracts & Stack-Lift Bridges -/

/-- `VmPreserved`-augmented 4 KiB-stacked `memcpy` contract (`0` allocations). -/
def p2Memcpy4KSpec : Spec (BitVec 64 × BitVec 64 × List (BitVec 8)) :=
  withVmPreserved CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Kits.p2Memcpy4KSpec

/-- Lift `withVmPreserved framelessMemcpySpec` (`framelessMemcpyBudgetSpec`) to `p2Memcpy4KSpec`. -/
theorem p2_framelessMemcpy_to_4K {prog : Program} {entry : BitVec 64}
    (h : subroutine_ok prog entry (withVmPreserved framelessMemcpySpec)) :
    subroutine_ok prog entry p2Memcpy4KSpec := by
  refine subroutine_ok_map h ?_
  rintro ⟨dst, src, bs⟩ R s0 hpre
  dsimp only [p2Memcpy4KSpec, withVmPreserved,
    CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Kits.p2Memcpy4KSpec, libcMemcpySpec] at hpre
  simp only [sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨hpure, hmem⟩
  refine ⟨(dst, src, bs), stackAt s0.sp allocHookStack ∗ R, ?_, fun sf hpost => ?_⟩
  · dsimp only [withVmPreserved, framelessMemcpySpec]
    simp only [sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨hpure, Satisfies.of_eq hmem (by ac_rfl)⟩
  · dsimp only [p2Memcpy4KSpec, withVmPreserved, framelessMemcpySpec,
      CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Kits.p2Memcpy4KSpec] at hpost ⊢
    simp only [sepConj_assoc, satisfies_pure_sepConj] at hpost ⊢
    exact ⟨hpost.1, hpost.2.1, Satisfies.of_eq hpost.2.2 (by ac_rfl)⟩

/-- `VmPreserved`-augmented `SessionRecord::promote_state` (empty-record fast path, `96` B stack). -/
def promoteStateEmptySpec : Spec (BitVec 64 × BitVec 64 × List (BitVec 8)) :=
  withVmPreserved CryptoVerification.E2E.Pqxdh.ResponderStore.promoteStateEmptySpec

/-- `VmPreserved`-augmented 4 KiB-stacked `SessionRecord::promote_state` (empty-record fast path). -/
def promoteStateEmpty4KSpec : Spec (BitVec 64 × BitVec 64 × List (BitVec 8)) :=
  withVmPreserved CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Kits.promoteStateEmpty4KSpec

/-- Lift `promoteStateEmptySpec` (`96` B stack) to `promoteStateEmpty4KSpec` (`allocHookStack = 4096` B). -/
theorem promoteStateEmptySpec_to_4K {prog : Program} {entry : BitVec 64}
    (h : subroutine_ok prog entry promoteStateEmptySpec) :
    subroutine_ok prog entry promoteStateEmpty4KSpec := by
  refine subroutine_ok_map h ?_
  rintro ⟨recPtr, srcPtr, bs⟩ R s0 hpre
  dsimp only [promoteStateEmpty4KSpec, withVmPreserved,
    CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Kits.promoteStateEmpty4KSpec] at hpre
  rw [stackAt_promote_state_eq s0.sp] at hpre
  simp only [sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨hpure, hmem⟩
  refine ⟨(recPtr, srcPtr, bs), stackAt (s0.sp - 96#64) (allocHookStack - 96) ∗ R,
    ?_, fun sf hpost => ?_⟩
  · dsimp only [promoteStateEmptySpec, withVmPreserved,
      CryptoVerification.E2E.Pqxdh.ResponderStore.promoteStateEmptySpec]
    simp only [sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨hpure, Satisfies.of_eq hmem (by ac_rfl)⟩
  · dsimp only [promoteStateEmptySpec, promoteStateEmpty4KSpec, withVmPreserved,
      CryptoVerification.E2E.Pqxdh.ResponderStore.promoteStateEmptySpec,
      CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Kits.promoteStateEmpty4KSpec] at hpost ⊢
    rw [stackAt_promote_state_eq s0.sp]
    simp only [sepConj_assoc, satisfies_pure_sepConj] at hpost ⊢
    exact ⟨hpost.1, hpost.2.1, Satisfies.of_eq hpost.2.2 (by ac_rfl)⟩

/-- `VmPreserved`-augmented `<IdentityKey>::is_same_account` contract under `DistinctSid` (`0` allocations). -/
def isSameAccountDistinctSpec (A : RustAlloc) (parse : UuidParser) :
    Spec IsSameAccountDistinctGhost :=
  withVmPreserved (CryptoVerification.E2E.Pqxdh.WireEntries.isSameAccountDistinctSpec A parse)

/-- `VmPreserved`-augmented stack-parameterized `<IdentityKey>::is_same_account` contract under `DistinctSid`. -/
def isSameAccountDistinctAtSpec (A : RustAlloc) (parse : UuidParser) (stk : Nat) :
    Spec (BitVec 64 × IdentityKey × BitVec 64 × AddrGhost ×
      BitVec 64 × IdentityKey × BitVec 64 × AddrGhost) :=
  withVmPreserved
    (CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Kits.isSameAccountDistinctAtSpec A parse stk)

/-- `VmPreserved`-augmented `isSameAccountDistinctStackExt`-stacked `<IdentityKey>::is_same_account` contract. -/
def isSameAccountDistinctSpecExt (A : RustAlloc) (parse : UuidParser) :
    Spec (BitVec 64 × IdentityKey × BitVec 64 × AddrGhost ×
      BitVec 64 × IdentityKey × BitVec 64 × AddrGhost) :=
  withVmPreserved
    (CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.isSameAccountDistinctSpecExt A parse)

theorem isSameAccountDistinctSpec_to_ext {prog : Program} {entry : BitVec 64}
    {A : RustAlloc} {parse : UuidParser}
    (h : subroutine_ok prog entry (isSameAccountDistinctSpec A parse)) :
    subroutine_ok prog entry (isSameAccountDistinctSpecExt A parse) := by
  refine subroutine_ok_map h ?_
  rintro ⟨lIkA, lIk, locA, loc, rIkA, rIk, remA, rem⟩ R s0 hpre
  dsimp only [isSameAccountDistinctSpecExt, withVmPreserved,
    CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.isSameAccountDistinctSpecExt] at hpre
  rw [p2_stackAt_split_of_le s0.sp
    CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.isSameAccountDistinctStackExt
    isSameAccountDistinctStack (by decide) (by decide)] at hpre
  simp only [sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨hpure, hmem⟩
  refine ⟨({ localIkA := lIkA, localIk := lIk, locA := locA, loc := loc,
             remoteIkA := rIkA, remoteIk := rIk, remA := remA, rem := rem } :
            IsSameAccountDistinctGhost),
    memRegion (s0.sp - BitVec.ofNat 64
      CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.isSameAccountDistinctStackExt)
      (CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.isSameAccountDistinctStackExt -
        isSameAccountDistinctStack) ∗ R, ?_, fun sf hpost => ?_⟩
  · dsimp only [isSameAccountDistinctSpec, withVmPreserved,
      CryptoVerification.E2E.Pqxdh.WireEntries.isSameAccountDistinctSpec]
    simp only [sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨hpure, Satisfies.of_eq hmem (by ac_rfl)⟩
  · dsimp only [isSameAccountDistinctSpec, isSameAccountDistinctSpecExt, withVmPreserved,
      CryptoVerification.E2E.Pqxdh.WireEntries.isSameAccountDistinctSpec,
      CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.isSameAccountDistinctSpecExt] at hpost ⊢
    rw [p2_stackAt_split_of_le s0.sp
      CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.isSameAccountDistinctStackExt
      isSameAccountDistinctStack (by decide) (by decide)]
    simp only [sepConj_assoc, satisfies_pure_sepConj] at hpost ⊢
    exact ⟨hpost.1, hpost.2.1, Satisfies.of_eq hpost.2.2 (by ac_rfl)⟩

end LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP2DefsBudget
