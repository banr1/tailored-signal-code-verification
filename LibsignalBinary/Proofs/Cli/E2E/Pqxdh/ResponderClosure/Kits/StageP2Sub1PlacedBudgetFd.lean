/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP2Sub1PlacedBudget
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP2DefsPlacedBudgetFd
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP2CalleesPlacedBudgetFd

/-!
# Descriptor-Threaded Relocatable Stage P2 Substage P2.1

Lifts budget-threaded placed Substage P2.1 (`+0x0868 → +0x0f14`) via `AllocWithFds.withFds A` to
preserve `FdsGe3Closed`.
-/

@[expose] public section

set_option autoImplicit false

namespace LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP2Sub1PlacedBudgetFd

open Arm64 Arm64.Process ProofLib SepProp
open CryptoGames.LibsignalSession (PublicKey ShaCompress)
open CryptoVerification (LibsignalPlacement lsmpl)
open CryptoVerification.LibsignalPublicApi.StoreKit (LibsignalCodeRoLoaded SignedPreKeyStoreSpec)
open CryptoVerification.E2E.Pqxdh.Initiator (AcceptKeysInput DRKey Primitives)
open CryptoVerification.E2E.Pqxdh.ResponderClosure (
  processPrekeyActive10At sessionRecordEmptyHeaderAt
)
open CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Kits (
  stageP1EntryPlaced stageP1ProgPlaced stageP2PureAndErrStack
)
open LibsignalBinary.Heap (
  AllocCostModel AllocEvent BudgetLimits FitsEnv RustCliAllocBudget
)
open LibsignalBinary.Proofs.PublicApi.StoreKit.SignedPreKeyStoreKitBudget (
  SignedPreKeyStoreBudgetEnv
)
open LibsignalBinary.Proofs.PublicApi.StoreKit.PlacedBudget (
  SignedPreKeyStoreKitPlacedOkFds
)
open LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP2DefsPlacedBudget (
  StageP2ClosureHooksPlaced
)
open LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP2DefsPlacedBudgetFd (
  spkKitFds_toWithFds
  stageP2ClosureHooks_toWithFds
  withFds_pool_eq_of_fdsGe3Closed
)
open LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP2CalleesPlacedBudgetFd (
  StageP2PureCalleesPlaced4KOfEnvFd StageP2PureCalleesPlacedOfEnvFd
)
open LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP2Sub1PlacedBudget (
  P2Sub1Env p2Sub1Events stageP2_sub1_kits_ext_placed stageP2_sub1_kits_placed
)
open LibsignalBinary.Proofs.SignalSession.Cli.F3.HRead.ReadFileBudgetPlaced (
  FdsGe3Closed
)
open LibsignalBinary.Proofs.SignalSession.Cli.Heap.AllocWithFds (
  withFds withFds_live withFds_pool_enforced
)

/-- `FdsGe3Closed`-preserving Substage P2.1 (`+0x0868 -> +0x0f14`, `4K` pure callees). -/
theorem stageP2_sub1_kits_ext_placed_fd [LibsignalPlacement]
    {M : AllocCostModel} {P : Primitives} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    (henf : lim.enforced = true)
    {F : ShaCompress} {BobV1Env : AcceptKeysInput → DRKey → List AllocEvent → Prop}
    {AcceptErrEnv : AcceptKeysInput → List AllocEvent → Prop}
    {Qp : State → SepProp → Prop}
    (ext : String → Option (State → State))
    (hH : StageP2ClosureHooksPlaced A lim ext)
    (hPure : StageP2PureCalleesPlaced4KOfEnvFd P A lim F BobV1Env AcceptErrEnv ext)
    (spkKit : SignedPreKeyStoreSpec A.repAlloc 0#64)
    (spkEnv : SignedPreKeyStoreBudgetEnv spkKit)
    (hspk_fds : spkKit.fdsOk = FdsGe3Closed)
    (hspkOk : SignedPreKeyStoreKitPlacedOkFds A lim spkKit spkEnv ext)
    (stk : Nat)
    (hstk_pure : stageP2PureAndErrStack ≤ stk)
    (hstk_shim : spkKit.getShimStack ≤ stk)
    (hstk_lt : stk ≤ 2 ^ 64)
    (st : M.σ)
    (s0 s : State)
    (coroPtr msgPtr remoteAddrPtr localAddrPtr
     idStorePtr idStoreVt preKeyStorePtr preKeyStoreVt
     spkStorePtr kyberStorePtr kyberStoreVt : BitVec 64)
    (baseKey : PublicKey) (spkId : BitVec 32) (b_4f1 : BitVec 8)
    (hfits : FitsEnv M lim st (P2Sub1Env spkKit.getBoxSize))
    (hfds : FdsGe3Closed s.fs)
    (hCode : LibsignalCodeRoLoaded lsmpl s.mem)
    (hpc : s.pc = stageP1EntryPlaced + 0x868#64)
    (hrun : s.status = .Running)
    (hsp_align : (s.sp &&& 15#64 == 0#64) = true)
    (hvregs : calleeSavedVRegs s = calleeSavedVRegs s0)
    (hx8 : s.readReg64 .x8 = kyberStorePtr) (hx9 : s.readReg64 .x9 = msgPtr)
    (hx10 : s.readReg64 .x10 = kyberStoreVt) (hx11 : s.readReg64 .x11 = preKeyStorePtr)
    (hx12 : s.readReg64 .x12 = remoteAddrPtr) (hx13 : s.readReg64 .x13 = preKeyStoreVt)
    (hx14 : s.readReg64 .x14 = localAddrPtr) (hx15 : s.readReg64 .x15 = idStorePtr)
    (hx16 : s.readReg64 .x16 = idStoreVt) (hx19 : s.readReg64 .x19 = coroPtr)
    (hx22 : s.readReg64 .x22 = spkStorePtr) (hx23 : s.readReg64 .x23 = coroPtr + 0xe0#64)
    (hx24 : s.readReg64 .x24 = spkKit.spk_vt) :
    SepWPp (stageP1ProgPlaced ext) (stageP1EntryPlaced + 0xf14#64) s
      (cells (coroPtr + 0x3f8#64) 6 ∗
       cells (coroPtr + 0x468#64) 4 ∗
       ((coroPtr + 0x4f1#64) ↦₈ b_4f1) ∗
       sessionRecordEmptyHeaderAt (coroPtr + 0xe0#64) ∗
       ((msgPtr + 0xa8#64) ↦ₛ baseKey.bytes.toList) ∗
       ((msgPtr + 0xec#64) ↦₃₂ spkId) ∗
       ((msgPtr + 0xf0#64) ↦₈ 4#8) ∗
       memRegion (s.sp + 0x3e0#64) 9 ∗
       ((spkKit.spk_vt + 0x18#64) ↦₆₄ᵣ (0#64 + spkKit.getShimOff)) ∗
       A.pool lim st s ∗
       stackAt s.sp stk)
      (fun sf P_f =>
        (P_f ⊢
          ∃∗ spkFutPtr : BitVec 64,
            ⌜sf.readReg64 .x0 = spkFutPtr ∧
              sf.readReg64 .x1 = 0#64 + spkKit.getFutVtOff ∧
              spkFutPtr ≠ 0#64 ∧
              spkFutPtr.toNat % 8 = 0⌝ ∗
            processPrekeyActive10At coroPtr msgPtr remoteAddrPtr localAddrPtr
              idStorePtr idStoreVt preKeyStorePtr preKeyStoreVt
              kyberStorePtr kyberStoreVt ∗
            ((coroPtr + 0x4f1#64) ↦₈ 0#8) ∗
            sessionRecordEmptyHeaderAt (coroPtr + 0xe0#64) ∗
            ((msgPtr + 0xa8#64) ↦ₛ baseKey.bytes.toList) ∗
            ((msgPtr + 0xec#64) ↦₃₂ spkId) ∗
            ((msgPtr + 0xf0#64) ↦₈ 4#8) ∗
            memRegion (s.sp + 0x3e0#64) 9 ∗
            ((spkKit.spk_vt + 0x18#64) ↦₆₄ᵣ (0#64 + spkKit.getShimOff)) ∗
            A.live spkFutPtr spkKit.getBoxSize 8 ∗
            spkKit.getBoxAt spkFutPtr spkStorePtr spkId 0#8 ∗
            (⌜FdsGe3Closed sf.fs⌝ ∗ A.pool lim (M.stepEvents (p2Sub1Events spkKit.getBoxSize) st) sf) ∗
            stackAt s.sp stk) ∧
        sf.sp = s.sp ∧ sf.trace = s.trace ∧ sf.readReg64 .x19 = coroPtr ∧
        sf.readReg64 .x22 = spkStorePtr ∧ sf.readReg64 .x23 = 0#64 ∧
        sf.readReg64 .x24 = spkKit.spk_vt ∧ sf.readReg64 .x25 = s.sp + 0x210#64 ∧
        sf.readReg64 .x26 = 33#64 ∧ sf.readReg64 .x27 = s.readReg64 .x27 ∧
        sf.readReg64 .x28 = s.readReg64 .x28 ∧ sf.readReg64 .x29 = s.readReg64 .x29 ∧
        calleeSavedVRegs sf = calleeSavedVRegs s0 ∧
        LibsignalCodeRoLoaded lsmpl sf.mem)
      Qp := by
  have h := stageP2_sub1_kits_ext_placed
    (A := withFds A) (lim := lim) (Qp := Qp) ext
    (stageP2ClosureHooks_toWithFds hH)
    (hPure.toWithFds henf)
    spkKit spkEnv
    (spkKitFds_toWithFds henf hspk_fds hspkOk)
    stk hstk_pure hstk_shim hstk_lt st s0 s
    coroPtr msgPtr remoteAddrPtr localAddrPtr
    idStorePtr idStoreVt preKeyStorePtr preKeyStoreVt
    spkStorePtr kyberStorePtr kyberStoreVt
    baseKey spkId b_4f1 hfits
    hCode hpc hrun hsp_align hvregs
    hx8 hx9 hx10 hx11 hx12 hx13 hx14 hx15 hx16 hx19 hx22 hx23 hx24
  rw [withFds_pool_eq_of_fdsGe3Closed A henf st hfds] at h
  simp only [withFds_live, withFds_pool_enforced A henf] at h
  exact h

/-- `FdsGe3Closed`-preserving Substage P2.1 (`+0x0868 -> +0x0f14`, non-`4K` pure callees). -/
theorem stageP2_sub1_kits_placed_fd [LibsignalPlacement]
    {M : AllocCostModel} {P : Primitives} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    (henf : lim.enforced = true)
    {F : ShaCompress} {BobV1Env : AcceptKeysInput → DRKey → List AllocEvent → Prop}
    {AcceptErrEnv : AcceptKeysInput → List AllocEvent → Prop}
    {Qp : State → SepProp → Prop}
    (ext : String → Option (State → State))
    (hH : StageP2ClosureHooksPlaced A lim ext)
    (hPure : StageP2PureCalleesPlacedOfEnvFd P A lim F BobV1Env AcceptErrEnv ext)
    (spkKit : SignedPreKeyStoreSpec A.repAlloc 0#64)
    (spkEnv : SignedPreKeyStoreBudgetEnv spkKit)
    (hspk_fds : spkKit.fdsOk = FdsGe3Closed)
    (hspkOk : SignedPreKeyStoreKitPlacedOkFds A lim spkKit spkEnv ext)
    (stk : Nat)
    (hstk_pure : stageP2PureAndErrStack ≤ stk)
    (hstk_shim : spkKit.getShimStack ≤ stk)
    (hstk_lt : stk ≤ 2 ^ 64)
    (st : M.σ)
    (s0 s : State)
    (coroPtr msgPtr remoteAddrPtr localAddrPtr
     idStorePtr idStoreVt preKeyStorePtr preKeyStoreVt
     spkStorePtr kyberStorePtr kyberStoreVt : BitVec 64)
    (baseKey : PublicKey) (spkId : BitVec 32) (b_4f1 : BitVec 8)
    (hfits : FitsEnv M lim st (P2Sub1Env spkKit.getBoxSize))
    (hfds : FdsGe3Closed s.fs)
    (hCode : LibsignalCodeRoLoaded lsmpl s.mem)
    (hpc : s.pc = stageP1EntryPlaced + 0x868#64)
    (hrun : s.status = .Running)
    (hsp_align : (s.sp &&& 15#64 == 0#64) = true)
    (hvregs : calleeSavedVRegs s = calleeSavedVRegs s0)
    (hx8 : s.readReg64 .x8 = kyberStorePtr) (hx9 : s.readReg64 .x9 = msgPtr)
    (hx10 : s.readReg64 .x10 = kyberStoreVt) (hx11 : s.readReg64 .x11 = preKeyStorePtr)
    (hx12 : s.readReg64 .x12 = remoteAddrPtr) (hx13 : s.readReg64 .x13 = preKeyStoreVt)
    (hx14 : s.readReg64 .x14 = localAddrPtr) (hx15 : s.readReg64 .x15 = idStorePtr)
    (hx16 : s.readReg64 .x16 = idStoreVt) (hx19 : s.readReg64 .x19 = coroPtr)
    (hx22 : s.readReg64 .x22 = spkStorePtr) (hx23 : s.readReg64 .x23 = coroPtr + 0xe0#64)
    (hx24 : s.readReg64 .x24 = spkKit.spk_vt) :
    SepWPp (stageP1ProgPlaced ext) (stageP1EntryPlaced + 0xf14#64) s
      (cells (coroPtr + 0x3f8#64) 6 ∗ cells (coroPtr + 0x468#64) 4 ∗
       ((coroPtr + 0x4f1#64) ↦₈ b_4f1) ∗ sessionRecordEmptyHeaderAt (coroPtr + 0xe0#64) ∗
       ((msgPtr + 0xa8#64) ↦ₛ baseKey.bytes.toList) ∗ ((msgPtr + 0xec#64) ↦₃₂ spkId) ∗
       ((msgPtr + 0xf0#64) ↦₈ 4#8) ∗ memRegion (s.sp + 0x3e0#64) 9 ∗
       ((spkKit.spk_vt + 0x18#64) ↦₆₄ᵣ (0#64 + spkKit.getShimOff)) ∗
       A.pool lim st s ∗ stackAt s.sp stk)
      (fun sf P_f =>
        (P_f ⊢
          ∃∗ spkFutPtr : BitVec 64,
            ⌜sf.readReg64 .x0 = spkFutPtr ∧
              sf.readReg64 .x1 = 0#64 + spkKit.getFutVtOff ∧
              spkFutPtr ≠ 0#64 ∧ spkFutPtr.toNat % 8 = 0⌝ ∗
            processPrekeyActive10At coroPtr msgPtr remoteAddrPtr localAddrPtr
              idStorePtr idStoreVt preKeyStorePtr preKeyStoreVt kyberStorePtr kyberStoreVt ∗
            ((coroPtr + 0x4f1#64) ↦₈ 0#8) ∗ sessionRecordEmptyHeaderAt (coroPtr + 0xe0#64) ∗
            ((msgPtr + 0xa8#64) ↦ₛ baseKey.bytes.toList) ∗ ((msgPtr + 0xec#64) ↦₃₂ spkId) ∗
            ((msgPtr + 0xf0#64) ↦₈ 4#8) ∗ memRegion (s.sp + 0x3e0#64) 9 ∗
            ((spkKit.spk_vt + 0x18#64) ↦₆₄ᵣ (0#64 + spkKit.getShimOff)) ∗
            A.live spkFutPtr spkKit.getBoxSize 8 ∗
            spkKit.getBoxAt spkFutPtr spkStorePtr spkId 0#8 ∗
            (⌜FdsGe3Closed sf.fs⌝ ∗ A.pool lim (M.stepEvents (p2Sub1Events spkKit.getBoxSize) st) sf) ∗
            stackAt s.sp stk) ∧
        sf.sp = s.sp ∧ sf.trace = s.trace ∧ sf.readReg64 .x19 = coroPtr ∧
        sf.readReg64 .x22 = spkStorePtr ∧ sf.readReg64 .x23 = 0#64 ∧
        sf.readReg64 .x24 = spkKit.spk_vt ∧ sf.readReg64 .x25 = s.sp + 0x210#64 ∧
        sf.readReg64 .x26 = 33#64 ∧ sf.readReg64 .x27 = s.readReg64 .x27 ∧
        sf.readReg64 .x28 = s.readReg64 .x28 ∧ sf.readReg64 .x29 = s.readReg64 .x29 ∧
        calleeSavedVRegs sf = calleeSavedVRegs s0 ∧
        LibsignalCodeRoLoaded lsmpl sf.mem)
      Qp := by
  have h := stageP2_sub1_kits_placed
    (A := withFds A) (lim := lim) (Qp := Qp) ext
    (stageP2ClosureHooks_toWithFds hH)
    (hPure.toWithFds henf)
    spkKit spkEnv
    (spkKitFds_toWithFds henf hspk_fds hspkOk)
    stk hstk_pure hstk_shim hstk_lt st s0 s
    coroPtr msgPtr remoteAddrPtr localAddrPtr
    idStorePtr idStoreVt preKeyStorePtr preKeyStoreVt
    spkStorePtr kyberStorePtr kyberStoreVt
    baseKey spkId b_4f1 hfits
    hCode hpc hrun hsp_align hvregs
    hx8 hx9 hx10 hx11 hx12 hx13 hx14 hx15 hx16 hx19 hx22 hx23 hx24
  rw [withFds_pool_eq_of_fdsGe3Closed A henf st hfds] at h
  simp only [withFds_live, withFds_pool_enforced A henf] at h
  exact h

end LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP2Sub1PlacedBudgetFd
