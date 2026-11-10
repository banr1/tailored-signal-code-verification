/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP2Sub3PlacedBudget
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP2DefsPlacedBudgetFd
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP2CalleesPlacedBudgetFd
import LibsignalBinary.Proofs.Common.SharedHelpers
meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep

/-!
# Descriptor-Threaded Relocatable Stage P2 Substage P2.3

Lifts budget-threaded placed CPS Substage P2.3 (`+0x1460 → +0x0d5c` or `+0x0998` Arm 2) via
`AllocWithFds.withFds A` to preserve `FdsGe3Closed`.
-/

@[expose] public section

set_option autoImplicit false

namespace LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP2Sub3PlacedBudgetFd

open Arm64 Arm64.Process ProofLib SepProp
open CryptoGames.LibsignalSession (ShaCompress)
open CryptoVerification (LibsignalPlacement lsmpl)
open CryptoVerification.LibsignalPublicApi.StoreKit (
  KyberPreKeyStoreSpec LibsignalCodeRoLoaded kpkGetPollOutAt
)
open CryptoVerification.RecordCodecs (KyberPreKeyRecord)
open CryptoVerification.E2E.Pqxdh.Initiator (AcceptKeysInput DRKey Primitives)
open CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Kits (
  stageP1EntryPlaced stageP1ProgPlaced stageP2PureAndErrStack
)
open LibsignalBinary.Heap (
  AllocCostModel AllocEvent BudgetLimits FitsEnv FreeOnlyEvs RustCliAllocBudget
  rustDeallocEvents
)
open LibsignalBinary.Proofs.E2E.Pqxdh.ResponderStore.KeyPairCalleesBudget (
  KemKeyPairFromPubPrivEnv
)
open LibsignalBinary.Proofs.PublicApi.StoreKit.KyberPreKeyStoreKitBudget (
  KyberPreKeyStoreBudgetEnv
)
open LibsignalBinary.Proofs.PublicApi.StoreKit.PlacedBudget (
  KyberPreKeyStoreKitPlacedOkFds
)
open LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP2DefsPlacedBudget (
  StageP2ClosureHooksPlaced
)
open LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP2DefsPlacedBudgetFd (
  kpkKitFds_toWithFds
  sepWPp_pure_false
  stageP2ClosureHooks_toWithFds
  withFds_pool_eq_of_fdsGe3Closed
  withFds_pool_eq_pure_false_of_not_fdsGe3Closed
)
open LibsignalBinary.Proofs.SignalSession.Cli.F3.HRead.ReadFileBudgetPlaced (
  FdsGe3Closed
)
open LibsignalBinary.Proofs.SignalSession.Cli.Heap.AllocWithFds (
  withFds withFds_live
)
open LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP2CalleesPlacedBudgetFd (
  StageP2PureCalleesPlaced4KOfEnvFd
)
open LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP2Sub3AuxPlacedBudget (
  P2Sub3TailAllocEnv
)
open LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP2Sub3PlacedBudget (
  p2Sub3OkPostPollEvents p2Sub3PreTailEvents stageP2_sub3_kits_ext_placed
)

/-- `FdsGe3Closed`-preserving CPS Substage P2.3 (`+0x1460 -> +0x0d5c` or `+0x0998` Arm 2). -/
theorem stageP2_sub3_kits_ext_placed_fd [LibsignalPlacement]
    {M : AllocCostModel} {P : Primitives} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    (henf : lim.enforced = true)
    {F : ShaCompress} {BobV1Env : AcceptKeysInput → DRKey → List AllocEvent → Prop}
    {AcceptErrEnv : AcceptKeysInput → List AllocEvent → Prop}
    (ext : String → Option (State → State))
    (hH : StageP2ClosureHooksPlaced A lim ext)
    (hPure : StageP2PureCalleesPlaced4KOfEnvFd P A lim F BobV1Env AcceptErrEnv ext)
    (kpkKit : KyberPreKeyStoreSpec A.repAlloc 0#64)
    (kpkEnv : KyberPreKeyStoreBudgetEnv kpkKit)
    (hkpk_fds : kpkKit.fdsOk = FdsGe3Closed)
    (hkpkOk : KyberPreKeyStoreKitPlacedOkFds A lim kpkKit kpkEnv ext)
    (stk : Nat) (hstk_pure : stageP2PureAndErrStack ≤ stk)
    (hstk_kpk_poll : kpkKit.getPollStack ≤ stk) (hstk_lt : stk ≤ 2 ^ 64)
    (ret : BitVec 64) (st : M.σ) (s0 s : State) (Frame : SepProp)
    (Q : State → SepProp → Prop) {Qp : State → SepProp → Prop}
    (coroPtr ctxPtr msgPtr kyberFutPtr kyberStorePtr kyberCtCap
     v_98 v_a0 v_b0 u_4f8 u_500 u_90 u_a8 u_b8 u_c0 u_d0
     u_3d8 u_3e0 u_3e8 u_3f0 : BitVec 64)
    (kyberPreKeyId : BitVec 32) (b_4f1 : BitVec 8) (stKpk : kpkKit.KpkState)
    (hfits_poll : FitsEnv M lim st (kpkEnv.getPollEnv stKpk kyberPreKeyId))
    (hfits_kem : ∀ (r : KyberPreKeyRecord) (evs_poll : List AllocEvent),
      kpkKit.getRel stKpk kyberPreKeyId (.ok r) → kpkKit.RecOk r →
      kpkEnv.getPollEnv stKpk kyberPreKeyId evs_poll →
      FitsEnv M lim
        (M.stepEvents (evs_poll ++ rustDeallocEvents kpkKit.getBoxSize 8) st)
        KemKeyPairFromPubPrivEnv)
    (hfits_tail : ∀ (r : KyberPreKeyRecord) (evs_poll : List AllocEvent)
      (pubCap privCap sigCap : Nat),
      kpkKit.getRel stKpk kyberPreKeyId (.ok r) → kpkKit.RecOk r →
      kpkEnv.getPollEnv stKpk kyberPreKeyId evs_poll →
      1569 ≤ pubCap → 3169 ≤ privCap →
      FitsEnv M lim
        (M.stepEvents
          (evs_poll ++ p2Sub3PreTailEvents kpkKit.getBoxSize pubCap privCap sigCap) st)
        P2Sub3TailAllocEnv)
    (hfds : FdsGe3Closed s.fs)
    (hkyber_nz : kyberCtCap ≠ 0#64)
    (hCode : LibsignalCodeRoLoaded lsmpl s.mem)
    (henv : ∀ s1 : State, Steps (stageP1ProgPlaced ext) s s1 →
      s1.trace = s.trace → kpkKit.envOk s1.fs.files)
    (hid_kpk : kpkKit.getIdOk kyberPreKeyId)
    (hrec_wf : ∀ r : KyberPreKeyRecord, kpkKit.getRel stKpk kyberPreKeyId (.ok r) →
      kpkKit.RecOk r →
      ∃ kyberPubBytes kyberPrivBytes : List (BitVec 8),
        kyberPubBytes.length = 1568 ∧ kyberPrivBytes.length = 3168 ∧
        r.signedPreKey.publicKey = 8#8 :: kyberPubBytes ∧
        r.signedPreKey.privateKey = 8#8 :: kyberPrivBytes)
    (hpc : s.pc = stageP1EntryPlaced + 0x1460#64)
    (hrun : s.status = .Running) (hsp_align : (s.sp &&& 15#64 == 0#64) = true)
    (hvregs : calleeSavedVRegs s = calleeSavedVRegs s0)
    (hx0 : s.readReg64 .x0 = kyberFutPtr) (hx1 : s.readReg64 .x1 = 0#64 + kpkKit.getFutVtOff)
    (hx19 : s.readReg64 .x19 = coroPtr) (hx21 : s.readReg64 .x21 = v_b0)
    (hx23 : s.readReg64 .x23 = v_a0) (hx26 : s.readReg64 .x26 = v_98)
    (hx27 : s.readReg64 .x27 = ctxPtr)
    (hErr : ∀ (e : kpkKit.GetErr) (evs_poll : List AllocEvent) (s2 : State),
      Steps (stageP1ProgPlaced ext) s s2 →
      kpkKit.getRel stKpk kyberPreKeyId (.error e) →
      kpkEnv.getPollEnv stKpk kyberPreKeyId evs_poll →
      s2.pc = stageP1EntryPlaced + 0x998#64 →
      s2.status = .Running → s2.sp = s.sp →
      s2.trace = s.trace ++ kpkKit.getEvs kyberPreKeyId (.error e) →
      s2.readReg64 .x19 = coroPtr → s2.readReg64 .x21 = v_b0 →
      s2.readReg64 .x23 = v_a0 → s2.readReg64 .x25 = s.readReg64 .x25 →
      s2.readReg64 .x26 = v_98 → s2.readReg64 .x27 = ctxPtr →
      s2.readReg64 .x28 = s.readReg64 .x28 → s2.readReg64 .x29 = s.readReg64 .x29 →
      calleeSavedVRegs s2 = calleeSavedVRegs s0 →
      LibsignalCodeRoLoaded lsmpl s2.mem →
      FdsGe3Closed s2.fs →
      SepWPp (stageP1ProgPlaced ext) ret s2
        (kpkGetPollOutAt kpkKit (s.sp + 0x3e0#64) (.error e) ∗
         kpkKit.getBoxAt kyberFutPtr kyberStorePtr kyberPreKeyId 1#8 ∗
         kpkKit.storeAt kyberStorePtr (kpkKit.getUpdate stKpk kyberPreKeyId (.error e)) ∗
         ((s.sp + 0x90#64) ↦₆₄ u_90) ∗ ((s.sp + 0x98#64) ↦₆₄ v_98) ∗
         ((s.sp + 0xa0#64) ↦₆₄ v_a0) ∗ ((s.sp + 0xa8#64) ↦₆₄ u_a8) ∗
         ((s.sp + 0xb0#64) ↦₆₄ v_b0) ∗ ((s.sp + 0xb8#64) ↦₆₄ u_b8) ∗
         ((s.sp + 0xc0#64) ↦₆₄ u_c0) ∗ ((s.sp + 0xd0#64) ↦₆₄ u_d0) ∗
         memRegion (s.sp + 0xa90#64) 65 ∗
         ((coroPtr + 0x3d8#64) ↦₆₄ u_3d8) ∗ ((coroPtr + 0x3e0#64) ↦₆₄ u_3e0) ∗
         ((coroPtr + 0x3e8#64) ↦₆₄ u_3e8) ∗ ((coroPtr + 0x3f0#64) ↦₆₄ u_3f0) ∗
         ((coroPtr + 0x468#64) ↦₆₄ msgPtr) ∗ ((coroPtr + 0x4f1#64) ↦₈ b_4f1) ∗
         ((coroPtr + 0x4f8#64) ↦₆₄ kyberFutPtr) ∗
         ((coroPtr + 0x500#64) ↦₆₄ (0#64 + kpkKit.getFutVtOff)) ∗
         ((msgPtr + 0x90#64) ↦₆₄ kyberCtCap) ∗
         ((0#64 + kpkKit.getFutVtOff) ↦₆₄ᵣ (0#64 + kpkKit.getFutDropOff)) ∗
         ((0#64 + kpkKit.getFutVtOff + 8#64) ↦₆₄ᵣ BitVec.ofNat 64 kpkKit.getBoxSize) ∗
         ((0#64 + kpkKit.getFutVtOff + 0x10#64) ↦₆₄ᵣ 8#64) ∗
         ((0#64 + kpkKit.getFutVtOff + 0x18#64) ↦₆₄ᵣ (0#64 + kpkKit.getPollOff)) ∗
         A.live kyberFutPtr kpkKit.getBoxSize 8 ∗
         A.pool lim (M.stepEvents evs_poll st) s2 ∗ stackAt s.sp stk ∗ Frame)
        Q Qp)
    (hOk : ∀ (r : KyberPreKeyRecord) (kyberPubBytes kyberPrivBytes : List (BitVec 8))
      (evs_poll evs_drop : List AllocEvent)
      (pkBuf skBuf pubCap sigCap privCap privPtr : BitVec 64) (sf : State),
      Steps (stageP1ProgPlaced ext) s sf →
      kpkKit.getRel stKpk kyberPreKeyId (.ok r) → kpkKit.RecOk r →
      kpkEnv.getPollEnv stKpk kyberPreKeyId evs_poll →
      FreeOnlyEvs evs_drop →
      1569 ≤ pubCap.toNat → 3169 ≤ privCap.toNat →
      kyberPubBytes.length = 1568 → kyberPrivBytes.length = 3168 →
      r.signedPreKey.publicKey = 8#8 :: kyberPubBytes →
      r.signedPreKey.privateKey = 8#8 :: kyberPrivBytes →
      pkBuf ≠ 0#64 → skBuf ≠ 0#64 →
      sf.pc = stageP1EntryPlaced + 0xd5c#64 →
      sf.status = .Running → sf.sp = s.sp →
      sf.trace = s.trace ++ kpkKit.getEvs kyberPreKeyId (.ok r) →
      sf.readReg64 .x19 = coroPtr → sf.readReg64 .x21 = msgPtr + 0x90#64 →
      sf.readReg64 .x22 = kyberCtCap → sf.readReg64 .x23 = v_a0 →
      sf.readReg64 .x25 = s.readReg64 .x25 → sf.readReg64 .x26 = v_98 →
      sf.readReg64 .x27 = ctxPtr → sf.readReg64 .x28 = s.sp + 0xa90#64 →
      sf.readReg64 .x29 = s.readReg64 .x29 →
      calleeSavedVRegs sf = calleeSavedVRegs s0 →
      LibsignalCodeRoLoaded lsmpl sf.mem →
      FdsGe3Closed sf.fs →
      SepWPp (stageP1ProgPlaced ext) ret sf
        (kpkKit.storeAt kyberStorePtr (kpkKit.getUpdate stKpk kyberPreKeyId (.ok r)) ∗
         (pkBuf ↦ₛ kyberPubBytes) ∗ A.live pkBuf 1568 1 ∗
         (skBuf ↦ₛ kyberPrivBytes) ∗ A.live skBuf 3168 1 ∗
         ((s.sp + 0x90#64) ↦₆₄ sigCap) ∗ ((s.sp + 0x98#64) ↦₆₄ v_98) ∗
         ((s.sp + 0xa0#64) ↦₆₄ v_a0) ∗ ((s.sp + 0xa8#64) ↦₆₄ 3169#64) ∗
         ((s.sp + 0xb0#64) ↦₆₄ v_b0) ∗ ((s.sp + 0xb8#64) ↦₆₄ privCap) ∗
         ((s.sp + 0xc0#64) ↦₆₄ ctxPtr) ∗ ((s.sp + 0xd0#64) ↦₆₄ privPtr) ∗
         memRegion (s.sp + 0x3e0#64) 88 ∗ memRegion (s.sp + 0xa90#64) 65 ∗
         ((coroPtr + 0x3d8#64) ↦₆₄ pkBuf) ∗ ((coroPtr + 0x3e0#64) ↦₆₄ 0x620#64) ∗
         ((coroPtr + 0x3e8#64) ↦₆₄ skBuf) ∗ ((coroPtr + 0x3f0#64) ↦₆₄ 0xc60#64) ∗
         ((coroPtr + 0x468#64) ↦₆₄ msgPtr) ∗ ((coroPtr + 0x4f1#64) ↦₈ 1#8) ∗
         ((coroPtr + 0x4f8#64) ↦₆₄ kyberFutPtr) ∗
         ((coroPtr + 0x500#64) ↦₆₄ (0#64 + kpkKit.getFutVtOff)) ∗
         ((msgPtr + 0x90#64) ↦₆₄ kyberCtCap) ∗
         ((0#64 + kpkKit.getFutVtOff) ↦₆₄ᵣ (0#64 + kpkKit.getFutDropOff)) ∗
         ((0#64 + kpkKit.getFutVtOff + 8#64) ↦₆₄ᵣ BitVec.ofNat 64 kpkKit.getBoxSize) ∗
         ((0#64 + kpkKit.getFutVtOff + 0x10#64) ↦₆₄ᵣ 8#64) ∗
         ((0#64 + kpkKit.getFutVtOff + 0x18#64) ↦₆₄ᵣ (0#64 + kpkKit.getPollOff)) ∗
         A.pool lim
           (M.stepEvents
             (evs_poll ++ p2Sub3OkPostPollEvents kpkKit.getBoxSize
               pubCap.toNat privCap.toNat sigCap.toNat evs_drop) st) sf ∗
         stackAt s.sp stk ∗ Frame)
        Q Qp) :
    SepWPp (stageP1ProgPlaced ext) ret s
      (((s.sp + 0x90#64) ↦₆₄ u_90) ∗ ((s.sp + 0x98#64) ↦₆₄ v_98) ∗
       ((s.sp + 0xa0#64) ↦₆₄ v_a0) ∗ ((s.sp + 0xa8#64) ↦₆₄ u_a8) ∗
       ((s.sp + 0xb0#64) ↦₆₄ v_b0) ∗ ((s.sp + 0xb8#64) ↦₆₄ u_b8) ∗
       ((s.sp + 0xc0#64) ↦₆₄ u_c0) ∗ ((s.sp + 0xd0#64) ↦₆₄ u_d0) ∗
       memRegion (s.sp + 0x3e0#64) 88 ∗ memRegion (s.sp + 0xa90#64) 65 ∗
       ((coroPtr + 0x3d8#64) ↦₆₄ u_3d8) ∗ ((coroPtr + 0x3e0#64) ↦₆₄ u_3e0) ∗
       ((coroPtr + 0x3e8#64) ↦₆₄ u_3e8) ∗ ((coroPtr + 0x3f0#64) ↦₆₄ u_3f0) ∗
       ((coroPtr + 0x468#64) ↦₆₄ msgPtr) ∗ ((coroPtr + 0x4f1#64) ↦₈ b_4f1) ∗
       ((coroPtr + 0x4f8#64) ↦₆₄ u_4f8) ∗ ((coroPtr + 0x500#64) ↦₆₄ u_500) ∗
       ((msgPtr + 0x90#64) ↦₆₄ kyberCtCap) ∗
       ((0#64 + kpkKit.getFutVtOff) ↦₆₄ᵣ (0#64 + kpkKit.getFutDropOff)) ∗
       ((0#64 + kpkKit.getFutVtOff + 8#64) ↦₆₄ᵣ BitVec.ofNat 64 kpkKit.getBoxSize) ∗
       ((0#64 + kpkKit.getFutVtOff + 0x10#64) ↦₆₄ᵣ 8#64) ∗
       ((0#64 + kpkKit.getFutVtOff + 0x18#64) ↦₆₄ᵣ (0#64 + kpkKit.getPollOff)) ∗
       A.live kyberFutPtr kpkKit.getBoxSize 8 ∗
       kpkKit.getBoxAt kyberFutPtr kyberStorePtr kyberPreKeyId 0#8 ∗
       kpkKit.storeAt kyberStorePtr stKpk ∗ A.pool lim st s ∗ stackAt s.sp stk ∗ Frame)
      Q Qp := by
  have h := stageP2_sub3_kits_ext_placed
    (A := withFds A) (lim := lim)
    (Qp := Qp) ext
    (stageP2ClosureHooks_toWithFds hH)
    (hPure.toWithFds henf)
    kpkKit kpkEnv (kpkKitFds_toWithFds henf hkpk_fds hkpkOk)
    stk hstk_pure hstk_kpk_poll hstk_lt ret st s0 s Frame Q
    coroPtr ctxPtr msgPtr kyberFutPtr kyberStorePtr kyberCtCap
    v_98 v_a0 v_b0 u_4f8 u_500 u_90 u_a8 u_b8 u_c0 u_d0
    u_3d8 u_3e0 u_3e8 u_3f0 kyberPreKeyId b_4f1 stKpk
    hfits_poll
    hfits_kem
    hfits_tail
    hkyber_nz hCode henv hid_kpk hrec_wf hpc hrun hsp_align hvregs
    hx0 hx1 hx19 hx21 hx23 hx26 hx27
    (fun e evs_poll s2 hst hrel hevs hpc2 hrun2 hsp2 htr2 hx19_2 hx21_2 hx23_2 hx25_2 hx26_2
         hx27_2 hx28_2 hx29_2 hvr2 hCode2 => by
      dsimp only [withFds_live]
      by_cases hfds2 : FdsGe3Closed s2.fs
      · rw [withFds_pool_eq_of_fdsGe3Closed A henf _ hfds2]
        exact hErr e evs_poll s2 hst hrel hevs hpc2 hrun2 hsp2 htr2 hx19_2 hx21_2 hx23_2 hx25_2
          hx26_2 hx27_2 hx28_2 hx29_2 hvr2 hCode2 hfds2
      · rw [withFds_pool_eq_pure_false_of_not_fdsGe3Closed A henf _ hfds2]
        simp only [pure_false_sepConj, sepConj_pure_false]
        exact sepWPp_pure_false)
    (fun r kyberPubBytes kyberPrivBytes evs_poll evs_drop pkBuf skBuf pubCap sigCap privCap
         privPtr sf hst hrel hrok hevs hfo hpub hpriv hl1 hl2 hp1 hp2 hpk hsk
         hpcf hrunf hspf htrf hx19f hx21f hx22f hx23f hx25f hx26f hx27f hx28f hx29f hvrf hCodef => by
      dsimp only [withFds_live]
      by_cases hfdsf : FdsGe3Closed sf.fs
      · rw [withFds_pool_eq_of_fdsGe3Closed A henf _ hfdsf]
        exact hOk r kyberPubBytes kyberPrivBytes evs_poll evs_drop pkBuf skBuf pubCap sigCap privCap
          privPtr sf hst hrel hrok hevs hfo hpub hpriv hl1 hl2 hp1 hp2 hpk hsk
          hpcf hrunf hspf htrf hx19f hx21f hx22f hx23f hx25f hx26f hx27f hx28f hx29f hvrf hCodef hfdsf
      · rw [withFds_pool_eq_pure_false_of_not_fdsGe3Closed A henf _ hfdsf]
        simp only [pure_false_sepConj, sepConj_pure_false]
        exact sepWPp_pure_false)
  dsimp only [withFds_live] at h
  rw [withFds_pool_eq_of_fdsGe3Closed A henf st hfds] at h
  exact h

end LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP2Sub3PlacedBudgetFd
