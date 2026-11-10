/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP2Sub2PlacedBudget
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP2DefsPlacedBudgetFd
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP2CalleesPlacedBudgetFd
import LibsignalBinary.Proofs.Common.SharedHelpers
meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep

/-!
# Descriptor-Threaded Relocatable Stage P2 Substage P2.2

Lifts budget-threaded placed CPS Substage P2.2 (`+0x0f14 → +0x1460` or `+0x0f38` Arm 1) via
`AllocWithFds.withFds A` to preserve `FdsGe3Closed`.
-/

@[expose] public section

set_option autoImplicit false

namespace LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP2Sub2PlacedBudgetFd

open Arm64 Arm64.Process ProofLib SepProp
open CryptoGames.LibsignalSession (ShaCompress)
open CryptoVerification (LibsignalPlacement lsmpl)
open CryptoVerification.LibsignalPublicApi.StoreKit (
  KyberPreKeyStoreSpec LibsignalCodeRoLoaded SignedPreKeyStoreSpec spkGetPollOutAt
)
open CryptoVerification.RecordCodecs (SignedPreKeyRecord)
open CryptoVerification.E2E.Pqxdh.Initiator (AcceptKeysInput DRKey Primitives)
open CryptoVerification.E2E.Pqxdh.ResponderStore (clampBv8List)
open CryptoVerification.E2E.Pqxdh.ResponderClosure (bytes7At keyPair64UnalignedAt)
open CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Kits (
  stageP1EntryPlaced stageP1ProgPlaced stageP2PureAndErrStack
)
open LibsignalBinary.Heap (
  AllocCostModel AllocEvent BudgetLimits FitsEnv RustCliAllocBudget
)
open LibsignalBinary.Proofs.PublicApi.StoreKit.PreKeyStoreKitBudget (BoxAllocEnv)
open LibsignalBinary.Proofs.PublicApi.StoreKit.SignedPreKeyStoreKitBudget (
  SignedPreKeyStoreBudgetEnv
)
open LibsignalBinary.Proofs.PublicApi.StoreKit.KyberPreKeyStoreKitBudget (
  KyberPreKeyStoreBudgetEnv
)
open LibsignalBinary.Proofs.PublicApi.StoreKit.PlacedBudget (
  KyberPreKeyStoreKitPlacedOkFds SignedPreKeyStoreKitPlacedOkFds
)
open LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP2DefsPlacedBudget (
  StageP2ClosureHooksPlaced
)
open LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP2DefsPlacedBudgetFd (
  kpkKitFds_toWithFds
  sepWPp_pure_false
  spkKitFds_toWithFds
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
open LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP2Sub2PlacedBudget (
  p2SpkRecFreeEvents p2Sub2TailEvents stageP2_sub2_kits_ext_placed
)

/-- `FdsGe3Closed`-preserving CPS Substage P2.2 (`+0x0f14 -> +0x1460` or `+0x0f38` Arm 1). -/
theorem stageP2_sub2_kits_ext_placed_fd [LibsignalPlacement]
    {M : AllocCostModel} {P : Primitives} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    (henf : lim.enforced = true)
    {F : ShaCompress} {BobV1Env : AcceptKeysInput → DRKey → List AllocEvent → Prop}
    {AcceptErrEnv : AcceptKeysInput → List AllocEvent → Prop}
    (ext : String → Option (State → State))
    (hH : StageP2ClosureHooksPlaced A lim ext)
    (hPure : StageP2PureCalleesPlaced4KOfEnvFd P A lim F BobV1Env AcceptErrEnv ext)
    (spkKit : SignedPreKeyStoreSpec A.repAlloc 0#64)
    (spkEnv : SignedPreKeyStoreBudgetEnv spkKit)
    (hspk_fds : spkKit.fdsOk = FdsGe3Closed)
    (hspkOk : SignedPreKeyStoreKitPlacedOkFds A lim spkKit spkEnv ext)
    (kpkKit : KyberPreKeyStoreSpec A.repAlloc 0#64)
    (kpkEnv : KyberPreKeyStoreBudgetEnv kpkKit)
    (hkpk_fds : kpkKit.fdsOk = FdsGe3Closed)
    (hkpkOk : KyberPreKeyStoreKitPlacedOkFds A lim kpkKit kpkEnv ext)
    (stk : Nat) (hstk_pure : stageP2PureAndErrStack ≤ stk)
    (hstk_spk_poll : spkKit.getPollStack ≤ stk) (hstk_kpk_shim : kpkKit.getShimStack ≤ stk)
    (hstk_lt : stk ≤ 2 ^ 64)
    (ret : BitVec 64) (st : M.σ) (s0 s : State) (Frame : SepProp)
    (Q : State → SepProp → Prop) {Qp : State → SepProp → Prop}
    (coroPtr ctxPtr msgPtr spkStorePtr spkFutPtr kyberStorePtr kyberCtCap
     v_a0 v_b0 u_90 u_b8 u_d0 u_4f8 u_500 : BitVec 64)
    (spkId kyberPreKeyId : BitVec 32) (stSpk : spkKit.SpkState)
    (s0_b s1_b s2_b s3_b s4_b s5_b s6_b
     c0_init c1_init c2_init c3_init c4_init c5_init c6_init c63_init : BitVec 8)
    (cw0_init cw1_init cw2_init cw3_init cw4_init cw5_init cw6_init : BitVec 64)
    (hfits_poll : FitsEnv M lim st (spkEnv.getPollEnv stSpk spkId))
    (hfits_kpk : ∀ (r : SignedPreKeyRecord) (evs_poll : List AllocEvent)
      (pubCap privCap sigCap : Nat),
      spkKit.getRel stSpk spkId (.ok r) → spkKit.RecOk r →
      spkEnv.getPollEnv stSpk spkId evs_poll →
      33 ≤ pubCap → 32 ≤ privCap →
      FitsEnv M lim
        (M.stepEvents
          (evs_poll ++ p2SpkRecFreeEvents spkKit.getBoxSize pubCap privCap sigCap) st)
        (BoxAllocEnv kpkKit.getBoxSize))
    (hfds : FdsGe3Closed s.fs)
    (hCode : LibsignalCodeRoLoaded lsmpl s.mem)
    (henv : ∀ s1 : State, Steps (stageP1ProgPlaced ext) s s1 →
      s1.trace = s.trace → spkKit.envOk s1.fs.files)
    (hid_spk : spkKit.idOk spkId)
    (hrec_wf : ∀ r : SignedPreKeyRecord, spkKit.getRel stSpk spkId (.ok r) → spkKit.RecOk r →
      ∃ spkPubBytes spkPrivBytes : List (BitVec 8),
        spkPubBytes.length = 32 ∧ spkPrivBytes.length = 32 ∧
        r.signedPreKey.publicKey = 5#8 :: spkPubBytes ∧ r.signedPreKey.privateKey = spkPrivBytes)
    (hkyber_nz : kyberCtCap ≠ 0#64)
    (hpc : s.pc = stageP1EntryPlaced + 0xf14#64)
    (hrun : s.status = .Running) (hsp_align : (s.sp &&& 15#64 == 0#64) = true)
    (hvregs : calleeSavedVRegs s = calleeSavedVRegs s0)
    (hx0 : s.readReg64 .x0 = spkFutPtr) (hx1 : s.readReg64 .x1 = 0#64 + spkKit.getFutVtOff)
    (hx19 : s.readReg64 .x19 = coroPtr)
    (hErr : ∀ (e : spkKit.GetErr) (evs_poll : List AllocEvent) (s2 : State),
      Steps (stageP1ProgPlaced ext) s s2 →
      spkKit.getRel stSpk spkId (.error e) →
      spkEnv.getPollEnv stSpk spkId evs_poll →
      s2.pc = stageP1EntryPlaced + 0xf38#64 →
      s2.status = .Running → s2.sp = s.sp →
      s2.trace = s.trace ++ spkKit.getEvs spkId (.error e) →
      s2.readReg64 .x19 = coroPtr → s2.readReg64 .x21 = v_b0 →
      s2.readReg64 .x23 = v_a0 → s2.readReg64 .x25 = s.readReg64 .x25 →
      s2.readReg64 .x26 = coroPtr + 0x398#64 → s2.readReg64 .x27 = ctxPtr →
      s2.readReg64 .x28 = s.readReg64 .x28 → s2.readReg64 .x29 = s.readReg64 .x29 →
      calleeSavedVRegs s2 = calleeSavedVRegs s0 →
      LibsignalCodeRoLoaded lsmpl s2.mem →
      FdsGe3Closed s2.fs →
      SepWPp (stageP1ProgPlaced ext) ret s2
        (spkGetPollOutAt spkKit (s.sp + 0x3e0#64) (.error e) ∗
         spkKit.getBoxAt spkFutPtr spkStorePtr spkId 1#8 ∗
         spkKit.storeAt spkStorePtr (spkKit.getUpdate stSpk spkId (.error e)) ∗
         ((s.sp + 0x90#64) ↦₆₄ u_90) ∗ ((s.sp + 0x98#64) ↦₆₄ (coroPtr + 0x398#64)) ∗
         ((s.sp + 0xa0#64) ↦₆₄ v_a0) ∗ ((s.sp + 0xb0#64) ↦₆₄ v_b0) ∗
         ((s.sp + 0xb8#64) ↦₆₄ u_b8) ∗ ((s.sp + 0xc0#64) ↦₆₄ ctxPtr) ∗
         ((s.sp + 0xd0#64) ↦₆₄ u_d0) ∗
         bytes7At (s.sp + 0x930#64) s0_b s1_b s2_b s3_b s4_b s5_b s6_b ∗
         memRegion (s.sp + 0xa90#64) 65 ∗
         ((coroPtr + 0x4f8#64) ↦₆₄ spkFutPtr) ∗
         ((coroPtr + 0x500#64) ↦₆₄ (0#64 + spkKit.getFutVtOff)) ∗
         keyPair64UnalignedAt (coroPtr + 0x398#64) c0_init c1_init c2_init c3_init
           c4_init c5_init c6_init cw0_init cw1_init cw2_init cw3_init cw4_init cw5_init
           cw6_init c63_init ∗
         ((coroPtr + 0x3f8#64) ↦₆₄ kyberStorePtr) ∗ ((coroPtr + 0x400#64) ↦₆₄ kpkKit.kpk_vt) ∗
         ((coroPtr + 0x468#64) ↦₆₄ msgPtr) ∗ ((msgPtr + 0x90#64) ↦₆₄ kyberCtCap) ∗
         ((msgPtr + 0xa0#64) ↦₃₂ kyberPreKeyId) ∗
         ((0#64 + spkKit.getFutVtOff) ↦₆₄ᵣ (0#64 + spkKit.getFutDropOff)) ∗
         ((0#64 + spkKit.getFutVtOff + 8#64) ↦₆₄ᵣ BitVec.ofNat 64 spkKit.getBoxSize) ∗
         ((0#64 + spkKit.getFutVtOff + 0x10#64) ↦₆₄ᵣ 8#64) ∗
         ((0#64 + spkKit.getFutVtOff + 0x18#64) ↦₆₄ᵣ (0#64 + spkKit.getPollOff)) ∗
         ((kpkKit.kpk_vt + 0x18#64) ↦₆₄ᵣ (0#64 + kpkKit.getShimOff)) ∗
         A.live spkFutPtr spkKit.getBoxSize 8 ∗
         A.pool lim (M.stepEvents evs_poll st) s2 ∗ stackAt s.sp stk ∗ Frame)
        Q Qp)
    (hOk : ∀ (r : SignedPreKeyRecord) (spkPubBytes spkPrivBytes : List (BitVec 8))
      (evs_poll : List AllocEvent)
      (pubCap privCap privPtr sigCap sigPtr kyberFutPtr : BitVec 64)
      (b0 b1 b2 b3 b4 b5 b6 b63 c0 c1 c2 c3 c4 c5 c6 : BitVec 8)
      (w0 w1 w2 w3 w4 w5 w6 u0_kp u1_kp u2_kp u3_kp u4_kp u5_kp u6_kp u7_kp : BitVec 64)
      (sf : State),
      Steps (stageP1ProgPlaced ext) s sf →
      spkKit.getRel stSpk spkId (.ok r) → spkKit.RecOk r →
      spkEnv.getPollEnv stSpk spkId evs_poll →
      33 ≤ pubCap.toNat → 32 ≤ privCap.toNat →
      spkPubBytes.length = 32 → spkPrivBytes.length = 32 →
      r.signedPreKey.publicKey = 5#8 :: spkPubBytes → r.signedPreKey.privateKey = spkPrivBytes →
      (∀ a : BitVec 64, (a ↦ₛ spkPubBytes) =
        (a ↦₆₄ u0_kp) ∗ ((a + 8#64) ↦₆₄ u1_kp) ∗ ((a + 16#64) ↦₆₄ u2_kp) ∗
          ((a + 24#64) ↦₆₄ u3_kp)) →
      (∀ a : BitVec 64, (a ↦ₛ clampBv8List spkPrivBytes) =
        (a ↦₆₄ u4_kp) ∗ ((a + 8#64) ↦₆₄ u5_kp) ∗ ((a + 16#64) ↦₆₄ u6_kp) ∗
          ((a + 24#64) ↦₆₄ u7_kp)) →
      (∀ a : BitVec 64,
        bytes7At a b0 b1 b2 b3 b4 b5 b6 ∗
        ((a + 7#64) ↦₆₄ w0) ∗ ((a + 15#64) ↦₆₄ w1) ∗ ((a + 23#64) ↦₆₄ w2) ∗ ((a + 31#64) ↦₆₄ w3) =
          (a ↦₆₄ u0_kp) ∗ ((a + 8#64) ↦₆₄ u1_kp) ∗ ((a + 16#64) ↦₆₄ u2_kp) ∗
            ((a + 24#64) ↦₆₄ u3_kp) ∗ bytes7At (a + 32#64) c0 c1 c2 c3 c4 c5 c6) →
      (∀ a : BitVec 64,
        bytes7At a c0 c1 c2 c3 c4 c5 c6 ∗
        ((a + 7#64) ↦₆₄ w4) ∗ ((a + 15#64) ↦₆₄ w5) ∗ ((a + 23#64) ↦₆₄ w6) ∗ ((a + 31#64) ↦₈ b63) =
          (a ↦₆₄ u4_kp) ∗ ((a + 8#64) ↦₆₄ u5_kp) ∗ ((a + 16#64) ↦₆₄ u6_kp) ∗
            ((a + 24#64) ↦₆₄ u7_kp)) →
      sf.pc = stageP1EntryPlaced + 0x1460#64 →
      sf.status = .Running → sf.sp = s.sp →
      sf.trace = s.trace ++ spkKit.getEvs spkId (.ok r) →
      sf.readReg64 .x0 = kyberFutPtr → sf.readReg64 .x1 = 0#64 + kpkKit.getFutVtOff →
      kyberFutPtr ≠ 0#64 → kyberFutPtr.toNat % 8 = 0 →
      sf.readReg64 .x19 = coroPtr → sf.readReg64 .x20 = sigPtr →
      sf.readReg64 .x21 = v_b0 → sf.readReg64 .x23 = v_a0 →
      sf.readReg64 .x25 = s.readReg64 .x25 →
      sf.readReg64 .x26 = coroPtr + 0x398#64 → sf.readReg64 .x27 = ctxPtr →
      sf.readReg64 .x28 = s.sp + 0xa90#64 → sf.readReg64 .x29 = s.readReg64 .x29 →
      calleeSavedVRegs sf = calleeSavedVRegs s0 →
      LibsignalCodeRoLoaded lsmpl sf.mem →
      FdsGe3Closed sf.fs →
      SepWPp (stageP1ProgPlaced ext) ret sf
        (spkKit.storeAt spkStorePtr (spkKit.getUpdate stSpk spkId (.ok r)) ∗
         A.live kyberFutPtr kpkKit.getBoxSize 8 ∗
         kpkKit.getBoxAt kyberFutPtr kyberStorePtr kyberPreKeyId 0#8 ∗
         ((s.sp + 0x90#64) ↦₆₄ sigCap) ∗ ((s.sp + 0x98#64) ↦₆₄ (coroPtr + 0x398#64)) ∗
         ((s.sp + 0xa0#64) ↦₆₄ v_a0) ∗ ((s.sp + 0xb0#64) ↦₆₄ v_b0) ∗
         ((s.sp + 0xb8#64) ↦₆₄ privCap) ∗ ((s.sp + 0xc0#64) ↦₆₄ ctxPtr) ∗
         ((s.sp + 0xd0#64) ↦₆₄ privPtr) ∗ memRegion (s.sp + 0x3e0#64) 88 ∗
         bytes7At (s.sp + 0x930#64) b0 b1 b2 b3 b4 b5 b6 ∗ memRegion (s.sp + 0xa90#64) 65 ∗
         ((coroPtr + 0x4f8#64) ↦₆₄ spkFutPtr) ∗
         ((coroPtr + 0x500#64) ↦₆₄ (0#64 + spkKit.getFutVtOff)) ∗
         keyPair64UnalignedAt (coroPtr + 0x398#64) b0 b1 b2 b3 b4 b5 b6 w0 w1 w2 w3 w4 w5 w6 b63 ∗
         ((coroPtr + 0x3f8#64) ↦₆₄ kyberStorePtr) ∗ ((coroPtr + 0x400#64) ↦₆₄ kpkKit.kpk_vt) ∗
         ((coroPtr + 0x468#64) ↦₆₄ msgPtr) ∗ ((msgPtr + 0x90#64) ↦₆₄ kyberCtCap) ∗
         ((msgPtr + 0xa0#64) ↦₃₂ kyberPreKeyId) ∗
         ((0#64 + spkKit.getFutVtOff) ↦₆₄ᵣ (0#64 + spkKit.getFutDropOff)) ∗
         ((0#64 + spkKit.getFutVtOff + 8#64) ↦₆₄ᵣ BitVec.ofNat 64 spkKit.getBoxSize) ∗
         ((0#64 + spkKit.getFutVtOff + 0x10#64) ↦₆₄ᵣ 8#64) ∗
         ((0#64 + spkKit.getFutVtOff + 0x18#64) ↦₆₄ᵣ (0#64 + spkKit.getPollOff)) ∗
         ((kpkKit.kpk_vt + 0x18#64) ↦₆₄ᵣ (0#64 + kpkKit.getShimOff)) ∗
         A.pool lim
           (M.stepEvents
             (evs_poll ++ p2Sub2TailEvents spkKit.getBoxSize
               pubCap.toNat privCap.toNat sigCap.toNat kpkKit.getBoxSize) st) sf ∗
         stackAt s.sp stk ∗ Frame)
        Q Qp) :
    SepWPp (stageP1ProgPlaced ext) ret s
      (((s.sp + 0x90#64) ↦₆₄ u_90) ∗ ((s.sp + 0x98#64) ↦₆₄ (coroPtr + 0x398#64)) ∗
       ((s.sp + 0xa0#64) ↦₆₄ v_a0) ∗ ((s.sp + 0xb0#64) ↦₆₄ v_b0) ∗
       ((s.sp + 0xb8#64) ↦₆₄ u_b8) ∗ ((s.sp + 0xc0#64) ↦₆₄ ctxPtr) ∗
       ((s.sp + 0xd0#64) ↦₆₄ u_d0) ∗ memRegion (s.sp + 0x3e0#64) 88 ∗
       bytes7At (s.sp + 0x930#64) s0_b s1_b s2_b s3_b s4_b s5_b s6_b ∗
       memRegion (s.sp + 0xa90#64) 65 ∗
       ((coroPtr + 0x4f8#64) ↦₆₄ u_4f8) ∗ ((coroPtr + 0x500#64) ↦₆₄ u_500) ∗
       keyPair64UnalignedAt (coroPtr + 0x398#64) c0_init c1_init c2_init c3_init
         c4_init c5_init c6_init cw0_init cw1_init cw2_init cw3_init cw4_init cw5_init
         cw6_init c63_init ∗
       ((coroPtr + 0x3f8#64) ↦₆₄ kyberStorePtr) ∗ ((coroPtr + 0x400#64) ↦₆₄ kpkKit.kpk_vt) ∗
       ((coroPtr + 0x468#64) ↦₆₄ msgPtr) ∗ ((msgPtr + 0x90#64) ↦₆₄ kyberCtCap) ∗
       ((msgPtr + 0xa0#64) ↦₃₂ kyberPreKeyId) ∗
       ((0#64 + spkKit.getFutVtOff) ↦₆₄ᵣ (0#64 + spkKit.getFutDropOff)) ∗
       ((0#64 + spkKit.getFutVtOff + 8#64) ↦₆₄ᵣ BitVec.ofNat 64 spkKit.getBoxSize) ∗
       ((0#64 + spkKit.getFutVtOff + 0x10#64) ↦₆₄ᵣ 8#64) ∗
       ((0#64 + spkKit.getFutVtOff + 0x18#64) ↦₆₄ᵣ (0#64 + spkKit.getPollOff)) ∗
       ((kpkKit.kpk_vt + 0x18#64) ↦₆₄ᵣ (0#64 + kpkKit.getShimOff)) ∗
       A.live spkFutPtr spkKit.getBoxSize 8 ∗
       spkKit.getBoxAt spkFutPtr spkStorePtr spkId 0#8 ∗
       spkKit.storeAt spkStorePtr stSpk ∗ A.pool lim st s ∗ stackAt s.sp stk ∗ Frame)
      Q Qp := by
  have h := stageP2_sub2_kits_ext_placed
    (A := withFds A) (lim := lim)
    (Qp := Qp) ext
    (stageP2ClosureHooks_toWithFds hH)
    (hPure.toWithFds henf)
    spkKit spkEnv (spkKitFds_toWithFds henf hspk_fds hspkOk)
    kpkKit kpkEnv (kpkKitFds_toWithFds henf hkpk_fds hkpkOk)
    stk hstk_pure hstk_spk_poll hstk_kpk_shim hstk_lt ret st s0 s Frame Q
    coroPtr ctxPtr msgPtr spkStorePtr spkFutPtr kyberStorePtr kyberCtCap
    v_a0 v_b0 u_90 u_b8 u_d0 u_4f8 u_500 spkId kyberPreKeyId stSpk
    s0_b s1_b s2_b s3_b s4_b s5_b s6_b
    c0_init c1_init c2_init c3_init c4_init c5_init c6_init c63_init
    cw0_init cw1_init cw2_init cw3_init cw4_init cw5_init cw6_init
    hfits_poll
    hfits_kpk
    hCode henv hid_spk hrec_wf hkyber_nz hpc hrun hsp_align hvregs hx0 hx1 hx19
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
    (fun r spkPubBytes spkPrivBytes evs_poll pubCap privCap privPtr sigCap sigPtr kyberFutPtr
         b0 b1 b2 b3 b4 b5 b6 b63 c0 c1 c2 c3 c4 c5 c6
         w0 w1 w2 w3 w4 w5 w6 u0_kp u1_kp u2_kp u3_kp u4_kp u5_kp u6_kp u7_kp sf
         hst hrel hrok hevs hpub hpriv hl1 hl2 hp1 hp2 heq1 heq2 heq3 heq4
         hpcf hrunf hspf htrf hx0f hx1f hknz hkal hx19f hx20f hx21f hx23f hx25f hx26f hx27f
         hx28f hx29f hvrf hCodef => by
      dsimp only [withFds_live]
      by_cases hfdsf : FdsGe3Closed sf.fs
      · rw [withFds_pool_eq_of_fdsGe3Closed A henf _ hfdsf]
        exact hOk r spkPubBytes spkPrivBytes evs_poll pubCap privCap privPtr sigCap sigPtr kyberFutPtr
          b0 b1 b2 b3 b4 b5 b6 b63 c0 c1 c2 c3 c4 c5 c6
          w0 w1 w2 w3 w4 w5 w6 u0_kp u1_kp u2_kp u3_kp u4_kp u5_kp u6_kp u7_kp sf
          hst hrel hrok hevs hpub hpriv hl1 hl2 hp1 hp2 heq1 heq2 heq3 heq4
          hpcf hrunf hspf htrf hx0f hx1f hknz hkal hx19f hx20f hx21f hx23f hx25f hx26f hx27f
          hx28f hx29f hvrf hCodef hfdsf
      · rw [withFds_pool_eq_pure_false_of_not_fdsGe3Closed A henf _ hfdsf]
        simp only [pure_false_sepConj, sepConj_pure_false]
        exact sepWPp_pure_false)
  dsimp only [withFds_live] at h
  rw [withFds_pool_eq_of_fdsGe3Closed A henf st hfds] at h
  exact h

end LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP2Sub2PlacedBudgetFd
