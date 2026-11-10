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
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP2BlocksA1PlacedBudget
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP2DefsPlacedBudget
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP2Sub1PlacedBudget
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP2Sub2Placed
public import LibsignalBinary.Proofs.E2E.Pqxdh.ResponderStore.KeyPairCalleesAuxBudget
public import LibsignalBinary.Proofs.E2E.Pqxdh.ResponderStore.KeyPairCalleesBudget
public import LibsignalBinary.Proofs.PublicApi.StoreKit.KyberPreKeyStoreKitBudget
public import LibsignalBinary.Proofs.PublicApi.StoreKit.PlacedBudget
public import LibsignalBinary.Proofs.PublicApi.StoreKit.PreKeyStoreKitBudget
public import LibsignalBinary.Proofs.PublicApi.StoreKit.SignedPreKeyStoreKitBudget
import Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic
import ProofLib.SepLogic.WPp
import LibsignalBinary.Proofs.Common.SharedHelpers
meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP2Sub1
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP2Sub2

/-!
# Budget-Threaded Relocatable Stage P2 Substage P2.2

Defines `P2Sub2TailEnv` and proves `RustCliAllocBudget M` / `VmPreserved` placed CPS Substage P2.2
(`+0x0f14 → +0x1460` on `Ok`, or `+0x0f38` Arm 1) on Block `518`.
-/

@[expose] public section

set_option autoImplicit false

namespace LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP2Sub2PlacedBudget

open Arm64 ProofLib ProofLib.ProgramReflection SepProp
open CryptoGames CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open CryptoVerification CryptoVerification.RustHeap
open CryptoVerification.LibsignalSession CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchet hiding
  publicKeySerializeSpec publicKeySerializeSpecWithStack
open CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalTripleRatchet.FromRecordCallees
open CryptoVerification.LibsignalPublicApi CryptoVerification.LibsignalPublicApiRepr
open CryptoVerification.LibsignalPublicApi.StoreSession
open CryptoVerification.LibsignalPublicApi.StoreKit hiding
  kitSpkGetShimSpec kitSpkGetPollSpec kitSpkGetPollSpecE kitKpkGetShimSpec
  SignedPreKeyStoreKitPlacedOk KyberPreKeyStoreKitPlacedOk
open CryptoVerification.RecordCodecs CryptoVerification.RecordCodecsBinary
open CryptoVerification.E2E.Bin
open CryptoVerification.E2E.Pqxdh
open CryptoVerification.E2E.Pqxdh.Initiator
open CryptoVerification.E2E.Pqxdh.ResponderCore
open CryptoVerification.E2E.Pqxdh.WireEntries
open CryptoVerification.E2E.Pqxdh.ResponderStore hiding
  sessionRecordEmptyHeaderAt promoteMatchingSessionEmptySpec promoteStateEmptySpec
open CryptoVerification.E2E.Pqxdh.ResponderClosure
open CryptoVerification.LibsignalTripleRatchet.Getters
open CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure
open CryptoVerification.CliHandshake.RespClosurePlaced
open CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Kits hiding
  StageP2ClosureHooksPlaced
  StageP2PureCalleesPlaced
  StageP2PureCalleesPlaced4K
  StageP2PureCalleesExtPlaced
  InitializeBobV1OkPlaced
  InitializeBobV1OkPlaced4K
  promoteStateEmpty4KSpec
  isSameAccountDistinctAtSpec
  p2Memcpy4KSpec
  p2_seg2a_ext_placed_wp
  p2_seg2b_gen_placed_wp
  p2_seg2c_hooks_placed_wp
  p2_seg2c_gen_placed_wp
  p2_seg2d_sig0_hooks_placed_wp
  p2_seg2d_sig0_gen_placed_wp
  p2_seg2d_sigNz_hooks_placed_wp
  p2_seg2d_sigNz_gen_placed_wp
  p2_spkGetShim_pre_intro_placed
  p2_spkGetPoll_pre_intro_placed
  p2_kpkGetShim_pre_intro_placed
  stageP2_sub2_kits_ext_placed
  stageP2_sub2_kits_4k_placed
  stageP2_sub2_kits_hooks_placed
  stageP2_sub2_kits_placed
open LibsignalBinary.Heap (
  AllocCostModel AllocEvent BudgetLimits FitsEnv FitsEvent FitsEvents FitsStep
  FreeOnlyEvs RustCliAllocBudget SeqEnv VmPreserved coarseCostModel coarseStep
  coarseStepReserve rustAllocEvents rustDeallocEvents
)
open LibsignalBinary.Heap.SpecBudget (withVmPreserved)
open LibsignalBinary.Proofs.PublicApi.StoreKit.PreKeyStoreKitBudget (
  BoxAllocEnv futDropBudgetSpec
)
open LibsignalBinary.Proofs.PublicApi.StoreKit.SignedPreKeyStoreKitBudget (
  SignedPreKeyStoreBudgetEnv kitSpkGetPollSpec kitSpkGetPollSpecE
)
open LibsignalBinary.Proofs.PublicApi.StoreKit.KyberPreKeyStoreKitBudget (
  KyberPreKeyStoreBudgetEnv kitKpkGetShimSpec
)
open LibsignalBinary.Proofs.PublicApi.StoreKit.PlacedBudget (
  SignedPreKeyStoreKitPlacedOk KyberPreKeyStoreKitPlacedOk
)
open LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP2DefsPlacedBudget (
  StageP2ClosureHooksPlaced
  StageP2PureCalleesPlaced StageP2PureCalleesPlaced4K
  StageP2PureCalleesPlaced4KOfEnv StageP2PureCalleesPlacedOfEnv
)
open LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP2BlocksA1PlacedBudget (
  p2_seg2a_ext_placed_wp p2_seg2b_gen_placed_wp
  p2_seg2c_hooks_placed_wp p2_seg2d_sig0_hooks_placed_wp p2_seg2d_sigNz_hooks_placed_wp
)
open LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP2Sub1PlacedBudget (
  boxAllocEvents boxAllocEnv_iff_eq fitsEnv_boxAllocEnv_iff
  p2_bind_sepWP_qp_frame_state_placed
  p2_call_nopanic_lscl_steps_frame_placed
  p2_call_rocl_nopanic_steps_frame_placed
  p2_kpkGetShim_pre_intro_placed
  p2_spkGetPoll_pre_intro_placed
)

set_option maxRecDepth 200000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

set_option allowUnsafeReducibility true in
attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff
  protocolAddressAt decryptPrekeySavedRegsAt

local macro "sep_norm" : tactic =>
  `(tactic| repeat (first
    | simp only [↓reduceIte]
    | simp only [BitVec.add_assoc]
    | simp only [BitVec.reduceAdd]
    | simp only [RustCliAllocBudget.repAlloc_live]
    | simp only [sepExists_sepConj_left]
    | simp only [sepExists_sepConj_right]
    | simp only [emp_sepConj]
    | simp only [sepConj_emp]
    | simp only [sepConj_assoc]))

/-! ## 1. Substage P2.2 Deallocation & `.ok`-Tail Event Lists and Envelopes -/

theorem freeOnlyEvs_rustDeallocEvents (size align : Nat) :
    FreeOnlyEvs (rustDeallocEvents size align) :=
  FreeOnlyEvs.singleton align size

/-- Exact deterministic deallocation events performed along the `.ok r` branch of Substage P2.2
between `spkKit.getPoll` and `kpkKit.getShim`:
`__rust_dealloc(spkBoxSize, 8)` on the SPK poll future box followed by freeing the cloned
`publicKey`, `privateKey`, and (when `sigCap ≠ 0`) `signature` `Vec<u8>` buffers. -/
def p2SpkRecFreeEvents (spkBoxSize pubCap privCap sigCap : Nat) : List AllocEvent :=
  rustDeallocEvents spkBoxSize 8 ++
    (if sigCap = 0 then
       rustDeallocEvents pubCap 1 ++ rustDeallocEvents privCap 1
     else
       rustDeallocEvents pubCap 1 ++ rustDeallocEvents privCap 1 ++
         rustDeallocEvents sigCap 1)

theorem p2SpkRecFreeEvents_freeOnly (spkBoxSize pubCap privCap sigCap : Nat) :
    FreeOnlyEvs (p2SpkRecFreeEvents spkBoxSize pubCap privCap sigCap) := by
  unfold p2SpkRecFreeEvents
  refine FreeOnlyEvs.append (freeOnlyEvs_rustDeallocEvents spkBoxSize 8) ?_
  split
  · exact FreeOnlyEvs.append (freeOnlyEvs_rustDeallocEvents pubCap 1)
      (freeOnlyEvs_rustDeallocEvents privCap 1)
  · exact FreeOnlyEvs.append
      (FreeOnlyEvs.append (freeOnlyEvs_rustDeallocEvents pubCap 1)
        (freeOnlyEvs_rustDeallocEvents privCap 1))
      (freeOnlyEvs_rustDeallocEvents sigCap 1)

/-- Exact deterministic post-`spkKit.getPoll` allocator event list along the `.ok r` branch of
Substage P2.2 (`p2SpkRecFreeEvents` followed by `kpkKit.getShim`'s `boxAllocEvents kpkBoxSize`). -/
def p2Sub2TailEvents (spkBoxSize pubCap privCap sigCap kpkBoxSize : Nat) : List AllocEvent :=
  p2SpkRecFreeEvents spkBoxSize pubCap privCap sigCap ++ boxAllocEvents kpkBoxSize

/-- Exact allocator event envelope for the post-`spkKit.getPoll` `.ok r` tail of Substage P2.2. -/
def P2Sub2TailEnv (spkBoxSize pubCap privCap sigCap kpkBoxSize : Nat)
    (evs : List AllocEvent) : Prop :=
  evs = p2Sub2TailEvents spkBoxSize pubCap privCap sigCap kpkBoxSize

theorem fitsEnv_p2Sub2TailEnv_iff {M : AllocCostModel} {lim : BudgetLimits} {st : M.σ}
    (spkBoxSize pubCap privCap sigCap kpkBoxSize : Nat) :
    FitsEnv M lim st (P2Sub2TailEnv spkBoxSize pubCap privCap sigCap kpkBoxSize) ↔
      FitsEvents M lim st (p2Sub2TailEvents spkBoxSize pubCap privCap sigCap kpkBoxSize) :=
  FitsEnv.eq_iff

-- Concrete `FitsEnv` non-vacuity witness for `P2Sub2TailEnv 64 33 32 64 64` under `coarseCostModel`.
example :
    FitsEnv coarseCostModel
      { staticCount := 64, staticBytes := 67108864, physCap := 536870912, enforced := true }
      coarseCostModel.init
      (P2Sub2TailEnv 64 33 32 64 64) := by
  rw [fitsEnv_p2Sub2TailEnv_iff]
  have hevs : p2Sub2TailEvents 64 33 32 64 64 =
      [.free 8 64, .free 1 33, .free 1 32, .free 1 64, .alloc 64] := by decide
  rw [hevs]
  dsimp only [FitsEvents, FitsEvent, AllocEvent.withinMaxAlloc, FitsStep,
    AllocCostModel.step, coarseCostModel, coarseStep, coarseStepReserve]
  decide

/-! ## 2. Budget-Threaded Placed Substage P2.2 (`+0x0f14 -> +0x1460` or `+0x0f38` Arm 1) -/

set_option maxHeartbeats 1400000 in
/-- Budget-Threaded Placed Kit-Generic Substage P2.2 (`+0x0f14 -> +0x1460` or `+0x0f38` Arm 1)
in CPS form on `stageP1ProgPlaced ext`:
polls `spkKit.getPoll`, delegates `.error e` at `+0x0f38` to `hErr` with `A.pool lim (M.stepEvents evs_poll st) s2`,
and on `.ok r` drops/frees the SPK future, deserializes & clamps the Curve25519 SPK keypair, frees
the cloned record buffers (`p2SpkRecFreeEvents`), and invokes `kpkKit.getShim` reaching `+0x1460`
(`hOk`) with `A.pool lim (M.stepEvents (evs_poll ++ p2Sub2TailEvents spkKit.getBoxSize pubCap.toNat privCap.toNat sigCap.toNat kpkKit.getBoxSize) st) sf`. -/
theorem stageP2_sub2_kits_ext_placed [LibsignalPlacement]
    {M : AllocCostModel} {P : Primitives} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {F : ShaCompress} {BobV1Env : AcceptKeysInput → DRKey → List AllocEvent → Prop}
    {AcceptErrEnv : AcceptKeysInput → List AllocEvent → Prop}
    (ext : String → Option (State → State))
    (hH : StageP2ClosureHooksPlaced A lim ext)
    (hPure : StageP2PureCalleesPlaced4KOfEnv P A lim F BobV1Env AcceptErrEnv ext)
    (spkKit : SignedPreKeyStoreSpec A.repAlloc 0#64)
    (spkEnv : SignedPreKeyStoreBudgetEnv spkKit)
    (hspkOk : SignedPreKeyStoreKitPlacedOk A lim spkKit spkEnv ext)
    (kpkKit : KyberPreKeyStoreSpec A.repAlloc 0#64)
    (kpkEnv : KyberPreKeyStoreBudgetEnv kpkKit)
    (hkpkOk : KyberPreKeyStoreKitPlacedOk A lim kpkKit kpkEnv ext)
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
    (hCode : StoreKit.LibsignalCodeRoLoaded lsmpl s.mem)
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
      StoreKit.LibsignalCodeRoLoaded lsmpl s2.mem →
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
      StoreKit.LibsignalCodeRoLoaded lsmpl sf.mem →
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
  have hstep1 := p2_seg2a_ext_placed_wp (A := A) (lim := lim) ext st s coroPtr ctxPtr spkFutPtr
    (0#64 + spkKit.getFutVtOff) (0#64 + spkKit.getPollOff)
    (coroPtr + 0x398#64) v_a0 v_b0 u_4f8 u_500 hpc hrun hsp_align hx0 hx1 hx19
  refine p2_bind_sepWP_qp_frame_state_placed hCode hstep1 (by sep_focus)
    fun s1 hst01 hpc1 hrun1 hCode1 hregs1 => ?_
  rcases hregs1 with ⟨hsp1, htr1, hx0_1, _, hx8_1, hx19_1, hx21_1, hx23_1, hx25_1, hx26_1, hx27_1,
    hx28_1, hx29_1, hx30_1, hvregs1⟩
  have hsp1_al : s1.spAligned = true := by simpa only [State.spAligned, hsp1] using hsp_align
  have hstk_poll := p2_stackAt_split_of_le s.sp stk spkKit.getPollStack hstk_spk_poll hstk_lt
  refine SepWPp.weaken_frame (Entails.of_eq hstk_poll) (by sep_focus) ?_
  sep_norm
  refine p2_call_rocl_nopanic_steps_frame_placed
    (x := (({ fut := spkFutPtr, self := spkStorePtr, out := s.sp + 0x3e0#64,
              id := spkId } : PreKeyPollCall), stSpk, st))
    hCode1 (hspkOk.getPoll (by decide)) hpc1 hrun1 hsp1_al hx30_1
    (hsp1 ▸ p2_spkGetPoll_pre_intro_placed (henv s1 hst01 htr1) hx0_1 hx8_1 hid_spk hfits_poll)
    (by sep_focus)
    (hnext := fun s2 hst12 hpc2 hrun2 hsp2_1 _ hcs2 hCode2 => ?_)
  dsimp only [kitSpkGetPollSpecE, withEnvPre, kitSpkGetPollSpec]
  rcases hcs2 with ⟨hcs2_19, _, hcs2_21, _, hcs2_23, _, hcs2_25, hcs2_26, hcs2_27, hcs2_28,
    hcs2_29, hvregs2_1⟩
  have hsp2 : s2.sp = s.sp := hsp2_1.trans hsp1
  have hsp2_align : (s2.sp &&& 15#64 == 0#64) = true := by rw [hsp2]; exact hsp_align
  rw [hsp1]
  simp only [sepExists_sepConj_left, sepConj_assoc]
  refine SepWPp.exists_elim fun ans => SepWPp.exists_elim fun evs_poll =>
    SepWPp.pure_elim fun ⟨hrel, htr2_1, hevs_poll⟩ => ?_
  refine SepWPp.weaken_frame (Entails.of_eq hstk_poll.symm) (by sep_focus) ?_
  have htr2 : s2.trace = s.trace ++ spkKit.getEvs spkId ans := by rw [htr2_1, htr1]
  cases ans with
  | error e =>
    have herr := hErr e evs_poll s2 (hst01.trans hst12) hrel hevs_poll hpc2 hrun2 hsp2 htr2
      (hcs2_19.trans hx19_1) (hcs2_21.trans hx21_1) (hcs2_23.trans hx23_1)
      (hcs2_25.trans hx25_1) (hcs2_26.trans hx26_1) (hcs2_27.trans hx27_1)
      (hcs2_28.trans hx28_1) (hcs2_29.trans hx29_1)
      (by rw [hvregs2_1, hvregs1, hvregs]) hCode2
    exact p2_sepWPp_weaken_eq herr (by sep_focus)
  | ok r =>
    dsimp only [spkGetPollOutAt]
    simp only [sepConj_assoc]
    refine p2_sepWPp_pure_elim_frame (spkKit.RecOk r) (by sep_focus) fun hrec_ok => ?_
    obtain ⟨spkPubBytes, spkPrivBytes, hpub_len, hpriv_len, hpub_eq, hpriv_eq⟩ :=
      hrec_wf r hrel hrec_ok
    refine SepWPp.weaken_frame
      (p2_signedPreKeyStructAt_unpack A.repAlloc (s.sp + 0x3e0#64) r.signedPreKey)
      (by sep_focus) ?_
    simp only [sepExists_sepConj_left, sepConj_assoc]
    refine SepWPp.exists_elim fun pubCap => SepWPp.exists_elim fun pubPtr =>
      SepWPp.exists_elim fun privCap => SepWPp.exists_elim fun privPtr =>
      SepWPp.exists_elim fun sigCap => SepWPp.exists_elim fun sigPtr =>
      SepWPp.exists_elim fun pad32 => ?_
    have hpub_bv : BitVec.ofNat 64 r.signedPreKey.publicKey.length = 33#64 := by
      rw [hpub_eq]; simp [hpub_len]
    have hpriv_bv : BitVec.ofNat 64 r.signedPreKey.privateKey.length = 32#64 := by
      rw [hpriv_eq, hpriv_len]
    rw [hpub_bv, hpriv_bv, hpub_eq, hpriv_eq]
    refine SepWPp.weaken_frame
      (p2_vecU8Buf_nonempty A.repAlloc pubCap pubPtr (5#8 :: spkPubBytes) (by simp))
      (by sep_focus) ?_
    simp only [sepConj_assoc, RustCliAllocBudget.repAlloc_live]
    refine SepWPp.pure_elim fun ⟨hpub_le, _, hpub_nz, hpub_ne2, hpub_ne1⟩ => ?_
    refine SepWPp.weaken_frame
      (p2_vecU8Buf_nonempty A.repAlloc privCap privPtr spkPrivBytes (by omega))
      (by sep_focus) ?_
    simp only [sepConj_assoc, RustCliAllocBudget.repAlloc_live]
    refine SepWPp.pure_elim fun ⟨hpriv_le, _, hpriv_nz, _, _⟩ => ?_
    have hpub_cap : 33 ≤ pubCap.toNat := by simpa [hpub_len] using hpub_le
    have hpriv_cap : 32 ≤ privCap.toNat := by simpa [hpriv_len] using hpriv_le
    let st_poll := M.stepEvents evs_poll st
    have hstep3 := p2_seg2b_gen_placed_wp (A := A) (lim := lim) ext st_poll s2 coroPtr spkFutPtr
      (0#64 + spkKit.getFutVtOff) (0#64 + spkKit.getFutDropOff)
      pubCap pubPtr privCap privPtr sigCap sigPtr
      (coroPtr + 0x398#64) v_a0 v_b0 u_90 (coroPtr + 0x398#64) v_a0 v_b0 u_b8 u_d0
      hpc2 hrun2 hsp2_align hpub_ne2 (spkKit.getFutDrop_ne_zero rfl)
      (hcs2_19.trans hx19_1) (hcs2_21.trans hx21_1) (hcs2_23.trans hx23_1) (hcs2_26.trans hx26_1)
    have hvt0 : (0#64 + spkKit.getFutVtOff) + 0x0#64 = 0#64 + spkKit.getFutVtOff :=
      BitVec.add_zero _
    rw [hsp2, hvt0] at hstep3
    refine p2_bind_sepWP_qp_frame_state_placed hCode2 hstep3 (by sep_focus)
      fun s3 hst23 hpc3 hrun3 hCode3 hregs3 => ?_
    rcases hregs3 with ⟨hsp3, htr3_2, _, hx19_3, hx20_3, hx21_3, hx22_3, hx23_3, hx24_3, hx25_3,
      hx26_3, hx27_3, hx28_3, hx29_3, hx30_3, hvregs3_2⟩
    have hsp3_al : s3.spAligned = true := by simpa only [State.spAligned, hsp3] using hsp_align
    refine p2_call_rocl_nopanic_steps_frame_placed (x := ()) (P_spec := emp)
      hCode3 (hspkOk.getFutDrop (by decide)) hpc3 hrun3 hsp3_al hx30_3
      (Entails.refl emp) (emp_sepConj _).symm
      (hnext := fun s4 hst34 hpc4 hrun4 hsp4_3 _ hcs4 hCode4 => ?_)
    dsimp only [futDropBudgetSpec]
    refine SepWPp.pure_elim fun ⟨htr4_3, hvm34⟩ => ?_
    refine SepWPp.transport_budgetPool hvm34 (by sep_focus) ?_
    rcases hcs4 with ⟨hcs4_19, hcs4_20, hcs4_21, hcs4_22, hcs4_23, hcs4_24, hcs4_25, hcs4_26,
      hcs4_27, hcs4_28, hcs4_29, hvregs4_3⟩
    have hsp4 : s4.sp = s.sp := hsp4_3.trans hsp3
    have hsp4_align : (s4.sp &&& 15#64 == 0#64) = true := by rw [hsp4]; exact hsp_align
    refine SepWPp.weaken_frame (spkKit.getBoxAt_memRegion spkFutPtr spkStorePtr spkId 1#8)
      (by sep_focus) ?_
    refine SepWPp.weaken_frame
      (p2_preKeyRecordOut64_tail_to_memRegion88 (s.sp + 0x3e0#64)
        pubCap pubPtr 33#64 privCap privPtr 32#64 sigCap sigPtr
        (BitVec.ofNat 64 r.signedPreKey.signature.length)
        r.signedPreKey.timestamp (pad32 ++ r.signedPreKey.id))
      (by sep_focus) ?_
    have hstk_alloc := p2_stackAt_split_of_le s.sp stk allocHookStack
      (Nat.le_trans p2_alloc_le_pure hstk_pure) hstk_lt
    refine SepWPp.weaken_frame (Entails.of_eq hstk_alloc) (by sep_focus) ?_
    have hstep5 := p2_seg2c_hooks_placed_wp ext hH st_poll s4 coroPtr spkFutPtr
      (0#64 + spkKit.getFutVtOff) pubCap pubPtr privPtr sigPtr spkKit.getBoxSize
      hpc4 hrun4 hsp4_align hpub_ne1 spkKit.getBoxSize_ne_zero spkKit.getBoxSize_lt
      (hcs4_19.trans hx19_3) (hcs4_20.trans hx20_3) (hcs4_21.trans hx21_3)
      (hcs4_22.trans hx22_3) (hcs4_23.trans hx23_3) (hcs4_24.trans hx24_3)
      (hcs4_26.trans hx26_3) (hcs4_28.trans hx28_3)
    rw [hsp4] at hstep5
    refine p2_bind_sepWP_qp_frame_state_placed hCode4 hstep5 (by sep_focus)
      fun s5 hst45 hpc5 hrun5 hCode5 hregs5 => ?_
    rcases hregs5 with ⟨hsp5, htr5_4, hx0_5, hx1_5, hx2_5, hx3_5, hx8_5, hx19_5, hx20_5, hx22_5,
      _, hx25_5, _, hx27_5, hx28_5, hx29_5, hx30_5, hvregs5_4⟩
    have hsp5_al : s5.spAligned = true := by simpa only [State.spAligned, hsp5] using hsp_align
    refine SepWPp.weaken_frame (Entails.of_eq hstk_alloc.symm) (by sep_focus) ?_
    have hstk_kp1 := p2_stackAt_split_of_le s.sp stk 176
      (Nat.le_trans p2_kp176_le_pure hstk_pure) hstk_lt
    have hstk_kp2 := stackAt_176_keypair_eq s.sp
    refine SepWPp.weaken_frame (Entails.of_eq hstk_kp1) (by sep_focus) ?_
    refine SepWPp.weaken_frame (Entails.of_eq hstk_kp2) (by sep_focus) ?_
    sep_norm
    let st_debox := M.stepEvents (rustDeallocEvents spkKit.getBoxSize 8) st_poll
    refine p2_call_nopanic_lscl_steps_frame_placed
      (x := (pubPtr, spkPubBytes, privPtr, spkPrivBytes, s.sp + 0xa90#64))
      (T := (pubPtr ↦ₛ (5#8 :: spkPubBytes)) ∗ (privPtr ↦ₛ spkPrivBytes) ∗
        memRegion (s.sp + 0xa90#64) 65 ∗ cells (s.sp - 176#64) 8 ∗ cells (s.sp - 112#64) 14)
      hCode5 hPure.curveKeyPairSerde hpc5 hrun5 hsp5_al hx30_5
      (by
        dsimp only [
          LibsignalBinary.Proofs.E2E.Pqxdh.ResponderStore.KeyPairCalleesBudget.curveKeyPairSerdeBudgetSpec,
          LibsignalBinary.Proofs.E2E.Pqxdh.ResponderStore.KeyPairCalleesAuxBudget.curveKeyPairSerdeBudgetSpec,
          withVmPreserved, curveKeyPairSerdeOkSpec]
        rw [hsp5])
      (And.intro hx0_5 (And.intro hx1_5 (And.intro hx2_5
        (And.intro hx3_5 (And.intro hx8_5 (And.intro hpub_len hpriv_len))))))
      (by sep_focus)
      (hnext := fun s6 hst56 hpc6 hrun6 hsp6_5 _ hcs6 hCode6 => ?_)
    dsimp only [
      LibsignalBinary.Proofs.E2E.Pqxdh.ResponderStore.KeyPairCalleesBudget.curveKeyPairSerdeBudgetSpec,
      LibsignalBinary.Proofs.E2E.Pqxdh.ResponderStore.KeyPairCalleesAuxBudget.curveKeyPairSerdeBudgetSpec,
      withVmPreserved, curveKeyPairSerdeOkSpec]
    rcases hcs6 with ⟨hcs6_19, hcs6_20, _, hcs6_22, _, _, hcs6_25, _, hcs6_27, hcs6_28, hcs6_29,
      hvregs6_5⟩
    have hsp6 : s6.sp = s.sp := hsp6_5.trans hsp5
    have hsp6_align : (s6.sp &&& 15#64 == 0#64) = true := by rw [hsp6]; exact hsp_align
    rw [hsp5, show (s.sp + 0xa90#64) + 1#64 = s.sp + 0xa91#64 by bv_omega,
      show (s.sp + 0xa90#64) + 33#64 = s.sp + 0xab1#64 by bv_omega]
    simp only [sepConj_assoc]
    refine SepWPp.pure_elim fun hvm56 => SepWPp.pure_elim fun htr6_5 => ?_
    refine SepWPp.transport_budgetPool hvm56 (by sep_focus) ?_
    refine SepWPp.weaken_frame (Entails.of_eq hstk_kp2.symm) (by sep_focus) ?_
    refine SepWPp.weaken_frame (Entails.of_eq hstk_kp1.symm) (by sep_focus) ?_
    have hclamp_len : (clampBv8List spkPrivBytes).length = 32 := clampBv8List_length hpriv_len
    obtain ⟨b0, b1, b2, b3, b4, b5, b6, b63, c0, c1, c2, c3, c4, c5, c6,
      w0, w1, w2, w3, w4, w5, w6, u0_kp, u1_kp, u2_kp, u3_kp, u4_kp, u5_kp, u6_kp, u7_kp,
      hpk_words, hsk_words, hkp64_eq, hkp_lo, hkp_hi⟩ := exists_keyPair64_decomp hpub_len hclamp_len
    have ha91_eq :
        ((s.sp + 0xa91#64) ↦ₛ spkPubBytes) ∗ ((s.sp + 0xab1#64) ↦ₛ clampBv8List spkPrivBytes) =
          keyPair64UnalignedAt (s.sp + 0xa91#64) b0 b1 b2 b3 b4 b5 b6 w0 w1 w2 w3 w4 w5 w6 b63 := by
      rw [show s.sp + 0xab1#64 = (s.sp + 0xa91#64) + 32#64 by bv_omega]
      exact hkp64_eq (s.sp + 0xa91#64)
    refine SepWPp.weaken_frame (Entails.of_eq ha91_eq) (by sep_focus) ?_
    refine SepWPp.weaken_frame (p2_vecU8Buf_rejoin pubPtr pubCap (5#8 :: spkPubBytes) hpub_le)
      (by sep_focus) ?_
    refine SepWPp.weaken_frame (p2_vecU8Buf_rejoin privPtr privCap spkPrivBytes hpriv_le)
      (by sep_focus) ?_
    have hmr88 : memRegion (s.sp + 0x3e0#64) 9 ∗ memRegion (s.sp + 0x3e9#64) 79 =
        memRegion (s.sp + 0x3e0#64) 88 :=
      (ProofLib.memRegion_split' (b := s.sp + 0x3e0#64) (n := 9) (k := 79)
        (b' := s.sp + 0x3e9#64) rfl (by bv_omega) (by decide)).symm
    refine SepWPp.weaken_frame (Entails.of_eq hmr88.symm) (by sep_focus) ?_
    refine SepWPp.weaken_frame (Entails.of_eq (memRegion_9_sp3e0_eq s.sp)) (by sep_focus) ?_
    simp only [sepExists_sepConj_left, sepConj_assoc]
    refine SepWPp.exists_elim fun u_3e0 => ?_
    simp only [sepExists_sepConj_right, sepExists_sepConj_left, sepConj_assoc]
    refine SepWPp.exists_elim fun b_3e8 => ?_
    refine SepWPp.weaken_frame (Entails.of_eq hstk_alloc) (by sep_focus) ?_
    sep_norm
    have hnext7 : ∀ (v90 : BitVec 64) (hv90 : v90 = sigCap) (st7 : M.σ)
        (hst7 : st7 = M.stepEvents
          (evs_poll ++ p2SpkRecFreeEvents spkKit.getBoxSize
            pubCap.toNat privCap.toNat v90.toNat) st)
        (s7 : State),
        Steps (stageP1ProgPlaced ext) s6 s7 →
        s7.pc = 0#64 + kpkKit.getShimOff → s7.status = .Running →
        StoreKit.LibsignalCodeRoLoaded lsmpl s7.mem →
        s7.sp = s.sp ∧ s7.trace = s6.trace ∧
        s7.readReg64 .x0 = kyberStorePtr ∧ s7.readReg64 .x1 = kyberPreKeyId.zeroExtend 64 ∧
        s7.readReg64 .x19 = coroPtr ∧ s7.readReg64 .x20 = sigPtr ∧
        s7.readReg64 .x21 = v_b0 ∧ s7.readReg64 .x22 = pubPtr ∧
        s7.readReg64 .x23 = v_a0 ∧ s7.readReg64 .x25 = s6.readReg64 .x25 ∧
        s7.readReg64 .x26 = coroPtr + 0x398#64 ∧ s7.readReg64 .x27 = s6.readReg64 .x27 ∧
        s7.readReg64 .x28 = s.sp + 0xa90#64 ∧ s7.readReg64 .x29 = s6.readReg64 .x29 ∧
        s7.readReg64 .x30 = stageP1EntryPlaced + 0x1460#64 ∧
        calleeSavedVRegs s7 = calleeSavedVRegs s6 →
        SepWPp (stageP1ProgPlaced ext) ret s7
          ((((s.sp + 0xa90#64) ↦₈ 0#8) ∗
            keyPair64UnalignedAt (s.sp + 0xa91#64) b0 b1 b2 b3 b4 b5 b6 w0 w1 w2 w3 w4 w5 w6 b63 ∗
            bytes7At (s.sp + 0x930#64) b0 b1 b2 b3 b4 b5 b6 ∗
            keyPair64UnalignedAt (coroPtr + 0x398#64) b0 b1 b2 b3 b4 b5 b6 w0 w1 w2 w3 w4 w5 w6 b63 ∗
            ((s.sp + 0x90#64) ↦₆₄ v90) ∗ ((s.sp + 0x98#64) ↦₆₄ (coroPtr + 0x398#64)) ∗
            ((s.sp + 0xa0#64) ↦₆₄ v_a0) ∗ ((s.sp + 0xb0#64) ↦₆₄ v_b0) ∗
            ((s.sp + 0xb8#64) ↦₆₄ privCap) ∗ ((s.sp + 0xd0#64) ↦₆₄ privPtr) ∗
            ((s.sp + 0x3e0#64) ↦₆₄ w6) ∗ ((s.sp + 0x3e8#64) ↦₈ b63) ∗
            A.pool lim st7 s7 ∗ stackAt s.sp allocHookStack ∗
            ((coroPtr + 0x3f8#64) ↦₆₄ kyberStorePtr) ∗ ((coroPtr + 0x400#64) ↦₆₄ kpkKit.kpk_vt) ∗
            ((coroPtr + 0x468#64) ↦₆₄ msgPtr) ∗ ((msgPtr + 0x90#64) ↦₆₄ kyberCtCap) ∗
            ((msgPtr + 0xa0#64) ↦₃₂ kyberPreKeyId) ∗
            ((kpkKit.kpk_vt + 0x18#64) ↦₆₄ᵣ (0#64 + kpkKit.getShimOff))) ∗
           (memRegion (s.sp - BitVec.ofNat 64 stk) (stk - allocHookStack) ∗
            memRegion (s.sp + 0x3e9#64) 79 ∗ ((s.sp + 0xc0#64) ↦₆₄ ctxPtr) ∗
            ((coroPtr + 0x4f8#64) ↦₆₄ spkFutPtr) ∗
            ((coroPtr + 0x500#64) ↦₆₄ (0#64 + spkKit.getFutVtOff)) ∗
            ((0#64 + spkKit.getFutVtOff) ↦₆₄ᵣ (0#64 + spkKit.getFutDropOff)) ∗
            ((0#64 + spkKit.getFutVtOff + 8#64) ↦₆₄ᵣ BitVec.ofNat 64 spkKit.getBoxSize) ∗
            ((0#64 + spkKit.getFutVtOff + 0x10#64) ↦₆₄ᵣ 8#64) ∗
            ((0#64 + spkKit.getFutVtOff + 0x18#64) ↦₆₄ᵣ (0#64 + spkKit.getPollOff)) ∗
            spkKit.storeAt spkStorePtr (spkKit.getUpdate stSpk spkId (.ok r)) ∗ Frame))
          Q Qp := by
      intro v90 hv90 st7 hst7 s7 hst67 hpc7 hrun7 hCode7 hregs7
      subst hv90
      rcases hregs7 with ⟨hsp7, htr7_6, hx0_7, hx1_7, hx19_7, hx20_7, hx21_7, _, hx23_7, hx25_7,
        hx26_7, hx27_7, hx28_7, hx29_7, hx30_7, hvregs7_6⟩
      have hsp7_al : s7.spAligned = true := by simpa only [State.spAligned, hsp7] using hsp_align
      refine SepWPp.weaken_frame (Entails.of_eq hstk_alloc.symm) (by sep_focus) ?_
      refine SepWPp.weaken_frame (Entails.of_eq ha91_eq.symm) (by sep_focus) ?_
      refine SepWPp.weaken_frame
        (sp_a90_65_entails_memRegion (s.sp + 0xa90#64) 0#8 spkPubBytes (clampBv8List spkPrivBytes)
          hpub_len hclamp_len)
        (by sep_focus) ?_
      refine SepWPp.weaken_frame (sp3e0_9_entails_memRegion s.sp w6 b63) (by sep_focus) ?_
      refine SepWPp.weaken_frame (Entails.of_eq hmr88) (by sep_focus) ?_
      have hstk_kpk := p2_stackAt_split_of_le s.sp stk kpkKit.getShimStack hstk_kpk_shim hstk_lt
      refine SepWPp.weaken_frame (Entails.of_eq hstk_kpk) (by sep_focus) ?_
      sep_norm
      have htr7 : s7.trace = s.trace ++ spkKit.getEvs spkId (.ok r) := by
        rw [htr7_6, htr6_5, htr5_4, htr4_3, htr3_2, htr2]
      have hx1_7_32 : s7.readReg32 .x1 = kyberPreKeyId := by
        change (s7.readReg64 .x1).setWidth 32 = kyberPreKeyId
        rw [hx1_7, p2_zext64_trunc32_id]
      have hfits_shim : FitsEnv M lim st7 (BoxAllocEnv kpkKit.getBoxSize) := by
        rw [hst7]
        exact hfits_kpk r evs_poll pubCap.toNat privCap.toNat v90.toNat
          hrel hrec_ok hevs_poll hpub_cap hpriv_cap
      refine p2_call_rocl_nopanic_steps_frame_placed
        (x := (({ self := kyberStorePtr, id := kyberPreKeyId } : PreKeyShimCall), st7))
        hCode7 (hkpkOk.getShim (by decide)) hpc7 hrun7 hsp7_al hx30_7
        (hsp7 ▸ p2_kpkGetShim_pre_intro_placed hx0_7 hx1_7_32 hfits_shim)
        (by sep_focus)
        (hnext := fun sf hst7f hpcf hrunf hspf_7 _ hcsf hCodef => ?_)
      dsimp only [kitKpkGetShimSpec]
      rcases hcsf with ⟨hcsf_19, hcsf_20, hcsf_21, _, hcsf_23, _, hcsf_25, hcsf_26, hcsf_27,
        hcsf_28, hcsf_29, hvregsf_7⟩
      rw [hsp7]
      sep_norm
      refine SepWPp.exists_elim fun evs_kpk =>
        SepWPp.pure_elim fun ⟨hx1_f, hfut_nz, hfut_al, htrf_7, hevs_kpk⟩ => ?_
      have hevs_kpk_eq : evs_kpk = boxAllocEvents kpkKit.getBoxSize :=
        (boxAllocEnv_iff_eq kpkKit.getBoxSize evs_kpk).mp hevs_kpk
      have hpool_eq :
          M.stepEvents evs_kpk st7 =
            M.stepEvents
              (evs_poll ++ p2Sub2TailEvents spkKit.getBoxSize
                pubCap.toNat privCap.toNat v90.toNat kpkKit.getBoxSize) st := by
        rw [hevs_kpk_eq, hst7]
        unfold p2Sub2TailEvents
        simp only [M.stepEvents_append, List.append_assoc]
      rw [hpool_eq]
      refine SepWPp.weaken_frame (Entails.of_eq hstk_kpk.symm) (by sep_focus) ?_
      have hsteps_all :=
        hst01.trans (hst12.trans (hst23.trans (hst34.trans (hst45.trans (hst56.trans (hst67.trans hst7f))))))
      have hok := hOk r spkPubBytes spkPrivBytes evs_poll
        pubCap privCap privPtr v90 sigPtr (sf.readReg64 .x0)
        b0 b1 b2 b3 b4 b5 b6 b63 c0 c1 c2 c3 c4 c5 c6
        w0 w1 w2 w3 w4 w5 w6 u0_kp u1_kp u2_kp u3_kp u4_kp u5_kp u6_kp u7_kp sf
        hsteps_all hrel hrec_ok hevs_poll hpub_cap hpriv_cap
        hpub_len hpriv_len hpub_eq hpriv_eq hpk_words hsk_words hkp_lo hkp_hi
        hpcf hrunf (hspf_7.trans hsp7) (by rw [htrf_7, htr7]) rfl hx1_f hfut_nz hfut_al
        (hcsf_19.trans hx19_7) (hcsf_20.trans hx20_7) (hcsf_21.trans hx21_7)
        (hcsf_23.trans hx23_7)
        (by rw [hcsf_25, hx25_7, hcs6_25, hx25_5, hcs4_25, hx25_3, hcs2_25, hx25_1])
        (hcsf_26.trans hx26_7)
        (by rw [hcsf_27, hx27_7, hcs6_27, hx27_5, hcs4_27, hx27_3, hcs2_27, hx27_1])
        (hcsf_28.trans hx28_7)
        (by rw [hcsf_29, hx29_7, hcs6_29, hx29_5, hcs4_29, hx29_3, hcs2_29, hx29_1])
        (by rw [hvregsf_7, hvregs7_6, hvregs6_5, hvregs5_4, hvregs4_3, hvregs3_2, hvregs2_1,
          hvregs1, hvregs])
        hCodef
      exact p2_sepWPp_weaken_eq hok (by sep_focus)
    by_cases hsig : sigCap = 0#64
    · rw [hsig]
      refine SepWPp.weaken_frame (p2_vecU8Buf_zero A.repAlloc sigPtr r.signedPreKey.signature)
        (by sep_focus) ?_
      sep_norm
      have hstep7 := p2_seg2d_sig0_hooks_placed_wp ext hH st_debox s6 coroPtr msgPtr
        pubCap pubPtr privCap privPtr sigPtr kyberCtCap kyberStorePtr kpkKit.kpk_vt
        (0#64 + kpkKit.getShimOff) v_a0 v_b0 u_3e0 kyberPreKeyId
        b0 b1 b2 b3 b4 b5 b6 b63 s0_b s1_b s2_b s3_b s4_b s5_b s6_b
        c0_init c1_init c2_init c3_init c4_init c5_init c6_init c63_init b_3e8
        w0 w1 w2 w3 w4 w5 w6 cw0_init cw1_init cw2_init cw3_init cw4_init cw5_init cw6_init
        hpc6 hrun6 hsp6_align hpub_nz hpriv_nz hkyber_nz
        (hcs6_19.trans hx19_5) (hcs6_20.trans hx20_5) (hcs6_22.trans hx22_5) (hcs6_28.trans hx28_5)
      rw [hsp6] at hstep7
      have hst7_0 :
          M.stepEvents
            (rustDeallocEvents pubCap.toNat 1 ++ rustDeallocEvents privCap.toNat 1) st_debox =
          M.stepEvents
            (evs_poll ++ p2SpkRecFreeEvents spkKit.getBoxSize
              pubCap.toNat privCap.toNat (0#64).toNat) st := by
        dsimp only [st_debox, st_poll, p2SpkRecFreeEvents]
        simp only [BitVec.toNat_ofNat, Nat.zero_mod, ↓reduceIte, M.stepEvents_append,
          List.append_assoc]
      exact p2_bind_sepWP_qp_frame_state_placed hCode6 hstep7 (by sep_focus)
        (hnext7 0#64 hsig.symm _ hst7_0)
    · refine SepWPp.weaken_frame
        (p2_vecU8Buf_dealloc_nonzero A.repAlloc sigCap sigPtr r.signedPreKey.signature hsig)
        (by sep_focus) ?_
      sep_norm
      have hstep7 := p2_seg2d_sigNz_hooks_placed_wp ext hH st_debox s6 coroPtr msgPtr
        pubCap pubPtr privCap privPtr sigCap sigPtr kyberCtCap kyberStorePtr kpkKit.kpk_vt
        (0#64 + kpkKit.getShimOff) v_a0 v_b0 u_3e0 kyberPreKeyId
        b0 b1 b2 b3 b4 b5 b6 b63 s0_b s1_b s2_b s3_b s4_b s5_b s6_b
        c0_init c1_init c2_init c3_init c4_init c5_init c6_init c63_init b_3e8
        w0 w1 w2 w3 w4 w5 w6 cw0_init cw1_init cw2_init cw3_init cw4_init cw5_init cw6_init
        hpc6 hrun6 hsp6_align hpub_nz hpriv_nz hsig hkyber_nz
        (hcs6_19.trans hx19_5) (hcs6_20.trans hx20_5) (hcs6_22.trans hx22_5) (hcs6_28.trans hx28_5)
      rw [hsp6] at hstep7
      have hsig_toNat : sigCap.toNat ≠ 0 := fun h0 =>
        hsig (BitVec.eq_of_toNat_eq (h0.trans (by simp)))
      have hst7_nz :
          M.stepEvents
            (rustDeallocEvents pubCap.toNat 1 ++ rustDeallocEvents privCap.toNat 1 ++
              rustDeallocEvents sigCap.toNat 1) st_debox =
          M.stepEvents
            (evs_poll ++ p2SpkRecFreeEvents spkKit.getBoxSize
              pubCap.toNat privCap.toNat sigCap.toNat) st := by
        dsimp only [st_debox, st_poll, p2SpkRecFreeEvents]
        simp only [hsig_toNat, ↓reduceIte, M.stepEvents_append, List.append_assoc]
      exact p2_bind_sepWP_qp_frame_state_placed hCode6 hstep7 (by sep_focus)
        (hnext7 sigCap rfl _ hst7_nz)

abbrev stageP2_sub2_kits_4k_placed := @stageP2_sub2_kits_ext_placed
abbrev stageP2_sub2_kits_hooks_placed := @stageP2_sub2_kits_ext_placed

theorem stageP2_sub2_kits_placed [LibsignalPlacement]
    {M : AllocCostModel} {P : Primitives} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {F : ShaCompress} {BobV1Env : AcceptKeysInput → DRKey → List AllocEvent → Prop}
    {AcceptErrEnv : AcceptKeysInput → List AllocEvent → Prop}
    (ext : String → Option (State → State))
    (hH : StageP2ClosureHooksPlaced A lim ext)
    (hPure : StageP2PureCalleesPlacedOfEnv P A lim F BobV1Env AcceptErrEnv ext)
    (spkKit : SignedPreKeyStoreSpec A.repAlloc 0#64)
    (spkEnv : SignedPreKeyStoreBudgetEnv spkKit)
    (hspkOk : SignedPreKeyStoreKitPlacedOk A lim spkKit spkEnv ext)
    (kpkKit : KyberPreKeyStoreSpec A.repAlloc 0#64)
    (kpkEnv : KyberPreKeyStoreBudgetEnv kpkKit)
    (hkpkOk : KyberPreKeyStoreKitPlacedOk A lim kpkKit kpkEnv ext)
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
    (hCode : StoreKit.LibsignalCodeRoLoaded lsmpl s.mem)
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
      StoreKit.LibsignalCodeRoLoaded lsmpl s2.mem →
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
      StoreKit.LibsignalCodeRoLoaded lsmpl sf.mem →
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
      Q Qp :=
  stageP2_sub2_kits_ext_placed ext hH hPure.to_4K
    spkKit spkEnv hspkOk kpkKit kpkEnv hkpkOk
    stk hstk_pure hstk_spk_poll hstk_kpk_shim hstk_lt
    ret st s0 s Frame Q (Qp := Qp)
    coroPtr ctxPtr msgPtr spkStorePtr spkFutPtr kyberStorePtr kyberCtCap
    v_a0 v_b0 u_90 u_b8 u_d0 u_4f8 u_500 spkId kyberPreKeyId stSpk
    s0_b s1_b s2_b s3_b s4_b s5_b s6_b
    c0_init c1_init c2_init c3_init c4_init c5_init c6_init c63_init
    cw0_init cw1_init cw2_init cw3_init cw4_init cw5_init cw6_init
    hfits_poll hfits_kpk hCode henv hid_spk hrec_wf hkyber_nz
    hpc hrun hsp_align hvregs hx0 hx1 hx19 hErr hOk

theorem stageP2_sub2_kits_seqEnv_ext_placed [LibsignalPlacement]
    {M : AllocCostModel} {P : Primitives} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {F : ShaCompress} {BobV1Env : AcceptKeysInput → DRKey → List AllocEvent → Prop}
    {AcceptErrEnv : AcceptKeysInput → List AllocEvent → Prop}
    (ext : String → Option (State → State))
    (hH : StageP2ClosureHooksPlaced A lim ext)
    (hPure : StageP2PureCalleesPlaced4KOfEnv P A lim F BobV1Env AcceptErrEnv ext)
    (spkKit : SignedPreKeyStoreSpec A.repAlloc 0#64)
    (spkEnv : SignedPreKeyStoreBudgetEnv spkKit)
    (hspkOk : SignedPreKeyStoreKitPlacedOk A lim spkKit spkEnv ext)
    (kpkKit : KyberPreKeyStoreSpec A.repAlloc 0#64)
    (kpkEnv : KyberPreKeyStoreBudgetEnv kpkKit)
    (hkpkOk : KyberPreKeyStoreKitPlacedOk A lim kpkKit kpkEnv ext)
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
    (hfits : FitsEnv M lim st
      (SeqEnv (spkEnv.getPollEnv stSpk spkId)
        (SeqEnv FreeOnlyEvs (BoxAllocEnv kpkKit.getBoxSize))))
    (hCode : StoreKit.LibsignalCodeRoLoaded lsmpl s.mem)
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
      StoreKit.LibsignalCodeRoLoaded lsmpl s2.mem →
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
      StoreKit.LibsignalCodeRoLoaded lsmpl sf.mem →
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
      Q Qp :=
  stageP2_sub2_kits_ext_placed ext hH hPure
    spkKit spkEnv hspkOk kpkKit kpkEnv hkpkOk
    stk hstk_pure hstk_spk_poll hstk_kpk_shim hstk_lt
    ret st s0 s Frame Q (Qp := Qp)
    coroPtr ctxPtr msgPtr spkStorePtr spkFutPtr kyberStorePtr kyberCtCap
    v_a0 v_b0 u_90 u_b8 u_d0 u_4f8 u_500 spkId kyberPreKeyId stSpk
    s0_b s1_b s2_b s3_b s4_b s5_b s6_b
    c0_init c1_init c2_init c3_init c4_init c5_init c6_init c63_init
    cw0_init cw1_init cw2_init cw3_init cw4_init cw5_init cw6_init
    hfits.seq_left
    (fun _ evs_poll pubCap privCap sigCap _ _ hevs_poll _ _ => by
      have h1 := (hfits.seq_right hevs_poll).seq_right
        (p2SpkRecFreeEvents_freeOnly spkKit.getBoxSize pubCap privCap sigCap)
      rwa [← M.stepEvents_append] at h1)
    hCode henv hid_spk hrec_wf hkyber_nz
    hpc hrun hsp_align hvregs hx0 hx1 hx19 hErr hOk

abbrev stageP2_sub2_kits_seqEnv_placed [LibsignalPlacement]
    {M : AllocCostModel} {P : Primitives} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {F : ShaCompress} {BobV1Env : AcceptKeysInput → DRKey → List AllocEvent → Prop}
    {AcceptErrEnv : AcceptKeysInput → List AllocEvent → Prop}
    (ext : String → Option (State → State))
    (hH : StageP2ClosureHooksPlaced A lim ext)
    (hPure : StageP2PureCalleesPlacedOfEnv P A lim F BobV1Env AcceptErrEnv ext) :=
  @stageP2_sub2_kits_seqEnv_ext_placed _ M P A lim F BobV1Env AcceptErrEnv ext hH hPure.to_4K

end LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP2Sub2PlacedBudget
