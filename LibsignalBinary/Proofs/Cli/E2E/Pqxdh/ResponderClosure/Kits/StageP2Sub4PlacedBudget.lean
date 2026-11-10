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
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP2BlocksA3PlacedBudget
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP2DefsPlacedBudget
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP2Sub1PlacedBudget
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP2Sub2PlacedBudget
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP2Sub4AuxPlacedBudget
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP2Sub4Placed
public import LibsignalBinary.Proofs.PublicApi.StoreKit.IdentitySelfStoreKitBudget
public import LibsignalBinary.Proofs.PublicApi.StoreKit.PlacedBudget
public import LibsignalBinary.Proofs.PublicApi.StoreKit.PreKeyStoreKitBudget
import Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic
import ProofLib.SepLogic.WPp
import LibsignalBinary.Proofs.Common.SharedHelpers
meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP2Sub1
import LibsignalBinary.Proofs.TripleRatchet.Wire.TryFromPostDefs

/-!
# Budget-Threaded Relocatable Stage P2 Substage P2.4 (`Some` Branch)

Defines `P2Sub4SomeFixedPollEnv` and proves `RustCliAllocBudget M` / `VmPreserved` placed CPS
Substage P2.4-Some (`+0x0d5c → +0x36ac` or `+0x09c4` Arm 3) on Block `518`.
-/

@[expose] public section

set_option autoImplicit false

namespace LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP2Sub4PlacedBudget

open Arm64 ProofLib ProofLib.ProgramReflection SepProp
open CryptoGames CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open CryptoVerification CryptoVerification.RustHeap
open CryptoVerification.RecordCodecs CryptoVerification.RecordCodecsBinary
open CryptoVerification.LibsignalSession CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchet hiding
  publicKeySerializeSpec publicKeySerializeSpecWithStack
open CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalPublicApi CryptoVerification.LibsignalPublicApiRepr
open CryptoVerification.LibsignalPublicApi.StoreSession
open CryptoVerification.LibsignalPublicApi.StoreKit hiding
  kitPreKeyGetShimSpec kitPreKeyGetPollSpec kitPreKeyGetPollSpecE kitKpShimSpec
  PreKeyStoreKitPlacedOk IdentitySelfStoreKitPlacedOkI
open CryptoVerification.E2E.Bin
open CryptoVerification.E2E.Pqxdh
open CryptoVerification.E2E.Pqxdh.Shared
open CryptoVerification.E2E.Pqxdh.Initiator
open CryptoVerification.E2E.Pqxdh.WireEntries
open CryptoVerification.E2E.Pqxdh.ResponderCore
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
  p2_seg4a_ext_placed_wp
  p2_seg4b_ext_placed_wp
  p2_seg4c_gen_placed_wp
  p2_pkGetShim_pre_intro_placed
  p2_pkGetPoll_pre_intro_placed
  p2_kpShim_pre_intro_placed
  stageP2_sub4_some_tail_kits_ext_placed
  stageP2_sub4_some_tail_kits_4k_placed
  stageP2_sub4_some_tail_kits_hooks_placed
  stageP2_sub4_some_tail_kits_placed
  stageP2_sub4_some_kits_ext_placed
  stageP2_sub4_some_kits_4k_placed
  stageP2_sub4_some_kits_hooks_placed
  stageP2_sub4_some_kits_placed
open LibsignalBinary.Heap (
  AllocCostModel AllocEvent BudgetLimits FitsEnv FitsEvent FitsEvents FitsStep
  FreeOnlyEvs RustCliAllocBudget SeqEnv VmPreserved coarseCostModel coarseStep
  coarseStepReserve
)
open LibsignalBinary.Proofs.PublicApi.StoreKit.PreKeyStoreKitBudget (
  BoxAllocEnv PreKeyStoreBudgetEnv futDropBudgetSpec kitPreKeyGetShimSpec
  kitPreKeyGetPollSpec kitPreKeyGetPollSpecE
)
open LibsignalBinary.Proofs.PublicApi.StoreKit.IdentitySelfStoreKitBudget (
  IdentitySelfStoreBudgetEnv
)
open LibsignalBinary.Proofs.PublicApi.StoreKit.PlacedBudget (
  PreKeyStoreKitPlacedOk IdentitySelfStoreKitPlacedOkI
)
open LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP2DefsPlacedBudget (
  StageP2ClosureHooksPlaced
  StageP2PureCalleesPlaced StageP2PureCalleesPlaced4K
  StageP2PureCalleesPlaced4KOfEnv StageP2PureCalleesPlacedOfEnv
)
open LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP2BlocksA3PlacedBudget (
  p2_seg4a_ext_placed_wp
  p2_seg4b_ext_placed_wp
  p2_seg4c_gen_placed_wp
)
open LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP2Sub1PlacedBudget (
  boxAllocEvents boxAllocEnv_iff_eq
  p2_bind_sepWP_qp_frame_state_placed
  p2_call_rocl_nopanic_steps_frame_placed
)
open LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP2Sub4AuxPlacedBudget (
  p2OpkRecFreeEvents p2OpkRecFreeEvents_freeOnly
  p2Sub4SomeTailEvents
  p2_pkGetShim_pre_intro_placed
  p2_pkGetPoll_pre_intro_placed
  stageP2_sub4_some_tail_kits_ext_placed
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

private theorem p2_vecU8Buf_keep_le (A : RustAlloc) (cap ptr : BitVec 64) (bs : List (BitVec 8)) :
    vecU8Buf A cap ptr bs ⊢ ⌜bs.length ≤ cap.toNat⌝ ∗ vecU8Buf A cap ptr bs := by
  unfold vecU8Buf
  exact Entails.pure_left fun h => Entails.pure_right h.1 (Entails.pure_right h (Entails.refl _))

/-! ## 1. Substage P2.4-Some Event Lists and Fixed-Poll Envelope -/

/-- Allocator event list of Substage P2.4-Some up to the `get_pre_key` poll return at `+0x09c4`:
`pkKit.getShim` (`boxAllocEvents opkBoxSize`) followed by `evs_poll` from `pkKit.getPoll`. -/
def p2Sub4SomePollEvents (opkBoxSize : Nat) (evs_poll : List AllocEvent) : List AllocEvent :=
  boxAllocEvents opkBoxSize ++ evs_poll

/-- Allocator event list of Substage P2.4-Some along the `.ok r` branch (`+0x0d5c -> +0x36ac`):
`pkKit.getShim` (`boxAllocEvents opkBoxSize`), `evs_poll` from `pkKit.getPoll`, and
`p2Sub4SomeTailEvents` (`p2OpkRecFreeEvents` + `skit.kpShim`). -/
def p2Sub4SomeOkEvents (opkBoxSize : Nat) (evs_poll : List AllocEvent)
    (pubCap privCap kpBoxSize : Nat) : List AllocEvent :=
  boxAllocEvents opkBoxSize ++ evs_poll ++
    p2Sub4SomeTailEvents opkBoxSize pubCap privCap kpBoxSize

/-- Deterministic fixed-poll allocator event envelope for Substage P2.4-Some `.ok r`
(`+0x0d5c -> +0x36ac`). -/
def P2Sub4SomeFixedPollEnv (opkBoxSize : Nat) (evs_poll : List AllocEvent)
    (pubCap privCap kpBoxSize : Nat) (evs : List AllocEvent) : Prop :=
  evs = p2Sub4SomeOkEvents opkBoxSize evs_poll pubCap privCap kpBoxSize

theorem fitsEnv_p2Sub4SomeFixedPollEnv_iff {M : AllocCostModel} {lim : BudgetLimits} {st : M.σ}
    (opkBoxSize : Nat) (evs_poll : List AllocEvent) (pubCap privCap kpBoxSize : Nat) :
    FitsEnv M lim st (P2Sub4SomeFixedPollEnv opkBoxSize evs_poll pubCap privCap kpBoxSize) ↔
      FitsEvents M lim st (p2Sub4SomeOkEvents opkBoxSize evs_poll pubCap privCap kpBoxSize) :=
  FitsEnv.eq_iff

-- Concrete `FitsEnv` non-vacuity witness for `P2Sub4SomeFixedPollEnv` under `coarseCostModel`.
example :
    FitsEnv coarseCostModel
      { staticCount := 64, staticBytes := 67108864, physCap := 536870912, enforced := true }
      coarseCostModel.init
      (P2Sub4SomeFixedPollEnv 64 [.alloc 33, .alloc 32] 33 32 64) := by
  rw [fitsEnv_p2Sub4SomeFixedPollEnv_iff]
  have hevs : p2Sub4SomeOkEvents 64 [.alloc 33, .alloc 32] 33 32 64 =
      [.alloc 64, .alloc 33, .alloc 32, .free 8 64, .free 1 33, .free 1 32, .alloc 64] := by
    decide
  rw [hevs]
  dsimp only [FitsEvents, FitsEvent, AllocEvent.withinMaxAlloc, FitsStep,
    AllocCostModel.step, coarseCostModel, coarseStep, coarseStepReserve]
  decide

/-! ## 2. Factored Substage P2.4-Some CPS Statement & Proof (`+0x0d5c -> +0x36ac` or `+0x09c4`) -/

/-- Residual CPS statement of `stageP2_sub4_some_kits_ext_placed` (`+0x0d5c -> +0x36ac` on `.ok r`,
or `+0x09c4` Arm 3 on `.error e`), factored so `4K`, non-`4K`, and `SeqEnv` entry points share one
definition. -/
abbrev stageP2Sub4SomeKitsPlacedProp [LibsignalPlacement]
    {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (ext : String → Option (State → State))
    (pkKit : PreKeyStoreSpec A.repAlloc 0#64)
    (pkEnv : PreKeyStoreBudgetEnv pkKit)
    (ikit : IdentityStoreSpec A.repAlloc 0#64)
    (skit : IdentitySelfStoreSpec ikit)
    (stk : Nat) (ret : BitVec 64) (st : M.σ) (s0 s : State) (Frame : SepProp)
    (Q : State → SepProp → Prop) (Qp : State → SepProp → Prop)
    (coroPtr msgPtr ctxPtr preKeyStorePtr idStorePtr ctSlicePtr
     v_98 v_a0 v_b0 u_a8 u_b8 u_d0 u_488 u_4f8 u_500 : BitVec 64)
    (opkId : BitVec 32) (stPk : pkKit.PkState)
    (b_4b0 s0_b s1_b s2_b s3_b s4_b s5_b s6_b
     c0_init c1_init c2_init c3_init c4_init c5_init c6_init c63_init : BitVec 8)
    (cw0_init cw1_init cw2_init cw3_init cw4_init cw5_init cw6_init : BitVec 64) : Prop :=
  StoreKit.LibsignalCodeRoLoaded lsmpl s.mem →
  (∀ s3 : State, Steps (stageP1ProgPlaced ext) s s3 →
    s3.trace = s.trace → pkKit.envOk s3.fs.files) →
  pkKit.getIdOk opkId →
  (∀ r : PreKeyRecord, pkKit.getRel stPk opkId (.ok r) → pkKit.RecOk r →
    ∃ opkPubBytes opkPrivBytes : List (BitVec 8),
      opkPubBytes.length = 32 ∧ opkPrivBytes.length = 32 ∧
      r.preKey.publicKey = 5#8 :: opkPubBytes ∧ r.preKey.privateKey = opkPrivBytes) →
  s.pc = stageP1EntryPlaced + 0xd5c#64 →
  s.status = .Running → (s.sp &&& 15#64 == 0#64) = true →
  calleeSavedVRegs s = calleeSavedVRegs s0 →
  s.readReg64 .x19 = coroPtr → s.readReg64 .x21 = ctSlicePtr →
  s.readReg64 .x23 = v_a0 → s.readReg64 .x26 = v_98 →
  s.readReg64 .x28 = s.sp + 0xa90#64 →
  (∀ (opkFutPtr : BitVec 64) (e : pkKit.GetErr) (evs_poll : List AllocEvent) (s4 : State),
    Steps (stageP1ProgPlaced ext) s s4 →
    pkKit.getRel stPk opkId (.error e) →
    pkEnv.getPollEnv stPk opkId evs_poll →
    s4.pc = stageP1EntryPlaced + 0x9c4#64 →
    s4.status = .Running → s4.sp = s.sp →
    s4.trace = s.trace ++ pkKit.getEvs opkId (.error e) →
    s4.readReg64 .x19 = coroPtr → s4.readReg64 .x21 = v_b0 →
    s4.readReg64 .x23 = v_a0 → s4.readReg64 .x25 = s.readReg64 .x25 →
    s4.readReg64 .x26 = v_98 → s4.readReg64 .x27 = ctxPtr →
    s4.readReg64 .x28 = s.sp + 0xa90#64 → s4.readReg64 .x29 = s.readReg64 .x29 →
    calleeSavedVRegs s4 = calleeSavedVRegs s0 →
    StoreKit.LibsignalCodeRoLoaded lsmpl s4.mem →
    SepWPp (stageP1ProgPlaced ext) ret s4
      (preKeyGetPollOutAt pkKit (s.sp + 0xa90#64) (.error e) ∗
       memRegion (s.sp + 0xac8#64) 8 ∗ memRegion (s.sp + 0xad0#64) 1 ∗
       pkKit.getBoxAt opkFutPtr preKeyStorePtr opkId 1#8 ∗
       pkKit.storeAt preKeyStorePtr (pkKit.getUpdate stPk opkId (.error e)) ∗
       A.live opkFutPtr pkKit.getBoxSize 8 ∗
       ((s.sp + 0x98#64) ↦₆₄ v_98) ∗ ((s.sp + 0xa0#64) ↦₆₄ v_a0) ∗
       ((s.sp + 0xa8#64) ↦₆₄ u_a8) ∗ ((s.sp + 0xb0#64) ↦₆₄ v_b0) ∗
       ((s.sp + 0xb8#64) ↦₆₄ u_b8) ∗ ((s.sp + 0xc0#64) ↦₆₄ ctxPtr) ∗
       ((s.sp + 0xd0#64) ↦₆₄ u_d0) ∗ memRegion (s.sp + 0x270#64) 9 ∗
       bytes7At (s.sp + 0x3b0#64) s0_b s1_b s2_b s3_b s4_b s5_b s6_b ∗
       memRegion (s.sp + 0x3e0#64) 88 ∗ memRegion (s.sp + 0x930#64) 56 ∗
       ((coroPtr + 0x408#64) ↦₆₄ preKeyStorePtr) ∗ ((coroPtr + 0x410#64) ↦₆₄ pkKit.pk_vt) ∗
       ((coroPtr + 0x418#64) ↦₆₄ idStorePtr) ∗ ((coroPtr + 0x420#64) ↦₆₄ ikit.id_vt) ∗
       ((coroPtr + 0x468#64) ↦₆₄ msgPtr) ∗ ((coroPtr + 0x488#64) ↦₆₄ ctSlicePtr) ∗
       ((coroPtr + 0x4b0#64) ↦₈ b_4b0) ∗
       keyPair64UnalignedAt (coroPtr + 0x4b1#64) c0_init c1_init c2_init c3_init
         c4_init c5_init c6_init cw0_init cw1_init cw2_init cw3_init cw4_init cw5_init
         cw6_init c63_init ∗
       ((coroPtr + 0x4f8#64) ↦₆₄ opkFutPtr) ∗
       ((coroPtr + 0x500#64) ↦₆₄ (0#64 + pkKit.getFutVtOff)) ∗
       ((msgPtr + 0x78#64) ↦₃₂ 1#32) ∗ ((msgPtr + 0x7c#64) ↦₃₂ opkId) ∗
       (lsLogFilterAddr ↦₆₄ 0#64) ∗
       ((pkKit.pk_vt + 0x18#64) ↦₆₄ᵣ (0#64 + pkKit.getShimOff)) ∗
       ((0#64 + pkKit.getFutVtOff) ↦₆₄ᵣ (0#64 + pkKit.getFutDropOff)) ∗
       ((0#64 + pkKit.getFutVtOff + 8#64) ↦₆₄ᵣ BitVec.ofNat 64 pkKit.getBoxSize) ∗
       ((0#64 + pkKit.getFutVtOff + 0x10#64) ↦₆₄ᵣ 8#64) ∗
       ((0#64 + pkKit.getFutVtOff + 0x18#64) ↦₆₄ᵣ (0#64 + pkKit.getPollOff)) ∗
       A.pool lim (M.stepEvents (p2Sub4SomePollEvents pkKit.getBoxSize evs_poll) st) s4 ∗
       stackAt s.sp stk ∗ Frame)
      Q Qp) →
  (∀ (r : PreKeyRecord) (opkPubBytes opkPrivBytes : List (BitVec 8))
    (evs_poll : List AllocEvent)
    (opkFutPtr idKpFutPtr pubCap privCap privPtr : BitVec 64)
    (b0 b1 b2 b3 b4 b5 b6 b63 c0 c1 c2 c3 c4 c5 c6 : BitVec 8)
    (w0 w1 w2 w3 w4 w5 w6 u0_kp u1_kp u2_kp u3_kp u4_kp u5_kp u6_kp u7_kp : BitVec 64)
    (sf : State),
    Steps (stageP1ProgPlaced ext) s sf →
    pkKit.getRel stPk opkId (.ok r) → pkKit.RecOk r →
    pkEnv.getPollEnv stPk opkId evs_poll →
    33 ≤ pubCap.toNat → 32 ≤ privCap.toNat →
    opkPubBytes.length = 32 → opkPrivBytes.length = 32 →
    r.preKey.publicKey = 5#8 :: opkPubBytes → r.preKey.privateKey = opkPrivBytes →
    (∀ a : BitVec 64, (a ↦ₛ opkPubBytes) =
      (a ↦₆₄ u0_kp) ∗ ((a + 8#64) ↦₆₄ u1_kp) ∗ ((a + 16#64) ↦₆₄ u2_kp) ∗
        ((a + 24#64) ↦₆₄ u3_kp)) →
    (∀ a : BitVec 64, (a ↦ₛ clampBv8List opkPrivBytes) =
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
    sf.pc = stageP1EntryPlaced + 0x36ac#64 →
    sf.status = .Running → sf.sp = s.sp →
    sf.trace = s.trace ++ pkKit.getEvs opkId (.ok r) →
    sf.readReg64 .x0 = idKpFutPtr → sf.readReg64 .x1 = 0#64 + skit.kpFutVtOff →
    idKpFutPtr ≠ 0#64 → idKpFutPtr.toNat % 8 = 0 →
    sf.readReg64 .x19 = coroPtr → sf.readReg64 .x21 = v_b0 →
    sf.readReg64 .x23 = v_a0 → sf.readReg64 .x24 = s.sp + 0x370#64 →
    sf.readReg64 .x25 = s.readReg64 .x25 → sf.readReg64 .x26 = v_98 →
    sf.readReg64 .x27 = ctxPtr → sf.readReg64 .x28 = s.sp + 0xa90#64 →
    sf.readReg64 .x29 = s.readReg64 .x29 →
    calleeSavedVRegs sf = calleeSavedVRegs s0 →
    StoreKit.LibsignalCodeRoLoaded lsmpl sf.mem →
    SepWPp (stageP1ProgPlaced ext) ret sf
      (pkKit.storeAt preKeyStorePtr (pkKit.getUpdate stPk opkId (.ok r)) ∗
       A.live idKpFutPtr skit.kpBoxSize 8 ∗
       skit.kpBoxAt idKpFutPtr idStorePtr 0#8 ∗
       ((s.sp + 0x98#64) ↦₆₄ v_98) ∗ ((s.sp + 0xa0#64) ↦₆₄ v_a0) ∗
       ((s.sp + 0xa8#64) ↦₆₄ 32#64) ∗ ((s.sp + 0xb0#64) ↦₆₄ v_b0) ∗
       ((s.sp + 0xb8#64) ↦₆₄ privCap) ∗ ((s.sp + 0xc0#64) ↦₆₄ ctxPtr) ∗
       ((s.sp + 0xd0#64) ↦₆₄ privPtr) ∗ memRegion (s.sp + 0x270#64) 9 ∗
       bytes7At (s.sp + 0x3b0#64) b0 b1 b2 b3 b4 b5 b6 ∗
       memRegion (s.sp + 0x3e0#64) 88 ∗ memRegion (s.sp + 0x930#64) 56 ∗
       memRegion (s.sp + 0xa90#64) 65 ∗
       ((coroPtr + 0x408#64) ↦₆₄ preKeyStorePtr) ∗ ((coroPtr + 0x410#64) ↦₆₄ pkKit.pk_vt) ∗
       ((coroPtr + 0x418#64) ↦₆₄ idStorePtr) ∗ ((coroPtr + 0x420#64) ↦₆₄ ikit.id_vt) ∗
       ((coroPtr + 0x468#64) ↦₆₄ msgPtr) ∗ ((coroPtr + 0x488#64) ↦₆₄ ctSlicePtr) ∗
       ((coroPtr + 0x4b0#64) ↦₈ 1#8) ∗
       keyPair64UnalignedAt (coroPtr + 0x4b1#64) b0 b1 b2 b3 b4 b5 b6 w0 w1 w2 w3 w4 w5 w6 b63 ∗
       ((coroPtr + 0x4f8#64) ↦₆₄ opkFutPtr) ∗
       ((coroPtr + 0x500#64) ↦₆₄ (0#64 + pkKit.getFutVtOff)) ∗
       ((msgPtr + 0x78#64) ↦₃₂ 1#32) ∗ ((msgPtr + 0x7c#64) ↦₃₂ opkId) ∗
       (lsLogFilterAddr ↦₆₄ 0#64) ∗
       ((pkKit.pk_vt + 0x18#64) ↦₆₄ᵣ (0#64 + pkKit.getShimOff)) ∗
       ((0#64 + pkKit.getFutVtOff) ↦₆₄ᵣ (0#64 + pkKit.getFutDropOff)) ∗
       ((0#64 + pkKit.getFutVtOff + 8#64) ↦₆₄ᵣ BitVec.ofNat 64 pkKit.getBoxSize) ∗
       ((0#64 + pkKit.getFutVtOff + 0x10#64) ↦₆₄ᵣ 8#64) ∗
       ((0#64 + pkKit.getFutVtOff + 0x18#64) ↦₆₄ᵣ (0#64 + pkKit.getPollOff)) ∗
       A.pool lim
         (M.stepEvents
           (p2Sub4SomeOkEvents pkKit.getBoxSize evs_poll
             pubCap.toNat privCap.toNat skit.kpBoxSize) st) sf ∗
       stackAt s.sp stk ∗ Frame)
      Q Qp) →
  SepWPp (stageP1ProgPlaced ext) ret s
    (((s.sp + 0x98#64) ↦₆₄ v_98) ∗ ((s.sp + 0xa0#64) ↦₆₄ v_a0) ∗
     ((s.sp + 0xa8#64) ↦₆₄ u_a8) ∗ ((s.sp + 0xb0#64) ↦₆₄ v_b0) ∗
     ((s.sp + 0xb8#64) ↦₆₄ u_b8) ∗ ((s.sp + 0xc0#64) ↦₆₄ ctxPtr) ∗
     ((s.sp + 0xd0#64) ↦₆₄ u_d0) ∗ memRegion (s.sp + 0x270#64) 9 ∗
     bytes7At (s.sp + 0x3b0#64) s0_b s1_b s2_b s3_b s4_b s5_b s6_b ∗
     memRegion (s.sp + 0x3e0#64) 88 ∗ memRegion (s.sp + 0x930#64) 56 ∗
     memRegion (s.sp + 0xa90#64) 65 ∗
     ((coroPtr + 0x408#64) ↦₆₄ preKeyStorePtr) ∗ ((coroPtr + 0x410#64) ↦₆₄ pkKit.pk_vt) ∗
     ((coroPtr + 0x418#64) ↦₆₄ idStorePtr) ∗ ((coroPtr + 0x420#64) ↦₆₄ ikit.id_vt) ∗
     ((coroPtr + 0x468#64) ↦₆₄ msgPtr) ∗ ((coroPtr + 0x488#64) ↦₆₄ u_488) ∗
     ((coroPtr + 0x4b0#64) ↦₈ b_4b0) ∗
     keyPair64UnalignedAt (coroPtr + 0x4b1#64) c0_init c1_init c2_init c3_init
       c4_init c5_init c6_init cw0_init cw1_init cw2_init cw3_init cw4_init cw5_init
       cw6_init c63_init ∗
     ((coroPtr + 0x4f8#64) ↦₆₄ u_4f8) ∗ ((coroPtr + 0x500#64) ↦₆₄ u_500) ∗
     ((msgPtr + 0x78#64) ↦₃₂ 1#32) ∗ ((msgPtr + 0x7c#64) ↦₃₂ opkId) ∗
     (lsLogFilterAddr ↦₆₄ 0#64) ∗
     ((pkKit.pk_vt + 0x18#64) ↦₆₄ᵣ (0#64 + pkKit.getShimOff)) ∗
     ((0#64 + pkKit.getFutVtOff) ↦₆₄ᵣ (0#64 + pkKit.getFutDropOff)) ∗
     ((0#64 + pkKit.getFutVtOff + 8#64) ↦₆₄ᵣ BitVec.ofNat 64 pkKit.getBoxSize) ∗
     ((0#64 + pkKit.getFutVtOff + 0x10#64) ↦₆₄ᵣ 8#64) ∗
     ((0#64 + pkKit.getFutVtOff + 0x18#64) ↦₆₄ᵣ (0#64 + pkKit.getPollOff)) ∗
     pkKit.storeAt preKeyStorePtr stPk ∗ A.pool lim st s ∗ stackAt s.sp stk ∗ Frame)
    Q Qp

set_option maxHeartbeats 1400000 in
/-- Budget-Threaded Placed Kit-Generic Substage P2.4-Some (`+0x0d5c -> +0x36ac` or `+0x09c4` Arm 3)
in CPS form on `stageP1ProgPlaced ext`:
invokes `pkKit.getShim`, polls `pkKit.getPoll` (delegating `.error e` at `+0x09c4` to `hErr` with
`A.pool lim (M.stepEvents (p2Sub4SomePollEvents pkKit.getBoxSize evs_poll) st) s4`), and on `.ok r`
drops the OPK future and delegates `+0x0e40 -> +0x36ac` to `stageP2_sub4_some_tail_kits_ext_placed`
reaching `+0x36ac` (`hOk`) with `A.pool lim (M.stepEvents (p2Sub4SomeOkEvents ...) st) sf`. -/
theorem stageP2_sub4_some_kits_ext_placed [LibsignalPlacement]
    {M : AllocCostModel} {P : Primitives} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {F : ShaCompress} {BobV1Env : AcceptKeysInput → DRKey → List AllocEvent → Prop}
    {AcceptErrEnv : AcceptKeysInput → List AllocEvent → Prop}
    (ext : String → Option (State → State))
    (hH : StageP2ClosureHooksPlaced A lim ext)
    (hPure : StageP2PureCalleesPlaced4KOfEnv P A lim F BobV1Env AcceptErrEnv ext)
    (pkKit : PreKeyStoreSpec A.repAlloc 0#64)
    (pkEnv : PreKeyStoreBudgetEnv pkKit)
    (hpkOk : PreKeyStoreKitPlacedOk A lim pkKit pkEnv ext)
    (ikit : IdentityStoreSpec A.repAlloc 0#64)
    (skit : IdentitySelfStoreSpec ikit)
    (senv : IdentitySelfStoreBudgetEnv skit)
    (hskitVt : IdentitySelfVtablesPlacedOk ikit skit)
    (hskitOk : IdentitySelfStoreKitPlacedOkI A lim ikit skit senv ext)
    (stk : Nat) (hstk_pure : stageP2PureAndErrStack ≤ stk)
    (hstk_pk_shim : pkKit.getShimStack ≤ stk) (hstk_pk_poll : pkKit.getPollStack ≤ stk)
    (hstk_kp_shim : skit.kpShimStack ≤ stk) (hstk_lt : stk ≤ 2 ^ 64)
    (ret : BitVec 64) (st : M.σ) (s0 s : State) (Frame : SepProp)
    (Q : State → SepProp → Prop) {Qp : State → SepProp → Prop}
    (coroPtr msgPtr ctxPtr preKeyStorePtr idStorePtr ctSlicePtr
     v_98 v_a0 v_b0 u_a8 u_b8 u_d0 u_488 u_4f8 u_500 : BitVec 64)
    (opkId : BitVec 32) (stPk : pkKit.PkState)
    (b_4b0 s0_b s1_b s2_b s3_b s4_b s5_b s6_b
     c0_init c1_init c2_init c3_init c4_init c5_init c6_init c63_init : BitVec 8)
    (cw0_init cw1_init cw2_init cw3_init cw4_init cw5_init cw6_init : BitVec 64)
    (hfits_shim : FitsEnv M lim st (BoxAllocEnv pkKit.getBoxSize))
    (hfits_poll : FitsEnv M lim (M.stepEvents (boxAllocEvents pkKit.getBoxSize) st)
      (pkEnv.getPollEnv stPk opkId))
    (hfits_kp : ∀ (r : PreKeyRecord) (evs_poll : List AllocEvent) (pubCap privCap : Nat),
      pkKit.getRel stPk opkId (.ok r) → pkKit.RecOk r →
      pkEnv.getPollEnv stPk opkId evs_poll →
      33 ≤ pubCap → 32 ≤ privCap →
      FitsEnv M lim
        (M.stepEvents
          (boxAllocEvents pkKit.getBoxSize ++ evs_poll ++
            p2OpkRecFreeEvents pkKit.getBoxSize pubCap privCap) st)
        (BoxAllocEnv skit.kpBoxSize)) :
    stageP2Sub4SomeKitsPlacedProp A lim ext pkKit pkEnv ikit skit
      stk ret st s0 s Frame Q Qp
      coroPtr msgPtr ctxPtr preKeyStorePtr idStorePtr ctSlicePtr
      v_98 v_a0 v_b0 u_a8 u_b8 u_d0 u_488 u_4f8 u_500 opkId stPk
      b_4b0 s0_b s1_b s2_b s3_b s4_b s5_b s6_b
      c0_init c1_init c2_init c3_init c4_init c5_init c6_init c63_init
      cw0_init cw1_init cw2_init cw3_init cw4_init cw5_init cw6_init := by
  intro hCode henv hid_pk hrec_wf hpc hrun hsp_align hvregs hx19 hx21 hx23 hx26 hx28 hErr hOk
  have hstep1 := p2_seg4a_ext_placed_wp (A := A) (lim := lim) ext st s coroPtr msgPtr ctxPtr
    preKeyStorePtr pkKit.pk_vt (0#64 + pkKit.getShimOff) ctSlicePtr u_488 opkId
    hpc hrun hsp_align hx19 hx21
  refine p2_bind_sepWP_qp_frame_state_placed hCode hstep1 (by sep_focus)
    fun s1 hst01 hpc1 hrun1 hCode1 hregs1 => ?_
  rcases hregs1 with ⟨hsp1, htr1, hx0_1, hx1_1, hx19_1, _, hx23_1, hx25_1, hx26_1, hx27_1,
    hx28_1, hx29_1, hx30_1, hvregs1⟩
  have hsp1_al : s1.spAligned = true := by simpa only [State.spAligned, hsp1] using hsp_align
  have hx1_1_32 : s1.readReg32 .x1 = opkId := by
    change (s1.readReg64 .x1).setWidth 32 = opkId
    rw [hx1_1, p2_zext64_trunc32_id]
  have hstk_shim := p2_stackAt_split_of_le s.sp stk pkKit.getShimStack hstk_pk_shim hstk_lt
  refine SepWPp.weaken_frame (Entails.of_eq hstk_shim) (by sep_focus) ?_
  sep_norm
  refine p2_call_rocl_nopanic_steps_frame_placed
    (x := (({ self := preKeyStorePtr, id := opkId } : PreKeyShimCall), st))
    hCode1 (hpkOk.getShim (by decide)) hpc1 hrun1 hsp1_al hx30_1
    (hsp1 ▸ p2_pkGetShim_pre_intro_placed hx0_1 hx1_1_32 hfits_shim)
    (by sep_focus)
    (hnext := fun s2 hst12 hpc2 hrun2 hsp2_1 _ hcs2 hCode2 => ?_)
  dsimp only [kitPreKeyGetShimSpec]
  rcases hcs2 with ⟨hcs2_19, _, _, _, hcs2_23, _, hcs2_25, hcs2_26, hcs2_27, hcs2_28,
    hcs2_29, hvregs2_1⟩
  have hsp2 : s2.sp = s.sp := hsp2_1.trans hsp1
  have hsp2_align : (s2.sp &&& 15#64 == 0#64) = true := by rw [hsp2]; exact hsp_align
  rw [hsp1]
  sep_norm
  refine SepWPp.exists_elim fun evs_shim =>
    SepWPp.pure_elim fun ⟨hx1_2, _, _, htr2_1, hevs_shim⟩ => ?_
  have hevs_shim_eq : evs_shim = boxAllocEvents pkKit.getBoxSize :=
    (boxAllocEnv_iff_eq pkKit.getBoxSize evs_shim).mp hevs_shim
  rw [hevs_shim_eq]
  refine SepWPp.weaken_frame (Entails.of_eq hstk_shim.symm) (by sep_focus) ?_
  let opkFutPtr := s2.readReg64 .x0
  let st_shim := M.stepEvents (boxAllocEvents pkKit.getBoxSize) st
  have hstep3 := p2_seg4b_ext_placed_wp (A := A) (lim := lim) ext st_shim s2 coroPtr ctxPtr
    opkFutPtr (0#64 + pkKit.getFutVtOff) (0#64 + pkKit.getPollOff) v_b0 u_4f8 u_500
    hpc2 hrun2 hsp2_align rfl hx1_2 (hcs2_19.trans hx19_1) (hcs2_27.trans hx27_1)
  rw [hsp2] at hstep3
  refine p2_bind_sepWP_qp_frame_state_placed hCode2 hstep3 (by sep_focus)
    fun s3 hst23 hpc3 hrun3 hCode3 hregs3 => ?_
  rcases hregs3 with ⟨hsp3_2, htr3_2, hx0_3, _, hx8_3, hx19_3, hx21_3, hx23_3, hx25_3, hx26_3,
    hx27_3, hx28_3, hx29_3, hx30_3, hvregs3_2⟩
  have hsp3 : s3.sp = s.sp := hsp3_2
  have hsp3_al : s3.spAligned = true := by simpa only [State.spAligned, hsp3] using hsp_align
  have htr3_s : s3.trace = s.trace := by rw [htr3_2, htr2_1, htr1]
  have hstk_poll := p2_stackAt_split_of_le s.sp stk pkKit.getPollStack hstk_pk_poll hstk_lt
  refine SepWPp.weaken_frame (Entails.of_eq hstk_poll) (by sep_focus) ?_
  refine SepWPp.weaken_frame (Entails.of_eq (p2_memRegion_65_pkPoll_split_eq (s.sp + 0xa90#64)))
    (by sep_focus) ?_
  rw [show (s.sp + 0xa90#64) + 0x38#64 = s.sp + 0xac8#64 by bv_omega,
      show (s.sp + 0xa90#64) + 0x40#64 = s.sp + 0xad0#64 by bv_omega]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  refine SepWPp.exists_elim fun u_ac8 => ?_
  sep_norm
  refine p2_call_rocl_nopanic_steps_frame_placed
    (x := (({ fut := opkFutPtr, self := preKeyStorePtr, out := s.sp + 0xa90#64,
              id := opkId } : PreKeyPollCall), stPk, st_shim))
    hCode3 (hpkOk.getPoll (by decide)) hpc3 hrun3 hsp3_al hx30_3
    (hsp3 ▸ p2_pkGetPoll_pre_intro_placed
      (henv s3 (hst01.trans (hst12.trans hst23)) htr3_s) hx0_3 hx8_3 hid_pk hfits_poll)
    (by sep_focus)
    (hnext := fun s4 hst34 hpc4 hrun4 hsp4_3 _ hcs4 hCode4 => ?_)
  dsimp only [kitPreKeyGetPollSpecE, withEnvPre, kitPreKeyGetPollSpec]
  rcases hcs4 with ⟨hcs4_19, _, hcs4_21, _, hcs4_23, _, hcs4_25, hcs4_26, hcs4_27, hcs4_28,
    hcs4_29, hvregs4_3⟩
  have hsp4 : s4.sp = s.sp := hsp4_3.trans hsp3
  have hsp4_align : (s4.sp &&& 15#64 == 0#64) = true := by rw [hsp4]; exact hsp_align
  rw [hsp3]
  sep_norm
  refine SepWPp.exists_elim fun ans => SepWPp.exists_elim fun evs_poll =>
    SepWPp.pure_elim fun ⟨hrel, htr4_3, hevs_poll⟩ => ?_
  refine SepWPp.weaken_frame (Entails.of_eq hstk_poll.symm) (by sep_focus) ?_
  have htr4 : s4.trace = s.trace ++ pkKit.getEvs opkId ans := by rw [htr4_3, htr3_s]
  have hst04 := hst01.trans (hst12.trans (hst23.trans hst34))
  let st_poll := M.stepEvents (p2Sub4SomePollEvents pkKit.getBoxSize evs_poll) st
  have hst_poll_eq : M.stepEvents evs_poll st_shim = st_poll := by
    dsimp only [st_shim, st_poll, p2Sub4SomePollEvents]
    simp only [M.stepEvents_append, List.append_assoc]
  rw [hst_poll_eq]
  cases ans with
  | error e =>
    refine SepWPp.weaken_frame (pointsTo64_entails_memRegion (s.sp + 0xac8#64) u_ac8)
      (by sep_focus) ?_
    have herr := hErr opkFutPtr e evs_poll s4 hst04 hrel hevs_poll hpc4 hrun4 hsp4 htr4
      (hcs4_19.trans hx19_3) (hcs4_21.trans hx21_3)
      (by rw [hcs4_23, hx23_3, hcs2_23, hx23_1, hx23])
      (by rw [hcs4_25, hx25_3, hcs2_25, hx25_1])
      (by rw [hcs4_26, hx26_3, hcs2_26, hx26_1, hx26])
      (hcs4_27.trans hx27_3)
      (by rw [hcs4_28, hx28_3, hcs2_28, hx28_1, hx28])
      (by rw [hcs4_29, hx29_3, hcs2_29, hx29_1])
      (by rw [hvregs4_3, hvregs3_2, hvregs2_1, hvregs1, hvregs]) hCode4
    exact p2_sepWPp_weaken_eq herr (by sep_focus)
  | ok r =>
    dsimp only [preKeyGetPollOutAt]
    simp only [sepConj_assoc]
    refine p2_sepWPp_pure_elim_frame (pkKit.RecOk r) (by sep_focus) fun hrec_ok => ?_
    obtain ⟨opkPubBytes, opkPrivBytes, hpub_len, hpriv_len, hpub_eq, hpriv_eq⟩ :=
      hrec_wf r hrel hrec_ok
    rw [show s.sp + 0xac8#64 = (s.sp + 0xa90#64) + 0x38#64 by bv_omega]
    refine SepWPp.weaken_frame (p2_preKeyRecordAt_unpack A.repAlloc (s.sp + 0xa90#64) u_ac8 r)
      (by sep_focus) ?_
    simp only [sepExists_sepConj_left, sepConj_assoc]
    refine SepWPp.exists_elim fun pubCap => SepWPp.exists_elim fun pubPtr =>
      SepWPp.exists_elim fun privCap => SepWPp.exists_elim fun privPtr =>
      SepWPp.exists_elim fun pad32 => ?_
    have hpub_bv : BitVec.ofNat 64 r.preKey.publicKey.length = 33#64 := by
      rw [hpub_eq]; simp [hpub_len]
    have hpriv_bv : BitVec.ofNat 64 r.preKey.privateKey.length = 32#64 := by
      rw [hpriv_eq, hpriv_len]
    rw [hpub_bv, hpriv_bv, hpub_eq, hpriv_eq]
    refine SepWPp.weaken_frame (p2_vecU8Buf_keep_le A.repAlloc privCap privPtr opkPrivBytes)
      (by sep_focus) ?_
    sep_norm
    refine SepWPp.pure_elim fun hpriv_le => ?_
    refine SepWPp.weaken_frame
      (p2_vecU8Buf_nonempty A.repAlloc pubCap pubPtr (5#8 :: opkPubBytes) (by simp))
      (by sep_focus) ?_
    sep_norm
    refine SepWPp.pure_elim fun ⟨hpub_le, hpub_lt, hpub_nz, hpub_ne2, hpub_ne1⟩ => ?_
    have hpub_cap : 33 ≤ pubCap.toNat := by simpa [hpub_len] using hpub_le
    have hpriv_cap : 32 ≤ privCap.toNat := by simpa [hpriv_len] using hpriv_le
    have hpub_ne3 : pubCap ≠ 0xfffffffffffffffd#64 := p2_cap_ne_neg3_of_lt hpub_lt
    have hstep5 := p2_seg4c_gen_placed_wp (A := A) (lim := lim) ext st_poll s4 coroPtr ctxPtr
      opkFutPtr (0#64 + pkKit.getFutVtOff) (0#64 + pkKit.getFutDropOff)
      pubCap pubPtr privCap privPtr (pad32 ++ r.preKey.id) u_ac8
      v_98 v_a0 v_b0 v_98 v_a0 u_a8 v_b0 u_b8 ctxPtr u_d0
      hpub_ne2 hpub_ne3 (pkKit.getFutDrop_ne_zero rfl) hpc4 hrun4 hsp4_align
      (hcs4_19.trans hx19_3) (hcs4_21.trans hx21_3)
      (by rw [hcs4_23, hx23_3, hcs2_23, hx23_1, hx23])
      (by rw [hcs4_26, hx26_3, hcs2_26, hx26_1, hx26])
      (hcs4_27.trans hx27_3)
    have hvt0 : (0#64 + pkKit.getFutVtOff) + 0x0#64 = 0#64 + pkKit.getFutVtOff :=
      BitVec.add_zero _
    rw [hsp4, hvt0] at hstep5
    refine p2_bind_sepWP_qp_frame_state_placed hCode4 hstep5 (by sep_focus)
      fun s5 hst45 hpc5 hrun5 hCode5 hregs5 => ?_
    rcases hregs5 with ⟨hsp5, htr5_4, _, hx19_5, hx21_5, hx22_5, hx23_5, hx24_5, hx25_5, hx26_5,
      hx27_5, hx28_5, hx29_5, hx30_5, hvregs5_4⟩
    have hsp5_al : s5.spAligned = true := by simpa only [State.spAligned, hsp5] using hsp_align
    refine p2_call_rocl_nopanic_steps_frame_placed (x := ()) (P_spec := emp)
      hCode5 (hpkOk.getFutDrop (by decide)) hpc5 hrun5 hsp5_al hx30_5
      (Entails.refl emp) (emp_sepConj _).symm
      (hnext := fun s6 hst56 hpc6 hrun6 hsp6_5 _ hcs6 hCode6 => ?_)
    dsimp only [futDropBudgetSpec]
    refine SepWPp.pure_elim fun ⟨htr6_5, hvm56⟩ => ?_
    refine SepWPp.transport_budgetPool hvm56 (by sep_focus) ?_
    rcases hcs6 with ⟨hcs6_19, _, hcs6_21, hcs6_22, hcs6_23, hcs6_24, hcs6_25, hcs6_26, hcs6_27,
      hcs6_28, hcs6_29, hvregs6_5⟩
    have hsp6 : s6.sp = s.sp := hsp6_5.trans hsp5
    have htr6 : s6.trace = s.trace ++ pkKit.getEvs opkId (.ok r) := by
      rw [htr6_5, htr5_4, htr4]
    have hvregs6 : calleeSavedVRegs s6 = calleeSavedVRegs s0 := by
      rw [hvregs6_5, hvregs5_4, hvregs4_3, hvregs3_2, hvregs2_1, hvregs1, hvregs]
    have hfits_kp_inst :
        FitsEnv M lim
          (M.stepEvents (p2OpkRecFreeEvents pkKit.getBoxSize pubCap.toNat privCap.toNat) st_poll)
          (BoxAllocEnv skit.kpBoxSize) := by
      have hkp := hfits_kp r evs_poll pubCap.toNat privCap.toNat
        hrel hrec_ok hevs_poll hpub_cap hpriv_cap
      dsimp only [st_poll, p2Sub4SomePollEvents]
      simpa only [M.stepEvents_append, List.append_assoc] using hkp
    let TailFrame : SepProp :=
      pkKit.storeAt preKeyStorePtr (pkKit.getUpdate stPk opkId (.ok r)) ∗
      ((coroPtr + 0x408#64) ↦₆₄ preKeyStorePtr) ∗ ((coroPtr + 0x410#64) ↦₆₄ pkKit.pk_vt) ∗
      ((coroPtr + 0x468#64) ↦₆₄ msgPtr) ∗ ((coroPtr + 0x488#64) ↦₆₄ ctSlicePtr) ∗
      ((coroPtr + 0x4f8#64) ↦₆₄ opkFutPtr) ∗
      ((coroPtr + 0x500#64) ↦₆₄ (0#64 + pkKit.getFutVtOff)) ∗
      ((msgPtr + 0x78#64) ↦₃₂ 1#32) ∗
      (lsLogFilterAddr ↦₆₄ 0#64) ∗
      ((pkKit.pk_vt + 0x18#64) ↦₆₄ᵣ (0#64 + pkKit.getShimOff)) ∗
      ((0#64 + pkKit.getFutVtOff) ↦₆₄ᵣ (0#64 + pkKit.getFutDropOff)) ∗
      ((0#64 + pkKit.getFutVtOff + 0x18#64) ↦₆₄ᵣ (0#64 + pkKit.getPollOff)) ∗
      Frame
    have htail := stageP2_sub4_some_tail_kits_ext_placed ext hH hPure pkKit ikit skit senv
      hskitVt hskitOk stk hstk_pure hstk_kp_shim hstk_lt
      ret st_poll s0 s6 s.sp TailFrame Q (Qp := Qp)
      coroPtr msgPtr ctxPtr preKeyStorePtr idStorePtr opkFutPtr
      pubCap pubPtr privCap privPtr (pad32 ++ r.preKey.id) u_ac8 v_98 v_a0 v_b0
      opkId opkPubBytes opkPrivBytes
      b_4b0 s0_b s1_b s2_b s3_b s4_b s5_b s6_b
      c0_init c1_init c2_init c3_init c4_init c5_init c6_init c63_init
      cw0_init cw1_init cw2_init cw3_init cw4_init cw5_init cw6_init
      hfits_kp_inst hpub_len hpriv_len hpub_le hpub_nz hpub_ne1
      hCode6 hpc6 hrun6 hsp6 hsp_align hvregs6
      (hcs6_19.trans hx19_5) (hcs6_21.trans hx21_5) (hcs6_22.trans hx22_5)
      (hcs6_23.trans hx23_5) (hcs6_24.trans hx24_5) (hcs6_26.trans hx26_5)
      (hcs6_27.trans hx27_5)
      (by rw [hcs6_28, hx28_5, hcs4_28, hx28_3, hcs2_28, hx28_1, hx28])
      (fun idKpFutPtr b0 b1 b2 b3 b4 b5 b6 b63 c0 c1 c2 c3 c4 c5 c6
           w0 w1 w2 w3 w4 w5 w6 u0_kp u1_kp u2_kp u3_kp u4_kp u5_kp u6_kp u7_kp sf
           hst6f hpk_words hsk_words hkp_lo hkp_hi
           hpcf hrunf hspf htrf_6 hx0_f hx1_f hx0_nz hx0_al
           hx19_f hx21_f hx23_f hx24_f hx25_f hx26_f hx27_f hx28_f hx29_f
           hvregsf hCodef => by
        have hpool_ok_eq :
            M.stepEvents
              (p2Sub4SomeTailEvents pkKit.getBoxSize pubCap.toNat privCap.toNat skit.kpBoxSize)
              st_poll =
            M.stepEvents
              (p2Sub4SomeOkEvents pkKit.getBoxSize evs_poll
                pubCap.toNat privCap.toNat skit.kpBoxSize) st := by
          dsimp only [st_poll, p2Sub4SomePollEvents, p2Sub4SomeOkEvents]
          simp only [M.stepEvents_append, List.append_assoc]
        have hok := hOk r opkPubBytes opkPrivBytes evs_poll
          opkFutPtr idKpFutPtr pubCap privCap privPtr
          b0 b1 b2 b3 b4 b5 b6 b63 c0 c1 c2 c3 c4 c5 c6
          w0 w1 w2 w3 w4 w5 w6 u0_kp u1_kp u2_kp u3_kp u4_kp u5_kp u6_kp u7_kp sf
          (hst04.trans (hst45.trans (hst56.trans hst6f))) hrel hrec_ok hevs_poll
          hpub_cap hpriv_cap
          hpub_len hpriv_len hpub_eq hpriv_eq hpk_words hsk_words hkp_lo hkp_hi
          hpcf hrunf hspf (htrf_6.trans htr6) hx0_f hx1_f hx0_nz hx0_al
          hx19_f hx21_f hx23_f hx24_f
          (by rw [hx25_f, hcs6_25, hx25_5, hcs4_25, hx25_3, hcs2_25, hx25_1])
          hx26_f hx27_f hx28_f
          (by rw [hx29_f, hcs6_29, hx29_5, hcs4_29, hx29_3, hcs2_29, hx29_1])
          hvregsf hCodef
        dsimp only [TailFrame]
        rw [hpool_ok_eq]
        exact p2_sepWPp_weaken_eq hok (by sep_focus))
    dsimp only [TailFrame] at htail
    exact p2_sepWPp_weaken_eq htail (by sep_focus)

abbrev stageP2_sub4_some_kits_4k_placed := @stageP2_sub4_some_kits_ext_placed
abbrev stageP2_sub4_some_kits_hooks_placed := @stageP2_sub4_some_kits_ext_placed

theorem stageP2_sub4_some_kits_placed [LibsignalPlacement]
    {M : AllocCostModel} {P : Primitives} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {F : ShaCompress} {BobV1Env : AcceptKeysInput → DRKey → List AllocEvent → Prop}
    {AcceptErrEnv : AcceptKeysInput → List AllocEvent → Prop}
    (ext : String → Option (State → State))
    (hH : StageP2ClosureHooksPlaced A lim ext)
    (hPure : StageP2PureCalleesPlacedOfEnv P A lim F BobV1Env AcceptErrEnv ext)
    (pkKit : PreKeyStoreSpec A.repAlloc 0#64)
    (pkEnv : PreKeyStoreBudgetEnv pkKit)
    (hpkOk : PreKeyStoreKitPlacedOk A lim pkKit pkEnv ext)
    (ikit : IdentityStoreSpec A.repAlloc 0#64)
    (skit : IdentitySelfStoreSpec ikit)
    (senv : IdentitySelfStoreBudgetEnv skit)
    (hskitVt : IdentitySelfVtablesPlacedOk ikit skit)
    (hskitOk : IdentitySelfStoreKitPlacedOkI A lim ikit skit senv ext)
    (stk : Nat) (hstk_pure : stageP2PureAndErrStack ≤ stk)
    (hstk_pk_shim : pkKit.getShimStack ≤ stk) (hstk_pk_poll : pkKit.getPollStack ≤ stk)
    (hstk_kp_shim : skit.kpShimStack ≤ stk) (hstk_lt : stk ≤ 2 ^ 64)
    (ret : BitVec 64) (st : M.σ) (s0 s : State) (Frame : SepProp)
    (Q : State → SepProp → Prop) {Qp : State → SepProp → Prop}
    (coroPtr msgPtr ctxPtr preKeyStorePtr idStorePtr ctSlicePtr
     v_98 v_a0 v_b0 u_a8 u_b8 u_d0 u_488 u_4f8 u_500 : BitVec 64)
    (opkId : BitVec 32) (stPk : pkKit.PkState)
    (b_4b0 s0_b s1_b s2_b s3_b s4_b s5_b s6_b
     c0_init c1_init c2_init c3_init c4_init c5_init c6_init c63_init : BitVec 8)
    (cw0_init cw1_init cw2_init cw3_init cw4_init cw5_init cw6_init : BitVec 64)
    (hfits_shim : FitsEnv M lim st (BoxAllocEnv pkKit.getBoxSize))
    (hfits_poll : FitsEnv M lim (M.stepEvents (boxAllocEvents pkKit.getBoxSize) st)
      (pkEnv.getPollEnv stPk opkId))
    (hfits_kp : ∀ (r : PreKeyRecord) (evs_poll : List AllocEvent) (pubCap privCap : Nat),
      pkKit.getRel stPk opkId (.ok r) → pkKit.RecOk r →
      pkEnv.getPollEnv stPk opkId evs_poll →
      33 ≤ pubCap → 32 ≤ privCap →
      FitsEnv M lim
        (M.stepEvents
          (boxAllocEvents pkKit.getBoxSize ++ evs_poll ++
            p2OpkRecFreeEvents pkKit.getBoxSize pubCap privCap) st)
        (BoxAllocEnv skit.kpBoxSize)) :
    stageP2Sub4SomeKitsPlacedProp A lim ext pkKit pkEnv ikit skit
      stk ret st s0 s Frame Q Qp
      coroPtr msgPtr ctxPtr preKeyStorePtr idStorePtr ctSlicePtr
      v_98 v_a0 v_b0 u_a8 u_b8 u_d0 u_488 u_4f8 u_500 opkId stPk
      b_4b0 s0_b s1_b s2_b s3_b s4_b s5_b s6_b
      c0_init c1_init c2_init c3_init c4_init c5_init c6_init c63_init
      cw0_init cw1_init cw2_init cw3_init cw4_init cw5_init cw6_init :=
  stageP2_sub4_some_kits_ext_placed ext hH hPure.to_4K pkKit pkEnv hpkOk ikit skit senv
    hskitVt hskitOk stk hstk_pure hstk_pk_shim hstk_pk_poll hstk_kp_shim hstk_lt
    ret st s0 s Frame Q (Qp := Qp)
    coroPtr msgPtr ctxPtr preKeyStorePtr idStorePtr ctSlicePtr
    v_98 v_a0 v_b0 u_a8 u_b8 u_d0 u_488 u_4f8 u_500 opkId stPk
    b_4b0 s0_b s1_b s2_b s3_b s4_b s5_b s6_b
    c0_init c1_init c2_init c3_init c4_init c5_init c6_init c63_init
    cw0_init cw1_init cw2_init cw3_init cw4_init cw5_init cw6_init
    hfits_shim hfits_poll hfits_kp

theorem stageP2_sub4_some_kits_seqEnv_ext_placed [LibsignalPlacement]
    {M : AllocCostModel} {P : Primitives} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {F : ShaCompress} {BobV1Env : AcceptKeysInput → DRKey → List AllocEvent → Prop}
    {AcceptErrEnv : AcceptKeysInput → List AllocEvent → Prop}
    (ext : String → Option (State → State))
    (hH : StageP2ClosureHooksPlaced A lim ext)
    (hPure : StageP2PureCalleesPlaced4KOfEnv P A lim F BobV1Env AcceptErrEnv ext)
    (pkKit : PreKeyStoreSpec A.repAlloc 0#64)
    (pkEnv : PreKeyStoreBudgetEnv pkKit)
    (hpkOk : PreKeyStoreKitPlacedOk A lim pkKit pkEnv ext)
    (ikit : IdentityStoreSpec A.repAlloc 0#64)
    (skit : IdentitySelfStoreSpec ikit)
    (senv : IdentitySelfStoreBudgetEnv skit)
    (hskitVt : IdentitySelfVtablesPlacedOk ikit skit)
    (hskitOk : IdentitySelfStoreKitPlacedOkI A lim ikit skit senv ext)
    (stk : Nat) (hstk_pure : stageP2PureAndErrStack ≤ stk)
    (hstk_pk_shim : pkKit.getShimStack ≤ stk) (hstk_pk_poll : pkKit.getPollStack ≤ stk)
    (hstk_kp_shim : skit.kpShimStack ≤ stk) (hstk_lt : stk ≤ 2 ^ 64)
    (ret : BitVec 64) (st : M.σ) (s0 s : State) (Frame : SepProp)
    (Q : State → SepProp → Prop) {Qp : State → SepProp → Prop}
    (coroPtr msgPtr ctxPtr preKeyStorePtr idStorePtr ctSlicePtr
     v_98 v_a0 v_b0 u_a8 u_b8 u_d0 u_488 u_4f8 u_500 : BitVec 64)
    (opkId : BitVec 32) (stPk : pkKit.PkState)
    (b_4b0 s0_b s1_b s2_b s3_b s4_b s5_b s6_b
     c0_init c1_init c2_init c3_init c4_init c5_init c6_init c63_init : BitVec 8)
    (cw0_init cw1_init cw2_init cw3_init cw4_init cw5_init cw6_init : BitVec 64)
    (hfits : FitsEnv M lim st
      (SeqEnv (BoxAllocEnv pkKit.getBoxSize)
        (SeqEnv (pkEnv.getPollEnv stPk opkId)
          (SeqEnv FreeOnlyEvs (BoxAllocEnv skit.kpBoxSize))))) :
    stageP2Sub4SomeKitsPlacedProp A lim ext pkKit pkEnv ikit skit
      stk ret st s0 s Frame Q Qp
      coroPtr msgPtr ctxPtr preKeyStorePtr idStorePtr ctSlicePtr
      v_98 v_a0 v_b0 u_a8 u_b8 u_d0 u_488 u_4f8 u_500 opkId stPk
      b_4b0 s0_b s1_b s2_b s3_b s4_b s5_b s6_b
      c0_init c1_init c2_init c3_init c4_init c5_init c6_init c63_init
      cw0_init cw1_init cw2_init cw3_init cw4_init cw5_init cw6_init := by
  have hAfterShim :=
    hfits.seq_right ((boxAllocEnv_iff_eq pkKit.getBoxSize (boxAllocEvents pkKit.getBoxSize)).mpr rfl)
  exact stageP2_sub4_some_kits_ext_placed ext hH hPure pkKit pkEnv hpkOk ikit skit senv
    hskitVt hskitOk stk hstk_pure hstk_pk_shim hstk_pk_poll hstk_kp_shim hstk_lt
    ret st s0 s Frame Q (Qp := Qp)
    coroPtr msgPtr ctxPtr preKeyStorePtr idStorePtr ctSlicePtr
    v_98 v_a0 v_b0 u_a8 u_b8 u_d0 u_488 u_4f8 u_500 opkId stPk
    b_4b0 s0_b s1_b s2_b s3_b s4_b s5_b s6_b
    c0_init c1_init c2_init c3_init c4_init c5_init c6_init c63_init
    cw0_init cw1_init cw2_init cw3_init cw4_init cw5_init cw6_init
    hfits.seq_left
    hAfterShim.seq_left
    (fun _ evs_poll pubCap privCap _ _ hevs_poll _ _ => by
      have h1 := (hAfterShim.seq_right hevs_poll).seq_right
        (p2OpkRecFreeEvents_freeOnly pkKit.getBoxSize pubCap privCap)
      simpa only [M.stepEvents_append, List.append_assoc] using h1)

abbrev stageP2_sub4_some_kits_seqEnv_placed [LibsignalPlacement]
    {M : AllocCostModel} {P : Primitives} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {F : ShaCompress} {BobV1Env : AcceptKeysInput → DRKey → List AllocEvent → Prop}
    {AcceptErrEnv : AcceptKeysInput → List AllocEvent → Prop}
    (ext : String → Option (State → State))
    (hH : StageP2ClosureHooksPlaced A lim ext)
    (hPure : StageP2PureCalleesPlacedOfEnv P A lim F BobV1Env AcceptErrEnv ext) :=
  @stageP2_sub4_some_kits_seqEnv_ext_placed _ M P A lim F BobV1Env AcceptErrEnv ext hH hPure.to_4K

end LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP2Sub4PlacedBudget
