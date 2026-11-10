/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Over.StageP2DefsPlacedBudget
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Over.StageP2Sub4PlacedBudget
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Over.StageP2Sub6Aux
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Over.StageP2Sub6AuxPlaced
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP2BlocksB6PlacedBudget
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP2DefsPlacedBudget
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP2ErrArmsAPlacedBudget
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP2Sub5DefsPlacedBudget
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP2Sub6AuxPlacedBudget
import Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic
import ProofLib.SepLogic.WPp
import LibsignalBinary.Proofs.Common.SharedHelpers
meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP2Sub1
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP2Sub2
import LibsignalBinary.Proofs.E2E.Pqxdh.ResponderClosure.AssemblyP2bAux
import LibsignalBinary.Proofs.SpqrV1.Kdf.HkdfToSliceExtract
import LibsignalBinary.Proofs.SpqrV1.Poly.EncoderFromPb.Defs
import LibsignalBinary.Proofs.E2E.Pqxdh.Initiator.InitializeAliceStage1Common -- shake: keep

/-!
# Budget-Threaded Placed Stage P2 Over-Path Substage P2.6 Tail

Defines the allocator event sequence `p2OverSub6TailEvents` and envelope `P2OverSub6TailEnvOf`, and
proves budget-threaded `[LibsignalPlacement]` specifications for the Over-path Substage P2.6 tail
(`+0x0b3c → +0x1778`).
-/

@[expose] public section

set_option autoImplicit false

namespace LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Over.StageP2Sub6AuxPlacedBudget

open Arm64 ProofLib ProofLib.ProgramReflection SepProp
open CryptoGames CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open CryptoVerification CryptoVerification.RustHeap
open CryptoVerification.LibsignalSession CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchet.Getters
open CryptoVerification.LibsignalTripleRatchet.FromRecordCallees
open CryptoVerification.LibsignalPublicApiRepr CryptoVerification.LibsignalPublicApi
open CryptoVerification.LibsignalPublicApi.StoreSession
open CryptoVerification.LibsignalPublicApi.StoreKit
open CryptoVerification.LibsignalPublicApi.StoreKit.Identity
open CryptoVerification.LibsignalPublicApi.StoreKit.IdentitySelf
open CryptoVerification.RecordCodecs CryptoVerification.RecordCodecsBinary
open CryptoVerification.E2E.Bin
open CryptoVerification.E2E.Record.Serialization (encSessionMem)
open CryptoVerification.E2E.Pqxdh
open CryptoVerification.E2E.Pqxdh.Initiator hiding PanicOomProp
open CryptoVerification.E2E.Pqxdh.WireEntries hiding isSameAccountDistinctSpec
open CryptoVerification.E2E.Pqxdh.ResponderStore hiding
  promoteMatchingSessionEmptySpec
  promoteStateEmptySpec
  dropProcessPrekeyImplState1Spec
open CryptoVerification.E2E.Pqxdh.ResponderCore hiding
  initializeBobSessionErrOwnedPlacedSpec
open CryptoVerification.E2E.Pqxdh.ResponderClosure
open CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure
open CryptoVerification.CliHandshake.RespClosurePlaced
open CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Matched (prevSessionsEmptyAt)
open CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.OverP2 (
  clearPending clearPendingGhost prevVecAt
)
open CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Over (
  P2PromoteOverCallGhost
  p2PromoteStackX
  stageP2OverPureAndErrStack
  p2_over_basePure_le_overPure
  p2_over_promoteOver_le_overPure
  prevArchived1At
  prevArchived1At_eq
)
open CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Kits hiding
  StageP2ClosureHooksPlaced
  StageP2PureCalleesPlaced
  StageP2PureCalleesPlaced4K
  promoteStateEmpty4KSpec
  p2_bind_sepWP_steps_cro_sub5_qpan
  p2_seg6d1_gen_hooks_placed_wp
  p2_seg6d2_hooks_placed_wp
  p2_seg6e_1568_hooks_placed_wp
  p2_seg6f_ext_placed_wp
  stageP2Sub6TailV1AtPlacedProp
  stageP2_sub6_tail_v1_kits_ext_placed
  stageP2_sub6_tail_v1_kits_4k_placed
  stageP2_sub6_tail_v1_kits_placed
open LibsignalBinary.Heap (
  AllocCostModel AllocEvent BudgetLimits FitsEnv RustCliAllocBudget SeqEnv VmPreserved
  rustDeallocEvents
)
open LibsignalBinary.Heap.SpecBudget (withVmPreserved)
open LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP2DefsPlacedBudget (
  StageP2ClosureHooksPlaced
  StageP2PureCalleesPlaced
  StageP2PureCalleesPlaced4K
  StageP2PureCalleesPlaced4KOfEnv
  StageP2PureCalleesPlacedOfEnv
  dropProcessPrekeyImplState1Spec
)
open LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP2BlocksB6PlacedBudget (
  p2_seg6d1_gen_hooks_placed_wp
  p2_seg6d2_hooks_placed_wp
  p2_seg6e_1568_hooks_placed_wp
  p2_seg6f_ext_placed_wp
)
open LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP2Sub5DefsPlacedBudget (
  p2_bind_sepWP_steps_cro_sub5_qpan
  p2_bind_sepWP_steps_cro_sub5_state
)
open LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Over.StageP2DefsPlacedBudget (
  PromoteOverEnv
  PromoteOverAtPlacedWithEnvProp
  PromoteOverAtPlacedProp
  p2PromoteOverAtSpecWithEnv
)

set_option linter.unusedSimpArgs false
set_option maxRecDepth 200000

attribute [-arm64_norm]
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_sub_688_eq_hsp
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_add_neg688_eq_hsp
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_sub_96_eq_hsp_592
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_add_neg96_eq_hsp_592

set_option allowUnsafeReducibility true in
attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff
  decryptPrekeySavedRegsAt p2BobSessHead56Bv8
  prevArchived1At sessionStateReprAt

attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero

private theorem p2_over_alloc_le_overPure :
    allocHookStack ≤ stageP2OverPureAndErrStack :=
  Nat.le_trans p2_alloc_le_pure p2_over_basePure_le_overPure

/-! ## Tail Event Sequence and Envelope -/

/-- Allocator event sequence for the Over-path Substage P2.6 tail (`+0x0b3c → +0x1778`): frees
`regIdFutPtr` (`regIdBoxSize`, align 8), runs `<SessionRecord>::promote_state` (`evsProm`), and
frees `kyberKpPubPtr` (1568 B) and `kyberKpSecPtr` (3168 B). -/
def p2OverSub6TailEvents (regIdBoxSize : Nat) (evsProm : List AllocEvent) : List AllocEvent :=
  rustDeallocEvents regIdBoxSize 8 ++ evsProm ++
    (rustDeallocEvents 1568 1 ++ rustDeallocEvents 3168 1)

/-- Envelope-parameterized allocation envelope for the Over-path Substage P2.6 tail (`+0x0b3c → +0x1778`). -/
def P2OverSub6TailEnvOf
    (Env : SessionGhost → Session (List (BitVec 8)) → List AllocEvent → Prop)
    (regIdBoxSize : Nat) (recG : SessionGhost) (sess : Session (List (BitVec 8))) :
    List AllocEvent → Prop :=
  SeqEnv (fun evs => evs = rustDeallocEvents regIdBoxSize 8)
    (SeqEnv (Env recG sess)
      (fun evs => evs = rustDeallocEvents 1568 1 ++ rustDeallocEvents 3168 1))

/-- Over-path Substage P2.6 tail allocation envelope instantiated at `PromoteOverEnv`. -/
abbrev P2OverSub6TailEnv
    (regIdBoxSize : Nat) (recG : SessionGhost) (sess : Session (List (BitVec 8))) :
    List AllocEvent → Prop :=
  P2OverSub6TailEnvOf PromoteOverEnv regIdBoxSize recG sess

theorem p2OverSub6TailEnvOf_intro
    {Env : SessionGhost → Session (List (BitVec 8)) → List AllocEvent → Prop}
    {regIdBoxSize : Nat} {recG : SessionGhost} {sess : Session (List (BitVec 8))}
    {evsProm : List AllocEvent}
    (hProm : Env recG sess evsProm) :
    P2OverSub6TailEnvOf Env regIdBoxSize recG sess
      (p2OverSub6TailEvents regIdBoxSize evsProm) := by
  unfold p2OverSub6TailEvents P2OverSub6TailEnvOf
  rw [List.append_assoc]
  exact SeqEnv.append rfl (SeqEnv.append hProm rfl)

theorem fitsPromote_of_fitsTailEnv {M : AllocCostModel} {lim : BudgetLimits} {st : M.σ}
    {Env : SessionGhost → Session (List (BitVec 8)) → List AllocEvent → Prop}
    {regIdBoxSize : Nat} {recG : SessionGhost} {sess : Session (List (BitVec 8))}
    (h : FitsEnv M lim st (P2OverSub6TailEnvOf Env regIdBoxSize recG sess)) :
    FitsEnv M lim (M.stepEvents (rustDeallocEvents regIdBoxSize 8) st) (Env recG sess) :=
  (h.seq_right rfl).seq_left

/-! ## Budget-Threaded Placed Substage P2.6 Tail (`+0x0b3c → +0x1778`) -/

/-- Envelope-parameterized budget-threaded specification `Prop` for the placed Over-path Substage
P2.6 tail (`+0x0b3c → +0x1778`). -/
abbrev stageP2OverSub6TailV1AtPlacedWithEnvProp [LibsignalPlacement] {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (Env : SessionGhost → Session (List (BitVec 8)) → List AllocEvent → Prop)
    (ext : String → Option (State → State))
    {ikit : IdentityStoreSpec A.repAlloc 0#64} (skit : IdentitySelfStoreSpec ikit)
    (coroPtr : BitVec 64) (g : RecordGhost) (recG : SessionGhost)
    (sess : Session (List (BitVec 8))) : Prop :=
  ∀ {st : M.σ} {Qp : State → SepProp → Prop}
    (inp : AcceptKeysInput) (ikBPk spkBPk : SignalPqxdh.Bytes)
    (s0 s6 : State) (ret : BitVec 64) (Q : State → SepProp → Prop)
    (sp msgPtr remoteAddrPtr localAddrPtr outPtr
     regIdFutPtr kyberKpPubPtr kyberKpSecPtr ctBufPtr
     p1 p2 v_330 v_388
     u_298 u_2a0 u_80 u_90 u_400 u_3f0 u_3f8
     u_3a0 u_3b0 u_3b8 u_3c0 u_3c8 u_3d0 u_3d8 : BitVec 64)
    (mid : List (BitVec 8)), mid.length = 280 →
    ∀ (localRegId remoteRegId opkIdIsSome opkId kyberPreKeyId signedPreKeyId u_2a8 : BitVec 32)
      (msgVerByte b_4f2 b_390 b_3ac : BitVec 8)
      (stk : Nat) (F_rest : SepProp),
    WellSizedAcceptKeysInput inp →
    ctBufPtr ≠ 0#64 →
    stageP2OverPureAndErrStack ≤ stk →
    stk ≤ sp.toNat →
    FitsEnv M lim (M.stepEvents (rustDeallocEvents skit.regIdBoxSize 8) st) (Env recG sess) →
    StoreKit.LibsignalCodeRoLoaded lsmpl s6.mem →
    s6.pc = stageP1EntryPlaced + 0xb3c#64 →
    s6.status = .Running →
    s6.sp = sp →
    (sp &&& 15#64 == 0#64) = true →
    calleeSavedVRegs s6 = calleeSavedVRegs s0 →
    s6.readReg64 .x19 = coroPtr →
    s6.readReg64 .x21 = regIdFutPtr →
    s6.readReg64 .x23 = localRegId.zeroExtend 64 →
    s6.readReg64 .x24 = 0#64 + skit.regIdFutVtOff →
    (∀ (evsProm : List AllocEvent) (sf : State),
      Env recG sess evsProm →
      Steps (stageP1ProgPlaced ext) s6 sf →
      sf.pc = stageP1EntryPlaced + 0x1778#64 →
      sf.status = .Running →
      sf.sp = sp →
      sf.trace = s6.trace →
      sf.readReg64 .x8 = coroPtr + 0xe0#64 →
      sf.readReg64 .x9 = 8#64 →
      sf.readReg64 .x10 = msgVerByte.zeroExtend 64 →
      sf.readReg64 .x11 = coroPtr + 0xf8#64 →
      sf.readReg64 .x19 = coroPtr →
      sf.readReg64 .x20 = 0xfffffffffffffffe#64 →
      sf.readReg64 .x22 = (kyberPreKeyId.zeroExtend 64 <<< 32) ||| 1#64 →
      sf.readReg64 .x23 = opkIdIsSome.zeroExtend 64 ||| (opkId.zeroExtend 64 <<< 32) →
      sf.readReg64 .x24 = opkIdIsSome.zeroExtend 64 ||| (opkId.zeroExtend 64 <<< 32) →
      sf.readReg64 .x25 = s6.readReg64 .x25 →
      sf.readReg64 .x26 = v_330 →
      sf.readReg64 .x27 = sp + 0x370#64 →
      sf.readReg64 .x28 = s6.readReg64 .x28 →
      sf.readReg64 .x29 = s6.readReg64 .x29 →
      calleeSavedVRegs sf = calleeSavedVRegs s0 →
      StoreKit.LibsignalCodeRoLoaded lsmpl sf.mem →
      SepWPp (stageP1ProgPlaced ext) ret sf
        (prevArchived1At A.repAlloc coroPtr recG sess ∗
         ((coroPtr + 0xf8#64) ↦ₛ (p2BobSessHead56Bv8 p1 p2 ++
           (mid ++ (unpack32 remoteRegId ++ unpack32 localRegId)))) ∗
         ((coroPtr + 0x4f8#64) ↦ₛ (p2BobSessHead56Bv8 p1 p2 ++
           (mid ++ (unpack32 remoteRegId ++ unpack32 localRegId)))) ∗
         ((sp + 0x3e0#64) ↦ₛ (p2BobSessHead56Bv8 p1 p2 ++
           (mid ++ (unpack32 remoteRegId ++ unpack32 localRegId)))) ∗
         ((coroPtr + 0x650#64) ↦₆₄ (coroPtr + 0x4f8#64)) ∗
         ((coroPtr + 0x468#64) ↦₆₄ msgPtr) ∗
         ((coroPtr + 0x480#64) ↦₆₄ (coroPtr + 0xe0#64)) ∗
         ((coroPtr + 0x718#64) ↦₆₄ kyberKpPubPtr) ∗
         ((coroPtr + 0x720#64) ↦₆₄ 0x620#64) ∗
         ((coroPtr + 0x728#64) ↦₆₄ kyberKpSecPtr) ∗
         ((coroPtr + 0x730#64) ↦₆₄ 0xc60#64) ∗
         ((coroPtr + 0x738#64) ↦₆₄ (msgPtr + 0x90#64)) ∗
         ((coroPtr + 0x740#64) ↦₈ opkPresentTag inp.opkBSk?) ∗
         opkOptFieldAt (coroPtr + 0x761#64) inp.opkBSk? ∗
         ((coroPtr + 0x781#64) ↦₈ 0#8) ∗
         ((coroPtr + 0x398#64) ↦ₛ bytesToBv8 spkBPk) ∗
         ((coroPtr + 0x3b8#64) ↦ₛ bytesToBv8 inp.spkBSk) ∗
         ((coroPtr + 0x658#64) ↦ₛ bytesToBv8 ikBPk) ∗
         ((coroPtr + 0x678#64) ↦ₛ bytesToBv8 inp.ikBSk) ∗
         ((coroPtr + 0x6b8#64) ↦ₛ bytesToBv8 inp.spkBSk) ∗
         ((coroPtr + 0x6d8#64) ↦ₛ bytesToBv8 inp.hdr.ikAPk) ∗
         ((coroPtr + 0x6f8#64) ↦ₛ bytesToBv8 inp.hdr.ekAPk) ∗
         ((coroPtr + 0x4f1#64) ↦₈ 0#8) ∗
         ((coroPtr + 0x4f2#64) ↦₈ 1#8) ∗
         ((coroPtr + 0x70#64) ↦₆₄ msgPtr) ∗
         ((coroPtr + 0x78#64) ↦₆₄ remoteAddrPtr) ∗
         ((coroPtr + 0x80#64) ↦₆₄ localAddrPtr) ∗
         cells (coroPtr + 0x250#64) 6 ∗
         ((coroPtr + 0x298#64) ↦₆₄ (opkIdIsSome.zeroExtend 64 ||| (opkId.zeroExtend 64 <<< 32))) ∗
         ((coroPtr + 0x2a0#64) ↦₆₄ ((kyberPreKeyId.zeroExtend 64 <<< 32) ||| 1#64)) ∗
         ((coroPtr + 0x2a8#64) ↦₃₂ signedPreKeyId) ∗
         ((coroPtr + 0x330#64) ↦₆₄ v_330) ∗
         ((coroPtr + 0x388#64) ↦₆₄ v_388) ∗
         ((coroPtr + 0x390#64) ↦₈ 1#8) ∗
         ((msgPtr + 0x70#64) ↦₈ msgVerByte) ∗
         ((msgPtr + 0x78#64) ↦₃₂ opkIdIsSome) ∗
         ((msgPtr + 0x7c#64) ↦₃₂ opkId) ∗
         ((msgPtr + 0x90#64) ↦₆₄ ctBufPtr) ∗
         ((msgPtr + 0x98#64) ↦₆₄ 1569#64) ∗
         ((msgPtr + 0xa0#64) ↦₃₂ kyberPreKeyId) ∗
         ((msgPtr + 0xe8#64) ↦₃₂ remoteRegId) ∗
         ((msgPtr + 0xec#64) ↦₃₂ signedPreKeyId) ∗
         (ctBufPtr ↦₈ 8#8) ∗
         ((ctBufPtr + 1#64) ↦₈ (bytesToBv8 inp.hdr.kemCt).getD 0 0#8) ∗
         ((ctBufPtr + 2#64) ↦ₛ (bytesToBv8 inp.hdr.kemCt).drop 1) ∗
         ((sp + 0x80#64) ↦₆₄ (coroPtr + 0xf8#64)) ∗
         ((sp + 0x88#64) ↦₆₄ (coroPtr + 0xe0#64)) ∗
         ((sp + 0x90#64) ↦₆₄ v_388) ∗
         ((sp + 0x98#64) ↦₆₄ (coroPtr + 0x398#64)) ∗
         ((sp + 0xa0#64) ↦₆₄ localAddrPtr) ∗
         ((sp + 0xa8#64) ↦₆₄ v_330) ∗
         ((sp + 0xb0#64) ↦₆₄ msgPtr) ∗
         ((sp + 0xb8#64) ↦₃₂ msgVerByte.zeroExtend 32) ∗
         memRegion (sp + 0xbc#64) 4 ∗
         ((sp + 0xc8#64) ↦₆₄ outPtr) ∗
         ((sp + 0xd0#64) ↦₆₄ signedPreKeyId.zeroExtend 64) ∗
         ((sp + 0x3a0#64) ↦₆₄ remoteAddrPtr) ∗
         ((sp + 0x3ac#64) ↦₈ 3#8) ∗
         ((sp + 0x3b0#64) ↦₆₄ (sp + 0x3ac#64)) ∗
         ((sp + 0x3b8#64) ↦₆₄ msgPtr) ∗
         ((sp + 0x3c0#64) ↦₆₄ (sp + 0x3a0#64)) ∗
         ((sp + 0x3c8#64) ↦₆₄ 0#64) ∗
         ((sp + 0x3d0#64) ↦₆₄ 8#64) ∗
         ((sp + 0x3d8#64) ↦₆₄ 0#64) ∗
         A.pool lim (M.stepEvents (p2OverSub6TailEvents skit.regIdBoxSize evsProm) st) sf ∗
         stackAt sp stk ∗ F_rest)
        Q Qp) →
    SepWPp (stageP1ProgPlaced ext) ret s6
      (bobParamsFieldsAt (coroPtr + 0x658#64) kyberKpSecPtr (msgPtr + 0x90#64) ctBufPtr
         (coroPtr + 0x398#64) inp ikBPk spkBPk 0#8 ∗
       ((coroPtr + 0x4f8#64) ↦₆₄ 33#64) ∗
       ((coroPtr + 0x500#64) ↦₆₄ p1) ∗
       ((coroPtr + 0x508#64) ↦₆₄ 33#64) ∗
       ((coroPtr + 0x510#64) ↦₆₄ 33#64) ∗
       ((coroPtr + 0x518#64) ↦₆₄ p2) ∗
       ((coroPtr + 0x520#64) ↦₆₄ 33#64) ∗
       ((coroPtr + 0x528#64) ↦₆₄ 32#64) ∗
       ((coroPtr + 0x530#64) ↦ₛ (mid ++ unpack64 0#64)) ∗
       ((coroPtr + 0x650#64) ↦₆₄ (coroPtr + 0x4f8#64)) ∗
       memRegion (sp + 0x3e0#64) 344 ∗
       A.live regIdFutPtr skit.regIdBoxSize 8 ∗
       memRegion regIdFutPtr skit.regIdBoxSize ∗
       ((coroPtr + 0x468#64) ↦₆₄ msgPtr) ∗
       ((coroPtr + 0x480#64) ↦₆₄ (coroPtr + 0xe0#64)) ∗
       ((coroPtr + 0x718#64) ↦₆₄ kyberKpPubPtr) ∗
       ((coroPtr + 0x720#64) ↦₆₄ 0x620#64) ∗
       ((coroPtr + 0x4f1#64) ↦₈ 0#8) ∗
       ((coroPtr + 0x4f2#64) ↦₈ b_4f2) ∗
       prevSessionsEmptyAt A.repAlloc coroPtr g ∗
       sessionStateReprAt A.repAlloc (coroPtr + 0xf8#64) recG sess ∗
       ((coroPtr + 0x70#64) ↦₆₄ msgPtr) ∗
       ((coroPtr + 0x78#64) ↦₆₄ remoteAddrPtr) ∗
       ((coroPtr + 0x80#64) ↦₆₄ localAddrPtr) ∗
       cells (coroPtr + 0x250#64) 6 ∗
       ((coroPtr + 0x298#64) ↦₆₄ u_298) ∗
       ((coroPtr + 0x2a0#64) ↦₆₄ u_2a0) ∗
       ((coroPtr + 0x2a8#64) ↦₃₂ u_2a8) ∗
       ((coroPtr + 0x330#64) ↦₆₄ v_330) ∗
       ((coroPtr + 0x388#64) ↦₆₄ v_388) ∗
       ((coroPtr + 0x390#64) ↦₈ b_390) ∗
       ((msgPtr + 0x70#64) ↦₈ msgVerByte) ∗
       ((msgPtr + 0x78#64) ↦₃₂ opkIdIsSome) ∗
       ((msgPtr + 0x7c#64) ↦₃₂ opkId) ∗
       ((msgPtr + 0xa0#64) ↦₃₂ kyberPreKeyId) ∗
       ((msgPtr + 0xe8#64) ↦₃₂ remoteRegId) ∗
       ((msgPtr + 0xec#64) ↦₃₂ signedPreKeyId) ∗
       ((sp + 0x80#64) ↦₆₄ u_80) ∗ ((sp + 0x88#64) ↦₆₄ 0xfffffffffffffffe#64) ∗
       ((sp + 0x90#64) ↦₆₄ u_90) ∗ ((sp + 0x98#64) ↦₆₄ (coroPtr + 0x398#64)) ∗
       ((sp + 0xa0#64) ↦₆₄ (coroPtr + 0x4f2#64)) ∗ ((sp + 0xa8#64) ↦₆₄ u_400) ∗
       ((sp + 0xb0#64) ↦₆₄ (coroPtr + 0x390#64)) ∗ ((sp + 0xb8#64) ↦₆₄ u_3f0) ∗
       ((sp + 0xc8#64) ↦₆₄ outPtr) ∗ ((sp + 0xd0#64) ↦₆₄ u_3f8) ∗
       ((sp + 0x3a0#64) ↦₆₄ u_3a0) ∗ ((sp + 0x3ac#64) ↦₈ b_3ac) ∗
       ((sp + 0x3b0#64) ↦₆₄ u_3b0) ∗ ((sp + 0x3b8#64) ↦₆₄ u_3b8) ∗
       ((sp + 0x3c0#64) ↦₆₄ u_3c0) ∗ ((sp + 0x3c8#64) ↦₆₄ u_3c8) ∗
       ((sp + 0x3d0#64) ↦₆₄ u_3d0) ∗ ((sp + 0x3d8#64) ↦₆₄ u_3d8) ∗
       A.live kyberKpPubPtr 1568 1 ∗
       memRegion kyberKpPubPtr 1568 ∗
       A.live kyberKpSecPtr 3168 1 ∗
       A.pool lim st s6 ∗ stackAt sp stk ∗ F_rest)
      Q Qp

abbrev stageP2OverSub6TailV1AtPlacedProp [LibsignalPlacement] {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (ext : String → Option (State → State))
    {ikit : IdentityStoreSpec A.repAlloc 0#64} (skit : IdentitySelfStoreSpec ikit)
    (coroPtr : BitVec 64) (g : RecordGhost) (recG : SessionGhost)
    (sess : Session (List (BitVec 8))) : Prop :=
  stageP2OverSub6TailV1AtPlacedWithEnvProp A lim PromoteOverEnv ext skit coroPtr g recG sess

set_option maxHeartbeats 1200000 in
/-- Budget-threaded placed Over-path Substage P2.6 tail (`+0x0b3c → +0x1778`) in direct callee form. -/
theorem stageP2_over_sub6_tail_v1_kits_callees_withEnv_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {Env : SessionGhost → Session (List (BitVec 8)) → List AllocEvent → Prop}
    (ext : String → Option (State → State))
    {ikit : IdentityStoreSpec A.repAlloc 0#64} (skit : IdentitySelfStoreSpec ikit)
    (hH : StageP2ClosureHooksPlaced A lim ext)
    (hskitVt : IdentitySelfVtablesPlacedOk ikit skit)
    (coroPtr : BitVec 64) (g : RecordGhost) (recG : SessionGhost)
    (sess : Session (List (BitVec 8)))
    (hPromoteOver : PromoteOverAtPlacedWithEnvProp M A lim Env ext coroPtr g recG sess)
    (hDrop :
      subroutine_ok (stageP1ProgPlaced ext)
        (lsmpl.base 509)
        (withLsCodeLoaded lsmpl dropProcessPrekeyImplState1Spec)) :
    stageP2OverSub6TailV1AtPlacedWithEnvProp A lim Env ext skit coroPtr g recG sess := by
  intro st Qp inp ikBPk spkBPk s0 s6 ret Q
    sp msgPtr remoteAddrPtr localAddrPtr outPtr
    regIdFutPtr kyberKpPubPtr kyberKpSecPtr ctBufPtr
    p1 p2 v_330 v_388
    u_298 u_2a0 u_80 u_90 u_400 u_3f0 u_3f8
    u_3a0 u_3b0 u_3b8 u_3c0 u_3c8 u_3d0 u_3d8
    mid hmid
    localRegId remoteRegId opkIdIsSome opkId kyberPreKeyId signedPreKeyId u_2a8
    msgVerByte b_4f2 b_390 b_3ac stk F_rest
    hwell hctBuf_nz hstk_pure hstk_lt hfit_prom hCode6 hpc6 hrun6 hsp6 hsp_align hvregs6
    hx19_6 hx21_6 hx23_6 hx24_6 hOk
  subst hsp6
  have hstk_le64 : stk ≤ 2 ^ 64 := Nat.le_trans hstk_lt (Nat.le_of_lt s6.sp.isLt)
  refine p2_sepWPp_intro_ro_placed hCode6 (fun hc hm => hskitVt.regIdFutSize hc.2 hm) ?_
  refine p2_sepWPp_intro_ro_placed hCode6 (fun hc hm => hskitVt.regIdFutAlign hc.2 hm) ?_
  refine SepWPp.weaken_frame
    (Entails.of_eq (bobParamsFieldsAt_intro coroPtr msgPtr kyberKpSecPtr ctBufPtr inp ikBPk
      spkBPk).symm)
    (by sep_focus) ?_
  refine SepWPp.weaken_frame (pqsk_entails_memRegion3168 kyberKpSecPtr inp.pqspkBSk
    hwell.2.2.2.2.2.1)
    (by sep_focus) ?_
  have hstk_alloc := p2_stackAt_split_of_le s6.sp stk allocHookStack
    (Nat.le_trans p2_over_alloc_le_overPure hstk_pure) hstk_le64
  have hstk_prom := p2_stackAt_split_of_le s6.sp stk p2PromoteStackX
    (Nat.le_trans p2_over_promoteOver_le_overPure hstk_pure) hstk_le64
  refine SepWPp.weaken_frame (Entails.of_eq hstk_alloc) (by sep_focus) ?_
  have h530_split := p2_sub6_bobSession288Rest_split_280_4_4 (coroPtr + 0x530#64) mid hmid
  simp only [BitVec.add_assoc, BitVec.reduceAdd] at h530_split
  refine SepWPp.weaken_frame (Entails.of_eq h530_split) (by sep_focus) ?_
  let st1 : M.σ := M.stepEvents (rustDeallocEvents skit.regIdBoxSize 8) st
  have hstep7 := p2_seg6d1_gen_hooks_placed_wp (st := st) ext hH s6 coroPtr msgPtr regIdFutPtr
    (0#64 + skit.regIdFutVtOff) localRegId remoteRegId 0#32 0#32 skit.regIdBoxSize
    hpc6 hrun6 hsp_align skit.regIdBoxSize_ne_zero skit.regIdBoxSize_lt
    hx19_6 hx21_6 hx23_6 hx24_6
  refine p2_bind_sepWP_steps_cro_sub5_state hCode6 hstep7 (by sep_focus)
    fun s7 hst67 hpc7 hrun7 hCode7 hregs7 => ?_
  rcases hregs7 with ⟨hsp7, htr7, hx0_7, hx1_7, hx2_7, hx19_7, hx21_7, _, _, _, hx25_7, _, _,
    hx28_7, hx29_7, hvregs7, _⟩
  have hsp7_align : (s7.sp &&& 15#64 == 0#64) = true := by rw [hsp7]; exact hsp_align
  refine p2_drop_frame_sub6
    (Drop := ((0#64 + skit.regIdFutVtOff + 8#64) ↦₆₄ᵣ BitVec.ofNat 64 skit.regIdBoxSize) ∗
             ((0#64 + skit.regIdFutVtOff + 0x10#64) ↦₆₄ᵣ 8#64))
    (by simp only [BitVec.add_assoc, BitVec.reduceAdd]; sep_focus) ?_
  have h4f8_fold := p2_sub6_bobSession344WithRegIds_fold (coroPtr + 0x4f8#64) p1 p2 mid hmid
    remoteRegId localRegId
  simp only [BitVec.add_assoc, BitVec.reduceAdd] at h4f8_fold
  refine SepWPp.weaken_frame (Entails.of_eq h4f8_fold) (by sep_focus) ?_
  have hx0_7' : s7.readReg64 .x0 = s7.sp + 0x3e0#64 := by rw [hx0_7, hsp7]
  have hssWithReg_len :=
    p2_sub6_bobSession344WithRegIds_length p1 p2 mid hmid remoteRegId localRegId
  have hstep8 := p2_seg6d2_hooks_placed_wp ext hH s7 coroPtr
    (p2BobSessHead56Bv8 p1 p2 ++ (mid ++ (unpack32 remoteRegId ++ unpack32 localRegId)))
    hssWithReg_len hpc7 hrun7 hsp7_align hx0_7' hx1_7 hx2_7 hx19_7 hx21_7
  rw [hsp7] at hstep8
  refine p2_bind_sepWP_steps_cro_sub5_qpan hCode7 hstep8 (by sep_focus)
    fun s8 hst78 hpc8 hrun8 hCode8 hregs8 => ?_
  rcases hregs8 with ⟨hsp8, htr8, hx0_8, hx1_8, hx19_8, _, _, _, _, hx25_8, _, _, hx28_8, hx29_8,
    hx30_8, hvregs8, hvm8_7⟩
  have hsp8_al : s8.spAligned = true := by simpa only [State.spAligned, hsp8] using hsp_align
  refine SepWPp.weaken_frame
    (Entails.of_eq (A.pool_of_vmPreserved (st := st1) hvm8_7).symm)
    (by sep_focus) ?_
  refine SepWPp.weaken_frame (Entails.of_eq hstk_alloc.symm) (by sep_focus) ?_
  refine SepWPp.weaken_frame (Entails.of_eq hstk_prom) (by sep_focus) ?_
  have hpc8_eq :
      libsignalSessionLib.resolve lsmpl
        "<libsignal_protocol::state::session::SessionRecord>::promote_state" = lsmpl.base 47 :=
    BitVec.add_zero _
  rw [hpc8_eq] at hpc8
  let newBs := p2BobSessHead56Bv8 p1 p2 ++ (mid ++ (unpack32 remoteRegId ++ unpack32 localRegId))
  refine p2_call_nopanic_lscl_steps_frame_placed
    (x := (P2PromoteOverCallGhost.mk (s6.sp + 0x3e0#64) newBs, st1))
    (R_pure := s8.readReg64 .x0 = coroPtr + 0xe0#64 ∧
      s8.readReg64 .x1 = s6.sp + 0x3e0#64 ∧
      newBs.length = 344 ∧
      FitsEnv M lim st1 (Env recG sess))
    (T := prevSessionsEmptyAt A.repAlloc coroPtr g ∗
      sessionStateReprAt A.repAlloc (coroPtr + 0xf8#64) recG sess ∗
      A.pool lim st1 s8 ∗
      ((s6.sp + 0x3e0#64) ↦ₛ newBs) ∗
      stackAt s6.sp p2PromoteStackX)
    hCode8
    (CryptoVerification.E2E.Record.Serialization.SerializeBodyAuxX.subroutine_ok_withLsCodeLoaded_of_withLsCl
      hPromoteOver)
    hpc8 hrun8 hsp8_al hx30_8
    (by
      dsimp only [p2PromoteOverAtSpecWithEnv, newBs]
      rw [hsp8])
    ⟨hx0_8, hx1_8, hssWithReg_len, hfit_prom⟩ (by sep_focus)
    (hnext := fun s9 hst89 hpc9 hrun9 hsp9_8 _ hcs9 hCode9 => ?_)
  dsimp only [p2PromoteOverAtSpecWithEnv, newBs]
  rw [hsp8, prevArchived1At_eq A.repAlloc coroPtr recG sess]
  conv => arg 4; (try simp only [sepConj_assoc])
  refine SepWPp.pure_elim fun htr9_8 => ?_
  conv => arg 4; simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  refine SepWPp.exists_elim fun evsProm => ?_
  refine SepWPp.weaken_frame (Entails.refl ⌜Env recG sess evsProm⌝) (by sep_focus) ?_
  refine SepWPp.pure_elim fun hevsProm => ?_
  refine SepWPp.weaken_frame (Entails.of_eq hstk_prom.symm) (by sep_focus) ?_
  refine SepWPp.weaken_frame (Entails.of_eq hstk_alloc) (by sep_focus) ?_
  have hsp9 : s9.sp = s6.sp := hsp9_8.trans hsp8
  have hsp9_align : (s9.sp &&& 15#64 == 0#64) = true := by rw [hsp9]; exact hsp_align
  rcases hcs9 with ⟨hx19_cs9, _, _, _, _, _, hx25_cs9, _, _, hx28_cs9, hx29_cs9, hvregs9_8⟩
  have hx19_9 : s9.readReg64 .x19 = coroPtr := hx19_cs9.trans hx19_8
  have hx25_9 : s9.readReg64 .x25 = s6.readReg64 .x25 := by rw [hx25_cs9, hx25_8, hx25_7]
  have hx28_9 : s9.readReg64 .x28 = s6.readReg64 .x28 := by rw [hx28_cs9, hx28_8, hx28_7]
  have hx29_9 : s9.readReg64 .x29 = s6.readReg64 .x29 := by rw [hx29_cs9, hx29_8, hx29_7]
  let st2 : M.σ := M.stepEvents evsProm st1
  have hstep10 := p2_seg6e_1568_hooks_placed_wp (st := st2) ext hH s9 coroPtr msgPtr ctBufPtr
    kyberKpPubPtr kyberKpSecPtr outPtr u_400 u_3f8
    opkIdIsSome opkId kyberPreKeyId signedPreKeyId 0#8 b_4f2
    hctBuf_nz hpc9 hrun9 hsp9_align hx19_9
  rw [hsp9] at hstep10
  refine p2_bind_sepWP_steps_cro_sub5_state hCode9 hstep10 (by sep_focus)
    fun s10 hst910 hpc10 hrun10 hCode10 hregs10 => ?_
  rcases hregs10 with ⟨hsp10, htr10, hx0_10, hx19_10, hx20_10, _, hx22_10, hx23_10, hx24_10,
    hx25_10, _, _, hx28_10, hx29_10, hx30_10, hvregs10, _⟩
  have hsp10_al : s10.spAligned = true := by simpa only [State.spAligned, hsp10] using hsp_align
  have hst_final_eq :
      M.stepEvents (rustDeallocEvents 1568 1 ++ rustDeallocEvents 3168 1) st2 =
        M.stepEvents (p2OverSub6TailEvents skit.regIdBoxSize evsProm) st := by
    simp only [p2OverSub6TailEvents, st2, st1, M.stepEvents_append]
  refine SepWPp.weaken_frame
    (Entails.of_eq (congrArg (fun st' => A.pool lim st' s10) hst_final_eq))
    (by sep_focus) ?_
  have hstk48 : stackAt s6.sp allocHookStack =
      stackAt (s6.sp - 48#64) (allocHookStack - 48) ∗ cells (s6.sp - 48#64) 6 :=
    ProofLib.stackAt_split_cells s6.sp (allocHookStack - 48) 6 (by decide)
  refine SepWPp.weaken_frame (Entails.of_eq hstk48) (by sep_focus) ?_
  have hpc10_eq :
      libsignalSessionLib.resolve lsmpl
        "core::ptr::drop_glue::<libsignal_protocol::session::process_prekey_impl::{closure#0}>" =
      lsmpl.base 509 :=
    BitVec.add_zero _
  rw [hpc10_eq] at hpc10
  refine p2_call_nopanic_lscl_steps_frame_placed (x := coroPtr + 0x398#64)
    (T := ((coroPtr + 0x4f2#64) ↦₈ 1#8) ∗ cells (s6.sp - 48#64) 6)
    hCode10 hDrop hpc10 hrun10 hsp10_al hx30_10
    (by
      dsimp only [dropProcessPrekeyImplState1Spec, withVmPreserved,
        CryptoVerification.E2E.Pqxdh.ResponderStore.dropProcessPrekeyImplState1Spec]
      rw [hsp10,
          show (coroPtr + 0x398#64) + 0x15a#64 = coroPtr + 0x4f2#64 by rw [BitVec.add_assoc]; rfl])
    hx0_10 (by sep_focus)
    (hnext := fun s11 hst1011 hpc11 hrun11 hsp11_10 _ hcs11 hCode11 => ?_)
  dsimp only [dropProcessPrekeyImplState1Spec, withVmPreserved,
    CryptoVerification.E2E.Pqxdh.ResponderStore.dropProcessPrekeyImplState1Spec]
  rw [hsp10,
      show (coroPtr + 0x398#64) + 0x15a#64 = coroPtr + 0x4f2#64 by rw [BitVec.add_assoc]; rfl]
  conv => arg 4; (try simp only [sepConj_assoc])
  refine SepWPp.pure_elim fun hvm11_10 => ?_
  refine SepWPp.pure_elim fun htr11_10 => ?_
  refine SepWPp.weaken_frame
    (Entails.of_eq
      (A.pool_of_vmPreserved
        (st := M.stepEvents (p2OverSub6TailEvents skit.regIdBoxSize evsProm) st)
        hvm11_10).symm)
    (by sep_focus) ?_
  refine SepWPp.weaken_frame (Entails.of_eq hstk48.symm) (by sep_focus) ?_
  refine SepWPp.weaken_frame (Entails.of_eq hstk_alloc.symm) (by sep_focus) ?_
  have hsp11 : s11.sp = s6.sp := hsp11_10.trans hsp10
  have hsp11_align : (s11.sp &&& 15#64 == 0#64) = true := by rw [hsp11]; exact hsp_align
  rcases hcs11 with ⟨hx19_cs11, hx20_cs11, _, hx22_cs11, hx23_cs11, hx24_cs11, hx25_cs11, _, _,
    hx28_cs11, hx29_cs11, hvregs11_10⟩
  have hx19_11 : s11.readReg64 .x19 = coroPtr := hx19_cs11.trans hx19_10
  have hx20_11 : s11.readReg64 .x20 = 0xfffffffffffffffe#64 := hx20_cs11.trans hx20_10
  have hx22_11 : s11.readReg64 .x22 = (kyberPreKeyId.zeroExtend 64 <<< 32) ||| 1#64 :=
    hx22_cs11.trans hx22_10
  have hx23_11 : s11.readReg64 .x23 = opkIdIsSome.zeroExtend 64 := hx23_cs11.trans hx23_10
  have hx24_11 : s11.readReg64 .x24 = opkIdIsSome.zeroExtend 64 ||| (opkId.zeroExtend 64 <<< 32) :=
    hx24_cs11.trans hx24_10
  have hx25_11 : s11.readReg64 .x25 = s6.readReg64 .x25 := by rw [hx25_cs11, hx25_10, hx25_9]
  have hx28_11 : s11.readReg64 .x28 = s6.readReg64 .x28 := by rw [hx28_cs11, hx28_10, hx28_9]
  have hx29_11 : s11.readReg64 .x29 = s6.readReg64 .x29 := by rw [hx29_cs11, hx29_10, hx29_9]
  have hhead_split := p2_sub6_bobSession344WithRegIds_head_split (coroPtr + 0xf8#64) p1 p2 mid
    remoteRegId localRegId
  rw [show (coroPtr + 0xf8#64) + 8#64 = coroPtr + 0x100#64 by
    rw [BitVec.add_assoc]; rfl] at hhead_split
  refine SepWPp.weaken_frame (Entails.of_eq hhead_split) (by sep_focus) ?_
  refine SepWPp.weaken_frame (cells6_250_split_for_seg6f coroPtr) (by sep_focus) ?_
  conv => arg 4; simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  refine SepWPp.exists_elim fun u_250 => SepWPp.exists_elim fun u_258 =>
    SepWPp.exists_elim fun u_260 => SepWPp.exists_elim fun u_268 =>
    SepWPp.exists_elim fun u_26c => SepWPp.exists_elim fun u_270 =>
    SepWPp.exists_elim fun u_278 => ?_
  have hb8_split : ((s6.sp + 0xb8#64) ↦₆₄ u_3f0) =
      ((s6.sp + 0xb8#64) ↦₃₂ (u_3f0.extractLsb' 0 32)) ∗
      ((s6.sp + 0xbc#64) ↦₃₂ (u_3f0.extractLsb' 32 32)) := by
    simpa only [BitVec.add_assoc, BitVec.reduceAdd] using pointsTo64_split32 (s6.sp + 0xb8#64) u_3f0
  refine SepWPp.weaken_frame (Entails.of_eq hb8_split) (by sep_focus) ?_
  have hpack_lo : ((opkIdIsSome.zeroExtend 64 ||| (opkId.zeroExtend 64 <<< 32)) &&& 0xff#64) =
      (opkIdIsSome.zeroExtend 64 &&& 0xff#64) := by bv_kernel
  have hstep12 := p2_seg6f_ext_placed_wp ext s11 coroPtr msgPtr remoteAddrPtr localAddrPtr
    (opkIdIsSome.zeroExtend 64 ||| (opkId.zeroExtend 64 <<< 32))
    ((kyberPreKeyId.zeroExtend 64 <<< 32) ||| 1#64)
    33#64 v_330 v_388
    u_250 u_258 u_260 u_270 u_278 u_298 u_2a0
    u_80 0xfffffffffffffffe#64 u_90 (coroPtr + 0x4f2#64) 0#64 (coroPtr + 0x390#64)
    u_3a0 u_3b0 u_3b8 u_3c0 u_3c8 u_3d0 u_3d8
    opkIdIsSome signedPreKeyId u_268 u_26c u_2a8 (u_3f0.extractLsb' 0 32)
    msgVerByte b_390 b_3ac
    (by decide) hpack_lo hpc11 hrun11 hsp11_align hx19_11 hx20_11 hx22_11 hx23_11 hx24_11
  rw [hsp11] at hstep12
  have hsub_3b0 : s6.sp + 0x3b0#64 - (s6.sp + 0x3b0#64) + u_3b0 = u_3b0 := by bv_omega
  rw [hsub_3b0] at hstep12
  refine p2_bind_sepWP_steps_cro_sub5_qpan hCode11 hstep12 (by sep_focus)
    fun sf hst11f hpcf hrunf hCodef hregsf => ?_
  rcases hregsf with ⟨hspf, htrf, hx8_f, hx9_f, hx10_f, hx11_f, hx19_f, hx20_f,
    hx22_f, hx23_f, hx24_f, hx25_f, hx26_f, hx27_f, hx28_f, hx29_f, hvregsf, hvmf_11⟩
  refine SepWPp.weaken_frame
    (Entails.of_eq
      (A.pool_of_vmPreserved
        (st := M.stepEvents (p2OverSub6TailEvents skit.regIdBoxSize evsProm) st)
        hvmf_11).symm)
    (by sep_focus) ?_
  refine SepWPp.weaken_frame (Entails.of_eq hhead_split.symm) (by sep_focus) ?_
  refine SepWPp.weaken_frame
    (cells6_250_fold coroPtr 0xfffffffffffffffe#64
      (opkIdIsSome.zeroExtend 64 ||| (opkId.zeroExtend 64 <<< 32))
      ((kyberPreKeyId.zeroExtend 64 <<< 32) ||| 1#64)
      v_330 v_388 signedPreKeyId ((s11.readReg64 (Reg.gpr 11#5)).truncate 32))
    (by sep_focus) ?_
  refine SepWPp.weaken_frame
    (pointsTo32_entails_memRegion (s6.sp + 0xbc#64) (u_3f0.extractLsb' 32 32))
    (by sep_focus) ?_
  have hsteps_6f : Steps (stageP1ProgPlaced ext) s6 sf :=
    hst67.trans (hst78.trans (hst89.trans (hst910.trans (hst1011.trans hst11f))))
  have htr_6f : sf.trace = s6.trace := by
    rw [htrf, htr11_10, htr10, htr9_8, htr8, htr7]
  have hvregs_f : calleeSavedVRegs sf = calleeSavedVRegs s0 := by
    rw [hvregsf, hvregs11_10, hvregs10, hvregs9_8, hvregs8, hvregs7, hvregs6]
  have hok := hOk evsProm sf hevsProm hsteps_6f hpcf hrunf hspf htr_6f hx8_f hx9_f hx10_f hx11_f
    hx19_f hx20_f hx22_f hx23_f hx24_f
    (hx25_f.trans hx25_11) hx26_f hx27_f
    (hx28_f.trans hx28_11) (hx29_f.trans hx29_11)
    hvregs_f hCodef
  exact p2_sepWPp_weaken_eq hok (by sep_focus)

theorem stageP2_over_sub6_tail_v1_kits_callees_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    (ext : String → Option (State → State))
    {ikit : IdentityStoreSpec A.repAlloc 0#64} (skit : IdentitySelfStoreSpec ikit)
    (hH : StageP2ClosureHooksPlaced A lim ext)
    (hskitVt : IdentitySelfVtablesPlacedOk ikit skit)
    (coroPtr : BitVec 64) (g : RecordGhost) (recG : SessionGhost)
    (sess : Session (List (BitVec 8)))
    (hPromoteOver : PromoteOverAtPlacedProp M A lim ext coroPtr g recG sess)
    (hDrop :
      subroutine_ok (stageP1ProgPlaced ext)
        (lsmpl.base 509)
        (withLsCodeLoaded lsmpl dropProcessPrekeyImplState1Spec)) :
    stageP2OverSub6TailV1AtPlacedProp A lim ext skit coroPtr g recG sess :=
  stageP2_over_sub6_tail_v1_kits_callees_withEnv_placed ext skit hH hskitVt
    coroPtr g recG sess hPromoteOver hDrop

theorem stageP2_over_sub6_tail_v1_kits_ext_placed_withEnv_ofEnv [LibsignalPlacement]
    {M : AllocCostModel} {P : Primitives} {A : RustCliAllocBudget M}
    {lim : BudgetLimits} {F : ShaCompress}
    {BobV1Env : AcceptKeysInput → DRKey → List AllocEvent → Prop}
    {AcceptErrEnv : AcceptKeysInput → List AllocEvent → Prop}
    {Env : SessionGhost → Session (List (BitVec 8)) → List AllocEvent → Prop}
    (ext : String → Option (State → State))
    {ikit : IdentityStoreSpec A.repAlloc 0#64} (skit : IdentitySelfStoreSpec ikit)
    (hH : StageP2ClosureHooksPlaced A lim ext)
    (hskitVt : IdentitySelfVtablesPlacedOk ikit skit)
    (hPure : StageP2PureCalleesPlaced4KOfEnv P A lim F BobV1Env AcceptErrEnv ext)
    (coroPtr : BitVec 64) (g : RecordGhost) (recG : SessionGhost)
    (sess : Session (List (BitVec 8)))
    (hPromoteOver : PromoteOverAtPlacedWithEnvProp M A lim Env ext coroPtr g recG sess) :
    stageP2OverSub6TailV1AtPlacedWithEnvProp A lim Env ext skit coroPtr g recG sess :=
  stageP2_over_sub6_tail_v1_kits_callees_withEnv_placed ext skit hH hskitVt
    coroPtr g recG sess hPromoteOver hPure.dropProcessPrekeyImplState1

theorem stageP2_over_sub6_tail_v1_kits_ext_placed_ofEnv [LibsignalPlacement]
    {M : AllocCostModel} {P : Primitives} {A : RustCliAllocBudget M}
    {lim : BudgetLimits} {F : ShaCompress}
    {BobV1Env : AcceptKeysInput → DRKey → List AllocEvent → Prop}
    {AcceptErrEnv : AcceptKeysInput → List AllocEvent → Prop}
    (ext : String → Option (State → State))
    {ikit : IdentityStoreSpec A.repAlloc 0#64} (skit : IdentitySelfStoreSpec ikit)
    (hH : StageP2ClosureHooksPlaced A lim ext)
    (hskitVt : IdentitySelfVtablesPlacedOk ikit skit)
    (hPure : StageP2PureCalleesPlaced4KOfEnv P A lim F BobV1Env AcceptErrEnv ext)
    (coroPtr : BitVec 64) (g : RecordGhost) (recG : SessionGhost)
    (sess : Session (List (BitVec 8)))
    (hPromoteOver : PromoteOverAtPlacedProp M A lim ext coroPtr g recG sess) :
    stageP2OverSub6TailV1AtPlacedProp A lim ext skit coroPtr g recG sess :=
  stageP2_over_sub6_tail_v1_kits_callees_placed ext skit hH hskitVt
    coroPtr g recG sess hPromoteOver hPure.dropProcessPrekeyImplState1

theorem stageP2_over_sub6_tail_v1_kits_ext_placed [LibsignalPlacement]
    {M : AllocCostModel} {P : Primitives} {A : RustCliAllocBudget M}
    {lim : BudgetLimits} {F : ShaCompress}
    {AcceptErrEnv : AcceptKeysInput → List AllocEvent → Prop}
    (ext : String → Option (State → State))
    {ikit : IdentityStoreSpec A.repAlloc 0#64} (skit : IdentitySelfStoreSpec ikit)
    (hH : StageP2ClosureHooksPlaced A lim ext)
    (hskitVt : IdentitySelfVtablesPlacedOk ikit skit)
    (hPure : StageP2PureCalleesPlaced4K P A lim F AcceptErrEnv ext)
    (coroPtr : BitVec 64) (g : RecordGhost) (recG : SessionGhost)
    (sess : Session (List (BitVec 8)))
    (hPromoteOver : PromoteOverAtPlacedProp M A lim ext coroPtr g recG sess) :
    stageP2OverSub6TailV1AtPlacedProp A lim ext skit coroPtr g recG sess :=
  stageP2_over_sub6_tail_v1_kits_ext_placed_ofEnv ext skit hH hskitVt hPure
    coroPtr g recG sess hPromoteOver

abbrev stageP2_over_sub6_tail_v1_kits_4k_placed [LibsignalPlacement] :=
  @stageP2_over_sub6_tail_v1_kits_ext_placed

theorem stageP2_over_sub6_tail_v1_kits_placed_ofEnv [LibsignalPlacement]
    {M : AllocCostModel} {P : Primitives} {A : RustCliAllocBudget M}
    {lim : BudgetLimits} {F : ShaCompress}
    {BobV1Env : AcceptKeysInput → DRKey → List AllocEvent → Prop}
    {AcceptErrEnv : AcceptKeysInput → List AllocEvent → Prop}
    (ext : String → Option (State → State))
    {ikit : IdentityStoreSpec A.repAlloc 0#64} (skit : IdentitySelfStoreSpec ikit)
    (hH : StageP2ClosureHooksPlaced A lim ext)
    (hskitVt : IdentitySelfVtablesPlacedOk ikit skit)
    (hPure : StageP2PureCalleesPlacedOfEnv P A lim F BobV1Env AcceptErrEnv ext)
    (coroPtr : BitVec 64) (g : RecordGhost) (recG : SessionGhost)
    (sess : Session (List (BitVec 8)))
    (hPromoteOver : PromoteOverAtPlacedProp M A lim ext coroPtr g recG sess) :
    stageP2OverSub6TailV1AtPlacedProp A lim ext skit coroPtr g recG sess :=
  stageP2_over_sub6_tail_v1_kits_callees_placed ext skit hH hskitVt
    coroPtr g recG sess hPromoteOver hPure.dropProcessPrekeyImplState1

theorem stageP2_over_sub6_tail_v1_kits_placed [LibsignalPlacement]
    {M : AllocCostModel} {P : Primitives} {A : RustCliAllocBudget M}
    {lim : BudgetLimits} {F : ShaCompress}
    {AcceptErrEnv : AcceptKeysInput → List AllocEvent → Prop}
    (ext : String → Option (State → State))
    {ikit : IdentityStoreSpec A.repAlloc 0#64} (skit : IdentitySelfStoreSpec ikit)
    (hH : StageP2ClosureHooksPlaced A lim ext)
    (hskitVt : IdentitySelfVtablesPlacedOk ikit skit)
    (hPure : StageP2PureCalleesPlaced P A lim F AcceptErrEnv ext)
    (coroPtr : BitVec 64) (g : RecordGhost) (recG : SessionGhost)
    (sess : Session (List (BitVec 8)))
    (hPromoteOver : PromoteOverAtPlacedProp M A lim ext coroPtr g recG sess) :
    stageP2OverSub6TailV1AtPlacedProp A lim ext skit coroPtr g recG sess :=
  stageP2_over_sub6_tail_v1_kits_placed_ofEnv ext skit hH hskitVt hPure
    coroPtr g recG sess hPromoteOver

end LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Over.StageP2Sub6AuxPlacedBudget
