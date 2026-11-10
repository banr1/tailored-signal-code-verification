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
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP2BridgePlacedBudget
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP2DefsBudget
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP2DefsPlacedBudget
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP2PurePlacedBudget
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP2Sub5DefsPlacedBudget
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP2Sub5V1PlacedBudget
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP2V1PlacedBudget
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Over.StageP2ArmsAPlacedBudget
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Over.StageP2ArmsBPlacedBudget
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Over.StageP2BridgesPlacedBudget
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Over.StageP2DefsPlacedBudget
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Over.StageP2Mid2PlacedBudget
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Over.StageP2Mid3PlacedBudget
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Over.StageP2PlacedBudget
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Over.StageP2Sub4PlacedBudget
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Over.StageP2Sub5PlacedBudget
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Over.StageP2Sub6AuxPlacedBudget
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Over.StageP2Sub6PlacedBudget
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Over.StageP2V1Placed
public import LibsignalBinary.Proofs.E2E.Pqxdh.ResponderCore.InitBobErrOwnedPlacedBudget
public import LibsignalBinary.Proofs.PublicApi.StoreKit.IdentitySelfStoreKitBudget
public import LibsignalBinary.Proofs.PublicApi.StoreKit.IdentityStoreKitBudget
public import LibsignalBinary.Proofs.PublicApi.StoreKit.KyberPreKeyStoreKitBudget
public import LibsignalBinary.Proofs.PublicApi.StoreKit.Over.ArchivePromoteBudget
public import LibsignalBinary.Proofs.PublicApi.StoreKit.PlacedBudget
public import LibsignalBinary.Proofs.PublicApi.StoreKit.PreKeyStoreKitBudget
public import LibsignalBinary.Proofs.PublicApi.StoreKit.SignedPreKeyStoreKitBudget
import Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic
import ProofLib.SepLogic.WPp
import LibsignalBinary.Proofs.Common.SharedHelpers
meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP2Arms2PlacedBudget
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP2ArmsPlacedBudget
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP2Mid3PlacedBudget
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP2Sub2
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP2Sub5AuxPlacedBudget
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP2V1
import LibsignalBinary.Proofs.SpqrV1.Kdf.HkdfToSliceExtract
import LibsignalBinary.Proofs.E2E.Pqxdh.Initiator.InitializeAliceStage1Common -- shake: keep

/-!
# Budget-Threaded Placed Stage P2 Over-Path Top-Level Specification

Defines bounded `SeqEnv` allocation envelopes for Over-path Stage P2 (`P2OverSub6EnvOf`,
`P2OverV1Arm4Env`, `P2OverV1Arm5EnvOfAcceptErr`, `P2OverV1Arm6EnvOfBob`, `P2OverV1OkEnvOfBobAndProm`)
and proves budget-threaded `[LibsignalPlacement]` Over-path Stage P2 theorems (`+0x0868 → +0x1778`
and error Arms 1–6), including `StageP2MemInv`- and `LibsignalFrozen`-guarded variants.
-/

@[expose] public section

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option maxRecDepth 200000

attribute [-arm64_norm]
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_sub_688_eq_hsp
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_add_neg688_eq_hsp
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_sub_96_eq_hsp_592
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_add_neg96_eq_hsp_592

namespace LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Over.StageP2V1PlacedBudget

open Arm64 Arm64.Process ProofLib SepProp
open CryptoGames.LibsignalSession (PublicKey ShaCompress)
open CryptoGames.LibsignalSessionApi (Session)
open CryptoVerification (LibsignalFrozen LibsignalPlacement lsmpl withLsCodeLoaded)
open CryptoVerification.LibsignalTripleRatchet (withLsCodeRoLoaded)
open CryptoVerification.RecordCodecs (
  IdentityKeyPair KyberPreKeyRecord PreKeyRecord SignedPreKeyRecord
)
open CryptoVerification.LibsignalTripleRatchetRepr (AddrGhost SessionGhost uuidTryParse)
open CryptoVerification.LibsignalTripleRatchet.FromRecordCallees (dropSessionStructureLocal2Stack)
open CryptoVerification.LibsignalPublicApiRepr (RecordGhost)
open CryptoVerification.LibsignalPublicApi.StoreKit (
  FsAt IdentitySelfStoreSpec IdentitySelfVtablesPlacedOk IdentityStoreSpec
  KyberPreKeyStoreSpec KyberPreKeyVtablesPlacedOk LibsignalCodeRoLoaded
  PreKeyStoreSpec PreKeyVtablesPlacedOk
  SignedPreKeyStoreSpec SignedPreKeyVtablesPlacedOk speErrAt speWordsAt
)
open CryptoVerification.E2E (toU8)
open CryptoVerification.E2E.Pqxdh.Initiator (
  AcceptKeysInput DRKey HandshakeHdr Primitives StructuralPrims WellSizedAcceptKeysInput
  bytesToBv8 encodeEC
)
open CryptoVerification.E2E.Pqxdh.Initiator.Model (acceptKeys)
open CryptoVerification.E2E.Pqxdh.WireEntries (DistinctSid)
open CryptoVerification.E2E.Pqxdh.ResponderStore (clampBv8List clampBv8List_length)
open CryptoVerification.E2E.Pqxdh.ResponderCore (bytesToBv8_toU8)
open CryptoVerification.E2E.Pqxdh.ResponderClosure (ClosureCalleeSaved)
open CryptoVerification.E2E.Pqxdh.ResponderClosure.P3P4 (mkBobSenderChainGhost)
open CryptoVerification.SpqrV1.Top.InitialState (initialStateValue)
open CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Kits (
  OpkOkWitness StageP2MemInv hdrOpkIdBv? hdr_opkId?_isSome_eq_opkOkSkBytes?
  mkBobGhostV1 mkP2AcceptKeysInput mkP2AcceptKeysInput_pqspkBSk mkP2AcceptKeysInput_spkBSk
  opkOkEvs opkOkKeyBytes opkOkRel opkOkSkBytes?_eq_of_some opkOkUpdate
  opkOptTag32 opkOptTag8_eq_opkPresentTag
  p2BobInitSessionV1 p2BobSessMid280V1 p2BobSessMid280V1_length p2BobSpqrParams p2Sub1To4Frame
  p2_bobStack_le_v1CallStack p2_envOk_id p2_fsAt_step_kp p2_fsAt_step_regId
  p2_mono_pre p2_sepWPp_weaken_eq p2_sub56_le_stageP2 p2_toU8_bytesToBv8
  pqxdhAcceptErrPayloadAt
  stageP1EntryPlaced stageP1ProgPlaced stageP2CallStack stageP2EnvOk stageP2Quiet
  stageP2Sub56Stack wellSized_mkP2AcceptKeysInput
)
open CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Over (
  p2_over_baseCall_le_callStack p2_over_baseV1Call_le_v1CallStack
  p2_over_bobExt_le_overPure p2_over_callStack_le_v1CallStack
  p2_over_dropSS3_le_overPure p2_over_pure_le_callStack p2_over_pure_le_v1CallStack
  stageP2OverCallStack stageP2OverCallStack4K stageP2OverCallStack4K_eq
  stageP2OverPureAndErrStack
  stageP2OverV1CallStack stageP2OverV1CallStack4K stageP2OverV1CallStack4K_eq
)
open LibsignalBinary.Heap (
  AllocCostModel AllocEvent BudgetLimits FitsEnv FreeOnlyEvs RustCliAllocBudget SeqEnv
  rustDeallocEvents
)
open LibsignalBinary.Proofs.PublicApi.StoreKit.PreKeyStoreKitBudget (
  BoxAllocEnv PreKeyStoreBudgetEnv
)
open LibsignalBinary.Proofs.PublicApi.StoreKit.SignedPreKeyStoreKitBudget (
  SignedPreKeyStoreBudgetEnv
)
open LibsignalBinary.Proofs.PublicApi.StoreKit.KyberPreKeyStoreKitBudget (
  KyberPreKeyStoreBudgetEnv
)
open LibsignalBinary.Proofs.PublicApi.StoreKit.IdentitySelfStoreKitBudget (
  IdentitySelfStoreBudgetEnv
)
open LibsignalBinary.Proofs.PublicApi.StoreKit.PlacedBudget (
  IdentitySelfStoreKitPlacedOkI KyberPreKeyStoreKitPlacedOk PreKeyStoreKitPlacedOk
  SignedPreKeyStoreKitPlacedOk
)
open LibsignalBinary.Proofs.E2E.Pqxdh.ResponderCore.InitBobErrOwnedPlacedBudget (
  initializeBobSessionErrOwnedFrozenPlacedSpec initializeBobSessionErrOwnedPlacedSpec
)
open LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP2DefsBudget (
  isSameAccountDistinctAtSpec
)
open LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP2DefsPlacedBudget (
  InitializeBobV1Env
  InitializeBobV1FrozenOkAtPlaced InitializeBobV1FrozenOkAtPlacedOfEnv
  InitializeBobV1FrozenOkPlaced InitializeBobV1FrozenOkPlaced4K
  InitializeBobV1FrozenOkPlaced4KOfEnv InitializeBobV1FrozenOkPlacedOfEnv
  InitializeBobV1MemInvOkAtPlaced InitializeBobV1MemInvOkAtPlacedOfEnv
  InitializeBobV1MemInvOkPlaced InitializeBobV1MemInvOkPlaced4K
  InitializeBobV1MemInvOkPlaced4KOfEnv InitializeBobV1MemInvOkPlacedOfEnv
  InitializeBobV1OkAtPlacedOfEnv StageP2BaseCalleesPlaced4K StageP2ClosureHooksPlaced
  StageP2PureCalleesPlaced StageP2PureCalleesPlaced4K StageP2PureCalleesPlaced4KOfEnv
  StageP2PureCalleesPlacedOfEnv initializeBobSessionErr4KInnerPlacedSpec
  initializeBobSessionErr4KPlacedSpec initializeBobSessionErrOwned4KInnerPlacedSpec
  initializeBobSessionErrOwned4KPlacedSpec initializeBobSessionErrOwnedMemInv4KPlacedSpec
  withBobMemInv
)
open LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP2PurePlacedBudget (
  InitializeBobV1OptFieldsEnv p2_errOwned_frozen_to_defs4K_placed
  p2_initBobV1FrozenPlacedOfEnv_to_4K
)
open LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP2Sub1PlacedBudget (
  boxAllocEnv_iff_eq boxAllocEvents p2Sub1Events
)
open LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP2Sub5DefsPlacedBudget (
  initBobErrOwnedAt_eq_kits
  isSameAccountDistinctSpecExt_to_at_placed
  isSameAccountDistinctSpec_to_at_placed
  of_responderCore_errOwned_placed
  p2_bobErr4K_le_bobExt
  p2_isSameAccountExt_le_bobExt
  p2_isSameAccount_le_bobV1
  p2_stageP2bStack_le_bobV1
)
open LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP2Sub5DefsPlacedBudget.Sub5Placed (
  initializeBobSessionErrOwnedAtInnerPlacedSpec
  initializeBobSessionErrOwnedAtPlacedSpec
  initializeBobSessionErrOwnedMemInvAtPlacedSpec
  of_stageP2Defs_errOwned4K_placed
)
open LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP2Sub5AuxPlacedBudget (
  initializeBobSessionV1StackExtPlaced initializeBobSessionV1StackPlaced
)
open LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP2Sub5V1PlacedBudget (
  stageP2_sub5_v1_kits_at_placed_ofEnv stageP2_sub5_v1_kits_memInv_at_placed_ofEnv
)
open LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP2BridgePlacedBudget (
  p2ErrFrameAtPlaced
)
open LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP2ArmsPlacedBudget (
  p2_v1_arm1_entails_placed p2_v1_arm2_entails_placed p2_v1_arm3_entails_placed
)
open LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP2Arms2PlacedBudget (
  p2Sub6FramePlaced
)
open LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP2V1PlacedBudget (
  P2Sub6Env P2V1Arm4Env P2V1Arm5EnvOfAcceptErr P2V1Arm6EnvOfBob p2_arm5_err_payload_pull_placed
)
open LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Over.StageP2DefsPlacedBudget (
  PromoteMatchingMissAtPlacedProp PromoteOverAtPlacedWithEnvProp PromoteOverEnv
)
open LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Over.StageP2ArmsAPlacedBudget (
  p2OverSub5FramePlaced p2_over_v1_arm4_hooks_placed_ok p2_over_v1_arm5_hooks_placed_ok
)
open LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Over.StageP2ArmsBPlacedBudget (
  p2_over_v1_arm6_hooks_placed_ok p2_over_v1_ok_entails_placed
)
open LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Over.StageP2BridgesPlacedBudget (
  p2_over_entry_to_sub1To4_placed p2_over_sub4_to_sub5_placed p2_over_sub5_to_sub6_placed
)
open LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Over.StageP2Mid2PlacedBudget (
  P2OverSub1To3Arm1Env P2OverSub1To3Arm2Env
)
open LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Over.StageP2Mid3PlacedBudget (
  P2OverSub1To4Arm3Env P2OverSub1To4Env P2OverSub1To4OkEnv
  stageP2_over_sub1_to_4_kits_ext_placed_ofEnv
)
open LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Over.StageP2Sub4PlacedBudget (
  p2OverOkPostAtPlaced
)
open LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Over.StageP2Sub5PlacedBudget (
  stageP2OverPreAtPlaced
)
open LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Over.StageP2Sub6AuxPlacedBudget (
  P2OverSub6TailEnvOf fitsPromote_of_fitsTailEnv p2OverSub6TailEnvOf_intro p2OverSub6TailEvents
)
open LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Over.StageP2Sub6PlacedBudget (
  stageP2_over_sub6_v1_kits_ext_placed_withEnv_ofEnv
)

/-! ## Bounded `SeqEnv` Envelopes (`+0x0868 → +0x1778` and Arms 1–6) -/

/-- Bounded sequential envelope for Over-path Substage P2.6 covering `regIdShim`, `regIdPollEnv`,
and either Arm 6 teardown (`FreeOnlyEvs`) or the `.ok` `promote_state` tail (`PromTailForSess`). -/
def P2OverSub6EnvOf (regIdBoxSize : Nat)
    (regIdPollEnv PromTailForSess : List AllocEvent → Prop) : List AllocEvent → Prop :=
  SeqEnv (BoxAllocEnv regIdBoxSize)
    (SeqEnv regIdPollEnv (fun evs => FreeOnlyEvs evs ∨ PromTailForSess evs))

example : P2OverSub6EnvOf 64 (· = []) (· = []) (boxAllocEvents 64) :=
  Or.inl ((boxAllocEnv_iff_eq 64 _).mpr rfl)

/-- Over-path Arm 4 (`get_identity_key_pair` error) event envelope across Substages P2.1–P2.5. -/
abbrev P2OverV1Arm4Env := P2V1Arm4Env

/-- Over-path Arm 5 (`initialize_bob_session` rejection) event envelope across Substages P2.1–P2.5. -/
abbrev P2OverV1Arm5EnvOfAcceptErr := P2V1Arm5EnvOfAcceptErr

/-- Over-path Arm 6 (`get_local_registration_id` error) event envelope across Substages P2.1–P2.6. -/
abbrev P2OverV1Arm6EnvOfBob := P2V1Arm6EnvOfBob

/-- Over-path normal `+0x1778` exit event envelope across Substages P2.1–P2.6 chaining `BobForInp`
and `PromTailForSess`. -/
def P2OverV1OkEnvOfBobAndProm (spkBoxSize : Nat) (spkPollEnv : List AllocEvent → Prop)
    (kpkBoxSize : Nat) (kpkPollEnv : List AllocEvent → Prop)
    (pkBoxSize : Nat) (pkPollEnv : BitVec 32 → List AllocEvent → Prop)
    (kpBoxSize : Nat) (opkId? : Option (BitVec 32))
    (kpPollEnv BobForInp : List AllocEvent → Prop)
    (regIdBoxSize : Nat) (regIdPollEnv PromTailForSess : List AllocEvent → Prop) :
    List AllocEvent → Prop :=
  SeqEnv
    (P2OverSub1To4OkEnv spkBoxSize spkPollEnv kpkBoxSize kpkPollEnv pkBoxSize pkPollEnv
      kpBoxSize opkId?)
    (SeqEnv kpPollEnv
      (SeqEnv FreeOnlyEvs
        (SeqEnv BobForInp
          (SeqEnv (BoxAllocEnv regIdBoxSize)
            (SeqEnv regIdPollEnv PromTailForSess)))))

example : P2OverV1OkEnvOfBobAndProm 64 (· = []) 64 (· = []) 64 (fun _ => (· = [])) 64 none
    (· = []) (· = []) 64 (· = []) (· = []) (p2Sub1Events 64) :=
  Or.inl (Or.inl (Or.inl rfl))

/-! ## Budget-Threaded Placed Over-Path Stage P2 -/

/-- Budget-threaded continuation telescope `Prop` for placed Over-path Stage P2, parameterized by
`BobV1Env`, `AcceptErrEnv`, and `PromEnv`. -/
abbrev stageP2OverV1KitsAtPlacedOfEnvProp [LibsignalPlacement] {M : AllocCostModel}
    (P : Primitives) (A : RustCliAllocBudget M) (lim : BudgetLimits) (F : ShaCompress)
    (BobV1Env : AcceptKeysInput → DRKey → List AllocEvent → Prop)
    (AcceptErrEnv : AcceptKeysInput → List AllocEvent → Prop)
    (PromEnv : SessionGhost → Session (List (BitVec 8)) → List AllocEvent → Prop)
    (ext : String → Option (State → State))
    {ikit : IdentityStoreSpec A.repAlloc 0#64}
    (skit : IdentitySelfStoreSpec ikit) (senv : IdentitySelfStoreBudgetEnv skit)
    (spkKit : SignedPreKeyStoreSpec A.repAlloc 0#64) (spkEnv : SignedPreKeyStoreBudgetEnv spkKit)
    (kpkKit : KyberPreKeyStoreSpec A.repAlloc 0#64) (kpkEnv : KyberPreKeyStoreBudgetEnv kpkKit)
    (pkKit : PreKeyStoreSpec A.repAlloc 0#64) (pkEnv : PreKeyStoreBudgetEnv pkKit)
    (stk : Nat) : Prop :=
  ∀ {st : M.σ} {Qp : State → SepProp → Prop}
    (s0 s : State) (Frame : SepProp) (Q : State → SepProp → Prop)
    (sp fp coroPtr ctxPtr outPtr msgPtr ctBufPtr remoteAddrPtr localAddrPtr
     idStorePtr preKeyStorePtr spkStorePtr kyberStorePtr
     v_330 v_388 u_488 u_80 u_88 u_90 u_a8 u_b8 u_d0 : BitVec 64)
    (hdr : HandshakeHdr) (ikBSk ikBPk : SignalPqxdh.Bytes)
    (msgVerByte b_2c0 b_390 b_4b0 b_4f1 b_4f2 : BitVec 8)
    (opkIdWord kyberPreKeyId remoteRegId signedPreKeyId : BitVec 32)
    (stSpk : spkKit.SpkState) (stKpk : kpkKit.KpkState)
    (stPk : pkKit.PkState) (stId : ikit.IdState)
    (gMe gPeer : AddrGhost)
    (g : RecordGhost) (recG : SessionGhost) (sess : Session (List (BitVec 8))),
    PromoteMatchingMissAtPlacedProp A.repAlloc ext coroPtr g recG sess 4#8
      (5#8 :: bytesToBv8 hdr.ekAPk) →
    PromoteOverAtPlacedWithEnvProp M A lim PromEnv ext coroPtr g recG sess →
    FitsEnv M lim st
      (P2OverSub1To4Env spkKit.getBoxSize (spkEnv.getPollEnv stSpk signedPreKeyId)
        kpkKit.getBoxSize (kpkEnv.getPollEnv stKpk kyberPreKeyId)
        pkKit.getBoxSize (pkEnv.getPollEnv stPk) skit.kpBoxSize (hdrOpkIdBv? hdr)) →
    (∀ evs14 : List AllocEvent,
      P2OverSub1To4OkEnv spkKit.getBoxSize (spkEnv.getPollEnv stSpk signedPreKeyId)
        kpkKit.getBoxSize (kpkEnv.getPollEnv stKpk kyberPreKeyId)
        pkKit.getBoxSize (pkEnv.getPollEnv stPk) skit.kpBoxSize (hdrOpkIdBv? hdr) evs14 →
      FitsEnv M lim (M.stepEvents evs14 st) (SeqEnv (senv.kpPollEnv stId) FreeOnlyEvs)) →
    (∀ (spkRec : SignedPreKeyRecord) (spkPubBytes spkPrivBytes : List (BitVec 8))
        (kpkRec : KyberPreKeyRecord) (kyberPubBytes kyberPrivBytes : List (BitVec 8))
        (wOpk : OpkOkWitness (hdrOpkIdBv? hdr)) (opkPkBytes opkSkBytes : List (BitVec 8))
        (kp : IdentityKeyPair) (drKey : DRKey) (evs14 evsKp : List AllocEvent),
      spkKit.getRel stSpk signedPreKeyId (.ok spkRec) → spkKit.RecOk spkRec →
      spkPubBytes.length = 32 → spkPrivBytes.length = 32 →
      spkRec.signedPreKey.publicKey = 5#8 :: spkPubBytes →
      spkRec.signedPreKey.privateKey = spkPrivBytes →
      kpkKit.getRel stKpk kyberPreKeyId (.ok kpkRec) → kpkKit.RecOk kpkRec →
      kyberPubBytes.length = 1568 → kyberPrivBytes.length = 3168 →
      kpkRec.signedPreKey.publicKey = 8#8 :: kyberPubBytes →
      kpkRec.signedPreKey.privateKey = 8#8 :: kyberPrivBytes →
      opkOkRel pkKit stPk (hdrOpkIdBv? hdr) wOpk →
      opkPkBytes.length = 32 → opkSkBytes.length = 32 →
      opkOkKeyBytes (hdrOpkIdBv? hdr) wOpk opkPkBytes opkSkBytes →
      skit.kpRel stId (.ok kp) →
      acceptKeys P
        (mkP2AcceptKeysInput hdr ikBSk ikBPk spkPubBytes spkPrivBytes
          kyberPubBytes kyberPrivBytes opkSkBytes) = some drKey →
      P2OverSub1To4OkEnv spkKit.getBoxSize (spkEnv.getPollEnv stSpk signedPreKeyId)
        kpkKit.getBoxSize (kpkEnv.getPollEnv stKpk kyberPreKeyId)
        pkKit.getBoxSize (pkEnv.getPollEnv stPk) skit.kpBoxSize (hdrOpkIdBv? hdr) evs14 →
      senv.kpPollEnv stId evsKp →
      FitsEnv M lim
        (M.stepEvents (evs14 ++ evsKp ++ rustDeallocEvents skit.kpBoxSize 8) st)
        (SeqEnv
          (BobV1Env
            (mkP2AcceptKeysInput hdr ikBSk ikBPk spkPubBytes spkPrivBytes
              kyberPubBytes kyberPrivBytes opkSkBytes) drKey)
          (P2OverSub6EnvOf skit.regIdBoxSize (senv.regIdPollEnv stId)
            (P2OverSub6TailEnvOf PromEnv skit.regIdBoxSize recG sess)))) →
    (∀ (spkRec : SignedPreKeyRecord) (spkPubBytes spkPrivBytes : List (BitVec 8))
        (kpkRec : KyberPreKeyRecord) (kyberPubBytes kyberPrivBytes : List (BitVec 8))
        (wOpk : OpkOkWitness (hdrOpkIdBv? hdr)) (opkPkBytes opkSkBytes : List (BitVec 8))
        (kp : IdentityKeyPair) (evs14 evsKp : List AllocEvent),
      spkKit.getRel stSpk signedPreKeyId (.ok spkRec) → spkKit.RecOk spkRec →
      spkPubBytes.length = 32 → spkPrivBytes.length = 32 →
      spkRec.signedPreKey.publicKey = 5#8 :: spkPubBytes →
      spkRec.signedPreKey.privateKey = spkPrivBytes →
      kpkKit.getRel stKpk kyberPreKeyId (.ok kpkRec) → kpkKit.RecOk kpkRec →
      kyberPubBytes.length = 1568 → kyberPrivBytes.length = 3168 →
      kpkRec.signedPreKey.publicKey = 8#8 :: kyberPubBytes →
      kpkRec.signedPreKey.privateKey = 8#8 :: kyberPrivBytes →
      opkOkRel pkKit stPk (hdrOpkIdBv? hdr) wOpk →
      opkPkBytes.length = 32 → opkSkBytes.length = 32 →
      opkOkKeyBytes (hdrOpkIdBv? hdr) wOpk opkPkBytes opkSkBytes →
      skit.kpRel stId (.ok kp) →
      acceptKeys P
        (mkP2AcceptKeysInput hdr ikBSk ikBPk spkPubBytes spkPrivBytes
          kyberPubBytes kyberPrivBytes opkSkBytes) = none →
      P2OverSub1To4OkEnv spkKit.getBoxSize (spkEnv.getPollEnv stSpk signedPreKeyId)
        kpkKit.getBoxSize (kpkEnv.getPollEnv stKpk kyberPreKeyId)
        pkKit.getBoxSize (pkEnv.getPollEnv stPk) skit.kpBoxSize (hdrOpkIdBv? hdr) evs14 →
      senv.kpPollEnv stId evsKp →
      FitsEnv M lim
        (M.stepEvents (evs14 ++ evsKp ++ rustDeallocEvents skit.kpBoxSize 8) st)
        (SeqEnv
          (AcceptErrEnv
            (mkP2AcceptKeysInput hdr ikBSk ikBPk spkPubBytes spkPrivBytes
              kyberPubBytes kyberPrivBytes opkSkBytes))
          FreeOnlyEvs)) →
    ctBufPtr ≠ 0#64 →
    sp - 576#64 ≠ 0#64 →
    stk ≤ sp.toNat →
    (hikBSk_len : ikBSk.length = 32) → (hikBPk_len : ikBPk.length = 32) →
    (hikAPk_len : hdr.ikAPk.length = 32) → (hekAPk_len : hdr.ekAPk.length = 32) →
    (hkemCt_len : hdr.kemCt.length = 1568) →
    LibsignalCodeRoLoaded lsmpl s.mem →
    FsAt (stageP2EnvOk spkKit kpkKit pkKit ikit)
      (stageP2Quiet spkKit kpkKit pkKit skit) (stageP1ProgPlaced ext) s →
    spkKit.idOk signedPreKeyId →
    (∀ r : SignedPreKeyRecord, spkKit.getRel stSpk signedPreKeyId (.ok r) →
      spkKit.RecOk r →
      ∃ spkPubBytes spkPrivBytes : List (BitVec 8),
        spkPubBytes.length = 32 ∧ spkPrivBytes.length = 32 ∧
        r.signedPreKey.publicKey = 5#8 :: spkPubBytes ∧ r.signedPreKey.privateKey = spkPrivBytes) →
    kpkKit.getIdOk kyberPreKeyId →
    (∀ r : KyberPreKeyRecord, kpkKit.getRel stKpk kyberPreKeyId (.ok r) →
      kpkKit.RecOk r →
      ∃ kyberPubBytes kyberPrivBytes : List (BitVec 8),
        kyberPubBytes.length = 1568 ∧ kyberPrivBytes.length = 3168 ∧
        r.signedPreKey.publicKey = 8#8 :: kyberPubBytes ∧
        r.signedPreKey.privateKey = 8#8 :: kyberPrivBytes) →
    (∀ id : BitVec 32, hdrOpkIdBv? hdr = some id → opkIdWord = id) →
    (∀ id : BitVec 32, hdrOpkIdBv? hdr = some id → pkKit.getIdOk id) →
    (∀ (id : BitVec 32) (r : PreKeyRecord), hdrOpkIdBv? hdr = some id →
      pkKit.getRel stPk id (.ok r) → pkKit.RecOk r →
      ∃ opkPubBytes opkPrivBytes : List (BitVec 8),
        opkPubBytes.length = 32 ∧ opkPrivBytes.length = 32 ∧
        r.preKey.publicKey = 5#8 :: opkPubBytes ∧ r.preKey.privateKey = opkPrivBytes) →
    (∀ kp : IdentityKeyPair, skit.kpRel stId (.ok kp) →
      kp.privateKey.bytes.toList = bytesToBv8 ikBSk) →
    (∀ kp : IdentityKeyPair, skit.kpRel stId (.ok kp) →
      kp.identityKey.publicKey.bytes.toList = bytesToBv8 ikBPk) →
    (bytesToBv8 ikBPk ≠ bytesToBv8 hdr.ikAPk ∨
      DistinctSid uuidTryParse gMe.name.bytes gPeer.name.bytes) →
    s.pc = stageP1EntryPlaced + 0x868#64 →
    s.status = .Running → s.sp = sp →
    (sp &&& 15#64 == 0#64) = true →
    s0.trace <+: s.trace →
    calleeSavedVRegs s = calleeSavedVRegs s0 →
    s.readReg64 .x8 = kyberStorePtr → s.readReg64 .x9 = msgPtr →
    s.readReg64 .x10 = kpkKit.kpk_vt → s.readReg64 .x11 = preKeyStorePtr →
    s.readReg64 .x12 = remoteAddrPtr → s.readReg64 .x13 = pkKit.pk_vt →
    s.readReg64 .x14 = localAddrPtr → s.readReg64 .x15 = idStorePtr →
    s.readReg64 .x16 = ikit.id_vt → s.readReg64 .x19 = coroPtr →
    s.readReg64 .x22 = spkStorePtr → s.readReg64 .x23 = coroPtr + 0xe0#64 →
    s.readReg64 .x24 = spkKit.spk_vt → s.readReg64 .x29 = fp →
    (∀ (e : spkKit.GetErr) (sf : State) (P_f : SepProp) (evs : List AllocEvent),
      spkKit.getRel stSpk signedPreKeyId (.error e) →
      P2OverSub1To3Arm1Env spkKit.getBoxSize (spkEnv.getPollEnv stSpk signedPreKeyId) evs →
      sf.pc = s0.readReg64 .x30 → sf.status = .Running →
      sf.trace = s.trace ++ spkKit.getEvs signedPreKeyId (.error e) →
      sf.sp = sp + 0xcd0#64 → ClosureCalleeSaved s0 sf →
      calleeSavedVRegs sf = calleeSavedVRegs s0 → LibsignalCodeRoLoaded lsmpl sf.mem →
      (P_f ⊢
        speErrAt spkKit.getErr outPtr e ∗
        spkKit.storeAt spkStorePtr (spkKit.getUpdate stSpk signedPreKeyId (.error e)) ∗
        kpkKit.storeAt kyberStorePtr stKpk ∗
        pkKit.storeAt preKeyStorePtr stPk ∗
        ikit.identityAt idStorePtr stId ∗
        p2ErrFrameAtPlaced A lim (M.stepEvents evs st) s0 sf
          sp fp coroPtr msgPtr ctBufPtr remoteAddrPtr localAddrPtr
          idStorePtr ikit.id_vt preKeyStorePtr pkKit.pk_vt kyberStorePtr kpkKit.kpk_vt
          v_330 v_388 hdr msgVerByte opkIdWord kyberPreKeyId remoteRegId signedPreKeyId
          gMe gPeer stk Frame) →
      Q sf P_f) →
    (∀ (spkRec : SignedPreKeyRecord) (e : kpkKit.GetErr) (sf : State) (P_f : SepProp)
        (evs : List AllocEvent),
      spkKit.getRel stSpk signedPreKeyId (.ok spkRec) → spkKit.RecOk spkRec →
      kpkKit.getRel stKpk kyberPreKeyId (.error e) →
      P2OverSub1To3Arm2Env spkKit.getBoxSize (spkEnv.getPollEnv stSpk signedPreKeyId)
        kpkKit.getBoxSize (kpkEnv.getPollEnv stKpk kyberPreKeyId) evs →
      sf.pc = s0.readReg64 .x30 → sf.status = .Running →
      sf.trace = s.trace ++ spkKit.getEvs signedPreKeyId (.ok spkRec) ++
        kpkKit.getEvs kyberPreKeyId (.error e) →
      sf.sp = sp + 0xcd0#64 → ClosureCalleeSaved s0 sf →
      calleeSavedVRegs sf = calleeSavedVRegs s0 → LibsignalCodeRoLoaded lsmpl sf.mem →
      (P_f ⊢
        speErrAt kpkKit.getErr outPtr e ∗
        spkKit.storeAt spkStorePtr (spkKit.getUpdate stSpk signedPreKeyId (.ok spkRec)) ∗
        kpkKit.storeAt kyberStorePtr (kpkKit.getUpdate stKpk kyberPreKeyId (.error e)) ∗
        pkKit.storeAt preKeyStorePtr stPk ∗
        ikit.identityAt idStorePtr stId ∗
        p2ErrFrameAtPlaced A lim (M.stepEvents evs st) s0 sf
          sp fp coroPtr msgPtr ctBufPtr remoteAddrPtr localAddrPtr
          idStorePtr ikit.id_vt preKeyStorePtr pkKit.pk_vt kyberStorePtr kpkKit.kpk_vt
          v_330 v_388 hdr msgVerByte opkIdWord kyberPreKeyId remoteRegId signedPreKeyId
          gMe gPeer stk Frame) →
      Q sf P_f) →
    (∀ (spkRec : SignedPreKeyRecord) (kpkRec : KyberPreKeyRecord)
        (opkId : BitVec 32) (e : pkKit.GetErr) (sf : State) (P_f : SepProp)
        (evs : List AllocEvent),
      spkKit.getRel stSpk signedPreKeyId (.ok spkRec) → spkKit.RecOk spkRec →
      kpkKit.getRel stKpk kyberPreKeyId (.ok kpkRec) → kpkKit.RecOk kpkRec →
      hdrOpkIdBv? hdr = some opkId → pkKit.getRel stPk opkId (.error e) →
      P2OverSub1To4Arm3Env spkKit.getBoxSize (spkEnv.getPollEnv stSpk signedPreKeyId)
        kpkKit.getBoxSize (kpkEnv.getPollEnv stKpk kyberPreKeyId)
        pkKit.getBoxSize (pkEnv.getPollEnv stPk) (hdrOpkIdBv? hdr) evs →
      sf.pc = s0.readReg64 .x30 → sf.status = .Running →
      sf.trace = s.trace ++ spkKit.getEvs signedPreKeyId (.ok spkRec) ++
        kpkKit.getEvs kyberPreKeyId (.ok kpkRec) ++ pkKit.getEvs opkId (.error e) →
      sf.sp = sp + 0xcd0#64 → ClosureCalleeSaved s0 sf →
      calleeSavedVRegs sf = calleeSavedVRegs s0 → LibsignalCodeRoLoaded lsmpl sf.mem →
      (P_f ⊢
        speErrAt pkKit.getErr outPtr e ∗
        spkKit.storeAt spkStorePtr (spkKit.getUpdate stSpk signedPreKeyId (.ok spkRec)) ∗
        kpkKit.storeAt kyberStorePtr (kpkKit.getUpdate stKpk kyberPreKeyId (.ok kpkRec)) ∗
        pkKit.storeAt preKeyStorePtr (pkKit.getUpdate stPk opkId (.error e)) ∗
        ikit.identityAt idStorePtr stId ∗
        p2ErrFrameAtPlaced A lim (M.stepEvents evs st) s0 sf
          sp fp coroPtr msgPtr ctBufPtr remoteAddrPtr localAddrPtr
          idStorePtr ikit.id_vt preKeyStorePtr pkKit.pk_vt kyberStorePtr kpkKit.kpk_vt
          v_330 v_388 hdr msgVerByte opkIdWord kyberPreKeyId remoteRegId signedPreKeyId
          gMe gPeer stk Frame) →
      Q sf P_f) →
    (∀ (spkRec : SignedPreKeyRecord) (kpkRec : KyberPreKeyRecord)
        (wOpk : OpkOkWitness (hdrOpkIdBv? hdr)) (e : skit.KpErr) (sf : State) (P_f : SepProp)
        (evs : List AllocEvent),
      spkKit.getRel stSpk signedPreKeyId (.ok spkRec) → spkKit.RecOk spkRec →
      kpkKit.getRel stKpk kyberPreKeyId (.ok kpkRec) → kpkKit.RecOk kpkRec →
      opkOkRel pkKit stPk (hdrOpkIdBv? hdr) wOpk →
      skit.kpRel stId (.error e) →
      P2OverV1Arm4Env spkKit.getBoxSize (spkEnv.getPollEnv stSpk signedPreKeyId)
        kpkKit.getBoxSize (kpkEnv.getPollEnv stKpk kyberPreKeyId)
        pkKit.getBoxSize (pkEnv.getPollEnv stPk) skit.kpBoxSize (hdrOpkIdBv? hdr)
        (senv.kpPollEnv stId) evs →
      sf.pc = s0.readReg64 .x30 → sf.status = .Running →
      sf.trace = s.trace ++ spkKit.getEvs signedPreKeyId (.ok spkRec) ++
        kpkKit.getEvs kyberPreKeyId (.ok kpkRec) ++ opkOkEvs pkKit (hdrOpkIdBv? hdr) wOpk ++
        skit.kpEvs (.error e) →
      sf.sp = sp + 0xcd0#64 → ClosureCalleeSaved s0 sf →
      calleeSavedVRegs sf = calleeSavedVRegs s0 → LibsignalCodeRoLoaded lsmpl sf.mem →
      (P_f ⊢
        speErrAt skit.kpErr outPtr e ∗
        spkKit.storeAt spkStorePtr (spkKit.getUpdate stSpk signedPreKeyId (.ok spkRec)) ∗
        kpkKit.storeAt kyberStorePtr (kpkKit.getUpdate stKpk kyberPreKeyId (.ok kpkRec)) ∗
        pkKit.storeAt preKeyStorePtr (opkOkUpdate pkKit stPk (hdrOpkIdBv? hdr) wOpk) ∗
        ikit.identityAt idStorePtr stId ∗
        p2ErrFrameAtPlaced A lim (M.stepEvents evs st) s0 sf
          sp fp coroPtr msgPtr ctBufPtr remoteAddrPtr localAddrPtr
          idStorePtr ikit.id_vt preKeyStorePtr pkKit.pk_vt kyberStorePtr kpkKit.kpk_vt
          v_330 v_388 hdr msgVerByte opkIdWord kyberPreKeyId remoteRegId signedPreKeyId
          gMe gPeer stk Frame) →
      Q sf P_f) →
    (∀ (spkRec : SignedPreKeyRecord) (spkPubBytes spkPrivBytes : List (BitVec 8))
        (kpkRec : KyberPreKeyRecord) (kyberPubBytes kyberPrivBytes : List (BitVec 8))
        (wOpk : OpkOkWitness (hdrOpkIdBv? hdr)) (opkPkBytes opkSkBytes : List (BitVec 8))
        (kp : IdentityKeyPair) (errTag w2 w3 w4 w5 w6 : BitVec 64)
        (sf : State) (P_f : SepProp) (evs : List AllocEvent),
      spkKit.getRel stSpk signedPreKeyId (.ok spkRec) → spkKit.RecOk spkRec →
      spkPubBytes.length = 32 → spkPrivBytes.length = 32 →
      spkRec.signedPreKey.publicKey = 5#8 :: spkPubBytes →
      spkRec.signedPreKey.privateKey = spkPrivBytes →
      kpkKit.getRel stKpk kyberPreKeyId (.ok kpkRec) → kpkKit.RecOk kpkRec →
      kyberPubBytes.length = 1568 → kyberPrivBytes.length = 3168 →
      kpkRec.signedPreKey.publicKey = 8#8 :: kyberPubBytes →
      kpkRec.signedPreKey.privateKey = 8#8 :: kyberPrivBytes →
      opkOkRel pkKit stPk (hdrOpkIdBv? hdr) wOpk →
      opkPkBytes.length = 32 → opkSkBytes.length = 32 →
      opkOkKeyBytes (hdrOpkIdBv? hdr) wOpk opkPkBytes opkSkBytes →
      skit.kpRel stId (.ok kp) →
      acceptKeys P
        (mkP2AcceptKeysInput hdr ikBSk ikBPk spkPubBytes spkPrivBytes
          kyberPubBytes kyberPrivBytes opkSkBytes) = none →
      P2OverV1Arm5EnvOfAcceptErr spkKit.getBoxSize (spkEnv.getPollEnv stSpk signedPreKeyId)
        kpkKit.getBoxSize (kpkEnv.getPollEnv stKpk kyberPreKeyId)
        pkKit.getBoxSize (pkEnv.getPollEnv stPk) skit.kpBoxSize (hdrOpkIdBv? hdr)
        (senv.kpPollEnv stId)
        (AcceptErrEnv
          (mkP2AcceptKeysInput hdr ikBSk ikBPk spkPubBytes spkPrivBytes
            kyberPubBytes kyberPrivBytes opkSkBytes))
        evs →
      errTag ≠ 0xfffffffffffffffe#64 → errTag ≠ 0xfffffffffffffffd#64 →
      sf.pc = s0.readReg64 .x30 → sf.status = .Running →
      sf.trace = s.trace ++ spkKit.getEvs signedPreKeyId (.ok spkRec) ++
        kpkKit.getEvs kyberPreKeyId (.ok kpkRec) ++ opkOkEvs pkKit (hdrOpkIdBv? hdr) wOpk ++
        skit.kpEvs (.ok kp) →
      sf.sp = sp + 0xcd0#64 → ClosureCalleeSaved s0 sf →
      calleeSavedVRegs sf = calleeSavedVRegs s0 → LibsignalCodeRoLoaded lsmpl sf.mem →
      (P_f ⊢
        speWordsAt outPtr errTag w2 w3 w4 w5 w6 ∗
        pqxdhAcceptErrPayloadAt A.repAlloc errTag w2 w3 w4 ∗
        spkKit.storeAt spkStorePtr (spkKit.getUpdate stSpk signedPreKeyId (.ok spkRec)) ∗
        kpkKit.storeAt kyberStorePtr (kpkKit.getUpdate stKpk kyberPreKeyId (.ok kpkRec)) ∗
        pkKit.storeAt preKeyStorePtr (opkOkUpdate pkKit stPk (hdrOpkIdBv? hdr) wOpk) ∗
        ikit.identityAt idStorePtr stId ∗
        p2ErrFrameAtPlaced A lim (M.stepEvents evs st) s0 sf
          sp fp coroPtr msgPtr ctBufPtr remoteAddrPtr localAddrPtr
          idStorePtr ikit.id_vt preKeyStorePtr pkKit.pk_vt kyberStorePtr kpkKit.kpk_vt
          v_330 v_388 hdr msgVerByte opkIdWord kyberPreKeyId remoteRegId signedPreKeyId
          gMe gPeer stk Frame) →
      Q sf P_f) →
    (∀ (spkRec : SignedPreKeyRecord) (spkPubBytes spkPrivBytes : List (BitVec 8))
        (kpkRec : KyberPreKeyRecord) (kyberPubBytes kyberPrivBytes : List (BitVec 8))
        (wOpk : OpkOkWitness (hdrOpkIdBv? hdr)) (opkPkBytes opkSkBytes : List (BitVec 8))
        (kp : IdentityKeyPair) (drKey : DRKey) (e : skit.RegIdErr)
        (sf : State) (P_f : SepProp) (evs : List AllocEvent),
      spkKit.getRel stSpk signedPreKeyId (.ok spkRec) → spkKit.RecOk spkRec →
      spkPubBytes.length = 32 → spkPrivBytes.length = 32 →
      spkRec.signedPreKey.publicKey = 5#8 :: spkPubBytes →
      spkRec.signedPreKey.privateKey = spkPrivBytes →
      kpkKit.getRel stKpk kyberPreKeyId (.ok kpkRec) → kpkKit.RecOk kpkRec →
      kyberPubBytes.length = 1568 → kyberPrivBytes.length = 3168 →
      kpkRec.signedPreKey.publicKey = 8#8 :: kyberPubBytes →
      kpkRec.signedPreKey.privateKey = 8#8 :: kyberPrivBytes →
      opkOkRel pkKit stPk (hdrOpkIdBv? hdr) wOpk →
      opkPkBytes.length = 32 → opkSkBytes.length = 32 →
      opkOkKeyBytes (hdrOpkIdBv? hdr) wOpk opkPkBytes opkSkBytes →
      skit.kpRel stId (.ok kp) →
      acceptKeys P
        (mkP2AcceptKeysInput hdr ikBSk ikBPk spkPubBytes spkPrivBytes
          kyberPubBytes kyberPrivBytes opkSkBytes) = some drKey →
      skit.regIdRel stId (.error e) →
      P2OverV1Arm6EnvOfBob spkKit.getBoxSize (spkEnv.getPollEnv stSpk signedPreKeyId)
        kpkKit.getBoxSize (kpkEnv.getPollEnv stKpk kyberPreKeyId)
        pkKit.getBoxSize (pkEnv.getPollEnv stPk) skit.kpBoxSize (hdrOpkIdBv? hdr)
        (senv.kpPollEnv stId)
        (BobV1Env
          (mkP2AcceptKeysInput hdr ikBSk ikBPk spkPubBytes spkPrivBytes
            kyberPubBytes kyberPrivBytes opkSkBytes) drKey)
        skit.regIdBoxSize (senv.regIdPollEnv stId) evs →
      sf.pc = s0.readReg64 .x30 → sf.status = .Running →
      sf.trace = s.trace ++ spkKit.getEvs signedPreKeyId (.ok spkRec) ++
        kpkKit.getEvs kyberPreKeyId (.ok kpkRec) ++ opkOkEvs pkKit (hdrOpkIdBv? hdr) wOpk ++
        skit.kpEvs (.ok kp) ++ skit.regIdEvs (.error e) →
      sf.sp = sp + 0xcd0#64 → ClosureCalleeSaved s0 sf →
      calleeSavedVRegs sf = calleeSavedVRegs s0 → LibsignalCodeRoLoaded lsmpl sf.mem →
      (P_f ⊢
        speErrAt skit.regIdErr outPtr e ∗
        spkKit.storeAt spkStorePtr (spkKit.getUpdate stSpk signedPreKeyId (.ok spkRec)) ∗
        kpkKit.storeAt kyberStorePtr (kpkKit.getUpdate stKpk kyberPreKeyId (.ok kpkRec)) ∗
        pkKit.storeAt preKeyStorePtr (opkOkUpdate pkKit stPk (hdrOpkIdBv? hdr) wOpk) ∗
        ikit.identityAt idStorePtr stId ∗
        p2ErrFrameAtPlaced A lim (M.stepEvents evs st) s0 sf
          sp fp coroPtr msgPtr ctBufPtr remoteAddrPtr localAddrPtr
          idStorePtr ikit.id_vt preKeyStorePtr pkKit.pk_vt kyberStorePtr kpkKit.kpk_vt
          v_330 v_388 hdr msgVerByte opkIdWord kyberPreKeyId remoteRegId signedPreKeyId
          gMe gPeer stk Frame) →
      Q sf P_f) →
    (∀ (spkRec : SignedPreKeyRecord) (spkPubBytes spkPrivBytes : List (BitVec 8))
        (kpkRec : KyberPreKeyRecord) (kyberPubBytes kyberPrivBytes : List (BitVec 8))
        (wOpk : OpkOkWitness (hdrOpkIdBv? hdr)) (opkPkBytes opkSkBytes : List (BitVec 8))
        (kp : IdentityKeyPair) (drKey : DRKey) (localRegId : BitVec 32)
        (G_bob : SessionGhost) (sf : State) (evs : List AllocEvent),
      spkKit.getRel stSpk signedPreKeyId (.ok spkRec) → spkKit.RecOk spkRec →
      (hspkPub_len : spkPubBytes.length = 32) → (hspkPriv_len : spkPrivBytes.length = 32) →
      spkRec.signedPreKey.publicKey = 5#8 :: spkPubBytes →
      spkRec.signedPreKey.privateKey = spkPrivBytes →
      kpkKit.getRel stKpk kyberPreKeyId (.ok kpkRec) → kpkKit.RecOk kpkRec →
      kyberPubBytes.length = 1568 → kyberPrivBytes.length = 3168 →
      kpkRec.signedPreKey.publicKey = 8#8 :: kyberPubBytes →
      kpkRec.signedPreKey.privateKey = 8#8 :: kyberPrivBytes →
      opkOkRel pkKit stPk (hdrOpkIdBv? hdr) wOpk →
      opkPkBytes.length = 32 → opkSkBytes.length = 32 →
      opkOkKeyBytes (hdrOpkIdBv? hdr) wOpk opkPkBytes opkSkBytes →
      skit.kpRel stId (.ok kp) →
      acceptKeys P
        (mkP2AcceptKeysInput hdr ikBSk ikBPk spkPubBytes spkPrivBytes
          kyberPubBytes kyberPrivBytes opkSkBytes) = some drKey →
      skit.regIdRel stId (.ok localRegId) →
      P2OverV1OkEnvOfBobAndProm spkKit.getBoxSize (spkEnv.getPollEnv stSpk signedPreKeyId)
        kpkKit.getBoxSize (kpkEnv.getPollEnv stKpk kyberPreKeyId)
        pkKit.getBoxSize (pkEnv.getPollEnv stPk) skit.kpBoxSize (hdrOpkIdBv? hdr)
        (senv.kpPollEnv stId)
        (BobV1Env
          (mkP2AcceptKeysInput hdr ikBSk ikBPk spkPubBytes spkPrivBytes
            kyberPubBytes kyberPrivBytes opkSkBytes) drKey)
        skit.regIdBoxSize (senv.regIdPollEnv stId)
        (P2OverSub6TailEnvOf PromEnv skit.regIdBoxSize recG sess) evs →
      G_bob.pending = none → G_bob.kyber = none →
      G_bob.alice.bytes = bytesToBv8 (encodeEC hdr.ekAPk) →
      G_bob.regIds = unpack32 remoteRegId ++ unpack32 localRegId →
      Steps (stageP1ProgPlaced ext) s sf →
      FsAt (stageP2EnvOk spkKit kpkKit pkKit ikit)
        (stageP2Quiet spkKit kpkKit pkKit skit) (stageP1ProgPlaced ext) sf →
      sf.pc = stageP1EntryPlaced + 0x1778#64 →
      sf.status = .Running → sf.sp = sp →
      sf.trace = s.trace ++ spkKit.getEvs signedPreKeyId (.ok spkRec) ++
        kpkKit.getEvs kyberPreKeyId (.ok kpkRec) ++ opkOkEvs pkKit (hdrOpkIdBv? hdr) wOpk ++
        skit.kpEvs (.ok kp) ++ skit.regIdEvs (.ok localRegId) →
      sf.readReg64 .x8 = coroPtr + 0xe0#64 → sf.readReg64 .x9 = 8#64 →
      sf.readReg64 .x10 = msgVerByte.zeroExtend 64 → sf.readReg64 .x11 = coroPtr + 0xf8#64 →
      sf.readReg64 .x19 = coroPtr → sf.readReg64 .x20 = 0xfffffffffffffffe#64 →
      sf.readReg64 .x22 = (kyberPreKeyId.zeroExtend 64 <<< 32) ||| 1#64 →
      sf.readReg64 .x23 = (opkOptTag32 (hdrOpkIdBv? hdr)).zeroExtend 64 ||| (opkIdWord.zeroExtend 64 <<< 32) →
      sf.readReg64 .x24 = (opkOptTag32 (hdrOpkIdBv? hdr)).zeroExtend 64 ||| (opkIdWord.zeroExtend 64 <<< 32) →
      sf.readReg64 .x25 = sp + 0x210#64 → sf.readReg64 .x26 = v_330 →
      sf.readReg64 .x27 = sp + 0x370#64 → sf.readReg64 .x28 = sp + 0xa90#64 →
      sf.readReg64 .x29 = fp → calleeSavedVRegs sf = calleeSavedVRegs s0 →
      LibsignalCodeRoLoaded lsmpl sf.mem →
      SepWPp (stageP1ProgPlaced ext) (s0.readReg64 .x30) sf
        (p2OverOkPostAtPlaced A lim 0#64 spkKit kpkKit pkKit ikit (M.stepEvents evs st) s0 sf
          sp fp coroPtr ctxPtr outPtr msgPtr ctBufPtr remoteAddrPtr localAddrPtr
          idStorePtr preKeyStorePtr spkStorePtr kyberStorePtr v_330 v_388
          recG sess G_bob
          (p2BobInitSessionV1 ikBPk (toU8 spkPubBytes)
            (mkP2AcceptKeysInput hdr ikBSk ikBPk spkPubBytes spkPrivBytes
              kyberPubBytes kyberPrivBytes opkSkBytes)
            drKey (initialStateValue F (p2BobSpqrParams drKey.pqrKey))
            hikBPk_len hikAPk_len
            (by simp [toU8, hspkPub_len])
            (by simp [mkP2AcceptKeysInput, toU8, clampBv8List_length hspkPriv_len]))
          hdr msgVerByte b_2c0 opkIdWord kyberPreKeyId remoteRegId signedPreKeyId
          (spkKit.getUpdate stSpk signedPreKeyId (.ok spkRec))
          (kpkKit.getUpdate stKpk kyberPreKeyId (.ok kpkRec))
          (opkOkUpdate pkKit stPk (hdrOpkIdBv? hdr) wOpk)
          stId gMe gPeer stk Frame)
        Q Qp) →
    SepWPp (stageP1ProgPlaced ext) (s0.readReg64 .x30) s
      (stageP2OverPreAtPlaced A lim 0#64 spkKit kpkKit pkKit ikit st s0 s
        sp fp coroPtr ctxPtr outPtr msgPtr ctBufPtr remoteAddrPtr localAddrPtr
        idStorePtr preKeyStorePtr spkStorePtr kyberStorePtr
        v_330 v_388 u_488 u_80 u_88 u_90 u_a8 u_b8 u_d0
        hdr msgVerByte b_2c0 b_390 b_4b0 b_4f1 b_4f2
        opkIdWord kyberPreKeyId remoteRegId signedPreKeyId
        stSpk stKpk stPk stId gMe gPeer g recG sess stk Frame)
      Q Qp

abbrev stageP2OverV1KitsAtPlacedProp [LibsignalPlacement] {M : AllocCostModel}
    (P : Primitives) (A : RustCliAllocBudget M) (lim : BudgetLimits) (F : ShaCompress)
    (AcceptErrEnv : AcceptKeysInput → List AllocEvent → Prop)
    (ext : String → Option (State → State))
    {ikit : IdentityStoreSpec A.repAlloc 0#64}
    (skit : IdentitySelfStoreSpec ikit) (senv : IdentitySelfStoreBudgetEnv skit)
    (spkKit : SignedPreKeyStoreSpec A.repAlloc 0#64) (spkEnv : SignedPreKeyStoreBudgetEnv spkKit)
    (kpkKit : KyberPreKeyStoreSpec A.repAlloc 0#64) (kpkEnv : KyberPreKeyStoreBudgetEnv kpkKit)
    (pkKit : PreKeyStoreSpec A.repAlloc 0#64) (pkEnv : PreKeyStoreBudgetEnv pkKit)
    (stk : Nat) : Prop :=
  stageP2OverV1KitsAtPlacedOfEnvProp P A lim F (InitializeBobV1Env F) AcceptErrEnv PromoteOverEnv
    ext skit senv spkKit spkEnv kpkKit kpkEnv pkKit pkEnv stk

private theorem freeOnlyEvs_rustDeallocEvents (size align : Nat) :
    FreeOnlyEvs (rustDeallocEvents size align) := by
  unfold FreeOnlyEvs rustDeallocEvents
  intro ev hev
  try split at hev
  all_goals simp at hev
  all_goals rcases hev with rfl
  all_goals exact ⟨_, _, rfl⟩

set_option maxHeartbeats 1200000 in
/-- Stack-, hooks-, and envelope-parameterized budget-threaded placed Over-path Stage P2
(`+0x0868 → +0x1778` archiving `sess` into `previous_sessions`, plus error Arms 1–6). -/
theorem stageP2_over_v1_kits_at_placed_ofEnv [LibsignalPlacement]
    {M : AllocCostModel} {P : Primitives} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {F : ShaCompress} {BobV1Env : AcceptKeysInput → DRKey → List AllocEvent → Prop}
    {AcceptErrEnv : AcceptKeysInput → List AllocEvent → Prop}
    {PromEnv : SessionGhost → Session (List (BitVec 8)) → List AllocEvent → Prop}
    (ext : String → Option (State → State))
    (hWF : StructuralPrims P)
    (hH : StageP2ClosureHooksPlaced A lim ext)
    (hPure : StageP2PureCalleesPlaced4KOfEnv P A lim F BobV1Env AcceptErrEnv ext)
    {sameStk bobErrStk bobV1Stk : Nat}
    (hSameAcct :
      subroutine_ok (stageP1ProgPlaced ext) (lsmpl.base 17)
        (withLsCodeLoaded lsmpl (isSameAccountDistinctAtSpec A.repAlloc uuidTryParse sameStk)))
    (hInitBobErrOwned :
      subroutine_ok (stageP1ProgPlaced ext) (lsmpl.base 75)
        (initializeBobSessionErrOwnedAtPlacedSpec P A lim AcceptErrEnv bobErrStk))
    (hInitBobV1 : InitializeBobV1OkAtPlacedOfEnv P A lim F BobV1Env ext bobV1Stk)
    (hsame_le : sameStk ≤ bobV1Stk)
    (herr_le : bobErrStk ≤ bobV1Stk)
    (ikit : IdentityStoreSpec A.repAlloc 0#64) (skit : IdentitySelfStoreSpec ikit)
    (senv : IdentitySelfStoreBudgetEnv skit)
    (hskitVt : IdentitySelfVtablesPlacedOk ikit skit)
    (hskitOk : IdentitySelfStoreKitPlacedOkI A lim ikit skit senv ext)
    (spkKit : SignedPreKeyStoreSpec A.repAlloc 0#64)
    (spkEnv : SignedPreKeyStoreBudgetEnv spkKit)
    (hspkVt : SignedPreKeyVtablesPlacedOk spkKit)
    (hspkOk : SignedPreKeyStoreKitPlacedOk A lim spkKit spkEnv ext)
    (kpkKit : KyberPreKeyStoreSpec A.repAlloc 0#64)
    (kpkEnv : KyberPreKeyStoreBudgetEnv kpkKit)
    (hkpkVt : KyberPreKeyVtablesPlacedOk kpkKit)
    (hkpkOk : KyberPreKeyStoreKitPlacedOk A lim kpkKit kpkEnv ext)
    (pkKit : PreKeyStoreSpec A.repAlloc 0#64)
    (pkEnv : PreKeyStoreBudgetEnv pkKit)
    (hpkVt : PreKeyVtablesPlacedOk pkKit)
    (hpkOk : PreKeyStoreKitPlacedOk A lim pkKit pkEnv ext)
    {v1CallStk : Nat}
    (hv1_p2 : stageP2OverCallStack spkKit kpkKit pkKit skit ≤ v1CallStk)
    (hv1_bob : bobV1Stk ≤ v1CallStk)
    (stk : Nat) (hstk : v1CallStk ≤ stk) :
    stageP2OverV1KitsAtPlacedOfEnvProp P A lim F BobV1Env AcceptErrEnv PromEnv ext
      skit senv spkKit spkEnv kpkKit kpkEnv pkKit pkEnv stk := by
  intro st Qp
    s0 s Frame Q
    sp fp coroPtr ctxPtr outPtr msgPtr ctBufPtr remoteAddrPtr localAddrPtr
    idStorePtr preKeyStorePtr spkStorePtr kyberStorePtr
    v_330 v_388 u_488 u_80 u_88 u_90 u_a8 u_b8 u_d0
    hdr ikBSk ikBPk
    msgVerByte b_2c0 b_390 b_4b0 b_4f1 b_4f2
    opkIdWord kyberPreKeyId remoteRegId signedPreKeyId
    stSpk stKpk stPk stId
    gMe gPeer g recG sess
    hPromMiss hPromoteOver
    hfits14 hfitsKp hfitsBob hfitsAccErr
    hctBuf_nz hpqr_ne hstk_lt
    hikBSk_len hikBPk_len hikAPk_len hekAPk_len hkemCt_len
    hCode hfs
    hid_spk hspk_wf hid_kpk hkpk_wf hopk_word hid_pk hpk_wf
    hkp_sk hkp_pk hneq
    hpc hrun hsp_eq hsp_align htr hvregs
    hx8 hx9 hx10 hx11 hx12 hx13 hx14 hx15 hx16 hx19 hx22 hx23 hx24 hx29
    hErrSpk hErrKpk hErrPk hErrKp hErrBob hErrRegId hOk
  have hstk_overCall : stageP2OverCallStack spkKit kpkKit pkKit skit ≤ stk :=
    Nat.le_trans hv1_p2 hstk
  have hstk_overP2 : stageP2OverCallStack4K spkKit kpkKit pkKit skit ≤ stk :=
    (stageP2OverCallStack4K_eq spkKit kpkKit pkKit skit).symm ▸ hstk_overCall
  have hstk_baseP2 : stageP2CallStack spkKit kpkKit pkKit skit ≤ stk :=
    Nat.le_trans (p2_over_baseCall_le_callStack spkKit kpkKit pkKit skit) hstk_overCall
  have hstk_overPure : stageP2OverPureAndErrStack ≤ stk :=
    Nat.le_trans (p2_over_pure_le_callStack spkKit kpkKit pkKit skit) hstk_overCall
  have hstk_bob : bobV1Stk ≤ stk :=
    Nat.le_trans hv1_bob hstk
  have hstk_sub56 : stageP2Sub56Stack skit ≤ stk :=
    Nat.le_trans (p2_sub56_le_stageP2 spkKit kpkKit pkKit skit) hstk_baseP2
  have hstk_drop : dropSessionStructureLocal2Stack ≤ stk :=
    Nat.le_trans p2_over_dropSS3_le_overPure hstk_overPure
  have hkem_pos : 0 < (bytesToBv8 hdr.kemCt).length := by
    simp [bytesToBv8, hkemCt_len]
  let baseKey : PublicKey := ⟨⟨bytesToBv8 hdr.ekAPk, by simpa [bytesToBv8] using hekAPk_len⟩⟩
  have hPromMiss_bk :
      PromoteMatchingMissAtPlacedProp A.repAlloc ext coroPtr g recG sess 4#8 baseKey.serialize :=
    hPromMiss
  refine p2_mono_pre
    (p2_over_entry_to_sub1To4_placed A lim st s0 s spkKit kpkKit pkKit ikit
      sp fp coroPtr ctxPtr outPtr msgPtr ctBufPtr remoteAddrPtr localAddrPtr
      idStorePtr preKeyStorePtr spkStorePtr kyberStorePtr
      v_330 v_388 u_488 u_80 u_88 u_90 u_a8 u_b8 u_d0
      hdr msgVerByte b_2c0 b_390 b_4b0 b_4f1 b_4f2
      opkIdWord kyberPreKeyId remoteRegId signedPreKeyId
      stSpk stKpk stPk stId gMe gPeer g recG sess stk Frame) ?_
  refine stageP2_over_sub1_to_4_kits_ext_placed_ofEnv ext hH hPure
    ikit skit senv hskitVt hskitOk spkKit spkEnv hspkVt hspkOk
    kpkKit kpkEnv hkpkVt hkpkOk pkKit pkEnv hpkVt hpkOk
    stk hstk_overP2 st s0 s
    (p2Sub1To4Frame A.repAlloc ikit sp fp coroPtr msgPtr ctBufPtr remoteAddrPtr localAddrPtr
      idStorePtr v_330 v_388 u_80 u_88 stId hdr msgVerByte remoteRegId gMe gPeer Frame)
    Q sp coroPtr ctxPtr outPtr msgPtr remoteAddrPtr localAddrPtr
    idStorePtr preKeyStorePtr spkStorePtr kyberStorePtr ctBufPtr
    (coroPtr + 0x390#64) u_90 u_a8 u_b8 u_d0 u_488 hstk_lt
    g recG sess baseKey signedPreKeyId kyberPreKeyId opkIdWord (hdrOpkIdBv? hdr)
    stSpk stKpk stPk b_2c0 b_390 b_4b0 b_4f1 b_4f2
    hfits14 hPromMiss_bk hctBuf_nz hCode hfs
    hid_spk hspk_wf hid_kpk hkpk_wf hopk_word hid_pk hpk_wf
    hpc hrun hsp_eq hsp_align htr hvregs
    hx8 hx9 hx10 hx11 hx12 hx13 hx14 hx15 hx16 hx19 hx22 hx23 hx24
    (fun e spkFutPtr evs sf P_f hrel hevs hpcf hrunf htrf hspf hcsf hvregsf hCodef hent =>
      hErrSpk e sf P_f evs hrel hevs hpcf hrunf htrf hspf hcsf hvregsf hCodef
        (Entails.trans hent
          (p2_v1_arm1_entails_placed A lim (M.stepEvents evs st) spkKit kpkKit pkKit ikit s0 sf
            sp fp coroPtr ctxPtr outPtr msgPtr ctBufPtr remoteAddrPtr localAddrPtr
            idStorePtr preKeyStorePtr spkStorePtr kyberStorePtr
            (coroPtr + 0x390#64) v_330 v_388 u_488 u_80 u_88 spkFutPtr
            b_4b0 msgVerByte opkIdWord kyberPreKeyId remoteRegId signedPreKeyId hdr
            stSpk stKpk stPk stId e gMe gPeer stk Frame)))
    (fun spkRec spkPubBytes spkPrivBytes e kyberFutPtr evs sf P_f
        hspk_rel hspk_ok hpub_len hpriv_len _ _ hkpk_rel hevs
        hpcf hrunf htrf hspf hcsf hvregsf hCodef hent =>
      hErrKpk spkRec e sf P_f evs hspk_rel hspk_ok hkpk_rel hevs
        hpcf hrunf htrf hspf hcsf hvregsf hCodef
        (Entails.trans hent
          (p2_v1_arm2_entails_placed A lim (M.stepEvents evs st) spkKit kpkKit pkKit ikit s0 sf
            sp fp coroPtr ctxPtr outPtr msgPtr ctBufPtr remoteAddrPtr localAddrPtr
            idStorePtr preKeyStorePtr spkStorePtr kyberStorePtr
            (coroPtr + 0x390#64) v_330 v_388 u_488 u_80 u_88 kyberFutPtr
            b_4b0 msgVerByte opkIdWord kyberPreKeyId remoteRegId signedPreKeyId hdr
            spkRec spkPubBytes spkPrivBytes hpub_len hpriv_len
            stSpk stKpk stPk stId e gMe gPeer stk Frame)))
    (fun spkRec spkPubBytes spkPrivBytes kpkRec _ _ opkId e pkBuf skBuf opkFutPtr v90 evs sf P_f
        hspk_rel hspk_ok hpub_len hpriv_len _ _ hkpk_rel hkpk_ok _ _ _ _ hopk_some hpk_rel hevs
        hpcf hrunf htrf hspf hcsf hvregsf hCodef hent =>
      hErrPk spkRec kpkRec opkId e sf P_f evs
        hspk_rel hspk_ok hkpk_rel hkpk_ok hopk_some hpk_rel hevs
        hpcf hrunf htrf hspf hcsf hvregsf hCodef
        (Entails.trans hent
          (p2_v1_arm3_entails_placed A lim (M.stepEvents evs st) spkKit kpkKit pkKit ikit s0 sf
            sp fp coroPtr ctxPtr outPtr msgPtr ctBufPtr remoteAddrPtr localAddrPtr
            idStorePtr preKeyStorePtr spkStorePtr kyberStorePtr
            (coroPtr + 0x390#64) v_330 v_388 u_80 u_88 pkBuf skBuf opkFutPtr v90
            b_4b0 msgVerByte opkId opkIdWord kyberPreKeyId remoteRegId signedPreKeyId hdr
            spkRec kpkRec spkPubBytes spkPrivBytes hpub_len hpriv_len
            stSpk stKpk stPk stId e gMe gPeer stk Frame)))
    (fun spkRec spkPubBytes spkPrivBytes kpkRec kyberPubBytes kyberPrivBytes
        wOpk opkPkBytes opkSkBytes pkBuf skBuf idKpFutPtr v90 v_a8' v_b8' v_d0' evs14 s4
        hst_s4 hfs4 hspk_rel hspk_ok hspkPub_len hspkPriv_len hspk_pub_eq hspk_priv_eq
        hkpk_rel hkpk_ok hkyberPub_len hkyberPriv_len hkpk_pub_eq hkpk_priv_eq
        hopk_rel hopkPk_len hopkSk_len hopk_kb hevs14
        _ _ _ _
        hpc4 hrun4 hsp4 htr4 hx0_4 hx1_4 hx19_4 hx21_4 hx23_4 hx24_4 hx25_4 hx26_4 hx27_4 hx28_4
        hx29_4 hvregs4 hCode4 => ?_)
  let inp := mkP2AcceptKeysInput hdr ikBSk ikBPk spkPubBytes spkPrivBytes
    kyberPubBytes kyberPrivBytes opkSkBytes
  let spkBPk : SignalPqxdh.Bytes := toU8 spkPubBytes
  have hspkBPk_len : spkBPk.length = 32 := by simp [spkBPk, toU8, hspkPub_len]
  have hwell : WellSizedAcceptKeysInput inp :=
    wellSized_mkP2AcceptKeysInput hikBSk_len hikBPk_len hspkPub_len hspkPriv_len
      hkyberPub_len hkyberPriv_len hopkSk_len hikAPk_len hekAPk_len hkemCt_len
  have hopkSk_eq : ∀ opkSk, inp.opkBSk? = some opkSk → opkSkBytes = bytesToBv8 opkSk :=
    fun _ h => opkOkSkBytes?_eq_of_some h
  refine p2_mono_pre
    (p2_over_sub4_to_sub5_placed A lim (M.stepEvents evs14 st) s0 s4 spkKit kpkKit pkKit skit
      sp fp coroPtr ctxPtr outPtr msgPtr ctBufPtr remoteAddrPtr localAddrPtr
      idStorePtr preKeyStorePtr spkStorePtr kyberStorePtr
      idKpFutPtr pkBuf skBuf v_330 v_388 u_80 u_88 v90 v_a8' v_b8' v_d0'
      inp hdr spkBPk spkPubBytes spkPrivBytes kyberPubBytes kyberPrivBytes opkPkBytes opkSkBytes
      opkIdWord kyberPreKeyId remoteRegId signedPreKeyId
      msgVerByte b_2c0 b_390 b_4f2
      (spkKit.getUpdate stSpk signedPreKeyId (.ok spkRec))
      (kpkKit.getUpdate stKpk kyberPreKeyId (.ok kpkRec))
      (opkOkUpdate pkKit stPk (hdrOpkIdBv? hdr) wOpk) stId
      gMe gPeer g recG sess stk Frame
      rfl (bytesToBv8_toU8 spkPubBytes)
      (mkP2AcceptKeysInput_spkBSk hdr ikBSk ikBPk spkPubBytes spkPrivBytes
        kyberPubBytes kyberPrivBytes opkSkBytes)
      (mkP2AcceptKeysInput_pqspkBSk hdr ikBSk ikBPk spkPubBytes spkPrivBytes
        kyberPubBytes kyberPrivBytes opkSkBytes)
      (opkOptTag8_eq_opkPresentTag (hdrOpkIdBv? hdr) opkSkBytes).symm
      hkyberPriv_len hkem_pos) ?_
  refine SepWPp.exists_elim fun u_b90 => SepWPp.exists_elim fun b_b98 => ?_
  refine stageP2_sub5_v1_kits_at_placed_ofEnv ext skit senv hH hskitOk hskitVt
    hSameAcct hInitBobErrOwned hInitBobV1 hsame_le herr_le
    (st := M.stepEvents evs14 st)
    inp spkBPk opkPkBytes opkSkBytes gMe gPeer stId s0 s4 Q
    sp coroPtr ctxPtr msgPtr remoteAddrPtr localAddrPtr
    idStorePtr idKpFutPtr pkBuf skBuf ctBufPtr fp
    v_a8' v_b8' v_d0' u_b90 opkIdWord 1#8 b_b98 stk
    (p2OverSub5FramePlaced A spkKit kpkKit pkKit ikit s0 sp coroPtr outPtr msgPtr
      remoteAddrPtr localAddrPtr idStorePtr preKeyStorePtr spkStorePtr kyberStorePtr
      pkBuf skBuf v_330 v_388 u_80 u_88 v90 kyberPubBytes inp.hdr
      msgVerByte b_2c0 b_390 b_4f2 kyberPreKeyId remoteRegId signedPreKeyId
      (spkKit.getUpdate stSpk signedPreKeyId (.ok spkRec))
      (kpkKit.getUpdate stKpk kyberPreKeyId (.ok kpkRec))
      (opkOkUpdate pkKit stPk (hdrOpkIdBv? hdr) wOpk) g recG sess Frame)
    rfl rfl (hdr_opkId?_isSome_eq_opkOkSkBytes? hdr opkSkBytes)
    hwell hspkBPk_len hopkPk_len hopkSk_len hopkSk_eq
    (fun kp hkp => hkp_sk kp hkp)
    (fun kp hkp => by rw [hkp_pk kp hkp]; exact hneq)
    hpqr_ne hstk_bob hstk_sub56 hstk_lt
    (hfitsKp evs14 hevs14).seq_left
    (fun kp evsKp drKey hkp_rel hevsKp hacc => by
      simpa only [M.stepEvents_append] using
        (hfitsBob spkRec spkPubBytes spkPrivBytes kpkRec kyberPubBytes kyberPrivBytes
          wOpk opkPkBytes opkSkBytes kp drKey evs14 evsKp
          hspk_rel hspk_ok hspkPub_len hspkPriv_len hspk_pub_eq hspk_priv_eq
          hkpk_rel hkpk_ok hkyberPub_len hkyberPriv_len hkpk_pub_eq hkpk_priv_eq
          hopk_rel hopkPk_len hopkSk_len hopk_kb hkp_rel hacc hevs14 hevsKp).seq_left)
    (fun kp evsKp hkp_rel hevsKp hacc_none => by
      simpa only [M.stepEvents_append] using
        (hfitsAccErr spkRec spkPubBytes spkPrivBytes kpkRec kyberPubBytes kyberPrivBytes
          wOpk opkPkBytes opkSkBytes kp evs14 evsKp
          hspk_rel hspk_ok hspkPub_len hspkPriv_len hspk_pub_eq hspk_priv_eq
          hkpk_rel hkpk_ok hkyberPub_len hkyberPriv_len hkpk_pub_eq hkpk_priv_eq
          hopk_rel hopkPk_len hopkSk_len hopk_kb hkp_rel hacc_none hevs14 hevsKp).seq_left)
    hCode4 hpc4 hrun4 hsp4 hsp_align hvregs4
    (fun s1 htr1 hst1 => p2_envOk_id hfs4 hst1 htr1)
    hx0_4 hx1_4 hx19_4 hx21_4 hx23_4 hx24_4 hx26_4 hx27_4 hx28_4 (hx29_4.trans hx29)
    (fun kp drKey evsKp evsBob s5 v_a8'' v_b8'' v_d0'' u_b90' b_b98'
        hkp_rel hevsKp hacc hevsBob hst_s5 hpc5 hrun5 hsp5 htr5
        hx19_5 _ _ _ _ hx25_5 _ hx28_5 hx29_5 hvregs5 hCode5 => ?_)
    (fun kp evsKp evsErr errTag w2 w3 w4 w5 w6 sf5 v_a8'' v_b8'' v_d0'' u_b90' b_b98'
        hkp_rel hevsKp hacc_none hevsErr herr_ne_ok herr_ne_pend _ hpc5 hrun5 hsp5 htr5
        hx19_5 _ _ _ _ hx25_5 _ hx28_5 _ hvregs5 hCode5 => by
      have hikBPk_eq : toU8 kp.identityKey.publicKey.bytes.toList = ikBPk := by
        rw [hkp_pk kp hkp_rel, p2_toU8_bytesToBv8]
      conv => arg 4; rw [hikBPk_eq]
      let st_arm5 :=
        M.stepEvents (evsKp ++ rustDeallocEvents skit.kpBoxSize 8 ++ evsErr)
          (M.stepEvents evs14 st)
      have harm5 :=
        p2_over_v1_arm5_hooks_placed_ok (st := st_arm5) (Qp := Qp) ext spkKit kpkKit pkKit ikit
          hH hPure.dropSessionStructure3 s0 sf5 Q
          sp fp coroPtr ctxPtr outPtr msgPtr ctBufPtr remoteAddrPtr localAddrPtr
          idStorePtr preKeyStorePtr spkStorePtr kyberStorePtr
          pkBuf skBuf v_330 v_388 u_80 u_88 v90
          errTag w2 w3 w4 w5 w6 v_a8'' v_b8'' v_d0'' u_b90'
          inp ikBPk spkBPk kyberPubBytes opkPkBytes opkSkBytes
          opkIdWord kyberPreKeyId remoteRegId signedPreKeyId
          msgVerByte b_2c0 b_390 b_4f2 b_b98'
          (spkKit.getUpdate stSpk signedPreKeyId (.ok spkRec))
          (kpkKit.getUpdate stKpk kyberPreKeyId (.ok kpkRec))
          (opkOkUpdate pkKit stPk (hdrOpkIdBv? hdr) wOpk) stId
          gMe gPeer g recG sess stk (pqxdhAcceptErrPayloadAt A.repAlloc errTag w2 w3 w4 ∗ Frame)
          hwell hikBPk_len hspkBPk_len hkyberPub_len hopkPk_len hopkSk_len hopkSk_eq
          herr_ne_ok herr_ne_pend hstk_drop hstk_lt
          hCode5 hpc5 hrun5 hsp5 hsp_align hx19_5 (hx25_5.trans hx25_4) hx28_5 hvregs5
          (fun sf P_f evsFree hfree _ hpcf hrunf htrf hspf hcsf hvregsf hCodef hent => by
            let evs :=
              evs14 ++
                (evsKp ++
                  (rustDeallocEvents skit.kpBoxSize 8 ++ (evsErr ++ evsFree)))
            have hevs :
                P2OverV1Arm5EnvOfAcceptErr spkKit.getBoxSize
                  (spkEnv.getPollEnv stSpk signedPreKeyId)
                  kpkKit.getBoxSize (kpkEnv.getPollEnv stKpk kyberPreKeyId)
                  pkKit.getBoxSize (pkEnv.getPollEnv stPk) skit.kpBoxSize (hdrOpkIdBv? hdr)
                  (senv.kpPollEnv stId) (AcceptErrEnv inp) evs :=
              SeqEnv.append hevs14
                (SeqEnv.append hevsKp
                  (SeqEnv.append (freeOnlyEvs_rustDeallocEvents skit.kpBoxSize 8)
                    (SeqEnv.append hevsErr hfree)))
            have hst_eq : M.stepEvents evsFree st_arm5 = M.stepEvents evs st := by
              simp only [st_arm5, evs, M.stepEvents_append]
            exact hErrBob spkRec spkPubBytes spkPrivBytes kpkRec kyberPubBytes kyberPrivBytes
              wOpk opkPkBytes opkSkBytes kp errTag w2 w3 w4 w5 w6 sf P_f evs
              hspk_rel hspk_ok hspkPub_len hspkPriv_len hspk_pub_eq hspk_priv_eq
              hkpk_rel hkpk_ok hkyberPub_len hkyberPriv_len hkpk_pub_eq hkpk_priv_eq
              hopk_rel hopkPk_len hopkSk_len hopk_kb hkp_rel hacc_none hevs
              herr_ne_ok herr_ne_pend
              hpcf hrunf (by rw [htrf, htr5, htr4]) hspf hcsf hvregsf hCodef
              (Entails.trans (hst_eq ▸ hent)
                (p2_arm5_err_payload_pull_placed A lim (M.stepEvents evs st) s0 sf
                  sp fp coroPtr outPtr msgPtr ctBufPtr
                  remoteAddrPtr localAddrPtr idStorePtr ikit.id_vt preKeyStorePtr pkKit.pk_vt
                  kyberStorePtr kpkKit.kpk_vt v_330 v_388 errTag w2 w3 w4 w5 w6
                  inp.hdr msgVerByte opkIdWord kyberPreKeyId remoteRegId signedPreKeyId
                  (spkKit.storeAt spkStorePtr (spkKit.getUpdate stSpk signedPreKeyId (.ok spkRec)))
                  (kpkKit.storeAt kyberStorePtr (kpkKit.getUpdate stKpk kyberPreKeyId (.ok kpkRec)))
                  (pkKit.storeAt preKeyStorePtr (opkOkUpdate pkKit stPk (hdrOpkIdBv? hdr) wOpk))
                  (ikit.identityAt idStorePtr stId)
                  gMe gPeer stk Frame)))
      dsimp only [p2OverSub5FramePlaced, CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Over.p2OverSub5FramePlaced] at harm5 ⊢
      exact p2_sepWPp_weaken_eq harm5 (by sep_focus))
    (fun e evsKp s2 hkp_err hevsKp _ hpc2 hrun2 hsp2 htr2
        hx19_2 hx21_2 hx23_2 hx24_2 hx25_2 hx26_2 hx27_2 hx28_2 hx29_2 hvregs2 hCode2 =>
      let st_arm4 := M.stepEvents evsKp (M.stepEvents evs14 st)
      p2_over_v1_arm4_hooks_placed_ok (st := st_arm4) ext spkKit kpkKit pkKit skit
        hH hPure.dropSessionStructure3 hskitOk s0 s2 Q
        sp fp coroPtr ctxPtr outPtr msgPtr ctBufPtr remoteAddrPtr localAddrPtr
        idStorePtr preKeyStorePtr spkStorePtr kyberStorePtr
        idKpFutPtr pkBuf skBuf v_330 v_388 u_80 u_88 v90
        v_a8' v_b8' v_d0' u_b90
        inp spkBPk kyberPubBytes opkPkBytes opkSkBytes
        opkIdWord kyberPreKeyId remoteRegId signedPreKeyId
        msgVerByte b_2c0 b_390 b_4f2 b_b98
        (spkKit.getUpdate stSpk signedPreKeyId (.ok spkRec))
        (kpkKit.getUpdate stKpk kyberPreKeyId (.ok kpkRec))
        (opkOkUpdate pkKit stPk (hdrOpkIdBv? hdr) wOpk) stId
        e gMe gPeer g recG sess stk Frame
        hwell hspkBPk_len hkyberPub_len hopkPk_len hopkSk_len hstk_drop hstk_lt
        hCode2 hpc2 hrun2 hsp2 hsp_align
        hx19_2 hx21_2 hx23_2 hx24_2 (hx25_2.trans hx25_4) hx26_2 hx27_2 hx28_2 hx29_2 hvregs2
        (fun sf P_f evsFree hfree _ hpcf hrunf htrf hspf hcsf hvregsf hCodef hent => by
          let evs := evs14 ++ (evsKp ++ evsFree)
          have hevs :
              P2OverV1Arm4Env spkKit.getBoxSize (spkEnv.getPollEnv stSpk signedPreKeyId)
                kpkKit.getBoxSize (kpkEnv.getPollEnv stKpk kyberPreKeyId)
                pkKit.getBoxSize (pkEnv.getPollEnv stPk) skit.kpBoxSize (hdrOpkIdBv? hdr)
                (senv.kpPollEnv stId) evs :=
            SeqEnv.append hevs14 (SeqEnv.append hevsKp hfree)
          have hst_eq : M.stepEvents evsFree st_arm4 = M.stepEvents evs st := by
            simp only [st_arm4, evs, M.stepEvents_append]
          exact hErrKp spkRec kpkRec wOpk e sf P_f evs
            hspk_rel hspk_ok hkpk_rel hkpk_ok hopk_rel hkp_err hevs
            hpcf hrunf (by rw [htrf, htr2, htr4]) hspf hcsf hvregsf hCodef (hst_eq ▸ hent)))
  have hikBPk_eq : toU8 kp.identityKey.publicKey.bytes.toList = ikBPk := by
    rw [hkp_pk kp hkp_rel, p2_toU8_bytesToBv8]
  have hfs5 : FsAt (stageP2EnvOk spkKit kpkKit pkKit ikit)
      (stageP2Quiet spkKit kpkKit pkKit skit) (stageP1ProgPlaced ext) s5 :=
    p2_fsAt_step_kp (.ok kp) hfs4 hst_s5 htr5
  have hx25_5' : s5.readReg64 .x25 = sp + 0x210#64 := hx25_5.trans hx25_4
  let pqBytes := initialStateValue F (p2BobSpqrParams drKey.pqrKey)
  let st5 :=
    M.stepEvents (evsKp ++ rustDeallocEvents skit.kpBoxSize 8 ++ evsBob)
      (M.stepEvents evs14 st)
  have hfitsSub6 :
      FitsEnv M lim st5
        (P2OverSub6EnvOf skit.regIdBoxSize (senv.regIdPollEnv stId)
          (P2OverSub6TailEnvOf PromEnv skit.regIdBoxSize recG sess)) := by
    have h0 :=
      (hfitsBob spkRec spkPubBytes spkPrivBytes kpkRec kyberPubBytes kyberPrivBytes
        wOpk opkPkBytes opkSkBytes kp drKey evs14 evsKp
        hspk_rel hspk_ok hspkPub_len hspkPriv_len hspk_pub_eq hspk_priv_eq
        hkpk_rel hkpk_ok hkyberPub_len hkyberPriv_len hkpk_pub_eq hkpk_priv_eq
        hopk_rel hopkPk_len hopkSk_len hopk_kb hkp_rel hacc hevs14 hevsKp).seq_right hevsBob
    simpa only [st5, M.stepEvents_append] using h0
  conv => arg 4; rw [hikBPk_eq]
  refine p2_mono_pre
    (p2_over_sub5_to_sub6_placed A lim st5 s0 s5 spkKit kpkKit pkKit ikit
      sp fp coroPtr ctxPtr outPtr msgPtr ctBufPtr remoteAddrPtr localAddrPtr
      idStorePtr preKeyStorePtr spkStorePtr kyberStorePtr
      pkBuf skBuf v_330 v_388 u_80 u_88 v90 v_a8'' v_b8'' v_d0'' u_b90'
      inp ikBPk spkBPk drKey pqBytes kyberPubBytes opkPkBytes opkSkBytes
      opkIdWord kyberPreKeyId remoteRegId signedPreKeyId
      msgVerByte b_2c0 b_390 b_4f2 b_b98'
      (spkKit.getUpdate stSpk signedPreKeyId (.ok spkRec))
      (kpkKit.getUpdate stKpk kyberPreKeyId (.ok kpkRec))
      (opkOkUpdate pkKit stPk (hdrOpkIdBv? hdr) wOpk) stId
      gMe gPeer g recG sess stk Frame hkyberPub_len) ?_
  refine SepWPp.exists_elim fun localIkBoxPtr =>
    SepWPp.exists_elim fun remoteIkBoxPtr =>
    SepWPp.exists_elim fun rootKeyBoxPtr =>
    SepWPp.exists_elim fun baseKeyBoxPtr =>
    SepWPp.exists_elim fun ratchetPubBoxPtr =>
    SepWPp.exists_elim fun ratchetPrivBoxPtr =>
    SepWPp.exists_elim fun chainKeyBoxPtr =>
    SepWPp.exists_elim fun spqrCap =>
    SepWPp.exists_elim fun spqrBufPtr =>
    SepWPp.exists_elim fun pad_f4 =>
    SepWPp.exists_elim fun c0 =>
    SepWPp.exists_elim fun c1 =>
    SepWPp.exists_elim fun c2 =>
    SepWPp.exists_elim fun c3 =>
    SepWPp.exists_elim fun c4 =>
    SepWPp.exists_elim fun d0 =>
    SepWPp.exists_elim fun d1 =>
    SepWPp.exists_elim fun d2 =>
    SepWPp.exists_elim fun u_650 =>
    SepWPp.exists_elim fun u_298 =>
    SepWPp.exists_elim fun u_2a0 =>
    SepWPp.exists_elim fun u_2a8 =>
    SepWPp.exists_elim fun u_3a0 =>
    SepWPp.exists_elim fun b_3ac =>
    SepWPp.exists_elim fun u_3b0 =>
    SepWPp.exists_elim fun u_3b8 =>
    SepWPp.exists_elim fun u_3c0 =>
    SepWPp.exists_elim fun u_3c8 =>
    SepWPp.exists_elim fun u_3d0 =>
    SepWPp.exists_elim fun u_3d8 => ?_
  refine SepWPp.pure_elim
    fun ⟨hloc_nz, hrem_nz, hroot_nz, halice_nz, hrat_pub, hrat_priv, hck_ptr⟩ => ?_
  have hspk_clamp : clampBv8List spkPrivBytes = bytesToBv8 inp.spkBSk :=
    (mkP2AcceptKeysInput_spkBSk hdr ikBSk ikBPk spkPubBytes spkPrivBytes
      kyberPubBytes kyberPrivBytes opkSkBytes).symm
  refine stageP2_over_sub6_v1_kits_ext_placed_withEnv_ofEnv ext skit senv hH hskitOk hskitVt hPure
    coroPtr g recG sess hPromoteOver
    (st := st5)
    inp ikBPk spkBPk stId s0 s5 (s0.readReg64 .x30) Q
    sp ctxPtr msgPtr remoteAddrPtr localAddrPtr outPtr
    idStorePtr pkBuf skBuf ctBufPtr
    localIkBoxPtr remoteIkBoxPtr v_330 v_388 u_650
    u_298 u_2a0 u_80 u_88 v90 v_a8'' v_b8'' v_d0''
    u_3a0 u_3b0 u_3b8 u_3c0 u_3c8 u_3d0 u_3d8
    (p2BobSessMid280V1 rootKeyBoxPtr baseKeyBoxPtr spqrCap spqrBufPtr
      (BitVec.ofNat 64 pqBytes.length) ratchetPubBoxPtr ratchetPrivBoxPtr chainKeyBoxPtr
      pad_f4 c0 c1 c2 c3 c4 d0 d1 d2)
    (p2BobSessMid280V1_length _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _)
    remoteRegId (opkOptTag32 (hdrOpkIdBv? inp.hdr)) opkIdWord kyberPreKeyId signedPreKeyId u_2a8
    msgVerByte b_4f2 b_390 b_3ac stk
    (p2Sub6FramePlaced A spkKit kpkKit pkKit s0 sp fp coroPtr outPtr msgPtr
      remoteAddrPtr localAddrPtr preKeyStorePtr spkStorePtr kyberStorePtr pkBuf skBuf
      localIkBoxPtr remoteIkBoxPtr rootKeyBoxPtr baseKeyBoxPtr spqrCap spqrBufPtr
      ratchetPubBoxPtr ratchetPrivBoxPtr chainKeyBoxPtr
      inp ikBPk spkBPk drKey pqBytes opkPkBytes opkSkBytes b_2c0
      (spkKit.getUpdate stSpk signedPreKeyId (.ok spkRec))
      (kpkKit.getUpdate stKpk kyberPreKeyId (.ok kpkRec))
      (opkOkUpdate pkKit stPk (hdrOpkIdBv? hdr) wOpk) gMe gPeer Frame)
    hwell hctBuf_nz hstk_sub56 hstk_overPure hstk_lt
    hfitsSub6.seq_left
    (fun evsShim hShim => (hfitsSub6.seq_right hShim).seq_left)
    (fun _ evsShim evsPoll _ hShim hPoll => by
      have hdisj := (hfitsSub6.seq_right hShim).seq_right hPoll
      have htail :
          FitsEnv M lim (M.stepEvents evsPoll (M.stepEvents evsShim st5))
            (P2OverSub6TailEnvOf PromEnv skit.regIdBoxSize recG sess) :=
        fun evs hevs => hdisj evs (Or.inr hevs)
      simpa only [M.stepEvents_append] using fitsPromote_of_fitsTailEnv htail)
    hCode5 hpc5 hrun5 hsp5 hsp_align hvregs5
    (fun s3 htr3 hst3 => p2_envOk_id hfs5 hst3 htr3) hx19_5
    (fun localRegId regIdFutPtr evsShim evsPoll evsProm sf
        hreg_rel hShim hPoll hProm hst_sf hpcf hrunf hspf htrf
        hx8f hx9f hx10f hx11f hx19f hx20f hx22f hx23f hx24f hx25f hx26f hx27f hx28f hx29f
        hvregsf hCodef => by
      let evs :=
        evs14 ++
          (evsKp ++
            (rustDeallocEvents skit.kpBoxSize 8 ++
              (evsBob ++
                (evsShim ++ (evsPoll ++ p2OverSub6TailEvents skit.regIdBoxSize evsProm)))))
      have hevs :
          P2OverV1OkEnvOfBobAndProm spkKit.getBoxSize (spkEnv.getPollEnv stSpk signedPreKeyId)
            kpkKit.getBoxSize (kpkEnv.getPollEnv stKpk kyberPreKeyId)
            pkKit.getBoxSize (pkEnv.getPollEnv stPk) skit.kpBoxSize (hdrOpkIdBv? hdr)
            (senv.kpPollEnv stId) (BobV1Env inp drKey)
            skit.regIdBoxSize (senv.regIdPollEnv stId)
            (P2OverSub6TailEnvOf PromEnv skit.regIdBoxSize recG sess) evs :=
        SeqEnv.append hevs14
          (SeqEnv.append hevsKp
            (SeqEnv.append (freeOnlyEvs_rustDeallocEvents skit.kpBoxSize 8)
              (SeqEnv.append hevsBob
                (SeqEnv.append hShim
                  (SeqEnv.append hPoll (p2OverSub6TailEnvOf_intro hProm))))))
      let st_ok :=
        M.stepEvents (evsShim ++ evsPoll ++ p2OverSub6TailEvents skit.regIdBoxSize evsProm) st5
      have hst_eq : st_ok = M.stepEvents evs st := by
        simp only [st_ok, st5, evs, M.stepEvents_append]
      exact p2_mono_pre
        (p2_over_v1_ok_entails_placed A lim st_ok spkKit kpkKit pkKit skit hWF s0 sf
          sp fp coroPtr ctxPtr outPtr msgPtr ctBufPtr remoteAddrPtr localAddrPtr
          idStorePtr preKeyStorePtr spkStorePtr kyberStorePtr
          regIdFutPtr pkBuf skBuf v_330 v_388
          localIkBoxPtr remoteIkBoxPtr rootKeyBoxPtr baseKeyBoxPtr spqrCap spqrBufPtr
          ratchetPubBoxPtr ratchetPrivBoxPtr chainKeyBoxPtr
          c0 c1 c2 c3 c4 d0 d1 d2
          recG sess inp ikBPk spkBPk drKey spkPrivBytes pqBytes opkPkBytes opkSkBytes
          pad_f4 opkIdWord kyberPreKeyId remoteRegId localRegId signedPreKeyId
          msgVerByte b_2c0
          (spkKit.getUpdate stSpk signedPreKeyId (.ok spkRec))
          (kpkKit.getUpdate stKpk kyberPreKeyId (.ok kpkRec))
          (opkOkUpdate pkKit stPk (hdrOpkIdBv? hdr) wOpk) stId
          gMe gPeer stk Frame
          hacc hwell hikBPk_len hspkBPk_len hspkPriv_len hspk_clamp
          hopkPk_len hopkSk_len hopkSk_eq
          hloc_nz hrem_nz hroot_nz halice_nz hrat_pub hrat_priv hck_ptr)
        (hst_eq.symm ▸
          hOk spkRec spkPubBytes spkPrivBytes kpkRec kyberPubBytes kyberPrivBytes
            wOpk opkPkBytes opkSkBytes kp drKey localRegId
            (mkBobGhostV1 localIkBoxPtr remoteIkBoxPtr rootKeyBoxPtr baseKeyBoxPtr spqrCap spqrBufPtr
              (bytesToBv8 (encodeEC ikBPk)) (bytesToBv8 (encodeEC inp.hdr.ikAPk))
              (bytesToBv8 (encodeEC inp.hdr.ekAPk))
              (mkBobSenderChainGhost ratchetPubBoxPtr ratchetPrivBoxPtr chainKeyBoxPtr
                (bytesToBv8 (encodeEC spkBPk)) (bytesToBv8 inp.spkBSk))
              remoteRegId localRegId)
            sf evs
            hspk_rel hspk_ok hspkPub_len hspkPriv_len hspk_pub_eq hspk_priv_eq
            hkpk_rel hkpk_ok hkyberPub_len hkyberPriv_len hkpk_pub_eq hkpk_priv_eq
            hopk_rel hopkPk_len hopkSk_len hopk_kb hkp_rel hacc hreg_rel hevs
            rfl rfl rfl rfl
            (hst_s4.trans (hst_s5.trans hst_sf))
            (p2_fsAt_step_regId (.ok localRegId) hfs5 hst_sf htrf)
            hpcf hrunf hspf (by rw [htrf, htr5, htr4])
            hx8f hx9f hx10f hx11f hx19f hx20f hx22f hx23f hx24f
            (hx25f.trans hx25_5') hx26f hx27f (hx28f.trans hx28_5) (hx29f.trans hx29_5)
            hvregsf hCodef))
    (fun e regIdFutPtr evsShim evsPoll s6 hreg_err hShim hPoll _ hpc6 hrun6 hsp6 htr6
        hx19_6 hx21_6 hx23_6 hx25_6 hx26_6 _ hx28_6 _ hvregs6 hCode6 =>
      p2_over_v1_arm6_hooks_placed_ok ext spkKit kpkKit pkKit skit
        hWF hH hPure.dropSessionStructure3 hskitOk s0 s6 Q
        sp fp coroPtr ctxPtr outPtr msgPtr ctBufPtr remoteAddrPtr localAddrPtr
        idStorePtr preKeyStorePtr spkStorePtr kyberStorePtr
        regIdFutPtr pkBuf skBuf v_330 v_388
        localIkBoxPtr remoteIkBoxPtr rootKeyBoxPtr baseKeyBoxPtr spqrCap spqrBufPtr
        ratchetPubBoxPtr ratchetPrivBoxPtr chainKeyBoxPtr
        c0 c1 c2 c3 c4 d0 d1 d2
        u_298 u_2a0 u_80 u_88 v90 v_a8'' v_b8'' v_d0''
        u_3a0 u_3b0 u_3b8 u_3c0 u_3c8 u_3d0 u_3d8
        inp ikBPk spkBPk drKey spkPrivBytes pqBytes opkPkBytes opkSkBytes
        pad_f4 opkIdWord kyberPreKeyId remoteRegId signedPreKeyId u_2a8
        msgVerByte b_2c0 b_390 b_4f2 b_3ac
        (spkKit.getUpdate stSpk signedPreKeyId (.ok spkRec))
        (kpkKit.getUpdate stKpk kyberPreKeyId (.ok kpkRec))
        (opkOkUpdate pkKit stPk (hdrOpkIdBv? hdr) wOpk) stId
        e gMe gPeer g recG sess stk Frame
        hacc hwell hikBPk_len hspkBPk_len hspkPriv_len hspk_clamp
        hopkPk_len hopkSk_len hopkSk_eq
        hloc_nz hrem_nz hroot_nz halice_nz hrat_pub hrat_priv hck_ptr
        hstk_drop hstk_lt hCode6 hpc6 hrun6 hsp6 hsp_align
        hx19_6 hx21_6 hx23_6 (hx25_6.trans hx25_5') hx26_6 (hx28_6.trans hx28_5) hvregs6
        (fun sf P_f evsFree hfree _ hpcf hrunf htrf hspf hcsf hvregsf hCodef hent => by
          let evs :=
            evs14 ++
              (evsKp ++
                (rustDeallocEvents skit.kpBoxSize 8 ++
                  (evsBob ++ (evsShim ++ (evsPoll ++ evsFree)))))
          have hevs :
              P2OverV1Arm6EnvOfBob spkKit.getBoxSize (spkEnv.getPollEnv stSpk signedPreKeyId)
                kpkKit.getBoxSize (kpkEnv.getPollEnv stKpk kyberPreKeyId)
                pkKit.getBoxSize (pkEnv.getPollEnv stPk) skit.kpBoxSize (hdrOpkIdBv? hdr)
                (senv.kpPollEnv stId) (BobV1Env inp drKey)
                skit.regIdBoxSize (senv.regIdPollEnv stId) evs :=
            SeqEnv.append hevs14
              (SeqEnv.append hevsKp
                (SeqEnv.append (freeOnlyEvs_rustDeallocEvents skit.kpBoxSize 8)
                  (SeqEnv.append hevsBob
                    (SeqEnv.append hShim (SeqEnv.append hPoll hfree)))))
          have hst_eq :
              M.stepEvents evsFree (M.stepEvents (evsShim ++ evsPoll) st5) =
                M.stepEvents evs st := by
            simp only [st5, evs, M.stepEvents_append]
          exact hErrRegId spkRec spkPubBytes spkPrivBytes kpkRec kyberPubBytes kyberPrivBytes
            wOpk opkPkBytes opkSkBytes kp drKey e sf P_f evs
            hspk_rel hspk_ok hspkPub_len hspkPriv_len hspk_pub_eq hspk_priv_eq
            hkpk_rel hkpk_ok hkyberPub_len hkyberPriv_len hkpk_pub_eq hkpk_priv_eq
            hopk_rel hopkPk_len hopkSk_len hopk_kb hkp_rel hacc hreg_err hevs
            hpcf hrunf (by rw [htrf, htr6, htr5, htr4]) hspf hcsf hvregsf hCodef
            (hst_eq ▸ hent)))

abbrev stageP2_over_v1_kits_at_placed [LibsignalPlacement]
    {M : AllocCostModel} {P : Primitives} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {F : ShaCompress} {AcceptErrEnv : AcceptKeysInput → List AllocEvent → Prop} :=
  @stageP2_over_v1_kits_at_placed_ofEnv _ M P A lim F (InitializeBobV1Env F) AcceptErrEnv
    PromoteOverEnv

theorem stageP2_over_v1_kits_placed_ofEnv [LibsignalPlacement]
    {M : AllocCostModel} {P : Primitives} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {F : ShaCompress} {BobV1Env : AcceptKeysInput → DRKey → List AllocEvent → Prop}
    {AcceptErrEnv : AcceptKeysInput → List AllocEvent → Prop}
    {PromEnv : SessionGhost → Session (List (BitVec 8)) → List AllocEvent → Prop}
    (ext : String → Option (State → State))
    (hWF : StructuralPrims P)
    (hH : StageP2ClosureHooksPlaced A lim ext)
    (hPure : StageP2PureCalleesPlacedOfEnv P A lim F BobV1Env AcceptErrEnv ext)
    (hInitBobErrOwned :
      subroutine_ok (stageP1ProgPlaced ext) (lsmpl.base 75)
        (initializeBobSessionErrOwnedPlacedSpec P A lim AcceptErrEnv))
    (ikit : IdentityStoreSpec A.repAlloc 0#64) (skit : IdentitySelfStoreSpec ikit)
    (senv : IdentitySelfStoreBudgetEnv skit)
    (hskitVt : IdentitySelfVtablesPlacedOk ikit skit)
    (hskitOk : IdentitySelfStoreKitPlacedOkI A lim ikit skit senv ext)
    (spkKit : SignedPreKeyStoreSpec A.repAlloc 0#64)
    (spkEnv : SignedPreKeyStoreBudgetEnv spkKit)
    (hspkVt : SignedPreKeyVtablesPlacedOk spkKit)
    (hspkOk : SignedPreKeyStoreKitPlacedOk A lim spkKit spkEnv ext)
    (kpkKit : KyberPreKeyStoreSpec A.repAlloc 0#64)
    (kpkEnv : KyberPreKeyStoreBudgetEnv kpkKit)
    (hkpkVt : KyberPreKeyVtablesPlacedOk kpkKit)
    (hkpkOk : KyberPreKeyStoreKitPlacedOk A lim kpkKit kpkEnv ext)
    (pkKit : PreKeyStoreSpec A.repAlloc 0#64)
    (pkEnv : PreKeyStoreBudgetEnv pkKit)
    (hpkVt : PreKeyVtablesPlacedOk pkKit)
    (hpkOk : PreKeyStoreKitPlacedOk A lim pkKit pkEnv ext)
    (stk : Nat) (hstk : stageP2OverV1CallStack spkKit kpkKit pkKit skit ≤ stk) :
    stageP2OverV1KitsAtPlacedOfEnvProp P A lim F BobV1Env AcceptErrEnv PromEnv ext
      skit senv spkKit spkEnv kpkKit kpkEnv pkKit pkEnv stk :=
  stageP2_over_v1_kits_at_placed_ofEnv ext hWF hH hPure.to_4K
    (isSameAccountDistinctSpec_to_at_placed hPure.isSameAccount)
    (of_responderCore_errOwned_placed hInitBobErrOwned)
    (bobV1Stk := initializeBobSessionV1StackPlaced) hPure.initializeBobV1
    p2_isSameAccount_le_bobV1 p2_stageP2bStack_le_bobV1
    ikit skit senv hskitVt hskitOk
    spkKit spkEnv hspkVt hspkOk
    kpkKit kpkEnv hkpkVt hkpkOk
    pkKit pkEnv hpkVt hpkOk
    (p2_over_callStack_le_v1CallStack spkKit kpkKit pkKit skit)
    (Nat.le_trans (p2_bobStack_le_v1CallStack spkKit kpkKit pkKit skit)
      (p2_over_baseV1Call_le_v1CallStack spkKit kpkKit pkKit skit))
    stk hstk

abbrev stageP2_over_v1_kits_placed [LibsignalPlacement]
    {M : AllocCostModel} {P : Primitives} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {F : ShaCompress} {AcceptErrEnv : AcceptKeysInput → List AllocEvent → Prop} :=
  @stageP2_over_v1_kits_placed_ofEnv _ M P A lim F (InitializeBobV1Env F) AcceptErrEnv
    PromoteOverEnv

theorem stageP2_over_v1_kits_ext_placed_ofEnv [LibsignalPlacement]
    {M : AllocCostModel} {P : Primitives} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {F : ShaCompress} {BobV1Env : AcceptKeysInput → DRKey → List AllocEvent → Prop}
    {AcceptErrEnv : AcceptKeysInput → List AllocEvent → Prop}
    {PromEnv : SessionGhost → Session (List (BitVec 8)) → List AllocEvent → Prop}
    (ext : String → Option (State → State))
    (hWF : StructuralPrims P)
    (hH : StageP2ClosureHooksPlaced A lim ext)
    (hPure : StageP2PureCalleesPlaced4KOfEnv P A lim F BobV1Env AcceptErrEnv ext)
    (hInitBobErrOwned :
      subroutine_ok (stageP1ProgPlaced ext) (lsmpl.base 75)
        (initializeBobSessionErrOwned4KPlacedSpec P A lim AcceptErrEnv))
    (ikit : IdentityStoreSpec A.repAlloc 0#64) (skit : IdentitySelfStoreSpec ikit)
    (senv : IdentitySelfStoreBudgetEnv skit)
    (hskitVt : IdentitySelfVtablesPlacedOk ikit skit)
    (hskitOk : IdentitySelfStoreKitPlacedOkI A lim ikit skit senv ext)
    (spkKit : SignedPreKeyStoreSpec A.repAlloc 0#64)
    (spkEnv : SignedPreKeyStoreBudgetEnv spkKit)
    (hspkVt : SignedPreKeyVtablesPlacedOk spkKit)
    (hspkOk : SignedPreKeyStoreKitPlacedOk A lim spkKit spkEnv ext)
    (kpkKit : KyberPreKeyStoreSpec A.repAlloc 0#64)
    (kpkEnv : KyberPreKeyStoreBudgetEnv kpkKit)
    (hkpkVt : KyberPreKeyVtablesPlacedOk kpkKit)
    (hkpkOk : KyberPreKeyStoreKitPlacedOk A lim kpkKit kpkEnv ext)
    (pkKit : PreKeyStoreSpec A.repAlloc 0#64)
    (pkEnv : PreKeyStoreBudgetEnv pkKit)
    (hpkVt : PreKeyVtablesPlacedOk pkKit)
    (hpkOk : PreKeyStoreKitPlacedOk A lim pkKit pkEnv ext)
    (stk : Nat) (hstk : stageP2OverV1CallStack4K spkKit kpkKit pkKit skit ≤ stk) :
    stageP2OverV1KitsAtPlacedOfEnvProp P A lim F BobV1Env AcceptErrEnv PromEnv ext
      skit senv spkKit spkEnv kpkKit kpkEnv pkKit pkEnv stk :=
  stageP2_over_v1_kits_at_placed_ofEnv ext hWF hH hPure
    (isSameAccountDistinctSpecExt_to_at_placed hPure.isSameAccount)
    (of_stageP2Defs_errOwned4K_placed hInitBobErrOwned)
    (bobV1Stk := initializeBobSessionV1StackExtPlaced) hPure.initializeBobV1
    p2_isSameAccountExt_le_bobExt p2_bobErr4K_le_bobExt
    ikit skit senv hskitVt hskitOk
    spkKit spkEnv hspkVt hspkOk
    kpkKit kpkEnv hkpkVt hkpkOk
    pkKit pkEnv hpkVt hpkOk
    ((stageP2OverV1CallStack4K_eq spkKit kpkKit pkKit skit).symm ▸
      p2_over_callStack_le_v1CallStack spkKit kpkKit pkKit skit)
    ((stageP2OverV1CallStack4K_eq spkKit kpkKit pkKit skit).symm ▸
      Nat.le_trans p2_over_bobExt_le_overPure
        (p2_over_pure_le_v1CallStack spkKit kpkKit pkKit skit))
    stk hstk

abbrev stageP2_over_v1_kits_ext_placed [LibsignalPlacement]
    {M : AllocCostModel} {P : Primitives} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {F : ShaCompress} {AcceptErrEnv : AcceptKeysInput → List AllocEvent → Prop} :=
  @stageP2_over_v1_kits_ext_placed_ofEnv _ M P A lim F (InitializeBobV1Env F) AcceptErrEnv
    PromoteOverEnv

abbrev stageP2_over_v1_kits_4k_placed [LibsignalPlacement] :=
  @stageP2_over_v1_kits_ext_placed

/-! ## `StageP2MemInv`- and `LibsignalFrozen`-Guarded Variants -/

private theorem of_stageP2Defs_errOwnedMemInv4K_placed [LibsignalPlacement]
    {prog : Program} {entry : BitVec 64} {M : AllocCostModel} {Φ : Memory → Prop}
    {P : Primitives} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {AcceptErrEnv : AcceptKeysInput → List AllocEvent → Prop}
    (h : subroutine_ok prog entry
      (initializeBobSessionErrOwnedMemInv4KPlacedSpec Φ P A lim AcceptErrEnv)) :
    subroutine_ok prog entry
      (initializeBobSessionErrOwnedMemInvAtPlacedSpec Φ P A lim AcceptErrEnv
        (768 + CryptoVerification.E2E.Pqxdh.Initiator.pqxdhEntryStackExt)) := by
  refine subroutine_ok_map h ?_
  rintro ⟨g, st⟩ R s0 hpre
  refine ⟨(g, st), R, ?_, fun sf hpost => ?_⟩
  · dsimp only [initializeBobSessionErrOwnedMemInvAtPlacedSpec,
      initializeBobSessionErrOwnedAtInnerPlacedSpec,
      CryptoVerification.LibsignalPublicApi.StoreKit.withLsCodeRoLoaded,
      initializeBobSessionErrOwnedMemInv4KPlacedSpec,
      initializeBobSessionErrOwned4KInnerPlacedSpec,
      withLsCodeRoLoaded, withBobMemInv] at hpre ⊢
    have hcro : LibsignalCodeRoLoaded lsmpl s0.mem =
        CryptoVerification.LibsignalTripleRatchet.LibsignalCodeRoLoaded lsmpl s0.mem := rfl
    simpa only [hcro] using hpre
  · dsimp only [initializeBobSessionErrOwnedMemInvAtPlacedSpec,
      initializeBobSessionErrOwnedAtInnerPlacedSpec,
      CryptoVerification.LibsignalPublicApi.StoreKit.withLsCodeRoLoaded,
      initializeBobSessionErrOwnedMemInv4KPlacedSpec,
      initializeBobSessionErrOwned4KInnerPlacedSpec,
      withLsCodeRoLoaded, withBobMemInv] at hpost ⊢
    simpa only [initBobErrOwnedAt_eq_kits] using hpost

private def p2ImpossibleEnv : List AllocEvent → Prop :=
  fun evs => evs = [.alloc (VerifiedLibraries.Mallocng.MallocngMaxAllocSize + 1)]

private theorem not_fitsEnv_p2ImpossibleEnv {M : AllocCostModel} {lim : BudgetLimits} {st : M.σ}
    (h : FitsEnv M lim st p2ImpossibleEnv) : False := by
  have hf := (h _ rfl).1.1
  dsimp only [AllocEvent.withinMaxAlloc] at hf
  omega

private theorem p2BaseToVacuousPure4K [LibsignalPlacement] {M : AllocCostModel}
    (P : Primitives) {A : RustCliAllocBudget M} {lim : BudgetLimits} (F : ShaCompress)
    {ext : String → Option (State → State)}
    (h : StageP2BaseCalleesPlaced4K A lim ext) :
    StageP2PureCalleesPlaced4KOfEnv P A lim F
      (fun _ _ => p2ImpossibleEnv) (fun _ => p2ImpossibleEnv) ext where
  publicKeySerialize := h.publicKeySerialize
  promoteMatchingSessionEmpty := h.promoteMatchingSessionEmpty
  curveKeyPairSerde := h.curveKeyPairSerde
  kemKeyPairSerde := h.kemKeyPairSerde
  preKeyRecordKeyPair := h.preKeyRecordKeyPair
  dropSpe2 := h.dropSpe2
  isSameAccount := h.isSameAccount
  initializeBobV1 := by
    intro st Qp s0 inp ikBPk spkBPk argPtr pqskPtr ctSlicePtr ctBufPtr ratchetKeyPairPtr outPtr
      drKey Frame _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hfits
    exact (not_fitsEnv_p2ImpossibleEnv hfits).elim
  initializeBobErr := by
    refine subroutine_ok_of_sepWPp fun ⟨g, st⟩ R s0 _ _ hpre _ => ?_
    dsimp only [initializeBobSessionErr4KPlacedSpec,
      CryptoVerification.LibsignalTripleRatchet.withLsCodeRoLoaded] at hpre
    rw [sepConj_assoc, sepConj_left_comm, satisfies_pure_sepConj] at hpre
    rcases hpre with ⟨_, hpre⟩
    dsimp only [initializeBobSessionErr4KInnerPlacedSpec] at hpre
    simp only [sepConj_assoc, satisfies_pure_sepConj] at hpre
    rcases hpre.1 with ⟨_, _, _, _, _, _, _, _, _, _, hfits⟩
    exact (not_fitsEnv_p2ImpossibleEnv hfits).elim
  promoteStateEmpty := h.promoteStateEmpty
  dropProcessPrekeyImplState1 := h.dropProcessPrekeyImplState1
  dropSessionStructure3 := h.dropSessionStructure3

/-- `KeepsFrozen`-invariant (`Φ : Memory → Prop`) continuation telescope `Prop` for placed Over-path
Stage P2, parameterized by `BobV1Env`, `AcceptErrEnv`, and `PromEnv`. -/
abbrev stageP2OverV1KitsMemInvAtPlacedOfEnvProp [LibsignalPlacement] {M : AllocCostModel}
    (Φ : Memory → Prop)
    (P : Primitives) (A : RustCliAllocBudget M) (lim : BudgetLimits) (F : ShaCompress)
    (BobV1Env : AcceptKeysInput → DRKey → List AllocEvent → Prop)
    (AcceptErrEnv : AcceptKeysInput → List AllocEvent → Prop)
    (PromEnv : SessionGhost → Session (List (BitVec 8)) → List AllocEvent → Prop)
    (ext : String → Option (State → State))
    {ikit : IdentityStoreSpec A.repAlloc 0#64}
    (skit : IdentitySelfStoreSpec ikit) (senv : IdentitySelfStoreBudgetEnv skit)
    (spkKit : SignedPreKeyStoreSpec A.repAlloc 0#64) (spkEnv : SignedPreKeyStoreBudgetEnv spkKit)
    (kpkKit : KyberPreKeyStoreSpec A.repAlloc 0#64) (kpkEnv : KyberPreKeyStoreBudgetEnv kpkKit)
    (pkKit : PreKeyStoreSpec A.repAlloc 0#64) (pkEnv : PreKeyStoreBudgetEnv pkKit)
    (stk : Nat) : Prop :=
  ∀ {st : M.σ} {Qp : State → SepProp → Prop}
    (s0 s : State) (Frame : SepProp) (Q : State → SepProp → Prop)
    (sp fp coroPtr ctxPtr outPtr msgPtr ctBufPtr remoteAddrPtr localAddrPtr
     idStorePtr preKeyStorePtr spkStorePtr kyberStorePtr
     v_330 v_388 u_488 u_80 u_88 u_90 u_a8 u_b8 u_d0 : BitVec 64)
    (hdr : HandshakeHdr) (ikBSk ikBPk : SignalPqxdh.Bytes)
    (msgVerByte b_2c0 b_390 b_4b0 b_4f1 b_4f2 : BitVec 8)
    (opkIdWord kyberPreKeyId remoteRegId signedPreKeyId : BitVec 32)
    (stSpk : spkKit.SpkState) (stKpk : kpkKit.KpkState)
    (stPk : pkKit.PkState) (stId : ikit.IdState)
    (gMe gPeer : AddrGhost)
    (g : RecordGhost) (recG : SessionGhost) (sess : Session (List (BitVec 8))),
    PromoteMatchingMissAtPlacedProp A.repAlloc ext coroPtr g recG sess 4#8
      (5#8 :: bytesToBv8 hdr.ekAPk) →
    PromoteOverAtPlacedWithEnvProp M A lim PromEnv ext coroPtr g recG sess →
    FitsEnv M lim st
      (P2OverSub1To4Env spkKit.getBoxSize (spkEnv.getPollEnv stSpk signedPreKeyId)
        kpkKit.getBoxSize (kpkEnv.getPollEnv stKpk kyberPreKeyId)
        pkKit.getBoxSize (pkEnv.getPollEnv stPk) skit.kpBoxSize (hdrOpkIdBv? hdr)) →
    (∀ evs14 : List AllocEvent,
      P2OverSub1To4OkEnv spkKit.getBoxSize (spkEnv.getPollEnv stSpk signedPreKeyId)
        kpkKit.getBoxSize (kpkEnv.getPollEnv stKpk kyberPreKeyId)
        pkKit.getBoxSize (pkEnv.getPollEnv stPk) skit.kpBoxSize (hdrOpkIdBv? hdr) evs14 →
      FitsEnv M lim (M.stepEvents evs14 st) (SeqEnv (senv.kpPollEnv stId) FreeOnlyEvs)) →
    (∀ (spkRec : SignedPreKeyRecord) (spkPubBytes spkPrivBytes : List (BitVec 8))
        (kpkRec : KyberPreKeyRecord) (kyberPubBytes kyberPrivBytes : List (BitVec 8))
        (wOpk : OpkOkWitness (hdrOpkIdBv? hdr)) (opkPkBytes opkSkBytes : List (BitVec 8))
        (kp : IdentityKeyPair) (drKey : DRKey) (evs14 evsKp : List AllocEvent),
      spkKit.getRel stSpk signedPreKeyId (.ok spkRec) → spkKit.RecOk spkRec →
      spkPubBytes.length = 32 → spkPrivBytes.length = 32 →
      spkRec.signedPreKey.publicKey = 5#8 :: spkPubBytes →
      spkRec.signedPreKey.privateKey = spkPrivBytes →
      kpkKit.getRel stKpk kyberPreKeyId (.ok kpkRec) → kpkKit.RecOk kpkRec →
      kyberPubBytes.length = 1568 → kyberPrivBytes.length = 3168 →
      kpkRec.signedPreKey.publicKey = 8#8 :: kyberPubBytes →
      kpkRec.signedPreKey.privateKey = 8#8 :: kyberPrivBytes →
      opkOkRel pkKit stPk (hdrOpkIdBv? hdr) wOpk →
      opkPkBytes.length = 32 → opkSkBytes.length = 32 →
      opkOkKeyBytes (hdrOpkIdBv? hdr) wOpk opkPkBytes opkSkBytes →
      skit.kpRel stId (.ok kp) →
      acceptKeys P
        (mkP2AcceptKeysInput hdr ikBSk ikBPk spkPubBytes spkPrivBytes
          kyberPubBytes kyberPrivBytes opkSkBytes) = some drKey →
      P2OverSub1To4OkEnv spkKit.getBoxSize (spkEnv.getPollEnv stSpk signedPreKeyId)
        kpkKit.getBoxSize (kpkEnv.getPollEnv stKpk kyberPreKeyId)
        pkKit.getBoxSize (pkEnv.getPollEnv stPk) skit.kpBoxSize (hdrOpkIdBv? hdr) evs14 →
      senv.kpPollEnv stId evsKp →
      FitsEnv M lim
        (M.stepEvents (evs14 ++ evsKp ++ rustDeallocEvents skit.kpBoxSize 8) st)
        (SeqEnv
          (BobV1Env
            (mkP2AcceptKeysInput hdr ikBSk ikBPk spkPubBytes spkPrivBytes
              kyberPubBytes kyberPrivBytes opkSkBytes) drKey)
          (P2OverSub6EnvOf skit.regIdBoxSize (senv.regIdPollEnv stId)
            (P2OverSub6TailEnvOf PromEnv skit.regIdBoxSize recG sess)))) →
    (∀ (spkRec : SignedPreKeyRecord) (spkPubBytes spkPrivBytes : List (BitVec 8))
        (kpkRec : KyberPreKeyRecord) (kyberPubBytes kyberPrivBytes : List (BitVec 8))
        (wOpk : OpkOkWitness (hdrOpkIdBv? hdr)) (opkPkBytes opkSkBytes : List (BitVec 8))
        (kp : IdentityKeyPair) (evs14 evsKp : List AllocEvent),
      spkKit.getRel stSpk signedPreKeyId (.ok spkRec) → spkKit.RecOk spkRec →
      spkPubBytes.length = 32 → spkPrivBytes.length = 32 →
      spkRec.signedPreKey.publicKey = 5#8 :: spkPubBytes →
      spkRec.signedPreKey.privateKey = spkPrivBytes →
      kpkKit.getRel stKpk kyberPreKeyId (.ok kpkRec) → kpkKit.RecOk kpkRec →
      kyberPubBytes.length = 1568 → kyberPrivBytes.length = 3168 →
      kpkRec.signedPreKey.publicKey = 8#8 :: kyberPubBytes →
      kpkRec.signedPreKey.privateKey = 8#8 :: kyberPrivBytes →
      opkOkRel pkKit stPk (hdrOpkIdBv? hdr) wOpk →
      opkPkBytes.length = 32 → opkSkBytes.length = 32 →
      opkOkKeyBytes (hdrOpkIdBv? hdr) wOpk opkPkBytes opkSkBytes →
      skit.kpRel stId (.ok kp) →
      acceptKeys P
        (mkP2AcceptKeysInput hdr ikBSk ikBPk spkPubBytes spkPrivBytes
          kyberPubBytes kyberPrivBytes opkSkBytes) = none →
      P2OverSub1To4OkEnv spkKit.getBoxSize (spkEnv.getPollEnv stSpk signedPreKeyId)
        kpkKit.getBoxSize (kpkEnv.getPollEnv stKpk kyberPreKeyId)
        pkKit.getBoxSize (pkEnv.getPollEnv stPk) skit.kpBoxSize (hdrOpkIdBv? hdr) evs14 →
      senv.kpPollEnv stId evsKp →
      FitsEnv M lim
        (M.stepEvents (evs14 ++ evsKp ++ rustDeallocEvents skit.kpBoxSize 8) st)
        (SeqEnv
          (AcceptErrEnv
            (mkP2AcceptKeysInput hdr ikBSk ikBPk spkPubBytes spkPrivBytes
              kyberPubBytes kyberPrivBytes opkSkBytes))
          FreeOnlyEvs)) →
    ctBufPtr ≠ 0#64 →
    sp - 576#64 ≠ 0#64 →
    stk ≤ sp.toNat →
    (hikBSk_len : ikBSk.length = 32) → (hikBPk_len : ikBPk.length = 32) →
    (hikAPk_len : hdr.ikAPk.length = 32) → (hekAPk_len : hdr.ekAPk.length = 32) →
    (hkemCt_len : hdr.kemCt.length = 1568) →
    Φ s.mem →
    FsAt (stageP2EnvOk spkKit kpkKit pkKit ikit)
      (stageP2Quiet spkKit kpkKit pkKit skit) (stageP1ProgPlaced ext) s →
    spkKit.idOk signedPreKeyId →
    (∀ r : SignedPreKeyRecord, spkKit.getRel stSpk signedPreKeyId (.ok r) →
      spkKit.RecOk r →
      ∃ spkPubBytes spkPrivBytes : List (BitVec 8),
        spkPubBytes.length = 32 ∧ spkPrivBytes.length = 32 ∧
        r.signedPreKey.publicKey = 5#8 :: spkPubBytes ∧ r.signedPreKey.privateKey = spkPrivBytes) →
    kpkKit.getIdOk kyberPreKeyId →
    (∀ r : KyberPreKeyRecord, kpkKit.getRel stKpk kyberPreKeyId (.ok r) →
      kpkKit.RecOk r →
      ∃ kyberPubBytes kyberPrivBytes : List (BitVec 8),
        kyberPubBytes.length = 1568 ∧ kyberPrivBytes.length = 3168 ∧
        r.signedPreKey.publicKey = 8#8 :: kyberPubBytes ∧
        r.signedPreKey.privateKey = 8#8 :: kyberPrivBytes) →
    (∀ id : BitVec 32, hdrOpkIdBv? hdr = some id → opkIdWord = id) →
    (∀ id : BitVec 32, hdrOpkIdBv? hdr = some id → pkKit.getIdOk id) →
    (∀ (id : BitVec 32) (r : PreKeyRecord), hdrOpkIdBv? hdr = some id →
      pkKit.getRel stPk id (.ok r) → pkKit.RecOk r →
      ∃ opkPubBytes opkPrivBytes : List (BitVec 8),
        opkPubBytes.length = 32 ∧ opkPrivBytes.length = 32 ∧
        r.preKey.publicKey = 5#8 :: opkPubBytes ∧ r.preKey.privateKey = opkPrivBytes) →
    (∀ kp : IdentityKeyPair, skit.kpRel stId (.ok kp) →
      kp.privateKey.bytes.toList = bytesToBv8 ikBSk) →
    (∀ kp : IdentityKeyPair, skit.kpRel stId (.ok kp) →
      kp.identityKey.publicKey.bytes.toList = bytesToBv8 ikBPk) →
    (bytesToBv8 ikBPk ≠ bytesToBv8 hdr.ikAPk ∨
      DistinctSid uuidTryParse gMe.name.bytes gPeer.name.bytes) →
    s.pc = stageP1EntryPlaced + 0x868#64 →
    s.status = .Running → s.sp = sp →
    (sp &&& 15#64 == 0#64) = true →
    s0.trace <+: s.trace →
    calleeSavedVRegs s = calleeSavedVRegs s0 →
    s.readReg64 .x8 = kyberStorePtr → s.readReg64 .x9 = msgPtr →
    s.readReg64 .x10 = kpkKit.kpk_vt → s.readReg64 .x11 = preKeyStorePtr →
    s.readReg64 .x12 = remoteAddrPtr → s.readReg64 .x13 = pkKit.pk_vt →
    s.readReg64 .x14 = localAddrPtr → s.readReg64 .x15 = idStorePtr →
    s.readReg64 .x16 = ikit.id_vt → s.readReg64 .x19 = coroPtr →
    s.readReg64 .x22 = spkStorePtr → s.readReg64 .x23 = coroPtr + 0xe0#64 →
    s.readReg64 .x24 = spkKit.spk_vt → s.readReg64 .x29 = fp →
    (∀ (e : spkKit.GetErr) (sf : State) (P_f : SepProp) (evs : List AllocEvent),
      spkKit.getRel stSpk signedPreKeyId (.error e) →
      P2OverSub1To3Arm1Env spkKit.getBoxSize (spkEnv.getPollEnv stSpk signedPreKeyId) evs →
      sf.pc = s0.readReg64 .x30 → sf.status = .Running →
      sf.trace = s.trace ++ spkKit.getEvs signedPreKeyId (.error e) →
      sf.sp = sp + 0xcd0#64 → ClosureCalleeSaved s0 sf →
      calleeSavedVRegs sf = calleeSavedVRegs s0 → LibsignalCodeRoLoaded lsmpl sf.mem →
      (P_f ⊢
        speErrAt spkKit.getErr outPtr e ∗
        spkKit.storeAt spkStorePtr (spkKit.getUpdate stSpk signedPreKeyId (.error e)) ∗
        kpkKit.storeAt kyberStorePtr stKpk ∗
        pkKit.storeAt preKeyStorePtr stPk ∗
        ikit.identityAt idStorePtr stId ∗
        p2ErrFrameAtPlaced A lim (M.stepEvents evs st) s0 sf
          sp fp coroPtr msgPtr ctBufPtr remoteAddrPtr localAddrPtr
          idStorePtr ikit.id_vt preKeyStorePtr pkKit.pk_vt kyberStorePtr kpkKit.kpk_vt
          v_330 v_388 hdr msgVerByte opkIdWord kyberPreKeyId remoteRegId signedPreKeyId
          gMe gPeer stk Frame) →
      Q sf P_f) →
    (∀ (spkRec : SignedPreKeyRecord) (e : kpkKit.GetErr) (sf : State) (P_f : SepProp)
        (evs : List AllocEvent),
      spkKit.getRel stSpk signedPreKeyId (.ok spkRec) → spkKit.RecOk spkRec →
      kpkKit.getRel stKpk kyberPreKeyId (.error e) →
      P2OverSub1To3Arm2Env spkKit.getBoxSize (spkEnv.getPollEnv stSpk signedPreKeyId)
        kpkKit.getBoxSize (kpkEnv.getPollEnv stKpk kyberPreKeyId) evs →
      sf.pc = s0.readReg64 .x30 → sf.status = .Running →
      sf.trace = s.trace ++ spkKit.getEvs signedPreKeyId (.ok spkRec) ++
        kpkKit.getEvs kyberPreKeyId (.error e) →
      sf.sp = sp + 0xcd0#64 → ClosureCalleeSaved s0 sf →
      calleeSavedVRegs sf = calleeSavedVRegs s0 → LibsignalCodeRoLoaded lsmpl sf.mem →
      (P_f ⊢
        speErrAt kpkKit.getErr outPtr e ∗
        spkKit.storeAt spkStorePtr (spkKit.getUpdate stSpk signedPreKeyId (.ok spkRec)) ∗
        kpkKit.storeAt kyberStorePtr (kpkKit.getUpdate stKpk kyberPreKeyId (.error e)) ∗
        pkKit.storeAt preKeyStorePtr stPk ∗
        ikit.identityAt idStorePtr stId ∗
        p2ErrFrameAtPlaced A lim (M.stepEvents evs st) s0 sf
          sp fp coroPtr msgPtr ctBufPtr remoteAddrPtr localAddrPtr
          idStorePtr ikit.id_vt preKeyStorePtr pkKit.pk_vt kyberStorePtr kpkKit.kpk_vt
          v_330 v_388 hdr msgVerByte opkIdWord kyberPreKeyId remoteRegId signedPreKeyId
          gMe gPeer stk Frame) →
      Q sf P_f) →
    (∀ (spkRec : SignedPreKeyRecord) (kpkRec : KyberPreKeyRecord)
        (opkId : BitVec 32) (e : pkKit.GetErr) (sf : State) (P_f : SepProp)
        (evs : List AllocEvent),
      spkKit.getRel stSpk signedPreKeyId (.ok spkRec) → spkKit.RecOk spkRec →
      kpkKit.getRel stKpk kyberPreKeyId (.ok kpkRec) → kpkKit.RecOk kpkRec →
      hdrOpkIdBv? hdr = some opkId → pkKit.getRel stPk opkId (.error e) →
      P2OverSub1To4Arm3Env spkKit.getBoxSize (spkEnv.getPollEnv stSpk signedPreKeyId)
        kpkKit.getBoxSize (kpkEnv.getPollEnv stKpk kyberPreKeyId)
        pkKit.getBoxSize (pkEnv.getPollEnv stPk) (hdrOpkIdBv? hdr) evs →
      sf.pc = s0.readReg64 .x30 → sf.status = .Running →
      sf.trace = s.trace ++ spkKit.getEvs signedPreKeyId (.ok spkRec) ++
        kpkKit.getEvs kyberPreKeyId (.ok kpkRec) ++ pkKit.getEvs opkId (.error e) →
      sf.sp = sp + 0xcd0#64 → ClosureCalleeSaved s0 sf →
      calleeSavedVRegs sf = calleeSavedVRegs s0 → LibsignalCodeRoLoaded lsmpl sf.mem →
      (P_f ⊢
        speErrAt pkKit.getErr outPtr e ∗
        spkKit.storeAt spkStorePtr (spkKit.getUpdate stSpk signedPreKeyId (.ok spkRec)) ∗
        kpkKit.storeAt kyberStorePtr (kpkKit.getUpdate stKpk kyberPreKeyId (.ok kpkRec)) ∗
        pkKit.storeAt preKeyStorePtr (pkKit.getUpdate stPk opkId (.error e)) ∗
        ikit.identityAt idStorePtr stId ∗
        p2ErrFrameAtPlaced A lim (M.stepEvents evs st) s0 sf
          sp fp coroPtr msgPtr ctBufPtr remoteAddrPtr localAddrPtr
          idStorePtr ikit.id_vt preKeyStorePtr pkKit.pk_vt kyberStorePtr kpkKit.kpk_vt
          v_330 v_388 hdr msgVerByte opkIdWord kyberPreKeyId remoteRegId signedPreKeyId
          gMe gPeer stk Frame) →
      Q sf P_f) →
    (∀ (spkRec : SignedPreKeyRecord) (kpkRec : KyberPreKeyRecord)
        (wOpk : OpkOkWitness (hdrOpkIdBv? hdr)) (e : skit.KpErr) (sf : State) (P_f : SepProp)
        (evs : List AllocEvent),
      spkKit.getRel stSpk signedPreKeyId (.ok spkRec) → spkKit.RecOk spkRec →
      kpkKit.getRel stKpk kyberPreKeyId (.ok kpkRec) → kpkKit.RecOk kpkRec →
      opkOkRel pkKit stPk (hdrOpkIdBv? hdr) wOpk →
      skit.kpRel stId (.error e) →
      P2OverV1Arm4Env spkKit.getBoxSize (spkEnv.getPollEnv stSpk signedPreKeyId)
        kpkKit.getBoxSize (kpkEnv.getPollEnv stKpk kyberPreKeyId)
        pkKit.getBoxSize (pkEnv.getPollEnv stPk) skit.kpBoxSize (hdrOpkIdBv? hdr)
        (senv.kpPollEnv stId) evs →
      sf.pc = s0.readReg64 .x30 → sf.status = .Running →
      sf.trace = s.trace ++ spkKit.getEvs signedPreKeyId (.ok spkRec) ++
        kpkKit.getEvs kyberPreKeyId (.ok kpkRec) ++ opkOkEvs pkKit (hdrOpkIdBv? hdr) wOpk ++
        skit.kpEvs (.error e) →
      sf.sp = sp + 0xcd0#64 → ClosureCalleeSaved s0 sf →
      calleeSavedVRegs sf = calleeSavedVRegs s0 → LibsignalCodeRoLoaded lsmpl sf.mem →
      (P_f ⊢
        speErrAt skit.kpErr outPtr e ∗
        spkKit.storeAt spkStorePtr (spkKit.getUpdate stSpk signedPreKeyId (.ok spkRec)) ∗
        kpkKit.storeAt kyberStorePtr (kpkKit.getUpdate stKpk kyberPreKeyId (.ok kpkRec)) ∗
        pkKit.storeAt preKeyStorePtr (opkOkUpdate pkKit stPk (hdrOpkIdBv? hdr) wOpk) ∗
        ikit.identityAt idStorePtr stId ∗
        p2ErrFrameAtPlaced A lim (M.stepEvents evs st) s0 sf
          sp fp coroPtr msgPtr ctBufPtr remoteAddrPtr localAddrPtr
          idStorePtr ikit.id_vt preKeyStorePtr pkKit.pk_vt kyberStorePtr kpkKit.kpk_vt
          v_330 v_388 hdr msgVerByte opkIdWord kyberPreKeyId remoteRegId signedPreKeyId
          gMe gPeer stk Frame) →
      Q sf P_f) →
    (∀ (spkRec : SignedPreKeyRecord) (spkPubBytes spkPrivBytes : List (BitVec 8))
        (kpkRec : KyberPreKeyRecord) (kyberPubBytes kyberPrivBytes : List (BitVec 8))
        (wOpk : OpkOkWitness (hdrOpkIdBv? hdr)) (opkPkBytes opkSkBytes : List (BitVec 8))
        (kp : IdentityKeyPair) (errTag w2 w3 w4 w5 w6 : BitVec 64)
        (sf : State) (P_f : SepProp) (evs : List AllocEvent),
      spkKit.getRel stSpk signedPreKeyId (.ok spkRec) → spkKit.RecOk spkRec →
      spkPubBytes.length = 32 → spkPrivBytes.length = 32 →
      spkRec.signedPreKey.publicKey = 5#8 :: spkPubBytes →
      spkRec.signedPreKey.privateKey = spkPrivBytes →
      kpkKit.getRel stKpk kyberPreKeyId (.ok kpkRec) → kpkKit.RecOk kpkRec →
      kyberPubBytes.length = 1568 → kyberPrivBytes.length = 3168 →
      kpkRec.signedPreKey.publicKey = 8#8 :: kyberPubBytes →
      kpkRec.signedPreKey.privateKey = 8#8 :: kyberPrivBytes →
      opkOkRel pkKit stPk (hdrOpkIdBv? hdr) wOpk →
      opkPkBytes.length = 32 → opkSkBytes.length = 32 →
      opkOkKeyBytes (hdrOpkIdBv? hdr) wOpk opkPkBytes opkSkBytes →
      skit.kpRel stId (.ok kp) →
      acceptKeys P
        (mkP2AcceptKeysInput hdr ikBSk ikBPk spkPubBytes spkPrivBytes
          kyberPubBytes kyberPrivBytes opkSkBytes) = none →
      P2OverV1Arm5EnvOfAcceptErr spkKit.getBoxSize (spkEnv.getPollEnv stSpk signedPreKeyId)
        kpkKit.getBoxSize (kpkEnv.getPollEnv stKpk kyberPreKeyId)
        pkKit.getBoxSize (pkEnv.getPollEnv stPk) skit.kpBoxSize (hdrOpkIdBv? hdr)
        (senv.kpPollEnv stId)
        (AcceptErrEnv
          (mkP2AcceptKeysInput hdr ikBSk ikBPk spkPubBytes spkPrivBytes
            kyberPubBytes kyberPrivBytes opkSkBytes))
        evs →
      errTag ≠ 0xfffffffffffffffe#64 → errTag ≠ 0xfffffffffffffffd#64 →
      sf.pc = s0.readReg64 .x30 → sf.status = .Running →
      sf.trace = s.trace ++ spkKit.getEvs signedPreKeyId (.ok spkRec) ++
        kpkKit.getEvs kyberPreKeyId (.ok kpkRec) ++ opkOkEvs pkKit (hdrOpkIdBv? hdr) wOpk ++
        skit.kpEvs (.ok kp) →
      sf.sp = sp + 0xcd0#64 → ClosureCalleeSaved s0 sf →
      calleeSavedVRegs sf = calleeSavedVRegs s0 → LibsignalCodeRoLoaded lsmpl sf.mem →
      (P_f ⊢
        speWordsAt outPtr errTag w2 w3 w4 w5 w6 ∗
        pqxdhAcceptErrPayloadAt A.repAlloc errTag w2 w3 w4 ∗
        spkKit.storeAt spkStorePtr (spkKit.getUpdate stSpk signedPreKeyId (.ok spkRec)) ∗
        kpkKit.storeAt kyberStorePtr (kpkKit.getUpdate stKpk kyberPreKeyId (.ok kpkRec)) ∗
        pkKit.storeAt preKeyStorePtr (opkOkUpdate pkKit stPk (hdrOpkIdBv? hdr) wOpk) ∗
        ikit.identityAt idStorePtr stId ∗
        p2ErrFrameAtPlaced A lim (M.stepEvents evs st) s0 sf
          sp fp coroPtr msgPtr ctBufPtr remoteAddrPtr localAddrPtr
          idStorePtr ikit.id_vt preKeyStorePtr pkKit.pk_vt kyberStorePtr kpkKit.kpk_vt
          v_330 v_388 hdr msgVerByte opkIdWord kyberPreKeyId remoteRegId signedPreKeyId
          gMe gPeer stk Frame) →
      Q sf P_f) →
    (∀ (spkRec : SignedPreKeyRecord) (spkPubBytes spkPrivBytes : List (BitVec 8))
        (kpkRec : KyberPreKeyRecord) (kyberPubBytes kyberPrivBytes : List (BitVec 8))
        (wOpk : OpkOkWitness (hdrOpkIdBv? hdr)) (opkPkBytes opkSkBytes : List (BitVec 8))
        (kp : IdentityKeyPair) (drKey : DRKey) (e : skit.RegIdErr)
        (sf : State) (P_f : SepProp) (evs : List AllocEvent),
      spkKit.getRel stSpk signedPreKeyId (.ok spkRec) → spkKit.RecOk spkRec →
      spkPubBytes.length = 32 → spkPrivBytes.length = 32 →
      spkRec.signedPreKey.publicKey = 5#8 :: spkPubBytes →
      spkRec.signedPreKey.privateKey = spkPrivBytes →
      kpkKit.getRel stKpk kyberPreKeyId (.ok kpkRec) → kpkKit.RecOk kpkRec →
      kyberPubBytes.length = 1568 → kyberPrivBytes.length = 3168 →
      kpkRec.signedPreKey.publicKey = 8#8 :: kyberPubBytes →
      kpkRec.signedPreKey.privateKey = 8#8 :: kyberPrivBytes →
      opkOkRel pkKit stPk (hdrOpkIdBv? hdr) wOpk →
      opkPkBytes.length = 32 → opkSkBytes.length = 32 →
      opkOkKeyBytes (hdrOpkIdBv? hdr) wOpk opkPkBytes opkSkBytes →
      skit.kpRel stId (.ok kp) →
      acceptKeys P
        (mkP2AcceptKeysInput hdr ikBSk ikBPk spkPubBytes spkPrivBytes
          kyberPubBytes kyberPrivBytes opkSkBytes) = some drKey →
      skit.regIdRel stId (.error e) →
      P2OverV1Arm6EnvOfBob spkKit.getBoxSize (spkEnv.getPollEnv stSpk signedPreKeyId)
        kpkKit.getBoxSize (kpkEnv.getPollEnv stKpk kyberPreKeyId)
        pkKit.getBoxSize (pkEnv.getPollEnv stPk) skit.kpBoxSize (hdrOpkIdBv? hdr)
        (senv.kpPollEnv stId)
        (BobV1Env
          (mkP2AcceptKeysInput hdr ikBSk ikBPk spkPubBytes spkPrivBytes
            kyberPubBytes kyberPrivBytes opkSkBytes) drKey)
        skit.regIdBoxSize (senv.regIdPollEnv stId) evs →
      sf.pc = s0.readReg64 .x30 → sf.status = .Running →
      sf.trace = s.trace ++ spkKit.getEvs signedPreKeyId (.ok spkRec) ++
        kpkKit.getEvs kyberPreKeyId (.ok kpkRec) ++ opkOkEvs pkKit (hdrOpkIdBv? hdr) wOpk ++
        skit.kpEvs (.ok kp) ++ skit.regIdEvs (.error e) →
      sf.sp = sp + 0xcd0#64 → ClosureCalleeSaved s0 sf →
      calleeSavedVRegs sf = calleeSavedVRegs s0 → LibsignalCodeRoLoaded lsmpl sf.mem →
      (P_f ⊢
        speErrAt skit.regIdErr outPtr e ∗
        spkKit.storeAt spkStorePtr (spkKit.getUpdate stSpk signedPreKeyId (.ok spkRec)) ∗
        kpkKit.storeAt kyberStorePtr (kpkKit.getUpdate stKpk kyberPreKeyId (.ok kpkRec)) ∗
        pkKit.storeAt preKeyStorePtr (opkOkUpdate pkKit stPk (hdrOpkIdBv? hdr) wOpk) ∗
        ikit.identityAt idStorePtr stId ∗
        p2ErrFrameAtPlaced A lim (M.stepEvents evs st) s0 sf
          sp fp coroPtr msgPtr ctBufPtr remoteAddrPtr localAddrPtr
          idStorePtr ikit.id_vt preKeyStorePtr pkKit.pk_vt kyberStorePtr kpkKit.kpk_vt
          v_330 v_388 hdr msgVerByte opkIdWord kyberPreKeyId remoteRegId signedPreKeyId
          gMe gPeer stk Frame) →
      Q sf P_f) →
    (∀ (spkRec : SignedPreKeyRecord) (spkPubBytes spkPrivBytes : List (BitVec 8))
        (kpkRec : KyberPreKeyRecord) (kyberPubBytes kyberPrivBytes : List (BitVec 8))
        (wOpk : OpkOkWitness (hdrOpkIdBv? hdr)) (opkPkBytes opkSkBytes : List (BitVec 8))
        (kp : IdentityKeyPair) (drKey : DRKey) (localRegId : BitVec 32)
        (G_bob : SessionGhost) (sf : State) (evs : List AllocEvent),
      spkKit.getRel stSpk signedPreKeyId (.ok spkRec) → spkKit.RecOk spkRec →
      (hspkPub_len : spkPubBytes.length = 32) → (hspkPriv_len : spkPrivBytes.length = 32) →
      spkRec.signedPreKey.publicKey = 5#8 :: spkPubBytes →
      spkRec.signedPreKey.privateKey = spkPrivBytes →
      kpkKit.getRel stKpk kyberPreKeyId (.ok kpkRec) → kpkKit.RecOk kpkRec →
      kyberPubBytes.length = 1568 → kyberPrivBytes.length = 3168 →
      kpkRec.signedPreKey.publicKey = 8#8 :: kyberPubBytes →
      kpkRec.signedPreKey.privateKey = 8#8 :: kyberPrivBytes →
      opkOkRel pkKit stPk (hdrOpkIdBv? hdr) wOpk →
      opkPkBytes.length = 32 → opkSkBytes.length = 32 →
      opkOkKeyBytes (hdrOpkIdBv? hdr) wOpk opkPkBytes opkSkBytes →
      skit.kpRel stId (.ok kp) →
      acceptKeys P
        (mkP2AcceptKeysInput hdr ikBSk ikBPk spkPubBytes spkPrivBytes
          kyberPubBytes kyberPrivBytes opkSkBytes) = some drKey →
      skit.regIdRel stId (.ok localRegId) →
      P2OverV1OkEnvOfBobAndProm spkKit.getBoxSize (spkEnv.getPollEnv stSpk signedPreKeyId)
        kpkKit.getBoxSize (kpkEnv.getPollEnv stKpk kyberPreKeyId)
        pkKit.getBoxSize (pkEnv.getPollEnv stPk) skit.kpBoxSize (hdrOpkIdBv? hdr)
        (senv.kpPollEnv stId)
        (BobV1Env
          (mkP2AcceptKeysInput hdr ikBSk ikBPk spkPubBytes spkPrivBytes
            kyberPubBytes kyberPrivBytes opkSkBytes) drKey)
        skit.regIdBoxSize (senv.regIdPollEnv stId)
        (P2OverSub6TailEnvOf PromEnv skit.regIdBoxSize recG sess) evs →
      G_bob.pending = none → G_bob.kyber = none →
      G_bob.alice.bytes = bytesToBv8 (encodeEC hdr.ekAPk) →
      G_bob.regIds = unpack32 remoteRegId ++ unpack32 localRegId →
      Steps (stageP1ProgPlaced ext) s sf →
      FsAt (stageP2EnvOk spkKit kpkKit pkKit ikit)
        (stageP2Quiet spkKit kpkKit pkKit skit) (stageP1ProgPlaced ext) sf →
      sf.pc = stageP1EntryPlaced + 0x1778#64 →
      sf.status = .Running → sf.sp = sp →
      sf.trace = s.trace ++ spkKit.getEvs signedPreKeyId (.ok spkRec) ++
        kpkKit.getEvs kyberPreKeyId (.ok kpkRec) ++ opkOkEvs pkKit (hdrOpkIdBv? hdr) wOpk ++
        skit.kpEvs (.ok kp) ++ skit.regIdEvs (.ok localRegId) →
      sf.readReg64 .x8 = coroPtr + 0xe0#64 → sf.readReg64 .x9 = 8#64 →
      sf.readReg64 .x10 = msgVerByte.zeroExtend 64 → sf.readReg64 .x11 = coroPtr + 0xf8#64 →
      sf.readReg64 .x19 = coroPtr → sf.readReg64 .x20 = 0xfffffffffffffffe#64 →
      sf.readReg64 .x22 = (kyberPreKeyId.zeroExtend 64 <<< 32) ||| 1#64 →
      sf.readReg64 .x23 = (opkOptTag32 (hdrOpkIdBv? hdr)).zeroExtend 64 ||| (opkIdWord.zeroExtend 64 <<< 32) →
      sf.readReg64 .x24 = (opkOptTag32 (hdrOpkIdBv? hdr)).zeroExtend 64 ||| (opkIdWord.zeroExtend 64 <<< 32) →
      sf.readReg64 .x25 = sp + 0x210#64 → sf.readReg64 .x26 = v_330 →
      sf.readReg64 .x27 = sp + 0x370#64 → sf.readReg64 .x28 = sp + 0xa90#64 →
      sf.readReg64 .x29 = fp → calleeSavedVRegs sf = calleeSavedVRegs s0 →
      LibsignalCodeRoLoaded lsmpl sf.mem →
      SepWPp (stageP1ProgPlaced ext) (s0.readReg64 .x30) sf
        (p2OverOkPostAtPlaced A lim 0#64 spkKit kpkKit pkKit ikit (M.stepEvents evs st) s0 sf
          sp fp coroPtr ctxPtr outPtr msgPtr ctBufPtr remoteAddrPtr localAddrPtr
          idStorePtr preKeyStorePtr spkStorePtr kyberStorePtr v_330 v_388
          recG sess G_bob
          (p2BobInitSessionV1 ikBPk (toU8 spkPubBytes)
            (mkP2AcceptKeysInput hdr ikBSk ikBPk spkPubBytes spkPrivBytes
              kyberPubBytes kyberPrivBytes opkSkBytes)
            drKey (initialStateValue F (p2BobSpqrParams drKey.pqrKey))
            hikBPk_len hikAPk_len
            (by simp [toU8, hspkPub_len])
            (by simp [mkP2AcceptKeysInput, toU8, clampBv8List_length hspkPriv_len]))
          hdr msgVerByte b_2c0 opkIdWord kyberPreKeyId remoteRegId signedPreKeyId
          (spkKit.getUpdate stSpk signedPreKeyId (.ok spkRec))
          (kpkKit.getUpdate stKpk kyberPreKeyId (.ok kpkRec))
          (opkOkUpdate pkKit stPk (hdrOpkIdBv? hdr) wOpk)
          stId gMe gPeer stk Frame)
        Q Qp) →
    SepWPp (stageP1ProgPlaced ext) (s0.readReg64 .x30) s
      (stageP2OverPreAtPlaced A lim 0#64 spkKit kpkKit pkKit ikit st s0 s
        sp fp coroPtr ctxPtr outPtr msgPtr ctBufPtr remoteAddrPtr localAddrPtr
        idStorePtr preKeyStorePtr spkStorePtr kyberStorePtr
        v_330 v_388 u_488 u_80 u_88 u_90 u_a8 u_b8 u_d0
        hdr msgVerByte b_2c0 b_390 b_4b0 b_4f1 b_4f2
        opkIdWord kyberPreKeyId remoteRegId signedPreKeyId
        stSpk stKpk stPk stId gMe gPeer g recG sess stk Frame)
      Q Qp

abbrev stageP2OverV1KitsMemInvAtPlacedProp [LibsignalPlacement] {M : AllocCostModel}
    (Φ : Memory → Prop)
    (P : Primitives) (A : RustCliAllocBudget M) (lim : BudgetLimits) (F : ShaCompress)
    (AcceptErrEnv : AcceptKeysInput → List AllocEvent → Prop)
    (ext : String → Option (State → State))
    {ikit : IdentityStoreSpec A.repAlloc 0#64}
    (skit : IdentitySelfStoreSpec ikit) (senv : IdentitySelfStoreBudgetEnv skit)
    (spkKit : SignedPreKeyStoreSpec A.repAlloc 0#64) (spkEnv : SignedPreKeyStoreBudgetEnv spkKit)
    (kpkKit : KyberPreKeyStoreSpec A.repAlloc 0#64) (kpkEnv : KyberPreKeyStoreBudgetEnv kpkKit)
    (pkKit : PreKeyStoreSpec A.repAlloc 0#64) (pkEnv : PreKeyStoreBudgetEnv pkKit)
    (stk : Nat) : Prop :=
  stageP2OverV1KitsMemInvAtPlacedOfEnvProp Φ P A lim F (InitializeBobV1OptFieldsEnv P F)
    AcceptErrEnv PromoteOverEnv ext skit senv spkKit spkEnv kpkKit kpkEnv pkKit pkEnv stk

abbrev stageP2OverV1KitsFrozenAtPlacedOfEnvProp [LibsignalPlacement] {M : AllocCostModel}
    (P : Primitives) (A : RustCliAllocBudget M) (lim : BudgetLimits) (F : ShaCompress)
    (BobV1Env : AcceptKeysInput → DRKey → List AllocEvent → Prop)
    (AcceptErrEnv : AcceptKeysInput → List AllocEvent → Prop)
    (PromEnv : SessionGhost → Session (List (BitVec 8)) → List AllocEvent → Prop)
    (ext : String → Option (State → State))
    {ikit : IdentityStoreSpec A.repAlloc 0#64}
    (skit : IdentitySelfStoreSpec ikit) (senv : IdentitySelfStoreBudgetEnv skit)
    (spkKit : SignedPreKeyStoreSpec A.repAlloc 0#64) (spkEnv : SignedPreKeyStoreBudgetEnv spkKit)
    (kpkKit : KyberPreKeyStoreSpec A.repAlloc 0#64) (kpkEnv : KyberPreKeyStoreBudgetEnv kpkKit)
    (pkKit : PreKeyStoreSpec A.repAlloc 0#64) (pkEnv : PreKeyStoreBudgetEnv pkKit)
    (stk : Nat) : Prop :=
  stageP2OverV1KitsMemInvAtPlacedOfEnvProp (LibsignalFrozen lsmpl) P A lim F BobV1Env
    AcceptErrEnv PromEnv ext skit senv spkKit spkEnv kpkKit kpkEnv pkKit pkEnv stk

abbrev stageP2OverV1KitsFrozenAtPlacedProp [LibsignalPlacement] {M : AllocCostModel}
    (P : Primitives) (A : RustCliAllocBudget M) (lim : BudgetLimits) (F : ShaCompress)
    (AcceptErrEnv : AcceptKeysInput → List AllocEvent → Prop)
    (ext : String → Option (State → State))
    {ikit : IdentityStoreSpec A.repAlloc 0#64}
    (skit : IdentitySelfStoreSpec ikit) (senv : IdentitySelfStoreBudgetEnv skit)
    (spkKit : SignedPreKeyStoreSpec A.repAlloc 0#64) (spkEnv : SignedPreKeyStoreBudgetEnv spkKit)
    (kpkKit : KyberPreKeyStoreSpec A.repAlloc 0#64) (kpkEnv : KyberPreKeyStoreBudgetEnv kpkKit)
    (pkKit : PreKeyStoreSpec A.repAlloc 0#64) (pkEnv : PreKeyStoreBudgetEnv pkKit)
    (stk : Nat) : Prop :=
  stageP2OverV1KitsFrozenAtPlacedOfEnvProp P A lim F (InitializeBobV1OptFieldsEnv P F)
    AcceptErrEnv PromoteOverEnv ext skit senv spkKit spkEnv kpkKit kpkEnv pkKit pkEnv stk

set_option maxHeartbeats 1200000 in
/-- `StageP2MemInv`-guarded budget-threaded placed Over-path Stage P2 (`+0x0868 → +0x1778` and error
Arms 1–6). -/
theorem stageP2_over_v1_kits_memInv_at_placed_ofEnv [LibsignalPlacement]
    {Φ : Memory → Prop} (hInv : StageP2MemInv Φ)
    {M : AllocCostModel} {P : Primitives} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {F : ShaCompress} {BobV1Env : AcceptKeysInput → DRKey → List AllocEvent → Prop}
    {AcceptErrEnv : AcceptKeysInput → List AllocEvent → Prop}
    {PromEnv : SessionGhost → Session (List (BitVec 8)) → List AllocEvent → Prop}
    (ext : String → Option (State → State))
    (hWF : StructuralPrims P)
    (hH : StageP2ClosureHooksPlaced A lim ext)
    (hPure : StageP2BaseCalleesPlaced4K A lim ext)
    {sameStk bobErrStk bobV1Stk : Nat}
    (hSameAcct :
      subroutine_ok (stageP1ProgPlaced ext) (lsmpl.base 17)
        (withLsCodeLoaded lsmpl (isSameAccountDistinctAtSpec A.repAlloc uuidTryParse sameStk)))
    (hInitBobErrOwned :
      subroutine_ok (stageP1ProgPlaced ext) (lsmpl.base 75)
        (initializeBobSessionErrOwnedMemInvAtPlacedSpec Φ P A lim AcceptErrEnv bobErrStk))
    (hInitBobV1 : InitializeBobV1MemInvOkAtPlacedOfEnv Φ P A lim F BobV1Env ext bobV1Stk)
    (hsame_le : sameStk ≤ bobV1Stk)
    (herr_le : bobErrStk ≤ bobV1Stk)
    (ikit : IdentityStoreSpec A.repAlloc 0#64) (skit : IdentitySelfStoreSpec ikit)
    (senv : IdentitySelfStoreBudgetEnv skit)
    (hskitVt : IdentitySelfVtablesPlacedOk ikit skit)
    (hskitOk : IdentitySelfStoreKitPlacedOkI A lim ikit skit senv ext)
    (spkKit : SignedPreKeyStoreSpec A.repAlloc 0#64)
    (spkEnv : SignedPreKeyStoreBudgetEnv spkKit)
    (hspkVt : SignedPreKeyVtablesPlacedOk spkKit)
    (hspkOk : SignedPreKeyStoreKitPlacedOk A lim spkKit spkEnv ext)
    (kpkKit : KyberPreKeyStoreSpec A.repAlloc 0#64)
    (kpkEnv : KyberPreKeyStoreBudgetEnv kpkKit)
    (hkpkVt : KyberPreKeyVtablesPlacedOk kpkKit)
    (hkpkOk : KyberPreKeyStoreKitPlacedOk A lim kpkKit kpkEnv ext)
    (pkKit : PreKeyStoreSpec A.repAlloc 0#64)
    (pkEnv : PreKeyStoreBudgetEnv pkKit)
    (hpkVt : PreKeyVtablesPlacedOk pkKit)
    (hpkOk : PreKeyStoreKitPlacedOk A lim pkKit pkEnv ext)
    {v1CallStk : Nat}
    (hv1_p2 : stageP2OverCallStack spkKit kpkKit pkKit skit ≤ v1CallStk)
    (hv1_bob : bobV1Stk ≤ v1CallStk)
    (stk : Nat) (hstk : v1CallStk ≤ stk) :
    stageP2OverV1KitsMemInvAtPlacedOfEnvProp Φ P A lim F BobV1Env AcceptErrEnv PromEnv ext
      skit senv spkKit spkEnv kpkKit kpkEnv pkKit pkEnv stk := by
  intro st Qp
    s0 s Frame Q
    sp fp coroPtr ctxPtr outPtr msgPtr ctBufPtr remoteAddrPtr localAddrPtr
    idStorePtr preKeyStorePtr spkStorePtr kyberStorePtr
    v_330 v_388 u_488 u_80 u_88 u_90 u_a8 u_b8 u_d0
    hdr ikBSk ikBPk
    msgVerByte b_2c0 b_390 b_4b0 b_4f1 b_4f2
    opkIdWord kyberPreKeyId remoteRegId signedPreKeyId
    stSpk stKpk stPk stId
    gMe gPeer g recG sess
    hPromMiss hPromoteOver
    hfits14 hfitsKp hfitsBob hfitsAccErr
    hctBuf_nz hpqr_ne hstk_lt
    hikBSk_len hikBPk_len hikAPk_len hekAPk_len hkemCt_len
    hInv_s hfs
    hid_spk hspk_wf hid_kpk hkpk_wf hopk_word hid_pk hpk_wf
    hkp_sk hkp_pk hneq
    hpc hrun hsp_eq hsp_align htr hvregs
    hx8 hx9 hx10 hx11 hx12 hx13 hx14 hx15 hx16 hx19 hx22 hx23 hx24 hx29
    hErrSpk hErrKpk hErrPk hErrKp hErrBob hErrRegId hOk
  have hCode : LibsignalCodeRoLoaded lsmpl s.mem := hInv.toCodeRo hInv_s
  have hPureVac := p2BaseToVacuousPure4K P F hPure
  have hstk_overCall : stageP2OverCallStack spkKit kpkKit pkKit skit ≤ stk :=
    Nat.le_trans hv1_p2 hstk
  have hstk_overP2 : stageP2OverCallStack4K spkKit kpkKit pkKit skit ≤ stk :=
    (stageP2OverCallStack4K_eq spkKit kpkKit pkKit skit).symm ▸ hstk_overCall
  have hstk_baseP2 : stageP2CallStack spkKit kpkKit pkKit skit ≤ stk :=
    Nat.le_trans (p2_over_baseCall_le_callStack spkKit kpkKit pkKit skit) hstk_overCall
  have hstk_overPure : stageP2OverPureAndErrStack ≤ stk :=
    Nat.le_trans (p2_over_pure_le_callStack spkKit kpkKit pkKit skit) hstk_overCall
  have hstk_bob : bobV1Stk ≤ stk :=
    Nat.le_trans hv1_bob hstk
  have hstk_sub56 : stageP2Sub56Stack skit ≤ stk :=
    Nat.le_trans (p2_sub56_le_stageP2 spkKit kpkKit pkKit skit) hstk_baseP2
  have hstk_drop : dropSessionStructureLocal2Stack ≤ stk :=
    Nat.le_trans p2_over_dropSS3_le_overPure hstk_overPure
  have hkem_pos : 0 < (bytesToBv8 hdr.kemCt).length := by
    simp [bytesToBv8, hkemCt_len]
  let baseKey : PublicKey := ⟨⟨bytesToBv8 hdr.ekAPk, by simpa [bytesToBv8] using hekAPk_len⟩⟩
  have hPromMiss_bk :
      PromoteMatchingMissAtPlacedProp A.repAlloc ext coroPtr g recG sess 4#8 baseKey.serialize :=
    hPromMiss
  refine p2_mono_pre
    (p2_over_entry_to_sub1To4_placed A lim st s0 s spkKit kpkKit pkKit ikit
      sp fp coroPtr ctxPtr outPtr msgPtr ctBufPtr remoteAddrPtr localAddrPtr
      idStorePtr preKeyStorePtr spkStorePtr kyberStorePtr
      v_330 v_388 u_488 u_80 u_88 u_90 u_a8 u_b8 u_d0
      hdr msgVerByte b_2c0 b_390 b_4b0 b_4f1 b_4f2
      opkIdWord kyberPreKeyId remoteRegId signedPreKeyId
      stSpk stKpk stPk stId gMe gPeer g recG sess stk Frame) ?_
  refine stageP2_over_sub1_to_4_kits_ext_placed_ofEnv ext hH hPureVac
    ikit skit senv hskitVt hskitOk spkKit spkEnv hspkVt hspkOk
    kpkKit kpkEnv hkpkVt hkpkOk pkKit pkEnv hpkVt hpkOk
    stk hstk_overP2 st s0 s
    (p2Sub1To4Frame A.repAlloc ikit sp fp coroPtr msgPtr ctBufPtr remoteAddrPtr localAddrPtr
      idStorePtr v_330 v_388 u_80 u_88 stId hdr msgVerByte remoteRegId gMe gPeer Frame)
    Q sp coroPtr ctxPtr outPtr msgPtr remoteAddrPtr localAddrPtr
    idStorePtr preKeyStorePtr spkStorePtr kyberStorePtr ctBufPtr
    (coroPtr + 0x390#64) u_90 u_a8 u_b8 u_d0 u_488 hstk_lt
    g recG sess baseKey signedPreKeyId kyberPreKeyId opkIdWord (hdrOpkIdBv? hdr)
    stSpk stKpk stPk b_2c0 b_390 b_4b0 b_4f1 b_4f2
    hfits14 hPromMiss_bk hctBuf_nz hCode hfs
    hid_spk hspk_wf hid_kpk hkpk_wf hopk_word hid_pk hpk_wf
    hpc hrun hsp_eq hsp_align htr hvregs
    hx8 hx9 hx10 hx11 hx12 hx13 hx14 hx15 hx16 hx19 hx22 hx23 hx24
    (fun e spkFutPtr evs sf P_f hrel hevs hpcf hrunf htrf hspf hcsf hvregsf hCodef hent =>
      hErrSpk e sf P_f evs hrel hevs hpcf hrunf htrf hspf hcsf hvregsf hCodef
        (Entails.trans hent
          (p2_v1_arm1_entails_placed A lim (M.stepEvents evs st) spkKit kpkKit pkKit ikit s0 sf
            sp fp coroPtr ctxPtr outPtr msgPtr ctBufPtr remoteAddrPtr localAddrPtr
            idStorePtr preKeyStorePtr spkStorePtr kyberStorePtr
            (coroPtr + 0x390#64) v_330 v_388 u_488 u_80 u_88 spkFutPtr
            b_4b0 msgVerByte opkIdWord kyberPreKeyId remoteRegId signedPreKeyId hdr
            stSpk stKpk stPk stId e gMe gPeer stk Frame)))
    (fun spkRec spkPubBytes spkPrivBytes e kyberFutPtr evs sf P_f
        hspk_rel hspk_ok hpub_len hpriv_len _ _ hkpk_rel hevs
        hpcf hrunf htrf hspf hcsf hvregsf hCodef hent =>
      hErrKpk spkRec e sf P_f evs hspk_rel hspk_ok hkpk_rel hevs
        hpcf hrunf htrf hspf hcsf hvregsf hCodef
        (Entails.trans hent
          (p2_v1_arm2_entails_placed A lim (M.stepEvents evs st) spkKit kpkKit pkKit ikit s0 sf
            sp fp coroPtr ctxPtr outPtr msgPtr ctBufPtr remoteAddrPtr localAddrPtr
            idStorePtr preKeyStorePtr spkStorePtr kyberStorePtr
            (coroPtr + 0x390#64) v_330 v_388 u_488 u_80 u_88 kyberFutPtr
            b_4b0 msgVerByte opkIdWord kyberPreKeyId remoteRegId signedPreKeyId hdr
            spkRec spkPubBytes spkPrivBytes hpub_len hpriv_len
            stSpk stKpk stPk stId e gMe gPeer stk Frame)))
    (fun spkRec spkPubBytes spkPrivBytes kpkRec _ _ opkId e pkBuf skBuf opkFutPtr v90 evs sf P_f
        hspk_rel hspk_ok hpub_len hpriv_len _ _ hkpk_rel hkpk_ok _ _ _ _ hopk_some hpk_rel hevs
        hpcf hrunf htrf hspf hcsf hvregsf hCodef hent =>
      hErrPk spkRec kpkRec opkId e sf P_f evs
        hspk_rel hspk_ok hkpk_rel hkpk_ok hopk_some hpk_rel hevs
        hpcf hrunf htrf hspf hcsf hvregsf hCodef
        (Entails.trans hent
          (p2_v1_arm3_entails_placed A lim (M.stepEvents evs st) spkKit kpkKit pkKit ikit s0 sf
            sp fp coroPtr ctxPtr outPtr msgPtr ctBufPtr remoteAddrPtr localAddrPtr
            idStorePtr preKeyStorePtr spkStorePtr kyberStorePtr
            (coroPtr + 0x390#64) v_330 v_388 u_80 u_88 pkBuf skBuf opkFutPtr v90
            b_4b0 msgVerByte opkId opkIdWord kyberPreKeyId remoteRegId signedPreKeyId hdr
            spkRec kpkRec spkPubBytes spkPrivBytes hpub_len hpriv_len
            stSpk stKpk stPk stId e gMe gPeer stk Frame)))
    (fun spkRec spkPubBytes spkPrivBytes kpkRec kyberPubBytes kyberPrivBytes
        wOpk opkPkBytes opkSkBytes pkBuf skBuf idKpFutPtr v90 v_a8' v_b8' v_d0' evs14 s4
        hst_s4 hfs4 hspk_rel hspk_ok hspkPub_len hspkPriv_len hspk_pub_eq hspk_priv_eq
        hkpk_rel hkpk_ok hkyberPub_len hkyberPriv_len hkpk_pub_eq hkpk_priv_eq
        hopk_rel hopkPk_len hopkSk_len hopk_kb hevs14
        _ _ _ _
        hpc4 hrun4 hsp4 htr4 hx0_4 hx1_4 hx19_4 hx21_4 hx23_4 hx24_4 hx25_4 hx26_4 hx27_4 hx28_4
        hx29_4 hvregs4 _hCode4 => ?_)
  let inp := mkP2AcceptKeysInput hdr ikBSk ikBPk spkPubBytes spkPrivBytes
    kyberPubBytes kyberPrivBytes opkSkBytes
  let spkBPk : SignalPqxdh.Bytes := toU8 spkPubBytes
  have hspkBPk_len : spkBPk.length = 32 := by simp [spkBPk, toU8, hspkPub_len]
  have hwell : WellSizedAcceptKeysInput inp :=
    wellSized_mkP2AcceptKeysInput hikBSk_len hikBPk_len hspkPub_len hspkPriv_len
      hkyberPub_len hkyberPriv_len hopkSk_len hikAPk_len hekAPk_len hkemCt_len
  have hopkSk_eq : ∀ opkSk, inp.opkBSk? = some opkSk → opkSkBytes = bytesToBv8 opkSk :=
    fun _ h => opkOkSkBytes?_eq_of_some h
  refine p2_mono_pre
    (p2_over_sub4_to_sub5_placed A lim (M.stepEvents evs14 st) s0 s4 spkKit kpkKit pkKit skit
      sp fp coroPtr ctxPtr outPtr msgPtr ctBufPtr remoteAddrPtr localAddrPtr
      idStorePtr preKeyStorePtr spkStorePtr kyberStorePtr
      idKpFutPtr pkBuf skBuf v_330 v_388 u_80 u_88 v90 v_a8' v_b8' v_d0'
      inp hdr spkBPk spkPubBytes spkPrivBytes kyberPubBytes kyberPrivBytes opkPkBytes opkSkBytes
      opkIdWord kyberPreKeyId remoteRegId signedPreKeyId
      msgVerByte b_2c0 b_390 b_4f2
      (spkKit.getUpdate stSpk signedPreKeyId (.ok spkRec))
      (kpkKit.getUpdate stKpk kyberPreKeyId (.ok kpkRec))
      (opkOkUpdate pkKit stPk (hdrOpkIdBv? hdr) wOpk) stId
      gMe gPeer g recG sess stk Frame
      rfl (bytesToBv8_toU8 spkPubBytes)
      (mkP2AcceptKeysInput_spkBSk hdr ikBSk ikBPk spkPubBytes spkPrivBytes
        kyberPubBytes kyberPrivBytes opkSkBytes)
      (mkP2AcceptKeysInput_pqspkBSk hdr ikBSk ikBPk spkPubBytes spkPrivBytes
        kyberPubBytes kyberPrivBytes opkSkBytes)
      (opkOptTag8_eq_opkPresentTag (hdrOpkIdBv? hdr) opkSkBytes).symm
      hkyberPriv_len hkem_pos) ?_
  refine SepWPp.exists_elim fun u_b90 => SepWPp.exists_elim fun b_b98 => ?_
  refine stageP2_sub5_v1_kits_memInv_at_placed_ofEnv hInv ext skit senv hH hskitOk hskitVt
    hSameAcct hInitBobErrOwned hInitBobV1 hsame_le herr_le
    (st := M.stepEvents evs14 st)
    inp spkBPk opkPkBytes opkSkBytes gMe gPeer stId s0 s4 Q
    sp coroPtr ctxPtr msgPtr remoteAddrPtr localAddrPtr
    idStorePtr idKpFutPtr pkBuf skBuf ctBufPtr fp
    v_a8' v_b8' v_d0' u_b90 opkIdWord 1#8 b_b98 stk
    (p2OverSub5FramePlaced A spkKit kpkKit pkKit ikit s0 sp coroPtr outPtr msgPtr
      remoteAddrPtr localAddrPtr idStorePtr preKeyStorePtr spkStorePtr kyberStorePtr
      pkBuf skBuf v_330 v_388 u_80 u_88 v90 kyberPubBytes inp.hdr
      msgVerByte b_2c0 b_390 b_4f2 kyberPreKeyId remoteRegId signedPreKeyId
      (spkKit.getUpdate stSpk signedPreKeyId (.ok spkRec))
      (kpkKit.getUpdate stKpk kyberPreKeyId (.ok kpkRec))
      (opkOkUpdate pkKit stPk (hdrOpkIdBv? hdr) wOpk) g recG sess Frame)
    rfl rfl (hdr_opkId?_isSome_eq_opkOkSkBytes? hdr opkSkBytes)
    hwell hspkBPk_len hopkPk_len hopkSk_len hopkSk_eq
    (fun kp hkp => hkp_sk kp hkp)
    (fun kp hkp => by rw [hkp_pk kp hkp]; exact hneq)
    hpqr_ne hstk_bob hstk_sub56 hstk_lt
    (hfitsKp evs14 hevs14).seq_left
    (fun kp evsKp drKey hkp_rel hevsKp hacc => by
      simpa only [M.stepEvents_append] using
        (hfitsBob spkRec spkPubBytes spkPrivBytes kpkRec kyberPubBytes kyberPrivBytes
          wOpk opkPkBytes opkSkBytes kp drKey evs14 evsKp
          hspk_rel hspk_ok hspkPub_len hspkPriv_len hspk_pub_eq hspk_priv_eq
          hkpk_rel hkpk_ok hkyberPub_len hkyberPriv_len hkpk_pub_eq hkpk_priv_eq
          hopk_rel hopkPk_len hopkSk_len hopk_kb hkp_rel hacc hevs14 hevsKp).seq_left)
    (fun kp evsKp hkp_rel hevsKp hacc_none => by
      simpa only [M.stepEvents_append] using
        (hfitsAccErr spkRec spkPubBytes spkPrivBytes kpkRec kyberPubBytes kyberPrivBytes
          wOpk opkPkBytes opkSkBytes kp evs14 evsKp
          hspk_rel hspk_ok hspkPub_len hspkPriv_len hspk_pub_eq hspk_priv_eq
          hkpk_rel hkpk_ok hkyberPub_len hkyberPriv_len hkpk_pub_eq hkpk_priv_eq
          hopk_rel hopkPk_len hopkSk_len hopk_kb hkp_rel hacc_none hevs14 hevsKp).seq_left)
    (hInv.of_keepsFrozen hInv_s hst_s4.keepsFrozen) hpc4 hrun4 hsp4 hsp_align hvregs4
    (fun s1 htr1 hst1 => p2_envOk_id hfs4 hst1 htr1)
    hx0_4 hx1_4 hx19_4 hx21_4 hx23_4 hx24_4 hx26_4 hx27_4 hx28_4 (hx29_4.trans hx29)
    (fun kp drKey evsKp evsBob s5 v_a8'' v_b8'' v_d0'' u_b90' b_b98'
        hkp_rel hevsKp hacc hevsBob hst_s5 hpc5 hrun5 hsp5 htr5
        hx19_5 _ _ _ _ hx25_5 _ hx28_5 hx29_5 hvregs5 hCode5 => ?_)
    (fun kp evsKp evsErr errTag w2 w3 w4 w5 w6 sf5 v_a8'' v_b8'' v_d0'' u_b90' b_b98'
        hkp_rel hevsKp hacc_none hevsErr herr_ne_ok herr_ne_pend _ hpc5 hrun5 hsp5 htr5
        hx19_5 _ _ _ _ hx25_5 _ hx28_5 _ hvregs5 hCode5 => by
      have hikBPk_eq : toU8 kp.identityKey.publicKey.bytes.toList = ikBPk := by
        rw [hkp_pk kp hkp_rel, p2_toU8_bytesToBv8]
      conv => arg 4; rw [hikBPk_eq]
      let st_arm5 :=
        M.stepEvents (evsKp ++ rustDeallocEvents skit.kpBoxSize 8 ++ evsErr)
          (M.stepEvents evs14 st)
      have harm5 :=
        p2_over_v1_arm5_hooks_placed_ok (st := st_arm5) (Qp := Qp) ext spkKit kpkKit pkKit ikit
          hH hPure.dropSessionStructure3 s0 sf5 Q
          sp fp coroPtr ctxPtr outPtr msgPtr ctBufPtr remoteAddrPtr localAddrPtr
          idStorePtr preKeyStorePtr spkStorePtr kyberStorePtr
          pkBuf skBuf v_330 v_388 u_80 u_88 v90
          errTag w2 w3 w4 w5 w6 v_a8'' v_b8'' v_d0'' u_b90'
          inp ikBPk spkBPk kyberPubBytes opkPkBytes opkSkBytes
          opkIdWord kyberPreKeyId remoteRegId signedPreKeyId
          msgVerByte b_2c0 b_390 b_4f2 b_b98'
          (spkKit.getUpdate stSpk signedPreKeyId (.ok spkRec))
          (kpkKit.getUpdate stKpk kyberPreKeyId (.ok kpkRec))
          (opkOkUpdate pkKit stPk (hdrOpkIdBv? hdr) wOpk) stId
          gMe gPeer g recG sess stk (pqxdhAcceptErrPayloadAt A.repAlloc errTag w2 w3 w4 ∗ Frame)
          hwell hikBPk_len hspkBPk_len hkyberPub_len hopkPk_len hopkSk_len hopkSk_eq
          herr_ne_ok herr_ne_pend hstk_drop hstk_lt
          hCode5 hpc5 hrun5 hsp5 hsp_align hx19_5 (hx25_5.trans hx25_4) hx28_5 hvregs5
          (fun sf P_f evsFree hfree _ hpcf hrunf htrf hspf hcsf hvregsf hCodef hent => by
            let evs :=
              evs14 ++
                (evsKp ++
                  (rustDeallocEvents skit.kpBoxSize 8 ++ (evsErr ++ evsFree)))
            have hevs :
                P2OverV1Arm5EnvOfAcceptErr spkKit.getBoxSize
                  (spkEnv.getPollEnv stSpk signedPreKeyId)
                  kpkKit.getBoxSize (kpkEnv.getPollEnv stKpk kyberPreKeyId)
                  pkKit.getBoxSize (pkEnv.getPollEnv stPk) skit.kpBoxSize (hdrOpkIdBv? hdr)
                  (senv.kpPollEnv stId) (AcceptErrEnv inp) evs :=
              SeqEnv.append hevs14
                (SeqEnv.append hevsKp
                  (SeqEnv.append (freeOnlyEvs_rustDeallocEvents skit.kpBoxSize 8)
                    (SeqEnv.append hevsErr hfree)))
            have hst_eq : M.stepEvents evsFree st_arm5 = M.stepEvents evs st := by
              simp only [st_arm5, evs, M.stepEvents_append]
            exact hErrBob spkRec spkPubBytes spkPrivBytes kpkRec kyberPubBytes kyberPrivBytes
              wOpk opkPkBytes opkSkBytes kp errTag w2 w3 w4 w5 w6 sf P_f evs
              hspk_rel hspk_ok hspkPub_len hspkPriv_len hspk_pub_eq hspk_priv_eq
              hkpk_rel hkpk_ok hkyberPub_len hkyberPriv_len hkpk_pub_eq hkpk_priv_eq
              hopk_rel hopkPk_len hopkSk_len hopk_kb hkp_rel hacc_none hevs
              herr_ne_ok herr_ne_pend
              hpcf hrunf (by rw [htrf, htr5, htr4]) hspf hcsf hvregsf hCodef
              (Entails.trans (hst_eq ▸ hent)
                (p2_arm5_err_payload_pull_placed A lim (M.stepEvents evs st) s0 sf
                  sp fp coroPtr outPtr msgPtr ctBufPtr
                  remoteAddrPtr localAddrPtr idStorePtr ikit.id_vt preKeyStorePtr pkKit.pk_vt
                  kyberStorePtr kpkKit.kpk_vt v_330 v_388 errTag w2 w3 w4 w5 w6
                  inp.hdr msgVerByte opkIdWord kyberPreKeyId remoteRegId signedPreKeyId
                  (spkKit.storeAt spkStorePtr (spkKit.getUpdate stSpk signedPreKeyId (.ok spkRec)))
                  (kpkKit.storeAt kyberStorePtr (kpkKit.getUpdate stKpk kyberPreKeyId (.ok kpkRec)))
                  (pkKit.storeAt preKeyStorePtr (opkOkUpdate pkKit stPk (hdrOpkIdBv? hdr) wOpk))
                  (ikit.identityAt idStorePtr stId)
                  gMe gPeer stk Frame)))
      dsimp only [p2OverSub5FramePlaced, CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Over.p2OverSub5FramePlaced] at harm5 ⊢
      exact p2_sepWPp_weaken_eq harm5 (by sep_focus))
    (fun e evsKp s2 hkp_err hevsKp _ hpc2 hrun2 hsp2 htr2
        hx19_2 hx21_2 hx23_2 hx24_2 hx25_2 hx26_2 hx27_2 hx28_2 hx29_2 hvregs2 hCode2 =>
      let st_arm4 := M.stepEvents evsKp (M.stepEvents evs14 st)
      p2_over_v1_arm4_hooks_placed_ok (st := st_arm4) ext spkKit kpkKit pkKit skit
        hH hPure.dropSessionStructure3 hskitOk s0 s2 Q
        sp fp coroPtr ctxPtr outPtr msgPtr ctBufPtr remoteAddrPtr localAddrPtr
        idStorePtr preKeyStorePtr spkStorePtr kyberStorePtr
        idKpFutPtr pkBuf skBuf v_330 v_388 u_80 u_88 v90
        v_a8' v_b8' v_d0' u_b90
        inp spkBPk kyberPubBytes opkPkBytes opkSkBytes
        opkIdWord kyberPreKeyId remoteRegId signedPreKeyId
        msgVerByte b_2c0 b_390 b_4f2 b_b98
        (spkKit.getUpdate stSpk signedPreKeyId (.ok spkRec))
        (kpkKit.getUpdate stKpk kyberPreKeyId (.ok kpkRec))
        (opkOkUpdate pkKit stPk (hdrOpkIdBv? hdr) wOpk) stId
        e gMe gPeer g recG sess stk Frame
        hwell hspkBPk_len hkyberPub_len hopkPk_len hopkSk_len hstk_drop hstk_lt
        hCode2 hpc2 hrun2 hsp2 hsp_align
        hx19_2 hx21_2 hx23_2 hx24_2 (hx25_2.trans hx25_4) hx26_2 hx27_2 hx28_2 hx29_2 hvregs2
        (fun sf P_f evsFree hfree _ hpcf hrunf htrf hspf hcsf hvregsf hCodef hent => by
          let evs := evs14 ++ (evsKp ++ evsFree)
          have hevs :
              P2OverV1Arm4Env spkKit.getBoxSize (spkEnv.getPollEnv stSpk signedPreKeyId)
                kpkKit.getBoxSize (kpkEnv.getPollEnv stKpk kyberPreKeyId)
                pkKit.getBoxSize (pkEnv.getPollEnv stPk) skit.kpBoxSize (hdrOpkIdBv? hdr)
                (senv.kpPollEnv stId) evs :=
            SeqEnv.append hevs14 (SeqEnv.append hevsKp hfree)
          have hst_eq : M.stepEvents evsFree st_arm4 = M.stepEvents evs st := by
            simp only [st_arm4, evs, M.stepEvents_append]
          exact hErrKp spkRec kpkRec wOpk e sf P_f evs
            hspk_rel hspk_ok hkpk_rel hkpk_ok hopk_rel hkp_err hevs
            hpcf hrunf (by rw [htrf, htr2, htr4]) hspf hcsf hvregsf hCodef (hst_eq ▸ hent)))
  have hikBPk_eq : toU8 kp.identityKey.publicKey.bytes.toList = ikBPk := by
    rw [hkp_pk kp hkp_rel, p2_toU8_bytesToBv8]
  have hfs5 : FsAt (stageP2EnvOk spkKit kpkKit pkKit ikit)
      (stageP2Quiet spkKit kpkKit pkKit skit) (stageP1ProgPlaced ext) s5 :=
    p2_fsAt_step_kp (.ok kp) hfs4 hst_s5 htr5
  have hx25_5' : s5.readReg64 .x25 = sp + 0x210#64 := hx25_5.trans hx25_4
  let pqBytes := initialStateValue F (p2BobSpqrParams drKey.pqrKey)
  let st5 :=
    M.stepEvents (evsKp ++ rustDeallocEvents skit.kpBoxSize 8 ++ evsBob)
      (M.stepEvents evs14 st)
  have hfitsSub6 :
      FitsEnv M lim st5
        (P2OverSub6EnvOf skit.regIdBoxSize (senv.regIdPollEnv stId)
          (P2OverSub6TailEnvOf PromEnv skit.regIdBoxSize recG sess)) := by
    have h0 :=
      (hfitsBob spkRec spkPubBytes spkPrivBytes kpkRec kyberPubBytes kyberPrivBytes
        wOpk opkPkBytes opkSkBytes kp drKey evs14 evsKp
        hspk_rel hspk_ok hspkPub_len hspkPriv_len hspk_pub_eq hspk_priv_eq
        hkpk_rel hkpk_ok hkyberPub_len hkyberPriv_len hkpk_pub_eq hkpk_priv_eq
        hopk_rel hopkPk_len hopkSk_len hopk_kb hkp_rel hacc hevs14 hevsKp).seq_right hevsBob
    simpa only [st5, M.stepEvents_append] using h0
  conv => arg 4; rw [hikBPk_eq]
  refine p2_mono_pre
    (p2_over_sub5_to_sub6_placed A lim st5 s0 s5 spkKit kpkKit pkKit ikit
      sp fp coroPtr ctxPtr outPtr msgPtr ctBufPtr remoteAddrPtr localAddrPtr
      idStorePtr preKeyStorePtr spkStorePtr kyberStorePtr
      pkBuf skBuf v_330 v_388 u_80 u_88 v90 v_a8'' v_b8'' v_d0'' u_b90'
      inp ikBPk spkBPk drKey pqBytes kyberPubBytes opkPkBytes opkSkBytes
      opkIdWord kyberPreKeyId remoteRegId signedPreKeyId
      msgVerByte b_2c0 b_390 b_4f2 b_b98'
      (spkKit.getUpdate stSpk signedPreKeyId (.ok spkRec))
      (kpkKit.getUpdate stKpk kyberPreKeyId (.ok kpkRec))
      (opkOkUpdate pkKit stPk (hdrOpkIdBv? hdr) wOpk) stId
      gMe gPeer g recG sess stk Frame hkyberPub_len) ?_
  refine SepWPp.exists_elim fun localIkBoxPtr =>
    SepWPp.exists_elim fun remoteIkBoxPtr =>
    SepWPp.exists_elim fun rootKeyBoxPtr =>
    SepWPp.exists_elim fun baseKeyBoxPtr =>
    SepWPp.exists_elim fun ratchetPubBoxPtr =>
    SepWPp.exists_elim fun ratchetPrivBoxPtr =>
    SepWPp.exists_elim fun chainKeyBoxPtr =>
    SepWPp.exists_elim fun spqrCap =>
    SepWPp.exists_elim fun spqrBufPtr =>
    SepWPp.exists_elim fun pad_f4 =>
    SepWPp.exists_elim fun c0 =>
    SepWPp.exists_elim fun c1 =>
    SepWPp.exists_elim fun c2 =>
    SepWPp.exists_elim fun c3 =>
    SepWPp.exists_elim fun c4 =>
    SepWPp.exists_elim fun d0 =>
    SepWPp.exists_elim fun d1 =>
    SepWPp.exists_elim fun d2 =>
    SepWPp.exists_elim fun u_650 =>
    SepWPp.exists_elim fun u_298 =>
    SepWPp.exists_elim fun u_2a0 =>
    SepWPp.exists_elim fun u_2a8 =>
    SepWPp.exists_elim fun u_3a0 =>
    SepWPp.exists_elim fun b_3ac =>
    SepWPp.exists_elim fun u_3b0 =>
    SepWPp.exists_elim fun u_3b8 =>
    SepWPp.exists_elim fun u_3c0 =>
    SepWPp.exists_elim fun u_3c8 =>
    SepWPp.exists_elim fun u_3d0 =>
    SepWPp.exists_elim fun u_3d8 => ?_
  refine SepWPp.pure_elim
    fun ⟨hloc_nz, hrem_nz, hroot_nz, halice_nz, hrat_pub, hrat_priv, hck_ptr⟩ => ?_
  have hspk_clamp : clampBv8List spkPrivBytes = bytesToBv8 inp.spkBSk :=
    (mkP2AcceptKeysInput_spkBSk hdr ikBSk ikBPk spkPubBytes spkPrivBytes
      kyberPubBytes kyberPrivBytes opkSkBytes).symm
  refine stageP2_over_sub6_v1_kits_ext_placed_withEnv_ofEnv ext skit senv hH hskitOk hskitVt
    hPureVac coroPtr g recG sess hPromoteOver
    (st := st5)
    inp ikBPk spkBPk stId s0 s5 (s0.readReg64 .x30) Q
    sp ctxPtr msgPtr remoteAddrPtr localAddrPtr outPtr
    idStorePtr pkBuf skBuf ctBufPtr
    localIkBoxPtr remoteIkBoxPtr v_330 v_388 u_650
    u_298 u_2a0 u_80 u_88 v90 v_a8'' v_b8'' v_d0''
    u_3a0 u_3b0 u_3b8 u_3c0 u_3c8 u_3d0 u_3d8
    (p2BobSessMid280V1 rootKeyBoxPtr baseKeyBoxPtr spqrCap spqrBufPtr
      (BitVec.ofNat 64 pqBytes.length) ratchetPubBoxPtr ratchetPrivBoxPtr chainKeyBoxPtr
      pad_f4 c0 c1 c2 c3 c4 d0 d1 d2)
    (p2BobSessMid280V1_length _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _)
    remoteRegId (opkOptTag32 (hdrOpkIdBv? inp.hdr)) opkIdWord kyberPreKeyId signedPreKeyId u_2a8
    msgVerByte b_4f2 b_390 b_3ac stk
    (p2Sub6FramePlaced A spkKit kpkKit pkKit s0 sp fp coroPtr outPtr msgPtr
      remoteAddrPtr localAddrPtr preKeyStorePtr spkStorePtr kyberStorePtr pkBuf skBuf
      localIkBoxPtr remoteIkBoxPtr rootKeyBoxPtr baseKeyBoxPtr spqrCap spqrBufPtr
      ratchetPubBoxPtr ratchetPrivBoxPtr chainKeyBoxPtr
      inp ikBPk spkBPk drKey pqBytes opkPkBytes opkSkBytes b_2c0
      (spkKit.getUpdate stSpk signedPreKeyId (.ok spkRec))
      (kpkKit.getUpdate stKpk kyberPreKeyId (.ok kpkRec))
      (opkOkUpdate pkKit stPk (hdrOpkIdBv? hdr) wOpk) gMe gPeer Frame)
    hwell hctBuf_nz hstk_sub56 hstk_overPure hstk_lt
    hfitsSub6.seq_left
    (fun evsShim hShim => (hfitsSub6.seq_right hShim).seq_left)
    (fun _ evsShim evsPoll _ hShim hPoll => by
      have hdisj := (hfitsSub6.seq_right hShim).seq_right hPoll
      have htail :
          FitsEnv M lim (M.stepEvents evsPoll (M.stepEvents evsShim st5))
            (P2OverSub6TailEnvOf PromEnv skit.regIdBoxSize recG sess) :=
        fun evs hevs => hdisj evs (Or.inr hevs)
      simpa only [M.stepEvents_append] using fitsPromote_of_fitsTailEnv htail)
    hCode5 hpc5 hrun5 hsp5 hsp_align hvregs5
    (fun s3 htr3 hst3 => p2_envOk_id hfs5 hst3 htr3) hx19_5
    (fun localRegId regIdFutPtr evsShim evsPoll evsProm sf
        hreg_rel hShim hPoll hProm hst_sf hpcf hrunf hspf htrf
        hx8f hx9f hx10f hx11f hx19f hx20f hx22f hx23f hx24f hx25f hx26f hx27f hx28f hx29f
        hvregsf hCodef => by
      let evs :=
        evs14 ++
          (evsKp ++
            (rustDeallocEvents skit.kpBoxSize 8 ++
              (evsBob ++
                (evsShim ++ (evsPoll ++ p2OverSub6TailEvents skit.regIdBoxSize evsProm)))))
      have hevs :
          P2OverV1OkEnvOfBobAndProm spkKit.getBoxSize (spkEnv.getPollEnv stSpk signedPreKeyId)
            kpkKit.getBoxSize (kpkEnv.getPollEnv stKpk kyberPreKeyId)
            pkKit.getBoxSize (pkEnv.getPollEnv stPk) skit.kpBoxSize (hdrOpkIdBv? hdr)
            (senv.kpPollEnv stId) (BobV1Env inp drKey)
            skit.regIdBoxSize (senv.regIdPollEnv stId)
            (P2OverSub6TailEnvOf PromEnv skit.regIdBoxSize recG sess) evs :=
        SeqEnv.append hevs14
          (SeqEnv.append hevsKp
            (SeqEnv.append (freeOnlyEvs_rustDeallocEvents skit.kpBoxSize 8)
              (SeqEnv.append hevsBob
                (SeqEnv.append hShim
                  (SeqEnv.append hPoll (p2OverSub6TailEnvOf_intro hProm))))))
      let st_ok :=
        M.stepEvents (evsShim ++ evsPoll ++ p2OverSub6TailEvents skit.regIdBoxSize evsProm) st5
      have hst_eq : st_ok = M.stepEvents evs st := by
        simp only [st_ok, st5, evs, M.stepEvents_append]
      exact p2_mono_pre
        (p2_over_v1_ok_entails_placed A lim st_ok spkKit kpkKit pkKit skit hWF s0 sf
          sp fp coroPtr ctxPtr outPtr msgPtr ctBufPtr remoteAddrPtr localAddrPtr
          idStorePtr preKeyStorePtr spkStorePtr kyberStorePtr
          regIdFutPtr pkBuf skBuf v_330 v_388
          localIkBoxPtr remoteIkBoxPtr rootKeyBoxPtr baseKeyBoxPtr spqrCap spqrBufPtr
          ratchetPubBoxPtr ratchetPrivBoxPtr chainKeyBoxPtr
          c0 c1 c2 c3 c4 d0 d1 d2
          recG sess inp ikBPk spkBPk drKey spkPrivBytes pqBytes opkPkBytes opkSkBytes
          pad_f4 opkIdWord kyberPreKeyId remoteRegId localRegId signedPreKeyId
          msgVerByte b_2c0
          (spkKit.getUpdate stSpk signedPreKeyId (.ok spkRec))
          (kpkKit.getUpdate stKpk kyberPreKeyId (.ok kpkRec))
          (opkOkUpdate pkKit stPk (hdrOpkIdBv? hdr) wOpk) stId
          gMe gPeer stk Frame
          hacc hwell hikBPk_len hspkBPk_len hspkPriv_len hspk_clamp
          hopkPk_len hopkSk_len hopkSk_eq
          hloc_nz hrem_nz hroot_nz halice_nz hrat_pub hrat_priv hck_ptr)
        (hst_eq.symm ▸
          hOk spkRec spkPubBytes spkPrivBytes kpkRec kyberPubBytes kyberPrivBytes
            wOpk opkPkBytes opkSkBytes kp drKey localRegId
            (mkBobGhostV1 localIkBoxPtr remoteIkBoxPtr rootKeyBoxPtr baseKeyBoxPtr spqrCap spqrBufPtr
              (bytesToBv8 (encodeEC ikBPk)) (bytesToBv8 (encodeEC inp.hdr.ikAPk))
              (bytesToBv8 (encodeEC inp.hdr.ekAPk))
              (mkBobSenderChainGhost ratchetPubBoxPtr ratchetPrivBoxPtr chainKeyBoxPtr
                (bytesToBv8 (encodeEC spkBPk)) (bytesToBv8 inp.spkBSk))
              remoteRegId localRegId)
            sf evs
            hspk_rel hspk_ok hspkPub_len hspkPriv_len hspk_pub_eq hspk_priv_eq
            hkpk_rel hkpk_ok hkyberPub_len hkyberPriv_len hkpk_pub_eq hkpk_priv_eq
            hopk_rel hopkPk_len hopkSk_len hopk_kb hkp_rel hacc hreg_rel hevs
            rfl rfl rfl rfl
            (hst_s4.trans (hst_s5.trans hst_sf))
            (p2_fsAt_step_regId (.ok localRegId) hfs5 hst_sf htrf)
            hpcf hrunf hspf (by rw [htrf, htr5, htr4])
            hx8f hx9f hx10f hx11f hx19f hx20f hx22f hx23f hx24f
            (hx25f.trans hx25_5') hx26f hx27f (hx28f.trans hx28_5) (hx29f.trans hx29_5)
            hvregsf hCodef))
    (fun e regIdFutPtr evsShim evsPoll s6 hreg_err hShim hPoll _ hpc6 hrun6 hsp6 htr6
        hx19_6 hx21_6 hx23_6 hx25_6 hx26_6 _ hx28_6 _ hvregs6 hCode6 =>
      p2_over_v1_arm6_hooks_placed_ok ext spkKit kpkKit pkKit skit
        hWF hH hPure.dropSessionStructure3 hskitOk s0 s6 Q
        sp fp coroPtr ctxPtr outPtr msgPtr ctBufPtr remoteAddrPtr localAddrPtr
        idStorePtr preKeyStorePtr spkStorePtr kyberStorePtr
        regIdFutPtr pkBuf skBuf v_330 v_388
        localIkBoxPtr remoteIkBoxPtr rootKeyBoxPtr baseKeyBoxPtr spqrCap spqrBufPtr
        ratchetPubBoxPtr ratchetPrivBoxPtr chainKeyBoxPtr
        c0 c1 c2 c3 c4 d0 d1 d2
        u_298 u_2a0 u_80 u_88 v90 v_a8'' v_b8'' v_d0''
        u_3a0 u_3b0 u_3b8 u_3c0 u_3c8 u_3d0 u_3d8
        inp ikBPk spkBPk drKey spkPrivBytes pqBytes opkPkBytes opkSkBytes
        pad_f4 opkIdWord kyberPreKeyId remoteRegId signedPreKeyId u_2a8
        msgVerByte b_2c0 b_390 b_4f2 b_3ac
        (spkKit.getUpdate stSpk signedPreKeyId (.ok spkRec))
        (kpkKit.getUpdate stKpk kyberPreKeyId (.ok kpkRec))
        (opkOkUpdate pkKit stPk (hdrOpkIdBv? hdr) wOpk) stId
        e gMe gPeer g recG sess stk Frame
        hacc hwell hikBPk_len hspkBPk_len hspkPriv_len hspk_clamp
        hopkPk_len hopkSk_len hopkSk_eq
        hloc_nz hrem_nz hroot_nz halice_nz hrat_pub hrat_priv hck_ptr
        hstk_drop hstk_lt hCode6 hpc6 hrun6 hsp6 hsp_align
        hx19_6 hx21_6 hx23_6 (hx25_6.trans hx25_5') hx26_6 (hx28_6.trans hx28_5) hvregs6
        (fun sf P_f evsFree hfree _ hpcf hrunf htrf hspf hcsf hvregsf hCodef hent => by
          let evs :=
            evs14 ++
              (evsKp ++
                (rustDeallocEvents skit.kpBoxSize 8 ++
                  (evsBob ++ (evsShim ++ (evsPoll ++ evsFree)))))
          have hevs :
              P2OverV1Arm6EnvOfBob spkKit.getBoxSize (spkEnv.getPollEnv stSpk signedPreKeyId)
                kpkKit.getBoxSize (kpkEnv.getPollEnv stKpk kyberPreKeyId)
                pkKit.getBoxSize (pkEnv.getPollEnv stPk) skit.kpBoxSize (hdrOpkIdBv? hdr)
                (senv.kpPollEnv stId) (BobV1Env inp drKey)
                skit.regIdBoxSize (senv.regIdPollEnv stId) evs :=
            SeqEnv.append hevs14
              (SeqEnv.append hevsKp
                (SeqEnv.append (freeOnlyEvs_rustDeallocEvents skit.kpBoxSize 8)
                  (SeqEnv.append hevsBob
                    (SeqEnv.append hShim (SeqEnv.append hPoll hfree)))))
          have hst_eq :
              M.stepEvents evsFree (M.stepEvents (evsShim ++ evsPoll) st5) =
                M.stepEvents evs st := by
            simp only [st5, evs, M.stepEvents_append]
          exact hErrRegId spkRec spkPubBytes spkPrivBytes kpkRec kyberPubBytes kyberPrivBytes
            wOpk opkPkBytes opkSkBytes kp drKey e sf P_f evs
            hspk_rel hspk_ok hspkPub_len hspkPriv_len hspk_pub_eq hspk_priv_eq
            hkpk_rel hkpk_ok hkyberPub_len hkyberPriv_len hkpk_pub_eq hkpk_priv_eq
            hopk_rel hopkPk_len hopkSk_len hopk_kb hkp_rel hacc hreg_err hevs
            hpcf hrunf (by rw [htrf, htr6, htr5, htr4]) hspf hcsf hvregsf hCodef
            (hst_eq ▸ hent)))

abbrev stageP2_over_v1_kits_memInv_at_placed [LibsignalPlacement]
    {Φ : Memory → Prop} (hInv : StageP2MemInv Φ)
    {M : AllocCostModel} {P : Primitives} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {F : ShaCompress} {AcceptErrEnv : AcceptKeysInput → List AllocEvent → Prop} :=
  @stageP2_over_v1_kits_memInv_at_placed_ofEnv _ Φ hInv M P A lim F
    (InitializeBobV1OptFieldsEnv P F) AcceptErrEnv PromoteOverEnv

theorem stageP2_over_v1_kits_memInv_ext_placed_ofEnv [LibsignalPlacement]
    {Φ : Memory → Prop} (hInv : StageP2MemInv Φ)
    {M : AllocCostModel} {P : Primitives} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {F : ShaCompress} {BobV1Env : AcceptKeysInput → DRKey → List AllocEvent → Prop}
    {AcceptErrEnv : AcceptKeysInput → List AllocEvent → Prop}
    {PromEnv : SessionGhost → Session (List (BitVec 8)) → List AllocEvent → Prop}
    (ext : String → Option (State → State))
    (hWF : StructuralPrims P)
    (hH : StageP2ClosureHooksPlaced A lim ext)
    (hPure : StageP2BaseCalleesPlaced4K A lim ext)
    (hInitBobErrOwned :
      subroutine_ok (stageP1ProgPlaced ext) (lsmpl.base 75)
        (initializeBobSessionErrOwnedMemInv4KPlacedSpec Φ P A lim AcceptErrEnv))
    (hInitBobV1 : InitializeBobV1MemInvOkPlaced4KOfEnv Φ P A lim F BobV1Env ext)
    (ikit : IdentityStoreSpec A.repAlloc 0#64) (skit : IdentitySelfStoreSpec ikit)
    (senv : IdentitySelfStoreBudgetEnv skit)
    (hskitVt : IdentitySelfVtablesPlacedOk ikit skit)
    (hskitOk : IdentitySelfStoreKitPlacedOkI A lim ikit skit senv ext)
    (spkKit : SignedPreKeyStoreSpec A.repAlloc 0#64)
    (spkEnv : SignedPreKeyStoreBudgetEnv spkKit)
    (hspkVt : SignedPreKeyVtablesPlacedOk spkKit)
    (hspkOk : SignedPreKeyStoreKitPlacedOk A lim spkKit spkEnv ext)
    (kpkKit : KyberPreKeyStoreSpec A.repAlloc 0#64)
    (kpkEnv : KyberPreKeyStoreBudgetEnv kpkKit)
    (hkpkVt : KyberPreKeyVtablesPlacedOk kpkKit)
    (hkpkOk : KyberPreKeyStoreKitPlacedOk A lim kpkKit kpkEnv ext)
    (pkKit : PreKeyStoreSpec A.repAlloc 0#64)
    (pkEnv : PreKeyStoreBudgetEnv pkKit)
    (hpkVt : PreKeyVtablesPlacedOk pkKit)
    (hpkOk : PreKeyStoreKitPlacedOk A lim pkKit pkEnv ext)
    (stk : Nat) (hstk : stageP2OverV1CallStack4K spkKit kpkKit pkKit skit ≤ stk) :
    stageP2OverV1KitsMemInvAtPlacedOfEnvProp Φ P A lim F BobV1Env AcceptErrEnv PromEnv ext
      skit senv spkKit spkEnv kpkKit kpkEnv pkKit pkEnv stk :=
  stageP2_over_v1_kits_memInv_at_placed_ofEnv hInv ext hWF hH hPure
    (isSameAccountDistinctSpecExt_to_at_placed hPure.isSameAccount)
    (of_stageP2Defs_errOwnedMemInv4K_placed hInitBobErrOwned)
    (bobV1Stk := initializeBobSessionV1StackExtPlaced) hInitBobV1
    p2_isSameAccountExt_le_bobExt p2_bobErr4K_le_bobExt
    ikit skit senv hskitVt hskitOk
    spkKit spkEnv hspkVt hspkOk
    kpkKit kpkEnv hkpkVt hkpkOk
    pkKit pkEnv hpkVt hpkOk
    ((stageP2OverV1CallStack4K_eq spkKit kpkKit pkKit skit).symm ▸
      p2_over_callStack_le_v1CallStack spkKit kpkKit pkKit skit)
    ((stageP2OverV1CallStack4K_eq spkKit kpkKit pkKit skit).symm ▸
      Nat.le_trans p2_over_bobExt_le_overPure
        (p2_over_pure_le_v1CallStack spkKit kpkKit pkKit skit))
    stk hstk

abbrev stageP2_over_v1_kits_memInv_ext_placed [LibsignalPlacement]
    {Φ : Memory → Prop} (hInv : StageP2MemInv Φ)
    {M : AllocCostModel} {P : Primitives} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {F : ShaCompress} {AcceptErrEnv : AcceptKeysInput → List AllocEvent → Prop} :=
  @stageP2_over_v1_kits_memInv_ext_placed_ofEnv _ Φ hInv M P A lim F
    (InitializeBobV1OptFieldsEnv P F) AcceptErrEnv PromoteOverEnv

abbrev stageP2_over_v1_kits_frozen_at_placed_ofEnv [LibsignalPlacement]
    {M : AllocCostModel} {P : Primitives} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {F : ShaCompress} {BobV1Env : AcceptKeysInput → DRKey → List AllocEvent → Prop}
    {AcceptErrEnv : AcceptKeysInput → List AllocEvent → Prop}
    {PromEnv : SessionGhost → Session (List (BitVec 8)) → List AllocEvent → Prop} :=
  @stageP2_over_v1_kits_memInv_at_placed_ofEnv _ (LibsignalFrozen lsmpl) StageP2MemInv.frozen
    M P A lim F BobV1Env AcceptErrEnv PromEnv

abbrev stageP2_over_v1_kits_frozen_at_placed [LibsignalPlacement]
    {M : AllocCostModel} {P : Primitives} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {F : ShaCompress} {AcceptErrEnv : AcceptKeysInput → List AllocEvent → Prop} :=
  @stageP2_over_v1_kits_frozen_at_placed_ofEnv _ M P A lim F
    (InitializeBobV1OptFieldsEnv P F) AcceptErrEnv PromoteOverEnv

theorem stageP2_over_v1_kits_frozen_ext_placed_ofEnv [LibsignalPlacement]
    {M : AllocCostModel} {P : Primitives} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {F : ShaCompress} {BobV1Env : AcceptKeysInput → DRKey → List AllocEvent → Prop}
    {AcceptErrEnv : AcceptKeysInput → List AllocEvent → Prop}
    {PromEnv : SessionGhost → Session (List (BitVec 8)) → List AllocEvent → Prop}
    (ext : String → Option (State → State))
    (hWF : StructuralPrims P)
    (hH : StageP2ClosureHooksPlaced A lim ext)
    (hPure : StageP2BaseCalleesPlaced4K A lim ext)
    (hInitBobErrOwned :
      subroutine_ok (stageP1ProgPlaced ext) (lsmpl.base 75)
        (LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP2Sub5DefsPlacedBudget.Sub5Placed.initializeBobSessionErrOwnedFrozen4KPlacedSpec
          P A lim AcceptErrEnv))
    (hInitBobV1 : InitializeBobV1FrozenOkPlaced4KOfEnv P A lim F BobV1Env ext)
    (ikit : IdentityStoreSpec A.repAlloc 0#64) (skit : IdentitySelfStoreSpec ikit)
    (senv : IdentitySelfStoreBudgetEnv skit)
    (hskitVt : IdentitySelfVtablesPlacedOk ikit skit)
    (hskitOk : IdentitySelfStoreKitPlacedOkI A lim ikit skit senv ext)
    (spkKit : SignedPreKeyStoreSpec A.repAlloc 0#64)
    (spkEnv : SignedPreKeyStoreBudgetEnv spkKit)
    (hspkVt : SignedPreKeyVtablesPlacedOk spkKit)
    (hspkOk : SignedPreKeyStoreKitPlacedOk A lim spkKit spkEnv ext)
    (kpkKit : KyberPreKeyStoreSpec A.repAlloc 0#64)
    (kpkEnv : KyberPreKeyStoreBudgetEnv kpkKit)
    (hkpkVt : KyberPreKeyVtablesPlacedOk kpkKit)
    (hkpkOk : KyberPreKeyStoreKitPlacedOk A lim kpkKit kpkEnv ext)
    (pkKit : PreKeyStoreSpec A.repAlloc 0#64)
    (pkEnv : PreKeyStoreBudgetEnv pkKit)
    (hpkVt : PreKeyVtablesPlacedOk pkKit)
    (hpkOk : PreKeyStoreKitPlacedOk A lim pkKit pkEnv ext)
    (stk : Nat) (hstk : stageP2OverV1CallStack4K spkKit kpkKit pkKit skit ≤ stk) :
    stageP2OverV1KitsFrozenAtPlacedOfEnvProp P A lim F BobV1Env AcceptErrEnv PromEnv ext
      skit senv spkKit spkEnv kpkKit kpkEnv pkKit pkEnv stk :=
  stageP2_over_v1_kits_memInv_at_placed_ofEnv StageP2MemInv.frozen ext hWF hH hPure
    (isSameAccountDistinctSpecExt_to_at_placed hPure.isSameAccount)
    hInitBobErrOwned
    (bobV1Stk := initializeBobSessionV1StackExtPlaced) hInitBobV1
    p2_isSameAccountExt_le_bobExt p2_bobErr4K_le_bobExt
    ikit skit senv hskitVt hskitOk
    spkKit spkEnv hspkVt hspkOk
    kpkKit kpkEnv hkpkVt hkpkOk
    pkKit pkEnv hpkVt hpkOk
    ((stageP2OverV1CallStack4K_eq spkKit kpkKit pkKit skit).symm ▸
      p2_over_callStack_le_v1CallStack spkKit kpkKit pkKit skit)
    ((stageP2OverV1CallStack4K_eq spkKit kpkKit pkKit skit).symm ▸
      Nat.le_trans p2_over_bobExt_le_overPure
        (p2_over_pure_le_v1CallStack spkKit kpkKit pkKit skit))
    stk hstk

abbrev stageP2_over_v1_kits_frozen_ext_placed [LibsignalPlacement]
    {M : AllocCostModel} {P : Primitives} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {F : ShaCompress} {AcceptErrEnv : AcceptKeysInput → List AllocEvent → Prop} :=
  @stageP2_over_v1_kits_frozen_ext_placed_ofEnv _ M P A lim F (InitializeBobV1OptFieldsEnv P F)
    AcceptErrEnv PromoteOverEnv

abbrev stageP2_over_v1_kits_frozen_4k_placed_ofEnv [LibsignalPlacement] :=
  @stageP2_over_v1_kits_frozen_ext_placed_ofEnv

abbrev stageP2_over_v1_kits_frozen_4k_placed [LibsignalPlacement] :=
  @stageP2_over_v1_kits_frozen_ext_placed

theorem stageP2_over_v1_kits_frozen_ext_defs_placed_ofEnv [LibsignalPlacement]
    {M : AllocCostModel} {P : Primitives} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {F : ShaCompress} {BobV1Env : AcceptKeysInput → DRKey → List AllocEvent → Prop}
    {AcceptErrEnv : AcceptKeysInput → List AllocEvent → Prop}
    {PromEnv : SessionGhost → Session (List (BitVec 8)) → List AllocEvent → Prop}
    (ext : String → Option (State → State))
    (hWF : StructuralPrims P)
    (hH : StageP2ClosureHooksPlaced A lim ext)
    (hPure : StageP2BaseCalleesPlaced4K A lim ext)
    (hInitBobErrOwned :
      subroutine_ok (stageP1ProgPlaced ext) (lsmpl.base 75)
        (LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP2DefsPlacedBudget.initializeBobSessionErrOwnedFrozen4KPlacedSpec
          P A lim AcceptErrEnv))
    (hInitBobV1 : InitializeBobV1FrozenOkPlaced4KOfEnv P A lim F BobV1Env ext)
    (ikit : IdentityStoreSpec A.repAlloc 0#64) (skit : IdentitySelfStoreSpec ikit)
    (senv : IdentitySelfStoreBudgetEnv skit)
    (hskitVt : IdentitySelfVtablesPlacedOk ikit skit)
    (hskitOk : IdentitySelfStoreKitPlacedOkI A lim ikit skit senv ext)
    (spkKit : SignedPreKeyStoreSpec A.repAlloc 0#64)
    (spkEnv : SignedPreKeyStoreBudgetEnv spkKit)
    (hspkVt : SignedPreKeyVtablesPlacedOk spkKit)
    (hspkOk : SignedPreKeyStoreKitPlacedOk A lim spkKit spkEnv ext)
    (kpkKit : KyberPreKeyStoreSpec A.repAlloc 0#64)
    (kpkEnv : KyberPreKeyStoreBudgetEnv kpkKit)
    (hkpkVt : KyberPreKeyVtablesPlacedOk kpkKit)
    (hkpkOk : KyberPreKeyStoreKitPlacedOk A lim kpkKit kpkEnv ext)
    (pkKit : PreKeyStoreSpec A.repAlloc 0#64)
    (pkEnv : PreKeyStoreBudgetEnv pkKit)
    (hpkVt : PreKeyVtablesPlacedOk pkKit)
    (hpkOk : PreKeyStoreKitPlacedOk A lim pkKit pkEnv ext)
    (stk : Nat) (hstk : stageP2OverV1CallStack4K spkKit kpkKit pkKit skit ≤ stk) :
    stageP2OverV1KitsFrozenAtPlacedOfEnvProp P A lim F BobV1Env AcceptErrEnv PromEnv ext
      skit senv spkKit spkEnv kpkKit kpkEnv pkKit pkEnv stk :=
  stageP2_over_v1_kits_memInv_ext_placed_ofEnv StageP2MemInv.frozen ext hWF hH hPure
    hInitBobErrOwned hInitBobV1
    ikit skit senv hskitVt hskitOk
    spkKit spkEnv hspkVt hspkOk
    kpkKit kpkEnv hkpkVt hkpkOk
    pkKit pkEnv hpkVt hpkOk
    stk hstk

abbrev stageP2_over_v1_kits_frozen_ext_defs_placed [LibsignalPlacement]
    {M : AllocCostModel} {P : Primitives} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {F : ShaCompress} {AcceptErrEnv : AcceptKeysInput → List AllocEvent → Prop} :=
  @stageP2_over_v1_kits_frozen_ext_defs_placed_ofEnv _ M P A lim F (InitializeBobV1OptFieldsEnv P F)
    AcceptErrEnv PromoteOverEnv

theorem stageP2_over_v1_kits_frozen_placed_ofEnv [LibsignalPlacement]
    {M : AllocCostModel} {P : Primitives} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {F : ShaCompress} {BobV1Env : AcceptKeysInput → DRKey → List AllocEvent → Prop}
    {AcceptErrEnv : AcceptKeysInput → List AllocEvent → Prop}
    {PromEnv : SessionGhost → Session (List (BitVec 8)) → List AllocEvent → Prop}
    (ext : String → Option (State → State))
    (hWF : StructuralPrims P)
    (hH : StageP2ClosureHooksPlaced A lim ext)
    (hPure : StageP2BaseCalleesPlaced4K A lim ext)
    (hInitBobErrOwned :
      subroutine_ok (stageP1ProgPlaced ext) (lsmpl.base 75)
        (withLsCodeRoLoaded lsmpl
          (initializeBobSessionErrOwnedFrozenPlacedSpec P A lim AcceptErrEnv)))
    (hInitBobV1 : InitializeBobV1FrozenOkPlacedOfEnv P A lim F BobV1Env ext)
    (ikit : IdentityStoreSpec A.repAlloc 0#64) (skit : IdentitySelfStoreSpec ikit)
    (senv : IdentitySelfStoreBudgetEnv skit)
    (hskitVt : IdentitySelfVtablesPlacedOk ikit skit)
    (hskitOk : IdentitySelfStoreKitPlacedOkI A lim ikit skit senv ext)
    (spkKit : SignedPreKeyStoreSpec A.repAlloc 0#64)
    (spkEnv : SignedPreKeyStoreBudgetEnv spkKit)
    (hspkVt : SignedPreKeyVtablesPlacedOk spkKit)
    (hspkOk : SignedPreKeyStoreKitPlacedOk A lim spkKit spkEnv ext)
    (kpkKit : KyberPreKeyStoreSpec A.repAlloc 0#64)
    (kpkEnv : KyberPreKeyStoreBudgetEnv kpkKit)
    (hkpkVt : KyberPreKeyVtablesPlacedOk kpkKit)
    (hkpkOk : KyberPreKeyStoreKitPlacedOk A lim kpkKit kpkEnv ext)
    (pkKit : PreKeyStoreSpec A.repAlloc 0#64)
    (pkEnv : PreKeyStoreBudgetEnv pkKit)
    (hpkVt : PreKeyVtablesPlacedOk pkKit)
    (hpkOk : PreKeyStoreKitPlacedOk A lim pkKit pkEnv ext)
    (stk : Nat) (hstk : stageP2OverV1CallStack spkKit kpkKit pkKit skit ≤ stk) :
    stageP2OverV1KitsFrozenAtPlacedOfEnvProp P A lim F BobV1Env AcceptErrEnv PromEnv ext
      skit senv spkKit spkEnv kpkKit kpkEnv pkKit pkEnv stk :=
  stageP2_over_v1_kits_frozen_ext_defs_placed_ofEnv ext hWF hH hPure
    (p2_errOwned_frozen_to_defs4K_placed hInitBobErrOwned)
    (p2_initBobV1FrozenPlacedOfEnv_to_4K hInitBobV1)
    ikit skit senv hskitVt hskitOk
    spkKit spkEnv hspkVt hspkOk
    kpkKit kpkEnv hkpkVt hkpkOk
    pkKit pkEnv hpkVt hpkOk
    stk ((stageP2OverV1CallStack4K_eq spkKit kpkKit pkKit skit).symm ▸ hstk)

abbrev stageP2_over_v1_kits_frozen_placed [LibsignalPlacement]
    {M : AllocCostModel} {P : Primitives} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {F : ShaCompress} {AcceptErrEnv : AcceptKeysInput → List AllocEvent → Prop} :=
  @stageP2_over_v1_kits_frozen_placed_ofEnv _ M P A lim F (InitializeBobV1OptFieldsEnv P F)
    AcceptErrEnv PromoteOverEnv

end LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Over.StageP2V1PlacedBudget
