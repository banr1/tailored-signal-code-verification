/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP2DefsPlacedBudget
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP2PurePlacedBudget
public import LibsignalBinary.Proofs.CliCBudget
public import LibsignalBinary.Proofs.E2E.Pqxdh.ResponderCore.AcceptBudget
public import LibsignalBinary.Proofs.E2E.Pqxdh.ResponderCore.AcceptPlacedABudget
public import LibsignalBinary.Proofs.E2E.Pqxdh.ResponderCore.InitBobCutPlacedBudget
public import LibsignalBinary.Proofs.E2E.Pqxdh.ResponderCore.InitBobErrOwnedPlacedBudget
public import LibsignalBinary.Proofs.PublicApi.StoreKit.IdentitySelfStoreKitBudget
public import LibsignalBinary.Proofs.PublicApi.StoreKit.KyberPreKeyStoreKitBudget
public import LibsignalBinary.Proofs.PublicApi.StoreKit.PlacedBudget
public import LibsignalBinary.Proofs.PublicApi.StoreKit.PreKeyStoreKitBudget
public import LibsignalBinary.Proofs.PublicApi.StoreKit.SignedPreKeyStoreKitBudget
public import LibsignalBinary.Proofs.RecordCodecs.DepsBudget
public import LibsignalBinary.Proofs.RecordCodecs.SignedDepsBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.AllocGhostLinkTransfer
public import LibsignalBinary.Proofs.SignalSession.Cli.KitInst.IdentityKitOkPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.KitInst.PreKeySpecsPlaced
public import LibsignalBinary.Proofs.SignalSession.Cli.KitInst.SessionKitOkCliPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Over.Stage2OverInstPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.KitCodecsPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.StagesInst.Stage2V1InstPlacedBudgetAux
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.StagesInst.Stage4V1InstPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.CliHookSatPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Store.DropSpeWordPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Store.KpkGetPollPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Store.PkGetPollPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Store.PkShimsPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Store.SpkGetPollPlacedBudget
import Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic
import LibsignalBinary.Proofs.Common.SharedHelpers
meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep
import ProofLib.SepLogic.WPp

/-!
# Budget-Threaded Relocatable `[LibsignalPlacement]` CLI Poll Stage P2 Store-Kit Discharges

Defines pre-state-pinned store poll budget envelopes (`cliStageP2KitEnvs`) and discharges
`SignedPreKeyStoreKitPlacedOk`, `PreKeyStoreKitPlacedOk`, and `KyberPreKeyStoreKitPlacedOk` at
`cliExternsPlaced mmpl W` to instantiate `StageP2PathAQpanCliPlacedAtStmt` and its
`LibsignalFrozen` counterpart.
-/

@[expose] public section

set_option autoImplicit false
set_option linter.dupNamespace false

open LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.CliHookSatPlacedBudget (CliGhostAllocHooks)
set_option maxRecDepth 200000
set_option warningAsError false

namespace LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.StagesInst.Stage2V1KitsPlacedBudgetAux

open Arm64 Arm64.Obj Arm64.Process ProofLib SepProp
open CryptoGames.LibsignalSession (PublicKey)
open CryptoVerification (
  IsLsBlockProg LibsignalFullPlacement LibsignalHooks LibsignalPlacement lsmpl lsρ lsProg_75
)
open CryptoVerification.RustHeap (RustAlloc)
open CryptoVerification.E2E (UnreachedPqxdhPrimitives acceptInput modelPrims)
open CryptoVerification.E2E.Pqxdh.Initiator (AcceptKeysInput)
open CryptoVerification.E2E.Pqxdh.ResponderCore (ofSignalPqxdhPrimitives)
open CryptoVerification.LibsignalTripleRatchetRepr (AddrGhost)
open CryptoVerification.RecordCodecs (KyberPreKeyRecord PreKeyRecord SignedPreKeyRecord)
open CryptoVerification.RecordCodecsBinary (preKeyResultAt signedPreKeyResultAt)
open CryptoVerification.RecordCodecs.Placed (lsProg_65 lsProg_595)
open CryptoVerification.LibsignalPublicApi.StoreKit (
  FsFiles LibsignalCodeRoLoaded extract_withLsCodeRoLoaded kpkGetPollOutAt
  ls_subroutine_ok_rocl_of_block preKeyGetPollOutAt spkGetPollOutAt
  subroutine_ok_rocl_of_withLsCodeRoLoaded subroutine_ok_withLsCodeRoLoaded_of_plain
  withEnvPre withLsCodeRoLoaded withLsRoCl
)
open CryptoVerification.SignalSession (
  CliHooks cliExternsPlaced lsDropOffPlaced lsDropOffPlaced_eq lsReadFileSym
)
open CryptoVerification.SignalSession.Cli (
  CliGhostHooks DirGhost KpkPollGhost KyberGhost PkPollGhost cliGhostExterns dirAt keyName kpkAnsAt
  kpkAnsOf kpkGetFutVtSym pkAnsAt pkAnsOf pkBoxAt pkGetAnsAt pkGetFutVtSym spkAnsAt spkGetFutVtSym
)
open CryptoVerification.SignalSession.Cli.Placed (
  lsProg_553 lsProg_571 lsProg_573 lsProg_576 lsProg_589 lsProg_597 lsProg_606 lsProg_608 lsProg_611
)
open CryptoVerification.SignalSession.Cli.MainHops (cliIo cliWrOk)
open CryptoVerification.SignalSession.Cli.RunSkeleton (RunBudgets)
open CryptoVerification.SignalSession.Cli.RunCompose (DecPkGhost)
open CryptoVerification.SignalSession.Cli.KitInst (
  CliKpkInv CliPkInv CliSpkInv cliKpkStoreSpec cliKyberPreKeyStoreSpec
  cliPkStoreAt cliPreKeyStoreSpec cliSignedPreKeyStoreSpec cliSpkStoreAt
  kpkAnsAt_entails_pollOut_placed pkGetAnsAt_entails_pollOut_placed
  spkAnsAt_entails_pollOut_placed
)
open CryptoVerification.SignalSession.Cli.RunProofs.Poll (
  CliKpkInvFull DpKitStk cliKitStk cliKpkStoreAtFull cliKpkStoreSpecFullPlaced
  cliPollIdKitPlaced cliPollKpkKitPlaced cliPollPkKitPlaced cliPollSelfKitPlaced
  cliPollSpkKitPlaced dpPollProgPlaced
)
open LibsignalBinary.Heap (AllocCostModel AllocEvent BudgetLimits FitsEnv RustCliAllocBudget)
open LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP2DefsPlacedBudget (
  InitializeBobV1Env
)
open LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP2PurePlacedBudget (
  InitializeBobV1OptFieldsEnv
)
open LibsignalBinary.Proofs.CliCBudget (signedHooksPlaced_of_codecHooks signedPortDepsPlaced_ok)
open LibsignalBinary.Proofs.E2E.Pqxdh.ResponderCore.AcceptBudget (pqxdhAcceptOptFieldsPlacedSpec)
open LibsignalBinary.Proofs.E2E.Pqxdh.ResponderCore.AcceptPlacedABudget (AcceptOptFieldsEnv)
open LibsignalBinary.Proofs.E2E.Pqxdh.ResponderCore.InitBobCutPlacedBudget (AcceptSuccessEnv)
open LibsignalBinary.Proofs.E2E.Pqxdh.ResponderCore.InitBobErrOwnedPlacedBudget (
  pqxdhAcceptErrOwnedPlacedSpec
)
open LibsignalBinary.Proofs.PublicApi.StoreKit.IdentitySelfStoreKitBudget (
  IdentitySelfStoreBudgetEnv
)
open LibsignalBinary.Proofs.PublicApi.StoreKit.KyberPreKeyStoreKitBudget (
  KyberPreKeyStoreBudgetEnv kitKpkGetPollSpec kitKpkGetPollSpecE kitKpkGetShimSpec
)
open LibsignalBinary.Proofs.PublicApi.StoreKit.PlacedBudget (
  IdentitySelfStoreKitPlacedOkI KyberPreKeyStoreKitPlacedOk PreKeyStoreKitPlacedOk
  SignedPreKeyStoreKitPlacedOk
)
open LibsignalBinary.Proofs.PublicApi.StoreKit.PreKeyStoreKitBudget (
  BoxAllocEnv PreKeyStoreBudgetEnv kitPreKeyGetPollSpec kitPreKeyGetPollSpecE kitPreKeyGetShimSpec
)
open LibsignalBinary.Proofs.PublicApi.StoreKit.SignedPreKeyStoreKitBudget (
  SignedPreKeyStoreBudgetEnv kitSpkGetPollSpec kitSpkGetPollSpecE kitSpkGetShimSpec
)
open LibsignalBinary.Proofs.RecordCodecs.DepsBudget (
  PreKeyDeserializeEnv RecordCodecLoopEnv
)
open LibsignalBinary.Proofs.RecordCodecs.SignedDepsBudget (
  KyberDecodeEnv SpkLoopEnv
)
open LibsignalBinary.Proofs.SignalSession.Cli.Dir.Decimal.ExecPlacedBudget (DecimalEnv)
open LibsignalBinary.Proofs.SignalSession.Cli.Dir.Get.PlacedBudgetAux1a (DirGetEnv)
open LibsignalBinary.Proofs.SignalSession.Cli.Dir.Path.PlacedBudget (PathEnv)
open LibsignalBinary.Proofs.SignalSession.Cli.KitInst.IdentityKitOkPlacedBudget (
  cliIdFutDrop_rocl_placed_ok
)
open LibsignalBinary.Proofs.SignalSession.Cli.KitInst.SessionKitOkCliPlacedBudget (
  cliDecimal_placed_ok cliDirGet_placed_ok
)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Over.Stage2OverInstPlacedBudget (
  CliPollStageP2Envs
)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.ClosureStagesStmtPlacedBudget (
  RunHooksPlaced
)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.KitCodecsPlacedBudget (
  cliDecodeKyberPreKey_placed_ok cliDecodeSignedPreKey_placed_ok cliPreKeyDeserialize_placed_ok
)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.StagesInst.Stage2V1InstPlacedBudgetAux (
  P2PathAErrEnvOf P2PathAOkEnvOf StageP2PathAQpanCliFrozenPlacedAtStmt
  StageP2PathAQpanCliPlacedAtStmt stageP2PathA_qpan_cli_full_placed_at_of_seams
  stageP2PathA_qpan_cli_placed_at_of_seams
)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.StagesInst.Stage4V1InstPlacedBudget (
  cliPollKpkMarkPollEnv cliPollKpk_markKitPlacedOk
  cliPollPkRemovePollEnv cliPollPk_removeKitPlacedOk
)
open LibsignalBinary.Proofs.SignalSession.Cli.SpecsPlacedBudget (
  AllocContractsXCliPlaced kpkGetPollSpecPlaced pkGetPollSpecPlaced pkGetPollSpecOfPlaced
  pkShimSpecPlaced readFileSpecPlaced spkGetPollSpecPlaced
)
open LibsignalBinary.Proofs.SignalSession.Cli.SpqrV1PlacedSeamsBudget (SpqrV1PlacedSeams)
open LibsignalBinary.Proofs.SignalSession.Cli.Store.DropSpeWordPlacedBudget (dropSpeWord_placed_ok)
open LibsignalBinary.Proofs.SignalSession.Cli.Store.KpkGetPoll.LayoutBudget (CliKpkGetPollEnv)
open LibsignalBinary.Proofs.SignalSession.Cli.Store.KpkGetPollPlacedBudget (
  kpkGetPoll_placed_fs_caller_ok_of_deps
)
open LibsignalBinary.Proofs.SignalSession.Cli.Store.PkGetPoll.LayoutBudget (CliPkGetPollEnv)
open LibsignalBinary.Proofs.SignalSession.Cli.Store.PkGetPollPlacedBudget (
  pkGetPoll_placed_fs_caller_ok_of_deps
)
open LibsignalBinary.Proofs.SignalSession.Cli.Store.PkShimsPlacedBudget (
  kpkGetShim_placed_ok_of_deps pkGetShim_placed_ok_of_deps spkGetShim_placed_ok_of_deps
)
open LibsignalBinary.Proofs.SignalSession.Cli.Store.SpkGetPoll.CalleesBudget (CliSpkGetPollEnv)
open LibsignalBinary.Proofs.SignalSession.Cli.Store.SpkGetPollPlacedBudget (
  spkGetPoll_placed_fs_caller_ok_of_deps
)

/-! ## 1. Hook Conversion & Concrete Store Poll Envelopes -/

private theorem toSkeletonRunHooks [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {ext : LibsignalHooks}
    (hh : RunHooksPlaced A lim ext) :
    LibsignalBinary.Proofs.SignalSession.Cli.Run.SkeletonPlacedBudget.RunHooksPlaced A lim ext :=
  { alloc := hh.alloc, allocFs := hh.allocFs, panics := hh.panics, memcpyRO := hh.memcpyRO,
    bcmp := hh.bcmp, fs := hh.fs, utf8 := hh.utf8, memrchr := hh.memrchr,
    codecHooks := hh.codecHooks, allocZeroed := hh.allocZeroed, stringClone := hh.stringClone,
    formatInner := hh.formatInner }

/-- Disjunction envelope for `decode_signed_pre_key` / `decode_kyber_pre_key` (Block `595`). -/
def CliSpkDecodeEnv (bs : List (BitVec 8)) (evs : List AllocEvent) : Prop :=
  SpkLoopEnv (2 * bs.length + 3) bs.length evs ∨ KyberDecodeEnv bs.length evs

/-- Disjunction envelope for `PreKeyRecord::deserialize` (Block `65`). -/
def CliPkDecodeEnv (bs : List (BitVec 8)) (evs : List AllocEvent) : Prop :=
  RecordCodecLoopEnv (2 * bs.length + 3) bs.length evs ∨ PreKeyDeserializeEnv bs.length evs

/-- Concrete `get_signed_pre_key` poll allocation envelope for `cliPollSpkKitPlaced`. -/
def cliPollSpkGetPollEnv
    (ReadEnv : FsFiles → List (BitVec 8) → List AllocEvent → Prop)
    (F0 : FsFiles) (dir : DirGhost) (id : BitVec 32) : List AllocEvent → Prop :=
  CliSpkGetPollEnv DecimalEnv
    (fun d k => DirGetEnv PathEnv ReadEnv cliIo.rd F0 d (keyName k))
    CliSpkDecodeEnv cliIo.rd F0 ⟨0#64, 0#64, 0#64, id, dir⟩

/-- Concrete `get_pre_key` poll allocation envelope for `cliPollPkKitPlaced`. -/
def cliPollPkGetPollEnv
    (ReadEnv : FsFiles → List (BitVec 8) → List AllocEvent → Prop)
    (F0 : FsFiles) (dir : DirGhost) (id : BitVec 32) : List AllocEvent → Prop :=
  CliPkGetPollEnv DecimalEnv
    (DirGetEnv PathEnv ReadEnv cliIo.rd F0)
    CliPkDecodeEnv cliIo.rd F0 ⟨0#64, 0#64, 0#64, id, dir⟩

/-- Concrete `get_kyber_pre_key` poll allocation envelope for `cliPollKpkKitPlaced`. -/
def cliPollKpkGetPollEnv
    (ReadEnv : FsFiles → List (BitVec 8) → List AllocEvent → Prop)
    (F0 : FsFiles) (kg : KyberGhost) (id : BitVec 32) : List AllocEvent → Prop :=
  CliKpkGetPollEnv DecimalEnv
    (fun d k => DirGetEnv PathEnv ReadEnv cliIo.rd F0 d (keyName k))
    CliSpkDecodeEnv cliIo.rd F0 ⟨0#64, 0#64, 0#64, id, kg⟩

/-- Full `SignedPreKeyStoreBudgetEnv` for `cliPollSpkKitPlaced`. -/
def cliPollSpkFullBudgetEnv [LibsignalPlacement] (A : RustAlloc) (F0 : FsFiles)
    (spkId : BitVec 32) (σ : DpKitStk)
    (ReadEnv : FsFiles → List (BitVec 8) → List AllocEvent → Prop) :
    SignedPreKeyStoreBudgetEnv (cliPollSpkKitPlaced A F0 spkId σ) where
  getPollEnv := cliPollSpkGetPollEnv ReadEnv F0

/-- Full `PreKeyStoreBudgetEnv` (`get_pre_key` + `remove_pre_key`) for `cliPollPkKitPlaced`. -/
def cliPollPkFullBudgetEnv [LibsignalPlacement] (A : RustAlloc) (F0 : FsFiles)
    (pkId : BitVec 32) (σ : DpKitStk)
    (ReadEnv : FsFiles → List (BitVec 8) → List AllocEvent → Prop) :
    PreKeyStoreBudgetEnv (cliPollPkKitPlaced A F0 pkId σ) where
  getPollEnv := cliPollPkGetPollEnv ReadEnv F0
  removePollEnv := cliPollPkRemovePollEnv ReadEnv F0

/-- Full `KyberPreKeyStoreBudgetEnv` (`get_kyber_pre_key` + `mark_kyber_pre_key_used`) for
`cliPollKpkKitPlaced`. -/
def cliPollKpkFullBudgetEnv [LibsignalPlacement] (A : RustAlloc) (F0 : FsFiles)
    (kpkId spkId : BitVec 32) (kbk : PublicKey) (σ : DpKitStk)
    (ReadEnv : FsFiles → List (BitVec 8) → List AllocEvent → Prop) :
    KyberPreKeyStoreBudgetEnv (cliPollKpkKitPlaced A F0 kpkId spkId kbk σ) where
  getPollEnv := cliPollKpkGetPollEnv ReadEnv F0
  markPollEnv := cliPollKpkMarkPollEnv ReadEnv F0

/-- Bundled 4-kit Stage P2 budget envelopes for CLI Poll (`self`, `spk`, `kpk`, `pk`). -/
def cliStageP2KitEnvs [LibsignalPlacement] {A : RustAlloc}
    (ReadEnv : FsFiles → List (BitVec 8) → List AllocEvent → Prop)
    (B : RunBudgets)
    (senv : ∀ (F0 : FsFiles) (peer : AddrGhost),
      IdentitySelfStoreBudgetEnv (cliPollSelfKitPlaced A F0 peer (cliKitStk B)))
    (F0 : FsFiles) (peer : AddrGhost)
    (spkId kpkId opkWord : BitVec 32) (kbk : PublicKey) :
    CliPollStageP2Envs (A := A) B F0 peer spkId kpkId opkWord kbk where
  selfEnv := senv F0 peer
  spkEnv := cliPollSpkFullBudgetEnv A F0 spkId (cliKitStk B) ReadEnv
  kpkEnv := cliPollKpkFullBudgetEnv A F0 kpkId spkId kbk (cliKitStk B) ReadEnv
  pkEnv := cliPollPkFullBudgetEnv A F0 opkWord (cliKitStk B) ReadEnv

/-! ## 2. Shims (`606`, `608`, `611`) -/

private theorem cliPollSpk_getShim_placed_ok [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    (B : RunBudgets) (F0 : FsFiles) (spkId : BitVec 32)
    (hC : AllocContractsXCliPlaced A lim H) :
    subroutine_ok (lsProg_606 H) (lsmpl.base 606)
      (withLsCodeRoLoaded lsmpl
        (kitSpkGetShimSpec M A lim
          (cliPollSpkKitPlaced A.repAlloc F0 spkId (cliKitStk B)))) := by
  let spkKit := cliPollSpkKitPlaced A.repAlloc F0 spkId (cliKitStk B)
  have hshim := spkGetShim_placed_ok_of_deps (stk := (cliKitStk B).spkGetShim)
    hC (by dsimp [cliKitStk]; omega)
  refine subroutine_ok.of_codeLoaded fun ⟨⟨self, id⟩, st⟩ R s0 hpc hrun hpre hsp _ => ?_
  obtain ⟨hcrl, hpre1⟩ := extract_withLsCodeRoLoaded hpre
  change s0.mem ⊨
    (⌜(0#64 &&& 0xfff#64) = 0#64 ∧ s0.readReg64 .x0 = self ∧ s0.readReg32 .x1 = id ∧
        FitsEnv M lim st (BoxAllocEnv 16)⌝ ∗
      A.pool lim st s0 ∗ stackAt s0.sp (cliKitStk B).spkGetShim) ∗ R at hpre1
  rw [sepConj_assoc, sepConj_assoc, satisfies_pure_sepConj] at hpre1
  obtain ⟨⟨_, hx0, hx1, hfit⟩, hmem⟩ := hpre1
  have hpre_shim : s0.mem ⊨
      (pkShimSpecPlaced spkGetFutVtSym A lim (cliKitStk B).spkGetShim).pre
        (⟨self, id⟩, st) s0 ∗ R := by
    dsimp only [pkShimSpecPlaced, withLsCodeRoLoaded]
    rw [sepConj_assoc, sepConj_left_comm, satisfies_pure_sepConj]
    refine ⟨hcrl, ?_⟩
    rw [sepConj_assoc, sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨⟨hx0, hx1, hfit⟩, hmem⟩
  refine subroutine_ok.mono_outcome hshim (⟨self, id⟩, st) R s0 hpc hrun hpre_shim hsp
    fun sf hout => ?_
  rcases hout with ⟨hret, hcc, hpost⟩ | hpan | hex | hoom
  · refine Or.inl ⟨hret, hcc, ?_⟩
    dsimp only [withLsCodeRoLoaded, kitSpkGetShimSpec, spkKit, cliPollSpkKitPlaced,
      CryptoVerification.SignalSession.Cli.KitInst.cliSignedPreKeyStoreSpecPlaced,
      CryptoVerification.SignalSession.Cli.RunProofs.Poll.cliSignedPreKeyStoreSpecPlaced,
      cliSignedPreKeyStoreSpec]
    dsimp only [pkShimSpecPlaced, withLsCodeRoLoaded] at hpost
    simpa only [BitVec.zero_add] using hpost
  · exact Or.inr (Or.inl hpan)
  · exact Or.inr (Or.inr (Or.inl hex))
  · exact Or.inr (Or.inr (Or.inr hoom))

private theorem cliPollSpk_getShim_rocl [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    (mmpl : Obj.MultiPlacement) (gh : CliGhostHooks) (W : CliHooks)
    (B : RunBudgets) (F0 : FsFiles) (spkId : BitVec 32)
    (hh : RunHooksPlaced A lim (cliGhostExterns gh (cliExternsPlaced mmpl W)))
    {callerProg : Program} {callerBlk : Nat}
    [IsLsBlockProg callerProg callerBlk (cliGhostExterns gh (cliExternsPlaced mmpl W))] (hblk : callerBlk < 619) :
    let spkKit := cliPollSpkKitPlaced A.repAlloc F0 spkId (cliKitStk B)
    subroutine_ok callerProg (0#64 + spkKit.getShimOff)
      (withLsRoCl lsmpl (kitSpkGetShimSpec M A lim spkKit)) := by
  intro spkKit
  have hrocl := ls_subroutine_ok_rocl_of_block (callerProg := callerProg) (j := 606)
    (cliPollSpk_getShim_placed_ok B F0 spkId hh.alloc) hblk (by decide) (by decide)
  change subroutine_ok callerProg (0#64 + lsmpl.base 606) _
  rw [BitVec.zero_add]
  exact hrocl

private theorem cliPollPk_getShim_placed_ok [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    (B : RunBudgets) (F0 : FsFiles) (pkId : BitVec 32)
    (hC : AllocContractsXCliPlaced A lim H) :
    subroutine_ok (lsProg_608 H) (lsmpl.base 608)
      (withLsCodeRoLoaded lsmpl
        (kitPreKeyGetShimSpec M A lim
          (cliPollPkKitPlaced A.repAlloc F0 pkId (cliKitStk B)))) := by
  let pkKit := cliPollPkKitPlaced A.repAlloc F0 pkId (cliKitStk B)
  have hshim := pkGetShim_placed_ok_of_deps (stk := (cliKitStk B).pkGetShim)
    hC (by dsimp [cliKitStk]; omega)
  refine subroutine_ok.of_codeLoaded fun ⟨⟨self, id⟩, st⟩ R s0 hpc hrun hpre hsp _ => ?_
  obtain ⟨hcrl, hpre1⟩ := extract_withLsCodeRoLoaded hpre
  change s0.mem ⊨
    (⌜(0#64 &&& 0xfff#64) = 0#64 ∧ s0.readReg64 .x0 = self ∧ s0.readReg32 .x1 = id ∧
        FitsEnv M lim st (BoxAllocEnv 16)⌝ ∗
      A.pool lim st s0 ∗ stackAt s0.sp (cliKitStk B).pkGetShim) ∗ R at hpre1
  rw [sepConj_assoc, sepConj_assoc, satisfies_pure_sepConj] at hpre1
  obtain ⟨⟨_, hx0, hx1, hfit⟩, hmem⟩ := hpre1
  have hpre_shim : s0.mem ⊨
      (pkShimSpecPlaced pkGetFutVtSym A lim (cliKitStk B).pkGetShim).pre
        (⟨self, id⟩, st) s0 ∗ R := by
    dsimp only [pkShimSpecPlaced, withLsCodeRoLoaded]
    rw [sepConj_assoc, sepConj_left_comm, satisfies_pure_sepConj]
    refine ⟨hcrl, ?_⟩
    rw [sepConj_assoc, sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨⟨hx0, hx1, hfit⟩, hmem⟩
  refine subroutine_ok.mono_outcome hshim (⟨self, id⟩, st) R s0 hpc hrun hpre_shim hsp
    fun sf hout => ?_
  rcases hout with ⟨hret, hcc, hpost⟩ | hpan | hex | hoom
  · refine Or.inl ⟨hret, hcc, ?_⟩
    dsimp only [withLsCodeRoLoaded, kitPreKeyGetShimSpec, pkKit, cliPollPkKitPlaced,
      CryptoVerification.SignalSession.Cli.KitInst.cliPreKeyStoreSpecPlaced,
      CryptoVerification.SignalSession.Cli.RunProofs.Poll.cliPreKeyStoreSpecPlaced,
      cliPreKeyStoreSpec]
    dsimp only [pkShimSpecPlaced, withLsCodeRoLoaded] at hpost
    simpa only [BitVec.zero_add] using hpost
  · exact Or.inr (Or.inl hpan)
  · exact Or.inr (Or.inr (Or.inl hex))
  · exact Or.inr (Or.inr (Or.inr hoom))

private theorem cliPollPk_getShim_rocl [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    (mmpl : Obj.MultiPlacement) (gh : CliGhostHooks) (W : CliHooks)
    (B : RunBudgets) (F0 : FsFiles) (pkId : BitVec 32)
    (hh : RunHooksPlaced A lim (cliGhostExterns gh (cliExternsPlaced mmpl W)))
    {callerProg : Program} {callerBlk : Nat}
    [IsLsBlockProg callerProg callerBlk (cliGhostExterns gh (cliExternsPlaced mmpl W))] (hblk : callerBlk < 619) :
    let pkKit := cliPollPkKitPlaced A.repAlloc F0 pkId (cliKitStk B)
    subroutine_ok callerProg (0#64 + pkKit.getShimOff)
      (withLsRoCl lsmpl (kitPreKeyGetShimSpec M A lim pkKit)) := by
  intro pkKit
  have hrocl := ls_subroutine_ok_rocl_of_block (callerProg := callerProg) (j := 608)
    (cliPollPk_getShim_placed_ok B F0 pkId hh.alloc) hblk (by decide) (by decide)
  change subroutine_ok callerProg (0#64 + lsmpl.base 608) _
  rw [BitVec.zero_add]
  exact hrocl

private theorem cliPollKpk_getShim_placed_ok [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    (B : RunBudgets) (F0 : FsFiles) (kpkId spkId : BitVec 32) (kbk : PublicKey)
    (hC : AllocContractsXCliPlaced A lim H) :
    subroutine_ok (lsProg_611 H) (lsmpl.base 611)
      (withLsCodeRoLoaded lsmpl
        (kitKpkGetShimSpec M A lim
          (cliPollKpkKitPlaced A.repAlloc F0 kpkId spkId kbk (cliKitStk B)))) := by
  let kpkKit := cliPollKpkKitPlaced A.repAlloc F0 kpkId spkId kbk (cliKitStk B)
  have hshim := kpkGetShim_placed_ok_of_deps (stk := (cliKitStk B).kpkGetShim)
    hC (by dsimp [cliKitStk]; omega)
  refine subroutine_ok.of_codeLoaded fun ⟨⟨self, id⟩, st⟩ R s0 hpc hrun hpre hsp _ => ?_
  obtain ⟨hcrl, hpre1⟩ := extract_withLsCodeRoLoaded hpre
  change s0.mem ⊨
    (⌜(0#64 &&& 0xfff#64) = 0#64 ∧ s0.readReg64 .x0 = self ∧ s0.readReg32 .x1 = id ∧
        FitsEnv M lim st (BoxAllocEnv 16)⌝ ∗
      A.pool lim st s0 ∗ stackAt s0.sp (cliKitStk B).kpkGetShim) ∗ R at hpre1
  rw [sepConj_assoc, sepConj_assoc, satisfies_pure_sepConj] at hpre1
  obtain ⟨⟨_, hx0, hx1, hfit⟩, hmem⟩ := hpre1
  have hpre_shim : s0.mem ⊨
      (pkShimSpecPlaced kpkGetFutVtSym A lim (cliKitStk B).kpkGetShim).pre
        (⟨self, id⟩, st) s0 ∗ R := by
    dsimp only [pkShimSpecPlaced, withLsCodeRoLoaded]
    rw [sepConj_assoc, sepConj_left_comm, satisfies_pure_sepConj]
    refine ⟨hcrl, ?_⟩
    rw [sepConj_assoc, sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨⟨hx0, hx1, hfit⟩, hmem⟩
  refine subroutine_ok.mono_outcome hshim (⟨self, id⟩, st) R s0 hpc hrun hpre_shim hsp
    fun sf hout => ?_
  rcases hout with ⟨hret, hcc, hpost⟩ | hpan | hex | hoom
  · refine Or.inl ⟨hret, hcc, ?_⟩
    dsimp only [withLsCodeRoLoaded, kitKpkGetShimSpec, kpkKit, cliPollKpkKitPlaced,
      cliKpkStoreSpecFullPlaced,
      CryptoVerification.SignalSession.Cli.KitInst.cliKyberPreKeyStoreSpecPlaced,
      CryptoVerification.SignalSession.Cli.RunProofs.Poll.cliKyberPreKeyStoreSpecPlaced,
      cliKyberPreKeyStoreSpec, cliKpkStoreSpec]
    dsimp only [pkShimSpecPlaced, withLsCodeRoLoaded] at hpost
    simpa only [BitVec.zero_add] using hpost
  · exact Or.inr (Or.inl hpan)
  · exact Or.inr (Or.inr (Or.inl hex))
  · exact Or.inr (Or.inr (Or.inr hoom))

private theorem cliPollKpk_getShim_rocl [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    (mmpl : Obj.MultiPlacement) (gh : CliGhostHooks) (W : CliHooks)
    (B : RunBudgets) (F0 : FsFiles) (kpkId spkId : BitVec 32) (kbk : PublicKey)
    (hh : RunHooksPlaced A lim (cliGhostExterns gh (cliExternsPlaced mmpl W)))
    {callerProg : Program} {callerBlk : Nat}
    [IsLsBlockProg callerProg callerBlk (cliGhostExterns gh (cliExternsPlaced mmpl W))] (hblk : callerBlk < 619) :
    let kpkKit := cliPollKpkKitPlaced A.repAlloc F0 kpkId spkId kbk (cliKitStk B)
    subroutine_ok callerProg (0#64 + kpkKit.getShimOff)
      (withLsRoCl lsmpl (kitKpkGetShimSpec M A lim kpkKit)) := by
  intro kpkKit
  have hrocl := ls_subroutine_ok_rocl_of_block (callerProg := callerProg) (j := 611)
    (cliPollKpk_getShim_placed_ok B F0 kpkId spkId kbk hh.alloc) hblk (by decide) (by decide)
  change subroutine_ok callerProg (0#64 + lsmpl.base 611) _
  rw [BitVec.zero_add]
  exact hrocl

/-! ## 3. Poll Closures (`571`, `573`, `576`) & Store-Kit Bundles -/

private theorem cliPollSpk_getPoll_rocl [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ReadEnv : FsFiles → List (BitVec 8) → List AllocEvent → Prop}
    (mmpl : Obj.MultiPlacement) (gh : CliGhostHooks) (W : CliHooks)
    (B : RunBudgets) (F0 : FsFiles) (spkId : BitVec 32)
    (hh : RunHooksPlaced A lim (cliGhostExterns gh (cliExternsPlaced mmpl W)))
    (hRead : subroutine_ok (dpPollProgPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W))) (lsρ lsReadFileSym)
      (readFileSpecPlaced cliIo.rd cliWrOk A lim B.readFile ReadEnv))
    {callerProg : Program} {callerBlk : Nat}
    [IsLsBlockProg callerProg callerBlk (cliGhostExterns gh (cliExternsPlaced mmpl W))] (hblk : callerBlk < 619) :
    let spkKit := cliPollSpkKitPlaced A.repAlloc F0 spkId (cliKitStk B)
    subroutine_ok callerProg (0#64 + spkKit.getPollOff)
      (withLsRoCl lsmpl
        (kitSpkGetPollSpecE M A lim spkKit
          (cliPollSpkFullBudgetEnv A.repAlloc F0 spkId (cliKitStk B) ReadEnv))) := by
  intro spkKit
  let spkEnv := cliPollSpkFullBudgetEnv A.repAlloc F0 spkId (cliKitStk B) ReadEnv
  let hhSkel := toSkeletonRunHooks hh
  have hDecimal := cliDecimal_placed_ok hhSkel
  have hGet := cliDirGet_placed_ok
    (readProg := dpPollProgPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W))) (jRead := 518)
    (fun _ hp => hp.2) hhSkel
    (subroutine_ok_withLsCodeRoLoaded_of_plain hRead) (by decide) (by decide)
  have hSpkDec := cliDecodeSignedPreKey_placed_ok A lim mmpl gh W
    (signedHooksPlaced_of_codecHooks hh.codecHooks) (signedPortDepsPlaced_ok hh.codecHooks)
  have hhop := spkGetPoll_placed_fs_caller_ok_of_deps
    (callerProg := callerProg) (i := callerBlk)
    (decProg := lsProg_597 (cliGhostExterns gh (cliExternsPlaced mmpl W))) (decBlk := 597)
    (getProg := lsProg_589 (cliGhostExterns gh (cliExternsPlaced mmpl W))) (getBlk := 589)
    (spkDecProg := lsProg_595 (cliGhostExterns gh (cliExternsPlaced mmpl W))) (spkDecBlk := 595)
    (dropProg := lsProg_553 (cliGhostExterns gh (cliExternsPlaced mmpl W))) (dropBlk := 553)
    (stk := (cliKitStk B).spkGetPoll)
    hh.alloc hDecimal hGet hSpkDec (dropSpeWord_placed_ok hh.alloc)
    (hh.fs (lsProg_571 (cliGhostExterns gh (cliExternsPlaced mmpl W))) 571)
    (Nat.le_refl _) (fun _ _ => Or.inl) (fun _ _ => Or.inr) hblk
  change subroutine_ok callerProg (0#64 + lsmpl.base 571) _
  rw [BitVec.zero_add]
  refine subroutine_ok_rocl_of_withLsCodeRoLoaded ?_
  refine subroutine_ok.of_codeLoaded
    fun ⟨⟨fut, out, self, id⟩, st0, st⟩ R s0 hpc hrun hpre hsp _ => ?_
  change DirGhost at st0
  obtain ⟨hcrl, hpre1⟩ := extract_withLsCodeRoLoaded hpre
  have hpre2 : s0.mem ⊨ ⌜s0.fs.files = F0⌝ ∗
      ((kitSpkGetPollSpec M A lim spkKit spkEnv).pre (⟨fut, out, self, id⟩, st0, st) s0 ∗ R) := by
    change s0.mem ⊨ (⌜s0.fs.files = F0⌝ ∗
      (kitSpkGetPollSpec M A lim spkKit spkEnv).pre (⟨fut, out, self, id⟩, st0, st) s0) ∗ R at hpre1
    simpa only [sepConj_assoc] using hpre1
  rw [satisfies_pure_sepConj] at hpre2
  obtain ⟨hfiles, hpre3⟩ := hpre2
  change s0.mem ⊨
    (⌜(0#64 &&& 0xfff#64) = 0#64 ∧ s0.readReg64 .x0 = fut ∧ s0.readReg64 .x8 = out ∧
        id = spkId ∧ FitsEnv M lim st (cliPollSpkGetPollEnv ReadEnv F0 st0 id)⌝ ∗
      pkBoxAt fut self id 0#8 ∗
      (⌜CliSpkInv cliIo.rd F0 cliWrOk spkId st0⌝ ∗ dirAt A.repAlloc self st0) ∗
      memRegion out 88 ∗ A.pool lim st s0 ∗ stackAt s0.sp (cliKitStk B).spkGetPoll) ∗ R at hpre3
  rw [sepConj_assoc, satisfies_pure_sepConj] at hpre3
  obtain ⟨⟨_, hx0, hx8, rfl, hfit_kit⟩, hpre4⟩ := hpre3
  have hpre5 : s0.mem ⊨ ⌜CliSpkInv cliIo.rd F0 cliWrOk id st0⌝ ∗
      (pkBoxAt fut self id 0#8 ∗ dirAt A.repAlloc self st0 ∗ memRegion out 88 ∗
        A.pool lim st s0 ∗ stackAt s0.sp (cliKitStk B).spkGetPoll ∗ R) :=
    Satisfies.mono (Entails.of_eq (by ac_rfl)) hpre4
  rw [satisfies_pure_sepConj] at hpre5
  obtain ⟨hinv, hspatial⟩ := hpre5
  let xg : PkPollGhost := ⟨fut, out, self, id, st0⟩
  let PollEnv := fun F (x : PkPollGhost) =>
    CliSpkGetPollEnv DecimalEnv (fun dir k => DirGetEnv PathEnv ReadEnv cliIo.rd F dir (keyName k))
      CliSpkDecodeEnv cliIo.rd F x
  have hfit_hop : FitsEnv M lim st (PollEnv s0.fs.files xg) := fun evs hm => by
    rw [hfiles] at hm
    exact hfit_kit evs hm
  have hpre_hop : s0.mem ⊨
      (spkGetPollSpecPlaced cliIo.rd cliWrOk A lim PollEnv (cliKitStk B).spkGetPoll).pre
        (xg, st) s0 ∗ R := by
    dsimp only [spkGetPollSpecPlaced, pkGetPollSpecOfPlaced, withLsCodeRoLoaded]
    rw [sepConj_assoc, sepConj_left_comm, satisfies_pure_sepConj]
    refine ⟨hcrl, ?_⟩
    rw [sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨⟨hx0, hx8, hinv.nameOk, hfiles ▸ hinv.sizeOk, hfit_hop⟩, ?_⟩
    simpa only [sepConj_assoc] using hspatial
  refine subroutine_ok.mono_outcome hhop (xg, st) R s0 hpc hrun hpre_hop hsp fun sf hout => ?_
  rcases hout with ⟨hret, hcc, hpost⟩ | hpan | hex | hoom
  · refine Or.inl ⟨hret, hcc, Satisfies.mono (sepConj_mono_left ?_) hpost⟩
    show (spkGetPollSpecPlaced cliIo.rd cliWrOk A lim PollEnv (cliKitStk B).spkGetPoll).post
        (xg, st) s0 sf ⊢
      (kitSpkGetPollSpec M A lim spkKit spkEnv).post (⟨fut, out, self, id⟩, st0, st) s0 sf
    dsimp only [spkGetPollSpecPlaced, pkGetPollSpecOfPlaced, kitSpkGetPollSpec, spkKit, spkEnv,
      cliPollSpkFullBudgetEnv, cliPollSpkKitPlaced,
      CryptoVerification.SignalSession.Cli.KitInst.cliSignedPreKeyStoreSpecPlaced,
      CryptoVerification.SignalSession.Cli.RunProofs.Poll.cliSignedPreKeyStoreSpecPlaced,
      cliSignedPreKeyStoreSpec, cliSpkStoreAt, xg]
    refine Entails.sepExists_elim fun evs => ?_
    rw [sepExists_sepConj_left]
    refine Entails.sepExists_elim fun pa => ?_
    rw [sepConj_assoc]
    refine Entails.pure_left fun ⟨hpa, htr, hmenv⟩ => ?_
    rw [hfiles] at hpa hmenv
    subst hpa
    have hent0 := spkAnsAt_entails_pollOut_placed A.repAlloc cliIo.rd F0 cliWrOk id
      (cliKitStk B).spkGetShim (cliKitStk B).spkGetPoll st0 id out
    dsimp only at hent0
    have hout_eq : spkGetPollOutAt
        (CryptoVerification.SignalSession.Cli.KitInst.cliSignedPreKeyStoreSpecPlaced
          A.repAlloc cliIo.rd F0 cliWrOk id
          (cliKitStk B).spkGetShim (cliKitStk B).spkGetPoll) out =
      spkGetPollOutAt spkKit out := by
      funext ans; cases ans <;> rfl
    rw [hout_eq] at hent0
    refine Entails.trans (sepConj_mono_left hent0) ?_
    rw [sepExists_sepConj_left]
    refine Entails.sepExists_elim fun ans => ?_
    rw [sepConj_assoc]
    refine Entails.pure_left fun hrel => ?_
    refine Entails.sepExists_right ans (Entails.sepExists_right evs ?_)
    refine Entails.pure_right ⟨hrel, by rw [List.append_nil]; exact htr, hmenv⟩ ?_
    exact Entails.trans (Entails.pure_right hinv (Entails.refl _)) (Entails.of_eq (by ac_rfl))
  · exact Or.inr (Or.inl hpan)
  · exact Or.inr (Or.inr (Or.inl hex))
  · exact Or.inr (Or.inr (Or.inr hoom))

/-- Discharges `SignedPreKeyStoreKitPlacedOk` for `cliPollSpkKitPlaced` from `RunHooksPlaced` and
`hRead`. -/
theorem cliPollSpk_kitPlacedOk [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ReadEnv : FsFiles → List (BitVec 8) → List AllocEvent → Prop}
    (mmpl : Obj.MultiPlacement) (gh : CliGhostHooks) (W : CliHooks)
    (B : RunBudgets) (F0 : FsFiles) (spkId : BitVec 32)
    (hDropNz : lsmpl.base 547 ≠ 0#64)
    (hh : RunHooksPlaced A lim (cliGhostExterns gh (cliExternsPlaced mmpl W)))
    (hRead : subroutine_ok (dpPollProgPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W))) (lsρ lsReadFileSym)
      (readFileSpecPlaced cliIo.rd cliWrOk A lim B.readFile ReadEnv)) :
    SignedPreKeyStoreKitPlacedOk A lim
      (cliPollSpkKitPlaced A.repAlloc F0 spkId (cliKitStk B))
      (cliPollSpkFullBudgetEnv A.repAlloc F0 spkId (cliKitStk B) ReadEnv)
      (cliGhostExterns gh (cliExternsPlaced mmpl W)) where
  getShim hblk := cliPollSpk_getShim_rocl mmpl gh W B F0 spkId hh hblk
  getPoll hblk := cliPollSpk_getPoll_rocl mmpl gh W B F0 spkId hh hRead hblk
  getFutDrop hblk := by
    change subroutine_ok _ (0#64 + lsDropOffPlaced) _
    rw [lsDropOffPlaced_eq hDropNz]
    exact cliIdFutDrop_rocl_placed_ok hblk

private theorem cliPollPk_getPoll_rocl [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ReadEnv : FsFiles → List (BitVec 8) → List AllocEvent → Prop}
    (mmpl : Obj.MultiPlacement) (gh : CliGhostHooks) (W : CliHooks)
    (B : RunBudgets) (F0 : FsFiles) (pkId : BitVec 32)
    (hh : RunHooksPlaced A lim (cliGhostExterns gh (cliExternsPlaced mmpl W)))
    (hRead : subroutine_ok (dpPollProgPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W))) (lsρ lsReadFileSym)
      (readFileSpecPlaced cliIo.rd cliWrOk A lim B.readFile ReadEnv))
    {callerProg : Program} {callerBlk : Nat}
    [IsLsBlockProg callerProg callerBlk (cliGhostExterns gh (cliExternsPlaced mmpl W))] (hblk : callerBlk < 619) :
    let pkKit := cliPollPkKitPlaced A.repAlloc F0 pkId (cliKitStk B)
    subroutine_ok callerProg (0#64 + pkKit.getPollOff)
      (withLsRoCl lsmpl
        (kitPreKeyGetPollSpecE M A lim pkKit
          (cliPollPkFullBudgetEnv A.repAlloc F0 pkId (cliKitStk B) ReadEnv))) := by
  intro pkKit
  let pkEnv := cliPollPkFullBudgetEnv A.repAlloc F0 pkId (cliKitStk B) ReadEnv
  let hhSkel := toSkeletonRunHooks hh
  have hDecimal := cliDecimal_placed_ok hhSkel
  have hGet := cliDirGet_placed_ok
    (readProg := dpPollProgPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W))) (jRead := 518)
    (fun _ hp => hp.2) hhSkel
    (subroutine_ok_withLsCodeRoLoaded_of_plain hRead) (by decide) (by decide)
  have hPkDec := cliPreKeyDeserialize_placed_ok A lim mmpl gh W hhSkel
  have hhop := pkGetPoll_placed_fs_caller_ok_of_deps
    (callerProg := callerProg) (i := callerBlk)
    (decProg := lsProg_597 (cliGhostExterns gh (cliExternsPlaced mmpl W))) (decBlk := 597)
    (getProg := lsProg_589 (cliGhostExterns gh (cliExternsPlaced mmpl W))) (getBlk := 589)
    (pkDecProg := lsProg_65 (cliGhostExterns gh (cliExternsPlaced mmpl W))) (pkDecBlk := 65)
    (dropProg := lsProg_553 (cliGhostExterns gh (cliExternsPlaced mmpl W))) (dropBlk := 553)
    (stk := (cliKitStk B).pkGetPoll)
    hh.alloc hDecimal hGet hPkDec (dropSpeWord_placed_ok hh.alloc)
    (hh.fs (lsProg_573 (cliGhostExterns gh (cliExternsPlaced mmpl W))) 573)
    (Nat.le_refl _) (fun _ _ => Or.inl) (fun _ _ => Or.inr) hblk
  change subroutine_ok callerProg (0#64 + lsmpl.base 573) _
  rw [BitVec.zero_add]
  refine subroutine_ok_rocl_of_withLsCodeRoLoaded ?_
  refine subroutine_ok.of_codeLoaded
    fun ⟨⟨fut, out, self, id⟩, st0, st⟩ R s0 hpc hrun hpre hsp _ => ?_
  change DirGhost at st0
  obtain ⟨hcrl, hpre1⟩ := extract_withLsCodeRoLoaded hpre
  have hpre2 : s0.mem ⊨ ⌜s0.fs.files = F0⌝ ∗
      ((kitPreKeyGetPollSpec M A lim pkKit pkEnv).pre (⟨fut, out, self, id⟩, st0, st) s0 ∗ R) := by
    change s0.mem ⊨ (⌜s0.fs.files = F0⌝ ∗
      (kitPreKeyGetPollSpec M A lim pkKit pkEnv).pre (⟨fut, out, self, id⟩, st0, st) s0) ∗ R at hpre1
    simpa only [sepConj_assoc] using hpre1
  rw [satisfies_pure_sepConj] at hpre2
  obtain ⟨hfiles, hpre3⟩ := hpre2
  change s0.mem ⊨
    (⌜(0#64 &&& 0xfff#64) = 0#64 ∧ s0.readReg64 .x0 = fut ∧ s0.readReg64 .x8 = out ∧
        id = pkId ∧ FitsEnv M lim st (cliPollPkGetPollEnv ReadEnv F0 st0 id)⌝ ∗
      pkBoxAt fut self id 0#8 ∗
      (⌜CliPkInv cliIo.rd F0 cliWrOk pkId st0⌝ ∗ dirAt A.repAlloc self st0) ∗
      memRegion out 56 ∗ A.pool lim st s0 ∗ stackAt s0.sp (cliKitStk B).pkGetPoll) ∗ R at hpre3
  rw [sepConj_assoc, satisfies_pure_sepConj] at hpre3
  obtain ⟨⟨_, hx0, hx8, rfl, hfit_kit⟩, hpre4⟩ := hpre3
  have hpre5 : s0.mem ⊨ ⌜CliPkInv cliIo.rd F0 cliWrOk id st0⌝ ∗
      (pkBoxAt fut self id 0#8 ∗ dirAt A.repAlloc self st0 ∗ memRegion out 56 ∗
        A.pool lim st s0 ∗ stackAt s0.sp (cliKitStk B).pkGetPoll ∗ R) :=
    Satisfies.mono (Entails.of_eq (by ac_rfl)) hpre4
  rw [satisfies_pure_sepConj] at hpre5
  obtain ⟨hinv, hspatial⟩ := hpre5
  let xg : PkPollGhost := ⟨fut, out, self, id, st0⟩
  let PollEnv := fun F (x : PkPollGhost) =>
    CliPkGetPollEnv DecimalEnv (DirGetEnv PathEnv ReadEnv cliIo.rd F)
      CliPkDecodeEnv cliIo.rd F x
  have hfit_hop : FitsEnv M lim st (PollEnv s0.fs.files xg) := fun evs hm => by
    rw [hfiles] at hm
    exact hfit_kit evs hm
  have hpre_hop : s0.mem ⊨
      (pkGetPollSpecPlaced cliIo.rd cliWrOk A lim PollEnv (cliKitStk B).pkGetPoll).pre
        (xg, st) s0 ∗ R := by
    dsimp only [pkGetPollSpecPlaced, pkGetPollSpecOfPlaced, withLsCodeRoLoaded]
    rw [sepConj_assoc, sepConj_left_comm, satisfies_pure_sepConj]
    refine ⟨hcrl, ?_⟩
    rw [sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨⟨hx0, hx8, hinv.nameOk, hfiles ▸ hinv.sizeOk, hfit_hop⟩, ?_⟩
    simpa only [sepConj_assoc] using hspatial
  refine subroutine_ok.mono_outcome hhop (xg, st) R s0 hpc hrun hpre_hop hsp fun sf hout => ?_
  rcases hout with ⟨hret, hcc, hpost⟩ | hpan | hex | hoom
  · refine Or.inl ⟨hret, hcc, Satisfies.mono (sepConj_mono_left ?_) hpost⟩
    show (pkGetPollSpecPlaced cliIo.rd cliWrOk A lim PollEnv (cliKitStk B).pkGetPoll).post
        (xg, st) s0 sf ⊢
      (kitPreKeyGetPollSpec M A lim pkKit pkEnv).post (⟨fut, out, self, id⟩, st0, st) s0 sf
    dsimp only [pkGetPollSpecPlaced, pkGetPollSpecOfPlaced, kitPreKeyGetPollSpec, pkKit, pkEnv,
      cliPollPkFullBudgetEnv, cliPollPkKitPlaced,
      CryptoVerification.SignalSession.Cli.KitInst.cliPreKeyStoreSpecPlaced,
      CryptoVerification.SignalSession.Cli.RunProofs.Poll.cliPreKeyStoreSpecPlaced,
      cliPreKeyStoreSpec, cliPkStoreAt, xg]
    refine Entails.sepExists_elim fun evs => ?_
    rw [sepExists_sepConj_left]
    refine Entails.sepExists_elim fun pa => ?_
    rw [sepConj_assoc]
    refine Entails.pure_left fun ⟨hpa, htr, hmenv⟩ => ?_
    rw [hfiles] at hpa hmenv
    subst hpa
    have hent0 := pkGetAnsAt_entails_pollOut_placed A.repAlloc cliIo.rd F0 cliWrOk id
      (cliKitStk B).pkGetShim (cliKitStk B).pkGetPoll
      (cliKitStk B).pkRemoveShim (cliKitStk B).pkRemovePoll st0 id out
    dsimp only at hent0
    have hout_eq : preKeyGetPollOutAt
        (CryptoVerification.SignalSession.Cli.KitInst.cliPreKeyStoreSpecPlaced
          A.repAlloc cliIo.rd F0 cliWrOk id
          (cliKitStk B).pkGetShim (cliKitStk B).pkGetPoll
          (cliKitStk B).pkRemoveShim (cliKitStk B).pkRemovePoll) out =
      preKeyGetPollOutAt pkKit out := by
      funext ans; cases ans <;> rfl
    rw [hout_eq] at hent0
    refine Entails.trans (sepConj_mono_left hent0) ?_
    rw [sepExists_sepConj_left]
    refine Entails.sepExists_elim fun ans => ?_
    rw [sepConj_assoc]
    refine Entails.pure_left fun hrel => ?_
    refine Entails.sepExists_right ans (Entails.sepExists_right evs ?_)
    refine Entails.pure_right ⟨hrel, by rw [List.append_nil]; exact htr, hmenv⟩ ?_
    exact Entails.trans (Entails.pure_right hinv (Entails.refl _)) (Entails.of_eq (by ac_rfl))
  · exact Or.inr (Or.inl hpan)
  · exact Or.inr (Or.inr (Or.inl hex))
  · exact Or.inr (Or.inr (Or.inr hoom))

/-- Discharges `PreKeyStoreKitPlacedOk` for `cliPollPkKitPlaced` from `RunHooksPlaced` and
`hRead`. -/
theorem cliPollPk_kitPlacedOk [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ReadEnv : FsFiles → List (BitVec 8) → List AllocEvent → Prop}
    (mmpl : Obj.MultiPlacement) (gh : CliGhostHooks) (W : CliHooks)
    (B : RunBudgets) (F0 : FsFiles) (pkId : BitVec 32)
    (hDropNz : lsmpl.base 547 ≠ 0#64)
    (hh : RunHooksPlaced A lim (cliGhostExterns gh (cliExternsPlaced mmpl W)))
    (hRead : subroutine_ok (dpPollProgPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W))) (lsρ lsReadFileSym)
      (readFileSpecPlaced cliIo.rd cliWrOk A lim B.readFile ReadEnv)) :
    PreKeyStoreKitPlacedOk A lim
      (cliPollPkKitPlaced A.repAlloc F0 pkId (cliKitStk B))
      (cliPollPkFullBudgetEnv A.repAlloc F0 pkId (cliKitStk B) ReadEnv)
      (cliGhostExterns gh (cliExternsPlaced mmpl W)) where
  getShim hblk := cliPollPk_getShim_rocl mmpl gh W B F0 pkId hh hblk
  getPoll hblk := cliPollPk_getPoll_rocl mmpl gh W B F0 pkId hh hRead hblk
  getFutDrop hblk := by
    change subroutine_ok _ (0#64 + lsDropOffPlaced) _
    rw [lsDropOffPlaced_eq hDropNz]
    exact cliIdFutDrop_rocl_placed_ok hblk
  removeShim hblk := (cliPollPk_removeKitPlacedOk mmpl gh W B F0 pkId hDropNz hh hRead).removeShim hblk
  removePoll hblk := (cliPollPk_removeKitPlacedOk mmpl gh W B F0 pkId hDropNz hh hRead).removePoll hblk
  removeFutDrop hblk := (cliPollPk_removeKitPlacedOk mmpl gh W B F0 pkId hDropNz hh hRead).removeFutDrop hblk

private theorem cliPollKpk_getPoll_rocl [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ReadEnv : FsFiles → List (BitVec 8) → List AllocEvent → Prop}
    (mmpl : Obj.MultiPlacement) (gh : CliGhostHooks) (W : CliHooks)
    (B : RunBudgets) (F0 : FsFiles) (kpkId spkId : BitVec 32) (kbk : PublicKey)
    (hh : RunHooksPlaced A lim (cliGhostExterns gh (cliExternsPlaced mmpl W)))
    (hRead : subroutine_ok (dpPollProgPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W))) (lsρ lsReadFileSym)
      (readFileSpecPlaced cliIo.rd cliWrOk A lim B.readFile ReadEnv))
    {callerProg : Program} {callerBlk : Nat}
    [IsLsBlockProg callerProg callerBlk (cliGhostExterns gh (cliExternsPlaced mmpl W))] (hblk : callerBlk < 619) :
    let kpkKit := cliPollKpkKitPlaced A.repAlloc F0 kpkId spkId kbk (cliKitStk B)
    subroutine_ok callerProg (0#64 + kpkKit.getPollOff)
      (withLsRoCl lsmpl
        (kitKpkGetPollSpecE M A lim kpkKit
          (cliPollKpkFullBudgetEnv A.repAlloc F0 kpkId spkId kbk (cliKitStk B) ReadEnv))) := by
  intro kpkKit
  let kpkEnv := cliPollKpkFullBudgetEnv A.repAlloc F0 kpkId spkId kbk (cliKitStk B) ReadEnv
  let hhSkel := toSkeletonRunHooks hh
  have hDecimal := cliDecimal_placed_ok hhSkel
  have hGet := cliDirGet_placed_ok
    (readProg := dpPollProgPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W))) (jRead := 518)
    (fun _ hp => hp.2) hhSkel
    (subroutine_ok_withLsCodeRoLoaded_of_plain hRead) (by decide) (by decide)
  have hKpkDec := cliDecodeKyberPreKey_placed_ok A lim mmpl gh W
    (signedHooksPlaced_of_codecHooks hh.codecHooks) (signedPortDepsPlaced_ok hh.codecHooks)
  have hhop := kpkGetPoll_placed_fs_caller_ok_of_deps
    (callerProg := callerProg) (i := callerBlk)
    (decProg := lsProg_597 (cliGhostExterns gh (cliExternsPlaced mmpl W))) (decBlk := 597)
    (getProg := lsProg_589 (cliGhostExterns gh (cliExternsPlaced mmpl W))) (getBlk := 589)
    (decodeProg := lsProg_595 (cliGhostExterns gh (cliExternsPlaced mmpl W))) (decodeBlk := 595)
    (stk := (cliKitStk B).kpkGetPoll)
    hh.alloc hDecimal hGet hKpkDec
    (hh.fs (lsProg_576 (cliGhostExterns gh (cliExternsPlaced mmpl W))) 576)
    (Nat.le_refl _) (fun _ _ => Or.inl) (fun _ _ => Or.inr) hblk
  change subroutine_ok callerProg (0#64 + lsmpl.base 576) _
  rw [BitVec.zero_add]
  refine subroutine_ok_rocl_of_withLsCodeRoLoaded ?_
  refine subroutine_ok.of_codeLoaded
    fun ⟨⟨fut, out, self, id⟩, st0, st⟩ R s0 hpc hrun hpre hsp _ => ?_
  change KyberGhost at st0
  obtain ⟨hcrl, hpre1⟩ := extract_withLsCodeRoLoaded hpre
  have hpre2 : s0.mem ⊨ ⌜s0.fs.files = F0⌝ ∗
      ((kitKpkGetPollSpec M A lim kpkKit kpkEnv).pre (⟨fut, out, self, id⟩, st0, st) s0 ∗ R) := by
    change s0.mem ⊨ (⌜s0.fs.files = F0⌝ ∗
      (kitKpkGetPollSpec M A lim kpkKit kpkEnv).pre (⟨fut, out, self, id⟩, st0, st) s0) ∗ R at hpre1
    simpa only [sepConj_assoc] using hpre1
  rw [satisfies_pure_sepConj] at hpre2
  obtain ⟨hfiles, hpre3⟩ := hpre2
  change s0.mem ⊨
    (⌜(0#64 &&& 0xfff#64) = 0#64 ∧ s0.readReg64 .x0 = fut ∧ s0.readReg64 .x8 = out ∧
        id = kpkId ∧ FitsEnv M lim st (cliPollKpkGetPollEnv ReadEnv F0 st0 id)⌝ ∗
      pkBoxAt fut self id 0#8 ∗
      (⌜CliKpkInvFull cliIo.rd F0 cliWrOk kpkId spkId kbk st0⌝ ∗
        (dirAt A.repAlloc self st0.oneTime ∗ dirAt A.repAlloc (self + 0x28#64) st0.lastResort)) ∗
      memRegion out 88 ∗ A.pool lim st s0 ∗ stackAt s0.sp (cliKitStk B).kpkGetPoll) ∗ R at hpre3
  rw [sepConj_assoc, satisfies_pure_sepConj] at hpre3
  obtain ⟨⟨_, hx0, hx8, rfl, hfit_kit⟩, hpre4⟩ := hpre3
  have hpre5 : s0.mem ⊨ ⌜CliKpkInvFull cliIo.rd F0 cliWrOk id spkId kbk st0⌝ ∗
      (pkBoxAt fut self id 0#8 ∗ dirAt A.repAlloc self st0.oneTime ∗
        dirAt A.repAlloc (self + 0x28#64) st0.lastResort ∗ memRegion out 88 ∗
        A.pool lim st s0 ∗ stackAt s0.sp (cliKitStk B).kpkGetPoll ∗ R) :=
    Satisfies.mono (Entails.of_eq (by ac_rfl)) hpre4
  rw [satisfies_pure_sepConj] at hpre5
  obtain ⟨hinv, hspatial⟩ := hpre5
  let xg : KpkPollGhost := ⟨fut, out, self, id, st0⟩
  let PollEnv := fun F (x : KpkPollGhost) =>
    CliKpkGetPollEnv DecimalEnv (fun dir k => DirGetEnv PathEnv ReadEnv cliIo.rd F dir (keyName k))
      CliSpkDecodeEnv cliIo.rd F x
  have hfit_hop : FitsEnv M lim st (PollEnv s0.fs.files xg) := fun evs hm => by
    rw [hfiles] at hm
    exact hfit_kit evs hm
  have hpre_hop : s0.mem ⊨
      (kpkGetPollSpecPlaced cliIo.rd cliWrOk A lim PollEnv (cliKitStk B).kpkGetPoll).pre
        (xg, st) s0 ∗ R := by
    dsimp only [kpkGetPollSpecPlaced, withLsCodeRoLoaded]
    rw [sepConj_assoc, sepConj_left_comm, satisfies_pure_sepConj]
    refine ⟨hcrl, ?_⟩
    rw [sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨⟨hx0, hx8, hinv.markInv.nameOk, hinv.lastNameOk,
      hfiles ▸ hinv.oneSizeOk, hfiles ▸ hinv.lastSizeOk, hfit_hop⟩, ?_⟩
    simpa only [sepConj_assoc] using hspatial
  refine subroutine_ok.mono_outcome hhop (xg, st) R s0 hpc hrun hpre_hop hsp fun sf hout => ?_
  rcases hout with ⟨hret, hcc, hpost⟩ | hpan | hex | hoom
  · refine Or.inl ⟨hret, hcc, Satisfies.mono (sepConj_mono_left ?_) hpost⟩
    show (kpkGetPollSpecPlaced cliIo.rd cliWrOk A lim PollEnv (cliKitStk B).kpkGetPoll).post
        (xg, st) s0 sf ⊢
      (kitKpkGetPollSpec M A lim kpkKit kpkEnv).post (⟨fut, out, self, id⟩, st0, st) s0 sf
    dsimp only [kpkGetPollSpecPlaced, kitKpkGetPollSpec, kpkKit, kpkEnv,
      cliPollKpkFullBudgetEnv, cliPollKpkKitPlaced, cliKpkStoreSpecFullPlaced,
      CryptoVerification.SignalSession.Cli.KitInst.cliKyberPreKeyStoreSpecPlaced,
      CryptoVerification.SignalSession.Cli.RunProofs.Poll.cliKyberPreKeyStoreSpecPlaced,
      cliKyberPreKeyStoreSpec, cliKpkStoreSpec, cliKpkStoreAtFull, xg]
    refine Entails.sepExists_elim fun evs => ?_
    rw [sepExists_sepConj_left]
    refine Entails.sepExists_elim fun pa => ?_
    rw [sepConj_assoc]
    refine Entails.pure_left fun ⟨hpa, htr, hmenv⟩ => ?_
    rw [hfiles] at hpa hmenv
    subst hpa
    have hent0 := kpkAnsAt_entails_pollOut_placed A.repAlloc cliIo.rd F0 cliWrOk id spkId kbk
      (cliKitStk B).kpkGetShim (cliKitStk B).kpkGetPoll
      (cliKitStk B).kpkMarkShim (cliKitStk B).kpkMarkPoll st0 id out
    dsimp only at hent0
    have hout_eq : kpkGetPollOutAt
        (CryptoVerification.SignalSession.Cli.KitInst.cliKyberPreKeyStoreSpecPlaced
          A.repAlloc cliIo.rd F0 cliWrOk id spkId kbk
          (cliKitStk B).kpkGetShim (cliKitStk B).kpkGetPoll
          (cliKitStk B).kpkMarkShim (cliKitStk B).kpkMarkPoll) out =
      kpkGetPollOutAt kpkKit out := by
      funext ans; cases ans <;> rfl
    rw [hout_eq] at hent0
    refine Entails.trans (sepConj_mono_left hent0) ?_
    rw [sepExists_sepConj_left]
    refine Entails.sepExists_elim fun ans => ?_
    rw [sepConj_assoc]
    refine Entails.pure_left fun hrel => ?_
    refine Entails.sepExists_right ans (Entails.sepExists_right evs ?_)
    refine Entails.pure_right ⟨hrel, by rw [List.append_nil]; exact htr, hmenv⟩ ?_
    exact Entails.trans (Entails.pure_right hinv (Entails.refl _)) (Entails.of_eq (by ac_rfl))
  · exact Or.inr (Or.inl hpan)
  · exact Or.inr (Or.inr (Or.inl hex))
  · exact Or.inr (Or.inr (Or.inr hoom))

/-- Discharges `KyberPreKeyStoreKitPlacedOk` for `cliPollKpkKitPlaced` from `RunHooksPlaced` and
`hRead`. -/
theorem cliPollKpk_kitPlacedOk [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ReadEnv : FsFiles → List (BitVec 8) → List AllocEvent → Prop}
    (mmpl : Obj.MultiPlacement) (gh : CliGhostHooks) (W : CliHooks)
    (B : RunBudgets) (F0 : FsFiles) (kpkId spkId : BitVec 32) (kbk : PublicKey)
    (hDropNz : lsmpl.base 547 ≠ 0#64)
    (hh : RunHooksPlaced A lim (cliGhostExterns gh (cliExternsPlaced mmpl W)))
    (hRead : subroutine_ok (dpPollProgPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W))) (lsρ lsReadFileSym)
      (readFileSpecPlaced cliIo.rd cliWrOk A lim B.readFile ReadEnv)) :
    KyberPreKeyStoreKitPlacedOk A lim
      (cliPollKpkKitPlaced A.repAlloc F0 kpkId spkId kbk (cliKitStk B))
      (cliPollKpkFullBudgetEnv A.repAlloc F0 kpkId spkId kbk (cliKitStk B) ReadEnv)
      (cliGhostExterns gh (cliExternsPlaced mmpl W)) where
  getShim hblk := cliPollKpk_getShim_rocl mmpl gh W B F0 kpkId spkId kbk hh hblk
  getPoll hblk := cliPollKpk_getPoll_rocl mmpl gh W B F0 kpkId spkId kbk hh hRead hblk
  getFutDrop hblk := by
    change subroutine_ok _ (0#64 + lsDropOffPlaced) _
    rw [lsDropOffPlaced_eq hDropNz]
    exact cliIdFutDrop_rocl_placed_ok hblk
  markShim hblk := (cliPollKpk_markKitPlacedOk mmpl gh W B F0 kpkId spkId kbk hDropNz hh hRead).markShim hblk
  markPoll hblk := (cliPollKpk_markKitPlacedOk mmpl gh W B F0 kpkId spkId kbk hDropNz hh hRead).markPoll hblk
  markFutDrop hblk := (cliPollKpk_markKitPlacedOk mmpl gh W B F0 kpkId spkId kbk hDropNz hh hRead).markFutDrop hblk

/-! ## 4. Concrete CLI Path A Stage P2 Envelopes & Instantiation -/

/-- Canonical CLI Path A Stage P2 error envelope at `(A, ReadEnv, X, W, B, senv, AcceptErrEnv)`. -/
abbrev cliP2PathAErrEnv [LibsignalPlacement] (A : RustAlloc)
    (ReadEnv : FsFiles → List (BitVec 8) → List AllocEvent → Prop)
    (X : UnreachedPqxdhPrimitives) (W : CliHooks) (B : RunBudgets)
    (senv : ∀ (F0 : FsFiles) (peer : AddrGhost),
      IdentitySelfStoreBudgetEnv (cliPollSelfKitPlaced A F0 peer (cliKitStk B)))
    (AcceptErrEnv : AcceptKeysInput → List AllocEvent → Prop) :
    DecPkGhost → List AllocEvent → Prop :=
  P2PathAErrEnvOf (A := A) X W B (InitializeBobV1Env W.C.F) AcceptErrEnv
    (cliStageP2KitEnvs (A := A) ReadEnv B senv)

/-- Canonical CLI Path A Stage P2 normal-exit (`+0x1778`) envelope at `(A, ReadEnv, X, W, B, senv)`. -/
abbrev cliP2PathAOkEnv [LibsignalPlacement] (A : RustAlloc)
    (ReadEnv : FsFiles → List (BitVec 8) → List AllocEvent → Prop)
    (X : UnreachedPqxdhPrimitives) (W : CliHooks) (B : RunBudgets)
    (senv : ∀ (F0 : FsFiles) (peer : AddrGhost),
      IdentitySelfStoreBudgetEnv (cliPollSelfKitPlaced A F0 peer (cliKitStk B))) :
    DecPkGhost → List AllocEvent → Prop :=
  P2PathAOkEnvOf (A := A) X W B (InitializeBobV1Env W.C.F)
    (cliStageP2KitEnvs (A := A) ReadEnv B senv)

/-- Instantiates `StageP2PathAQpanCliPlacedAtStmt` for all 4 CLI store kits (`self`, `spk`, `kpk`,
`pk`) from `hDropNz`, `SpqrV1PlacedSeams`, the Block `79` `pqxdhAccept*` contracts, and `hSelfKit`
(mirroring `Stage2V1InstPlaced.stageP2PathA_qpan_cli_placed_of_seams`). -/
theorem stageP2PathA_qpan_cli_placed_at_ok [LibsignalPlacement] {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits)
    {ReadEnv : FsFiles → List (BitVec 8) → List AllocEvent → Prop}
    (X : UnreachedPqxdhPrimitives) (mmpl : Obj.MultiPlacement) (gh : CliGhostHooks)
    (W : CliHooks) (B : RunBudgets)
    {senv : ∀ (F0 : FsFiles) (peer : AddrGhost),
      IdentitySelfStoreBudgetEnv (cliPollSelfKitPlaced A.repAlloc F0 peer (cliKitStk B))}
    {AcceptErrEnv : AcceptKeysInput → List AllocEvent → Prop}
    (hDropNz : lsmpl.base 547 ≠ 0#64)
    (hSpqr : SpqrV1PlacedSeams M A lim mmpl gh W)
    (h_accept_ok :
      subroutine_ok (lsProg_75 (cliGhostExterns gh (cliExternsPlaced mmpl W))) (lsmpl.base 79)
        (pqxdhAcceptOptFieldsPlacedSpec
          (ofSignalPqxdhPrimitives (modelPrims X ⟨W.C, W.Q⟩)) A lim AcceptSuccessEnv))
    (h_accept_err :
      subroutine_ok (lsProg_75 (cliGhostExterns gh (cliExternsPlaced mmpl W))) (lsmpl.base 79)
        (pqxdhAcceptOptFieldsPlacedSpec
          (ofSignalPqxdhPrimitives (modelPrims X ⟨W.C, W.Q⟩)) A lim AcceptErrEnv))
    (h_accept_err_owned :
      subroutine_ok (lsProg_75 (cliGhostExterns gh (cliExternsPlaced mmpl W))) (lsmpl.base 79)
        (pqxdhAcceptErrOwnedPlacedSpec
          (ofSignalPqxdhPrimitives (modelPrims X ⟨W.C, W.Q⟩)) A lim AcceptErrEnv))
    (hSelfKit : ∀ (F0 : FsFiles) (peer : AddrGhost),
      RunHooksPlaced A lim (cliGhostExterns gh (cliExternsPlaced mmpl W)) →
      subroutine_ok (dpPollProgPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W))) (lsρ lsReadFileSym)
        (readFileSpecPlaced cliIo.rd cliWrOk A lim B.readFile ReadEnv) →
      IdentitySelfStoreKitPlacedOkI A lim
        (cliPollIdKitPlaced A.repAlloc F0 peer (cliKitStk B))
        (cliPollSelfKitPlaced A.repAlloc F0 peer (cliKitStk B))
        (senv F0 peer) (cliGhostExterns gh (cliExternsPlaced mmpl W))) :
    StageP2PathAQpanCliPlacedAtStmt A lim ReadEnv X mmpl gh W B
      (cliP2PathAErrEnv A.repAlloc ReadEnv X W B senv AcceptErrEnv)
      (cliP2PathAOkEnv A.repAlloc ReadEnv X W B senv) :=
  stageP2PathA_qpan_cli_placed_at_of_seams A lim X mmpl gh W B
    (kitEnvs := cliStageP2KitEnvs (A := A.repAlloc) ReadEnv B senv)
    hDropNz hSpqr h_accept_ok h_accept_err h_accept_err_owned
    (fun F0 peer _ _ _ _ hh hRead => hSelfKit F0 peer hh hRead)
    (fun F0 _ spkId _ _ _ hh hRead =>
      cliPollSpk_kitPlacedOk mmpl gh W B F0 spkId hDropNz hh hRead)
    (fun F0 _ spkId kpkId _ kbk hh hRead =>
      cliPollKpk_kitPlacedOk mmpl gh W B F0 kpkId spkId kbk hDropNz hh hRead)
    (fun F0 _ _ _ opkWord _ hh hRead =>
      cliPollPk_kitPlacedOk mmpl gh W B F0 opkWord hDropNz hh hRead)

/-- Canonical CLI Path A Stage P2 error envelope under `[LibsignalFullPlacement]` (`InitializeBobV1OptFieldsEnv`
and `AcceptOptFieldsEnv`, with zero Block `79` envelope parameters). -/
abbrev cliP2PathAOptFieldsErrEnv [LibsignalPlacement] (A : RustAlloc)
    (ReadEnv : FsFiles → List (BitVec 8) → List AllocEvent → Prop)
    (X : UnreachedPqxdhPrimitives) (W : CliHooks) (B : RunBudgets)
    (senv : ∀ (F0 : FsFiles) (peer : AddrGhost),
      IdentitySelfStoreBudgetEnv (cliPollSelfKitPlaced A F0 peer (cliKitStk B))) :
    DecPkGhost → List AllocEvent → Prop :=
  P2PathAErrEnvOf (A := A) X W B
    (InitializeBobV1OptFieldsEnv (ofSignalPqxdhPrimitives (modelPrims X ⟨W.C, W.Q⟩)) W.C.F)
    (AcceptOptFieldsEnv (ofSignalPqxdhPrimitives (modelPrims X ⟨W.C, W.Q⟩)))
    (cliStageP2KitEnvs (A := A) ReadEnv B senv)

/-- Canonical CLI Path A Stage P2 normal-exit (`+0x1778`) envelope under `[LibsignalFullPlacement]`
(`InitializeBobV1OptFieldsEnv`). -/
abbrev cliP2PathAOptFieldsOkEnv [LibsignalPlacement] (A : RustAlloc)
    (ReadEnv : FsFiles → List (BitVec 8) → List AllocEvent → Prop)
    (X : UnreachedPqxdhPrimitives) (W : CliHooks) (B : RunBudgets)
    (senv : ∀ (F0 : FsFiles) (peer : AddrGhost),
      IdentitySelfStoreBudgetEnv (cliPollSelfKitPlaced A F0 peer (cliKitStk B))) :
    DecPkGhost → List AllocEvent → Prop :=
  P2PathAOkEnvOf (A := A) X W B
    (InitializeBobV1OptFieldsEnv (ofSignalPqxdhPrimitives (modelPrims X ⟨W.C, W.Q⟩)) W.C.F)
    (cliStageP2KitEnvs (A := A) ReadEnv B senv)

/-- Instantiates `StageP2PathAQpanCliFrozenPlacedAtStmt` for all 4 CLI store kits (`self`, `spk`,
`kpk`, `pk`) under `[LibsignalFullPlacement]` from `hDropNz`, `SpqrV1PlacedSeams`, and `hSelfKit`
with zero `h_accept*` seams. -/
theorem stageP2PathA_qpan_cli_full_placed_at_ok [LibsignalFullPlacement] {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits)
    {ReadEnv : FsFiles → List (BitVec 8) → List AllocEvent → Prop}
    (X : UnreachedPqxdhPrimitives) (mmpl : Obj.MultiPlacement) (gh : CliGhostHooks)
    (W : CliHooks) (B : RunBudgets)
    {senv : ∀ (F0 : FsFiles) (peer : AddrGhost),
      IdentitySelfStoreBudgetEnv (cliPollSelfKitPlaced A.repAlloc F0 peer (cliKitStk B))}
    (hDropNz : lsmpl.base 547 ≠ 0#64)
    (hG : CliGhostAllocHooks M A lim gh)
    (hSpqr : SpqrV1PlacedSeams M A lim mmpl gh W)
    (hSelfKit : ∀ (F0 : FsFiles) (peer : AddrGhost),
      RunHooksPlaced A lim (cliGhostExterns gh (cliExternsPlaced mmpl W)) →
      subroutine_ok (dpPollProgPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W))) (lsρ lsReadFileSym)
        (readFileSpecPlaced cliIo.rd cliWrOk A lim B.readFile ReadEnv) →
      IdentitySelfStoreKitPlacedOkI A lim
        (cliPollIdKitPlaced A.repAlloc F0 peer (cliKitStk B))
        (cliPollSelfKitPlaced A.repAlloc F0 peer (cliKitStk B))
        (senv F0 peer) (cliGhostExterns gh (cliExternsPlaced mmpl W))) :
    StageP2PathAQpanCliFrozenPlacedAtStmt A lim ReadEnv X mmpl gh W B
      (cliP2PathAOptFieldsErrEnv A.repAlloc ReadEnv X W B senv)
      (cliP2PathAOptFieldsOkEnv A.repAlloc ReadEnv X W B senv) :=
  stageP2PathA_qpan_cli_full_placed_at_of_seams A lim X mmpl gh W B
    (kitEnvs := cliStageP2KitEnvs (A := A.repAlloc) ReadEnv B senv)
    hDropNz hG hSpqr
    (fun F0 peer _ _ _ _ hh hRead => hSelfKit F0 peer hh hRead)
    (fun F0 _ spkId _ _ _ hh hRead =>
      cliPollSpk_kitPlacedOk mmpl gh W B F0 spkId hDropNz hh hRead)
    (fun F0 _ spkId kpkId _ kbk hh hRead =>
      cliPollKpk_kitPlacedOk mmpl gh W B F0 kpkId spkId kbk hDropNz hh hRead)
    (fun F0 _ _ _ opkWord _ hh hRead =>
      cliPollPk_kitPlacedOk mmpl gh W B F0 opkWord hDropNz hh hRead)

end LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.StagesInst.Stage2V1KitsPlacedBudgetAux
