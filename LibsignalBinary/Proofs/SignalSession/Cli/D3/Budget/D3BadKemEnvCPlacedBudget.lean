/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.D3.Budget.D3BadKemEnvAPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.D3.Budget.D3BadKemEnvBPlacedBudget

/-!
# `SingleSlotFineSpec` and Fine-Credit Cap Bounds for `DecPkD3UntypedEnv`

Characterizes stage-exit traces of `DecPkD3UntypedEnv`, verifies closed `fineCostModel` slot-cap
bounds (`decPkD3Untyped_caps_le`, `decPkD3Untyped_caps_le_1MiB`), and proves `SingleSlotFineSpec`
and non-vacuity witnesses for untyped/bad-KEM `decrypt_prekey` rejection.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 2000000

namespace LibsignalBinary.Proofs.SignalSession.Cli.D3.Budget.D3BadKemEnvCPlacedBudget

open Arm64.Process (bytesOfString)
open CryptoGames.LibsignalSessionApi (PreKeySignalMessage SessionRecord)
open CryptoVerification (LibsignalPlacement)
open CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Over (
  x3dhUnsupportedBytes x3dhUnsupportedBytes_length
)
open CryptoVerification.E2E (PEParams)
open CryptoVerification.E2E.Record (encodeRecord)
open CryptoVerification.LibsignalPublicApi.StoreKit (FsFiles)
open CryptoVerification.LibsignalTripleRatchetRepr (uuidTryParse)
open CryptoVerification.RustHeap (RustAlloc)
open CryptoVerification.SignalSession (
  CliHooks CliPqxdhInputs Inputs PqParty PqxdhPartyInSpecDomain pqRecvInputs
)
open CryptoVerification.SignalSession.Cli (StoresGhost addressText pathOf utf8)
open CryptoVerification.SignalSession.Cli.MainHops (AddrV RunCall cliIo parseArgs)
open CryptoVerification.SignalSession.Cli.RunCompose (DecPkGhost runFiles)
open CryptoVerification.SignalSession.Cli.RunProofs.Poll (
  cliKitStk cliPollIdKitPlaced cliPollKpkKitPlaced cliPollPkKitPlaced cliPollSelfKitPlaced
  cliPollSessKitPlaced cliPollSpkKitPlaced pmKyberId
)
open CryptoVerification.SignalSession.Cli.RunSkeleton (RunBudgets)
open CryptoVerification.SignalSession.Cli.Slots (scopeKit)
open LibsignalBinary.Heap (AllocEvent FreeOnlyEvs SeqEnv rustAllocEvents rustDeallocEvents)
open LibsignalBinary.Heap.Fine (FineScale fineCostModel)
open LibsignalBinary.Heap.Fine.ClientBounds (fineCostModel_smallMaxReq_eq)
open LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP2Mid3PlacedBudget (
  P2Sub1To3Arm1Env P2Sub1To3Arm2Env P2Sub1To3OkEnv P2Sub1To4Arm3Env P2Sub4OkEnv
)
open LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP2Sub1PlacedBudget (
  P2Sub1Env boxAllocEnv_iff_eq boxAllocEvents
)
open LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP2Sub3AuxPlacedBudget (
  P2Sub3TailAllocEnv
)
open LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP2Sub4AuxPlacedBudget (
  p2Sub4NoneEnv_iff_boxAllocEnv
)
open LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP2V1PlacedBudget (
  P2V1Arm4Env P2V1Arm5EnvOfAcceptErr
)
open LibsignalBinary.Proofs.E2E.Pqxdh.ResponderStore.KeyPairCalleesAuxBudget (
  KemKeyPairFromPubPrivEnv
)
open LibsignalBinary.Proofs.PeakBudget.CliDomainCaps (
  DirDomainCaps dirDomainCaps_opened_own dirDomainCaps_opened_peers dirDomainCaps_opened_sess
  parseArgs_peer_name_length_le
)
open LibsignalBinary.Proofs.PeakBudget.CliRealExistentialCalleeEnvs (
  cliIo_rd_ok_length_le_sessionCapBytes
)
open LibsignalBinary.Proofs.PeakBudget.CliSlotFineSpec (SingleSlotFineSpec)
open LibsignalBinary.Proofs.PeakBudget.CliTopBudgetSpec (
  cliRecvPrekeySlotCumCap cliRecvPrekeySlotGrpSCap cliRecvPrekeySlotLiveCap cliRecvPrekeySlotPeakCap
  cliRecvPrekeySlotReqCap
)
open LibsignalBinary.Proofs.PeakBudget.GroupCreditKit (PhaseGroupSpec)
open LibsignalBinary.Proofs.PeakBudget.SeqCreditKit (ConcatEnv PhaseCreditSpec)
open LibsignalBinary.Proofs.PeakBudget.SeqCreditKitLemmas (fineCostModel_modelHyps)
open LibsignalBinary.Proofs.PeakBudget.SerCloneStorePeakSpec (
  fineReadFileCum fineReadFileLive fineReadFileMaxReq fineReadFilePeak
)
open LibsignalBinary.Proofs.PeakBudget.SpqrDomainCapsAux (sessionCapBytes)
open LibsignalBinary.Proofs.PeakBudget.W4OuterHelpers (stringClone_phaseCredit_small)
open LibsignalBinary.Proofs.PeakBudget.W4OuterStageHelpers (
  loadStepEnv_phaseCredit phaseCreditSpec_seq_freeOnly_exact trustStepEnv_phaseCredit w4BoxedStepCum
  w4BoxedStepLive w4BoxedStepMaxReq w4BoxedStepPeak
)
open LibsignalBinary.Proofs.PeakBudget.W4OuterTightSpecAux (
  PhaseCreditSpec.zero_live_peak_of_small boxAllocEnv_fine_le_28
)
open LibsignalBinary.Proofs.PeakBudget.W4RecvPrekeyRealSlot (w4RecvPrekeyRealGrpS)
open LibsignalBinary.Proofs.PeakBudget.W4RecvPrekeyRealSlot1MiB (
  w4RecvPrekeyReal1MiB_i_Cum w4RecvPrekeyReal1MiB_i_Live w4RecvPrekeyReal1MiB_i_MaxReq
  w4RecvPrekeyReal1MiB_i_Peak
)
open LibsignalBinary.Proofs.PeakBudget.W4SlotGroupSpec (boxAllocEnv_le_28_fine_groupSpec)
open LibsignalBinary.Proofs.PublicApi.StoreKit.IdentityStoreKitBudget (TrustStepEnv)
open LibsignalBinary.Proofs.PublicApi.StoreKit.PreKeyStoreKitBudget (BoxAllocEnv)
open LibsignalBinary.Proofs.PublicApi.StoreKit.SessionStoreKitBudget (LoadStepEnv)
open LibsignalBinary.Proofs.SessionRecordMin.DeserializeCancelBudget (
  deserCancelFineCum deserCancelFineGrpS deserCancelFineLive deserCancelFineMaxReq
  deserCancelFinePeak recordDeserializeCancelEnv_fine_groupSpec
  recordDeserializeCancelEnv_fine_phaseCreditSpec
  sessDeserializeCancelEnv_imp_recordDeserializeCancelEnv
)
open LibsignalBinary.Proofs.SessionRecordMin.DeserializeCancelBudgetAux (SessDeserializeCancelEnv)
open LibsignalBinary.Proofs.SignalSession.Cli.D3.Budget.D3BadKemEnvAPlacedBudget (
  DecPkD3UntypedEnv DecPkKeyFilesBounded PqxdhAcceptBadKemErrEnv StageP2BadKemRejectEnv
  StageP2UntypedRejectEnv StageP2V3RejectEnv decPkKeyFilesBounded_of_pqOrD3Recv utf8_eq_kutf8
)
open LibsignalBinary.Proofs.SignalSession.Cli.D3.Budget.D3BadKemEnvBPlacedBudget (
  dirGet_small_fine_phaseCredit kpPollFineCum kpPollFineGrpS kpkPollFineCum kpkPollFineGrpS
  kpkPoll_fine_specs optIkpTryFrom_256_groupSpec optIkpTryFrom_256_phaseCredit pkPollFineCum
  pkPollFineGrpS pkPoll_fine_specs smallAlloc_fine_groupSpec smallAlloc_fine_phaseCredit
  spkPollFineCum spkPollFineGrpS spkPoll_fine_specs
)
open LibsignalBinary.Proofs.SignalSession.Cli.Dir.Get.PlacedBudgetAux1a (DirGetEnv)
open LibsignalBinary.Proofs.SignalSession.Cli.Dir.Path.PlacedBudget (PathEnv)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.Arms.R3bProofPlacedBudget (r3bDecPkGhost)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Over.StagesOverCliPlacedBudget (
  cliPollSelfBudgetEnv cliPollSelfKpPollEnv
)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.ClosureStageDefsPlacedBudget (
  StageP1OkEnv StageP1UntrustedEnv
)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.ClosureUntrustedPlacedBudget (
  CliDpPollUntrustedEnv cliPollIdBudgetEnv cliPollSessBudgetEnv
)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.StagesInst.Stage2V1KitsPlacedBudgetAux (
  cliPollKpkFullBudgetEnv cliPollKpkGetPollEnv cliPollPkFullBudgetEnv cliPollPkGetPollEnv
  cliPollSpkFullBudgetEnv cliPollSpkGetPollEnv
)
open LibsignalBinary.Proofs.SignalSession.Cli.SpecsPlacedBudget (ReadFileRuleEnv)
open LibsignalBinary.Proofs.SignalSession.Cli.Store.LoadPollRecordDeser (
  defaultLoadPollEnv_fine_groupSpec defaultLoadPollEnv_fine_phaseCredit_tight
  defaultLoadPollTightDeltaCum defaultW4LoadCum defaultW4LoadLive defaultW4LoadMaxReq
  defaultW4LoadPeak
)
open LibsignalBinary.Proofs.SignalSession.Cli.Store.LoadPollRecordDeserAux (
  dirGetEnv_path_readFile_fine_phaseCredit_tight dirGetEnv_path_readFile_groupSpec
)

/-! ## 1. Stage-Exit Unfolding Characterization -/

/-- `DecPkD3UntypedEnv` exits either on Stage P1 untrusted identity (`CliDpPollUntrustedEnv`) or
after Stage P1 (`StageP1OkEnv`) into `StageP2UntypedRejectEnv` (`StageP2V3RejectEnv` ∨
`StageP2BadKemRejectEnv`). -/
theorem decPkD3UntypedEnv_exits_stage1_or_2 [LibsignalPlacement]
    (A : RustAlloc) (W : CliHooks) (B : RunBudgets) (g : DecPkGhost) (evs : List AllocEvent) :
    DecPkD3UntypedEnv A W B g evs ↔
      CliDpPollUntrustedEnv (A := A) B (ReadFileRuleEnv cliIo.rd) SessDeserializeCancelEnv g evs ∨
      ∃ opt : Option (SessionRecord (List (BitVec 8))),
        SeqEnv
          (StageP1OkEnv (cliPollSessKitPlaced A g.F scopeKit g.peer (cliKitStk B))
            (cliPollSessBudgetEnv A g.F g.peer B (ReadFileRuleEnv cliIo.rd)
              SessDeserializeCancelEnv)
            StoresGhost.opened.sessions
            (cliPollIdKitPlaced A g.F g.peer (cliKitStk B))
            (cliPollIdBudgetEnv A g.F g.peer B (ReadFileRuleEnv cliIo.rd))
            StoresGhost.opened.identity g.peer.val g.msg.identityKey)
          (StageP2UntypedRejectEnv (A := A) B (ReadFileRuleEnv cliIo.rd)
            PqxdhAcceptBadKemErrEnv g opt)
          evs :=
  Iff.rfl

private theorem kpPoll_fine_specs {F0 : FsFiles} (hkf : DecPkKeyFilesBounded F0) :
    PhaseCreditSpec fineCostModel
      (cliPollSelfKpPollEnv (ReadFileRuleEnv cliIo.rd) F0 StoresGhost.opened.identity)
      kpPollFineCum 0 0 8192 ∧
    PhaseGroupSpec fineCostModel
      (cliPollSelfKpPollEnv (ReadFileRuleEnv cliIo.rd) F0 StoresGhost.opened.identity)
      kpPollFineGrpS := by
  have hdcOwn : DirDomainCaps 64 0 0 StoresGhost.opened.identity.own :=
    dirDomainCaps_opened_own.mono (by decide) (Nat.le_refl 0) (Nat.le_refl 0)
  have hGetC := dirGet_small_fine_phaseCredit (F0 := F0) hdcOwn
    (by rw [utf8_eq_kutf8]; decide : (utf8 "identity-key-pair").length ≤ 64) (by decide) hkf.1
  have hOptC := optIkpTryFrom_256_phaseCredit
    (gr := StoresGhost.opened.identity.own.get cliIo.rd F0 (utf8 "identity-key-pair")) hkf.1
  have hGetG := dirGetEnv_path_readFile_groupSpec fineCostModel cliIo.rd F0
    StoresGhost.opened.identity.own (utf8 "identity-key-pair")
  have hOptG := optIkpTryFrom_256_groupSpec
    (gr := StoresGhost.opened.identity.own.get cliIo.rd F0 (utf8 "identity-key-pair")) hkf.1
  unfold cliPollSelfKpPollEnv kpPollFineCum kpPollFineGrpS
  refine ⟨?_, ?_⟩
  · exact (hGetC.seq
      (phaseCreditSpec_seq_freeOnly_exact fineCostModel_modelHyps hOptC)).mono
      (by decide) (by decide) (by decide) (by decide)
  · exact (hGetG.seq
      ((hOptG.seq (PhaseGroupSpec.freeOnly fineCostModel)).mono
        (Nat.le_of_eq (Nat.add_zero _)))).mono (by decide)

private theorem p2Sub1_16_fine_specs :
    PhaseCreditSpec fineCostModel (P2Sub1Env 16) 19176 0 0 33 ∧
    PhaseGroupSpec fineCostModel (P2Sub1Env 16) (6 * FineScale) := by
  have h33c := smallAlloc_fine_phaseCredit (req := 33) (al := 1) (by decide) (by decide)
  have hfc : PhaseCreditSpec fineCostModel (· = rustDeallocEvents 33 1) 0 0 0 0 :=
    PhaseCreditSpec.rustDealloc_align16 fineCostModel (by decide)
  have h16c := smallAlloc_fine_phaseCredit (req := 16) (al := 8) (by decide) (by decide)
  refine ⟨?_, ?_⟩
  · exact (((h33c.concat hfc).concat h16c).mono
      (by decide) (by decide) (by decide) (by decide)).of_imp fun evs he => by
        rw [he]; exact ConcatEnv.append (ConcatEnv.append rfl rfl) rfl
  · exact (PhaseGroupSpec.of_nonFreeBound fineCostModel (maxOps := 2) (by
      rintro _ rfl; decide)).mono (by decide)

private theorem kemKpFromPubPriv_fine_specs :
    PhaseCreditSpec fineCostModel KemKeyPairFromPubPrivEnv 28550 0 0 3168 ∧
    PhaseGroupSpec fineCostModel KemKeyPairFromPubPrivEnv (6 * FineScale) := by
  have h1 := smallAlloc_fine_phaseCredit (req := 1568) (al := 1) (by decide) (by decide)
  have h2 := smallAlloc_fine_phaseCredit (req := 3168) (al := 1) (by decide) (by decide)
  refine ⟨?_, ?_⟩
  · exact ((h1.concat h2).mono
      (by decide) (by decide) (by decide) (by decide)).of_imp fun evs he => by
        rw [he]; exact ConcatEnv.append rfl rfl
  · exact (PhaseGroupSpec.of_nonFreeBound fineCostModel (maxOps := 2) (by
      rintro _ rfl; decide)).mono (by decide)

private theorem p2Sub3Tail_fine_specs :
    PhaseCreditSpec fineCostModel P2Sub3TailAllocEnv 9581 0 0 21 ∧
    PhaseGroupSpec fineCostModel P2Sub3TailAllocEnv (3 * FineScale) := by
  refine ⟨?_, ?_⟩
  · exact (smallAlloc_fine_phaseCredit (req := 21) (al := 1) (by decide) (by decide)).mono
      (by decide) (by decide) (by decide) (by decide)
  · exact smallAlloc_fine_groupSpec 21 1

theorem pqxdhAcceptBadKemErr_fine_specs :
    PhaseCreditSpec fineCostModel PqxdhAcceptBadKemErrEnv 48335 0 0 192 ∧
    PhaseGroupSpec fineCostModel PqxdhAcceptBadKemErrEnv (15 * FineScale) := by
  have h28 : PhaseCreditSpec fineCostModel (· = [.alloc 28]) 9595 0 0 28 :=
    smallAlloc_fine_phaseCredit (req := 28) (al := 1) (by decide) (by decide)
  have h192 : PhaseCreditSpec fineCostModel (· = [.alloc 192]) 9923 0 0 192 :=
    smallAlloc_fine_phaseCredit (req := 192) (al := 1) (by decide) (by decide)
  have h32a : PhaseCreditSpec fineCostModel (· = [.alloc 32]) 9603 0 0 32 :=
    (smallAlloc_fine_phaseCredit (req := 32) (al := 1) (by decide) (by decide)).mono
      (by decide) (by decide) (by decide) (by decide)
  have hf32 : PhaseCreditSpec fineCostModel (· = [.free 1 32]) 0 0 0 0 :=
    PhaseCreditSpec.rustDealloc_align16 fineCostModel (req := 32) (al := 1) (by decide)
  have h32f : PhaseCreditSpec fineCostModel (· = [.alloc 32, .free 1 32]) 9603 0 0 32 :=
    ((h32a.concat hf32).mono
      (by decide) (by decide) (by decide) (by decide)).of_imp fun _ h => by
        rw [h]; exact ⟨[.alloc 32], [.free 1 32], rfl, rfl, rfl⟩
  have hf192 : PhaseCreditSpec fineCostModel (· = [.free 1 192]) 0 0 0 0 :=
    PhaseCreditSpec.rustDealloc_align16 fineCostModel (req := 192) (al := 1) (by decide)
  have h28' : PhaseCreditSpec fineCostModel (· = [.alloc 28]) 48335 0 0 192 :=
    h28.mono (by decide) (by decide) (by decide) (by decide)
  have ha1' : PhaseCreditSpec fineCostModel _ 48335 0 0 192 :=
    (h192.concat hf192).mono (by decide) (by decide) (by decide) (by decide)
  have ha2' : PhaseCreditSpec fineCostModel _ 48335 0 0 192 :=
    ((h192.concat h32f).concat hf192).mono (by decide) (by decide) (by decide) (by decide)
  have ha3' : PhaseCreditSpec fineCostModel _ 48335 0 0 192 :=
    (((h192.concat h32f).concat h32f).concat hf192).mono
      (by decide) (by decide) (by decide) (by decide)
  have ha4' : PhaseCreditSpec fineCostModel _ 48335 0 0 192 :=
    ((((h192.concat h32f).concat h32f).concat h32f).concat hf192).mono
      (by decide) (by decide) (by decide) (by decide)
  have ha5' : PhaseCreditSpec fineCostModel _ 48335 0 0 192 :=
    (((((h192.concat h32f).concat h32f).concat h32f).concat h32f).concat hf192).mono
      (by decide) (by decide) (by decide) (by decide)
  refine ⟨?_, ?_⟩
  · refine ((((((h28'.or ha1').or ha2').or ha3').or ha4').or ha5').mono
        (by decide) (by decide) (by decide) (by decide)).of_imp fun evs h => ?_
    let s0 : List AllocEvent := [.alloc 192]
    let f32 : List AllocEvent := [.alloc 32, .free 1 32]
    let e192 : List AllocEvent := [.free 1 192]
    let s1 : List AllocEvent := s0 ++ f32
    let s2 : List AllocEvent := s1 ++ f32
    let s3 : List AllocEvent := s2 ++ f32
    let s4 : List AllocEvent := s3 ++ f32
    have w1 : ConcatEnv (· = s0) (· = f32) s1 := ⟨s0, f32, rfl, rfl, rfl⟩
    have w2 : ConcatEnv (ConcatEnv (· = s0) (· = f32)) (· = f32) s2 := ⟨s1, f32, rfl, w1, rfl⟩
    have w3 : ConcatEnv _ (· = f32) s3 := ⟨s2, f32, rfl, w2, rfl⟩
    have w4 : ConcatEnv _ (· = f32) s4 := ⟨s3, f32, rfl, w3, rfl⟩
    rcases h with rfl | rfl | rfl | rfl | rfl | rfl
    · exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inl rfl))))
    · exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inr ⟨s0, e192, rfl, rfl, rfl⟩))))
    · exact Or.inl (Or.inl (Or.inl (Or.inr ⟨s1, e192, rfl, w1, rfl⟩)))
    · exact Or.inl (Or.inl (Or.inr ⟨s2, e192, rfl, w2, rfl⟩))
    · exact Or.inl (Or.inr ⟨s3, e192, rfl, w3, rfl⟩)
    · exact Or.inr ⟨s4, e192, rfl, w4, rfl⟩
  · exact (PhaseGroupSpec.of_nonFreeBound fineCostModel (maxOps := 5) (by
      rintro evs (rfl | rfl | rfl | rfl | rfl | rfl) <;> decide)).mono (by decide)

def stageP2UntypedFineCum : Nat :=
  19176 + spkPollFineCum + 488 + kpkPollFineCum + 28550 + 9581 +
    488 + pkPollFineCum + 488 + kpPollFineCum + 48335

def stageP2UntypedFineGrpS : Nat :=
  (6 + 3 + 6 + 3 + 3 + 3 + 15) * FineScale +
    spkPollFineGrpS + kpkPollFineGrpS + pkPollFineGrpS + kpPollFineGrpS

theorem stageP2V3Reject_fine_specs :
    PhaseCreditSpec fineCostModel StageP2V3RejectEnv stageP2UntypedFineCum 0 0 9808 ∧
    PhaseGroupSpec fineCostModel StageP2V3RejectEnv stageP2UntypedFineGrpS := by
  have h33c := smallAlloc_fine_phaseCredit (req := 33) (al := 1) (by decide) (by decide)
  have hfc : PhaseCreditSpec fineCostModel (· = rustDeallocEvents 33 1) 0 0 0 0 :=
    PhaseCreditSpec.rustDealloc_align16 fineCostModel (by decide)
  have h24c : PhaseCreditSpec fineCostModel
      (· = rustAllocEvents x3dhUnsupportedBytes.length 1) 9587 0 0 24 := by
    rw [x3dhUnsupportedBytes_length]
    exact smallAlloc_fine_phaseCredit (req := 24) (al := 1) (by decide) (by decide)
  have h33g := smallAlloc_fine_groupSpec 33 1
  have hfg : PhaseGroupSpec fineCostModel (· = rustDeallocEvents 33 1) 0 :=
    (PhaseGroupSpec.of_nonFreeBound fineCostModel (maxOps := 0) (by rintro _ rfl; decide)).mono
      (by decide)
  have h24g : PhaseGroupSpec fineCostModel
      (· = rustAllocEvents x3dhUnsupportedBytes.length 1) (3 * FineScale) := by
    rw [x3dhUnsupportedBytes_length]
    exact smallAlloc_fine_groupSpec 24 1
  unfold StageP2V3RejectEnv
  refine ⟨?_, ?_⟩
  · exact (h33c.seq (hfc.seq
      (phaseCreditSpec_seq_freeOnly_exact fineCostModel_modelHyps h24c))).mono
      (by decide) (by decide) (by decide) (by decide)
  · exact (h33g.seq (hfg.seq
      ((h24g.seq (PhaseGroupSpec.freeOnly fineCostModel)).mono
        (Nat.le_of_eq (Nat.add_zero _))))).mono (by decide)

theorem stageP2BadKemReject_fine_specs [LibsignalPlacement] {A : RustAlloc}
    (B : RunBudgets) (g : DecPkGhost) (opt : Option (SessionRecord (List (BitVec 8))))
    (hkf : DecPkKeyFilesBounded g.F) :
    PhaseCreditSpec fineCostModel
      (StageP2BadKemRejectEnv (A := A) B (ReadFileRuleEnv cliIo.rd) PqxdhAcceptBadKemErrEnv g opt)
      stageP2UntypedFineCum 0 0 9808 ∧
    PhaseGroupSpec fineCostModel
      (StageP2BadKemRejectEnv (A := A) B (ReadFileRuleEnv cliIo.rd) PqxdhAcceptBadKemErrEnv g opt)
      stageP2UntypedFineGrpS := by
  have hbox16c : PhaseCreditSpec fineCostModel (BoxAllocEnv 16) 488 0 0 16 :=
    boxAllocEnv_fine_le_28 (by decide)
  have hbox16g : PhaseGroupSpec fineCostModel (BoxAllocEnv 16) (3 * FineScale) :=
    (boxAllocEnv_le_28_fine_groupSpec (boxSz := 16) (by decide)).mono (by decide)
  have hfree_c : PhaseCreditSpec fineCostModel FreeOnlyEvs 0 0 0 0 :=
    PhaseCreditSpec.freeOnly fineCostModel_modelHyps.freeNonInc
  have ⟨hs1c, hs1g⟩ := p2Sub1_16_fine_specs
  have ⟨hspkc, hspkg⟩ := spkPoll_fine_specs g.msg.signedPreKeyId hkf
  have ⟨hkpkc, hkpkg⟩ := kpkPoll_fine_specs (pmKyberId g.msg) hkf
  have ⟨hkemc, hkemg⟩ := kemKpFromPubPriv_fine_specs
  have ⟨htlc, htlg⟩ := p2Sub3Tail_fine_specs
  have ⟨hkpc, hkpg⟩ := kpPoll_fine_specs hkf
  have ⟨herrc, herrg⟩ := pqxdhAcceptBadKemErr_fine_specs
  have hspkf_c := phaseCreditSpec_seq_freeOnly_exact fineCostModel_modelHyps hspkc
  have hspkf_g := (hspkg.seq (PhaseGroupSpec.freeOnly fineCostModel)).mono
    (Nat.le_of_eq (Nat.add_zero _))
  have hkpkf_c := phaseCreditSpec_seq_freeOnly_exact fineCostModel_modelHyps hkpkc
  have hkpkf_g := (hkpkg.seq (PhaseGroupSpec.freeOnly fineCostModel)).mono
    (Nat.le_of_eq (Nat.add_zero _))
  have hkemf_c := phaseCreditSpec_seq_freeOnly_exact fineCostModel_modelHyps hkemc
  have hkemf_g := (hkemg.seq (PhaseGroupSpec.freeOnly fineCostModel)).mono
    (Nat.le_of_eq (Nat.add_zero _))
  have htlf_c := phaseCreditSpec_seq_freeOnly_exact fineCostModel_modelHyps htlc
  have htlf_g := (htlg.seq (PhaseGroupSpec.freeOnly fineCostModel)).mono
    (Nat.le_of_eq (Nat.add_zero _))
  have hkpf_c := phaseCreditSpec_seq_freeOnly_exact fineCostModel_modelHyps hkpc
  have hkpf_g := (hkpg.seq (PhaseGroupSpec.freeOnly fineCostModel)).mono
    (Nat.le_of_eq (Nat.add_zero _))
  have herrf_c := phaseCreditSpec_seq_freeOnly_exact fineCostModel_modelHyps herrc
  have herrf_g := (herrg.seq (PhaseGroupSpec.freeOnly fineCostModel)).mono
    (Nat.le_of_eq (Nat.add_zero _))
  have harm1_c : PhaseCreditSpec fineCostModel
      (P2Sub1To3Arm1Env 16
        (cliPollSpkGetPollEnv (ReadFileRuleEnv cliIo.rd) g.F StoresGhost.opened.signed
          g.msg.signedPreKeyId))
      stageP2UntypedFineCum 0 0 9808 :=
    (hs1c.seq hspkf_c).mono (by decide) (by decide) (by decide) (by decide)
  have harm1_g : PhaseGroupSpec fineCostModel
      (P2Sub1To3Arm1Env 16
        (cliPollSpkGetPollEnv (ReadFileRuleEnv cliIo.rd) g.F StoresGhost.opened.signed
          g.msg.signedPreKeyId))
      stageP2UntypedFineGrpS :=
    (hs1g.seq hspkf_g).mono (by decide)
  have harm2_c : PhaseCreditSpec fineCostModel
      (P2Sub1To3Arm2Env 16
        (cliPollSpkGetPollEnv (ReadFileRuleEnv cliIo.rd) g.F StoresGhost.opened.signed
          g.msg.signedPreKeyId)
        16
        (cliPollKpkGetPollEnv (ReadFileRuleEnv cliIo.rd) g.F StoresGhost.opened.kyber
          (pmKyberId g.msg)))
      stageP2UntypedFineCum 0 0 9808 :=
    (hs1c.seq (hspkc.seq (hfree_c.seq (hbox16c.seq hkpkf_c)))).mono
      (by decide) (by decide) (by decide) (by decide)
  have harm2_g : PhaseGroupSpec fineCostModel
      (P2Sub1To3Arm2Env 16
        (cliPollSpkGetPollEnv (ReadFileRuleEnv cliIo.rd) g.F StoresGhost.opened.signed
          g.msg.signedPreKeyId)
        16
        (cliPollKpkGetPollEnv (ReadFileRuleEnv cliIo.rd) g.F StoresGhost.opened.kyber
          (pmKyberId g.msg)))
      stageP2UntypedFineGrpS :=
    (hs1g.seq (hspkg.seq
      ((PhaseGroupSpec.freeOnly fineCostModel).seq
        (hbox16g.seq hkpkf_g)))).mono (by decide)
  have h13ok_c : PhaseCreditSpec fineCostModel
      (P2Sub1To3OkEnv 16
        (cliPollSpkGetPollEnv (ReadFileRuleEnv cliIo.rd) g.F StoresGhost.opened.signed
          g.msg.signedPreKeyId)
        16
        (cliPollKpkGetPollEnv (ReadFileRuleEnv cliIo.rd) g.F StoresGhost.opened.kyber
          (pmKyberId g.msg)))
      (19176 + spkPollFineCum + 488 + kpkPollFineCum + 28550 + 9581) 0 0 9808 :=
    (hs1c.seq (hspkc.seq
      (hfree_c.seq
        (hbox16c.seq (hkpkc.seq
          (hfree_c.seq
            (hkemc.seq
              (hfree_c.seq htlf_c)))))))).mono (by decide) (by decide) (by decide) (by decide)
  have h13ok_g : PhaseGroupSpec fineCostModel
      (P2Sub1To3OkEnv 16
        (cliPollSpkGetPollEnv (ReadFileRuleEnv cliIo.rd) g.F StoresGhost.opened.signed
          g.msg.signedPreKeyId)
        16
        (cliPollKpkGetPollEnv (ReadFileRuleEnv cliIo.rd) g.F StoresGhost.opened.kyber
          (pmKyberId g.msg)))
      ((6 + 3 + 6 + 3) * FineScale + spkPollFineGrpS + kpkPollFineGrpS) :=
    (hs1g.seq (hspkg.seq
      ((PhaseGroupSpec.freeOnly fineCostModel).seq
        (hbox16g.seq (hkpkg.seq
          ((PhaseGroupSpec.freeOnly fineCostModel).seq
            (hkemg.seq
              ((PhaseGroupSpec.freeOnly fineCostModel).seq htlf_g)))))))).mono (by decide)
  have hsub4_c : PhaseCreditSpec fineCostModel
      (P2Sub4OkEnv 16
        (cliPollPkGetPollEnv (ReadFileRuleEnv cliIo.rd) g.F StoresGhost.opened.oneTime)
        16 g.msg.preKeyId)
      (488 + pkPollFineCum + 488) 0 0 8192 := by
    unfold P2Sub4OkEnv
    cases g.msg.preKeyId with
    | none =>
      exact (hbox16c.of_imp fun _ h => (p2Sub4NoneEnv_iff_boxAllocEnv 16 _).mp h).mono
        (by decide) (by decide) (by decide) (by decide)
    | some id =>
      have ⟨hpkc, _⟩ := pkPoll_fine_specs id hkf
      exact (hbox16c.seq (hpkc.seq (hfree_c.seq hbox16c))).mono
        (by decide) (by decide) (by decide) (by decide)
  have hsub4_g : PhaseGroupSpec fineCostModel
      (P2Sub4OkEnv 16
        (cliPollPkGetPollEnv (ReadFileRuleEnv cliIo.rd) g.F StoresGhost.opened.oneTime)
        16 g.msg.preKeyId)
      ((3 + 3) * FineScale + pkPollFineGrpS) := by
    unfold P2Sub4OkEnv
    cases g.msg.preKeyId with
    | none =>
      exact ⟨fun st0 {_} h =>
        (hbox16g.mono (by decide)).groups_le st0 ((p2Sub4NoneEnv_iff_boxAllocEnv 16 _).mp h)⟩
    | some id =>
      have ⟨_, hpkg⟩ := pkPoll_fine_specs id hkf
      exact (hbox16g.seq (hpkg.seq
        ((PhaseGroupSpec.freeOnly fineCostModel).seq hbox16g))).mono (by decide)
  have harm3_c : PhaseCreditSpec fineCostModel
      (P2Sub1To4Arm3Env 16
        (cliPollSpkGetPollEnv (ReadFileRuleEnv cliIo.rd) g.F StoresGhost.opened.signed
          g.msg.signedPreKeyId)
        16
        (cliPollKpkGetPollEnv (ReadFileRuleEnv cliIo.rd) g.F StoresGhost.opened.kyber
          (pmKyberId g.msg))
        16
        (cliPollPkGetPollEnv (ReadFileRuleEnv cliIo.rd) g.F StoresGhost.opened.oneTime)
        g.msg.preKeyId)
      stageP2UntypedFineCum 0 0 9808 := by
    unfold P2Sub1To4Arm3Env
    cases g.msg.preKeyId with
    | none =>
      exact (PhaseCreditSpec.empty fineCostModel).mono
        (by decide) (by decide) (by decide) (by decide)
    | some id =>
      have ⟨hpkc, _⟩ := pkPoll_fine_specs id hkf
      have hpkf_c := phaseCreditSpec_seq_freeOnly_exact fineCostModel_modelHyps hpkc
      exact (h13ok_c.seq (hbox16c.seq hpkf_c)).mono
        (by decide) (by decide) (by decide) (by decide)
  have harm3_g : PhaseGroupSpec fineCostModel
      (P2Sub1To4Arm3Env 16
        (cliPollSpkGetPollEnv (ReadFileRuleEnv cliIo.rd) g.F StoresGhost.opened.signed
          g.msg.signedPreKeyId)
        16
        (cliPollKpkGetPollEnv (ReadFileRuleEnv cliIo.rd) g.F StoresGhost.opened.kyber
          (pmKyberId g.msg))
        16
        (cliPollPkGetPollEnv (ReadFileRuleEnv cliIo.rd) g.F StoresGhost.opened.oneTime)
        g.msg.preKeyId)
      stageP2UntypedFineGrpS := by
    unfold P2Sub1To4Arm3Env
    cases g.msg.preKeyId with
    | none => exact ⟨fun _ {_} h => False.elim h⟩
    | some id =>
      have ⟨_, hpkg⟩ := pkPoll_fine_specs id hkf
      have hpkf_g := (hpkg.seq (PhaseGroupSpec.freeOnly fineCostModel)).mono
        (Nat.le_of_eq (Nat.add_zero _))
      exact (h13ok_g.seq (hbox16g.seq hpkf_g)).mono (by decide)
  have h14ok_c := h13ok_c.seq hsub4_c
  have h14ok_g := h13ok_g.seq hsub4_g
  have harm4_c : PhaseCreditSpec fineCostModel
      (P2V1Arm4Env 16
        (cliPollSpkGetPollEnv (ReadFileRuleEnv cliIo.rd) g.F StoresGhost.opened.signed
          g.msg.signedPreKeyId)
        16
        (cliPollKpkGetPollEnv (ReadFileRuleEnv cliIo.rd) g.F StoresGhost.opened.kyber
          (pmKyberId g.msg))
        16
        (cliPollPkGetPollEnv (ReadFileRuleEnv cliIo.rd) g.F StoresGhost.opened.oneTime)
        16 g.msg.preKeyId
        (cliPollSelfKpPollEnv (ReadFileRuleEnv cliIo.rd) g.F StoresGhost.opened.identity))
      stageP2UntypedFineCum 0 0 9808 :=
    (h14ok_c.seq hkpf_c).mono (by decide) (by decide) (by decide) (by decide)
  have harm4_g : PhaseGroupSpec fineCostModel
      (P2V1Arm4Env 16
        (cliPollSpkGetPollEnv (ReadFileRuleEnv cliIo.rd) g.F StoresGhost.opened.signed
          g.msg.signedPreKeyId)
        16
        (cliPollKpkGetPollEnv (ReadFileRuleEnv cliIo.rd) g.F StoresGhost.opened.kyber
          (pmKyberId g.msg))
        16
        (cliPollPkGetPollEnv (ReadFileRuleEnv cliIo.rd) g.F StoresGhost.opened.oneTime)
        16 g.msg.preKeyId
        (cliPollSelfKpPollEnv (ReadFileRuleEnv cliIo.rd) g.F StoresGhost.opened.identity))
      stageP2UntypedFineGrpS :=
    (h14ok_g.seq hkpf_g).mono (by decide)
  have harm5_c : PhaseCreditSpec fineCostModel
      (P2V1Arm5EnvOfAcceptErr 16
        (cliPollSpkGetPollEnv (ReadFileRuleEnv cliIo.rd) g.F StoresGhost.opened.signed
          g.msg.signedPreKeyId)
        16
        (cliPollKpkGetPollEnv (ReadFileRuleEnv cliIo.rd) g.F StoresGhost.opened.kyber
          (pmKyberId g.msg))
        16
        (cliPollPkGetPollEnv (ReadFileRuleEnv cliIo.rd) g.F StoresGhost.opened.oneTime)
        16 g.msg.preKeyId
        (cliPollSelfKpPollEnv (ReadFileRuleEnv cliIo.rd) g.F StoresGhost.opened.identity)
        PqxdhAcceptBadKemErrEnv)
      stageP2UntypedFineCum 0 0 9808 :=
    (h14ok_c.seq (hkpc.seq (hfree_c.seq herrf_c))).mono
      (by decide) (by decide) (by decide) (by decide)
  have harm5_g : PhaseGroupSpec fineCostModel
      (P2V1Arm5EnvOfAcceptErr 16
        (cliPollSpkGetPollEnv (ReadFileRuleEnv cliIo.rd) g.F StoresGhost.opened.signed
          g.msg.signedPreKeyId)
        16
        (cliPollKpkGetPollEnv (ReadFileRuleEnv cliIo.rd) g.F StoresGhost.opened.kyber
          (pmKyberId g.msg))
        16
        (cliPollPkGetPollEnv (ReadFileRuleEnv cliIo.rd) g.F StoresGhost.opened.oneTime)
        16 g.msg.preKeyId
        (cliPollSelfKpPollEnv (ReadFileRuleEnv cliIo.rd) g.F StoresGhost.opened.identity)
        PqxdhAcceptBadKemErrEnv)
      stageP2UntypedFineGrpS :=
    (h14ok_g.seq (hkpg.seq
      ((PhaseGroupSpec.freeOnly fineCostModel).seq herrf_g))).mono (by decide)
  change PhaseCreditSpec fineCostModel _ _ _ _ _ ∧ PhaseGroupSpec fineCostModel _ _
  unfold StageP2BadKemRejectEnv
  dsimp only [cliPollSpkKitPlaced, cliPollSpkFullBudgetEnv, cliPollKpkKitPlaced,
    cliPollKpkFullBudgetEnv, cliPollPkKitPlaced, cliPollPkFullBudgetEnv, cliPollSelfKitPlaced,
    cliPollSelfBudgetEnv]
  refine ⟨?_, ?_⟩
  · exact (harm1_c.or (harm2_c.or (harm3_c.or (harm4_c.or harm5_c)))).mono
      (Nat.le_refl _) (Nat.le_refl 0) (Nat.le_refl 0) (Nat.le_refl 9808)
  · exact (harm1_g.or (harm2_g.or (harm3_g.or (harm4_g.or harm5_g)))).mono (by decide)

/-! ## 2. Closed Cap Constants and `SingleSlotFineSpec` -/

def trustPollFineCum : Nat := 21185 + max 738 (fineReadFileCum sessionCapBytes)
def trustPollFineLive : Nat := fineReadFileLive sessionCapBytes
def trustPollFinePeak : Nat := fineReadFilePeak sessionCapBytes
def trustPollFineMaxReq : Nat := max 256 (fineReadFileMaxReq sessionCapBytes)

def stageP1UntypedFineCum : Nat :=
  defaultW4LoadCum sessionCapBytes deserCancelFineCum +
    w4BoxedStepCum 32 trustPollFineCum + (2 * 40 + 9539)

/-- Closed `fineCostModel` cumulative small-allocation charge bound for `DecPkD3UntypedEnv`. -/
def decPkD3UntypedCum : Nat := stageP1UntypedFineCum + stageP2UntypedFineCum

/-- Closed `fineCostModel` large-allocation live-byte delta bound for `DecPkD3UntypedEnv`. -/
def decPkD3UntypedLive : Nat :=
  defaultW4LoadLive sessionCapBytes deserCancelFineLive +
    w4BoxedStepLive 32 trustPollFineLive

/-- Closed `fineCostModel` large-allocation peak-byte delta bound for `DecPkD3UntypedEnv`. -/
def decPkD3UntypedPeak : Nat :=
  max (defaultW4LoadPeak sessionCapBytes deserCancelFinePeak)
    (defaultW4LoadLive sessionCapBytes deserCancelFineLive +
      max (w4BoxedStepPeak 32 trustPollFinePeak) (w4BoxedStepLive 32 trustPollFineLive))

/-- Closed `fineCostModel` max-request byte bound for `DecPkD3UntypedEnv`. -/
def decPkD3UntypedMaxReq : Nat :=
  max (max (defaultW4LoadMaxReq sessionCapBytes deserCancelFineMaxReq)
    (max (w4BoxedStepMaxReq 32 trustPollFineMaxReq) 40)) 9808

/-- Closed `fineCostModel` scaled `meta_area` group bound for `DecPkD3UntypedEnv`. -/
def decPkD3UntypedGrpS : Nat :=
  93 * FineScale + deserCancelFineGrpS + stageP2UntypedFineGrpS

/-- Closed inequalities bounding `DecPkD3UntypedEnv` within
`CliTopBudgetSpec.cliRecvPrekeySlot*Cap`. -/
theorem decPkD3Untyped_caps_le :
    decPkD3UntypedLive ≤ decPkD3UntypedPeak ∧
    decPkD3UntypedCum ≤ cliRecvPrekeySlotCumCap ∧
    decPkD3UntypedLive ≤ cliRecvPrekeySlotLiveCap ∧
    decPkD3UntypedPeak ≤ cliRecvPrekeySlotPeakCap ∧
    decPkD3UntypedMaxReq ≤ cliRecvPrekeySlotReqCap ∧
    decPkD3UntypedGrpS ≤ cliRecvPrekeySlotGrpSCap :=
  ⟨by decide, by decide, by decide, by decide, by decide, by decide⟩

/-- Closed inequalities bounding `DecPkD3UntypedEnv` within the `1 MiB` `recv` pre-key slot caps
(`W4RecvPrekeyRealSlot1MiB` and `w4RecvPrekeyRealGrpS`). -/
theorem decPkD3Untyped_caps_le_1MiB :
    decPkD3UntypedCum ≤ w4RecvPrekeyReal1MiB_i_Cum ∧
    decPkD3UntypedLive ≤ w4RecvPrekeyReal1MiB_i_Live ∧
    decPkD3UntypedPeak ≤ w4RecvPrekeyReal1MiB_i_Peak ∧
    decPkD3UntypedMaxReq ≤ w4RecvPrekeyReal1MiB_i_MaxReq ∧
    decPkD3UntypedGrpS ≤ w4RecvPrekeyRealGrpS :=
  ⟨by decide, by decide, by decide, by decide, by decide⟩

theorem decPkD3UntypedEnv_phaseCreditSpec [LibsignalPlacement]
    (A : RustAlloc) (W : CliHooks) (B : RunBudgets) (g : DecPkGhost)
    (hpeer : g.peer.name.bytes.length ≤ 40)
    (hkf : DecPkKeyFilesBounded g.F) :
    PhaseCreditSpec fineCostModel (DecPkD3UntypedEnv A W B g)
      decPkD3UntypedCum decPkD3UntypedLive decPkD3UntypedPeak decPkD3UntypedMaxReq := by
  have hdcPeers : DirDomainCaps 64 0 0 StoresGhost.opened.identity.peers :=
    dirDomainCaps_opened_peers.mono (by decide) (Nat.le_refl 0) (Nat.le_refl 0)
  have hdcSess : DirDomainCaps 64 0 0 StoresGhost.opened.sessions :=
    dirDomainCaps_opened_sess.mono (by decide) (Nat.le_refl 0) (Nat.le_refl 0)
  have hname_le : g.peer.val.name.length ≤ 64 :=
    Nat.le_trans hpeer (by decide)
  have hSessCap : ∀ bs,
      cliIo.rd g.F (pathOf StoresGhost.opened.sessions.path (addressText g.peer.val)) = .ok bs →
      bs.length ≤ sessionCapBytes :=
    fun bs hrd => cliIo_rd_ok_length_le_sessionCapBytes g.F _ bs hrd
  have hPeersCap : ∀ bs,
      cliIo.rd g.F (pathOf StoresGhost.opened.identity.peers.path g.peer.val.name) = .ok bs →
      bs.length ≤ sessionCapBytes :=
    fun bs hrd => cliIo_rd_ok_length_le_sessionCapBytes g.F _ bs hrd
  have hDeser : ∀ r, scopeKit r → (encodeRecord r).length ≤ max 0 sessionCapBytes →
      PhaseCreditSpec fineCostModel (SessDeserializeCancelEnv r)
        deserCancelFineCum deserCancelFineLive deserCancelFinePeak deserCancelFineMaxReq := by
    intro r _ hr
    have hr' : (encodeRecord r).length ≤ sessionCapBytes := by omega
    exact (recordDeserializeCancelEnv_fine_phaseCreditSpec hr').of_imp
      fun _ h => sessDeserializeCancelEnv_imp_recordDeserializeCancelEnv h
  let sKit := cliPollSessKitPlaced A g.F scopeKit g.peer (cliKitStk B)
  let sEnv := cliPollSessBudgetEnv A g.F g.peer B (ReadFileRuleEnv cliIo.rd) SessDeserializeCancelEnv
  let iKit := cliPollIdKitPlaced A g.F g.peer (cliKitStk B)
  let iEnv := cliPollIdBudgetEnv A g.F g.peer B (ReadFileRuleEnv cliIo.rd)
  have hsBox : sKit.loadBoxSize = 24 := rfl
  have hiBox : iKit.trustBoxSize = 32 := rfl
  have hTrust : PhaseCreditSpec fineCostModel
      (iEnv.trustPollEnv StoresGhost.opened.identity g.peer.val g.msg.identityKey .receiving)
      trustPollFineCum trustPollFineLive trustPollFinePeak trustPollFineMaxReq :=
    phaseCreditSpec_seq_freeOnly_exact fineCostModel_modelHyps
      (dirGetEnv_path_readFile_fine_phaseCredit_tight cliIo.rd g.F
        StoresGhost.opened.identity.peers g.peer.val.name hdcPeers hname_le hPeersCap)
  have hLoadPoll : PhaseCreditSpec fineCostModel
      (sEnv.loadPollEnv StoresGhost.opened.sessions g.peer.val)
      (defaultLoadPollTightDeltaCum sessionCapBytes deserCancelFineCum)
      (fineReadFileLive sessionCapBytes + deserCancelFineLive)
      (max (fineReadFilePeak sessionCapBytes)
        (fineReadFileLive sessionCapBytes + deserCancelFinePeak))
      (max (max 256 (fineReadFileMaxReq sessionCapBytes)) deserCancelFineMaxReq) :=
    defaultLoadPollEnv_fine_phaseCredit_tight hdcSess (by decide) hpeer hSessCap hDeser
  have hLoadStep : PhaseCreditSpec fineCostModel
      (LoadStepEnv sKit sEnv StoresGhost.opened.sessions g.peer.val)
      (defaultW4LoadCum sessionCapBytes deserCancelFineCum)
      (defaultW4LoadLive sessionCapBytes deserCancelFineLive)
      (defaultW4LoadPeak sessionCapBytes deserCancelFinePeak)
      (defaultW4LoadMaxReq sessionCapBytes deserCancelFineMaxReq) := by
    have h := loadStepEnv_phaseCredit fineCostModel_modelHyps sKit sEnv
      StoresGhost.opened.sessions g.peer.val hLoadPoll
    rw [hsBox] at h
    exact h
  have hTrustStep : PhaseCreditSpec fineCostModel
      (TrustStepEnv iKit iEnv StoresGhost.opened.identity g.peer.val g.msg.identityKey .receiving)
      (w4BoxedStepCum 32 trustPollFineCum)
      (w4BoxedStepLive 32 trustPollFineLive)
      (w4BoxedStepPeak 32 trustPollFinePeak)
      (w4BoxedStepMaxReq 32 trustPollFineMaxReq) := by
    have h := trustStepEnv_phaseCredit fineCostModel_modelHyps iKit iEnv
      StoresGhost.opened.identity g.peer.val g.msg.identityKey .receiving hTrust
    rw [hiBox] at h
    exact h
  have hStrCl : PhaseCreditSpec fineCostModel
      (SeqEnv (LibsignalBinary.Heap.RustStdAllocBudgetBridge.StringCloneEnv g.peer.name) FreeOnlyEvs)
      (2 * 40 + 9539) 0 0 40 :=
    phaseCreditSpec_seq_freeOnly_exact fineCostModel_modelHyps
      (stringClone_phaseCredit_small fineCostModel_modelHyps hpeer
        (by rw [fineCostModel_smallMaxReq_eq]; decide))
  have hUntr : PhaseCreditSpec fineCostModel
      (CliDpPollUntrustedEnv (A := A) B (ReadFileRuleEnv cliIo.rd) SessDeserializeCancelEnv g)
      decPkD3UntypedCum decPkD3UntypedLive decPkD3UntypedPeak decPkD3UntypedMaxReq := by
    unfold CliDpPollUntrustedEnv StageP1UntrustedEnv
    exact (hLoadStep.seq (hTrustStep.seq hStrCl)).mono
      (by decide) (by decide) (by decide) (by decide)
  have hP1Ok : PhaseCreditSpec fineCostModel
      (StageP1OkEnv (cliPollSessKitPlaced A g.F scopeKit g.peer (cliKitStk B))
        (cliPollSessBudgetEnv A g.F g.peer B (ReadFileRuleEnv cliIo.rd) SessDeserializeCancelEnv)
        StoresGhost.opened.sessions
        (cliPollIdKitPlaced A g.F g.peer (cliKitStk B))
        (cliPollIdBudgetEnv A g.F g.peer B (ReadFileRuleEnv cliIo.rd))
        StoresGhost.opened.identity g.peer.val g.msg.identityKey)
      stageP1UntypedFineCum decPkD3UntypedLive decPkD3UntypedPeak
      (max (defaultW4LoadMaxReq sessionCapBytes deserCancelFineMaxReq)
        (max (w4BoxedStepMaxReq 32 trustPollFineMaxReq) 40)) := by
    unfold StageP1OkEnv
    exact (hLoadStep.seq hTrustStep).mono (by decide) (by decide) (by decide) (by decide)
  have hP2 (opt : Option (SessionRecord (List (BitVec 8)))) : PhaseCreditSpec fineCostModel
      (StageP2UntypedRejectEnv (A := A) B (ReadFileRuleEnv cliIo.rd) PqxdhAcceptBadKemErrEnv g opt)
      stageP2UntypedFineCum 0 0 9808 :=
    (stageP2V3Reject_fine_specs.1.or (stageP2BadKemReject_fine_specs B g opt hkf).1).mono
      (Nat.max_self _).le (Nat.max_self 0).le (Nat.max_self 0).le (Nat.max_self 9808).le
  have hopt (opt : Option (SessionRecord (List (BitVec 8)))) : PhaseCreditSpec fineCostModel
      (SeqEnv
        (StageP1OkEnv (cliPollSessKitPlaced A g.F scopeKit g.peer (cliKitStk B))
          (cliPollSessBudgetEnv A g.F g.peer B (ReadFileRuleEnv cliIo.rd)
            SessDeserializeCancelEnv)
          StoresGhost.opened.sessions
          (cliPollIdKitPlaced A g.F g.peer (cliKitStk B))
          (cliPollIdBudgetEnv A g.F g.peer B (ReadFileRuleEnv cliIo.rd))
          StoresGhost.opened.identity g.peer.val g.msg.identityKey)
        (StageP2UntypedRejectEnv (A := A) B (ReadFileRuleEnv cliIo.rd)
          PqxdhAcceptBadKemErrEnv g opt))
      decPkD3UntypedCum decPkD3UntypedLive decPkD3UntypedPeak decPkD3UntypedMaxReq :=
    (hP1Ok.seq (hP2 opt)).mono (by decide) (by decide) (by decide) (by decide)
  have hArm2 : PhaseCreditSpec fineCostModel
      (fun evs => ∃ opt : Option (SessionRecord (List (BitVec 8))),
        SeqEnv
          (StageP1OkEnv (cliPollSessKitPlaced A g.F scopeKit g.peer (cliKitStk B))
            (cliPollSessBudgetEnv A g.F g.peer B (ReadFileRuleEnv cliIo.rd)
              SessDeserializeCancelEnv)
            StoresGhost.opened.sessions
            (cliPollIdKitPlaced A g.F g.peer (cliKitStk B))
            (cliPollIdBudgetEnv A g.F g.peer B (ReadFileRuleEnv cliIo.rd))
            StoresGhost.opened.identity g.peer.val g.msg.identityKey)
          (StageP2UntypedRejectEnv (A := A) B (ReadFileRuleEnv cliIo.rd)
            PqxdhAcceptBadKemErrEnv g opt) evs)
      decPkD3UntypedCum decPkD3UntypedLive decPkD3UntypedPeak decPkD3UntypedMaxReq :=
    ⟨fun evs ⟨opt, hseq⟩ => (hopt opt).req_align evs hseq,
     fun st0 {_} ⟨opt, hseq⟩ => (hopt opt).credit_le st0 hseq⟩
  exact (hUntr.or hArm2).mono
    (Nat.max_self _).le (Nat.max_self _).le (Nat.max_self _).le (Nat.max_self _).le

theorem decPkD3UntypedEnv_fine_groupSpec [LibsignalPlacement]
    (A : RustAlloc) (W : CliHooks) (B : RunBudgets) (g : DecPkGhost)
    (hpeer : g.peer.name.bytes.length ≤ 40)
    (hkf : DecPkKeyFilesBounded g.F) :
    PhaseGroupSpec fineCostModel (DecPkD3UntypedEnv A W B g) decPkD3UntypedGrpS := by
  have hSessCap : ∀ bs,
      StoresGhost.opened.sessions.get cliIo.rd g.F (addressText g.peer.val) = .ok bs →
      bs.length ≤ sessionCapBytes :=
    fun bs hrd => cliIo_rd_ok_length_le_sessionCapBytes g.F _ bs hrd
  have hDeserG : ∀ r, scopeKit r → (encodeRecord r).length ≤ sessionCapBytes →
      PhaseGroupSpec fineCostModel (SessDeserializeCancelEnv r) deserCancelFineGrpS := by
    intro r _ _
    exact ⟨fun st0 {_} h =>
      (recordDeserializeCancelEnv_fine_groupSpec (encodeRecord r)).groups_le st0
        (sessDeserializeCancelEnv_imp_recordDeserializeCancelEnv h)⟩
  have hLoadPollG := defaultLoadPollEnv_fine_groupSpec hpeer hSessCap hDeserG
  have hBox24G : PhaseGroupSpec fineCostModel (BoxAllocEnv 24) (3 * FineScale) :=
    (boxAllocEnv_le_28_fine_groupSpec (boxSz := 24) (by decide)).mono (by decide)
  have hBox24FreeG : PhaseGroupSpec fineCostModel (· = rustDeallocEvents 24 8) 0 :=
    (PhaseGroupSpec.of_nonFreeBound fineCostModel (maxOps := 0) (by
      rintro _ rfl; decide)).mono (by decide)
  have hLoadStepG : PhaseGroupSpec fineCostModel
      (LoadStepEnv
        (cliPollSessKitPlaced A g.F scopeKit g.peer (cliKitStk B))
        (cliPollSessBudgetEnv A g.F g.peer B (ReadFileRuleEnv cliIo.rd) SessDeserializeCancelEnv)
        StoresGhost.opened.sessions g.peer.val)
      (48 * FineScale + deserCancelFineGrpS) := by
    unfold LoadStepEnv
    change PhaseGroupSpec fineCostModel
      (SeqEnv (BoxAllocEnv 24) (SeqEnv _ (· = rustDeallocEvents 24 8)))
      (48 * FineScale + deserCancelFineGrpS)
    exact (hBox24G.seq (hLoadPollG.seq hBox24FreeG)).mono (by omega)
  have hBox32G : PhaseGroupSpec fineCostModel (BoxAllocEnv 32) (3 * FineScale) :=
    PhaseGroupSpec.of_nonFreeBound fineCostModel (maxOps := 1) (by
      intro evs h
      rw [(boxAllocEnv_iff_eq 32 evs).mp h]
      decide)
  have hBox32FreeG : PhaseGroupSpec fineCostModel (· = rustDeallocEvents 32 8) 0 :=
    (PhaseGroupSpec.of_nonFreeBound fineCostModel (maxOps := 0) (by
      rintro _ rfl; decide)).mono (by decide)
  have hTrustPollG : PhaseGroupSpec fineCostModel
      ((cliPollIdBudgetEnv A g.F g.peer B (ReadFileRuleEnv cliIo.rd)).trustPollEnv
        StoresGhost.opened.identity g.peer.val g.msg.identityKey .receiving)
      (39 * FineScale) := by
    change PhaseGroupSpec fineCostModel
      (SeqEnv
        (DirGetEnv PathEnv (ReadFileRuleEnv cliIo.rd) cliIo.rd g.F
          StoresGhost.opened.identity.peers g.peer.val.name)
        FreeOnlyEvs)
      (39 * FineScale)
    exact ((dirGetEnv_path_readFile_groupSpec fineCostModel cliIo.rd g.F
      StoresGhost.opened.identity.peers g.peer.val.name).seq
      (PhaseGroupSpec.freeOnly fineCostModel)).mono (by decide)
  have hTrustStepG : PhaseGroupSpec fineCostModel
      (TrustStepEnv
        (cliPollIdKitPlaced A g.F g.peer (cliKitStk B))
        (cliPollIdBudgetEnv A g.F g.peer B (ReadFileRuleEnv cliIo.rd))
        StoresGhost.opened.identity g.peer.val g.msg.identityKey .receiving)
      (42 * FineScale) := by
    unfold TrustStepEnv
    change PhaseGroupSpec fineCostModel
      (SeqEnv (BoxAllocEnv 32)
        (SeqEnv
          ((cliPollIdBudgetEnv A g.F g.peer B (ReadFileRuleEnv cliIo.rd)).trustPollEnv
            StoresGhost.opened.identity g.peer.val g.msg.identityKey .receiving)
          (· = rustDeallocEvents 32 8)))
      (42 * FineScale)
    exact (hBox32G.seq (hTrustPollG.seq hBox32FreeG)).mono (by decide)
  have hStrClG : PhaseGroupSpec fineCostModel
      (LibsignalBinary.Heap.RustStdAllocBudgetBridge.StringCloneEnv g.peer.name)
      (3 * FineScale) :=
    PhaseGroupSpec.of_nonFreeBound fineCostModel (maxOps := 1) (by
      intro evs h
      rcases h with ⟨_, rfl⟩ | ⟨_, rfl⟩
      · exact Nat.zero_le 1
      · unfold rustAllocEvents
        split <;> exact Nat.le_refl 1)
  have hUntrG : PhaseGroupSpec fineCostModel
      (CliDpPollUntrustedEnv (A := A) B (ReadFileRuleEnv cliIo.rd) SessDeserializeCancelEnv g)
      decPkD3UntypedGrpS := by
    unfold CliDpPollUntrustedEnv StageP1UntrustedEnv
    have hcore := hLoadStepG.seq (hTrustStepG.seq
      ((hStrClG.seq (PhaseGroupSpec.freeOnly fineCostModel)).mono
        (Nat.le_of_eq (Nat.add_zero _))))
    exact hcore.mono (by decide)
  have hP1OkG : PhaseGroupSpec fineCostModel
      (StageP1OkEnv (cliPollSessKitPlaced A g.F scopeKit g.peer (cliKitStk B))
        (cliPollSessBudgetEnv A g.F g.peer B (ReadFileRuleEnv cliIo.rd) SessDeserializeCancelEnv)
        StoresGhost.opened.sessions
        (cliPollIdKitPlaced A g.F g.peer (cliKitStk B))
        (cliPollIdBudgetEnv A g.F g.peer B (ReadFileRuleEnv cliIo.rd))
        StoresGhost.opened.identity g.peer.val g.msg.identityKey)
      (90 * FineScale + deserCancelFineGrpS) :=
    (hLoadStepG.seq hTrustStepG).mono (by omega)
  have hP2G (opt : Option (SessionRecord (List (BitVec 8)))) : PhaseGroupSpec fineCostModel
      (StageP2UntypedRejectEnv (A := A) B (ReadFileRuleEnv cliIo.rd) PqxdhAcceptBadKemErrEnv g opt)
      stageP2UntypedFineGrpS :=
    (stageP2V3Reject_fine_specs.2.or (stageP2BadKemReject_fine_specs B g opt hkf).2).mono
      (Nat.max_self _).le
  have hoptG (opt : Option (SessionRecord (List (BitVec 8)))) : PhaseGroupSpec fineCostModel
      (SeqEnv
        (StageP1OkEnv (cliPollSessKitPlaced A g.F scopeKit g.peer (cliKitStk B))
          (cliPollSessBudgetEnv A g.F g.peer B (ReadFileRuleEnv cliIo.rd)
            SessDeserializeCancelEnv)
          StoresGhost.opened.sessions
          (cliPollIdKitPlaced A g.F g.peer (cliKitStk B))
          (cliPollIdBudgetEnv A g.F g.peer B (ReadFileRuleEnv cliIo.rd))
          StoresGhost.opened.identity g.peer.val g.msg.identityKey)
        (StageP2UntypedRejectEnv (A := A) B (ReadFileRuleEnv cliIo.rd)
          PqxdhAcceptBadKemErrEnv g opt))
      decPkD3UntypedGrpS :=
    (hP1OkG.seq (hP2G opt)).mono (by decide)
  have hArm2G : PhaseGroupSpec fineCostModel
      (fun evs => ∃ opt : Option (SessionRecord (List (BitVec 8))),
        SeqEnv
          (StageP1OkEnv (cliPollSessKitPlaced A g.F scopeKit g.peer (cliKitStk B))
            (cliPollSessBudgetEnv A g.F g.peer B (ReadFileRuleEnv cliIo.rd)
              SessDeserializeCancelEnv)
            StoresGhost.opened.sessions
            (cliPollIdKitPlaced A g.F g.peer (cliKitStk B))
            (cliPollIdBudgetEnv A g.F g.peer B (ReadFileRuleEnv cliIo.rd))
            StoresGhost.opened.identity g.peer.val g.msg.identityKey)
          (StageP2UntypedRejectEnv (A := A) B (ReadFileRuleEnv cliIo.rd)
            PqxdhAcceptBadKemErrEnv g opt) evs)
      decPkD3UntypedGrpS :=
    ⟨fun st0 {_} ⟨opt, hseq⟩ => (hoptG opt).groups_le st0 hseq⟩
  exact (hUntrG.or hArm2G).mono (Nat.max_self _).le

/-- `SingleSlotFineSpec` for `DecPkD3UntypedEnv A W B g` from `g.peer.name.bytes.length ≤ 40`
and `DecPkKeyFilesBounded g.F`. -/
def decPkD3UntypedEnv_singleSlotFineSpec [LibsignalPlacement]
    (A : RustAlloc) (W : CliHooks) (B : RunBudgets) (g : DecPkGhost)
    (hpeer : g.peer.name.bytes.length ≤ 40)
    (hkf : DecPkKeyFilesBounded g.F) :
    SingleSlotFineSpec (DecPkD3UntypedEnv A W B g) where
  cum := decPkD3UntypedCum
  live := decPkD3UntypedLive
  peak := decPkD3UntypedPeak
  maxReq := decPkD3UntypedMaxReq
  grpS := decPkD3UntypedGrpS
  credit := decPkD3UntypedEnv_phaseCreditSpec A W B g hpeer hkf
  live_le_peak := decPkD3Untyped_caps_le.1
  groups := decPkD3UntypedEnv_fine_groupSpec A W B g hpeer hkf

/-- Call-site `SingleSlotFineSpec` for `DecPkD3UntypedEnv` when `g.peer.name.bytes = peerV.name`
and `g.F = runFiles i` under `CliPqxdhInputs P i` or `pqRecvInputs P st ct rc`. -/
def decPkD3UntypedEnv_of_inputs_singleSlotFineSpec [LibsignalPlacement]
    (A : RustAlloc) (W : CliHooks) (B : RunBudgets)
    {P : PEParams} {i : Inputs} {peerV : AddrV} (g : DecPkGhost)
    (hi : CliPqxdhInputs P i ∨
      ∃ (st : PqParty) (ct : List (BitVec 8)) (rc : BitVec 256),
        PqxdhPartyInSpecDomain P st ∧ i = pqRecvInputs P st ct rc)
    (hparse : parseArgs uuidTryParse (i.argv.map bytesOfString) = some (.recv peerV))
    (hpeer_eq : g.peer.name.bytes = peerV.name)
    (hF : g.F = runFiles i) :
    SingleSlotFineSpec (DecPkD3UntypedEnv A W B g) :=
  decPkD3UntypedEnv_singleSlotFineSpec A W B g
    (by rw [hpeer_eq]; exact parseArgs_peer_name_length_le hparse)
    (by rw [hF]; exact decPkKeyFilesBounded_of_pqOrD3Recv hi)

/-- `SingleSlotFineSpec` for `DecPkD3UntypedEnv` at `r3bDecPkGhost` under `CliPqxdhInputs P call.i`
or `pqRecvInputs P st ct rc`. -/
def decPkD3UntypedEnv_r3b_singleSlotFineSpec [LibsignalPlacement]
    (A : RustAlloc) (W : CliHooks) (B : RunBudgets)
    {P : PEParams} (call : RunCall) (meV peerV : AddrV) (pm : PreKeySignalMessage)
    (hi : CliPqxdhInputs P call.i ∨
      ∃ (st : PqParty) (ct : List (BitVec 8)) (rc : BitVec 256),
        PqxdhPartyInSpecDomain P st ∧ call.i = pqRecvInputs P st ct rc)
    (hparse : parseArgs uuidTryParse (call.i.argv.map bytesOfString) = some (.recv peerV)) :
    SingleSlotFineSpec (DecPkD3UntypedEnv A W B (r3bDecPkGhost call meV peerV pm)) :=
  decPkD3UntypedEnv_of_inputs_singleSlotFineSpec A W B (r3bDecPkGhost call meV peerV pm)
    hi hparse rfl rfl

/-- Non-empty allocation trace witness (`boxAllocEvents 24 ≠ []`) for `DecPkD3UntypedEnv`. -/
theorem decPkD3UntypedEnv_nonvacuous_alloc [LibsignalPlacement]
    (A : RustAlloc) (W : CliHooks) (B : RunBudgets) (g : DecPkGhost) :
    ∃ evs : List AllocEvent, evs ≠ [] ∧ DecPkD3UntypedEnv A W B g evs :=
  ⟨boxAllocEvents 24, by decide,
    Or.inr ⟨none, Or.inl (Or.inl (Or.inl ((boxAllocEnv_iff_eq 24 _).mpr rfl)))⟩⟩

abbrev nonvacuous_alloc := @decPkD3UntypedEnv_nonvacuous_alloc

export LibsignalBinary.Proofs.SignalSession.Cli.D3.Budget.D3BadKemEnvAPlacedBudget (
  DecPkKeyFilesBounded decPkKeyFilesBounded_of_cliPqInputs decPkKeyFilesBounded_of_pqOrD3Recv
)

end LibsignalBinary.Proofs.SignalSession.Cli.D3.Budget.D3BadKemEnvCPlacedBudget
