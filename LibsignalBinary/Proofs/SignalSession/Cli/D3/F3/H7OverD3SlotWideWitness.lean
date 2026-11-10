/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP2PurePlacedBudget
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Matched.M3PrevCapPlacedBudget
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Over.StageP3PlacedBudgetAux
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Over.StageP4Prev1DefsPlacedBudget
public import LibsignalBinary.Proofs.E2E.Pqxdh.ResponderCore.AcceptPlacedABudget
public import LibsignalBinary.Proofs.PeakBudget.CliRealBinaryKitEnvs
public import LibsignalBinary.Proofs.PeakBudget.RealCliRunEnvMemFixed
public import LibsignalBinary.Proofs.PeakBudget.SpqrTrialDomainLiftAux
public import LibsignalBinary.Proofs.PeakBudget.W2DecryptCloneBounds
public import LibsignalBinary.Proofs.PeakBudget.W4OuterPeakSpec
public import LibsignalBinary.Proofs.PeakBudget.W4OuterTightSpecAux
public import LibsignalBinary.Proofs.PeakBudget.W4PathCVerNeWideDefs
public import LibsignalBinary.Proofs.PeakBudget.W4RecvPrekeyCmkSlot
public import LibsignalBinary.Proofs.PublicApi.MessageDecrypt.DefsBudget
public import LibsignalBinary.Proofs.SessionRecordMin.DeserializeCancelBudgetAux
public import LibsignalBinary.Proofs.SignalSession.Cli.D3.Budget.D3NonCanonValidOverPollPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.D3.F3.H7OverD3SlotDom0EnvSub
public import LibsignalBinary.Proofs.SignalSession.Cli.D3.F3.H7OverD3SlotDom0Leaves16
public import LibsignalBinary.Proofs.SignalSession.Cli.F3.HRead.ReadFileBudgetPlaced
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Over.PollOverP4ContPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Over.PollOverPathCPlacedBudgetAux
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Over.Stage2OverInstPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Over.StagesOverCliPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.ClosureUntrustedPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.StagesInst.Stage2V1KitsPlacedBudgetAux
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.StagesInst.Stage4V1InstPlacedBudget

/-!
# `Out1Dom`-Parametric `OverD3` Witness and Per-Arm Envelope Assembly

Constructs the `Out1Dom`-parametric call-site domain bundle `H7wCallSiteDomOut1`, the Path-C slot
envelope `H7wOverSlotEnvAllFixedOf`, its embedding into 4-arm outer `AllFixed` slot envelopes, and
witness theorems for all seven `OverD3` execution arms.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000

namespace LibsignalBinary.Proofs.SignalSession.Cli.D3.F3.H7OverD3SlotWideWitness

open CryptoGames.LibsignalSession (
  Crypto IdentityKey PublicKey SessionState ShaCompress SignalMessage
)
open CryptoGames.LibsignalSessionApi (Session SessionRecord)
open CryptoVerification (LibsignalPlacement)
open CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Over (clearPending)
open CryptoVerification.E2E (PreKeyMessageFields UnreachedPqxdhPrimitives modelPrims)
open CryptoVerification.E2E.Pqxdh.ResponderCore (ofSignalPqxdhPrimitives)
open CryptoVerification.E2E.Record (encSession encodeRecord)
open CryptoVerification.LibsignalPublicApi.StoreKit (FsFiles)
open CryptoVerification.LibsignalPublicApiRepr (AddrVal RecordGhost)
open CryptoVerification.LibsignalSpqrV1 (MlKem)
open CryptoVerification.LibsignalTripleRatchet (DoReserveCall reserveCap)
open CryptoVerification.LibsignalTripleRatchetRepr (
  AddrGhost SessionGhost SignalMessageGhost
)
open CryptoVerification.RustHeap (RustAlloc)
open CryptoVerification.SignalSession (CliHooks)
open CryptoVerification.SignalSession.Cli (StoresGhost)
open CryptoVerification.SignalSession.Cli.MainHops (cliIo cliRunBudgets)
open CryptoVerification.SignalSession.Cli.RunCompose (DecPkGhost)
open CryptoVerification.SignalSession.Cli.RunProofs (pkToE?)
open CryptoVerification.SignalSession.Cli.RunProofs.Poll (
  cliKitStk cliPollIdKitPlaced cliPollKpkKitPlaced cliPollPkKitPlaced cliPollSessPrev1KitPlaced
)
open CryptoVerification.SpqrV1.Top.InitialState (InitialStateGhost)
open LibsignalBinary.Heap (AllocEvent FreeOnlyEvs SeqEnv)
open LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP2PurePlacedBudget (
  InitializeBobV1OptFieldsEnv
)
open LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Matched.M3PrevCapPlacedBudget (
  StageP3ErrM3Env StageP3OkPrefixM3Env stageP3M3TryDecryptEnvArgs
)
open LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Over.StageP3PlacedBudgetAux (
  StageP3Prev1Env StageP3VerNePrev1Env
)
open LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Over.StageP4Prev1DefsPlacedBudget (
  StageP4Prev1ExitEnv
)
open LibsignalBinary.Proofs.E2E.Pqxdh.ResponderCore.AcceptPlacedABudget (AcceptOptFieldsEnv)
open LibsignalBinary.Proofs.PeakBudget.CliRealBinaryKitEnvs (W4CloneACDomEnv)
open LibsignalBinary.Proofs.PeakBudget.RealCliRunEnvMemFixed (
  W4BinaryStageP1OkEnvAllFixed W4BinaryStageP1UntrustedEnvAllFixed
  W4BinaryStageP2PathCWideEnvAllFixed W4BinaryStageP4PathCWideEnvAllFixed
)
open LibsignalBinary.Proofs.PeakBudget.SpqrTrialDomainLiftAux (TopStateTight)
open LibsignalBinary.Proofs.PeakBudget.W2DecryptCloneBounds (
  FreshBobCloneDom SessionCloneDom
)
open LibsignalBinary.Proofs.PeakBudget.W4OuterPeakSpec (OptStageEnv)
open LibsignalBinary.Proofs.PeakBudget.W4OuterTightSpecAux (FreshBobPrev1Dom)
open LibsignalBinary.Proofs.PeakBudget.W4PathCVerNeWideDefs (
  VerNeTightTopEnv VerNeTightTopRawEnv W4StageP3Prev1WideEnv W4StageP3Prev1WideEnvOf
)
open LibsignalBinary.Proofs.PeakBudget.W4RecvPrekeyCmkSlot (
  W4ArchivedTrialCmk W4ArchivedTrialDomCmkOf W4BinaryCallSiteDomCmk W4BinaryRecvPrekeyParamsCmk
  W4BinaryRecvPrekeyWideSlotEnvCmkWithP3CAllFixedOf W4FailedTdCancelCmkEnvOf W4FailedTdDomCmkOf
  W4FailedTryDecryptCallCmk W4LoopAdvEnv W4RecvPrekeyRealParamsCmk W4RecvPrekeyTryDecACCmkEnvOf
  W4TrialDecCmkEnv W4TrialDropCmkEnv W4TrialRunWideCmkEnvOf W4TryDecryptCallCmk
  W4TryDecryptCallDomCmkOf W4TryDecryptPathACDomCmkOf w4c_TryDecryptCliLinkedEnvOf
)
open LibsignalBinary.Proofs.PublicApi.MessageDecrypt.DefsBudget (SessionGhostValid)
open LibsignalBinary.Proofs.SessionRecordMin.DeserializeCancelBudgetAux (SessDeserializeCancelEnv)
open LibsignalBinary.Proofs.SignalSession.Cli.D3.Budget.D3NonCanonValidOverPollPlacedBudget (
  CliStageP1OkEnv
)
open LibsignalBinary.Proofs.SignalSession.Cli.D3.F3.H7OverD3SlotDom0EnvSub (
  h7w_p2OverOk_sub_w4StageP2PathCAllFixed h7w_stageP2Over_sub_w4StageP2PathCAllFixed
  h7w_stageP4Prev1Exit_sub_w4StageP4PathCAllFixed
)
open LibsignalBinary.Proofs.SignalSession.Cli.D3.F3.H7OverD3SlotDom0Leaves16 (
  h7w_l1_proved h7w_l6_proved
)
open LibsignalBinary.Proofs.SignalSession.Cli.F3.HRead.ReadFileBudgetPlaced (ReadFileRuleEnvFixed)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Over.PollOverP4ContPlacedBudget (
  cliPollSessPrev1SeqFreeBudgetEnv
)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Over.PollOverPathCPlacedBudgetAux (
  StageP2OverEnv
)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Over.Stage2OverInstPlacedBudget (
  P2OverPathCErrEnvOf P2OverPathCOkEnvOf PromoteOverArchiveCanonSessEnv
)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Over.StagesOverCliPlacedBudget (
  cliPollSelfBudgetEnv
)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.ClosureUntrustedPlacedBudget (
  CliDpPollUntrustedEnv
)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.StagesInst.Stage2V1KitsPlacedBudgetAux (
  cliStageP2KitEnvs
)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.StagesInst.Stage4V1InstPlacedBudget (
  cliPollIdBudgetEnv cliPollKpkBudgetEnv cliPollPkBudgetEnv
)
open LibsignalBinary.Proofs.TripleRatchet.Record.DefsBudget (SegCloneEnv TryDecryptEnvArgs)

/-! ## 1. `Out1Dom`-Parametric Call-Site Domain & `TdTargetEnv`-Parametric Path-C Envelope -/

/-- `Out1Dom`-parametric call-site domain bundle for `W4RecvPrekeyRealParamsCmk` with
`archivedTrials = []`. -/
structure H7wCallSiteDomOut1
    (Out1Dom : SessionGhost → Session (List (BitVec 8)) → List (BitVec 8) → Prop)
    (C : Crypto) (K : MlKem) (maxCt : Nat)
    (peerVal : AddrVal) (files : FsFiles) (R : W4RecvPrekeyRealParamsCmk) : Prop where
  eq_C : R.C = C
  eq_K : R.K = K
  eq_rd : R.rd = cliIo.rd
  eq_files : R.files = files
  eq_peerVal : R.peer.val = peerVal
  kpk_dir : R.kpkDir = StoresGhost.opened.kyber.oneTime ∨
            R.kpkDir = StoresGhost.opened.kyber.lastResort
  ownKey_len : R.ownKeyName.length ≤ 64
  ownReg_len : R.ownRegName.length ≤ 64
  kpkMark_len : R.kpkMarkName.length ≤ 64
  res_old : R.x_res.cap.toNat ≤ 4096
  res_new : reserveCap R.x_res.cap.toNat R.x_res.bs.length R.x_res.additional ≤ 4096
  spqr_key : R.x_spqr.p.authKey.length ≤ 32
  cur_dom : R.hasCurSession = false ∨
    ∃ ses_cur : Session (List (BitVec 8)),
      ses_cur.state = R.st_cur ∧ SessionGhostValid R.G_cur ses_cur ∧
        SessionCloneDom 286196 ses_cur
  arch_valid : ∀ G ses, R.g_arch.cur = some G → R.r_arch.currentSession = some ses →
    SessionGhostValid G ses ∧ SessionCloneDom 286196 ses
  arch_enc : (encodeRecord R.r_arch).length ≤ 2097152
  out0_valid : ∀ G ses, R.g_out0.cur = some G → R.r_out0.currentSession = some ses →
    SessionGhostValid G ses ∧ SessionCloneDom 286196 ses
  out0_enc : (encodeRecord R.r_out0).length ≤ 2097152
  out1_dom : Out1Dom R.G_out1 R.sess_out1 R.enc_prev1
  trials_len4 : R.archivedTrials.length ≤ 4
  cur_fail_dom : R.hasCurSession = true → W4FailedTdDomCmkOf R.C.F R.K maxCt R.fc_cur
  trials_dom : ∀ y ∈ R.archivedTrials, W4ArchivedTrialDomCmkOf R.C.F R.K maxCt y
  tdB_dom : R.isPathB = true → W4TryDecryptCallDomCmkOf R.C.F R.K maxCt R.td_B
  tdAC_dom : R.isPathAC = true → W4TryDecryptPathACDomCmkOf R.C.F R.K maxCt R.td_AC
  archivedTrials_nil : R.archivedTrials = []

theorem H7wCallSiteDomOut1.mono_out1
    {Out1Dom₁ Out1Dom₂ : SessionGhost → Session (List (BitVec 8)) → List (BitVec 8) → Prop}
    {C : Crypto} {K : MlKem} {maxCt : Nat} {peerVal : AddrVal} {files : FsFiles}
    {R : W4RecvPrekeyRealParamsCmk}
    (hSub : ∀ G s e, Out1Dom₁ G s e → Out1Dom₂ G s e)
    (h : H7wCallSiteDomOut1 Out1Dom₁ C K maxCt peerVal files R) :
    H7wCallSiteDomOut1 Out1Dom₂ C K maxCt peerVal files R :=
  { h with out1_dom := hSub R.G_out1 R.sess_out1 R.enc_prev1 h.out1_dom }

theorem H7wCallSiteDomOut1.toCallSiteDomCmk0
    {C : Crypto} {K : MlKem} {maxCt : Nat} {peerVal : AddrVal} {files : FsFiles}
    {R : W4RecvPrekeyRealParamsCmk}
    (h : H7wCallSiteDomOut1 (FreshBobPrev1Dom 16384 2097152 2457152) C K maxCt peerVal files R) :
    W4BinaryCallSiteDomCmk C K maxCt peerVal files R ∧ R.archivedTrials = [] :=
  ⟨⟨h.eq_C, h.eq_K, h.eq_rd, h.eq_files, h.eq_peerVal, h.kpk_dir, h.ownKey_len, h.ownReg_len,
    h.kpkMark_len, h.res_old, h.res_new, h.spqr_key, h.cur_dom, h.arch_valid, h.arch_enc,
    h.out0_valid, h.out0_enc, h.out1_dom, h.trials_len4, h.cur_fail_dom, h.trials_dom,
    h.tdB_dom, h.tdAC_dom⟩, h.archivedTrials_nil⟩

def H7wCurTrialFailEnvOf
    (FailTargetEnv : Crypto → MlKem → W4FailedTryDecryptCallCmk → List AllocEvent → Prop)
    (R : W4RecvPrekeyRealParamsCmk) : List AllocEvent → Prop :=
  if R.hasCurSession then FailTargetEnv R.C R.K R.fc_cur else fun _ => False

def H7wTryDecACEnvOf
    (TdTargetEnv : Crypto → MlKem → TryDecryptEnvArgs → List AllocEvent → Prop)
    (R : W4RecvPrekeyRealParamsCmk) (evs : List AllocEvent) : Prop :=
  if R.isPathAC then TdTargetEnv R.C R.K R.td_AC.a evs else False

/-- `OverD3`-reachable `AllFixed` W4 slot envelope (`Untrusted ∨ Path C` with `VerNeTightTopEnv`),
parametric in `(FailTargetEnv, TrialTargetEnv, TdTargetEnv)`. -/
def H7wOverSlotEnvAllFixedOf
    (FailTargetEnv : Crypto → MlKem → W4FailedTryDecryptCallCmk → List AllocEvent → Prop)
    (TrialTargetEnv : Crypto → MlKem → W4ArchivedTrialCmk → List AllocEvent → Prop)
    (TdTargetEnv : Crypto → MlKem → TryDecryptEnvArgs → List AllocEvent → Prop)
    (w : W4BinaryRecvPrekeyParamsCmk) (evs : List AllocEvent) : Prop :=
  W4BinaryStageP1UntrustedEnvAllFixed w.base.rd w.base.files w.base.peer w.remoteIdKey evs ∨
  SeqEnv (W4BinaryStageP1OkEnvAllFixed w.base.rd w.base.files w.base.peer w.remoteIdKey)
    (SeqEnv
      (OptStageEnv
        (W4BinaryStageP2PathCWideEnvAllFixed w.base.G_cur w.base.st_cur
          (H7wCurTrialFailEnvOf FailTargetEnv w.base)
          W4TrialDecCmkEnv (TrialTargetEnv w.base.C w.base.K) W4TrialDropCmkEnv
          w.base.archivedTrials w.base.g_arch w.base.r_arch
          w.base.hasOpk w.base.rd w.base.files w.base.spkId w.base.kpkId w.base.opkId
          w.base.C.F w.base.x_res w.base.x_spqr))
      (SeqEnv
        (OptStageEnv
          (W4StageP3Prev1WideEnvOf VerNeTightTopEnv W4CloneACDomEnv
            (H7wTryDecACEnvOf TdTargetEnv w.base) w.base.enc_prev1))
        (OptStageEnv
          (W4BinaryStageP4PathCWideEnvAllFixed w.base.hasOpk w.base.rd w.base.files w.base.peer
            w.remoteIdKey w.base.kpkId w.base.spkId w.base.opkId w.baseKey
            w.base.G_out1 w.base.sess_out1 w.base.enc_prev1)))) evs

/-- Embeds `H7wOverSlotEnvAllFixedOf` into any 4-arm outer `AllFixed` slot envelope
(`FreeOnlyEvs ∨ SeqEnv (Untrusted ∨ PathB ∨ PathA ∨ PathC) FreeOnlyEvs`). -/
theorem h7w_overSlotEnv_to_fourArmAllFixed
    {FailTargetEnv : Crypto → MlKem → W4FailedTryDecryptCallCmk → List AllocEvent → Prop}
    {TrialTargetEnv : Crypto → MlKem → W4ArchivedTrialCmk → List AllocEvent → Prop}
    {TdTargetEnv : Crypto → MlKem → TryDecryptEnvArgs → List AllocEvent → Prop}
    (PathBEnv PathAEnv : List AllocEvent → Prop)
    {w : W4BinaryRecvPrekeyParamsCmk} {evs : List AllocEvent}
    (h : H7wOverSlotEnvAllFixedOf FailTargetEnv TrialTargetEnv TdTargetEnv w evs) :
    FreeOnlyEvs evs ∨
    SeqEnv
      (fun e =>
        W4BinaryStageP1UntrustedEnvAllFixed w.base.rd w.base.files w.base.peer w.remoteIdKey e ∨
        PathBEnv e ∨
        PathAEnv e ∨
        SeqEnv (W4BinaryStageP1OkEnvAllFixed w.base.rd w.base.files w.base.peer w.remoteIdKey)
          (SeqEnv
            (OptStageEnv
              (W4BinaryStageP2PathCWideEnvAllFixed w.base.G_cur w.base.st_cur
                (H7wCurTrialFailEnvOf FailTargetEnv w.base)
                W4TrialDecCmkEnv (TrialTargetEnv w.base.C w.base.K) W4TrialDropCmkEnv
                w.base.archivedTrials w.base.g_arch w.base.r_arch
                w.base.hasOpk w.base.rd w.base.files w.base.spkId w.base.kpkId w.base.opkId
                w.base.C.F w.base.x_res w.base.x_spqr))
            (SeqEnv
              (OptStageEnv
                (W4StageP3Prev1WideEnv W4CloneACDomEnv
                  (H7wTryDecACEnvOf TdTargetEnv w.base) w.base.enc_prev1))
              (OptStageEnv
                (W4BinaryStageP4PathCWideEnvAllFixed w.base.hasOpk w.base.rd w.base.files
                  w.base.peer w.remoteIdKey w.base.kpkId w.base.spkId w.base.opkId w.baseKey
                  w.base.G_out1 w.base.sess_out1 w.base.enc_prev1)))) e)
      FreeOnlyEvs evs := by
  rcases h with hunt | hpc
  · exact Or.inr (Or.inl (Or.inl hunt))
  · exact Or.inr (Or.inl (Or.inr (Or.inr (Or.inr hpc))))

theorem h7w_overSlotEnv_sub_wideSlotWithP3CAllFixed
    (LoopAdvEnv : W4LoopAdvEnv) (maxOps : Nat)
    {w : W4BinaryRecvPrekeyParamsCmk} {evs : List AllocEvent}
    (h : H7wOverSlotEnvAllFixedOf
      (W4FailedTdCancelCmkEnvOf LoopAdvEnv maxOps)
      (W4TrialRunWideCmkEnvOf LoopAdvEnv maxOps)
      (w4c_TryDecryptCliLinkedEnvOf LoopAdvEnv maxOps) w evs) :
    W4BinaryRecvPrekeyWideSlotEnvCmkWithP3CAllFixedOf LoopAdvEnv maxOps
      (fun w' => OptStageEnv
        (W4StageP3Prev1WideEnv W4CloneACDomEnv
          (W4RecvPrekeyTryDecACCmkEnvOf LoopAdvEnv maxOps w'.base) w'.base.enc_prev1))
      w evs :=
  h7w_overSlotEnv_to_fourArmAllFixed _ _ h

/-! ## 2. Concrete `OverD3` Stage Envelopes & Witness Builders -/

abbrev H7wP1OkEnv [LibsignalPlacement] (A : RustAlloc) (x : DecPkGhost) :
    List AllocEvent → Prop :=
  CliStageP1OkEnv (A := A) cliRunBudgets (ReadFileRuleEnvFixed cliIo.rd) SessDeserializeCancelEnv x

abbrev H7wP2OverErrEnv [LibsignalPlacement]
    (A : RustAlloc) (X : UnreachedPqxdhPrimitives) (W : CliHooks)
    (x : DecPkGhost) (r : SessionRecord (List (BitVec 8))) : List AllocEvent → Prop :=
  let ReadEnv := ReadFileRuleEnvFixed cliIo.rd
  let selfEnv := fun F0 peer => cliPollSelfBudgetEnv A F0 peer (cliKitStk cliRunBudgets) ReadEnv
  let kitEnvs := cliStageP2KitEnvs (A := A) ReadEnv cliRunBudgets selfEnv
  P2OverPathCErrEnvOf (A := A) X W cliRunBudgets
    (InitializeBobV1OptFieldsEnv (ofSignalPqxdhPrimitives (modelPrims X ⟨W.C, W.Q⟩)) W.C.F)
    (AcceptOptFieldsEnv (ofSignalPqxdhPrimitives (modelPrims X ⟨W.C, W.Q⟩)))
    kitEnvs x r

abbrev H7wP2OverOkEnv [LibsignalPlacement]
    (A : RustAlloc) (X : UnreachedPqxdhPrimitives) (W : CliHooks)
    (x : DecPkGhost) (r : SessionRecord (List (BitVec 8))) : List AllocEvent → Prop :=
  let ReadEnv := ReadFileRuleEnvFixed cliIo.rd
  let selfEnv := fun F0 peer => cliPollSelfBudgetEnv A F0 peer (cliKitStk cliRunBudgets) ReadEnv
  let kitEnvs := cliStageP2KitEnvs (A := A) ReadEnv cliRunBudgets selfEnv
  P2OverPathCOkEnvOf (A := A) X W cliRunBudgets
    (InitializeBobV1OptFieldsEnv (ofSignalPqxdhPrimitives (modelPrims X ⟨W.C, W.Q⟩)) W.C.F)
    PromoteOverArchiveCanonSessEnv
    kitEnvs x r

private theorem e2ar_optStageEnv_nil (E : List AllocEvent → Prop) : OptStageEnv E [] :=
  Or.inl (fun _ h => nomatch h)

private theorem e2ar_chain4_of_p12
    {P1 P2 P3 P4 : List AllocEvent → Prop} {evs : List AllocEvent}
    (h1Sub : ∀ e, P1 e → P1 e)
    (h : SeqEnv P1 P2 evs) :
    SeqEnv P1 (SeqEnv (OptStageEnv P2) (SeqEnv (OptStageEnv P3) (OptStageEnv P4))) evs := by
  rcases h with h1 | ⟨e1, e2, rfl, h1, h2⟩
  · exact Or.inl (h1Sub _ h1)
  · exact Or.inr ⟨e1, e2, rfl, h1Sub _ h1, Or.inl (Or.inr h2)⟩

private theorem e2ar_chain4_of_p123
    {P1 P1' P2 P2' P3 P3' P4' : List AllocEvent → Prop} {evs : List AllocEvent}
    (h1Sub : ∀ e, P1 e → P1' e)
    (h2Sub : ∀ e, P2 e → P2' e)
    (h3Sub : ∀ e, P3 e → P3' e)
    (h : SeqEnv (SeqEnv P1 P2) P3 evs) :
    SeqEnv P1' (SeqEnv (OptStageEnv P2') (SeqEnv (OptStageEnv P3') (OptStageEnv P4'))) evs := by
  rcases h with h12 | ⟨e12, e3, rfl, h12, h3⟩
  · rcases h12 with h1 | ⟨e1, e2, rfl, h1, h2⟩
    · exact Or.inl (h1Sub _ h1)
    · exact Or.inr ⟨e1, e2, rfl, h1Sub _ h1, Or.inl (Or.inr (h2Sub _ h2))⟩
  · rcases h12 with h1 | ⟨e1, e2, rfl, h1, h2⟩
    · exact Or.inr ⟨e12, e3, rfl, h1Sub _ h1,
        Or.inr ⟨[], e3, rfl, e2ar_optStageEnv_nil P2', Or.inl (Or.inr (h3Sub _ h3))⟩⟩
    · exact Or.inr ⟨e1, e2 ++ e3, List.append_assoc e1 e2 e3, h1Sub _ h1,
        Or.inr ⟨e2, e3, rfl, Or.inr (h2Sub _ h2), Or.inl (Or.inr (h3Sub _ h3))⟩⟩

private theorem e2ar_chain4_of_p1234
    {P1 P1' P2 P2' P3 P3' P4 P4' : List AllocEvent → Prop} {evs : List AllocEvent}
    (h1Sub : ∀ e, P1 e → P1' e)
    (h2Sub : ∀ e, P2 e → P2' e)
    (h3Sub : ∀ e, P3 e → P3' e)
    (h4Sub : ∀ e, P4 e → P4' e)
    (h : SeqEnv (SeqEnv (SeqEnv P1 P2) P3) P4 evs) :
    SeqEnv P1' (SeqEnv (OptStageEnv P2') (SeqEnv (OptStageEnv P3') (OptStageEnv P4'))) evs := by
  rcases h with h123 | ⟨e123, e4, rfl, h123, h4⟩
  · exact e2ar_chain4_of_p123 h1Sub h2Sub h3Sub h123
  · rcases h123 with h12 | ⟨e12, e3, rfl, h12, h3⟩
    · rcases h12 with h1 | ⟨e1, e2, rfl, h1, h2⟩
      · exact Or.inr ⟨e123, e4, rfl, h1Sub _ h1,
          Or.inr ⟨[], e4, rfl, e2ar_optStageEnv_nil P2',
            Or.inr ⟨[], e4, rfl, e2ar_optStageEnv_nil P3', Or.inr (h4Sub _ h4)⟩⟩⟩
      · exact Or.inr ⟨e1, e2 ++ e4, List.append_assoc e1 e2 e4, h1Sub _ h1,
          Or.inr ⟨e2, e4, rfl, Or.inr (h2Sub _ h2),
            Or.inr ⟨[], e4, rfl, e2ar_optStageEnv_nil P3', Or.inr (h4Sub _ h4)⟩⟩⟩
    · rcases h12 with h1 | ⟨e1, e2, rfl, h1, h2⟩
      · exact Or.inr ⟨e12, e3 ++ e4, List.append_assoc e12 e3 e4, h1Sub _ h1,
          Or.inr ⟨[], e3 ++ e4, rfl, e2ar_optStageEnv_nil P2',
            Or.inr ⟨e3, e4, rfl, Or.inr (h3Sub _ h3), Or.inr (h4Sub _ h4)⟩⟩⟩
      · have hassoc : ((e1 ++ e2) ++ e3) ++ e4 = e1 ++ (e2 ++ (e3 ++ e4)) := by
          simp only [List.append_assoc]
        exact Or.inr ⟨e1, e2 ++ (e3 ++ e4), hassoc, h1Sub _ h1,
          Or.inr ⟨e2, e3 ++ e4, rfl, Or.inr (h2Sub _ h2),
            Or.inr ⟨e3, e4, rfl, Or.inr (h3Sub _ h3), Or.inr (h4Sub _ h4)⟩⟩⟩

private def e2ar_dummyReserve : DoReserveCall :=
  ⟨0#64, 0#64, 0#64, [], 0⟩

private theorem e2ar_dummyReserve_old : e2ar_dummyReserve.cap.toNat ≤ 4096 := by decide

private theorem e2ar_dummyReserve_new :
    reserveCap e2ar_dummyReserve.cap.toNat e2ar_dummyReserve.bs.length
      e2ar_dummyReserve.additional ≤ 4096 := by
  decide

private def e2ar_dummyInitialStateGhost : InitialStateGhost :=
  ⟨0#64, 0#64, 0#64, { direction := .b2a, version := .v1, minVersion := .v1, authKey := [] }⟩

private theorem e2ar_dummyInitialStateGhost_key :
    e2ar_dummyInitialStateGhost.p.authKey.length ≤ 32 := by
  decide

private def e2ar_noneRecordGhost : RecordGhost :=
  ⟨0#64, 0#64, none⟩

private def e2ar_emptySessionRecord : SessionRecord (List (BitVec 8)) :=
  ⟨none⟩

private theorem e2ar_emptySessionRecord_enc :
    (encodeRecord e2ar_emptySessionRecord).length ≤ 2097152 := by
  decide

private def e2ar_dummyWhisperGhost : SignalMessageGhost :=
  ⟨0#64, 0#64, 0#64, 0#64, 0#64⟩

private def e2ar_dummyTdCall
    (G_d : SessionGhost) (st_d : SessionState (List (BitVec 8))) (x : DecPkGhost) :
    W4TryDecryptCallCmk :=
  ⟨stageP3M3TryDecryptEnvArgs G_d st_d x.peer x.me e2ar_dummyWhisperGhost x.msg.message x.coins⟩

private def e2ar_dummyFailedTdCall
    (G_d : SessionGhost) (st_d : SessionState (List (BitVec 8))) (x : DecPkGhost) :
    W4FailedTryDecryptCallCmk :=
  ⟨e2ar_dummyTdCall G_d st_d x, []⟩

private def e2ar_mkWitnessParams
    (W : CliHooks) (x : DecPkGhost)
    (hasOpk : Bool) (spkId kpkId opkId : BitVec 32)
    (x_spqr : InitialStateGhost)
    (G_cur : SessionGhost) (st_cur : SessionState (List (BitVec 8)))
    (isPathAC : Bool) (td_AC : W4TryDecryptCallCmk)
    (r_arch : SessionRecord (List (BitVec 8)))
    (G_out1 : SessionGhost) (sess_out1 : Session (List (BitVec 8)))
    (enc_prev1 : List (BitVec 8)) : W4BinaryRecvPrekeyParamsCmk where
  base := {
    C := W.C
    K := W.Q.K
    rd := cliIo.rd
    files := x.F
    kpkDir := StoresGhost.opened.kyber.oneTime
    peer := x.peer
    hasOpk := hasOpk
    spkId := spkId
    kpkId := kpkId
    opkId := opkId
    kpkMarkName := []
    ownKeyName := []
    ownRegName := []
    x_res := e2ar_dummyReserve
    x_spqr := x_spqr
    hasCurSession := false
    G_cur := G_cur
    st_cur := st_cur
    fc_cur := e2ar_dummyFailedTdCall G_cur st_cur x
    archivedTrials := []
    isPathB := false
    td_B := e2ar_dummyTdCall G_cur st_cur x
    isPathAC := isPathAC
    td_AC := td_AC
    g_arch := e2ar_noneRecordGhost
    r_arch := r_arch
    g_out0 := e2ar_noneRecordGhost
    r_out0 := e2ar_emptySessionRecord
    G_out1 := G_out1
    sess_out1 := sess_out1
    enc_prev1 := enc_prev1
  }
  remoteIdKey := x.msg.identityKey
  baseKey := x.msg.baseKey

private theorem e2ar_mkWitnessParams_dom
    {Out1Dom : SessionGhost → Session (List (BitVec 8)) → List (BitVec 8) → Prop}
    {maxCt : Nat} (W : CliHooks) (x : DecPkGhost)
    (hasOpk : Bool) (spkId kpkId opkId : BitVec 32)
    (x_spqr : InitialStateGhost)
    (G_cur : SessionGhost) (st_cur : SessionState (List (BitVec 8)))
    (isPathAC : Bool) (td_AC : W4TryDecryptCallCmk)
    (r_arch : SessionRecord (List (BitVec 8)))
    (G_out1 : SessionGhost) (sess_out1 : Session (List (BitVec 8)))
    (enc_prev1 : List (BitVec 8))
    (hSpqrKey : x_spqr.p.authKey.length ≤ 32)
    (hArchEnc : (encodeRecord r_arch).length ≤ 2097152)
    (hOut1 : Out1Dom G_out1 sess_out1 enc_prev1)
    (hTdAC : isPathAC = true → W4TryDecryptPathACDomCmkOf W.C.F W.Q.K maxCt td_AC) :
    H7wCallSiteDomOut1 Out1Dom W.C W.Q.K maxCt x.peer.val x.F
      (e2ar_mkWitnessParams W x hasOpk spkId kpkId opkId x_spqr G_cur st_cur
        isPathAC td_AC r_arch G_out1 sess_out1 enc_prev1).base where
  eq_C := rfl
  eq_K := rfl
  eq_rd := rfl
  eq_files := rfl
  eq_peerVal := rfl
  kpk_dir := Or.inl rfl
  ownKey_len := Nat.zero_le 64
  ownReg_len := Nat.zero_le 64
  kpkMark_len := Nat.zero_le 64
  res_old := e2ar_dummyReserve_old
  res_new := e2ar_dummyReserve_new
  spqr_key := hSpqrKey
  cur_dom := Or.inl rfl
  arch_valid := fun _ _ hg _ => nomatch hg
  arch_enc := hArchEnc
  out0_valid := fun _ _ hg _ => nomatch hg
  out0_enc := e2ar_emptySessionRecord_enc
  out1_dom := hOut1
  trials_len4 := Nat.zero_le 4
  cur_fail_dom := fun h => Bool.noConfusion h
  trials_dom := fun _ hy => nomatch hy
  tdB_dom := fun h => Bool.noConfusion h
  tdAC_dom := hTdAC
  archivedTrials_nil := rfl

private theorem e2ar_tdPathACDom_of_stageP3
    {maxCt : Nat} (W : CliHooks) (x : DecPkGhost)
    (G₁ : SessionGhost) (st0 : SessionState (List (BitVec 8)))
    (whisperG : SignalMessageGhost)
    (hrc_nil : st0.receiverChains = [])
    (htop : TopStateTight W.C.F W.Q.K st0.pqRatchetState)
    (hct : x.msg.message.ciphertext.length ≤ maxCt) :
    W4TryDecryptPathACDomCmkOf W.C.F W.Q.K maxCt
      ⟨stageP3M3TryDecryptEnvArgs G₁ st0 x.peer x.me whisperG x.msg.message x.coins⟩ := by
  refine ⟨⟨?_, ?_, htop, hct⟩, hrc_nil⟩
  · change st0.receiverChains.length ≤ 5
    rw [hrc_nil]
    exact Nat.zero_le 5
  · change ∀ c ∈ st0.receiverChains, c.messageKeys.length ≤ 2000
    rw [hrc_nil]
    intro _ hc
    nomatch hc

/-! ## 3. Per-Arm Witness & Envelope Theorems (Arms 0..6) -/

/-- Untrusted identity-check exit (`CliDpPollUntrustedEnv`) embeds into `H7wOverSlotEnvAllFixedOf`. -/
theorem h7w_witness_untrusted [LibsignalPlacement]
    {Out1Dom : SessionGhost → Session (List (BitVec 8)) → List (BitVec 8) → Prop}
    {FailTargetEnv : Crypto → MlKem → W4FailedTryDecryptCallCmk → List AllocEvent → Prop}
    {TrialTargetEnv : Crypto → MlKem → W4ArchivedTrialCmk → List AllocEvent → Prop}
    {TdTargetEnv : Crypto → MlKem → TryDecryptEnvArgs → List AllocEvent → Prop}
    {maxCt : Nat} (A : RustAlloc) (W : CliHooks) (x : DecPkGhost)
    (G_idle : SessionGhost) (ses_idle : Session (List (BitVec 8)))
    (hOut1 : Out1Dom G_idle ses_idle [])
    {evs : List AllocEvent}
    (h : CliDpPollUntrustedEnv (A := A) cliRunBudgets
      (ReadFileRuleEnvFixed cliIo.rd) SessDeserializeCancelEnv x evs) :
    ∃ w4 : W4BinaryRecvPrekeyParamsCmk,
      H7wCallSiteDomOut1 Out1Dom W.C W.Q.K maxCt x.peer.val x.F w4.base ∧
      w4.remoteIdKey = x.msg.identityKey ∧
      w4.baseKey = x.msg.baseKey ∧
      H7wOverSlotEnvAllFixedOf FailTargetEnv TrialTargetEnv TdTargetEnv w4 evs := by
  refine ⟨e2ar_mkWitnessParams W x false 0#32 0#32 0#32 e2ar_dummyInitialStateGhost
      G_idle ses_idle.state false (e2ar_dummyTdCall G_idle ses_idle.state x)
      e2ar_emptySessionRecord G_idle ses_idle [],
    e2ar_mkWitnessParams_dom W x false 0#32 0#32 0#32 e2ar_dummyInitialStateGhost
      G_idle ses_idle.state false (e2ar_dummyTdCall G_idle ses_idle.state x)
      e2ar_emptySessionRecord G_idle ses_idle []
      e2ar_dummyInitialStateGhost_key e2ar_emptySessionRecord_enc hOut1
      (fun hfalse => Bool.noConfusion hfalse),
    rfl, rfl,
    Or.inl ((h7w_l1_proved A cliRunBudgets x evs).1 h)⟩

/-- Stage-P1 early exit (`CliStageP1OkEnv`) embeds into `H7wOverSlotEnvAllFixedOf`. -/
theorem h7w_witness_p1Ok [LibsignalPlacement]
    {Out1Dom : SessionGhost → Session (List (BitVec 8)) → List (BitVec 8) → Prop}
    {FailTargetEnv : Crypto → MlKem → W4FailedTryDecryptCallCmk → List AllocEvent → Prop}
    {TrialTargetEnv : Crypto → MlKem → W4ArchivedTrialCmk → List AllocEvent → Prop}
    {TdTargetEnv : Crypto → MlKem → TryDecryptEnvArgs → List AllocEvent → Prop}
    {maxCt : Nat} (A : RustAlloc) (W : CliHooks) (x : DecPkGhost)
    (G_idle : SessionGhost) (ses_idle : Session (List (BitVec 8)))
    (hOut1 : Out1Dom G_idle ses_idle [])
    {evs : List AllocEvent}
    (h : H7wP1OkEnv A x evs) :
    ∃ w4 : W4BinaryRecvPrekeyParamsCmk,
      H7wCallSiteDomOut1 Out1Dom W.C W.Q.K maxCt x.peer.val x.F w4.base ∧
      w4.remoteIdKey = x.msg.identityKey ∧
      w4.baseKey = x.msg.baseKey ∧
      H7wOverSlotEnvAllFixedOf FailTargetEnv TrialTargetEnv TdTargetEnv w4 evs := by
  refine ⟨e2ar_mkWitnessParams W x false 0#32 0#32 0#32 e2ar_dummyInitialStateGhost
      G_idle ses_idle.state false (e2ar_dummyTdCall G_idle ses_idle.state x)
      e2ar_emptySessionRecord G_idle ses_idle [],
    e2ar_mkWitnessParams_dom W x false 0#32 0#32 0#32 e2ar_dummyInitialStateGhost
      G_idle ses_idle.state false (e2ar_dummyTdCall G_idle ses_idle.state x)
      e2ar_emptySessionRecord G_idle ses_idle []
      e2ar_dummyInitialStateGhost_key e2ar_emptySessionRecord_enc hOut1
      (fun hfalse => Bool.noConfusion hfalse),
    rfl, rfl,
    Or.inr (Or.inl ((h7w_l1_proved A cliRunBudgets x evs).2 h))⟩

/-- Stage-P2 `Over` exit embeds into `H7wOverSlotEnvAllFixedOf` under
`(encodeRecord ⟨some (clearPending s_old)⟩).length ≤ 2097152`. -/
theorem h7w_witness_p2Over [LibsignalPlacement]
    {Out1Dom : SessionGhost → Session (List (BitVec 8)) → List (BitVec 8) → Prop}
    {FailTargetEnv : Crypto → MlKem → W4FailedTryDecryptCallCmk → List AllocEvent → Prop}
    {TrialTargetEnv : Crypto → MlKem → W4ArchivedTrialCmk → List AllocEvent → Prop}
    {TdTargetEnv : Crypto → MlKem → TryDecryptEnvArgs → List AllocEvent → Prop}
    {maxCt : Nat} (A : RustAlloc) (X : UnreachedPqxdhPrimitives) (W : CliHooks)
    (x : DecPkGhost) (r : SessionRecord (List (BitVec 8))) (s_old : Session (List (BitVec 8)))
    (G_idle : SessionGhost) (ses_idle : Session (List (BitVec 8)))
    (hcur : r.currentSession = some s_old)
    (hCap : (encodeRecord ⟨some (clearPending s_old)⟩).length ≤ 2097152)
    (hOut1 : Out1Dom G_idle ses_idle [])
    {evs : List AllocEvent}
    (h : SeqEnv (H7wP1OkEnv A x)
      (StageP2OverEnv (H7wP2OverErrEnv A X W) (H7wP2OverOkEnv A X W) x r) evs) :
    ∃ w4 : W4BinaryRecvPrekeyParamsCmk,
      H7wCallSiteDomOut1 Out1Dom W.C W.Q.K maxCt x.peer.val x.F w4.base ∧
      w4.remoteIdKey = x.msg.identityKey ∧
      w4.baseKey = x.msg.baseKey ∧
      H7wOverSlotEnvAllFixedOf FailTargetEnv TrialTargetEnv TdTargetEnv w4 evs := by
  rcases h with hp1 | ⟨e1, e2, rfl, hp1, hp2⟩
  · exact h7w_witness_p1Ok A W x G_idle ses_idle hOut1 hp1
  · let r_arch : SessionRecord (List (BitVec 8)) := ⟨some (clearPending s_old)⟩
    obtain ⟨m, x_spqr, _hm, _hver, hlen, hp2W4⟩ :=
      h7w_stageP2Over_sub_w4StageP2PathCAllFixed A X W G_idle ses_idle.state
        (fun _ => False) W4TrialDecCmkEnv (TrialTargetEnv W.C W.Q.K) W4TrialDropCmkEnv
        ([] : List W4ArchivedTrialCmk) e2ar_noneRecordGhost e2ar_dummyReserve
        (r_arch := r_arch) hcur rfl hp2
    refine ⟨e2ar_mkWitnessParams W x m.opkId.isSome m.spkId m.kpkId (m.opkId.getD 0#32)
        x_spqr G_idle ses_idle.state false (e2ar_dummyTdCall G_idle ses_idle.state x)
        r_arch G_idle ses_idle [],
      e2ar_mkWitnessParams_dom W x m.opkId.isSome m.spkId m.kpkId (m.opkId.getD 0#32)
        x_spqr G_idle ses_idle.state false (e2ar_dummyTdCall G_idle ses_idle.state x)
        r_arch G_idle ses_idle []
        hlen hCap hOut1 (fun hfalse => Bool.noConfusion hfalse),
      rfl, rfl,
      Or.inr (Or.inr ⟨e1, e2, rfl, (h7w_l1_proved A cliRunBudgets x e1).2 hp1,
        Or.inl (Or.inr hp2W4)⟩)⟩

/-- Stage-P3 combined `Prev1` arm (`try_decrypt` failure ∨ `VerNeTightTopRawEnv` exit) embeds into `H7wOverSlotEnvAllFixedOf`. -/
theorem h7w_witness_p3Prev1 [LibsignalPlacement]
    {Out1Dom : SessionGhost → Session (List (BitVec 8)) → List (BitVec 8) → Prop}
    {FailTargetEnv : Crypto → MlKem → W4FailedTryDecryptCallCmk → List AllocEvent → Prop}
    {TrialTargetEnv : Crypto → MlKem → W4ArchivedTrialCmk → List AllocEvent → Prop}
    {TdTargetEnv : Crypto → MlKem → TryDecryptEnvArgs → List AllocEvent → Prop}
    {tdEnv : CliHooks → TryDecryptEnvArgs → List AllocEvent → Prop}
    {maxCt : Nat} (A : RustAlloc) (X : UnreachedPqxdhPrimitives) (W : CliHooks)
    (htdSub : ∀ a e,
      TopStateTight W.C.F W.Q.K a.st.pqRatchetState →
      a.msg.ciphertext.length ≤ maxCt →
      tdEnv W a e →
      TdTargetEnv W.C W.Q.K a e)
    (x : DecPkGhost) (r : SessionRecord (List (BitVec 8))) (s_old : Session (List (BitVec 8)))
    (recG : SessionGhost) (ses0 : Session (List (BitVec 8))) (whisperG : SignalMessageGhost)
    (G_out1 : SessionGhost) (sess_out1 : Session (List (BitVec 8)))
    (hcur : r.currentSession = some s_old)
    (hCap : (encodeRecord ⟨some (clearPending s_old)⟩).length ≤ 2097152)
    (hCloneDom : FreshBobCloneDom 16384 recG ses0)
    (htop : TopStateTight W.C.F W.Q.K ses0.state.pqRatchetState)
    (hct : x.msg.message.ciphertext.length ≤ maxCt)
    (hOut1Idle : Out1Dom G_out1 sess_out1 [])
    (hOut1Prev1 : Out1Dom G_out1 sess_out1 (encSession (clearPending s_old)))
    {evs : List AllocEvent}
    (h : SeqEnv (SeqEnv (H7wP1OkEnv A x) (H7wP2OverOkEnv A X W x r))
      (StageP3Prev1Env (tdEnv W) VerNeTightTopRawEnv recG ses0.state x.peer x.me whisperG
        x.msg.message (x.msg.message.messageVersion.zeroExtend 32)
        (encSession (clearPending s_old)) x.coins) evs) :
    ∃ w4 : W4BinaryRecvPrekeyParamsCmk,
      H7wCallSiteDomOut1 Out1Dom W.C W.Q.K maxCt x.peer.val x.F w4.base ∧
      w4.remoteIdKey = x.msg.identityKey ∧
      w4.baseKey = x.msg.baseKey ∧
      H7wOverSlotEnvAllFixedOf FailTargetEnv TrialTargetEnv TdTargetEnv w4 evs := by
  rcases h with h12 | ⟨e12, e3, rfl, h12, hp3⟩
  · exact h7w_witness_p2Over A X W x r s_old G_out1 sess_out1 hcur hCap hOut1Idle
      (match h12 with
       | Or.inl hp1 => Or.inl hp1
       | Or.inr ⟨e1, e2, heq, hp1, hp2⟩ => Or.inr ⟨e1, e2, heq, hp1, Or.inr hp2⟩)
  · have hCapPow : (encodeRecord ⟨some (clearPending s_old)⟩).length ≤ 2 ^ 21 := hCap
    have hL6 := (h7w_l6_proved W tdEnv recG ses0.state x.peer x.me x.msg.message x.coins s_old
      (CloneEnv := W4CloneACDomEnv) (fun _ hcl => ⟨recG, ses0, hCloneDom, hcl⟩)).2.2
      hCapPow whisperG (x.msg.message.messageVersion.zeroExtend 32) e3 hp3
    let r_arch : SessionRecord (List (BitVec 8)) := ⟨some (clearPending s_old)⟩
    let enc_prev1 := encSession (clearPending s_old)
    rcases h12 with hp1 | ⟨e1, e2, rfl, hp1, hp2⟩
    · rcases hL6 with ⟨G₁, _hcl, hp3Sub⟩ | hp3VerNe
      · let tdCall : W4TryDecryptCallCmk :=
          ⟨stageP3M3TryDecryptEnvArgs G₁ ses0.state x.peer x.me whisperG x.msg.message x.coins⟩
        have hp3W4 := hp3Sub (TryDecEnv := TdTargetEnv W.C W.Q.K tdCall.a)
          (fun _ htd => htdSub tdCall.a _ htop hct htd)
        refine ⟨e2ar_mkWitnessParams W x false 0#32 0#32 0#32 e2ar_dummyInitialStateGhost
            recG ses0.state true tdCall r_arch G_out1 sess_out1 enc_prev1,
          e2ar_mkWitnessParams_dom W x false 0#32 0#32 0#32 e2ar_dummyInitialStateGhost
            recG ses0.state true tdCall r_arch G_out1 sess_out1 enc_prev1
            e2ar_dummyInitialStateGhost_key hCap hOut1Prev1
            (fun _ => e2ar_tdPathACDom_of_stageP3 W x G₁ ses0.state whisperG
              hCloneDom.rc_nil htop hct),
          rfl, rfl,
          Or.inr (Or.inr ⟨e12, e3, rfl, (h7w_l1_proved A cliRunBudgets x e12).2 hp1,
            Or.inr ⟨[], e3, rfl, e2ar_optStageEnv_nil _, Or.inl (Or.inr hp3W4)⟩⟩)⟩
      · let tdCall := e2ar_dummyTdCall recG ses0.state x
        refine ⟨e2ar_mkWitnessParams W x false 0#32 0#32 0#32 e2ar_dummyInitialStateGhost
            recG ses0.state false tdCall r_arch G_out1 sess_out1 enc_prev1,
          e2ar_mkWitnessParams_dom W x false 0#32 0#32 0#32 e2ar_dummyInitialStateGhost
            recG ses0.state false tdCall r_arch G_out1 sess_out1 enc_prev1
            e2ar_dummyInitialStateGhost_key hCap hOut1Prev1 (fun hf => Bool.noConfusion hf),
          rfl, rfl,
          Or.inr (Or.inr ⟨e12, e3, rfl, (h7w_l1_proved A cliRunBudgets x e12).2 hp1,
            Or.inr ⟨[], e3, rfl, e2ar_optStageEnv_nil _, Or.inl (Or.inr (hp3VerNe _))⟩⟩)⟩
    · obtain ⟨m, sess, x_spqr, _hm, hsess, _hver, hlen, hp2Sub⟩ :=
        h7w_p2OverOk_sub_w4StageP2PathCAllFixed A X W recG ses0.state
          (fun _ => False) W4TrialDecCmkEnv (TrialTargetEnv W.C W.Q.K) W4TrialDropCmkEnv
          ([] : List W4ArchivedTrialCmk) e2ar_noneRecordGhost e2ar_dummyReserve hp2
      have hse : sess = s_old := Option.some.inj (hsess.symm.trans hcur)
      subst hse
      have hp2W4 := hp2Sub r_arch rfl
      rcases hL6 with ⟨G₁, _hcl, hp3Sub⟩ | hp3VerNe
      · let tdCall : W4TryDecryptCallCmk :=
          ⟨stageP3M3TryDecryptEnvArgs G₁ ses0.state x.peer x.me whisperG x.msg.message x.coins⟩
        have hp3W4 := hp3Sub (TryDecEnv := TdTargetEnv W.C W.Q.K tdCall.a)
          (fun _ htd => htdSub tdCall.a _ htop hct htd)
        refine ⟨e2ar_mkWitnessParams W x m.opkId.isSome m.spkId m.kpkId (m.opkId.getD 0#32)
            x_spqr recG ses0.state true tdCall r_arch G_out1 sess_out1 enc_prev1,
          e2ar_mkWitnessParams_dom W x m.opkId.isSome m.spkId m.kpkId (m.opkId.getD 0#32)
            x_spqr recG ses0.state true tdCall r_arch G_out1 sess_out1 enc_prev1
            hlen hCap hOut1Prev1
            (fun _ => e2ar_tdPathACDom_of_stageP3 W x G₁ ses0.state whisperG
              hCloneDom.rc_nil htop hct),
          rfl, rfl,
          Or.inr (Or.inr ⟨e1, e2 ++ e3, List.append_assoc e1 e2 e3,
            (h7w_l1_proved A cliRunBudgets x e1).2 hp1,
            Or.inr ⟨e2, e3, rfl, Or.inr hp2W4, Or.inl (Or.inr hp3W4)⟩⟩)⟩
      · let tdCall := e2ar_dummyTdCall recG ses0.state x
        refine ⟨e2ar_mkWitnessParams W x m.opkId.isSome m.spkId m.kpkId (m.opkId.getD 0#32)
            x_spqr recG ses0.state false tdCall r_arch G_out1 sess_out1 enc_prev1,
          e2ar_mkWitnessParams_dom W x m.opkId.isSome m.spkId m.kpkId (m.opkId.getD 0#32)
            x_spqr recG ses0.state false tdCall r_arch G_out1 sess_out1 enc_prev1
            hlen hCap hOut1Prev1 (fun hf => Bool.noConfusion hf),
          rfl, rfl,
          Or.inr (Or.inr ⟨e1, e2 ++ e3, List.append_assoc e1 e2 e3,
            (h7w_l1_proved A cliRunBudgets x e1).2 hp1,
            Or.inr ⟨e2, e3, rfl, Or.inr hp2W4, Or.inl (Or.inr (hp3VerNe _))⟩⟩)⟩

/-- Stage-P3 `M3` `try_decrypt` error exit embeds into `H7wOverSlotEnvAllFixedOf`. -/
theorem h7w_witness_p3ErrM3 [LibsignalPlacement]
    {Out1Dom : SessionGhost → Session (List (BitVec 8)) → List (BitVec 8) → Prop}
    {FailTargetEnv : Crypto → MlKem → W4FailedTryDecryptCallCmk → List AllocEvent → Prop}
    {TrialTargetEnv : Crypto → MlKem → W4ArchivedTrialCmk → List AllocEvent → Prop}
    {TdTargetEnv : Crypto → MlKem → TryDecryptEnvArgs → List AllocEvent → Prop}
    {tdEnv : CliHooks → TryDecryptEnvArgs → List AllocEvent → Prop}
    {maxCt : Nat} (A : RustAlloc) (X : UnreachedPqxdhPrimitives) (W : CliHooks)
    (htdSub : ∀ a e,
      TopStateTight W.C.F W.Q.K a.st.pqRatchetState →
      a.msg.ciphertext.length ≤ maxCt →
      tdEnv W a e →
      TdTargetEnv W.C W.Q.K a e)
    (x : DecPkGhost) (r : SessionRecord (List (BitVec 8))) (s_old : Session (List (BitVec 8)))
    (recG G₁ : SessionGhost) (ses0 : Session (List (BitVec 8))) (whisperG : SignalMessageGhost)
    (G_out1 : SessionGhost) (sess_out1 : Session (List (BitVec 8)))
    (hcur : r.currentSession = some s_old)
    (hCap : (encodeRecord ⟨some (clearPending s_old)⟩).length ≤ 2097152)
    (hCloneDom : FreshBobCloneDom 16384 recG ses0)
    (htop : TopStateTight W.C.F W.Q.K ses0.state.pqRatchetState)
    (hct : x.msg.message.ciphertext.length ≤ maxCt)
    (hOut1Idle : Out1Dom G_out1 sess_out1 [])
    (hOut1Prev1 : Out1Dom G_out1 sess_out1 (encSession (clearPending s_old)))
    {evs : List AllocEvent}
    (h : SeqEnv (SeqEnv (H7wP1OkEnv A x) (H7wP2OverOkEnv A X W x r))
      (StageP3ErrM3Env (tdEnv W) recG G₁ ses0.state x.peer x.me whisperG
        x.msg.message x.coins) evs) :
    ∃ w4 : W4BinaryRecvPrekeyParamsCmk,
      H7wCallSiteDomOut1 Out1Dom W.C W.Q.K maxCt x.peer.val x.F w4.base ∧
      w4.remoteIdKey = x.msg.identityKey ∧
      w4.baseKey = x.msg.baseKey ∧
      H7wOverSlotEnvAllFixedOf FailTargetEnv TrialTargetEnv TdTargetEnv w4 evs := by
  rcases h with h12 | ⟨e12, e3, rfl, h12, hp3⟩
  · exact h7w_witness_p2Over A X W x r s_old G_out1 sess_out1 hcur hCap hOut1Idle
      (match h12 with
       | Or.inl hp1 => Or.inl hp1
       | Or.inr ⟨e1, e2, heq, hp1, hp2⟩ => Or.inr ⟨e1, e2, heq, hp1, Or.inr hp2⟩)
  · let tdCall : W4TryDecryptCallCmk :=
      ⟨stageP3M3TryDecryptEnvArgs G₁ ses0.state x.peer x.me whisperG x.msg.message x.coins⟩
    let r_arch : SessionRecord (List (BitVec 8)) := ⟨some (clearPending s_old)⟩
    let enc_prev1 := encSession (clearPending s_old)
    have hp3W4 := (h7w_l6_proved W tdEnv recG ses0.state x.peer x.me x.msg.message x.coins s_old
      (CloneEnv := W4CloneACDomEnv) (fun _ hcl => ⟨recG, ses0, hCloneDom, hcl⟩)).1
      G₁ whisperG (TryDecEnv := TdTargetEnv W.C W.Q.K tdCall.a)
      (fun _ htd => htdSub tdCall.a _ htop hct htd) e3 (Or.inl hp3)
    rcases h12 with hp1 | ⟨e1, e2, rfl, hp1, hp2⟩
    · refine ⟨e2ar_mkWitnessParams W x false 0#32 0#32 0#32 e2ar_dummyInitialStateGhost
          recG ses0.state true tdCall r_arch G_out1 sess_out1 enc_prev1,
        e2ar_mkWitnessParams_dom W x false 0#32 0#32 0#32 e2ar_dummyInitialStateGhost
          recG ses0.state true tdCall r_arch G_out1 sess_out1 enc_prev1
          e2ar_dummyInitialStateGhost_key hCap hOut1Prev1
          (fun _ => e2ar_tdPathACDom_of_stageP3 W x G₁ ses0.state whisperG
            hCloneDom.rc_nil htop hct),
        rfl, rfl,
        Or.inr (Or.inr ⟨e12, e3, rfl, (h7w_l1_proved A cliRunBudgets x e12).2 hp1,
          Or.inr ⟨[], e3, rfl, e2ar_optStageEnv_nil _, Or.inl (Or.inr hp3W4)⟩⟩)⟩
    · obtain ⟨m, sess, x_spqr, _hm, hsess, _hver, hlen, hp2Sub⟩ :=
        h7w_p2OverOk_sub_w4StageP2PathCAllFixed A X W recG ses0.state
          (fun _ => False) W4TrialDecCmkEnv (TrialTargetEnv W.C W.Q.K) W4TrialDropCmkEnv
          ([] : List W4ArchivedTrialCmk) e2ar_noneRecordGhost e2ar_dummyReserve hp2
      have hse : sess = s_old := Option.some.inj (hsess.symm.trans hcur)
      subst hse
      refine ⟨e2ar_mkWitnessParams W x m.opkId.isSome m.spkId m.kpkId (m.opkId.getD 0#32)
          x_spqr recG ses0.state true tdCall r_arch G_out1 sess_out1 enc_prev1,
        e2ar_mkWitnessParams_dom W x m.opkId.isSome m.spkId m.kpkId (m.opkId.getD 0#32)
          x_spqr recG ses0.state true tdCall r_arch G_out1 sess_out1 enc_prev1
          hlen hCap hOut1Prev1
          (fun _ => e2ar_tdPathACDom_of_stageP3 W x G₁ ses0.state whisperG
            hCloneDom.rc_nil htop hct),
        rfl, rfl,
        Or.inr (Or.inr ⟨e1, e2 ++ e3, List.append_assoc e1 e2 e3,
          (h7w_l1_proved A cliRunBudgets x e1).2 hp1,
          Or.inr ⟨e2, e3, rfl, Or.inr (hp2Sub r_arch rfl), Or.inl (Or.inr hp3W4)⟩⟩)⟩

/-- Stage-P3 `VerNe` exit upgrades `VerNeTightTopRawEnv` under the `2 MiB` `clearPending` cap and embeds into `H7wOverSlotEnvAllFixedOf`. -/
theorem h7w_witness_p3VerNe [LibsignalPlacement]
    {Out1Dom : SessionGhost → Session (List (BitVec 8)) → List (BitVec 8) → Prop}
    {FailTargetEnv : Crypto → MlKem → W4FailedTryDecryptCallCmk → List AllocEvent → Prop}
    {TrialTargetEnv : Crypto → MlKem → W4ArchivedTrialCmk → List AllocEvent → Prop}
    {TdTargetEnv : Crypto → MlKem → TryDecryptEnvArgs → List AllocEvent → Prop}
    {tdEnv : CliHooks → TryDecryptEnvArgs → List AllocEvent → Prop}
    {maxCt : Nat} (A : RustAlloc) (X : UnreachedPqxdhPrimitives) (W : CliHooks)
    (x : DecPkGhost) (r : SessionRecord (List (BitVec 8))) (s_old : Session (List (BitVec 8)))
    (recG : SessionGhost) (ses0 : Session (List (BitVec 8)))
    (G_out1 : SessionGhost) (sess_out1 : Session (List (BitVec 8)))
    (hcur : r.currentSession = some s_old)
    (hCap : (encodeRecord ⟨some (clearPending s_old)⟩).length ≤ 2097152)
    (hCloneDom : FreshBobCloneDom 16384 recG ses0)
    (hOut1Idle : Out1Dom G_out1 sess_out1 [])
    (hOut1Prev1 : Out1Dom G_out1 sess_out1 (encSession (clearPending s_old)))
    {evs : List AllocEvent}
    (h : SeqEnv (SeqEnv (H7wP1OkEnv A x) (H7wP2OverOkEnv A X W x r))
      (StageP3VerNePrev1Env VerNeTightTopRawEnv recG ses0.state
        (encSession (clearPending s_old))) evs) :
    ∃ w4 : W4BinaryRecvPrekeyParamsCmk,
      H7wCallSiteDomOut1 Out1Dom W.C W.Q.K maxCt x.peer.val x.F w4.base ∧
      w4.remoteIdKey = x.msg.identityKey ∧
      w4.baseKey = x.msg.baseKey ∧
      H7wOverSlotEnvAllFixedOf FailTargetEnv TrialTargetEnv TdTargetEnv w4 evs := by
  rcases h with h12 | ⟨e12, e3, rfl, h12, hp3⟩
  · exact h7w_witness_p2Over A X W x r s_old G_out1 sess_out1 hcur hCap hOut1Idle
      (match h12 with
       | Or.inl hp1 => Or.inl hp1
       | Or.inr ⟨e1, e2, heq, hp1, hp2⟩ => Or.inr ⟨e1, e2, heq, hp1, Or.inr hp2⟩)
  · have hCapPow : (encodeRecord ⟨some (clearPending s_old)⟩).length ≤ 2 ^ 21 := hCap
    let tdCall := e2ar_dummyTdCall recG ses0.state x
    let r_arch : SessionRecord (List (BitVec 8)) := ⟨some (clearPending s_old)⟩
    let enc_prev1 := encSession (clearPending s_old)
    have hp3W4 := (h7w_l6_proved W tdEnv recG ses0.state x.peer x.me x.msg.message x.coins s_old
      (CloneEnv := W4CloneACDomEnv) (fun _ hcl => ⟨recG, ses0, hCloneDom, hcl⟩)).2.1
      hCapPow (fun _ => False) e3 hp3
    rcases h12 with hp1 | ⟨e1, e2, rfl, hp1, hp2⟩
    · refine ⟨e2ar_mkWitnessParams W x false 0#32 0#32 0#32 e2ar_dummyInitialStateGhost
          recG ses0.state false tdCall r_arch G_out1 sess_out1 enc_prev1,
        e2ar_mkWitnessParams_dom W x false 0#32 0#32 0#32 e2ar_dummyInitialStateGhost
          recG ses0.state false tdCall r_arch G_out1 sess_out1 enc_prev1
          e2ar_dummyInitialStateGhost_key hCap hOut1Prev1 (fun hf => Bool.noConfusion hf),
        rfl, rfl,
        Or.inr (Or.inr ⟨e12, e3, rfl, (h7w_l1_proved A cliRunBudgets x e12).2 hp1,
          Or.inr ⟨[], e3, rfl, e2ar_optStageEnv_nil _, Or.inl (Or.inr hp3W4)⟩⟩)⟩
    · obtain ⟨m, sess, x_spqr, _hm, hsess, _hver, hlen, hp2Sub⟩ :=
        h7w_p2OverOk_sub_w4StageP2PathCAllFixed A X W recG ses0.state
          (fun _ => False) W4TrialDecCmkEnv (TrialTargetEnv W.C W.Q.K) W4TrialDropCmkEnv
          ([] : List W4ArchivedTrialCmk) e2ar_noneRecordGhost e2ar_dummyReserve hp2
      have hse : sess = s_old := Option.some.inj (hsess.symm.trans hcur)
      subst hse
      refine ⟨e2ar_mkWitnessParams W x m.opkId.isSome m.spkId m.kpkId (m.opkId.getD 0#32)
          x_spqr recG ses0.state false tdCall r_arch G_out1 sess_out1 enc_prev1,
        e2ar_mkWitnessParams_dom W x m.opkId.isSome m.spkId m.kpkId (m.opkId.getD 0#32)
          x_spqr recG ses0.state false tdCall r_arch G_out1 sess_out1 enc_prev1
          hlen hCap hOut1Prev1 (fun hf => Bool.noConfusion hf),
        rfl, rfl,
        Or.inr (Or.inr ⟨e1, e2 ++ e3, List.append_assoc e1 e2 e3,
          (h7w_l1_proved A cliRunBudgets x e1).2 hp1,
          Or.inr ⟨e2, e3, rfl, Or.inr (hp2Sub r_arch rfl), Or.inl (Or.inr hp3W4)⟩⟩)⟩

/-- Full 4-stage `OverD3` `Ok pt` continuation embeds into `H7wOverSlotEnvAllFixedOf`. -/
theorem h7w_witness_p4Prev1Exit [LibsignalPlacement]
    {Out1Dom : SessionGhost → Session (List (BitVec 8)) → List (BitVec 8) → Prop}
    {FailTargetEnv : Crypto → MlKem → W4FailedTryDecryptCallCmk → List AllocEvent → Prop}
    {TrialTargetEnv : Crypto → MlKem → W4ArchivedTrialCmk → List AllocEvent → Prop}
    {TdTargetEnv : Crypto → MlKem → TryDecryptEnvArgs → List AllocEvent → Prop}
    {tdEnv : CliHooks → TryDecryptEnvArgs → List AllocEvent → Prop}
    {pid₀ kpkId₀ spkId₀ : BitVec 32} {kbk₀ : PublicKey}
    {maxCt : Nat} (A : RustAlloc) (X : UnreachedPqxdhPrimitives) (W : CliHooks)
    (htdSub : ∀ a e,
      TopStateTight W.C.F W.Q.K a.st.pqRatchetState →
      a.msg.ciphertext.length ≤ maxCt →
      tdEnv W a e →
      TdTargetEnv W.C W.Q.K a e)
    (x : DecPkGhost) (r : SessionRecord (List (BitVec 8))) (s_old : Session (List (BitVec 8)))
    (m : PreKeyMessageFields)
    (recG G₁ G' : SessionGhost) (ses0 ses' : Session (List (BitVec 8)))
    (whisperG : SignalMessageGhost)
    (hcur : r.currentSession = some s_old)
    (hm_arm : pkToE? x.msg = some m)
    (hCap : (encodeRecord ⟨some (clearPending s_old)⟩).length ≤ 2097152)
    (hCloneDom : FreshBobCloneDom 16384 recG ses0)
    (htop : TopStateTight W.C.F W.Q.K ses0.state.pqRatchetState)
    (hct : x.msg.message.ciphertext.length ≤ maxCt)
    (hOut1Post : Out1Dom G' ses' (encSession (clearPending s_old)))
    {evs : List AllocEvent}
    (h :
      let ReadEnv := ReadFileRuleEnvFixed cliIo.rd
      let σ := cliKitStk cliRunBudgets
      SeqEnv
        (SeqEnv (SeqEnv (H7wP1OkEnv A x) (H7wP2OverOkEnv A X W x r))
          (StageP3OkPrefixM3Env (tdEnv W) recG G₁ ses0.state x.peer x.me whisperG
            x.msg.message x.coins))
        (StageP4Prev1ExitEnv
          (cliPollSessPrev1KitPlaced A x.F x.peer σ)
          (cliPollSessPrev1SeqFreeBudgetEnv A x.F x.peer σ)
          (cliPollIdKitPlaced A x.F x.peer σ)
          (cliPollIdBudgetEnv A x.F x.peer σ ReadEnv)
          (cliPollPkKitPlaced A x.F pid₀ σ)
          (cliPollPkBudgetEnv A x.F pid₀ σ ReadEnv)
          (cliPollKpkKitPlaced A x.F kpkId₀ spkId₀ kbk₀ σ)
          (cliPollKpkBudgetEnv A x.F kpkId₀ spkId₀ kbk₀ σ ReadEnv)
          StoresGhost.opened.sessions StoresGhost.opened.identity
          StoresGhost.opened.oneTime StoresGhost.opened.kyber
          m.opkId x.peer.val x.msg.identityKey m.kpkId m.spkId x.msg.baseKey
          G' ses' (encSession (clearPending s_old))) evs) :
    ∃ w4 : W4BinaryRecvPrekeyParamsCmk,
      H7wCallSiteDomOut1 Out1Dom W.C W.Q.K maxCt x.peer.val x.F w4.base ∧
      w4.remoteIdKey = x.msg.identityKey ∧
      w4.baseKey = x.msg.baseKey ∧
      H7wOverSlotEnvAllFixedOf FailTargetEnv TrialTargetEnv TdTargetEnv w4 evs := by
  dsimp only [] at h
  let tdCall : W4TryDecryptCallCmk :=
    ⟨stageP3M3TryDecryptEnvArgs G₁ ses0.state x.peer x.me whisperG x.msg.message x.coins⟩
  let r_arch : SessionRecord (List (BitVec 8)) := ⟨some (clearPending s_old)⟩
  let enc_prev1 := encSession (clearPending s_old)
  have hp1Sub : ∀ e, H7wP1OkEnv A x e →
      W4BinaryStageP1OkEnvAllFixed cliIo.rd x.F x.peer x.msg.identityKey e :=
    fun e he => (h7w_l1_proved A cliRunBudgets x e).2 he
  have hp3Sub : ∀ e,
      StageP3OkPrefixM3Env (tdEnv W) recG G₁ ses0.state x.peer x.me whisperG
        x.msg.message x.coins e →
      W4StageP3Prev1WideEnvOf VerNeTightTopEnv W4CloneACDomEnv
        (TdTargetEnv W.C W.Q.K tdCall.a) enc_prev1 e :=
    fun e he =>
      (h7w_l6_proved W tdEnv recG ses0.state x.peer x.me x.msg.message x.coins s_old
        (CloneEnv := W4CloneACDomEnv) (fun _ hcl => ⟨recG, ses0, hCloneDom, hcl⟩)).1
        G₁ whisperG (TryDecEnv := TdTargetEnv W.C W.Q.K tdCall.a)
        (fun _ htd => htdSub tdCall.a _ htop hct htd) e (Or.inr he)
  have hp4Sub : ∀ e,
      StageP4Prev1ExitEnv
        (cliPollSessPrev1KitPlaced A x.F x.peer (cliKitStk cliRunBudgets))
        (cliPollSessPrev1SeqFreeBudgetEnv A x.F x.peer (cliKitStk cliRunBudgets))
        (cliPollIdKitPlaced A x.F x.peer (cliKitStk cliRunBudgets))
        (cliPollIdBudgetEnv A x.F x.peer (cliKitStk cliRunBudgets) (ReadFileRuleEnvFixed cliIo.rd))
        (cliPollPkKitPlaced A x.F pid₀ (cliKitStk cliRunBudgets))
        (cliPollPkBudgetEnv A x.F pid₀ (cliKitStk cliRunBudgets) (ReadFileRuleEnvFixed cliIo.rd))
        (cliPollKpkKitPlaced A x.F kpkId₀ spkId₀ kbk₀ (cliKitStk cliRunBudgets))
        (cliPollKpkBudgetEnv A x.F kpkId₀ spkId₀ kbk₀ (cliKitStk cliRunBudgets)
          (ReadFileRuleEnvFixed cliIo.rd))
        StoresGhost.opened.sessions StoresGhost.opened.identity
        StoresGhost.opened.oneTime StoresGhost.opened.kyber
        m.opkId x.peer.val x.msg.identityKey m.kpkId m.spkId x.msg.baseKey
        G' ses' enc_prev1 e →
      W4BinaryStageP4PathCWideEnvAllFixed m.opkId.isSome cliIo.rd x.F x.peer x.msg.identityKey
        m.kpkId m.spkId (m.opkId.getD 0#32) x.msg.baseKey G' ses' enc_prev1 e :=
    fun _ he => h7w_stageP4Prev1Exit_sub_w4StageP4PathCAllFixed A cliRunBudgets he
  have hTdDom : W4TryDecryptPathACDomCmkOf W.C.F W.Q.K maxCt tdCall :=
    e2ar_tdPathACDom_of_stageP3 W x G₁ ses0.state whisperG hCloneDom.rc_nil htop hct
  have hP2Case :
      (∃ x_spqr : InitialStateGhost,
        x_spqr.p.authKey.length ≤ 32 ∧
        SeqEnv (W4BinaryStageP1OkEnvAllFixed cliIo.rd x.F x.peer x.msg.identityKey)
          (SeqEnv
            (OptStageEnv
              (W4BinaryStageP2PathCWideEnvAllFixed recG ses0.state (fun _ => False)
                W4TrialDecCmkEnv (TrialTargetEnv W.C W.Q.K) W4TrialDropCmkEnv
                ([] : List W4ArchivedTrialCmk) e2ar_noneRecordGhost r_arch
                m.opkId.isSome cliIo.rd x.F m.spkId m.kpkId (m.opkId.getD 0#32)
                W.C.F e2ar_dummyReserve x_spqr))
            (SeqEnv
              (OptStageEnv
                (W4StageP3Prev1WideEnvOf VerNeTightTopEnv W4CloneACDomEnv
                  (TdTargetEnv W.C W.Q.K tdCall.a) enc_prev1))
              (OptStageEnv
                (W4BinaryStageP4PathCWideEnvAllFixed m.opkId.isSome cliIo.rd x.F x.peer
                  x.msg.identityKey m.kpkId m.spkId (m.opkId.getD 0#32) x.msg.baseKey
                  G' ses' enc_prev1)))) evs) := by
    rcases h with h123 | ⟨e123, e4, rfl, h123, hp4⟩
    · rcases h123 with h12 | ⟨e12, e3, rfl, h12, hp3⟩
      · rcases h12 with hp1 | ⟨e1, e2, rfl, hp1, hp2⟩
        · exact ⟨e2ar_dummyInitialStateGhost, e2ar_dummyInitialStateGhost_key,
            Or.inl (hp1Sub _ hp1)⟩
        · obtain ⟨m₂, sess, x_spqr, hm₂, hsess, _hver, hlen, hp2f⟩ :=
            h7w_p2OverOk_sub_w4StageP2PathCAllFixed A X W recG ses0.state
              (fun _ => False) W4TrialDecCmkEnv (TrialTargetEnv W.C W.Q.K) W4TrialDropCmkEnv
              ([] : List W4ArchivedTrialCmk) e2ar_noneRecordGhost e2ar_dummyReserve hp2
          cases Option.some.inj (hm₂.symm.trans hm_arm)
          cases Option.some.inj (hsess.symm.trans hcur)
          exact ⟨x_spqr, hlen, Or.inr ⟨e1, e2, rfl, hp1Sub _ hp1, Or.inl (Or.inr (hp2f r_arch rfl))⟩⟩
      · rcases h12 with hp1 | ⟨e1, e2, rfl, hp1, hp2⟩
        · exact ⟨e2ar_dummyInitialStateGhost, e2ar_dummyInitialStateGhost_key,
            Or.inr ⟨e12, e3, rfl, hp1Sub _ hp1,
              Or.inr ⟨[], e3, rfl, e2ar_optStageEnv_nil _, Or.inl (Or.inr (hp3Sub _ hp3))⟩⟩⟩
        · obtain ⟨m₂, sess, x_spqr, hm₂, hsess, _hver, hlen, hp2f⟩ :=
            h7w_p2OverOk_sub_w4StageP2PathCAllFixed A X W recG ses0.state
              (fun _ => False) W4TrialDecCmkEnv (TrialTargetEnv W.C W.Q.K) W4TrialDropCmkEnv
              ([] : List W4ArchivedTrialCmk) e2ar_noneRecordGhost e2ar_dummyReserve hp2
          cases Option.some.inj (hm₂.symm.trans hm_arm)
          cases Option.some.inj (hsess.symm.trans hcur)
          exact ⟨x_spqr, hlen, Or.inr ⟨e1, e2 ++ e3, List.append_assoc e1 e2 e3, hp1Sub _ hp1,
            Or.inr ⟨e2, e3, rfl, Or.inr (hp2f r_arch rfl), Or.inl (Or.inr (hp3Sub _ hp3))⟩⟩⟩
    · rcases h123 with h12 | ⟨e12, e3, rfl, h12, hp3⟩
      · rcases h12 with hp1 | ⟨e1, e2, rfl, hp1, hp2⟩
        · exact ⟨e2ar_dummyInitialStateGhost, e2ar_dummyInitialStateGhost_key,
            Or.inr ⟨e123, e4, rfl, hp1Sub _ hp1,
              Or.inr ⟨[], e4, rfl, e2ar_optStageEnv_nil _,
                Or.inr ⟨[], e4, rfl, e2ar_optStageEnv_nil _, Or.inr (hp4Sub _ hp4)⟩⟩⟩⟩
        · obtain ⟨m₂, sess, x_spqr, hm₂, hsess, _hver, hlen, hp2f⟩ :=
            h7w_p2OverOk_sub_w4StageP2PathCAllFixed A X W recG ses0.state
              (fun _ => False) W4TrialDecCmkEnv (TrialTargetEnv W.C W.Q.K) W4TrialDropCmkEnv
              ([] : List W4ArchivedTrialCmk) e2ar_noneRecordGhost e2ar_dummyReserve hp2
          cases Option.some.inj (hm₂.symm.trans hm_arm)
          cases Option.some.inj (hsess.symm.trans hcur)
          exact ⟨x_spqr, hlen, Or.inr ⟨e1, e2 ++ e4, List.append_assoc e1 e2 e4, hp1Sub _ hp1,
            Or.inr ⟨e2, e4, rfl, Or.inr (hp2f r_arch rfl),
              Or.inr ⟨[], e4, rfl, e2ar_optStageEnv_nil _, Or.inr (hp4Sub _ hp4)⟩⟩⟩⟩
      · rcases h12 with hp1 | ⟨e1, e2, rfl, hp1, hp2⟩
        · exact ⟨e2ar_dummyInitialStateGhost, e2ar_dummyInitialStateGhost_key,
            Or.inr ⟨e12, e3 ++ e4, List.append_assoc e12 e3 e4, hp1Sub _ hp1,
              Or.inr ⟨[], e3 ++ e4, rfl, e2ar_optStageEnv_nil _,
                Or.inr ⟨e3, e4, rfl, Or.inr (hp3Sub _ hp3), Or.inr (hp4Sub _ hp4)⟩⟩⟩⟩
        · obtain ⟨m₂, sess, x_spqr, hm₂, hsess, _hver, hlen, hp2f⟩ :=
            h7w_p2OverOk_sub_w4StageP2PathCAllFixed A X W recG ses0.state
              (fun _ => False) W4TrialDecCmkEnv (TrialTargetEnv W.C W.Q.K) W4TrialDropCmkEnv
              ([] : List W4ArchivedTrialCmk) e2ar_noneRecordGhost e2ar_dummyReserve hp2
          cases Option.some.inj (hm₂.symm.trans hm_arm)
          cases Option.some.inj (hsess.symm.trans hcur)
          have hassoc : ((e1 ++ e2) ++ e3) ++ e4 = e1 ++ (e2 ++ (e3 ++ e4)) := by
            simp only [List.append_assoc]
          exact ⟨x_spqr, hlen, Or.inr ⟨e1, e2 ++ (e3 ++ e4), hassoc, hp1Sub _ hp1,
            Or.inr ⟨e2, e3 ++ e4, rfl, Or.inr (hp2f r_arch rfl),
              Or.inr ⟨e3, e4, rfl, Or.inr (hp3Sub _ hp3), Or.inr (hp4Sub _ hp4)⟩⟩⟩⟩
  obtain ⟨x_spqr, hlen, hChain⟩ := hP2Case
  refine ⟨e2ar_mkWitnessParams W x m.opkId.isSome m.spkId m.kpkId (m.opkId.getD 0#32)
      x_spqr recG ses0.state true tdCall r_arch G' ses' enc_prev1,
    e2ar_mkWitnessParams_dom W x m.opkId.isSome m.spkId m.kpkId (m.opkId.getD 0#32)
      x_spqr recG ses0.state true tdCall r_arch G' ses' enc_prev1
      hlen hCap hOut1Post (fun _ => hTdDom),
    rfl, rfl,
    Or.inr hChain⟩

end LibsignalBinary.Proofs.SignalSession.Cli.D3.F3.H7OverD3SlotWideWitness
