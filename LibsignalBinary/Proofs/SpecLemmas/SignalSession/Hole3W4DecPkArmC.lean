/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Matched.M3PrevCapPlacedBudget
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Over.StageP3PlacedBudgetAux
public import LibsignalBinary.Proofs.PeakBudget.CliDpPollTrustedWideBridgeX
public import LibsignalBinary.Proofs.PeakBudget.SpqrTrialDomainLift
public import LibsignalBinary.Proofs.PeakBudget.W4PathCVerNeWideDefs
public import LibsignalBinary.Proofs.PeakBudget.W4PostBobPrev1Dom
public import LibsignalBinary.Proofs.PeakBudget.W4RecvPrekeyCmkDom0TdAux
public import LibsignalBinary.Proofs.SignalSession.Cli.F3.HRead.ReadFileBudgetPlaced
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Over.PollOverPathCPlacedBudgetAux
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.ClosureTrustedP1PlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.SkeletonPlacedBudget
public import LibsignalBinary.Proofs.SpecLemmas.SignalSession.Hole3W4DecPkR2
public import LibsignalBinary.Proofs.SpecLemmas.SignalSession.Hole3W4DecPkWireStep2
import LibsignalBinary.Proofs.ConsumeMessageKey.AdvanceEpilogueProofs.FetchBudget
import LibsignalBinary.Proofs.PeakBudget.CliRealBinaryKitEnvs
import LibsignalBinary.Proofs.PeakBudget.CliRealExistentialCalleeEnvs
import LibsignalBinary.Proofs.PeakBudget.RealCliRunEnvMemFixed
import LibsignalBinary.Proofs.PeakBudget.SpqrDomainCapsAux
import LibsignalBinary.Proofs.PeakBudget.SpqrTrialDomainLiftAux
import LibsignalBinary.Proofs.PeakBudget.W2DecryptCloneBounds
import LibsignalBinary.Proofs.PeakBudget.W4OuterPeakSpec
import LibsignalBinary.Proofs.PeakBudget.W4PostBobPrev1Derive
import LibsignalBinary.Proofs.PeakBudget.W4PostBobPrev1DomIdle
import LibsignalBinary.Proofs.PeakBudget.W4RecvPrekeyCmkDom0
import LibsignalBinary.Proofs.PeakBudget.W4RecvPrekeyCmkSlot
import LibsignalBinary.Proofs.PublicApi.MessageDecrypt.DefsBudget
import LibsignalBinary.Proofs.SignalSession.Cli.D3.F3.H7OverD3SlotDom0EnvSub
import LibsignalBinary.Proofs.SignalSession.Cli.D3.F3.H7OverD3SlotDom0LeafL23
import LibsignalBinary.Proofs.SignalSession.Cli.D3.F3.H7OverD3SlotDom0LeafL45R
import LibsignalBinary.Proofs.SignalSession.Cli.D3.F3.H7OverD3SlotDom0Leaves16
import LibsignalBinary.Proofs.SignalSession.Cli.D3.F3.H7OverD3SlotWideWitness
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.S0
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.LoadRec
import LibsignalBinary.Proofs.SpecLemmas.SignalSession.Hole3W4DecPkStep2

/-!
# Path-C (`Over`) Envelope Inclusion for Post-Bob `decryptPrekey` (`W4`)

Proves `w4pb_armC_sub_dom0'`, embedding the Path-C (`Over`) disjunct of
`W4r2PollCustomP3GvSeqFreeEnv` (`p2Over`, `p3ErrM3`, `p3VerNe`, and `p4Prev1Exit`) into
`realCliDecPkBinaryWideSlotEnvCmkDom0'Fixed w4c_repairedStatesRecvEnvFam`.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000

namespace LibsignalBinary.Proofs.SpecLemmas.SignalSession.Hole3W4DecPkArmC

open CryptoGames.LibsignalSession (Crypto PublicKey SessionState SignalMessage)
open CryptoGames.LibsignalSessionApi (Session SessionRecord)
open CryptoVerification (LibsignalPlacement)
open CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.GenP3 (genP3S5Model)
open CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Over (clearPending)
open CryptoVerification.E2E
  (LocalIdentity PEParams PreKeyMessageFields ResponderPreKeySecrets UnreachedPqxdhPrimitives
   acceptInput modelPrims)
open CryptoVerification.E2E.Record (encSession encodeRecord)
open CryptoVerification.LibsignalProtoCodec (protoSignalCodec)
open CryptoVerification.LibsignalPublicApi.StoreKit (FsFiles)
open CryptoVerification.LibsignalPublicApiRepr (AddrVal RecordGhost)
open CryptoVerification.LibsignalSpqrV1 (MlKem)
open CryptoVerification.LibsignalTripleRatchet (DoReserveCall reserveCap)
open CryptoVerification.LibsignalTripleRatchet.Record (CloneRel)
open CryptoVerification.LibsignalTripleRatchetRepr (SessionGhost SignalMessageGhost)
open CryptoVerification.RecordCodecs (IdentityKeyPair)
open CryptoVerification.RustHeap (RustAlloc)
open CryptoVerification.SignalSession (CliHooks)
open CryptoVerification.SignalSession.Cli (StoresGhost)
open CryptoVerification.SignalSession.Cli.MainHops (cliIo cliRunBudgets)
open CryptoVerification.SignalSession.Cli.RunCompose (DecPkGhost)
open CryptoVerification.SignalSession.Cli.RunProofs
  (DecPkOkD2c SessMatchesPm pkStoreKeys pkToE? pkToE?_pmOfE pmOfE)
open CryptoVerification.SignalSession.Cli.RunProofs.Poll
  (cliKitStk cliPollIdKitPlaced cliPollKpkKitPlaced cliPollPkKitPlaced cliPollSessPrev1KitPlaced
   pathAInitSession pathAInitState pmPreKeyId)
open CryptoVerification.SignalSession.Cli.Slots (FilesOkPeer loadRec scopeIn sessLoadAns_loadRec)
open CryptoVerification.SpqrV1.Top.InitialState (InitialStateGhost)
open LibsignalBinary.Heap (AllocEvent SeqEnv)
open LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Matched.M3PrevCapPlacedBudget
  (StageP3ErrM3Env StageP3OkPrefixM3Env stageP3M3TryDecryptEnvArgs)
open LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Over.StageP3PlacedBudgetAux
  (StageP3VerNePrev1Env)
open LibsignalBinary.Proofs.ConsumeMessageKey.AdvanceEpilogueProofs.FetchBudget (CmkLoopAdvanceEvs)
open LibsignalBinary.Proofs.PeakBudget.CliDpPollTrustedWideBridgeX
  (dpx_cliStageP1OkEnv_sub_w4StageP1OkAllFixed dpx_deserEnv dpx_p2OverErrEnv dpx_p2OverOkEnv
   dpx_stageP4Prev1SeqFree_sub_w4StageP4PathCAllFixed)
open LibsignalBinary.Proofs.PeakBudget.CliRealBinaryKitEnvs
  (W4BinaryStageP2MatchedWideEnv W4CloneACDomEnv W4CloneBDomEnv)
open LibsignalBinary.Proofs.PeakBudget.CliRealExistentialCalleeEnvs
  (cliIo_rd_ok_length_le_sessionCapBytes)
open LibsignalBinary.Proofs.PeakBudget.RealCliRunEnvMemFixed
  (W4BinaryStageP1OkEnvAllFixed W4BinaryStageP2PathAWideEnvAllFixed
   W4BinaryStageP2PathCWideEnvAllFixed W4BinaryStageP4MatchedWideEnvAllFixed
   W4BinaryStageP4PathAWideEnvAllFixed W4BinaryStageP4PathCWideEnvAllFixed)
open LibsignalBinary.Proofs.PeakBudget.SpqrDomainCapsAux (sessionCapBytes)
open LibsignalBinary.Proofs.PeakBudget.SpqrTrialDomainLift (PeerSpqrStateTight640)
open LibsignalBinary.Proofs.PeakBudget.SpqrTrialDomainLiftAux (TopStateTight)
open LibsignalBinary.Proofs.PeakBudget.W2DecryptCloneBounds (FreshBobCloneDom SessionCloneDom)
open LibsignalBinary.Proofs.PeakBudget.W4OuterPeakSpec (OptStageEnv W4StageP3WideEnv)
open LibsignalBinary.Proofs.PeakBudget.W4PathCVerNeWideDefs
  (VerNeTightTopEnv VerNeTightTopRawEnv W4StageP3Prev1WideEnvOf)
open LibsignalBinary.Proofs.PeakBudget.W4PostBobPrev1Derive
  (postBobPrev1Dom_of_arm4 postBobPrev1Dom_of_leaves)
open LibsignalBinary.Proofs.PeakBudget.W4PostBobPrev1Dom
  (PostBobPrev1Dom SessionGetPrev0Guard W4BinaryCallSiteDomCmk0' postBobTotalPrev1Cap286K
   realCliDecPkBinaryWideSlotEnvCmkDom0'Fixed w4PostBobPqCap)
open LibsignalBinary.Proofs.PeakBudget.W4PostBobPrev1DomIdle (postBobPrev1Dom_idle_exists)
open LibsignalBinary.Proofs.PeakBudget.W4RecvPrekeyCmkDom0
  (W4BinaryRecvPrekeyWideSlotEnvCmkVerNeSrAllFixedOf W4RecvPrekeyTryDecACCmkSrEnvOf
   W4TrialRunWideCmkSrEnvOf mkW4RecvPrekeyWideCmkSrSlotParamsOf)
open LibsignalBinary.Proofs.PeakBudget.W4RecvPrekeyCmkDom0TdAux
  (W4FailedTdCancelCmkSrEnvOf W4StatesRecvEnv w4c_TryDecryptCliLinkedSrEnvOf
   w4c_repairedStatesRecvEnvFam)
open LibsignalBinary.Proofs.PeakBudget.W4RecvPrekeyCmkSlot
  (W4ArchivedTrialCmk W4BinaryRecvPrekeyParamsCmk W4FailedTryDecryptCallCmk W4LoopAdvEnv
   W4RecvPrekeyRealParamsCmk W4TrialDecCmkEnv W4TrialDropCmkEnv W4TryDecryptCallCmk
   W4TryDecryptPathACDomCmkOf w4c_defaultDecodeMaxOps)
open LibsignalBinary.Proofs.PublicApi.MessageDecrypt.DefsBudget (SessionGhostValid)
open LibsignalBinary.Proofs.SignalSession.Cli.D3.F3.H7OverD3SlotDom0EnvSub
  (h7w_p2OverOk_sub_w4StageP2PathCAllFixed h7w_stageP2Over_sub_w4StageP2PathCAllFixed)
open LibsignalBinary.Proofs.SignalSession.Cli.D3.F3.H7OverD3SlotDom0LeafL23
  (h7l23_encSession_clearPending_le_encodeRecord h7l23_encodeRecord_clearPending_le_encodeRecord)
open LibsignalBinary.Proofs.SignalSession.Cli.D3.F3.H7OverD3SlotDom0LeafL45R
  (h7l45r_pathAInit_freshBobCloneDom h7l45r_pathAInit_receiverChains_nil
   h7l45r_pathAInit_topStateTight)
open LibsignalBinary.Proofs.SignalSession.Cli.D3.F3.H7OverD3SlotDom0Leaves16 (h7w_l6_proved)
open LibsignalBinary.Proofs.SignalSession.Cli.D3.F3.H7OverD3SlotWideWitness
  (H7wCallSiteDomOut1 H7wOverSlotEnvAllFixedOf h7w_overSlotEnv_to_fourArmAllFixed)
open LibsignalBinary.Proofs.SignalSession.Cli.F3.HRead.ReadFileBudgetPlaced (ReadFileRuleEnvFixed)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Over.PollOverPathCPlacedBudgetAux
  (StageP2OverEnv StageP4Prev1Env)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.ClosureTrustedP1PlacedBudget
  (CliStageP1OkEnv)
open LibsignalBinary.Proofs.SpecLemmas.SignalSession.Hole3W4DecPkR2
  (W4r2SessionGhostValid w4r2_cliPollStageP4Prev1SeqFreeEnvsAt)
open LibsignalBinary.Proofs.SpecLemmas.SignalSession.Hole3W4DecPkStep2
  (w4s2_tryDecryptCliLinkedEnvOf_eq_m2rg)
open LibsignalBinary.Proofs.SpecLemmas.SignalSession.Hole3W4DecPkWireStep2
  (w4s2_TryDecryptTopStateGuardedEnv w4s2_tryDecryptTopStateGuardedEnv_eq_linked_of_top)
open LibsignalBinary.Proofs.TripleRatchet.Record.DefsBudget (TryDecryptEnvArgs)

private def w4pb_armc_dummyReserve : DoReserveCall :=
  ⟨0#64, 0#64, 0#64, [], 0⟩

private theorem w4pb_armc_dummyReserve_old : w4pb_armc_dummyReserve.cap.toNat ≤ 4096 := by decide

private theorem w4pb_armc_dummyReserve_new :
    reserveCap w4pb_armc_dummyReserve.cap.toNat w4pb_armc_dummyReserve.bs.length
      w4pb_armc_dummyReserve.additional ≤ 4096 := by
  decide

private def w4pb_armc_dummyInitialStateGhost : InitialStateGhost :=
  ⟨0#64, 0#64, 0#64, { direction := .b2a, version := .v1, minVersion := .v1, authKey := [] }⟩

private theorem w4pb_armc_dummyInitialStateGhost_key :
    w4pb_armc_dummyInitialStateGhost.p.authKey.length ≤ 32 := by
  decide

private def w4pb_armc_noneRecordGhost : RecordGhost :=
  ⟨0#64, 0#64, none⟩

private def w4pb_armc_emptySessionRecord : SessionRecord (List (BitVec 8)) :=
  ⟨none⟩

private theorem w4pb_armc_emptySessionRecord_enc :
    (encodeRecord w4pb_armc_emptySessionRecord).length ≤ 2097152 := by
  decide

private def w4pb_armc_dummyWhisperGhost : SignalMessageGhost :=
  ⟨0#64, 0#64, 0#64, 0#64, 0#64⟩

private def w4pb_armc_dummyTdCall
    (G_d : SessionGhost) (st_d : SessionState (List (BitVec 8))) (x : DecPkGhost) :
    W4TryDecryptCallCmk :=
  ⟨stageP3M3TryDecryptEnvArgs G_d st_d x.peer x.me w4pb_armc_dummyWhisperGhost x.msg.message x.coins⟩

private def w4pb_armc_dummyFailedTdCall
    (G_d : SessionGhost) (st_d : SessionState (List (BitVec 8))) (x : DecPkGhost) :
    W4FailedTryDecryptCallCmk :=
  ⟨w4pb_armc_dummyTdCall G_d st_d x, []⟩

private def w4pb_armc_mkWitnessParams
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
    x_res := w4pb_armc_dummyReserve
    x_spqr := x_spqr
    hasCurSession := false
    G_cur := G_cur
    st_cur := st_cur
    fc_cur := w4pb_armc_dummyFailedTdCall G_cur st_cur x
    archivedTrials := []
    isPathB := false
    td_B := w4pb_armc_dummyTdCall G_cur st_cur x
    isPathAC := isPathAC
    td_AC := td_AC
    g_arch := w4pb_armc_noneRecordGhost
    r_arch := r_arch
    g_out0 := w4pb_armc_noneRecordGhost
    r_out0 := w4pb_armc_emptySessionRecord
    G_out1 := G_out1
    sess_out1 := sess_out1
    enc_prev1 := enc_prev1
  }
  remoteIdKey := x.msg.identityKey
  baseKey := x.msg.baseKey

private theorem w4pb_armc_mkWitnessParams_dom
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
      (w4pb_armc_mkWitnessParams W x hasOpk spkId kpkId opkId x_spqr G_cur st_cur
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
  res_old := w4pb_armc_dummyReserve_old
  res_new := w4pb_armc_dummyReserve_new
  spqr_key := hSpqrKey
  cur_dom := Or.inl rfl
  arch_valid := fun _ _ hg _ => nomatch hg
  arch_enc := hArchEnc
  out0_valid := fun _ _ hg _ => nomatch hg
  out0_enc := w4pb_armc_emptySessionRecord_enc
  out1_dom := hOut1
  trials_len4 := Nat.zero_le 4
  cur_fail_dom := fun h => Bool.noConfusion h
  trials_dom := fun _ hy => nomatch hy
  tdB_dom := fun h => Bool.noConfusion h
  tdAC_dom := hTdAC
  archivedTrials_nil := rfl

private theorem w4pb_armc_tdPathACDom_of_stageP3
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

private theorem w4pb_armc_toCallSiteDomCmk0'
    {C : Crypto} {K : MlKem} {maxCt : Nat} {peerVal : AddrVal} {files : FsFiles}
    {R : W4RecvPrekeyRealParamsCmk}
    (h : H7wCallSiteDomOut1
      (PostBobPrev1Dom w4PostBobPqCap 2097152 postBobTotalPrev1Cap286K)
      C K maxCt peerVal files R) :
    W4BinaryCallSiteDomCmk0' C K maxCt peerVal files R :=
  ⟨{ eq_C := h.eq_C
     eq_K := h.eq_K
     eq_rd := h.eq_rd
     eq_files := h.eq_files
     eq_peerVal := h.eq_peerVal
     kpk_dir := h.kpk_dir
     ownKey_len := h.ownKey_len
     ownReg_len := h.ownReg_len
     kpkMark_len := h.kpkMark_len
     res_old := h.res_old
     res_new := h.res_new
     spqr_key := h.spqr_key
     cur_dom := h.cur_dom
     arch_valid := h.arch_valid
     arch_enc := h.arch_enc
     out0_valid := h.out0_valid
     out0_enc := h.out0_enc
     out1_postBob := h.out1_dom
     trials_len4 := h.trials_len4
     cur_fail_dom := h.cur_fail_dom
     trials_dom := h.trials_dom
     tdB_dom := h.tdB_dom
     tdAC_dom := h.tdAC_dom },
   h.archivedTrials_nil⟩

private theorem w4pb_armc_overSlotEnv_to_allFixed
    {SR : W4StatesRecvEnv} {LoopAdvEnv : W4LoopAdvEnv} {maxOps : Nat}
    {w : W4BinaryRecvPrekeyParamsCmk} {evs : List AllocEvent}
    (h : H7wOverSlotEnvAllFixedOf
      (W4FailedTdCancelCmkSrEnvOf SR LoopAdvEnv maxOps)
      (W4TrialRunWideCmkSrEnvOf SR LoopAdvEnv maxOps)
      (w4c_TryDecryptCliLinkedSrEnvOf SR LoopAdvEnv maxOps) w evs) :
    W4BinaryRecvPrekeyWideSlotEnvCmkVerNeSrAllFixedOf SR LoopAdvEnv maxOps w evs := by
  let P := mkW4RecvPrekeyWideCmkSrSlotParamsOf SR LoopAdvEnv maxOps w.base
  exact h7w_overSlotEnv_to_fourArmAllFixed
    (fun e =>
      SeqEnv (W4BinaryStageP1OkEnvAllFixed w.base.rd w.base.files w.base.peer w.remoteIdKey)
        (SeqEnv
          (OptStageEnv
            (W4BinaryStageP2MatchedWideEnv P.DecEnv P.TrialEnv P.DropEnv P.archivedTrials
              w.base.g_arch w.base.r_arch))
          (SeqEnv (OptStageEnv (W4StageP3WideEnv W4CloneBDomEnv P.TryDecEnv))
            (OptStageEnv
              (W4BinaryStageP4MatchedWideEnvAllFixed w.base.rd w.base.files w.base.peer
                w.remoteIdKey w.base.g_out0 w.base.r_out0)))) e)
    (fun e =>
      SeqEnv (W4BinaryStageP1OkEnvAllFixed w.base.rd w.base.files w.base.peer w.remoteIdKey)
        (SeqEnv
          (OptStageEnv
            (W4BinaryStageP2PathAWideEnvAllFixed w.base.hasOpk w.base.rd w.base.files
              w.base.spkId w.base.kpkId w.base.opkId w.base.C.F w.base.x_res w.base.x_spqr))
          (SeqEnv
            (OptStageEnv
              (W4StageP3WideEnv W4CloneACDomEnv
                (W4RecvPrekeyTryDecACCmkSrEnvOf SR LoopAdvEnv maxOps w.base)))
            (OptStageEnv
              (W4BinaryStageP4PathAWideEnvAllFixed w.base.hasOpk w.base.rd w.base.files w.base.peer
                w.remoteIdKey w.base.kpkId w.base.spkId w.base.opkId w.baseKey
                w.base.g_out0 w.base.r_out0)))) e)
    h

private theorem w4pb_armc_loadRec_encodeRecord_le_cap
    {F : FsFiles} {peer : AddrVal} {r : SessionRecord (List (BitVec 8))}
    (hfPeer : FilesOkPeer scopeIn F peer)
    (hload : loadRec scopeIn F peer = .ok (some r)) :
    (encodeRecord r).length ≤ 2097152 := by
  have hans := sessLoadAns_loadRec hfPeer
  obtain ⟨bs, hget, _⟩ := hfPeer.sessGet
  rw [hget, hload] at hans
  have hbs : bs.length ≤ sessionCapBytes :=
    cliIo_rd_ok_length_le_sessionCapBytes F _ bs hget
  have hcap_eq : sessionCapBytes = 2097152 := rfl
  rw [hcap_eq] at hbs
  cases bs with
  | nil => cases hans
  | cons b₀ bs' =>
    obtain ⟨r', hr', henc, _⟩ := hans
    injection hr' with hr'
    injection hr' with hr'
    subst hr'
    rw [henc]
    exact hbs

private theorem w4pb_armc_sessionCloneDom_16K_to_postBob {s : Session (List (BitVec 8))}
    (hdom : SessionCloneDom 16384 s) :
    SessionCloneDom w4PostBobPqCap s where
  rc_len := hdom.rc_len
  seeds32 := hdom.seeds32
  alice_len := hdom.alice_len
  kyber_cap := hdom.kyber_cap
  pq_len := Nat.le_trans hdom.pq_len (by decide)

private theorem w4pb_armc_freshBob_postBobPrev1Dom
    (P : PEParams) (me : LocalIdentity) (k : ResponderPreKeySecrets)
    (m : PreKeyMessageFields) (dk : SignalPqxdh.DRKey)
    (recG : SessionGhost) {enc : List (BitVec 8)}
    (hgv : SessionGhostValid recG (pathAInitSession P me k m dk))
    (hprev : enc.length ≤ 2097152) :
    PostBobPrev1Dom w4PostBobPqCap 2097152 postBobTotalPrev1Cap286K
      recG (pathAInitSession P me k m dk) enc := by
  have hClone := h7l45r_pathAInit_freshBobCloneDom P me k m dk recG hgv
  have hrc1 : (pathAInitSession P me k m dk).state.receiverChains.length ≤ 1 := by
    have hnil : (pathAInitState P me k m dk).receiverChains = [] :=
      h7l45r_pathAInit_receiverChains_nil P me k m dk
    change (pathAInitState P me k m dk).receiverChains.length ≤ 1
    rw [hnil]
    decide
  exact postBobPrev1Dom_of_leaves hrc1 hgv (w4pb_armc_sessionCloneDom_16K_to_postBob hClone.dom) hprev

private theorem w4pb_armc_tdSub (W : CliHooks) (a : TryDecryptEnvArgs) (e : List AllocEvent)
    (hTop : TopStateTight W.C.F W.Q.K a.st.pqRatchetState)
    (htd : w4s2_TryDecryptTopStateGuardedEnv W a e) :
    w4c_TryDecryptCliLinkedSrEnvOf w4c_repairedStatesRecvEnvFam CmkLoopAdvanceEvs
      w4c_defaultDecodeMaxOps W.C W.Q.K a e := by
  have heq : w4s2_TryDecryptTopStateGuardedEnv W a =
      w4c_TryDecryptCliLinkedSrEnvOf w4c_repairedStatesRecvEnvFam CmkLoopAdvanceEvs
        w4c_defaultDecodeMaxOps W.C W.Q.K a :=
    (w4s2_tryDecryptTopStateGuardedEnv_eq_linked_of_top W a hTop).trans
      (congrFun (w4s2_tryDecryptCliLinkedEnvOf_eq_m2rg 109 W.C W.Q.K) a)
  rwa [heq] at htd

private theorem w4pb_armc_optStageEnv_nil (P : List AllocEvent → Prop) : OptStageEnv P [] :=
  Or.inl fun _ h => nomatch h

private theorem w4pb_armc_witness_p1Ok [LibsignalPlacement]
    {Out1Dom : SessionGhost → Session (List (BitVec 8)) → List (BitVec 8) → Prop}
    {FailTargetEnv : Crypto → MlKem → W4FailedTryDecryptCallCmk → List AllocEvent → Prop}
    {TrialTargetEnv : Crypto → MlKem → W4ArchivedTrialCmk → List AllocEvent → Prop}
    {TdTargetEnv : Crypto → MlKem → TryDecryptEnvArgs → List AllocEvent → Prop}
    {maxCt : Nat} (A : RustAlloc) (W : CliHooks) (x : DecPkGhost)
    (G_idle : SessionGhost) (ses_idle : Session (List (BitVec 8)))
    (hOut1 : Out1Dom G_idle ses_idle [])
    {evs : List AllocEvent}
    (h : CliStageP1OkEnv (A := A) cliRunBudgets
      (ReadFileRuleEnvFixed cliIo.rd) dpx_deserEnv x evs) :
    ∃ w4 : W4BinaryRecvPrekeyParamsCmk,
      H7wCallSiteDomOut1 Out1Dom W.C W.Q.K maxCt x.peer.val x.F w4.base ∧
      w4.remoteIdKey = x.msg.identityKey ∧
      w4.baseKey = x.msg.baseKey ∧
      H7wOverSlotEnvAllFixedOf FailTargetEnv TrialTargetEnv TdTargetEnv w4 evs :=
  ⟨w4pb_armc_mkWitnessParams W x false 0#32 0#32 0#32 w4pb_armc_dummyInitialStateGhost
      G_idle ses_idle.state false (w4pb_armc_dummyTdCall G_idle ses_idle.state x)
      w4pb_armc_emptySessionRecord G_idle ses_idle [],
    w4pb_armc_mkWitnessParams_dom W x false 0#32 0#32 0#32 w4pb_armc_dummyInitialStateGhost
      G_idle ses_idle.state false (w4pb_armc_dummyTdCall G_idle ses_idle.state x)
      w4pb_armc_emptySessionRecord G_idle ses_idle []
      w4pb_armc_dummyInitialStateGhost_key w4pb_armc_emptySessionRecord_enc hOut1
      (fun hfalse => Bool.noConfusion hfalse),
    rfl, rfl,
    Or.inr (Or.inl (dpx_cliStageP1OkEnv_sub_w4StageP1OkAllFixed h))⟩

private theorem w4pb_armc_witness_p2Over [LibsignalPlacement]
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
    (h : SeqEnv
      (CliStageP1OkEnv (A := A) cliRunBudgets (ReadFileRuleEnvFixed cliIo.rd) dpx_deserEnv x)
      (StageP2OverEnv (dpx_p2OverErrEnv A X W) (dpx_p2OverOkEnv A X W) x r) evs) :
    ∃ w4 : W4BinaryRecvPrekeyParamsCmk,
      H7wCallSiteDomOut1 Out1Dom W.C W.Q.K maxCt x.peer.val x.F w4.base ∧
      w4.remoteIdKey = x.msg.identityKey ∧
      w4.baseKey = x.msg.baseKey ∧
      H7wOverSlotEnvAllFixedOf FailTargetEnv TrialTargetEnv TdTargetEnv w4 evs := by
  rcases h with hp1 | ⟨e1, e2, rfl, hp1, hp2⟩
  · exact w4pb_armc_witness_p1Ok A W x G_idle ses_idle hOut1 hp1
  · let r_arch : SessionRecord (List (BitVec 8)) := ⟨some (clearPending s_old)⟩
    obtain ⟨m, x_spqr, _hm, _hver, hlen, hp2W4⟩ :=
      h7w_stageP2Over_sub_w4StageP2PathCAllFixed A X W G_idle ses_idle.state
        (fun _ => False) W4TrialDecCmkEnv (TrialTargetEnv W.C W.Q.K) W4TrialDropCmkEnv
        ([] : List W4ArchivedTrialCmk) w4pb_armc_noneRecordGhost w4pb_armc_dummyReserve
        (r_arch := r_arch) hcur rfl hp2
    exact ⟨w4pb_armc_mkWitnessParams W x m.opkId.isSome m.spkId m.kpkId (m.opkId.getD 0#32)
        x_spqr G_idle ses_idle.state false (w4pb_armc_dummyTdCall G_idle ses_idle.state x)
        r_arch G_idle ses_idle [],
      w4pb_armc_mkWitnessParams_dom W x m.opkId.isSome m.spkId m.kpkId (m.opkId.getD 0#32)
        x_spqr G_idle ses_idle.state false (w4pb_armc_dummyTdCall G_idle ses_idle.state x)
        r_arch G_idle ses_idle []
        hlen hCap hOut1 (fun hfalse => Bool.noConfusion hfalse),
      rfl, rfl,
      Or.inr (Or.inr ⟨e1, e2, rfl, dpx_cliStageP1OkEnv_sub_w4StageP1OkAllFixed hp1,
        Or.inl (Or.inr hp2W4)⟩)⟩

private theorem w4pb_armc_witness_p3ErrM3 [LibsignalPlacement]
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
    (h : SeqEnv
      (SeqEnv
        (CliStageP1OkEnv (A := A) cliRunBudgets (ReadFileRuleEnvFixed cliIo.rd) dpx_deserEnv x)
        (dpx_p2OverOkEnv A X W x r))
      (StageP3ErrM3Env (tdEnv W) recG G₁ ses0.state x.peer x.me whisperG
        x.msg.message x.coins) evs) :
    ∃ w4 : W4BinaryRecvPrekeyParamsCmk,
      H7wCallSiteDomOut1 Out1Dom W.C W.Q.K maxCt x.peer.val x.F w4.base ∧
      w4.remoteIdKey = x.msg.identityKey ∧
      w4.baseKey = x.msg.baseKey ∧
      H7wOverSlotEnvAllFixedOf FailTargetEnv TrialTargetEnv TdTargetEnv w4 evs := by
  rcases h with h12 | ⟨e12, e3, rfl, h12, hp3⟩
  · exact w4pb_armc_witness_p2Over A X W x r s_old G_out1 sess_out1 hcur hCap hOut1Idle
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
    · exact ⟨w4pb_armc_mkWitnessParams W x false 0#32 0#32 0#32 w4pb_armc_dummyInitialStateGhost
          recG ses0.state true tdCall r_arch G_out1 sess_out1 enc_prev1,
        w4pb_armc_mkWitnessParams_dom W x false 0#32 0#32 0#32 w4pb_armc_dummyInitialStateGhost
          recG ses0.state true tdCall r_arch G_out1 sess_out1 enc_prev1
          w4pb_armc_dummyInitialStateGhost_key hCap hOut1Prev1
          (fun _ => w4pb_armc_tdPathACDom_of_stageP3 W x G₁ ses0.state whisperG
            hCloneDom.rc_nil htop hct),
        rfl, rfl,
        Or.inr (Or.inr ⟨e12, e3, rfl, dpx_cliStageP1OkEnv_sub_w4StageP1OkAllFixed hp1,
          Or.inr ⟨[], e3, rfl, w4pb_armc_optStageEnv_nil _, Or.inl (Or.inr hp3W4)⟩⟩)⟩
    · obtain ⟨m, sess, x_spqr, _hm, hsess, _hver, hlen, hp2Sub⟩ :=
        h7w_p2OverOk_sub_w4StageP2PathCAllFixed A X W recG ses0.state
          (fun _ => False) W4TrialDecCmkEnv (TrialTargetEnv W.C W.Q.K) W4TrialDropCmkEnv
          ([] : List W4ArchivedTrialCmk) w4pb_armc_noneRecordGhost w4pb_armc_dummyReserve hp2
      have hse : sess = s_old := Option.some.inj (hsess.symm.trans hcur)
      subst hse
      exact ⟨w4pb_armc_mkWitnessParams W x m.opkId.isSome m.spkId m.kpkId (m.opkId.getD 0#32)
          x_spqr recG ses0.state true tdCall r_arch G_out1 sess_out1 enc_prev1,
        w4pb_armc_mkWitnessParams_dom W x m.opkId.isSome m.spkId m.kpkId (m.opkId.getD 0#32)
          x_spqr recG ses0.state true tdCall r_arch G_out1 sess_out1 enc_prev1
          hlen hCap hOut1Prev1
          (fun _ => w4pb_armc_tdPathACDom_of_stageP3 W x G₁ ses0.state whisperG
            hCloneDom.rc_nil htop hct),
        rfl, rfl,
        Or.inr (Or.inr ⟨e1, e2 ++ e3, List.append_assoc e1 e2 e3,
          dpx_cliStageP1OkEnv_sub_w4StageP1OkAllFixed hp1,
          Or.inr ⟨e2, e3, rfl, Or.inr (hp2Sub r_arch rfl), Or.inl (Or.inr hp3W4)⟩⟩)⟩

private theorem w4pb_armc_witness_p3VerNe [LibsignalPlacement]
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
    (h : SeqEnv
      (SeqEnv
        (CliStageP1OkEnv (A := A) cliRunBudgets (ReadFileRuleEnvFixed cliIo.rd) dpx_deserEnv x)
        (dpx_p2OverOkEnv A X W x r))
      (StageP3VerNePrev1Env VerNeTightTopRawEnv recG ses0.state
        (encSession (clearPending s_old))) evs) :
    ∃ w4 : W4BinaryRecvPrekeyParamsCmk,
      H7wCallSiteDomOut1 Out1Dom W.C W.Q.K maxCt x.peer.val x.F w4.base ∧
      w4.remoteIdKey = x.msg.identityKey ∧
      w4.baseKey = x.msg.baseKey ∧
      H7wOverSlotEnvAllFixedOf FailTargetEnv TrialTargetEnv TdTargetEnv w4 evs := by
  rcases h with h12 | ⟨e12, e3, rfl, h12, hp3⟩
  · exact w4pb_armc_witness_p2Over A X W x r s_old G_out1 sess_out1 hcur hCap hOut1Idle
      (match h12 with
       | Or.inl hp1 => Or.inl hp1
       | Or.inr ⟨e1, e2, heq, hp1, hp2⟩ => Or.inr ⟨e1, e2, heq, hp1, Or.inr hp2⟩)
  · have hCapPow : (encodeRecord ⟨some (clearPending s_old)⟩).length ≤ 2 ^ 21 := hCap
    let tdCall := w4pb_armc_dummyTdCall recG ses0.state x
    let r_arch : SessionRecord (List (BitVec 8)) := ⟨some (clearPending s_old)⟩
    let enc_prev1 := encSession (clearPending s_old)
    have hp3W4 := (h7w_l6_proved W tdEnv recG ses0.state x.peer x.me x.msg.message x.coins s_old
      (CloneEnv := W4CloneACDomEnv) (fun _ hcl => ⟨recG, ses0, hCloneDom, hcl⟩)).2.1
      hCapPow (fun _ => False) e3 hp3
    rcases h12 with hp1 | ⟨e1, e2, rfl, hp1, hp2⟩
    · exact ⟨w4pb_armc_mkWitnessParams W x false 0#32 0#32 0#32 w4pb_armc_dummyInitialStateGhost
          recG ses0.state false tdCall r_arch G_out1 sess_out1 enc_prev1,
        w4pb_armc_mkWitnessParams_dom W x false 0#32 0#32 0#32 w4pb_armc_dummyInitialStateGhost
          recG ses0.state false tdCall r_arch G_out1 sess_out1 enc_prev1
          w4pb_armc_dummyInitialStateGhost_key hCap hOut1Prev1 (fun hf => Bool.noConfusion hf),
        rfl, rfl,
        Or.inr (Or.inr ⟨e12, e3, rfl, dpx_cliStageP1OkEnv_sub_w4StageP1OkAllFixed hp1,
          Or.inr ⟨[], e3, rfl, w4pb_armc_optStageEnv_nil _, Or.inl (Or.inr hp3W4)⟩⟩)⟩
    · obtain ⟨m, sess, x_spqr, _hm, hsess, _hver, hlen, hp2Sub⟩ :=
        h7w_p2OverOk_sub_w4StageP2PathCAllFixed A X W recG ses0.state
          (fun _ => False) W4TrialDecCmkEnv (TrialTargetEnv W.C W.Q.K) W4TrialDropCmkEnv
          ([] : List W4ArchivedTrialCmk) w4pb_armc_noneRecordGhost w4pb_armc_dummyReserve hp2
      have hse : sess = s_old := Option.some.inj (hsess.symm.trans hcur)
      subst hse
      exact ⟨w4pb_armc_mkWitnessParams W x m.opkId.isSome m.spkId m.kpkId (m.opkId.getD 0#32)
          x_spqr recG ses0.state false tdCall r_arch G_out1 sess_out1 enc_prev1,
        w4pb_armc_mkWitnessParams_dom W x m.opkId.isSome m.spkId m.kpkId (m.opkId.getD 0#32)
          x_spqr recG ses0.state false tdCall r_arch G_out1 sess_out1 enc_prev1
          hlen hCap hOut1Prev1 (fun hf => Bool.noConfusion hf),
        rfl, rfl,
        Or.inr (Or.inr ⟨e1, e2 ++ e3, List.append_assoc e1 e2 e3,
          dpx_cliStageP1OkEnv_sub_w4StageP1OkAllFixed hp1,
          Or.inr ⟨e2, e3, rfl, Or.inr (hp2Sub r_arch rfl), Or.inl (Or.inr hp3W4)⟩⟩)⟩

private theorem w4pb_armc_witness_p4Prev1 [LibsignalPlacement]
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
      let envs := w4r2_cliPollStageP4Prev1SeqFreeEnvsAt A cliRunBudgets x.F x.peer pid₀
        kpkId₀ spkId₀ kbk₀ ReadEnv
      SeqEnv
        (SeqEnv
          (SeqEnv
            (CliStageP1OkEnv (A := A) cliRunBudgets ReadEnv dpx_deserEnv x)
            (dpx_p2OverOkEnv A X W x r))
          (StageP3OkPrefixM3Env (tdEnv W) recG G₁ ses0.state x.peer x.me whisperG
            x.msg.message x.coins))
        (StageP4Prev1Env
          (cliPollSessPrev1KitPlaced A x.F x.peer σ) envs.opsEnv
          (cliPollIdKitPlaced A x.F x.peer σ) envs.ikitEnv
          (cliPollPkKitPlaced A x.F pid₀ σ) envs.pkKitEnv
          (cliPollKpkKitPlaced A x.F kpkId₀ spkId₀ kbk₀ σ) envs.kpkKitEnv
          StoresGhost.opened.sessions StoresGhost.opened.identity
          StoresGhost.opened.oneTime StoresGhost.opened.kyber
          x.peer.val x.msg.identityKey m.kpkId m.spkId x.msg.baseKey m.opkId
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
  let ReadEnv := ReadFileRuleEnvFixed cliIo.rd
  let σ := cliKitStk cliRunBudgets
  let envs := w4r2_cliPollStageP4Prev1SeqFreeEnvsAt A cliRunBudgets x.F x.peer pid₀
    kpkId₀ spkId₀ kbk₀ ReadEnv
  have hp1Sub : ∀ e,
      CliStageP1OkEnv (A := A) cliRunBudgets ReadEnv dpx_deserEnv x e →
      W4BinaryStageP1OkEnvAllFixed cliIo.rd x.F x.peer x.msg.identityKey e :=
    fun _ he => dpx_cliStageP1OkEnv_sub_w4StageP1OkAllFixed he
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
      StageP4Prev1Env
        (cliPollSessPrev1KitPlaced A x.F x.peer σ) envs.opsEnv
        (cliPollIdKitPlaced A x.F x.peer σ) envs.ikitEnv
        (cliPollPkKitPlaced A x.F pid₀ σ) envs.pkKitEnv
        (cliPollKpkKitPlaced A x.F kpkId₀ spkId₀ kbk₀ σ) envs.kpkKitEnv
        StoresGhost.opened.sessions StoresGhost.opened.identity
        StoresGhost.opened.oneTime StoresGhost.opened.kyber
        x.peer.val x.msg.identityKey m.kpkId m.spkId x.msg.baseKey m.opkId
        G' ses' enc_prev1 e →
      W4BinaryStageP4PathCWideEnvAllFixed m.opkId.isSome cliIo.rd x.F x.peer x.msg.identityKey
        m.kpkId m.spkId (m.opkId.getD 0#32) x.msg.baseKey G' ses' enc_prev1 e :=
    fun _ he => dpx_stageP4Prev1SeqFree_sub_w4StageP4PathCAllFixed he
  have hTdDom : W4TryDecryptPathACDomCmkOf W.C.F W.Q.K maxCt tdCall :=
    w4pb_armc_tdPathACDom_of_stageP3 W x G₁ ses0.state whisperG hCloneDom.rc_nil htop hct
  have hP2Case :
      ∃ x_spqr : InitialStateGhost,
        x_spqr.p.authKey.length ≤ 32 ∧
        SeqEnv (W4BinaryStageP1OkEnvAllFixed cliIo.rd x.F x.peer x.msg.identityKey)
          (SeqEnv
            (OptStageEnv
              (W4BinaryStageP2PathCWideEnvAllFixed recG ses0.state (fun _ => False)
                W4TrialDecCmkEnv (TrialTargetEnv W.C W.Q.K) W4TrialDropCmkEnv
                ([] : List W4ArchivedTrialCmk) w4pb_armc_noneRecordGhost r_arch
                m.opkId.isSome cliIo.rd x.F m.spkId m.kpkId (m.opkId.getD 0#32)
                W.C.F w4pb_armc_dummyReserve x_spqr))
            (SeqEnv
              (OptStageEnv
                (W4StageP3Prev1WideEnvOf VerNeTightTopEnv W4CloneACDomEnv
                  (TdTargetEnv W.C W.Q.K tdCall.a) enc_prev1))
              (OptStageEnv
                (W4BinaryStageP4PathCWideEnvAllFixed m.opkId.isSome cliIo.rd x.F x.peer
                  x.msg.identityKey m.kpkId m.spkId (m.opkId.getD 0#32) x.msg.baseKey
                  G' ses' enc_prev1)))) evs := by
    rcases h with h123 | ⟨e123, e4, rfl, h123, hp4⟩
    · rcases h123 with h12 | ⟨e12, e3, rfl, h12, hp3⟩
      · rcases h12 with hp1 | ⟨e1, e2, rfl, hp1, hp2⟩
        · exact ⟨w4pb_armc_dummyInitialStateGhost, w4pb_armc_dummyInitialStateGhost_key,
            Or.inl (hp1Sub _ hp1)⟩
        · obtain ⟨m₂, sess, x_spqr, hm₂, hsess, _hver, hlen, hp2f⟩ :=
            h7w_p2OverOk_sub_w4StageP2PathCAllFixed A X W recG ses0.state
              (fun _ => False) W4TrialDecCmkEnv (TrialTargetEnv W.C W.Q.K) W4TrialDropCmkEnv
              ([] : List W4ArchivedTrialCmk) w4pb_armc_noneRecordGhost w4pb_armc_dummyReserve hp2
          cases Option.some.inj (hm₂.symm.trans hm_arm)
          cases Option.some.inj (hsess.symm.trans hcur)
          exact ⟨x_spqr, hlen,
            Or.inr ⟨e1, e2, rfl, hp1Sub _ hp1, Or.inl (Or.inr (hp2f r_arch rfl))⟩⟩
      · rcases h12 with hp1 | ⟨e1, e2, rfl, hp1, hp2⟩
        · exact ⟨w4pb_armc_dummyInitialStateGhost, w4pb_armc_dummyInitialStateGhost_key,
            Or.inr ⟨e12, e3, rfl, hp1Sub _ hp1,
              Or.inr ⟨[], e3, rfl, w4pb_armc_optStageEnv_nil _, Or.inl (Or.inr (hp3Sub _ hp3))⟩⟩⟩
        · obtain ⟨m₂, sess, x_spqr, hm₂, hsess, _hver, hlen, hp2f⟩ :=
            h7w_p2OverOk_sub_w4StageP2PathCAllFixed A X W recG ses0.state
              (fun _ => False) W4TrialDecCmkEnv (TrialTargetEnv W.C W.Q.K) W4TrialDropCmkEnv
              ([] : List W4ArchivedTrialCmk) w4pb_armc_noneRecordGhost w4pb_armc_dummyReserve hp2
          cases Option.some.inj (hm₂.symm.trans hm_arm)
          cases Option.some.inj (hsess.symm.trans hcur)
          exact ⟨x_spqr, hlen, Or.inr ⟨e1, e2 ++ e3, List.append_assoc e1 e2 e3, hp1Sub _ hp1,
            Or.inr ⟨e2, e3, rfl, Or.inr (hp2f r_arch rfl), Or.inl (Or.inr (hp3Sub _ hp3))⟩⟩⟩
    · rcases h123 with h12 | ⟨e12, e3, rfl, h12, hp3⟩
      · rcases h12 with hp1 | ⟨e1, e2, rfl, hp1, hp2⟩
        · exact ⟨w4pb_armc_dummyInitialStateGhost, w4pb_armc_dummyInitialStateGhost_key,
            Or.inr ⟨e123, e4, rfl, hp1Sub _ hp1,
              Or.inr ⟨[], e4, rfl, w4pb_armc_optStageEnv_nil _,
                Or.inr ⟨[], e4, rfl, w4pb_armc_optStageEnv_nil _, Or.inr (hp4Sub _ hp4)⟩⟩⟩⟩
        · obtain ⟨m₂, sess, x_spqr, hm₂, hsess, _hver, hlen, hp2f⟩ :=
            h7w_p2OverOk_sub_w4StageP2PathCAllFixed A X W recG ses0.state
              (fun _ => False) W4TrialDecCmkEnv (TrialTargetEnv W.C W.Q.K) W4TrialDropCmkEnv
              ([] : List W4ArchivedTrialCmk) w4pb_armc_noneRecordGhost w4pb_armc_dummyReserve hp2
          cases Option.some.inj (hm₂.symm.trans hm_arm)
          cases Option.some.inj (hsess.symm.trans hcur)
          exact ⟨x_spqr, hlen, Or.inr ⟨e1, e2 ++ e4, List.append_assoc e1 e2 e4, hp1Sub _ hp1,
            Or.inr ⟨e2, e4, rfl, Or.inr (hp2f r_arch rfl),
              Or.inr ⟨[], e4, rfl, w4pb_armc_optStageEnv_nil _, Or.inr (hp4Sub _ hp4)⟩⟩⟩⟩
      · rcases h12 with hp1 | ⟨e1, e2, rfl, hp1, hp2⟩
        · exact ⟨w4pb_armc_dummyInitialStateGhost, w4pb_armc_dummyInitialStateGhost_key,
            Or.inr ⟨e12, e3 ++ e4, List.append_assoc e12 e3 e4, hp1Sub _ hp1,
              Or.inr ⟨[], e3 ++ e4, rfl, w4pb_armc_optStageEnv_nil _,
                Or.inr ⟨e3, e4, rfl, Or.inr (hp3Sub _ hp3), Or.inr (hp4Sub _ hp4)⟩⟩⟩⟩
        · obtain ⟨m₂, sess, x_spqr, hm₂, hsess, _hver, hlen, hp2f⟩ :=
            h7w_p2OverOk_sub_w4StageP2PathCAllFixed A X W recG ses0.state
              (fun _ => False) W4TrialDecCmkEnv (TrialTargetEnv W.C W.Q.K) W4TrialDropCmkEnv
              ([] : List W4ArchivedTrialCmk) w4pb_armc_noneRecordGhost w4pb_armc_dummyReserve hp2
          cases Option.some.inj (hm₂.symm.trans hm_arm)
          cases Option.some.inj (hsess.symm.trans hcur)
          have hassoc : ((e1 ++ e2) ++ e3) ++ e4 = e1 ++ (e2 ++ (e3 ++ e4)) := by
            simp only [List.append_assoc]
          exact ⟨x_spqr, hlen, Or.inr ⟨e1, e2 ++ (e3 ++ e4), hassoc, hp1Sub _ hp1,
            Or.inr ⟨e2, e3 ++ e4, rfl, Or.inr (hp2f r_arch rfl),
              Or.inr ⟨e3, e4, rfl, Or.inr (hp3Sub _ hp3), Or.inr (hp4Sub _ hp4)⟩⟩⟩⟩
  obtain ⟨x_spqr, hlen, hChain⟩ := hP2Case
  exact ⟨w4pb_armc_mkWitnessParams W x m.opkId.isSome m.spkId m.kpkId (m.opkId.getD 0#32)
      x_spqr recG ses0.state true tdCall r_arch G' ses' enc_prev1,
    w4pb_armc_mkWitnessParams_dom W x m.opkId.isSome m.spkId m.kpkId (m.opkId.getD 0#32)
      x_spqr recG ses0.state true tdCall r_arch G' ses' enc_prev1
      hlen hCap hOut1Post (fun _ => hTdDom),
    rfl, rfl,
    Or.inr hChain⟩

/-- Embeds the Path-C (`Over`) disjunct of `W4r2PollCustomP3GvSeqFreeEnv` into `realCliDecPkBinaryWideSlotEnvCmkDom0'Fixed`. -/
theorem w4pb_armC_sub_dom0' [LibsignalPlacement]
    (A : RustAlloc) (X : UnreachedPqxdhPrimitives) (W : CliHooks)
    (g : DecPkGhost) (evs : List AllocEvent)
    (hfPeer : FilesOkPeer scopeIn g.F g.peer.val)
    (hdecOk : DecPkOkD2c ⟨W.C, W.Q⟩ scopeIn g.F g.peer.val g.me.val g.msg)
    (hTight : PeerSpqrStateTight640 W.C.F W.Q.K g.F g.peer.val)
    (hPrev0 : SessionGetPrev0Guard g.F g.peer.val)
    (h :
      let σ := cliKitStk cliRunBudgets
      let pid := pmPreKeyId g.msg
      let kbk := g.msg.baseKey
      let ReadEnv := ReadFileRuleEnvFixed cliIo.rd
      let P1 := CliStageP1OkEnv (A := A) cliRunBudgets ReadEnv dpx_deserEnv g
      let P2OverErrEnv := dpx_p2OverErrEnv A X W
      let P2OverOkEnv := dpx_p2OverOkEnv A X W
      let tdEnvW := w4s2_TryDecryptTopStateGuardedEnv W
      ∃ (r : SessionRecord (List (BitVec 8))) (s_old : Session (List (BitVec 8))),
        loadRec scopeIn g.F g.peer.val = .ok (some r) ∧
        r.currentSession = some s_old ∧
        ¬ SessMatchesPm s_old g.msg ∧
        StoresGhost.opened.identity.trusted cliIo.rd g.F g.peer.val g.msg.identityKey = .ok true ∧
        (SeqEnv P1 (StageP2OverEnv P2OverErrEnv P2OverOkEnv g r) evs ∨
         ∃ (m : PreKeyMessageFields) (i : SignalMessage) (k : ResponderPreKeySecrets)
           (kp : IdentityKeyPair) (reg : BitVec 32) (dk : SignalPqxdh.DRKey)
           (recG : SessionGhost) (whisperG : SignalMessageGhost),
           g.msg = pmOfE m i ∧
           SignalMessage.tryFrom protoSignalCodec m.inner = .ok i ∧
           pkStoreKeys g.F m = some k ∧
           StoresGhost.opened.identity.keyPair cliIo.rd g.F = .ok kp ∧
           StoresGhost.opened.identity.regId cliIo.rd g.F = .ok reg ∧
           SignalPqxdh.Model.acceptKeys (modelPrims X ⟨W.C, W.Q⟩)
             (acceptInput ⟨W.C, W.Q⟩ ⟨kp.privateKey.bytes, reg⟩ k m) = some dk ∧
           W4r2SessionGhostValid recG
             (pathAInitSession ⟨W.C, W.Q⟩ ⟨kp.privateKey.bytes, reg⟩ k m dk) ∧
           let st0 := pathAInitState ⟨W.C, W.Q⟩ ⟨kp.privateKey.bytes, reg⟩ k m dk
           let enc_old := encSession (clearPending s_old)
           ((∃ G₁, CloneRel recG G₁ ∧
               SeqEnv (SeqEnv P1 (P2OverOkEnv g r))
                 (StageP3ErrM3Env tdEnvW recG G₁ st0 g.peer g.me whisperG g.msg.message g.coins)
                 evs) ∨
            SeqEnv (SeqEnv P1 (P2OverOkEnv g r))
              (StageP3VerNePrev1Env VerNeTightTopRawEnv recG st0 enc_old) evs ∨
            ∃ G₁ G' pt,
              CloneRel recG G₁ ∧
              G₁.AfterTryDecrypt true G' ∧
              (genP3S5Model W.C W.Q.K g.peer g.me g.msg.message g.coins st0).1 = .ok pt ∧
              let envs := w4r2_cliPollStageP4Prev1SeqFreeEnvsAt A cliRunBudgets g.F g.peer pid
                m.kpkId m.spkId kbk ReadEnv
              let ses' : Session (List (BitVec 8)) :=
                { pathAInitSession ⟨W.C, W.Q⟩ ⟨kp.privateKey.bytes, reg⟩ k m dk with
                  state := (genP3S5Model W.C W.Q.K g.peer g.me g.msg.message g.coins st0).2
                  pendingPreKey := none
                  pendingKyberPreKey := none }
              W4r2SessionGhostValid G' ses' ∧
              SeqEnv
                (SeqEnv (SeqEnv P1 (P2OverOkEnv g r))
                  (StageP3OkPrefixM3Env tdEnvW recG G₁ st0
                    g.peer g.me whisperG g.msg.message g.coins))
                (StageP4Prev1Env
                  (cliPollSessPrev1KitPlaced A g.F g.peer σ) envs.opsEnv
                  (cliPollIdKitPlaced A g.F g.peer σ) envs.ikitEnv
                  (cliPollPkKitPlaced A g.F pid σ) envs.pkKitEnv
                  (cliPollKpkKitPlaced A g.F m.kpkId m.spkId kbk σ) envs.kpkKitEnv
                  StoresGhost.opened.sessions StoresGhost.opened.identity
                  StoresGhost.opened.oneTime StoresGhost.opened.kyber
                  g.peer.val g.msg.identityKey m.kpkId m.spkId kbk m.opkId G' ses' enc_old)
                evs))) :
    realCliDecPkBinaryWideSlotEnvCmkDom0'Fixed w4c_repairedStatesRecvEnvFam X W g evs := by
  have _ : True := by have := hdecOk; have := hTight; have := hPrev0; trivial
  have hw : ∃ w4 : W4BinaryRecvPrekeyParamsCmk,
      H7wCallSiteDomOut1
        (PostBobPrev1Dom w4PostBobPqCap 2097152 postBobTotalPrev1Cap286K)
        W.C W.Q.K g.msg.message.ciphertext.length g.peer.val g.F w4.base ∧
      w4.remoteIdKey = g.msg.identityKey ∧
      w4.baseKey = g.msg.baseKey ∧
      H7wOverSlotEnvAllFixedOf
        (W4FailedTdCancelCmkSrEnvOf w4c_repairedStatesRecvEnvFam CmkLoopAdvanceEvs
          w4c_defaultDecodeMaxOps)
        (W4TrialRunWideCmkSrEnvOf w4c_repairedStatesRecvEnvFam CmkLoopAdvanceEvs
          w4c_defaultDecodeMaxOps)
        (w4c_TryDecryptCliLinkedSrEnvOf w4c_repairedStatesRecvEnvFam CmkLoopAdvanceEvs
          w4c_defaultDecodeMaxOps) w4 evs := by
    dsimp only [] at h
    obtain ⟨r, s_old, hload, hcur, _hNotMatch, _hTrusted, hArms⟩ := h
    have hr_cap : (encodeRecord r).length ≤ 2097152 :=
      w4pb_armc_loadRec_encodeRecord_le_cap hfPeer hload
    have hCap : (encodeRecord ⟨some (clearPending s_old)⟩).length ≤ 2097152 :=
      Nat.le_trans (h7l23_encodeRecord_clearPending_le_encodeRecord hcur (by omega)) hr_cap
    have hprevEnc : (encSession (clearPending s_old)).length ≤ 2097152 :=
      Nat.le_trans (h7l23_encSession_clearPending_le_encodeRecord r s_old hcur) hr_cap
    rcases hArms with hp2 | ⟨m, i, k, kp, reg, dk, recG, whisperG,
        hpm, hi, _hk, _hkp, _hreg, _hacc, hgv, hSubArms⟩
    · obtain ⟨G_idle, ses_idle, hOut1Idle⟩ := postBobPrev1Dom_idle_exists
      exact w4pb_armc_witness_p2Over A X W g r s_old G_idle ses_idle hcur hCap hOut1Idle hp2
    · let P_pe : PEParams := ⟨W.C, W.Q⟩
      let me_id : LocalIdentity := ⟨kp.privateKey.bytes, reg⟩
      have htdSub : ∀ a e,
          TopStateTight W.C.F W.Q.K a.st.pqRatchetState →
          a.msg.ciphertext.length ≤ g.msg.message.ciphertext.length →
          w4s2_TryDecryptTopStateGuardedEnv W a e →
          w4c_TryDecryptCliLinkedSrEnvOf w4c_repairedStatesRecvEnvFam CmkLoopAdvanceEvs
            w4c_defaultDecodeMaxOps W.C W.Q.K a e :=
        fun a e hTop _ htd => w4pb_armc_tdSub W a e hTop htd
      rcases hSubArms with ⟨G₁, _hcl, hp3Err⟩ | hp3VerNe | ⟨G₁, G', pt, _hcl, _haft, hok, hgv', hp4⟩
      · exact w4pb_armc_witness_p3ErrM3 A X W htdSub g r s_old recG G₁
          (pathAInitSession P_pe me_id k m dk) whisperG
          recG (pathAInitSession P_pe me_id k m dk)
          hcur hCap
          (h7l45r_pathAInit_freshBobCloneDom P_pe me_id k m dk recG hgv)
          (h7l45r_pathAInit_topStateTight P_pe me_id k m dk)
          (Nat.le_refl _)
          (w4pb_armc_freshBob_postBobPrev1Dom P_pe me_id k m dk recG hgv (Nat.zero_le _))
          (w4pb_armc_freshBob_postBobPrev1Dom P_pe me_id k m dk recG hgv hprevEnc)
          hp3Err
      · exact w4pb_armc_witness_p3VerNe
          (tdEnv := w4s2_TryDecryptTopStateGuardedEnv)
          A X W g r s_old recG
          (pathAInitSession P_pe me_id k m dk)
          recG (pathAInitSession P_pe me_id k m dk)
          hcur hCap
          (h7l45r_pathAInit_freshBobCloneDom P_pe me_id k m dk recG hgv)
          (w4pb_armc_freshBob_postBobPrev1Dom P_pe me_id k m dk recG hgv (Nat.zero_le _))
          (w4pb_armc_freshBob_postBobPrev1Dom P_pe me_id k m dk recG hgv hprevEnc)
          hp3VerNe
      · have hm_arm : pkToE? g.msg = some m := hpm ▸ pkToE?_pmOfE m i hi
        have hOut1Post :=
          postBobPrev1Dom_of_arm4 P_pe me_id k m dk g.peer g.me g.msg.message g.coins
            hok hgv' hprevEnc
        exact w4pb_armc_witness_p4Prev1 A X W htdSub g r s_old m recG G₁ G'
          (pathAInitSession P_pe me_id k m dk)
          { pathAInitSession P_pe me_id k m dk with
            state := (genP3S5Model W.C W.Q.K g.peer g.me g.msg.message g.coins
              (pathAInitState P_pe me_id k m dk)).2
            pendingPreKey := none
            pendingKyberPreKey := none }
          whisperG
          hcur hm_arm hCap
          (h7l45r_pathAInit_freshBobCloneDom P_pe me_id k m dk recG hgv)
          (h7l45r_pathAInit_topStateTight P_pe me_id k m dk)
          (Nat.le_refl _) hOut1Post hp4
  obtain ⟨w4, hdom, hrem, hbk, hall⟩ := hw
  exact ⟨w4, w4pb_armc_toCallSiteDomCmk0' hdom, hrem, hbk, w4pb_armc_overSlotEnv_to_allFixed hall⟩

end LibsignalBinary.Proofs.SpecLemmas.SignalSession.Hole3W4DecPkArmC

