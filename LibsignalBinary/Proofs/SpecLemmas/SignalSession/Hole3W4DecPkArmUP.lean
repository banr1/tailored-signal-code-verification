/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.PeakBudget.CliDpPollTrustedWideBridgeX
public import LibsignalBinary.Proofs.PeakBudget.W4PostBobPrev1Dom
public import LibsignalBinary.Proofs.PeakBudget.W4RecvPrekeyCmkDom0
public import LibsignalBinary.Proofs.SignalSession.Cli.F3.HRead.ReadFileBudgetPlaced
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.ClosureTrustedP1PlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.ClosureUntrustedPlacedBudget
import LibsignalBinary.Proofs.PeakBudget.W4PostBobPrev1DomIdle

/-!
# Untrusted and Stage-P1-Ok Envelope Inclusions for Post-Bob `decryptPrekey` (`W4`)

Embeds the `CliDpPollUntrustedEnv` and `CliStageP1OkEnv` disjuncts of
`W4r2PollCustomP3GvSeqFreeEnv` into `realCliDecPkBinaryWideSlotEnvCmkDom0'Fixed`.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000

namespace LibsignalBinary.Proofs.SpecLemmas.SignalSession.Hole3W4DecPkArmUP

open CryptoGames.LibsignalSession (SessionState)
open CryptoGames.LibsignalSessionApi (Session SessionRecord)
open CryptoVerification (LibsignalPlacement)
open CryptoVerification.E2E (UnreachedPqxdhPrimitives)
open CryptoVerification.E2E.Record (encodeRecord)
open CryptoVerification.LibsignalPublicApiRepr (RecordGhost)
open CryptoVerification.LibsignalTripleRatchet (DoReserveCall reserveCap)
open CryptoVerification.LibsignalTripleRatchetRepr (SessionGhost SignalMessageGhost)
open CryptoVerification.RustHeap (RustAlloc)
open CryptoVerification.SignalSession (CliHooks)
open CryptoVerification.SignalSession.Cli (StoresGhost)
open CryptoVerification.SignalSession.Cli.MainHops (cliIo cliRunBudgets)
open CryptoVerification.SignalSession.Cli.RunCompose (DecPkGhost)
open CryptoVerification.SpqrV1.Top.InitialState (InitialStateGhost)
open LibsignalBinary.Heap (AllocEvent)
open LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Matched.M3PrevCapPlacedBudget
  (stageP3M3TryDecryptEnvArgs)
open LibsignalBinary.Proofs.ConsumeMessageKey.AdvanceEpilogueProofs.FetchBudget (CmkLoopAdvanceEvs)
open LibsignalBinary.Proofs.PeakBudget.CliDpPollTrustedWideBridgeX
  (dpx_cliDpPollUntrustedEnv_sub_w4StageP1UntrustedAllFixed
   dpx_cliStageP1OkEnv_sub_w4StageP1OkAllFixed dpx_deserEnv)
open LibsignalBinary.Proofs.PeakBudget.W4PostBobPrev1Dom
  (PostBobPrev1Dom W4BinaryCallSiteDomCmk0' realCliDecPkBinaryWideSlotEnvCmkDom0'Fixed
   realCliDecPkBinaryWideSlotEnvCmkDom0'FixedOf)
open LibsignalBinary.Proofs.PeakBudget.W4PostBobPrev1DomIdle (postBobPrev1Dom_idle_exists)
open LibsignalBinary.Proofs.PeakBudget.W4RecvPrekeyCmkDom0TdAux
  (W4StatesRecvEnv w4c_repairedStatesRecvEnvFam)
open LibsignalBinary.Proofs.PeakBudget.W4RecvPrekeyCmkSlot
  (W4BinaryRecvPrekeyParamsCmk W4FailedTryDecryptCallCmk W4LoopAdvEnv W4TryDecryptCallCmk
   w4c_defaultDecodeMaxOps)
open LibsignalBinary.Proofs.SignalSession.Cli.F3.HRead.ReadFileBudgetPlaced (ReadFileRuleEnvFixed)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.ClosureTrustedP1PlacedBudget
  (CliStageP1OkEnv)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.ClosureUntrustedPlacedBudget
  (CliDpPollUntrustedEnv)

private def w4pb_dummyReserve : DoReserveCall :=
  ⟨0#64, 0#64, 0#64, [], 0⟩

private theorem w4pb_dummyReserve_old : w4pb_dummyReserve.cap.toNat ≤ 4096 := by
  decide

private theorem w4pb_dummyReserve_new :
    reserveCap w4pb_dummyReserve.cap.toNat w4pb_dummyReserve.bs.length
      w4pb_dummyReserve.additional ≤ 4096 := by
  decide

private def w4pb_dummyInitialStateGhost : InitialStateGhost :=
  ⟨0#64, 0#64, 0#64, { direction := .b2a, version := .v1, minVersion := .v1, authKey := [] }⟩

private theorem w4pb_dummyInitialStateGhost_key :
    w4pb_dummyInitialStateGhost.p.authKey.length ≤ 32 := by
  decide

private def w4pb_noneRecordGhost : RecordGhost :=
  ⟨0#64, 0#64, none⟩

private def w4pb_emptySessionRecord : SessionRecord (List (BitVec 8)) :=
  ⟨none⟩

private theorem w4pb_emptySessionRecord_enc :
    (encodeRecord w4pb_emptySessionRecord).length ≤ 2097152 := by
  decide

private def w4pb_dummyWhisperGhost : SignalMessageGhost :=
  ⟨0#64, 0#64, 0#64, 0#64, 0#64⟩

private def w4pb_dummyTdCall
    (G_d : SessionGhost) (st_d : SessionState (List (BitVec 8))) (g : DecPkGhost) :
    W4TryDecryptCallCmk :=
  ⟨stageP3M3TryDecryptEnvArgs G_d st_d g.peer g.me w4pb_dummyWhisperGhost g.msg.message g.coins⟩

private def w4pb_dummyFailedTdCall
    (G_d : SessionGhost) (st_d : SessionState (List (BitVec 8))) (g : DecPkGhost) :
    W4FailedTryDecryptCallCmk :=
  ⟨w4pb_dummyTdCall G_d st_d g, []⟩

private def w4pb_idleWitnessParams
    (W : CliHooks) (g : DecPkGhost)
    (G_idle : SessionGhost) (ses_idle : Session (List (BitVec 8))) :
    W4BinaryRecvPrekeyParamsCmk where
  base := {
    C := W.C
    K := W.Q.K
    rd := cliIo.rd
    files := g.F
    kpkDir := StoresGhost.opened.kyber.oneTime
    peer := g.peer
    hasOpk := false
    spkId := 0#32
    kpkId := 0#32
    opkId := 0#32
    kpkMarkName := []
    ownKeyName := []
    ownRegName := []
    x_res := w4pb_dummyReserve
    x_spqr := w4pb_dummyInitialStateGhost
    hasCurSession := false
    G_cur := G_idle
    st_cur := ses_idle.state
    fc_cur := w4pb_dummyFailedTdCall G_idle ses_idle.state g
    archivedTrials := []
    isPathB := false
    td_B := w4pb_dummyTdCall G_idle ses_idle.state g
    isPathAC := false
    td_AC := w4pb_dummyTdCall G_idle ses_idle.state g
    g_arch := w4pb_noneRecordGhost
    r_arch := w4pb_emptySessionRecord
    g_out0 := w4pb_noneRecordGhost
    r_out0 := w4pb_emptySessionRecord
    G_out1 := G_idle
    sess_out1 := ses_idle
    enc_prev1 := []
  }
  remoteIdKey := g.msg.identityKey
  baseKey := g.msg.baseKey

private theorem w4pb_idleWitnessParams_dom0'
    {maxCt : Nat} (W : CliHooks) (g : DecPkGhost)
    (G_idle : SessionGhost) (ses_idle : Session (List (BitVec 8)))
    (hOut1 : PostBobPrev1Dom 286196 2097152 2469364 G_idle ses_idle []) :
    W4BinaryCallSiteDomCmk0' W.C W.Q.K maxCt g.peer.val g.F
      (w4pb_idleWitnessParams W g G_idle ses_idle).base :=
  ⟨{ eq_C := rfl
     eq_K := rfl
     eq_rd := rfl
     eq_files := rfl
     eq_peerVal := rfl
     kpk_dir := Or.inl rfl
     ownKey_len := Nat.zero_le 64
     ownReg_len := Nat.zero_le 64
     kpkMark_len := Nat.zero_le 64
     res_old := w4pb_dummyReserve_old
     res_new := w4pb_dummyReserve_new
     spqr_key := w4pb_dummyInitialStateGhost_key
     cur_dom := Or.inl rfl
     arch_valid := fun _ _ hg _ => nomatch hg
     arch_enc := w4pb_emptySessionRecord_enc
     out0_valid := fun _ _ hg _ => nomatch hg
     out0_enc := w4pb_emptySessionRecord_enc
     out1_postBob := hOut1
     trials_len4 := Nat.zero_le 4
     cur_fail_dom := fun h => Bool.noConfusion h
     trials_dom := fun _ hy => nomatch hy
     tdB_dom := fun h => Bool.noConfusion h
     tdAC_dom := fun h => Bool.noConfusion h },
   rfl⟩

/-- `(SR, LoopAdvEnv, maxOps)`-parametric inclusion of the untrusted arm into `realCliDecPkBinaryWideSlotEnvCmkDom0'FixedOf`. -/
theorem w4pb_armUntrusted_sub_dom0'Of [LibsignalPlacement]
    (SR : W4StatesRecvEnv) (LoopAdvEnv : W4LoopAdvEnv) (maxOps : Nat)
    (A : RustAlloc) (X : UnreachedPqxdhPrimitives) (W : CliHooks)
    (g : DecPkGhost) (evs : List AllocEvent)
    (h : CliDpPollUntrustedEnv (A := A) cliRunBudgets
      (ReadFileRuleEnvFixed cliIo.rd) dpx_deserEnv g evs) :
    realCliDecPkBinaryWideSlotEnvCmkDom0'FixedOf SR LoopAdvEnv maxOps X W g evs := by
  obtain ⟨G_idle, ses_idle, hOut1⟩ := postBobPrev1Dom_idle_exists
  exact ⟨w4pb_idleWitnessParams W g G_idle ses_idle,
    w4pb_idleWitnessParams_dom0' W g G_idle ses_idle hOut1,
    rfl, rfl,
    Or.inr (Or.inl (Or.inl (dpx_cliDpPollUntrustedEnv_sub_w4StageP1UntrustedAllFixed h)))⟩

/-- `(SR, LoopAdvEnv, maxOps)`-parametric inclusion of the Stage-P1-Ok arm into `realCliDecPkBinaryWideSlotEnvCmkDom0'FixedOf`. -/
theorem w4pb_armP1Ok_sub_dom0'Of [LibsignalPlacement]
    (SR : W4StatesRecvEnv) (LoopAdvEnv : W4LoopAdvEnv) (maxOps : Nat)
    (A : RustAlloc) (X : UnreachedPqxdhPrimitives) (W : CliHooks)
    (g : DecPkGhost) (evs : List AllocEvent)
    (h : CliStageP1OkEnv (A := A) cliRunBudgets
      (ReadFileRuleEnvFixed cliIo.rd) dpx_deserEnv g evs) :
    realCliDecPkBinaryWideSlotEnvCmkDom0'FixedOf SR LoopAdvEnv maxOps X W g evs := by
  obtain ⟨G_idle, ses_idle, hOut1⟩ := postBobPrev1Dom_idle_exists
  exact ⟨w4pb_idleWitnessParams W g G_idle ses_idle,
    w4pb_idleWitnessParams_dom0' W g G_idle ses_idle hOut1,
    rfl, rfl,
    Or.inr (Or.inl (Or.inr (Or.inl (Or.inl (dpx_cliStageP1OkEnv_sub_w4StageP1OkAllFixed h)))))⟩

theorem w4pb_armUntrusted_sub_dom0' [LibsignalPlacement]
    (A : RustAlloc) (X : UnreachedPqxdhPrimitives) (W : CliHooks)
    (g : DecPkGhost) (evs : List AllocEvent)
    (h : CliDpPollUntrustedEnv (A := A) cliRunBudgets
      (ReadFileRuleEnvFixed cliIo.rd) dpx_deserEnv g evs) :
    realCliDecPkBinaryWideSlotEnvCmkDom0'Fixed w4c_repairedStatesRecvEnvFam X W g evs :=
  w4pb_armUntrusted_sub_dom0'Of
    w4c_repairedStatesRecvEnvFam CmkLoopAdvanceEvs w4c_defaultDecodeMaxOps A X W g evs h

theorem w4pb_armP1Ok_sub_dom0' [LibsignalPlacement]
    (A : RustAlloc) (X : UnreachedPqxdhPrimitives) (W : CliHooks)
    (g : DecPkGhost) (evs : List AllocEvent)
    (h : CliStageP1OkEnv (A := A) cliRunBudgets
      (ReadFileRuleEnvFixed cliIo.rd) dpx_deserEnv g evs) :
    realCliDecPkBinaryWideSlotEnvCmkDom0'Fixed w4c_repairedStatesRecvEnvFam X W g evs :=
  w4pb_armP1Ok_sub_dom0'Of
    w4c_repairedStatesRecvEnvFam CmkLoopAdvanceEvs w4c_defaultDecodeMaxOps A X W g evs h

/-- Embeds the untrusted and Stage-P1-Ok disjuncts of `W4r2PollCustomP3GvSeqFreeEnv` into `realCliDecPkBinaryWideSlotEnvCmkDom0'Fixed`. -/
theorem w4pb_armUP_sub_dom0' [LibsignalPlacement]
    (A : RustAlloc) (X : UnreachedPqxdhPrimitives) (W : CliHooks)
    (g : DecPkGhost) (evs : List AllocEvent)
    (h :
      CliDpPollUntrustedEnv (A := A) cliRunBudgets
        (ReadFileRuleEnvFixed cliIo.rd) dpx_deserEnv g evs ∨
      CliStageP1OkEnv (A := A) cliRunBudgets
        (ReadFileRuleEnvFixed cliIo.rd) dpx_deserEnv g evs) :
    realCliDecPkBinaryWideSlotEnvCmkDom0'Fixed w4c_repairedStatesRecvEnvFam X W g evs := by
  rcases h with hUntrusted | hP1
  · exact w4pb_armUntrusted_sub_dom0' A X W g evs hUntrusted
  · exact w4pb_armP1Ok_sub_dom0' A X W g evs hP1

end LibsignalBinary.Proofs.SpecLemmas.SignalSession.Hole3W4DecPkArmUP
