/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Symbolic.Proofs.Swarm.CREF.RecvPrekeyProm.Tie.BlockReadPure
import DY.ALaCarte.Basic
import DY.Trace.Basic
import DY.Trace.Monad
import DY.Trace.Manipulation
import DY.Trace.BaseAttackerKnowledge
import DY.Actions.Network
import DY.Actions.PersistentLocalState
import DY.Actions.PersistentGlobalState
import DY.Actions.ProtocolEvent
import DY.Actions.Random
public import Symbolic.Proofs.Refinement.RecordBytesBridge
public import Symbolic.Proofs.Swarm.TRREF.GrowthRecvPure.BranchesBPure
import Symbolic.Proofs.Swarm.CREF.Cli.Rpk.ByteFreshInstallTRPure
import Symbolic.Proofs.Swarm.CREF.Cli.Rpk.RecRecvRkOkRatchetDHPure
import Symbolic.Proofs.Swarm.CREF.Cli.Rpk.SkippedKeyRunInvPure
import Symbolic.Proofs.Swarm.CREF.Prelude
import Symbolic.Proofs.Swarm.CREF.RecvPrekeyProm.HistOpkPureA
import Symbolic.Proofs.Swarm.CREF.RecvPrekeyProm.HxplRep
import Symbolic.Proofs.Swarm.CREF.TR.FreshSigma
import Symbolic.Proofs.Swarm.CREF.TROpen
import Symbolic.Proofs.Swarm.CREF.Xpl.NoRatchet
import Symbolic.Proofs.Swarm.CREF.Xpl.RatchetHit
import Symbolic.DYBridge.DY.ALaCarte.Basic
import Symbolic.DYBridge.DY.Trace.Basic
import Symbolic.DYBridge.DY.Trace.Monad
import Symbolic.DYBridge.DY.Trace.Manipulation
import Symbolic.DYBridge.DY.Trace.BaseAttackerKnowledge
import Symbolic.DYBridge.DY.Actions.Network
import Symbolic.DYBridge.DY.Actions.PersistentLocalState
import Symbolic.DYBridge.DY.Actions.PersistentGlobalState
import Symbolic.DYBridge.DY.Actions.ProtocolEvent
import Symbolic.DYBridge.DY.Actions.Random

/-!
# `CHist` and `SkippedInstallByteFresh` Preservation on Session Promotion

Proves `prom_recRecvRkOk_of_acceptOut`, `prom_skippedInstallByteFresh_step₂`, `prom_cHist_step`,
and `prom_histOK` across accepting session-promotion calls.
-/

@[expose] public section

set_option autoImplicit false

cref_hide_foreign_instances

namespace Symbolic.Swarm.CREF.CliPure

cref_open
cref_open_tr
open DY.Libsignal.HwEvents (MachineEvent StateAndMessage)
open CryptoProofLib.Refinement (ExternInterpretation)
open DY DY.Comparse DY.Literal DY.Libsignal
open DY.Libsignal.Refinement (ExternCryptoLawsHold)
open DY.Libsignal.TripleRatchet
open DY.Libsignal.PQXDH hiding kdfRk createChain x25519LowOrder
open DY.Libsignal.Composed
open DY.Libsignal.Composed.Refinement
open DY.Libsignal.HwEvents DY.Libsignal.Rust
open CryptoGames CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open CryptoVerification
open CryptoVerification.LibsignalProtoCodec (protoSignalCodec)
open CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchet.Seeds
open CryptoVerification.E2E.Record
open Proofs.libsignal.Hooks2 (cryptoOf')
open Proofs.libsignal.RngG.R3 Proofs.libsignal.RngG.CliPure.R3
open Proofs.libsignal.SR
open Swarm.Phase0WholeFunctionBridge (sessionToRecordRec sessionToSessionRec receiverChainToChainRec)
open Symbolic.Swarm.TRREF
open Symbolic.Swarm.CREF.TR (StateRel normPending)
open Symbolic.Swarm.CREF.CliPure.TR.CHistStep (RecRecvRkOk)
open Symbolic.Swarm.CREF.CliPure.TR.RecvDecStep
open Symbolic.Swarm.CREF.CliPure.RecvPrekeyProm
open Symbolic.Swarm.CREF.CliPure.RpkCli

attribute [local simp] ho_exec_pure_hw ho_exec_get_hw ho_exec_set_hw ho_exec_liftE_hw ho_exec_bind_hw

theorem prom_recRecvRkOk_of_acceptOut
    {interpretation : ExternInterpretation} {r : ProtocolSetup}
    {rec b : HwBytes} {mid : List MachineEvent} {sm : StateAndMessage}
    {pf : PreKeyFields} {sess sess' : Session (List (BitVec 8))}
    {coins : BitVec 256} {expected : Option (List (BitVec 8))} {pt : List (BitVec 8)}
    {rr₀ : RecordRec}
    (hEq : ExternCryptoLawsHold interpretation)
    (hrec : rec = recordBytes rr₀)
    (hok₀ : RecRecvRkOk rr₀)
    (hOut : PromBinAcceptOut interpretation r rec b mid sm pf sess sess' coins expected pt) :
    ∀ rec' : RecordRec, sm.state = recordBytes rec' → RecRecvRkOk rec' := by
  intro rec' hrec'
  have hnorm_in : normPending rr₀ = normPending (sessionToRecordRecPending sess) :=
    ho_prom_normPending_of_canonical_Q hrec hOut.hcan_in
  have hrc_in : rr₀.current.receiverChains = (sessionToRecordRec sess).current.receiverChains := by
    change (normPending rr₀).current.receiverChains =
      (normPending (sessionToRecordRecPending sess)).current.receiverChains
    exact congrArg (fun r : RecordRec => r.current.receiverChains) hnorm_in
  have hbytes_out : recordBytes (sessionToRecordRecPending sess') = sm.state :=
    recordBytes_of_promAcceptOut hOut
  have hnorm_out : normPending rec' = normPending (sessionToRecordRecPending sess') := by
    apply TR.recordBytes_injective
    rw [← hrec', hbytes_out]
  have hrc_out : rec'.current.receiverChains = (sessionToRecordRec sess').current.receiverChains := by
    change (normPending rec').current.receiverChains =
      (normPending (sessionToRecordRecPending sess')).current.receiverChains
    exact congrArg (fun r : RecordRec => r.current.receiverChains) hnorm_out
  rcases tryDecryptWithStateW_receiverChains_cases hOut.hexec with hsub | ⟨ck, r1, hDh, hchains⟩
  · intro rc hrc
    have hmem_out : rc ∈ (sessionToRecordRec sess').current.receiverChains := by
      rwa [← hrc_out]
    simp only [sessionToRecordRec, sessionToSessionRec, List.mem_map] at hmem_out
    obtain ⟨rc', hrc', rfl⟩ := hmem_out
    obtain ⟨rc₀, hrc₀, heq⟩ := hsub rc' hrc'
    have hmem_in : receiverChainToChainRec rc₀ ∈ rr₀.current.receiverChains := by
      rw [hrc_in]
      simp only [sessionToRecordRec, sessionToSessionRec, List.mem_map]
      exact ⟨rc₀, hrc₀, rfl⟩
    have hkey : (receiverChainToChainRec rc').senderRatchetKey =
        (receiverChainToChainRec rc₀).senderRatchetKey := by
      simp [receiverChainToChainRec, heq]
    rw [hkey]
    exact hok₀ (receiverChainToChainRec rc₀) hmem_in
  · refine TR.CHistStep.recRecvRkOk_of_subset_or_dhRatchetStep
      interpretation hEq (fun _ b => b) (fun _ b => b) (rec := rr₀) (rec' := rec') hok₀ hDh ?_
    intro k hk
    rw [hrc_out] at hk
    rw [hrc_in]
    simp only [sessionToRecordRec, sessionToSessionRec, List.map_map, List.mem_map] at hk ⊢
    obtain ⟨rc', hrc', rfl⟩ := hk
    rcases hchains rc' hrc' with ⟨rc₀, hrc₀, heq⟩ | hnew
    · left
      refine ⟨rc₀, hrc₀, ?_⟩
      simp [receiverChainToChainRec, heq]
    · right
      simp [receiverChainToChainRec, hnew]

/-! ## `SkippedInstallByteFresh` preservation -/

private theorem prom_accBlk_nil_no_rng (b pt : HwBytes) :
    ∀ e ∈ promAccBlk b [] pt, eventKind e ≠ .rng := by
  intro e he
  simp only [promAccBlk, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with rfl | rfl <;> simp [eventKind]

theorem prom_skippedInstallByteFresh_decrypt_noRatchet
    {interpretation : ExternInterpretation} {r₀ : ProtocolSetup} {S : OpaqueSymbolSemantics} {who : List Participant}
    {g : Ghost} {ms₀ pre post : List Move} {acc : List MachineEvent} {p : Participant}
    {stateIdx msgIdx pqIdx : Nat} {spqrMsgIdx : UInt32} {wrapped : Bool}
    {b pt : HwBytes}
    (hB : XplBlock interpretation r₀ S who g ms₀
      (pre ++ .decrypt p stateIdx msgIdx pqIdx spqrMsgIdx wrapped :: post) acc
      (promAccBlk b [] pt))
    (hpre : MovesFrom InvisibleNoEffect (runTraceMoves r₀ ms₀) pre)
    (hpost : MovesFrom InvisibleNoEffect
      ((Move.decrypt p stateIdx msgIdx pqIdx spqrMsgIdx wrapped).next
        (runMoves pre (runTraceMoves r₀ ms₀)).1) post)
    (hBF : TR.SkippedInstallByteFresh interpretation S g r₀ (ms₀ ++ pre)) :
    TR.SkippedInstallByteFresh interpretation S g r₀
      (ms₀ ++ pre ++ [.decrypt p stateIdx msgIdx pqIdx spqrMsgIdx wrapped]) := by
  let ms := ms₀ ++ pre
  have hmatch := prom_block_vis hB hpre hpost
  obtain ⟨st, t, msg, c, c', seed, spqr', key, pqSalt, ptTerm, hst, hmsg, hparse, hver, _hrcf,
      hfind, _hidx, hcons, hspqr, hpqSalt, hmac_eq, hdec, _hpt⟩ :=
    noRatchet_of_matched hmatch (prom_accBlk_nil_no_rng b pt) (prom_accBlk_has_accept b [] pt)
  let tr₀ := runTraceMoves r₀ ms
  let tr_k := tr₀.append (⟨key⟩ : Network.ExecEntryT)
  have htr_post :
      runTraceMoves r₀ (ms ++ [.decrypt p stateIdx msgIdx pqIdx spqrMsgIdx wrapped]) =
      TR.RecvDec.decTailTr tr_k p stateIdx st c c' msg.ratchetKey seed pqSalt ptTerm spqr' msg.counter := by
    rw [TR.runTrace_snoc]
    exact TR.RecvDec.decrypt_next_noRatchet_eq hst hmsg hparse hver hfind hcons hspqr hpqSalt hmac_eq hdec
  have htr_le : tr₀ ≤ tr_k := Trace.append_le tr₀ _
  have hno_new_pre : ∀ s' pk' n' seed' rIdx' src' i',
      tr_k.EventLoggedAt (TREvent.SkippedKeyStored s' pk' n' seed' rIdx' src') i' →
      tr₀.EventLoggedAt (TREvent.SkippedKeyStored s' pk' n' seed' rIdx' src') i' := by
    intro s' pk' n' seed' rIdx' src' i' hlog
    rw [Symbolic.DYBridge.DY.Trace.EventLoggedAt_eq_1] at hlog ⊢
    dsimp only [tr_k] at hlog
    rw [TR.RecvDec.at?_append_non_entry _ _ rfl] at hlog
    exact hlog
  have hst_pre : ∀ {p₀ : Participant} {st₀ : TRState} {src : Nat},
      src < tr₀.length →
      TR.TRStateStoredAt p₀ st₀ src
        (TR.RecvDec.decTailTr tr_k p stateIdx st c c' msg.ratchetKey seed pqSalt ptTerm spqr' msg.counter) →
      TR.TRStateStoredAt p₀ st₀ src tr₀ := by
    intro p₀ st₀ src hlt hst_tail
    have hle_tail : tr₀ ≤
        TR.RecvDec.decTailTr tr_k p stateIdx st c c' msg.ratchetKey seed pqSalt ptTerm spqr' msg.counter := by
      rw [← htr_post, TR.runTrace_snoc]
      exact TR.le_runMoves_fst [.decrypt p stateIdx msgIdx pqIdx spqrMsgIdx wrapped] tr₀
    exact TR.trStateStoredAt_of_le_of_lt hle_tail hlt hst_tail
  have hstH : TR.TRStateStoredAt p st stateIdx tr_k := by
    have hat0 : TR.TRStateStoredAt p st stateIdx tr₀ :=
      TR.FreshSigma.at?_eq_some_of_getLocalState_some hst
    change (tr_k.at? stateIdx : Option ho_PromStEntry) = some ⟨⟨p, st⟩⟩
    dsimp only [tr_k]
    rw [TR.RecvDec.at?_append_non_entry _ _ rfl]
    exact hat0
  intro s' pk' n' seed' rIdx' src' i' p₀ st₀ c₀ hlog hst₀ hrc c_m hc_m
  rw [htr_post] at hlog hst₀
  exact TR.skippedInstallByteFresh_decTailTr_of_findRecvChain_some interpretation S g r₀ ms
    htr_le hno_new_pre hst_pre hstH hfind (Symbolic.Swarm.CREF.CliPure.RpkCli.Skr.skippedKeySrcLt_runTrace r₀ ms) hBF
    s' pk' n' seed' rIdx' src' i' p₀ st₀ c₀ hlog hst₀ hrc c_m hc_m

private theorem eventLoggedAt_decTailTr_skippedKeyStored_src_prom₂
    {tr_pre : ExecTrace} {q : Participant} {stateIdx : Nat} {st1 : TRState} {c c' : RecvChain}
    {pk seed pqSalt ptTerm spqr' : DY.Bytes} {n : UInt32}
    {s : SessionInfo} {pk' : DY.Bytes} {n' : UInt32} {seed' : DY.Bytes} {r' srcIdx' i : Nat}
    (hlog : (TR.RecvDec.decTailTr tr_pre q stateIdx st1 c c' pk seed pqSalt ptTerm spqr' n).EventLoggedAt
      (TREvent.SkippedKeyStored s pk' n' seed' r' srcIdx') i) :
    tr_pre.EventLoggedAt (TREvent.SkippedKeyStored s pk' n' seed' r' srcIdx') i ∨
      (pk' = pk ∧ srcIdx' = stateIdx) := by
  let tr_sk := TR.RecvDec.logSkippedKeysTr (st1.sessionInfo q) pk c.rIdx stateIdx c.chainKey c.index
    (n.toNat - c.index.toNat) tr_pre
  have hlog_sk : tr_sk.EventLoggedAt (TREvent.SkippedKeyStored s pk' n' seed' r' srcIdx') i := by
    rw [Symbolic.DYBridge.DY.Trace.EventLoggedAt_eq_1]
    have hlog' := (Symbolic.DYBridge.DY.Trace.EventLoggedAt_eq_1 _ _ _).mp hlog
    unfold TR.RecvDec.decTailTr at hlog'; dsimp only at hlog'
    rw [TR.RecvDec.at?_append_non_entry _ _ rfl] at hlog'
    rcases Nat.lt_or_ge i (tr_sk.length + 1) with hlt1 | hge1
    · rw [TR.RecvDec.at?_append_of_lt _ _ (by
        dsimp only [tr_sk] at hlt1
        simp only [Symbolic.DYBridge.DY.Trace.append_eq_1, Symbolic.DYBridge.DY.Trace.length_eq_2]
        omega)] at hlog'
      rcases Nat.lt_or_ge i tr_sk.length with hlt0 | hge0
      · rw [TR.RecvDec.at?_append_of_lt _ _ hlt0] at hlog'; exact hlog'
      · have heq0 : i = tr_sk.length := by omega
        subst heq0; rw [Trace.at?_append] at hlog'; nomatch hlog'
    · rcases Nat.eq_or_lt_of_le hge1 with heq1 | hgt1
      · have hlen_rcv : tr_sk.length + 1 =
            (tr_sk.append (⟨TREvent.Received q st1.peer pk n ptTerm⟩ : ho_PromTREntry)).length := by
          simp only [Symbolic.DYBridge.DY.Trace.append_eq_1, Symbolic.DYBridge.DY.Trace.length_eq_2]
        rw [← heq1, hlen_rcv, Trace.at?_append] at hlog'; nomatch hlog'
      · rw [TR.RecvDec.at?_eq_none_of_le _ (by
          dsimp only [tr_sk] at hgt1
          simp only [Symbolic.DYBridge.DY.Trace.append_eq_1, Symbolic.DYBridge.DY.Trace.length_eq_2]
          omega)] at hlog'
        nomatch hlog'
  have hlog_sk' := (Symbolic.DYBridge.DY.Trace.EventLoggedAt_eq_1 _ _ _).mp hlog_sk
  by_cases hi : i < tr_pre.length
  · have hlog0 : tr_pre.EventLoggedAt (TREvent.SkippedKeyStored s pk' n' seed' r' srcIdx') i := by
      rw [Symbolic.DYBridge.DY.Trace.EventLoggedAt_eq_1]
      rw [← TR.RecvDec.at?_trEntry_logSkippedKeysTr_lt _ _ _ _ _ _ _ _ hi]; exact hlog_sk'
    exact Or.inl hlog0
  · have hi_lt : i < tr_sk.length := by
      by_contra hge
      have hnone : (tr_sk.at? i : Option ho_PromTREntry) = none :=
        TR.RecvDec.at?_eq_none_of_le tr_sk (Nat.le_of_not_lt hge)
      rw [hnone] at hlog_sk'; cases hlog_sk'
    have hlen_sk : tr_sk.length = tr_pre.length + (n.toNat - c.index.toNat) :=
      TR.RecvDec.logSkippedKeysTr_length _ _ _ _ _ _ _ _
    have hj : i - tr_pre.length < n.toNat - c.index.toNat := by omega
    have hi_eq : i = tr_pre.length + (i - tr_pre.length) := by omega
    have hat := TR.RecvDec.at?_trEntry_logSkippedKeysTr_add (st1.sessionInfo q) pk c.rIdx stateIdx
      c.chainKey c.index (n.toNat - c.index.toNat) tr_pre hj
    rw [hi_eq, hat] at hlog_sk'; cases hlog_sk'; exact Or.inr ⟨rfl, rfl⟩

private theorem eventLoggedAt_decRatchetPreTr_skippedKeyStored_prom₂ {tr : ExecTrace}
    {q : Participant} {st1 : TRState} {pk key : DY.Bytes}
    {s : SessionInfo} {pk' : DY.Bytes} {n' : UInt32} {seed' : DY.Bytes} {r' srcIdx' i : Nat}
    (hlog : (TR.RecvDec.decRatchetPreTr tr q st1 pk key).EventLoggedAt
      (TREvent.SkippedKeyStored s pk' n' seed' r' srcIdx') i) :
    tr.EventLoggedAt (TREvent.SkippedKeyStored s pk' n' seed' r' srcIdx') i := by
  rw [Symbolic.DYBridge.DY.Trace.EventLoggedAt_eq_1]
  have hlog' := (Symbolic.DYBridge.DY.Trace.EventLoggedAt_eq_1 _ _ _).mp hlog
  unfold TR.RecvDec.decRatchetPreTr at hlog'
  let tr2 := (tr.append (⟨32⟩ : DY.Random.ExecEntryT)).append (⟨key⟩ : DY.Network.ExecEntryT)
  rcases Nat.lt_or_ge i (tr2.length + 1) with hlt1 | hge1
  · rw [TR.RecvDec.at?_append_of_lt _ _ (by
      simp only [tr2, Symbolic.DYBridge.DY.Trace.append_eq_1, Symbolic.DYBridge.DY.Trace.length_eq_2] at hlt1 ⊢
      omega)] at hlog'
    rcases Nat.lt_or_ge i tr2.length with hlt0 | hge0
    · rw [TR.RecvDec.at?_append_of_lt _ _ hlt0] at hlog'; dsimp only [tr2] at hlog'
      rw [TR.RecvDec.at?_append_non_entry _ _ rfl, TR.RecvDec.at?_append_non_entry _ _ rfl] at hlog'
      exact hlog'
    · have heq0 : i = tr2.length := Nat.le_antisymm (Nat.lt_succ_iff.mp hlt1) hge0
      subst heq0; rw [Trace.at?_append] at hlog'; nomatch hlog'
  · rcases Nat.eq_or_lt_of_le hge1 with heq1 | hgt1
    · have hlen_dh : tr2.length + 1 =
          (tr2.append (⟨TREvent.DHRatchet q st1.peer pk (DY.DiffieHellman.dhPk st1.dhs)⟩ : ho_PromTREntry)).length := by
        simp only [Symbolic.DYBridge.DY.Trace.append_eq_1, Symbolic.DYBridge.DY.Trace.length_eq_2]
      rw [← heq1, hlen_dh, Trace.at?_append] at hlog'; nomatch hlog'
    · rw [TR.RecvDec.at?_eq_none_of_le _ (by
        simp only [tr2, Symbolic.DYBridge.DY.Trace.append_eq_1, Symbolic.DYBridge.DY.Trace.length_eq_2] at hgt1 ⊢
        omega)] at hlog'
      nomatch hlog'

private theorem le_logSkippedKeysTr_prom₂ (s : SessionInfo) (pk : DY.Bytes) (rIdx srcIdx : Nat)
    (ck : DY.Bytes) (idx : UInt32) :
    ∀ (cnt : Nat) (tr : ExecTrace),
      tr ≤ TR.RecvDec.logSkippedKeysTr s pk rIdx srcIdx ck idx cnt tr
  | 0, tr => DY.Trace.le_refl tr
  | cnt + 1, _tr =>
    DY.Trace.le_trans _ _ _ (DY.Trace.append_le _ _)
      (le_logSkippedKeysTr_prom₂ s pk rIdx srcIdx (kdfCk ck).1 (idx + 1) cnt _)

private theorem le_decTailTr_prom₂ (tr : ExecTrace) (q : Participant) (stateIdx : Nat)
    (st : TRState) (c c' : RecvChain) (pk seed pqSalt ptTerm spqr' : DY.Bytes) (n : UInt32) :
    tr ≤ TR.RecvDec.decTailTr tr q stateIdx st c c' pk seed pqSalt ptTerm spqr' n := by
  unfold TR.RecvDec.decTailTr
  exact DY.Trace.le_trans _ _ _ (le_logSkippedKeysTr_prom₂ _ _ _ _ _ _ _ _)
    (DY.Trace.le_trans _ _ _
      (DY.Trace.le_trans _ _ _ (DY.Trace.append_le _ _) (DY.Trace.append_le _ _))
      (DY.Trace.append_le _ _))

private theorem le_decRatchetPreTr_prom₂ (tr : ExecTrace) (q : Participant) (st1 : TRState)
    (pk key : DY.Bytes) :
    tr ≤ TR.RecvDec.decRatchetPreTr tr q st1 pk key := by
  unfold TR.RecvDec.decRatchetPreTr
  exact DY.Trace.le_trans _ _ _
    (DY.Trace.le_trans _ _ _
      (DY.Trace.le_trans _ _ _ (DY.Trace.append_le _ _) (DY.Trace.append_le _ _))
      (DY.Trace.append_le _ _))
    (DY.Trace.append_le _ _)

theorem prom_skippedInstallByteFresh_decrypt_ratchet₂
    {interpretation : ExternInterpretation} {r₀ : ProtocolSetup} {S : OpaqueSymbolSemantics}
    {who : List Participant} {ok : Nat → Bool}
    {j : Nat} {e' : PromTurn}
    {acc : List MachineEvent} {rec b rngBytes : HwBytes} {sm : StateAndMessage}
    {pf : PreKeyFields} {sess sess' : Session (List (BitVec 8))}
    {coins : BitVec 256} {expected : Option (List (BitVec 8))} {pt : List (BitVec 8)}
    {g : Ghost} {ms₀ pre post : List Move}
    {stateIdx msgIdx pqIdx : Nat} {spqrMsgIdx : UInt32} {wrapped : Bool}
    (hwf : ProtocolSetupWF r₀)
    (hC : PromAcceptCallBy₂ interpretation r₀ S who ok j e' [.rng rngBytes] acc rec b sm pf sess sess' coins expected pt)
    (hB : XplBlock interpretation r₀ S who g ms₀
      (pre ++ .decrypt r₀.bob stateIdx msgIdx pqIdx spqrMsgIdx wrapped :: post) acc
      (promAccBlk b [.rng rngBytes] pt))
    (hpre : MovesFrom InvisibleNoEffect (runTraceMoves r₀ ms₀) pre)
    (hpost : MovesFrom InvisibleNoEffect
      ((Move.decrypt r₀.bob stateIdx msgIdx pqIdx spqrMsgIdx wrapped).next
        (runMoves pre (runTraceMoves r₀ ms₀)).1) post)
    (hcurR : PromCurrentRead interpretation r₀ S g (ms₀ ++ pre) pf.message
      (.decrypt r₀.bob stateIdx msgIdx pqIdx spqrMsgIdx wrapped))
    (hrr : PureCRecRel interpretation r₀ S g (ms₀ ++ pre) r₀.bob rec)
    (hrole : RoleSnapshots r₀ (runTraceMoves r₀ (ms₀ ++ pre)))
    (hBF : TR.SkippedInstallByteFresh interpretation S g r₀ (ms₀ ++ pre)) :
    TR.SkippedInstallByteFresh interpretation S g r₀
      (ms₀ ++ pre ++ [.decrypt r₀.bob stateIdx msgIdx pqIdx spqrMsgIdx wrapped]) := by
  let ms := ms₀ ++ pre
  have hmatch := prom_block_vis hB hpre hpost
  have hrng_blk : .rng rngBytes ∈ promAccBlk b [.rng rngBytes] pt := by
    simp [promAccBlk]
  obtain ⟨_hRng, st, t, msg, c', seed, spqr', key, pqSalt, ptTerm,
      hst, hmsg, hparse, hver, hfind, hlow, hcons, hspqr, hpqSalt, hmac_eq, hdec, _hpt⟩ :=
    ratchet_of_matched hmatch hrng_blk (prom_accBlk_has_accept b [.rng rngBytes] pt)
  have hdraws : pureDrawsCoins (cryptoOf' interpretation) sess.state pf.inner.senderRatchetKey = true := by
    rcases hC.out.hcoins with ⟨_, hnil⟩ | ⟨_, _, _, _, hd⟩
    · cases hnil
    · exact hd
  have hfind_bin : (ratchetStateOf sess.state).findReceiverChainKey pf.inner.senderRatchetKey = .ok none := by
    unfold pureDrawsCoins at hdraws
    cases hrem : sess.state.remoteIdentity
    · rw [hrem] at hdraws; cases hdraws
    · rw [hrem] at hdraws
      cases hf : RatchetState.findReceiverChainKey
          ⟨sess.state.rootKey, sess.state.senderChain, sess.state.receiverChains,
            sess.state.previousCounter, LibsignalSession.maxForwardJumps⟩
          pf.inner.senderRatchetKey with
      | error _ => rw [hf] at hdraws; cases hdraws
      | ok opt =>
        cases opt with
        | none => exact hf
        | some _ => rw [hf] at hdraws; cases hdraws
  have hci : (ratchetStateOf sess.state).findReceiverChainIndex pf.inner.senderRatchetKey = none :=
    Proofs.libsignal.RngG.CliPure.R3.findReceiverChainKey_ok_none
      (ratchetStateOf sess.state) pf.inner.senderRatchetKey hfind_bin
  have hrc_none : ∀ rc ∈ sess.state.receiverChains, rc.senderRatchetKey ≠ pf.inner.senderRatchetKey := by
    intro rc hMem hEq
    unfold CryptoGames.LibsignalSession.RatchetState.findReceiverChainIndex at hci
    rw [List.findIdx?_eq_none_iff] at hci
    have hFalse := hci rc hMem
    simp [hEq] at hFalse
  have htry : SignalMessage.tryFrom protoSignalCodec pf.message = .ok pf.inner :=
    parsePreKeyWire_inner_tryFrom hC.out.hpf
  have hrr_inv : ∃ rec₀ st₀ stateIdx₀,
      rec = recordBytes rec₀ ∧
      ((PersistentLocalState.getLocalState r₀.bob stateIdx₀ : Traceful TRState).run (runTraceMoves r₀ ms)).1 = some st₀ ∧
      isCurrentSnapshot (runTraceMoves r₀ ms) stateIdx₀ = true ∧
      StateRel interpretation S g st₀ rec₀ := by
    rcases hrr with hrsi | ⟨hab, _⟩
    · obtain ⟨_, rec₀, st₀, stateIdx₀, hrecBytes₀, hst₀, hcur₀, hrel₀, _, _, _, _⟩ :=
        hrsi r₀.bob rec (by simp)
      exact ⟨rec₀, st₀, stateIdx₀, hrecBytes₀, hst₀, hcur₀, hrel₀⟩
    · exact False.elim (hwf.1 hab.symm)
  obtain ⟨rec₀, st₀, stateIdx₀, hrecBytes₀, hst₀, hcur₀, hrel₀⟩ := hrr_inv
  have hidx : stateIdx = stateIdx₀ :=
    prom_currentSnapshot_unique_of_role hrole hst hst₀ hcurR.1 hcur₀
  cases hidx.symm
  have hst_eq : st = st₀ := Option.some.inj (hst.symm.trans hst₀)
  cases hst_eq.symm
  have hnorm_eq : normPending rec₀ = normPending (sessionToRecordRecPending sess) :=
    ho_prom_normPending_of_canonical_Q hrecBytes₀ hC.out.hcan_in
  have hrel_sess : StateRel interpretation S g st (sessionToRecordRec sess) := by
    change StateRel interpretation S g st (normPending (sessionToRecordRecPending sess))
    rw [← hnorm_eq]
    exact hrel₀
  have hrep : t ∈ recvRepresentations interpretation r₀ S g ms pf.message := hcurR.2 t hmsg
  obtain ⟨_hwire_t, _hmac_t, _hhd_t, hfld⟩ := hrep.2.2.2 msg hparse
  obtain ⟨_hct_m, hrk_m, _hpq_m, _hctr_m, _hver_m⟩ := hfld pf.inner htry
  have hTheir' : pf.inner.senderRatchetKey.bytes.toList = gamma interpretation S g msg.ratchetKey :=
    hrk_m.symm
  have hTheir : pf.inner.senderRatchetKey = ⟨vec32 (gamma interpretation S g msg.ratchetKey)⟩ :=
    (Proofs.libsignal.RngG.CliPure.R3.publicKey_eq_vec32_of_toList_eq hTheir').1
  have hByteFresh_new : ∀ c_m ∈ st.recv,
      gamma interpretation S g c_m.ratchetKey ≠ gamma interpretation S g msg.ratchetKey := by
    intro c_m hc_m hγ_eq
    obtain ⟨rc, hrcMem, hSrk⟩ :=
      senderRatchetKey_of_mem_recv_of_stateRel_tr interpretation S g hrel_sess hc_m
    exact hrc_none rc hrcMem (by rw [hSrk, hγ_eq, hTheir])
  let tr₀ := runTraceMoves r₀ ms
  let st1 := (TR.RecvDec.trDhRatchetState st msg.ratchetKey tr₀.length).1
  let c_new := (TR.RecvDec.trDhRatchetState st msg.ratchetKey tr₀.length).2
  let tr_pre := TR.RecvDec.decRatchetPreTr tr₀ r₀.bob st1 msg.ratchetKey key
  let T := TR.RecvDec.decTailTr tr_pre r₀.bob stateIdx st1 c_new c' msg.ratchetKey seed pqSalt ptTerm spqr'
    msg.counter
  have htr : runTraceMoves r₀ (ms ++ [.decrypt r₀.bob stateIdx msgIdx pqIdx spqrMsgIdx wrapped]) = T := by
    rw [TR.runTrace_snoc]
    exact TR.RecvDec.decrypt_next_ratchet_eq
      hst hmsg hparse hver hfind hlow hcons hspqr hpqSalt hmac_eq hdec
  have hle : tr₀ ≤ T :=
    DY.Trace.le_trans _ _ _ (le_decRatchetPreTr_prom₂ _ _ _ _ _) (le_decTailTr_prom₂ _ _ _ _ _ _ _ _ _ _ _ _)
  intro s pk n' seed' rIdx src i p₀ st_src c₀ hev hsrc hrcf
  rw [htr] at hev hsrc
  rcases eventLoggedAt_decTailTr_skippedKeyStored_src_prom₂ hev with hev_pre | ⟨hpk_eq, hsrc_eq⟩
  · have hev₀ : tr₀.EventLoggedAt (TREvent.SkippedKeyStored s pk n' seed' rIdx src) i :=
      eventLoggedAt_decRatchetPreTr_skippedKeyStored_prom₂ hev_pre
    have hlt_src : src < tr₀.length :=
      Symbolic.Swarm.CREF.CliPure.RpkCli.Skr.skippedKeySrcLt_runTrace r₀ ms s pk n' seed' rIdx src i hev₀
    have hst_src₀ : TR.TRStateStoredAt p₀ st_src src tr₀ :=
      TR.trStateStoredAt_of_le_of_lt hle hlt_src hsrc
    exact hBF s pk n' seed' rIdx src i p₀ st_src c₀ hev₀ hst_src₀ hrcf
  · cases hpk_eq; cases hsrc_eq.symm
    have hat₀ : TR.TRStateStoredAt r₀.bob st stateIdx tr₀ :=
      TR.FreshSigma.at?_eq_some_of_getLocalState_some hst
    have hlt_idx : stateIdx < tr₀.length := by
      have hlen := Trace.at?_eq_some_implies_length_le (EntryT := ho_PromStEntry) tr₀ stateIdx
      change (tr₀.at? stateIdx : Option ho_PromStEntry) = some _ at hat₀
      rwa [hat₀] at hlen
    have hsrc₀ : TR.TRStateStoredAt p₀ st_src stateIdx tr₀ :=
      TR.trStateStoredAt_of_le_of_lt hle hlt_idx hsrc
    have heq : (some ⟨⟨r₀.bob, st⟩⟩ : Option ho_PromStEntry) = some ⟨⟨p₀, st_src⟩⟩ :=
      hat₀.symm.trans hsrc₀
    injection heq with h1
    injection h1 with h2
    injection h2 with _ hst_eq
    subst hst_eq
    exact hByteFresh_new

theorem prom_skippedInstallByteFresh_step₂
    {interpretation : ExternInterpretation} {r₀ : ProtocolSetup} {S : OpaqueSymbolSemantics}
    {who : List Participant} {ok : Nat → Bool}
    {j : Nat} {e' : PromTurn} {mid acc : List MachineEvent}
    {rec b : HwBytes} {sm : StateAndMessage} {pf : PreKeyFields}
    {sess sess' : Session (List (BitVec 8))}
    {coins : BitVec 256} {expected : Option (List (BitVec 8))} {pt : List (BitVec 8)}
    {g : Ghost} {ms₀ pre post : List Move} {m : Move}
    (hwf : ProtocolSetupWF r₀)
    (hC : PromAcceptCallBy₂ interpretation r₀ S who ok j e' mid acc rec b sm pf sess sess' coins expected pt)
    (hB : XplBlock interpretation r₀ S who g ms₀ (pre ++ m :: post) acc (promAccBlk b mid pt))
    (hpre : MovesFrom InvisibleNoEffect (runTraceMoves r₀ ms₀) pre)
    (hm : DecryptBy r₀.bob m)
    (hpost : MovesFrom InvisibleNoEffect (m.next (runMoves pre (runTraceMoves r₀ ms₀)).1) post)
    (hcurR : PromCurrentRead interpretation r₀ S g (ms₀ ++ pre) pf.message m)
    (hrr : PureCRecRel interpretation r₀ S g (ms₀ ++ pre) r₀.bob rec)
    (hrole : RoleSnapshots r₀ (runTraceMoves r₀ (ms₀ ++ pre)))
    (hBF : TR.SkippedInstallByteFresh interpretation S g r₀ (ms₀ ++ pre)) :
    TR.SkippedInstallByteFresh interpretation S g r₀ (ms₀ ++ pre ++ [m]) := by
  cases m with
  | decryptSkipped me stateIdx msgIdx skIdx pqIdx spqrMsgIdx wrapped =>
    exact Symbolic.Swarm.CREF.CliPure.RpkCli.Skr.skippedInstallByteFresh_decryptSkipped' interpretation S g r₀ (ms₀ ++ pre)
      me stateIdx msgIdx skIdx pqIdx spqrMsgIdx wrapped hBF
  | decrypt me stateIdx msgIdx pqIdx spqrMsgIdx wrapped =>
    have hme : me = r₀.bob := hm
    subst hme
    rcases hC.hmid with rfl | ⟨rngBytes, rfl, _⟩
    · exact prom_skippedInstallByteFresh_decrypt_noRatchet hB hpre hpost hBF
    · exact prom_skippedInstallByteFresh_decrypt_ratchet₂ hwf hC hB hpre hpost hcurR hrr hrole hBF
  | _ => nomatch hm

/-! ## `PromHistStep` and `PromHistOK` -/

theorem prom_cHist_step
    {interpretation : ExternInterpretation} {r : ProtocolSetup} {S : OpaqueSymbolSemantics}
    {who : List Participant} {ok : Nat → Bool}
    {j : Nat} {e' : PromTurn} {mid acc : List MachineEvent}
    {rec b : HwBytes} {sm : StateAndMessage} {pf : PreKeyFields}
    {sess sess' : Session (List (BitVec 8))}
    {coins : BitVec 256} {expected : Option (List (BitVec 8))} {pt : List (BitVec 8)}
    (hext : DY.Libsignal.Composed.Refinement.Cli.ExternContractsHoldCli interpretation)
    (hwf : ProtocolSetupWF r)
    (hC : PromAcceptCall interpretation r S who ok j e' mid acc rec b sm pf sess sess' coins expected pt) :
    PromHistStep interpretation r S who ok r.bob rec sm.state acc (promAccBlk b mid pt) := by
  intro g ms₀ δ hc hB h1 ⟨hch₀, hrole₀⟩ hrec hrec'
  obtain ⟨pre, m, post, rfl, hpre, hstep, hpost⟩ := h1
  have hrun_pre : (runMoves pre (runTraceMoves r ms₀)).1 = runTraceMoves r (ms₀ ++ pre) :=
    (TR.runTrace_append r ms₀ pre).symm
  have hm : DecryptBy r.bob m := hstep.2.2 (prom_accBlk_has_accept b mid pt)
  have hcur := prom_currentRead_of_clean hC.out.hpf hc hB hpre hpost
  have hq_pre := prom_quietPre hpre
  have hrr_pre := Symbolic.Swarm.CREF.CliPure.RpkCli.XplQuiet.quiet_pureCRecRel hq_pre hrec
  have hrole_pre : RoleSnapshots r (runTraceMoves r (ms₀ ++ pre)) := by
    rw [TR.runTrace_append]
    exact roleSnapshots_of_movesFrom_invisibleNoEffect hpre hrole₀
  have hpost' : MovesFrom InvisibleNoEffect (m.next (runTraceMoves r (ms₀ ++ pre))) post := by
    rwa [← hrun_pre]
  have hrsi := prom_inv_of_cRecRel_post hwf hpost' hrec'
  have hrole_pair := prom_role_pair_of_roleSnapshots hwf hrole₀ hpre hm
  obtain ⟨rr₀, hrec_rr₀, _, hok₀⟩ := prom_recRecvRkOk_entry_of_cRecRel hch₀ hrec
  have hok_rk := prom_recRecvRkOk_of_acceptOut (hext.1)
    hrec_rr₀ hok₀ hC.out
  have hstore := prom_hist_store_of_inv hrsi hrole_pair hok_rk
  have hch_pre : CHist interpretation r S g (ms₀ ++ pre) :=
    Symbolic.Swarm.CREF.CliPure.RpkCli.XplQuiet.quiet_cHist hq_pre hch₀
  have hch_m : CHist interpretation r S g (ms₀ ++ pre ++ [m]) :=
    prom_hist_snoc_of_parts hm hch_pre
      (prom_skippedInstallByteFresh_step₂ hwf hC hB hpre hm hpost hcur hrr_pre hrole_pre)
      hstore
  exact Symbolic.Swarm.CREF.CliPure.RpkCli.XplQuiet.quiet_cHist (prom_quietPost hpost') hch_m

/-- Discharges `PromHistOK` on accepting session-promotion calls. -/
theorem prom_histOK {interpretation : ExternInterpretation} (hext : DY.Libsignal.Composed.Refinement.Cli.ExternContractsHoldCli interpretation)
    {r : ProtocolSetup} (hwf : ProtocolSetupWF r) {S : OpaqueSymbolSemantics}
    {who : List Participant} {ok : Nat → Bool} :
    PromHistOK interpretation r S who ok :=
  fun _ _ _ _ _ _ _ _ _ _ _ _ _ hC _ => prom_cHist_step hext hwf hC

end Symbolic.Swarm.CREF.CliPure
