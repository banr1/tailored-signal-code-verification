/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Symbolic.Proofs.Swarm.CREF.TR.RecvDec
public import Symbolic.Proofs.RngG.R3ModelInv
import DY.Trace.Basic
import DY.Trace.Monad
import DY.Trace.Manipulation
import DY.ALaCarte.Basic
import DY.Actions.Network
public import Symbolic.Proofs.Swarm.CREF.Cli.Rpk.RecvDecStepCommonPureA
import Symbolic.Proofs.RngG.R3SetRecv
import Symbolic.Proofs.Swarm.CREF.Cli.Rpk.RecvDecStepCommonPure
import Symbolic.Proofs.Swarm.CREF.ModelBridge
import Symbolic.Proofs.Swarm.CREF.Prelude
import Symbolic.Proofs.Swarm.CREF.TROpen
import Symbolic.DYBridge.DY.Trace.Basic
import Symbolic.DYBridge.DY.Trace.Monad
import Symbolic.DYBridge.DY.Trace.Manipulation
import Symbolic.DYBridge.DY.ALaCarte.Basic
import Symbolic.DYBridge.DY.Actions.Network

/-!
# Existing Receiver-Chain Decrypt Step Bridge

Bridges existing-chain `advanceChain` and `setReceiverChainKey` execution to symbolic
`consumeMessageKey` and `StateRel`, and steps `MatchedPrefix` across `Move.decrypt` without a DH
ratchet step.
-/

@[expose] public section

cref_hide_foreign_instances

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace Symbolic.Swarm.CREF.CliPure.TR
open Symbolic.Swarm.CREF.TR hiding runMoves_append runTrace_append runTrace_snoc runVis_append runVis_snoc

cref_open
cref_open_tr
open CryptoProofLib.Refinement (ExternInterpretation)
open DY.Libsignal.HwEvents (MachineEvent)

end Symbolic.Swarm.CREF.CliPure.TR

namespace Symbolic.Swarm.CREF.CliPure.TR.RecvDecStep
open Symbolic.Swarm.CREF.TR hiding runMoves_append runTrace_append runTrace_snoc runVis_append runVis_snoc

cref_open
cref_open_tr

open DY DY.Comparse DY.Literal DY.Libsignal
open DY.Libsignal.TripleRatchet (SessionInfo RecvChain findRecvChain setRecvChain consumeMessageKey
  chainKeyAt kdfCk maxForwardJumps computeMac messageVersion)
open DY.Libsignal.TripleRatchet
open DY.Libsignal.TripleRatchet.Refinement (wireWhisperTag)
open DY.Libsignal.Refinement (sha256CompressFunction)
open DY.Libsignal.HwEvents DY.Libsignal.Rust
open CryptoGames CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open CryptoVerification
open CryptoVerification.LibsignalProtoCodec
open CryptoVerification.E2E CryptoVerification.E2E.Record
open CryptoVerification.SessionModel.AdvanceAndFrame
open CryptoProofLib.Refinement (ExternInterpretation)
open Proofs.libsignal.RngG Proofs.libsignal.RngG.R3 Proofs.libsignal.RngG.CliPure.R3
open Swarm.Phase0WholeFunctionBridge (sessionToRecordRec)
open Symbolic.Swarm.CREF Symbolic.Swarm.CREF.CliPure Symbolic.Swarm.CREF.CliPure.TR
open Symbolic.Swarm.CREF.TR.RecvDec
  (matchedPrefix_attackerSend getLocalState_attackerSend getMessageSentAt_attackerSend
   matchedPrefix_step_decrypt_noRatchet decrypt_next_noRatchet_eq)

theorem stateRel_and_consumeMessageKey_of_existing_tr
    (interpretation : ExternInterpretation) (S : SpqrSem) (g : Ghost)
    {st : TRState} {s : CryptoGames.LibsignalSessionApi.Session (List (BitVec 8))}
    (hrel : StateRel interpretation S g st (sessionToRecordRec s))
    (hNodup : (st.recv.map RecvChain.ratchetKey).Nodup)
    (hCkLens : ∀ c ∈ st.recv, (gamma interpretation S g c.chainKey).length = 32)
    {their : PublicKey} {counter : BitVec 32} {ck ck_adv ck_next : ChainKey} {r_adv r2 : RatchetState}
    {spqr' : DY.Bytes} {newPqrState : List (BitVec 8)} (hspqr' : gamma interpretation S g spqr' = newPqrState)
    (hFind : (ratchetStateOf s.state).findReceiverChainKey their = .ok (some ck)) (hNotLt : ¬ (counter < ck.index))
    (hJump : (counter - ck.index).toNat ≤ CryptoGames.LibsignalSession.maxForwardJumps)
    (hAdv : Mut.exec (RatchetState.advanceChain (sha256CompressFunction interpretation)
      their counter (counter - ck.index).toNat ck) (ratchetStateOf s.state) = (.ok ck_adv, r_adv))
    (hNext : ck_adv.nextChainKey (sha256CompressFunction interpretation) = .ok ck_next)
    (hSet : Mut.exec (RatchetState.setReceiverChainKey their ck_next) r_adv = (.ok (), r2)) :
    let F := sha256CompressFunction interpretation
    let msgCounter := UInt32.ofBitVec counter
    ∃ (ci : Nat) (ch : ReceiverChain) (c : RecvChain) (mks' : List MessageKeyGenerator)
      (seed : DY.Bytes) (c' : RecvChain),
      s.state.receiverChains[ci]? = some ch ∧ st.recv[ci]? = some c ∧
      findRecvChain st.recv c.ratchetKey = some c ∧ ch.senderRatchetKey = their ∧
      their = ⟨vec32 (gamma interpretation S g c.ratchetKey)⟩ ∧
      ck = ⟨CryptoGames.HKDF.bytesToKey32 (gamma interpretation S g c.chainKey), c.index.toBitVec⟩ ∧
      ch.chainKey = some ck ∧ consumeMessageKey c msgCounter = some (seed, c') ∧
      (ck_adv.messageKeys F).seed = gamma interpretation S g seed ∧ (ck_adv.messageKeys F).counter = counter ∧
      c'.ratchetKey = c.ratchetKey ∧ c'.rIdx = c.rIdx ∧
      r2 = { ratchetStateOf s.state with
        receiverChains := (ratchetStateOf s.state).receiverChains.set ci
          { ch with chainKey := some ck_next, messageKeys := mks' } } ∧
      StateRel interpretation S g { st with recv := setRecvChain st.recv c', spqr := spqr' }
        (sessionToRecordRec { s with state := { s.state with receiverChains := r2.receiverChains, pqRatchetState := newPqrState } }) ∧
      (∀ k ∈ mks', k ∈ ch.messageKeys ∨
        ∃ j < msgCounter.toNat - c.index.toNat,
          k.counter = c.index.toBitVec + BitVec.ofNat 32 j ∧
          UInt32.ofBitVec k.counter = c.index + UInt32.ofNat j ∧
          UInt32.ofBitVec k.counter ≠ msgCounter ∧
          k.seed = gamma interpretation S g (kdfCk (chainKeyAt c.chainKey j)).2 ∧ k.seed.length = 32) := by
  intro F msgCounter
  have hMap : (ratchetStateOf s.state).receiverChains.map eraseRecvChain =
      st.recv.map (modelRecvChainOfTr interpretation S g) :=
    recvMap_of_stateRel_tr interpretation S g hrel hCkLens
  obtain ⟨ci, ch, c, hci0, hch0, hc0, hsrk0, htheir, hck, hch_ck⟩ := findReceiverChainKey_some_of_map_erase_tr hMap hFind
  obtain ⟨hLe, hNeAllOnes, hCkAdvEq, hCkAdvIdx, hCkNextEq, _, ci', ch', mks', hci1, hch1, _, hR2Eq, hMksSub⟩ :=
    advanceChain_setReceiverChainKey_ok_inv hNotLt hAdv hNext hSet
  rw [hci0] at hci1; injection hci1 with hci_eq; subst hci_eq
  rw [hch0] at hch1; injection hch1 with hch_eq; subst hch_eq
  have hFindSym := findRecvChain_eq_some_of_getElem?_nodup_tr st.recv ci c hNodup hc0
  have hCkLen := hCkLens c (List.mem_of_getElem? hc0)
  have hCkIdx : ck.index = c.index.toBitVec := by rw [hck]
  have hIdxLe : c.index ≤ msgCounter := by rw [uint32_ofBitVec_le_iff, ← hCkIdx]; exact hLe
  have hn_eq : (counter - ck.index).toNat = msgCounter.toNat - c.index.toNat := by
    have hadd := index_toNat_add_sub_eq ck counter hLe
    change ck.index.toNat + (counter - ck.index).toNat = msgCounter.toNat at hadd
    have hck_nat : ck.index.toNat = c.index.toNat := by rw [hCkIdx]; rfl
    omega
  let n := msgCounter.toNat - c.index.toNat
  let seed : DY.Bytes := (kdfCk (chainKeyAt c.chainKey n)).2
  let c' : RecvChain := { ratchetKey := c.ratchetKey, chainKey := (kdfCk (chainKeyAt c.chainKey n)).1, index := msgCounter + 1, rIdx := c.rIdx }
  have hNotLtSym : ¬ msgCounter < c.index := by
    intro h; rw [UInt32.lt_iff_toNat_lt] at h; rw [UInt32.le_iff_toNat_le] at hIdxLe; omega
  have hConsSym : consumeMessageKey c msgCounter = some (seed, c') :=
    (consumeMessageKey_eq_some_iff_tr c msgCounter seed c').mpr
      ⟨hNotLtSym, by rw [← hn_eq]; exact hJump, uint32_ofBitVec_ne_u32Max_of_ne_allOnes hNeAllOnes, rfl, rfl⟩
  have hSeedEq : (ck_adv.messageKeys F).seed = gamma interpretation S g seed := by
    rw [hCkAdvEq, hn_eq, hck]; exact chainStepN_messageKeys_seed_eq_gamma_tr interpretation S g c.chainKey c.index.toBitVec n hCkLen
  have hCkNextVal : ck_next = ⟨CryptoGames.HKDF.bytesToKey32 (gamma interpretation S g c'.chainKey), c'.index.toBitVec⟩ := by
    have hAdvKey : ck_adv.key = CryptoGames.HKDF.bytesToKey32 (gamma interpretation S g (chainKeyAt c.chainKey n)) := by
      rw [hCkAdvEq, hn_eq, hck]; exact chainStepN_eq_gamma_chainKeyAt_tr interpretation S g c.chainKey c.index.toBitVec n hCkLen
    have hAdvFull : ck_adv = ⟨CryptoGames.HKDF.bytesToKey32 (gamma interpretation S g (chainKeyAt c.chainKey n)), counter⟩ := by
      rcases ck_adv with ⟨k_a, i_a⟩; dsimp only at hAdvKey hCkAdvIdx; rw [hAdvKey, hCkAdvIdx]
    rw [hCkNextEq, hAdvFull, step1_key_eq_gamma_kdfCk_fst_tr interpretation S g (chainKeyAt c.chainKey n)
      counter (length_gamma_chainKeyAt_tr interpretation S g c.chainKey n hCkLen)]; rfl
  have hEraseCh' : eraseRecvChain { ch with chainKey := some ck_next, messageKeys := mks' } = modelRecvChainOfTr interpretation S g c' := by
    unfold eraseRecvChain modelRecvChainOfTr; dsimp only; rw [hsrk0, htheir, hCkNextVal]
  have hR2RcErase : r2.receiverChains.map eraseRecvChain = (setRecvChain st.recv c').map (modelRecvChainOfTr interpretation S g) := by
    rw [hR2Eq]; dsimp only; rw [List.map_set, hMap, hEraseCh', ← List.map_set, setRecvChain_eq_set_of_getElem?_nodup_tr st.recv ci c c' hNodup hc0 rfl]
  have hRkLens := rkLens_of_stateRel_tr hrel
  have hRkLens' : ∀ c0 ∈ setRecvChain st.recv c', (gamma interpretation S g c0.ratchetKey).length = 32 := by
    intro c0 hc0'
    rcases mem_setRecvChain_tr hc0' with rfl | hold
    · exact hRkLens c (List.mem_of_getElem? hc0)
    · exact hRkLens c0 hold
  have hCkLens' : ∀ c0 ∈ setRecvChain st.recv c', (gamma interpretation S g c0.chainKey).length = 32 := by
    intro c0 hc0'
    rcases mem_setRecvChain_tr hc0' with rfl | hold
    · exact length_gamma_kdfCk_fst_tr interpretation S g (chainKeyAt c.chainKey n)
    · exact hCkLens c0 hold
  refine ⟨ci, ch, c, mks', seed, c', hch0, hc0, hFindSym, hsrk0, htheir, hck, hch_ck,
    hConsSym, hSeedEq, hCkAdvIdx, rfl, rfl, hR2Eq,
    stateRel_of_recvMap_tr interpretation S g hrel hRkLens' hCkLens' hspqr' hR2RcErase, ?_⟩
  intro k hk
  rcases hMksSub k hk with hSkip | hOld
  · right; rw [hn_eq, hck] at hSkip
    obtain ⟨j, hjLt, hjCnt, hjSeed⟩ := skippedKeys_mem_gamma_kdfCk_tr interpretation S g c.chainKey c.index.toBitVec n hCkLen k hSkip
    have hjU32 : UInt32.ofBitVec k.counter = c.index + UInt32.ofNat j := by rw [hjCnt, uint32_ofBitVec_add_ofNat]
    have hjNe : UInt32.ofBitVec k.counter ≠ msgCounter := by
      intro hEqCnt
      have h1 : (c.index.toBitVec + BitVec.ofNat 32 j).toNat = counter.toNat := by
        have hbv : k.counter = counter := congrArg UInt32.toBitVec hEqCnt
        exact congrArg BitVec.toNat (hjCnt.symm.trans hbv)
      have hadd : c.index.toBitVec.toNat + n = counter.toNat := by
        have h := index_toNat_add_sub_eq ck counter hLe; rwa [hn_eq, hCkIdx] at h
      have hlt32 : c.index.toBitVec.toNat + j < 2 ^ 32 := by have := counter.isLt; omega
      have htoNat : (c.index.toBitVec + BitVec.ofNat 32 j).toNat = c.index.toBitVec.toNat + j := by
        rw [BitVec.toNat_add, BitVec.toNat_ofNat]; omega
      omega
    exact ⟨j, hjLt, hjCnt, hjU32, hjNe, hjSeed,
      by rw [hjSeed]; exact length_gamma_kdfCk_snd_tr interpretation S g (chainKeyAt c.chainKey j)⟩
  · exact Or.inl hOld

theorem matchedPrefix_decrypt_noRatchet_two_attackerSend {interpretation : ExternInterpretation} {r₀ : ProtocolSetup} {S : SpqrSem}
    {who : List Participant} {g' : Ghost} {ms₁ : List Move} {evs acc : List MachineEvent}
    {p : Participant} {stateIdx : Nat} {spqrMsgIdx : UInt32} {st : TRState} {c c' : RecvChain}
    {t seed key pqSalt ptTerm spqr' : DY.Bytes} {msg : TRSignalMsg} {body outPt : HwBytes}
    (hmp : DY.Libsignal.Composed.Refinement.MatchedPrefix interpretation r₀ S who g' ms₁ (acc ++ evs))
    (hpqSalt_kn : pqSalt.AttackerKnows (runTraceMoves r₀ ms₁)) (ht_kn : t.AttackerKnows (runTraceMoves r₀ ms₁))
    (hcur : isCurrentSnapshot (runTraceMoves r₀ ms₁) stateIdx = true)
    (hst : ((PersistentLocalState.getLocalState p stateIdx : Traceful TRState).run (runTraceMoves r₀ ms₁)).1 = some st)
    (hparse : parseTrSignalMsg t = some msg) (hver : msg.version = messageVersion)
    (hfind : findRecvChain st.recv msg.ratchetKey = some c)
    (hcons : consumeMessageKey c msg.counter = some (seed, c'))
    (hspqr : Spqr.spqrRecv st.spqr msg.pqRatchet spqrMsgIdx = some (spqr', key))
    (hmac_eq : msg.mac = computeMac (trMsgKeys pqSalt seed).macKey st.peerIk st.myIk msg.wire)
    (hdec : DY.SymEnc.symDec (trMsgKeys pqSalt seed).cipherKey (trMsgKeys pqSalt seed).iv msg.ciphertext = some ptTerm)
    (ht_gam : gamma interpretation S g' t = body) (hpt_gam : gamma interpretation S g' ptTerm = outPt)
    (hwho : who[callCount (runVis r₀ ms₁)]? = some p)
    (ht_rep : t ∈ recvRepresentations interpretation r₀ S g' ms₁ body) :
    DY.Libsignal.Composed.Refinement.MatchedPrefix interpretation r₀ S who g'
      (ms₁ ++ [.attackerSend pqSalt, .attackerSend t,
        .decrypt p stateIdx ((runTraceMoves r₀ ms₁).length + 1) (runTraceMoves r₀ ms₁).length spqrMsgIdx false])
      (acc ++ (evs ++ [.recv (wireWhisperTag :: body)] ++ [] ++ [.accept outPt])) := by
  let tr₀ := runTraceMoves r₀ ms₁
  let ms_a1 := ms₁ ++ [Move.attackerSend pqSalt]; let ms_a2 := ms_a1 ++ [Move.attackerSend t]
  have htr_a1 : runTraceMoves r₀ ms_a1 = tr₀.append (⟨pqSalt⟩ : Network.ExecEntryT) := by
    rw [runTrace_snoc, b5_attackerSend_next]
  have htr_a2 : runTraceMoves r₀ ms_a2 = (tr₀.append (⟨pqSalt⟩ : Network.ExecEntryT)).append (⟨t⟩ : Network.ExecEntryT) := by
    rw [runTrace_snoc, htr_a1, b5_attackerSend_next]
  have hmp1 := matchedPrefix_attackerSend hmp hpqSalt_kn
  have ht_kn1 : t.AttackerKnows (runTraceMoves r₀ ms_a1) := by
    rw [htr_a1]; exact DY.Bytes.AttackerKnows_le t tr₀ _ (Trace.append_le tr₀ _) ht_kn
  have hmp2 := matchedPrefix_attackerSend hmp1 ht_kn1
  have hwho2 : who[callCount (runVis r₀ ms_a2)]? = some p := by
    have hv : runVis r₀ ms_a2 = runVis r₀ ms₁ := by
      change runVis r₀ ((ms₁ ++ [Move.attackerSend pqSalt]) ++ [Move.attackerSend t]) = runVis r₀ ms₁
      rw [runVis_snoc, vis_attackerSend_nil, List.append_nil, runVis_snoc, vis_attackerSend_nil, List.append_nil]
    rw [hv]; exact hwho
  have ht_rep2 : t ∈ recvRepresentations interpretation r₀ S g' ms_a2 body :=
    ⟨by rw [htr_a2]; rw [htr_a1] at ht_kn1; exact DY.Bytes.AttackerKnows_le t _ _ (Trace.append_le _ _) ht_kn1, ht_rep.2⟩
  have hcur2 : isCurrentSnapshot (runTraceMoves r₀ ms_a2) stateIdx = true := by
    rw [htr_a2, isCurrentSnapshot_append_non_st _ _ rfl, isCurrentSnapshot_append_non_st _ _ rfl]; exact hcur
  have hst2 : ((PersistentLocalState.getLocalState p stateIdx : Traceful TRState).run (runTraceMoves r₀ ms_a2)).1 = some st := by
    rw [runTrace_snoc, getLocalState_attackerSend, runTrace_snoc, getLocalState_attackerSend]; exact hst
  have hmsg2 : (runTraceMoves r₀ ms_a2).getMessageSentAt (tr₀.length + 1) = some t := by
    rw [htr_a2]
    have hlen : tr₀.length + 1 = (tr₀.append (⟨pqSalt⟩ : Network.ExecEntryT)).length := by
      simp only [Symbolic.DYBridge.DY.Trace.append_eq_1, Symbolic.DYBridge.DY.Trace.length_eq_2]
    rw [hlen, Symbolic.DYBridge.DY.Trace.getMessageSentAt_eq_1, Trace.at?_append]
  have hpqSalt2 : (((runTraceMoves r₀ ms_a2).append (⟨key⟩ : Network.ExecEntryT)).at? tr₀.length :
      Option Network.ExecEntryT) = some ⟨pqSalt⟩ := by
    rw [htr_a2,
        at?_append_of_lt _ _ (by simp only [Symbolic.DYBridge.DY.Trace.append_eq_1, Symbolic.DYBridge.DY.Trace.length_eq_2]; omega),
        at?_append_of_lt _ _ (by simp only [Symbolic.DYBridge.DY.Trace.append_eq_1, Symbolic.DYBridge.DY.Trace.length_eq_2]; omega)]
    exact Trace.at?_append tr₀ (⟨pqSalt⟩ : Network.ExecEntryT)
  have hstep := matchedPrefix_step_decrypt_noRatchet hmp2 hcur2 hst2 hmsg2 hparse hver hfind
    hcons hspqr hpqSalt2 hmac_eq hdec ht_gam hpt_gam hwho2 ht_rep2
  have hms_eq : ms_a2 ++ [Move.decrypt p stateIdx (tr₀.length + 1) tr₀.length spqrMsgIdx false] =
      ms₁ ++ [.attackerSend pqSalt, .attackerSend t, .decrypt p stateIdx (tr₀.length + 1) tr₀.length spqrMsgIdx false] := by
    simp only [ms_a2, ms_a1, List.append_assoc, List.cons_append, List.nil_append]
  have hevs_eq : (acc ++ evs) ++ [.recv (wireWhisperTag :: body), .accept outPt] =
      acc ++ (evs ++ [.recv (wireWhisperTag :: body)] ++ [] ++ [.accept outPt]) := by
    simp only [List.append_assoc, List.cons_append, List.nil_append]
  rw [← hms_eq, ← hevs_eq]; exact hstep

private theorem logSkippedKeysTr_eq_recvDec (s : SessionInfo) (pk : DY.Bytes) (rIdx sourceStateIdx : Nat)
    (ck : DY.Bytes) (n : UInt32) (k : Nat) (tr : ExecTrace) :
    RecvDec.logSkippedKeysTr s pk rIdx sourceStateIdx ck n k tr =
      logSkippedKeysTr s pk rIdx sourceStateIdx ck n k tr := by
  induction k generalizing ck n tr with
  | zero => rfl
  | succ k ih => unfold RecvDec.logSkippedKeysTr logSkippedKeysTr; exact ih _ _ _

theorem decTailTr_eq_recvDec (tr_pre : ExecTrace) (me : Participant) (stateIdx : Nat)
    (st1 : TRState) (c c' : RecvChain) (pk seed pqSalt ptTerm spqr' : DY.Bytes) (n : UInt32) :
    RecvDec.decTailTr tr_pre me stateIdx st1 c c' pk seed pqSalt ptTerm spqr' n =
      decTailTr tr_pre me stateIdx st1 c c' pk seed pqSalt ptTerm spqr' n := by
  unfold RecvDec.decTailTr decTailTr
  rw [logSkippedKeysTr_eq_recvDec]

end Symbolic.Swarm.CREF.CliPure.TR.RecvDecStep
