/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Symbolic.Proofs.Swarm.CREF.RecvWire.SlotG2HelpersPure
public import Symbolic.Proofs.Swarm.CREF.TR.RecvDecStepSkippedG1AtPureA
import Batteries.Data.UInt
public import Symbolic.Proofs.Swarm.CREF.Cli.Rpk.RecvAtFactsPure
public import Symbolic.Proofs.Swarm.CREF.Cli.Rpk.RecvDecStepSpqrPureA
public import Symbolic.Proofs.Swarm.CREF.RecvWire.AcceptSplitPure
public import Symbolic.Proofs.Swarm.CREF.RecvWire.RcvByPureA
public import Symbolic.Proofs.Swarm.CREF.RecvWire.ReadableBy2Pure
import Symbolic.Proofs.Swarm.CREF.Cli.Rpk.R3ChainsWFPresPure
import Symbolic.Proofs.Swarm.CREF.Cli.Rpk.RecvDecStepSpqrPure
import Symbolic.Proofs.Swarm.CREF.Cli.Rpk.SendRetCoinsCliPure
import Symbolic.Proofs.Swarm.CREF.Cli.Rpk.SendRetCoinsCliPureB
import Symbolic.Proofs.Swarm.CREF.Cli.World.RelCliPure
import Symbolic.Proofs.Swarm.CREF.Prelude
import Symbolic.Proofs.Swarm.CREF.RecvWire.AcceptNewRecPendingAPure
import Symbolic.Proofs.Swarm.CREF.RecvWire.RcvByPure
import Symbolic.Proofs.Swarm.CREF.RecvWire.SkippedProvBPure
import Symbolic.Proofs.Swarm.CREF.RecvWire.SlotG2BranchesPure
import Symbolic.Proofs.Swarm.CREF.RecvWire.SlotG2ProvBPure
import Symbolic.Proofs.Swarm.CREF.RecvWire.SpinePeelPure
import Symbolic.Proofs.Swarm.CREF.TR.G1.LitKeyKnownFinal
import Symbolic.Proofs.Swarm.CREF.TR.PureRecvStepBridge
import Symbolic.Proofs.Swarm.CREF.TR.RecvDecStepSkippedProvTR
import Symbolic.Proofs.Swarm.CREF.TR.RecvRep
import Symbolic.Proofs.Swarm.CREF.TROpen
import Symbolic.Proofs.Swarm.TRREF.HooksOKXTRPure

/-!
# Accepting Whisper Receive Witness Assembly

Combines the skipped-key, no-ratchet, and DH-ratchet decrypt-branch witnesses into
`recvWireStepWitness_of_acceptCallBy₂K` for an accepting Whisper receive call.
-/

@[expose] public section

cref_hide_foreign_instances
set_option autoImplicit false

namespace Symbolic.Swarm.CREF.CliPureRcv.RecvWirePure
open Symbolic.Swarm.CREF Symbolic.Swarm.CREF.CliPure Symbolic.Swarm.CREF.CliPureRcv
open Symbolic.Swarm.CREF.CliPureRcv.TR.RecvDecStepPure
open Symbolic.Swarm.CREF.CliPureRcv.TR.RecvDecStepAtPure
open Symbolic.Swarm.CREF.CliPureRcv.TR.RecvDecStepTiePure hiding StEntry TREntry
open DY.Libsignal.Composed.Refinement.Cli (ExternContractsHoldCli)
private theorem verifyMacWithAddresses_eq_true_iff_slotG2 (F) (m : CryptoGames.LibsignalSession.SignalMessage) (expected : Option (List (BitVec 8))) (sender receiver : CryptoGames.LibsignalSession.IdentityKey) (macKey : BitVec 256) : m.verifyMacWithAddresses F expected sender receiver macKey = true ↔ m.verifyMac F sender receiver macKey = true ∧ CryptoGames.LibsignalAead.addressCheckPasses m.addresses expected = true := by simp [CryptoGames.LibsignalSession.SignalMessage.verifyMacWithAddresses]

cref_open
cref_open_tr

open DY DY.Comparse DY.Literal DY.Libsignal DY.DiffieHellman
open DY.Libsignal.HwEvents DY.Libsignal.Rust
open CryptoGames CryptoGames.HMAC CryptoGames.HKDF
open CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open CryptoVerification
open CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalProtoCodec
open CryptoProofLib.Refinement (ExternInterpretation)
open DY.Libsignal.Composed DY.Libsignal.Composed.Refinement
open DY.Libsignal.TripleRatchet (RecvChain computeMac messageVersion)
open DY.Libsignal.TripleRatchet (TRState TREvent TRSignalMsg parseTrSignalMsg
  isCurrentSnapshot skippedKeyUsedB receiverKeyUsedB trMsgKeys)
open DY.Libsignal.TripleRatchet.Refinement (wireWhisperTag)
open DY.Libsignal.Refinement (aesCbcDecryptSymbol)
open CryptoVerification.E2E.Pqxdh.WireEntries.SymP3 (RecvWireGhost)
open Proofs.libsignal.Hooks2 (cryptoOf')
open Proofs.libsignal.RngG
open Proofs.libsignal.RngG.R3 (ratchetStateOf)
open Proofs.libsignal.RngG.CliPure.R3 (takeSkippedKey_ok_some_inv RecordChainsWF3)
open Swarm.Phase0WholeFunctionBridge (sessionToRecordRec sessionToSessionRec)
open Symbolic.Swarm.TRREF.SpqrSemOf (spqrModelOf saltToBytes)
open Symbolic.Swarm.CREF.CliPure.TR.SendRetCoins (gamma_trMsgKeys_eq_generateKeys stateRel_sessionToRecordRec_extract_TR gamma_computeMac_tr)
open Symbolic.Swarm.CREF.TR Symbolic.Swarm.CREF.CliPure.TR Symbolic.Swarm.CREF.CliPureRcv.TR
open Symbolic.Swarm.CREF.TR.RecvDec hiding StEntry TREntry TRRecvAllCollide
open Symbolic.Swarm.CREF.TR.RecvDecStep
open Symbolic.Swarm.CREF.CliPure.TR.RecvDecStep hiding StEntry TREntry
  isCurrentSnapshot_append_non_st at?_eq_none_of_le at?_append_of_lt
open Symbolic.Swarm.CREF.CliPure.TR.RecvDecStepAt
open Symbolic.Swarm.CREF.TR.G1

private theorem slotG2_skipped_trace_sidecars_and_st_prov_or_bobStart_at (interpretation : ExternInterpretation)
    (r₀ : ProtocolSetup) (hwf : ProtocolSetupWF r₀) (S : OpaqueSymbolSemantics) {who : List Participant}
    (p : Participant) (evs acc : List MachineEvent) (g : Ghost) (ms₁ : List Move)
    (st₀ : TRState) (stateIdx₀ : Nat) (g_rw : RecvWireGhost) (m : SignalMessage) (msg₀ : TRSignalMsg)
    (pk seed : DY.Bytes) (rIdx srcIdx skIdx : Nat)
    (hmp : MatchedPrefix interpretation r₀ S who g ms₁ (acc ++ evs)) (hat : RecvAtFacts interpretation r₀ S g ms₁)
    (hp_mem : p = r₀.alice ∨ p = r₀.bob)
    (hst₀ : ((PersistentLocalState.getLocalState p stateIdx₀ : Traceful TRState).run (runTraceMoves r₀ ms₁)).1 = some st₀)
    (hcur₀ : isCurrentSnapshot (runTraceMoves r₀ ms₁) stateIdx₀ = true)
    (hsk_pre₀ : ∀ c ∈ (sessionToRecordRec g_rw.sess).current.receiverChains, ∀ k ∈ c.messageKeys, ∃ pk rIdx srcIdx skIdx seed,
      (runTraceMoves r₀ ms₁).EventLoggedAt (TREvent.SkippedKeyStored (st₀.sessionInfo p) pk (UInt32.ofBitVec k.1) seed rIdx srcIdx) skIdx ∧
      (!skippedKeyUsedB (runTraceMoves r₀ ms₁) skIdx) = true ∧ (!receiverKeyUsedB (runTraceMoves r₀ ms₁) (st₀.sessionInfo p) seed (UInt32.ofBitVec k.1) rIdx) = true ∧
      gamma interpretation S g seed = k.2 ∧ c.senderRatchetKey = serializedKey (gamma interpretation S g pk))
    (hlog : (runTraceMoves r₀ ms₁).EventLoggedAt (TREvent.SkippedKeyStored (st₀.sessionInfo p) pk (UInt32.ofBitVec m.counter) seed rIdx srcIdx) skIdx)
    (hctr₀ : msg₀.counter = UInt32.ofBitVec m.counter) :
    (∀ pk_k n_k seed_k srcIdx_k skIdx_k,
      (runTraceMoves r₀ ms₁).EventLoggedAt (TREvent.SkippedKeyStored (st₀.sessionInfo p) pk_k n_k seed_k rIdx srcIdx_k) skIdx_k → pk_k = pk) ∧
    (∀ c_k ∈ (sessionToRecordRec g_rw.sess).current.receiverChains, ∀ k ∈ c_k.messageKeys, ∃ pk_k rIdx_k srcIdx_k skIdx_k seed_k,
      (runTraceMoves r₀ ms₁).EventLoggedAt (TREvent.SkippedKeyStored (st₀.sessionInfo p) pk_k (UInt32.ofBitVec k.1) seed_k rIdx_k srcIdx_k) skIdx_k ∧
      (!skippedKeyUsedB (runTraceMoves r₀ ms₁) skIdx_k) = true ∧ (!receiverKeyUsedB (runTraceMoves r₀ ms₁) (st₀.sessionInfo p) seed_k (UInt32.ofBitVec k.1) rIdx_k) = true ∧
      gamma interpretation S g seed_k = k.2 ∧ c_k.senderRatchetKey = serializedKey (gamma interpretation S g pk_k)) ∧
    TR.G1.RecvHistInvTR interpretation S g r₀ ms₁ ∧ TR.G1.InstallWitnessTR r₀ (runTraceMoves r₀ ms₁) ∧
    (TR.G1.JunkTR pk → ∀ x, pk.view? DY.X25519.Variant.SubF = some x → seed.AttackerKnows (runTraceMoves r₀ ms₁)) ∧
    ∃ (st_prov : TRState) (k_own : DY.Bytes),
      st_prov ∈ availableStates r₀ (runTraceMoves r₀ ms₁) ∧ (st_prov.peerIk = st₀.peerIk ∧ st_prov.myIk = st₀.myIk) ∧
      k_own = ({ st := st₀.spqr, msg := msg₀.pqRatchet } : DY.Spqr.RecvKey.SubF DY.Bytes).pack ∧
      k_own ∈ ownKeys r₀ (runTraceMoves r₀ ms₁) st_prov msg₀ ∧
      st_prov.peerIk.AttackerKnows (runTraceMoves r₀ ms₁) ∧ st_prov.myIk.AttackerKnows (runTraceMoves r₀ ms₁) ∧
      ((∀ msg, msg.version = messageVersion → msg.ratchetKey = pk → msg.counter = msg₀.counter → recvSeed st_prov msg = some seed) ∨
       (∃ (p_src : Participant) (c₀ : RecvChain),
         TR.G1.TRStateStoredAt p_src st_prov srcIdx (runTraceMoves r₀ ms₁) ∧
         st_prov.sessionInfo p_src = st₀.sessionInfo p ∧ st_prov.initiator = false ∧
         c₀ ∈ st_prov.recv ∧ c₀.ratchetKey = pk ∧ c₀.rIdx = rIdx ∧ msg₀.counter < c₀.index)) := by
  have hRun : ModelRun r₀ ms₁ := hmp.2.1
  have hreach : (runTraceMoves r₀ ms₁).Reachable reachability := hRun.2.2.1.1
  have hRIdxFun : ∀ pk_k n_k seed_k srcIdx_k skIdx_k,
      (runTraceMoves r₀ ms₁).EventLoggedAt (TREvent.SkippedKeyStored (st₀.sessionInfo p) pk_k n_k seed_k rIdx srcIdx_k) skIdx_k → pk_k = pk :=
    fun pk_k n_k seed_k srcIdx_k skIdx_k hlog_k =>
      (hat.fresh p stateIdx₀ st₀ hp_mem hst₀ hcur₀).2.1
        pk_k n_k seed_k srcIdx_k skIdx_k pk (UInt32.ofBitVec m.counter) seed srcIdx skIdx rIdx hlog_k hlog
  have hSeedK_var : TR.G1.JunkTR pk → ∀ x, pk.view? DY.X25519.Variant.SubF = some x → seed.AttackerKnows (runTraceMoves r₀ ms₁) :=
    fun hJunk _ _ => (TR.G1.skippedSeedKnownTR_of_litJunk hreach hlog hJunk).2
  have hIW : TR.G1.InstallWitnessTR r₀ (runTraceMoves r₀ ms₁) := installWitnessTR_of_reachable r₀ ms₁ hreach
  refine ⟨hRIdxFun, hsk_pre₀, hat.hist, hIW, hSeedK_var, ?_⟩
  rcases provEvTR_st_prov_or_bobStart r₀ hwf ms₁ p st₀ stateIdx₀ m msg₀ pk seed rIdx srcIdx skIdx
      hRun hst₀ hlog hctr₀ with
    ⟨st_prov, k_own, hst_prov, hIkEq, hseed_pk, hk_own_eq, hk_own, hPeerK, hMyK⟩ |
    ⟨p_src, st_src, c₀, k_own, hst_at, hst_avail, hIkEq, hsinfo_eq, hinit_f, hc₀, hc₀_rk, hc₀_rIdx,
      hlt, hk_own_eq, hk_own, hPeerK, hMyK⟩
  · exact ⟨st_prov, k_own, hst_prov, hIkEq, hk_own_eq, hk_own, hPeerK, hMyK, Or.inl hseed_pk⟩
  · exact ⟨st_src, k_own, hst_avail, hIkEq, hk_own_eq, hk_own, hPeerK, hMyK,
      Or.inr ⟨p_src, c₀, hst_at, hsinfo_eq, hinit_f, hc₀, hc₀_rk, hc₀_rIdx, hlt⟩⟩

set_option maxHeartbeats 400000 in
theorem skipped_g1_inputs_of_takeSkippedKey_atK
    (interpretation : ExternInterpretation) (hExt : ExternContractsHoldCli interpretation)
    (r₀ : ProtocolSetup) (hwf : ProtocolSetupWF r₀) (S : OpaqueSymbolSemantics) (hS : S = compSemOf interpretation r₀)
    {who : List Participant}
    (p : Participant) (recBytes body : HwBytes) (evs acc : List MachineEvent)
    (g : Ghost) (ms₁ : List Move) (rec₀ : RecordRec) (st₀ : TRState) (stateIdx₀ : Nat)
    (r : StateAndMessage) (g_rw : RecvWireGhost) (m : SignalMessage) {addr : Option HwBytes} (remIk : IdentityKey)
    (r2 : RatchetState) (mkGen : MessageKeyGenerator)
    (t₀ pk seed : DY.Bytes) (rIdx srcIdx skIdx : Nat) (newPqrState : HwBytes) (pqrKey : HKDF.Salt)
    (hmp : MatchedPrefix interpretation r₀ S who g ms₁ (acc ++ evs))
    (hat : RecvAtFacts interpretation r₀ S g ms₁)
    (hPkD : SkippedPkDispatchAtKPure interpretation r₀ S g ms₁ (acc ++ evs))
    (hp_mem : p = r₀.alice ∨ p = r₀.bob)
    (hrecBytes₀ : recBytes = DY.Libsignal.Composed.Refinement.recordBytes rec₀)
    (hnorm_eq : normPending rec₀ = normPending (RecvDecStep.sessionToRecordRecPending g_rw.sess))
    (hst₀ : ((PersistentLocalState.getLocalState p stateIdx₀ : Traceful TRState).run (runTraceMoves r₀ ms₁)).1 = some st₀)
    (hcur₀ : isCurrentSnapshot (runTraceMoves r₀ ms₁) stateIdx₀ = true)
    (hrel₀_sess : StateRel interpretation S g st₀ (sessionToRecordRec g_rw.sess)) (hks₀ : TRKeyShape interpretation S g st₀)
    (ht₀ : t₀ ∈ recvRepresentations interpretation r₀ S g ms₁ body)
    (hNotCol₀ : ¬RecvCollision interpretation r₀ S g ms₁ t₀)
    (hNotRS₀ : ¬ReselectCollision interpretation r₀ S g ms₁ t₀)
    (hcanon_q : TR.Pure.slots_RecordCanonical_Q TR.Pure.slots_NonEmptyV1Q recBytes g_rw.sess) (htry : SignalMessage.tryFrom protoSignalCodec body = .ok m)
    (hVer : g_rw.sess.state.version.toNat = m.messageVersion.toNat) (hRem : g_rw.sess.state.remoteIdentity = some remIk)
    (hTake : Mut.exec (RatchetState.takeSkippedKey m.senderRatchetKey m.counter) (Proofs.libsignal.RngG.R3.ratchetStateOf g_rw.sess.state) = (.ok (some mkGen), r2))
    (hMac : m.verifyMacWithAddresses (cryptoOf' interpretation).F addr remIk g_rw.sess.state.localIdentity
      (mkGen.generateKeys (cryptoOf' interpretation).F pqrKey).macKey = true)
    (hDec : (Proofs.libsignal.SR.interpW interpretation).dec (mkGen.generateKeys (cryptoOf' interpretation).F pqrKey).cipherKey
      (mkGen.generateKeys (cryptoOf' interpretation).F pqrKey).iv m.ciphertext = some r.message)
    (hrecv_spqr : (spqrModelOf interpretation).recv g_rw.sess.state.pqRatchetState m.pqRatchet = .ok (newPqrState, pqrKey))
    (hsk_pre₀ : ∀ c ∈ (sessionToRecordRec g_rw.sess).current.receiverChains, ∀ k ∈ c.messageKeys, ∃ pk rIdx srcIdx skIdx seed,
      (runTraceMoves r₀ ms₁).EventLoggedAt (TREvent.SkippedKeyStored (st₀.sessionInfo p) pk (UInt32.ofBitVec k.1) seed rIdx srcIdx) skIdx ∧
      (!skippedKeyUsedB (runTraceMoves r₀ ms₁) skIdx) = true ∧ (!receiverKeyUsedB (runTraceMoves r₀ ms₁) (st₀.sessionInfo p) seed (UInt32.ofBitVec k.1) rIdx) = true ∧
      gamma interpretation S g seed = k.2 ∧ c.senderRatchetKey = serializedKey (gamma interpretation S g pk))
    (hlog : (runTraceMoves r₀ ms₁).EventLoggedAt (TREvent.SkippedKeyStored (st₀.sessionInfo p) pk (UInt32.ofBitVec m.counter) seed rIdx srcIdx) skIdx)
    (hseed_gam : gamma interpretation S g seed = mkGen.seed)
    (hlink : serializedKey (gamma interpretation S g pk) = m.senderRatchetKey.serialize) :
    ∃ (t₁ : DY.Bytes) (msg₁ : TRSignalMsg) (st_prov : TRState) (k_own : DY.Bytes),
      StateRel interpretation S g st₀ rec₀ ∧
      (∀ pk_k n_k seed_k srcIdx_k skIdx_k,
        (runTraceMoves r₀ ms₁).EventLoggedAt (TREvent.SkippedKeyStored (st₀.sessionInfo p) pk_k n_k seed_k rIdx srcIdx_k) skIdx_k → pk_k = pk) ∧
      (∀ c_k ∈ (sessionToRecordRec g_rw.sess).current.receiverChains, ∀ k ∈ c_k.messageKeys, ∃ pk_k rIdx_k srcIdx_k skIdx_k seed_k,
        (runTraceMoves r₀ ms₁).EventLoggedAt (TREvent.SkippedKeyStored (st₀.sessionInfo p) pk_k (UInt32.ofBitVec k.1) seed_k rIdx_k srcIdx_k) skIdx_k ∧
        (!skippedKeyUsedB (runTraceMoves r₀ ms₁) skIdx_k) = true ∧ (!receiverKeyUsedB (runTraceMoves r₀ ms₁) (st₀.sessionInfo p) seed_k (UInt32.ofBitVec k.1) rIdx_k) = true ∧
        gamma interpretation S g seed_k = k.2 ∧ c_k.senderRatchetKey = serializedKey (gamma interpretation S g pk_k)) ∧
      t₁ ∈ recvRepresentations interpretation r₀ S g ms₁ body ∧
      parseTrSignalMsg t₁ = some msg₁ ∧ msg₁.version = messageVersion ∧ msg₁.ratchetKey = pk ∧ msg₁.counter = UInt32.ofBitVec m.counter ∧
      st_prov ∈ availableStates r₀ (runTraceMoves r₀ ms₁) ∧ (st_prov.peerIk = st₀.peerIk ∧ st_prov.myIk = st₀.myIk) ∧
      gamma interpretation S g k_own = spqrKeyBytes (saltToBytes pqrKey) ∧
      body.drop (body.length - 8) = gamma interpretation S g (computeMac (trMsgKeys k_own seed).macKey st_prov.peerIk st_prov.myIk msg₁.wire) ∧
      st_prov.peerIk.AttackerKnows (runTraceMoves r₀ ms₁) ∧ st_prov.myIk.AttackerKnows (runTraceMoves r₀ ms₁) ∧
      interpretation aesCbcDecryptSymbol [m.ciphertext, gamma interpretation S g (trMsgKeys k_own seed).cipherKey,
        (gamma interpretation S g (trMsgKeys k_own seed).iv).take 16] = some r.message ∧
      (seed.AttackerKnows (runTraceMoves r₀ ms₁) ∨ ∃ salt ∈ honestSalts r₀ ms₁,
        AuthenticDecryptRepB3_g1 interpretation r₀ S g ms₁ body r.message t₁ msg₁ st_prov salt seed ∧
        gamma interpretation S g (computeMac (trMsgKeys k_own seed).macKey st_prov.peerIk st_prov.myIk msg₁.wire) =
          gamma interpretation S g (computeMac (trMsgKeys salt seed).macKey st_prov.peerIk st_prov.myIk msg₁.wire) ∧
        interpretation aesCbcDecryptSymbol [m.ciphertext, gamma interpretation S g (trMsgKeys salt seed).cipherKey,
          (gamma interpretation S g (trMsgKeys salt seed).iv).take 16] = some r.message) := by
  obtain ⟨msg₀, hparse₀⟩ := Option.isSome_iff_exists.mp ht₀.2.2.1
  have hrel₀_rec₀ : StateRel interpretation S g st₀ rec₀ := by
    rw [← stateRel_normPending_iff, hnorm_eq, stateRel_normPending_iff, stateRel_sessionToRecordRecPending_iff]; exact hrel₀_sess
  have hγ_pk : gamma interpretation S g pk = m.senderRatchetKey.bytes.toList :=
    (List.cons.inj hlink).2
  obtain ⟨_, _, hpq_sess, _, _, hver_sess, _⟩ :=
    TR.PureRecvEval.pqRatchetState_eq_gamma_pending_pure interpretation S g recBytes rec₀ st₀ st₀ g_rw hrecBytes₀ hrel₀_rec₀ hcanon_q rfl
  have hctr₀ : msg₀.counter = UInt32.ofBitVec m.counter := UInt32.ext (((ht₀.2.2.2 msg₀ hparse₀).2.2.2 m htry).2.2.2.1)
  have hver₀_nat : msg₀.version.toNat = m.messageVersion.toNat := ((ht₀.2.2.2 msg₀ hparse₀).2.2.2 m htry).2.2.2.2
  have hver_g : g_rw.sess.state.version.toNat = 4 := by unfold SessionState.version; rw [hver_sess]; rfl
  have hver₀ : msg₀.version = messageVersion := UInt8.ext (hver₀_nat.trans (hVer.symm.trans hver_g))
  obtain ⟨hRIdxFun, hsk_pre₀'', hHist, hIW, hSeedK_var,
      st_prov, k_own, hst_prov, hIkEq, hk_own_eq, hk_own, hPeerK, hMyK, hProvMB⟩ :=
    slotG2_skipped_trace_sidecars_and_st_prov_or_bobStart_at interpretation r₀ hwf S
      p evs acc g ms₁ st₀ stateIdx₀ g_rw m msg₀
      pk seed rIdx srcIdx skIdx hmp hat hp_mem hst₀ hcur₀ hsk_pre₀ hlog hctr₀
  obtain ⟨_, hk_own_gam⟩ :=
    spqrRecv_step_gamma_state_and_key interpretation hExt.1 r₀ S hS g ms₁ body st₀ g_rw
      t₀ msg₀ m newPqrState pqrKey hpq_sess ht₀ hparse₀ htry hrecv_spqr
  rw [← hk_own_eq] at hk_own_gam
  obtain ⟨_, _, _, _, _, _, _, _, hmk_ctr, _, _, _⟩ := takeSkippedKey_ok_some_inv hTake
  have hmkGen_eq : mkGen = ⟨gamma interpretation S g seed, m.counter⟩ := by
    rcases mkGen with ⟨sd, ct⟩; dsimp only at hseed_gam hmk_ctr; subst hseed_gam hmk_ctr; rfl
  obtain ⟨hck_mk, hmk_mk, hiv_mk, _⟩ :=
    gamma_trMsgKeys_eq_generateKeys interpretation S g k_own seed m.counter pqrKey hk_own_gam
  have hDecOk :
      interpretation aesCbcDecryptSymbol
        [m.ciphertext, gamma interpretation S g (trMsgKeys k_own seed).cipherKey,
         (gamma interpretation S g (trMsgKeys k_own seed).iv).take 16] = some r.message := by
    rw [← hck_mk, ← hiv_mk]
    change (Proofs.libsignal.SR.interpW interpretation).dec
      (MessageKeyGenerator.generateKeys (cryptoOf' interpretation).F ⟨gamma interpretation S g seed, m.counter⟩ pqrKey).cipherKey
      (MessageKeyGenerator.generateKeys (cryptoOf' interpretation).F ⟨gamma interpretation S g seed, m.counter⟩ pqrKey).iv m.ciphertext = some r.message
    rw [← hmkGen_eq]; exact hDec
  obtain ⟨_, _, _, hloc_ser, ⟨rem0, hrem0, hrem_ser⟩, _⟩ :=
    stateRel_sessionToRecordRec_extract_TR interpretation S g st₀ g_rw.sess hrel₀_sess
  rw [hRem] at hrem0; injection hrem0 with hrem_eq; subst hrem_eq
  have hpeer_ser : remIk.serialize = gamma interpretation S g st_prov.peerIk := by
    rw [hIkEq.1]; exact hrem_ser.trans hks₀.peerIk_ser
  have hmy_ser : g_rw.sess.state.localIdentity.serialize = gamma interpretation S g st_prov.myIk := by
    rw [hIkEq.2]; exact hloc_ser.trans hks₀.myIk_ser
  have hwire₀_take : gamma interpretation S g msg₀.wire = body.take (body.length - 8) :=
    (ht₀.2.2.2 msg₀ hparse₀).1
  have hm_ser : m.serialized = body :=
    tryFrom_serialized_eq_slotG2 htry
  have hMacBytes :
      body.drop (body.length - 8) =
        gamma interpretation S g (computeMac (trMsgKeys k_own seed).macKey st_prov.peerIk st_prov.myIk msg₀.wire) := by
    have hmac_ver : m.verifyMac (cryptoOf' interpretation).F remIk g_rw.sess.state.localIdentity
        (mkGen.generateKeys (cryptoOf' interpretation).F pqrKey).macKey = true :=
      ((verifyMacWithAddresses_eq_true_iff_slotG2 _ _ _ _ _ _).mp hMac).1
    unfold SignalMessage.verifyMac macLength at hmac_ver
    dsimp only at hmac_ver
    have hmac_eq := (beq_iff_eq.mp hmac_ver).symm
    rw [hm_ser] at hmac_eq
    rw [hmac_eq]
    have hkey_mk : keyToBytes32 ((mkGen.generateKeys (cryptoOf' interpretation).F pqrKey).macKey) =
        gamma interpretation S g (trMsgKeys k_own seed).macKey := by
      rw [hmkGen_eq]; exact hmk_mk
    exact gamma_computeMac_tr interpretation S g (trMsgKeys k_own seed).macKey
      st_prov.peerIk st_prov.myIk msg₀.wire remIk g_rw.sess.state.localIdentity
      ((mkGen.generateKeys (cryptoOf' interpretation).F pqrKey).macKey)
      hkey_mk hpeer_ser hmy_ser (body.take (body.length - 8)) hwire₀_take.symm
  have hDisp :
      ∃ (t₁ : DY.Bytes) (msg₁ : TRSignalMsg),
        t₁ ∈ recvRepresentations interpretation r₀ S g ms₁ body ∧ parseTrSignalMsg t₁ = some msg₁ ∧
        msg₁.version = messageVersion ∧ msg₁.ratchetKey = pk ∧ msg₁.counter = msg₀.counter ∧
        body.drop (body.length - 8) = gamma interpretation S g (computeMac (trMsgKeys k_own seed).macKey st_prov.peerIk st_prov.myIk msg₁.wire) ∧
        (seed.AttackerKnows (runTraceMoves r₀ ms₁) ∨ ∃ salt ∈ honestSalts r₀ ms₁,
          AuthenticDecryptRepB3_g1 interpretation r₀ S g ms₁ body r.message t₁ msg₁ st_prov salt seed ∧
          gamma interpretation S g (computeMac (trMsgKeys k_own seed).macKey st_prov.peerIk st_prov.myIk msg₁.wire) =
            gamma interpretation S g (computeMac (trMsgKeys salt seed).macKey st_prov.peerIk st_prov.myIk msg₁.wire) ∧
          interpretation aesCbcDecryptSymbol [m.ciphertext, gamma interpretation S g (trMsgKeys salt seed).cipherKey,
            (gamma interpretation S g (trMsgKeys salt seed).iv).take 16] = some r.message) := by
    rcases hProvMB with hseed_pk | ⟨p_src, c₀, hst_at, hsinfo_eq, hinit_f, hc₀, hc₀_rk, hc₀_rIdx, hlt⟩
    · exact hPkD p stateIdx₀ body r.message m st₀ st_prov t₀ pk seed k_own msg₀ rIdx srcIdx skIdx
        htry ht₀ hparse₀ hver₀ hctr₀ hNotCol₀ hNotRS₀ hst₀ hst_prov
        hIkEq hseed_pk hk_own hk_own_eq hlog hHist hIW hSeedK_var hγ_pk hMacBytes hPeerK hMyK hDecOk
    · exact slotG2_skipped_provB_dispatch_at hExt.1 p p_src body r.message m st₀ st_prov
        c₀ t₀ pk seed k_own msg₀ rIdx srcIdx skIdx hmp hat htry ht₀ hparse₀ hver₀ hctr₀
        hNotCol₀ hst_at hst_prov hsinfo_eq hinit_f hc₀ hc₀_rk hc₀_rIdx hlt hk_own hlog
        hIW hγ_pk hMacBytes hPeerK hMyK hDecOk
  obtain ⟨t₁, msg₁, ht₁_rep, hparse₁, hver₁, hrk₁, hctr₁, hMacBytes₁, hDisj⟩ := hDisp
  exact ⟨t₁, msg₁, st_prov, k_own, hrel₀_rec₀,
    hRIdxFun, hsk_pre₀'', ht₁_rep, hparse₁, hver₁, hrk₁, hctr₁.trans hctr₀,
    hst_prov, hIkEq, hk_own_gam, hMacBytes₁, hPeerK, hMyK, hDecOk, hDisj⟩

set_option maxHeartbeats 400000 in
theorem recvWireStepWitness_of_skipped_branchK
    (interpretation : ExternInterpretation) (hExt : ExternContractsHoldCli interpretation)
    (r₀ : ProtocolSetup) (hwf : ProtocolSetupWF r₀) (S : OpaqueSymbolSemantics) (hS : S = compSemOf interpretation r₀)
    {who : List Participant} {slots : PureTRSlots}
    (records : Participant → Option HwBytes) (sent : List HwBytes) (p : Participant) (recBytes body : HwBytes)
    (acc : List MachineEvent) (g : Ghost) (ms₁ : List Move) (r : StateAndMessage) (g_rw : RecvWireGhost) (m : SignalMessage)
    (ci : Nat) (rc : ReceiverChain) (ck : ChainKey) (newPqrState : HwBytes) (pqrKey : HKDF.Salt)
    (hmp : MatchedPrefix interpretation r₀ S who g ms₁ acc) (hrsi : PureTRRecordStateInv interpretation r₀ S slots g ms₁ records)
    (hat : RecvAtFacts interpretation r₀ S g ms₁)
    (hPkD : SkippedPkDispatchAtKPure interpretation r₀ S g ms₁ acc)
    (hsent : sent = sentBodies acc) (hfit : SrHonestVer.SendsFit acc) (hrec : records p = some recBytes)
    (hpq : PqFromHonest sent body) (t : DY.Bytes) (ht : t ∈ recvRepresentations interpretation r₀ S g ms₁ body)
    (hnocol : ¬ RecvCollision interpretation r₀ S g ms₁ t)
    (hnors : ¬ ReselectCollision interpretation r₀ S g ms₁ t) (hwire : g_rw.wireBytes = wireWhisperTag :: body)
    (hcanon_q : TR.Pure.slots_RecordCanonical_Q TR.Pure.slots_NonEmptyV1Q recBytes g_rw.sess) (htry : SignalMessage.tryFrom protoSignalCodec body = .ok m)
    (hrc : g_rw.sess.state.receiverChains[ci]? = some rc) (hrc_key : rc.senderRatchetKey = m.senderRatchetKey)
    (hck : rc.chainKey = some ck) (hskip_idx : m.counter < ck.index)
    (hrecv_spqr : (spqrModelOf interpretation).recv
        g_rw.sess.state.pqRatchetState m.pqRatchet = .ok (newPqrState, pqrKey))
    (heval : TR.PureRecvEval.pureEvalRecvWireWithCoinsW (cryptoOf' interpretation)
        (Proofs.libsignal.SR.interpW interpretation) (spqrModelOf interpretation) g_rw 0#256 =
        some (r.state, r.message))
    (hwho : who[callCount (runVis r₀ ms₁)]? = some p) :
    RecvWireRawWitness interpretation r₀ S who g ms₁ acc [] p body r.message := by
  have hmp_nil : MatchedPrefix interpretation r₀ S who g ms₁ (acc ++ []) := by simpa only [List.append_nil] using hmp
  have hPkD_nil : SkippedPkDispatchAtKPure interpretation r₀ S g ms₁ (acc ++ []) := by simpa only [List.append_nil] using hPkD
  have hsent_nil : sent = sentBodies (acc ++ []) := by simpa only [List.append_nil] using hsent
  have hfit_nil : SrHonestVer.SendsFit (acc ++ []) := by simpa only [List.append_nil] using hfit
  obtain ⟨hp_mem, rec₀, st₀, stateIdx₀, hrecBytes₀, hst₀, hcur₀, hrel₀, _hsk_pre₀, _hcanon₀, hks₀, hnd₀⟩ :=
    hrsi p recBytes hrec
  have hnorm_eq : normPending rec₀ = normPending (RecvDecStep.sessionToRecordRecPending g_rw.sess) :=
    TR.PureRecvEval.rec_eq_sessionToRecordRec_of_pureCanonical_Q hrecBytes₀ hcanon_q
  have hrc_rec₀ : rec₀.current.receiverChains = (sessionToRecordRec g_rw.sess).current.receiverChains :=
    congrArg (fun r => r.current.receiverChains) hnorm_eq
  have hrel₀_sess : StateRel interpretation S g st₀ (sessionToRecordRec g_rw.sess) := by
    rw [← stateRel_sessionToRecordRecPending_iff, ← stateRel_normPending_iff, ← hnorm_eq, stateRel_normPending_iff]
    exact hrel₀
  have hsk_pre₀_sess : ∀ c ∈ (sessionToRecordRec g_rw.sess).current.receiverChains, ∀ k ∈ c.messageKeys,
      ∃ pk rIdx srcIdx skIdx seed,
        (runTraceMoves r₀ ms₁).EventLoggedAt
          (TREvent.SkippedKeyStored (st₀.sessionInfo p) pk (UInt32.ofBitVec k.1) seed rIdx srcIdx) skIdx ∧
        (!skippedKeyUsedB (runTraceMoves r₀ ms₁) skIdx) = true ∧
        (!receiverKeyUsedB (runTraceMoves r₀ ms₁) (st₀.sessionInfo p) seed (UInt32.ofBitVec k.1) rIdx) = true ∧
        gamma interpretation S g seed = k.2 ∧
        c.senderRatchetKey = serializedKey (gamma interpretation S g pk) ∧
        (DY.Libsignal.TripleRatchet.findRecvChain st₀.toDRState.recv pk).isSome = true :=
    hrc_rec₀ ▸ _hsk_pre₀
  have hnd₀_sess : RecordChainsWF3 (sessionToRecordRec g_rw.sess) :=
    ⟨hrc_rec₀ ▸ hnd₀.1, hrc_rec₀ ▸ hnd₀.2.1, hrc_rec₀ ▸ hnd₀.2.2⟩
  have hnodup_rc : (g_rw.sess.state.receiverChains.map ReceiverChain.senderRatchetKey).Nodup := by
    have hmap : (sessionToRecordRec g_rw.sess).current.receiverChains.map ChainRec.senderRatchetKey =
        (g_rw.sess.state.receiverChains.map ReceiverChain.senderRatchetKey).map PublicKey.serialize := by
      dsimp only [sessionToRecordRec, sessionToSessionRec]; rw [List.map_map, List.map_map]; rfl
    exact List.Nodup.of_map PublicKey.serialize (hmap ▸ hnd₀_sess.1)
  obtain ⟨_role, remIk, r2, mkGen, _st', _hrole, hVer, hRem, hTake, hMac, hDec, _hSt', _hr_enc⟩ :=
    evalRecvWireWithCoinsW_skipped_inv_g1 interpretation body r g_rw m ci rc ck newPqrState pqrKey
      hwire htry hrc hrc_key hck hskip_idx hnodup_rc hrecv_spqr heval
  obtain ⟨pk, rIdx, srcIdx, skIdx, seed, hlog, hsk_at, hunused, _hru, hseed_gam, hlink, hfind_pk⟩ :=
    extract_skippedKeyStored_of_takeSkippedKey_g1 interpretation r₀ S g ms₁ rfl hsk_pre₀_sess hTake
  obtain ⟨t₁, msg₁, st_prov, k_own, hrel₀_rec₀,
      _hRIdxFun, _hsk_pre₀'', ht₁_rep, hparse₁, hver₁, hrk₁, hctr₁,
      _hst_prov, hIkEq, hk_own_gam, hMacBytes₁, hPeerK, hMyK, hDecOk, hDisj⟩ :=
    skipped_g1_inputs_of_takeSkippedKey_atK interpretation hExt r₀ hwf S hS
      p recBytes body [] acc g ms₁
      rec₀ st₀ stateIdx₀ r g_rw m remIk r2 mkGen t pk seed rIdx srcIdx skIdx newPqrState pqrKey
      hmp_nil hat hPkD_nil hp_mem hrecBytes₀ hnorm_eq hst₀ hcur₀ hrel₀_sess hks₀ ht hnocol hnors hcanon_q
      htry hVer hRem hTake hMac hDec hrecv_spqr
      (fun c hc k hk => let ⟨pk, rIdx, srcIdx, skIdx, seed, h1, h2, h3, h4, h5, _⟩ := hsk_pre₀_sess c hc k hk; ⟨pk, rIdx, srcIdx, skIdx, seed, h1, h2, h3, h4, h5⟩)
      hlog hseed_gam hlink
  obtain ⟨t_m, msg', pqSalt, ptTerm, spqr', key, spqrMsgIdx, ht_m_rep, hpqSalt_kn, ht_m_kn,
      hparse', hver', hrk', hctr'_msg₁, hspqr_step, _hspqr'_gam, hmac', hdec', ht_m_gam, hpt_gam⟩ :=
    decryptWitness_of_g1_disj_at interpretation hExt.1
      r₀ S hS g p stateIdx₀ ms₁ (acc ++ []) sent
      recBytes body r.message rec₀ st₀ st₀ st_prov g_rw
      t₁ msg₁ m pk seed k_own newPqrState pqrKey
      hmp_nil hfit_nil hsent_nil hrecBytes₀ hrel₀_rec₀ rfl hst₀ hcanon_q hpq htry
      ht₁_rep hparse₁ hver₁ hrk₁ hIkEq hk_own_gam hMacBytes₁ hPeerK hMyK hDecOk hrecv_spqr hDisj
  have hctr' : msg'.counter = UInt32.ofBitVec m.counter := hctr'_msg₁.trans hctr₁
  have hsk_at' : ((runTraceMoves r₀ ms₁).at? skIdx : Option RecvDec.TREntry) =
      some ⟨TREvent.SkippedKeyStored (st₀.sessionInfo p) msg'.ratchetKey msg'.counter seed rIdx srcIdx⟩ := by
    rw [hrk', hctr']; exact hsk_at
  have hmp₁ := matchedPrefix_decryptSkipped_two_attackerSend_g1
    hmp_nil hpqSalt_kn ht_m_kn hcur₀ hst₀ hparse' hver' hsk_at' hunused
    hspqr_step hmac' hdec' ht_m_gam hpt_gam hwho ht_m_rep (by rw [hrk']; exact hfind_pk)
  exact ⟨g, stateIdx₀, spqrMsgIdx, pqSalt, t_m,
    Move.decryptSkipped p stateIdx₀ ((runTraceMoves r₀ ms₁).length + 1) skIdx
      (runTraceMoves r₀ ms₁).length spqrMsgIdx false,
    cbadSigmaFrame_refl g (runTraceMoves r₀ ms₁).length, ht_m_rep, hpqSalt_kn, hcur₀,
    Or.inr ⟨skIdx, rfl⟩, by simpa using hmp₁⟩

/-- Constructs a `RecvWireRawWitness` for an accepting Whisper receive call across all three ratchet branches. -/
theorem recvWireStepWitness_of_acceptCallBy₂K
    {interpretation : ExternInterpretation} (hExt : ExternContractsHoldCli interpretation)
    {r₀ : ProtocolSetup} (hwf : ProtocolSetupWF r₀) (hik : IkShape interpretation r₀)
    {S : OpaqueSymbolSemantics} (hS : S = compSemOf interpretation r₀)
    {who : List Participant} {ok : Nat → Bool}
    {j : Nat} {p : Participant} {records : Participant → Option HwBytes} {sent accepted : List HwBytes} {opkUsed : Bool}
    {mid acc : List MachineEvent} {rec body : HwBytes} {sm : StateAndMessage}
    (hC : PureRcvAcceptCall interpretation r₀ S who ok j p records sent accepted opkUsed acc mid rec body sm)
    (g : Ghost) (ms₁ : List Move) (t : DY.Bytes)
    (hc : CleanBy interpretation r₀ S who ok g ms₁ acc)
    (ht : t ∈ recvRepresentations interpretation r₀ S g ms₁ body)
    (hnocol : ¬ RecvCollision interpretation r₀ S g ms₁ t)
    (hnors : RecvExcuseFree interpretation r₀ S who ok g ms₁ acc (.recv (wireWhisperTag :: body)) (mid ++ [.accept sm.message]) body t)
    (hfresh : TRRecvFreshAll r₀ ms₁)
    (hPkDNR : NoRatchetPkDispatchAtSt interpretation r₀ S g ms₁ acc)
    (hPkDSk : SkippedPkDispatchAtKPure interpretation r₀ S g ms₁ acc)
    (hABS' : G1cAttackerBuiltSeedExcl' interpretation r₀ S g ms₁) :
    RecvWireRawWitness interpretation r₀ S who g ms₁ acc mid p body sm.message := by
  obtain ⟨_hcanon_r0, g_rw, coins, _hwho, hwire, hcanon_q, hmid_cases, _hcoins_ok, heval⟩ :=
    rcv_pending_callEnd_of_pureAccept interpretation hC
  obtain ⟨m, newPqrState, pqrKey, htry, hrecv_spqr, hbranch⟩ :=
    evalRecvWireWithCoinsW_branch_cases interpretation body mid sm g_rw coins hwire hmid_cases heval
  have ⟨slots, hrsi⟩ : ∃ slots, PureTRRecordStateInv interpretation r₀ S slots g ms₁
      (fun q => if q = p then some rec else none) := by
    rcases pureCRecRelH_single (hC.hrel.recs hc p rec hC.hrec).2.2 hC.hss with hrsi | ⟨hp, hpend⟩
    · exact ⟨pureTrSlots r₀, hrsi⟩
    · exact ⟨pureTrSlotsPend r₀, trRecordStateInv_pend_of_aliceInitPending hp hpend⟩
  have hch := hC.hrel.hist hc
  have hat : RecvAtFacts interpretation r₀ S g ms₁ := ⟨hch.1, hch.2.1, hch.2.2.1, hch.2.2.2, hfresh⟩
  have hrec_p : (fun q => if q = p then some rec else none) p = some rec := by simp
  have hsent : sent = sentBodies acc := (hC.hrel.book hc).1
  have hfit : SrHonestVer.SendsFit acc := hC.hrel.sendsFit
  have hIW : InstallWitnessTR r₀ (runTraceMoves r₀ ms₁) :=
    installWitnessTR_of_reachable r₀ ms₁ hc.matched.2.1.2.2.1.1
  have hwho_vis : who[callCount (runVis r₀ ms₁)]? = some p := by
    rw [matchedPrefix_callCount_eq hc.matched, hC.hj]; exact hC.hwho
  rcases hbranch with
    ⟨ci, rc, ck, rfl, rfl, hrc, hrc_key, hck, hskip_idx⟩ |
    ⟨ci, rc, ck, rfl, rfl, hrc, hrc_key, hck, hstep_idx⟩ |
    ⟨rngBytes, rfl, hrng_len, rfl, hrc_none⟩
  · exact recvWireStepWitness_of_skipped_branchK interpretation hExt r₀ hwf S hS
      (fun q => if q = p then some rec else none) sent p rec body acc g ms₁ sm g_rw m
      ci rc ck newPqrState pqrKey hc.matched hrsi hat hPkDSk hsent hfit hrec_p hC.hpq
      t ht hnocol hnors.1 hwire hcanon_q htry hrc hrc_key hck hskip_idx hrecv_spqr heval hwho_vis
  · exact recvWireStepWitness_of_noRatchet_branch interpretation hExt r₀ hwf S hS
      (fun q => if q = p then some rec else none) sent p rec body acc g ms₁ sm g_rw m
      ci rc ck newPqrState pqrKey hc.matched hrsi hat hsent hfit hrec_p hC.hpq
      t ht hnocol hnors.1 hwire hcanon_q htry hrc hrc_key hck hstep_idx hrecv_spqr heval hIW hPkDNR hwho_vis
  · exact recvWireStepWitness_of_ratchetDH_branch interpretation hExt r₀ hwf hik S hS
      (fun q => if q = p then some rec else none) sent p rec body rngBytes acc g ms₁ sm g_rw m
      newPqrState pqrKey hc.matched hc.1 hrsi hat hsent hfit hrec_p hC.hpq hC.hstate_lt
      t ht hnocol hwire hcanon_q hrng_len htry hrc_none hrecv_spqr heval hABS' hwho_vis

end Symbolic.Swarm.CREF.CliPureRcv.RecvWirePure
