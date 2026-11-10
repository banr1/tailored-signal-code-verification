/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Symbolic.Proofs.Swarm.CREF.RecvWire.ReadableBy2Pure
import Batteries.Data.UInt
public import Symbolic.Proofs.Swarm.CREF.Cli.PureCRel
public import Symbolic.Proofs.Swarm.CREF.Cli.Rpk.PkDispatchAtPure
public import Symbolic.Proofs.Swarm.CREF.Cli.Rpk.RecvAtFactsPure
public import Symbolic.Proofs.Swarm.CREF.TR.G1.OwnKeyBranch
public import Symbolic.Proofs.Swarm.CREF.TR.RecvDecStepSkippedG1LeavesPure
import Symbolic.Proofs.Swarm.CREF.Cli.Rpk.DecCryptoBPure
import Symbolic.Proofs.Swarm.CREF.Cli.Rpk.RatchetDHRkSwapStepTRPureA
import Symbolic.Proofs.Swarm.CREF.Cli.Rpk.RecvDecStepCommonPure
import Symbolic.Proofs.Swarm.CREF.Cli.Rpk.RecvDecStepNoRatchetPure
import Symbolic.Proofs.Swarm.CREF.Cli.Rpk.RecvDecStepRatchetDHaPure
import Symbolic.Proofs.Swarm.CREF.Cli.Rpk.RecvDecStepSpqrPure
import Symbolic.Proofs.Swarm.CREF.Cli.Rpk.SendRetCoinsCliPure
import Symbolic.Proofs.Swarm.CREF.Cli.Rpk.SendRetCoinsCliPureB
import Symbolic.Proofs.Swarm.CREF.Initiate.InitRej
import Symbolic.Proofs.Swarm.CREF.Prelude
import Symbolic.Proofs.Swarm.CREF.TR.PureRecvStepBridge
import Symbolic.Proofs.Swarm.CREF.TR.RecvDecStepNoRatchetWAtPure
import Symbolic.Proofs.Swarm.CREF.TR.RecvDecStepRatchetDHAtPure
import Symbolic.Proofs.Swarm.CREF.TR.TrStateRkCkIk
import Symbolic.Proofs.Swarm.CREF.TROpen
public import Symbolic.Proofs.Swarm.CREF.TR.RecvCol -- shake: keep

/-!
# `NoRatchet` and `RatchetDH` Branch Witnesses for Whisper Receive

Constructs `RecvWireRawWitness` for the `NoRatchet` and `RatchetDH` decryption branches of
incoming Whisper messages.
-/

@[expose] public section

cref_hide_foreign_instances
set_option autoImplicit false

namespace Symbolic.Swarm.CREF.CliPureRcv.RecvWirePure
open Symbolic.Swarm.CREF Symbolic.Swarm.CREF.CliPure Symbolic.Swarm.CREF.CliPureRcv
open Symbolic.Swarm.CREF.CliPureRcv.TRPure
open Symbolic.Swarm.CREF.CliPureRcv.TR.RecvDecStepPure
open Symbolic.Swarm.CREF.CliPureRcv.TR.RecvDecStepAtPure
open DY.Libsignal.Composed.Refinement.Cli (ExternContractsHoldCli)

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
open DY.Libsignal.TripleRatchet (RecvChain findRecvChain recvChainFor consumeMessageKey computeMac
  messageVersion x25519LowOrder)
open DY.Libsignal.TripleRatchet (trMsgKeys)
open DY.Libsignal.TripleRatchet.Refinement (wireWhisperTag)
open DY.Libsignal.Refinement (sha256CompressFunction aesCbcDecryptSymbol)
open CryptoVerification.E2E.Pqxdh.WireEntries.SymP3 (RecvWireGhost)
open Proofs.libsignal.Hooks2 (cryptoOf')
open Proofs.libsignal.RngG.R3 (dhRatchetStep_ok_inv)
open Proofs.libsignal.RngG.CliPure.R3 (RecordChainsWF3)
open Swarm.Phase0WholeFunctionBridge (sessionToRecordRec sessionToSessionRec)
open Symbolic.Swarm.TRREF.SpqrSemOf (spqrModelOf saltToBytes)
open Symbolic.Swarm.CREF.CliPure.TR.SendRetCoins (gamma_trMsgKeys_eq_generateKeys stateRel_sessionToRecordRec_extract_TR gamma_computeMac_tr)
open Symbolic.Swarm.CREF.TR Symbolic.Swarm.CREF.CliPure.TR Symbolic.Swarm.CREF.CliPureRcv.TR
open Symbolic.Swarm.CREF.TR.RecvDec hiding StEntry TREntry TRRecvAllCollide
open Symbolic.Swarm.CREF.TR.RecvDecStep
open Symbolic.Swarm.CREF.CliPure.TR.RecvDecStep hiding StEntry TREntry
  isCurrentSnapshot_append_non_st at?_eq_none_of_le at?_append_of_lt
open Symbolic.Swarm.CREF.CliPure.TR.RecvDecStepAt
open Symbolic.Swarm.CREF.TR.FreshSigma hiding TREntry StEntry
open Symbolic.Swarm.CREF.TR.G1 Symbolic.Swarm.CREF.CliPure.TR.G1

theorem tryFrom_serialized_eq_slotG2 {body : HwBytes} {m : SignalMessage}
    (htry : SignalMessage.tryFrom protoSignalCodec body = .ok m) : m.serialized = body := by
  simp only [SignalMessage.tryFrom, bind, Except.bind, Pure.pure, Except.pure, throw, throwThe, MonadExceptOf.throw] at htry
  split at htry; · cases htry
  split at htry; · cases htry
  split at htry; · cases htry
  split at htry <;> try cases htry
  split at htry <;> try cases htry
  split at htry <;> try cases htry
  split at htry <;> try cases htry
  split at htry <;> try cases htry
  rfl

set_option maxHeartbeats 400000 in
theorem recvWireStepWitness_of_noRatchet_branch
    (interpretation : ExternInterpretation) (hExt : ExternContractsHoldCli interpretation)
    (r₀ : ProtocolSetup) (hwf : ProtocolSetupWF r₀) (S : OpaqueSymbolSemantics) (hS : S = compSemOf interpretation r₀)
    {who : List Participant} {slots : PureTRSlots}
    (records : Participant → Option HwBytes) (sent : List HwBytes) (p : Participant) (recBytes body : HwBytes)
    (acc : List MachineEvent) (g : Ghost) (ms₁ : List Move) (r : StateAndMessage) (g_rw : RecvWireGhost) (m : SignalMessage)
    (ci : Nat) (rc : ReceiverChain) (ck : ChainKey) (newPqrState : HwBytes) (pqrKey : HKDF.Salt)
    (hmp : MatchedPrefix interpretation r₀ S who g ms₁ acc) (hrsi : PureTRRecordStateInv interpretation r₀ S slots g ms₁ records)
    (hat : RecvAtFacts interpretation r₀ S g ms₁) (hsent : sent = sentBodies acc) (hfit : SrHonestVer.SendsFit acc)
    (hrec : records p = some recBytes) (hpq : PqFromHonest sent body)
    (t : DY.Bytes) (ht : t ∈ recvRepresentations interpretation r₀ S g ms₁ body)
    (hnocol : ¬ RecvCollision interpretation r₀ S g ms₁ t)
    (hnors : ¬ ReselectCollision interpretation r₀ S g ms₁ t) (hwire : g_rw.wireBytes = wireWhisperTag :: body)
    (hcanon_q : TR.Pure.slots_RecordCanonical_Q TR.Pure.slots_NonEmptyV1Q recBytes g_rw.sess)
    (htry : SignalMessage.tryFrom protoSignalCodec body = .ok m)
    (hrc : g_rw.sess.state.receiverChains[ci]? = some rc) (hrc_key : rc.senderRatchetKey = m.senderRatchetKey)
    (hck : rc.chainKey = some ck) (hstep_idx : ck.index ≤ m.counter)
    (hrecv_spqr : (spqrModelOf interpretation).recv
        g_rw.sess.state.pqRatchetState m.pqRatchet = .ok (newPqrState, pqrKey))
    (heval : TR.PureRecvEval.pureEvalRecvWireWithCoinsW (cryptoOf' interpretation)
        (Proofs.libsignal.SR.interpW interpretation) (spqrModelOf interpretation) g_rw
        (Symbolic.Swarm.CREF.CliPureRcv.TR.RecvDecStepPure.purePinCoins none) =
        some (r.state, r.message))
    (hIW : InstallWitnessTR r₀ (runTraceMoves r₀ ms₁))
    (hPkD : NoRatchetPkDispatchAtSt interpretation r₀ S g ms₁ acc)
    (hwho : who[callCount (runVis r₀ ms₁)]? = some p) :
    RecvWireRawWitness interpretation r₀ S who g ms₁ acc [] p body r.message := by
  have hmp_nil : MatchedPrefix interpretation r₀ S who g ms₁ (acc ++ []) := by simpa only [List.append_nil] using hmp
  have hPkD_nil : NoRatchetPkDispatchAtSt interpretation r₀ S g ms₁ (acc ++ []) := by simpa only [List.append_nil] using hPkD
  have hsent_nil : sent = sentBodies (acc ++ []) := by simpa only [List.append_nil] using hsent
  have hfit_nil : SrHonestVer.SendsFit (acc ++ []) := by simpa only [List.append_nil] using hfit
  obtain ⟨_hp_mem, rec₀, st₀, stateIdx₀, hrecBytes₀, hst₀, hcur₀, hrel₀, _hsk_pre₀, _hcanon₀, hks₀, hnd₀⟩ :=
    hrsi p recBytes hrec
  have hnorm_eq : normPending rec₀ = normPending (RecvDecStep.sessionToRecordRecPending g_rw.sess) :=
    TR.PureRecvEval.rec_eq_sessionToRecordRec_of_pureCanonical_Q hrecBytes₀ hcanon_q
  have hrc_rec₀ : rec₀.current.receiverChains = (sessionToRecordRec g_rw.sess).current.receiverChains :=
    congrArg (fun r => r.current.receiverChains) hnorm_eq
  have hrel₀_sess : StateRel interpretation S g st₀ (sessionToRecordRec g_rw.sess) := by
    rw [← stateRel_sessionToRecordRecPending_iff, ← stateRel_normPending_iff, ← hnorm_eq, stateRel_normPending_iff]
    exact hrel₀
  have hnd₀_sess : RecordChainsWF3 (sessionToRecordRec g_rw.sess) :=
    ⟨hrc_rec₀ ▸ hnd₀.1, hrc_rec₀ ▸ hnd₀.2.1, hrc_rec₀ ▸ hnd₀.2.2⟩
  have hnodup_rc : (g_rw.sess.state.receiverChains.map ReceiverChain.senderRatchetKey).Nodup := by
    have hmap : (sessionToRecordRec g_rw.sess).current.receiverChains.map ChainRec.senderRatchetKey =
        (g_rw.sess.state.receiverChains.map ReceiverChain.senderRatchetKey).map PublicKey.serialize := by
      dsimp only [sessionToRecordRec, sessionToSessionRec]; rw [List.map_map, List.map_map]; rfl
    exact List.Nodup.of_map PublicKey.serialize (hmap ▸ hnd₀_sess.1)
  obtain ⟨_role, remIk, ck_adv, ck_next, r_adv, r2, mkGen, _st',
      _hrole, hVer, hRem, hFind, hNotLt, hJump, hAdv, hNext, hSet, hMkGen, hMac, hDec, _hSt', _hr_enc⟩ :=
    evalRecvWireWithCoinsW_noRatchet_inv interpretation body r g_rw m ci rc ck newPqrState pqrKey
      hwire htry hrc hrc_key hck hstep_idx hnodup_rc hrecv_spqr heval
  obtain ⟨msg₀, hparse₀⟩ := Option.isSome_iff_exists.mp ht.2.2.1
  have hRkLensAll₀ : RecvRkLensAll interpretation S g r₀ ms₁ := hat.lens
  have hst₀_avail : st₀ ∈ availableStates r₀ (runTraceMoves r₀ ms₁) :=
    Symbolic.Swarm.CREF.TR.RecvHistStep2.mem_availableStates_of_at? r₀ ms₁
      (Symbolic.Swarm.CREF.TR.FreshSigma.at?_eq_some_of_getLocalState_some hst₀)
  have hRkLens₀ : ∀ c ∈ st₀.recv, (gamma interpretation S g c.ratchetKey).length = 32 :=
    hRkLensAll₀ st₀ hst₀_avail
  obtain ⟨_hrk_sess, _hcks_sess, _hdhs_sess, hloc_ser, ⟨rem0, hrem0, hrem_ser⟩, _hrc_sess⟩ :=
    stateRel_sessionToRecordRec_extract_TR interpretation S g st₀ g_rw.sess hrel₀_sess
  have hst₀_rci : TrStateRkCkIk r₀ st₀ := trStateRkCkIk_of_getLocalState hmp.2.1 hst₀
  have hCkLens : ∀ c ∈ st₀.recv, (gamma interpretation S g c.chainKey).length = 32 :=
    hst₀_rci.recv_ck_len interpretation S g hwf hmp.1
  have hNodupSym : (st₀.recv.map RecvChain.ratchetKey).Nodup :=
    nodup_ratchetKey_of_stateRel_tr hrel₀_sess hnd₀_sess.1
  have hctr₀ : msg₀.counter = UInt32.ofBitVec m.counter :=
    UInt32.ext (((ht.2.2.2 msg₀ hparse₀).2.2.2 m htry).2.2.2.1)
  obtain ⟨_ci₀, _ch, c, _mks', seed, c', _hch0, hc0, hfind₀, _hsrk0, _htheir, _hck, _hch_ck,
      hcons₀_bv, hSeedEq, hCntEq, _hc'_rk, _hc'_rIdx, _hR2Eq, _hRel_lit, _hMks'⟩ :=
    stateRel_and_consumeMessageKey_of_existing_tr interpretation S g hrel₀_sess hNodupSym hCkLens
      (gamma_litOf interpretation S g newPqrState) hFind hNotLt hJump hAdv hNext hSet
  have hc_mem : c ∈ st₀.recv := List.mem_of_getElem? hc0
  have hcons₀ : consumeMessageKey c msg₀.counter = some (seed, c') := hctr₀ ▸ hcons₀_bv
  have hγ_c_rk : gamma interpretation S g c.ratchetKey = m.senderRatchetKey.bytes.toList := by
    rw [_htheir]; simp [vec32, hRkLens₀ c hc_mem]
  have hrk_oi : RkKnownOrInit (runTraceMoves r₀ ms₁) c.ratchetKey :=
    (storedRkKnown_of_modelRun hmp.2.1 st₀ hst₀_avail).ratchetKey hc_mem
  have hrel₀'_rec₀ : StateRel interpretation S g st₀ rec₀ := by
    rw [← stateRel_normPending_iff, hnorm_eq, stateRel_normPending_iff, stateRel_sessionToRecordRecPending_iff]
    exact hrel₀_sess
  obtain ⟨_, _, hpq_sess, _, _, hver_sess, _⟩ :=
    TR.PureRecvEval.pqRatchetState_eq_gamma_pending_pure interpretation S g recBytes rec₀ st₀ st₀ g_rw hrecBytes₀ hrel₀'_rec₀ hcanon_q rfl
  have hver₀_nat : msg₀.version.toNat = m.messageVersion.toNat := ((ht.2.2.2 msg₀ hparse₀).2.2.2 m htry).2.2.2.2
  have hver_g : g_rw.sess.state.version.toNat = 4 := by unfold SessionState.version; rw [hver_sess]; rfl
  have hver₀ : msg₀.version = messageVersion := UInt8.ext (hver₀_nat.trans (hVer.symm.trans hver_g))
  have hseed_c : msg₀.ratchetKey = c.ratchetKey → recvSeed st₀ msg₀ = some seed := by
    intro hrk₀; unfold recvSeed; simp only [hver₀, ↓reduceIte, recvChainFor, hrk₀, hfind₀]
    change Option.map Prod.fst (consumeMessageKey c msg₀.counter) = some seed; rw [hcons₀]; rfl
  let k_own : DY.Bytes := ({ st := st₀.spqr, msg := msg₀.pqRatchet } : DY.Spqr.RecvKey.SubF DY.Bytes).pack
  have hk_own : k_own ∈ ownKeys r₀ (runTraceMoves r₀ ms₁) st₀ msg₀ := by
    unfold ownKeys; exact List.mem_map_of_mem (List.mem_filter.mpr ⟨hst₀_avail, beq_self_eq_true _⟩)
  have hk_own_gam : gamma interpretation S g k_own = spqrKeyBytes (saltToBytes pqrKey) :=
    (spqrRecv_step_gamma_state_and_key interpretation hExt.1
      r₀ S hS g ms₁ body st₀ g_rw t msg₀ m newPqrState pqrKey hpq_sess ht hparse₀ htry hrecv_spqr).2
  have hmkGen_eq : mkGen = ⟨gamma interpretation S g seed, m.counter⟩ := by
    rw [hMkGen]; change ck_adv.messageKeys (sha256CompressFunction interpretation) = _
    rcases h : ck_adv.messageKeys (sha256CompressFunction interpretation) with ⟨sd, ct⟩
    rw [h] at hSeedEq hCntEq; dsimp only at hSeedEq hCntEq; subst hSeedEq hCntEq; rfl
  obtain ⟨hck_mk, hmk_mk, hiv_mk, _⟩ := gamma_trMsgKeys_eq_generateKeys interpretation S g k_own seed m.counter pqrKey hk_own_gam
  have hDecOk : interpretation aesCbcDecryptSymbol
      [m.ciphertext, gamma interpretation S g (trMsgKeys k_own seed).cipherKey,
       (gamma interpretation S g (trMsgKeys k_own seed).iv).take 16] = some r.message := by
    rw [← hck_mk, ← hiv_mk]
    change (Proofs.libsignal.SR.interpW interpretation).dec
      (MessageKeyGenerator.generateKeys (cryptoOf' interpretation).F ⟨gamma interpretation S g seed, m.counter⟩ pqrKey).cipherKey
      (MessageKeyGenerator.generateKeys (cryptoOf' interpretation).F ⟨gamma interpretation S g seed, m.counter⟩ pqrKey).iv
      m.ciphertext = some r.message
    rw [← hmkGen_eq]; exact hDec
  rw [hRem] at hrem0; injection hrem0 with hrem_eq; subst hrem_eq
  have hpeer_ser : remIk.serialize = gamma interpretation S g st₀.peerIk := hrem_ser.trans hks₀.peerIk_ser
  have hmy_ser : g_rw.sess.state.localIdentity.serialize = gamma interpretation S g st₀.myIk := hloc_ser.trans hks₀.myIk_ser
  have hwire₀_take : gamma interpretation S g msg₀.wire = body.take (body.length - 8) := (ht.2.2.2 msg₀ hparse₀).1
  have hm_ser : m.serialized = body :=
    tryFrom_serialized_eq_slotG2 htry
  have hMacBytes : body.drop (body.length - 8) =
      gamma interpretation S g (computeMac (trMsgKeys k_own seed).macKey st₀.peerIk st₀.myIk msg₀.wire) := by
    have hmac_ver : m.verifyMac (cryptoOf' interpretation).F remIk g_rw.sess.state.localIdentity
        (mkGen.generateKeys (cryptoOf' interpretation).F pqrKey).macKey = true :=
      ((Proofs.libsignal.RngG.CliPure.DecCrypto.verifyMacWithAddresses_eq_true_iff _ _ _ _ _ _).mp hMac).1
    unfold SignalMessage.verifyMac macLength at hmac_ver; dsimp only at hmac_ver
    have hmac_eq := (beq_iff_eq.mp hmac_ver).symm; rw [hm_ser] at hmac_eq; rw [hmac_eq]
    have hkey_mk : keyToBytes32 ((mkGen.generateKeys (cryptoOf' interpretation).F pqrKey).macKey) =
        gamma interpretation S g (trMsgKeys k_own seed).macKey := by rw [hmkGen_eq]; exact hmk_mk
    exact gamma_computeMac_tr interpretation S g (trMsgKeys k_own seed).macKey st₀.peerIk st₀.myIk msg₀.wire
      remIk g_rw.sess.state.localIdentity ((mkGen.generateKeys (cryptoOf' interpretation).F pqrKey).macKey)
      hkey_mk hpeer_ser hmy_ser (body.take (body.length - 8)) hwire₀_take.symm
  have hik0_kn : (DY.Libsignal.PQXDH.serializedIk (setupPublic r₀ 0)).AttackerKnows (runTraceMoves r₀ ms₁) :=
    Concat.attacker_knows_concat _ _ _ (Literal.attacker_knows_literalToBytes _ _)
      (Symbolic.Swarm.CREF.CliPureRcv.TRPure.knows_setupPublic r₀ hwf.1 ms₁ 0 (Or.inl rfl))
  have hik2_kn : (DY.Libsignal.PQXDH.serializedIk (setupPublic r₀ 2)).AttackerKnows (runTraceMoves r₀ ms₁) :=
    Concat.attacker_knows_concat _ _ _ (Literal.attacker_knows_literalToBytes _ _)
      (Symbolic.Swarm.CREF.CliPureRcv.TRPure.knows_setupPublic r₀ hwf.1 ms₁ 2 (Or.inr rfl))
  have hPeerK : st₀.peerIk.AttackerKnows (runTraceMoves r₀ ms₁) := hst₀_rci.peerIk.elim (· ▸ hik0_kn) (· ▸ hik2_kn)
  have hMyK : st₀.myIk.AttackerKnows (runTraceMoves r₀ ms₁) := hst₀_rci.myIk.elim (· ▸ hik0_kn) (· ▸ hik2_kn)
  have hHist : RecvHistInvTR interpretation S g r₀ ms₁ := hat.hist
  obtain ⟨t₁, msg₁, ht₁_rep, hparse₁, hver₁, hrk₁, hctr₁, hMacBytes₁, hDisj⟩ :=
    hPkD_nil p stateIdx₀ body r.message m st₀ c c' t seed k_own msg₀ hmp.2.1 hmp.2.1.2.2.1.1
      htry ht hparse₀ hver₀ hctr₀ hnocol hnors hst₀ hc_mem hcons₀ hseed_c hk_own
      hHist hIW hrk_oi hγ_c_rk hMacBytes hPeerK hMyK hDecOk
  obtain ⟨t_m, msg', pqSalt, ptTerm, spqr', key, spqrMsgIdx,
      ht_m_rep, hpqSalt_kn, ht_m_kn, hparse', hver', hrk', hctr',
      hspqr_step, _hspqr'_gam, hmac', hdec', ht_m_gam, hpt_gam⟩ :=
    noRatchet_decryptWitness_of_g1_disj_at interpretation hExt.1
      r₀ S hS g p stateIdx₀ ms₁ (acc ++ []) sent
      recBytes body r.message rec₀ st₀ g_rw t₁ msg₁ m c.ratchetKey seed k_own newPqrState pqrKey
      hmp_nil hfit_nil hsent_nil hrecBytes₀ hrel₀'_rec₀ hst₀ hcanon_q hpq htry ht₁_rep hparse₁ hver₁ hrk₁
      hMacBytes₁ hPeerK hMyK hDecOk hrecv_spqr hDisj
  have hctr_eq : msg'.counter = msg₀.counter := hctr'.trans hctr₁
  have hfind' : findRecvChain st₀.recv msg'.ratchetKey = some c := hrk' ▸ hfind₀
  have hcons' : consumeMessageKey c msg'.counter = some (seed, c') := hctr_eq ▸ hcons₀
  have hmp₁ := matchedPrefix_decrypt_noRatchet_two_attackerSend
    hmp_nil hpqSalt_kn ht_m_kn hcur₀ hst₀ hparse' hver' hfind' hcons'
    hspqr_step hmac' hdec' ht_m_gam hpt_gam hwho ht_m_rep
  exact ⟨g, stateIdx₀, spqrMsgIdx, pqSalt, t_m,
    Move.decrypt p stateIdx₀ ((runTraceMoves r₀ ms₁).length + 1)
      (runTraceMoves r₀ ms₁).length spqrMsgIdx false,
    cbadSigmaFrame_refl g (runTraceMoves r₀ ms₁).length, ht_m_rep, hpqSalt_kn, hcur₀,
    Or.inl rfl, by simpa using hmp₁⟩

set_option maxHeartbeats 400000 in
theorem recvWireStepWitness_of_ratchetDH_branch
    (interpretation : ExternInterpretation) (hExt : ExternContractsHoldCli interpretation)
    (r₀ : ProtocolSetup) (hwf : ProtocolSetupWF r₀) (_hik : IkShape interpretation r₀) (S : OpaqueSymbolSemantics) (hS : S = compSemOf interpretation r₀)
    {who : List Participant} {ok : Nat → Bool} {slots : PureTRSlots} (records : Participant → Option HwBytes) (sent : List HwBytes)
    (p : Participant) (recBytes body rngBytes : HwBytes)
    (acc : List MachineEvent) (g : Ghost) (ms₁ : List Move) (r : StateAndMessage) (g_rw : RecvWireGhost) (m : SignalMessage)
    (newPqrState : HwBytes) (pqrKey : HKDF.Salt) (hmp : MatchedPrefix interpretation r₀ S who g ms₁ acc)
    (hEx : ExplainsMoves interpretation r₀ S who ok g ms₁ acc)
    (hrsi : PureTRRecordStateInv interpretation r₀ S slots g ms₁ records) (_hat : RecvAtFacts interpretation r₀ S g ms₁)
    (hsent : sent = sentBodies acc) (hfit : SrHonestVer.SendsFit acc) (hrec : records p = some recBytes)
    (hpq : PqFromHonest sent body) (_hstate_lt : r.state.length < 2 ^ 64)
    (t : DY.Bytes) (ht : t ∈ recvRepresentations interpretation r₀ S g ms₁ body)
    (hnocol : ¬ RecvCollision interpretation r₀ S g ms₁ t) (hwire : g_rw.wireBytes = wireWhisperTag :: body)
    (hcanon_q : TR.Pure.slots_RecordCanonical_Q TR.Pure.slots_NonEmptyV1Q recBytes g_rw.sess)
    (hrng_len : rngBytes.length = 32)
    (htry : SignalMessage.tryFrom protoSignalCodec body = .ok m)
    (hrc_none : ∀ rc ∈ g_rw.sess.state.receiverChains, rc.senderRatchetKey ≠ m.senderRatchetKey)
    (hrecv_spqr : (spqrModelOf interpretation).recv
        g_rw.sess.state.pqRatchetState m.pqRatchet = .ok (newPqrState, pqrKey))
    (heval : TR.PureRecvEval.pureEvalRecvWireWithCoinsW (cryptoOf' interpretation)
        (Proofs.libsignal.SR.interpW interpretation) (spqrModelOf interpretation) g_rw
        (Symbolic.Swarm.CREF.CliPureRcv.TR.RecvDecStepPure.purePinCoins (some rngBytes)) = some (r.state, r.message))
    (hABS' : G1cAttackerBuiltSeedExcl' interpretation r₀ S g ms₁)
    (hwho : who[callCount (runVis r₀ ms₁)]? = some p) :
    RecvWireRawWitness interpretation r₀ S who g ms₁ acc [.rng rngBytes] p body r.message := by
  have hmp_nil : MatchedPrefix interpretation r₀ S who g ms₁ (acc ++ []) := by simpa only [List.append_nil] using hmp
  have hsent_nil : sent = sentBodies (acc ++ []) := by simpa only [List.append_nil] using hsent
  have hfit_nil : SrHonestVer.SendsFit (acc ++ []) := by simpa only [List.append_nil] using hfit
  have hceh := hExt.1
  obtain ⟨_hp_mem, rec₀, st₀, stateIdx₀, hrecBytes₀, hst₀, hcur₀, hrel₀, _hsk_pre₀, _hcanon₀, hks₀, _hnd₀⟩ :=
    hrsi p recBytes hrec
  obtain ⟨_hnp_eq, hrel₀_sess, _, _, _, _, _⟩ :=
    TR.PureRecvEval.pqRatchetState_eq_gamma_pending_pure interpretation S g recBytes rec₀ st₀ st₀ g_rw hrecBytes₀ hrel₀ hcanon_q rfl
  obtain ⟨_role, remIk, ck, ck_adv, ck_next, r1, r_adv, r2, mkGen, _st',
      _hrole, hVer, hRem, hFind, hDh, hNotLt, hJump, hAdv, hNext, hSet, hMkGen, hMac, hDec, _hSt', _hr_enc⟩ :=
    Symbolic.Swarm.CREF.CliPureRcv.TR.RecvDecStepAtPure.evalRecvWireWithCoinsW_ratchetDH_inv_at
      interpretation body rngBytes r g_rw m newPqrState pqrKey
      hwire htry hrc_none hrecv_spqr heval
  obtain ⟨msg₀, hparse₀⟩ := Option.isSome_iff_exists.mp ht.2.2.1
  have hctr₀ : msg₀.counter = UInt32.ofBitVec m.counter :=
    UInt32.ext (((ht.2.2.2 msg₀ hparse₀).2.2.2 m htry).2.2.2.1)
  let g' : Ghost := { g with σ := updateFreshAt g.σ ((runTraceMoves r₀ ms₁).length + 2) 32 rngBytes }
  have hRun : ModelRun r₀ ms₁ := hmp.2.1
  have hreach : (runTraceMoves r₀ ms₁).Reachable reachability := hRun.2.2.1.1
  have hst_avail : st₀ ∈ availableStates r₀ (runTraceMoves r₀ ms₁) :=
    Symbolic.Swarm.CREF.TR.RecvHistStep2.mem_availableStates_of_at? r₀ ms₁ (at?_eq_some_of_getLocalState_some hst₀)
  obtain ⟨hRng, hmp', _hrsi', hrel₀', hks₀', _hst_lt, _hmsg_lt, _ht_gam, _hwire_gam, _hmac_gam,
      _hrk_gam, _hct_gam, _hpq_gam, _hspqr_gam, _hrecv_gam⟩ :=
    TR.PureRecvEval.pureRatchetDH_sigma_bridge interpretation r₀ hwf S slots g ms₁ (acc ++ [])
      records p stateIdx₀ st₀ (sessionToRecordRec g_rw.sess) t msg₀
      ((runTraceMoves r₀ ms₁).length + 2) rngBytes (by omega)
      hmp_nil hrsi hst₀ hrel₀_sess hks₀ ht.1 hparse₀
  have htr_lt : TraceEntriesLt interpretation S g ((runTraceMoves r₀ ms₁).length + 2) (runTraceMoves r₀ ms₁) :=
    traceEntriesLt_of_reachable interpretation S g ((runTraceMoves r₀ ms₁).length + 2) hreach (by omega)
  obtain ⟨_hrk_sess, _hcks_sess, _hdhs_sess, hloc_ser, ⟨rem0, hrem0, hrem_ser⟩, _hrc_sess⟩ :=
    stateRel_sessionToRecordRec_extract_TR interpretation S g' st₀ g_rw.sess hrel₀'
  have hst₀_rci : TrStateRkCkIk r₀ st₀ := trStateRkCkIk_of_getLocalState hmp'.2.1 hst₀
  have hRkLen : (gamma interpretation S g' st₀.rk).length = 32 :=
    hst₀_rci.rk_len interpretation S g' hwf hmp'.1
  have hCkLens : ∀ c ∈ st₀.recv, (gamma interpretation S g' c.chainKey).length = 32 :=
    hst₀_rci.recv_ck_len interpretation S g' hwf hmp'.1
  have hTheir' : m.senderRatchetKey.bytes.toList = gamma interpretation S g' msg₀.ratchetKey :=
    ((ht.2.2.2 msg₀ hparse₀).2.2.2 m htry).2.1.symm.trans _hrk_gam.symm
  have hPkLen : (gamma interpretation S g' msg₀.ratchetKey).length = 32 :=
    hTheir' ▸ m.senderRatchetKey.bytes.2
  have hTheir : m.senderRatchetKey = ⟨vec32 (gamma interpretation S g' msg₀.ratchetKey)⟩ := by
    cases hmk : m.senderRatchetKey with | mk b =>
    have hb : b.toList = (vec32 (gamma interpretation S g' msg₀.ratchetKey)).toList := by
      rw [hmk] at hTheir'; exact hTheir'.trans (vec32_toList_of_length_eq_tr hPkLen).symm
    exact congrArg PublicKey.mk (Subtype.ext hb)
  have ht₀' : t ∈ recvRepresentations interpretation r₀ S g' ms₁ body := by
    refine ⟨ht.1, _ht_gam.trans ht.2.1, ht.2.2.1, fun msg hmsg => ?_⟩
    rcases Option.some.inj (hparse₀.symm.trans hmsg) with rfl
    have h₀ := ht.2.2.2 msg₀ hparse₀
    refine ⟨_hwire_gam.trans h₀.1, _hmac_gam.trans h₀.2.1, h₀.2.2.1, fun parsed hparsed => ?_⟩
    have hp := h₀.2.2.2 parsed hparsed
    exact ⟨_hct_gam.trans hp.1, _hrk_gam.trans hp.2.1, _hpq_gam.trans hp.2.2.1, hp.2.2.2⟩
  have hJump' : (m.counter - ck.index).toNat ≤ CryptoGames.LibsignalSession.maxForwardJumps := by
    obtain ⟨_, _, _, _, _, _, _, hr1⟩ := dhRatchetStep_ok_inv hDh
    rw [hr1] at hJump; exact hJump
  obtain ⟨hfind₀, _mks', seed, c', hcons₀_bv, hSeedEq, hCntEq,
      _hc'_rk, _hc'_rIdx, _hc_idx0, _hc_rIdx, _hR2Eq', _hRel_lit, _hRcMem, _hMks'⟩ :=
    stateRel_and_consumeMessageKey_of_dhRatchetStep_tr interpretation S g' hceh (hrel := hrel₀')
      (hRkLen := hRkLen) (hDhsLen := hks₀'.dhs_len) (hCkLens := hCkLens) (hTheir := hTheir) (hPkLen := hPkLen)
      (hRng := hRng) (hRngLen := hrng_len)
      (hspqr' := gamma_litOf interpretation S g' newPqrState)
      (hFindNone := hFind) (hStep := hDh)
      (hNotLt := hNotLt) (hJump := hJump') (hAdv := hAdv) (hNext := hNext) (hSet := hSet)
  have hcons₀ :
      consumeMessageKey (trDhRatchetState st₀ msg₀.ratchetKey ((runTraceMoves r₀ ms₁).length + 2)).2 msg₀.counter =
        some (seed, c') := by
    rw [hctr₀]; exact hcons₀_bv
  have hlow₀ : DY.Libsignal.TripleRatchet.x25519LowOrder msg₀.ratchetKey = false :=
    x25519LowOrder_false_of_dhRatchetStep_ok_tr interpretation S g' hceh (hTheir := hTheir') (hDh := hDh)
  let k_own : DY.Bytes := ({ st := st₀.spqr, msg := msg₀.pqRatchet } : DY.Spqr.RecvKey.SubF DY.Bytes).pack
  have hk_own : k_own ∈ ownKeys r₀ (runTraceMoves r₀ ms₁) st₀ msg₀ := by
    unfold ownKeys
    exact List.mem_map_of_mem (List.mem_filter.mpr ⟨hst_avail, beq_self_eq_true _⟩)
  have hpq_sess : g_rw.sess.state.pqRatchetState = gamma interpretation S g' st₀.spqr :=
    congrArg SessionRec.pqRatchetState hrel₀'.2
  have hver_sess : g_rw.sess.state.sessionVersion = 4#32 :=
    congrArg SessionRec.sessionVersion hrel₀'.2
  have hk_own_gam : gamma interpretation S g' k_own = spqrKeyBytes (saltToBytes pqrKey) :=
    (spqrRecv_step_gamma_state_and_key interpretation hceh r₀ S hS g' ms₁ body st₀ g_rw t msg₀ m
      newPqrState pqrKey hpq_sess ht₀' hparse₀ htry hrecv_spqr).2
  have hver₀_nat : msg₀.version.toNat = m.messageVersion.toNat :=
    ((ht₀'.2.2.2 msg₀ hparse₀).2.2.2 m htry).2.2.2.2
  have hver_g : g_rw.sess.state.version.toNat = 4 := by
    unfold SessionState.version; rw [hver_sess]; rfl
  have hver₀ : msg₀.version = messageVersion :=
    UInt8.ext (hver₀_nat.trans (hVer.symm.trans hver_g))
  have hseed : recvSeed st₀ msg₀ = some seed := by
    unfold recvSeed
    simp only [hver₀, ↓reduceIte, recvChainFor, hfind₀, hlow₀, Bool.false_eq_true]
    change Option.map Prod.fst
      (consumeMessageKey (trDhRatchetState st₀ msg₀.ratchetKey ((runTraceMoves r₀ ms₁).length + 2)).2 msg₀.counter) =
      some seed
    rw [hcons₀]; rfl
  have hmkGen_eq : mkGen = ⟨gamma interpretation S g' seed, m.counter⟩ := by
    rw [hMkGen]
    change ck_adv.messageKeys (sha256CompressFunction interpretation) = _
    rcases h : ck_adv.messageKeys (sha256CompressFunction interpretation) with ⟨sd, ct⟩
    rw [h] at hSeedEq hCntEq; dsimp only at hSeedEq hCntEq; subst hSeedEq hCntEq; rfl
  obtain ⟨hck_mk, hmk_mk, hiv_mk, _⟩ :=
    gamma_trMsgKeys_eq_generateKeys interpretation S g' k_own seed m.counter pqrKey hk_own_gam
  have hDecOk :
      interpretation aesCbcDecryptSymbol
        [m.ciphertext, gamma interpretation S g' (trMsgKeys k_own seed).cipherKey,
         (gamma interpretation S g' (trMsgKeys k_own seed).iv).take 16] = some r.message := by
    rw [← hck_mk, ← hiv_mk]
    change (Proofs.libsignal.SR.interpW interpretation).dec
      (MessageKeyGenerator.generateKeys (cryptoOf' interpretation).F
        ⟨gamma interpretation S g' seed, m.counter⟩ pqrKey).cipherKey
      (MessageKeyGenerator.generateKeys (cryptoOf' interpretation).F
        ⟨gamma interpretation S g' seed, m.counter⟩ pqrKey).iv m.ciphertext = some r.message
    rw [← hmkGen_eq]; exact hDec
  rw [hRem] at hrem0; injection hrem0 with hrem_eq; subst hrem_eq
  have hpeer_ser : remIk.serialize = gamma interpretation S g' st₀.peerIk :=
    hrem_ser.trans hks₀'.peerIk_ser
  have hmy_ser : g_rw.sess.state.localIdentity.serialize = gamma interpretation S g' st₀.myIk :=
    hloc_ser.trans hks₀'.myIk_ser
  have hwire₀_take : gamma interpretation S g' msg₀.wire = body.take (body.length - 8) :=
    (ht₀'.2.2.2 msg₀ hparse₀).1
  have hm_ser : m.serialized = body :=
    tryFrom_serialized_eq_slotG2 htry
  have hMacBytes :
      body.drop (body.length - 8) =
        gamma interpretation S g' (computeMac (trMsgKeys k_own seed).macKey st₀.peerIk st₀.myIk msg₀.wire) := by
    have hmac_ver : m.verifyMac (cryptoOf' interpretation).F remIk g_rw.sess.state.localIdentity
        (mkGen.generateKeys (cryptoOf' interpretation).F pqrKey).macKey = true :=
      ((Proofs.libsignal.RngG.CliPure.DecCrypto.verifyMacWithAddresses_eq_true_iff _ _ _ _ _ _).mp hMac).1
    unfold SignalMessage.verifyMac macLength at hmac_ver
    dsimp only at hmac_ver
    have hmac_eq := (beq_iff_eq.mp hmac_ver).symm
    rw [hm_ser] at hmac_eq; rw [hmac_eq]
    have hkey_mk : keyToBytes32 ((mkGen.generateKeys (cryptoOf' interpretation).F pqrKey).macKey) =
        gamma interpretation S g' (trMsgKeys k_own seed).macKey := by
      rw [hmkGen_eq]; exact hmk_mk
    exact gamma_computeMac_tr interpretation S g' (trMsgKeys k_own seed).macKey
      st₀.peerIk st₀.myIk msg₀.wire remIk g_rw.sess.state.localIdentity
      ((mkGen.generateKeys (cryptoOf' interpretation).F pqrKey).macKey)
      hkey_mk hpeer_ser hmy_ser (body.take (body.length - 8)) hwire₀_take.symm
  have hc_lt : ChainStampsLt interpretation S g ((runTraceMoves r₀ ms₁).length + 2)
      (trDhRatchetState st₀ msg₀.ratchetKey ((runTraceMoves r₀ ms₁).length + 2)).2 :=
    ⟨_hmsg_lt.2.2.1, (stampsLt_createChain _hst_lt.2.2.1 _hmsg_lt.2.2.1 _hst_lt.2.2.2.1).2⟩
  have hseed_lt : StampsLt interpretation S g ((runTraceMoves r₀ ms₁).length + 2) seed :=
    (stampsLt_consumeMessageKey hc_lt hcons₀).1
  have hk_own_lt : StampsLt interpretation S g ((runTraceMoves r₀ ms₁).length + 2) k_own :=
    (stampsLt_spqrRecvKey_pack interpretation S g ((runTraceMoves r₀ ms₁).length + 2) ⟨st₀.spqr, msg₀.pqRatchet⟩).mpr
      ⟨_hst_lt.2.2.2.2.2.1, _hmsg_lt.2.2.2.2⟩
  have hkeys_lt := stampsLt_trMsgKeys hk_own_lt hseed_lt
  have hmac_term_lt := stampsLt_computeMac hkeys_lt.2.1 _hst_lt.2.1 _hst_lt.1 _hmsg_lt.1
  have hMacBytes₁ :
      body.drop (body.length - 8) =
        gamma interpretation S g (computeMac (trMsgKeys k_own seed).macKey st₀.peerIk st₀.myIk msg₀.wire) := by
    rw [← gamma_updateFreshAt_of_stampsLt interpretation S g ((runTraceMoves r₀ ms₁).length + 2) 32 rngBytes _ hmac_term_lt]
    exact hMacBytes
  have hDecOk₁ :
      interpretation aesCbcDecryptSymbol
        [m.ciphertext, gamma interpretation S g (trMsgKeys k_own seed).cipherKey,
         (gamma interpretation S g (trMsgKeys k_own seed).iv).take 16] = some r.message := by
    rw [← gamma_updateFreshAt_of_stampsLt interpretation S g ((runTraceMoves r₀ ms₁).length + 2) 32 rngBytes _ hkeys_lt.1,
        ← gamma_updateFreshAt_of_stampsLt interpretation S g ((runTraceMoves r₀ ms₁).length + 2) 32 rngBytes _ hkeys_lt.2.2]
    exact hDecOk
  have hik0_kn : (DY.Libsignal.PQXDH.serializedIk (setupPublic r₀ 0)).AttackerKnows (runTraceMoves r₀ ms₁) :=
    Concat.attacker_knows_concat _ _ _ (Literal.attacker_knows_literalToBytes _ _)
      (Symbolic.Swarm.CREF.CliPureRcv.TRPure.knows_setupPublic r₀ hwf.1 ms₁ 0 (Or.inl rfl))
  have hik2_kn : (DY.Libsignal.PQXDH.serializedIk (setupPublic r₀ 2)).AttackerKnows (runTraceMoves r₀ ms₁) :=
    Concat.attacker_knows_concat _ _ _ (Literal.attacker_knows_literalToBytes _ _)
      (Symbolic.Swarm.CREF.CliPureRcv.TRPure.knows_setupPublic r₀ hwf.1 ms₁ 2 (Or.inr rfl))
  have hPeerK : st₀.peerIk.AttackerKnows (runTraceMoves r₀ ms₁) := hst₀_rci.peerIk.elim (· ▸ hik0_kn) (· ▸ hik2_kn)
  have hMyK : st₀.myIk.AttackerKnows (runTraceMoves r₀ ms₁) := hst₀_rci.myIk.elim (· ▸ hik0_kn) (· ▸ hik2_kn)
  have hDisjRks := recv_mac_authentic_or_rkSwap_seed_known_of_not_collision_explains'
    interpretation hceh r₀ S g ms₁ body r.message m hEx hABS' hreach
    htry t msg₀ ht hparse₀ hnocol st₀ hst_avail hfind₀ seed hseed k_own hk_own hMacBytes₁ hDecOk₁
  have hHon : PqFromHonest (sentBodies (acc ++ [])) body := hsent_nil ▸ hpq
  have hBridge₁ := hDisjRks.elim
    (fun hRkSwap => TR.PureRecvEval.spqrRecv_step_bridge_ratchetDH_rkSwap_nw_pure
      interpretation hceh r₀ S hS g p stateIdx₀ ms₁ (acc ++ []) recBytes body r.message
      rec₀ st₀ g_rw t msg₀ m seed k_own c' newPqrState pqrKey
      hmp_nil hfit_nil hrecBytes₀ hrel₀ hst₀ hcanon_q hHon htry ht hparse₀ hver₀ hctr₀ hcons₀
      hMacBytes₁ hPeerK hMyK hDecOk₁ hrecv_spqr (Or.inl hRkSwap))
    (fun ⟨salt₁, _hsalt₁, hrk_sid, hAuth, hMacBytes_salt₁, hDecOk_salt₁⟩ =>
      TR.PureRecvEval.spqrRecv_step_bridge_ratchetDH_rkSwap_nw_pure
        interpretation hceh r₀ S hS g p stateIdx₀ ms₁ (acc ++ []) recBytes body r.message
        rec₀ st₀ g_rw t msg₀ m seed salt₁ c' newPqrState pqrKey
        hmp_nil hfit_nil hrecBytes₀ hrel₀ hst₀ hcanon_q hHon htry ht hparse₀ hver₀ hctr₀ hcons₀
        hMacBytes_salt₁.symm hPeerK hMyK hDecOk_salt₁ hrecv_spqr (Or.inr ⟨hrk_sid, hAuth⟩))
  obtain ⟨rk_c, seed_c, c'_c, t_m, msg', pqSalt, ptTerm, spqr', key, spqrMsgIdx,
      _hrk_c_sid, hγ_rk_c₁, _hγ_seed_c, hcons_c, ht_m_rep, hpqSalt_kn, ht_m_kn,
      hparse', hver', hrk', _hctr', hspqr_step, _hspqr'_gam₁, hmac', hdec', ht_m_gam₁, hpt_gam₁,
      _st_s, _t_c, _coinsLen, _hst_s, _hpq_eq⟩ := hBridge₁
  have ht_m_lt : StampsLt interpretation S g ((runTraceMoves r₀ ms₁).length + 2) t_m :=
    traceEntriesLt_knows htr_lt ht_m_kn
  have hmsg'_lt := stampsLt_parseTrSignalMsg ht_m_lt hparse'
  have hrk_c_lt : StampsLt interpretation S g ((runTraceMoves r₀ ms₁).length + 2) rk_c :=
    hrk' ▸ hmsg'_lt.2.2.1
  have hpt_lt := stampsLt_symDec hdec' hmsg'_lt.2.2.2.1
  have hγ_rk_c : gamma interpretation S g' rk_c = gamma interpretation S g' msg₀.ratchetKey := by
    rw [gamma_updateFreshAt_of_stampsLt interpretation S g ((runTraceMoves r₀ ms₁).length + 2) 32 rngBytes rk_c hrk_c_lt,
        gamma_updateFreshAt_of_stampsLt interpretation S g ((runTraceMoves r₀ ms₁).length + 2) 32 rngBytes msg₀.ratchetKey _hmsg_lt.2.2.1]
    exact hγ_rk_c₁
  have ht_m_gam : gamma interpretation S g' t_m = body := by
    rw [gamma_updateFreshAt_of_stampsLt interpretation S g ((runTraceMoves r₀ ms₁).length + 2) 32 rngBytes t_m ht_m_lt]
    exact ht_m_gam₁
  have hpt_gam : gamma interpretation S g' ptTerm = r.message := by
    rw [gamma_updateFreshAt_of_stampsLt interpretation S g ((runTraceMoves r₀ ms₁).length + 2) 32 rngBytes ptTerm hpt_lt]
    exact hpt_gam₁
  have ht_m_rep' : t_m ∈ recvRepresentations interpretation r₀ S g' ms₁ body := by
    refine ⟨ht_m_rep.1, ht_m_gam, ht_m_rep.2.2.1, fun msg hmsg => ?_⟩
    rcases Option.some.inj (hparse'.symm.trans hmsg) with rfl
    have h₀ := ht_m_rep.2.2.2 msg' hparse'
    refine ⟨(gamma_updateFreshAt_of_stampsLt interpretation S g ((runTraceMoves r₀ ms₁).length + 2) 32 rngBytes msg'.wire hmsg'_lt.1).trans h₀.1,
      (gamma_updateFreshAt_of_stampsLt interpretation S g ((runTraceMoves r₀ ms₁).length + 2) 32 rngBytes msg'.mac hmsg'_lt.2.1).trans h₀.2.1,
      h₀.2.2.1, fun parsed hparsed => ?_⟩
    have hp := h₀.2.2.2 parsed hparsed
    exact ⟨(gamma_updateFreshAt_of_stampsLt interpretation S g ((runTraceMoves r₀ ms₁).length + 2) 32 rngBytes msg'.ciphertext hmsg'_lt.2.2.2.1).trans hp.1,
      (gamma_updateFreshAt_of_stampsLt interpretation S g ((runTraceMoves r₀ ms₁).length + 2) 32 rngBytes msg'.ratchetKey hmsg'_lt.2.2.1).trans hp.2.1,
      (gamma_updateFreshAt_of_stampsLt interpretation S g ((runTraceMoves r₀ ms₁).length + 2) 32 rngBytes msg'.pqRatchet hmsg'_lt.2.2.2.2).trans hp.2.2.1,
      hp.2.2.2⟩
  have hfind' : findRecvChain st₀.recv msg'.ratchetKey = none := hrk' ▸
    (findRecvChain_eq_none_of_dhRatchetStep_rkSwap (msg₀ := msg₀) interpretation S g' hrel₀' hCkLens hFind hTheir hγ_rk_c).1
  have hlow' : DY.Libsignal.TripleRatchet.x25519LowOrder msg'.ratchetKey = false := hrk' ▸
    x25519LowOrder_false_of_dhRatchetStep_rkSwap (msg₀ := msg₀)
      interpretation S g' hceh (hTheir₀ := hTheir) (hPkLen₀ := hPkLen) (hγ_rk_c := hγ_rk_c) (hDh := hDh)
  have hcons' : consumeMessageKey (trDhRatchetState st₀ msg'.ratchetKey ((runTraceMoves r₀ ms₁).length + 2)).2 msg'.counter = some (seed_c, c'_c) :=
    hrk' ▸ hcons_c
  have hspqr_step' : Spqr.spqrRecv (trDhRatchetState st₀ msg'.ratchetKey ((runTraceMoves r₀ ms₁).length + 2)).1.spqr msg'.pqRatchet spqrMsgIdx = some (spqr', key) :=
    hrk' ▸ hspqr_step
  have hmac_eq' : msg'.mac = computeMac (trMsgKeys pqSalt seed_c).macKey
      (trDhRatchetState st₀ msg'.ratchetKey ((runTraceMoves r₀ ms₁).length + 2)).1.peerIk
      (trDhRatchetState st₀ msg'.ratchetKey ((runTraceMoves r₀ ms₁).length + 2)).1.myIk msg'.wire :=
    hrk' ▸ hmac'
  have hrng_gam : gamma interpretation S g' (randTerm ((runTraceMoves r₀ ms₁).length + 2) 32) = rngBytes := by
    rw [Symbolic.Swarm.TRREF.SpqrSemOf.gamma_randTerm32]; exact hRng
  have hmp₁ := Symbolic.Swarm.CREF.CliPureRcv.TR.RecvDecStepAtPure.matchedPrefix_decrypt_ratchet_two_attackerSend_at
    hmp' hpqSalt_kn ht_m_kn hcur₀ hst₀ hparse' hver' hfind' hlow' hcons'
    hspqr_step' hmac_eq' hdec' ht_m_gam hrng_gam hpt_gam hwho ht_m_rep'
  have hfr : CBadSigmaFrame g g' (runTraceMoves r₀ ms₁).length :=
    cBadSigmaFrame_updateFreshAt g (n := (runTraceMoves r₀ ms₁).length) (ts := (runTraceMoves r₀ ms₁).length + 2) (by omega) 32 rngBytes
  exact ⟨g', stateIdx₀, spqrMsgIdx, pqSalt, t_m,
    Move.decrypt p stateIdx₀ ((runTraceMoves r₀ ms₁).length + 1)
      (runTraceMoves r₀ ms₁).length spqrMsgIdx false,
    hfr, ht_m_rep, hpqSalt_kn, hcur₀, Or.inl rfl, by simpa using hmp₁⟩

end Symbolic.Swarm.CREF.CliPureRcv.RecvWirePure
