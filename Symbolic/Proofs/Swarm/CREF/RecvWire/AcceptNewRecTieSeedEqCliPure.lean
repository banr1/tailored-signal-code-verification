/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Symbolic.Proofs.Swarm.CREF.RecvWire.AcceptNewRecTieBExclPure
public import Symbolic.Proofs.Swarm.CREF.RecvWire.AcceptNewRecTieSeedShapePure
import Batteries.Data.UInt
public import Symbolic.Proofs.Swarm.CREF.Sem
import Symbolic.Proofs.Swarm.CREF.Cli.Rpk.RecvDecStepCommonPure
import Symbolic.Proofs.Swarm.CREF.Cli.Rpk.RecvDecStepNoRatchetPure
import Symbolic.Proofs.Swarm.CREF.Cli.Rpk.RecvDecStepSpqrPure
import Symbolic.Proofs.Swarm.CREF.Cli.Rpk.SendRetCoinsCliPure
import Symbolic.Proofs.Swarm.CREF.Cli.Rpk.SendRetCoinsCliPureB
import Symbolic.Proofs.Swarm.CREF.Initiate.InitRej
import Symbolic.Proofs.Swarm.CREF.Prelude
import Symbolic.Proofs.Swarm.CREF.TR.RecvDecStepNoRatchetWAtHelpersPure
import Symbolic.Proofs.Swarm.CREF.TR.TrStateRkCkIk
import Symbolic.Proofs.Swarm.CREF.TROpen
import Symbolic.Proofs.Swarm.CREF.TR.Leaks -- shake: keep
import Symbolic.Proofs.Swarm.CREF.TR.PQGamma -- shake: keep
import Symbolic.Proofs.Swarm.CREF.TR.PQModelRunNil -- shake: keep

/-!
# Skipped-Key vs. Chain-Step Seed Equality Bridges

Proves `A2bSkStepSeedEq` (`a2b_skStepSeedEq_of_shapeRes`) when the implementation takes its
chain-step branch while a `decryptSkipped` move reads a non-colliding message under a cached
skipped seed.
-/

@[expose] public section

cref_hide_foreign_instances
set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace Symbolic.Swarm.CREF.CliPureRcv.TR.RecvDecStepTiePure
open Symbolic.Swarm.CREF.TR hiding at?_append_of_lt gamma_concat gamma_dhPk getLocalState_fst newRandoms_append_rnd runMoves_append runTrace_append runTrace_snoc runVis_append runVis_snoc run_bind_fst run_bind_snd
open Symbolic.Swarm.CREF Symbolic.Swarm.CREF.CliPure Symbolic.Swarm.CREF.CliPureRcv
open Symbolic.Swarm.CREF.CliPureRcv.RecvWirePure
open Symbolic.Swarm.CREF.CliPure.TR Symbolic.Swarm.CREF.CliPureRcv.TR
open Symbolic.Swarm.CREF.CliPureRcv.TRPure
open Symbolic.Swarm.CREF.TR.RecvDecStep
open Symbolic.Swarm.CREF.CliPure.TR.RecvDecStep hiding SpqrSem StEntry TREntry
open Symbolic.Swarm.CREF.CliPureRcv.TR.RecvDecStepPure
open Symbolic.Swarm.CREF.CliPure.TR.RecvDecStepAt
open Symbolic.Swarm.CREF.CliPureRcv.TR.RecvDecStepAtPure

cref_open
cref_open_tr

open DY DY.Comparse DY.Literal DY.Libsignal
open DY.Libsignal.TripleRatchet (RecvChain findRecvChain consumeMessageKey computeMac)
open DY.Libsignal.TripleRatchet
open DY.Libsignal.TripleRatchet.Refinement (wireWhisperTag)
open DY.Libsignal.Refinement (sha256CompressFunction ExternCryptoLawsHold)
open DY.Libsignal.HwEvents DY.Libsignal.Rust
open CryptoGames CryptoGames.HMAC CryptoGames.HKDF
open CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open CryptoVerification.LibsignalTripleRatchet CryptoVerification.LibsignalProtoCodec
open CryptoVerification.E2E CryptoVerification.E2E.InMem CryptoVerification.E2E.Record CryptoVerification.E2E.RecordX
open CryptoVerification.E2E.Bin hiding RecordCanonical recordDeserializeOpenSpec encodeRecord
open CryptoVerification.E2E.Pqxdh.WireEntries
open CryptoVerification.E2E.Pqxdh.WireEntries.SymP3 hiding encodeRecord
open CryptoProofLib.Refinement (ExternInterpretation)
open Proofs.libsignal.Hooks2 (cryptoOf')
open Proofs.libsignal.RngG Proofs.libsignal.RngG.R3 Proofs.libsignal.RngG.CliPure.R3
open Swarm.Phase0WholeFunctionBridge (sessionToRecordRec sessionToSessionRec)
open Symbolic.Swarm.CREF Symbolic.Swarm.CREF.CliPure Symbolic.Swarm.CREF.CliPureRcv
open Symbolic.Swarm.CREF.CliPure.TR Symbolic.Swarm.CREF.CliPureRcv.TR
open Symbolic.Swarm.CREF.CliPure.TR.SendRetCoins (stateRel_sessionToRecordRec_extract_TR
  gamma_trMsgKeys_eq_generateKeys gamma_computeMac_tr)
open Symbolic.Swarm.TRREF.SpqrSemOf (saltToBytes)

private theorem verifyMacWithAddresses_eq_true_iff_cli (F)
    (m : CryptoGames.LibsignalSession.SignalMessage) (expected : Option (List (BitVec 8)))
    (sender receiver : CryptoGames.LibsignalSession.IdentityKey) (macKey : BitVec 256) :
    m.verifyMacWithAddresses F expected sender receiver macKey = true ↔
      m.verifyMac F sender receiver macKey = true ∧
      CryptoGames.LibsignalAead.addressCheckPasses m.addresses expected = true := by
  simp [CryptoGames.LibsignalSession.SignalMessage.verifyMacWithAddresses]

private theorem a2b_tryFrom_serialized_eq {body : HwBytes} {m : SignalMessage}
    (htry : SignalMessage.tryFrom protoSignalCodec body = .ok m) : m.serialized = body := by
  simp only [SignalMessage.tryFrom, bind, Except.bind, Pure.pure, Except.pure, throw, throwThe,
    MonadExceptOf.throw] at htry
  split at htry; · cases htry
  split at htry; · cases htry
  split at htry; · cases htry
  split at htry <;> try cases htry
  split at htry <;> try cases htry
  split at htry <;> try cases htry
  split at htry <;> try cases htry
  split at htry <;> try cases htry
  rfl

/-- Extracts the consumed chain seed, `findRecvChain` lookup, ratchet-key byte match, and own-key
MAC byte equality from a successful chain-step evaluation. -/
theorem a2b_seedEq_core
    (interpretation : ExternInterpretation) (hceh : ExternCryptoLawsHold interpretation)
    (r₀ : ProtocolSetup) (hwf : ProtocolSetupWF r₀) (S : OpaqueSymbolSemantics) (hS : S = compSemOf interpretation r₀)
    (g : Ghost) (ms : List Move)
    (hcompat : GhostAndSemMatchSetup interpretation r₀ S g) (hrun : ModelRun r₀ ms)
    (hat : RecvDecStepAt.RecvAtFacts interpretation r₀ S g ms)
    (p : Participant) (stateIdx : Nat) (st : TRState) (c : RecvChain) (t : DY.Bytes)
    (msg : TRSignalMsg) (body : HwBytes) (r : StateAndMessage) (g_rw : RecvWireGhost)
    (m : SignalMessage) (ci : Nat) (rc : ReceiverChain) (ck : ChainKey)
    (newPqrState : HwBytes) (pqrKey : HKDF.Salt)
    (hst : ((PersistentLocalState.getLocalState p stateIdx : Traceful TRState).run
      (runTraceMoves r₀ ms)).1 = some st)
    (hrel : StateRel interpretation S g st (sessionToRecordRec g_rw.sess))
    (hnd : ((sessionToRecordRec g_rw.sess).current.receiverChains.map
      ChainRec.senderRatchetKey).Nodup)
    (hpq : g_rw.sess.state.pqRatchetState = gamma interpretation S g st.spqr)
    (hks : TRKeyShape interpretation S g st)
    (hc : st.recv[ci]? = some c)
    (hrep : t ∈ recvRepresentations interpretation r₀ S g ms body)
    (hparse : parseTrSignalMsg t = some msg)
    (hwire : g_rw.wireBytes = wireWhisperTag :: body)
    (htry : SignalMessage.tryFrom protoSignalCodec body = .ok m)
    (hrc : g_rw.sess.state.receiverChains[ci]? = some rc)
    (hrc_key : rc.senderRatchetKey = m.senderRatchetKey) (hck : rc.chainKey = some ck)
    (hstep_idx : ck.index ≤ m.counter)
    (hrecv_spqr : (Symbolic.Swarm.TRREF.SpqrSemOf.spqrModelOf interpretation).recv
        g_rw.sess.state.pqRatchetState m.pqRatchet = .ok (newPqrState, pqrKey))
    (heval : TR.PureRecvEval.pureEvalRecvWireWithCoinsW (cryptoOf' interpretation)
        (Proofs.libsignal.SR.interpW interpretation)
        (Symbolic.Swarm.TRREF.SpqrSemOf.spqrModelOf interpretation) g_rw 0#256 =
        some (r.state, r.message)) :
    ∃ seed_c c', consumeMessageKey c msg.counter = some (seed_c, c') ∧
      findRecvChain st.recv c.ratchetKey = some c ∧
      gamma interpretation S g c.ratchetKey = gamma interpretation S g msg.ratchetKey ∧
      st ∈ availableStates r₀ (runTraceMoves r₀ ms) ∧
      ({ st := st.spqr, msg := msg.pqRatchet } : DY.Spqr.RecvKey.SubF DY.Bytes).pack ∈
        ownKeys r₀ (runTraceMoves r₀ ms) st msg ∧
      gamma interpretation S g (computeMac (trMsgKeys
          ({ st := st.spqr, msg := msg.pqRatchet } : DY.Spqr.RecvKey.SubF DY.Bytes).pack seed_c).macKey
          st.peerIk st.myIk msg.wire) =
        gamma interpretation S g msg.mac := by
  have hnodup_rc : (g_rw.sess.state.receiverChains.map ReceiverChain.senderRatchetKey).Nodup := by
    have hmap : (sessionToRecordRec g_rw.sess).current.receiverChains.map
          ChainRec.senderRatchetKey =
        (g_rw.sess.state.receiverChains.map ReceiverChain.senderRatchetKey).map
          PublicKey.serialize := by
      dsimp only [sessionToRecordRec, sessionToSessionRec]; rw [List.map_map, List.map_map]; rfl
    exact List.Nodup.of_map PublicKey.serialize (hmap ▸ hnd)
  obtain ⟨role, remIk, ck_adv, ck_next, r_adv, r2, mkGen, st', _hrole, _hVer, hRem, hFind, hNotLt,
      hJump, hAdv, hNext, hSet, hMkGen, hMac, _hDec, _hSt', _hr_enc⟩ :=
    evalRecvWireWithCoinsW_noRatchet_inv interpretation body r g_rw m ci rc ck newPqrState pqrKey
      hwire htry hrc hrc_key hck hstep_idx hnodup_rc hrecv_spqr heval
  have hst_avail : st ∈ availableStates r₀ (runTraceMoves r₀ ms) :=
    Symbolic.Swarm.CREF.TR.RecvHistStep2.mem_availableStates_of_at? r₀ ms
      (Symbolic.Swarm.CREF.TR.FreshSigma.at?_eq_some_of_getLocalState_some hst)
  have hRkLens : ∀ c ∈ st.recv, (gamma interpretation S g c.ratchetKey).length = 32 :=
    hat.lens st hst_avail
  have hst_rci : TrStateRkCkIk r₀ st := trStateRkCkIk_of_getLocalState hrun hst
  have hCkLens : ∀ c ∈ st.recv, (gamma interpretation S g c.chainKey).length = 32 :=
    hst_rci.recv_ck_len interpretation S g hwf hcompat
  have hNodupSym : (st.recv.map RecvChain.ratchetKey).Nodup :=
    nodup_ratchetKey_of_stateRel_tr hrel hnd
  obtain ⟨ci₀, ch, c₀, mks', seed, c', hch0, hc0, hfind₀, hsrk0, htheir, _hck, _hch_ck,
      hcons₀_bv, hSeedEq, hCntEq, _hc'_rk, _hc'_rIdx, _hR2Eq, _hRel_c, _hMks'⟩ :=
    stateRel_and_consumeMessageKey_of_existing_tr interpretation S g hrel hNodupSym hCkLens
      (gamma_litOf interpretation S g newPqrState) hFind hNotLt hJump hAdv hNext hSet
  have hc₀_mem : c₀ ∈ st.recv := List.mem_of_getElem? hc0
  have hc_mem : c ∈ st.recv := List.mem_of_getElem? hc
  obtain ⟨hwire_t, hmac_t, _hhd_t, hfld⟩ := hrep.2.2.2 msg hparse
  obtain ⟨_hct_m, hrk_m, _hpq_m, hctr_m, _hver_m⟩ := hfld m htry
  have hγ_c₀ : gamma interpretation S g c₀.ratchetKey = m.senderRatchetKey.bytes.toList := by
    rw [htheir]; simp [vec32, hRkLens c₀ hc₀_mem]
  obtain ⟨c₁, hc₁, _hidx₁, hγ_c₁⟩ := a2b_modelChain_of_binChain hrel hrc hck
  have hc₁_eq : c = c₁ := Option.some.inj (hc.symm.trans hc₁)
  subst hc₁_eq
  have hcc : c₀ = c :=
    a2b_recvChain_eq_of_gamma hrel hnd hc₀_mem hc_mem (by rw [hγ_c₀, hγ_c₁, hrc_key])
  subst hcc
  have hctr_eq : UInt32.ofBitVec m.counter = msg.counter := UInt32.ext hctr_m.symm
  have hcons : consumeMessageKey c₀ msg.counter = some (seed, c') := by
    rw [← hctr_eq]; exact hcons₀_bv
  let k_own : DY.Bytes := ({ st := st.spqr, msg := msg.pqRatchet } : DY.Spqr.RecvKey.SubF DY.Bytes).pack
  have hk_own : k_own ∈ ownKeys r₀ (runTraceMoves r₀ ms) st msg := by
    unfold ownKeys; exact List.mem_map_of_mem (List.mem_filter.mpr ⟨hst_avail, beq_self_eq_true _⟩)
  have hk_own_gam : gamma interpretation S g k_own = spqrKeyBytes (saltToBytes pqrKey) :=
    (spqrRecv_step_gamma_state_and_key interpretation hceh r₀ S hS g ms body st g_rw t msg m
      newPqrState pqrKey hpq hrep hparse htry hrecv_spqr).2
  have hmkGen_eq : mkGen = ⟨gamma interpretation S g seed, m.counter⟩ := by
    rw [hMkGen]; change ck_adv.messageKeys (sha256CompressFunction interpretation) = _
    rcases h : ck_adv.messageKeys (sha256CompressFunction interpretation) with ⟨sd, ct⟩
    rw [h] at hSeedEq hCntEq; dsimp only at hSeedEq hCntEq; subst hSeedEq hCntEq; rfl
  obtain ⟨_hck_mk, hmk_mk, _hiv_mk, _⟩ :=
    gamma_trMsgKeys_eq_generateKeys interpretation S g k_own seed m.counter pqrKey hk_own_gam
  obtain ⟨_hrk_sess, _hcks_sess, _hdhs_sess, hloc_ser, ⟨rem0, hrem0, hrem_ser⟩, _hrc_sess⟩ :=
    stateRel_sessionToRecordRec_extract_TR interpretation S g st g_rw.sess hrel
  rw [hRem] at hrem0; injection hrem0 with hrem_eq; subst hrem_eq
  have hpeer_ser : remIk.serialize = gamma interpretation S g st.peerIk :=
    hrem_ser.trans hks.peerIk_ser
  have hmy_ser : g_rw.sess.state.localIdentity.serialize = gamma interpretation S g st.myIk :=
    hloc_ser.trans hks.myIk_ser
  have hm_ser : m.serialized = body := a2b_tryFrom_serialized_eq htry
  have hMacBytes : body.drop (body.length - 8) =
      gamma interpretation S g (computeMac (trMsgKeys k_own seed).macKey st.peerIk st.myIk msg.wire) := by
    have hmac_ver : m.verifyMac (cryptoOf' interpretation).F remIk g_rw.sess.state.localIdentity
        (mkGen.generateKeys (cryptoOf' interpretation).F pqrKey).macKey = true :=
      ((verifyMacWithAddresses_eq_true_iff_cli _ _ _ _ _ _).mp hMac).1
    unfold SignalMessage.verifyMac macLength at hmac_ver; dsimp only at hmac_ver
    have hmac_eq := (beq_iff_eq.mp hmac_ver).symm; rw [hm_ser] at hmac_eq; rw [hmac_eq]
    have hkey_mk : keyToBytes32 ((mkGen.generateKeys (cryptoOf' interpretation).F pqrKey).macKey) =
        gamma interpretation S g (trMsgKeys k_own seed).macKey := by rw [hmkGen_eq]; exact hmk_mk
    exact gamma_computeMac_tr interpretation S g (trMsgKeys k_own seed).macKey st.peerIk st.myIk
      msg.wire remIk g_rw.sess.state.localIdentity
      ((mkGen.generateKeys (cryptoOf' interpretation).F pqrKey).macKey)
      hkey_mk hpeer_ser hmy_ser (body.take (body.length - 8)) hwire_t.symm
  exact ⟨seed, c', hcons, hfind₀, hγ_c₀.trans hrk_m.symm, hst_avail, hk_own,
    hMacBytes.symm.trans hmac_t.symm⟩

/-- Discharges `A2bSkStepSeedEq` from `A2bCrossSeedExcl`, `A2bSeedShapeEqRes`, and
`A2bSeedRkAliasRes`. -/
theorem a2b_skStepSeedEq_of_shapeRes
    (interpretation : ExternInterpretation) (hceh : ExternCryptoLawsHold interpretation)
    (r₀ : ProtocolSetup) (hwf : ProtocolSetupWF r₀) (S : OpaqueSymbolSemantics) (hS : S = compSemOf interpretation r₀)
    (g : Ghost) (ms : List Move) (acc : List MachineEvent)
    (hcompat : GhostAndSemMatchSetup interpretation r₀ S g) (hrun : ModelRun r₀ ms)
    (hat : RecvDecStepAt.RecvAtFacts interpretation r₀ S g ms)
    (hX : A2bCrossSeedExcl interpretation r₀ S g ms acc)
    (hA : A2bSeedShapeEqRes interpretation r₀ S g ms acc)
    (hB : A2bSeedRkAliasRes interpretation r₀ S g ms acc) :
    A2bSkStepSeedEq interpretation r₀ S g ms acc := by
  intro p stateIdx st c t msg skIdx rIdx_s srcIdx seed_s pqSalt body r g_rw m ci rc ck
    hst hcur hrel hc hrep hparse hnc hsk hmac_eq hfind_s hwire htry hrc hrc_key hck hstep_idx heval
    newPqrState pqrKey hver hnd hpq hks hrecv_spqr
  obtain ⟨seed_c, c', hcons, _hfind, hγrk, hst_avail, hk_own, hmacγ⟩ :=
    a2b_seedEq_core interpretation hceh r₀ hwf S hS g ms hcompat hrun hat p stateIdx st c t msg body
      r g_rw m ci rc ck newPqrState pqrKey hst hrel hnd hpq hks hc hrep hparse hwire htry hrc
      hrc_key hck hstep_idx hrecv_spqr heval
  refine ⟨seed_c, c', hcons, ?_⟩
  by_cases hγ : gamma interpretation S g seed_c = gamma interpretation S g seed_s
  · exact a2b_seedEq_of_shapeRes interpretation r₀ S g ms acc hrun hA hB p stateIdx st c c' t msg
      skIdx rIdx_s srcIdx seed_s seed_c pqSalt body _ hst hcur hrel hnd hver
      (List.mem_of_getElem? hc) hrep hparse hnc hsk hmac_eq hγrk hcons hγ
  · exact (hnc (hX t ⟨msg, hparse, hver, seed_s, a2b_mem_skippedSeedsFor hsk, pqSalt, st,
      hst_avail, hfind_s, hmac_eq,
      st, hst_avail, c, List.mem_of_getElem? hc, seed_c, c', hγrk, hcons, hγ, _, hk_own,
      hmacγ⟩)).elim

end Symbolic.Swarm.CREF.CliPureRcv.TR.RecvDecStepTiePure
