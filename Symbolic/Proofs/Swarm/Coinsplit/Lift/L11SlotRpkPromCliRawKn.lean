/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

import Batteries.Data.UInt
import DY.Bytes.Basic
import DY.Trace.Basic
import DY.Trace.Monad
import DY.Trace.Manipulation
import DY.Actions.Network
public import Symbolic.Proofs.Swarm.CREF.RecvPrekeyProm.PromXplAssemblyPure
public import Symbolic.Proofs.Swarm.CREF.Sem
import Symbolic.Proofs.Swarm.CREF.Cli.Rpk.DecCryptoBPure
import Symbolic.Proofs.Swarm.CREF.Cli.Rpk.RatchetDHRkSwapStepTRPure
import Symbolic.Proofs.Swarm.CREF.Cli.Rpk.RatchetDHRkSwapStepTRPureA
import Symbolic.Proofs.Swarm.CREF.Cli.Rpk.RecvDecStepCommonPure
import Symbolic.Proofs.Swarm.CREF.Cli.Rpk.RecvDecStepNoRatchetPure
import Symbolic.Proofs.Swarm.CREF.Cli.Rpk.RecvDecStepNoRatchetWAtPure
import Symbolic.Proofs.Swarm.CREF.Cli.Rpk.RecvDecStepRatchetDHAtPure
import Symbolic.Proofs.Swarm.CREF.Cli.Rpk.RecvDecStepRatchetDHaPure
import Symbolic.Proofs.Swarm.CREF.Cli.Rpk.RecvDecStepRatchetDHaPureA
import Symbolic.Proofs.Swarm.CREF.Cli.Rpk.RecvDecStepSkippedG1LeavesPure
import Symbolic.Proofs.Swarm.CREF.Cli.Rpk.RecvDecStepSpqrPure
import Symbolic.Proofs.Swarm.CREF.Cli.Rpk.SendRetCoinsCliPure
import Symbolic.Proofs.Swarm.CREF.Cli.Rpk.SlotG2ProvBPure
import Symbolic.Proofs.Swarm.CREF.Cli.Rpk.SpinePeelPure
import Symbolic.Proofs.Swarm.CREF.Cli.World.RelCliPure
import Symbolic.Proofs.Swarm.CREF.Prelude
import Symbolic.Proofs.Swarm.CREF.RecvPrekeyProm.HxplG2W.BaseKeyFromRBKS
import Symbolic.Proofs.Swarm.CREF.RecvPrekeyProm.HxplG2W.SkippedProvBPure
import Symbolic.Proofs.Swarm.CREF.RecvPrekeyProm.HxplG2W.SupplyPkPure
import Symbolic.Proofs.Swarm.CREF.RecvPrekeyProm.HxplG2W.SupplyPure
import Symbolic.Proofs.Swarm.CREF.RecvPrekeyProm.HxplG2W.VersionPure
import Symbolic.Proofs.Swarm.CREF.RecvPrekeyProm.HxplRep
import Symbolic.Proofs.Swarm.CREF.RecvWire.By2SupplyA
import Symbolic.Proofs.Swarm.CREF.TR.G1.LitKeyKnownFinal
import Symbolic.Proofs.Swarm.CREF.TR.Leaks
import Symbolic.Proofs.Swarm.CREF.TR.RecvDecStepSkippedProvTR
import Symbolic.Proofs.Swarm.CREF.TR.RecvRep
import Symbolic.Proofs.Swarm.CREF.TR.TrStateRkCkIk
import Symbolic.Proofs.Swarm.CREF.TROpen
import Symbolic.DYBridge.DY.Bytes.Basic
import Symbolic.DYBridge.DY.Trace.Basic
import Symbolic.DYBridge.DY.Trace.Monad
import Symbolic.DYBridge.DY.Trace.Manipulation
import Symbolic.DYBridge.DY.Actions.Network

/-!
# Raw Witness Assembly for Session-Promote Pre-Key `recv`

Assembles the single-trace `PromXplRawKnWitness` (`prom_rawKnWitness_at_clean`) for Bob's
matching-session promote `recv` branch.
-/

@[expose] public section

set_option autoImplicit false

namespace Symbolic.Swarm.Coinsplit.Lift.L11

open CryptoProofLib.Refinement (ExternInterpretation)
open _root_.DY (Participant)
open _root_.DY.Libsignal (HwBytes)
open _root_.DY.Libsignal.HwEvents (MachineEvent StateAndMessage)
open _root_.DY.Libsignal.Composed.Refinement
open _root_.DY.Libsignal.Composed.Refinement.Cli
open _root_.DY.Libsignal.TripleRatchet.Refinement (wireWhisperTag)
open CryptoGames CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open CryptoVerification.LibsignalProtoCodec (protoSignalCodec)
open CryptoVerification.SignalSession
open Proofs.libsignal.Hooks2 (cryptoOf')
open Symbolic.Swarm.CREF
open Symbolic.Swarm.CREF.CliPure hiding pureDrawsCoins

section RawKn

cref_open
cref_open_tr

open _root_.DY _root_.DY.Comparse _root_.DY.Literal _root_.DY.Libsignal
open _root_.DY.Libsignal.Rust
open _root_.DY.Libsignal.Composed
open _root_.DY.Libsignal.TripleRatchet (SessionInfo DRState RecvChain findRecvChain setRecvChain recvChainFor consumeMessageKey chainKeyAt kdfCk kdfRk maxForwardJumps u32Max computeMac messageVersion createChain x25519LowOrder TRState TREvent TRSignalMsg parseTrSignalMsg isCurrentSnapshot skippedKeyUsedB receiverKeyUsedB trMsgKeys)
open _root_.DY.Libsignal.Refinement (ExternCryptoLawsHold sha256CompressFunction aesCbcDecryptSymbol)
open CryptoVerification
open CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.E2E.InMem CryptoVerification.E2E.Record
open CryptoVerification.E2E.Pqxdh.WireEntries.SymP3 (RecvWireGhost)
open Symbolic.Swarm.TRREF
open Symbolic.Swarm.TRREF.SpqrSemOf (saltToBytes)
open Symbolic.Swarm.CREF.TR.Pure
open Symbolic.Swarm.CREF.TR Symbolic.Swarm.CREF.CliPure.TR
open Symbolic.Swarm.CREF.TR.RecvDec hiding StEntry TREntry TRRecvAllCollide
open Symbolic.Swarm.CREF.TR.RecvDecStep
open Symbolic.Swarm.CREF.CliPure.TR.RecvDecStep hiding StEntry TREntry
  isCurrentSnapshot_append_non_st at?_eq_none_of_le at?_append_of_lt
open Symbolic.Swarm.CREF.CliPure.TR.RecvDecStepAt
open Symbolic.Swarm.CREF.TR.FreshSigma hiding TREntry StEntry
open Symbolic.Swarm.CREF.TR.G1 Symbolic.Swarm.CREF.CliPure.TR.G1
open Symbolic.Swarm.CREF.CliPure.TR.SendRetCoins
  (gamma_trMsgKeys_eq_generateKeys stateRel_sessionToRecordRec_extract_TR gamma_computeMac_tr)
open Proofs.libsignal.RngG Proofs.libsignal.RngG.R3 Proofs.libsignal.RngG.CliPure.R3
open Swarm.Phase0WholeFunctionBridge (sessionToRecordRec sessionToSessionRec)

private theorem promRawCtx_at_clean
    {interpretation : ExternInterpretation}
    (hext : ExternContractsHoldCli interpretation)
    {r : ProtocolSetup} (hwf : ProtocolSetupWF r) {S : OpaqueSymbolSemantics}
    {who : List Participant} {ok : Nat → Bool}
    {j : Nat} {e' : PromTurn} {mid acc : List MachineEvent}
    {rec b : HwBytes} {sm : StateAndMessage} {pf : PreKeyFields}
    {sess sess' : Session (List (BitVec 8))}
    {coins : BitVec 256} {expected : Option (List (BitVec 8))} {pt : List (BitVec 8)}
    (hC : PromAcceptCallBy₂ interpretation r S who ok j e' mid acc rec b sm pf
      sess sess' coins expected pt)
    {g : Ghost} {ms : List Move} (hc : CleanBy interpretation r S who ok g ms acc) :
    PromRawCtx interpretation r S g ms acc := by
  have hch := prom_cHist_at_clean hC hc
  have hreach : (runTraceMoves r ms).Reachable Composed.reachability := hc.matched.2.1.2.2.1.1
  exact
    { atF := prom_recvAtFacts_at_clean hC hc
        (trRecvFreshAll_of_matchedPrefix interpretation hc.matched)
      pkNR := rcv_hPkDNR_of_cleanBy hext hwf hc
        (rcv_honestSkelUniq_of_matchedPrefix hc.matched)
        (rcv_abs_of_matchedPrefix hc.matched)
      pkSk := skipped_pk_dispatch_atK' hext hwf hc
        (rcv_skippedNotJunkSeedProvAt_of_notLowAll hreach hch.2.1)
        (rcv_byteChainReselectAt_of_c16 interpretation r S g ms acc)
        hch.2.2.1
        (skippedFreshAliasExclB_of_reach interpretation hreach)
      abs' := prom_g1cAttackerBuiltSeedExcl'_of_matchedPrefix hc.matched }

theorem prom_tag_ne_wireWhisperTag_of_parsePreKeyWire
    {tag : BitVec 8} {body : HwBytes} {pf : PreKeyFields}
    (hpf : parsePreKeyWire (tag :: body) = some pf) :
    tag ≠ wireWhisperTag := by
  rintro rfl
  unfold parsePreKeyWire wireWhisperTag _root_.DY.Libsignal.PQXDH.Refinement.wirePrekeyTag at hpf
  simp at hpf

private theorem prom_tryFrom_serialized_eq {body : HwBytes} {m : SignalMessage}
    (htry : SignalMessage.tryFrom protoSignalCodec body = .ok m) : m.serialized = body := by
  simp only [SignalMessage.tryFrom, bind, Except.bind, Pure.pure, Except.pure,
    throw, throwThe, MonadExceptOf.throw] at htry
  split at htry; · cases htry
  split at htry; · cases htry
  split at htry; · cases htry
  split at htry <;> try cases htry
  split at htry <;> try cases htry
  split at htry <;> try cases htry
  split at htry <;> try cases htry
  split at htry <;> try cases htry
  rfl

private theorem prom_gamma_randTerm32_eq
    (interpretation : ExternInterpretation) (S : OpaqueSymbolSemantics) (g : Ghost) (idx : Nat) :
    gamma interpretation S g (randTerm idx 32) = g.σ idx 32 := by
  unfold gamma gamma' randTerm
  rw [_root_.DY.Bytes.rec_eq (concretizeRandom g) (concretizeAll interpretation S g)]; rfl

private theorem prom_two_attackerSend_setup
    {interpretation : ExternInterpretation} {r₀ : ProtocolSetup} {S : OpaqueSymbolSemantics} {who : List Participant}
    {g : Ghost} {ms₁ : List Move} {acc : List MachineEvent}
    {p : Participant} {stateIdx : Nat} {st : TRState} {pqSalt t : DY.Bytes}
    (hmp : MatchedPrefix interpretation r₀ S who g ms₁ acc)
    (hpq_kn : pqSalt.AttackerKnows (runTraceMoves r₀ ms₁)) (ht_kn : t.AttackerKnows (runTraceMoves r₀ ms₁))
    (hcur : isCurrentSnapshot (runTraceMoves r₀ ms₁) stateIdx = true)
    (hst : ((PersistentLocalState.getLocalState p stateIdx : Traceful TRState).run (runTraceMoves r₀ ms₁)).1 = some st) :
    let ms₂ := ms₁ ++ [Move.attackerSend pqSalt, Move.attackerSend t]
    runTraceMoves r₀ ms₂ = ((runTraceMoves r₀ ms₁).append (⟨pqSalt⟩ : Network.ExecEntryT)).append (⟨t⟩ : Network.ExecEntryT) ∧
    (runTraceMoves r₀ ms₂).length = (runTraceMoves r₀ ms₁).length + 2 ∧
    MatchedPrefix interpretation r₀ S who g ms₂ acc ∧
    isCurrentSnapshot (runTraceMoves r₀ ms₂) stateIdx = true ∧
    ((PersistentLocalState.getLocalState p stateIdx : Traceful TRState).run (runTraceMoves r₀ ms₂)).1 = some st ∧
    (runTraceMoves r₀ ms₂).getMessageSentAt ((runTraceMoves r₀ ms₁).length + 1) = some t := by
  let tr₀ := runTraceMoves r₀ ms₁
  let ms_a1 := ms₁ ++ [Move.attackerSend pqSalt]
  let ms_a2 := ms_a1 ++ [Move.attackerSend t]
  dsimp only; rw [show ms₁ ++ [Move.attackerSend pqSalt, Move.attackerSend t] = ms_a2 by simp [ms_a2, ms_a1, List.append_assoc]]
  have htr_a1 : runTraceMoves r₀ ms_a1 = tr₀.append (⟨pqSalt⟩ : Network.ExecEntryT) := by
    rw [TR.runTrace_snoc]
    dsimp only [Move.next, Move.act, tr₀]
    simp only [Symbolic.DYBridge.DY.Network.sendMessage_eq_1,
      Symbolic.DYBridge.DY.appendEntry_eq_1,
      _root_.DY.Traceful.run_bind, _root_.DY.Traceful.run_mk, _root_.DY.Traceful.run_pure]
  have htr_a2 : runTraceMoves r₀ ms_a2 = (tr₀.append (⟨pqSalt⟩ : Network.ExecEntryT)).append (⟨t⟩ : Network.ExecEntryT) := by
    rw [TR.runTrace_snoc, htr_a1]
    dsimp only [Move.next, Move.act]
    simp only [Symbolic.DYBridge.DY.Network.sendMessage_eq_1,
      Symbolic.DYBridge.DY.appendEntry_eq_1,
      _root_.DY.Traceful.run_bind, _root_.DY.Traceful.run_mk, _root_.DY.Traceful.run_pure]
  have hmp2 := RecvDec.matchedPrefix_attackerSend (RecvDec.matchedPrefix_attackerSend hmp hpq_kn)
    (by rw [htr_a1]; exact attackerKnows_append_g1 ht_kn)
  refine ⟨htr_a2, by rw [htr_a2]; simp only [Symbolic.DYBridge.DY.Trace.append_eq_1, Symbolic.DYBridge.DY.Trace.length_eq_2, tr₀], hmp2, ?_, ?_, ?_⟩
  · rw [htr_a2, RecvDec.isCurrentSnapshot_append_non_st _ _ rfl, RecvDec.isCurrentSnapshot_append_non_st _ _ rfl]; exact hcur
  · rw [TR.runTrace_snoc, getLocalState_attackerSend, TR.runTrace_snoc, getLocalState_attackerSend]; exact hst
  · rw [TR.runTrace_snoc, htr_a1]
    have hlen1 : (tr₀.append (⟨pqSalt⟩ : Network.ExecEntryT)).length =
        (runTraceMoves r₀ ms₁).length + 1 := by
      simp only [Symbolic.DYBridge.DY.Trace.append_eq_1, Symbolic.DYBridge.DY.Trace.length_eq_2, tr₀]
    rw [← hlen1]
    exact RecvDec.getMessageSentAt_attackerSend _ t

private theorem prom_bob_session_extract {interpretation : ExternInterpretation} {r : ProtocolSetup} {S : OpaqueSymbolSemantics}
    {who : List Participant} {ok : Nat → Bool} (hwf : ProtocolSetupWF r)
    {j : Nat} {e' : PromTurn} {mid acc : List MachineEvent}
    {rec : HwBytes} {tag : BitVec 8} {body : HwBytes} {sm : StateAndMessage} {pf : PreKeyFields}
    {sess sess' : Session (List (BitVec 8))} {coins : BitVec 256} {expected : Option (List (BitVec 8))} {pt : List (BitVec 8)}
    (hC : PromAcceptCallBy₂ interpretation r S who ok j e' mid acc rec (tag :: body) sm pf sess sess' coins expected pt)
    {g : Ghost} {ms : List Move} (hc : CleanBy interpretation r S who ok g ms acc) :
    PureTRRecordStateInv interpretation r S (pureTrSlots r) g ms (fun q => if q = r.bob then some rec else none) ∧
    (sess.state.receiverChains.map ReceiverChain.senderRatchetKey).Nodup := by
  have hss : SingleSession rec := let ⟨rr₀, _, hrec_rr₀, hprev₀, _⟩ := hC.entry.pm; ⟨rr₀, hrec_rr₀, hprev₀⟩
  have hrr := pureCRecRelH_single (hC.entry.ready.2.1.recs hc r.bob rec hC.entry.rec_lookup).2.2 hss
  have hrsi : PureTRRecordStateInv interpretation r S (pureTrSlots r) g ms (fun q => if q = r.bob then some rec else none) :=
    hrr.elim id (fun ⟨hab, _⟩ => False.elim (hwf.1 hab.symm))
  obtain ⟨_, rec₀, _, _, hrecBytes₀, _, _, _, _, _, _, hnd₀⟩ := hrsi r.bob rec (by simp only [↓reduceIte])
  have hnorm_eq := rec_eq_sessionToRecordRec_of_canonical_Q hrecBytes₀ hC.out.hcan_in
  have hrc_rec₀ : rec₀.current.receiverChains = (sessionToRecordRec sess).current.receiverChains :=
    congrArg (fun r => r.current.receiverChains) hnorm_eq
  have hmap : (sessionToRecordRec sess).current.receiverChains.map ChainRec.senderRatchetKey =
      (sess.state.receiverChains.map ReceiverChain.senderRatchetKey).map PublicKey.serialize := by
    dsimp only [sessionToRecordRec, sessionToSessionRec]; rw [List.map_map, List.map_map]; rfl
  exact ⟨hrsi, List.Nodup.of_map PublicKey.serialize (hmap ▸ hrc_rec₀ ▸ hnd₀.1)⟩

private theorem prom_dec_mac_gamma {interpretation : ExternInterpretation} {S : OpaqueSymbolSemantics}
    (g0 : Ghost) {pf : PreKeyFields} {pt : List (BitVec 8)} {sess : Session (List (BitVec 8))}
    {expected : Option (List (BitVec 8))}
    {k_own seed : DY.Bytes} {pqrKey : HKDF.Salt} {mkGen : MessageKeyGenerator}
    {remIk : IdentityKey} {peerIk myIk : DY.Bytes} {msg₀ : TRSignalMsg}
    (htry : SignalMessage.tryFrom protoSignalCodec pf.message = .ok pf.inner)
    (hk_own_gam : gamma interpretation S g0 k_own = spqrKeyBytes (saltToBytes pqrKey))
    (hmkGen_eq : mkGen = ⟨gamma interpretation S g0 seed, pf.inner.counter⟩)
    (hDec : (Proofs.libsignal.SR.interpW interpretation).dec (mkGen.generateKeys (cryptoOf' interpretation).F pqrKey).cipherKey
      (mkGen.generateKeys (cryptoOf' interpretation).F pqrKey).iv pf.inner.ciphertext = some pt)
    (hMac : pf.inner.verifyMacWithAddresses (cryptoOf' interpretation).F expected remIk sess.state.localIdentity
      (mkGen.generateKeys (cryptoOf' interpretation).F pqrKey).macKey = true)
    (hpeer_ser : remIk.serialize = gamma interpretation S g0 peerIk)
    (hmy_ser : sess.state.localIdentity.serialize = gamma interpretation S g0 myIk)
    (hwire₀_take : gamma interpretation S g0 msg₀.wire = pf.message.take (pf.message.length - 8)) :
    interpretation aesCbcDecryptSymbol
      [pf.inner.ciphertext, gamma interpretation S g0 (trMsgKeys k_own seed).cipherKey,
        (gamma interpretation S g0 (trMsgKeys k_own seed).iv).take 16] = some pt ∧
    pf.message.drop (pf.message.length - 8) =
      gamma interpretation S g0 (computeMac (trMsgKeys k_own seed).macKey peerIk myIk msg₀.wire) := by
  obtain ⟨hck_mk, hmk_mk, hiv_mk, _⟩ := gamma_trMsgKeys_eq_generateKeys interpretation S g0 k_own seed pf.inner.counter pqrKey hk_own_gam
  refine ⟨?_, ?_⟩
  · rw [← hck_mk, ← hiv_mk]
    change (Proofs.libsignal.SR.interpW interpretation).dec
      (MessageKeyGenerator.generateKeys (cryptoOf' interpretation).F ⟨gamma interpretation S g0 seed, pf.inner.counter⟩ pqrKey).cipherKey
      (MessageKeyGenerator.generateKeys (cryptoOf' interpretation).F ⟨gamma interpretation S g0 seed, pf.inner.counter⟩ pqrKey).iv pf.inner.ciphertext = some pt
    rw [← hmkGen_eq]; exact hDec
  · have hmac_ver : pf.inner.verifyMac (cryptoOf' interpretation).F remIk sess.state.localIdentity
        (mkGen.generateKeys (cryptoOf' interpretation).F pqrKey).macKey = true :=
      ((Proofs.libsignal.RngG.CliPure.DecCrypto.verifyMacWithAddresses_eq_true_iff _ _ _ _ _ _).mp hMac).1
    unfold SignalMessage.verifyMac macLength at hmac_ver; dsimp only at hmac_ver
    have hmac_eq := (beq_iff_eq.mp hmac_ver).symm
    rw [prom_tryFrom_serialized_eq htry] at hmac_eq; rw [hmac_eq]
    exact gamma_computeMac_tr interpretation S g0 (trMsgKeys k_own seed).macKey peerIk myIk msg₀.wire
      remIk sess.state.localIdentity ((mkGen.generateKeys (cryptoOf' interpretation).F pqrKey).macKey)
      (by rw [hmkGen_eq]; exact hmk_mk) hpeer_ser hmy_ser (pf.message.take (pf.message.length - 8)) hwire₀_take.symm

private theorem prom_st_ik_knows {r : ProtocolSetup} (hwf : ProtocolSetupWF r) (ms : List Move) {st₀ : TRState}
    (hrci : TrStateRkCkIk r st₀) :
    st₀.peerIk.AttackerKnows (runTraceMoves r ms) ∧ st₀.myIk.AttackerKnows (runTraceMoves r ms) := by
  have hik0 : (DY.Libsignal.PQXDH.serializedIk (setupPublic r 0)).AttackerKnows (runTraceMoves r ms) :=
    Concat.attacker_knows_concat _ _ _ (Literal.attacker_knows_literalToBytes _ _)
      (Symbolic.Swarm.CREF.CliPure.TR.knows_setupPublic r hwf.1 ms 0 (Or.inl rfl))
  have hik2 : (DY.Libsignal.PQXDH.serializedIk (setupPublic r 2)).AttackerKnows (runTraceMoves r ms) :=
    Concat.attacker_knows_concat _ _ _ (Literal.attacker_knows_literalToBytes _ _)
      (Symbolic.Swarm.CREF.CliPure.TR.knows_setupPublic r hwf.1 ms 2 (Or.inr rfl))
  exact ⟨hrci.peerIk.elim (· ▸ hik0) (· ▸ hik2), hrci.myIk.elim (· ▸ hik0) (· ▸ hik2)⟩

set_option maxHeartbeats 400000 in
private theorem prom_rawKn_skipped
    {interpretation : ExternInterpretation} {r : ProtocolSetup} {S : OpaqueSymbolSemantics}
    {who : List Participant} {ok : Nat → Bool}
    (hext : ExternContractsHoldCli interpretation) (hwf : ProtocolSetupWF r) (hSeq : S = compSemOf interpretation r)
    (hVer : PromVersionOK interpretation r S who ok)
    {j : Nat} {e' : PromTurn} {mid acc : List MachineEvent}
    {rec : HwBytes} {tag : BitVec 8} {body : HwBytes} {sm : StateAndMessage} {pf : PreKeyFields}
    {sess sess' : Session (List (BitVec 8))} {coins : BitVec 256} {expected : Option (List (BitVec 8))} {pt : List (BitVec 8)}
    (hC : PromAcceptCallBy₂ interpretation r S who ok j e' mid acc rec (tag :: body) sm pf sess sess' coins expected pt)
    (hsel : PromDecSelSkipped sess pf.inner mid coins)
    {g : Ghost} {ms : List Move} {t' : DY.Bytes}
    (hc : CleanBy interpretation r S who ok g ms acc) (hctx : PromRawCtx interpretation r S g ms acc)
    (ht' : t' ∈ recvRepresentations interpretation r S g ms pf.message)
    (hncol : ¬ RecvCollision interpretation r S g ms t')
    (hnors : RecvExcuseFree interpretation r S who ok g ms acc (.recv (tag :: body)) (mid ++ [.accept pt]) pf.message t') :
    PromXplRawKnWitness interpretation r S g ms acc mid r.bob tag body pf.message pt := by
  have hmp : MatchedPrefix interpretation r S who g ms acc := hc.matched
  have hmp_nil : MatchedPrefix interpretation r S who g ms (acc ++ []) := by simpa only [List.append_nil] using hmp
  have hPkD_nil : SkippedPkDispatchAtK interpretation r S g ms (acc ++ []) := by simpa only [List.append_nil] using hctx.pkSk
  have hsent_nil : e'.sent = sentBodies (acc ++ []) := by simpa only [List.append_nil] using hC.entry.sent_eq
  have hfit_nil : TR.SendsFit (acc ++ []) := by simpa only [List.append_nil] using hC.entry.ready.2.1.sendsFit
  have hpq : PqFromHonest e'.sent pf.message := hC.entry.pqh pf hC.out.hpf
  have htry : SignalMessage.tryFrom protoSignalCodec pf.message = .ok pf.inner := parsePreKeyWire_inner_tryFrom hC.out.hpf
  obtain ⟨hrsi, hnodup_rc⟩ := prom_bob_session_extract hwf hC hc
  obtain ⟨hp_mem, rec₀, st₀, stateIdx₀, hrecBytes₀, hst₀, hcur₀, hrel₀, hsk_pre₀, _, hks₀, _⟩ :=
    hrsi r.bob rec (by simp only [↓reduceIte])
  let g_rw : RecvWireGhost :=
    { who := 1, aPtr := 0, meBytes := [], stateBytes := rec, sess := sess,
      wirePtr := 0, wireBytes := wireWhisperTag :: pf.message, cur := 0, rest := [], tlsInit := none }
  obtain ⟨hnorm_eq, hrel₀_sess, hpq_sess, _, _, _, _⟩ :=
    pqRatchetState_eq_gamma_pending interpretation S g rec rec₀ st₀ st₀ g_rw hrecBytes₀ hrel₀ hC.out.hcan_in rfl
  have hrc_rec₀ : rec₀.current.receiverChains = (sessionToRecordRec g_rw.sess).current.receiverChains :=
    congrArg (fun r => r.current.receiverChains) hnorm_eq
  have hsk_pre₀' : ∀ c ∈ (sessionToRecordRec g_rw.sess).current.receiverChains,
      ∀ k ∈ c.messageKeys, ∃ pk rIdx srcIdx skIdx seed,
        (runTraceMoves r ms).EventLoggedAt (TREvent.SkippedKeyStored (st₀.sessionInfo r.bob) pk (UInt32.ofBitVec k.1) seed rIdx srcIdx) skIdx ∧
        (!skippedKeyUsedB (runTraceMoves r ms) skIdx) = true ∧
        (!receiverKeyUsedB (runTraceMoves r ms) (st₀.sessionInfo r.bob) seed (UInt32.ofBitVec k.1) rIdx) = true ∧
        gamma interpretation S g seed = k.2 ∧ c.senderRatchetKey = serializedKey (gamma interpretation S g pk) ∧
        (findRecvChain st₀.toDRState.recv pk).isSome = true :=
    fun c hc_mem => hsk_pre₀ c (hrc_rec₀.symm ▸ hc_mem)
  obtain ⟨remIk, _, _, mkGen, newPqrState, pqrKey, _, hmid_nil, _, hRem, _, _, hTake, hrecv_spqr, hMac, hDec, _, _, _⟩ :=
    prom_adapter_skipped_out hC.out hnodup_rc hsel
  subst hmid_nil
  obtain ⟨pk, rIdx, srcIdx, skIdx, seed, hlog, hsk_at, hunused, _, hseed_gam, hlink, hfind_pk⟩ :=
    extract_skippedKeyStored_of_takeSkippedKey_g1 interpretation r S g ms rfl hsk_pre₀' hTake
  obtain ⟨msg₀, hparse₀⟩ := Option.isSome_iff_exists.mp ht'.2.2.1
  have hγ_pk : gamma interpretation S g pk = pf.inner.senderRatchetKey.bytes.toList := (List.cons.inj hlink).2
  have hfld₀ := (ht'.2.2.2 msg₀ hparse₀).2.2.2 pf.inner htry
  have hctr₀ : msg₀.counter = UInt32.ofBitVec pf.inner.counter := UInt32.ext hfld₀.2.2.2.1
  have hver_pf : pf.inner.messageVersion = 4#8 := hVer j e' [] acc rec (tag :: body) sm pf sess sess' coins expected pt hC
  have hver₀ : msg₀.version = messageVersion := by apply UInt8.ext; rw [hfld₀.2.2.2.2, hver_pf]; rfl
  have hreach : (runTraceMoves r ms).Reachable Composed.reachability := hmp.2.1.2.2.1.1
  have hIW : InstallWitnessTR r (runTraceMoves r ms) := installWitnessTR_of_reachable r ms hreach
  have hSeedK_var : TR.G1.JunkTR pk → ∀ x, pk.view? DY.X25519.Variant.SubF = some x → seed.AttackerKnows (runTraceMoves r ms) :=
    fun hJunk _ _ => (TR.G1.skippedSeedKnownTR_of_litJunk hreach hlog hJunk).2
  have hex_prov : ∃ (st_prov : TRState) (k_own : DY.Bytes),
      st_prov ∈ availableStates r (runTraceMoves r ms) ∧ (st_prov.peerIk = st₀.peerIk ∧ st_prov.myIk = st₀.myIk) ∧
      k_own = ({ st := st₀.spqr, msg := msg₀.pqRatchet } : DY.Spqr.RecvKey.SubF DY.Bytes).pack ∧
      k_own ∈ ownKeys r (runTraceMoves r ms) st_prov msg₀ ∧
      st_prov.peerIk.AttackerKnows (runTraceMoves r ms) ∧ st_prov.myIk.AttackerKnows (runTraceMoves r ms) ∧
      ((∀ msg, msg.version = messageVersion → msg.ratchetKey = pk → msg.counter = msg₀.counter → recvSeed st_prov msg = some seed) ∨
       (∃ (p_src : Participant) (c₀ : RecvChain),
         TR.G1.TRStateStoredAt p_src st_prov srcIdx (runTraceMoves r ms) ∧
         st_prov.sessionInfo p_src = st₀.sessionInfo r.bob ∧ st_prov.initiator = false ∧
         c₀ ∈ st_prov.recv ∧ c₀.ratchetKey = pk ∧ c₀.rIdx = rIdx ∧ msg₀.counter < c₀.index)) := by
    rcases provEvTR_st_prov_or_bobStart r hwf ms r.bob st₀ stateIdx₀ pf.inner msg₀ pk seed rIdx srcIdx skIdx hmp.2.1 hst₀ hlog hctr₀ with
      ⟨st_prov, k_own, hst_prov, hIkEq, hseed_pk, hk_own_eq, hk_own, hPeerK, hMyK⟩ |
      ⟨p_src, st_src, c₀, k_own, hst_at, hst_avail, hIkEq, hsinfo_eq, hinit_f, hc₀, hc₀_rk, hc₀_rIdx, hlt, hk_own_eq, hk_own, hPeerK, hMyK⟩
    · exact ⟨st_prov, k_own, hst_prov, hIkEq, hk_own_eq, hk_own, hPeerK, hMyK, Or.inl hseed_pk⟩
    · exact ⟨st_src, k_own, hst_avail, hIkEq, hk_own_eq, hk_own, hPeerK, hMyK,
        Or.inr ⟨p_src, c₀, hst_at, hsinfo_eq, hinit_f, hc₀, hc₀_rk, hc₀_rIdx, hlt⟩⟩
  obtain ⟨st_prov, k_own, hst_prov, hIkEq, hk_own_eq, hk_own, hPeerK, hMyK, hseed_or_provB⟩ := hex_prov
  obtain ⟨_, hk_own_gam⟩ :=
    spqrRecv_step_gamma_state_and_key interpretation hext.1 r S hSeq g ms pf.message st₀ g_rw t' msg₀ pf.inner newPqrState pqrKey hpq_sess ht' hparse₀ htry hrecv_spqr
  rw [← hk_own_eq] at hk_own_gam
  obtain ⟨_, _, _, _, _, _, _, _, hmk_ctr, _, _, _⟩ := takeSkippedKey_ok_some_inv hTake
  have hmkGen_eq : mkGen = ⟨gamma interpretation S g seed, pf.inner.counter⟩ := by
    rcases mkGen with ⟨sd, ct⟩; dsimp only at hseed_gam hmk_ctr; subst hseed_gam hmk_ctr; rfl
  obtain ⟨_, _, _, hloc_ser, ⟨rem0, hrem0, hrem_ser⟩, _⟩ := stateRel_sessionToRecordRec_extract_TR interpretation S g st₀ g_rw.sess hrel₀_sess
  rw [hRem] at hrem0; injection hrem0 with hrem_eq; subst hrem_eq
  obtain ⟨hDecOk, hMacBytes⟩ := prom_dec_mac_gamma (peerIk := st_prov.peerIk) (myIk := st_prov.myIk)
    g htry hk_own_gam hmkGen_eq hDec hMac
    (by rw [hIkEq.1]; exact hrem_ser.trans hks₀.peerIk_ser)
    (by rw [hIkEq.2]; exact hloc_ser.trans hks₀.myIk_ser) (ht'.2.2.2 msg₀ hparse₀).1
  obtain ⟨t₁, msg₁, ht₁_rep, hparse₁, hver₁, hrk₁, hctr₁, hMacBytes₁, hDisj⟩ :=
    hseed_or_provB.elim
      (fun hseed_pk => hPkD_nil r.bob stateIdx₀ pf.message pt pf.inner st₀ st_prov t' pk seed k_own msg₀ rIdx srcIdx skIdx
        htry ht' hparse₀ hver₀ hctr₀ hncol hnors.1 hst₀ hst_prov hIkEq hseed_pk
        hk_own hk_own_eq hlog hctx.atF.hist hIW hSeedK_var hγ_pk hMacBytes hPeerK hMyK hDecOk)
      (fun ⟨p_src, c₀, hst_at, hsinfo_eq, hinit_f, hc₀, hc₀_rk, hc₀_rIdx, hlt⟩ =>
        slotG2_skipped_provB_dispatch_at hext.1 r.bob p_src pf.message pt pf.inner st₀ st_prov c₀
          t' pk seed k_own msg₀ rIdx srcIdx skIdx hmp_nil hctx.atF htry ht' hparse₀ hver₀ hctr₀ hncol
          hst_at hst_prov hsinfo_eq hinit_f hc₀ hc₀_rk hc₀_rIdx hlt hk_own hlog hIW hγ_pk hMacBytes hPeerK hMyK hDecOk)
  obtain ⟨t_m, msg', pqSalt, ptTerm, spqr', key, spqrMsgIdx, ht_m_rep, hpqSalt_kn, ht_m_kn, hparse', hver', hrk', hctr'_msg₁,
      hspqr_step, _, hmac', hdec', ht_m_gam, hpt_gam⟩ :=
    decryptWitness_of_g1_disj_at interpretation hext.1 r S hSeq g r.bob stateIdx₀ ms (acc ++ []) e'.sent
      rec pf.message pt rec₀ st₀ st₀ st_prov g_rw t₁ msg₁ pf.inner pk seed k_own newPqrState pqrKey
      hmp_nil hfit_nil hsent_nil hrecBytes₀ hrel₀ rfl hst₀ hC.out.hcan_in hpq htry
      ht₁_rep hparse₁ hver₁ hrk₁ hIkEq hk_own_gam hMacBytes₁ hPeerK hMyK hDecOk hrecv_spqr hDisj
  have hsk_at' : ((runTraceMoves r ms).at? skIdx : Option RecvDec.TREntry) =
      some ⟨TREvent.SkippedKeyStored (st₀.sessionInfo r.bob) msg'.ratchetKey msg'.counter seed rIdx srcIdx⟩ := by
    rw [hrk', hctr'_msg₁.trans (hctr₁.trans hctr₀)]; exact hsk_at
  have hbk := prom_baseKeyInSession_of_rbks hC.entry.pm hC.out.hpf hC.entry.rec_lookup
    (hC.entry.ready.2.1.bks hc) hc.matched.2.1 hst₀ hcur₀ ⟨fun _ _ _ => rfl, rfl⟩ pqSalt t_m
  let tr₀ := runTraceMoves r ms
  let ms₂ := ms ++ [Move.attackerSend pqSalt, Move.attackerSend t_m]
  obtain ⟨htr₂, _, hmp₂, hcur₂, hst₂, hmsg₂⟩ := prom_two_attackerSend_setup hmp hpqSalt_kn ht_m_kn hcur₀ hst₀
  have hsk₂ : ((runTraceMoves r ms₂).at? skIdx : Option RecvDec.TREntry) =
      some ⟨TREvent.SkippedKeyStored (st₀.sessionInfo r.bob) msg'.ratchetKey msg'.counter seed rIdx srcIdx⟩ := by
    rw [htr₂, RecvDec.at?_append_non_entry _ _ rfl, RecvDec.at?_append_non_entry _ _ rfl]; exact hsk_at'
  have hunused₂ : skippedKeyUsedB (runTraceMoves r ms₂) skIdx = false := by
    rw [htr₂, skippedKeyUsedB_append_non_tr_a2 _ _ rfl, skippedKeyUsedB_append_non_tr_a2 _ _ rfl]; exact hunused
  have hpqSalt₂ : (((runTraceMoves r ms₂).append (⟨key⟩ : Network.ExecEntryT)).at? tr₀.length : Option Network.ExecEntryT) = some ⟨pqSalt⟩ := by
    rw [htr₂,
        RecvDec.at?_append_of_lt _ _
          (by simp only [Symbolic.DYBridge.DY.Trace.append_eq_1, Symbolic.DYBridge.DY.Trace.length_eq_2, tr₀]; omega),
        RecvDec.at?_append_of_lt _ _
          (by simp only [Symbolic.DYBridge.DY.Trace.append_eq_1, Symbolic.DYBridge.DY.Trace.length_eq_2, tr₀]; omega)]
    exact Trace.at?_append tr₀ (⟨pqSalt⟩ : Network.ExecEntryT)
  have hnext := decryptSkipped_next_eq (wrapped := true) hst₂ hmsg₂ hparse' hver' hsk₂ hunused₂ hspqr_step hpqSalt₂ hmac' hdec' (by rw [hrk']; exact hfind_pk)
  refine ⟨g, stateIdx₀, spqrMsgIdx, pqSalt, t_m,
    Move.decryptSkipped r.bob stateIdx₀ (tr₀.length + 1) skIdx tr₀.length spqrMsgIdx (decide (tag ≠ wireWhisperTag)),
    ⟨fun _ _ _ => rfl, rfl⟩, ht_m_rep, hpqSalt_kn, hcur₀, Or.inr ⟨skIdx, rfl⟩, ?_⟩
  rw [decide_eq_true (prom_tag_ne_wireWhisperTag_of_parsePreKeyWire hC.out.hpf),
      show ms ++ ([.attackerSend pqSalt, .attackerSend t_m] ++ [.decryptSkipped r.bob stateIdx₀ (tr₀.length + 1) skIdx tr₀.length spqrMsgIdx true]) =
        ms₂ ++ [.decryptSkipped r.bob stateIdx₀ (tr₀.length + 1) skIdx tr₀.length spqrMsgIdx true] by simp [ms₂, List.append_assoc]]
  refine ⟨hmp₂.1, modelRun_snoc_decryptSkipped r.bob stateIdx₀ (tr₀.length + 1) skIdx tr₀.length spqrMsgIdx true hmp₂.2.1 hcur₂, ?_⟩
  rw [TR.runVis_snoc, vis_decryptSkipped hnext, decVis_true, hmsg₂, newRandoms_decSkippedTr, receivedPlaintext_decSkippedTr, exposures_decSkippedTr]
  refine TR.forall₂_append hmp₂.2.2.2.2.2 (List.Forall₂.cons ?_ (List.Forall₂.cons ?_ List.Forall₂.nil))
  · unfold EventMatchesEntry; dsimp only; exact ⟨rfl, t_m, pf, rfl, hC.out.hpf, hbk, ht_m_gam.symm⟩
  · unfold EventMatchesEntry trEntry trLayout; dsimp only; exact ⟨rfl, by simp only [List.map, hpt_gam]; rfl⟩

set_option maxHeartbeats 400000 in
private theorem prom_rawKn_noRatchet
    {interpretation : ExternInterpretation} {r : ProtocolSetup} {S : OpaqueSymbolSemantics}
    {who : List Participant} {ok : Nat → Bool}
    (hext : ExternContractsHoldCli interpretation) (hwf : ProtocolSetupWF r) (hSeq : S = compSemOf interpretation r)
    (hVer : PromVersionOK interpretation r S who ok)
    {j : Nat} {e' : PromTurn} {mid acc : List MachineEvent}
    {rec : HwBytes} {tag : BitVec 8} {body : HwBytes} {sm : StateAndMessage} {pf : PreKeyFields}
    {sess sess' : Session (List (BitVec 8))} {coins : BitVec 256} {expected : Option (List (BitVec 8))} {pt : List (BitVec 8)}
    (hC : PromAcceptCallBy₂ interpretation r S who ok j e' mid acc rec (tag :: body) sm pf sess sess' coins expected pt)
    (hsel : PromDecSelNoRatchet sess pf.inner mid coins)
    {g : Ghost} {ms : List Move} {t' : DY.Bytes}
    (hc : CleanBy interpretation r S who ok g ms acc) (hctx : PromRawCtx interpretation r S g ms acc)
    (ht' : t' ∈ recvRepresentations interpretation r S g ms pf.message)
    (hncol : ¬ RecvCollision interpretation r S g ms t')
    (hnors : RecvExcuseFree interpretation r S who ok g ms acc (.recv (tag :: body)) (mid ++ [.accept pt]) pf.message t') :
    PromXplRawKnWitness interpretation r S g ms acc mid r.bob tag body pf.message pt := by
  have hmp : MatchedPrefix interpretation r S who g ms acc := hc.matched
  have hmp_nil : MatchedPrefix interpretation r S who g ms (acc ++ []) := by simpa only [List.append_nil] using hmp
  have hIW : InstallWitnessTR r (runTraceMoves r ms) := installWitnessTR_of_reachable r ms hc.matched.2.1.2.2.1.1
  have hPkD_nil : NoRatchetPkDispatchAt interpretation r S g ms (acc ++ []) := by simpa only [List.append_nil] using hctx.pkNR
  have hsent_nil : e'.sent = sentBodies (acc ++ []) := by simpa only [List.append_nil] using hC.entry.sent_eq
  have hfit_nil : TR.SendsFit (acc ++ []) := by simpa only [List.append_nil] using hC.entry.ready.2.1.sendsFit
  have hpq : PqFromHonest e'.sent pf.message := hC.entry.pqh pf hC.out.hpf
  have htry : SignalMessage.tryFrom protoSignalCodec pf.message = .ok pf.inner := parsePreKeyWire_inner_tryFrom hC.out.hpf
  obtain ⟨hrsi, hnodup_rc⟩ := prom_bob_session_extract hwf hC hc
  obtain ⟨_, rec₀, st₀, stateIdx₀, hrecBytes₀, hst₀, hcur₀, hrel₀, _, _, hks₀, hnd₀⟩ := hrsi r.bob rec (by simp only [↓reduceIte])
  let g_rw : RecvWireGhost :=
    { who := 1, aPtr := 0, meBytes := [], stateBytes := rec, sess := sess,
      wirePtr := 0, wireBytes := wireWhisperTag :: pf.message, cur := 0, rest := [], tlsInit := none }
  obtain ⟨hnorm_eq, hrel₀_sess, hpq_sess, _, _, _, _⟩ :=
    pqRatchetState_eq_gamma_pending interpretation S g rec rec₀ st₀ st₀ g_rw hrecBytes₀ hrel₀ hC.out.hcan_in rfl
  have hrc_rec₀ : rec₀.current.receiverChains = (sessionToRecordRec g_rw.sess).current.receiverChains :=
    congrArg (fun r => r.current.receiverChains) hnorm_eq
  obtain ⟨remIk, ck, ck_adv, ck_next, r_adv, r2, mkGen, newPqrState, pqrKey, _,
      hmid_nil, _, hRem, hFind, hNotLt, hJump, hAdv, hNext, hSet, hMkGen, hrecv_spqr, hMac, hDec, _, _, _⟩ :=
    prom_adapter_noRatchet_out hC.out hnodup_rc hsel
  subst hmid_nil
  obtain ⟨msg₀, hparse₀⟩ := Option.isSome_iff_exists.mp ht'.2.2.1
  have hst₀_avail : st₀ ∈ availableStates r (runTraceMoves r ms) :=
    Symbolic.Swarm.CREF.TR.RecvHistStep2.mem_availableStates_of_at? r ms
      (Symbolic.Swarm.CREF.TR.FreshSigma.at?_eq_some_of_getLocalState_some hst₀)
  obtain ⟨_, _, _, hloc_ser, ⟨rem0, hrem0, hrem_ser⟩, _⟩ := stateRel_sessionToRecordRec_extract_TR interpretation S g st₀ g_rw.sess hrel₀_sess
  have hst₀_rci : TrStateRkCkIk r st₀ := trStateRkCkIk_of_getLocalState hmp.2.1 hst₀
  have hNodupSym : (st₀.recv.map RecvChain.ratchetKey).Nodup := nodup_ratchetKey_of_stateRel_tr hrel₀_sess (hrc_rec₀ ▸ hnd₀.1)
  have hctr₀ : msg₀.counter = UInt32.ofBitVec pf.inner.counter := UInt32.ext (((ht'.2.2.2 msg₀ hparse₀).2.2.2 pf.inner htry).2.2.2.1)
  obtain ⟨_, _, c, _, seed, c', _, hc0, hfind₀, _, _htheir, _, _, hcons₀_bv, hSeedEq, hCntEq, _, _, _, _, _⟩ :=
    stateRel_and_consumeMessageKey_of_existing_tr interpretation S g hrel₀_sess hNodupSym
      (hst₀_rci.recv_ck_len interpretation S g hwf hmp.1)
      (Symbolic.Swarm.CREF.TR.RecvRep.gamma_litOf interpretation S g newPqrState) hFind hNotLt hJump hAdv hNext hSet
  have hc_mem : c ∈ st₀.recv := List.mem_of_getElem? hc0
  have hcons₀ : consumeMessageKey c msg₀.counter = some (seed, c') := hctr₀ ▸ hcons₀_bv
  have hγ_c_rk : gamma interpretation S g c.ratchetKey = pf.inner.senderRatchetKey.bytes.toList := by
    rw [_htheir]; simp [vec32, hctx.atF.lens st₀ hst₀_avail c hc_mem]
  have hrk_oi : RkKnownOrInit (runTraceMoves r ms) c.ratchetKey := (storedRkKnown_of_modelRun hmp.2.1 st₀ hst₀_avail).ratchetKey hc_mem
  have hver_pf : pf.inner.messageVersion = 4#8 := hVer j e' [] acc rec (tag :: body) sm pf sess sess' coins expected pt hC
  have hver₀ : msg₀.version = messageVersion := UInt8.ext (by rw [((ht'.2.2.2 msg₀ hparse₀).2.2.2 pf.inner htry).2.2.2.2, hver_pf]; rfl)
  have hseed_c : msg₀.ratchetKey = c.ratchetKey → recvSeed st₀ msg₀ = some seed := by
    intro hrk₀; unfold recvSeed; simp only [hver₀, ↓reduceIte, recvChainFor, hrk₀, hfind₀]
    change Option.map Prod.fst (consumeMessageKey c msg₀.counter) = some seed; rw [hcons₀]; rfl
  let k_own : DY.Bytes := ({ st := st₀.spqr, msg := msg₀.pqRatchet } : DY.Spqr.RecvKey.SubF DY.Bytes).pack
  have hk_own : k_own ∈ ownKeys r (runTraceMoves r ms) st₀ msg₀ :=
    List.mem_map_of_mem (List.mem_filter.mpr ⟨hst₀_avail, beq_self_eq_true _⟩)
  have hk_own_gam := (spqrRecv_step_gamma_state_and_key interpretation hext.1
    r S hSeq g ms pf.message st₀ g_rw t' msg₀ pf.inner newPqrState pqrKey hpq_sess ht' hparse₀ htry hrecv_spqr).2
  have hmkGen_eq : mkGen = ⟨gamma interpretation S g seed, pf.inner.counter⟩ := by
    rw [hMkGen]; change ck_adv.messageKeys (sha256CompressFunction interpretation) = _
    rcases h : ck_adv.messageKeys (sha256CompressFunction interpretation) with ⟨sd, ct⟩
    rw [h] at hSeedEq hCntEq; dsimp only at hSeedEq hCntEq; subst hSeedEq hCntEq; rfl
  rw [hRem] at hrem0; injection hrem0 with hrem_eq; subst hrem_eq
  obtain ⟨hDecOk, hMacBytes⟩ := prom_dec_mac_gamma g htry hk_own_gam hmkGen_eq hDec hMac
    (hrem_ser.trans hks₀.peerIk_ser) (hloc_ser.trans hks₀.myIk_ser) (ht'.2.2.2 msg₀ hparse₀).1
  obtain ⟨hPeerK, hMyK⟩ := prom_st_ik_knows hwf ms hst₀_rci
  obtain ⟨t₁, msg₁, ht₁_rep, hparse₁, hver₁, hrk₁, hctr₁, hMacBytes₁, hDisj⟩ :=
    hPkD_nil r.bob stateIdx₀ pf.message pt pf.inner st₀ c c' t' seed k_own msg₀ hmp.2.1 hmp.2.1.2.2.1.1
      htry ht' hparse₀ hver₀ hctr₀ hncol hnors.1 hst₀ hc_mem hcons₀ hseed_c hk_own
      hctx.atF.hist hIW hrk_oi hγ_c_rk hMacBytes hPeerK hMyK hDecOk
  obtain ⟨t_m, msg', pqSalt, ptTerm, spqr', key, spqrMsgIdx,
      ht_m_rep, hpqSalt_kn, ht_m_kn, hparse', hver', hrk', hctr',
      hspqr_step, _, hmac', hdec', ht_m_gam, hpt_gam⟩ :=
    noRatchet_decryptWitness_of_g1_disj_at interpretation hext.1
      r S hSeq g r.bob stateIdx₀ ms (acc ++ []) e'.sent
      rec pf.message pt rec₀ st₀ g_rw t₁ msg₁ pf.inner c.ratchetKey seed k_own newPqrState pqrKey
      hmp_nil hfit_nil hsent_nil hrecBytes₀ hrel₀ hst₀ hC.out.hcan_in hpq htry ht₁_rep hparse₁ hver₁ hrk₁
      hMacBytes₁ hPeerK hMyK hDecOk hrecv_spqr hDisj
  have hfr_refl : CBadSigmaFrame g g (runTraceMoves r ms).length := ⟨fun _ _ _ => rfl, rfl⟩
  have hbk := prom_baseKeyInSession_of_rbks hC.entry.pm hC.out.hpf hC.entry.rec_lookup
    (hC.entry.ready.2.1.bks hc) hc.matched.2.1 hst₀ hcur₀ hfr_refl pqSalt t_m
  let tr₀ := runTraceMoves r ms
  let ms₂ := ms ++ [Move.attackerSend pqSalt, Move.attackerSend t_m]
  obtain ⟨htr₂, _, hmp₂, hcur₂, hst₂, hmsg₂⟩ := prom_two_attackerSend_setup hmp hpqSalt_kn ht_m_kn hcur₀ hst₀
  have hpqSalt₂ : (((runTraceMoves r ms₂).append (⟨key⟩ : Network.ExecEntryT)).at? tr₀.length : Option Network.ExecEntryT) = some ⟨pqSalt⟩ := by
    rw [htr₂,
        RecvDec.at?_append_of_lt _ _
          (by simp only [Symbolic.DYBridge.DY.Trace.append_eq_1, Symbolic.DYBridge.DY.Trace.length_eq_2, tr₀]; omega),
        RecvDec.at?_append_of_lt _ _
          (by simp only [Symbolic.DYBridge.DY.Trace.append_eq_1, Symbolic.DYBridge.DY.Trace.length_eq_2, tr₀]; omega)]
    exact Trace.at?_append tr₀ (⟨pqSalt⟩ : Network.ExecEntryT)
  have hnext := decrypt_next_noRatchet_eq (wrapped := true) hst₂ hmsg₂ hparse' hver' (hrk' ▸ hfind₀) ((hctr'.trans hctr₁) ▸ hcons₀) hspqr_step hpqSalt₂ hmac' hdec'
  have hpre_pt : receivedPlaintext (runTraceMoves r ms₂) ((runTraceMoves r ms₂).append (⟨key⟩ : Network.ExecEntryT)) = none := by
    rw [receivedPlaintext_append_of_proj (Nat.le_refl _) _ rfl, receivedPlaintext_self]
  refine ⟨g, stateIdx₀, spqrMsgIdx, pqSalt, t_m,
    Move.decrypt r.bob stateIdx₀ (tr₀.length + 1) tr₀.length spqrMsgIdx (decide (tag ≠ wireWhisperTag)),
    hfr_refl, ht_m_rep, hpqSalt_kn, hcur₀, Or.inl rfl, ?_⟩
  rw [decide_eq_true (prom_tag_ne_wireWhisperTag_of_parsePreKeyWire hC.out.hpf),
      show ms ++ ([.attackerSend pqSalt, .attackerSend t_m] ++ [.decrypt r.bob stateIdx₀ (tr₀.length + 1) tr₀.length spqrMsgIdx true]) =
        ms₂ ++ [.decrypt r.bob stateIdx₀ (tr₀.length + 1) tr₀.length spqrMsgIdx true] by simp [ms₂, List.append_assoc]]
  refine ⟨hmp₂.1, RecvDec.modelRun_snoc_decrypt r.bob stateIdx₀ (tr₀.length + 1) tr₀.length spqrMsgIdx true hmp₂.2.1 hcur₂, ?_⟩
  rw [TR.runVis_snoc, vis_decrypt hnext, decVis_true, hmsg₂, newRandoms_decNoRatchet,
      receivedPlaintext_decTailTr
        (by simp only [Symbolic.DYBridge.DY.Trace.append_eq_1, Symbolic.DYBridge.DY.Trace.length_eq_2]; omega)
        hpre_pt, exposures_decNoRatchet]
  refine RecvDec.forall₂_append hmp₂.2.2.2.2.2 (List.Forall₂.cons ?_ (List.Forall₂.cons ?_ List.Forall₂.nil))
  · unfold EventMatchesEntry; dsimp only; exact ⟨rfl, t_m, pf, rfl, hC.out.hpf, hbk, ht_m_gam.symm⟩
  · unfold EventMatchesEntry trEntry trLayout; dsimp only; exact ⟨rfl, by simp only [List.map, hpt_gam]; rfl⟩

set_option maxHeartbeats 400000 in
private theorem prom_rawKn_ratchetDH
    {interpretation : ExternInterpretation} {r : ProtocolSetup} {S : OpaqueSymbolSemantics}
    {who : List Participant} {ok : Nat → Bool}
    (hext : ExternContractsHoldCli interpretation) (hwf : ProtocolSetupWF r) (hSeq : S = compSemOf interpretation r)
    (hVer : PromVersionOK interpretation r S who ok)
    {j : Nat} {e' : PromTurn} {mid acc : List MachineEvent}
    {rec : HwBytes} {tag : BitVec 8} {body : HwBytes} {sm : StateAndMessage} {pf : PreKeyFields}
    {sess sess' : Session (List (BitVec 8))} {coins : BitVec 256} {expected : Option (List (BitVec 8))} {pt : List (BitVec 8)}
    (hC : PromAcceptCallBy₂ interpretation r S who ok j e' mid acc rec (tag :: body) sm pf sess sess' coins expected pt)
    (hsel : PromDecSelRatchetDH sess pf.inner mid coins)
    {g : Ghost} {ms : List Move} {t' : DY.Bytes}
    (hc : CleanBy interpretation r S who ok g ms acc) (hctx : PromRawCtx interpretation r S g ms acc)
    (ht' : t' ∈ recvRepresentations interpretation r S g ms pf.message)
    (hncol : ¬ RecvCollision interpretation r S g ms t') :
    PromXplRawKnWitness interpretation r S g ms acc mid r.bob tag body pf.message pt := by
  have hmp : MatchedPrefix interpretation r S who g ms acc := hc.matched
  have hmp_nil : MatchedPrefix interpretation r S who g ms (acc ++ []) := by simpa only [List.append_nil] using hmp
  have hsent_nil : e'.sent = sentBodies (acc ++ []) := by simpa only [List.append_nil] using hC.entry.sent_eq
  have hfit_nil : TR.SendsFit (acc ++ []) := by simpa only [List.append_nil] using hC.entry.ready.2.1.sendsFit
  have hpq : PqFromHonest e'.sent pf.message := hC.entry.pqh pf hC.out.hpf
  have htry : SignalMessage.tryFrom protoSignalCodec pf.message = .ok pf.inner := parsePreKeyWire_inner_tryFrom hC.out.hpf
  obtain ⟨hrsi, _⟩ := prom_bob_session_extract hwf hC hc
  obtain ⟨_, rec₀, st₀, stateIdx₀, hrecBytes₀, hst₀, hcur₀, hrel₀, _, _, hks₀, _⟩ := hrsi r.bob rec (by simp)
  let g_rw : RecvWireGhost :=
    { who := 1, aPtr := 0, meBytes := [], stateBytes := rec, sess := sess,
      wirePtr := 0, wireBytes := wireWhisperTag :: pf.message, cur := 0, rest := [], tlsInit := none }
  obtain ⟨_, hrel₀_sess, _, _, _, _, _⟩ :=
    pqRatchetState_eq_gamma_pending interpretation S g rec rec₀ st₀ st₀ g_rw hrecBytes₀ hrel₀ hC.out.hcan_in rfl
  obtain ⟨rngBytes, remIk, ck, ck_adv, ck_next, r1, r_adv, r2, mkGen, newPqrState, pqrKey, _,
      hmid_rng, hrng_len, _, hRem, hFind, hDh, hNotLt, hJump, hAdv, hNext, hSet, hMkGen,
      hrecv_spqr, hMac, hDec, _, _, _⟩ := prom_adapter_ratchetDH_out hC.out hsel
  subst hmid_rng
  obtain ⟨msg₀, hparse₀⟩ := Option.isSome_iff_exists.mp ht'.2.2.1
  let g' : Ghost := { g with σ := updateFreshAt g.σ ((runTraceMoves r ms).length + 2) 32 rngBytes }
  have hreach : (runTraceMoves r ms).Reachable reachability := hmp.2.1.2.2.1.1
  have hst_avail : st₀ ∈ availableStates r (runTraceMoves r ms) :=
    Symbolic.Swarm.CREF.TR.RecvHistStep2.mem_availableStates_of_at? r ms
      (Symbolic.Swarm.CREF.TR.FreshSigma.at?_eq_some_of_getLocalState_some hst₀)
  obtain ⟨hRng, hmp', _, hrel₀', hks₀', _hst_lt, _hmsg_lt, _ht_gam, _hwire_gam, _hmac_gam, _hrk_gam, _hct_gam, _hpq_gam, _, _⟩ :=
    ratchetDH_sigma_bridge interpretation r hwf S (pureTrSlots r) g ms (acc ++ [])
      (fun q => if q = r.bob then some rec else none) r.bob stateIdx₀ st₀ (sessionToRecordRec g_rw.sess) t' msg₀
      ((runTraceMoves r ms).length + 2) rngBytes (by omega) hmp_nil hrsi hst₀ hrel₀_sess hks₀ ht'.1 hparse₀
  have htr_lt : TraceEntriesLt interpretation S g ((runTraceMoves r ms).length + 2) (runTraceMoves r ms) :=
    traceEntriesLt_of_reachable interpretation S g ((runTraceMoves r ms).length + 2) hreach (by omega)
  obtain ⟨_, _, _, hloc_ser, ⟨rem0, hrem0, hrem_ser⟩, _⟩ := stateRel_sessionToRecordRec_extract_TR interpretation S g' st₀ g_rw.sess hrel₀'
  have hst₀_rci : TrStateRkCkIk r st₀ := trStateRkCkIk_of_getLocalState hmp'.2.1 hst₀
  have hTheir' : pf.inner.senderRatchetKey.bytes.toList = gamma interpretation S g' msg₀.ratchetKey :=
    ((ht'.2.2.2 msg₀ hparse₀).2.2.2 pf.inner htry).2.1.symm.trans _hrk_gam.symm
  have hPkLen : (gamma interpretation S g' msg₀.ratchetKey).length = 32 := hTheir' ▸ pf.inner.senderRatchetKey.bytes.2
  have hTheir : pf.inner.senderRatchetKey = ⟨vec32 (gamma interpretation S g' msg₀.ratchetKey)⟩ := by
    cases hmk : pf.inner.senderRatchetKey with | mk b =>
    exact congrArg PublicKey.mk (Subtype.ext ((hmk ▸ hTheir').trans (vec32_toList_of_length_eq_tr hPkLen).symm))
  have ht₀' : t' ∈ recvRepresentations interpretation r S g' ms pf.message := by
    refine ⟨ht'.1, _ht_gam.trans ht'.2.1, ht'.2.2.1, fun msg hmsg => ?_⟩
    rcases Option.some.inj (hparse₀.symm.trans hmsg) with rfl
    have h₀ := ht'.2.2.2 msg₀ hparse₀
    exact ⟨_hwire_gam.trans h₀.1, _hmac_gam.trans h₀.2.1, h₀.2.2.1, fun parsed hparsed =>
      let hp := h₀.2.2.2 parsed hparsed
      ⟨_hct_gam.trans hp.1, _hrk_gam.trans hp.2.1, _hpq_gam.trans hp.2.2.1, hp.2.2.2⟩⟩
  have hJump' : (pf.inner.counter - ck.index).toNat ≤ CryptoGames.LibsignalSession.maxForwardJumps := by
    obtain ⟨_, _, _, _, _, _, _, hr1⟩ := Proofs.libsignal.RngG.R3.dhRatchetStep_ok_inv hDh; rwa [hr1] at hJump
  have hctr₀ : msg₀.counter = UInt32.ofBitVec pf.inner.counter := UInt32.ext (((ht₀'.2.2.2 msg₀ hparse₀).2.2.2 pf.inner htry).2.2.2.1)
  have hCkLens := hst₀_rci.recv_ck_len interpretation S g' hwf hmp'.1
  obtain ⟨hfind₀, _, seed, c', hcons₀_bv, hSeedEq, hCntEq, _, _, _, _, _, _, _, _⟩ :=
    stateRel_and_consumeMessageKey_of_dhRatchetStep_tr interpretation S g' hext.1 (hrel := hrel₀')
      (hRkLen := hst₀_rci.rk_len interpretation S g' hwf hmp'.1) (hDhsLen := hks₀'.1) (hCkLens := hCkLens)
      (hTheir := hTheir) (hPkLen := hPkLen) (hRng := hRng) (hRngLen := hrng_len)
      (hspqr' := Symbolic.Swarm.CREF.TR.RecvRep.gamma_litOf interpretation S g' newPqrState)
      (hFindNone := hFind) (hStep := hDh) (hNotLt := hNotLt) (hJump := hJump') (hAdv := hAdv) (hNext := hNext) (hSet := hSet)
  have hcons₀ : consumeMessageKey (trDhRatchetState st₀ msg₀.ratchetKey ((runTraceMoves r ms).length + 2)).2 msg₀.counter = some (seed, c') := hctr₀ ▸ hcons₀_bv
  have hlow₀ := x25519LowOrder_false_of_dhRatchetStep_ok_tr interpretation S g' hext.1 (hTheir := hTheir') (hDh := hDh)
  have hver_pf : pf.inner.messageVersion = 4#8 := hVer j e' [.rng rngBytes] acc rec (tag :: body) sm pf sess sess' coins expected pt hC
  have hver₀ : msg₀.version = messageVersion := UInt8.ext (by rw [((ht₀'.2.2.2 msg₀ hparse₀).2.2.2 pf.inner htry).2.2.2.2, hver_pf]; rfl)
  have hseed : recvSeed st₀ msg₀ = some seed := by
    unfold recvSeed; simp only [hver₀, ↓reduceIte, recvChainFor, hfind₀, hlow₀, Bool.false_eq_true]
    change Option.map Prod.fst (consumeMessageKey (trDhRatchetState st₀ msg₀.ratchetKey ((runTraceMoves r ms).length + 2)).2 msg₀.counter) = some seed
    rw [hcons₀]; rfl
  let k_own : DY.Bytes := ({ st := st₀.spqr, msg := msg₀.pqRatchet } : DY.Spqr.RecvKey.SubF DY.Bytes).pack
  have hk_own : k_own ∈ ownKeys r (runTraceMoves r ms) st₀ msg₀ :=
    List.mem_map_of_mem (List.mem_filter.mpr ⟨hst_avail, beq_self_eq_true _⟩)
  have hk_own_gam : gamma interpretation S g' k_own = spqrKeyBytes (saltToBytes pqrKey) :=
    (spqrRecv_step_gamma_state_and_key interpretation hext.1 r S hSeq g' ms pf.message st₀ g_rw t' msg₀ pf.inner
      newPqrState pqrKey (congrArg SessionRec.pqRatchetState hrel₀'.2) ht₀' hparse₀ htry hrecv_spqr).2
  have hmkGen_eq : mkGen = ⟨gamma interpretation S g' seed, pf.inner.counter⟩ := by
    rw [hMkGen]; change ck_adv.messageKeys (sha256CompressFunction interpretation) = _
    rcases h : ck_adv.messageKeys (sha256CompressFunction interpretation) with ⟨sd, ct⟩
    rw [h] at hSeedEq hCntEq; dsimp only at hSeedEq hCntEq; subst hSeedEq hCntEq; rfl
  rw [hRem] at hrem0; injection hrem0 with hrem_eq; subst hrem_eq
  obtain ⟨hDecOk, hMacBytes⟩ := prom_dec_mac_gamma g' htry hk_own_gam hmkGen_eq hDec hMac
    (hrem_ser.trans hks₀'.peerIk_ser) (hloc_ser.trans hks₀'.myIk_ser) (ht₀'.2.2.2 msg₀ hparse₀).1
  have hc_lt : ChainStampsLt interpretation S g ((runTraceMoves r ms).length + 2)
      (trDhRatchetState st₀ msg₀.ratchetKey ((runTraceMoves r ms).length + 2)).2 :=
    ⟨_hmsg_lt.2.2.1, (stampsLt_createChain _hst_lt.2.2.1 _hmsg_lt.2.2.1 _hst_lt.2.2.2.1).2⟩
  have hk_own_lt : StampsLt interpretation S g ((runTraceMoves r ms).length + 2) k_own :=
    (stampsLt_spqrRecvKey_pack interpretation S g ((runTraceMoves r ms).length + 2) ⟨st₀.spqr, msg₀.pqRatchet⟩).mpr
      ⟨_hst_lt.2.2.2.2.2.1, _hmsg_lt.2.2.2.2⟩
  have hkeys_lt := stampsLt_trMsgKeys hk_own_lt (stampsLt_consumeMessageKey hc_lt hcons₀).1
  have hMacBytes₁ : pf.message.drop (pf.message.length - 8) =
      gamma interpretation S g (computeMac (trMsgKeys k_own seed).macKey st₀.peerIk st₀.myIk msg₀.wire) := by
    rw [← gamma_updateFreshAt_of_stampsLt interpretation S g ((runTraceMoves r ms).length + 2) 32 rngBytes _
      (stampsLt_computeMac hkeys_lt.2.1 _hst_lt.2.1 _hst_lt.1 _hmsg_lt.1)]; exact hMacBytes
  have hDecOk₁ : interpretation aesCbcDecryptSymbol
      [pf.inner.ciphertext, gamma interpretation S g (trMsgKeys k_own seed).cipherKey, (gamma interpretation S g (trMsgKeys k_own seed).iv).take 16] = some pt := by
    rw [← gamma_updateFreshAt_of_stampsLt interpretation S g ((runTraceMoves r ms).length + 2) 32 rngBytes _ hkeys_lt.1,
        ← gamma_updateFreshAt_of_stampsLt interpretation S g ((runTraceMoves r ms).length + 2) 32 rngBytes _ hkeys_lt.2.2]; exact hDecOk
  obtain ⟨hPeerK, hMyK⟩ := prom_st_ik_knows hwf ms hst₀_rci
  have hDisjRks := recv_mac_authentic_or_rkSwap_seed_known_of_not_collision_explains'
    interpretation hext.1 r S g ms pf.message pt pf.inner hc.1 hctx.abs' hreach
    htry t' msg₀ ht' hparse₀ hncol st₀ hst_avail hfind₀ seed hseed k_own hk_own hMacBytes₁ hDecOk₁
  have hHon : PqFromHonest (sentBodies (acc ++ [])) pf.message := hsent_nil ▸ hpq
  obtain ⟨rk_c, seed_c, c'_c, t_m, msg', pqSalt, ptTerm, spqr', key, spqrMsgIdx,
      _, hγ_rk_c₁, _, hcons_c, ht_m_rep, hpqSalt_kn, ht_m_kn,
      hparse', hver', hrk', _, hspqr_step, _, hmac', hdec', ht_m_gam₁, hpt_gam₁, _, _, _, _, _⟩ :=
    hDisjRks.elim
      (fun hRkSwap => spqrRecv_step_bridge_ratchetDH_rkSwap_nw
        interpretation hext.1 r S hSeq g r.bob stateIdx₀ ms (acc ++ []) rec pf.message pt
        rec₀ st₀ g_rw t' msg₀ pf.inner seed k_own c' newPqrState pqrKey
        hmp_nil hfit_nil hrecBytes₀ hrel₀ hst₀ hC.out.hcan_in hHon htry ht' hparse₀ hver₀ hctr₀ hcons₀
        hMacBytes₁ hPeerK hMyK hDecOk₁ hrecv_spqr (Or.inl hRkSwap))
      (fun ⟨salt₁, _, hrk_sid, hAuth, hMacBytes_salt₁, hDecOk_salt₁⟩ =>
        spqrRecv_step_bridge_ratchetDH_rkSwap_nw
          interpretation hext.1 r S hSeq g r.bob stateIdx₀ ms (acc ++ []) rec pf.message pt
          rec₀ st₀ g_rw t' msg₀ pf.inner seed salt₁ c' newPqrState pqrKey
          hmp_nil hfit_nil hrecBytes₀ hrel₀ hst₀ hC.out.hcan_in hHon htry ht' hparse₀ hver₀ hctr₀ hcons₀
          hMacBytes_salt₁.symm hPeerK hMyK hDecOk_salt₁ hrecv_spqr (Or.inr ⟨hrk_sid, hAuth⟩))
  have ht_m_lt : StampsLt interpretation S g ((runTraceMoves r ms).length + 2) t_m := traceEntriesLt_knows htr_lt ht_m_kn
  have hmsg'_lt := stampsLt_parseTrSignalMsg ht_m_lt hparse'
  have hγ_rk_c : gamma interpretation S g' rk_c = gamma interpretation S g' msg₀.ratchetKey := by
    rw [gamma_updateFreshAt_of_stampsLt interpretation S g ((runTraceMoves r ms).length + 2) 32 rngBytes rk_c (hrk' ▸ hmsg'_lt.2.2.1),
        gamma_updateFreshAt_of_stampsLt interpretation S g ((runTraceMoves r ms).length + 2) 32 rngBytes msg₀.ratchetKey _hmsg_lt.2.2.1]
    exact hγ_rk_c₁
  have ht_m_gam : gamma interpretation S g' t_m = pf.message := by
    rw [gamma_updateFreshAt_of_stampsLt interpretation S g ((runTraceMoves r ms).length + 2) 32 rngBytes t_m ht_m_lt]; exact ht_m_gam₁
  have hpt_gam : gamma interpretation S g' ptTerm = pt := by
    rw [gamma_updateFreshAt_of_stampsLt interpretation S g ((runTraceMoves r ms).length + 2) 32 rngBytes ptTerm
      (stampsLt_symDec hdec' hmsg'_lt.2.2.2.1)]; exact hpt_gam₁
  have hfind' : findRecvChain st₀.recv msg'.ratchetKey = none := hrk' ▸
    (findRecvChain_eq_none_of_dhRatchetStep_rkSwap (msg₀ := msg₀) interpretation S g' hrel₀' hCkLens hFind hTheir hγ_rk_c).1
  have hlow' : x25519LowOrder msg'.ratchetKey = false := hrk' ▸
    x25519LowOrder_false_of_dhRatchetStep_rkSwap (msg₀ := msg₀) interpretation S g' hext.1 (hTheir₀ := hTheir) (hPkLen₀ := hPkLen) (hγ_rk_c := hγ_rk_c) (hDh := hDh)
  have hfr : CBadSigmaFrame g g' (runTraceMoves r ms).length := ⟨fun _ _ _ => ite_eq_right (by omega), rfl⟩
  have hbk := prom_baseKeyInSession_of_rbks hC.entry.pm hC.out.hpf hC.entry.rec_lookup
    (hC.entry.ready.2.1.bks hc) hc.matched.2.1 hst₀ hcur₀ hfr pqSalt t_m
  let tr₀ := runTraceMoves r ms
  let ms₂ := ms ++ [Move.attackerSend pqSalt, Move.attackerSend t_m]
  obtain ⟨htr₂, hlen₂, hmp₂, hcur₂, hst₂, hmsg₂⟩ := prom_two_attackerSend_setup
    (by simpa only [List.append_nil] using hmp') hpqSalt_kn ht_m_kn hcur₀ hst₀
  have hpqSalt₂ : ((((runTraceMoves r ms₂).append (⟨32⟩ : DY.Random.ExecEntryT)).append (⟨key⟩ : Network.ExecEntryT)).at? tr₀.length :
      Option Network.ExecEntryT) = some ⟨pqSalt⟩ := by
    rw [htr₂,
        RecvDec.at?_append_of_lt _ _
          (by simp only [Symbolic.DYBridge.DY.Trace.append_eq_1, Symbolic.DYBridge.DY.Trace.length_eq_2, tr₀]; omega),
        RecvDec.at?_append_of_lt _ _
          (by simp only [Symbolic.DYBridge.DY.Trace.append_eq_1, Symbolic.DYBridge.DY.Trace.length_eq_2, tr₀]; omega),
        RecvDec.at?_append_of_lt _ _
          (by simp only [Symbolic.DYBridge.DY.Trace.append_eq_1, Symbolic.DYBridge.DY.Trace.length_eq_2, tr₀]; omega)]
    exact Trace.at?_append tr₀ (⟨pqSalt⟩ : Network.ExecEntryT)
  have hcons₂ : consumeMessageKey (trDhRatchetState st₀ msg'.ratchetKey (runTraceMoves r ms₂).length).2 msg'.counter = some (seed_c, c'_c) := by rw [hlen₂]; exact hrk' ▸ hcons_c
  have hspqr₂ : Spqr.spqrRecv (trDhRatchetState st₀ msg'.ratchetKey (runTraceMoves r ms₂).length).1.spqr msg'.pqRatchet spqrMsgIdx = some (spqr', key) := by rw [hlen₂]; exact hrk' ▸ hspqr_step
  have hmac₂ : msg'.mac = computeMac (trMsgKeys pqSalt seed_c).macKey
      (trDhRatchetState st₀ msg'.ratchetKey (runTraceMoves r ms₂).length).1.peerIk
      (trDhRatchetState st₀ msg'.ratchetKey (runTraceMoves r ms₂).length).1.myIk msg'.wire := by rw [hlen₂]; exact hrk' ▸ hmac'
  have hrng₂ : gamma interpretation S g' (randTerm (runTraceMoves r ms₂).length 32) = rngBytes := by
    rw [hlen₂]; exact (prom_gamma_randTerm32_eq interpretation S g' (tr₀.length + 2)).trans hRng
  have hnext := decrypt_next_ratchet_eq (wrapped := true) hst₂ hmsg₂ hparse' hver' hfind' hlow' hcons₂ hspqr₂ hpqSalt₂ hmac₂ hdec'
  dsimp only at hnext
  refine ⟨g', stateIdx₀, spqrMsgIdx, pqSalt, t_m,
    Move.decrypt r.bob stateIdx₀ (tr₀.length + 1) tr₀.length spqrMsgIdx (decide (tag ≠ wireWhisperTag)),
    hfr, ht_m_rep, hpqSalt_kn, hcur₀, Or.inl rfl, ?_⟩
  rw [decide_eq_true (prom_tag_ne_wireWhisperTag_of_parsePreKeyWire hC.out.hpf),
      show ms ++ ([.attackerSend pqSalt, .attackerSend t_m] ++ [.decrypt r.bob stateIdx₀ (tr₀.length + 1) tr₀.length spqrMsgIdx true]) =
        ms₂ ++ [.decrypt r.bob stateIdx₀ (tr₀.length + 1) tr₀.length spqrMsgIdx true] by simp [ms₂, List.append_assoc]]
  refine ⟨hmp₂.1, RecvDec.modelRun_snoc_decrypt r.bob stateIdx₀ (tr₀.length + 1) tr₀.length spqrMsgIdx true hmp₂.2.1 hcur₂, ?_⟩
  rw [TR.runVis_snoc, vis_decrypt hnext, decVis_true, hmsg₂, newRandoms_decRatchet,
      receivedPlaintext_decTailTr
        (by unfold decRatchetPreTr; simp only [Symbolic.DYBridge.DY.Trace.append_eq_1, Symbolic.DYBridge.DY.Trace.length_eq_2]; omega)
        (receivedPlaintext_decRatchetPreTr ..),
      exposures_decRatchet]
  refine RecvDec.forall₂_append hmp₂.2.2.2.2.2 (List.Forall₂.cons ?_ (List.Forall₂.cons ?_ (List.Forall₂.cons ?_ List.Forall₂.nil)))
  · unfold EventMatchesEntry; dsimp only; exact ⟨rfl, t_m, pf, rfl, hC.out.hpf, hbk, ht_m_gam.symm⟩
  · unfold EventMatchesEntry trEntry trLayout; dsimp only; exact ⟨rfl, congrArg (· :: []) hrng₂⟩
  · unfold EventMatchesEntry trEntry trLayout; dsimp only; exact ⟨rfl, by simp only [List.map, hpt_gam]; rfl⟩

theorem prom_rawKnWitness_at_clean
    {interpretation : ExternInterpretation} {r : ProtocolSetup} {S : OpaqueSymbolSemantics}
    {who : List Participant} {ok : Nat → Bool}
    (hext : ExternContractsHoldCli interpretation) (hwf : ProtocolSetupWF r) (hSeq : S = compSemOf interpretation r)
    {j : Nat} {e' : PromTurn} {mid acc : List MachineEvent}
    {rec : HwBytes} {tag : BitVec 8} {body : HwBytes} {sm : StateAndMessage} {pf : PreKeyFields}
    {sess sess' : Session (List (BitVec 8))} {coins : BitVec 256} {expected : Option (List (BitVec 8))} {pt : List (BitVec 8)}
    (hC : PromAcceptCallBy₂ interpretation r S who ok j e' mid acc rec (tag :: body) sm pf sess sess' coins expected pt)
    {g : Ghost} {ms : List Move} {t' : DY.Bytes}
    (hc : CleanBy interpretation r S who ok g ms acc)
    (ht' : t' ∈ recvRepresentations interpretation r S g ms pf.message)
    (hncol : ¬ RecvCollision interpretation r S g ms t')
    (hnors : RecvExcuseFree interpretation r S who ok g ms acc (.recv (tag :: body)) (mid ++ [.accept pt]) pf.message t') :
    PromXplRawKnWitness interpretation r S g ms acc mid r.bob tag body pf.message pt := by
  have hctx := promRawCtx_at_clean hext hwf hC hc
  have hsel := prom_decSel_cases_out hC.out fun hnil =>
    prom_noDrawOK_proved j e' acc rec (tag :: body) sm pf sess sess' coins expected pt (hnil ▸ hC)
  rcases hsel with hSk | hNR | hDH
  · exact prom_rawKn_skipped hext hwf hSeq prom_versionOK_proved hC hSk hc hctx ht' hncol hnors
  · exact prom_rawKn_noRatchet hext hwf hSeq prom_versionOK_proved hC hNR hc hctx ht' hncol hnors
  · exact prom_rawKn_ratchetDH hext hwf hSeq prom_versionOK_proved hC hDH hc hctx ht' hncol

end RawKn

end Symbolic.Swarm.Coinsplit.Lift.L11
